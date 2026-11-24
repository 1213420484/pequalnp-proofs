import Mathlib.Data.List.OfFn
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4907

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [step]
    omega

lemma keepInput (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_lt {α : Type} (l r : List α) (i : ℕ) (d : α) (hi : i < l.length) :
    (l ++ r).getD i d = l.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_snoc_eq {α : Type} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  rw [List.getD_append_right _ _ _ _ (le_refl _)]
  simp

inductive WireVal where
  | const (b : Bool)
  | wire (idx : ℕ)

def evalWV (w : List Bool) : WireVal → Bool
  | .const b => b
  | .wire idx => w.getD idx false

def wvOk (bound : ℕ) : WireVal → Prop
  | .const _ => True
  | .wire idx => idx < bound

def simpGate (n : ℕ) (acc : List Gate) (env : List WireVal) (g : Gate) : List Gate × WireVal :=
  let vs := g.inputs.map (fun i => env.getD i (.const false))
  match g.op, vs with
  | .not, [] => (acc, .const true)
  | .not, .const b :: _ => (acc, .const (!b))
  | .not, .wire i :: _ => (acc ++ [{ op := .not, inputs := [i] }], .wire (n + acc.length))
  | .and, [] => (acc, .const true)
  | .and, [v] => (acc, v)
  | .and, [.const false, _] => (acc, .const false)
  | .and, [_, .const false] => (acc, .const false)
  | .and, [.const true, v] => (acc, v)
  | .and, [v, .const true] => (acc, v)
  | .and, [.wire i, .wire j] => (acc ++ [{ op := .and, inputs := [i, j] }], .wire (n + acc.length))
  | .or, [] => (acc, .const false)
  | .or, [v] => (acc, v)
  | .or, [.const true, _] => (acc, .const true)
  | .or, [_, .const true] => (acc, .const true)
  | .or, [.const false, v] => (acc, v)
  | .or, [v, .const false] => (acc, v)
  | .or, [.wire i, .wire j] => (acc ++ [{ op := .or, inputs := [i, j] }], .wire (n + acc.length))
  | _, _ => (acc, .const false)

def simpLoop (n : ℕ) (gs : List Gate) (st : List Gate × List WireVal) : List Gate × List WireVal :=
  gs.foldl (fun p g =>
    let r := simpGate n p.1 p.2 g
    (r.1, p.2 ++ [r.2])) st

lemma simpGate_len_le (n : ℕ) (acc : List Gate) (env : List WireVal) (g : Gate) :
    (simpGate n acc env g).1.length ≤ acc.length + 1 := by
  unfold simpGate
  cases g.op <;> simp only
  · rcases g.inputs.map (fun i => env.getD i (.const false)) with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, rest⟩⟩⟩
    · simp
    · simp
    · cases v1 with
      | const b1 => cases b1 <;> cases v2 <;> (try cases ‹Bool›) <;> simp
      | wire _ => cases v2 <;> (try cases ‹Bool›) <;> simp
    · simp
  · rcases g.inputs.map (fun i => env.getD i (.const false)) with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, rest⟩⟩⟩
    · simp
    · simp
    · cases v1 with
      | const b1 => cases b1 <;> cases v2 <;> (try cases ‹Bool›) <;> simp
      | wire _ => cases v2 <;> (try cases ‹Bool›) <;> simp
    · simp
  · rcases g.inputs.map (fun i => env.getD i (.const false)) with _ | ⟨v1, rest⟩
    · simp
    · cases v1 <;> simp
  · simp
  · simp

lemma simpLoop_len_le (n : ℕ) (gs : List Gate) (acc : List Gate) (env : List WireVal) :
    (simpLoop n gs (acc, env)).1.length ≤ acc.length + gs.length := by
  induction gs generalizing acc env with
  | nil => simp [simpLoop]
  | cons g gs ih =>
    simp only [simpLoop, List.foldl_cons, List.length_cons]
    have h1 := ih (simpGate n acc env g).1 (env ++ [(simpGate n acc env g).2])
    have h2 := simpGate_len_le n acc env g
    simp only [simpLoop] at h1
    omega

lemma simpGate_fan (n : ℕ) (acc : List Gate) (env : List WireVal) (g : Gate)
    (hacc : ∀ g' ∈ acc, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2) :
    ∀ g' ∈ (simpGate n acc env g).1,
      g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 := by
  have hpush : ∀ (ng : Gate),
      (ng.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ ng.inputs.length ≤ 2) →
      ∀ g' ∈ acc ++ [ng], g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 := by
    intro ng hng g' hg'
    simp only [List.mem_append, List.mem_singleton] at hg'
    rcases hg' with h | rfl
    · exact hacc g' h
    · exact hng
  unfold simpGate
  cases g.op <;> simp only
  · rcases g.inputs.map (fun i => env.getD i (.const false)) with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, rest⟩⟩⟩
    · exact hacc
    · exact hacc
    · cases v1 with
      | const b1 => cases b1 <;> cases v2 <;> (try cases ‹Bool›) <;> exact hacc
      | wire i1 =>
        cases v2 with
        | const b2 => cases b2 <;> exact hacc
        | wire i2 => exact hpush _ (by simp)
    · exact hacc
  · rcases g.inputs.map (fun i => env.getD i (.const false)) with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, rest⟩⟩⟩
    · exact hacc
    · exact hacc
    · cases v1 with
      | const b1 => cases b1 <;> cases v2 <;> (try cases ‹Bool›) <;> exact hacc
      | wire i1 =>
        cases v2 with
        | const b2 => cases b2 <;> exact hacc
        | wire i2 => exact hpush _ (by simp)
    · exact hacc
  · rcases g.inputs.map (fun i => env.getD i (.const false)) with _ | ⟨v1, rest⟩
    · exact hacc
    · cases v1 with
      | const b1 => exact hacc
      | wire i1 => exact hpush _ (by simp)
  · exact hacc
  · exact hacc

lemma simpLoop_fan (n : ℕ) (gs : List Gate) (acc : List Gate) (env : List WireVal)
    (hacc : ∀ g' ∈ acc, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2) :
    ∀ g' ∈ (simpLoop n gs (acc, env)).1,
      g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 := by
  induction gs generalizing acc env with
  | nil => exact hacc
  | cons g gs ih =>
    simp only [simpLoop, List.foldl_cons]
    exact ih _ _ (simpGate_fan n acc env g hacc)

lemma simpGate_ok (n : ℕ) (acc : List Gate) (env : List WireVal) (g : Gate)
    (henv : ∀ i, wvOk (n + acc.length) (env.getD i (.const false))) :
    let r := simpGate n acc env g
    acc.length ≤ r.1.length ∧ wvOk (n + r.1.length) r.2 := by
  have hmem : ∀ v ∈ g.inputs.map (fun i => env.getD i (.const false)), wvOk (n + acc.length) v := by
    intro v hv
    rcases List.mem_map.mp hv with ⟨i, _, rfl⟩
    exact henv i
  unfold simpGate
  cases g.op <;> simp only
  · generalize hvs : g.inputs.map (fun i => env.getD i (.const false)) = vs
    rw [hvs] at hmem
    rcases vs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, rest⟩⟩⟩
    · exact ⟨le_refl _, trivial⟩
    · exact ⟨le_refl _, hmem v1 (by simp)⟩
    · cases v1 with
      | const b1 =>
        cases b1
        · exact ⟨le_refl _, trivial⟩
        · cases v2 with
          | const b2 => cases b2 <;> exact ⟨le_refl _, trivial⟩
          | wire i2 => exact ⟨le_refl _, hmem (.wire i2) (by simp)⟩
      | wire i1 =>
        cases v2 with
        | const b2 =>
          cases b2
          · exact ⟨le_refl _, trivial⟩
          · exact ⟨le_refl _, hmem (.wire i1) (by simp)⟩
        | wire i2 =>
          refine ⟨by simp, ?_⟩
          simp [wvOk]
    · exact ⟨le_refl _, trivial⟩
  · generalize hvs : g.inputs.map (fun i => env.getD i (.const false)) = vs
    rw [hvs] at hmem
    rcases vs with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, rest⟩⟩⟩
    · exact ⟨le_refl _, trivial⟩
    · exact ⟨le_refl _, hmem v1 (by simp)⟩
    · cases v1 with
      | const b1 =>
        cases b1
        · cases v2 with
          | const b2 => cases b2 <;> exact ⟨le_refl _, trivial⟩
          | wire i2 => exact ⟨le_refl _, hmem (.wire i2) (by simp)⟩
        · exact ⟨le_refl _, trivial⟩
      | wire i1 =>
        cases v2 with
        | const b2 =>
          cases b2
          · exact ⟨le_refl _, hmem (.wire i1) (by simp)⟩
          · exact ⟨le_refl _, trivial⟩
        | wire i2 =>
          refine ⟨by simp, ?_⟩
          simp [wvOk]
    · exact ⟨le_refl _, trivial⟩
  · generalize hvs : g.inputs.map (fun i => env.getD i (.const false)) = vs
    rcases vs with _ | ⟨v1, rest⟩
    · exact ⟨le_refl _, trivial⟩
    · cases v1 with
      | const b1 => exact ⟨le_refl _, trivial⟩
      | wire i1 =>
        refine ⟨by simp, ?_⟩
        simp [wvOk]
  · exact ⟨le_refl _, trivial⟩
  · exact ⟨le_refl _, trivial⟩

lemma simpGate_correct (n : ℕ) (x : Fin n → Bool) (acc : List Gate) (env : List WireVal)
    (oldW : List Bool) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (henv : ∀ i, wvOk (n + acc.length) (env.getD i (.const false)))
    (hinv : ∀ i, evalWV (acc.foldl step (List.ofFn x)) (env.getD i (.const false)) = oldW.getD i false) :
    let r := simpGate n acc env g
    (∀ i, evalWV (r.1.foldl step (List.ofFn x)) (env.getD i (.const false)) = oldW.getD i false) ∧
    evalWV (r.1.foldl step (List.ofFn x)) r.2 =
      g.op.eval (g.inputs.map fun i => oldW.getD i false) := by
  let newW := acc.foldl step (List.ofFn x)
  have hnewW_len : newW.length = n + acc.length := by simp [newW, foldl_length]
  have hkeep : ∀ (ng : Gate) (i : ℕ),
      evalWV ((acc ++ [ng]).foldl step (List.ofFn x)) (env.getD i (.const false)) = oldW.getD i false := by
    intro ng i
    have hfold : (acc ++ [ng]).foldl step (List.ofFn x) = step newW ng := by
      simp [newW, List.foldl_append]
    rw [hfold]
    have hok := henv i
    have hi := hinv i
    cases hv : env.getD i (.const false) with
    | const b =>
      rw [hv] at hi
      exact hi
    | wire idx =>
      rw [hv] at hok hi
      simp only [wvOk] at hok
      simp only [evalWV] at hi ⊢
      rw [step, getD_append_lt newW _ idx false (by omega)]
      exact hi
  have hsnoc : ∀ (ng : Gate),
      evalWV ((acc ++ [ng]).foldl step (List.ofFn x)) (.wire (n + acc.length)) =
        ng.op.eval (ng.inputs.map fun k => newW.getD k false) := by
    intro ng
    have hfold : (acc ++ [ng]).foldl step (List.ofFn x) = step newW ng := by
      simp [newW, List.foldl_append]
    rw [hfold, evalWV, step, ← hnewW_len, getD_snoc_eq]
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  obtain ⟨hop, hlen⟩ := hg
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · refine ⟨hinv, ?_⟩; simp [simpGate, evalWV, GateOp.eval]
    · refine ⟨hinv, ?_⟩
      simp only [simpGate, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
        id_eq, Bool.and_true]
      exact hinv a
    · simp only [simpGate, List.map_cons, List.map_nil]
      have ha : evalWV newW (env.getD a (.const false)) = oldW.getD a false := hinv a
      have hb : evalWV newW (env.getD b (.const false)) = oldW.getD b false := hinv b
      cases hva : env.getD a (.const false) with
      | const ba =>
        rw [hva] at ha; dsimp only [evalWV] at ha
        cases ba
        · refine ⟨hinv, ?_⟩
          simp only [evalWV, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq]
          rw [← ha]; simp
        · cases hvb : env.getD b (.const false) with
          | const bb =>
            rw [hvb] at hb; dsimp only [evalWV] at hb
            cases bb
            · refine ⟨hinv, ?_⟩
              simp only [evalWV, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq]
              rw [← ha, ← hb]; simp
            · refine ⟨hinv, ?_⟩
              simp only [evalWV, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq]
              rw [← ha, ← hb]; simp
          | wire ib =>
            rw [hvb] at hb; dsimp only [evalWV] at hb
            refine ⟨hinv, ?_⟩
            change newW.getD ib false = _
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq]
            rw [← ha, ← hb]; simp
      | wire ia =>
        rw [hva] at ha; dsimp only [evalWV] at ha
        cases hvb : env.getD b (.const false) with
        | const bb =>
          rw [hvb] at hb; dsimp only [evalWV] at hb
          cases bb
          · refine ⟨hinv, ?_⟩
            simp only [evalWV, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq]
            rw [← hb]; simp
          · refine ⟨hinv, ?_⟩
            change newW.getD ia false = _
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq]
            rw [← ha, ← hb]; simp
        | wire ib =>
          rw [hvb] at hb; dsimp only [evalWV] at hb
          refine ⟨hkeep _, ?_⟩
          rw [hsnoc]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq]
          rw [ha, hb]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · refine ⟨hinv, ?_⟩; simp [simpGate, evalWV, GateOp.eval]
    · refine ⟨hinv, ?_⟩
      simp only [simpGate, List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
        id_eq, Bool.or_false]
      exact hinv a
    · simp only [simpGate, List.map_cons, List.map_nil]
      have ha : evalWV newW (env.getD a (.const false)) = oldW.getD a false := hinv a
      have hb : evalWV newW (env.getD b (.const false)) = oldW.getD b false := hinv b
      cases hva : env.getD a (.const false) with
      | const ba =>
        rw [hva] at ha; dsimp only [evalWV] at ha
        cases ba
        · cases hvb : env.getD b (.const false) with
          | const bb =>
            rw [hvb] at hb; dsimp only [evalWV] at hb
            cases bb
            · refine ⟨hinv, ?_⟩
              simp only [evalWV, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq]
              rw [← ha, ← hb]; simp
            · refine ⟨hinv, ?_⟩
              simp only [evalWV, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq]
              rw [← ha, ← hb]; simp
          | wire ib =>
            rw [hvb] at hb; dsimp only [evalWV] at hb
            refine ⟨hinv, ?_⟩
            change newW.getD ib false = _
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq]
            rw [← ha, ← hb]; simp
        · refine ⟨hinv, ?_⟩
          simp only [evalWV, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq]
          rw [← ha]; simp
      | wire ia =>
        rw [hva] at ha; dsimp only [evalWV] at ha
        cases hvb : env.getD b (.const false) with
        | const bb =>
          rw [hvb] at hb; dsimp only [evalWV] at hb
          cases bb
          · refine ⟨hinv, ?_⟩
            change newW.getD ia false = _
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq]
            rw [← ha, ← hb]; simp
          · refine ⟨hinv, ?_⟩
            simp only [evalWV, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq]
            rw [← hb]; simp
        | wire ib =>
          rw [hvb] at hb; dsimp only [evalWV] at hb
          refine ⟨hkeep _, ?_⟩
          rw [hsnoc]
          simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq]
          rw [ha, hb]
    · simp at hlen
  · rcases ins with _ | ⟨a, rest⟩
    · refine ⟨hinv, ?_⟩; simp [simpGate, evalWV, GateOp.eval]
    · simp only [simpGate, List.map_cons]
      have ha : evalWV newW (env.getD a (.const false)) = oldW.getD a false := hinv a
      cases hva : env.getD a (.const false) with
      | const ba =>
        rw [hva] at ha; dsimp only [evalWV] at ha
        refine ⟨hinv, ?_⟩
        simp only [evalWV, GateOp.eval, List.map_cons, List.headD_cons]
        rw [← ha]
      | wire ia =>
        rw [hva] at ha; dsimp only [evalWV] at ha
        refine ⟨hkeep _, ?_⟩
        rw [hsnoc]
        simp only [GateOp.eval, List.map_cons, List.headD_cons]
        rw [ha]

lemma simpLoop_correct (n : ℕ) (x : Fin n → Bool) (gs : List Gate)
    (acc : List Gate) (env : List WireVal) (oldW : List Bool)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hlen : env.length = oldW.length)
    (henv : ∀ i, wvOk (n + acc.length) (env.getD i (.const false)))
    (hinv : ∀ i, evalWV (acc.foldl step (List.ofFn x)) (env.getD i (.const false)) = oldW.getD i false) :
    let res := simpLoop n gs (acc, env)
    ∀ i, evalWV (res.1.foldl step (List.ofFn x)) (res.2.getD i (.const false)) =
         (gs.foldl step oldW).getD i false := by
  induction gs generalizing acc env oldW with
  | nil => exact hinv
  | cons g gs ih =>
    simp only [simpLoop, List.foldl_cons]
    have hg := hfan g (by simp)
    have hgs' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hfan g' (by simp [hg'])
    have hok := simpGate_ok n acc env g henv
    have hcorr := simpGate_correct n x acc env oldW g hg henv hinv
    let r := simpGate n acc env g
    let env' := env ++ [r.2]
    apply ih r.1 env' (step oldW g) hgs'
    · simp [env', step, hlen]
    · intro i
      by_cases hi : i < env.length
      · rw [getD_append_lt env [r.2] i (.const false) hi]
        have h1 := henv i
        cases hv : env.getD i (.const false) with
        | const _ => trivial
        | wire idx =>
          rw [hv] at h1
          simp only [wvOk] at h1 ⊢
          have hle : acc.length ≤ r.1.length := hok.1
          omega
      · by_cases heq : i = env.length
        · subst heq; rw [getD_snoc_eq]; exact hok.2
        · rw [List.getD_eq_default env' _ (by simp [env']; omega)]; trivial
    · intro i
      by_cases hi : i < env.length
      · rw [getD_append_lt env [r.2] i (.const false) hi,
            step, getD_append_lt oldW _ i false (hlen ▸ hi)]
        exact hcorr.1 i
      · by_cases heq : i = env.length
        · subst heq
          rw [getD_snoc_eq, step, hlen, getD_snoc_eq]
          exact hcorr.2
        · rw [List.getD_eq_default env' _ (by simp [env']; omega),
              List.getD_eq_default (step oldW g) _ (by simp [step]; omega)]
          rfl

lemma simpGate_full_indep (n : ℕ) (a : Fin n) (acc : List Gate) (env : List WireVal) (g : Gate)
    (u v : List Bool) (hu : u.length = env.length) (hv : v.length = env.length)
    (heq : ∀ i, i ≠ a.val → u.getD i false = v.getD i false)
    (ha : env.getD a.val (.const false) = .const false)
    (hfull : (simpGate n acc env g).1.length = acc.length + 1) :
    g.op.eval (g.inputs.map fun i => u.getD i false) =
      g.op.eval (g.inputs.map fun i => v.getD i false) := by
  have hne : ∀ (i : ℕ) (k : ℕ), env.getD i (.const false) = .wire k → i ≠ a.val := by
    intro i k hik hia
    rw [hia, ha] at hik
    cases hik
  unfold simpGate at hfull
  cases hop : g.op <;> rw [hop] at hfull
  · simp only at hfull
    rcases hins : g.inputs with _ | ⟨i1, _ | ⟨i2, _ | ⟨i3, rest⟩⟩⟩
    · simp [hins] at hfull
    · simp [hins] at hfull
    · simp only [hins, List.map_cons, List.map_nil] at hfull
      cases hv1 : env.getD i1 (.const false) <;> cases hv2 : env.getD i2 (.const false)
      · rw [hv1, hv2] at hfull; cases ‹Bool› <;> cases ‹Bool› <;> simp at hfull
      · rw [hv1, hv2] at hfull; cases ‹Bool› <;> simp at hfull
      · rw [hv1, hv2] at hfull; cases ‹Bool› <;> simp at hfull
      · simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq]
        rw [heq i1 (hne i1 _ hv1), heq i2 (hne i2 _ hv2)]
    · simp [hins] at hfull
  · simp only at hfull
    rcases hins : g.inputs with _ | ⟨i1, _ | ⟨i2, _ | ⟨i3, rest⟩⟩⟩
    · simp [hins] at hfull
    · simp [hins] at hfull
    · simp only [hins, List.map_cons, List.map_nil] at hfull
      cases hv1 : env.getD i1 (.const false) <;> cases hv2 : env.getD i2 (.const false)
      · rw [hv1, hv2] at hfull; cases ‹Bool› <;> cases ‹Bool› <;> simp at hfull
      · rw [hv1, hv2] at hfull; cases ‹Bool› <;> simp at hfull
      · rw [hv1, hv2] at hfull; cases ‹Bool› <;> simp at hfull
      · simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq]
        rw [heq i1 (hne i1 _ hv1), heq i2 (hne i2 _ hv2)]
    · simp [hins] at hfull
  · simp only at hfull
    rcases hins : g.inputs with _ | ⟨i1, rest⟩
    · simp [hins] at hfull
    · simp only [hins, List.map_cons] at hfull
      cases hv1 : env.getD i1 (.const false)
      · rw [hv1] at hfull; simp at hfull
      · simp only [GateOp.eval, List.map_cons, List.headD_cons]
        rw [heq i1 (hne i1 _ hv1)]
  · simp at hfull
  · simp at hfull

lemma simpLoop_full_indep (n : ℕ) (a : Fin n) (gs : List Gate)
    (acc : List Gate) (env : List WireVal) (u v : List Bool)
    (ha_lt : a.val < env.length)
    (ha : env.getD a.val (.const false) = .const false)
    (hu : u.length = env.length) (hv : v.length = env.length)
    (heq : ∀ i, i ≠ a.val → u.getD i false = v.getD i false)
    (hfull : (simpLoop n gs (acc, env)).1.length = acc.length + gs.length) :
    ∀ i, i ≠ a.val → (gs.foldl step u).getD i false = (gs.foldl step v).getD i false := by
  induction gs generalizing acc env u v with
  | nil => exact heq
  | cons g gs ih =>
    simp only [simpLoop, List.foldl_cons, List.length_cons] at hfull ⊢
    have hstep_le := simpGate_len_le n acc env g
    have htail_le := simpLoop_len_le n gs (simpGate n acc env g).1 (env ++ [(simpGate n acc env g).2])
    simp only [simpLoop] at htail_le
    have hstep_eq : (simpGate n acc env g).1.length = acc.length + 1 := by omega
    have htail_eq : (simpLoop n gs ((simpGate n acc env g).1, env ++ [(simpGate n acc env g).2])).1.length =
        (simpGate n acc env g).1.length + gs.length := by
      simp only [simpLoop]; omega
    have hgv := simpGate_full_indep n a acc env g u v hu hv heq ha hstep_eq
    apply ih (simpGate n acc env g).1 (env ++ [(simpGate n acc env g).2]) (step u g) (step v g)
    · simp; omega
    · rw [getD_append_lt env _ a.val (.const false) ha_lt, ha]
    · simp [step, hu]
    · simp [step, hv]
    · intro i hi
      by_cases hilt : i < env.length
      · rw [step, getD_append_lt u _ i false (hu ▸ hilt),
            step, getD_append_lt v _ i false (hv ▸ hilt)]
        exact heq i hi
      · by_cases hieq : i = env.length
        · subst hieq
          have huv : u.length = v.length := hu.trans hv.symm
          rw [step, ← hu, getD_snoc_eq, step, huv, getD_snoc_eq]
          exact hgv
        · rw [List.getD_eq_default (step u g) _ (by simp [step, hu]; omega),
              List.getD_eq_default (step v g) _ (by simp [step, hv]; omega)]
    · exact htail_eq

lemma graphFun_zero {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n)) :
    graphFun G A (fun _ => false) = false := by
  simp [graphFun]

lemma elim_one_isolated {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n)) (a : Fin n) (haA : a ∈ A)
    (hiso : ∀ u w, G.Adj u w → u ∉ A)
    (hedge : ∃ u w, G.Adj u w)
    (C : Circuit) (hfan : FanInTwo C)
    (hC : ∀ x, C.eval (List.ofFn x) = graphFun G A x) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + 1 ≤ C.size ∧
      ∀ x, D.eval (List.ofFn x) = graphFun G (A.erase a) x := by
  let env0 : List WireVal := (List.finRange n).map (fun i => if i = a then .const false else .wire i.val)
  have henv0_len : env0.length = n := by simp [env0]
  have henv0_get : ∀ i : ℕ, env0.getD i (.const false) =
      if h : i < n then if (⟨i, h⟩ : Fin n) = a then .const false else .wire i else .const false := by
    intro i
    by_cases hi : i < n
    · simp only [hi, ↓reduceDIte]
      rw [List.getD_eq_getElem env0 _ (by simp [env0]; exact hi)]
      simp only [env0, List.getElem_map, List.getElem_finRange, Fin.cast_mk]
    · simp only [hi, ↓reduceDIte]
      exact List.getD_eq_default _ _ (by simp [env0]; omega)
  have henv0_ok : ∀ i, wvOk (n + ([] : List Gate).length) (env0.getD i (.const false)) := by
    intro i
    rw [henv0_get i]
    split_ifs with h1 h2
    · trivial
    · simp [wvOk, h1]
    · trivial
  have hupdate_fun : ∀ x, graphFun G A (Function.update x a false) = graphFun G (A.erase a) x := by
    intro x
    apply Bool.eq_iff_iff.mpr
    simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq, Finset.mem_erase]
    constructor
    · rintro (⟨b, hbA, hxb⟩ | ⟨u, w, hadj, hxu, hxw⟩)
      · left
        have hba : b ≠ a := by intro e; subst e; simp at hxb
        exact ⟨b, ⟨hba, hbA⟩, by simpa [Function.update, hba] using hxb⟩
      · right
        have hua : u ≠ a := fun e => hiso u w hadj (e ▸ haA)
        have hwa : w ≠ a := fun e => hiso w u hadj.symm (e ▸ haA)
        exact ⟨u, w, hadj, by simpa [Function.update, hua] using hxu, by simpa [Function.update, hwa] using hxw⟩
    · rintro (⟨b, ⟨hba, hbA⟩, hxb⟩ | ⟨u, w, hadj, hxu, hxw⟩)
      · left; exact ⟨b, hbA, by simpa [Function.update, hba] using hxb⟩
      · right
        have hua : u ≠ a := fun e => hiso u w hadj (e ▸ haA)
        have hwa : w ≠ a := fun e => hiso w u hadj.symm (e ▸ haA)
        exact ⟨u, w, hadj, by simpa [Function.update, hua] using hxu, by simpa [Function.update, hwa] using hxw⟩
  let res := simpLoop n C.gates ([], env0)
  have hcorr (x : Fin n → Bool) :
      evalWV (res.1.foldl step (List.ofFn x)) (res.2.getD C.output (.const false)) =
        graphFun G (A.erase a) x := by
    rw [← hupdate_fun x, ← hC (Function.update x a false)]
    exact simpLoop_correct n x C.gates [] env0 (List.ofFn (Function.update x a false)) hfan
      (by simp [env0]) henv0_ok (by
        intro i
        rw [List.foldl_nil, henv0_get i]
        by_cases hi : i < n
        · simp only [hi, ↓reduceDIte]
          split_ifs with hia
          · simp only [evalWV]
            rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn, hia]
            simp
          · simp only [evalWV]
            rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega),
                List.getElem_ofFn, List.getElem_ofFn, Function.update_of_ne hia]
        · simp only [hi, ↓reduceDIte, evalWV]
          rw [List.getD_eq_default _ _ (by simp; omega)]) C.output
  have hle : res.1.length ≤ C.gates.length := by
    simpa using simpLoop_len_le n C.gates [] env0
  have hlt : res.1.length < C.gates.length := by
    by_contra hnot
    have hfull : res.1.length = ([] : List Gate).length + C.gates.length := by simp; omega
    have ha_env0 : env0.getD a.val (.const false) = .const false := by
      rw [henv0_get a.val]; simp [a.isLt]
    by_cases hout : C.output = a.val
    · obtain ⟨u, w, hadj⟩ := hedge
      let x : Fin n → Bool := fun i => decide (i = u ∨ i = w)
      have h1 : C.eval (List.ofFn x) = true := by
        rw [hC x]
        simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq]
        right; exact ⟨u, w, hadj, by simp [x], by simp [x]⟩
      have h2 : C.eval (List.ofFn x) = x a := by
        simp only [Circuit.eval, Circuit.wires, hout]
        have hk := keepInput C.gates (List.ofFn x) a.val (by simp)
        change (C.gates.foldl step (List.ofFn x)).getD a.val false = x a
        rw [hk, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      have h3 : x a = false := by
        have hua : a ≠ u := fun e => hiso u w hadj (e ▸ haA)
        have hwa : a ≠ w := fun e => hiso w u hadj.symm (e ▸ haA)
        simp [x, hua, hwa]
      rw [h2, h3] at h1; cases h1
    · let x : Fin n → Bool := fun i => decide (i = a)
      let y : Fin n → Bool := fun _ => false
      have heq0 : ∀ i, i ≠ a.val → (List.ofFn x).getD i false = (List.ofFn y).getD i false := by
        intro i hi
        by_cases hilt : i < n
        · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega),
              List.getElem_ofFn, List.getElem_ofFn]
          have hne : (⟨i, hilt⟩ : Fin n) ≠ a := fun e => hi (congrArg Fin.val e)
          simp [x, y, hne]
        · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
      have hind := simpLoop_full_indep n a C.gates [] env0 (List.ofFn x) (List.ofFn y)
        (by rw [henv0_len]; exact a.isLt) ha_env0 (by simp [henv0_len]) (by simp [henv0_len])
        heq0 hfull C.output hout
      change C.eval (List.ofFn x) = C.eval (List.ofFn y) at hind
      rw [hC x, hC y, graphFun_zero] at hind
      have hxT : graphFun G A x = true := by
        simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq]
        left; exact ⟨a, haA, by simp [x]⟩
      rw [hxT] at hind; cases hind
  let outIdx : ℕ := match res.2.getD C.output (.const false) with
    | .const _ => n + res.1.length
    | .wire idx => idx
  refine ⟨{ gates := res.1, output := outIdx }, simpLoop_fan n C.gates [] env0 (by simp), by simp [Circuit.size]; omega, ?_⟩
  intro x
  have hcx := hcorr x
  cases hrv : res.2.getD C.output (.const false) with
  | const b =>
    cases b
    · simp only [outIdx, hrv, Circuit.eval, Circuit.wires]
      rw [hrv] at hcx
      simp only [evalWV] at hcx
      rw [← hcx]
      change (res.1.foldl step (List.ofFn x)).getD (n + res.1.length) false = false
      exact List.getD_eq_default _ _ (by rw [foldl_length]; simp)
    · have h0 := hcorr (fun _ => false)
      rw [hrv, evalWV, graphFun_zero] at h0
      cases h0
  | wire idx =>
    simp only [outIdx, hrv, Circuit.eval, Circuit.wires]
    rw [hrv] at hcx
    exact hcx

lemma elim_all_isolated {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A : Finset (Fin n))
    (hiso : ∀ u w, G.Adj u w → u ∉ A)
    (hedge : ∃ u w, G.Adj u w)
    (C : Circuit) (hfan : FanInTwo C)
    (hC : ∀ x, C.eval (List.ofFn x) = graphFun G A x) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + A.card ≤ C.size ∧
      ∀ x, D.eval (List.ofFn x) = graphFun G ∅ x := by
  induction A using Finset.induction_on generalizing C with
  | empty => exact ⟨C, hfan, by simp, hC⟩
  | @insert a A haA ih =>
    have hisoA : ∀ u w, G.Adj u w → u ∉ A := fun u w h hmem => hiso u w h (Finset.mem_insert_of_mem hmem)
    obtain ⟨C1, hfan1, hsz1, hC1⟩ := elim_one_isolated G (insert a A) a (Finset.mem_insert_self a A)
      hiso hedge C hfan hC
    have herase : (insert a A).erase a = A := Finset.erase_insert haA
    rw [herase] at hC1
    obtain ⟨D, hfanD, hszD, hD⟩ := ih hisoA C1 hfan1 hC1
    refine ⟨D, hfanD, ?_, hD⟩
    rw [Finset.card_insert_of_notMem haA]
    omega

def appendOrs (n : ℕ) (L : List (Fin n)) (gs : List Gate) (out : ℕ) : List Gate × ℕ :=
  L.foldl (fun p a => (p.1 ++ [{ op := .or, inputs := [p.2, a.val] }], n + p.1.length)) (gs, out)

lemma appendOrs_size (n : ℕ) (L : List (Fin n)) (gs : List Gate) (out : ℕ) :
    (appendOrs n L gs out).1.length = gs.length + L.length := by
  induction L generalizing gs out with
  | nil => simp [appendOrs]
  | cons a L ih =>
    simp only [appendOrs, List.foldl_cons, List.length_cons]
    have h1 := ih (gs ++ [{ op := .or, inputs := [out, a.val] }]) (n + gs.length)
    simp only [appendOrs, List.length_append, List.length_singleton] at h1
    omega

lemma appendOrs_fan (n : ℕ) (L : List (Fin n)) (gs : List Gate) (out : ℕ)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ (appendOrs n L gs out).1,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction L generalizing gs out with
  | nil => exact hgs
  | cons a L ih =>
    simp only [appendOrs, List.foldl_cons]
    apply ih
    intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with h | rfl
    · exact hgs g h
    · simp

lemma appendOrs_eval (n : ℕ) (x : Fin n → Bool) (L : List (Fin n)) (gs : List Gate) (out : ℕ)
    (hout : out < n + gs.length ∨ n + gs.length + L.length < out) :
    let r := appendOrs n L gs out
    (r.1.foldl step (List.ofFn x)).getD r.2 false =
      ((gs.foldl step (List.ofFn x)).getD out false || decide (∃ a ∈ L, x a = true)) := by
  induction L generalizing gs out with
  | nil => simp [appendOrs]
  | cons a L ih =>
    simp only [appendOrs, List.foldl_cons, List.length_cons] at hout ⊢
    let g1 : Gate := { op := .or, inputs := [out, a.val] }
    let gs1 := gs ++ [g1]
    have hout1 : n + gs.length < n + gs1.length ∨ n + gs1.length + L.length < n + gs.length := by
      left; simp [gs1]
    have h1 := ih gs1 (n + gs.length) hout1
    simp only [appendOrs] at h1
    rw [h1]
    have hfold : gs1.foldl step (List.ofFn x) = step (gs.foldl step (List.ofFn x)) g1 := by
      simp [gs1, List.foldl_append]
    rw [hfold]
    let w := gs.foldl step (List.ofFn x)
    have hwlen : w.length = n + gs.length := by simp [w, foldl_length]
    have hnew : (step w g1).getD (n + gs.length) false = (w.getD out false || x a) := by
      rw [step, ← hwlen, getD_snoc_eq]
      have ha : w.getD a.val false = x a := by
        rw [keepInput gs (List.ofFn x) a.val (by simp),
            List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
      simp only [g1, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        id_eq, Bool.or_false, ha]
    rw [hnew, Bool.or_assoc]
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro (h | ⟨b, hb, hxb⟩)
      · exact ⟨a, Or.inl rfl, h⟩
      · exact ⟨b, Or.inr hb, hxb⟩
    · rintro ⟨b, rfl | hb, hxb⟩
      · exact Or.inl hxb
      · exact Or.inr ⟨b, hb, hxb⟩

end PEqualNP.Outside.L_meta_4907

theorem PEqualNP.Outside.L_meta_4907 :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 x6 : ℕ),
      have x7 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅;
      have x8 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;
      (∀ (x9 x10 : Fin x1), x2.Adj x9 x10 → x9 ∉ x4) →
      (∃ (x10 : Fin x1) (x11 : Fin x1), x2.Adj x10 x11) →
      PEqualNP.MetaComplexity.HasCircuitSize x1 x8 x5 →
      (∀ (x12 : ℕ), PEqualNP.MetaComplexity.HasCircuitSize x1 x7 x12 → x6 ≤ x12) →
      (∃ x13 ∉ x4, ∃ (x14 : ℕ), x14 + (4 : ℕ) ≤ x6 ∧
        PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x15 : Fin x1 → Bool) => x7 (Function.update x15 x13 Bool.false)) x14) →
      ∃ x14 ∉ x4, ∃ (x15 : ℕ), x15 + (4 : ℕ) ≤ x5 ∧
        PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x16 : Fin x1 → Bool) => x8 (Function.update x16 x14 Bool.false)) x15 := by
  intro n G _ A s s0
  dsimp only
  intro hiso hedge ⟨C, hfanC, hszC, hC⟩ hmin ⟨v, hvA, t, ht, ⟨D0, hfanD0, hszD0, hD0⟩⟩
  obtain ⟨C0, hfanC0, hszC0, hC0⟩ :=
    PEqualNP.Outside.L_meta_4907.elim_all_isolated G A hiso hedge C hfanC hC
  have hs0_le : s0 ≤ C0.size := hmin C0.size ⟨C0, hfanC0, le_refl _, hC0⟩
  let L := A.toList
  have hLlen : L.length = A.card := Finset.length_toList A
  let initOut := if D0.output < n + D0.gates.length then D0.output else n + D0.gates.length + L.length + 1
  let res := PEqualNP.Outside.L_meta_4907.appendOrs n L D0.gates initOut
  let D : PEqualNP.CircuitLowerBounds.Circuit := { gates := res.1, output := res.2 }
  refine ⟨v, hvA, t + A.card, by omega, ⟨D, ?_, ?_, ?_⟩⟩
  · exact PEqualNP.Outside.L_meta_4907.appendOrs_fan n L D0.gates initOut hfanD0
  · change res.1.length ≤ t + A.card
    rw [PEqualNP.Outside.L_meta_4907.appendOrs_size, hLlen]
    change D0.size + A.card ≤ t + A.card
    omega
  · intro x
    have hout : initOut < n + D0.gates.length ∨ n + D0.gates.length + L.length < initOut := by
      dsimp only [initOut]
      split_ifs with h
      · exact Or.inl h
      · right; omega
    have hev := PEqualNP.Outside.L_meta_4907.appendOrs_eval n x L D0.gates initOut hout
    change (res.1.foldl PEqualNP.Outside.L_meta_4907.step (List.ofFn x)).getD res.2 false = _
    rw [hev]
    have hinit : (D0.gates.foldl PEqualNP.Outside.L_meta_4907.step (List.ofFn x)).getD initOut false =
        D0.eval (List.ofFn x) := by
      dsimp only [initOut]
      split_ifs with h
      · rfl
      · have h1 : (D0.gates.foldl PEqualNP.Outside.L_meta_4907.step (List.ofFn x)).getD
            (n + D0.gates.length + L.length + 1) false = false :=
          List.getD_eq_default _ _ (by rw [PEqualNP.Outside.L_meta_4907.foldl_length]; simp; omega)
        have h2 : D0.eval (List.ofFn x) = false := by
          change (D0.gates.foldl PEqualNP.Outside.L_meta_4907.step (List.ofFn x)).getD D0.output false = false
          exact List.getD_eq_default _ _ (by rw [PEqualNP.Outside.L_meta_4907.foldl_length]; simp; omega)
        rw [h1, h2]
    rw [hinit, hD0 x]
    apply Bool.eq_iff_iff.mpr
    simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Bool.or_eq_true, decide_eq_true_eq,
      Finset.notMem_empty, false_and, exists_false, false_or, L, Finset.mem_toList]
    constructor
    · rintro (⟨u, w, hadj, hxu, hxw⟩ | ⟨a, haA, hxa⟩)
      · exact Or.inr ⟨u, w, hadj, hxu, hxw⟩
      · left
        have hav : a ≠ v := fun e => hvA (e ▸ haA)
        exact ⟨a, haA, by simpa [Function.update, hav] using hxa⟩
    · rintro (⟨a, haA, hxa⟩ | ⟨u, w, hadj, hxu, hxw⟩)
      · right
        have hav : a ≠ v := fun e => hvA (e ▸ haA)
        exact ⟨a, haA, by simpa [Function.update, hav] using hxa⟩
      · exact Or.inl ⟨u, w, hadj, hxu, hxw⟩
