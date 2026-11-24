import Mathlib.Data.List.OfFn
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4793

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

lemma getD_append_lt {α : Type} (l r : List α) (i : ℕ) (d : α) (hi : i < l.length) :
    (l ++ r).getD i d = l.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_snoc_eq {α : Type} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  rw [List.getD_append_right _ _ _ _ (le_refl _)]
  simp

def isOrAt (x4 : ℕ) (g : Gate) : Bool :=
  g.op.eval [true, false] && g.inputs.contains x4

def elimStep (n x4 fw : ℕ) (st : List Gate × List ℕ) (g : Gate) : List Gate × List ℕ :=
  let acc := st.1
  let env := st.2
  if isOrAt x4 g then
    match g.inputs.filter (fun i => i != x4) with
    | [] => (acc, env ++ [fw])
    | b :: _ => (acc, env ++ [env.getD b fw])
  else
    let g' : Gate := { op := g.op, inputs := g.inputs.map (fun i => env.getD i fw) }
    (acc ++ [g'], env ++ [n + acc.length])

def elimLoop (n x4 fw : ℕ) (gs : List Gate) (st : List Gate × List ℕ) : List Gate × List ℕ :=
  gs.foldl (elimStep n x4 fw) st

lemma elimLoop_size (n x4 fw : ℕ) (gs : List Gate) (acc : List Gate) (env : List ℕ) :
    (elimLoop n x4 fw gs (acc, env)).1.length + (gs.filter (isOrAt x4)).length =
      acc.length + gs.length := by
  induction gs generalizing acc env with
  | nil => simp [elimLoop]
  | cons g gs ih =>
    simp only [elimLoop, List.foldl_cons, List.filter_cons, List.length_cons]
    unfold elimStep
    cases h : isOrAt x4 g
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have h1 := ih (acc ++ [⟨g.op, g.inputs.map (fun i => env.getD i fw)⟩]) (env ++ [n + acc.length])
      simp only [elimLoop, List.length_append, List.length_singleton] at h1
      change (gs.foldl (elimStep n x4 fw) _).1.length + _ = _
      omega
    · simp only [↓reduceIte, List.length_cons]
      cases hf : g.inputs.filter (fun i => i != x4) with
      | nil =>
        have h1 := ih acc (env ++ [fw])
        simp only [elimLoop] at h1
        change (gs.foldl (elimStep n x4 fw) (acc, env ++ [fw])).1.length + _ = _
        omega
      | cons b bs =>
        have h1 := ih acc (env ++ [env.getD b fw])
        simp only [elimLoop] at h1
        change (gs.foldl (elimStep n x4 fw) (acc, env ++ [env.getD b fw])).1.length + _ = _
        omega

lemma elimLoop_fan (n x4 fw : ℕ) (gs : List Gate) (acc : List Gate) (env : List ℕ)
    (hacc : ∀ g ∈ acc, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ (elimLoop n x4 fw gs (acc, env)).1,
      g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction gs generalizing acc env with
  | nil => exact hacc
  | cons g gs ih =>
    simp only [elimLoop, List.foldl_cons]
    have hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
      hgs g (by simp)
    have hgs' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hgs g' (by simp [hg'])
    unfold elimStep
    cases h : isOrAt x4 g
    · simp only [Bool.false_eq_true, ↓reduceIte]
      apply ih _ _ _ hgs'
      intro g' hg'
      simp only [List.mem_append, List.mem_singleton] at hg'
      rcases hg' with hg' | rfl
      · exact hacc g' hg'
      · simpa using hg
    · simp only [↓reduceIte]
      cases g.inputs.filter (fun i => i != x4) with
      | nil => exact ih acc (env ++ [fw]) hacc hgs'
      | cons b bs => exact ih acc (env ++ [env.getD b fw]) hacc hgs'

lemma eval_or_at_false (w : List Bool) (x4 : ℕ) (g : Gate)
    (hfan : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hor : isOrAt x4 g = true)
    (hw4 : w.getD x4 false = false) :
    g.op.eval (g.inputs.map fun i => w.getD i false) =
      match g.inputs.filter (fun i => i != x4) with
      | [] => false
      | b :: _ => w.getD b false := by
  simp only [isOrAt, Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hor
  obtain ⟨hopT, hmem⟩ := hor
  have hop : g.op = GateOp.or := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hfan
    rcases hfan.1 with h | h | h
    · rw [h] at hopT; simp [GateOp.eval] at hopT
    · exact h
    · rw [h] at hopT; simp [GateOp.eval] at hopT
  rw [hop]
  rcases g with ⟨op, ins⟩
  simp only at hop hfan hmem ⊢
  simp only [List.getD_eq_getElem?_getD] at hw4 ⊢
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp at hmem
  · simp only [List.mem_singleton] at hmem
    rw [← hmem]
    simp [GateOp.eval, hw4]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    by_cases ha : a = x4
    · rw [ha]
      by_cases hb : b = x4
      · rw [hb]
        simp [GateOp.eval, hw4]
      · simp [GateOp.eval, hw4, hb]
    · have hb : b = x4 := by
        rcases hmem with h1 | h2
        · exact (ha h1.symm).elim
        · exact h2.symm
      rw [hb]
      simp [GateOp.eval, hw4, ha]
  · simp at hfan

lemma elimLoop_correct (n x4 fw : ℕ) (x : Fin n → Bool)
    (gs : List Gate) (acc : List Gate) (env : List ℕ) (oldW : List Bool)
    (hfw : n + acc.length + gs.length < fw)
    (hfan : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hx4 : x4 < oldW.length)
    (hw4 : oldW.getD x4 false = false)
    (hlen : env.length = oldW.length)
    (hbnd : ∀ i, env.getD i fw < n + acc.length ∨ env.getD i fw = fw)
    (hinv : ∀ i, (acc.foldl step (List.ofFn x)).getD (env.getD i fw) false = oldW.getD i false) :
    let res := elimLoop n x4 fw gs (acc, env)
    ∀ i, (res.1.foldl step (List.ofFn x)).getD (res.2.getD i fw) false =
         (gs.foldl step oldW).getD i false := by
  induction gs generalizing acc env oldW with
  | nil => exact hinv
  | cons g gs ih =>
    simp only [List.length_cons] at hfw
    simp only [elimLoop, List.foldl_cons]
    have hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 :=
      hfan g (by simp)
    have hgs' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hfan g' (by simp [hg'])
    have hstep_len : (step oldW g).length = oldW.length + 1 := by simp [step]
    have hx4' : x4 < (step oldW g).length := by omega
    have hw4' : (step oldW g).getD x4 false = false := by
      rw [step, getD_append_lt _ _ _ _ hx4, hw4]
    let newW := acc.foldl step (List.ofFn x)
    have hnewW_len : newW.length = n + acc.length := by
      simp [newW, foldl_length]
    unfold elimStep
    cases hor : isOrAt x4 g
    · simp only [Bool.false_eq_true, ↓reduceIte]
      let g' : Gate := { op := g.op, inputs := g.inputs.map (fun i => env.getD i fw) }
      let acc' := acc ++ [g']
      let env' := env ++ [n + acc.length]
      have heval : g'.op.eval (g'.inputs.map fun i => newW.getD i false) =
          g.op.eval (g.inputs.map fun i => oldW.getD i false) := by
        simp only [g', List.map_map]
        congr 1
        apply List.map_congr_left
        intro k _
        exact hinv k
      have hfold : acc'.foldl step (List.ofFn x) = step newW g' := by
        simp [acc', newW, List.foldl_append]
      apply ih acc' env' (step oldW g)
      · simp [acc']; omega
      · exact hgs'
      · exact hx4'
      · exact hw4'
      · simp [env', hstep_len, hlen]
      · intro i
        by_cases hi : i < env.length
        · rw [getD_append_lt env [n + acc.length] i fw hi]
          rcases hbnd i with hlt | hEq
          · left; simp only [acc', List.length_append, List.length_singleton]; omega
          · right; exact hEq
        · by_cases heq : i = env.length
          · subst heq
            rw [getD_snoc_eq]
            left; simp [acc']
          · have hge : env'.length ≤ i := by simp [env']; omega
            rw [List.getD_eq_default _ _ hge]
            right; rfl
      · intro i
        rw [hfold]
        by_cases hi : i < env.length
        · rw [getD_append_lt env [n + acc.length] i fw hi]
          have ho : (step oldW g).getD i false = oldW.getD i false := by
            rw [step, getD_append_lt oldW _ i false (hlen ▸ hi)]
          rw [ho]
          rcases hbnd i with hlt | hEq
          · rw [step, getD_append_lt newW _ _ false (hnewW_len ▸ hlt)]
            exact hinv i
          · rw [hEq]
            have h1 : (step newW g').getD fw false = false :=
              List.getD_eq_default _ _ (by simp [step, hnewW_len]; omega)
            have h2 : newW.getD fw false = false :=
              List.getD_eq_default _ _ (by omega)
            calc (step newW g').getD fw false = false := h1
              _ = newW.getD fw false := h2.symm
              _ = newW.getD (env.getD i fw) false := by rw [hEq]
              _ = oldW.getD i false := hinv i
        · by_cases heq : i = env.length
          · subst heq
            rw [getD_snoc_eq]
            have h1 : (step newW g').getD (n + acc.length) false =
                g'.op.eval (g'.inputs.map fun k => newW.getD k false) := by
              rw [step, ← hnewW_len, getD_snoc_eq]
            have h2 : (step oldW g).getD env.length false =
                g.op.eval (g.inputs.map fun k => oldW.getD k false) := by
              rw [step, hlen, getD_snoc_eq]
            rw [h1, h2, heval]
          · have hge1 : env'.length ≤ i := by simp [env']; omega
            have hge2 : (step oldW g).length ≤ i := by simp [step]; omega
            rw [List.getD_eq_default env' _ hge1, List.getD_eq_default (step oldW g) _ hge2]
            exact List.getD_eq_default _ _ (by simp [step, hnewW_len]; omega)
    · simp only [↓reduceIte]
      have heval := eval_or_at_false oldW x4 g hg hor hw4
      cases hf : g.inputs.filter (fun i => i != x4) with
      | nil =>
        rw [hf] at heval
        let env' := env ++ [fw]
        apply ih acc env' (step oldW g)
        · omega
        · exact hgs'
        · exact hx4'
        · exact hw4'
        · simp [env', hstep_len, hlen]
        · intro i
          by_cases hi : i < env.length
          · rw [getD_append_lt env [fw] i fw hi]; exact hbnd i
          · by_cases heq : i = env.length
            · subst heq; rw [getD_snoc_eq]; right; rfl
            · rw [List.getD_eq_default env' _ (by simp [env']; omega)]; right; rfl
        · intro i
          by_cases hi : i < env.length
          · rw [getD_append_lt env [fw] i fw hi, step, getD_append_lt oldW _ i false (hlen ▸ hi)]
            exact hinv i
          · by_cases heq : i = env.length
            · subst heq
              rw [getD_snoc_eq]
              have h1 : newW.getD fw false = false := List.getD_eq_default _ _ (by omega)
              have h2 : (step oldW g).getD env.length false =
                  g.op.eval (g.inputs.map fun k => oldW.getD k false) := by
                rw [step, hlen, getD_snoc_eq]
              rw [h2, heval]; exact h1
            · rw [List.getD_eq_default env' _ (by simp [env']; omega),
                  List.getD_eq_default (step oldW g) _ (by simp [step]; omega)]
              exact List.getD_eq_default _ _ (by rw [foldl_length]; simp; omega)
      | cons b bs =>
        rw [hf] at heval
        let env' := env ++ [env.getD b fw]
        apply ih acc env' (step oldW g)
        · omega
        · exact hgs'
        · exact hx4'
        · exact hw4'
        · simp [env', hstep_len, hlen]
        · intro i
          by_cases hi : i < env.length
          · rw [getD_append_lt env [env.getD b fw] i fw hi]; exact hbnd i
          · by_cases heq : i = env.length
            · subst heq; rw [getD_snoc_eq]; exact hbnd b
            · rw [List.getD_eq_default env' _ (by simp [env']; omega)]; right; rfl
        · intro i
          by_cases hi : i < env.length
          · rw [getD_append_lt env [env.getD b fw] i fw hi, step, getD_append_lt oldW _ i false (hlen ▸ hi)]
            exact hinv i
          · by_cases heq : i = env.length
            · subst heq
              rw [getD_snoc_eq]
              have h2 : (step oldW g).getD env.length false =
                  g.op.eval (g.inputs.map fun k => oldW.getD k false) := by
                rw [step, hlen, getD_snoc_eq]
              rw [h2, heval]
              exact hinv b
            · rw [List.getD_eq_default env' _ (by simp [env']; omega),
                  List.getD_eq_default (step oldW g) _ (by simp [step]; omega)]
              exact List.getD_eq_default _ _ (by rw [foldl_length]; simp; omega)

end PEqualNP.Outside.L_meta_4793

theorem PEqualNP.Outside.L_meta_4793 :
    ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : List (Option (Fin x1))) (x4 : ℕ),
      PEqualNP.MetaComplexity.FanInTwo x2 →
      x3[x4]? = Option.some Option.none →
      (∃ (x7 : Fin x1 → Bool) (x8 : Fin x1 → Bool),
        x2.eval (List.map (fun (x9 : Option (Fin x1)) => x9.elim Bool.false x7) x3) ≠
        x2.eval (List.map (fun (x9 : Option (Fin x1)) => x9.elim Bool.false x8) x3)) →
      ∃ (x8 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo x8 ∧
        x8.size + (List.filter (fun (x9 : PEqualNP.CircuitLowerBounds.Gate) =>
          x9.op.eval [Bool.true, Bool.false] && x9.inputs.contains x4) x2.gates).length ≤ x2.size ∧
        ∀ (x9 : Fin x1 → Bool),
          x8.eval (List.ofFn x9) = x2.eval (List.map (fun (x10 : Option (Fin x1)) => x10.elim Bool.false x9) x3) := by
  intro n C x3 x4 hfan hx4 _
  let fw : ℕ := n + C.gates.length + 1
  let initEnv : List ℕ := x3.map (fun o => o.elim fw Fin.val)
  let res := PEqualNP.Outside.L_meta_4793.elimLoop n x4 fw C.gates ([], initEnv)
  let D : PEqualNP.CircuitLowerBounds.Circuit :=
    { gates := res.1, output := res.2.getD C.output fw }
  refine ⟨D, ?_, ?_, ?_⟩
  · exact PEqualNP.Outside.L_meta_4793.elimLoop_fan n x4 fw C.gates [] initEnv (by simp) hfan
  · have hsz := PEqualNP.Outside.L_meta_4793.elimLoop_size n x4 fw C.gates [] initEnv
    change res.1.length + (C.gates.filter (PEqualNP.Outside.L_meta_4793.isOrAt x4)).length ≤ C.gates.length
    simp only [List.length_nil, Nat.zero_add] at hsz
    exact le_of_eq hsz
  · intro x
    let oldW : List Bool := x3.map (fun o => o.elim false x)
    have hx4_lt : x4 < oldW.length := by
      have : x4 < x3.length := by
        by_contra h
        rw [List.getElem?_eq_none (Nat.le_of_not_lt h)] at hx4
        cases hx4
      simp [oldW, this]
    have hw4 : oldW.getD x4 false = false := by
      simp only [oldW, List.getD_eq_getElem?_getD, List.getElem?_map, hx4]
      rfl
    have hlen : initEnv.length = oldW.length := by simp [initEnv, oldW]
    have hbnd : ∀ i, initEnv.getD i fw < n + ([] : List PEqualNP.CircuitLowerBounds.Gate).length ∨
        initEnv.getD i fw = fw := by
      intro i
      simp only [initEnv, List.getD_eq_getElem?_getD, List.getElem?_map, List.length_nil, Nat.add_zero]
      cases h : x3[i]? with
      | none => right; rfl
      | some o =>
        cases o with
        | none => right; rfl
        | some v => left; exact v.isLt
    have hinv : ∀ i, (([] : List PEqualNP.CircuitLowerBounds.Gate).foldl
        PEqualNP.Outside.L_meta_4793.step (List.ofFn x)).getD (initEnv.getD i fw) false = oldW.getD i false := by
      intro i
      simp only [List.foldl_nil, initEnv, oldW, List.getD_eq_getElem?_getD, List.getElem?_map]
      cases h : x3[i]? with
      | none =>
        simp only [Option.map_none, Option.getD_none]
        have : (List.ofFn x)[fw]? = none := List.getElem?_eq_none (by simp [fw]; omega)
        simp [this]
      | some o =>
        cases o with
        | none =>
          simp only [Option.map_some, Option.getD_some, Option.elim_none]
          have : (List.ofFn x)[fw]? = none := List.getElem?_eq_none (by simp [fw]; omega)
          simp [this]
        | some v =>
          simp only [Option.map_some, Option.getD_some, Option.elim_some]
          rw [List.getElem?_eq_getElem (by simp), List.getElem_ofFn]
          rfl
    have hcorr := PEqualNP.Outside.L_meta_4793.elimLoop_correct n x4 fw x C.gates [] initEnv oldW
      (by simp [fw]) hfan hx4_lt hw4 hlen hbnd hinv C.output
    exact hcorr
