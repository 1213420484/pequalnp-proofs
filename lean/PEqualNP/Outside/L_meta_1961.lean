import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1961

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

theorem val_mono (gates : List Gate) {n : ℕ}
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x x' : Fin n → Bool) (hx : ∀ v, x v = true → x' v = true) :
    ∀ w, val gates w x = true → val gates w x' = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h
    by_cases hwn : w < n
    · rw [val_input gates _ w hwn] at h ⊢
      exact hx _ h
    · by_cases hbig : n + gates.length ≤ w
      · rw [val_big gates x w hbig] at h
        exact Bool.noConfusion h
      · have hi : w - n < gates.length := by omega
        have he : n + (w - n) = w := by omega
        rw [← he] at h ⊢
        rcases (legal gates[w - n] (List.getElem_mem hi)).1 with ha | ho
        · apply (val_and gates x' (w - n) hi ha).2
          intro j hj
          obtain ⟨hjlt, hjv⟩ := (val_and gates x (w - n) hi ha).1 h j hj
          exact ⟨hjlt, ih j (by omega) hjv⟩
        · obtain ⟨j, hj, hjlt, hv⟩ := (val_or gates x (w - n) hi ho).1 h
          exact (val_or gates x' (w - n) hi ho).2 ⟨j, hj, hjlt, ih j (by omega) hv⟩

theorem val_zero (gates : List Gate) {n : ℕ}
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hlen2 : ∀ g ∈ gates, g.inputs.length = 2) :
    ∀ w, val gates w (fun _ : Fin n => false) = false := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwn : w < n
    · rw [val_input gates _ w hwn]
    · by_cases hbig : n + gates.length ≤ w
      · exact val_big gates _ w hbig
      · have hi : w - n < gates.length := by omega
        have he : n + (w - n) = w := by omega
        rw [← he]
        cases hv : val gates (n + (w - n)) (fun _ : Fin n => false) with
        | false => rfl
        | true =>
          exfalso
          rcases (legal gates[w - n] (List.getElem_mem hi)).1 with ha | ho
          · obtain ⟨a, b, hab⟩ := List.length_eq_two.1 (hlen2 gates[w - n] (List.getElem_mem hi))
            have hma : a ∈ gates[w - n].inputs := by rw [hab]; simp
            obtain ⟨halt, hav⟩ := (val_and gates _ (w - n) hi ha).1 hv a hma
            rw [ih a (by omega)] at hav
            exact Bool.noConfusion hav
          · obtain ⟨a, _, halt, hav⟩ := (val_or gates _ (w - n) hi ho).1 hv
            rw [ih a (by omega)] at hav
            exact Bool.noConfusion hav

def Cl {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool) (τ : Fin n → Fin n → Bool)
    (i : Fin gates.length) (X : Finset (Fin n)) : Prop :=
  (gates.get i).op = GateOp.or → val gates (n + (i : ℕ)) c = false →
    ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ M, ∀ y' ∈ M,
      (val gates a (τ y) = true ∨ val gates b (τ y) = true) →
      (val gates a (τ y') = true ∨ val gates b (τ y') = true) → (y ∈ X ↔ y' ∈ X)

def Con {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool) (τ : Fin n → Fin n → Bool)
    (k : ℕ) (X : Finset (Fin n)) : Prop :=
  ∀ i : Fin gates.length, (i : ℕ) < k → Cl gates M c τ i X

def Mrg {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool) (τ : Fin n → Fin n → Bool)
    (g : Fin gates.length) : Prop :=
  (gates.get g).op = GateOp.or ∧ val gates (n + (g : ℕ)) c = false ∧
    ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ M, ∃ r' ∈ M,
      val gates w1 (τ r) = true ∧ val gates w2 (τ r') = true ∧
      ∃ X : Finset (Fin n), r ∈ X ∧ r' ∉ X ∧ Con gates M c τ (g : ℕ) X

theorem single {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hτ : ∀ p ∈ M, ∀ v, τ p v = true → v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (k : ℕ) (hk : k ≤ gates.length) (X : Finset (Fin n)) (hX : Con gates M c τ k X) :
    ∀ w, w < n + k → val gates w c = false → ∀ y ∈ M, ∀ y' ∈ M,
      val gates w (τ y) = true → val gates w (τ y') = true → (y ∈ X ↔ y' ∈ X) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hwc y hy y' hy' h1 h2
    by_cases hwn : w < n
    · rw [val_input gates _ w hwn] at h1 h2
      have e1 := hτ y hy _ h1
      have e2 := hτ y' hy' _ h2
      rw [← e1, ← e2]
    · have hi : w - n < gates.length := by omega
      have he : n + (w - n) = w := by omega
      rw [← he] at hwc h1 h2
      have hinp : ∀ a ∈ gates[w - n].inputs, a < n + (w - n) :=
        hin ⟨w - n, hi⟩
      have hlen := (legal gates[w - n] (List.getElem_mem hi)).2
      rcases (legal gates[w - n] (List.getElem_mem hi)).1 with ha | ho
      · have hex : ∃ j ∈ gates[w - n].inputs, val gates j c = false := by
          by_contra hne
          have hall : val gates (n + (w - n)) c = true := by
            apply (val_and gates c (w - n) hi ha).2
            intro j hj
            refine ⟨hinp j hj, ?_⟩
            cases hv : val gates j c with
            | true => rfl
            | false => exact absurd ⟨j, hj, hv⟩ hne
          rw [hall] at hwc
          exact Bool.noConfusion hwc
        obtain ⟨j, hj, hjc⟩ := hex
        have hjlt := hinp j hj
        exact ih j (by omega) (by omega) hjc y hy y' hy'
          ((val_and gates (τ y) (w - n) hi ha).1 h1 j hj).2
          ((val_and gates (τ y') (w - n) hi ha).1 h2 j hj).2
      · have hall : ∀ j ∈ gates[w - n].inputs, val gates j c = false := by
          intro j hj
          cases hv : val gates j c with
          | false => rfl
          | true =>
            have ht : val gates (n + (w - n)) c = true :=
              (val_or gates c (w - n) hi ho).2 ⟨j, hj, hinp j hj, hv⟩
            rw [ht] at hwc
            exact Bool.noConfusion hwc
        obtain ⟨j1, hj1, _, hv1⟩ := (val_or gates (τ y) (w - n) hi ho).1 h1
        obtain ⟨j2, hj2, _, hv2⟩ := (val_or gates (τ y') (w - n) hi ho).1 h2
        rcases hinpe : gates[w - n].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
        · rw [hinpe] at hj1
          simp at hj1
        · rw [hinpe] at hj1 hj2
          have e1 : j1 = a := by simpa using hj1
          have e2 : j2 = a := by simpa using hj2
          rw [e1] at hv1
          rw [e2] at hv2
          have hjlt := hinp a (by rw [hinpe]; simp)
          exact ih a (by omega) (by omega) (hall a (by rw [hinpe]; simp)) y hy y' hy' hv1 hv2
        · rw [hinpe] at hj1 hj2
          have d1 : val gates a (τ y) = true ∨ val gates b (τ y) = true := by
            rcases List.mem_pair.1 hj1 with e | e
            · subst e; exact Or.inl hv1
            · subst e; exact Or.inr hv1
          have d2 : val gates a (τ y') = true ∨ val gates b (τ y') = true := by
            rcases List.mem_pair.1 hj2 with e | e
            · subst e; exact Or.inl hv2
            · subst e; exact Or.inr hv2
          exact hX ⟨w - n, hi⟩ (by simp; omega) ho hwc a b hinpe y hy y' hy' d1 d2
        · rw [hinpe] at hlen
          simp at hlen

theorem con_succ {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (hk : k < gates.length) (X : Finset (Fin n)) :
    Con gates M c τ (k + 1) X ↔ Con gates M c τ k X ∧ Cl gates M c τ ⟨k, hk⟩ X := by
  constructor
  · intro h
    exact ⟨fun i hi => h i (by omega), h ⟨k, hk⟩ (by simp)⟩
  · rintro ⟨h1, h2⟩ i hi
    by_cases e : (i : ℕ) = k
    · have e' : i = ⟨k, hk⟩ := Fin.ext e
      rw [e']
      exact h2
    · exact h1 i (by omega)

theorem con_compl {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X : Finset (Fin n)) (h : Con gates M c τ k X) :
    Con gates M c τ k Xᶜ := by
  intro i hi ho hc' a b hab y hy y' hy' h1 h2
  rw [Finset.mem_compl, Finset.mem_compl, not_iff_not]
  exact h i hi ho hc' a b hab y hy y' hy' h1 h2

theorem con_symm {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X Y : Finset (Fin n)) (hX : Con gates M c τ k X)
    (hY : Con gates M c τ k Y) : Con gates M c τ k (symmDiff X Y) := by
  intro i hi ho hc' a b hab y hy y' hy' h1 h2
  have e1 := hX i hi ho hc' a b hab y hy y' hy' h1 h2
  have e2 := hY i hi ho hc' a b hab y hy y' hy' h1 h2
  rw [Finset.mem_symmDiff, Finset.mem_symmDiff, e1, e2]

theorem con_inter {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X : Finset (Fin n)) (hX : Con gates M c τ k X) :
    Con gates M c τ k (X ∩ M) := by
  intro i hi ho hc' a b hab y hy y' hy' h1 h2
  have e1 := hX i hi ho hc' a b hab y hy y' hy' h1 h2
  rw [Finset.mem_inter, Finset.mem_inter, e1]
  exact ⟨fun h => ⟨h.1, hy'⟩, fun h => ⟨h.1, hy⟩⟩

theorem cl_of {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (g : Fin gates.length) (X : Finset (Fin n)) (a b : ℕ)
    (hab : (gates.get g).inputs = [a, b])
    (sA : ∀ y ∈ M, ∀ y' ∈ M, val gates a (τ y) = true → val gates a (τ y') = true →
      (y ∈ X ↔ y' ∈ X))
    (sB : ∀ y ∈ M, ∀ y' ∈ M, val gates b (τ y) = true → val gates b (τ y') = true →
      (y ∈ X ↔ y' ∈ X))
    (Q : ∀ y ∈ M, ∀ y' ∈ M, val gates a (τ y) = true → val gates b (τ y') = true →
      (y ∈ X ↔ y' ∈ X)) : Cl gates M c τ g X := by
  intro _ _ a' b' hab' y hy y' hy' h1 h2
  rw [hab] at hab'
  obtain ⟨e1, e2⟩ : a = a' ∧ b = b' := by simpa using hab'
  subst e1
  subst e2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact sA y hy y' hy' h1 h2
  · exact Q y hy y' hy' h1 h2
  · exact (Q y' hy' y hy h2 h1).symm
  · exact sB y hy y' hy' h1 h2

theorem symm_flip {n : ℕ} (X Y : Finset (Fin n)) (r r' : Fin n) (hr : r ∈ Y) (hr' : r' ∉ Y) :
    (r ∈ symmDiff X Y ↔ r' ∈ symmDiff X Y) ↔ ¬ (r ∈ X ↔ r' ∈ X) := by
  by_cases h1 : r ∈ X <;> by_cases h2 : r' ∈ X <;> simp [Finset.mem_symmDiff, h1, h2, hr, hr']

open Classical in
noncomputable def P {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) : Finset (Finset (Fin n)) :=
  M.powerset.filter (fun X => Con gates M c τ k X)

open Classical in
theorem symm_mem {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X Y : Finset (Fin n)) (hX : X ∈ P gates M c τ k)
    (hY : Y ⊆ M) (hYc : Con gates M c τ k Y) : symmDiff X Y ∈ P gates M c τ k := by
  rw [P, Finset.mem_filter, Finset.mem_powerset] at hX ⊢
  refine ⟨?_, con_symm gates M c τ k X Y hX.2 hYc⟩
  intro v hv
  rw [Finset.mem_symmDiff] at hv
  rcases hv with hv | hv
  · exact hX.1 hv.1
  · exact hY hv.1

open Classical in
theorem step {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hτ : ∀ p ∈ M, ∀ v, τ p v = true → v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (g : Fin gates.length) :
    (P gates M c τ ((g : ℕ) + 1)).card * (if Mrg gates M c τ g then 2 else 1)
      = (P gates M c τ (g : ℕ)).card := by
  by_cases hal : (gates.get g).op = GateOp.or ∧ val gates (n + (g : ℕ)) c = false ∧
      ∃ a b : ℕ, (gates.get g).inputs = [a, b]
  swap
  · have hnm : ¬ Mrg gates M c τ g := by
      rintro ⟨h1, h2, w1, w2, h3, _⟩
      exact hal ⟨h1, h2, w1, w2, h3⟩
    have hP : P gates M c τ ((g : ℕ) + 1) = P gates M c τ (g : ℕ) := by
      unfold P
      apply Finset.filter_congr
      intro X _
      rw [con_succ gates M c τ g g.2 X]
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, ?_⟩
        intro ho hc' a b hab
        exact absurd ⟨ho, hc', a, b, hab⟩ hal
    simp [hP, hnm]
  · obtain ⟨ho, hgc, a, b, hab⟩ := hal
    have hma : a ∈ (gates.get g).inputs := by rw [hab]; simp
    have hmb : b ∈ (gates.get g).inputs := by rw [hab]; simp
    have ha : a < n + (g : ℕ) := hin g a hma
    have hb : b < n + (g : ℕ) := hin g b hmb
    have hac : val gates a c = false := by
      cases hv : val gates a c with
      | false => rfl
      | true =>
        have ht : val gates (n + (g : ℕ)) c = true :=
          (val_or gates c g g.2 ho).2 ⟨a, hma, ha, hv⟩
        rw [ht] at hgc
        exact Bool.noConfusion hgc
    have hbc : val gates b c = false := by
      cases hv : val gates b c with
      | false => rfl
      | true =>
        have ht : val gates (n + (g : ℕ)) c = true :=
          (val_or gates c g g.2 ho).2 ⟨b, hmb, hb, hv⟩
        rw [ht] at hgc
        exact Bool.noConfusion hgc
    have sA : ∀ X, Con gates M c τ g X → ∀ y ∈ M, ∀ y' ∈ M, val gates a (τ y) = true →
        val gates a (τ y') = true → (y ∈ X ↔ y' ∈ X) := fun X hX =>
      single gates M c τ hτ legal hin g (le_of_lt g.2) X hX a ha hac
    have sB : ∀ X, Con gates M c τ g X → ∀ y ∈ M, ∀ y' ∈ M, val gates b (τ y) = true →
        val gates b (τ y') = true → (y ∈ X ↔ y' ∈ X) := fun X hX =>
      single gates M c τ hτ legal hin g (le_of_lt g.2) X hX b hb hbc
    by_cases hm : ∃ r ∈ M, ∃ r' ∈ M, val gates a (τ r) = true ∧ val gates b (τ r') = true ∧
        ∃ X : Finset (Fin n), r ∈ X ∧ r' ∉ X ∧ Con gates M c τ (g : ℕ) X
    · have hmrg : Mrg gates M c τ g := ⟨ho, hgc, a, b, hab, hm⟩
      obtain ⟨r, hr, r', hr', hra, hrb, X0, hrX, hr'X, hX0⟩ := hm
      simp only [hmrg, ite_true]
      have hP : P gates M c τ ((g : ℕ) + 1)
          = (P gates M c τ (g : ℕ)).filter (fun X => r ∈ X ↔ r' ∈ X) := by
        unfold P
        rw [Finset.filter_filter]
        apply Finset.filter_congr
        intro X _
        rw [con_succ gates M c τ g g.2 X]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, h2 ho hgc a b hab r hr r' hr' (Or.inl hra) (Or.inr hrb)⟩
        · rintro ⟨h1, h2⟩
          refine ⟨h1, cl_of gates M c τ g X a b hab (sA X h1) (sB X h1) ?_⟩
          intro y hy y' hy' hya hyb
          exact ((sA X h1 y hy r hr hya hra).trans h2).trans (sB X h1 r' hr' y' hy' hrb hyb)
      rw [hP]
      have hsplit := Finset.card_filter_add_card_filter_not (s := P gates M c τ (g : ℕ))
        (fun X => r ∈ X ↔ r' ∈ X)
      have hY0 : X0 ∩ M ⊆ M := Finset.inter_subset_right
      have hY0c := con_inter gates M c τ g X0 hX0
      have hrY : r ∈ X0 ∩ M := Finset.mem_inter.2 ⟨hrX, hr⟩
      have hr'Y : r' ∉ X0 ∩ M := fun h => hr'X (Finset.mem_inter.1 h).1
      have hbij : ((P gates M c τ (g : ℕ)).filter (fun X => ¬ (r ∈ X ↔ r' ∈ X))).card
          = ((P gates M c τ (g : ℕ)).filter (fun X => r ∈ X ↔ r' ∈ X)).card := by
        refine Finset.card_bij' (fun X _ => symmDiff X (X0 ∩ M)) (fun X _ => symmDiff X (X0 ∩ M))
          ?_ ?_ ?_ ?_
        · intro X hX
          rw [Finset.mem_filter] at hX ⊢
          refine ⟨symm_mem gates M c τ g X _ hX.1 hY0 hY0c, ?_⟩
          exact (symm_flip X (X0 ∩ M) r r' hrY hr'Y).2 hX.2
        · intro X hX
          rw [Finset.mem_filter] at hX ⊢
          refine ⟨symm_mem gates M c τ g X _ hX.1 hY0 hY0c, ?_⟩
          intro hcon
          exact (symm_flip X (X0 ∩ M) r r' hrY hr'Y).1 hcon hX.2
        · intro X _
          exact symmDiff_symmDiff_cancel_right _ _
        · intro X _
          exact symmDiff_symmDiff_cancel_right _ _
      omega
    · have hnm : ¬ Mrg gates M c τ g := by
        rintro ⟨_, _, w1, w2, h3, r, hr, r', hr', h4, h5, h6⟩
        rw [hab] at h3
        obtain ⟨e1, e2⟩ : a = w1 ∧ b = w2 := by simpa using h3
        subst e1
        subst e2
        exact hm ⟨r, hr, r', hr', h4, h5, h6⟩
      simp only [hnm, ite_false, Nat.mul_one]
      congr 1
      unfold P
      apply Finset.filter_congr
      intro X _
      rw [con_succ gates M c τ g g.2 X]
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, cl_of gates M c τ g X a b hab (sA X h) (sB X h) ?_⟩
        intro y hy y' hy' hya hyb
        constructor
        · intro hyX
          by_contra hn
          exact hm ⟨y, hy, y', hy', hya, hyb, X, hyX, hn, h⟩
        · intro hyX
          by_contra hn
          exact hm ⟨y, hy, y', hy', hya, hyb, Xᶜ, Finset.mem_compl.2 hn,
            fun h' => Finset.mem_compl.1 h' hyX, con_compl gates M c τ g X h⟩

open Classical in
theorem count {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hτ : ∀ p ∈ M, ∀ v, τ p v = true → v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (k : ℕ) (hk : k ≤ gates.length) :
    (P gates M c τ k).card *
      2 ^ (∑ g : Fin gates.length, if (g : ℕ) < k ∧ Mrg gates M c τ g then 1 else 0)
      = 2 ^ M.card := by
  induction k with
  | zero =>
    have h0 : P gates M c τ 0 = M.powerset := by
      unfold P
      apply Finset.filter_true_of_mem
      intro X _ i hi
      exact absurd hi (Nat.not_lt_zero _)
    rw [h0, Finset.card_powerset]
    simp
  | succ k ih =>
    have hk' : k < gates.length := hk
    have hs : (P gates M c τ (k + 1)).card * (if Mrg gates M c τ ⟨k, hk'⟩ then 2 else 1)
        = (P gates M c τ k).card := step gates M c τ hτ legal hin ⟨k, hk'⟩
    have hsum : (∑ g : Fin gates.length, if (g : ℕ) < k + 1 ∧ Mrg gates M c τ g then 1 else 0)
        = (∑ g : Fin gates.length, if (g : ℕ) < k ∧ Mrg gates M c τ g then 1 else 0)
          + (if Mrg gates M c τ ⟨k, hk'⟩ then 1 else 0) := by
      have hpt : ∀ g : Fin gates.length,
          (if (g : ℕ) < k + 1 ∧ Mrg gates M c τ g then 1 else 0)
          = (if (g : ℕ) < k ∧ Mrg gates M c τ g then 1 else 0)
            + (if g = ⟨k, hk'⟩ then (if Mrg gates M c τ ⟨k, hk'⟩ then 1 else 0) else 0) := by
        intro g
        by_cases e : g = ⟨k, hk'⟩
        · subst e
          simp
        · have hne : (g : ℕ) ≠ k := fun h => e (Fin.ext h)
          have h2 : ((g : ℕ) < k + 1) ↔ ((g : ℕ) < k) := by omega
          simp [e, h2]
      rw [Finset.sum_congr rfl (fun g _ => hpt g), Finset.sum_add_distrib]
      simp
    rw [hsum, pow_add, ← ih (le_of_lt hk'), ← hs]
    split_ifs <;> ring

open Classical in
theorem mcount {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hτ : ∀ p ∈ M, ∀ v, τ p v = true → v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (hM : 1 ≤ M.card) (o : ℕ) (hoc : val gates o c = false)
    (hot : ∀ p ∈ M, val gates o (τ p) = true) :
    (∑ g : Fin gates.length, if Mrg gates M c τ g then 1 else 0) = M.card - 1 := by
  have hne : M.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨p0, hp0⟩ := hne
  have holt : o < n + gates.length := by
    by_contra h
    have hb := val_big gates (τ p0) o (by omega)
    rw [hot p0 hp0] at hb
    exact Bool.noConfusion hb
  have hfin : P gates M c τ gates.length = {∅, M} := by
    ext X
    rw [P, Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hsub, hX⟩
      have hs := single gates M c τ hτ legal hin gates.length le_rfl X hX o holt hoc
      by_cases hex : ∃ y ∈ M, y ∈ X
      · obtain ⟨y, hy, hyX⟩ := hex
        right
        apply Finset.Subset.antisymm hsub
        intro z hz
        exact (hs y hy z hz (hot y hy) (hot z hz)).1 hyX
      · left
        apply Finset.eq_empty_of_forall_notMem
        intro z hz
        exact hex ⟨z, hsub hz, hz⟩
    · rintro (e | e)
      · subst e
        refine ⟨Finset.empty_subset _, ?_⟩
        intro i _ _ _ a b _ y _ y' _ _ _
        simp
      · subst e
        refine ⟨Finset.Subset.refl _, ?_⟩
        intro i _ _ _ a b _ y hy y' hy' _ _
        exact ⟨fun _ => hy', fun _ => hy⟩
  have hcnt := count gates M c τ hτ legal hin gates.length le_rfl
  have hpair : ({∅, M} : Finset (Finset (Fin n))).card = 2 := by
    apply Finset.card_pair
    intro h
    rw [← h] at hp0
    simp at hp0
  rw [hfin, hpair] at hcnt
  have hsum : (∑ g : Fin gates.length, if (g : ℕ) < gates.length ∧ Mrg gates M c τ g then 1 else 0)
      = ∑ g : Fin gates.length, if Mrg gates M c τ g then 1 else 0 :=
    Finset.sum_congr rfl (fun g _ => by simp [g.2])
  rw [hsum] at hcnt
  have hm1 : 2 ^ M.card = 2 * 2 ^ (M.card - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h8 : 2 ^ (∑ g : Fin gates.length, if Mrg gates M c τ g then 1 else 0) = 2 ^ (M.card - 1) :=
    Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) (hcnt.trans hm1)
  exact Nat.pow_right_injective (le_refl 2) h8

theorem disj_gen {n : ℕ} (gates : List Gate)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (L1 L2 A1 A2 : Finset (Fin n)) (c1 : Fin n → Bool) (hA : A1 ⊆ L1) (hcard : (L1 ∩ L2).card ≤ 1)
    (g : Fin gates.length)
    (h1 : Mrg gates A1 c1 (fun y v => decide (v = y)) g)
    (h2 : Mrg gates A2 (fun v => decide (v ∉ L2)) (fun y v => decide (v = y)) g) : False := by
  obtain ⟨ho, _, w1, w2, hab, r, hr, r', hr', hv1, hv2, X, hrX, hr'X, _⟩ := h1
  obtain ⟨_, hc2, _⟩ := h2
  have hne : r ≠ r' := fun e => hr'X (e ▸ hrX)
  have hm1 : w1 ∈ (gates.get g).inputs := by rw [hab]; simp
  have hm2 : w2 ∈ (gates.get g).inputs := by rw [hab]; simp
  have ht1 : val gates (n + (g : ℕ)) (fun v : Fin n => decide (v = r)) = true :=
    (val_or gates _ g g.2 ho).2 ⟨w1, hm1, hin g w1 hm1, hv1⟩
  have ht2 : val gates (n + (g : ℕ)) (fun v : Fin n => decide (v = r')) = true :=
    (val_or gates _ g g.2 ho).2 ⟨w2, hm2, hin g w2 hm2, hv2⟩
  have key : ∀ s : Fin n, val gates (n + (g : ℕ)) (fun v : Fin n => decide (v = s)) = true →
      s ∈ L2 := by
    intro s hs
    by_contra hns
    have hmo := val_mono gates legal (fun v : Fin n => decide (v = s))
      (fun v : Fin n => decide (v ∉ L2)) (by
        intro v hv
        have e : v = s := of_decide_eq_true hv
        rw [e]
        exact decide_eq_true hns) _ hs
    rw [hc2] at hmo
    exact Bool.noConfusion hmo
  have hr2 := key r ht1
  have hr2' := key r' ht2
  have hsub : ({r, r'} : Finset (Fin n)) ⊆ L1 ∩ L2 := by
    intro v hv
    rw [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with e | e
    · rw [e]; exact Finset.mem_inter.2 ⟨hA hr, hr2⟩
    · rw [e]; exact Finset.mem_inter.2 ⟨hA hr', hr2'⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_pair hne] at hc
  omega

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have h1 : (cones n C).getD k [] =
      (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
    rw [hc, coneFold_getD_lt n post _ k (by simp [coneStep, hl0])]
    have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n post _ m (by simp [coneStep, hl0]; omega)]
    exact coneStep_getD_lt n _ gk m (by omega)
  unfold InCone
  rw [h1]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro ⟨w, hw, hn, hlt, h⟩
    refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [← h2 (w - n) (by omega)]
      exact h

lemma inCone_lt (n : ℕ) (C : Circuit) (i k : ℕ) (h : InCone n C i k) :
    k < C.gates.length ∧ i < k := by
  have hk : k < C.gates.length := by
    by_contra hge
    have hlen : (cones n C).length = C.gates.length := by
      unfold cones
      rw [coneFold_length]
      simp
    unfold InCone at h
    rw [List.getD_eq_default _ _ (by omega)] at h
    simp at h
  refine ⟨hk, ?_⟩
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    obtain ⟨w, _, hn, hlt, hw⟩ := (inCone_iff n C i k hk).1 h
    rcases hw with rfl | h2
    · omega
    · have h3 := ih (w - n) (by omega) h2 (by omega)
      omega

lemma unique_and_pair (C : Circuit) (hp : PEqualNP.TopForm.andPairs 26 C ≤ 1)
    (i0 j0 : ℕ) (hi0 : (gateAt C i0).op = GateOp.and) (hj0 : (gateAt C j0).op = GateOp.and)
    (hc0 : InCone 26 C i0 j0) :
    ∀ i' j', (gateAt C i').op = GateOp.and → (gateAt C j').op = GateOp.and →
      InCone 26 C i' j' → i' = i0 ∧ j' = j0 := by
  intro i' j' hi' hj' hc'
  have hlt0 := inCone_lt 26 C i0 j0 hc0
  have hlt' := inCone_lt 26 C i' j' hc'
  let := gateOpDecEq
  unfold PEqualNP.TopForm.andPairs at hp
  have heq := Finset.card_le_one.1 hp (i', j') (by
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨⟨by omega, hlt'.1⟩, hi', hj', hc'⟩) (i0, j0) (by
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨⟨by omega, hlt0.1⟩, hi0, hj0, hc0⟩)
  exact Prod.mk.inj heq

def adjb (s t : Fin 26) : Bool :=
  decide (s.val < 13 ∧ 13 ≤ t.val ∧ (s.val + 26 - t.val) % 13 ∈ [0, 1, 3, 9]) ||
  decide (t.val < 13 ∧ 13 ≤ s.val ∧ (t.val + 26 - s.val) % 13 ∈ [0, 1, 3, 9])

def mk (f g : Fin 13 → Bool) (u : Fin 26) : Bool :=
  if h : u.val < 13 then f ⟨u.val, h⟩ else g ⟨u.val - 13, by omega⟩

theorem mk_eq (f g : Fin 13 → Bool) : List.ofFn f ++ List.ofFn g = List.ofFn (mk f g) := by
  have hl : (List.ofFn f).length = 13 := List.length_ofFn
  apply List.ext_getElem
  · rw [List.length_append, List.length_ofFn, List.length_ofFn, List.length_ofFn]
  · intro i h1 h2
    rw [List.getElem_ofFn]
    by_cases h : i < 13
    · rw [List.getElem_append_left (by rw [hl]; exact h), List.getElem_ofFn]
      simp [mk, h]
    · rw [List.getElem_append_right (by rw [hl]; omega), List.getElem_ofFn]
      simp [mk, h]

def pr (s t : Fin 26) : Fin 26 → Bool := fun u => decide (u = s ∨ u = t)

def N (v : Fin 26) : Finset (Fin 26) := Finset.univ.filter (fun y => adjb v y = true)

theorem mem_N (v y : Fin 26) : y ∈ N v ↔ adjb v y = true := by
  simp [N]

def qin (Q : Finset (Fin 13)) : Fin 26 → Bool :=
  mk (fun u => decide (u ∈ Q)) (fun v => decide (∀ r ∈ Q, r - v ∉ ({0, 1, 3, 9} : Finset (Fin 13))))

def ein (p l : Fin 13) : Fin 26 → Bool :=
  mk (fun x => decide (x = p)) (fun x => decide (x = l))

def Pp (s t : Fin 26) : Fin 13 := ⟨(min s.val t.val) % 13, Nat.mod_lt _ (by norm_num)⟩

def Ll (s t : Fin 26) : Fin 13 := ⟨(max s.val t.val - 13) % 13, Nat.mod_lt _ (by norm_num)⟩

def tab : List (List ℕ) := [[0, 1, 2, 5], [0, 1, 2, 5], [0, 1, 2, 5], [0, 2, 3, 4], [0, 1, 4, 6], [0, 1, 2, 5], [0, 1, 2, 6], [0, 1, 2, 7], [0, 1, 4, 8], [0, 2, 4, 9], [0, 1, 5, 10], [0, 1, 2, 11], [0, 1, 4, 12], [], [0, 3, 5, 6], [0, 1, 4, 6], [0, 1, 2, 5], [], [0, 2, 3, 4], [0, 1, 4, 8], [0, 1, 2, 5], [0, 1, 2, 5], [0, 1, 2, 6], [], [0, 2, 3, 4], [], [], [], [2, 4, 5, 6], [], [2, 4, 5, 6], [2, 4, 5, 6], [2, 4, 5, 6], [2, 4, 7, 8], [2, 4, 5, 8], [], [2, 5, 6, 10], [2, 4, 6, 11], [2, 4, 5, 12], [2, 4, 5, 6], [5, 6, 7, 11], [4, 6, 7, 8], [2, 5, 7, 8], [2, 6, 8, 10], [2, 4, 7, 11], [4, 5, 8, 10], [2, 4, 5, 6], [2, 5, 6, 10], [2, 4, 6, 8], [2, 4, 5, 8], [2, 4, 5, 6], [4, 5, 6, 10]]

def sh (s : Fin 26) : ℕ := if s.val < 13 then s.val else s.val - 13

def tidx (s t : Fin 26) : ℕ :=
  (if s.val < 13 then 0 else 26) +
    (if t.val < 13 then (t.val + 13 - sh s) % 13 else 13 + (t.val - 13 + 13 - sh s) % 13)

def Wt (s t : Fin 26) : Finset (Fin 13) :=
  ((tab.getD (tidx s t) []).map
    (fun a => (⟨(a + sh s) % 13, Nat.mod_lt _ (by norm_num)⟩ : Fin 13))).toFinset

theorem adj_irr : ∀ s : Fin 26, adjb s s = false := by decide +kernel

theorem adj_symm : ∀ s t : Fin 26, adjb s t = adjb t s := by decide +kernel

theorem hLN : ∀ i j : Fin 26, i ≠ j → (N i ∩ N j).card ≤ 1 := by decide +kernel

theorem degN : ∀ v : Fin 26, (N v).card = 4 := by decide +kernel

theorem adj_total :
    ∑ v : Fin 26, ∑ y : Fin 26, (if adjb v y = true then (1 : ℕ) else 0) = 104 := by
  decide +kernel

theorem adj_no_tri :
    ∀ w x y : Fin 26, adjb w x = true → adjb w y = true → adjb x y = true → False := by
  decide +kernel

theorem accwit : ∀ s t : Fin 26, adjb s t = true →
    (Pp s t - Ll s t ∈ ({0, 1, 3, 9} : Finset (Fin 13))) ∧
      ∀ u : Fin 26, ein (Pp s t) (Ll s t) u = true → (u = s ∨ u = t) := by
  decide +kernel

theorem wit : ∀ s t : Fin 26, adjb s t = false →
    (Wt s t).card = 4 ∧
    (∀ l : Fin 13, ({x ∈ Wt s t | x - l ∈ ({0, 1, 3, 9} : Finset (Fin 13))}).card ≤ 2) ∧
    qin (Wt s t) s = true ∧ qin (Wt s t) t = true := by
  decide +kernel

theorem k22 (s1 s2 t1 t2 : Fin 26) (h11 : adjb s1 t1 = true) (h12 : adjb s1 t2 = true)
    (h21 : adjb s2 t1 = true) (h22 : adjb s2 t2 = true) (hne : s1 ≠ s2) : t1 = t2 := by
  have hc := hLN s1 s2 hne
  rw [Finset.card_le_one] at hc
  exact hc t1 (Finset.mem_inter.2 ⟨(mem_N _ _).2 h11, (mem_N _ _).2 h21⟩) t2
    (Finset.mem_inter.2 ⟨(mem_N _ _).2 h12, (mem_N _ _).2 h22⟩)

theorem bip_star (S T : Finset (Fin 26)) (hST : ∀ s ∈ S, ∀ t ∈ T, adjb s t = true)
    (hS : S.Nonempty) (hT : T.Nonempty) :
    (∃ z : Fin 26, S = {z} ∧ T ⊆ N z) ∨ (∃ z : Fin 26, T = {z} ∧ S ⊆ N z) := by
  obtain ⟨s0, hs0⟩ := hS
  obtain ⟨t0, ht0⟩ := hT
  by_cases h1 : ∀ s ∈ S, s = s0
  · left
    refine ⟨s0, ?_, ?_⟩
    · ext s
      simp only [Finset.mem_singleton]
      exact ⟨h1 s, fun e => e ▸ hs0⟩
    · intro t ht
      exact (mem_N s0 t).2 (hST s0 hs0 t ht)
  · push Not at h1
    obtain ⟨s1, hs1, hne⟩ := h1
    right
    refine ⟨t0, ?_, ?_⟩
    · ext t
      simp only [Finset.mem_singleton]
      constructor
      · intro ht
        exact k22 s1 s0 t t0 (hST s1 hs1 t ht) (hST s1 hs1 t0 ht0)
          (hST s0 hs0 t ht) (hST s0 hs0 t0 ht0) hne
      · intro e
        exact e ▸ ht0
    · intro s hs
      rw [mem_N, adj_symm]
      exact hST s hs t0 ht0

def cOf (v0 : Option (Fin 26)) (v : Fin 26) : Fin 26 → Bool :=
  if v0 = some v then (fun _ => false) else (fun u => decide (u ∉ N v))

def MJ' (gates : List Gate) (v0 : Option (Fin 26)) (A' : Fin 26 → Finset (Fin 26)) (v : Fin 26)
    (g : Fin gates.length) : Prop :=
  Mrg gates (A' v) (cOf v0 v) (fun y u => decide (u = y)) g

open Classical in
noncomputable def MGS' (gates : List Gate) (v0 : Option (Fin 26)) (A' : Fin 26 → Finset (Fin 26)) :
    Finset (Fin gates.length) :=
  Finset.univ.filter (fun g : Fin gates.length => ∃ v, MJ' gates v0 A' v g)

open Classical in
theorem mrg_count_opt (gates : List Gate) (v0 : Option (Fin 26))
    (A' : Fin 26 → Finset (Fin 26)) (o' : Fin 26 → ℕ)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < 26 + (i : ℕ))
    (hA : ∀ v : Fin 26, A' v ⊆ N v)
    (hot : ∀ (v p : Fin 26), p ∈ A' v →
      val gates (o' v) (fun u : Fin 26 => decide (u = p)) = true)
    (hoc : ∀ v : Fin 26, 1 ≤ (A' v).card → val gates (o' v) (cOf v0 v) = false) :
    ∑ v : Fin 26, ((A' v).card - 1) ≤ (MGS' gates v0 A').card := by
  have h1 : ∀ v : Fin 26, (A' v).card - 1 ≤
      ∑ g : Fin gates.length, (if MJ' gates v0 A' v g then (1 : ℕ) else 0) := by
    intro v
    by_cases hc : 1 ≤ (A' v).card
    · exact le_of_eq (mcount gates (A' v) (cOf v0 v) (fun y u => decide (u = y))
        (fun p _ u hu => of_decide_eq_true hu) legal hin hc (o' v) (hoc v hc)
        (fun p hp => hot v p hp)).symm
    · have hz : (A' v).card - 1 = 0 := by omega
      rw [hz]
      exact Nat.zero_le _
  have h2 : ∀ g : Fin gates.length,
      (∑ v : Fin 26, (if MJ' gates v0 A' v g then (1 : ℕ) else 0)) ≤
        (if ∃ v, MJ' gates v0 A' v g then (1 : ℕ) else 0) := by
    intro g
    by_cases hex : ∃ v1 : Fin 26, MJ' gates v0 A' v1 g
    · simp only [hex, ite_true]
      obtain ⟨v1, hv1⟩ := hex
      have hle : ∀ v ∈ (Finset.univ : Finset (Fin 26)),
          (if MJ' gates v0 A' v g then (1 : ℕ) else 0) ≤ (if v = v1 then (1 : ℕ) else 0) := by
        intro v _
        by_cases hv : MJ' gates v0 A' v g
        · have e : v = v1 := by
            by_contra hne
            by_cases h1eq : v0 = some v1
            · have hvneq : v0 ≠ some v := by
                intro he
                rw [h1eq] at he
                exact hne (Option.some.inj he).symm
              have hcv : cOf v0 v = fun u => decide (u ∉ N v) := by simp [cOf, hvneq]
              have hv' : Mrg gates (A' v) (fun u => decide (u ∉ N v)) (fun y u => decide (u = y)) g := by
                simpa [MJ', hcv] using hv
              exact disj_gen gates legal hin (N v1) (N v) (A' v1) (A' v) (cOf v0 v1)
                (hA v1) (hLN v1 v (Ne.symm hne)) g hv1 hv'
            · have hcv1 : cOf v0 v1 = fun u => decide (u ∉ N v1) := by simp [cOf, h1eq]
              have hv1' : Mrg gates (A' v1) (fun u => decide (u ∉ N v1)) (fun y u => decide (u = y)) g := by
                simpa [MJ', hcv1] using hv1
              exact disj_gen gates legal hin (N v) (N v1) (A' v) (A' v1) (cOf v0 v)
                (hA v) (hLN v v1 hne) g hv hv1'
          simp [e, hv1]
        · simp [hv]
      refine (Finset.sum_le_sum hle).trans ?_
      simp
    · have hz : ∀ v ∈ (Finset.univ : Finset (Fin 26)),
          (if MJ' gates v0 A' v g then (1 : ℕ) else 0) = 0 := by
        intro v _
        have hnv : ¬ MJ' gates v0 A' v g := fun h => hex ⟨v, h⟩
        simp [hnv]
      rw [Finset.sum_eq_zero hz]
      exact Nat.zero_le _
  calc ∑ v : Fin 26, ((A' v).card - 1)
      ≤ ∑ v : Fin 26, ∑ g : Fin gates.length, (if MJ' gates v0 A' v g then (1 : ℕ) else 0) :=
        Finset.sum_le_sum (fun v _ => h1 v)
    _ = ∑ g : Fin gates.length, ∑ v : Fin 26, (if MJ' gates v0 A' v g then (1 : ℕ) else 0) :=
        Finset.sum_comm
    _ ≤ ∑ g : Fin gates.length, (if ∃ v, MJ' gates v0 A' v g then (1 : ℕ) else 0) :=
        Finset.sum_le_sum (fun g _ => h2 g)
    _ = (MGS' gates v0 A').card := by
        unfold MGS'
        rw [Finset.card_filter]

def Reach (gs : List Gate) (o : ℕ) (w : ℕ) : Prop :=
  ∀ S : ℕ → Prop, S o →
    (∀ (k : ℕ) (hk : k < gs.length), gs[k].op = GateOp.or → S (26 + k) →
      ∀ a ∈ gs[k].inputs, S a) → S w

theorem reach_out (gs : List Gate) (o : ℕ) : Reach gs o o := fun _ h _ => h

theorem reach_step (gs : List Gate) (o : ℕ) (k : ℕ) (hk : k < gs.length)
    (hop : gs[k].op = GateOp.or) (hr : Reach gs o (26 + k)) (a : ℕ) (ha : a ∈ gs[k].inputs) :
    Reach gs o a :=
  fun S h0 hs => hs k hk hop (hr S h0 hs) a ha

theorem reach_up (gs : List Gate) (o : ℕ)
    (hin : ∀ i : Fin gs.length, ∀ a ∈ (gs.get i).inputs, a < 26 + (i : ℕ))
    (w : ℕ) (hr : Reach gs o w) :
    ∀ x : Fin 26 → Bool, val gs w x = true → val gs o x = true := by
  apply hr (fun w => ∀ x : Fin 26 → Bool, val gs w x = true → val gs o x = true)
  · intro x h
    exact h
  · intro k hk hop hS a ha x hx
    exact hS x ((val_or gs x k hk hop).2 ⟨a, ha, hin ⟨k, hk⟩ a ha, hx⟩)

theorem reach_down (gs : List Gate) (o : ℕ)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x : Fin 26 → Bool) :
    ∀ w, Reach gs o w → val gs w x = true →
      ∃ w', Reach gs o w' ∧ val gs w' x = true ∧
        (w' < 26 ∨ ∃ (j : ℕ) (hj : j < gs.length), w' = 26 + j ∧ gs[j].op = GateOp.and) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hr hx
    by_cases hwn : w < 26
    · exact ⟨w, hr, hx, Or.inl hwn⟩
    · by_cases hbig : 26 + gs.length ≤ w
      · rw [val_big gs x w hbig] at hx
        exact Bool.noConfusion hx
      · have hi : w - 26 < gs.length := by omega
        have he : 26 + (w - 26) = w := by omega
        rcases (legal gs[w - 26] (List.getElem_mem hi)).1 with ha | ho
        · exact ⟨w, hr, hx, Or.inr ⟨w - 26, hi, he.symm, ha⟩⟩
        · have hx' : val gs (26 + (w - 26)) x = true := by rw [he]; exact hx
          have hr' : Reach gs o (26 + (w - 26)) := by rw [he]; exact hr
          obtain ⟨a, ha, halt, hav⟩ := (val_or gs x (w - 26) hi ho).1 hx'
          exact ih a (by omega) (reach_step gs o (w - 26) hi ho hr' a ha) hav

theorem reach_parent (gs : List Gate) (o : ℕ) (w : ℕ) (hr : Reach gs o w) :
    w = o ∨ ∃ (k : ℕ) (hk : k < gs.length), gs[k].op = GateOp.or ∧ Reach gs o (26 + k) ∧
      w ∈ gs[k].inputs := by
  apply hr (fun w => w = o ∨ ∃ (k : ℕ) (hk : k < gs.length), gs[k].op = GateOp.or ∧
    Reach gs o (26 + k) ∧ w ∈ gs[k].inputs)
  · exact Or.inl rfl
  · intro k hk hop hS a ha
    right
    refine ⟨k, hk, hop, ?_, ha⟩
    rcases hS with h | ⟨k', hk', hop', hr', hmem⟩
    · rw [h]
      exact reach_out gs o
    · exact reach_step gs o k' hk' hop' hr' _ hmem

open Classical in
theorem top_count (gs : List Gate) (o : ℕ)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (U RO : Finset (Fin gs.length))
    (hU : ∀ j ∈ U, (gs.get j).op = GateOp.and ∧ Reach gs o (26 + (j : ℕ)))
    (hRO : ∀ j, j ∈ RO ↔ ((gs.get j).op = GateOp.or ∧ Reach gs o (26 + (j : ℕ)))) :
    U.card ≤ RO.card + 1 := by
  have hdisj : Disjoint U RO := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    have a1 := (hU j h1).1
    have a2 := ((hRO j).1 h2).1
    rw [a1] at a2
    exact GateOp.noConfusion a2
  have hsub : (U ∪ RO).image (fun j : Fin gs.length => 26 + (j : ℕ)) ⊆
      insert o (RO.biUnion (fun k => (gs.get k).inputs.toFinset)) := by
    intro w hw
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hw
    have hr : Reach gs o (26 + (j : ℕ)) := by
      rcases Finset.mem_union.1 hj with h | h
      · exact (hU j h).2
      · exact ((hRO j).1 h).2
    rcases reach_parent gs o _ hr with h | ⟨k, hk, hop, hrk, hmem⟩
    · rw [h]
      exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      rw [Finset.mem_biUnion]
      exact ⟨⟨k, hk⟩, (hRO ⟨k, hk⟩).2 ⟨hop, hrk⟩, List.mem_toFinset.2 hmem⟩
  have hinj : Function.Injective (fun j : Fin gs.length => 26 + (j : ℕ)) := by
    intro a b h
    apply Fin.ext
    simpa using h
  have hc1 : ((U ∪ RO).image (fun j : Fin gs.length => 26 + (j : ℕ))).card
      = U.card + RO.card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_union_of_disjoint hdisj]
  have hc2 : (RO.biUnion (fun k => (gs.get k).inputs.toFinset)).card ≤ RO.card * 2 := by
    refine Finset.card_biUnion_le.trans ?_
    refine (Finset.sum_le_card_nsmul _ _ 2 ?_).trans (by simp)
    intro k _
    exact (List.toFinset_card_le _).trans (legal _ (List.getElem_mem k.2)).2
  have hc3 := Finset.card_le_card hsub
  have hc4 := Finset.card_insert_le o (RO.biUnion (fun k => (gs.get k).inputs.toFinset))
  omega

def Hy0 (gs : List Gate) (o : ℕ) : Prop :=
  (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
  (∀ g ∈ gs, g.inputs.length = 2) ∧
  (∀ i : Fin gs.length, ∀ a ∈ (gs.get i).inputs, a < 26 + (i : ℕ)) ∧
  (∀ s t : Fin 26, adjb s t = true → val gs o (pr s t) = true) ∧
  (∀ s t : Fin 26, adjb s t = false → val gs o (pr s t) = false)

theorem reach_adj (gs : List Gate) (o : ℕ) (H : Hy0 gs o) (w : ℕ) (hr : Reach gs o w)
    (s t : Fin 26) (h : val gs w (pr s t) = true) : adjb s t = true := by
  have h2 := reach_up gs o H.2.2.1 w hr _ h
  cases hb : adjb s t with
  | true => rfl
  | false =>
    rw [H.2.2.2.2 s t hb] at h2
    exact Bool.noConfusion h2

theorem val_e_pr (gs : List Gate)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (s t u : Fin 26) (hu : u = s ∨ u = t)
    (h : val gs w (fun v : Fin 26 => decide (v = u)) = true) : val gs w (pr s t) = true :=
  val_mono gs legal _ _ (by
    intro v hv
    have e : v = u := of_decide_eq_true hv
    rw [e]
    exact decide_eq_true hu) w h

theorem reach_single (gs : List Gate) (o : ℕ) (H : Hy0 gs o) (w : ℕ) (hr : Reach gs o w)
    (s : Fin 26) (h : val gs w (fun v : Fin 26 => decide (v = s)) = true) : False := by
  have h2 := reach_adj gs o H w hr s s (val_e_pr gs H.1 w s s s (Or.inl rfl) h)
  rw [adj_irr s] at h2
  exact Bool.noConfusion h2

open Classical in
noncomputable def US (gs : List Gate) (o : ℕ) : Finset (Fin gs.length) :=
  Finset.univ.filter (fun j => (gs.get j).op = GateOp.and ∧ Reach gs o (26 + (j : ℕ)) ∧
    ∃ s t : Fin 26, val gs (26 + (j : ℕ)) (pr s t) = true)

open Classical in
noncomputable def ROS (gs : List Gate) (o : ℕ) : Finset (Fin gs.length) :=
  Finset.univ.filter (fun j => (gs.get j).op = GateOp.or ∧ Reach gs o (26 + (j : ℕ)))

open Classical in
theorem mem_US (gs : List Gate) (o : ℕ) (j : Fin gs.length) :
    j ∈ US gs o ↔ ((gs.get j).op = GateOp.and ∧ Reach gs o (26 + (j : ℕ)) ∧
      ∃ s t : Fin 26, val gs (26 + (j : ℕ)) (pr s t) = true) := by
  unfold US
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

open Classical in
theorem mem_ROS (gs : List Gate) (o : ℕ) (j : Fin gs.length) :
    j ∈ ROS gs o ↔ ((gs.get j).op = GateOp.or ∧ Reach gs o (26 + (j : ℕ))) := by
  unfold ROS
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem cover (gs : List Gate) (o : ℕ) (H : Hy0 gs o) (v y : Fin 26) (hadj : adjb v y = true) :
    ∃ j : Fin gs.length, j ∈ US gs o ∧ val gs (26 + (j : ℕ)) (pr v y) = true := by
  have hout := H.2.2.2.1 v y hadj
  obtain ⟨w, hr, hx, hw⟩ := reach_down gs o H.1 (pr v y) o (reach_out gs o) hout
  rcases hw with hw | ⟨j, hj, e, hop⟩
  · exfalso
    apply reach_single gs o H w hr ⟨w, hw⟩
    rw [val_input gs _ w hw]
    simp
  · rw [e] at hr hx
    exact ⟨⟨j, hj⟩, (mem_US gs o _).2 ⟨hop, hr, v, y, hx⟩, hx⟩

theorem arith_gen (b c m e : ℕ) (h4 : b ≤ 4) (hm : b ≤ c * m + e)
    (he : e = 0 ∨ (e = 1 ∧ 1 ≤ c ∧ 2 ≤ m)) :
    5 * b ≤ 4 * (2 * c + (m - 1) + e) := by
  rcases he with rfl | ⟨rfl, hc, hm2⟩
  · rcases c with _ | _ | _ | c
    · simp at hm; omega
    · simp at hm; omega
    · rcases m with _ | _ | m <;> omega
    · omega
  · rcases c with _ | _ | c
    · omega
    · simp at hm; omega
    · omega

theorem tally_gen {ι : Type} [DecidableEq ι] (U : Finset ι) (z : ι → Fin 26)
    (A : ι → Finset (Fin 26)) (A' : Fin 26 → Finset (Fin 26)) (e : Fin 26 → ℕ)
    (h1 : ∀ k ∈ U, A k ⊆ N (z k))
    (h2 : ∀ v : Fin 26, (∑ k ∈ U.filter (fun k => z k = v), (A k).card) ≤
      (U.filter (fun k => z k = v)).card * (A' v).card + e v)
    (h3 : ∀ v : Fin 26, e v = 0 ∨ (e v = 1 ∧ 1 ≤ (U.filter (fun k => z k = v)).card ∧ 2 ≤ (A' v).card))
    (h4 : ∀ v y : Fin 26, adjb v y = true →
      ∃ k ∈ U, (v = z k ∧ y ∈ A k) ∨ (y = z k ∧ v ∈ A k)) :
    260 ≤ 8 * U.card + 4 * (∑ v : Fin 26, ((A' v).card - 1)) + 4 * (∑ v : Fin 26, e v) := by
  obtain ⟨B, hB⟩ : ∃ B : Fin 26 → Finset (Fin 26),
      ∀ v, B v = (U.filter (fun k => z k = v)).biUnion A := ⟨_, fun _ => rfl⟩
  have hB4 : ∀ v, (B v).card ≤ 4 := by
    intro v
    rw [← degN v, hB v]
    apply Finset.card_le_card
    intro y hy
    obtain ⟨k, hk, hyk⟩ := Finset.mem_biUnion.1 hy
    rw [Finset.mem_filter] at hk
    rw [← hk.2]
    exact h1 k hk.1 hyk
  have hBm : ∀ v, (B v).card ≤ (U.filter (fun k => z k = v)).card * (A' v).card + e v := by
    intro v
    rw [hB v]
    exact Finset.card_biUnion_le.trans (h2 v)
  have hv : ∀ v, 5 * (B v).card ≤
      4 * (2 * (U.filter (fun k => z k = v)).card + ((A' v).card - 1) + e v) :=
    fun v => arith_gen _ _ _ _ (hB4 v) (hBm v) (h3 v)
  have hpt : ∀ v y : Fin 26, (if adjb v y = true then (1 : ℕ) else 0) ≤
      (if y ∈ B v then (1 : ℕ) else 0) + (if v ∈ B y then (1 : ℕ) else 0) := by
    intro v y
    by_cases hadj : adjb v y = true
    · obtain ⟨k, hk, h | h⟩ := h4 v y hadj
      · have hm : y ∈ B v := by
          rw [hB v]
          exact Finset.mem_biUnion.2 ⟨k, Finset.mem_filter.2 ⟨hk, h.1.symm⟩, h.2⟩
        simp [hadj, hm]
      · have hm : v ∈ B y := by
          rw [hB y]
          exact Finset.mem_biUnion.2 ⟨k, Finset.mem_filter.2 ⟨hk, h.1.symm⟩, h.2⟩
        simp [hadj, hm]
    · simp [hadj]
  have hsumB : ∀ v : Fin 26, ∑ y : Fin 26, (if y ∈ B v then (1 : ℕ) else 0) = (B v).card := by
    intro v; simp
  have hsumB' : ∑ v : Fin 26, ∑ y : Fin 26, (if v ∈ B y then (1 : ℕ) else 0)
      = ∑ y : Fin 26, (B y).card := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun y _ => hsumB y)
  have h104 : 104 ≤ 2 * ∑ v : Fin 26, (B v).card := by
    calc 104 = ∑ v : Fin 26, ∑ y : Fin 26, (if adjb v y = true then (1 : ℕ) else 0) :=
          adj_total.symm
      _ ≤ ∑ v : Fin 26, ∑ y : Fin 26,
            ((if y ∈ B v then (1 : ℕ) else 0) + (if v ∈ B y then (1 : ℕ) else 0)) :=
          Finset.sum_le_sum (fun v _ => Finset.sum_le_sum (fun y _ => hpt v y))
      _ = (∑ v : Fin 26, (B v).card) + ∑ y : Fin 26, (B y).card := by
          simp only [Finset.sum_add_distrib]
          rw [hsumB', Finset.sum_congr rfl (fun v _ => hsumB v)]
      _ = 2 * ∑ v : Fin 26, (B v).card := by ring
  have hU : U.card = ∑ v : Fin 26, (U.filter (fun k => z k = v)).card :=
    Finset.card_eq_sum_card_fiberwise (fun k _ => Finset.mem_univ (z k))
  have hfin : ∑ v : Fin 26, 5 * (B v).card ≤ ∑ v : Fin 26,
      4 * (2 * (U.filter (fun k => z k = v)).card + ((A' v).card - 1) + e v) :=
    Finset.sum_le_sum (fun v _ => hv v)
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← hU] at hfin
  omega

open Classical in
theorem master_64 {ι : Type} (gs : List Gate) (o : ℕ) (H : Hy0 gs o)
    (U : Finset ι) (z : ι → Fin 26) (A : ι → Finset (Fin 26))
    (A' : Fin 26 → Finset (Fin 26)) (o' : Fin 26 → ℕ)
    (v0 : Option (Fin 26)) (e : Fin 26 → ℕ) (E : Finset (Fin gs.length))
    (h1 : ∀ k ∈ U, A k ⊆ N (z k))
    (h2 : ∀ v : Fin 26, (∑ k ∈ U.filter (fun k => z k = v), (A k).card) ≤
      (U.filter (fun k => z k = v)).card * (A' v).card + e v)
    (h3 : ∀ v : Fin 26, e v = 0 ∨ (e v = 1 ∧ 1 ≤ (U.filter (fun k => z k = v)).card ∧ 2 ≤ (A' v).card))
    (h4 : ∀ v y : Fin 26, adjb v y = true →
      ∃ k ∈ U, (v = z k ∧ y ∈ A k) ∨ (y = z k ∧ v ∈ A k))
    (hA' : ∀ v : Fin 26, A' v ⊆ N v)
    (hot : ∀ (v p : Fin 26), p ∈ A' v →
      val gs (o' v) (fun u : Fin 26 => decide (u = p)) = true)
    (hoc : ∀ v : Fin 26, 1 ≤ (A' v).card → val gs (o' v) (cOf v0 v) = false)
    (hE : ∀ g ∈ E, g ∉ US gs o ∧ g ∉ ROS gs o ∧ ∀ v, ¬ MJ' gs v0 A' v g)
    (hbudget : 2 * U.card + ∑ v : Fin 26, e v ≤ 2 * (US gs o).card + E.card) :
    64 ≤ gs.length := by
  have hmc := mrg_count_opt gs v0 A' o' H.1 H.2.2.1 hA' hot hoc
  have htl := tally_gen U z A A' e h1 h2 h3 h4
  have htop := top_count gs o H.1 (US gs o) (ROS gs o)
    (fun k hk => ⟨((mem_US gs o k).1 hk).1, ((mem_US gs o k).1 hk).2.1⟩) (mem_ROS gs o)
  have hd1 : Disjoint (US gs o) (ROS gs o) := by
    rw [Finset.disjoint_left]
    intro g h1' h2'
    have a1 := ((mem_US gs o g).1 h1').1
    have a2 := ((mem_ROS gs o g).1 h2').1
    rw [a1] at a2
    exact GateOp.noConfusion a2
  have hd2 : Disjoint (US gs o ∪ ROS gs o) (MGS' gs v0 A') := by
    rw [Finset.disjoint_left]
    intro g hg hm
    obtain ⟨_, v, hmj⟩ := Finset.mem_filter.1 hm
    obtain ⟨ho, _, w1, w2, hab, r, _, _, _, hv1, _⟩ := hmj
    rcases Finset.mem_union.1 hg with h | h
    · have a1 := ((mem_US gs o g).1 h).1
      rw [a1] at ho
      exact GateOp.noConfusion ho
    · have hr := ((mem_ROS gs o g).1 h).2
      have hm1 : w1 ∈ (gs.get g).inputs := by rw [hab]; simp
      exact reach_single gs o H _ hr r
        ((val_or gs _ g g.2 ho).2 ⟨w1, hm1, H.2.2.1 g w1 hm1, hv1⟩)
  have hd3 : Disjoint (US gs o ∪ ROS gs o ∪ MGS' gs v0 A') E := by
    rw [Finset.disjoint_left]
    intro g hg he
    obtain ⟨hnu, hnr, hnm⟩ := hE g he
    rcases Finset.mem_union.1 hg with h | h
    · rcases Finset.mem_union.1 h with h' | h'
      · exact hnu h'
      · exact hnr h'
    · obtain ⟨_, v, hmj⟩ := Finset.mem_filter.1 h
      exact hnm v hmj
  have hcard : (US gs o ∪ ROS gs o ∪ MGS' gs v0 A' ∪ E).card ≤ gs.length := by
    simpa using Finset.card_le_univ (US gs o ∪ ROS gs o ∪ MGS' gs v0 A' ∪ E)
  rw [Finset.card_union_of_disjoint hd3, Finset.card_union_of_disjoint hd2,
    Finset.card_union_of_disjoint hd1] at hcard
  omega

open Classical in
theorem master_simple {ι : Type} (gs : List Gate) (o : ℕ) (H : Hy0 gs o)
    (U : Finset ι) (z : ι → Fin 26) (A : ι → Finset (Fin 26)) (lw : ι → ℕ)
    (v0 : Option (Fin 26)) (E : Finset (Fin gs.length))
    (h1 : ∀ k ∈ U, A k ⊆ N (z k))
    (h2 : ∀ k ∈ U, ∀ p ∈ A k, val gs (lw k) (fun u : Fin 26 => decide (u = p)) = true)
    (h3 : ∀ k ∈ U, 1 ≤ (A k).card → val gs (lw k) (cOf v0 (z k)) = false)
    (h4 : ∀ v y : Fin 26, adjb v y = true →
      ∃ k ∈ U, (v = z k ∧ y ∈ A k) ∨ (y = z k ∧ v ∈ A k))
    (hE : ∀ g ∈ E, g ∉ US gs o ∧ g ∉ ROS gs o ∧
      ∀ (v : Fin 26) (Av : Finset (Fin 26)), Av ⊆ N v →
        ¬ Mrg gs Av (cOf v0 v) (fun y u => decide (u = y)) g)
    (hbudget : 2 * U.card ≤ 2 * (US gs o).card + E.card) :
    64 ≤ gs.length := by
  have hmax : ∀ v : Fin 26, ∃ (A' : Finset (Fin 26)) (o' : ℕ), A' ⊆ N v ∧
      (∀ p : Fin 26, p ∈ A' → val gs o' (fun u : Fin 26 => decide (u = p)) = true) ∧
      (1 ≤ A'.card → val gs o' (cOf v0 v) = false) ∧
      (∀ k ∈ U, z k = v → (A k).card ≤ A'.card) := by
    intro v
    by_cases hne : (U.filter (fun k => z k = v)).Nonempty
    · obtain ⟨k0, hk0, hmx⟩ := Finset.exists_max_image _ (fun k => (A k).card) hne
      rw [Finset.mem_filter] at hk0
      refine ⟨A k0, lw k0, ?_, h2 k0 hk0.1, ?_, fun k hk hz => hmx k (Finset.mem_filter.2 ⟨hk, hz⟩)⟩
      · rw [← hk0.2]; exact h1 k0 hk0.1
      · rw [← hk0.2]; exact h3 k0 hk0.1
    · refine ⟨∅, 0, Finset.empty_subset _, by simp, by simp, ?_⟩
      intro k hk hz
      exact absurd ⟨k, Finset.mem_filter.2 ⟨hk, hz⟩⟩ hne
  choose A' o' hA' hot hoc hle using hmax
  refine master_64 gs o H U z A A' o' v0 (fun _ => 0) E h1 ?_ (fun _ => Or.inl rfl) h4
    hA' hot hoc (fun g hg => ⟨(hE g hg).1, (hE g hg).2.1, fun v => (hE g hg).2.2 v (A' v) (hA' v)⟩)
    (by simpa using hbudget)
  intro v
  simp only [Nat.add_zero]
  refine (Finset.sum_le_card_nsmul _ _ (A' v).card ?_).trans (by simp)
  intro k hk
  rw [Finset.mem_filter] at hk
  exact hle v k hk.1 hk.2

def HasI (C : Circuit) (i0 w : ℕ) : Prop :=
  w = 26 + i0 ∨ (26 ≤ w ∧ w - 26 < C.gates.length ∧ InCone 26 C i0 (w - 26))

def NoOtherAnd (C : Circuit) (i0 w : ℕ) : Prop :=
  (26 ≤ w → w - 26 < C.gates.length → w - 26 ≠ i0 → (gateAt C (w - 26)).op = GateOp.or) ∧
  (26 ≤ w → w - 26 < C.gates.length → ∀ k, InCone 26 C k (w - 26) → k ≠ i0 →
    (gateAt C k).op ≠ GateOp.and)

lemma noOtherAnd_child (C : Circuit) (i0 k a : ℕ)
    (legal : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hk : k < C.gates.length) (hno : NoOtherAnd C i0 (26 + k)) (ha : a ∈ C.gates[k].inputs)
    (halt : a < 26 + k) : NoOtherAnd C i0 a := by
  have hga : a ∈ (gateAt C k).inputs := by rw [gateAt_eq C k hk]; exact ha
  have h1 : ∀ m, InCone 26 C m k → m ≠ i0 → (gateAt C m).op ≠ GateOp.and := by
    intro m hm hne
    have h2 := hno.2 (by omega) (by omega) m
    have he : 26 + k - 26 = k := by omega
    rw [he] at h2
    exact h2 hm hne
  refine ⟨?_, ?_⟩
  · intro ha26 hai hne
    have hic : InCone 26 C (a - 26) k :=
      (inCone_iff 26 C (a - 26) k hk).2 ⟨a, hga, ha26, halt, Or.inl rfl⟩
    have hna := h1 (a - 26) hic hne
    rw [gateAt_eq C (a - 26) hai] at hna ⊢
    rcases (legal _ (List.getElem_mem hai)).1 with h | h
    · exact absurd h hna
    · exact h
  · intro ha26 hai m hm hne
    have hic : InCone 26 C m k :=
      (inCone_iff 26 C m k hk).2 ⟨a, hga, ha26, halt, Or.inr hm⟩
    exact h1 m hic hne

lemma hasI_or_iff (C : Circuit) (i0 k a b : ℕ)
    (hk : k < C.gates.length) (hkne : k ≠ i0) (hab : C.gates[k].inputs = [a, b])
    (ha : a < 26 + k) (hb : b < 26 + k) :
    HasI C i0 (26 + k) ↔ HasI C i0 a ∨ HasI C i0 b := by
  have hga : (gateAt C k).inputs = [a, b] := by rw [gateAt_eq C k hk]; exact hab
  unfold HasI
  have he : 26 + k - 26 = k := by omega
  rw [he]
  constructor
  · rintro (h | ⟨_, _, hc⟩)
    · omega
    · obtain ⟨w, hw, hw26, hwlt, hw'⟩ := (inCone_iff 26 C i0 k hk).1 hc
      rw [hga] at hw
      rcases List.mem_pair.1 hw with rfl | rfl
      · left
        rcases hw' with h1 | h2
        · left; omega
        · right; exact ⟨hw26, by omega, h2⟩
      · right
        rcases hw' with h1 | h2
        · left; omega
        · right; exact ⟨hw26, by omega, h2⟩
  · rintro ((rfl | ⟨ha26, _, hca⟩) | (rfl | ⟨hb26, _, hcb⟩))
    · right
      refine ⟨by omega, hk, (inCone_iff 26 C i0 k hk).2 ⟨26 + i0, by rw [hga]; simp, by omega, ha, Or.inl (by omega)⟩⟩
    · right
      refine ⟨by omega, hk, (inCone_iff 26 C i0 k hk).2 ⟨a, by rw [hga]; simp, ha26, ha, Or.inr hca⟩⟩
    · right
      refine ⟨by omega, hk, (inCone_iff 26 C i0 k hk).2 ⟨26 + i0, by rw [hga]; simp, by omega, hb, Or.inl (by omega)⟩⟩
    · right
      refine ⟨by omega, hk, (inCone_iff 26 C i0 k hk).2 ⟨b, by rw [hga]; simp, hb26, hb, Or.inr hcb⟩⟩

lemma decomp_wire (C : Circuit) (i0 : ℕ)
    (legal : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hlen2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hin : ∀ k : Fin C.gates.length, ∀ a ∈ (C.gates.get k).inputs, a < 26 + (k : ℕ)) :
    ∀ w, NoOtherAnd C i0 w →
      ∃ S : Finset (Fin 26), ∀ x : Fin 26 → Bool,
        val C.gates w x = true ↔ (HasI C i0 w ∧ val C.gates (26 + i0) x = true) ∨
          ∃ v ∈ S, x v = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hno
    by_cases hwn : w < 26
    · refine ⟨{⟨w, hwn⟩}, fun x => ?_⟩
      have hnh : ¬ HasI C i0 w := by
        rintro (h | ⟨h, _⟩) <;> omega
      rw [val_input C.gates x w hwn]
      simp [hnh]
    · by_cases hbig : 26 + C.gates.length ≤ w
      · refine ⟨∅, fun x => ?_⟩
        rw [val_big C.gates x w hbig]
        by_cases hhi : HasI C i0 w
        · rcases hhi with rfl | ⟨_, hlt, _⟩
          · rw [val_big C.gates x (26 + i0) hbig]; simp
          · omega
        · simp [hhi]
      · have hk : w - 26 < C.gates.length := by omega
        have he : 26 + (w - 26) = w := by omega
        by_cases hki : w - 26 = i0
        · refine ⟨∅, fun x => ?_⟩
          have hw : w = 26 + i0 := by omega
          rw [hw]
          simp [HasI]
        · have hor : C.gates[w - 26].op = GateOp.or := by
            have := hno.1 (by omega) hk hki
            rw [gateAt_eq C (w - 26) hk] at this
            exact this
          obtain ⟨a, b, hab⟩ := List.length_eq_two.1 (hlen2 _ (List.getElem_mem hk))
          have hma : a ∈ C.gates[w - 26].inputs := by rw [hab]; simp
          have hmb : b ∈ C.gates[w - 26].inputs := by rw [hab]; simp
          have ha : a < 26 + (w - 26) := hin ⟨w - 26, hk⟩ a hma
          have hb : b < 26 + (w - 26) := hin ⟨w - 26, hk⟩ b hmb
          have hno' : NoOtherAnd C i0 (26 + (w - 26)) := by rw [he]; exact hno
          have hnoa := noOtherAnd_child C i0 (w - 26) a legal hk hno' hma ha
          have hnob := noOtherAnd_child C i0 (w - 26) b legal hk hno' hmb hb
          obtain ⟨Sa, hSa⟩ := ih a (by omega) hnoa
          obtain ⟨Sb, hSb⟩ := ih b (by omega) hnob
          refine ⟨Sa ∪ Sb, fun x => ?_⟩
          have hI := hasI_or_iff C i0 (w - 26) a b hk hki hab ha hb
          rw [← he, hI, val_or C.gates x (w - 26) hk hor]
          constructor
          · rintro ⟨u, hu, _, hvu⟩
            rw [hab] at hu
            rcases List.mem_pair.1 hu with rfl | rfl
            · rcases (hSa x).1 hvu with ⟨h1, h2⟩ | ⟨v, hv, hxv⟩
              · exact Or.inl ⟨Or.inl h1, h2⟩
              · exact Or.inr ⟨v, Finset.mem_union_left _ hv, hxv⟩
            · rcases (hSb x).1 hvu with ⟨h1, h2⟩ | ⟨v, hv, hxv⟩
              · exact Or.inl ⟨Or.inr h1, h2⟩
              · exact Or.inr ⟨v, Finset.mem_union_right _ hv, hxv⟩
          · rintro (⟨h1 | h1, h2⟩ | ⟨v, hv, hxv⟩)
            · exact ⟨a, hma, ha, (hSa x).2 (Or.inl ⟨h1, h2⟩)⟩
            · exact ⟨b, hmb, hb, (hSb x).2 (Or.inl ⟨h1, h2⟩)⟩
            · rcases Finset.mem_union.1 hv with hv | hv
              · exact ⟨a, hma, ha, (hSa x).2 (Or.inr ⟨v, hv, hxv⟩)⟩
              · exact ⟨b, hmb, hb, (hSb x).2 (Or.inr ⟨v, hv, hxv⟩)⟩

lemma mix_gate (C : Circuit) (i0 : ℕ)
    (legal : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hlen2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hin : ∀ k : Fin C.gates.length, ∀ a ∈ (C.gates.get k).inputs, a < 26 + (k : ℕ))
    (hi0z : ∀ r : Fin 26, val C.gates (26 + i0) (fun u => decide (u = r)) = false) :
    ∀ w, HasI C i0 w → NoOtherAnd C i0 w →
      (∃ r : Fin 26, val C.gates w (fun u => decide (u = r)) = true) →
      ∃ m : Fin C.gates.length, (C.gates.get m).op = GateOp.or ∧
        (∃ r : Fin 26, val C.gates (26 + (m : ℕ)) (fun u => decide (u = r)) = true) ∧
        ∃ w1 w2 : ℕ, (C.gates.get m).inputs = [w1, w2] ∧
          ((∀ r : Fin 26, val C.gates w1 (fun u => decide (u = r)) = false) ∨
           (∀ r : Fin 26, val C.gates w2 (fun u => decide (u = r)) = false)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rintro hI hno ⟨r0, hr0⟩
    have hne0 : w ≠ 26 + i0 := by
      intro e
      rw [e, hi0z r0] at hr0
      exact Bool.noConfusion hr0
    rcases hI with rfl | ⟨hw26, hk, hcone⟩
    · exact absurd rfl hne0
    · have he : 26 + (w - 26) = w := by omega
      have hki : w - 26 ≠ i0 := by omega
      have hor : C.gates[w - 26].op = GateOp.or := by
        have := hno.1 hw26 hk hki
        rw [gateAt_eq C (w - 26) hk] at this
        exact this
      obtain ⟨a, b, hab⟩ := List.length_eq_two.1 (hlen2 _ (List.getElem_mem hk))
      have hma : a ∈ C.gates[w - 26].inputs := by rw [hab]; simp
      have hmb : b ∈ C.gates[w - 26].inputs := by rw [hab]; simp
      have ha : a < 26 + (w - 26) := hin ⟨w - 26, hk⟩ a hma
      have hb : b < 26 + (w - 26) := hin ⟨w - 26, hk⟩ b hmb
      have hno' : NoOtherAnd C i0 (26 + (w - 26)) := by rw [he]; exact hno
      have hI' : HasI C i0 (26 + (w - 26)) := by rw [he]; exact Or.inr ⟨hw26, hk, hcone⟩
      rcases (hasI_or_iff C i0 (w - 26) a b hk hki hab ha hb).1 hI' with hIa | hIb
      · by_cases hta : ∃ r : Fin 26, val C.gates a (fun u => decide (u = r)) = true
        · exact ih a (by omega) hIa (noOtherAnd_child C i0 (w - 26) a legal hk hno' hma ha) hta
        · refine ⟨⟨w - 26, hk⟩, hor, ⟨r0, by rw [he]; exact hr0⟩, a, b, hab, Or.inl ?_⟩
          intro r
          cases hv : val C.gates a (fun u => decide (u = r)) with
          | false => rfl
          | true => exact absurd ⟨r, hv⟩ hta
      · by_cases htb : ∃ r : Fin 26, val C.gates b (fun u => decide (u = r)) = true
        · exact ih b (by omega) hIb (noOtherAnd_child C i0 (w - 26) b legal hk hno' hmb hb) htb
        · refine ⟨⟨w - 26, hk⟩, hor, ⟨r0, by rw [he]; exact hr0⟩, a, b, hab, Or.inr ?_⟩
          intro r
          cases hv : val C.gates b (fun u => decide (u = r)) with
          | false => rfl
          | true => exact absurd ⟨r, hv⟩ htb

open Classical in
lemma cross_gate (gs : List Gate)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hlen2 : ∀ g ∈ gs, g.inputs.length = 2)
    (hin : ∀ k : Fin gs.length, ∀ a ∈ (gs.get k).inputs, a < 26 + (k : ℕ))
    (w : ℕ) (x y : Fin 26) (hxy : adjb x y = true)
    (hx : val gs w (fun u => decide (u = x)) = true)
    (hy : val gs w (fun u => decide (u = y)) = true) :
    ∃ m : Fin gs.length, (gs.get m).op = GateOp.or ∧
      val gs (26 + (m : ℕ)) (fun u => decide (u = x)) = true ∧
      val gs (26 + (m : ℕ)) (fun u => decide (u = y)) = true := by
  have hne : x ≠ y := by
    intro e
    rw [e, adj_irr] at hxy
    exact Bool.noConfusion hxy
  have hmc := mcount gs ({x, y} : Finset (Fin 26)) (fun _ => false)
    (fun p u => decide (u = p)) (fun p _ u hu => of_decide_eq_true hu) legal hin
    (by rw [Finset.card_pair hne]; omega) w (val_zero gs legal hlen2 w) (by
      intro p hp
      rw [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact hx
      · exact hy)
  rw [Finset.card_pair hne] at hmc
  have hex : ∃ m : Fin gs.length,
      Mrg gs ({x, y} : Finset (Fin 26)) (fun _ => false) (fun p u => decide (u = p)) m := by
    by_contra hnone
    have hz : (∑ g : Fin gs.length,
        if Mrg gs ({x, y} : Finset (Fin 26)) (fun _ => false) (fun p u => decide (u = p)) g
        then (1 : ℕ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro g _
      have hng : ¬ Mrg gs ({x, y} : Finset (Fin 26)) (fun _ => false) (fun p u => decide (u = p)) g :=
        fun h => hnone ⟨g, h⟩
      simp [hng]
    rw [hz] at hmc
    omega
  obtain ⟨m, ho, _, w1, w2, hab, r, hr, r', hr', hv1, hv2, X, hrX, hr'X, _⟩ := hex
  have hrr' : r ≠ r' := fun e => hr'X (e ▸ hrX)
  have hm1 : w1 ∈ (gs.get m).inputs := by rw [hab]; simp
  have hm2 : w2 ∈ (gs.get m).inputs := by rw [hab]; simp
  have ht1 : val gs (26 + (m : ℕ)) (fun u => decide (u = r)) = true :=
    (val_or gs _ m m.2 ho).2 ⟨w1, hm1, hin m w1 hm1, hv1⟩
  have ht2 : val gs (26 + (m : ℕ)) (fun u => decide (u = r')) = true :=
    (val_or gs _ m m.2 ho).2 ⟨w2, hm2, hin m w2 hm2, hv2⟩
  rw [Finset.mem_insert, Finset.mem_singleton] at hr hr'
  refine ⟨m, ho, ?_, ?_⟩
  · rcases hr with rfl | rfl <;> rcases hr' with rfl | rfl
    · exact absurd rfl hrr'
    · exact ht1
    · exact ht2
    · exact absurd rfl hrr'
  · rcases hr with rfl | rfl <;> rcases hr' with rfl | rfl
    · exact absurd rfl hrr'
    · exact ht2
    · exact ht1
    · exact absurd rfl hrr'

lemma mix_gate_disj (gs : List Gate) (o : ℕ) (H : Hy0 gs o)
    (v0 : Option (Fin 26)) (m : Fin gs.length)
    (hor : (gs.get m).op = GateOp.or)
    (hsing : ∃ r : Fin 26, val gs (26 + (m : ℕ)) (fun u => decide (u = r)) = true)
    (hzero : ∃ w1 w2 : ℕ, (gs.get m).inputs = [w1, w2] ∧
      ((∀ r : Fin 26, val gs w1 (fun u => decide (u = r)) = false) ∨
       (∀ r : Fin 26, val gs w2 (fun u => decide (u = r)) = false))) :
    m ∉ US gs o ∧ m ∉ ROS gs o ∧
      ∀ (v : Fin 26) (Av : Finset (Fin 26)), Av ⊆ N v →
        ¬ Mrg gs Av (cOf v0 v) (fun y u => decide (u = y)) m := by
  refine ⟨?_, ?_, ?_⟩
  · intro hm
    have ha := ((mem_US gs o m).1 hm).1
    rw [hor] at ha
    exact GateOp.noConfusion ha
  · intro hm
    obtain ⟨r, hr⟩ := hsing
    exact reach_single gs o H _ ((mem_ROS gs o m).1 hm).2 r hr
  · intro v Av _ hmrg
    obtain ⟨_, _, w1', w2', hab', r, _, r', _, hv1, hv2, _⟩ := hmrg
    obtain ⟨w1, w2, hab, h0⟩ := hzero
    rw [hab] at hab'
    obtain ⟨rfl, rfl⟩ : w1 = w1' ∧ w2 = w2' := by simpa using hab'
    rcases h0 with h0 | h0
    · rw [h0 r] at hv1; exact Bool.noConfusion hv1
    · rw [h0 r'] at hv2; exact Bool.noConfusion hv2

lemma cross_gate_disj (gs : List Gate) (o : ℕ) (H : Hy0 gs o)
    (m : Fin gs.length) (x y : Fin 26) (hxy : adjb x y = true)
    (hor : (gs.get m).op = GateOp.or)
    (hx : val gs (26 + (m : ℕ)) (fun u => decide (u = x)) = true)
    (hy : val gs (26 + (m : ℕ)) (fun u => decide (u = y)) = true) :
    m ∉ US gs o ∧ m ∉ ROS gs o ∧
      ∀ (v : Fin 26) (Av : Finset (Fin 26)), Av ⊆ N v →
        ¬ Mrg gs Av (cOf none v) (fun p u => decide (u = p)) m := by
  refine ⟨?_, ?_, ?_⟩
  · intro hm
    have ha := ((mem_US gs o m).1 hm).1
    rw [hor] at ha
    exact GateOp.noConfusion ha
  · intro hm
    exact reach_single gs o H _ ((mem_ROS gs o m).1 hm).2 x hx
  · intro v Av _ hmrg
    obtain ⟨_, hc, _⟩ := hmrg
    have hc' : val gs (26 + (m : ℕ)) (fun u => decide (u ∉ N v)) = false := by
      simpa [cOf] using hc
    have hxv : x ∈ N v := by
      by_contra hnx
      have hmo := val_mono gs H.1 (fun u => decide (u = x)) (fun u => decide (u ∉ N v))
        (fun u hu => by rw [of_decide_eq_true hu]; exact decide_eq_true hnx) _ hx
      rw [hc'] at hmo
      exact Bool.noConfusion hmo
    have hyv : y ∈ N v := by
      by_contra hny
      have hmo := val_mono gs H.1 (fun u => decide (u = y)) (fun u => decide (u ∉ N v))
        (fun u hu => by rw [of_decide_eq_true hu]; exact decide_eq_true hny) _ hy
      rw [hc'] at hmo
      exact Bool.noConfusion hmo
    exact adj_no_tri v x y ((mem_N v x).1 hxv) ((mem_N v y).1 hyv) hxy

lemma and_gate_disj (gs : List Gate) (o : ℕ) (v0 : Option (Fin 26))
    (g : Fin gs.length) (hand : (gs.get g).op = GateOp.and) (hnu : g ∉ US gs o) :
    g ∉ US gs o ∧ g ∉ ROS gs o ∧
      ∀ (v : Fin 26) (Av : Finset (Fin 26)), Av ⊆ N v →
        ¬ Mrg gs Av (cOf v0 v) (fun p u => decide (u = p)) g := by
  refine ⟨hnu, ?_, ?_⟩
  · intro h
    have ho := ((mem_ROS gs o g).1 h).1
    rw [hand] at ho
    exact GateOp.noConfusion ho
  · intro v Av _ h
    have ho := h.1
    rw [hand] at ho
    exact GateOp.noConfusion ho

lemma star_lin (gs : List Gate) (o : ℕ) (H : Hy0 gs o) (k : Fin gs.length)
    (hk : k ∈ US gs o)
    (hlin : ∀ w ∈ (gs.get k).inputs, ∃ S : Finset (Fin 26),
      ∀ x : Fin 26 → Bool, val gs w x = true ↔ ∃ v ∈ S, x v = true) :
    ∃ (z : Fin 26) (A : Finset (Fin 26)) (lw : ℕ), A ⊆ N z ∧
      (∀ p ∈ A, val gs lw (fun u : Fin 26 => decide (u = p)) = true) ∧
      val gs lw (fun u : Fin 26 => decide (u ∉ N z)) = false ∧
      ∀ s t : Fin 26, val gs (26 + (k : ℕ)) (pr s t) = true →
        (s = z ∧ t ∈ A) ∨ (t = z ∧ s ∈ A) := by
  obtain ⟨hop, hr, s0, t0, h0⟩ := (mem_US gs o k).1 hk
  obtain ⟨a, b, hab⟩ := List.length_eq_two.1 (H.2.1 _ (List.getElem_mem k.2))
  have hma : a ∈ (gs.get k).inputs := by simp [hab]
  have hmb : b ∈ (gs.get k).inputs := by simp [hab]
  have ha : a < 26 + (k : ℕ) := H.2.2.1 k a hma
  have hb : b < 26 + (k : ℕ) := H.2.2.1 k b hmb
  obtain ⟨Sa, hSa⟩ := hlin a hma
  obtain ⟨Sb, hSb⟩ := hlin b hmb
  have hST : ∀ s ∈ Sa, ∀ t ∈ Sb, adjb s t = true := by
    intro s hs t ht
    apply reach_adj gs o H _ hr s t
    apply (val_and gs (pr s t) k k.2 hop).2
    intro w hw
    rw [hab] at hw
    rcases List.mem_pair.1 hw with rfl | rfl
    · exact ⟨ha, (hSa (pr s t)).2 ⟨s, hs, by simp [pr]⟩⟩
    · exact ⟨hb, (hSb (pr s t)).2 ⟨t, ht, by simp [pr]⟩⟩
  have hcov : ∀ s t : Fin 26, val gs (26 + (k : ℕ)) (pr s t) = true →
      (s ∈ Sa ∧ t ∈ Sb) ∨ (t ∈ Sa ∧ s ∈ Sb) := by
    intro s t hst
    have hall := (val_and gs (pr s t) k k.2 hop).1 hst
    obtain ⟨u1, hu1, h1⟩ := (hSa _).1 (hall a hma).2
    obtain ⟨u2, hu2, h2⟩ := (hSb _).1 (hall b hmb).2
    have hadj := hST u1 hu1 u2 hu2
    have hne : u1 ≠ u2 := by
      intro e; rw [e, adj_irr] at hadj; exact Bool.noConfusion hadj
    rcases of_decide_eq_true h1 with rfl | rfl <;> rcases of_decide_eq_true h2 with rfl | rfl
    · exact absurd rfl hne
    · exact Or.inl ⟨hu1, hu2⟩
    · exact Or.inr ⟨hu1, hu2⟩
    · exact absurd rfl hne
  have hSne : Sa.Nonempty := by
    rcases hcov s0 t0 h0 with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact ⟨s0, h1⟩
    · exact ⟨t0, h1⟩
  have hTne : Sb.Nonempty := by
    rcases hcov s0 t0 h0 with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact ⟨t0, h2⟩
    · exact ⟨s0, h2⟩
  rcases bip_star Sa Sb hST hSne hTne with ⟨z, rfl, hsub⟩ | ⟨z, rfl, hsub⟩
  · refine ⟨z, Sb, b, hsub, ?_, ?_, ?_⟩
    · intro p hp
      exact (hSb _).2 ⟨p, hp, by simp⟩
    · cases hv : val gs b (fun u => decide (u ∉ N z)) with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨u, hu, hnu⟩ := (hSb _).1 hv
        exact of_decide_eq_true hnu (hsub hu)
    · intro s t hst
      rcases hcov s t hst with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨Finset.mem_singleton.1 h1, h2⟩
      · exact Or.inr ⟨Finset.mem_singleton.1 h1, h2⟩
  · refine ⟨z, Sa, a, hsub, ?_, ?_, ?_⟩
    · intro p hp
      exact (hSa _).2 ⟨p, hp, by simp⟩
    · cases hv : val gs a (fun u => decide (u ∉ N z)) with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨u, hu, hnu⟩ := (hSa _).1 hv
        exact of_decide_eq_true hnu (hsub hu)
    · intro s t hst
      rcases hcov s t hst with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr ⟨Finset.mem_singleton.1 h2, h1⟩
      · exact Or.inl ⟨Finset.mem_singleton.1 h2, h1⟩

lemma lin_of_other_and (C : Circuit) (i0 j0 : ℕ)
    (hi0and : (gateAt C i0).op = GateOp.and)
    (legal : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hlen2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hin : ∀ k : Fin C.gates.length, ∀ a ∈ (C.gates.get k).inputs, a < 26 + (k : ℕ))
    (huniq : ∀ i' j', (gateAt C i').op = GateOp.and → (gateAt C j').op = GateOp.and →
      InCone 26 C i' j' → i' = i0 ∧ j' = j0)
    (k : Fin C.gates.length) (hop : (C.gates.get k).op = GateOp.and) (hne : (k : ℕ) ≠ j0)
    (w : ℕ) (hw : w ∈ (C.gates.get k).inputs) :
    ∃ S : Finset (Fin 26), ∀ x : Fin 26 → Bool, val C.gates w x = true ↔ ∃ v ∈ S, x v = true := by
  have hgk : (gateAt C k).op = GateOp.and := by rw [gateAt_eq C k k.2]; exact hop
  have hgw : w ∈ (gateAt C k).inputs := by rw [gateAt_eq C k k.2]; exact hw
  have hwlt : w < 26 + (k : ℕ) := hin k w hw
  have hno_all : ∀ m, InCone 26 C m k → (gateAt C m).op ≠ GateOp.and := by
    intro m hm hand
    exact hne (huniq m k hand hgk hm).2
  have hno : NoOtherAnd C i0 w := by
    refine ⟨?_, ?_⟩
    · intro hw26 hwl _
      have hic : InCone 26 C (w - 26) k :=
        (inCone_iff 26 C (w - 26) k k.2).2 ⟨w, hgw, hw26, hwlt, Or.inl rfl⟩
      have hna := hno_all (w - 26) hic
      rw [gateAt_eq C (w - 26) hwl] at hna ⊢
      rcases (legal _ (List.getElem_mem hwl)).1 with h | h
      · exact absurd h hna
      · exact h
    · intro hw26 hwl m hm _
      have hic : InCone 26 C m k :=
        (inCone_iff 26 C m k k.2).2 ⟨w, hgw, hw26, hwlt, Or.inr hm⟩
      exact hno_all m hic
  have hnh : ¬ HasI C i0 w := by
    rintro (rfl | ⟨hw26, hwl, hic⟩)
    · have hic0 : InCone 26 C i0 k :=
        (inCone_iff 26 C i0 k k.2).2 ⟨26 + i0, hgw, by omega, hwlt, Or.inl (by omega)⟩
      exact hno_all i0 hic0 hi0and
    · have hic0 : InCone 26 C i0 k :=
        (inCone_iff 26 C i0 k k.2).2 ⟨w, hgw, hw26, hwlt, Or.inr hic⟩
      exact hno_all i0 hic0 hi0and
  obtain ⟨S, hS⟩ := decomp_wire C i0 legal hlen2 hin w hno
  exact ⟨S, fun x => by rw [hS x]; simp [hnh]⟩

lemma noOtherAnd_j0_child (C : Circuit) (i0 j0 : ℕ)
    (hj0lt : j0 < C.gates.length) (hj0and : (gateAt C j0).op = GateOp.and)
    (legal : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ k : Fin C.gates.length, ∀ a ∈ (C.gates.get k).inputs, a < 26 + (k : ℕ))
    (huniq : ∀ i' j', (gateAt C i').op = GateOp.and → (gateAt C j').op = GateOp.and →
      InCone 26 C i' j' → i' = i0 ∧ j' = j0)
    (w : ℕ) (hw : w ∈ C.gates[j0].inputs) : NoOtherAnd C i0 w := by
  have hgw : w ∈ (gateAt C j0).inputs := by rw [gateAt_eq C j0 hj0lt]; exact hw
  have hwlt : w < 26 + j0 := hin ⟨j0, hj0lt⟩ w hw
  refine ⟨?_, ?_⟩
  · intro hw26 hwl hne
    have hic : InCone 26 C (w - 26) j0 :=
      (inCone_iff 26 C (w - 26) j0 hj0lt).2 ⟨w, hgw, hw26, hwlt, Or.inl rfl⟩
    rw [gateAt_eq C (w - 26) hwl]
    rcases (legal _ (List.getElem_mem hwl)).1 with h | h
    · exfalso
      have hga : (gateAt C (w - 26)).op = GateOp.and := by rw [gateAt_eq C (w - 26) hwl]; exact h
      exact hne (huniq (w - 26) j0 hga hj0and hic).1
    · exact h
  · intro hw26 hwl m hm hne hand
    have hic : InCone 26 C m j0 :=
      (inCone_iff 26 C m j0 hj0lt).2 ⟨w, hgw, hw26, hwlt, Or.inr hm⟩
    exact hne (huniq m j0 hand hj0and hic).1

lemma star_false_outside (gs : List Gate) (w : ℕ) (S : Finset (Fin 26)) (z : Fin 26)
    (hS : ∀ x : Fin 26 → Bool, val gs w x = true ↔ ∃ v ∈ S, x v = true)
    (hsub : S ⊆ N z) :
    val gs w (fun u : Fin 26 => decide (u ∉ N z)) = false := by
  cases hv : val gs w (fun u => decide (u ∉ N z)) with
  | false => rfl
  | true =>
    exfalso
    obtain ⟨u, hu, hnu⟩ := (hS _).1 hv
    exact of_decide_eq_true hnu (hsub hu)

lemma cOf_false_of_zero (gs : List Gate) (o : ℕ) (H : Hy0 gs o) (w : ℕ) (z : Fin 26) :
    val gs w (cOf (some z) z) = false := by
  simp only [cOf, ite_true]
  exact val_zero gs H.1 H.2.1 w

lemma union_card_le_max_add_one (S1 S2 : Finset (Fin 26)) (y : Fin 26)
    (h1 : S1 ⊆ N y) (h2 : S2 ⊆ N y) (hi : (S1 ∩ S2).Nonempty) :
    (S1 ∪ S2).card ≤ max S1.card S2.card + 1 := by
  have hu : (S1 ∪ S2).card ≤ 4 := by
    rw [← degN y]
    exact Finset.card_le_card (Finset.union_subset h1 h2)
  have hci : 1 ≤ (S1 ∩ S2).card := Finset.card_pos.2 hi
  have hadd := Finset.card_union_add_card_inter S1 S2
  omega

def OtherStars (gs : List Gate) (o : ℕ) (jF : Fin gs.length)
    (zk : Fin gs.length → Fin 26) (Ak : Fin gs.length → Finset (Fin 26)) (lwk : Fin gs.length → ℕ) : Prop :=
  ∀ k ∈ US gs o, k ≠ jF →
    Ak k ⊆ N (zk k) ∧
    (∀ p ∈ Ak k, val gs (lwk k) (fun u => decide (u = p)) = true) ∧
    val gs (lwk k) (fun u => decide (u ∉ N (zk k))) = false ∧
    ∀ s t : Fin 26, val gs (26 + (k : ℕ)) (pr s t) = true →
      (s = zk k ∧ t ∈ Ak k) ∨ (t = zk k ∧ s ∈ Ak k)

open Classical in
theorem finish_no_j_thm (gs : List Gate) (o : ℕ) (H : Hy0 gs o) (jF : Fin gs.length)
    (zk : Fin gs.length → Fin 26) (Ak : Fin gs.length → Finset (Fin 26)) (lwk : Fin gs.length → ℕ)
    (hoth : OtherStars gs o jF zk Ak lwk)
    (hcov' : ∀ s t : Fin 26, adjb s t = true → ∃ k ∈ US gs o, k ≠ jF ∧
      val gs (26 + (k : ℕ)) (pr s t) = true) : 64 ≤ gs.length := by
  refine master_simple gs o H ((US gs o).erase jF) zk Ak lwk none ∅ ?_ ?_ ?_ ?_ (by simp) ?_
  · intro k hk
    exact (hoth k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk)).1
  · intro k hk p hp
    exact (hoth k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk)).2.1 p hp
  · intro k hk _
    simpa [cOf] using (hoth k (Finset.mem_of_mem_erase hk) (Finset.ne_of_mem_erase hk)).2.2.1
  · intro s t hadj
    obtain ⟨k, hk, hne, hv⟩ := hcov' s t hadj
    exact ⟨k, Finset.mem_erase.2 ⟨hne, hk⟩, (hoth k hk hne).2.2.2 s t hv⟩
  · have := Finset.card_erase_le (s := US gs o) (a := jF)
    omega

open Classical in
theorem finish_one_star_thm (gs : List Gate) (o : ℕ) (H : Hy0 gs o) (jF : Fin gs.length)
    (zk : Fin gs.length → Fin 26) (Ak : Fin gs.length → Finset (Fin 26)) (lwk : Fin gs.length → ℕ)
    (hoth : OtherStars gs o jF zk Ak lwk)
    (zj : Fin 26) (Aj : Finset (Fin 26)) (lwj : ℕ) (v0 : Option (Fin 26))
    (hAj : Aj ⊆ N zj)
    (hhot : ∀ p ∈ Aj, val gs lwj (fun u => decide (u = p)) = true)
    (hhoc : val gs lwj (cOf v0 zj) = false)
    (hcovj : ∀ s t : Fin 26, adjb s t = true → val gs (26 + (jF : ℕ)) (pr s t) = true →
      ((s = zj ∧ t ∈ Aj) ∨ (t = zj ∧ s ∈ Aj)) ∨
      (∃ k ∈ US gs o, k ≠ jF ∧ val gs (26 + (k : ℕ)) (pr s t) = true)) :
    64 ≤ gs.length := by
  let z' : Fin gs.length → Fin 26 := fun k => if k = jF then zj else zk k
  let A' : Fin gs.length → Finset (Fin 26) := fun k => if k = jF then Aj else Ak k
  let lw' : Fin gs.length → ℕ := fun k => if k = jF then lwj else lwk k
  refine master_simple gs o H (US gs o) z' A' lw' v0 ∅ ?_ ?_ ?_ ?_ (by simp) (by omega)
  · intro k hk
    by_cases e : k = jF
    · simp [z', A', e, hAj]
    · simp [z', A', e, (hoth k hk e).1]
  · intro k hk p hp
    by_cases e : k = jF
    · simp only [A', e, ite_true] at hp
      simp only [lw', e, ite_true]
      exact hhot p hp
    · simp only [A', e, ite_false] at hp
      simp only [lw', e, ite_false]
      exact (hoth k hk e).2.1 p hp
  · intro k hk _
    by_cases e : k = jF
    · simp only [z', lw', e, ite_true]
      exact hhoc
    · simp only [z', lw', e, ite_false]
      by_cases hveq : v0 = some (zk k)
      · simp only [cOf, hveq, ite_true]
        exact val_zero gs H.1 H.2.1 _
      · simp only [cOf, hveq, ite_false]
        exact (hoth k hk e).2.2.1
  · intro s t hadj
    obtain ⟨k, hk, hv⟩ := cover gs o H s t hadj
    by_cases e : k = jF
    · subst e
      rcases hcovj s t hadj hv with h1 | ⟨k2, hk2, hne2, hv2⟩
      · exact ⟨k, hk, by simpa [z', A'] using h1⟩
      · exact ⟨k2, hk2, by simpa [z', A', hne2] using (hoth k2 hk2 hne2).2.2.2 s t hv2⟩
    · exact ⟨k, hk, by simpa [z', A', e] using (hoth k hk e).2.2.2 s t hv⟩

open Classical in
theorem finish_two_stars_thm (gs : List Gate) (o : ℕ) (H : Hy0 gs o) (jF : Fin gs.length)
    (zk : Fin gs.length → Fin 26) (Ak : Fin gs.length → Finset (Fin 26)) (lwk : Fin gs.length → ℕ)
    (hoth : OtherStars gs o jF zk Ak lwk)
    (z1 : Fin 26) (A1 : Finset (Fin 26)) (lw1 : ℕ)
    (z2 : Fin 26) (A2 : Finset (Fin 26)) (lw2 : ℕ)
    (v0 : Option (Fin 26)) (E : Finset (Fin gs.length))
    (hA1 : A1 ⊆ N z1)
    (hot1 : ∀ p ∈ A1, val gs lw1 (fun u => decide (u = p)) = true)
    (hoc1 : val gs lw1 (cOf v0 z1) = false)
    (hA2 : A2 ⊆ N z2)
    (hot2 : ∀ p ∈ A2, val gs lw2 (fun u => decide (u = p)) = true)
    (hoc2 : val gs lw2 (cOf v0 z2) = false)
    (hcovj : ∀ s t : Fin 26, adjb s t = true → val gs (26 + (jF : ℕ)) (pr s t) = true →
      ((s = z1 ∧ t ∈ A1) ∨ (t = z1 ∧ s ∈ A1)) ∨
      ((s = z2 ∧ t ∈ A2) ∨ (t = z2 ∧ s ∈ A2)) ∨
      (∃ k ∈ US gs o, k ≠ jF ∧ val gs (26 + (k : ℕ)) (pr s t) = true))
    (hE : ∀ g ∈ E, g ∉ US gs o ∧ g ∉ ROS gs o ∧
      ∀ (v : Fin 26) (Av : Finset (Fin 26)), Av ⊆ N v →
        ¬ Mrg gs Av (cOf v0 v) (fun p u => decide (u = p)) g)
    (hE2 : 2 ≤ E.card) :
    64 ≤ gs.length := by
  let U2 : Finset (Option (Fin gs.length)) := insert none ((US gs o).image some)
  let z' : Option (Fin gs.length) → Fin 26 := fun x =>
    match x with
    | none => z2
    | some k => if k = jF then z1 else zk k
  let A' : Option (Fin gs.length) → Finset (Fin 26) := fun x =>
    match x with
    | none => A2
    | some k => if k = jF then A1 else Ak k
  let lw' : Option (Fin gs.length) → ℕ := fun x =>
    match x with
    | none => lw2
    | some k => if k = jF then lw1 else lwk k
  have hU2card : U2.card = (US gs o).card + 1 := by
    have hnm : (none : Option (Fin gs.length)) ∉ (US gs o).image some := by simp
    rw [Finset.card_insert_of_notMem hnm, Finset.card_image_of_injective _ (Option.some_injective _)]
  refine master_simple gs o H U2 z' A' lw' v0 E ?_ ?_ ?_ ?_ hE (by omega)
  · intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx'
    · exact hA2
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx'
      by_cases e : k = jF
      · simp [z', A', e, hA1]
      · simp [z', A', e, (hoth k hk e).1]
  · intro x hx p hp
    rcases Finset.mem_insert.1 hx with rfl | hx'
    · exact hot2 p hp
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx'
      by_cases e : k = jF
      · simp only [A', e, ite_true] at hp
        simp only [lw', e, ite_true]
        exact hot1 p hp
      · simp only [A', e, ite_false] at hp
        simp only [lw', e, ite_false]
        exact (hoth k hk e).2.1 p hp
  · intro x hx _
    rcases Finset.mem_insert.1 hx with rfl | hx'
    · exact hoc2
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx'
      by_cases e : k = jF
      · simp only [z', lw', e, ite_true]
        exact hoc1
      · simp only [z', lw', e, ite_false]
        by_cases hveq : v0 = some (zk k)
        · simp only [cOf, hveq, ite_true]
          exact val_zero gs H.1 H.2.1 _
        · simp only [cOf, hveq, ite_false]
          exact (hoth k hk e).2.2.1
  · intro s t hadj
    obtain ⟨k, hk, hv⟩ := cover gs o H s t hadj
    by_cases e : k = jF
    · subst e
      rcases hcovj s t hadj hv with h1 | h2 | ⟨k2, hk2, hne2, hv2⟩
      · exact ⟨some k, Finset.mem_insert_of_mem (Finset.mem_image_of_mem some hk),
          by simpa [z', A'] using h1⟩
      · exact ⟨none, Finset.mem_insert_self _ _, h2⟩
      · exact ⟨some k2, Finset.mem_insert_of_mem (Finset.mem_image_of_mem some hk2),
          by simpa [z', A', hne2] using (hoth k2 hk2 hne2).2.2.2 s t hv2⟩
    · exact ⟨some k, Finset.mem_insert_of_mem (Finset.mem_image_of_mem some hk),
        by simpa [z', A', e] using (hoth k hk e).2.2.2 s t hv⟩

open Classical in
theorem finish_plus1_thm (gs : List Gate) (o : ℕ) (H : Hy0 gs o) (iF jF : Fin gs.length)
    (hi0op : (gs.get iF).op = GateOp.and) (hjUS : jF ∈ US gs o)
    (zk : Fin gs.length → Fin 26) (Ak : Fin gs.length → Finset (Fin 26)) (lwk : Fin gs.length → ℕ)
    (hoth : OtherStars gs o jF zk Ak lwk)
    (y : Fin 26) (S1 S2 : Finset (Fin 26)) (lw1 lw2 : ℕ)
    (hS1 : S1 ⊆ N y) (hS2 : S2 ⊆ N y) (hS1c : 2 ≤ S1.card) (hInt : (S1 ∩ S2).Nonempty)
    (hot1 : ∀ p ∈ S1, val gs lw1 (fun u => decide (u = p)) = true)
    (hot2 : ∀ p ∈ S2, val gs lw2 (fun u => decide (u = p)) = true)
    (hcovj : ∀ s t : Fin 26, adjb s t = true → val gs (26 + (jF : ℕ)) (pr s t) = true →
      (s = y ∧ t ∈ S1 ∪ S2) ∨ (t = y ∧ s ∈ S1 ∪ S2))
    (hniUS : iF ∉ US gs o) :
    64 ≤ gs.length := by
  let z' : Fin gs.length → Fin 26 := fun k => if k = jF then y else zk k
  let A' : Fin gs.length → Finset (Fin 26) := fun k => if k = jF then S1 ∪ S2 else Ak k
  have hmax : ∀ v : Fin 26, ∃ (Av : Finset (Fin 26)) (ov : ℕ), Av ⊆ N v ∧
      (∀ p ∈ Av, val gs ov (fun u => decide (u = p)) = true) ∧
      (1 ≤ Av.card → val gs ov (cOf (some y) v) = false) ∧
      (∀ k ∈ US gs o, k ≠ jF → zk k = v → (Ak k).card ≤ Av.card) ∧
      (v = y → S1.card ≤ Av.card ∧ S2.card ≤ Av.card) := by
    intro v
    by_cases hvy : v = y
    · subst hvy
      let cands : Finset (Finset (Fin 26) × ℕ) :=
        insert (S1, lw1) (insert (S2, lw2)
          (((US gs o).filter (fun k => k ≠ jF ∧ zk k = v)).image (fun k => (Ak k, lwk k))))
      have hne : cands.Nonempty := ⟨(S1, lw1), Finset.mem_insert_self _ _⟩
      obtain ⟨⟨Av, ov⟩, hmem, hmx⟩ := Finset.exists_max_image cands (fun p => p.1.card) hne
      have hprops : Av ⊆ N v ∧ (∀ p ∈ Av, val gs ov (fun u => decide (u = p)) = true) := by
        rcases Finset.mem_insert.1 hmem with h | h
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact ⟨hS1, hot1⟩
        · rcases Finset.mem_insert.1 h with h | h
          · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; exact ⟨hS2, hot2⟩
          · obtain ⟨k, hk, hEq⟩ := Finset.mem_image.1 h
            rw [Finset.mem_filter] at hk
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj hEq
            have ho := hoth k hk.1 hk.2.1
            rw [hk.2.2] at ho
            exact ⟨ho.1, ho.2.1⟩
      refine ⟨Av, ov, hprops.1, hprops.2, ?_, ?_, ?_⟩
      · intro _; exact cOf_false_of_zero gs o H ov v
      · intro k hk hne' hzk
        exact hmx (Ak k, lwk k) (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hk, hne', hzk⟩))))
      · intro _
        exact ⟨hmx (S1, lw1) (Finset.mem_insert_self _ _),
          hmx (S2, lw2) (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))⟩
    · by_cases hne : ((US gs o).filter (fun k => k ≠ jF ∧ zk k = v)).Nonempty
      · obtain ⟨k0, hk0, hmx⟩ := Finset.exists_max_image _ (fun k => (Ak k).card) hne
        rw [Finset.mem_filter] at hk0
        have ho := hoth k0 hk0.1 hk0.2.1
        rw [hk0.2.2] at ho
        refine ⟨Ak k0, lwk k0, ho.1, ho.2.1, ?_, ?_, fun h => absurd h hvy⟩
        · intro _
          have hne' : (some y : Option (Fin 26)) ≠ some v := fun e => hvy (Option.some.inj e).symm
          simp only [cOf, hne', ite_false]
          exact ho.2.2.1
        · intro k hk hne' hzk
          exact hmx k (Finset.mem_filter.2 ⟨hk, hne', hzk⟩)
      · refine ⟨∅, 0, Finset.empty_subset _, by simp, by simp, ?_, fun h => absurd h hvy⟩
        intro k hk hne' hzk
        exact absurd ⟨k, Finset.mem_filter.2 ⟨hk, hne', hzk⟩⟩ hne
  choose Av ov hAv hotv hocv hlev hley using hmax
  let ef : Fin 26 → ℕ := fun v => if v = y then 1 else 0
  have hsum_e : ∑ v : Fin 26, ef v = 1 := by simp [ef]
  refine master_64 gs o H (US gs o) z' A' Av ov (some y) ef {iF}
    ?_ ?_ ?_ ?_ hAv hotv hocv ?_ (by rw [hsum_e, Finset.card_singleton])
  · intro k hk
    by_cases e : k = jF
    · simp only [z', A', e, ite_true]
      exact Finset.union_subset hS1 hS2
    · simp only [z', A', e, ite_false]
      exact (hoth k hk e).1
  · intro v
    by_cases hvy : v = y
    · subst hvy
      simp only [ef, ite_true]
      have hjmem : jF ∈ (US gs o).filter (fun k => z' k = v) := by simp [z', hjUS]
      rw [← Finset.add_sum_erase _ _ hjmem]
      have h1j : (A' jF).card ≤ (Av v).card + 1 := by
        simp only [A', ite_true]
        have h1 := union_card_le_max_add_one S1 S2 v hS1 hS2 hInt
        have h2 := hley v rfl
        omega
      have hrest : (∑ k ∈ ((US gs o).filter (fun k => z' k = v)).erase jF, (A' k).card) ≤
          (((US gs o).filter (fun k => z' k = v)).erase jF).card * (Av v).card := by
        refine (Finset.sum_le_card_nsmul _ _ (Av v).card ?_).trans (by simp)
        intro k hk
        have hne := Finset.ne_of_mem_erase hk
        have hmf := Finset.mem_filter.1 (Finset.mem_of_mem_erase hk)
        have hzk : zk k = v := by simpa [z', hne] using hmf.2
        simpa [A', hne] using hlev v k hmf.1 hne hzk
      have hce : (((US gs o).filter (fun k => z' k = v)).erase jF).card + 1 =
          ((US gs o).filter (fun k => z' k = v)).card := Finset.card_erase_add_one hjmem
      have hmul : ((US gs o).filter (fun k => z' k = v)).card * (Av v).card =
          (((US gs o).filter (fun k => z' k = v)).erase jF).card * (Av v).card + (Av v).card := by
        rw [← hce, Nat.add_mul, Nat.one_mul]
      omega
    · simp only [ef, hvy, ite_false, Nat.add_zero]
      refine (Finset.sum_le_card_nsmul _ _ (Av v).card ?_).trans (by simp)
      intro k hk
      rw [Finset.mem_filter] at hk
      have hne : k ≠ jF := by
        intro e; rw [e] at hk; simp [z'] at hk; exact hvy hk.2.symm
      have hzk : zk k = v := by simpa [z', hne] using hk.2
      simpa [A', hne] using hlev v k hk.1 hne hzk
  · intro v
    by_cases hvy : v = y
    · right
      subst hvy
      have hjmem : jF ∈ (US gs o).filter (fun k => z' k = v) := by simp [z', hjUS]
      have hc1 : 1 ≤ ((US gs o).filter (fun k => z' k = v)).card := Finset.card_pos.2 ⟨jF, hjmem⟩
      have h2 := (hley v rfl).1
      exact ⟨by simp [ef], hc1, by omega⟩
    · left; simp [ef, hvy]
  · intro s t hadj
    obtain ⟨k, hk, hv⟩ := cover gs o H s t hadj
    by_cases e : k = jF
    · subst e
      exact ⟨k, hk, by simpa [z', A'] using hcovj s t hadj hv⟩
    · exact ⟨k, hk, by simpa [z', A', e] using (hoth k hk e).2.2.2 s t hv⟩
  · intro g hg
    rw [Finset.mem_singleton] at hg
    rw [hg]
    have hd := and_gate_disj gs o (some y) iF hi0op hniUS
    exact ⟨hd.1, hd.2.1, fun v => hd.2.2 v (Av v) (hAv v)⟩

open Classical in
theorem handle_sing_U'Y (C : Circuit) (H : Hy0 C.gates C.output)
    (iF jF : Fin C.gates.length) (hi0op : (C.gates.get iF).op = GateOp.and)
    (hneij : iF ≠ jF)
    (zk : Fin C.gates.length → Fin 26) (Ak : Fin C.gates.length → Finset (Fin 26))
    (lwk : Fin C.gates.length → ℕ) (hoth : OtherStars C.gates C.output jF zk Ak lwk)
    (u1 v1 a0 b0 : ℕ) (U1 V1 A0 B0 U' Y0 : Finset (Fin 26))
    (hIu : HasI C iF u1) (hnou1 : NoOtherAnd C iF u1)
    (hV1' : ∀ x : Fin 26 → Bool, val C.gates v1 x = true ↔ ∃ v ∈ V1, x v = true)
    (hA0 : ∀ x : Fin 26 → Bool, val C.gates a0 x = true ↔ ∃ v ∈ A0, x v = true)
    (hB0 : ∀ x : Fin 26 → Bool, val C.gates b0 x = true ↔ ∃ v ∈ B0, x v = true)
    (hi0_0 : ∀ x : Fin 26 → Bool, val C.gates (26 + (iF : ℕ)) x = true ↔
      (∃ v ∈ A0, x v = true) ∧ (∃ v ∈ B0, x v = true))
    (hu1_sing : ∀ p ∈ U', val C.gates u1 (fun u => decide (u = p)) = true)
    (hY0eq : Y0 = A0 ∩ V1) (hU'eq : U' = U1 ∪ (A0 ∩ B0))
    (hU'V : ∀ s ∈ U', ∀ t ∈ V1, adjb s t = true)
    (hY0B0 : ∀ s ∈ Y0, ∀ t ∈ B0, adjb s t = true)
    (hcov2 : ∀ s t : Fin 26, val C.gates (26 + (jF : ℕ)) (pr s t) = true →
      ((s ∈ U' ∧ t ∈ V1) ∨ (t ∈ U' ∧ s ∈ V1)) ∨ ((s ∈ Y0 ∧ t ∈ B0) ∨ (t ∈ Y0 ∧ s ∈ B0)))
    (x y : Fin 26) (hUx : U' = {x}) (hY0y : Y0 = {y}) :
    64 ≤ C.gates.length := by
  have hyin : y ∈ Y0 := by rw [hY0y]; simp
  have hxin : x ∈ U' := by rw [hUx]; simp
  have hxy : adjb x y = true := hU'V x hxin y (Finset.mem_inter.1 (hY0eq ▸ hyin)).2
  have hVsub : V1 ⊆ N x := fun t ht => (mem_N x t).2 (hU'V x hxin t ht)
  have hBsub : B0 ⊆ N y := fun t ht => (mem_N y t).2 (hY0B0 y hyin t ht)
  by_cases hiUS : iF ∈ US C.gates C.output
  · refine finish_one_star_thm C.gates C.output H jF zk Ak lwk hoth x V1 v1 none hVsub
      (fun p hp => (hV1' _).2 ⟨p, hp, by simp⟩)
      (by simpa [cOf] using star_false_outside C.gates v1 V1 x hV1' hVsub) ?_
    intro s t _ hst
    rcases hcov2 s t hst with h1 | h2
    · left
      rcases h1 with ⟨hs, ht⟩ | ⟨ht, hs⟩
      · rw [hUx, Finset.mem_singleton] at hs; exact Or.inl ⟨hs, ht⟩
      · rw [hUx, Finset.mem_singleton] at ht; exact Or.inr ⟨ht, hs⟩
    · right
      refine ⟨iF, hiUS, hneij, ?_⟩
      rw [hi0_0]
      rcases h2 with ⟨hs, ht⟩ | ⟨ht, hs⟩
      · exact ⟨⟨s, (Finset.mem_inter.1 (hY0eq ▸ hs)).1, by simp [pr]⟩, ⟨t, ht, by simp [pr]⟩⟩
      · exact ⟨⟨t, (Finset.mem_inter.1 (hY0eq ▸ ht)).1, by simp [pr]⟩, ⟨s, hs, by simp [pr]⟩⟩
  · by_cases hxX : x ∈ A0 ∩ B0
    · have hxA0 : x ∈ A0 := (Finset.mem_inter.1 hxX).1
      have hyA0 : y ∈ A0 := (Finset.mem_inter.1 (hY0eq ▸ hyin)).1
      obtain ⟨m, hm_or, hmx, hmy⟩ := cross_gate C.gates H.1 H.2.1 H.2.2.1 a0 x y hxy
        ((hA0 _).2 ⟨x, hxA0, by simp⟩) ((hA0 _).2 ⟨y, hyA0, by simp⟩)
      have hne_im : iF ≠ m := by
        intro e; rw [← e] at hm_or; rw [hi0op] at hm_or; exact GateOp.noConfusion hm_or
      refine finish_two_stars_thm C.gates C.output H jF zk Ak lwk hoth x V1 v1 y B0 b0 none {iF, m}
        hVsub (fun p hp => (hV1' _).2 ⟨p, hp, by simp⟩)
        (by simpa [cOf] using star_false_outside C.gates v1 V1 x hV1' hVsub)
        hBsub (fun p hp => (hB0 _).2 ⟨p, hp, by simp⟩)
        (by simpa [cOf] using star_false_outside C.gates b0 B0 y hB0 hBsub)
        ?_ ?_ (by rw [Finset.card_pair hne_im])
      · intro s t _ hst
        rcases hcov2 s t hst with h1 | h2
        · left
          rcases h1 with ⟨hs, ht⟩ | ⟨ht, hs⟩
          · rw [hUx, Finset.mem_singleton] at hs; exact Or.inl ⟨hs, ht⟩
          · rw [hUx, Finset.mem_singleton] at ht; exact Or.inr ⟨ht, hs⟩
        · right; left
          rcases h2 with ⟨hs, ht⟩ | ⟨ht, hs⟩
          · rw [hY0y, Finset.mem_singleton] at hs; exact Or.inl ⟨hs, ht⟩
          · rw [hY0y, Finset.mem_singleton] at ht; exact Or.inr ⟨ht, hs⟩
      · intro g hg
        rcases Finset.mem_insert.1 hg with hg' | hg'
        · rw [hg']; exact and_gate_disj C.gates C.output none iF hi0op hiUS
        · rw [Finset.mem_singleton.1 hg']
          exact cross_gate_disj C.gates C.output H m x y hxy hm_or hmx hmy
    · have hi0z : ∀ r : Fin 26, val C.gates (26 + (iF : ℕ)) (fun u => decide (u = r)) = false := by
        intro r
        cases hv : val C.gates (26 + (iF : ℕ)) (fun u => decide (u = r)) with
        | false => rfl
        | true =>
          exfalso
          rw [hi0_0] at hv
          obtain ⟨⟨a1, ha1, h1⟩, ⟨b1, hb1, h2⟩⟩ := hv
          have e1 : a1 = r := of_decide_eq_true h1
          have e2 : b1 = r := of_decide_eq_true h2
          rw [e1] at ha1; rw [e2] at hb1
          have hrX : r ∈ A0 ∩ B0 := Finset.mem_inter.2 ⟨ha1, hb1⟩
          have hrU : r ∈ U' := by rw [hU'eq]; exact Finset.mem_union_right _ hrX
          rw [hUx, Finset.mem_singleton] at hrU
          exact hxX (hrU ▸ hrX)
      obtain ⟨m, hm_or, hmsing, hmzero⟩ := mix_gate C iF H.1 H.2.1 H.2.2.1 hi0z u1 hIu hnou1
        ⟨x, hu1_sing x hxin⟩
      have hne_im : iF ≠ m := by
        intro e; rw [← e] at hm_or; rw [hi0op] at hm_or; exact GateOp.noConfusion hm_or
      refine finish_two_stars_thm C.gates C.output H jF zk Ak lwk hoth x V1 v1 y B0 b0 none {iF, m}
        hVsub (fun p hp => (hV1' _).2 ⟨p, hp, by simp⟩)
        (by simpa [cOf] using star_false_outside C.gates v1 V1 x hV1' hVsub)
        hBsub (fun p hp => (hB0 _).2 ⟨p, hp, by simp⟩)
        (by simpa [cOf] using star_false_outside C.gates b0 B0 y hB0 hBsub)
        ?_ ?_ (by rw [Finset.card_pair hne_im])
      · intro s t _ hst
        rcases hcov2 s t hst with h1 | h2
        · left
          rcases h1 with ⟨hs, ht⟩ | ⟨ht, hs⟩
          · rw [hUx, Finset.mem_singleton] at hs; exact Or.inl ⟨hs, ht⟩
          · rw [hUx, Finset.mem_singleton] at ht; exact Or.inr ⟨ht, hs⟩
        · right; left
          rcases h2 with ⟨hs, ht⟩ | ⟨ht, hs⟩
          · rw [hY0y, Finset.mem_singleton] at hs; exact Or.inl ⟨hs, ht⟩
          · rw [hY0y, Finset.mem_singleton] at ht; exact Or.inr ⟨ht, hs⟩
      · intro g hg
        rcases Finset.mem_insert.1 hg with hg' | hg'
        · rw [hg']; exact and_gate_disj C.gates C.output none iF hi0op hiUS
        · rw [Finset.mem_singleton.1 hg']
          exact mix_gate_disj C.gates C.output H none m hm_or hmsing hmzero

open Classical in
theorem handle_U'Y_thm (C : Circuit) (H : Hy0 C.gates C.output)
    (iF jF : Fin C.gates.length) (hi0op : (C.gates.get iF).op = GateOp.and)
    (hjUS : jF ∈ US C.gates C.output) (hneij : iF ≠ jF)
    (zk : Fin C.gates.length → Fin 26) (Ak : Fin C.gates.length → Finset (Fin 26))
    (lwk : Fin C.gates.length → ℕ) (hoth : OtherStars C.gates C.output jF zk Ak lwk)
    (u1 v1 a0 b0 : ℕ) (U1 V1 A0 B0 U' Y0 : Finset (Fin 26))
    (hIu : HasI C iF u1) (hnou1 : NoOtherAnd C iF u1)
    (hV1' : ∀ x : Fin 26 → Bool, val C.gates v1 x = true ↔ ∃ v ∈ V1, x v = true)
    (hA0 : ∀ x : Fin 26 → Bool, val C.gates a0 x = true ↔ ∃ v ∈ A0, x v = true)
    (hB0 : ∀ x : Fin 26 → Bool, val C.gates b0 x = true ↔ ∃ v ∈ B0, x v = true)
    (hi0_0 : ∀ x : Fin 26 → Bool, val C.gates (26 + (iF : ℕ)) x = true ↔
      (∃ v ∈ A0, x v = true) ∧ (∃ v ∈ B0, x v = true))
    (hu1_sing : ∀ p ∈ U', val C.gates u1 (fun u => decide (u = p)) = true)
    (hY0eq : Y0 = A0 ∩ V1) (hU'eq : U' = U1 ∪ (A0 ∩ B0))
    (hU'V : ∀ s ∈ U', ∀ t ∈ V1, adjb s t = true)
    (hY0B0 : ∀ s ∈ Y0, ∀ t ∈ B0, adjb s t = true)
    (hcov2 : ∀ s t : Fin 26, val C.gates (26 + (jF : ℕ)) (pr s t) = true →
      ((s ∈ U' ∧ t ∈ V1) ∨ (t ∈ U' ∧ s ∈ V1)) ∨ ((s ∈ Y0 ∧ t ∈ B0) ∨ (t ∈ Y0 ∧ s ∈ B0)))
    (hU'ne : U'.Nonempty) (hY0ne : Y0.Nonempty) :
    64 ≤ C.gates.length := by
  have hU'Y0 : ∀ u ∈ U', ∀ y ∈ Y0, adjb u y = true := fun u hu y hy =>
    hU'V u hu y (Finset.mem_inter.1 (hY0eq ▸ hy)).2
  have hV1ne : V1.Nonempty := by
    obtain ⟨y, hy⟩ := hY0ne
    exact ⟨y, (Finset.mem_inter.1 (hY0eq ▸ hy)).2⟩
  by_cases hB0ne : B0.Nonempty
  swap
  · have hB0e : B0 = ∅ := Finset.not_nonempty_iff_eq_empty.1 hB0ne
    rcases bip_star U' V1 hU'V hU'ne hV1ne with ⟨x, hUx, hVsub⟩ | ⟨y, hVy, hUsub⟩
    · refine finish_one_star_thm C.gates C.output H jF zk Ak lwk hoth x V1 v1 none hVsub
        (fun p hp => (hV1' _).2 ⟨p, hp, by simp⟩)
        (by simpa [cOf] using star_false_outside C.gates v1 V1 x hV1' hVsub) ?_
      intro s t _ hst
      rcases hcov2 s t hst with h1 | h2
      · left
        rcases h1 with ⟨hs, ht⟩ | ⟨ht, hs⟩
        · rw [hUx, Finset.mem_singleton] at hs; exact Or.inl ⟨hs, ht⟩
        · rw [hUx, Finset.mem_singleton] at ht; exact Or.inr ⟨ht, hs⟩
      · rw [hB0e] at h2; simp at h2
    · refine finish_one_star_thm C.gates C.output H jF zk Ak lwk hoth y U' u1 (some y) hUsub hu1_sing
        (cOf_false_of_zero C.gates C.output H u1 y) ?_
      intro s t _ hst
      rcases hcov2 s t hst with h1 | h2
      · left
        rcases h1 with ⟨hs, ht⟩ | ⟨ht, hs⟩
        · rw [hVy, Finset.mem_singleton] at ht; exact Or.inr ⟨ht, hs⟩
        · rw [hVy, Finset.mem_singleton] at hs; exact Or.inl ⟨hs, ht⟩
      · rw [hB0e] at h2; simp at h2
  rcases bip_star U' Y0 hU'Y0 hU'ne hY0ne with ⟨x, hUx, hY0sub⟩ | ⟨y, hY0y, hU'sub⟩
  · by_cases hY1 : ∃ y : Fin 26, Y0 = {y}
    · obtain ⟨y, hY0y⟩ := hY1
      exact handle_sing_U'Y C H iF jF hi0op hneij zk Ak lwk hoth u1 v1 a0 b0 U1 V1 A0 B0 U' Y0
        hIu hnou1 hV1' hA0 hB0 hi0_0 hu1_sing hY0eq hU'eq hU'V hY0B0 hcov2 x y hUx hY0y
    · have hYge2 : 2 ≤ Y0.card := by
        by_contra hlt
        have h1 : Y0.card = 1 := by have hp := Finset.card_pos.2 hY0ne; omega
        exact hY1 (Finset.card_eq_one.1 h1)
      rcases bip_star Y0 B0 hY0B0 hY0ne hB0ne with ⟨y, hYy, _⟩ | ⟨b1, hBb1, hYsub⟩
      · rw [hYy] at hYge2; simp at hYge2
      · have hbx : b1 = x := by
          by_contra hne
          have hsub2 : Y0 ⊆ N x ∩ N b1 := Finset.subset_inter hY0sub hYsub
          have hc := (Finset.card_le_card hsub2).trans (hLN x b1 (Ne.symm hne))
          omega
        subst hbx
        have hVsub : V1 ⊆ N b1 := fun t ht => (mem_N b1 t).2 (hU'V b1 (by rw [hUx]; simp) t ht)
        refine finish_one_star_thm C.gates C.output H jF zk Ak lwk hoth b1 V1 v1 none hVsub
          (fun p hp => (hV1' _).2 ⟨p, hp, by simp⟩)
          (by simpa [cOf] using star_false_outside C.gates v1 V1 b1 hV1' hVsub) ?_
        intro s t _ hst
        left
        rcases hcov2 s t hst with h1 | h2
        · rcases h1 with ⟨hs, ht⟩ | ⟨ht, hs⟩
          · rw [hUx, Finset.mem_singleton] at hs; exact Or.inl ⟨hs, ht⟩
          · rw [hUx, Finset.mem_singleton] at ht; exact Or.inr ⟨ht, hs⟩
        · rcases h2 with ⟨hs, ht⟩ | ⟨ht, hs⟩
          · rw [hBb1, Finset.mem_singleton] at ht
            exact Or.inr ⟨ht, (Finset.mem_inter.1 (hY0eq ▸ hs)).2⟩
          · rw [hBb1, Finset.mem_singleton] at hs
            exact Or.inl ⟨hs, (Finset.mem_inter.1 (hY0eq ▸ ht)).2⟩
  · by_cases hU1c : ∃ x : Fin 26, U' = {x}
    · obtain ⟨x, hUx⟩ := hU1c
      exact handle_sing_U'Y C H iF jF hi0op hneij zk Ak lwk hoth u1 v1 a0 b0 U1 V1 A0 B0 U' Y0
        hIu hnou1 hV1' hA0 hB0 hi0_0 hu1_sing hY0eq hU'eq hU'V hY0B0 hcov2 x y hUx hY0y
    · have hBsub : B0 ⊆ N y := fun t ht => (mem_N y t).2 (hY0B0 y (by rw [hY0y]; simp) t ht)
      have hUge2 : 2 ≤ U'.card := by
        by_contra hlt
        have h1 : U'.card = 1 := by have hp := Finset.card_pos.2 hU'ne; omega
        exact hU1c (Finset.card_eq_one.1 h1)
      have hVy : V1 = {y} := by
        rcases bip_star U' V1 hU'V hU'ne hV1ne with ⟨x, hUx, _⟩ | ⟨y', hVy', _⟩
        · rw [hUx] at hUge2; simp at hUge2
        · have hyin : y ∈ V1 := (Finset.mem_inter.1 (hY0eq ▸ (by rw [hY0y]; simp : y ∈ Y0))).2
          rw [hVy', Finset.mem_singleton] at hyin
          rw [hVy', ← hyin]
      have hcov_y : ∀ s t : Fin 26, val C.gates (26 + (jF : ℕ)) (pr s t) = true →
          (s = y ∧ t ∈ U' ∪ B0) ∨ (t = y ∧ s ∈ U' ∪ B0) := by
        intro s t hst
        rcases hcov2 s t hst with h1 | h2
        · rcases h1 with ⟨hs, ht⟩ | ⟨ht, hs⟩
          · rw [hVy, Finset.mem_singleton] at ht; exact Or.inr ⟨ht, Finset.mem_union_left _ hs⟩
          · rw [hVy, Finset.mem_singleton] at hs; exact Or.inl ⟨hs, Finset.mem_union_left _ ht⟩
        · rcases h2 with ⟨hs, ht⟩ | ⟨ht, hs⟩
          · rw [hY0y, Finset.mem_singleton] at hs; exact Or.inl ⟨hs, Finset.mem_union_right _ ht⟩
          · rw [hY0y, Finset.mem_singleton] at ht; exact Or.inr ⟨ht, Finset.mem_union_right _ hs⟩
      by_cases hiUS : iF ∈ US C.gates C.output
      · refine finish_one_star_thm C.gates C.output H jF zk Ak lwk hoth y U' u1 (some y) hU'sub hu1_sing
          (cOf_false_of_zero C.gates C.output H u1 y) ?_
        intro s t _ hst
        rcases hcov2 s t hst with h1 | h2
        · left
          rcases h1 with ⟨hs, ht⟩ | ⟨ht, hs⟩
          · rw [hVy, Finset.mem_singleton] at ht; exact Or.inr ⟨ht, hs⟩
          · rw [hVy, Finset.mem_singleton] at hs; exact Or.inl ⟨hs, ht⟩
        · right
          refine ⟨iF, hiUS, hneij, ?_⟩
          rw [hi0_0]
          rcases h2 with ⟨hs, ht⟩ | ⟨ht, hs⟩
          · exact ⟨⟨s, (Finset.mem_inter.1 (hY0eq ▸ hs)).1, by simp [pr]⟩, ⟨t, ht, by simp [pr]⟩⟩
          · exact ⟨⟨t, (Finset.mem_inter.1 (hY0eq ▸ ht)).1, by simp [pr]⟩, ⟨s, hs, by simp [pr]⟩⟩
      · by_cases hInt : (U' ∩ B0).Nonempty
        · exact finish_plus1_thm C.gates C.output H iF jF hi0op hjUS zk Ak lwk hoth
            y U' B0 u1 b0 hU'sub hBsub hUge2 hInt hu1_sing
            (fun p hp => (hB0 _).2 ⟨p, hp, by simp⟩) (fun s t _ => hcov_y s t) hiUS
        · have hdisjUB : Disjoint U' B0 := Finset.disjoint_iff_inter_eq_empty.2
            (Finset.not_nonempty_iff_eq_empty.1 hInt)
          have hi0z : ∀ r : Fin 26, val C.gates (26 + (iF : ℕ)) (fun u => decide (u = r)) = false := by
            intro r
            cases hv : val C.gates (26 + (iF : ℕ)) (fun u => decide (u = r)) with
            | false => rfl
            | true =>
              exfalso
              rw [hi0_0] at hv
              obtain ⟨⟨a1, ha1, h1⟩, ⟨b1, hb1, h2⟩⟩ := hv
              have e1 : a1 = r := of_decide_eq_true h1
              have e2 : b1 = r := of_decide_eq_true h2
              rw [e1] at ha1; rw [e2] at hb1
              have hrU : r ∈ U' := by
                rw [hU'eq]; exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨ha1, hb1⟩)
              exact Finset.disjoint_left.1 hdisjUB hrU hb1
          obtain ⟨u0, hu0⟩ := hU'ne
          obtain ⟨m, hm_or, hmsing, hmzero⟩ := mix_gate C iF H.1 H.2.1 H.2.2.1 hi0z u1 hIu hnou1
            ⟨u0, hu1_sing u0 hu0⟩
          have hne_im : iF ≠ m := by
            intro e; rw [← e] at hm_or; rw [hi0op] at hm_or; exact GateOp.noConfusion hm_or
          refine finish_two_stars_thm C.gates C.output H jF zk Ak lwk hoth
            y U' u1 y B0 b0 (some y) {iF, m}
            hU'sub hu1_sing (cOf_false_of_zero C.gates C.output H u1 y)
            hBsub (fun p hp => (hB0 _).2 ⟨p, hp, by simp⟩)
            (cOf_false_of_zero C.gates C.output H b0 y) ?_ ?_ (by rw [Finset.card_pair hne_im])
          · intro s t _ hst
            rcases hcov2 s t hst with h1 | h2
            · left
              rcases h1 with ⟨hs, ht⟩ | ⟨ht, hs⟩
              · rw [hVy, Finset.mem_singleton] at ht; exact Or.inr ⟨ht, hs⟩
              · rw [hVy, Finset.mem_singleton] at hs; exact Or.inl ⟨hs, ht⟩
            · right; left
              rcases h2 with ⟨hs, ht⟩ | ⟨ht, hs⟩
              · rw [hY0y, Finset.mem_singleton] at hs; exact Or.inl ⟨hs, ht⟩
              · rw [hY0y, Finset.mem_singleton] at ht; exact Or.inr ⟨ht, hs⟩
          · intro g hg
            rcases Finset.mem_insert.1 hg with hg' | hg'
            · rw [hg']; exact and_gate_disj C.gates C.output (some y) iF hi0op hiUS
            · rw [Finset.mem_singleton.1 hg']
              exact mix_gate_disj C.gates C.output H (some y) m hm_or hmsing hmzero

open Classical in
theorem handle_sing_YZ (C : Circuit) (H : Hy0 C.gates C.output)
    (iF jF : Fin C.gates.length) (hi0op : (C.gates.get iF).op = GateOp.and) (hneij : iF ≠ jF)
    (zk : Fin C.gates.length → Fin 26) (Ak : Fin C.gates.length → Finset (Fin 26))
    (lwk : Fin C.gates.length → ℕ) (hoth : OtherStars C.gates C.output jF zk Ak lwk)
    (v1 ai bi : ℕ) (V1 A B : Finset (Fin 26))
    (hV1' : ∀ x : Fin 26 → Bool, val C.gates v1 x = true ↔ ∃ v ∈ V1, x v = true)
    (hA : ∀ x : Fin 26 → Bool, val C.gates ai x = true ↔ ∃ v ∈ A, x v = true)
    (hB : ∀ x : Fin 26 → Bool, val C.gates bi x = true ↔ ∃ v ∈ B, x v = true)
    (hi0_val : ∀ x : Fin 26 → Bool, val C.gates (26 + (iF : ℕ)) x = true ↔
      (∃ v ∈ A, x v = true) ∧ (∃ v ∈ B, x v = true))
    (hYB : ∀ s ∈ A ∩ V1, ∀ t ∈ B, adjb s t = true)
    (hZA : ∀ s ∈ B ∩ V1, ∀ t ∈ A, adjb s t = true)
    (hcovYZ : ∀ s t : Fin 26, val C.gates (26 + (jF : ℕ)) (pr s t) = true →
      ((s ∈ A ∩ V1 ∧ t ∈ B) ∨ (t ∈ A ∩ V1 ∧ s ∈ B)) ∨
      ((s ∈ B ∩ V1 ∧ t ∈ A) ∨ (t ∈ B ∩ V1 ∧ s ∈ A)))
    (y z : Fin 26) (hYy : A ∩ V1 = {y}) (hZz : B ∩ V1 = {z}) :
    64 ≤ C.gates.length := by
  have hyin : y ∈ A ∩ V1 := by rw [hYy]; simp
  have hzin : z ∈ B ∩ V1 := by rw [hZz]; simp
  have hyz : adjb y z = true := hYB y hyin z (Finset.mem_inter.1 hzin).1
  have hBsub : B ⊆ N y := fun t ht => (mem_N y t).2 (hYB y hyin t ht)
  have hAsub : A ⊆ N z := fun t ht => (mem_N z t).2 (hZA z hzin t ht)
  by_cases hiUS : iF ∈ US C.gates C.output
  · apply finish_no_j_thm C.gates C.output H jF zk Ak lwk hoth
    intro s t hadj
    obtain ⟨k, hk, hv⟩ := cover C.gates C.output H s t hadj
    by_cases e : k = jF
    · subst e
      refine ⟨iF, hiUS, hneij, ?_⟩
      rw [hi0_val]
      rcases hcovYZ s t hv with h1 | h2
      · rcases h1 with ⟨hs, ht⟩ | ⟨ht, hs⟩
        · exact ⟨⟨s, (Finset.mem_inter.1 hs).1, by simp [pr]⟩, ⟨t, ht, by simp [pr]⟩⟩
        · exact ⟨⟨t, (Finset.mem_inter.1 ht).1, by simp [pr]⟩, ⟨s, hs, by simp [pr]⟩⟩
      · rcases h2 with ⟨hs, ht⟩ | ⟨ht, hs⟩
        · exact ⟨⟨t, ht, by simp [pr]⟩, ⟨s, (Finset.mem_inter.1 hs).1, by simp [pr]⟩⟩
        · exact ⟨⟨s, hs, by simp [pr]⟩, ⟨t, (Finset.mem_inter.1 ht).1, by simp [pr]⟩⟩
    · exact ⟨k, hk, e, hv⟩
  · have hyV : y ∈ V1 := (Finset.mem_inter.1 hyin).2
    have hzV : z ∈ V1 := (Finset.mem_inter.1 hzin).2
    obtain ⟨m, hm_or, hmy, hmz⟩ := cross_gate C.gates H.1 H.2.1 H.2.2.1 v1 y z hyz
      ((hV1' _).2 ⟨y, hyV, by simp⟩) ((hV1' _).2 ⟨z, hzV, by simp⟩)
    have hne_im : iF ≠ m := by
      intro e; rw [← e] at hm_or; rw [hi0op] at hm_or; exact GateOp.noConfusion hm_or
    refine finish_two_stars_thm C.gates C.output H jF zk Ak lwk hoth y B bi z A ai none {iF, m}
      hBsub (fun p hp => (hB _).2 ⟨p, hp, by simp⟩)
      (by simpa [cOf] using star_false_outside C.gates bi B y hB hBsub)
      hAsub (fun p hp => (hA _).2 ⟨p, hp, by simp⟩)
      (by simpa [cOf] using star_false_outside C.gates ai A z hA hAsub)
      ?_ ?_ (by rw [Finset.card_pair hne_im])
    · intro s t _ hst
      rcases hcovYZ s t hst with h1 | h2
      · left
        rcases h1 with ⟨hs, ht⟩ | ⟨ht, hs⟩
        · rw [hYy, Finset.mem_singleton] at hs; exact Or.inl ⟨hs, ht⟩
        · rw [hYy, Finset.mem_singleton] at ht; exact Or.inr ⟨ht, hs⟩
      · right; left
        rcases h2 with ⟨hs, ht⟩ | ⟨ht, hs⟩
        · rw [hZz, Finset.mem_singleton] at hs; exact Or.inl ⟨hs, ht⟩
        · rw [hZz, Finset.mem_singleton] at ht; exact Or.inr ⟨ht, hs⟩
    · intro g hg
      rcases Finset.mem_insert.1 hg with hg' | hg'
      · rw [hg']; exact and_gate_disj C.gates C.output none iF hi0op hiUS
      · rw [Finset.mem_singleton.1 hg']
        exact cross_gate_disj C.gates C.output H m y z hyz hm_or hmy hmz

open Classical in
theorem case_one_side_thm (C : Circuit) (H : Hy0 C.gates C.output)
    (iF jF : Fin C.gates.length) (hi0op : (C.gates.get iF).op = GateOp.and)
    (hjUS : jF ∈ US C.gates C.output) (hneij : iF ≠ jF)
    (zk : Fin C.gates.length → Fin 26) (Ak : Fin C.gates.length → Finset (Fin 26))
    (lwk : Fin C.gates.length → ℕ) (hoth : OtherStars C.gates C.output jF zk Ak lwk)
    (ai bi u1 v1 : ℕ) (A B U1 V1 : Finset (Fin 26))
    (hA : ∀ x : Fin 26 → Bool, val C.gates ai x = true ↔ ∃ v ∈ A, x v = true)
    (hB : ∀ x : Fin 26 → Bool, val C.gates bi x = true ↔ ∃ v ∈ B, x v = true)
    (hi0_val : ∀ x : Fin 26 → Bool, val C.gates (26 + (iF : ℕ)) x = true ↔
      (∃ v ∈ A, x v = true) ∧ (∃ v ∈ B, x v = true))
    (hIu : HasI C iF u1) (hnv : ¬ HasI C iF v1) (hnou1 : NoOtherAnd C iF u1)
    (hjv : ∀ x : Fin 26 → Bool, val C.gates (26 + (jF : ℕ)) x = true ↔
      val C.gates u1 x = true ∧ val C.gates v1 x = true)
    (hU1 : ∀ x : Fin 26 → Bool, val C.gates u1 x = true ↔
      (HasI C iF u1 ∧ val C.gates (26 + (iF : ℕ)) x = true) ∨ ∃ v ∈ U1, x v = true)
    (hV1 : ∀ x : Fin 26 → Bool, val C.gates v1 x = true ↔
      (HasI C iF v1 ∧ val C.gates (26 + (iF : ℕ)) x = true) ∨ ∃ v ∈ V1, x v = true) :
    64 ≤ C.gates.length := by
  have hrj : Reach C.gates C.output (26 + (jF : ℕ)) := ((mem_US _ _ jF).1 hjUS).2.1
  have hV1' : ∀ x : Fin 26 → Bool, val C.gates v1 x = true ↔ ∃ v ∈ V1, x v = true := by
    intro x; rw [hV1 x]; simp [hnv]
  have hU1' : ∀ x : Fin 26 → Bool, val C.gates u1 x = true ↔
      val C.gates (26 + (iF : ℕ)) x = true ∨ ∃ v ∈ U1, x v = true := by
    intro x; rw [hU1 x]; simp [hIu]
  let X : Finset (Fin 26) := A ∩ B
  let U' : Finset (Fin 26) := U1 ∪ X
  let Y : Finset (Fin 26) := A ∩ V1
  let Z : Finset (Fin 26) := B ∩ V1
  have hU'V : ∀ s ∈ U', ∀ t ∈ V1, adjb s t = true := by
    intro s hs t ht
    apply reach_adj C.gates C.output H _ hrj s t
    rw [hjv, hU1', hV1']
    refine ⟨?_, ⟨t, ht, by simp [pr]⟩⟩
    rcases Finset.mem_union.1 hs with hs1 | hs2
    · exact Or.inr ⟨s, hs1, by simp [pr]⟩
    · left
      rw [hi0_val]
      exact ⟨⟨s, (Finset.mem_inter.1 hs2).1, by simp [pr]⟩,
             ⟨s, (Finset.mem_inter.1 hs2).2, by simp [pr]⟩⟩
  have hYB : ∀ s ∈ Y, ∀ t ∈ B, adjb s t = true := by
    intro s hs t ht
    apply reach_adj C.gates C.output H _ hrj s t
    rw [hjv, hU1', hV1', hi0_val]
    exact ⟨Or.inl ⟨⟨s, (Finset.mem_inter.1 hs).1, by simp [pr]⟩, ⟨t, ht, by simp [pr]⟩⟩,
           ⟨s, (Finset.mem_inter.1 hs).2, by simp [pr]⟩⟩
  have hZA : ∀ s ∈ Z, ∀ t ∈ A, adjb s t = true := by
    intro s hs t ht
    apply reach_adj C.gates C.output H _ hrj s t
    rw [hjv, hU1', hV1', hi0_val]
    exact ⟨Or.inl ⟨⟨t, ht, by simp [pr]⟩, ⟨s, (Finset.mem_inter.1 hs).1, by simp [pr]⟩⟩,
           ⟨s, (Finset.mem_inter.1 hs).2, by simp [pr]⟩⟩
  have hcov_dec : ∀ s t : Fin 26, val C.gates (26 + (jF : ℕ)) (pr s t) = true →
      ((s ∈ U' ∧ t ∈ V1) ∨ (t ∈ U' ∧ s ∈ V1)) ∨
      ((s ∈ Y ∧ t ∈ B) ∨ (t ∈ Y ∧ s ∈ B)) ∨
      ((s ∈ Z ∧ t ∈ A) ∨ (t ∈ Z ∧ s ∈ A)) := by
    intro s t hst
    rw [hjv, hU1', hV1'] at hst
    obtain ⟨hleft, v, hvV, hvp⟩ := hst
    have hvs : v = s ∨ v = t := of_decide_eq_true hvp
    rcases hleft with hi_t | ⟨u, huU, hup⟩
    · rw [hi0_val] at hi_t
      obtain ⟨⟨a1, ha1, hap⟩, ⟨b1, hb1, hbp⟩⟩ := hi_t
      have has : a1 = s ∨ a1 = t := of_decide_eq_true hap
      have hbs : b1 = s ∨ b1 = t := of_decide_eq_true hbp
      rcases hvs with rfl | rfl <;> rcases has with rfl | rfl <;> rcases hbs with rfl | rfl
      · exfalso
        have hf := hU'V _ (Finset.mem_union_right _ (Finset.mem_inter.2 ⟨ha1, hb1⟩)) _ hvV
        rw [adj_irr] at hf; exact Bool.noConfusion hf
      · right; left; left; exact ⟨Finset.mem_inter.2 ⟨ha1, hvV⟩, hb1⟩
      · right; right; left; exact ⟨Finset.mem_inter.2 ⟨hb1, hvV⟩, ha1⟩
      · left; right; exact ⟨Finset.mem_union_right _ (Finset.mem_inter.2 ⟨ha1, hb1⟩), hvV⟩
      · left; left; exact ⟨Finset.mem_union_right _ (Finset.mem_inter.2 ⟨ha1, hb1⟩), hvV⟩
      · right; right; right; exact ⟨Finset.mem_inter.2 ⟨hb1, hvV⟩, ha1⟩
      · right; left; right; exact ⟨Finset.mem_inter.2 ⟨ha1, hvV⟩, hb1⟩
      · exfalso
        have hf := hU'V _ (Finset.mem_union_right _ (Finset.mem_inter.2 ⟨ha1, hb1⟩)) _ hvV
        rw [adj_irr] at hf; exact Bool.noConfusion hf
    · rcases of_decide_eq_true hup with rfl | rfl <;> rcases hvs with rfl | rfl
      · exfalso
        have hf := hU'V _ (Finset.mem_union_left _ huU) _ hvV
        rw [adj_irr] at hf; exact Bool.noConfusion hf
      · left; left; exact ⟨Finset.mem_union_left _ huU, hvV⟩
      · left; right; exact ⟨Finset.mem_union_left _ huU, hvV⟩
      · exfalso
        have hf := hU'V _ (Finset.mem_union_left _ huU) _ hvV
        rw [adj_irr] at hf; exact Bool.noConfusion hf
  have hu1_sing : ∀ p ∈ U', val C.gates u1 (fun u => decide (u = p)) = true := by
    intro p hp
    rw [hU1']
    rcases Finset.mem_union.1 hp with hp1 | hp2
    · exact Or.inr ⟨p, hp1, by simp⟩
    · left
      rw [hi0_val]
      exact ⟨⟨p, (Finset.mem_inter.1 hp2).1, by simp⟩,
             ⟨p, (Finset.mem_inter.1 hp2).2, by simp⟩⟩
  have hno_all3 : ¬ (U'.Nonempty ∧ Y.Nonempty ∧ Z.Nonempty) := by
    rintro ⟨⟨u, hu⟩, ⟨y, hy⟩, ⟨z, hz⟩⟩
    have h1 := hU'V u hu y (Finset.mem_inter.1 hy).2
    have h2 := hU'V u hu z (Finset.mem_inter.1 hz).2
    have h3 := hZA z hz y (Finset.mem_inter.1 hy).1
    rw [adj_symm] at h3
    exact adj_no_tri u y z h1 h2 h3
  by_cases hU'ne : U'.Nonempty
  · by_cases hYne : Y.Nonempty
    · have hZe : Z = ∅ := by
        by_contra hne
        exact hno_all3 ⟨hU'ne, hYne, Finset.nonempty_iff_ne_empty.2 hne⟩
      refine handle_U'Y_thm C H iF jF hi0op hjUS hneij zk Ak lwk hoth u1 v1 ai bi U1 V1 A B U' Y
        hIu hnou1 hV1' hA hB hi0_val hu1_sing rfl rfl hU'V hYB ?_ hU'ne hYne
      intro s t hst
      rcases hcov_dec s t hst with h1 | h2 | h3
      · exact Or.inl h1
      · exact Or.inr h2
      · rw [hZe] at h3; simp at h3
    · have hYe : Y = ∅ := Finset.not_nonempty_iff_eq_empty.1 hYne
      by_cases hZne : Z.Nonempty
      · refine handle_U'Y_thm C H iF jF hi0op hjUS hneij zk Ak lwk hoth u1 v1 bi ai U1 V1 B A U' Z
          hIu hnou1 hV1' hB hA (fun x => by rw [hi0_val, and_comm]) hu1_sing rfl
          (by simp [U', X, Finset.inter_comm]) hU'V hZA ?_ hU'ne hZne
        intro s t hst
        rcases hcov_dec s t hst with h1 | h2 | h3
        · exact Or.inl h1
        · rw [hYe] at h2; simp at h2
        · exact Or.inr h3
      · have hZe : Z = ∅ := Finset.not_nonempty_iff_eq_empty.1 hZne
        by_cases hVne : V1.Nonempty
        · rcases bip_star U' V1 hU'V hU'ne hVne with ⟨x, hUx, hVsub⟩ | ⟨y, hVy, hUsub⟩
          · refine finish_one_star_thm C.gates C.output H jF zk Ak lwk hoth x V1 v1 none hVsub
              (fun p hp => (hV1' _).2 ⟨p, hp, by simp⟩)
              (by simpa [cOf] using star_false_outside C.gates v1 V1 x hV1' hVsub) ?_
            intro s t _ hst
            rcases hcov_dec s t hst with h1 | h2 | h3
            · left
              rcases h1 with ⟨hs, ht⟩ | ⟨ht, hs⟩
              · rw [hUx, Finset.mem_singleton] at hs; exact Or.inl ⟨hs, ht⟩
              · rw [hUx, Finset.mem_singleton] at ht; exact Or.inr ⟨ht, hs⟩
            · rw [hYe] at h2; simp at h2
            · rw [hZe] at h3; simp at h3
          · refine finish_one_star_thm C.gates C.output H jF zk Ak lwk hoth y U' u1 (some y) hUsub hu1_sing
              (cOf_false_of_zero C.gates C.output H u1 y) ?_
            intro s t _ hst
            rcases hcov_dec s t hst with h1 | h2 | h3
            · left
              rcases h1 with ⟨hs, ht⟩ | ⟨ht, hs⟩
              · rw [hVy, Finset.mem_singleton] at ht; exact Or.inr ⟨ht, hs⟩
              · rw [hVy, Finset.mem_singleton] at hs; exact Or.inl ⟨hs, ht⟩
            · rw [hYe] at h2; simp at h2
            · rw [hZe] at h3; simp at h3
        · have hVe : V1 = ∅ := Finset.not_nonempty_iff_eq_empty.1 hVne
          obtain ⟨_, _, s0, t0, h0⟩ := (mem_US C.gates C.output jF).1 hjUS
          rcases hcov_dec s0 t0 h0 with h1 | h2 | h3
          · rw [hVe] at h1; simp at h1
          · rw [hYe] at h2; simp at h2
          · rw [hZe] at h3; simp at h3
  · have hU'e : U' = ∅ := Finset.not_nonempty_iff_eq_empty.1 hU'ne
    have handle_one_Y :
        ∀ (A0 B0 : Finset (Fin 26)) (b0 : ℕ) (Y0 : Finset (Fin 26)),
          (∀ x : Fin 26 → Bool, val C.gates b0 x = true ↔ ∃ v ∈ B0, x v = true) →
          Y0 = A0 ∩ V1 →
          (∀ s ∈ Y0, ∀ t ∈ B0, adjb s t = true) →
          (∀ s t : Fin 26, val C.gates (26 + (jF : ℕ)) (pr s t) = true →
            (s ∈ Y0 ∧ t ∈ B0) ∨ (t ∈ Y0 ∧ s ∈ B0)) →
          Y0.Nonempty →
          64 ≤ C.gates.length := by
      intro A0 B0 b0 Y0 hB0 hY0eq hY0B0 hcov1 hY0ne
      by_cases hB0ne : B0.Nonempty
      · rcases bip_star Y0 B0 hY0B0 hY0ne hB0ne with ⟨y, hYy, hBsub⟩ | ⟨b1, hBb1, hYsub⟩
        · refine finish_one_star_thm C.gates C.output H jF zk Ak lwk hoth y B0 b0 none hBsub
            (fun p hp => (hB0 _).2 ⟨p, hp, by simp⟩)
            (by simpa [cOf] using star_false_outside C.gates b0 B0 y hB0 hBsub) ?_
          intro s t _ hst
          left
          rcases hcov1 s t hst with ⟨hs, ht⟩ | ⟨ht, hs⟩
          · rw [hYy, Finset.mem_singleton] at hs; exact Or.inl ⟨hs, ht⟩
          · rw [hYy, Finset.mem_singleton] at ht; exact Or.inr ⟨ht, hs⟩
        · refine finish_one_star_thm C.gates C.output H jF zk Ak lwk hoth b1 Y0 v1 (some b1) hYsub
            (fun p hp => (hV1' _).2 ⟨p, (Finset.mem_inter.1 (hY0eq ▸ hp)).2, by simp⟩)
            (cOf_false_of_zero C.gates C.output H v1 b1) ?_
          intro s t _ hst
          left
          rcases hcov1 s t hst with ⟨hs, ht⟩ | ⟨ht, hs⟩
          · rw [hBb1, Finset.mem_singleton] at ht; exact Or.inr ⟨ht, hs⟩
          · rw [hBb1, Finset.mem_singleton] at hs; exact Or.inl ⟨hs, ht⟩
      · have hB0e : B0 = ∅ := Finset.not_nonempty_iff_eq_empty.1 hB0ne
        obtain ⟨_, _, s0, t0, h0⟩ := (mem_US C.gates C.output jF).1 hjUS
        have hc := hcov1 s0 t0 h0
        rw [hB0e] at hc; simp at hc
    by_cases hYne : Y.Nonempty
    · by_cases hZne : Z.Nonempty
      · have hYZ : ∀ y ∈ Y, ∀ z ∈ Z, adjb y z = true := fun y hy z hz =>
          hYB y hy z (Finset.mem_inter.1 hz).1
        have hAne : A.Nonempty := by
          obtain ⟨y, hy⟩ := hYne; exact ⟨y, (Finset.mem_inter.1 hy).1⟩
        have hBne : B.Nonempty := by
          obtain ⟨z, hz⟩ := hZne; exact ⟨z, (Finset.mem_inter.1 hz).1⟩
        have hcovYZ : ∀ s t : Fin 26, val C.gates (26 + (jF : ℕ)) (pr s t) = true →
            ((s ∈ Y ∧ t ∈ B) ∨ (t ∈ Y ∧ s ∈ B)) ∨ ((s ∈ Z ∧ t ∈ A) ∨ (t ∈ Z ∧ s ∈ A)) := by
          intro s t hst
          rcases hcov_dec s t hst with h1 | h2 | h3
          · rw [hU'e] at h1; simp at h1
          · exact Or.inl h2
          · exact Or.inr h3
        rcases bip_star Y Z hYZ hYne hZne with ⟨y, hYy, _⟩ | ⟨z, hZz, _⟩
        · by_cases hZ1 : ∃ z : Fin 26, Z = {z}
          · obtain ⟨z, hZz⟩ := hZ1
            exact handle_sing_YZ C H iF jF hi0op hneij zk Ak lwk hoth v1 ai bi V1 A B
              hV1' hA hB hi0_val hYB hZA hcovYZ y z hYy hZz
          · have hZge2 : 2 ≤ Z.card := by
              by_contra hlt
              have h1 : Z.card = 1 := by have hp := Finset.card_pos.2 hZne; omega
              exact hZ1 (Finset.card_eq_one.1 h1)
            have hAy : A = {y} := by
              rcases bip_star Z A hZA hZne hAne with ⟨z, hZz, _⟩ | ⟨a1, hAa1, _⟩
              · rw [hZz] at hZge2; simp at hZge2
              · have hyA : y ∈ A := (Finset.mem_inter.1 (by rw [hYy]; simp : y ∈ Y)).1
                rw [hAa1, Finset.mem_singleton] at hyA
                rw [hAa1, ← hyA]
            have hBsub : B ⊆ N y := fun t ht => (mem_N y t).2 (hYB y (by rw [hYy]; simp) t ht)
            refine finish_one_star_thm C.gates C.output H jF zk Ak lwk hoth y B bi none hBsub
              (fun p hp => (hB _).2 ⟨p, hp, by simp⟩)
              (by simpa [cOf] using star_false_outside C.gates bi B y hB hBsub) ?_
            intro s t _ hst
            left
            rcases hcovYZ s t hst with h1 | h2
            · rcases h1 with ⟨hs, ht⟩ | ⟨ht, hs⟩
              · rw [hYy, Finset.mem_singleton] at hs; exact Or.inl ⟨hs, ht⟩
              · rw [hYy, Finset.mem_singleton] at ht; exact Or.inr ⟨ht, hs⟩
            · rcases h2 with ⟨hs, ht⟩ | ⟨ht, hs⟩
              · rw [hAy, Finset.mem_singleton] at ht; exact Or.inr ⟨ht, (Finset.mem_inter.1 hs).1⟩
              · rw [hAy, Finset.mem_singleton] at hs; exact Or.inl ⟨hs, (Finset.mem_inter.1 ht).1⟩
        · by_cases hY1 : ∃ y : Fin 26, Y = {y}
          · obtain ⟨y, hYy⟩ := hY1
            exact handle_sing_YZ C H iF jF hi0op hneij zk Ak lwk hoth v1 ai bi V1 A B
              hV1' hA hB hi0_val hYB hZA hcovYZ y z hYy hZz
          · have hYge2 : 2 ≤ Y.card := by
              by_contra hlt
              have h1 : Y.card = 1 := by have hp := Finset.card_pos.2 hYne; omega
              exact hY1 (Finset.card_eq_one.1 h1)
            have hBz : B = {z} := by
              rcases bip_star Y B hYB hYne hBne with ⟨y, hYy, _⟩ | ⟨b1, hBb1, _⟩
              · rw [hYy] at hYge2; simp at hYge2
              · have hzB : z ∈ B := (Finset.mem_inter.1 (by rw [hZz]; simp : z ∈ Z)).1
                rw [hBb1, Finset.mem_singleton] at hzB
                rw [hBb1, ← hzB]
            have hAsub : A ⊆ N z := fun t ht => (mem_N z t).2 (hZA z (by rw [hZz]; simp) t ht)
            refine finish_one_star_thm C.gates C.output H jF zk Ak lwk hoth z A ai none hAsub
              (fun p hp => (hA _).2 ⟨p, hp, by simp⟩)
              (by simpa [cOf] using star_false_outside C.gates ai A z hA hAsub) ?_
            intro s t _ hst
            left
            rcases hcovYZ s t hst with h1 | h2
            · rcases h1 with ⟨hs, ht⟩ | ⟨ht, hs⟩
              · rw [hBz, Finset.mem_singleton] at ht; exact Or.inr ⟨ht, (Finset.mem_inter.1 hs).1⟩
              · rw [hBz, Finset.mem_singleton] at hs; exact Or.inl ⟨hs, (Finset.mem_inter.1 ht).1⟩
            · rcases h2 with ⟨hs, ht⟩ | ⟨ht, hs⟩
              · rw [hZz, Finset.mem_singleton] at hs; exact Or.inl ⟨hs, ht⟩
              · rw [hZz, Finset.mem_singleton] at ht; exact Or.inr ⟨ht, hs⟩
      · have hZe : Z = ∅ := Finset.not_nonempty_iff_eq_empty.1 hZne
        refine handle_one_Y A B bi Y hB rfl hYB ?_ hYne
        intro s t hst
        rcases hcov_dec s t hst with h1 | h2 | h3
        · rw [hU'e] at h1; simp at h1
        · exact h2
        · rw [hZe] at h3; simp at h3
    · have hYe : Y = ∅ := Finset.not_nonempty_iff_eq_empty.1 hYne
      by_cases hZne : Z.Nonempty
      · refine handle_one_Y B A ai Z hA rfl hZA ?_ hZne
        intro s t hst
        rcases hcov_dec s t hst with h1 | h2 | h3
        · rw [hU'e] at h1; simp at h1
        · rw [hYe] at h2; simp at h2
        · exact h3
      · have hZe : Z = ∅ := Finset.not_nonempty_iff_eq_empty.1 hZne
        obtain ⟨_, _, s0, t0, h0⟩ := (mem_US C.gates C.output jF).1 hjUS
        rcases hcov_dec s0 t0 h0 with h1 | h2 | h3
        · rw [hU'e] at h1; simp at h1
        · rw [hYe] at h2; simp at h2
        · rw [hZe] at h3; simp at h3

open Classical in
theorem case_both_sides_thm (C : Circuit) (H : Hy0 C.gates C.output)
    (iF jF : Fin C.gates.length) (hi0op : (C.gates.get iF).op = GateOp.and)
    (hjUS : jF ∈ US C.gates C.output) (hneij : iF ≠ jF)
    (zk : Fin C.gates.length → Fin 26) (Ak : Fin C.gates.length → Finset (Fin 26))
    (lwk : Fin C.gates.length → ℕ) (hoth : OtherStars C.gates C.output jF zk Ak lwk)
    (ai bi uj vj : ℕ) (A B U V : Finset (Fin 26))
    (hA : ∀ x : Fin 26 → Bool, val C.gates ai x = true ↔ ∃ v ∈ A, x v = true)
    (hB : ∀ x : Fin 26 → Bool, val C.gates bi x = true ↔ ∃ v ∈ B, x v = true)
    (hi0_val : ∀ x : Fin 26 → Bool, val C.gates (26 + (iF : ℕ)) x = true ↔
      (∃ v ∈ A, x v = true) ∧ (∃ v ∈ B, x v = true))
    (hIu : HasI C iF uj) (hIv : HasI C iF vj) (hnou : NoOtherAnd C iF uj)
    (hj0_val : ∀ x : Fin 26 → Bool, val C.gates (26 + (jF : ℕ)) x = true ↔
      val C.gates uj x = true ∧ val C.gates vj x = true)
    (hU : ∀ x : Fin 26 → Bool, val C.gates uj x = true ↔
      (HasI C iF uj ∧ val C.gates (26 + (iF : ℕ)) x = true) ∨ ∃ v ∈ U, x v = true)
    (hV : ∀ x : Fin 26 → Bool, val C.gates vj x = true ↔
      (HasI C iF vj ∧ val C.gates (26 + (iF : ℕ)) x = true) ∨ ∃ v ∈ V, x v = true) :
    64 ≤ C.gates.length := by
  have hrj : Reach C.gates C.output (26 + (jF : ℕ)) := ((mem_US _ _ jF).1 hjUS).2.1
  have hj_eq : ∀ x : Fin 26 → Bool, val C.gates (26 + (jF : ℕ)) x = true ↔
      val C.gates (26 + (iF : ℕ)) x = true ∨ ((∃ u ∈ U, x u = true) ∧ (∃ v ∈ V, x v = true)) := by
    intro x
    rw [hj0_val, hU, hV]
    simp only [hIu, hIv, true_and]
    tauto
  have hAB : ∀ a ∈ A, ∀ b ∈ B, adjb a b = true := by
    intro a ha b hb
    apply reach_adj C.gates C.output H _ hrj a b
    rw [hj_eq]; left; rw [hi0_val]
    exact ⟨⟨a, ha, by simp [pr]⟩, ⟨b, hb, by simp [pr]⟩⟩
  have hUV : ∀ u ∈ U, ∀ v ∈ V, adjb u v = true := by
    intro u hu v hv
    apply reach_adj C.gates C.output H _ hrj u v
    rw [hj_eq]; right
    exact ⟨⟨u, hu, by simp [pr]⟩, ⟨v, hv, by simp [pr]⟩⟩
  have hi0z : ∀ r : Fin 26, val C.gates (26 + (iF : ℕ)) (fun u => decide (u = r)) = false := by
    intro r
    cases hv : val C.gates (26 + (iF : ℕ)) (fun u => decide (u = r)) with
    | false => rfl
    | true =>
      exfalso
      rw [hi0_val] at hv
      obtain ⟨⟨a1, ha1, h1⟩, ⟨b1, hb1, h2⟩⟩ := hv
      have e1 : a1 = r := of_decide_eq_true h1
      have e2 : b1 = r := of_decide_eq_true h2
      rw [e1] at ha1; rw [e2] at hb1
      have hadj := hAB r ha1 r hb1
      rw [adj_irr] at hadj
      exact Bool.noConfusion hadj
  have hcov_both : ∀ s t : Fin 26, val C.gates (26 + (jF : ℕ)) (pr s t) = true →
      ((s ∈ A ∧ t ∈ B) ∨ (t ∈ A ∧ s ∈ B)) ∨ ((s ∈ U ∧ t ∈ V) ∨ (t ∈ U ∧ s ∈ V)) := by
    intro s t hst
    rw [hj_eq] at hst
    rcases hst with hi_t | ⟨⟨u, hu, hup⟩, ⟨v, hv, hvp⟩⟩
    · left
      rw [hi0_val] at hi_t
      obtain ⟨⟨a1, ha1, hap⟩, ⟨b1, hb1, hbp⟩⟩ := hi_t
      rcases of_decide_eq_true hap with rfl | rfl <;> rcases of_decide_eq_true hbp with rfl | rfl
      · have hf := hAB _ ha1 _ hb1; rw [adj_irr] at hf; exact Bool.noConfusion hf
      · exact Or.inl ⟨ha1, hb1⟩
      · exact Or.inr ⟨ha1, hb1⟩
      · have hf := hAB _ ha1 _ hb1; rw [adj_irr] at hf; exact Bool.noConfusion hf
    · right
      rcases of_decide_eq_true hup with rfl | rfl <;> rcases of_decide_eq_true hvp with rfl | rfl
      · have hf := hUV _ hu _ hv; rw [adj_irr] at hf; exact Bool.noConfusion hf
      · exact Or.inl ⟨hu, hv⟩
      · exact Or.inr ⟨hu, hv⟩
      · have hf := hUV _ hu _ hv; rw [adj_irr] at hf; exact Bool.noConfusion hf
  have hstar_UV : U.Nonempty → V.Nonempty →
      ∃ (zu : Fin 26) (Au : Finset (Fin 26)) (lwu : ℕ), Au ⊆ N zu ∧
        (∀ p ∈ Au, val C.gates lwu (fun u => decide (u = p)) = true) ∧
        val C.gates lwu (cOf (some zu) zu) = false ∧
        ∀ s t : Fin 26, ((s ∈ U ∧ t ∈ V) ∨ (t ∈ U ∧ s ∈ V)) →
          (s = zu ∧ t ∈ Au) ∨ (t = zu ∧ s ∈ Au) := by
    intro hUne hVne
    rcases bip_star U V hUV hUne hVne with ⟨x, hUx, hVsub⟩ | ⟨y, hVy, hUsub⟩
    · refine ⟨x, V, vj, hVsub, fun p hp => (hV _).2 (Or.inr ⟨p, hp, by simp⟩),
        cOf_false_of_zero C.gates C.output H vj x, ?_⟩
      rintro s t (⟨hs, ht⟩ | ⟨ht, hs⟩)
      · rw [hUx, Finset.mem_singleton] at hs; exact Or.inl ⟨hs, ht⟩
      · rw [hUx, Finset.mem_singleton] at ht; exact Or.inr ⟨ht, hs⟩
    · refine ⟨y, U, uj, hUsub, fun p hp => (hU _).2 (Or.inr ⟨p, hp, by simp⟩),
        cOf_false_of_zero C.gates C.output H uj y, ?_⟩
      rintro s t (⟨hs, ht⟩ | ⟨ht, hs⟩)
      · rw [hVy, Finset.mem_singleton] at ht; exact Or.inr ⟨ht, hs⟩
      · rw [hVy, Finset.mem_singleton] at hs; exact Or.inl ⟨hs, ht⟩
  have hstar_AB : A.Nonempty → B.Nonempty →
      ∃ (za : Fin 26) (Aa : Finset (Fin 26)) (lwa : ℕ), Aa ⊆ N za ∧
        (∀ p ∈ Aa, val C.gates lwa (fun u => decide (u = p)) = true) ∧
        val C.gates lwa (fun u => decide (u ∉ N za)) = false ∧
        ∀ s t : Fin 26, ((s ∈ A ∧ t ∈ B) ∨ (t ∈ A ∧ s ∈ B)) →
          (s = za ∧ t ∈ Aa) ∨ (t = za ∧ s ∈ Aa) := by
    intro hAne hBne
    rcases bip_star A B hAB hAne hBne with ⟨x, hAx, hBsub⟩ | ⟨y, hBy, hAsub⟩
    · refine ⟨x, B, bi, hBsub, fun p hp => (hB _).2 ⟨p, hp, by simp⟩,
        star_false_outside C.gates bi B x hB hBsub, ?_⟩
      rintro s t (⟨hs, ht⟩ | ⟨ht, hs⟩)
      · rw [hAx, Finset.mem_singleton] at hs; exact Or.inl ⟨hs, ht⟩
      · rw [hAx, Finset.mem_singleton] at ht; exact Or.inr ⟨ht, hs⟩
    · refine ⟨y, A, ai, hAsub, fun p hp => (hA _).2 ⟨p, hp, by simp⟩,
        star_false_outside C.gates ai A y hA hAsub, ?_⟩
      rintro s t (⟨hs, ht⟩ | ⟨ht, hs⟩)
      · rw [hBy, Finset.mem_singleton] at ht; exact Or.inr ⟨ht, hs⟩
      · rw [hBy, Finset.mem_singleton] at hs; exact Or.inl ⟨hs, ht⟩
  by_cases hABne : A.Nonempty ∧ B.Nonempty
  · obtain ⟨za, Aa, lwa, hAasub, hAahot, hAahoc, hAacov⟩ := hstar_AB hABne.1 hABne.2
    by_cases hUVne : U.Nonempty ∧ V.Nonempty
    · obtain ⟨zu, Au, lwu, hAusub, hAuhot, hAuhoc, hAucov⟩ := hstar_UV hUVne.1 hUVne.2
      by_cases hiUS : iF ∈ US C.gates C.output
      · refine finish_one_star_thm C.gates C.output H jF zk Ak lwk hoth zu Au lwu (some zu)
          hAusub hAuhot hAuhoc ?_
        intro s t _ hst
        rcases hcov_both s t hst with h1 | h2
        · right
          refine ⟨iF, hiUS, hneij, ?_⟩
          rw [hi0_val]
          rcases h1 with ⟨hs, ht⟩ | ⟨ht, hs⟩
          · exact ⟨⟨s, hs, by simp [pr]⟩, ⟨t, ht, by simp [pr]⟩⟩
          · exact ⟨⟨t, ht, by simp [pr]⟩, ⟨s, hs, by simp [pr]⟩⟩
        · exact Or.inl (hAucov s t h2)
      · obtain ⟨u0, hu0⟩ := hUVne.1
        obtain ⟨m, hm_or, hmsing, hmzero⟩ := mix_gate C iF H.1 H.2.1 H.2.2.1 hi0z uj hIu hnou
          ⟨u0, (hU _).2 (Or.inr ⟨u0, hu0, by simp⟩)⟩
        have hne_im : iF ≠ m := by
          intro e; rw [← e] at hm_or; rw [hi0op] at hm_or; exact GateOp.noConfusion hm_or
        refine finish_two_stars_thm C.gates C.output H jF zk Ak lwk hoth
          zu Au lwu za Aa lwa (some zu) {iF, m}
          hAusub hAuhot hAuhoc hAasub hAahot ?_ ?_ ?_ (by rw [Finset.card_pair hne_im])
        · by_cases heq : (some zu : Option (Fin 26)) = some za
          · simp only [cOf, heq, ite_true]; exact val_zero C.gates H.1 H.2.1 _
          · simp only [cOf, heq, ite_false]; exact hAahoc
        · intro s t _ hst
          rcases hcov_both s t hst with h1 | h2
          · exact Or.inr (Or.inl (hAacov s t h1))
          · exact Or.inl (hAucov s t h2)
        · intro g hg
          rcases Finset.mem_insert.1 hg with hg' | hg'
          · rw [hg']; exact and_gate_disj C.gates C.output (some zu) iF hi0op hiUS
          · rw [Finset.mem_singleton.1 hg']
            exact mix_gate_disj C.gates C.output H (some zu) m hm_or hmsing hmzero
    · refine finish_one_star_thm C.gates C.output H jF zk Ak lwk hoth za Aa lwa none hAasub hAahot
        (by simpa [cOf] using hAahoc) ?_
      intro s t _ hst
      rcases hcov_both s t hst with h1 | h2
      · exact Or.inl (hAacov s t h1)
      · exfalso
        rcases h2 with ⟨hs, ht⟩ | ⟨ht, hs⟩
        · exact hUVne ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
        · exact hUVne ⟨⟨t, ht⟩, ⟨s, hs⟩⟩
  · by_cases hUVne : U.Nonempty ∧ V.Nonempty
    · obtain ⟨zu, Au, lwu, hAusub, hAuhot, hAuhoc, hAucov⟩ := hstar_UV hUVne.1 hUVne.2
      refine finish_one_star_thm C.gates C.output H jF zk Ak lwk hoth zu Au lwu (some zu)
        hAusub hAuhot hAuhoc ?_
      intro s t _ hst
      rcases hcov_both s t hst with h1 | h2
      · exfalso
        rcases h1 with ⟨hs, ht⟩ | ⟨ht, hs⟩
        · exact hABne ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
        · exact hABne ⟨⟨t, ht⟩, ⟨s, hs⟩⟩
      · exact Or.inl (hAucov s t h2)
    · obtain ⟨_, _, s0, t0, h0⟩ := (mem_US C.gates C.output jF).1 hjUS
      rcases hcov_both s0 t0 h0 with h1 | h2
      · rcases h1 with ⟨hs, ht⟩ | ⟨ht, hs⟩
        · exact absurd ⟨⟨s0, hs⟩, ⟨t0, ht⟩⟩ hABne
        · exact absurd ⟨⟨t0, ht⟩, ⟨s0, hs⟩⟩ hABne
      · rcases h2 with ⟨hs, ht⟩ | ⟨ht, hs⟩
        · exact absurd ⟨⟨s0, hs⟩, ⟨t0, ht⟩⟩ hUVne
        · exact absurd ⟨⟨t0, ht⟩, ⟨s0, hs⟩⟩ hUVne

open Classical in
theorem core_one_pair (C : Circuit) (H : Hy0 C.gates C.output)
    (i0 j0 : ℕ) (hi0 : (gateAt C i0).op = GateOp.and) (hj0 : (gateAt C j0).op = GateOp.and)
    (hc0 : InCone 26 C i0 j0)
    (huniq : ∀ i' j', (gateAt C i').op = GateOp.and → (gateAt C j').op = GateOp.and →
      InCone 26 C i' j' → i' = i0 ∧ j' = j0) :
    64 ≤ C.gates.length := by
  have hlt0 := inCone_lt 26 C i0 j0 hc0
  have hj0lt : j0 < C.gates.length := hlt0.1
  have hi0lt : i0 < C.gates.length := by omega
  let iF : Fin C.gates.length := ⟨i0, hi0lt⟩
  let jF : Fin C.gates.length := ⟨j0, hj0lt⟩
  have hneij : iF ≠ jF := by
    intro e
    have hval : i0 = j0 := congrArg Fin.val e
    omega
  have hi0op : (C.gates.get iF).op = GateOp.and := by
    simpa [iF, gateAt_eq C i0 hi0lt] using hi0
  have hj0op : (C.gates.get jF).op = GateOp.and := by
    simpa [jF, gateAt_eq C j0 hj0lt] using hj0
  have hother : ∀ k : Fin C.gates.length, ∃ (z : Fin 26) (A : Finset (Fin 26)) (lw : ℕ),
      (k ∈ US C.gates C.output → k ≠ jF →
        A ⊆ N z ∧ (∀ p ∈ A, val C.gates lw (fun u => decide (u = p)) = true) ∧
        val C.gates lw (fun u => decide (u ∉ N z)) = false ∧
        ∀ s t : Fin 26, val C.gates (26 + (k : ℕ)) (pr s t) = true →
          (s = z ∧ t ∈ A) ∨ (t = z ∧ s ∈ A)) := by
    intro k
    by_cases hk : k ∈ US C.gates C.output ∧ k ≠ jF
    · have hkne : (k : ℕ) ≠ j0 := fun e => hk.2 (Fin.ext e)
      have hlin : ∀ w ∈ (C.gates.get k).inputs, ∃ S : Finset (Fin 26),
          ∀ x : Fin 26 → Bool, val C.gates w x = true ↔ ∃ v ∈ S, x v = true :=
        lin_of_other_and C i0 j0 hi0 H.1 H.2.1 H.2.2.1 huniq k ((mem_US _ _ k).1 hk.1).1 hkne
      obtain ⟨z, A, lw, hh⟩ := star_lin C.gates C.output H k hk.1 hlin
      exact ⟨z, A, lw, fun _ _ => hh⟩
    · exact ⟨0, ∅, 0, fun h1 h2 => absurd ⟨h1, h2⟩ hk⟩
  choose zk Ak lwk hoth using hother
  by_cases hjUS : jF ∈ US C.gates C.output
  swap
  · apply finish_no_j_thm C.gates C.output H jF zk Ak lwk hoth
    intro s t hadj
    obtain ⟨k, hk, hv⟩ := cover C.gates C.output H s t hadj
    exact ⟨k, hk, fun e => hjUS (e ▸ hk), hv⟩
  obtain ⟨ai, bi, habi⟩ := List.length_eq_two.1 (H.2.1 _ (List.getElem_mem hi0lt))
  have hmai : ai ∈ (C.gates.get iF).inputs := by simp [iF, habi]
  have hmbi : bi ∈ (C.gates.get iF).inputs := by simp [iF, habi]
  have hai_lt : ai < 26 + i0 := H.2.2.1 iF ai hmai
  have hbi_lt : bi < 26 + i0 := H.2.2.1 iF bi hmbi
  have hi0nej0 : (iF : ℕ) ≠ j0 := by show i0 ≠ j0; omega
  obtain ⟨A, hA⟩ := lin_of_other_and C i0 j0 hi0 H.1 H.2.1 H.2.2.1 huniq iF hi0op hi0nej0 ai hmai
  obtain ⟨B, hB⟩ := lin_of_other_and C i0 j0 hi0 H.1 H.2.1 H.2.2.1 huniq iF hi0op hi0nej0 bi hmbi
  have hi0_val : ∀ x : Fin 26 → Bool,
      val C.gates (26 + (iF : ℕ)) x = true ↔ (∃ v ∈ A, x v = true) ∧ (∃ v ∈ B, x v = true) := by
    intro x
    change val C.gates (26 + i0) x = true ↔ _
    rw [val_and C.gates x i0 hi0lt hi0op]
    constructor
    · intro hall
      exact ⟨(hA x).1 (hall ai (by simpa [iF] using hmai)).2,
             (hB x).1 (hall bi (by simpa [iF] using hmbi)).2⟩
    · rintro ⟨h1, h2⟩ w hw
      rw [habi] at hw
      rcases List.mem_pair.1 hw with rfl | rfl
      · exact ⟨hai_lt, (hA x).2 h1⟩
      · exact ⟨hbi_lt, (hB x).2 h2⟩
  obtain ⟨uj, vj, habj⟩ := List.length_eq_two.1 (H.2.1 _ (List.getElem_mem hj0lt))
  have hmuj : uj ∈ C.gates[j0].inputs := by rw [habj]; simp
  have hmvj : vj ∈ C.gates[j0].inputs := by rw [habj]; simp
  have huj_lt : uj < 26 + j0 := H.2.2.1 jF uj hmuj
  have hvj_lt : vj < 26 + j0 := H.2.2.1 jF vj hmvj
  have hnou : NoOtherAnd C i0 uj := noOtherAnd_j0_child C i0 j0 hj0lt hj0 H.1 H.2.2.1 huniq uj hmuj
  have hnov : NoOtherAnd C i0 vj := noOtherAnd_j0_child C i0 j0 hj0lt hj0 H.1 H.2.2.1 huniq vj hmvj
  obtain ⟨U, hU⟩ := decomp_wire C i0 H.1 H.2.1 H.2.2.1 uj hnou
  obtain ⟨V, hV⟩ := decomp_wire C i0 H.1 H.2.1 H.2.2.1 vj hnov
  have hj0_val : ∀ x : Fin 26 → Bool,
      val C.gates (26 + (jF : ℕ)) x = true ↔ val C.gates uj x = true ∧ val C.gates vj x = true := by
    intro x
    change val C.gates (26 + j0) x = true ↔ _
    rw [val_and C.gates x j0 hj0lt hj0op]
    constructor
    · intro hall
      exact ⟨(hall uj hmuj).2, (hall vj hmvj).2⟩
    · rintro ⟨h1, h2⟩ w hw
      rw [habj] at hw
      rcases List.mem_pair.1 hw with rfl | rfl
      · exact ⟨huj_lt, h1⟩
      · exact ⟨hvj_lt, h2⟩
  have hIuv : HasI C i0 uj ∨ HasI C i0 vj := by
    have hI0 : HasI C i0 (26 + j0) := Or.inr ⟨by omega, by omega, by simpa using hc0⟩
    exact (hasI_or_iff C i0 j0 uj vj hj0lt (by omega) habj huj_lt hvj_lt).1 hI0
  by_cases hIu : HasI C i0 uj
  · by_cases hIv : HasI C i0 vj
    · exact case_both_sides_thm C H iF jF hi0op hjUS hneij zk Ak lwk hoth
        ai bi uj vj A B U V hA hB hi0_val hIu hIv hnou hj0_val hU hV
    · exact case_one_side_thm C H iF jF hi0op hjUS hneij zk Ak lwk hoth
        ai bi uj vj A B U V hA hB hi0_val hIu hIv hnou hj0_val hU hV
  · have hIv : HasI C i0 vj := by
      rcases hIuv with h | h
      · exact absurd h hIu
      · exact h
    exact case_one_side_thm C H iF jF hi0op hjUS hneij zk Ak lwk hoth
      ai bi vj uj A B V U hA hB hi0_val hIv hIu hnov (fun x => by rw [hj0_val, and_comm]) hV hU

theorem legal_of (C : Circuit) (hmono : Monotone2 C) :
    ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨h1, h2⟩ := hmono g hg
  refine ⟨?_, h2⟩
  rcases h1 with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem hin_of (C : Circuit) (hrb : ReadsBack 26 C) :
    ∀ i : Fin C.gates.length, ∀ a ∈ (C.gates.get i).inputs, a < 26 + (i : ℕ) := by
  intro i a ha
  apply hrb i i.2 a
  unfold gateAt
  rw [List.getD_eq_getElem _ _ i.2]
  exact ha

theorem main_ge64 (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (hacc : ∀ (x3 x4 : Fin 13), x3 - x4 ∈ ({0, 1, 3, 9} : Finset (Fin 13)) →
      C.eval ((List.ofFn fun (x6 : Fin 13) => decide (x6 = x3)) ++
        List.ofFn fun (x6 : Fin 13) => decide (x6 = x4)) = true)
    (hrej : ∀ (x3 : Finset (Fin 13)), x3.card = 4 →
      (∀ (x5 : Fin 13), ({x6 ∈ x3 | x6 - x5 ∈ ({0, 1, 3, 9} : Finset (Fin 13))}).card ≤ 2) →
      C.eval ((List.ofFn fun (x6 : Fin 13) => decide (x6 ∈ x3)) ++
        List.ofFn fun (x6 : Fin 13) => decide (∀ x7 ∈ x3, x7 - x6 ∉ ({0, 1, 3, 9} : Finset (Fin 13)))) = false)
    (hnest : ∃ i j : ℕ, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧
      InCone 26 C i j)
    (hlen2 : ∀ g ∈ C.gates, g.inputs.length = 2)
    (hpairs : PEqualNP.TopForm.andPairs 26 C ≤ 1) :
    64 ≤ C.size := by
  have legal := legal_of C hmono
  have hin := hin_of C hrb
  have H : Hy0 C.gates C.output := by
    refine ⟨legal, hlen2, hin, ?_, ?_⟩
    · intro s t hadj
      obtain ⟨hD, hsub⟩ := accwit s t hadj
      have h : val C.gates C.output (ein (Pp s t) (Ll s t)) = true := by
        have h := hacc _ _ hD
        rw [mk_eq] at h
        exact h
      exact val_mono C.gates legal _ _ (fun u hu => decide_eq_true (hsub u hu)) C.output h
    · intro s t hadj
      obtain ⟨hc, hq, hs, ht⟩ := wit s t hadj
      have h : val C.gates C.output (qin (Wt s t)) = false := by
        have h := hrej _ hc hq
        rw [mk_eq] at h
        exact h
      cases hv : val C.gates C.output (pr s t) with
      | false => rfl
      | true =>
        have h2 := val_mono C.gates legal (pr s t) (qin (Wt s t)) (by
          intro u hu
          have e : u = s ∨ u = t := of_decide_eq_true hu
          rcases e with e | e
          · rw [e]; exact hs
          · rw [e]; exact ht) C.output hv
        rw [h] at h2
        exact Bool.noConfusion h2
  obtain ⟨i0, j0, hi0, hj0, hc0⟩ := hnest
  have huniq := unique_and_pair C hpairs i0 j0 hi0 hj0 hc0
  exact core_one_pair C H i0 j0 hi0 hj0 hc0 huniq

end PEqualNP.Outside.L_meta_1961

theorem PEqualNP.Outside.L_meta_1961 : have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => (∀ (x3 x4 : Fin (13 : ℕ)), x3 - x4 ∈ x1 → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 = x4)) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card = (4 : ℕ) → (∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x3 | x6 - x5 ∈ x1}.card ≤ (2 : ℕ)) → x2.eval ((List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) ++ List.ofFn fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 - x6 ∉ x1)) = Bool.false; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∃ (x4 : ℕ) (x5 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ PEqualNP.EdgeOwnership.InCone (26 : ℕ) x3 x4 x5; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x4 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x4 → x2 x4 → x4.size < (64 : ℕ) → x3 x4 → (∀ x10 ∈ x4.gates, x10.inputs.length = (2 : ℕ) ∧ x10.inputs.getD (0 : ℕ) (0 : ℕ) ≠ x10.inputs.getD (1 : ℕ) (0 : ℕ)) → PEqualNP.TopForm.andPairs (26 : ℕ) x4 ≤ (1 : ℕ) → ∃ (x12 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x12 ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x12 ∧ x2 x12 ∧ x12.size < x4.size := by
  intro x1 x2 x3 C hmono hrb hok hsz hnest hstrict hpairs
  have hge := PEqualNP.Outside.L_meta_1961.main_ge64 C hmono hrb hok.1 hok.2 hnest
    (fun g hg => (hstrict g hg).1) hpairs
  omega
