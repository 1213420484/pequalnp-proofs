import Mathlib.Data.List.OfFn
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4069

open PEqualNP.CircuitLowerBounds

private def stepGate (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem eval_mono_of_mem (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (ins : List ℕ) (w1 w2 : List Bool)
    (hle : ∀ i, w1.getD i false = true → w2.getD i false = true) :
    op.eval (ins.map fun i => w1.getD i false) = true →
    op.eval (ins.map fun i => w2.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂]
    intro h i hi
    exact hle i (h i hi)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and]
    rintro ⟨i, hi, hv⟩
    exact ⟨i, hi, hle i hv⟩

private theorem foldl_mono (gs : List Gate)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ (w1 w2 : List Bool), w1.length = w2.length →
      (∀ i, w1.getD i false = true → w2.getD i false = true) →
      ∀ i, (gs.foldl stepGate w1).getD i false = true →
           (gs.foldl stepGate w2).getD i false = true := by
  induction gs with
  | nil =>
    intro w1 w2 _ hle i hi
    exact hle i hi
  | cons g gs ih =>
    intro w1 w2 hlen hle i hi
    apply ih (fun g' hg' => hmono g' (List.mem_cons_of_mem g hg'))
      (stepGate w1 g) (stepGate w2 g)
    · simp [stepGate, hlen]
    · intro j hj
      simp only [stepGate] at hj ⊢
      by_cases hlt : j < w1.length
      · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hlt] at hj
        rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left (by omega)]
        have hj' : w1.getD j false = true := by rwa [List.getD_eq_getElem _ _ hlt]
        have h2 := hle j hj'
        rwa [List.getD_eq_getElem _ _ (by omega)] at h2
      · by_cases heq : j = w1.length
        · subst heq
          rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (Nat.le_refl _)] at hj
          simp only [Nat.sub_self, List.getElem_singleton] at hj
          rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right (by omega)]
          have hsub : w1.length - w2.length = 0 := by omega
          simp only [hsub, List.getElem_singleton]
          exact eval_mono_of_mem g.op (hmono g List.mem_cons_self) g.inputs w1 w2 hle hj
        · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
          exact Bool.noConfusion hj
    · exact hi

private theorem main_proof (n : ℕ) (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : Fin n → Bool) (hle : ∀ i : Fin n, x i = true → y i = true)
    (hx : PEqualNP.MetaComplexity.circuitFun n C x = true) :
    PEqualNP.MetaComplexity.circuitFun n C y = true := by
  unfold PEqualNP.MetaComplexity.circuitFun Circuit.eval Circuit.wires at hx ⊢
  apply foldl_mono C.gates (fun g hg => by
    have h := (hm g hg).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h)
    (List.ofFn x) (List.ofFn y) (by simp) _ C.output hx
  intro i hi
  by_cases hlt : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_ofFn] at hi
    rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_ofFn]
    exact hle ⟨i, hlt⟩ hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    exact Bool.noConfusion hi

end PEqualNP.Outside.L_meta_4069

theorem PEqualNP.Outside.L_meta_4069 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → ∀ (x4 x5 : Fin x1 → Bool), (∀ (x6 : Fin x1), x4 x6 = Bool.true → x5 x6 = Bool.true) → PEqualNP.MetaComplexity.circuitFun x1 x2 x4 = Bool.true → PEqualNP.MetaComplexity.circuitFun x1 x2 x5 = Bool.true :=
  PEqualNP.Outside.L_meta_4069.main_proof
