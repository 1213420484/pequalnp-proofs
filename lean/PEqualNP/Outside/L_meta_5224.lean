import Mathlib.Data.List.OfFn
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5224

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma flatMap_take_le_two (gs : List Gate) :
    (gs.flatMap fun g => g.inputs.take (bif g.op.eval [false] then 1 else 2)).length ≤
      2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have htake : (g.inputs.take (bif g.op.eval [false] then 1 else 2)).length ≤ 2 := by
      have h1 := List.length_take_le (bif g.op.eval [false] then 1 else 2) g.inputs
      cases g.op.eval [false] <;> simp at h1 ⊢
    omega

end PEqualNP.Outside.L_meta_5224

theorem PEqualNP.Outside.L_meta_5224 :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) =>
      x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) ||
      x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) ||
      x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) ||
      x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) ||
      x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) ||
      x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) ||
      x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) ||
      x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) ||
      x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) ||
      x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) ||
      x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) ||
      x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ));
    ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x2 →
        (∀ (x4 : Fin (9 : ℕ) → Bool),
          x2.eval (List.ofFn x4 ++ [x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ))]) = x1 x4) →
        (have x5 : List ℕ := List.flatMap (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) =>
            List.take (bif x5.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x5.inputs) x2.gates;
          (∀ x6 < (10 : ℕ) + x2.size, x6 ≠ x2.output → x6 ∈ x5) ∧
          (List.filter (fun (x6 : PEqualNP.CircuitLowerBounds.Gate) => x6.op.eval [Bool.false]) x2.gates).length +
            (x5.length - x5.toFinset.card) ≤ (5 : ℕ)) →
        (∀ (x6 : Fin (9 : ℕ)) (x7 : Fin (10 : ℕ)),
          x6 ≠ (0 : Fin (9 : ℕ)) → x6 ≠ (2 : Fin (9 : ℕ)) → x6.castSucc ≠ x7 →
          ∀ x11 ∈ x2.gates,
            x11.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
            x11.op = PEqualNP.CircuitLowerBounds.GateOp.or →
            x11.inputs = [↑x6, ↑x7] ∨ x11.inputs = [↑x7, ↑x6] →
            (2 : ℕ) ≤ (List.filter (fun (x15 : PEqualNP.CircuitLowerBounds.Gate) =>
              (List.take (bif x15.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x15.inputs).contains ↑x6)
              x2.gates).length) →
        (¬∃ (x7 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[(1 : ℕ)]? = Option.some x7) →
        (15 : ℕ) ≤ x2.size := by
  intro x1 x2 _ _ huse _ hno1
  exfalso
  have hlen : x2.gates.length ≤ 1 := by
    by_contra h
    push Not at h
    exact hno1 ⟨x2.gates[1], List.getElem?_eq_getElem h⟩
  let x5 : List ℕ := List.flatMap (fun g =>
    List.take (bif g.op.eval [Bool.false] then 1 else 2) g.inputs) x2.gates
  have hx5len : x5.length ≤ 2 := by
    have := PEqualNP.Outside.L_meta_5224.flatMap_take_le_two x2.gates
    dsimp only [x5]
    omega
  have hsub : (Finset.range 10).erase x2.output ⊆ x5.toFinset := by
    intro w hw
    rw [Finset.mem_erase, Finset.mem_range] at hw
    rw [List.mem_toFinset]
    exact huse.1 w (by omega) hw.1
  have hc1 : ((Finset.range 10).erase x2.output).card ≤ x5.toFinset.card :=
    Finset.card_le_card hsub
  have hc2 : x5.toFinset.card ≤ x5.length := List.toFinset_card_le x5
  have hc3 : 9 ≤ ((Finset.range 10).erase x2.output).card := by
    have hpred := Finset.pred_card_le_card_erase (s := Finset.range 10) (a := x2.output)
    simp at hpred
    omega
  omega
