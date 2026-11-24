import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4823

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

lemma flatMap_inputs_length (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length = 2) :
    (gs.flatMap Gate.inputs).length = 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hg : g.inputs.length = 2 := h g (by simp)
    have hgs : ∀ g' ∈ gs, g'.inputs.length = 2 := fun g' hg' => h g' (by simp [hg'])
    simp [hg, ih hgs]
    omega

end PEqualNP.Outside.L_meta_4823

theorem PEqualNP.Outside.L_meta_4823 :
    ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.IsAO2 x1 x2 →
      (0 : ℕ) < x1 + x2.size →
      (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates).toFinset =
        Finset.range (x1 + x2.size - (1 : ℕ)) →
      x1 + ((List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates).length -
            (List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x2.gates).toFinset.card) =
        x2.size + (1 : ℕ) := by
  intro x1 x2 hAO hpos hfin
  have hlen : (x2.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).length = 2 * x2.size :=
    PEqualNP.Outside.L_meta_4823.flatMap_inputs_length x2.gates hAO.2.2
  have hle : (x2.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).toFinset.card ≤
      (x2.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).length :=
    List.toFinset_card_le _
  have hcard : (x2.gates.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs).toFinset.card = x1 + x2.size - 1 := by
    rw [hfin, Finset.card_range]
  omega
