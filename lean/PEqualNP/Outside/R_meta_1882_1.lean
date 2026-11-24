import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1882_1 :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
       (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
       ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
         (PEqualNP.TopForm.Ustar G C).card ≤
           4 * ((Finset.univ : Finset (Fin n)).image (fun u =>
             ((PEqualNP.TopForm.junk G C).filter (fun h => u ∈ PEqualNP.TopForm.side C h 0),
              (PEqualNP.TopForm.junk G C).filter (fun h => u ∈ PEqualNP.TopForm.side C h 1)))).card * C.size) →
    (∃ k1 : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
       (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
       ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
         4 ≤ (PEqualNP.TopForm.junk G C).card →
         64 < ((Finset.univ : Finset (Fin n)).image (fun u =>
           ((PEqualNP.TopForm.junk G C).filter (fun h => u ∈ PEqualNP.TopForm.side C h 0),
            (PEqualNP.TopForm.junk G C).filter (fun h => u ∈ PEqualNP.TopForm.side C h 1)))).card →
         (∃ i ∈ PEqualNP.TopForm.junk G C, ∃ j ∈ PEqualNP.TopForm.junk G C,
           PEqualNP.EdgeOwnership.InCone n C i j) →
         (∀ i ∈ PEqualNP.TopForm.junk G C, ∀ j ∈ PEqualNP.TopForm.junk G C, ∀ k ∈ PEqualNP.TopForm.junk G C,
           ¬ (PEqualNP.EdgeOwnership.InCone n C i j ∧ PEqualNP.EdgeOwnership.InCone n C j k)) →
         (PEqualNP.TopForm.Ustar G C).card ≤ k1 * (C.size + 1)) →
    (∃ k2 : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
       (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 5 ≤ p.length) → G.edgeFinset.Nonempty →
       ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
         4 ≤ (PEqualNP.TopForm.junk G C).card →
         64 < ((Finset.univ : Finset (Fin n)).image (fun u =>
           ((PEqualNP.TopForm.junk G C).filter (fun h => u ∈ PEqualNP.TopForm.side C h 0),
            (PEqualNP.TopForm.junk G C).filter (fun h => u ∈ PEqualNP.TopForm.side C h 1)))).card →
         (∃ i ∈ PEqualNP.TopForm.junk G C, ∃ j ∈ PEqualNP.TopForm.junk G C, ∃ k ∈ PEqualNP.TopForm.junk G C,
           PEqualNP.EdgeOwnership.InCone n C i j ∧ PEqualNP.EdgeOwnership.InCone n C j k) →
         (PEqualNP.TopForm.Ustar G C).card ≤ k2 * (C.size + 1)) →
    ∃ (x1 : ℕ), ∀ (x2 : ℕ) (x3 : SimpleGraph (Fin x2)) [x4 : DecidableRel x3.Adj], (∀ (x5 : Fin x2) (x6 : x3.Walk x5 x5), x6.IsCycle → (5 : ℕ) ≤ x6.length) → x3.edgeFinset.Nonempty → ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsLeastAO x3 x7 → PEqualNP.TopForm.TopForm x3 x7 → (2 : ℕ) ≤ (PEqualNP.TopForm.junk x3 x7).card → (∃ x11 ∈ PEqualNP.TopForm.junk x3 x7, ∃ x12 ∈ PEqualNP.TopForm.junk x3 x7, PEqualNP.EdgeOwnership.InCone x2 x7 x11 x12) → (PEqualNP.TopForm.Ustar x3 x7).card ≤ x1 * (x7.size + (1 : ℕ)) := by
  intro hsig hc2 hc3
  obtain ⟨k1, h1⟩ := hc2
  obtain ⟨k2, h2⟩ := hc3
  refine ⟨max 256 (max k1 k2), ?_⟩
  intro n G _ hgirth hne C hL hT _ hnest
  let S := (Finset.univ : Finset (Fin n)).image (fun u =>
    ((PEqualNP.TopForm.junk G C).filter (fun h => u ∈ PEqualNP.TopForm.side C h 0),
     (PEqualNP.TopForm.junk G C).filter (fun h => u ∈ PEqualNP.TopForm.side C h 1)))
  by_cases hS : S.card ≤ 64
  · have hb : (PEqualNP.TopForm.Ustar G C).card ≤ 4 * S.card * C.size :=
      hsig n G hgirth hne C hL hT
    have hmul : 4 * S.card * C.size ≤ 256 * (C.size + 1) := by
      calc
        4 * S.card * C.size ≤ 4 * 64 * C.size :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 hS)
        _ = 256 * C.size := by norm_num
        _ ≤ 256 * (C.size + 1) := Nat.mul_le_mul_left 256 (Nat.le_succ _)
    exact (hb.trans hmul).trans (Nat.mul_le_mul_right _ (le_max_left _ _))
  · have hSgt : 64 < S.card := by omega
    have hj4 : 4 ≤ (PEqualNP.TopForm.junk G C).card := by
      have hsub : S ⊆ (PEqualNP.TopForm.junk G C).powerset ×ˢ (PEqualNP.TopForm.junk G C).powerset := by
        intro A hA
        obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hA
        exact Finset.mem_product.mpr
          ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _),
           Finset.mem_powerset.mpr (Finset.filter_subset _ _)⟩
      have hcard : S.card ≤ 2 ^ (PEqualNP.TopForm.junk G C).card * 2 ^ (PEqualNP.TopForm.junk G C).card := by
        calc
          S.card ≤ ((PEqualNP.TopForm.junk G C).powerset ×ˢ (PEqualNP.TopForm.junk G C).powerset).card :=
            Finset.card_le_card hsub
          _ = 2 ^ (PEqualNP.TopForm.junk G C).card * 2 ^ (PEqualNP.TopForm.junk G C).card := by
            rw [Finset.card_product, Finset.card_powerset]
      by_contra hlt
      have hle3 : (PEqualNP.TopForm.junk G C).card ≤ 3 := by omega
      have hpow : 2 ^ (PEqualNP.TopForm.junk G C).card ≤ 8 :=
        (Nat.pow_le_pow_right (by norm_num) hle3).trans (by norm_num)
      have hprod : 2 ^ (PEqualNP.TopForm.junk G C).card * 2 ^ (PEqualNP.TopForm.junk G C).card ≤ 64 := by
        calc
          2 ^ (PEqualNP.TopForm.junk G C).card * 2 ^ (PEqualNP.TopForm.junk G C).card ≤ 8 * 8 :=
            Nat.mul_le_mul hpow hpow
          _ = 64 := by norm_num
      omega
    by_cases h3 : ∃ i ∈ PEqualNP.TopForm.junk G C, ∃ j ∈ PEqualNP.TopForm.junk G C,
        ∃ k ∈ PEqualNP.TopForm.junk G C,
          PEqualNP.EdgeOwnership.InCone n C i j ∧ PEqualNP.EdgeOwnership.InCone n C j k
    · exact (h2 n G hgirth hne C hL hT hj4 hSgt h3).trans
        (Nat.mul_le_mul_right _ ((le_max_right k1 k2).trans (le_max_right 256 _)))
    · refine (h1 n G hgirth hne C hL hT hj4 hSgt hnest ?_).trans
        (Nat.mul_le_mul_right _ ((le_max_left k1 k2).trans (le_max_right 256 _)))
      intro i hi j hj k hk hijk
      exact h3 ⟨i, hi, j, hj, k, hk, hijk⟩
