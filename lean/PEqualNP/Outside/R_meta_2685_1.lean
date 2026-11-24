import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

theorem PEqualNP.Outside.R_meta_2685_1
    (hTopForm : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      G.edgeFinset.Nonempty → PEqualNP.TopForm.IsLeastAO G C →
      ∃ C' : Circuit, PEqualNP.TopForm.IsLeastAO G C' ∧ C'.size = C.size ∧
        PEqualNP.TopForm.TopForm G C')
    (hNoJunk : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty →
      PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      PEqualNP.TopForm.junk G C = ∅ →
      ∀ K : Finset (Fin n), IsMinCover G K → G.edgeFinset.card + K.card ≤ C.size + 1)
    (hOneJunk : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∃ S : Finset (Fin n), ∀ u v : Fin n, G.Adj u v → (u ∈ S ↔ v ∉ S)) →
      PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty →
      PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      (PEqualNP.TopForm.junk G C).card = 1 →
      ∀ K : Finset (Fin n), IsMinCover G K → G.edgeFinset.card + K.card ≤ C.size + 1)
    (hManyJunk : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∃ S : Finset (Fin n), ∀ u v : Fin n, G.Adj u v → (u ∈ S ↔ v ∉ S)) →
      PEqualNP.TopForm.NoFourCycle G → G.edgeFinset.Nonempty →
      PEqualNP.TopForm.IsLeastAO G C → PEqualNP.TopForm.TopForm G C →
      2 ≤ (PEqualNP.TopForm.junk G C).card →
      ∀ K : Finset (Fin n), IsMinCover G K → G.edgeFinset.card + K.card ≤ C.size + 1) :
    ∀ (Np Nl : ℕ) (I : Fin Np → Fin Nl → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' : Fin Np, ∀ l l' : Fin Nl, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.TopForm.IsAO2 (Np + Nl) C → (∀ z : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) C z = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true)) → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (P L : Finset ℕ), PEqualNP.TopForm.IsAO2 (Np + Nl) D ∧ (∀ y : Fin (Np + Nl) → Bool, PEqualNP.MetaComplexity.circuitFun (Np + Nl) D y = decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ y (Fin.castAdd Nl p) = true ∧ y (Fin.natAdd Np l) = true)) ∧ D.size ≤ C.size ∧ (∀ w ∈ P, w < Np ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ P) ∧ (∀ w ∈ L, (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < D.gates.length, w = Np + Nl + i ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ u ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs, u ∈ L) ∧ ∀ i < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ a b : ℕ, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).inputs = [a, b] ∧ ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P)) := by
  classical
  intro Np Nl I instI C hC4 hAO2 hFun
  have hCastNeNat : ∀ (p : Fin Np) (l : Fin Nl), Fin.castAdd Nl p ≠ Fin.natAdd Np l := by
    intro p l h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  have hCastInj : ∀ {p1 p2 : Fin Np}, Fin.castAdd Nl p1 = Fin.castAdd Nl p2 → p1 = p2 := by
    intro p1 p2 h
    apply Fin.ext
    have hv := congrArg Fin.val h
    simpa only [Fin.val_castAdd] using hv
  have hNatInj : ∀ {l1 l2 : Fin Nl}, Fin.natAdd Np l1 = Fin.natAdd Np l2 → l1 = l2 := by
    intro l1 l2 h
    apply Fin.ext
    have hv := congrArg Fin.val h
    simp only [Fin.val_natAdd] at hv
    omega
  let adj : Fin (Np + Nl) → Fin (Np + Nl) → Prop := fun u v =>
    ∃ (p : Fin Np) (l : Fin Nl), I p l ∧
      ((u = Fin.castAdd Nl p ∧ v = Fin.natAdd Np l) ∨
       (u = Fin.natAdd Np l ∧ v = Fin.castAdd Nl p))
  let G : SimpleGraph (Fin (Np + Nl)) := {
    Adj := adj
    symm := ⟨by
      rintro _ _ ⟨p, l, hI, h⟩
      refine ⟨p, l, hI, ?_⟩
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr ⟨h2, h1⟩
      · exact Or.inl ⟨h2, h1⟩⟩
    loopless := ⟨by
      rintro _ ⟨p, l, _, h⟩
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hCastNeNat p l (h1.symm.trans h2)
      · exact hCastNeNat p l (h2.symm.trans h1)⟩
  }
  have hBip : ∃ S : Finset (Fin (Np + Nl)), ∀ u v : Fin (Np + Nl), G.Adj u v → (u ∈ S ↔ v ∉ S) := by
    refine ⟨Finset.univ.filter (fun u : Fin (Np + Nl) => u.val < Np), ?_⟩
    rintro u v ⟨p, l, _, h⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [Fin.val_castAdd, Fin.val_natAdd]
      exact ⟨fun _ => by omega, fun _ => p.isLt⟩
    · simp only [Fin.val_castAdd, Fin.val_natAdd]
      exact ⟨fun h1 => by omega, fun h1 => by exfalso; exact h1 p.isLt⟩
  have hNo4 : PEqualNP.TopForm.NoFourCycle G := by
    intro a b hab
    rw [Finset.card_le_one]
    intro w1 hw1 w2 hw2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw1 hw2
    obtain ⟨p1, l1, hI1, h1⟩ := hw1.1
    obtain ⟨p2, l2, hI2, h2⟩ := hw1.2
    obtain ⟨p3, l3, hI3, h3⟩ := hw2.1
    obtain ⟨p4, l4, hI4, h4⟩ := hw2.2
    rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases h2 with ⟨rfl, h2w⟩ | ⟨_, h2w⟩
      · have hl : l2 = l1 := hNatInj h2w.symm
        rcases h3 with ⟨h3a, rfl⟩ | ⟨h3a, _⟩
        · have hp : p3 = p1 := hCastInj h3a.symm
          rcases h4 with ⟨h4a, h4w⟩ | ⟨h4a, _⟩
          · have hp2 : p4 = p2 := hCastInj h4a.symm
            have hl3 : l4 = l3 := hNatInj h4w.symm
            have hpp : p1 ≠ p2 := fun he => hab (congrArg (Fin.castAdd Nl) he)
            by_contra hne
            have hll : l1 ≠ l3 := fun he => hne (congrArg (Fin.natAdd Np) he)
            exact hC4 p1 p2 l1 l3 hpp hll ⟨hI1, hp ▸ hI3, hl ▸ hI2, hp2 ▸ hl3 ▸ hI4⟩
          · exact False.elim (hCastNeNat p2 l4 h4a)
        · exact False.elim (hCastNeNat p1 l3 h3a)
      · exact False.elim (hCastNeNat p2 l1 h2w.symm)
    · rcases h2 with ⟨_, h2w⟩ | ⟨rfl, h2w⟩
      · exact False.elim (hCastNeNat p1 l2 h2w)
      · have hp : p2 = p1 := hCastInj h2w.symm
        rcases h3 with ⟨h3a, _⟩ | ⟨h3a, rfl⟩
        · exact False.elim (hCastNeNat p3 l1 h3a.symm)
        · have hl : l3 = l1 := hNatInj h3a.symm
          rcases h4 with ⟨h4a, _⟩ | ⟨h4a, h4w⟩
          · exact False.elim (hCastNeNat p4 l2 h4a.symm)
          · have hl2 : l4 = l2 := hNatInj h4a.symm
            have hp3 : p4 = p3 := hCastInj h4w.symm
            have hll : l1 ≠ l2 := fun he => hab (congrArg (Fin.natAdd Np) he)
            by_contra hne
            have hpp : p1 ≠ p3 := fun he => hne (congrArg (Fin.castAdd Nl) he)
            exact hC4 p1 p3 l1 l2 hpp hll ⟨hI1, hp ▸ hI2, hl ▸ hI3, hp3 ▸ hl2 ▸ hI4⟩
  have hFunEq : ∀ z : Fin (Np + Nl) → Bool,
      decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ z (Fin.castAdd Nl p) = true ∧ z (Fin.natAdd Np l) = true) =
      graphFun G ∅ z := by
    intro z
    unfold graphFun
    have hempty : decide (∃ a ∈ (∅ : Finset (Fin (Np + Nl))), z a = true) = false := by simp
    rw [hempty, Bool.false_or]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · rintro ⟨p, l, hI, hp, hl⟩
      exact ⟨Fin.castAdd Nl p, Fin.natAdd Np l, ⟨p, l, hI, Or.inl ⟨rfl, rfl⟩⟩, hp, hl⟩
    · rintro ⟨u, v, ⟨p, l, hI, h⟩, hu, hv⟩
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨p, l, hI, hu, hv⟩
      · exact ⟨p, l, hI, hv, hu⟩
  have hEqFun : circuitFun (Np + Nl) C = graphFun G ∅ := by
    funext z
    exact (hFun z).trans (hFunEq z)
  by_cases hNE : G.edgeFinset.Nonempty
  swap
  · have hNoI : ∀ p : Fin Np, ∀ l : Fin Nl, ¬ I p l := by
      intro p l hI
      apply hNE
      refine ⟨s(Fin.castAdd Nl p, Fin.natAdd Np l), ?_⟩
      rw [SimpleGraph.mem_edgeFinset]
      exact ⟨p, l, hI, Or.inl ⟨rfl, rfl⟩⟩
    refine ⟨⟨[], Np + Nl⟩, ∅, ∅, ?_, ?_, Nat.zero_le _, ?_, ?_, ?_⟩
    · refine ⟨(fun g hg => by cases hg), (fun j hj => by cases hj), (fun g hg => by cases hg)⟩
    · intro y
      have hL : circuitFun (Np + Nl) ⟨[], Np + Nl⟩ y = false := by
        show (List.ofFn y).getD (Np + Nl) false = false
        rw [List.getD_eq_default _ _ (by simp)]
      have hR : decide (∃ p : Fin Np, ∃ l : Fin Nl, I p l ∧ y (Fin.castAdd Nl p) = true ∧ y (Fin.natAdd Np l) = true) = false := by
        simp only [decide_eq_false_iff_not]
        rintro ⟨p, l, hI, _, _⟩
        exact hNoI p l hI
      exact hL.trans hR.symm
    · intro w hw; cases hw
    · intro w hw; cases hw
    · intro i hi; cases hi
  let exSize : ℕ → Prop := fun s =>
    ∃ C0 : Circuit, PEqualNP.TopForm.IsAO2 (Np + Nl) C0 ∧
      circuitFun (Np + Nl) C0 = graphFun G ∅ ∧ C0.size = s
  have hExSize : ∃ s, exSize s := ⟨C.size, C, hAO2, hEqFun, rfl⟩
  obtain ⟨C0, hC0AO, hC0Fun, hC0Sz⟩ := Nat.find_spec hExSize
  have hC0Le : C0.size ≤ C.size := hC0Sz ▸ Nat.find_min' hExSize ⟨C, hAO2, hEqFun, rfl⟩
  have hLeast0 : PEqualNP.TopForm.IsLeastAO G C0 :=
    ⟨hC0AO, hC0Fun, fun C' h1 h2 => hC0Sz ▸ Nat.find_min' hExSize ⟨C', h1, h2, rfl⟩⟩
  obtain ⟨C1, hLeast1, hSz1, hTF1⟩ := hTopForm (Np + Nl) G C0 hNE hLeast0
  let exCov : ℕ → Prop := fun k =>
    ∃ T : Finset (Fin (Np + Nl)), (∀ u v : Fin (Np + Nl), G.Adj u v → u ∈ T ∨ v ∈ T) ∧ T.card = k
  have hExCov : ∃ k, exCov k :=
    ⟨(Finset.univ : Finset (Fin (Np + Nl))).card, Finset.univ, fun u _ _ => Or.inl (Finset.mem_univ u), rfl⟩
  obtain ⟨K, hKcov, hKcard⟩ := Nat.find_spec hExCov
  have hMinK : IsMinCover G K :=
    ⟨hKcov, fun T hT => hKcard ▸ Nat.find_min' hExCov ⟨T, hT, rfl⟩⟩
  have hBound1 : G.edgeFinset.card + K.card ≤ C1.size + 1 := by
    by_cases h0 : (PEqualNP.TopForm.junk G C1).card = 0
    · exact hNoJunk (Np + Nl) G C1 hNo4 hNE hLeast1 hTF1 (Finset.card_eq_zero.mp h0) K hMinK
    · by_cases h1 : (PEqualNP.TopForm.junk G C1).card = 1
      · exact hOneJunk (Np + Nl) G C1 hBip hNo4 hNE hLeast1 hTF1 h1 K hMinK
      · exact hManyJunk (Np + Nl) G C1 hBip hNo4 hNE hLeast1 hTF1 (by omega) K hMinK
  have hBound : G.edgeFinset.card + K.card ≤ C.size + 1 := by omega
  let Kp : Finset (Fin Np) := Finset.univ.filter (fun p : Fin Np => Fin.castAdd Nl p ∈ K)
  let Kl : Finset (Fin Nl) := Finset.univ.filter (fun l : Fin Nl => Fin.natAdd Np l ∈ K)
  have hKsplit : Kp.card + Kl.card = K.card := by
    have hKeq : K = Kp.image (Fin.castAdd Nl) ∪ Kl.image (Fin.natAdd Np) := by
      ext u
      simp only [Finset.mem_union, Finset.mem_image, Kp, Kl, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hu
        by_cases hlt : u.val < Np
        · left
          refine ⟨⟨u.val, hlt⟩, ?_, Fin.ext rfl⟩
          have he : Fin.castAdd Nl ⟨u.val, hlt⟩ = u := Fin.ext rfl
          rwa [he]
        · right
          have he : Fin.natAdd Np ⟨u.val - Np, by omega⟩ = u := Fin.ext (by simp; omega)
          refine ⟨⟨u.val - Np, by omega⟩, ?_, he⟩
          rwa [he]
      · rintro (⟨p, hp, rfl⟩ | ⟨l, hl, rfl⟩)
        · exact hp
        · exact hl
    have hdisj : Disjoint (Kp.image (Fin.castAdd Nl)) (Kl.image (Fin.natAdd Np)) := by
      rw [Finset.disjoint_left]
      intro u hu1 hu2
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hu1
      obtain ⟨l, _, h2⟩ := Finset.mem_image.mp hu2
      exact hCastNeNat p l h2.symm
    rw [hKeq, Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ (fun _ _ h => hCastInj h),
      Finset.card_image_of_injective _ (fun _ _ h => hNatInj h)]
  let Lp : Fin Np → Finset (Fin Nl) := fun p => Finset.univ.filter (fun l : Fin Nl => I p l)
  let Pl : Fin Nl → Finset (Fin Np) := fun l => Finset.univ.filter (fun p : Fin Np => I p l ∧ p ∉ Kp)
  let Eall : Finset (Fin Np × Fin Nl) := Finset.univ.filter (fun e : Fin Np × Fin Nl => I e.1 e.2)
  have hEcard : G.edgeFinset.card = Eall.card := by
    have heq : G.edgeFinset = Eall.image (fun e : Fin Np × Fin Nl => s(Fin.castAdd Nl e.1, Fin.natAdd Np e.2)) := by
      ext e
      induction e using Sym2.ind with
      | _ u v =>
        simp only [SimpleGraph.mem_edgeFinset, Finset.mem_image, Eall, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨p, l, hI, h⟩
          refine ⟨(p, l), hI, ?_⟩
          rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rfl
          · exact Sym2.eq_swap
        · rintro ⟨⟨p, l⟩, hI, h⟩
          rw [Sym2.eq_iff] at h
          rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨p, l, hI, Or.inl ⟨rfl, rfl⟩⟩
          · exact ⟨p, l, hI, Or.inr ⟨rfl, rfl⟩⟩
    rw [heq]
    apply Finset.card_image_of_injective
    rintro ⟨p1, l1⟩ ⟨p2, l2⟩ h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, _⟩
    · exact Prod.ext (hCastInj h1) (hNatInj h2)
    · exact False.elim (hCastNeNat p1 l2 h1)
  have hSumEdges : (∑ p ∈ Kp, (Lp p).card) + (∑ l ∈ Kl, (Pl l).card) = G.edgeFinset.card := by
    rw [hEcard]
    let E1 := Eall.filter (fun e : Fin Np × Fin Nl => e.1 ∈ Kp)
    let E2 := Eall.filter (fun e : Fin Np × Fin Nl => e.1 ∉ Kp)
    have hE1 : ∑ p ∈ Kp, (Lp p).card = E1.card := by
      have himg : ∑ p ∈ Kp, (Lp p).card = ∑ p ∈ Kp, ((Lp p).image (fun l => (p, l))).card := by
        apply Finset.sum_congr rfl
        intro p _
        exact (Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)).symm
      rw [himg, ← Finset.card_biUnion]
      · congr 1
        ext ⟨p, l⟩
        simp only [Finset.mem_biUnion, Finset.mem_image, Lp, E1, Eall, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨p', hp', l', hI, hpair⟩
          rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
          exact ⟨hI, hp'⟩
        · rintro ⟨hI, hp⟩
          exact ⟨p, hp, l, hI, rfl⟩
      · intro p1 _ p2 _ hne
        change Disjoint ((Lp p1).image (fun l => (p1, l))) ((Lp p2).image (fun l => (p2, l)))
        rw [Finset.disjoint_left]
        intro e he1 he2
        obtain ⟨l1, _, rfl⟩ := Finset.mem_image.mp he1
        obtain ⟨l2, _, h2⟩ := Finset.mem_image.mp he2
        exact hne (Prod.mk.inj h2).1.symm
    have hE2 : ∑ l ∈ Kl, (Pl l).card = E2.card := by
      have himg : ∑ l ∈ Kl, (Pl l).card = ∑ l ∈ Kl, ((Pl l).image (fun p => (p, l))).card := by
        apply Finset.sum_congr rfl
        intro l _
        exact (Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)).symm
      rw [himg, ← Finset.card_biUnion]
      · congr 1
        ext ⟨p, l⟩
        simp only [Finset.mem_biUnion, Finset.mem_image, Pl, E2, Eall, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨l', _, p', ⟨hI, hp⟩, hpair⟩
          rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
          exact ⟨hI, hp⟩
        · rintro ⟨hI, hp⟩
          have hlK : l ∈ Kl := by
            simp only [Kl, Finset.mem_filter, Finset.mem_univ, true_and]
            rcases hKcov (Fin.castAdd Nl p) (Fin.natAdd Np l) ⟨p, l, hI, Or.inl ⟨rfl, rfl⟩⟩ with h1 | h2
            · exfalso
              exact hp (Finset.mem_filter.mpr ⟨Finset.mem_univ p, h1⟩)
            · exact h2
          exact ⟨l, hlK, p, ⟨hI, hp⟩, rfl⟩
      · intro l1 _ l2 _ hne
        change Disjoint ((Pl l1).image (fun p => (p, l1))) ((Pl l2).image (fun p => (p, l2)))
        rw [Finset.disjoint_left]
        intro e he1 he2
        obtain ⟨p1, _, rfl⟩ := Finset.mem_image.mp he1
        obtain ⟨p2, _, h2⟩ := Finset.mem_image.mp he2
        exact hne (Prod.mk.inj h2).2.symm
    have hE12 : E1.card + E2.card = Eall.card := by
      have hu : E1 ∪ E2 = Eall := by
        ext e
        simp only [Finset.mem_union, E1, E2, Finset.mem_filter]
        by_cases h : e.1 ∈ Kp <;> simp [h]
      have hd : Disjoint E1 E2 := by
        rw [Finset.disjoint_left]
        intro e he1 he2
        exact (Finset.mem_filter.mp he2).2 (Finset.mem_filter.mp he1).2
      rw [← Finset.card_union_of_disjoint hd, hu]
    rw [hE1, hE2, hE12]
  let Kp' := Kp.filter (fun p => (Lp p).Nonempty)
  let Kl' := Kl.filter (fun l => (Pl l).Nonempty)
  have hSumEdges' : (∑ p ∈ Kp', (Lp p).card) + (∑ l ∈ Kl', (Pl l).card) = G.edgeFinset.card := by
    have h1 : ∑ p ∈ Kp', (Lp p).card = ∑ p ∈ Kp, (Lp p).card := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro p hp hnot
      simp only [Finset.mem_filter, hp, true_and, Finset.not_nonempty_iff_eq_empty] at hnot
      simp [hnot]
    have h2 : ∑ l ∈ Kl', (Pl l).card = ∑ l ∈ Kl, (Pl l).card := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro l hl hnot
      simp only [Finset.mem_filter, hl, true_and, Finset.not_nonempty_iff_eq_empty] at hnot
      simp [hnot]
    rw [h1, h2, hSumEdges]
  have hStarsPos : 1 ≤ Kp'.card + Kl'.card := by
    have hEpos : 0 < G.edgeFinset.card := Finset.card_pos.mpr hNE
    by_contra hle
    have hz1 : Kp' = ∅ := Finset.card_eq_zero.mp (by omega)
    have hz2 : Kl' = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [hz1, hz2] at hSumEdges'
    simp at hSumEdges'
    omega
  have hStarsLe : Kp'.card + Kl'.card ≤ K.card := by
    have h1 : Kp'.card ≤ Kp.card := Finset.card_le_card (Finset.filter_subset _ _)
    have h2 : Kl'.card ≤ Kl.card := Finset.card_le_card (Finset.filter_subset _ _)
    omega
  let stepW : List Bool → Gate → List Bool := fun w g =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have hFoldLen : ∀ (gs : List Gate) (w : List Bool), (gs.foldl stepW w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih]
      simp only [stepW, List.length_append, List.length_cons, List.length_nil]
      omega
  have hFoldKeep : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl stepW w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g gs ih =>
      intro w i hi
      rw [List.foldl_cons, ih _ i (by simp only [stepW, List.length_append, List.length_cons, List.length_nil]; omega)]
      exact List.getD_append _ _ _ _ hi
  have hFoldAppend : ∀ (gs1 gs2 : List Gate) (w : List Bool),
      (gs1 ++ gs2).foldl stepW w = gs2.foldl stepW (gs1.foldl stepW w) := by
    intro gs1 gs2 w
    exact List.foldl_append
  have hWiresStep : ∀ (gs : List Gate) (g : Gate) (y : Fin (Np + Nl) → Bool),
      ((gs ++ [g]).foldl stepW (List.ofFn y)).getD (Np + Nl + gs.length) false =
        g.op.eval (g.inputs.map fun i => (gs.foldl stepW (List.ofFn y)).getD i false) := by
    intro gs g y
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hl : (gs.foldl stepW (List.ofFn y)).length = Np + Nl + gs.length := by
      rw [hFoldLen, List.length_ofFn]
    change (gs.foldl stepW (List.ofFn y) ++ [g.op.eval (g.inputs.map fun i => (gs.foldl stepW (List.ofFn y)).getD i false)]).getD (Np + Nl + gs.length) false = _
    rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self]
    rfl
  have hInputValPt : ∀ (gs : List Gate) (y : Fin (Np + Nl) → Bool) (p : Fin Np),
      (gs.foldl stepW (List.ofFn y)).getD p.val false = y (Fin.castAdd Nl p) := by
    intro gs y p
    have hlt : p.val < (List.ofFn y).length := by simp only [List.length_ofFn]; omega
    rw [hFoldKeep gs (List.ofFn y) p.val hlt, List.getD_eq_getElem _ _ hlt]
    simp only [List.getElem_ofFn]
    rfl
  have hInputValLn : ∀ (gs : List Gate) (y : Fin (Np + Nl) → Bool) (l : Fin Nl),
      (gs.foldl stepW (List.ofFn y)).getD (Np + l.val) false = y (Fin.natAdd Np l) := by
    intro gs y l
    have hlt : Np + l.val < (List.ofFn y).length := by simp only [List.length_ofFn]; omega
    rw [hFoldKeep gs (List.ofFn y) (Np + l.val) hlt, List.getD_eq_getElem _ _ hlt]
    simp only [List.getElem_ofFn]
    rfl
  let GoodState : List Gate → Finset ℕ → Finset ℕ → Prop := fun gs P L =>
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2) ∧
    (∀ j < gs.length, ∀ u ∈ (gs.getD j (Gate.mk GateOp.or [])).inputs, u < Np + Nl + j) ∧
    (∀ w ∈ P, w < Np + Nl + gs.length) ∧
    (∀ w ∈ L, w < Np + Nl + gs.length) ∧
    (∀ w ∈ P, w < Np ∨ ∃ i < gs.length, w = Np + Nl + i ∧
      (gs.getD i (Gate.mk GateOp.or [])).op = GateOp.or ∧
      ∀ u ∈ (gs.getD i (Gate.mk GateOp.or [])).inputs, u ∈ P) ∧
    (∀ w ∈ L, (Np ≤ w ∧ w < Np + Nl) ∨ ∃ i < gs.length, w = Np + Nl + i ∧
      (gs.getD i (Gate.mk GateOp.or [])).op = GateOp.or ∧
      ∀ u ∈ (gs.getD i (Gate.mk GateOp.or [])).inputs, u ∈ L) ∧
    (∀ i < gs.length, (gs.getD i (Gate.mk GateOp.or [])).op = GateOp.and →
      ∃ a b : ℕ, (gs.getD i (Gate.mk GateOp.or [])).inputs = [a, b] ∧
        ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P)))
  have hAppendOr : ∀ (gs : List Gate) (P L : Finset ℕ) (a b : ℕ),
      GoodState gs P L → a < Np + Nl + gs.length → b < Np + Nl + gs.length →
      GoodState (gs ++ [Gate.mk GateOp.or [a, b]]) P L := by
    rintro gs P L a b ⟨h1, h2, h3, h4, h5, h6, h7⟩ ha hb
    have hget : ∀ i < gs.length, (gs ++ [Gate.mk GateOp.or [a, b]]).getD i (Gate.mk GateOp.or []) = gs.getD i (Gate.mk GateOp.or []) :=
      fun i hi => List.getD_append _ _ _ _ hi
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact h1 g hg
      · rw [List.mem_singleton.mp hg]; exact ⟨Or.inr rfl, rfl⟩
    · intro j hj u hu
      simp only [List.length_append, List.length_singleton] at hj
      by_cases hlt : j < gs.length
      · rw [hget j hlt] at hu; exact h2 j hlt u hu
      · have hjEq : j = gs.length := by omega
        subst hjEq
        rw [List.getD_append_right _ _ _ _ le_rfl] at hu
        simp only [Nat.sub_self, List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl <;> omega
    · intro w hw; have := h3 w hw; simp; omega
    · intro w hw; have := h4 w hw; simp; omega
    · intro w hw
      rcases h5 w hw with hlt | ⟨i, hi, heq, hop, hin⟩
      · exact Or.inl hlt
      · right; refine ⟨i, by simp; omega, heq, ?_, ?_⟩
        · rw [hget i hi]; exact hop
        · rw [hget i hi]; exact hin
    · intro w hw
      rcases h6 w hw with hlt | ⟨i, hi, heq, hop, hin⟩
      · exact Or.inl hlt
      · right; refine ⟨i, by simp; omega, heq, ?_, ?_⟩
        · rw [hget i hi]; exact hop
        · rw [hget i hi]; exact hin
    · intro i hi hop
      simp only [List.length_append, List.length_singleton] at hi
      by_cases hlt : i < gs.length
      · rw [hget i hlt] at hop ⊢; exact h7 i hlt hop
      · have hiEq : i = gs.length := by omega
        subst hiEq
        rw [List.getD_append_right _ _ _ _ le_rfl] at hop
        simp at hop
  have hAppendOrP : ∀ (gs : List Gate) (P L : Finset ℕ) (a b : ℕ),
      GoodState gs P L → a ∈ P → b ∈ P →
      GoodState (gs ++ [Gate.mk GateOp.or [a, b]]) (insert (Np + Nl + gs.length) P) L := by
    intro gs P L a b hG ha hb
    have hha : a < Np + Nl + gs.length := hG.2.2.1 a ha
    have hhb : b < Np + Nl + gs.length := hG.2.2.1 b hb
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hAppendOr gs P L a b hG hha hhb
    refine ⟨h1, h2, ?_, h4, ?_, h6, ?_⟩
    · intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · simp
      · exact h3 w hw
    · intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · right
        refine ⟨gs.length, by simp, rfl, ?_, ?_⟩
        · rw [List.getD_append_right _ _ _ _ le_rfl]; simp
        · rw [List.getD_append_right _ _ _ _ le_rfl]
          intro u hu
          simp only [Nat.sub_self, List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl
          · exact Finset.mem_insert_of_mem ha
          · exact Finset.mem_insert_of_mem hb
      · rcases h5 w hw with hlt | ⟨i, hi, heq, hop, hin⟩
        · exact Or.inl hlt
        · exact Or.inr ⟨i, hi, heq, hop, fun u hu => Finset.mem_insert_of_mem (hin u hu)⟩
    · intro i hi hop
      obtain ⟨x, y, hxy, hmem⟩ := h7 i hi hop
      refine ⟨x, y, hxy, ?_⟩
      rcases hmem with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · exact Or.inl ⟨Finset.mem_insert_of_mem hx, hy⟩
      · exact Or.inr ⟨hx, Finset.mem_insert_of_mem hy⟩
  have hAppendOrL : ∀ (gs : List Gate) (P L : Finset ℕ) (a b : ℕ),
      GoodState gs P L → a ∈ L → b ∈ L →
      GoodState (gs ++ [Gate.mk GateOp.or [a, b]]) P (insert (Np + Nl + gs.length) L) := by
    intro gs P L a b hG ha hb
    have hha : a < Np + Nl + gs.length := hG.2.2.2.1 a ha
    have hhb : b < Np + Nl + gs.length := hG.2.2.2.1 b hb
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hAppendOr gs P L a b hG hha hhb
    refine ⟨h1, h2, h3, ?_, h5, ?_, ?_⟩
    · intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · simp
      · exact h4 w hw
    · intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · right
        refine ⟨gs.length, by simp, rfl, ?_, ?_⟩
        · rw [List.getD_append_right _ _ _ _ le_rfl]; simp
        · rw [List.getD_append_right _ _ _ _ le_rfl]
          intro u hu
          simp only [Nat.sub_self, List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl
          · exact Finset.mem_insert_of_mem ha
          · exact Finset.mem_insert_of_mem hb
      · rcases h6 w hw with hlt | ⟨i, hi, heq, hop, hin⟩
        · exact Or.inl hlt
        · exact Or.inr ⟨i, hi, heq, hop, fun u hu => Finset.mem_insert_of_mem (hin u hu)⟩
    · intro i hi hop
      obtain ⟨x, y, hxy, hmem⟩ := h7 i hi hop
      refine ⟨x, y, hxy, ?_⟩
      rcases hmem with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · exact Or.inl ⟨hx, Finset.mem_insert_of_mem hy⟩
      · exact Or.inr ⟨Finset.mem_insert_of_mem hx, hy⟩
  have hAppendAnd : ∀ (gs : List Gate) (P L : Finset ℕ) (a b : ℕ),
      GoodState gs P L → ((a ∈ P ∧ b ∈ L) ∨ (a ∈ L ∧ b ∈ P)) →
      GoodState (gs ++ [Gate.mk GateOp.and [a, b]]) P L := by
    rintro gs P L a b ⟨h1, h2, h3, h4, h5, h6, h7⟩ hab
    have hha : a < Np + Nl + gs.length := by
      rcases hab with ⟨ha, _⟩ | ⟨ha, _⟩
      · exact h3 a ha
      · exact h4 a ha
    have hhb : b < Np + Nl + gs.length := by
      rcases hab with ⟨_, hb⟩ | ⟨_, hb⟩
      · exact h4 b hb
      · exact h3 b hb
    have hget : ∀ i < gs.length, (gs ++ [Gate.mk GateOp.and [a, b]]).getD i (Gate.mk GateOp.or []) = gs.getD i (Gate.mk GateOp.or []) :=
      fun i hi => List.getD_append _ _ _ _ hi
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact h1 g hg
      · rw [List.mem_singleton.mp hg]; exact ⟨Or.inl rfl, rfl⟩
    · intro j hj u hu
      simp only [List.length_append, List.length_singleton] at hj
      by_cases hlt : j < gs.length
      · rw [hget j hlt] at hu; exact h2 j hlt u hu
      · have hjEq : j = gs.length := by omega
        subst hjEq
        rw [List.getD_append_right _ _ _ _ le_rfl] at hu
        simp only [Nat.sub_self, List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hu
        rcases hu with rfl | rfl <;> omega
    · intro w hw; have := h3 w hw; simp; omega
    · intro w hw; have := h4 w hw; simp; omega
    · intro w hw
      rcases h5 w hw with hlt | ⟨i, hi, heq, hop, hin⟩
      · exact Or.inl hlt
      · right; refine ⟨i, by simp; omega, heq, ?_, ?_⟩
        · rw [hget i hi]; exact hop
        · rw [hget i hi]; exact hin
    · intro w hw
      rcases h6 w hw with hlt | ⟨i, hi, heq, hop, hin⟩
      · exact Or.inl hlt
      · right; refine ⟨i, by simp; omega, heq, ?_, ?_⟩
        · rw [hget i hi]; exact hop
        · rw [hget i hi]; exact hin
    · intro i hi hop
      simp only [List.length_append, List.length_singleton] at hi
      by_cases hlt : i < gs.length
      · rw [hget i hlt] at hop ⊢; exact h7 i hlt hop
      · have hiEq : i = gs.length := by omega
        subst hiEq
        rw [List.getD_append_right _ _ _ _ le_rfl]
        simp only [Nat.sub_self, List.getD_cons_zero]
        exact ⟨a, b, rfl, hab⟩
  have hAnyCongr : ∀ (xs : List ℕ) (f g : ℕ → Bool), (∀ x ∈ xs, f x = g x) → xs.any f = xs.any g := by
    intro xs f g h
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true]
    constructor
    · rintro ⟨x, hx, hf⟩; exact ⟨x, hx, (h x hx) ▸ hf⟩
    · rintro ⟨x, hx, hg⟩; exact ⟨x, hx, (h x hx).symm ▸ hg⟩
  let chainOr : List Gate × ℕ → List ℕ → List Gate × ℕ := fun st xs =>
    xs.foldl (fun acc x => (acc.1 ++ [Gate.mk GateOp.or [acc.2, x]], Np + Nl + acc.1.length)) st
  have hChainOr : ∀ (xs : List ℕ) (gs : List Gate) (P L : Finset ℕ) (cur : ℕ),
      GoodState gs P L → cur < Np + Nl + gs.length → (∀ x ∈ xs, x < Np + Nl + gs.length) →
      let res := chainOr (gs, cur) xs
      ∃ ext : List Gate, res.1 = gs ++ ext ∧ ext.length = xs.length ∧
        GoodState res.1 P L ∧ res.2 < Np + Nl + res.1.length ∧
        ∀ y : Fin (Np + Nl) → Bool,
          (res.1.foldl stepW (List.ofFn y)).getD res.2 false =
            ((gs.foldl stepW (List.ofFn y)).getD cur false ||
              xs.any (fun x => (gs.foldl stepW (List.ofFn y)).getD x false)) := by
    intro xs
    induction xs with
    | nil =>
      intro gs P L cur hG hcur _
      exact ⟨[], by simp [chainOr], rfl, hG, hcur, fun y => by simp [chainOr]⟩
    | cons x xs ih =>
      intro gs P L cur hG hcur hxs
      have hx : x < Np + Nl + gs.length := hxs x (by simp)
      let gs1 := gs ++ [Gate.mk GateOp.or [cur, x]]
      let cur1 := Np + Nl + gs.length
      have hG1 : GoodState gs1 P L := hAppendOr gs P L cur x hG hcur hx
      have hcur1 : cur1 < Np + Nl + gs1.length := by simp [gs1, cur1]
      have hxs1 : ∀ u ∈ xs, u < Np + Nl + gs1.length := by
        intro u hu; have := hxs u (by simp [hu]); simp [gs1]; omega
      obtain ⟨ext, heq, hlen, hG2, hcur2, hval2⟩ := ih gs1 P L cur1 hG1 hcur1 hxs1
      have hres : chainOr (gs, cur) (x :: xs) = chainOr (gs1, cur1) xs := rfl
      refine ⟨[Gate.mk GateOp.or [cur, x]] ++ ext, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hres, heq]; simp [gs1, List.append_assoc]
      · simp [hlen]
      · rw [hres]; exact hG2
      · rw [hres]; exact hcur2
      · intro y
        rw [hres, hval2 y]
        have hcur1Val : (gs1.foldl stepW (List.ofFn y)).getD cur1 false =
            ((gs.foldl stepW (List.ofFn y)).getD cur false || (gs.foldl stepW (List.ofFn y)).getD x false) := by
          rw [hWiresStep gs (Gate.mk GateOp.or [cur, x]) y]
          change ((gs.foldl stepW (List.ofFn y)).getD cur false || ((gs.foldl stepW (List.ofFn y)).getD x false || false)) = _
          rw [Bool.or_false]
        have hAnyEq : xs.any (fun u => (gs1.foldl stepW (List.ofFn y)).getD u false) =
            xs.any (fun u => (gs.foldl stepW (List.ofFn y)).getD u false) := by
          apply hAnyCongr
          intro u hu
          have huLt : u < Np + Nl + gs.length := hxs u (by simp [hu])
          rw [show gs1 = gs ++ [Gate.mk GateOp.or [cur, x]] from rfl, hFoldAppend,
            hFoldKeep _ _ u (by rw [hFoldLen, List.length_ofFn]; exact huLt)]
        rw [hcur1Val, hAnyEq, List.any_cons, Bool.or_assoc]
  let chainOrL : List Gate × Finset ℕ × ℕ → List ℕ → List Gate × Finset ℕ × ℕ := fun st xs =>
    xs.foldl (fun acc x =>
      (acc.1 ++ [Gate.mk GateOp.or [acc.2.2, x]], insert (Np + Nl + acc.1.length) acc.2.1, Np + Nl + acc.1.length)) st
  have hChainOrL : ∀ (xs : List ℕ) (gs : List Gate) (P L : Finset ℕ) (cur : ℕ),
      GoodState gs P L → cur ∈ L → (∀ x ∈ xs, x ∈ L) →
      let res := chainOrL (gs, L, cur) xs
      ∃ ext : List Gate, res.1 = gs ++ ext ∧ ext.length = xs.length ∧
        L ⊆ res.2.1 ∧ GoodState res.1 P res.2.1 ∧ res.2.2 ∈ res.2.1 ∧
        ∀ y : Fin (Np + Nl) → Bool,
          (res.1.foldl stepW (List.ofFn y)).getD res.2.2 false =
            ((gs.foldl stepW (List.ofFn y)).getD cur false ||
              xs.any (fun x => (gs.foldl stepW (List.ofFn y)).getD x false)) := by
    intro xs
    induction xs with
    | nil =>
      intro gs P L cur hG hcur _
      exact ⟨[], by simp [chainOrL], rfl, Finset.Subset.refl L, hG, hcur, fun y => by simp [chainOrL]⟩
    | cons x xs ih =>
      intro gs P L cur hG hcur hxs
      have hx : x ∈ L := hxs x (by simp)
      let gs1 := gs ++ [Gate.mk GateOp.or [cur, x]]
      let L1 := insert (Np + Nl + gs.length) L
      let cur1 := Np + Nl + gs.length
      have hG1 : GoodState gs1 P L1 := hAppendOrL gs P L cur x hG hcur hx
      have hLsub1 : L ⊆ L1 := Finset.subset_insert _ _
      have hcur1 : cur1 ∈ L1 := Finset.mem_insert_self _ _
      have hxs1 : ∀ u ∈ xs, u ∈ L1 := fun u hu => hLsub1 (hxs u (by simp [hu]))
      obtain ⟨ext, heq, hlen, hLsub2, hG2, hcur2, hval2⟩ := ih gs1 P L1 cur1 hG1 hcur1 hxs1
      have hres : chainOrL (gs, L, cur) (x :: xs) = chainOrL (gs1, L1, cur1) xs := rfl
      refine ⟨[Gate.mk GateOp.or [cur, x]] ++ ext, ?_, ?_, hLsub1.trans hLsub2, ?_, ?_, ?_⟩
      · rw [hres, heq]; simp [gs1, List.append_assoc]
      · simp [hlen]
      · rw [hres]; exact hG2
      · rw [hres]; exact hcur2
      · intro y
        rw [hres, hval2 y]
        have hcur1Val : (gs1.foldl stepW (List.ofFn y)).getD cur1 false =
            ((gs.foldl stepW (List.ofFn y)).getD cur false || (gs.foldl stepW (List.ofFn y)).getD x false) := by
          rw [hWiresStep gs (Gate.mk GateOp.or [cur, x]) y]
          change ((gs.foldl stepW (List.ofFn y)).getD cur false || ((gs.foldl stepW (List.ofFn y)).getD x false || false)) = _
          rw [Bool.or_false]
        have hAnyEq : xs.any (fun u => (gs1.foldl stepW (List.ofFn y)).getD u false) =
            xs.any (fun u => (gs.foldl stepW (List.ofFn y)).getD u false) := by
          apply hAnyCongr
          intro u hu
          have huLt : u < Np + Nl + gs.length := hG.2.2.2.1 u (hxs u (by simp [hu]))
          rw [show gs1 = gs ++ [Gate.mk GateOp.or [cur, x]] from rfl, hFoldAppend,
            hFoldKeep _ _ u (by rw [hFoldLen, List.length_ofFn]; exact huLt)]
        rw [hcur1Val, hAnyEq, List.any_cons, Bool.or_assoc]
  let chainOrP : List Gate × Finset ℕ × ℕ → List ℕ → List Gate × Finset ℕ × ℕ := fun st xs =>
    xs.foldl (fun acc x =>
      (acc.1 ++ [Gate.mk GateOp.or [acc.2.2, x]], insert (Np + Nl + acc.1.length) acc.2.1, Np + Nl + acc.1.length)) st
  have hChainOrP : ∀ (xs : List ℕ) (gs : List Gate) (P L : Finset ℕ) (cur : ℕ),
      GoodState gs P L → cur ∈ P → (∀ x ∈ xs, x ∈ P) →
      let res := chainOrP (gs, P, cur) xs
      ∃ ext : List Gate, res.1 = gs ++ ext ∧ ext.length = xs.length ∧
        P ⊆ res.2.1 ∧ GoodState res.1 res.2.1 L ∧ res.2.2 ∈ res.2.1 ∧
        ∀ y : Fin (Np + Nl) → Bool,
          (res.1.foldl stepW (List.ofFn y)).getD res.2.2 false =
            ((gs.foldl stepW (List.ofFn y)).getD cur false ||
              xs.any (fun x => (gs.foldl stepW (List.ofFn y)).getD x false)) := by
    intro xs
    induction xs with
    | nil =>
      intro gs P L cur hG hcur _
      exact ⟨[], by simp [chainOrP], rfl, Finset.Subset.refl P, hG, hcur, fun y => by simp [chainOrP]⟩
    | cons x xs ih =>
      intro gs P L cur hG hcur hxs
      have hx : x ∈ P := hxs x (by simp)
      let gs1 := gs ++ [Gate.mk GateOp.or [cur, x]]
      let P1 := insert (Np + Nl + gs.length) P
      let cur1 := Np + Nl + gs.length
      have hG1 : GoodState gs1 P1 L := hAppendOrP gs P L cur x hG hcur hx
      have hPsub1 : P ⊆ P1 := Finset.subset_insert _ _
      have hcur1 : cur1 ∈ P1 := Finset.mem_insert_self _ _
      have hxs1 : ∀ u ∈ xs, u ∈ P1 := fun u hu => hPsub1 (hxs u (by simp [hu]))
      obtain ⟨ext, heq, hlen, hPsub2, hG2, hcur2, hval2⟩ := ih gs1 P1 L cur1 hG1 hcur1 hxs1
      have hres : chainOrP (gs, P, cur) (x :: xs) = chainOrP (gs1, P1, cur1) xs := rfl
      refine ⟨[Gate.mk GateOp.or [cur, x]] ++ ext, ?_, ?_, hPsub1.trans hPsub2, ?_, ?_, ?_⟩
      · rw [hres, heq]; simp [gs1, List.append_assoc]
      · simp [hlen]
      · rw [hres]; exact hG2
      · rw [hres]; exact hcur2
      · intro y
        rw [hres, hval2 y]
        have hcur1Val : (gs1.foldl stepW (List.ofFn y)).getD cur1 false =
            ((gs.foldl stepW (List.ofFn y)).getD cur false || (gs.foldl stepW (List.ofFn y)).getD x false) := by
          rw [hWiresStep gs (Gate.mk GateOp.or [cur, x]) y]
          change ((gs.foldl stepW (List.ofFn y)).getD cur false || ((gs.foldl stepW (List.ofFn y)).getD x false || false)) = _
          rw [Bool.or_false]
        have hAnyEq : xs.any (fun u => (gs1.foldl stepW (List.ofFn y)).getD u false) =
            xs.any (fun u => (gs.foldl stepW (List.ofFn y)).getD u false) := by
          apply hAnyCongr
          intro u hu
          have huLt : u < Np + Nl + gs.length := hG.2.2.1 u (hxs u (by simp [hu]))
          rw [show gs1 = gs ++ [Gate.mk GateOp.or [cur, x]] from rfl, hFoldAppend,
            hFoldKeep _ _ u (by rw [hFoldLen, List.length_ofFn]; exact huLt)]
        rw [hcur1Val, hAnyEq, List.any_cons, Bool.or_assoc]
  have hBaseGood : GoodState [] (Finset.range Np) (Finset.Ico Np (Np + Nl)) := by
    refine ⟨(fun g hg => by cases hg), (fun j hj => by cases hj), ?_, ?_, ?_, ?_, (fun i hi => by cases hi)⟩
    · intro w hw; simp only [Finset.mem_range] at hw; omega
    · intro w hw; simp only [Finset.mem_Ico] at hw; omega
    · intro w hw; left; exact Finset.mem_range.mp hw
    · intro w hw; left; exact Finset.mem_Ico.mp hw
  have hBuildP : ∀ (ps : List (Fin Np)), (∀ p ∈ ps, (Lp p).Nonempty) →
      ∃ (gs : List Gate) (P L : Finset ℕ) (aws : List ℕ),
        GoodState gs P L ∧
        Finset.range Np ⊆ P ∧ Finset.Ico Np (Np + Nl) ⊆ L ∧
        gs.length = (ps.map (fun p => (Lp p).card)).sum ∧
        aws.length = ps.length ∧
        (∀ aw ∈ aws, aw < Np + Nl + gs.length) ∧
        ∀ y : Fin (Np + Nl) → Bool,
          aws.any (fun aw => (gs.foldl stepW (List.ofFn y)).getD aw false) =
            decide (∃ p ∈ ps, ∃ l ∈ Lp p, y (Fin.castAdd Nl p) = true ∧ y (Fin.natAdd Np l) = true) := by
    intro ps
    induction ps with
    | nil =>
      intro _
      exact ⟨[], Finset.range Np, Finset.Ico Np (Np + Nl), [], hBaseGood,
        Finset.Subset.refl _, Finset.Subset.refl _, rfl, rfl, (fun _ h => by cases h),
        (fun _ => by simp)⟩
    | cons p ps ih =>
      intro hne
      obtain ⟨gs, P, L, aws, hG, hPsub, hLsub, hglen, hawlen, hawlt, hval⟩ :=
        ih (fun q hq => hne q (by simp [hq]))
      have hneP : (Lp p).Nonempty := hne p (by simp)
      cases hls : (Lp p).toList with
      | nil =>
        exfalso
        obtain ⟨l0, hl0⟩ := hneP
        have hmem : l0 ∈ (Lp p).toList := Finset.mem_toList.mpr hl0
        rw [hls] at hmem
        cases hmem
      | cons l0 ls =>
        have hLenLs : 1 + ls.length = (Lp p).card := by
          have := Finset.length_toList (Lp p)
          rw [hls] at this
          simp only [List.length_cons] at this
          omega
        have hl0L : Np + l0.val ∈ L := hLsub (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
        have hlsL : ∀ w ∈ ls.map (fun l : Fin Nl => Np + l.val), w ∈ L := by
          intro w hw
          obtain ⟨l, _, rfl⟩ := List.mem_map.mp hw
          exact hLsub (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
        let res := chainOrL (gs, L, Np + l0.val) (ls.map (fun l : Fin Nl => Np + l.val))
        obtain ⟨ext, heq, hexlen, hLsub', hG1, hcur1, hval1⟩ :=
          hChainOrL (ls.map (fun l : Fin Nl => Np + l.val)) gs P L (Np + l0.val) hG hl0L hlsL
        have hpP : p.val ∈ P := hPsub (Finset.mem_range.mpr p.isLt)
        let gs2 := res.1 ++ [Gate.mk GateOp.and [p.val, res.2.2]]
        let aw := Np + Nl + res.1.length
        have hG2 : GoodState gs2 P res.2.1 := hAppendAnd res.1 P res.2.1 p.val res.2.2 hG1 (Or.inl ⟨hpP, hcur1⟩)
        refine ⟨gs2, P, res.2.1, aw :: aws, hG2, hPsub, hLsub.trans hLsub', ?_, ?_, ?_, ?_⟩
        · have hresLen : res.1.length = gs.length + ls.length := by
            change (chainOrL (gs, L, Np + l0.val) (ls.map (fun l : Fin Nl => Np + l.val))).1.length = _
            rw [heq, List.length_append, hexlen, List.length_map]
          have hgs2Len : gs2.length = res.1.length + 1 := by simp [gs2]
          simp only [List.map_cons, List.sum_cons]
          omega
        · simp [hawlen]
        · intro u hu
          rcases List.mem_cons.mp hu with rfl | hu
          · simp [gs2, aw]
          · have huLt := hawlt u hu
            have hresLen : res.1.length = gs.length + ls.length := by
              change (chainOrL (gs, L, Np + l0.val) (ls.map (fun l : Fin Nl => Np + l.val))).1.length = _
              rw [heq, List.length_append, hexlen, List.length_map]
            have hgs2Len : gs2.length = res.1.length + 1 := by simp [gs2]
            omega
        · intro y
          have hKeepOld : aws.any (fun u => (gs2.foldl stepW (List.ofFn y)).getD u false) =
              aws.any (fun u => (gs.foldl stepW (List.ofFn y)).getD u false) := by
            apply hAnyCongr
            intro u hu
            have huLt : u < Np + Nl + gs.length := hawlt u hu
            have hgs2 : gs2 = gs ++ (ext ++ [Gate.mk GateOp.and [p.val, res.2.2]]) := by
              change res.1 ++ [Gate.mk GateOp.and [p.val, res.2.2]] = _
              rw [show res.1 = gs ++ ext from heq, List.append_assoc]
            rw [hgs2, hFoldAppend, hFoldKeep _ _ u (by rw [hFoldLen, List.length_ofFn]; exact huLt)]
          have hawVal : (gs2.foldl stepW (List.ofFn y)).getD aw false =
              (y (Fin.castAdd Nl p) &&
                decide (∃ l ∈ Lp p, y (Fin.natAdd Np l) = true)) := by
            rw [hWiresStep res.1 (Gate.mk GateOp.and [p.val, res.2.2]) y]
            change ((res.1.foldl stepW (List.ofFn y)).getD p.val false && ((res.1.foldl stepW (List.ofFn y)).getD res.2.2 false && true)) = _
            rw [Bool.and_true]
            rw [hInputValPt res.1 y p, hval1 y]
            congr 1
            rw [hInputValLn gs y l0]
            apply Bool.eq_iff_iff.mpr
            simp only [Bool.or_eq_true, List.any_eq_true, List.mem_map, decide_eq_true_eq]
            constructor
            · rintro (h | ⟨w, ⟨l, hl, rfl⟩, hw⟩)
              · exact ⟨l0, Finset.mem_toList.mp (by rw [hls]; simp), h⟩
              · rw [hInputValLn gs y l] at hw
                exact ⟨l, Finset.mem_toList.mp (by rw [hls]; simp [hl]), hw⟩
            · rintro ⟨l, hl, hy⟩
              have hmem : l ∈ l0 :: ls := by rw [← hls]; exact Finset.mem_toList.mpr hl
              rcases List.mem_cons.mp hmem with rfl | hl'
              · exact Or.inl hy
              · right
                refine ⟨Np + l.val, ⟨l, hl', rfl⟩, ?_⟩
                rw [hInputValLn gs y l]
                exact hy
          rw [List.any_cons, hKeepOld, hval y, hawVal]
          apply Bool.eq_iff_iff.mpr
          simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.mem_cons]
          constructor
          · rintro (⟨hp, l, hl, hyl⟩ | ⟨q, hq, l, hl, hqp, hyl⟩)
            · exact ⟨p, Or.inl rfl, l, hl, hp, hyl⟩
            · exact ⟨q, Or.inr hq, l, hl, hqp, hyl⟩
          · rintro ⟨q, rfl | hq, l, hl, hqp, hyl⟩
            · exact Or.inl ⟨hqp, l, hl, hyl⟩
            · exact Or.inr ⟨q, hq, l, hl, hqp, hyl⟩
  obtain ⟨gsP, P1, L1, awsP, hGP, hP1sub, hL1sub, hgsPlen, hawsPlen, hawsPlt, hvalP⟩ :=
    hBuildP Kp'.toList (fun p hp => (Finset.mem_filter.mp (Finset.mem_toList.mp hp)).2)
  have hBuildL : ∀ (ls : List (Fin Nl)), (∀ l ∈ ls, (Pl l).Nonempty) →
      ∃ (gs : List Gate) (P L : Finset ℕ) (aws : List ℕ),
        GoodState gs P L ∧
        P1 ⊆ P ∧ L1 ⊆ L ∧
        gs.length = gsP.length + (ls.map (fun l => (Pl l).card)).sum ∧
        aws.length = awsP.length + ls.length ∧
        (∀ aw ∈ aws, aw < Np + Nl + gs.length) ∧
        ∀ y : Fin (Np + Nl) → Bool,
          aws.any (fun aw => (gs.foldl stepW (List.ofFn y)).getD aw false) =
            (decide (∃ p ∈ Kp'.toList, ∃ l ∈ Lp p, y (Fin.castAdd Nl p) = true ∧ y (Fin.natAdd Np l) = true) ||
             decide (∃ l ∈ ls, ∃ p ∈ Pl l, y (Fin.castAdd Nl p) = true ∧ y (Fin.natAdd Np l) = true)) := by
    intro ls
    induction ls with
    | nil =>
      intro _
      exact ⟨gsP, P1, L1, awsP, hGP, Finset.Subset.refl _, Finset.Subset.refl _,
        by simp, by simp, hawsPlt, fun y => by rw [hvalP y]; simp⟩
    | cons l ls ih =>
      intro hne
      obtain ⟨gs, P, L, aws, hG, hPsub, hLsub, hglen, hawlen, hawlt, hval⟩ :=
        ih (fun l' hl' => hne l' (by simp [hl']))
      have hneL : (Pl l).Nonempty := hne l (by simp)
      cases hps : (Pl l).toList with
      | nil =>
        exfalso
        obtain ⟨p0, hp0⟩ := hneL
        have hmem : p0 ∈ (Pl l).toList := Finset.mem_toList.mpr hp0
        rw [hps] at hmem
        cases hmem
      | cons p0 ps =>
        have hLenPs : 1 + ps.length = (Pl l).card := by
          have := Finset.length_toList (Pl l)
          rw [hps] at this
          simp only [List.length_cons] at this
          omega
        have hp0P : p0.val ∈ P := hPsub (hP1sub (Finset.mem_range.mpr p0.isLt))
        have hpsP : ∀ w ∈ ps.map (fun p : Fin Np => p.val), w ∈ P := by
          intro w hw
          obtain ⟨p, _, rfl⟩ := List.mem_map.mp hw
          exact hPsub (hP1sub (Finset.mem_range.mpr p.isLt))
        let res := chainOrP (gs, P, p0.val) (ps.map (fun p : Fin Np => p.val))
        obtain ⟨ext, heq, hexlen, hPsub', hG1, hcur1, hval1⟩ :=
          hChainOrP (ps.map (fun p : Fin Np => p.val)) gs P L p0.val hG hp0P hpsP
        have hlL : Np + l.val ∈ L := hLsub (hL1sub (Finset.mem_Ico.mpr ⟨by omega, by omega⟩))
        let gs2 := res.1 ++ [Gate.mk GateOp.and [res.2.2, Np + l.val]]
        let aw := Np + Nl + res.1.length
        have hG2 : GoodState gs2 res.2.1 L := hAppendAnd res.1 res.2.1 L res.2.2 (Np + l.val) hG1 (Or.inl ⟨hcur1, hlL⟩)
        refine ⟨gs2, res.2.1, L, aw :: aws, hG2, hPsub.trans hPsub', hLsub, ?_, ?_, ?_, ?_⟩
        · have hresLen : res.1.length = gs.length + ps.length := by
            change (chainOrP (gs, P, p0.val) (ps.map (fun p : Fin Np => p.val))).1.length = _
            rw [heq, List.length_append, hexlen, List.length_map]
          have hgs2Len : gs2.length = res.1.length + 1 := by simp [gs2]
          simp only [List.map_cons, List.sum_cons]
          omega
        · simp [hawlen]; omega
        · intro u hu
          rcases List.mem_cons.mp hu with rfl | hu
          · simp [gs2, aw]
          · have huLt := hawlt u hu
            have hresLen : res.1.length = gs.length + ps.length := by
              change (chainOrP (gs, P, p0.val) (ps.map (fun p : Fin Np => p.val))).1.length = _
              rw [heq, List.length_append, hexlen, List.length_map]
            have hgs2Len : gs2.length = res.1.length + 1 := by simp [gs2]
            omega
        · intro y
          have hKeepOld : aws.any (fun u => (gs2.foldl stepW (List.ofFn y)).getD u false) =
              aws.any (fun u => (gs.foldl stepW (List.ofFn y)).getD u false) := by
            apply hAnyCongr
            intro u hu
            have huLt : u < Np + Nl + gs.length := hawlt u hu
            have hgs2 : gs2 = gs ++ (ext ++ [Gate.mk GateOp.and [res.2.2, Np + l.val]]) := by
              change res.1 ++ [Gate.mk GateOp.and [res.2.2, Np + l.val]] = _
              rw [show res.1 = gs ++ ext from heq, List.append_assoc]
            rw [hgs2, hFoldAppend, hFoldKeep _ _ u (by rw [hFoldLen, List.length_ofFn]; exact huLt)]
          have hawVal : (gs2.foldl stepW (List.ofFn y)).getD aw false =
              (decide (∃ p ∈ Pl l, y (Fin.castAdd Nl p) = true) && y (Fin.natAdd Np l)) := by
            rw [hWiresStep res.1 (Gate.mk GateOp.and [res.2.2, Np + l.val]) y]
            change ((res.1.foldl stepW (List.ofFn y)).getD res.2.2 false && ((res.1.foldl stepW (List.ofFn y)).getD (Np + l.val) false && true)) = _
            rw [Bool.and_true]
            rw [hInputValLn res.1 y l, hval1 y]
            congr 1
            rw [hInputValPt gs y p0]
            apply Bool.eq_iff_iff.mpr
            simp only [Bool.or_eq_true, List.any_eq_true, List.mem_map, decide_eq_true_eq]
            constructor
            · rintro (h | ⟨w, ⟨p, hp, rfl⟩, hw⟩)
              · exact ⟨p0, Finset.mem_toList.mp (by rw [hps]; simp), h⟩
              · rw [hInputValPt gs y p] at hw
                exact ⟨p, Finset.mem_toList.mp (by rw [hps]; simp [hp]), hw⟩
            · rintro ⟨p, hp, hy⟩
              have hmem : p ∈ p0 :: ps := by rw [← hps]; exact Finset.mem_toList.mpr hp
              rcases List.mem_cons.mp hmem with rfl | hp'
              · exact Or.inl hy
              · right
                refine ⟨p.val, ⟨p, hp', rfl⟩, ?_⟩
                rw [hInputValPt gs y p]
                exact hy
          rw [List.any_cons, hKeepOld, hval y, hawVal]
          apply Bool.eq_iff_iff.mpr
          simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.mem_cons]
          constructor
          · rintro (⟨⟨p, hp, hyp⟩, hyl⟩ | h1 | ⟨l', hl', p, hp, hyp, hyl⟩)
            · exact Or.inr ⟨l, Or.inl rfl, p, hp, hyp, hyl⟩
            · exact Or.inl h1
            · exact Or.inr ⟨l', Or.inr hl', p, hp, hyp, hyl⟩
          · rintro (h1 | ⟨l', rfl | hl', p, hp, hyp, hyl⟩)
            · exact Or.inr (Or.inl h1)
            · exact Or.inl ⟨⟨p, hp, hyp⟩, hyl⟩
            · exact Or.inr (Or.inr ⟨l', hl', p, hp, hyp, hyl⟩)
  obtain ⟨gsAll, Pfin, Lfin, awsAll, hGall, _, _, hgsAllLen, hawsAllLen, hawsAllLt, hvalAll⟩ :=
    hBuildL Kl'.toList (fun l hl => (Finset.mem_filter.mp (Finset.mem_toList.mp hl)).2)
  have hPsum : (Kp'.toList.map (fun p => (Lp p).card)).sum = ∑ p ∈ Kp', (Lp p).card := by
    rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
    rfl
  have hLsum : (Kl'.toList.map (fun l => (Pl l).card)).sum = ∑ l ∈ Kl', (Pl l).card := by
    rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
    rfl
  have hgsCard : gsAll.length = G.edgeFinset.card := by
    rw [hgsAllLen, hgsPlen, hPsum, hLsum, hSumEdges']
  have hawsCard : awsAll.length = Kp'.card + Kl'.card := by
    rw [hawsAllLen, hawsPlen, Finset.length_toList, Finset.length_toList]
  cases haws : awsAll with
  | nil =>
    exfalso
    rw [haws] at hawsCard
    simp at hawsCard
    omega
  | cons aw0 aws =>
    have haw0Lt : aw0 < Np + Nl + gsAll.length := hawsAllLt aw0 (by rw [haws]; simp)
    have hawsLt : ∀ u ∈ aws, u < Np + Nl + gsAll.length := fun u hu => hawsAllLt u (by rw [haws]; simp [hu])
    let fin := chainOr (gsAll, aw0) aws
    obtain ⟨extFin, heqFin, hexFinLen, hGfin, _, hvalFin⟩ :=
      hChainOr aws gsAll Pfin Lfin aw0 hGall haw0Lt hawsLt
    let D : Circuit := ⟨fin.1, fin.2⟩
    refine ⟨D, Pfin, Lfin, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · intro g hg; exact (hGfin.1 g hg).1
      · intro j hj u hu; exact hGfin.2.1 j hj u hu
      · intro g hg; exact (hGfin.1 g hg).2
    · intro y
      show (fin.1.foldl stepW (List.ofFn y)).getD fin.2 false = _
      rw [hvalFin y]
      have hConsAny : ((gsAll.foldl stepW (List.ofFn y)).getD aw0 false ||
          aws.any (fun x => (gsAll.foldl stepW (List.ofFn y)).getD x false)) =
          awsAll.any (fun aw => (gsAll.foldl stepW (List.ofFn y)).getD aw false) := by
        rw [haws, List.any_cons]
      rw [hConsAny, hvalAll y]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, decide_eq_true_eq, Finset.mem_toList]
      constructor
      · rintro (⟨p, _, l, hl, hyp, hyl⟩ | ⟨l, _, p, hp, hyp, hyl⟩)
        · exact ⟨p, l, (Finset.mem_filter.mp hl).2, hyp, hyl⟩
        · exact ⟨p, l, (Finset.mem_filter.mp hp).2.1, hyp, hyl⟩
      · rintro ⟨p, l, hI, hyp, hyl⟩
        by_cases hpK : p ∈ Kp
        · left
          refine ⟨p, Finset.mem_filter.mpr ⟨hpK, ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hI⟩⟩⟩,
            l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hI⟩, hyp, hyl⟩
        · right
          have hlK : l ∈ Kl := by
            simp only [Kl, Finset.mem_filter, Finset.mem_univ, true_and]
            rcases hKcov (Fin.castAdd Nl p) (Fin.natAdd Np l) ⟨p, l, hI, Or.inl ⟨rfl, rfl⟩⟩ with h1 | h2
            · exfalso; exact hpK (Finset.mem_filter.mpr ⟨Finset.mem_univ p, h1⟩)
            · exact h2
          refine ⟨l, Finset.mem_filter.mpr ⟨hlK, ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hI, hpK⟩⟩⟩,
            p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hI, hpK⟩, hyp, hyl⟩
    · show fin.1.length ≤ C.size
      change (chainOr (gsAll, aw0) aws).1.length ≤ C.size
      rw [heqFin, List.length_append, hgsCard, hexFinLen]
      have hawsL : 1 + aws.length = Kp'.card + Kl'.card := by
        rw [haws] at hawsCard
        simp only [List.length_cons] at hawsCard
        omega
      omega
    · exact hGfin.2.2.2.2.1
    · exact hGfin.2.2.2.2.2.1
    · exact hGfin.2.2.2.2.2.2
