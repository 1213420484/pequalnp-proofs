import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Order.Minimal
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace PEqualNP.Outside.L_meta_4889

def inc (a b : Fin 13) : Prop :=
  (a.val + b.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)

instance : DecidableRel inc := fun a b => by unfold inc; infer_instance

lemma inc_symm (a b : Fin 13) : inc a b ↔ inc b a := by
  simp [inc, Nat.add_comm]

lemma lines_card (p : Fin 13) :
    (Finset.univ.filter fun l : Fin 13 => inc p l).card = 4 := by
  revert p; decide +kernel

lemma inter_card (p q : Fin 13) (h : p ≠ q) :
    (Finset.univ.filter fun l : Fin 13 => inc p l ∧ inc q l).card = 1 := by
  revert p q h; decide +kernel

def orth (S : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter fun l => ∀ p ∈ S, ¬ inc p l

lemma exists_orth_inc (S : Finset (Fin 13)) (hS : S.card ≤ 3) (p : Fin 13) (hp : p ∉ S) :
    ∃ l ∈ orth S, inc p l := by
  let Lp : Finset (Fin 13) := Finset.univ.filter fun l => inc p l
  let bad : Finset (Fin 13) := S.biUnion fun q => Finset.univ.filter fun l => inc p l ∧ inc q l
  have hbad : bad.card ≤ S.card := by
    calc bad.card
        ≤ ∑ q ∈ S, (Finset.univ.filter fun l : Fin 13 => inc p l ∧ inc q l).card :=
          Finset.card_biUnion_le
      _ = ∑ _q ∈ S, 1 := by
          refine Finset.sum_congr rfl fun q hq => ?_
          have hpq : p ≠ q := fun e => hp (e ▸ hq)
          exact inter_card p q hpq
      _ = S.card := by simp
  have hlt : bad.card < Lp.card := by
    have hLp : Lp.card = 4 := lines_card p
    omega
  obtain ⟨l, hlLp, hlNotBad⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  have hinc : inc p l := (Finset.mem_filter.mp hlLp).2
  refine ⟨l, ?_, hinc⟩
  simp only [orth, Finset.mem_filter, Finset.mem_univ, true_and]
  intro q hq hql
  apply hlNotBad
  simp only [bad, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨q, hq, hinc, hql⟩

def mkVec (P L : Finset (Fin 13)) (i : Fin 26) : Bool :=
  if i.val < 13 then decide (Fin.ofNat 13 i.val ∈ P) else decide (Fin.ofNat 13 i.val ∈ L)

def hasInc (z : Fin 26 → Bool) : Prop :=
  ∃ p l : Fin 13, inc p l ∧ z (Fin.castAdd 13 p) = true ∧ z (Fin.natAdd 13 l) = true

lemma mkVec_castAdd (P L : Finset (Fin 13)) (p : Fin 13) :
    mkVec P L (Fin.castAdd 13 p) = decide (p ∈ P) := by
  simp only [mkVec, Fin.val_castAdd, p.isLt, ↓reduceIte]
  have h : Fin.ofNat 13 p.val = p := Fin.ext (Nat.mod_eq_of_lt p.isLt)
  simp only [h]

lemma mkVec_natAdd (P L : Finset (Fin 13)) (l : Fin 13) :
    mkVec P L (Fin.natAdd 13 l) = decide (l ∈ L) := by
  have hnot : ¬ (13 + l.val < 13) := by omega
  simp only [mkVec, Fin.val_natAdd, hnot, ↓reduceIte]
  have h : Fin.ofNat 13 (13 + l.val) = l := Fin.ext (by
    change (13 + l.val) % 13 = l.val
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt l.isLt])
  simp only [h]

lemma bool_le_imp {a b : Bool} (h : a ≤ b) : a = true → b = true := by
  cases a <;> cases b
  · intro h1; cases h1
  · intro _; rfl
  · exact absurd h (by decide)
  · intro _; rfl

lemma imp_bool_le {a b : Bool} (h : a = true → b = true) : a ≤ b := by
  cases a <;> cases b
  · decide
  · decide
  · exact absurd (h rfl) (by decide)
  · decide

lemma fin26_cases (i : Fin 26) :
    (∃ p : Fin 13, i = Fin.castAdd 13 p) ∨ (∃ l : Fin 13, i = Fin.natAdd 13 l) := by
  by_cases h : i.val < 13
  · left; exact ⟨⟨i.val, h⟩, Fin.ext rfl⟩
  · right; exact ⟨⟨i.val - 13, by omega⟩, Fin.ext (by simp; omega)⟩

lemma part1 (p l : Fin 13) (hpl : inc p l) : Minimal hasInc (mkVec {p} {l}) := by
  refine ⟨⟨p, l, hpl, ?_, ?_⟩, ?_⟩
  · rw [mkVec_castAdd]; simp
  · rw [mkVec_natAdd]; simp
  · intro y hy hle i
    apply imp_bool_le
    intro hmk
    obtain ⟨p', l', _, hyp', hyl'⟩ := hy
    have hp' : p' = p := by
      have h1 := bool_le_imp (hle (Fin.castAdd 13 p')) hyp'
      rw [mkVec_castAdd] at h1
      simpa using h1
    have hl' : l' = l := by
      have h1 := bool_le_imp (hle (Fin.natAdd 13 l')) hyl'
      rw [mkVec_natAdd] at h1
      simpa using h1
    rw [hp'] at hyp'
    rw [hl'] at hyl'
    rcases fin26_cases i with ⟨q, rfl⟩ | ⟨m, rfl⟩
    · rw [mkVec_castAdd] at hmk
      have hq : q = p := by simpa using hmk
      rw [hq]; exact hyp'
    · rw [mkVec_natAdd] at hmk
      have hm : m = l := by simpa using hmk
      rw [hm]; exact hyl'

lemma part2_left (S : Finset (Fin 13)) (hS : S.card ≤ 3) :
    Maximal (fun z => ¬ hasInc z) (mkVec S (orth S)) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨p, l, hpl, hp, hl⟩
    rw [mkVec_castAdd, decide_eq_true_eq] at hp
    rw [mkVec_natAdd, decide_eq_true_eq] at hl
    exact (Finset.mem_filter.mp hl).2 p hp hpl
  · intro y hny hle i
    apply imp_bool_le
    intro hyi
    rcases fin26_cases i with ⟨p, rfl⟩ | ⟨l, rfl⟩
    · rw [mkVec_castAdd, decide_eq_true_eq]
      by_contra hpS
      obtain ⟨l, hl, hpl⟩ := exists_orth_inc S hS p hpS
      have hyl : y (Fin.natAdd 13 l) = true :=
        bool_le_imp (hle (Fin.natAdd 13 l)) (by rw [mkVec_natAdd, decide_eq_true_eq]; exact hl)
      exact hny ⟨p, l, hpl, hyi, hyl⟩
    · rw [mkVec_natAdd, decide_eq_true_eq]
      by_contra hlO
      simp only [orth, Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_not] at hlO
      obtain ⟨p, hpS, hpl⟩ := hlO
      have hyp : y (Fin.castAdd 13 p) = true :=
        bool_le_imp (hle (Fin.castAdd 13 p)) (by rw [mkVec_castAdd, decide_eq_true_eq]; exact hpS)
      exact hny ⟨p, l, hpl, hyp, hyi⟩

lemma part2_right (S : Finset (Fin 13)) (hS : S.card ≤ 3) :
    Maximal (fun z => ¬ hasInc z) (mkVec (orth S) S) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨p, l, hpl, hp, hl⟩
    rw [mkVec_castAdd, decide_eq_true_eq] at hp
    rw [mkVec_natAdd, decide_eq_true_eq] at hl
    exact (Finset.mem_filter.mp hp).2 l hl ((inc_symm p l).mp hpl)
  · intro y hny hle i
    apply imp_bool_le
    intro hyi
    rcases fin26_cases i with ⟨p, rfl⟩ | ⟨l, rfl⟩
    · rw [mkVec_castAdd, decide_eq_true_eq]
      by_contra hpO
      simp only [orth, Finset.mem_filter, Finset.mem_univ, true_and, not_forall, not_not] at hpO
      obtain ⟨l, hlS, hlp⟩ := hpO
      have hyl : y (Fin.natAdd 13 l) = true :=
        bool_le_imp (hle (Fin.natAdd 13 l)) (by rw [mkVec_natAdd, decide_eq_true_eq]; exact hlS)
      exact hny ⟨p, l, (inc_symm l p).mp hlp, hyi, hyl⟩
    · rw [mkVec_natAdd, decide_eq_true_eq]
      by_contra hlS
      obtain ⟨p, hp, hlp⟩ := exists_orth_inc S hS l hlS
      have hyp : y (Fin.castAdd 13 p) = true :=
        bool_le_imp (hle (Fin.castAdd 13 p)) (by rw [mkVec_castAdd, decide_eq_true_eq]; exact hp)
      exact hny ⟨p, l, (inc_symm l p).mp hlp, hyp, hyi⟩

end PEqualNP.Outside.L_meta_4889

theorem PEqualNP.Outside.L_meta_4889 :
    let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop :=
      fun (x1 x2 : Fin (13 : ℕ)) => (↑x1 + ↑x2) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)];
    have x2 : (Fin (26 : ℕ) → Bool) → Prop :=
      fun (x2 : Fin (26 : ℕ) → Bool) =>
        ∃ (x3 : Fin (13 : ℕ)) (x4 : Fin (13 : ℕ)),
          x1 x3 x4 ∧ x2 (Fin.castAdd (13 : ℕ) x3) = Bool.true ∧ x2 (Fin.natAdd (13 : ℕ) x4) = Bool.true;
    have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool :=
      fun (x3 x4 : Finset (Fin (13 : ℕ))) (x5 : Fin (26 : ℕ)) =>
        if ↑x5 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x3)
        else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x5 ∈ x4);
    have x4 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) :=
      fun (x4 : Finset (Fin (13 : ℕ))) => {x5 : Fin (13 : ℕ) | ∀ x6 ∈ x4, ¬x1 x6 x5};
    (∀ (x5 x6 : Fin (13 : ℕ)), x1 x5 x6 → Minimal x2 (x3 {x5} {x6})) ∧
    ∀ (x5 : Finset (Fin (13 : ℕ))), x5.card ≤ (3 : ℕ) →
      Maximal (fun (x7 : Fin (26 : ℕ) → Bool) => ¬x2 x7) (x3 x5 (x4 x5)) ∧
      Maximal (fun (x7 : Fin (26 : ℕ) → Bool) => ¬x2 x7) (x3 (x4 x5) x5) :=
  ⟨PEqualNP.Outside.L_meta_4889.part1,
   fun S hS => ⟨PEqualNP.Outside.L_meta_4889.part2_left S hS,
                PEqualNP.Outside.L_meta_4889.part2_right S hS⟩⟩
