import Mathlib.Data.List.OfFn
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4827

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [step]
    omega

def remapWire (σ : Fin 9 → Fin 9) (i : ℕ) : ℕ :=
  if h : i < 9 then (σ ⟨i, h⟩).val else i

def remapGate (σ : Fin 9 → Fin 9) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (remapWire σ)⟩

theorem remapWire_lt9 (σ : Fin 9 → Fin 9) (i : ℕ) (hi : i < 9) : remapWire σ i < 9 := by
  unfold remapWire
  simp [hi]

theorem remapWire_ge9 (σ : Fin 9 → Fin 9) (i : ℕ) (hi : 9 ≤ i) : remapWire σ i = i := by
  unfold remapWire
  have h : ¬ i < 9 := by omega
  simp [h]

theorem remapWire_invol (σ : Fin 9 → Fin 9) (hσ : ∀ a, σ (σ a) = a) (i : ℕ) :
    remapWire σ (remapWire σ i) = i := by
  by_cases hi : i < 9
  · have h1 : remapWire σ i = (σ ⟨i, hi⟩).val := by unfold remapWire; simp [hi]
    rw [h1]
    have hlt : (σ ⟨i, hi⟩).val < 9 := (σ ⟨i, hi⟩).isLt
    unfold remapWire
    simp [hlt, hσ]
  · have hge : 9 ≤ i := Nat.le_of_not_lt hi
    rw [remapWire_ge9 σ i hge, remapWire_ge9 σ i hge]

theorem remap_foldl (σ : Fin 9 → Fin 9) (gs : List Gate) (u v : List Bool)
    (hu : u.length = 9) (hv : v.length = 9)
    (hinit : ∀ i, u.getD (remapWire σ i) false = v.getD i false) :
    ∀ i, ((gs.map (remapGate σ)).foldl step u).getD (remapWire σ i) false =
         (gs.foldl step v).getD i false := by
  induction gs using List.reverseRecOn with
  | nil => exact hinit
  | append_singleton gs g ih =>
    let wu := (gs.map (remapGate σ)).foldl step u
    let wv := gs.foldl step v
    have hlu : wu.length = 9 + gs.length := by
      simp [wu, foldl_length, hu]
    have hlv : wv.length = 9 + gs.length := by
      simp [wv, foldl_length, hv]
    have hev : (remapGate σ g).op.eval ((remapGate σ g).inputs.map fun i => wu.getD i false) =
        g.op.eval (g.inputs.map fun i => wv.getD i false) := by
      simp only [remapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro k _
      exact ih k
    intro i
    simp only [List.map_append, List.map_singleton, List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (step wu (remapGate σ g)).getD (remapWire σ i) false = (step wv g).getD i false
    by_cases hilt : i < 9 + gs.length
    · have hrlt : remapWire σ i < 9 + gs.length := by
        by_cases h9 : i < 9
        · exact Nat.lt_of_lt_of_le (remapWire_lt9 σ i h9) (by omega)
        · rw [remapWire_ge9 σ i (by omega)]; exact hilt
      simp only [step, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (hlu ▸ hrlt), List.getElem?_append_left (hlv ▸ hilt)]
      exact ih i
    · have hge : 9 + gs.length ≤ i := Nat.le_of_not_lt hilt
      have hr : remapWire σ i = i := remapWire_ge9 σ i (by omega)
      rw [hr]
      simp only [List.getD_eq_getElem?_getD] at hev
      simp only [step, List.getD_eq_getElem?_getD,
        List.getElem?_append_right (hlu ▸ hge), List.getElem?_append_right (hlv ▸ hge),
        hlu, hlv, hev]

theorem get_map_eq {α β : Type} (f : α → β) (l : List α) (i : Fin (l.map f).length)
    (j : Fin l.length) (h : i.val = j.val) :
    (l.map f).get i = f (l.get j) := by
  rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_map]
  simp [h]

end PEqualNP.Outside.L_meta_4827

theorem PEqualNP.Outside.L_meta_4827 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (9 : ℕ) → Fin (9 : ℕ))
      (x3 : Fin (9 : ℕ)) (x4 : Fin x1.size),
      (∀ (x5 : Fin (9 : ℕ)), x2 (x2 x5) = x5) →
      PEqualNP.MetaComplexity.FanInTwo x1 →
      (x1.gates.get x4).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or →
      (∀ (x8 : Fin x1.size), ↑x3 ∈ (x1.gates.get x8).inputs ↔ x8 = x4) →
      ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit) (x10 : Fin x9.size),
        PEqualNP.MetaComplexity.FanInTwo x9 ∧
        x9.size = x1.size ∧
        (∀ (x11 : Fin (9 : ℕ) → Bool),
          PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x9 x11 =
            PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 fun (x12 : Fin (9 : ℕ)) => x11 (x2 x12)) ∧
        (x9.gates.get x10).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or ∧
        ∀ (x11 : Fin x9.size), ↑(x2 x3) ∈ (x9.gates.get x11).inputs ↔ x11 = x10 := by
  intro C σ v k hσ hfan hne huniq
  let D : PEqualNP.CircuitLowerBounds.Circuit :=
    { gates := C.gates.map (PEqualNP.Outside.L_meta_4827.remapGate σ)
      output := PEqualNP.Outside.L_meta_4827.remapWire σ C.output }
  have hsz : D.size = C.size := by
    simp [D, PEqualNP.CircuitLowerBounds.Circuit.size]
  let k' : Fin D.size := ⟨k.val, by rw [hsz]; exact k.isLt⟩
  refine ⟨D, k', ?_, hsz, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_map.mp hg with ⟨g0, hg0, rfl⟩
    simpa [PEqualNP.Outside.L_meta_4827.remapGate] using hfan g0 hg0
  · intro x
    simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, D]
    apply PEqualNP.Outside.L_meta_4827.remap_foldl σ C.gates (List.ofFn x) (List.ofFn fun i => x (σ i))
    · simp
    · simp
    · intro i
      by_cases hi : i < 9
      · have hr : PEqualNP.Outside.L_meta_4827.remapWire σ i = (σ ⟨i, hi⟩).val := by
          unfold PEqualNP.Outside.L_meta_4827.remapWire; simp [hi]
        rw [hr, List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simp; omega),
            List.getElem_ofFn, List.getElem_ofFn]
      · have hge : 9 ≤ i := Nat.le_of_not_lt hi
        rw [PEqualNP.Outside.L_meta_4827.remapWire_ge9 σ i hge,
            List.getD_eq_default _ _ (by simp; omega),
            List.getD_eq_default _ _ (by simp; omega)]
  · have hget : D.gates.get k' = PEqualNP.Outside.L_meta_4827.remapGate σ (C.gates.get k) :=
      PEqualNP.Outside.L_meta_4827.get_map_eq _ C.gates k' k rfl
    rw [hget]
    exact hne
  · intro j
    let j0 : Fin C.size := ⟨j.val, by rw [← hsz]; exact j.isLt⟩
    have hget : D.gates.get j = PEqualNP.Outside.L_meta_4827.remapGate σ (C.gates.get j0) :=
      PEqualNP.Outside.L_meta_4827.get_map_eq _ C.gates j j0 rfl
    rw [hget]
    simp only [PEqualNP.Outside.L_meta_4827.remapGate, List.mem_map]
    constructor
    · rintro ⟨a, ha, hrem⟩
      have ha_eq : a = v.val := by
        have h1 := congrArg (PEqualNP.Outside.L_meta_4827.remapWire σ) hrem
        rw [PEqualNP.Outside.L_meta_4827.remapWire_invol σ hσ a] at h1
        have h2 : PEqualNP.Outside.L_meta_4827.remapWire σ (σ v).val = v.val := by
          unfold PEqualNP.Outside.L_meta_4827.remapWire
          simp [(σ v).isLt, hσ]
        rw [h2] at h1
        exact h1
      subst ha_eq
      have hj0 : j0 = k := (huniq j0).mp ha
      have hval : j0.val = k.val := congrArg Fin.val hj0
      exact Fin.ext hval
    · rintro rfl
      refine ⟨v.val, (huniq j0).mpr (Fin.ext rfl), ?_⟩
      unfold PEqualNP.Outside.L_meta_4827.remapWire
      simp [v.isLt]
