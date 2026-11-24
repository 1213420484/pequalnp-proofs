import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Count
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Push
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4367

open PEqualNP.CircuitLowerBounds

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

theorem keepInput (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem maskAgreement (gs : List Gate) (x y : List Bool) (bad : Finset ℕ)
    (hlen : x.length = y.length)
    (hin : ∀ i, i ∉ bad → x.getD i false = y.getD i false)
    (hmask : ∀ g ∈ gs, (∃ i ∈ g.inputs, i ∈ bad) →
      (∀ i ∈ g.inputs, i < x.length) ∧
      g.op.eval (g.inputs.map fun i => x.getD i false) =
        g.op.eval (g.inputs.map fun i => y.getD i false)) :
    ∀ i, i ∉ bad → (gs.foldl step x).getD i false = (gs.foldl step y).getD i false := by
  induction gs using List.reverseRecOn with
  | nil => exact hin
  | append_singleton gs g ih =>
    have eqPrev : ∀ i, i ∉ bad →
        (gs.foldl step x).getD i false = (gs.foldl step y).getD i false :=
      ih (fun h hh => hmask h (List.mem_append_left _ hh))
    let w := gs.foldl step x
    let z := gs.foldl step y
    have hlen' : w.length = z.length := by simp [w, z, foldl_length, hlen]
    have heval : g.op.eval (g.inputs.map fun i => w.getD i false) =
        g.op.eval (g.inputs.map fun i => z.getD i false) := by
      by_cases hhit : ∃ i ∈ g.inputs, i ∈ bad
      · obtain ⟨hsmall, hsame⟩ := hmask g (by simp) hhit
        have h1 : g.inputs.map (fun i => w.getD i false) =
            g.inputs.map (fun i => x.getD i false) :=
          List.map_congr_left fun i hi => keepInput gs x i (hsmall i hi)
        have h2 : g.inputs.map (fun i => z.getD i false) =
            g.inputs.map (fun i => y.getD i false) :=
          List.map_congr_left fun i hi => keepInput gs y i (hlen ▸ hsmall i hi)
        rw [h1, h2]
        exact hsame
      · congr 1
        apply List.map_congr_left
        intro i hi
        exact eqPrev i (fun hb => hhit ⟨i, hi, hb⟩)
    intro i hi
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    change (step w g).getD i false = (step z g).getD i false
    by_cases hiw : i < w.length
    · have hiz : i < z.length := hlen' ▸ hiw
      simp only [step, List.getD_eq_getElem?_getD,
        List.getElem?_append_left hiw, List.getElem?_append_left hiz]
      exact eqPrev i hi
    · have hw : w.length ≤ i := Nat.le_of_not_lt hiw
      have hz : z.length ≤ i := hlen' ▸ hw
      simp only [List.getD_eq_getElem?_getD] at heval
      simp only [step, List.getD_eq_getElem?_getD,
        List.getElem?_append_right hw, List.getElem?_append_right hz, hlen', heval]

theorem unique_reader {gs : List Gate} {out v : ℕ} {g : Gate}
    (hg : g ∈ gs) (hv : v ∈ g.inputs)
    (hlt : List.count v (out :: gs.flatMap Gate.inputs) < 2) :
    out ≠ v ∧ g.inputs.count v = 1 ∧ ∀ h ∈ gs, v ∈ h.inputs → h = g := by
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hg
  have hflat : (l₁ ++ g :: l₂).flatMap Gate.inputs =
      l₁.flatMap Gate.inputs ++ g.inputs ++ l₂.flatMap Gate.inputs := by
    simp [List.flatMap_append, List.flatMap_cons, List.append_assoc]
  have hcnt : List.count v (out :: (l₁ ++ g :: l₂).flatMap Gate.inputs) =
      (l₁.flatMap Gate.inputs).count v + g.inputs.count v + (l₂.flatMap Gate.inputs).count v +
        (if out == v then 1 else 0) := by
    rw [List.count_cons, hflat, List.count_append, List.count_append]
  have hpos : 1 ≤ g.inputs.count v := List.count_pos_iff.mpr hv
  rw [hcnt] at hlt
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    subst heq
    simp at hlt
    omega
  · omega
  · intro h hh hvh
    have h1 : (l₁.flatMap Gate.inputs).count v = 0 := by omega
    have h2 : (l₂.flatMap Gate.inputs).count v = 0 := by omega
    simp only [List.mem_append, List.mem_cons] at hh
    rcases hh with hm1 | rfl | hm2
    · exfalso
      have hmem : v ∈ l₁.flatMap Gate.inputs := List.mem_flatMap.mpr ⟨h, hm1, hvh⟩
      exact List.count_eq_zero.mp h1 hmem
    · rfl
    · exfalso
      have hmem : v ∈ l₂.flatMap Gate.inputs := List.mem_flatMap.mpr ⟨h, hm2, hvh⟩
      exact List.count_eq_zero.mp h2 hmem

def P9 (x : Fin 9 → Bool) : Bool :=
  [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ),
   (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun e =>
    x (Fin.ofNat 9 (e / 10)) && x (Fin.ofNat 9 (e % 10))

def tape (x : Fin 9 → Bool) : List Bool :=
  List.ofFn x ++ [x 0 || x 3]

def row (m : ℕ) : Fin 9 → Bool :=
  fun i => m.testBit i.val

def tableAnd : List ℕ :=
  [0, 40, 10, 0, 10, 10, 10, 10, 10, 0,
   4, 0, 1, 1, 1, 1, 1, 1, 1, 4,
   2, 8, 0, 2, 2, 2, 2, 2, 2, 2,
   0, 5, 257, 0, 5, 5, 5, 5, 5, 0,
   8, 1, 1, 1, 0, 1, 1, 1, 1, 0,
   128, 1, 1, 1, 1, 0, 1, 1, 1, 128,
   2, 256, 2, 2, 2, 2, 0, 2, 2, 2,
   4, 4, 32, 4, 4, 4, 4, 0, 4, 4,
   8, 8, 8, 32, 8, 8, 8, 8, 0, 32]

def tableOr : List ℕ :=
  [0, 10, 0, 10, 0, 40, 104, 138, 0, 10,
   1, 0, 4, 9, 20, 36, 64, 129, 257, 1,
   9, 2, 0, 8, 18, 34, 72, 128, 258, 8,
   5, 0, 5, 0, 0, 0, 69, 385, 257, 5,
   1, 10, 5, 8, 0, 40, 65, 129, 257, 1,
   1, 130, 5, 9, 144, 0, 65, 128, 256, 1,
   257, 2, 260, 10, 18, 34, 0, 130, 256, 10,
   5, 34, 4, 40, 20, 32, 68, 0, 260, 5,
   9, 10, 36, 8, 48, 32, 64, 136, 0, 8]

theorem checkAnd : ∀ (a : Fin 9) (b : Fin 10),
    a.val ≠ b.val → 10 * a.val + b.val ∉ ([3, 9, 30, 39, 49] : List ℕ) →
    let m := tableAnd.getD (10 * a.val + b.val) 0
    let m2 := m ||| (1 <<< a.val)
    P9 (row m) ≠ P9 (row m2) ∧
    (∀ j : Fin 10, j.val ≠ a.val → (tape (row m)).getD j.val false = (tape (row m2)).getD j.val false) ∧
    (tape (row m)).getD b.val false = false := by
  decide +kernel

theorem checkOr : ∀ (a : Fin 9) (b : Fin 10),
    a.val ≠ b.val → 10 * a.val + b.val ∉ ([2, 4, 8, 31, 34, 35] : List ℕ) →
    let m := tableOr.getD (10 * a.val + b.val) 0
    let m2 := m ||| (1 <<< a.val)
    P9 (row m) ≠ P9 (row m2) ∧
    (∀ j : Fin 10, j.val ≠ a.val → (tape (row m)).getD j.val false = (tape (row m2)).getD j.val false) ∧
    (tape (row m)).getD b.val false = true := by
  decide +kernel

theorem checkPart2 :
    P9 (row 3) ≠ P9 (row 10) ∧
    (∀ j : Fin 10, j.val ≠ 0 → j.val ≠ 3 →
      (tape (row 3)).getD j.val false = (tape (row 10)).getD j.val false) ∧
    ((tape (row 3)).getD 0 false && (tape (row 3)).getD 3 false) =
      ((tape (row 10)).getD 0 false && (tape (row 10)).getD 3 false) := by
  decide +kernel

theorem tape_length (x : Fin 9 → Bool) : (tape x).length = 10 := by
  simp [tape]

theorem tape_agree_ext (x y : Fin 9 → Bool) (bad : Finset ℕ)
    (h10 : ∀ j : Fin 10, j.val ∉ bad → (tape x).getD j.val false = (tape y).getD j.val false) :
    ∀ i, i ∉ bad → (tape x).getD i false = (tape y).getD i false := by
  intro i hi
  by_cases hlt : i < 10
  · exact h10 ⟨i, hlt⟩ hi
  · rw [List.getD_eq_default _ _ (by rw [tape_length]; omega),
        List.getD_eq_default _ _ (by rw [tape_length]; omega)]

theorem part1 (C : Circuit) (hC : ∀ x : Fin 9 → Bool, C.eval (tape x) = P9 x)
    (g : Gate) (hg : g ∈ C.gates) (a : Fin 9) (b : Fin 10)
    (hins : g.inputs = [a.val, b.val] ∨ g.inputs = [b.val, a.val])
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hnot : 10 * a.val + b.val ∉
      if g.op.eval [] = true then ([3, 9, 30, 39, 49] : List ℕ) else [2, 4, 8, 31, 34, 35]) :
    2 ≤ List.count a.val (C.output :: C.gates.flatMap Gate.inputs) := by
  by_contra hlt
  have hlt2 : List.count a.val (C.output :: C.gates.flatMap Gate.inputs) < 2 := by omega
  have ha_mem : a.val ∈ g.inputs := by rcases hins with h | h <;> simp [h]
  obtain ⟨hout, hgcnt, huniq⟩ := unique_reader hg ha_mem hlt2
  have hab : a.val ≠ b.val := by
    intro heq
    have : g.inputs = [a.val, a.val] := by
      rcases hins with h | h <;> simp [h, heq]
    rw [this] at hgcnt
    simp at hgcnt
  have hsmall : ∀ i ∈ g.inputs, i < (tape (row 0)).length := by
    intro i hi
    rw [tape_length]
    rcases hins with h | h <;> rw [h] at hi <;> simp at hi <;> rcases hi with rfl | rfl <;> omega
  rcases hop with hop | hop
  · have hnot' : 10 * a.val + b.val ∉ ([3, 9, 30, 39, 49] : List ℕ) := by
      simpa [hop, GateOp.eval] using hnot
    obtain ⟨hdiff, hag, hbf⟩ := checkAnd a b hab hnot'
    let m := tableAnd.getD (10 * a.val + b.val) 0
    let m2 := m ||| (1 <<< a.val)
    have hbf1 : (tape (row m)).getD b.val false = false := hbf
    have hbf2 : (tape (row m2)).getD b.val false = false := by
      rw [← hag b (Ne.symm hab), hbf1]
    have hsame : g.op.eval (g.inputs.map fun i => (tape (row m)).getD i false) =
        g.op.eval (g.inputs.map fun i => (tape (row m2)).getD i false) := by
      rcases hins with h | h <;> rw [hop, h] <;>
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
          hbf1, hbf2, Bool.and_false, Bool.false_and, Bool.and_true]
    have heq := maskAgreement C.gates (tape (row m)) (tape (row m2)) {a.val}
      (by simp [tape_length])
      (tape_agree_ext _ _ _ (fun j hj => hag j (by simpa using hj)))
      (fun h hh hhit => by
        obtain ⟨i, hi, hib⟩ := hhit
        have hia : i = a.val := by simpa using hib
        have hhg : h = g := huniq h hh (hia ▸ hi)
        subst hhg
        exact ⟨by simpa [tape_length] using hsmall, hsame⟩)
      C.output (by simpa using hout)
    change C.eval (tape (row m)) = C.eval (tape (row m2)) at heq
    rw [hC, hC] at heq
    exact hdiff heq
  · have hnot' : 10 * a.val + b.val ∉ ([2, 4, 8, 31, 34, 35] : List ℕ) := by
      simpa [hop, GateOp.eval] using hnot
    obtain ⟨hdiff, hag, hbt⟩ := checkOr a b hab hnot'
    let m := tableOr.getD (10 * a.val + b.val) 0
    let m2 := m ||| (1 <<< a.val)
    have hbt1 : (tape (row m)).getD b.val false = true := hbt
    have hbt2 : (tape (row m2)).getD b.val false = true := by
      rw [← hag b (Ne.symm hab), hbt1]
    have hsame : g.op.eval (g.inputs.map fun i => (tape (row m)).getD i false) =
        g.op.eval (g.inputs.map fun i => (tape (row m2)).getD i false) := by
      rcases hins with h | h <;> rw [hop, h] <;>
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
          hbt1, hbt2, Bool.or_true, Bool.true_or, Bool.or_false]
    have heq := maskAgreement C.gates (tape (row m)) (tape (row m2)) {a.val}
      (by simp [tape_length])
      (tape_agree_ext _ _ _ (fun j hj => hag j (by simpa using hj)))
      (fun h hh hhit => by
        obtain ⟨i, hi, hib⟩ := hhit
        have hia : i = a.val := by simpa using hib
        have hhg : h = g := huniq h hh (hia ▸ hi)
        subst hhg
        exact ⟨by simpa [tape_length] using hsmall, hsame⟩)
      C.output (by simpa using hout)
    change C.eval (tape (row m)) = C.eval (tape (row m2)) at heq
    rw [hC, hC] at heq
    exact hdiff heq

theorem part2 (C : Circuit) (hC : ∀ x : Fin 9 → Bool, C.eval (tape x) = P9 x)
    (hg : ({ op := GateOp.and, inputs := [0, 3] } : Gate) ∈ C.gates ∨
          ({ op := GateOp.and, inputs := [3, 0] } : Gate) ∈ C.gates) :
    2 ≤ List.count 0 (C.output :: C.gates.flatMap Gate.inputs) ∨
    2 ≤ List.count 3 (C.output :: C.gates.flatMap Gate.inputs) := by
  by_contra hboth
  push Not at hboth
  obtain ⟨h0, h3⟩ := hboth
  obtain ⟨g, hgm, hg_op, hg_in⟩ :
      ∃ g ∈ C.gates, g.op = GateOp.and ∧ (g.inputs = [0, 3] ∨ g.inputs = [3, 0]) := by
    rcases hg with h | h
    · exact ⟨_, h, rfl, Or.inl rfl⟩
    · exact ⟨_, h, rfl, Or.inr rfl⟩
  have h0m : 0 ∈ g.inputs := by rcases hg_in with h | h <;> simp [h]
  have h3m : 3 ∈ g.inputs := by rcases hg_in with h | h <;> simp [h]
  obtain ⟨hout0, _, huniq0⟩ := unique_reader hgm h0m h0
  obtain ⟨hout3, _, huniq3⟩ := unique_reader hgm h3m h3
  obtain ⟨hdiff, hag, hand⟩ := checkPart2
  have hsame : g.op.eval (g.inputs.map fun i => (tape (row 3)).getD i false) =
      g.op.eval (g.inputs.map fun i => (tape (row 10)).getD i false) := by
    rcases hg_in with h | h
    · simpa [hg_op, h, GateOp.eval] using hand
    · simpa [hg_op, h, GateOp.eval, Bool.and_comm] using hand
  have heq := maskAgreement C.gates (tape (row 3)) (tape (row 10)) {0, 3}
    (by simp [tape_length])
    (tape_agree_ext _ _ _ (fun j hj => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
      exact hag j hj.1 hj.2))
    (fun h hh hhit => by
      obtain ⟨i, hi, hib⟩ := hhit
      simp only [Finset.mem_insert, Finset.mem_singleton] at hib
      have hhg : h = g := by
        rcases hib with rfl | rfl
        · exact huniq0 h hh hi
        · exact huniq3 h hh hi
      subst hhg
      refine ⟨?_, hsame⟩
      intro k hk
      rw [tape_length]
      rcases hg_in with h | h <;> rw [h] at hk <;> simp at hk <;> rcases hk with rfl | rfl <;> omega)
    C.output (by simp [hout0, hout3])
  change C.eval (tape (row 3)) = C.eval (tape (row 10)) at heq
  rw [hC, hC] at heq
  exact hdiff heq

end PEqualNP.Outside.L_meta_4367

theorem PEqualNP.Outside.L_meta_4367 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [(1 : ℕ), (12 : ℕ), (23 : ℕ), (34 : ℕ), (40 : ℕ), (5 : ℕ), (16 : ℕ), (27 : ℕ), (38 : ℕ), (57 : ℕ), (68 : ℕ), (85 : ℕ)].any fun (x2 : ℕ) => x1 (Fin.ofNat (9 : ℕ) (x2 / (10 : ℕ))) && x1 (Fin.ofNat (9 : ℕ) (x2 % (10 : ℕ))); have x2 : (Fin (9 : ℕ) → Bool) → List Bool := fun (x2 : Fin (9 : ℕ) → Bool) => List.ofFn x2 ++ [x2 (0 : Fin (9 : ℕ)) || x2 (3 : Fin (9 : ℕ))]; have x3 : PEqualNP.CircuitLowerBounds.GateOp → List ℕ := fun (x3 : PEqualNP.CircuitLowerBounds.GateOp) => if x3.eval [] = Bool.true then [(3 : ℕ), (9 : ℕ), (30 : ℕ), (39 : ℕ), (49 : ℕ)] else [(2 : ℕ), (4 : ℕ), (8 : ℕ), (31 : ℕ), (34 : ℕ), (35 : ℕ)]; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 : Fin (9 : ℕ) → Bool), x4.eval (x2 x5) = x1 x5) → (∀ x6 ∈ x4.gates, ∀ (x8 : Fin (9 : ℕ)) (x9 : Fin (10 : ℕ)), x6.inputs = [↑x8, ↑x9] ∨ x6.inputs = [↑x9, ↑x8] → x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.or → (10 : ℕ) * ↑x8 + ↑x9 ∉ x3 x6.op → (2 : ℕ) ≤ List.count (↑x8) (x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates)) ∧ ({ op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [(0 : ℕ), (3 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∈ x4.gates ∨ { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [(3 : ℕ), (0 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∈ x4.gates → (2 : ℕ) ≤ List.count (0 : ℕ) (x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates) ∨ (2 : ℕ) ≤ List.count (3 : ℕ) (x4.output :: List.flatMap PEqualNP.CircuitLowerBounds.Gate.inputs x4.gates)) := by
  dsimp only
  intro C hC
  exact ⟨fun g hg a b hins hop hnot => PEqualNP.Outside.L_meta_4367.part1 C hC g hg a b hins hop hnot,
         fun hg => PEqualNP.Outside.L_meta_4367.part2 C hC hg⟩
