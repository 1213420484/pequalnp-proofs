import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4891

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def toGate (t : Bool × Fin 89 × Fin 89) : Gate :=
  { op := bif t.1 then GateOp.and else GateOp.or
    inputs := [↑t.2.1, ↑t.2.2] }

lemma toGate_eval (w : List Bool) (t : Bool × Fin 89 × Fin 89) :
    (toGate t).op.eval ((toGate t).inputs.map fun i => w.getD i false) =
      (bif t.1 then w.getD (↑t.2.1) false && w.getD (↑t.2.2) false
       else w.getD (↑t.2.1) false || w.getD (↑t.2.2) false) := by
  cases t with
  | mk b pq =>
    cases b <;> simp [toGate, GateOp.eval]

lemma foldl_toGate (init : List Bool) (L : List (Bool × Fin 89 × Fin 89)) :
    (L.map toGate).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) init =
      L.foldl
        (fun w t => w ++ [bif t.1 then w.getD (↑t.2.1) false && w.getD (↑t.2.2) false
                          else w.getD (↑t.2.1) false || w.getD (↑t.2.2) false]) init := by
  rw [List.foldl_map]
  congr 1
  funext w t
  rw [toGate_eval]

end PEqualNP.Outside.L_meta_4891

theorem PEqualNP.Outside.L_meta_4891 :
    ∀ (x1 : Fin (63 : ℕ) → Bool) (x2 x3 : Fin (63 : ℕ) → Fin (89 : ℕ)),
      (∀ (x4 : Fin (63 : ℕ)), ↑(x2 x4) < (26 : ℕ) + ↑x4 ∧ ↑(x3 x4) < (26 : ℕ) + ↑x4 ∧ x2 x4 ≤ x3 x4) →
      ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.Monotone2 x5 ∧
        x5.size = (63 : ℕ) ∧
        ∀ (x6 : Fin (26 : ℕ) → Bool),
          x5.eval (List.ofFn x6) =
            (fun (x7 : Fin (26 : ℕ) → Bool) =>
              (List.foldl
                (fun (x8 : List Bool) (x9 : Bool × Fin (89 : ℕ) × Fin (89 : ℕ)) =>
                  x8 ++ [bif x9.1 then x8.getD (↑x9.2.1) Bool.false && x8.getD (↑x9.2.2) Bool.false
                         else x8.getD (↑x9.2.1) Bool.false || x8.getD (↑x9.2.2) Bool.false])
                (List.ofFn x7)
                (List.ofFn fun (x8 : Fin (63 : ℕ)) => (x1 x8, x2 x8, x3 x8))).getD (88 : ℕ) Bool.false) x6 := by
  intro x1 x2 x3 _
  let L : List (Bool × Fin 89 × Fin 89) := List.ofFn fun i : Fin 63 => (x1 i, x2 i, x3 i)
  refine ⟨{ gates := L.map PEqualNP.Outside.L_meta_4891.toGate, output := 88 }, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_map.mp hg with ⟨t, _, rfl⟩
    cases t.1 <;> simp [PEqualNP.Outside.L_meta_4891.toGate]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size, L]
  · intro x6
    simp only [PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires, L]
    rw [PEqualNP.Outside.L_meta_4891.foldl_toGate]
