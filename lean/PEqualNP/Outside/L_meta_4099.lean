import Mathlib.Data.List.OfFn
import Mathlib.Logic.Relation
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4099

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

private def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w

private theorem wiresFrom_append (gs1 gs2 : List Gate) (w : List Bool) :
    wiresFrom (gs1 ++ gs2) w = wiresFrom gs2 (wiresFrom gs1 w) := by
  simp [wiresFrom, List.foldl_append]

private theorem wiresFrom_ext (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    let v := g.op.eval (g.inputs.map fun i => w.getD i false)
    obtain ⟨t, ht, hl⟩ := ih (w ++ [v])
    refine ⟨v :: t, ?_, by simp [hl]⟩
    have hstep : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [v]) := rfl
    rw [hstep, ht]
    simp

private theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_ext gs w
  rw [ht, List.length_append, hl]

private theorem getD_wiresFrom_lt (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_ext gs w
  rw [ht, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left h,
    List.getD_eq_getElem _ _ h]

private theorem getD_wiresFrom_take (gs : List Gate) (w : List Bool) (k i : ℕ)
    (hk : k ≤ gs.length) (hi : i < w.length + k) :
    (wiresFrom (gs.take k) w).getD i false = (wiresFrom gs w).getD i false := by
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left hk]
  have hsplit : gs = gs.take k ++ gs.drop k := (List.take_append_drop k gs).symm
  conv_rhs => rw [hsplit, wiresFrom_append]
  exact (getD_wiresFrom_lt (gs.drop k) (wiresFrom (gs.take k) w) i (by omega)).symm

private theorem getD_wiresFrom_gate (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < gs.length)
    (hrb : ∀ i ∈ gs[k].inputs, i < w.length + k) :
    (wiresFrom gs w).getD (w.length + k) false =
      gs[k].op.eval (gs[k].inputs.map fun i => (wiresFrom gs w).getD i false) := by
  have hsplit : gs = gs.take k ++ gs[k] :: gs.drop (k + 1) := by
    have h1 := (List.take_append_drop k gs).symm
    rw [List.drop_eq_getElem_cons hk] at h1
    exact h1
  have hlen : (wiresFrom (gs.take k) w).length = w.length + k := by
    rw [length_wiresFrom, List.length_take, min_eq_left (Nat.le_of_lt hk)]
  let prev := wiresFrom (gs.take k) w
  let v := gs[k].op.eval (gs[k].inputs.map fun i => prev.getD i false)
  have heq : wiresFrom gs w = wiresFrom (gs.drop (k + 1)) (prev ++ [v]) := by
    conv_lhs => rw [hsplit, wiresFrom_append]
    rfl
  rw [heq, getD_wiresFrom_lt _ _ _ (by simp [prev, hlen])]
  rw [List.getD_eq_getElem _ _ (by simp [prev, hlen]),
    List.getElem_append_right (by simp [prev, hlen])]
  have hsub : w.length + k - prev.length = 0 := by simp [prev, hlen]
  simp only [hsub, List.getElem_singleton]
  dsimp only [v, prev]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [getD_wiresFrom_take gs w k i (Nat.le_of_lt hk) (hrb i hi), heq]

private abbrev wireVal (C : Circuit) (x : Fin 26 → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private abbrev orStep (C : Circuit) (u v : ℕ) : Prop :=
  ∃ g : ℕ, v = 26 + g ∧ (gateAt C g).op = GateOp.or ∧ u ∈ (gateAt C g).inputs

private abbrev andReach (C : Circuit) (x : Fin 26 → Bool) (g w : ℕ) : Prop :=
  (gateAt C g).op = GateOp.and ∧ wireVal C x (26 + g) = true ∧ Relation.ReflTransGen (orStep C) (26 + g) w

private abbrev pairInput (a b : Fin 26) : Fin 26 → Bool :=
  fun i => Decidable.decide (i = a ∨ i = b)

private theorem wireVal_input (C : Circuit) (x : Fin 26 → Bool) (w : ℕ) (hw : w < 26) :
    wireVal C x w = x ⟨w, hw⟩ := by
  change (wiresFrom C.gates (List.ofFn x)).getD w false = x ⟨w, hw⟩
  rw [getD_wiresFrom_lt _ _ _ (by simpa using hw)]
  rw [List.getD_eq_getElem _ _ (by simpa using hw), List.getElem_ofFn]

private theorem main_proof (C : Circuit) (a b : Fin 26) (w : ℕ)
    (hao : PEqualNP.TopForm.IsAO2 26 C)
    (hpair : wireVal C (pairInput a b) w = true)
    (ha : wireVal C (fun i => Decidable.decide (i = a)) w = false)
    (hb : wireVal C (fun i => Decidable.decide (i = b)) w = false) :
    ∃ g : ℕ, andReach C (pairInput a b) g w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hlt26 : w < 26
    · rw [wireVal_input C _ w hlt26] at hpair ha hb
      simp only [pairInput, decide_eq_true_eq] at hpair
      rcases hpair with heq | heq
      · simp [heq] at ha
      · simp [heq] at hb
    · by_cases hltN : w < 26 + C.gates.length
      · let k := w - 26
        have hk : k < C.gates.length := by omega
        have hw : w = 26 + k := by omega
        have hgat : gateAt C k = C.gates[k] := by
          unfold gateAt
          exact List.getD_eq_getElem _ _ hk
        have hrb : ∀ i ∈ C.gates[k].inputs, i < (List.ofFn (pairInput a b)).length + k := by
          intro i hi
          rw [List.length_ofFn]
          exact hao.2.1 k hk i (hgat.symm ▸ hi)
        have hrbA : ∀ i ∈ C.gates[k].inputs, i < (List.ofFn (fun i : Fin 26 => Decidable.decide (i = a))).length + k := by
          intro i hi; rw [List.length_ofFn]; exact hao.2.1 k hk i (hgat.symm ▸ hi)
        have hrbB : ∀ i ∈ C.gates[k].inputs, i < (List.ofFn (fun i : Fin 26 => Decidable.decide (i = b))).length + k := by
          intro i hi; rw [List.length_ofFn]; exact hao.2.1 k hk i (hgat.symm ▸ hi)
        have hop : (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
          rw [hgat]
          exact hao.1 _ (List.getElem_mem hk)
        rcases hop with hand | hor
        · exact ⟨k, hand, hw ▸ hpair, hw ▸ Relation.ReflTransGen.refl⟩
        · have hevP : wireVal C (pairInput a b) w =
              C.gates[k].op.eval (C.gates[k].inputs.map fun i => wireVal C (pairInput a b) i) := by
            rw [hw]
            exact getD_wiresFrom_gate C.gates (List.ofFn (pairInput a b)) k hk hrb
          have hevA : wireVal C (fun i => Decidable.decide (i = a)) w =
              C.gates[k].op.eval (C.gates[k].inputs.map fun i => wireVal C (fun i => Decidable.decide (i = a)) i) := by
            rw [hw]
            exact getD_wiresFrom_gate C.gates (List.ofFn _) k hk hrbA
          have hevB : wireVal C (fun i => Decidable.decide (i = b)) w =
              C.gates[k].op.eval (C.gates[k].inputs.map fun i => wireVal C (fun i => Decidable.decide (i = b)) i) := by
            rw [hw]
            exact getD_wiresFrom_gate C.gates (List.ofFn _) k hk hrbB
          have hor' : C.gates[k].op = GateOp.or := hgat ▸ hor
          rw [hevP, hor'] at hpair
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq, exists_exists_and_eq_and] at hpair
          obtain ⟨u, huMem, huVal⟩ := hpair
          have huLt : u < w := by
            have := hao.2.1 k hk u (hgat.symm ▸ huMem)
            omega
          have huA : wireVal C (fun i => Decidable.decide (i = a)) u = false := by
            by_contra hne
            have ht : wireVal C (fun i => Decidable.decide (i = a)) u = true := by
              cases h : wireVal C (fun i => Decidable.decide (i = a)) u <;> simp_all
            rw [hevA, hor'] at ha
            have haTrue : GateOp.or.eval (C.gates[k].inputs.map fun i =>
                wireVal C (fun i => Decidable.decide (i = a)) i) = true := by
              simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
              exact ⟨true, ⟨u, huMem, ht⟩, rfl⟩
            rw [haTrue] at ha
            exact Bool.noConfusion ha
          have huB : wireVal C (fun i => Decidable.decide (i = b)) u = false := by
            by_contra hne
            have ht : wireVal C (fun i => Decidable.decide (i = b)) u = true := by
              cases h : wireVal C (fun i => Decidable.decide (i = b)) u <;> simp_all
            rw [hevB, hor'] at hb
            have hbTrue : GateOp.or.eval (C.gates[k].inputs.map fun i =>
                wireVal C (fun i => Decidable.decide (i = b)) i) = true := by
              simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
              exact ⟨true, ⟨u, huMem, ht⟩, rfl⟩
            rw [hbTrue] at hb
            exact Bool.noConfusion hb
          obtain ⟨g, hgAnd, hgVal, hgPath⟩ := ih u huLt huVal huA huB
          refine ⟨g, hgAnd, hgVal, Relation.ReflTransGen.tail hgPath ?_⟩
          exact ⟨k, hw, hor, hgat.symm ▸ huMem⟩
      · have hdef : wireVal C (pairInput a b) w = false := by
          change (wiresFrom C.gates (List.ofFn (pairInput a b))).getD w false = false
          apply List.getD_eq_default
          rw [length_wiresFrom, List.length_ofFn]
          omega
        rw [hdef] at hpair
        exact Bool.noConfusion hpair

end PEqualNP.Outside.L_meta_4099

theorem PEqualNP.Outside.L_meta_4099 : have x1 : PEqualNP.CircuitLowerBounds.Circuit → (Fin (26 : ℕ) → Bool) → ℕ → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (26 : ℕ) → Bool) (x3 : ℕ) => (x1.wires (List.ofFn x2)).getD x3 Bool.false; have x2 : PEqualNP.CircuitLowerBounds.Circuit → ℕ → ℕ → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 x4 : ℕ) => ∃ (x5 : ℕ), x4 = (26 : ℕ) + x5 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x5).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x5).inputs; have x3 : PEqualNP.CircuitLowerBounds.Circuit → (Fin (26 : ℕ) → Bool) → ℕ → ℕ → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 : Fin (26 : ℕ) → Bool) (x5 x6 : ℕ) => (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x1 x3 x4 ((26 : ℕ) + x5) = Bool.true ∧ Relation.ReflTransGen (x2 x3) ((26 : ℕ) + x5) x6; have x4 : Fin (26 : ℕ) → Fin (26 : ℕ) → Fin (26 : ℕ) → Bool := fun (x4 x5 x6 : Fin (26 : ℕ)) => Decidable.decide (x6 = x4 ∨ x6 = x5); ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : Fin (26 : ℕ)) (x8 : ℕ), PEqualNP.TopForm.IsAO2 (26 : ℕ) x5 → x1 x5 (x4 x6 x7) x8 = Bool.true → x1 x5 (fun (x11 : Fin (26 : ℕ)) => Decidable.decide (x11 = x6)) x8 = Bool.false → x1 x5 (fun (x12 : Fin (26 : ℕ)) => Decidable.decide (x12 = x7)) x8 = Bool.false → ∃ (x13 : ℕ), x3 x5 (x4 x6 x7) x13 x8 :=
  PEqualNP.Outside.L_meta_4099.main_proof
