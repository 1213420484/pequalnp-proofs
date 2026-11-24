import Mathlib.Data.List.OfFn
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5276

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.HeptadCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wv (C : Circuit) (z : List Bool) (w : ℕ) : Bool :=
  (C.wires z).getD w false

lemma wires_eq_foldl (C : Circuit) (z : List Bool) :
    C.wires z = C.gates.foldl step z := rfl

lemma foldl_step_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons, ih, step, List.length_append, List.length_nil]
    omega

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (step w g).length := by simp only [step, List.length_append]; omega
    rw [ih (step w g) hlt, List.getD_eq_getElem _ _ hlt, List.getD_eq_getElem _ _ hi]
    simp only [step, List.getElem_append_left hi]

lemma wv_input (C : Circuit) (z : List Bool) (i : ℕ) (hi : i < z.length) :
    wv C z i = z.getD i false := by
  unfold wv
  rw [wires_eq_foldl]
  exact foldl_step_getD_lt C.gates z i hi

lemma wv_ge (C : Circuit) (z : List Bool) (w : ℕ) (hw : z.length + C.gates.length ≤ w) :
    wv C z w = false := by
  unfold wv
  rw [wires_eq_foldl]
  have hlen : (C.gates.foldl step z).length ≤ w := by rw [foldl_step_length]; omega
  rw [List.getD_eq_default _ _ hlen]

lemma wv_gate (C : Circuit) (hRB : ReadsBack 26 C) (z : List Bool) (hz : z.length = 26)
    (j : ℕ) (hj : j < C.gates.length) :
    wv C z (26 + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => wv C z i) := by
  unfold wv
  rw [wires_eq_foldl]
  have hsplit : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    have := List.take_append_drop j C.gates
    have hdrop : C.gates.drop j = C.gates[j] :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [← hdrop, this]
  let pref := (C.gates.take j).foldl step z
  have hplen : pref.length = 26 + j := by
    simp only [pref, foldl_step_length, hz, List.length_take]
    omega
  have hpref_get : ∀ i < 26 + j, (C.gates.foldl step z).getD i false = pref.getD i false := by
    intro i hi
    conv_lhs => rw [hsplit]
    rw [List.foldl_append]
    exact foldl_step_getD_lt _ pref i (by omega)
  have hgate_eq : gateAt C j = C.gates[j] := by
    simp only [gateAt, List.getD_eq_getElem _ _ hj]
  have hval : (C.gates.foldl step z).getD (26 + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i => pref.getD i false) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
    have hlt : 26 + j < (step pref C.gates[j]).length := by
      simp only [step, List.length_append, List.length_singleton, hplen]; omega
    rw [foldl_step_getD_lt _ (step pref C.gates[j]) (26 + j) hlt, List.getD_eq_getElem _ _ hlt]
    have hidx : 26 + j = pref.length := hplen.symm
    simp only [step, hidx, List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
  rw [hval, hgate_eq]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < 26 + j := hRB j hj i (hgate_eq ▸ hi)
  exact (hpref_get i hilt).symm

lemma gate_inputs_pair {C : Circuit} (hAO : IsAO2 26 C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [(gateAt C j).inputs.getD 0 0, (gateAt C j).inputs.getD 1 0] := by
  have hmem : gateAt C j ∈ C.gates := by
    simp only [gateAt, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 (gateAt C j) hmem
  match h : (gateAt C j).inputs with
  | [a, b] => simp
  | [] => simp [h] at hlen
  | [_] => simp [h] at hlen
  | _ :: _ :: _ :: _ => simp [h] at hlen

lemma gate_inputs_lt {C : Circuit} (hAO : IsAO2 26 C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs.getD 0 0 < 26 + j ∧ (gateAt C j).inputs.getD 1 0 < 26 + j := by
  have hpair := gate_inputs_pair hAO hj
  have h0 : (gateAt C j).inputs.getD 0 0 ∈ (gateAt C j).inputs := by rw [hpair]; simp
  have h1 : (gateAt C j).inputs.getD 1 0 ∈ (gateAt C j).inputs := by rw [hpair]; simp
  exact ⟨hAO.2.1 j hj _ h0, hAO.2.1 j hj _ h1⟩

def wireSets (C : Circuit) (w : ℕ) : Finset ℕ × Finset ℕ :=
  if w < 26 then ({w}, ∅)
  else if w - 26 < C.gates.length then
    let g := gateAt C (w - 26)
    match g.op with
    | GateOp.and => (∅, {w - 26})
    | GateOp.or =>
      let u := g.inputs.getD 0 0
      let v := g.inputs.getD 1 0
      if _hu : u < w then
        if _hv : v < w then
          let su := wireSets C u
          let sv := wireSets C v
          (su.1 ∪ sv.1, su.2 ∪ sv.2)
        else (∅, ∅)
      else (∅, ∅)
    | _ => (∅, ∅)
  else (∅, ∅)
termination_by w

lemma wireSets_and_eq (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) :
    wireSets C (26 + j) = (∅, {j}) := by
  rw [wireSets]
  have h1 : ¬ (26 + j < 26) := by omega
  have hsub : 26 + j - 26 = j := by omega
  simp only [h1, ↓reduceIte, hsub, hj, hop]

lemma wireSets_or_eq (C : Circuit) (hAO : IsAO2 26 C) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) :
    let u := (gateAt C j).inputs.getD 0 0
    let v := (gateAt C j).inputs.getD 1 0
    wireSets C (26 + j) =
      ((wireSets C u).1 ∪ (wireSets C v).1, (wireSets C u).2 ∪ (wireSets C v).2) := by
  dsimp only
  rw [wireSets]
  have h1 : ¬ (26 + j < 26) := by omega
  have hsub : 26 + j - 26 = j := by omega
  have hlt := gate_inputs_lt hAO hj
  simp only [h1, ↓reduceIte, hsub, hj, hop, hlt.1, hlt.2, ↓reduceDIte]

lemma wireSets_eval (C : Circuit) (hAO : IsAO2 26 C) (z : List Bool) (hz : z.length = 26) :
    ∀ w : ℕ,
      wv C z w = true ↔
        (∃ i ∈ (wireSets C w).1, z.getD i false = true) ∨
        (∃ j ∈ (wireSets C w).2, wv C z (26 + j) = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h1 : w < 26
    · have hws : wireSets C w = ({w}, ∅) := by rw [wireSets]; simp only [h1, ↓reduceIte]
      rw [hws, wv_input C z w (by omega)]
      simp
    · by_cases h2 : w - 26 < C.gates.length
      · let j := w - 26
        have hjlt : j < C.gates.length := h2
        have hwj : w = 26 + j := by omega
        have hmem : gateAt C j ∈ C.gates := by
          simp only [gateAt, List.getD_eq_getElem _ _ hjlt]; exact List.getElem_mem hjlt
        rcases hAO.1 (gateAt C j) hmem with hand | hor
        · rw [hwj, wireSets_and_eq C j hjlt hand]; simp
        · rw [hwj, wireSets_or_eq C hAO j hjlt hor, wv_gate C hAO.2.1 z hz j hjlt]
          have hpair := gate_inputs_pair hAO hjlt
          have hlt := gate_inputs_lt hAO hjlt
          let u := (gateAt C j).inputs.getD 0 0
          let v := (gateAt C j).inputs.getD 1 0
          have hev : (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => wv C z i) =
              (wv C z u || wv C z v) := by
            rw [hor, hpair]; simp [GateOp.eval, u, v]
          rw [hev, Bool.or_eq_true, ih u (by dsimp only [u]; omega), ih v (by dsimp only [v]; omega)]
          dsimp only [u, v]
          simp only [Finset.mem_union, or_and_right, exists_or]
          constructor
          · rintro ((h | h) | (h | h))
            · exact Or.inl (Or.inl h)
            · exact Or.inr (Or.inl h)
            · exact Or.inl (Or.inr h)
            · exact Or.inr (Or.inr h)
          · rintro ((h | h) | (h | h))
            · exact Or.inl (Or.inl h)
            · exact Or.inr (Or.inl h)
            · exact Or.inl (Or.inr h)
            · exact Or.inr (Or.inr h)
      · have hws : wireSets C w = (∅, ∅) := by rw [wireSets]; simp only [h1, h2, ↓reduceIte]
        rw [hws, wv_ge C z w (by omega)]
        simp

lemma wireSets_bare_lt (C : Circuit) (hAO : IsAO2 26 C) :
    ∀ w : ℕ, ∀ i ∈ (wireSets C w).1, i < 26 := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h1 : w < 26
    · rw [wireSets]; simp [h1]
    · by_cases h2 : w - 26 < C.gates.length
      · let j := w - 26
        have hjlt : j < C.gates.length := h2
        have hwj : w = 26 + j := by omega
        have hmem : gateAt C j ∈ C.gates := by
          simp only [gateAt, List.getD_eq_getElem _ _ hjlt]; exact List.getElem_mem hjlt
        rcases hAO.1 (gateAt C j) hmem with hand | hor
        · rw [hwj, wireSets_and_eq C j hjlt hand]; simp
        · rw [hwj, wireSets_or_eq C hAO j hjlt hor]
          have hlt := gate_inputs_lt hAO hjlt
          intro i hi
          simp only [Finset.mem_union] at hi
          rcases hi with h | h
          · exact ih _ (by omega) i h
          · exact ih _ (by omega) i h
      · rw [wireSets]; simp [h1, h2]

lemma wireSets_and_mem (C : Circuit) (hAO : IsAO2 26 C) :
    ∀ w : ℕ, ∀ j ∈ (wireSets C w).2, j < C.gates.length ∧ (gateAt C j).op = GateOp.and := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h1 : w < 26
    · rw [wireSets]; simp [h1]
    · by_cases h2 : w - 26 < C.gates.length
      · let j0 := w - 26
        have hj0lt : j0 < C.gates.length := h2
        have hwj : w = 26 + j0 := by omega
        have hmem : gateAt C j0 ∈ C.gates := by
          simp only [gateAt, List.getD_eq_getElem _ _ hj0lt]; exact List.getElem_mem hj0lt
        rcases hAO.1 (gateAt C j0) hmem with hand | hor
        · rw [hwj, wireSets_and_eq C j0 hj0lt hand]
          intro j hj; simp only [Finset.mem_singleton] at hj; subst hj; exact ⟨hj0lt, hand⟩
        · rw [hwj, wireSets_or_eq C hAO j0 hj0lt hor]
          have hlt := gate_inputs_lt hAO hj0lt
          intro j hj
          simp only [Finset.mem_union] at hj
          rcases hj with h | h
          · exact ih _ (by omega) j h
          · exact ih _ (by omega) j h
      · rw [wireSets]; simp [h1, h2]

lemma dag_expand {α : Type*} [DecidableEq α]
    (F : ℕ → Finset α) (E : Finset ℕ) (ch : ℕ → ℕ × ℕ)
    (hlt : ∀ w ∈ E, (ch w).1 < w ∧ (ch w).2 < w)
    (hsub : ∀ w ∈ E, F w ⊆ F (ch w).1 ∪ F (ch w).2)
    (hclosed : ∀ w ∈ E, ((ch w).1 ∈ E ∨ (F (ch w).1).card ≤ 1) ∧ ((ch w).2 ∈ E ∨ (F (ch w).2).card ≤ 1)) :
    ∀ (W : Finset ℕ), (∀ w ∈ W, w ∈ E ∨ (F w).card ≤ 1) →
      (W.biUnion F).card ≤ W.card + E.card := by
  classical
  have hgen : ∀ (k : ℕ) (E : Finset ℕ), E.card = k →
      (∀ w ∈ E, (ch w).1 < w ∧ (ch w).2 < w) →
      (∀ w ∈ E, F w ⊆ F (ch w).1 ∪ F (ch w).2) →
      (∀ w ∈ E, ((ch w).1 ∈ E ∨ (F (ch w).1).card ≤ 1) ∧ ((ch w).2 ∈ E ∨ (F (ch w).2).card ≤ 1)) →
      ∀ (W : Finset ℕ), (∀ w ∈ W, w ∈ E ∨ (F w).card ≤ 1) →
        (W.biUnion F).card ≤ W.card + E.card := by
    intro k
    induction k with
    | zero =>
      intro E hcard _ _ _ W hW
      have hE : E = ∅ := Finset.card_eq_zero.mp hcard
      subst hE
      calc (W.biUnion F).card
          ≤ ∑ w ∈ W, (F w).card := Finset.card_biUnion_le
        _ ≤ ∑ _w ∈ W, 1 := Finset.sum_le_sum fun w hw => (hW w hw).resolve_left (by simp)
        _ = W.card := by simp
        _ = W.card + (∅ : Finset ℕ).card := by simp
    | succ k ih =>
      intro E hcard hlt hsub hclosed W hW
      have hne : E.Nonempty := Finset.card_pos.mp (by omega)
      let m := E.max' hne
      have hmE : m ∈ E := Finset.max'_mem E hne
      let E' := E.erase m
      have hE'card : E'.card = k := by
        change (E.erase m).card = k
        rw [Finset.card_erase_of_mem hmE]
        omega
      have hlt' : ∀ w ∈ E', (ch w).1 < w ∧ (ch w).2 < w :=
        fun w hw => hlt w (Finset.mem_of_mem_erase hw)
      have hsub' : ∀ w ∈ E', F w ⊆ F (ch w).1 ∪ F (ch w).2 :=
        fun w hw => hsub w (Finset.mem_of_mem_erase hw)
      have hclosed' : ∀ w ∈ E',
          ((ch w).1 ∈ E' ∨ (F (ch w).1).card ≤ 1) ∧ ((ch w).2 ∈ E' ∨ (F (ch w).2).card ≤ 1) := by
        intro w hw
        have hwE : w ∈ E := Finset.mem_of_mem_erase hw
        have hwm : w ≤ m := Finset.le_max' E w hwE
        have hc := hclosed w hwE
        have hltw := hlt w hwE
        constructor
        · rcases hc.1 with h | h
          · left; exact Finset.mem_erase.mpr ⟨by omega, h⟩
          · exact Or.inr h
        · rcases hc.2 with h | h
          · left; exact Finset.mem_erase.mpr ⟨by omega, h⟩
          · exact Or.inr h
      by_cases hmW : m ∈ W
      · let W' := insert (ch m).1 (insert (ch m).2 (W.erase m))
        have hW'ok : ∀ w ∈ W', w ∈ E' ∨ (F w).card ≤ 1 := by
          intro w hw
          simp only [W', Finset.mem_insert, Finset.mem_erase] at hw
          have hcm := hclosed m hmE
          have hltm := hlt m hmE
          rcases hw with rfl | rfl | ⟨hwne, hwW⟩
          · rcases hcm.1 with h | h
            · left; exact Finset.mem_erase.mpr ⟨by omega, h⟩
            · exact Or.inr h
          · rcases hcm.2 with h | h
            · left; exact Finset.mem_erase.mpr ⟨by omega, h⟩
            · exact Or.inr h
          · rcases hW w hwW with h | h
            · left; exact Finset.mem_erase.mpr ⟨hwne, h⟩
            · exact Or.inr h
        have hW'sub : W.biUnion F ⊆ W'.biUnion F := by
          intro a ha
          obtain ⟨w, hwW, haw⟩ := Finset.mem_biUnion.mp ha
          by_cases hwm : w = m
          · subst hwm
            have h1 := hsub m hmE haw
            simp only [Finset.mem_union] at h1
            rcases h1 with h | h
            · exact Finset.mem_biUnion.mpr ⟨(ch m).1, Finset.mem_insert_self _ _, h⟩
            · exact Finset.mem_biUnion.mpr ⟨(ch m).2,
                Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), h⟩
          · exact Finset.mem_biUnion.mpr ⟨w,
              Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hwm, hwW⟩)), haw⟩
        have hW'card : W'.card ≤ W.card + 1 := by
          change (insert (ch m).1 (insert (ch m).2 (W.erase m))).card ≤ W.card + 1
          have h1 := Finset.card_insert_le (ch m).1 (insert (ch m).2 (W.erase m))
          have h2 := Finset.card_insert_le (ch m).2 (W.erase m)
          have h3 := Finset.card_erase_of_mem hmW
          have h4 : 1 ≤ W.card := Finset.card_pos.mpr ⟨m, hmW⟩
          omega
        have hih := ih E' hE'card hlt' hsub' hclosed' W' hW'ok
        have hle := Finset.card_le_card hW'sub
        omega
      · have hWok : ∀ w ∈ W, w ∈ E' ∨ (F w).card ≤ 1 := by
          intro w hw
          have hne : w ≠ m := fun e => hmW (e ▸ hw)
          rcases hW w hw with h | h
          · left; exact Finset.mem_erase.mpr ⟨hne, h⟩
          · exact Or.inr h
        have hih := ih E' hE'card hlt' hsub' hclosed' W hWok
        omega
  exact hgen E.card E rfl hlt hsub hclosed

def Qshift (p : Fin 13) : Finset (Fin 13) :=
  {p, p + 1, p + 2, p + 5}

lemma mem_quadrangles_iff (Q : Finset (Fin 13)) :
    Q ∈ quadrangles singerLines3 ↔ Q.card = 4 ∧ ∀ l : Fin 13, (Q ∩ singerLines3 l).card ≤ 2 := by
  simp [quadrangles, Finset.mem_powersetCard]

lemma Qshift_mem_quadrangles (p : Fin 13) : Qshift p ∈ quadrangles singerLines3 := by
  rw [mem_quadrangles_iff]
  fin_cases p <;> decide

lemma mem_Qshift (p : Fin 13) : p ∈ Qshift p := by
  simp [Qshift]

lemma mem_missLines_Qshift (l : Fin 13) :
    l ∈ missLines singerLines3 (Qshift (l - 3)) := by
  simp only [missLines, Finset.mem_filter, Finset.mem_univ, true_and]
  fin_cases l <;> decide

def quadInput (Q : Finset (Fin 13)) : List Bool :=
  (List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
  (List.ofFn fun l : Fin 13 => decide (l ∈ missLines singerLines3 Q))

lemma quadInput_length (Q : Finset (Fin 13)) : (quadInput Q).length = 26 := by
  simp [quadInput]

lemma quadInput_getD_pt (Q : Finset (Fin 13)) (p : Fin 13) :
    (quadInput Q).getD p.val false = decide (p ∈ Q) := by
  have hlt1 : p.val < (List.ofFn fun x : Fin 13 => decide (x ∈ Q)).length := by simp
  have hlt2 : p.val < (quadInput Q).length := by rw [quadInput_length]; exact Nat.lt_trans p.isLt (by omega)
  rw [List.getD_eq_getElem _ _ hlt2]
  simp only [quadInput, List.getElem_append_left hlt1, List.getElem_ofFn, Fin.eta]

lemma quadInput_getD_ln (Q : Finset (Fin 13)) (l : Fin 13) :
    (quadInput Q).getD (13 + l.val) false = decide (l ∈ missLines singerLines3 Q) := by
  have hlt2 : 13 + l.val < (quadInput Q).length := by rw [quadInput_length]; omega
  rw [List.getD_eq_getElem _ _ hlt2]
  simp only [quadInput]
  have hge : (List.ofFn fun x : Fin 13 => decide (x ∈ Q)).length ≤ 13 + l.val := by simp
  rw [List.getElem_append_right hge]
  simp only [List.length_ofFn, Nat.add_sub_cancel_left, List.getElem_ofFn, Fin.eta]

lemma main_proof (C : Circuit) (hAO : IsAO2 26 C)
    (hquad : ∀ Q ∈ quadrangles singerLines3, C.eval (quadInput Q) = false)
    (_hpos : ∃ z : List Bool, z.length = 26 ∧ C.eval z = true) :
    ∃ A : Finset ℕ,
      (∀ j ∈ A, j < C.size ∧ (gateAt C j).op = GateOp.and ∧
        ∀ Q ∈ quadrangles singerLines3, (C.wires (quadInput Q)).getD (26 + j) false = false) ∧
      2 * A.card ≤ C.size + 1 ∧
      ∀ z : List Bool, z.length = 26 →
        (C.eval z = true ↔ ∃ j ∈ A, (C.wires z).getD (26 + j) false = true) := by
  classical
  have hbare : (wireSets C C.output).1 = ∅ := by
    ext i
    simp only [Finset.notMem_empty, iff_false]
    intro hi
    have hilt : i < 26 := wireSets_bare_lt C hAO C.output i hi
    by_cases hp : i < 13
    · let p : Fin 13 := ⟨i, hp⟩
      let Q := Qshift p
      have hQ : Q ∈ quadrangles singerLines3 := Qshift_mem_quadrangles p
      have hget : (quadInput Q).getD i false = true := by
        have := quadInput_getD_pt Q p
        simp only [Q, mem_Qshift p, decide_true] at this
        exact this
      have htrue : C.eval (quadInput Q) = true :=
        (wireSets_eval C hAO (quadInput Q) (quadInput_length Q) C.output).mpr (Or.inl ⟨i, hi, hget⟩)
      rw [hquad Q hQ] at htrue
      cases htrue
    · let l : Fin 13 := ⟨i - 13, by omega⟩
      let Q := Qshift (l - 3)
      have hQ : Q ∈ quadrangles singerLines3 := Qshift_mem_quadrangles (l - 3)
      have hi_eq : i = 13 + l.val := by simp only [l]; omega
      have hget : (quadInput Q).getD i false = true := by
        rw [hi_eq]
        have := quadInput_getD_ln Q l
        simp only [Q, mem_missLines_Qshift l, decide_true] at this
        exact this
      have htrue : C.eval (quadInput Q) = true :=
        (wireSets_eval C hAO (quadInput Q) (quadInput_length Q) C.output).mpr (Or.inl ⟨i, hi, hget⟩)
      rw [hquad Q hQ] at htrue
      cases htrue
  let A : Finset ℕ := (wireSets C C.output).2
  have heval : ∀ z : List Bool, z.length = 26 →
      (C.eval z = true ↔ ∃ j ∈ A, (C.wires z).getD (26 + j) false = true) := by
    intro z hz
    change wv C z C.output = true ↔ _
    rw [wireSets_eval C hAO z hz C.output, hbare]
    simp [A, wv]
  have hA_and : ∀ j ∈ A, j < C.size ∧ (gateAt C j).op = GateOp.and :=
    wireSets_and_mem C hAO C.output
  have hA_quad : ∀ j ∈ A, ∀ Q ∈ quadrangles singerLines3,
      (C.wires (quadInput Q)).getD (26 + j) false = false := by
    intro j hj Q hQ
    by_contra hne
    have htrue : (C.wires (quadInput Q)).getD (26 + j) false = true := by
      cases h : (C.wires (quadInput Q)).getD (26 + j) false
      · exact absurd h hne
      · rfl
    have hev := (heval (quadInput Q) (quadInput_length Q)).mpr ⟨j, hj, htrue⟩
    rw [hquad Q hQ] at hev
    cases hev
  let allG := Finset.range C.gates.length
  let GA := allG.filter fun j => (gateAt C j).op = GateOp.and
  let GO := allG.filter fun j => (gateAt C j).op = GateOp.or
  have hGsum : GA.card + GO.card ≤ C.size := by
    have hdisj : Disjoint GA GO := Finset.disjoint_filter.mpr fun j _ h1 h2 => by rw [h1] at h2; cases h2
    have hsub : GA ∪ GO ⊆ allG := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_range] at hc
    exact hc
  have hA_le_GA : A.card ≤ GA.card := by
    apply Finset.card_le_card
    intro j hj
    have hja := hA_and j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hja.1, hja.2⟩
  let ch (w : ℕ) : ℕ × ℕ := ((gateAt C (w - 26)).inputs.getD 0 0, (gateAt C (w - 26)).inputs.getD 1 0)
  have hA_le_GO : A.card ≤ GO.card + 1 := by
    let E := GO.image (fun j => 26 + j)
    have hEcard : E.card = GO.card := Finset.card_image_of_injective _ (fun _ _ h => by omega)
    have hnot_in : ∀ w, w ∉ E → ((wireSets C w).2).card ≤ 1 := by
      intro w hw
      by_cases h1 : w < 26
      · rw [wireSets]; simp [h1]
      · by_cases h2 : w - 26 < C.gates.length
        · let j := w - 26
          have hjlt : j < C.gates.length := h2
          have hwj : w = 26 + j := by omega
          have hmem : gateAt C j ∈ C.gates := by
            simp only [gateAt, List.getD_eq_getElem _ _ hjlt]; exact List.getElem_mem hjlt
          rcases hAO.1 (gateAt C j) hmem with hand | hor
          · rw [hwj, wireSets_and_eq C j hjlt hand]; simp
          · exfalso; apply hw
            exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjlt, hor⟩, hwj.symm⟩
        · rw [wireSets]; simp [h1, h2]
    have hexp := dag_expand (fun w => (wireSets C w).2) E ch
      (fun w hw => by
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
        have hjlt := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
        simpa [ch] using gate_inputs_lt hAO hjlt)
      (fun w hw => by
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
        have hjf := Finset.mem_filter.mp hj
        rw [wireSets_or_eq C hAO j (Finset.mem_range.mp hjf.1) hjf.2]
        simp [ch])
      (fun w _ => ⟨by by_cases h : (ch w).1 ∈ E; exact Or.inl h; exact Or.inr (hnot_in _ h),
                   by by_cases h : (ch w).2 ∈ E; exact Or.inl h; exact Or.inr (hnot_in _ h)⟩)
      {C.output}
      (fun w _ => by by_cases h : w ∈ E; exact Or.inl h; exact Or.inr (hnot_in _ h))
    have hb : ({C.output} : Finset ℕ).biUnion (fun w => (wireSets C w).2) = A := by
      ext j; simp [A]
    rw [hb, Finset.card_singleton, hEcard] at hexp
    omega
  refine ⟨A, fun j hj => ⟨(hA_and j hj).1, (hA_and j hj).2, hA_quad j hj⟩, by omega, heval⟩

end PEqualNP.Outside.L_meta_5276

theorem PEqualNP.Outside.L_meta_5276 :
    have x1 : Finset (Fin (13 : ℕ)) → List Bool := fun (x1 : Finset (Fin (13 : ℕ))) =>
      (List.ofFn fun (x2 : Fin (13 : ℕ)) => Decidable.decide (x2 ∈ x1)) ++
      List.ofFn fun (x2 : Fin (13 : ℕ)) =>
        Decidable.decide (x2 ∈ PEqualNP.HeptadCover.missLines PEqualNP.HeptadCover.singerLines3 x1);
    ∀ (x2 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.TopForm.IsAO2 (26 : ℕ) x2 →
      (∀ x4 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3,
        x2.eval (x1 x4) = Bool.false) →
      (∃ (x5 : List Bool), x5.length = (26 : ℕ) ∧ x2.eval x5 = Bool.true) →
      ∃ (x6 : Finset ℕ),
        (∀ x7 ∈ x6, x7 < x2.size ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt x2 x7).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
          ∀ x9 ∈ PEqualNP.HeptadCover.quadrangles PEqualNP.HeptadCover.singerLines3,
            (x2.wires (x1 x9)).getD ((26 : ℕ) + x7) Bool.false = Bool.false) ∧
        (2 : ℕ) * x6.card ≤ x2.size + (1 : ℕ) ∧
        ∀ (x7 : List Bool), x7.length = (26 : ℕ) →
          (x2.eval x7 = Bool.true ↔
            ∃ x9 ∈ x6, (x2.wires x7).getD ((26 : ℕ) + x9) Bool.false = Bool.true) :=
  PEqualNP.Outside.L_meta_5276.main_proof
