import Mathlib.Data.List.OfFn
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4990

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.ReadTwo

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [step]
    omega

lemma keepInput (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

def wv (n : ℕ) (C : Circuit) (z : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn z)).getD w false

lemma wv_input {n : ℕ} (C : Circuit) (z : Fin n → Bool) (i : Fin n) :
    wv n C z i.val = z i := by
  change (C.gates.foldl step (List.ofFn z)).getD i.val false = z i
  rw [keepInput C.gates (List.ofFn z) i.val (by simp),
      List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]

lemma wv_ge {n : ℕ} (C : Circuit) (z : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    wv n C z w = false := by
  change (C.gates.foldl step (List.ofFn z)).getD w false = false
  exact List.getD_eq_default _ _ (by rw [foldl_length]; simp; omega)

lemma wv_gate {n : ℕ} (C : Circuit) (hRB : ReadsBack n C) (z : Fin n → Bool)
    (j : ℕ) (hj : j < C.gates.length) :
    wv n C z (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => wv n C z i) := by
  let g := C.gates[j]
  have hgat : gateAt C j = g := by
    simp only [gateAt, g, List.getD_eq_getElem _ _ hj]
  rw [hgat]
  have hsplit : C.gates = C.gates.take j ++ g :: C.gates.drop (j + 1) := by
    have h1 := List.take_append_drop j C.gates
    have h2 : C.gates.drop j = g :: C.gates.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    exact h1.symm
  let pre := C.gates.take j
  let post := C.gates.drop (j + 1)
  have hpre_len : pre.length = j := List.length_take_of_le (Nat.le_of_lt hj)
  let w0 := pre.foldl step (List.ofFn z)
  have hw0_len : w0.length = n + j := by
    simp [w0, foldl_length, hpre_len]
  have hfull : C.gates.foldl step (List.ofFn z) = post.foldl step (step w0 g) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hlt_eq : ∀ i, i < n + j → wv n C z i = w0.getD i false := by
    intro i hi
    change (C.gates.foldl step (List.ofFn z)).getD i false = w0.getD i false
    rw [hfull, keepInput post (step w0 g) i (by simp [step, hw0_len]; omega)]
    simp only [step, List.getD_eq_getElem?_getD, List.getElem?_append_left (hw0_len ▸ hi)]
  have hres : wv n C z (n + j) = g.op.eval (g.inputs.map fun i => w0.getD i false) := by
    change (C.gates.foldl step (List.ofFn z)).getD (n + j) false = _
    rw [hfull, keepInput post (step w0 g) (n + j) (by simp [step, hw0_len])]
    rw [step, List.getD_append_right _ _ _ _ (by omega)]
    simp [hw0_len]
  rw [hres]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hilt : i < n + j := hRB j hj i (hgat ▸ hi)
  exact (hlt_eq i hilt).symm

lemma gate_inputs_pair {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [(gateAt C j).inputs.getD 0 0, (gateAt C j).inputs.getD 1 0] := by
  have hmem : gateAt C j ∈ C.gates := by
    simp only [gateAt, List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 (gateAt C j) hmem
  rcases h : (gateAt C j).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp [h] at hlen
  · simp [h] at hlen
  · simp
  · simp [h] at hlen

lemma gate_inputs_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs.getD 0 0 < n + j ∧ (gateAt C j).inputs.getD 1 0 < n + j := by
  have hp := gate_inputs_pair hAO hj
  have h0 : (gateAt C j).inputs.getD 0 0 ∈ (gateAt C j).inputs := by rw [hp]; simp
  have h1 : (gateAt C j).inputs.getD 1 0 ∈ (gateAt C j).inputs := by rw [hp]; simp
  exact ⟨hAO.2.1 j hj _ h0, hAO.2.1 j hj _ h1⟩

noncomputable def wireSets (x1 x2 : ℕ) (C : Circuit) (w : ℕ) :
    Finset (Fin x1) × Finset (Fin x2) × Finset ℕ :=
  if h1 : w < x1 then
    ({⟨w, h1⟩}, ∅, ∅)
  else if h2 : w < x1 + x2 then
    (∅, {⟨w - x1, by omega⟩}, ∅)
  else if h3 : w - (x1 + x2) < C.gates.length then
    let j := w - (x1 + x2)
    let g := gateAt C j
    match g.op with
    | GateOp.and => (∅, ∅, {j})
    | GateOp.or =>
      let u := g.inputs.getD 0 0
      let v := g.inputs.getD 1 0
      if hu : u < w then
        if hv : v < w then
          let ru := wireSets x1 x2 C u
          let rv := wireSets x1 x2 C v
          (ru.1 ∪ rv.1, ru.2.1 ∪ rv.2.1, ru.2.2 ∪ rv.2.2)
        else (∅, ∅, ∅)
      else (∅, ∅, ∅)
    | _ => (∅, ∅, ∅)
  else (∅, ∅, ∅)
termination_by w

lemma wireSets_or_eq (x1 x2 : ℕ) (C : Circuit) (hAO : IsAO2 (x1 + x2) C)
    (j : ℕ) (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    let u := (gateAt C j).inputs.getD 0 0
    let v := (gateAt C j).inputs.getD 1 0
    wireSets x1 x2 C (x1 + x2 + j) =
      ((wireSets x1 x2 C u).1 ∪ (wireSets x1 x2 C v).1,
       (wireSets x1 x2 C u).2.1 ∪ (wireSets x1 x2 C v).2.1,
       (wireSets x1 x2 C u).2.2 ∪ (wireSets x1 x2 C v).2.2) := by
  have hlt := gate_inputs_lt hAO hj
  have h1 : ¬ (x1 + x2 + j < x1) := by omega
  have h2 : ¬ (x1 + x2 + j < x1 + x2) := by omega
  have hsub : x1 + x2 + j - (x1 + x2) = j := by omega
  rw [wireSets]
  simp only [h1, h2, hsub, hj, hop, hlt.1, hlt.2, ↓reduceDIte]

lemma wireSets_and_eq (x1 x2 : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and) :
    wireSets x1 x2 C (x1 + x2 + j) = (∅, ∅, {j}) := by
  have h1 : ¬ (x1 + x2 + j < x1) := by omega
  have h2 : ¬ (x1 + x2 + j < x1 + x2) := by omega
  have hsub : x1 + x2 + j - (x1 + x2) = j := by omega
  rw [wireSets]
  simp only [h1, h2, hsub, hj, hop, ↓reduceDIte]

lemma wireSets_eval (x1 x2 : ℕ) (C : Circuit) (hAO : IsAO2 (x1 + x2) C)
    (z : Fin (x1 + x2) → Bool) :
    ∀ w : ℕ,
      wv (x1 + x2) C z w = true ↔
        (∃ p ∈ (wireSets x1 x2 C w).1, z (Fin.castAdd x2 p) = true) ∨
        (∃ l ∈ (wireSets x1 x2 C w).2.1, z (Fin.natAdd x1 l) = true) ∨
        (∃ j ∈ (wireSets x1 x2 C w).2.2, wv (x1 + x2) C z (x1 + x2 + j) = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h1 : w < x1
    · have hws : wireSets x1 x2 C w = ({⟨w, h1⟩}, ∅, ∅) := by
        rw [wireSets]; simp only [h1, ↓reduceDIte]
      rw [hws]
      have hcast : Fin.castAdd x2 (⟨w, h1⟩ : Fin x1) = ⟨w, by omega⟩ := Fin.ext rfl
      have hwi : wv (x1 + x2) C z w = z (Fin.castAdd x2 ⟨w, h1⟩) := by
        rw [hcast]; exact wv_input C z ⟨w, by omega⟩
      simp [hwi]
    · by_cases h2 : w < x1 + x2
      · have hws : wireSets x1 x2 C w = (∅, {⟨w - x1, by omega⟩}, ∅) := by
          rw [wireSets]; simp only [h1, h2, ↓reduceDIte]
        rw [hws]
        have hnat : Fin.natAdd x1 (⟨w - x1, by omega⟩ : Fin x2) = ⟨w, h2⟩ := Fin.ext (by simp; omega)
        have hwi : wv (x1 + x2) C z w = z (Fin.natAdd x1 ⟨w - x1, by omega⟩) := by
          rw [hnat]; exact wv_input C z ⟨w, h2⟩
        simp [hwi]
      · by_cases h3 : w - (x1 + x2) < C.gates.length
        · let j := w - (x1 + x2)
          have hjlt : j < C.gates.length := h3
          have hwj : w = x1 + x2 + j := by omega
          have hmem : gateAt C j ∈ C.gates := by
            simp only [gateAt, List.getD_eq_getElem _ _ hjlt]; exact List.getElem_mem hjlt
          have hop := hAO.1 (gateAt C j) hmem
          rcases hop with hand | hor
          · rw [hwj, wireSets_and_eq x1 x2 C j hjlt hand]
            simp
          · rw [hwj, wireSets_or_eq x1 x2 C hAO j hjlt hor, wv_gate C hAO.2.1 z j hjlt]
            have hpair := gate_inputs_pair hAO hjlt
            have hlt := gate_inputs_lt hAO hjlt
            let u := (gateAt C j).inputs.getD 0 0
            let v := (gateAt C j).inputs.getD 1 0
            have hev : (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => wv (x1 + x2) C z i) =
                (wv (x1 + x2) C z u || wv (x1 + x2) C z v) := by
              rw [hor, hpair]
              simp [GateOp.eval, u, v]
            rw [hev, Bool.or_eq_true, ih u (by dsimp only [u]; omega), ih v (by dsimp only [v]; omega)]
            dsimp only [u, v]
            simp only [Finset.mem_union, or_and_right, exists_or]
            constructor
            · rintro ((h | h | h) | (h | h | h))
              · exact Or.inl (Or.inl h)
              · exact Or.inr (Or.inl (Or.inl h))
              · exact Or.inr (Or.inr (Or.inl h))
              · exact Or.inl (Or.inr h)
              · exact Or.inr (Or.inl (Or.inr h))
              · exact Or.inr (Or.inr (Or.inr h))
            · rintro ((h | h) | (h | h) | (h | h))
              · exact Or.inl (Or.inl h)
              · exact Or.inr (Or.inl h)
              · exact Or.inl (Or.inr (Or.inl h))
              · exact Or.inr (Or.inr (Or.inl h))
              · exact Or.inl (Or.inr (Or.inr h))
              · exact Or.inr (Or.inr (Or.inr h))
        · have hws : wireSets x1 x2 C w = (∅, ∅, ∅) := by
            rw [wireSets]; simp only [h1, h2, h3, ↓reduceDIte]
          rw [hws, wv_ge C z w (by omega)]
          simp

lemma wireSets_and_mem (x1 x2 : ℕ) (C : Circuit) (hAO : IsAO2 (x1 + x2) C) :
    ∀ w : ℕ, ∀ j ∈ (wireSets x1 x2 C w).2.2,
      j < C.gates.length ∧ (gateAt C j).op = GateOp.and := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases h1 : w < x1
    · rw [wireSets]; simp [h1]
    · by_cases h2 : w < x1 + x2
      · rw [wireSets]; simp [h1, h2]
      · by_cases h3 : w - (x1 + x2) < C.gates.length
        · let j0 := w - (x1 + x2)
          have hj0lt : j0 < C.gates.length := h3
          have hwj : w = x1 + x2 + j0 := by omega
          have hmem : gateAt C j0 ∈ C.gates := by
            simp only [gateAt, List.getD_eq_getElem _ _ hj0lt]; exact List.getElem_mem hj0lt
          rcases hAO.1 (gateAt C j0) hmem with hand | hor
          · rw [hwj, wireSets_and_eq x1 x2 C j0 hj0lt hand]
            intro j hj; simp only [Finset.mem_singleton] at hj; subst hj; exact ⟨hj0lt, hand⟩
          · rw [hwj, wireSets_or_eq x1 x2 C hAO j0 hj0lt hor]
            have hlt := gate_inputs_lt hAO hj0lt
            intro j hj
            simp only [Finset.mem_union] at hj
            rcases hj with h | h
            · exact ih _ (by omega) j h
            · exact ih _ (by omega) j h
        · rw [wireSets]; simp [h1, h2, h3]

lemma x6_pure (x1 x2 : ℕ) (C : Circuit) (hAO : IsAO2 (x1 + x2) C) (x6 : Finset ℕ)
    (hx6 : ∀ w ∈ x6, w < x1 ∨ ∃ j < C.gates.length, w = x1 + x2 + j ∧ (gateAt C j).op = GateOp.or ∧
      ∀ u ∈ (gateAt C j).inputs, u ∈ x6) :
    ∀ w : ℕ, w ∈ x6 →
      (wireSets x1 x2 C w).1.Nonempty ∧ (wireSets x1 x2 C w).2.1 = ∅ ∧ (wireSets x1 x2 C w).2.2 = ∅ := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    rcases hx6 w hw with hlt | ⟨j, hj, rfl, hor, hins⟩
    · rw [wireSets]; simp [hlt]
    · rw [wireSets_or_eq x1 x2 C hAO j hj hor]
      have hpair := gate_inputs_pair hAO hj
      have hlt := gate_inputs_lt hAO hj
      have hu6 : (gateAt C j).inputs.getD 0 0 ∈ x6 := hins _ (by rw [hpair]; simp)
      have hv6 : (gateAt C j).inputs.getD 1 0 ∈ x6 := hins _ (by rw [hpair]; simp)
      have ihu := ih _ hlt.1 hu6
      have ihv := ih _ hlt.2 hv6
      refine ⟨ihu.1.mono Finset.subset_union_left, ?_, ?_⟩
      · dsimp only; rw [ihu.2.1, ihv.2.1]; simp
      · dsimp only; rw [ihu.2.2, ihv.2.2]; simp

lemma x7_pure (x1 x2 : ℕ) (C : Circuit) (hAO : IsAO2 (x1 + x2) C) (x7 : Finset ℕ)
    (hx7 : ∀ w ∈ x7, (x1 ≤ w ∧ w < x1 + x2) ∨ ∃ j < C.gates.length, w = x1 + x2 + j ∧
      (gateAt C j).op = GateOp.or ∧ ∀ u ∈ (gateAt C j).inputs, u ∈ x7) :
    ∀ w : ℕ, w ∈ x7 →
      (wireSets x1 x2 C w).1 = ∅ ∧ (wireSets x1 x2 C w).2.1.Nonempty ∧ (wireSets x1 x2 C w).2.2 = ∅ := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    rcases hx7 w hw with ⟨hge, hlt⟩ | ⟨j, hj, rfl, hor, hins⟩
    · have hnot : ¬ (w < x1) := by omega
      rw [wireSets]; simp [hnot, hlt]
    · rw [wireSets_or_eq x1 x2 C hAO j hj hor]
      have hpair := gate_inputs_pair hAO hj
      have hlt := gate_inputs_lt hAO hj
      have hu7 : (gateAt C j).inputs.getD 0 0 ∈ x7 := hins _ (by rw [hpair]; simp)
      have hv7 : (gateAt C j).inputs.getD 1 0 ∈ x7 := hins _ (by rw [hpair]; simp)
      have ihu := ih _ hlt.1 hu7
      have ihv := ih _ hlt.2 hv7
      refine ⟨?_, ihu.2.1.mono Finset.subset_union_left, ?_⟩
      · dsimp only; rw [ihu.1, ihv.1]; simp
      · dsimp only; rw [ihu.2.2, ihv.2.2]; simp

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

lemma main_proof (x1 x2 : ℕ) (I : Fin x1 → Fin x2 → Prop) [DecidableRel I]
    (C : Circuit) (x6 x7 : Finset ℕ)
    (hc4 : ∀ p p' : Fin x1, ∀ l l' : Fin x2, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (hAO : IsAO2 (x1 + x2) C)
    (hfun : ∀ z : Fin (x1 + x2) → Bool,
      circuitFun (x1 + x2) C z = decide (∃ p : Fin x1, ∃ l : Fin x2,
        I p l ∧ z (Fin.castAdd x2 p) = true ∧ z (Fin.natAdd x1 l) = true))
    (hx6 : ∀ w ∈ x6, w < x1 ∨ ∃ j < C.gates.length, w = x1 + x2 + j ∧ (gateAt C j).op = GateOp.or ∧
      ∀ u ∈ (gateAt C j).inputs, u ∈ x6)
    (hx7 : ∀ w ∈ x7, (x1 ≤ w ∧ w < x1 + x2) ∨ ∃ j < C.gates.length, w = x1 + x2 + j ∧
      (gateAt C j).op = GateOp.or ∧ ∀ u ∈ (gateAt C j).inputs, u ∈ x7)
    (hand : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∃ a b, (gateAt C j).inputs = [a, b] ∧ a ∈ x7 ∧ b ∈ x6) :
    ∃ T : Finset (Fin (x1 + x2)),
      (∀ p l, I p l → Fin.castAdd x2 p ∈ T ∨ Fin.natAdd x1 l ∈ T) ∧
      (incid I).card + T.card ≤ C.size + 1 := by
  classical
  let n := x1 + x2
  -- First show bareP and bareL of C.output are empty
  have hbareP : (wireSets x1 x2 C C.output).1 = ∅ := by
    ext p
    simp only [Finset.notMem_empty, iff_false]
    intro hp
    let z : Fin n → Bool := fun i => decide (i = Fin.castAdd x2 p)
    have h1 : wv n C z C.output = true :=
      (wireSets_eval x1 x2 C hAO z C.output).mpr (Or.inl ⟨p, hp, by simp [z]⟩)
    change circuitFun n C z = true at h1
    rw [hfun z, decide_eq_true_eq] at h1
    obtain ⟨_, l, _, _, hl⟩ := h1
    simp only [z, decide_eq_true_eq] at hl
    have hval := congrArg Fin.val hl
    simp at hval
    have := p.isLt
    omega
  have hbareL : (wireSets x1 x2 C C.output).2.1 = ∅ := by
    ext l
    simp only [Finset.notMem_empty, iff_false]
    intro hl
    let z : Fin n → Bool := fun i => decide (i = Fin.natAdd x1 l)
    have h1 : wv n C z C.output = true :=
      (wireSets_eval x1 x2 C hAO z C.output).mpr (Or.inr (Or.inl ⟨l, hl, by simp [z]⟩))
    change circuitFun n C z = true at h1
    rw [hfun z, decide_eq_true_eq] at h1
    obtain ⟨p, _, _, hp, _⟩ := h1
    simp only [z, decide_eq_true_eq] at hp
    have hval := congrArg Fin.val hp
    simp at hval
    have := p.isLt
    omega
  let Aout : Finset ℕ := (wireSets x1 x2 C C.output).2.2
  have hout_eval (z : Fin n → Bool) :
      circuitFun n C z = true ↔ ∃ j ∈ Aout, wv n C z (n + j) = true := by
    change wv n C z C.output = true ↔ _
    rw [wireSets_eval x1 x2 C hAO z C.output, hbareP, hbareL]
    simp [Aout, n]
  -- Evaluate each AND gate j < C.gates.length
  have hand_eval : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      let a := (gateAt C j).inputs.getD 0 0
      let b := (gateAt C j).inputs.getD 1 0
      a ∈ x7 ∧ b ∈ x6 ∧
      ∀ z : Fin n → Bool, wv n C z (n + j) = true ↔
        (∃ l ∈ (wireSets x1 x2 C a).2.1, z (Fin.natAdd x1 l) = true) ∧
        (∃ p ∈ (wireSets x1 x2 C b).1, z (Fin.castAdd x2 p) = true) := by
    intro j hj hop
    obtain ⟨a, b, hins, ha7, hb6⟩ := hand j hj hop
    have ha_eq : (gateAt C j).inputs.getD 0 0 = a := by simp [hins]
    have hb_eq : (gateAt C j).inputs.getD 1 0 = b := by simp [hins]
    rw [ha_eq, hb_eq]
    refine ⟨ha7, hb6, fun z => ?_⟩
    rw [wv_gate C hAO.2.1 z j hj, hop, hins]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
      Bool.and_true, Bool.and_eq_true]
    rw [wireSets_eval x1 x2 C hAO z a, wireSets_eval x1 x2 C hAO z b]
    have hp7 := x7_pure x1 x2 C hAO x7 hx7 a ha7
    have hp6 := x6_pure x1 x2 C hAO x6 hx6 b hb6
    rw [hp7.1, hp7.2.2, hp6.2.1, hp6.2.2]
    simp
  -- For every j ∈ Aout, S_P(b_j) × S_L(a_j) ⊆ I, and either |S_P| ≤ 1 or |S_L| ≤ 1
  have hAout_and : ∀ j ∈ Aout, j < C.gates.length ∧ (gateAt C j).op = GateOp.and :=
    wireSets_and_mem x1 x2 C hAO C.output
  have hAout_clean : ∀ j ∈ Aout,
      let a := (gateAt C j).inputs.getD 0 0
      let b := (gateAt C j).inputs.getD 1 0
      ∀ p ∈ (wireSets x1 x2 C b).1, ∀ l ∈ (wireSets x1 x2 C a).2.1, I p l := by
    intro j hj a b p hp l hl
    have hja := hAout_and j hj
    have he := hand_eval j hja.1 hja.2
    let z : Fin n → Bool := fun i => decide (i = Fin.castAdd x2 p ∨ i = Fin.natAdd x1 l)
    have htrue : wv n C z (n + j) = true := (he.2.2 z).mpr ⟨⟨l, hl, by simp [z]⟩, ⟨p, hp, by simp [z]⟩⟩
    have houtT : circuitFun n C z = true := (hout_eval z).mpr ⟨j, hj, htrue⟩
    rw [hfun z, decide_eq_true_eq] at houtT
    obtain ⟨p', l', hI', hp', hl'⟩ := houtT
    simp only [z, decide_eq_true_eq] at hp' hl'
    have hpp' : p' = p := by
      rcases hp' with h | h
      · exact Fin.ext (by have := congrArg Fin.val h; simpa using this)
      · exfalso; have := congrArg Fin.val h; simp at this; have := p'.isLt; omega
    have hll' : l' = l := by
      rcases hl' with h | h
      · exfalso; have := congrArg Fin.val h; simp at this; have := p.isLt; omega
      · exact Fin.ext (by have := congrArg Fin.val h; simp at this; omega)
    rw [hpp', hll'] at hI'
    exact hI'
  have hAout_star : ∀ j ∈ Aout,
      ((wireSets x1 x2 C ((gateAt C j).inputs.getD 1 0)).1).card = 1 ∨
      ((wireSets x1 x2 C ((gateAt C j).inputs.getD 0 0)).2.1).card = 1 := by
    intro j hj
    have hja := hAout_and j hj
    have he := hand_eval j hja.1 hja.2
    have hneP := (x6_pure x1 x2 C hAO x6 hx6 _ he.2.1).1
    have hneL := (x7_pure x1 x2 C hAO x7 hx7 _ he.1).2.1
    by_contra hboth
    push Not at hboth
    have hP2 : 1 < ((wireSets x1 x2 C ((gateAt C j).inputs.getD 1 0)).1).card := by
      have := hneP.card_pos; omega
    have hL2 : 1 < ((wireSets x1 x2 C ((gateAt C j).inputs.getD 0 0)).2.1).card := by
      have := hneL.card_pos; omega
    obtain ⟨p, hp, p', hp', hpp'⟩ := Finset.one_lt_card.mp hP2
    obtain ⟨l, hl, l', hl', hll'⟩ := Finset.one_lt_card.mp hL2
    exact hc4 p p' l l' hpp' hll'
      ⟨hAout_clean j hj p hp l hl, hAout_clean j hj p hp l' hl',
       hAout_clean j hj p' hp' l hl, hAout_clean j hj p' hp' l' hl'⟩
  -- Split Aout into AP (|S_P| = 1) and AL (|S_P| > 1, so |S_L| = 1)
  let AP : Finset ℕ := Aout.filter fun j => ((wireSets x1 x2 C ((gateAt C j).inputs.getD 1 0)).1).card = 1
  let AL : Finset ℕ := Aout.filter fun j => ((wireSets x1 x2 C ((gateAt C j).inputs.getD 1 0)).1).card ≠ 1
  have hAout_split : AP.card + AL.card = Aout.card := by
    rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter.mpr fun _ _ h1 h2 => h2 h1)]
    congr 1; ext j; simp only [Finset.mem_union, Finset.mem_filter]; tauto
  -- Centers of AP and AL
  let pCtr (j : ℕ) : Finset (Fin x1) := (wireSets x1 x2 C ((gateAt C j).inputs.getD 1 0)).1
  let lCtr (j : ℕ) : Finset (Fin x2) := (wireSets x1 x2 C ((gateAt C j).inputs.getD 0 0)).2.1
  let TP : Finset (Fin x1) := AP.biUnion pCtr
  let TL : Finset (Fin x2) := AL.biUnion lCtr
  let T : Finset (Fin n) := TP.image (Fin.castAdd x2) ∪ TL.image (Fin.natAdd x1)
  have hT_card : T.card = TP.card + TL.card := by
    have hdisj : Disjoint (TP.image (Fin.castAdd x2)) (TL.image (Fin.natAdd x1)) := by
      rw [Finset.disjoint_left]
      intro v hvP hvL
      obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hvP
      obtain ⟨l, _, hl⟩ := Finset.mem_image.mp hvL
      have := congrArg Fin.val hl; simp at this; have := p.isLt; omega
    rw [Finset.card_union_of_disjoint hdisj,
        Finset.card_image_of_injective _ (Fin.castAdd_injective x1 x2),
        Finset.card_image_of_injective _ (Fin.natAdd_injective x2 x1)]
  -- T is a vertex cover of I, and every edge of incid I is covered by AP or AL
  have hedge_cov : ∀ e ∈ incid I,
      (∃ p ∈ TP, e.1 = p ∧ e.2 ∈ (AP.filter fun j => p ∈ pCtr j).biUnion lCtr) ∨
      (∃ l ∈ TL, e.2 = l ∧ e.1 ∈ (AL.filter fun j => l ∈ lCtr j).biUnion pCtr) := by
    intro ⟨p, l⟩ he
    simp only [incid, Finset.mem_filter, Finset.mem_univ, true_and] at he
    let z : Fin n → Bool := fun i => decide (i = Fin.castAdd x2 p ∨ i = Fin.natAdd x1 l)
    have hct : circuitFun n C z = true := by
      rw [hfun z, decide_eq_true_eq]; exact ⟨p, l, he, by simp [z], by simp [z]⟩
    obtain ⟨j, hjAout, hjT⟩ := (hout_eval z).mp hct
    have hja := hAout_and j hjAout
    obtain ⟨⟨l', hl', hzl'⟩, ⟨p', hp', hzp'⟩⟩ := ((hand_eval j hja.1 hja.2).2.2 z).mp hjT
    simp only [z, decide_eq_true_eq] at hzp' hzl'
    have hpp' : p' = p := by
      rcases hzp' with h | h
      · exact Fin.ext (by have := congrArg Fin.val h; simpa using this)
      · exfalso; have := congrArg Fin.val h; simp at this; have := p'.isLt; omega
    have hll' : l' = l := by
      rcases hzl' with h | h
      · exfalso; have := congrArg Fin.val h; simp at this; have := p.isLt; omega
      · exact Fin.ext (by have := congrArg Fin.val h; simp at this; omega)
    subst hpp'; subst hll'
    by_cases hjP : (pCtr j).card = 1
    · left
      have hjAP : j ∈ AP := Finset.mem_filter.mpr ⟨hjAout, hjP⟩
      refine ⟨p', Finset.mem_biUnion.mpr ⟨j, hjAP, hp'⟩, rfl, ?_⟩
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hjAP, hp'⟩, hl'⟩
    · right
      have hjAL : j ∈ AL := Finset.mem_filter.mpr ⟨hjAout, hjP⟩
      refine ⟨l', Finset.mem_biUnion.mpr ⟨j, hjAL, hl'⟩, rfl, ?_⟩
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_filter.mpr ⟨hjAL, hl'⟩, hp'⟩
  have hT_vc : ∀ p l, I p l → Fin.castAdd x2 p ∈ T ∨ Fin.natAdd x1 l ∈ T := by
    intro p l hI
    have he : (p, l) ∈ incid I := by simp [incid, hI]
    rcases hedge_cov (p, l) he with ⟨p', hp', rfl, _⟩ | ⟨l', hl', rfl, _⟩
    · exact Or.inl (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp'))
    · exact Or.inr (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hl'))
  -- Partition the gates of C into GA, GP, GLs, Gtop
  let allG := Finset.range C.gates.length
  let GA := allG.filter fun j => (gateAt C j).op = GateOp.and
  let GP := allG.filter fun j => (gateAt C j).op = GateOp.or ∧ n + j ∈ x6
  let GLs := allG.filter fun j => (gateAt C j).op = GateOp.or ∧ n + j ∈ x7
  let Gtop := allG.filter fun j => (gateAt C j).op = GateOp.or ∧ n + j ∉ x6 ∧ n + j ∉ x7
  have hx67_disj : ∀ w, w ∈ x6 → w ∈ x7 → False := by
    intro w hw6 hw7
    have h1 := (x6_pure x1 x2 C hAO x6 hx6 w hw6).1
    have h2 := (x7_pure x1 x2 C hAO x7 hx7 w hw7).1
    rw [h2] at h1
    exact Finset.not_nonempty_empty h1
  have hgates_sum : GA.card + GP.card + GLs.card + Gtop.card ≤ C.size := by
    have h1 : Disjoint GA GP := Finset.disjoint_filter.mpr fun j _ h1 h2 => by rw [h1] at h2; cases h2.1
    have h2 : Disjoint (GA ∪ GP) GLs := Finset.disjoint_left.mpr fun j hj hGL => by
      simp only [Finset.mem_union, GA, GP, GLs, Finset.mem_filter] at hj hGL
      rcases hj with hA | hP
      · rw [hA.2] at hGL; cases hGL.2.1
      · exact hx67_disj (n + j) hP.2.2 hGL.2.2
    have h3 : Disjoint (GA ∪ GP ∪ GLs) Gtop := Finset.disjoint_left.mpr fun j hj hT => by
      simp only [Finset.mem_union, GA, GP, GLs, Gtop, Finset.mem_filter] at hj hT
      rcases hj with (hA | hP) | hL
      · rw [hA.2] at hT; cases hT.2.1
      · exact hT.2.2.1 hP.2.2
      · exact hT.2.2.2 hL.2.2
    have hsub : GA ∪ GP ∪ GLs ∪ Gtop ⊆ allG := by
      intro j hj
      simp only [Finset.mem_union, GA, GP, GLs, Gtop, Finset.mem_filter] at hj
      rcases hj with ((h | h) | h) | h <;> exact h.1
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint h3, Finset.card_union_of_disjoint h2,
        Finset.card_union_of_disjoint h1, Finset.card_range] at hc
    exact hc
  -- Bound 1: Aout.card ≤ GA.card
  have hAout_le_GA : Aout.card ≤ GA.card := by
    apply Finset.card_le_card
    intro j hj
    have hja := hAout_and j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hja.1, hja.2⟩
  -- Bound 2: Aout.card ≤ Gtop.card + 1 via dag_expand
  let ch (w : ℕ) : ℕ × ℕ := ((gateAt C (w - n)).inputs.getD 0 0, (gateAt C (w - n)).inputs.getD 1 0)
  have hAout_le_Gtop : Aout.card ≤ Gtop.card + 1 := by
    let Etop := Gtop.image (fun j => n + j)
    have hEtop_card : Etop.card = Gtop.card :=
      Finset.card_image_of_injective _ (fun _ _ h => by omega)
    have hnot_in : ∀ w, w ∉ Etop → ((wireSets x1 x2 C w).2.2).card ≤ 1 := by
      intro w hw
      by_cases h1 : w < x1
      · rw [wireSets]; simp [h1]
      · by_cases h2 : w < x1 + x2
        · rw [wireSets]; simp [h1, h2]
        · by_cases h3 : w - (x1 + x2) < C.gates.length
          · let j := w - (x1 + x2)
            have hwj : w = x1 + x2 + j := by omega
            have hmem : gateAt C j ∈ C.gates := by
              simp only [gateAt, List.getD_eq_getElem _ _ (show j < C.gates.length from h3)]
              exact List.getElem_mem h3
            rcases hAO.1 (gateAt C j) hmem with hand | hor
            · rw [hwj, wireSets_and_eq x1 x2 C j h3 hand]; simp
            · by_cases h6 : w ∈ x6
              · rw [(x6_pure x1 x2 C hAO x6 hx6 w h6).2.2]; simp
              · by_cases h7 : w ∈ x7
                · rw [(x7_pure x1 x2 C hAO x7 hx7 w h7).2.2]; simp
                · exfalso; apply hw
                  exact Finset.mem_image.mpr ⟨j,
                    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h3, hor, hwj ▸ h6, hwj ▸ h7⟩, hwj.symm⟩
          · rw [wireSets]; simp [h1, h2, h3]
    have hexp := dag_expand (fun w => (wireSets x1 x2 C w).2.2) Etop ch
      (fun w hw => by
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
        have hjlt := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
        have hlt := gate_inputs_lt hAO hjlt
        simpa [ch] using hlt)
      (fun w hw => by
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
        have hjf := Finset.mem_filter.mp hj
        have hjlt := Finset.mem_range.mp hjf.1
        rw [wireSets_or_eq x1 x2 C hAO j hjlt hjf.2.1]
        simp [ch])
      (fun w _ => ⟨by by_cases h : (ch w).1 ∈ Etop; exact Or.inl h; exact Or.inr (hnot_in _ h),
                   by by_cases h : (ch w).2 ∈ Etop; exact Or.inl h; exact Or.inr (hnot_in _ h)⟩)
      {C.output}
      (fun w _ => by by_cases h : w ∈ Etop; exact Or.inl h; exact Or.inr (hnot_in _ h))
    have hb : ({C.output} : Finset ℕ).biUnion (fun w => (wireSets x1 x2 C w).2.2) = Aout := by
      ext j; simp [Aout]
    rw [hb, Finset.card_singleton, hEtop_card] at hexp
    omega
  -- Bound 3: For each p ∈ TP, count edges covered by AP(p) using disjoint GL(p) ⊆ GLs
  let GLp (p : Fin x1) : Finset ℕ :=
    GLs.filter fun j => 2 ≤ ((wireSets x1 x2 C (n + j)).2.1).card ∧
      ∀ l ∈ (wireSets x1 x2 C (n + j)).2.1, I p l
  have hGLp_disj : ∀ p ∈ TP, ∀ p' ∈ TP, p ≠ p' → Disjoint (GLp p) (GLp p') := by
    intro p _ p' _ hpp'
    rw [Finset.disjoint_left]
    intro j hjp hjp'
    have h1 := (Finset.mem_filter.mp hjp).2
    have h2 := (Finset.mem_filter.mp hjp').2
    obtain ⟨l, hl, l', hl', hll'⟩ := Finset.one_lt_card.mp (by omega : 1 < ((wireSets x1 x2 C (n + j)).2.1).card)
    exact hc4 p p' l l' hpp' hll' ⟨h1.2 l hl, h1.2 l' hl', h2.2 l hl, h2.2 l' hl'⟩
  have hAP_bound : ∀ p ∈ TP,
      ((AP.filter fun j => p ∈ pCtr j).biUnion lCtr).card + 1 ≤
        (GLp p).card + 2 * (AP.filter fun j => p ∈ pCtr j).card := by
    intro p hpTP
    let Ap := AP.filter fun j => p ∈ pCtr j
    have hAp_ne : Ap.Nonempty := by
      obtain ⟨j, hjAP, hjp⟩ := Finset.mem_biUnion.mp hpTP
      exact ⟨j, Finset.mem_filter.mpr ⟨hjAP, hjp⟩⟩
    let Ep := (GLp p).image (fun j => n + j)
    have hEp_card : Ep.card = (GLp p).card :=
      Finset.card_image_of_injective _ (fun _ _ h => by omega)
    let Wp := Ap.image (fun j => (gateAt C j).inputs.getD 0 0)
    have hWp_card : Wp.card ≤ Ap.card := Finset.card_image_le
    have hmem_ok : ∀ w, w ∈ x7 → (∀ l ∈ (wireSets x1 x2 C w).2.1, I p l) →
        w ∈ Ep ∨ ((wireSets x1 x2 C w).2.1).card ≤ 1 := by
      intro w hw7 hI
      by_cases hc : ((wireSets x1 x2 C w).2.1).card ≤ 1
      · exact Or.inr hc
      · left
        rcases hx7 w hw7 with ⟨hge, hlt⟩ | ⟨j, hjlt, rfl, hor, _⟩
        · exfalso
          have hnot : ¬ (w < x1) := by omega
          rw [wireSets] at hc; simp [hnot, hlt] at hc
        · exact Finset.mem_image.mpr ⟨j,
            Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjlt, hor, hw7⟩,
              by dsimp only [n]; omega, hI⟩, rfl⟩
    have hexp := dag_expand (fun w => (wireSets x1 x2 C w).2.1) Ep ch
      (fun w hw => by
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
        have hjlt := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1
        simpa [ch] using gate_inputs_lt hAO hjlt)
      (fun w hw => by
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
        have hjf := Finset.mem_filter.mp (Finset.mem_filter.mp hj).1
        have hjlt := Finset.mem_range.mp hjf.1
        rw [wireSets_or_eq x1 x2 C hAO j hjlt hjf.2.1]; simp [ch])
      (fun w hw => by
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
        have hj1 := Finset.mem_filter.mp hj
        have hj2 := Finset.mem_filter.mp hj1.1
        have hjlt := Finset.mem_range.mp hj2.1
        have hws := wireSets_or_eq x1 x2 C hAO j hjlt hj2.2.1
        have hpair := gate_inputs_pair hAO hjlt
        rcases hx7 (n + j) hj2.2.2 with ⟨_, hlt⟩ | ⟨j', _, heqj, _, hins⟩
        · omega
        · have hjj' : j' = j := by omega
          rw [hjj'] at hins
          have hu7 : (ch (n + j)).1 ∈ x7 := by
            simp only [ch, Nat.add_sub_cancel_left]; exact hins _ (by rw [hpair]; simp)
          have hv7 : (ch (n + j)).2 ∈ x7 := by
            simp only [ch, Nat.add_sub_cancel_left]; exact hins _ (by rw [hpair]; simp)
          have huI : ∀ l ∈ (wireSets x1 x2 C (ch (n + j)).1).2.1, I p l := fun l hl =>
            hj1.2.2 l (by rw [hws]; exact Finset.mem_union_left _ (by simpa [ch] using hl))
          have hvI : ∀ l ∈ (wireSets x1 x2 C (ch (n + j)).2).2.1, I p l := fun l hl =>
            hj1.2.2 l (by rw [hws]; exact Finset.mem_union_right _ (by simpa [ch] using hl))
          exact ⟨hmem_ok _ hu7 huI, hmem_ok _ hv7 hvI⟩)
      Wp
      (fun w hw => by
        obtain ⟨j, hjAp, rfl⟩ := Finset.mem_image.mp hw
        have hjf := Finset.mem_filter.mp hjAp
        have hjAout := (Finset.mem_filter.mp hjf.1).1
        have hja := hAout_and j hjAout
        have ha7 := (hand_eval j hja.1 hja.2).1
        exact hmem_ok _ ha7 (fun l hl => hAout_clean j hjAout p hjf.2 l hl))
    have hbiEq : Ap.biUnion lCtr = Wp.biUnion (fun w => (wireSets x1 x2 C w).2.1) := by
      ext l; simp [Wp, lCtr]
    rw [← hbiEq, hEp_card] at hexp
    have hAp_pos : 1 ≤ Ap.card := hAp_ne.card_pos
    change (Ap.biUnion lCtr).card + 1 ≤ (GLp p).card + 2 * Ap.card
    omega
  -- Bound 4: Symmetric for each l ∈ TL using disjoint GP(l) ⊆ GP
  let GPl (l : Fin x2) : Finset ℕ :=
    GP.filter fun j => 2 ≤ ((wireSets x1 x2 C (n + j)).1).card ∧
      ∀ p ∈ (wireSets x1 x2 C (n + j)).1, I p l
  have hGPl_disj : ∀ l ∈ TL, ∀ l' ∈ TL, l ≠ l' → Disjoint (GPl l) (GPl l') := by
    intro l _ l' _ hll'
    rw [Finset.disjoint_left]
    intro j hjl hjl'
    have h1 := (Finset.mem_filter.mp hjl).2
    have h2 := (Finset.mem_filter.mp hjl').2
    obtain ⟨p, hp, p', hp', hpp'⟩ := Finset.one_lt_card.mp (by omega : 1 < ((wireSets x1 x2 C (n + j)).1).card)
    exact hc4 p p' l l' hpp' hll' ⟨h1.2 p hp, h2.2 p hp, h1.2 p' hp', h2.2 p' hp'⟩
  have hAL_bound : ∀ l ∈ TL,
      ((AL.filter fun j => l ∈ lCtr j).biUnion pCtr).card + 1 ≤
        (GPl l).card + 2 * (AL.filter fun j => l ∈ lCtr j).card := by
    intro l hlTL
    let Al := AL.filter fun j => l ∈ lCtr j
    have hAl_ne : Al.Nonempty := by
      obtain ⟨j, hjAL, hjl⟩ := Finset.mem_biUnion.mp hlTL
      exact ⟨j, Finset.mem_filter.mpr ⟨hjAL, hjl⟩⟩
    let El := (GPl l).image (fun j => n + j)
    have hEl_card : El.card = (GPl l).card :=
      Finset.card_image_of_injective _ (fun _ _ h => by omega)
    let Wl := Al.image (fun j => (gateAt C j).inputs.getD 1 0)
    have hWl_card : Wl.card ≤ Al.card := Finset.card_image_le
    have hmem_ok : ∀ w, w ∈ x6 → (∀ p ∈ (wireSets x1 x2 C w).1, I p l) →
        w ∈ El ∨ ((wireSets x1 x2 C w).1).card ≤ 1 := by
      intro w hw6 hI
      by_cases hc : ((wireSets x1 x2 C w).1).card ≤ 1
      · exact Or.inr hc
      · left
        rcases hx6 w hw6 with hlt | ⟨j, hjlt, rfl, hor, _⟩
        · exfalso; rw [wireSets] at hc; simp [hlt] at hc
        · exact Finset.mem_image.mpr ⟨j,
            Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hjlt, hor, hw6⟩,
              by dsimp only [n]; omega, hI⟩, rfl⟩
    have hexp := dag_expand (fun w => (wireSets x1 x2 C w).1) El ch
      (fun w hw => by
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
        have hjlt := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1
        simpa [ch] using gate_inputs_lt hAO hjlt)
      (fun w hw => by
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
        have hjf := Finset.mem_filter.mp (Finset.mem_filter.mp hj).1
        have hjlt := Finset.mem_range.mp hjf.1
        rw [wireSets_or_eq x1 x2 C hAO j hjlt hjf.2.1]; simp [ch])
      (fun w hw => by
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
        have hj1 := Finset.mem_filter.mp hj
        have hj2 := Finset.mem_filter.mp hj1.1
        have hjlt := Finset.mem_range.mp hj2.1
        have hws := wireSets_or_eq x1 x2 C hAO j hjlt hj2.2.1
        have hpair := gate_inputs_pair hAO hjlt
        rcases hx6 (n + j) hj2.2.2 with hlt | ⟨j', _, heqj, _, hins⟩
        · omega
        · have hjj' : j' = j := by omega
          rw [hjj'] at hins
          have hu6 : (ch (n + j)).1 ∈ x6 := by
            simp only [ch, Nat.add_sub_cancel_left]; exact hins _ (by rw [hpair]; simp)
          have hv6 : (ch (n + j)).2 ∈ x6 := by
            simp only [ch, Nat.add_sub_cancel_left]; exact hins _ (by rw [hpair]; simp)
          have huI : ∀ p ∈ (wireSets x1 x2 C (ch (n + j)).1).1, I p l := fun p hp =>
            hj1.2.2 p (by rw [hws]; exact Finset.mem_union_left _ (by simpa [ch] using hp))
          have hvI : ∀ p ∈ (wireSets x1 x2 C (ch (n + j)).2).1, I p l := fun p hp =>
            hj1.2.2 p (by rw [hws]; exact Finset.mem_union_right _ (by simpa [ch] using hp))
          exact ⟨hmem_ok _ hu6 huI, hmem_ok _ hv6 hvI⟩)
      Wl
      (fun w hw => by
        obtain ⟨j, hjAl, rfl⟩ := Finset.mem_image.mp hw
        have hjf := Finset.mem_filter.mp hjAl
        have hjAout := (Finset.mem_filter.mp hjf.1).1
        have hja := hAout_and j hjAout
        have hb6 := (hand_eval j hja.1 hja.2).2.1
        exact hmem_ok _ hb6 (fun p hp => hAout_clean j hjAout p hp l hjf.2))
    have hbiEq : Al.biUnion pCtr = Wl.biUnion (fun w => (wireSets x1 x2 C w).1) := by
      ext p; simp [Wl, pCtr]
    rw [← hbiEq, hEl_card] at hexp
    have hAl_pos : 1 ≤ Al.card := hAl_ne.card_pos
    change (Al.biUnion pCtr).card + 1 ≤ (GPl l).card + 2 * Al.card
    omega
  -- Sum over TP and TL
  have hsum_AP_card : ∑ p ∈ TP, (AP.filter fun j => p ∈ pCtr j).card = AP.card := by
    have hdisj : Set.PairwiseDisjoint (TP : Set (Fin x1)) (fun p => AP.filter fun j => p ∈ pCtr j) := by
      intro p _ p' _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro j h1 h2
      have hcard1 : (pCtr j).card = 1 := (Finset.mem_filter.mp (Finset.mem_filter.mp h1).1).2
      obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hcard1
      have hp1 : p = q := Finset.mem_singleton.mp (hq ▸ (Finset.mem_filter.mp h1).2)
      have hp2 : p' = q := Finset.mem_singleton.mp (hq ▸ (Finset.mem_filter.mp h2).2)
      exact hne (hp1.trans hp2.symm)
    rw [← Finset.card_biUnion hdisj]
    congr 1
    ext j
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · rintro ⟨_, _, hjAP, _⟩; exact hjAP
    · intro hjAP
      have hcard1 : (pCtr j).card = 1 := (Finset.mem_filter.mp hjAP).2
      obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcard1
      have hpm : p ∈ pCtr j := by rw [hp]; simp
      exact ⟨p, Finset.mem_biUnion.mpr ⟨j, hjAP, hpm⟩, hjAP, hpm⟩
  have hsum_AL_card : ∑ l ∈ TL, (AL.filter fun j => l ∈ lCtr j).card = AL.card := by
    have hdisj : Set.PairwiseDisjoint (TL : Set (Fin x2)) (fun l => AL.filter fun j => l ∈ lCtr j) := by
      intro l _ l' _ hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro j h1 h2
      have hjAL := (Finset.mem_filter.mp h1).1
      have hjAout := (Finset.mem_filter.mp hjAL).1
      have hnot1 : (pCtr j).card ≠ 1 := (Finset.mem_filter.mp hjAL).2
      have hcard1 : (lCtr j).card = 1 := (hAout_star j hjAout).resolve_left hnot1
      obtain ⟨q, hq⟩ := Finset.card_eq_one.mp hcard1
      have hl1 : l = q := Finset.mem_singleton.mp (hq ▸ (Finset.mem_filter.mp h1).2)
      have hl2 : l' = q := Finset.mem_singleton.mp (hq ▸ (Finset.mem_filter.mp h2).2)
      exact hne (hl1.trans hl2.symm)
    rw [← Finset.card_biUnion hdisj]
    congr 1
    ext j
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · rintro ⟨_, _, hjAL, _⟩; exact hjAL
    · intro hjAL
      have hjAout := (Finset.mem_filter.mp hjAL).1
      have hnot1 : (pCtr j).card ≠ 1 := (Finset.mem_filter.mp hjAL).2
      have hcard1 : (lCtr j).card = 1 := (hAout_star j hjAout).resolve_left hnot1
      obtain ⟨l, hl⟩ := Finset.card_eq_one.mp hcard1
      have hlm : l ∈ lCtr j := by rw [hl]; simp
      exact ⟨l, Finset.mem_biUnion.mpr ⟨j, hjAL, hlm⟩, hjAL, hlm⟩
  have hsum_GL : ∑ p ∈ TP, (GLp p).card ≤ GLs.card := by
    rw [← Finset.card_biUnion (fun p hp p' hp' hne => hGLp_disj p hp p' hp' hne)]
    exact Finset.card_le_card (Finset.biUnion_subset.mpr fun p _ => Finset.filter_subset _ _)
  have hsum_GP : ∑ l ∈ TL, (GPl l).card ≤ GP.card := by
    rw [← Finset.card_biUnion (fun l hl l' hl' hne => hGPl_disj l hl l' hl' hne)]
    exact Finset.card_le_card (Finset.biUnion_subset.mpr fun l _ => Finset.filter_subset _ _)
  -- Bound |incid I| by sum of star sizes
  have hincid_le : (incid I).card ≤
      (∑ p ∈ TP, ((AP.filter fun j => p ∈ pCtr j).biUnion lCtr).card) +
      (∑ l ∈ TL, ((AL.filter fun j => l ∈ lCtr j).biUnion pCtr).card) := by
    let covP : Finset (Fin x1 × Fin x2) :=
      TP.biUnion fun p => ((AP.filter fun j => p ∈ pCtr j).biUnion lCtr).image fun l => (p, l)
    let covL : Finset (Fin x1 × Fin x2) :=
      TL.biUnion fun l => ((AL.filter fun j => l ∈ lCtr j).biUnion pCtr).image fun p => (p, l)
    have hsub : incid I ⊆ covP ∪ covL := by
      intro e he
      rcases hedge_cov e he with ⟨p, hpTP, hpEq, hlMem⟩ | ⟨l, hlTL, hlEq, hpMem⟩
      · apply Finset.mem_union_left
        refine Finset.mem_biUnion.mpr ⟨p, hpTP, Finset.mem_image.mpr ⟨e.2, hlMem, Prod.ext hpEq.symm rfl⟩⟩
      · apply Finset.mem_union_right
        refine Finset.mem_biUnion.mpr ⟨l, hlTL, Finset.mem_image.mpr ⟨e.1, hpMem, Prod.ext rfl hlEq.symm⟩⟩
    have hc1 := Finset.card_le_card hsub
    have hc2 := Finset.card_union_le covP covL
    have hcP : covP.card ≤ ∑ p ∈ TP, ((AP.filter fun j => p ∈ pCtr j).biUnion lCtr).card := by
      calc covP.card
          ≤ ∑ p ∈ TP, (((AP.filter fun j => p ∈ pCtr j).biUnion lCtr).image fun l => (p, l)).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ p ∈ TP, ((AP.filter fun j => p ∈ pCtr j).biUnion lCtr).card :=
            Finset.sum_le_sum fun _ _ => Finset.card_image_le
    have hcL : covL.card ≤ ∑ l ∈ TL, ((AL.filter fun j => l ∈ lCtr j).biUnion pCtr).card := by
      calc covL.card
          ≤ ∑ l ∈ TL, (((AL.filter fun j => l ∈ lCtr j).biUnion pCtr).image fun p => (p, l)).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ l ∈ TL, ((AL.filter fun j => l ∈ lCtr j).biUnion pCtr).card :=
            Finset.sum_le_sum fun _ _ => Finset.card_image_le
    omega
  have hsumP := Finset.sum_le_sum hAP_bound
  have hsumL := Finset.sum_le_sum hAL_bound
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, ← Finset.mul_sum] at hsumP hsumL
  rw [hsum_AP_card] at hsumP
  rw [hsum_AL_card] at hsumL
  refine ⟨T, hT_vc, ?_⟩
  omega

end PEqualNP.Outside.L_meta_4990

theorem PEqualNP.Outside.L_meta_4990 :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [_x4 : DecidableRel x3]
      (x5 : PEqualNP.CircuitLowerBounds.Circuit) (x6 x7 : Finset ℕ),
      (∀ (x8 x9 : Fin x1) (x10 x11 : Fin x2), x8 ≠ x9 → x10 ≠ x11 →
        ¬(x3 x8 x10 ∧ x3 x8 x11 ∧ x3 x9 x10 ∧ x3 x9 x11)) →
      PEqualNP.TopForm.IsAO2 (x1 + x2) x5 →
      (∀ (x10 : Fin (x1 + x2) → Bool),
        PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x10 =
          Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x2),
            x3 x11 x12 ∧ x10 (Fin.castAdd x2 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) →
      (∀ x11 ∈ x6, x11 < x1 ∨ ∃ x13 < x5.gates.length, x11 = x1 + x2 + x13 ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x13).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        ∀ x14 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x13).inputs, x14 ∈ x6) →
      (∀ x12 ∈ x7, x1 ≤ x12 ∧ x12 < x1 + x2 ∨ ∃ x14 < x5.gates.length, x12 = x1 + x2 + x14 ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x14).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        ∀ x15 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x14).inputs, x15 ∈ x7) →
      (∀ x13 < x5.gates.length,
        (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x13).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        ∃ (x16 : ℕ) (x17 : ℕ),
          (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x13).inputs = [x16, x17] ∧ x16 ∈ x7 ∧ x17 ∈ x6) →
      ∃ (x14 : Finset (Fin (x1 + x2))),
        (∀ (x15 : Fin x1) (x16 : Fin x2), x3 x15 x16 → Fin.castAdd x2 x15 ∈ x14 ∨ Fin.natAdd x1 x16 ∈ x14) ∧
        (PEqualNP.ReadTwo.incid x3).card + x14.card ≤ x5.size + (1 : ℕ) :=
  PEqualNP.Outside.L_meta_4990.main_proof
