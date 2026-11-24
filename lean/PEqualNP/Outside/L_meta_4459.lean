import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4459

open PEqualNP PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD (i : ℕ) false = x i := by simp

def Bld (n : ℕ) (F : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∀ m, n ≤ m → ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length ≤ s ∧
    out < m + gs.length ∧ ∀ w : List Bool, w.length = m →
      (wiresFrom gs w).getD out false = F (fun i => w.getD i false)

theorem bld_mono {n : ℕ} {F : (Fin n → Bool) → Bool} {s s' : ℕ} (h : Bld n F s) (hs : s ≤ s') :
    Bld n F s' := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, le_trans len hs, ho, ev⟩

theorem bld_congr {n : ℕ} {F H : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s)
    (e : ∀ x, F x = H x) : Bld n H s := by
  intro m hm
  obtain ⟨gs, out, ok, len, ho, ev⟩ := h m hm
  exact ⟨gs, out, ok, len, ho, fun w hw => by rw [ev w hw, e]⟩

theorem bld_var {n : ℕ} (i : Fin n) : Bld n (fun x => x i) 0 := by
  intro m hm
  refine ⟨[], i, by simp, le_rfl, by simp; omega, ?_⟩
  intro w _
  simp [wiresFrom]

theorem bld_bin {n : ℕ} (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (c : Bool → Bool → Bool) (hc : ∀ a b, op.eval [a, b] = c a b)
    {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1) (h2 : Bld n H s2) :
    Bld n (fun x => c (F x) (H x)) (s1 + s2 + 1) := by
  intro m hm
  obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ := h1 m hm
  obtain ⟨gs2, o2, ok2, len2, ho2, ev2⟩ := h2 (m + gs1.length) (by omega)
  refine ⟨gs1 ++ gs2 ++ [⟨op, [o1, o2]⟩], m + gs1.length + gs2.length, ?_, ?_, ?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact ok1 g hg
    · exact ok2 g hg
    · subst hg; rcases hop with h | h <;> simp [Ok, h]
  · simp; omega
  · simp; omega
  · intro w hw
    rw [wiresFrom_append, wiresFrom_append]
    set v := wiresFrom gs1 w with hv
    have lv : v.length = m + gs1.length := by rw [hv, length_wiresFrom, hw]
    set u := wiresFrom gs2 v with hu
    have lu : u.length = m + gs1.length + gs2.length := by rw [hu, length_wiresFrom, lv]
    have step : wiresFrom [⟨op, [o1, o2]⟩] u
        = u ++ [op.eval ([o1, o2].map fun i => u.getD i false)] := rfl
    rw [step, ← lu, getD_snoc_eq]
    simp only [List.map_cons, List.map_nil, hc]
    have e1 : u.getD o1 false = F (fun i => w.getD i false) := by
      rw [hu, getD_wiresFrom _ _ _ (by omega), hv, ev1 w hw]
    have e2 : u.getD o2 false = H (fun i => w.getD i false) := by
      rw [hu, ev2 v lv]
      congr 1
      funext i
      rw [hv, getD_wiresFrom _ _ _ (by have := i.2; omega)]
    rw [e1, e2]

theorem bld_or {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x || H x) (s1 + s2 + 1) :=
  bld_bin GateOp.or (Or.inr rfl) (· || ·) (by intro a b; simp [GateOp.eval]) h1 h2

theorem bld_and {n : ℕ} {F H : (Fin n → Bool) → Bool} {s1 s2 : ℕ} (h1 : Bld n F s1)
    (h2 : Bld n H s2) : Bld n (fun x => F x && H x) (s1 + s2 + 1) :=
  bld_bin GateOp.and (Or.inl rfl) (· && ·) (by intro a b; simp [GateOp.eval]) h1 h2

theorem bld_hasCircuitSize {n : ℕ} {F : (Fin n → Bool) → Bool} {s : ℕ} (h : Bld n F s) :
    HasCircuitSize n F s := by
  obtain ⟨gs, out, ok, len, _, ev⟩ := h n le_rfl
  refine ⟨⟨gs, out⟩, ok, len, ?_⟩
  intro x
  have e := ev (List.ofFn x) (by simp)
  simp only [Circuit.eval, wires_eq, e]
  congr 1
  funext i
  exact getD_ofFn x i

theorem bld_anyList {n : ℕ} (vs : List (Fin n)) : ∀ v : Fin n,
    Bld n (fun x => (v :: vs).any fun j => x j) vs.length := by
  induction vs with
  | nil => intro v; exact bld_congr (bld_var v) (by intro x; simp)
  | cons w ws ih =>
    intro v
    have := bld_or (bld_var v) (ih w)
    refine bld_congr (bld_mono this (by simp)) ?_
    intro x
    simp

theorem bld_anyFinset {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) :
    Bld n (fun x => decide (∃ v ∈ S, x v = true)) (S.card - 1) := by
  obtain ⟨v, vs, hl⟩ : ∃ v vs, S.toList = v :: vs := by
    cases h : S.toList with
    | nil => simp at h; exact absurd h hS.ne_empty
    | cons v vs => exact ⟨v, vs, rfl⟩
  have hc : S.card = vs.length + 1 := by rw [← Finset.length_toList, hl]; rfl
  refine bld_congr (bld_mono (bld_anyList vs v) (by omega)) ?_
  intro x
  rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hl, List.any_eq_true]
  simp

theorem bld_edges (n : ℕ) (T : Finset (Fin n)) : ∀ E : Finset (Sym2 (Fin n)), E.Nonempty →
    (∀ e ∈ E, ∃ t ∈ T, t ∈ e) →
    Bld n (fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true)) (E.card + T.card - 1) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro E hE hc
    obtain ⟨e, he⟩ := hE
    obtain ⟨t, ht, _⟩ := hc e he
    simp at ht
  | @insert t T0 htT ih =>
    intro E hE hc
    set E1 := E.filter (fun e => t ∈ e) with hE1
    set E2 := E.filter (fun e => t ∉ e) with hE2
    have hsplit : E1.card + E2.card = E.card := Finset.card_filter_add_card_filter_not _
    have hcard : (insert t T0).card = T0.card + 1 := Finset.card_insert_of_notMem htT
    have c2 : ∀ e ∈ E2, ∃ t' ∈ T0, t' ∈ e := by
      intro e he
      rw [hE2, Finset.mem_filter] at he
      obtain ⟨t', ht', hte⟩ := hc e he.1
      rcases Finset.mem_insert.1 ht' with h | h
      · subst h; exact absurd hte he.2
      · exact ⟨t', h, hte⟩
    set S := Finset.univ.filter (fun v : Fin n => s(t, v) ∈ E1) with hS
    have hSc : S.card ≤ E1.card := by
      refine Finset.card_le_card_of_injOn (fun v => s(t, v)) ?_ ?_
      · intro v hv
        simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv
        exact hv
      · intro a _ b _ hab
        exact Sym2.congr_right.1 hab
    have star : E1.Nonempty → Bld n (fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true))
        E1.card := by
      intro h1
      have hSne : S.Nonempty := by
        obtain ⟨e, he⟩ := h1
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        exact ⟨b, by simp [hS, ← hb, he]⟩
      have := bld_and (bld_var t) (bld_anyFinset S hSne)
      have hpos := hSne.card_pos
      refine bld_congr (bld_mono this (by omega)) ?_
      intro x
      rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
      constructor
      · rintro ⟨ht, v, hv, hxv⟩
        refine ⟨s(t, v), (Finset.mem_filter.1 hv).2, ?_⟩
        intro u hu
        rcases Sym2.mem_iff.1 hu with rfl | rfl <;> assumption
      · rintro ⟨e, he, hall⟩
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        subst hb
        exact ⟨hall t (Sym2.mem_mk_left _ _), b, by simp [hS, he],
          hall b (Sym2.mem_mk_right _ _)⟩
    have key : ∀ x : Fin n → Bool, decide (∃ e ∈ E, ∀ v ∈ e, x v = true)
        = (decide (∃ e ∈ E1, ∀ v ∈ e, x v = true) || decide (∃ e ∈ E2, ∀ v ∈ e, x v = true)) := by
      intro x
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_iff, hE1, hE2, Finset.mem_filter]
      constructor
      · rintro ⟨e, he, h⟩
        by_cases hte : t ∈ e
        · exact Or.inl ⟨e, ⟨he, hte⟩, h⟩
        · exact Or.inr ⟨e, ⟨he, hte⟩, h⟩
      · rintro (⟨e, ⟨he, _⟩, h⟩ | ⟨e, ⟨he, _⟩, h⟩) <;> exact ⟨e, he, h⟩
    rw [hcard]
    by_cases h1 : E1.Nonempty
    · by_cases h2 : E2.Nonempty
      · have := bld_or (star h1) (ih E2 h2 c2)
        have hp := h2.card_pos
        refine bld_congr (bld_mono this (by omega)) ?_
        intro x
        rw [key]
      · rw [Finset.not_nonempty_iff_eq_empty] at h2
        refine bld_congr (bld_mono (star h1) (by omega)) ?_
        intro x
        rw [key, h2]
        simp
    · rw [Finset.not_nonempty_iff_eq_empty] at h1
      have h2 : E2.Nonempty := by
        by_contra h2
        rw [Finset.not_nonempty_iff_eq_empty] at h2
        have := hE.card_pos
        rw [h1, h2] at hsplit
        simp at hsplit
        omega
      refine bld_congr (bld_mono (ih E2 h2 c2) (by omega)) ?_
      intro x
      rw [key, h1]
      simp

theorem edge_bld (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n))
    (hE : ∃ i j : Fin n, G.Adj i j) (hc : ∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) :
    Bld n (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true))
      (G.edgeFinset.card + T.card - 1) := by
  obtain ⟨i0, j0, h0⟩ := hE
  have hne : G.edgeFinset.Nonempty := ⟨s(i0, j0), by simpa using h0⟩
  have cov : ∀ e ∈ G.edgeFinset, ∃ t ∈ T, t ∈ e := by
    intro e
    refine Sym2.ind (fun a b => ?_) e
    intro he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    rcases hc a b he with h | h
    · exact ⟨a, h, Sym2.mem_mk_left _ _⟩
    · exact ⟨b, h, Sym2.mem_mk_right _ _⟩
  refine bld_congr (bld_edges n T G.edgeFinset hne cov) ?_
  intro x
  rw [decide_eq_decide]
  constructor
  · rintro ⟨e, he, h⟩
    revert he h
    refine Sym2.ind (fun a b => ?_) e
    intro he h
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    exact ⟨a, b, he, h a (Sym2.mem_mk_left _ _), h b (Sym2.mem_mk_right _ _)⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    refine ⟨s(i, j), by simpa using hij, ?_⟩
    intro v hv
    rcases Sym2.mem_iff.1 hv with rfl | rfl <;> assumption

theorem main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n))
    (hcol : G.Colorable 2)
    (hdeg : ∀ v ∉ A, (G.neighborSet v).ncard = 3)
    (hA : ∀ u v : Fin n, G.Adj u v → u ∉ A)
    (hedge : ∃ u v : Fin n, G.Adj u v) :
    ∃ u v : Fin n, u ∉ A ∧ v ∉ A ∧ u ≠ v ∧ ¬ G.Adj u v ∧
      ∃ s : ℕ, s + 8 ≤ 2 * (n - A.card) - 1 ∧
        HasCircuitSize n (fun x : Fin n → Bool =>
          graphFun G ∅ (Function.update (Function.update x u false) v false)) s := by
  classical
  let col : G.Coloring (Fin 2) := Classical.choice hcol
  let V : Finset (Fin n) := Finset.univ \ A
  let L : Finset (Fin n) := V.filter (fun v => col v = 0)
  let R : Finset (Fin n) := V.filter (fun v => col v = 1)
  have hVcard : V.card = n - A.card := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    change V.card + A.card = n at h
    omega
  have hcol_cases : ∀ v : Fin n, col v = 0 ∨ col v = 1 := by
    intro v
    have hlt : (col v).val < 2 := (col v).isLt
    have h01 : (col v).val = 0 ∨ (col v).val = 1 := by omega
    rcases h01 with h0 | h1
    · exact Or.inl (Fin.ext h0)
    · exact Or.inr (Fin.ext h1)
  have hLR_disj : Disjoint L R := by
    rw [Finset.disjoint_left]
    intro v hvL hvR
    have h0 : col v = 0 := (Finset.mem_filter.1 hvL).2
    have h1 : col v = 1 := (Finset.mem_filter.1 hvR).2
    rw [h0] at h1
    exact absurd h1 (by decide)
  have hLR_union : L ∪ R = V := by
    ext v
    simp only [L, R, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hV, _⟩ | ⟨hV, _⟩) <;> exact hV
    · intro hV
      rcases hcol_cases v with h0 | h1
      · exact Or.inl ⟨hV, h0⟩
      · exact Or.inr ⟨hV, h1⟩
  have hLR_sum : L.card + R.card = n - A.card := by
    rw [← Finset.card_union_of_disjoint hLR_disj, hLR_union, hVcard]
  have hnbr_card : ∀ v ∉ A, (G.neighborFinset v).card = 3 := by
    intro v hv
    rw [← Set.ncard_coe_finset, SimpleGraph.coe_neighborFinset]
    exact hdeg v hv
  let incE : Fin n → Finset (Sym2 (Fin n)) :=
    fun a => (G.neighborFinset a).image (fun b => s(a, b))
  have hincE_card : ∀ a ∉ A, (incE a).card = 3 := by
    intro a ha
    rw [Finset.card_image_of_injective _ (fun b1 b2 h => Sym2.congr_right.1 h)]
    exact hnbr_card a ha
  have hcolor_side : ∀ c : Fin 2,
      G.edgeFinset.card = 3 * (V.filter (fun v => col v = c)).card := by
    intro c
    let S := V.filter (fun v => col v = c)
    have hdisj : Set.PairwiseDisjoint (S : Set (Fin n)) incE := by
      intro a1 ha1 a2 ha2 hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro e he1 he2
      obtain ⟨b1, hb1, rfl⟩ := Finset.mem_image.1 he1
      obtain ⟨b2, hb2, heq⟩ := Finset.mem_image.1 he2
      have h1 : col a1 = c := (Finset.mem_filter.1 ha1).2
      have h2 : col a2 = c := (Finset.mem_filter.1 ha2).2
      have hadj2 : G.Adj a2 b2 := (SimpleGraph.mem_neighborFinset G a2 b2).1 hb2
      have hmem : a1 ∈ s(a2, b2) := by rw [heq]; exact Sym2.mem_mk_left _ _
      rcases Sym2.mem_iff.1 hmem with rfl | rfl
      · exact hne rfl
      · exact col.valid hadj2 (h2.trans h1.symm)
    have heqE : S.biUnion incE = G.edgeFinset := by
      ext e
      refine Sym2.ind (fun x y => ?_) e
      simp only [Finset.mem_biUnion, incE, Finset.mem_image, SimpleGraph.mem_neighborFinset,
        SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, S, V, Finset.mem_filter,
        Finset.mem_sdiff, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨a, _, b, hab, heq⟩
        have : s(x, y) = s(a, b) := heq.symm
        rcases Sym2.eq_iff.1 this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hab
        · exact G.adj_symm hab
      · intro hxy
        have hxA : x ∉ A := hA x y hxy
        have hyA : y ∉ A := hA y x (G.adj_symm hxy)
        have hcolne : col x ≠ col y := col.valid hxy
        have hside : col x = c ∨ col y = c := by
          fin_cases c <;> rcases hcol_cases x with hx | hx <;> rcases hcol_cases y with hy | hy <;>
            simp_all
        rcases hside with hx | hy
        · exact ⟨x, ⟨hxA, hx⟩, y, hxy, rfl⟩
        · exact ⟨y, ⟨hyA, hy⟩, x, G.adj_symm hxy, Sym2.eq_swap⟩
    rw [← heqE, Finset.card_biUnion hdisj]
    have hterm : ∀ a ∈ S, (incE a).card = 3 := fun a ha =>
      hincE_card a (Finset.mem_sdiff.1 (Finset.mem_filter.1 ha).1).2
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  have hE_L : G.edgeFinset.card = 3 * L.card := hcolor_side 0
  have hE_R : G.edgeFinset.card = 3 * R.card := hcolor_side 1
  have hLR_eq : L.card = R.card := by omega
  have hL_ge3 : 3 ≤ L.card := by
    obtain ⟨a0, b0, hab0⟩ := hedge
    have hcolne : col a0 ≠ col b0 := col.valid hab0
    have hexR : ∃ w ∈ R, True := by
      rcases hcol_cases a0 with ha | ha
      · rcases hcol_cases b0 with hb | hb
        · exact absurd (ha.trans hb.symm) hcolne
        · exact ⟨b0, Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hA b0 a0 (G.adj_symm hab0)⟩, hb⟩, trivial⟩
      · exact ⟨a0, Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hA a0 b0 hab0⟩, ha⟩, trivial⟩
    obtain ⟨w, hwR, _⟩ := hexR
    have hwA : w ∉ A := (Finset.mem_sdiff.1 (Finset.mem_filter.1 hwR).1).2
    have hw1 : col w = 1 := (Finset.mem_filter.1 hwR).2
    have hsub : G.neighborFinset w ⊆ L := by
      intro z hz
      have hwz : G.Adj w z := (SimpleGraph.mem_neighborFinset G w z).1 hz
      have hzA : z ∉ A := hA z w (G.adj_symm hwz)
      have hz0 : col z = 0 := by
        rcases hcol_cases z with h0 | h1
        · exact h0
        · exact absurd (hw1.trans h1.symm) (col.valid hwz)
      exact Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hzA⟩, hz0⟩
    calc 3 = (G.neighborFinset w).card := (hnbr_card w hwA).symm
      _ ≤ L.card := Finset.card_le_card hsub
  -- Pick two distinct vertices u, v ∈ L
  have hL_pos : L.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨u, huL⟩ := hL_pos
  have hLu_pos : (L.erase u).Nonempty := Finset.card_pos.1 (by rw [Finset.card_erase_of_mem huL]; omega)
  obtain ⟨v, hvLu⟩ := hLu_pos
  have hvne : v ≠ u := (Finset.mem_erase.1 hvLu).1
  have hvL : v ∈ L := (Finset.mem_erase.1 hvLu).2
  have huA : u ∉ A := (Finset.mem_sdiff.1 (Finset.mem_filter.1 huL).1).2
  have hvA : v ∉ A := (Finset.mem_sdiff.1 (Finset.mem_filter.1 hvL).1).2
  have hu0 : col u = 0 := (Finset.mem_filter.1 huL).2
  have hv0 : col v = 0 := (Finset.mem_filter.1 hvL).2
  have hnotAdj : ¬ G.Adj u v := fun hadj => col.valid hadj (hu0.trans hv0.symm)
  -- Remaining graph H = G - {u, v}
  let H : SimpleGraph (Fin n) :=
    { Adj := fun x y => G.Adj x y ∧ x ≠ u ∧ x ≠ v ∧ y ≠ u ∧ y ≠ v
      symm := ⟨fun _ _ ⟨h1, h2, h3, h4, h5⟩ => ⟨G.adj_symm h1, h4, h5, h2, h3⟩⟩
      loopless := ⟨fun x ⟨h1, _⟩ => G.loopless.irrefl x h1⟩ }
  let L' : Finset (Fin n) := (L.erase u).erase v
  have hL'card : L'.card = L.card - 2 := by
    rw [Finset.card_erase_of_mem hvLu, Finset.card_erase_of_mem huL]
    omega
  have hL'cov : ∀ x y : Fin n, H.Adj x y → x ∈ L' ∨ y ∈ L' := by
    intro x y ⟨hxy, hxu, hxv, hyu, hyv⟩
    have hxA : x ∉ A := hA x y hxy
    have hyA : y ∉ A := hA y x (G.adj_symm hxy)
    have hcolne : col x ≠ col y := col.valid hxy
    rcases hcol_cases x with hx0 | hx1
    · left
      exact Finset.mem_erase.2 ⟨hxv, Finset.mem_erase.2 ⟨hxu,
        Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hxA⟩, hx0⟩⟩⟩
    · right
      have hy0 : col y = 0 := by
        rcases hcol_cases y with h0 | h1
        · exact h0
        · exact absurd (hx1.trans h1.symm) hcolne
      exact Finset.mem_erase.2 ⟨hyv, Finset.mem_erase.2 ⟨hyu,
        Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hyA⟩, hy0⟩⟩⟩
  have hHedges : H.edgeFinset = L'.biUnion incE := by
    ext e
    refine Sym2.ind (fun x y => ?_) e
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Finset.mem_biUnion,
      incE, Finset.mem_image, SimpleGraph.mem_neighborFinset]
    constructor
    · intro hHxy
      obtain ⟨hxy, hxu, hxv, hyu, hyv⟩ := hHxy
      rcases hL'cov x y ⟨hxy, hxu, hxv, hyu, hyv⟩ with hxL' | hyL'
      · exact ⟨x, hxL', y, hxy, rfl⟩
      · exact ⟨y, hyL', x, G.adj_symm hxy, Sym2.eq_swap⟩
    · rintro ⟨a, haL', b, hab, heq⟩
      have haL : a ∈ L := (Finset.mem_erase.1 (Finset.mem_erase.1 haL').2).2
      have hau : a ≠ u := (Finset.mem_erase.1 (Finset.mem_erase.1 haL').2).1
      have hav : a ≠ v := (Finset.mem_erase.1 haL').1
      have ha0 : col a = 0 := (Finset.mem_filter.1 haL).2
      have hb1 : col b ≠ 0 := fun h0 => col.valid hab (ha0.trans h0.symm)
      have hbu : b ≠ u := fun h => hb1 (h ▸ hu0)
      have hbv : b ≠ v := fun h => hb1 (h ▸ hv0)
      have hHab : H.Adj a b := ⟨hab, hau, hav, hbu, hbv⟩
      have : s(x, y) = s(a, b) := heq.symm
      rcases Sym2.eq_iff.1 this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hHab
      · exact H.adj_symm hHab
  have hHcard : H.edgeFinset.card = 3 * (L.card - 2) := by
    have hdisj : Set.PairwiseDisjoint (L' : Set (Fin n)) incE := by
      intro a1 ha1 a2 ha2 hne
      dsimp only [Function.onFun]
      rw [Finset.disjoint_left]
      intro e he1 he2
      obtain ⟨b1, hb1, rfl⟩ := Finset.mem_image.1 he1
      obtain ⟨b2, hb2, heq⟩ := Finset.mem_image.1 he2
      have h1 : col a1 = 0 := (Finset.mem_filter.1 (Finset.mem_erase.1 (Finset.mem_erase.1 ha1).2).2).2
      have h2 : col a2 = 0 := (Finset.mem_filter.1 (Finset.mem_erase.1 (Finset.mem_erase.1 ha2).2).2).2
      have hadj2 : G.Adj a2 b2 := (SimpleGraph.mem_neighborFinset G a2 b2).1 hb2
      have hmem : a1 ∈ s(a2, b2) := by rw [heq]; exact Sym2.mem_mk_left _ _
      rcases Sym2.mem_iff.1 hmem with rfl | rfl
      · exact hne rfl
      · exact col.valid hadj2 (h2.trans h1.symm)
    rw [hHedges, Finset.card_biUnion hdisj]
    have hterm : ∀ a ∈ L', (incE a).card = 3 := fun a ha =>
      hincE_card a (Finset.mem_sdiff.1 (Finset.mem_filter.1
        (Finset.mem_erase.1 (Finset.mem_erase.1 ha).2).2).1).2
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, smul_eq_mul, hL'card, Nat.mul_comm]
  have hH_has_edge : ∃ x y : Fin n, H.Adj x y := by
    have hne : H.edgeFinset.Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨e, he⟩ := hne
    revert he
    refine Sym2.ind (fun x y he => ⟨x, y, SimpleGraph.mem_edgeFinset.1 he⟩) e
  have hfun_eq : ∀ x : Fin n → Bool,
      decide (∃ i j : Fin n, H.Adj i j ∧ x i = true ∧ x j = true) =
      graphFun G ∅ (Function.update (Function.update x u false) v false) := by
    intro x
    unfold graphFun
    simp only [Finset.notMem_empty, false_and, exists_false, decide_false, Bool.false_or]
    rw [decide_eq_decide]
    constructor
    · rintro ⟨i, j, ⟨hij, hiu, hiv, hju, hjv⟩, hi, hj⟩
      refine ⟨i, j, hij, ?_, ?_⟩
      · rw [Function.update_of_ne hiv, Function.update_of_ne hiu]; exact hi
      · rw [Function.update_of_ne hjv, Function.update_of_ne hju]; exact hj
    · rintro ⟨i, j, hij, hi, hj⟩
      have hiv : i ≠ v := by intro e; subst e; simp at hi
      have hiu : i ≠ u := by intro e; subst e; rw [Function.update_of_ne hiv, Function.update_self] at hi; exact Bool.noConfusion hi
      have hjv : j ≠ v := by intro e; subst e; simp at hj
      have hju : j ≠ u := by intro e; subst e; rw [Function.update_of_ne hjv, Function.update_self] at hj; exact Bool.noConfusion hj
      rw [Function.update_of_ne hiv, Function.update_of_ne hiu] at hi
      rw [Function.update_of_ne hjv, Function.update_of_ne hju] at hj
      exact ⟨i, j, ⟨hij, hiu, hiv, hju, hjv⟩, hi, hj⟩
  have hBld := bld_congr (edge_bld n H L' hH_has_edge hL'cov) hfun_eq
  refine ⟨u, v, huA, hvA, hvne.symm, hnotAdj, H.edgeFinset.card + L'.card - 1, ?_,
    bld_hasCircuitSize hBld⟩
  omega

end PEqualNP.Outside.L_meta_4459

theorem PEqualNP.Outside.L_meta_4459 : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)), x2.Colorable (2 : ℕ) → (∀ x6 ∉ x4, (x2.neighborSet x6).ncard = (3 : ℕ)) → (∀ (x7 : Fin x1) (x8 : x2.Walk x7 x7), x8.IsCycle → (7 : ℕ) ≤ x8.length) → (∀ (x8 x9 : Fin x1), x2.Adj x8 x9 → x8 ∉ x4) → (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10) → ∃ (x10 : Fin x1) (x11 : Fin x1), x10 ∉ x4 ∧ x11 ∉ x4 ∧ x10 ≠ x11 ∧ ¬x2.Adj x10 x11 ∧ ∃ (x12 : ℕ), x12 + (8 : ℕ) ≤ (2 : ℕ) * (x1 - x4.card) - (1 : ℕ) ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x13 : Fin x1 → Bool) => PEqualNP.MetaComplexity.NestedCover.graphFun x2 ∅ (Function.update (Function.update x13 x10 Bool.false) x11 Bool.false)) x12 := by
  intro n G _ A hcol hdeg _ hA hedge
  exact PEqualNP.Outside.L_meta_4459.main n G A hcol hdeg hA hedge
