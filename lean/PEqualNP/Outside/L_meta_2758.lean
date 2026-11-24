import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.List.Sublists
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_2758
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

def Live (target : Sig) (k t : Nat) (S : Finset Sig) : Prop :=
  ∀ M : Nat → Nat → Finset Sig → Prop,
  (∀ (hp : proper target), M 0 0 {target}) →
  (∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a) (hf : neg a ∉ insert a U) (tail : M k t (insert (neg a) U)), M (k+1) (t+1) (insert a U)) →
  (∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} (ha : proper a) (hb : proper b) (hab : a ≠ b) (hf : bin d a b ∉ insert a (insert b U)) (tail : M k t (insert (bin d a b) U)), M (k+1) t (insert a (insert b U))) → M k t S
theorem Live.stop {target : Sig} : ∀ (hp : proper target), Live target 0 0 {target} := by
  intro hp
  intro M stopStep unaryStep binaryStep
  exact stopStep hp
theorem Live.unary {target : Sig} : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a) (hf : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)), Live target (k+1) (t+1) (insert a U) := by
  intro k t  U  a  ha hf tail
  intro M stopStep unaryStep binaryStep
  exact unaryStep ha hf (tail M stopStep unaryStep binaryStep)
theorem Live.binary {target : Sig} : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} (ha : proper a) (hb : proper b) (hab : a ≠ b) (hf : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)), Live target (k+1) t (insert a (insert b U)) := by
  intro k t  U  a b  d  ha hb hab hf tail
  intro M stopStep unaryStep binaryStep
  exact binaryStep ha hb hab hf (tail M stopStep unaryStep binaryStep)
theorem Live.weakInduct {target : Sig} {M : Nat → Nat → Finset Sig → Prop} {k t : Nat} {S : Finset Sig} (h : Live target k t S)
    (stop : ∀ (hp : proper target), M 0 0 {target})
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a) (hf : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) (ih : M k t (insert (neg a) U)), M (k+1) (t+1) (insert a U))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} (ha : proper a) (hb : proper b) (hab : a ≠ b) (hf : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) (ih : M k t (insert (bin d a b) U)), M (k+1) t (insert a (insert b U)))
    : M k t S := by
  apply And.right (a := Live target k t S)
  apply h (fun k t S => Live target k t S ∧ M k t S)
  · intro hp
    exact ⟨Live.stop hp, stop hp ⟩
  · intro k t  U  a  ha hf tail
    exact ⟨Live.unary ha hf tail.1, unary ha hf tail.1 tail.2⟩
  · intro k t  U  a b  d  ha hb hab hf tail
    exact ⟨Live.binary ha hb hab hf tail.1, binary ha hb hab hf tail.1 tail.2⟩
theorem Live.induct {target : Sig} {M : ∀ (k t : Nat) (S : Finset Sig), Live target k t S → Prop} {k t : Nat} {S : Finset Sig} (h : Live target k t S)
    (stop : ∀ (hp : proper target), M 0 0 {target} (Live.stop hp))
    (unary : ∀ {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a) (hf : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) (ih : M k t (insert (neg a) U) tail), M (k+1) (t+1) (insert a U) (Live.unary ha hf tail))
    (binary : ∀ {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool} (ha : proper a) (hb : proper b) (hab : a ≠ b) (hf : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) (ih : M k t (insert (bin d a b) U) tail), M (k+1) t (insert a (insert b U)) (Live.binary ha hb hab hf tail))
    : M k t S h := by
  apply Live.weakInduct (M := fun k t S => ∀ z, M k t S z) h _ _ _ h
  · intro hp z
    exact stop hp 
  · intro k t  U  a  ha hf tail ih z
    exact unary ha hf tail (ih tail)
  · intro k t  U  a b  d  ha hb hab hf tail ih z
    exact binary ha hb hab hf tail (ih tail)


private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h using Live.induct with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h using Live.induct with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩


def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)



private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live target k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live target k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]




abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop := v ∈ pool ∨ Constant v

def supply {R} (pool xs : List (Wire R)) := ∀ a ∈ xs, Available pool a

def Reach {R : Type} (roots : List (Wire R)) (p : Nat) (bank : List (Wire R)) : Prop :=
  ∀ M : Nat → List (Wire R) → Prop,
  (M 0 roots) →
  (∀ {p : Nat} {bank : List (Wire R)} {a : Wire R} (tail : M p bank) (ha : Available bank a), M (p+1) (inv a :: bank)) →
  (∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool) (tail : M p bank) (ha : Available bank a) (hb : Available bank b), M (p+1) (combine op a b :: bank)) → M p bank
theorem Reach.start {R : Type} {roots : List (Wire R)} : Reach roots 0 roots := by
  intro M startStep oneStep twoStep
  exact startStep 
theorem Reach.one {R : Type} {roots : List (Wire R)} : ∀ {p : Nat} {bank : List (Wire R)} {a : Wire R} (tail : Reach roots p bank) (ha : Available bank a), Reach roots (p+1) (inv a :: bank) := by
  intro p  bank  a  tail ha
  intro M startStep oneStep twoStep
  exact oneStep (tail M startStep oneStep twoStep) ha
theorem Reach.two {R : Type} {roots : List (Wire R)} : ∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool) (tail : Reach roots p bank) (ha : Available bank a) (hb : Available bank b), Reach roots (p+1) (combine op a b :: bank) := by
  intro p  bank  a b  op tail ha hb
  intro M startStep oneStep twoStep
  exact twoStep op (tail M startStep oneStep twoStep) ha hb
theorem Reach.weakInduct {R : Type} {roots : List (Wire R)} {M : Nat → List (Wire R) → Prop} {p : Nat} {bank : List (Wire R)} (h : Reach roots p bank)
    (start : M 0 roots)
    (one : ∀ {p : Nat} {bank : List (Wire R)} {a : Wire R} (tail : Reach roots p bank) (ha : Available bank a) (ih : M p bank), M (p+1) (inv a :: bank))
    (two : ∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool) (tail : Reach roots p bank) (ha : Available bank a) (hb : Available bank b) (ih : M p bank), M (p+1) (combine op a b :: bank))
    : M p bank := by
  apply And.right (a := Reach roots p bank)
  apply h (fun p bank => Reach roots p bank ∧ M p bank)
  · exact ⟨Reach.start , start  ⟩
  · intro p  bank  a  tail ha
    exact ⟨Reach.one tail.1 ha, one tail.1 ha tail.2⟩
  · intro p  bank  a b  op tail ha hb
    exact ⟨Reach.two op tail.1 ha hb, two op tail.1 ha hb tail.2⟩
theorem Reach.induct {R : Type} {roots : List (Wire R)} {M : ∀ (p : Nat) (bank : List (Wire R)), Reach roots p bank → Prop} {p : Nat} {bank : List (Wire R)} (h : Reach roots p bank)
    (start : M 0 roots (Reach.start ))
    (one : ∀ {p : Nat} {bank : List (Wire R)} {a : Wire R} (tail : Reach roots p bank) (ha : Available bank a) (ih : M p bank tail), M (p+1) (inv a :: bank) (Reach.one tail ha))
    (two : ∀ {p : Nat} {bank : List (Wire R)} {a b : Wire R} (op : Bool) (tail : Reach roots p bank) (ha : Available bank a) (hb : Available bank b) (ih : M p bank tail), M (p+1) (combine op a b :: bank) (Reach.two op tail ha hb))
    : M p bank h := by
  apply Reach.weakInduct (M := fun p bank => ∀ z, M p bank z) h _ _ _ h
  · intro z
    exact start  
  · intro p  bank  a  tail ha ih z
    exact one tail ha (ih tail)
  · intro p  bank  a b  op tail ha hb ih z
    exact two op tail ha hb (ih tail)


def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R : Type} (goal : Wire R) (s : Nat) (ws : List (Wire R)) : Prop :=
  ∀ M : Nat → List (Wire R) → Prop,
  (M 0 [goal]) →
  (∀ {s : Nat} {xs zs : List (Wire R)} (eq : xs.Perm zs) (tail : M s xs), M s zs) →
  (∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool) (tail : M s (inv a :: kept save a rest)), M (s+1) (a :: rest)) →
  (∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Bool) (ka : Bool) (kb : Bool) (tail : M s (combine op a b :: kept ka a (kept kb b rest))), M (s+1) (a :: b :: rest)) → M s ws
theorem Run.stop {R : Type} {goal : Wire R} : Run goal 0 [goal] := by
  intro M stopStep permStep oneStep twoStep
  exact stopStep 
theorem Run.perm {R : Type} {goal : Wire R} : ∀ {s : Nat} {xs zs : List (Wire R)} (eq : xs.Perm zs) (tail : Run goal s xs), Run goal s zs := by
  intro s  xs zs  eq tail
  intro M stopStep permStep oneStep twoStep
  exact permStep eq (tail M stopStep permStep oneStep twoStep)
theorem Run.one {R : Type} {goal : Wire R} : ∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool) (tail : Run goal s (inv a :: kept save a rest)), Run goal (s+1) (a :: rest) := by
  intro s  a  rest  save tail
  intro M stopStep permStep oneStep twoStep
  exact oneStep save (tail M stopStep permStep oneStep twoStep)
theorem Run.two {R : Type} {goal : Wire R} : ∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Bool) (ka : Bool) (kb : Bool) (tail : Run goal s (combine op a b :: kept ka a (kept kb b rest))), Run goal (s+1) (a :: b :: rest) := by
  intro s  a b  rest  op ka kb tail
  intro M stopStep permStep oneStep twoStep
  exact twoStep op ka kb (tail M stopStep permStep oneStep twoStep)
theorem Run.weakInduct {R : Type} {goal : Wire R} {M : Nat → List (Wire R) → Prop} {s : Nat} {ws : List (Wire R)} (h : Run goal s ws)
    (stop : M 0 [goal])
    (perm : ∀ {s : Nat} {xs zs : List (Wire R)} (eq : xs.Perm zs) (tail : Run goal s xs) (ih : M s xs), M s zs)
    (one : ∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool) (tail : Run goal s (inv a :: kept save a rest)) (ih : M s (inv a :: kept save a rest)), M (s+1) (a :: rest))
    (two : ∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Bool) (ka : Bool) (kb : Bool) (tail : Run goal s (combine op a b :: kept ka a (kept kb b rest))) (ih : M s (combine op a b :: kept ka a (kept kb b rest))), M (s+1) (a :: b :: rest))
    : M s ws := by
  apply And.right (a := Run goal s ws)
  apply h (fun s ws => Run goal s ws ∧ M s ws)
  · exact ⟨Run.stop , stop  ⟩
  · intro s  xs zs  eq tail
    exact ⟨Run.perm eq tail.1, perm eq tail.1 tail.2⟩
  · intro s  a  rest  save tail
    exact ⟨Run.one save tail.1, one save tail.1 tail.2⟩
  · intro s  a b  rest  op ka kb tail
    exact ⟨Run.two op ka kb tail.1, two op ka kb tail.1 tail.2⟩
theorem Run.induct {R : Type} {goal : Wire R} {M : ∀ (s : Nat) (ws : List (Wire R)), Run goal s ws → Prop} {s : Nat} {ws : List (Wire R)} (h : Run goal s ws)
    (stop : M 0 [goal] (Run.stop ))
    (perm : ∀ {s : Nat} {xs zs : List (Wire R)} (eq : xs.Perm zs) (tail : Run goal s xs) (ih : M s xs tail), M s zs (Run.perm eq tail))
    (one : ∀ {s : Nat} {a : Wire R} {rest : List (Wire R)} (save : Bool) (tail : Run goal s (inv a :: kept save a rest)) (ih : M s (inv a :: kept save a rest) tail), M (s+1) (a :: rest) (Run.one save tail))
    (two : ∀ {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Bool) (ka : Bool) (kb : Bool) (tail : Run goal s (combine op a b :: kept ka a (kept kb b rest))) (ih : M s (combine op a b :: kept ka a (kept kb b rest)) tail), M (s+1) (a :: b :: rest) (Run.two op ka kb tail))
    : M s ws h := by
  apply Run.weakInduct (M := fun s ws => ∀ z, M s ws z) h _ _ _ _ h
  · intro z
    exact stop  
  · intro s  xs zs  eq tail ih z
    exact perm eq tail (ih tail)
  · intro s  a  rest  save tail ih z
    exact one save tail (ih tail)
  · intro s  a b  rest  op ka kb tail ih z
    exact two op ka kb tail (ih tail)


theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩

theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w::bank) v := by
  exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr

theorem extend_one {R} (roots : List (Wire R)) {p bank a} (hp : Reach roots p bank)
    (ha : Available bank a) :
    ∃ q next, Reach roots q next ∧ Available next (inv a) ∧
        (∀ v, Available bank v → Available next v) ∧ q+cost a ≤ p+1+cost (inv a) := by
  classical
  by_cases c : Constant a
  · exact ⟨p,bank,hp,Or.inr (inv_constant c),fun _ h => h,by simp [cost,c,inv_constant c]⟩
  · exact ⟨p+1,_,Reach.one hp ha,Or.inl (by simp),fun _ h => available_cons _ h,by simp [cost,c]⟩

theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (combine op a b) ∧
        (∀ v, Available bank v → Available next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next, Reach roots q next ∧ Available next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.induct generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @one s a rest save _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_one roots hp (hs a (by simp))
    have ht : supply T (inv a :: kept save a rest) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (mem_kept hh)))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a rest save
    rw [mass_cons] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_two roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (combine op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.induct with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | one save _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    exact Run.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    cases op
    · exact Run.two false ka kb ih
    · exact Run.two true ka kb ih

theorem projected_bound {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega


abbrev Row := Fin 512
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Bool) (a b : Sig) :
    observe (bin d a b) = combine d (observe a) (observe b) := by
  funext r
  cases d <;> exact bit_bin _ _ _ _

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {T : Sig} {k u S} (h : Live T k u S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (observe T) k (v.map observe) := by
  classical
  induction h using Live.induct generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @unary k u U a ha fresh _ ih =>
    let rest := (U.erase a).toList
    let save := decide (a ∈ U)
    let tail := kept save a rest
    have er : rest.toFinset = U.erase a := by simp [rest]
    have hm : a ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have ht : tail.toFinset = U := by
      rw [show tail=kept save a rest by rfl,kept_fin,er]
      by_cases hh : a ∈ U <;> simp [save,hh]
    have nd := kept_nd save a rest hr hm
    have hf : neg a ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress := ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    rw [List.map_cons,map_kept,obs_neg] at progress
    have perm : (a::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
      simp [er,eqv]
    exact Run.perm (perm.map _) (Run.one save progress)
  | @binary k u U a b d ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_bin (d : Bool) (f g : Wire Row) :
    table (combine d f g) = bin d (table f) (table g) := by
  rw [←table_observe (bin d (table f) (table g)),obs_bin,observe_table,observe_table]

theorem available_rep {bank : List (Wire Row)} {a} (h : Available bank a) :
    represented (bank.map table) (table a) := by
  rcases h with hm | ⟨b,rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z : table (fun _ => false) = zero := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_zero ⟨j,hj⟩).symm
      exact fun hp => hp.1 z
    · have z : table (fun _ => true) = one := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_one ⟨j,hj⟩).symm
      exact fun hp => hp.2 z

theorem inv_rep {w a} (ha : represented w a) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
  · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)

theorem pull_cons {w : List Sig} {z : Sig} {T k t S} (h : Live T k t S)
    (hz : represented w z ∨ witness w z) (hs : ∀ a ∈ S, a ∈ z::w) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live T k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  apply pull_gate h hz
  intro a hm
  simpa [or_comm] using hs a hm

theorem reach_live_sub {roots : List (Wire Row)} {p bank}
    (h : Reach roots p bank) {T k t S} (run : Live T k t S)
    (sub : ∀ a ∈ S, a ∈ bank.map table) :
    ∃ l v U, l ≤ p+k ∧ Live T l v U ∧ ∀ a ∈ U, a ∈ roots.map table := by
  induction h using Reach.induct generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p bank a h ha ih =>
    rw [List.map_cons,table_inv] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (inv_rep (available_rep ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,table_bin] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (bin_rep d (available_rep ha) (available_rep hb)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩

theorem reach_live {roots : List Sig} {p bank T} (hp : proper T)
    (h : Reach (roots.map observe) p bank) (hit : Available bank (observe T)) :
    ∃ k t S, k ≤ p ∧ Live T k t S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,v,U,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,v,U,by omega,hr,?_⟩
  simpa [List.map_map,Function.comp_def,table_observe] using hs

theorem live_row_difference {T k t S} (h : Live T k t S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.induct with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @unary k t U a hp hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · refine ⟨a,by simp,?_⟩
      exact fun he => hd (by rw [bit_neg,bit_neg,he])
    · exact ⟨v,Finset.mem_insert_of_mem hu,hd⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {T k t S} (h : Live T k t S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def seed : Sig := 0x88888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888888

def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem seed_table : ∀ r : Row, bit r seed = (sample r 0 && sample r 1) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem seed_nonzero : seed ≠ zero := by decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

theorem exec_extends (gs : List Gate) (ws : List Sig) : ∃ l, execute gs ws = ws ++ l := by
  induction gs generalizing ws with
  | nil => exact ⟨[],by simp [execute]⟩
  | cons g gs ih =>
    obtain ⟨l,hl⟩ := ih (ws++[gv ws g])
    exact ⟨gv ws g::l,by simpa [execute,List.append_assoc] using hl⟩

def neighbor (i : Fin 9) : Nat := [4,2,1,2,3,0,1,2,3].getD i.val 0
def absentRow (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor i)
def presentRow (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor i))

theorem seed_witness : ∀ i : Fin 9,
    (bit (absentRow i) graph != bit (presentRow i) graph) &&
    ((inputs++[seed]).all fun w => w == inputs.getD i.val zero ||
      bit (absentRow i) w == bit (presentRow i) w) = true := by decide +kernel

theorem all_roots {k t S} (h : Live graph k t S) (sub : ∀ v ∈ S, v ∈ inputs++[seed]) :
    S=inputs.toFinset ∨ S=(inputs++[seed]).toFinset := by
  have all (i : Fin 9) : inputs.getD i.val zero ∈ S := by
    have cut := seed_witness i
    simp only [Bool.and_eq_true,Bool.not_eq_true',bne_iff_ne,List.all_eq_true,
      Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] at cut
    apply raw_required h _ _ sub (absentRow i) (presentRow i) cut.1
    exact fun v hv hne => (cut.2 v hv).resolve_left hne
  have needed : inputs.toFinset ⊆ S := by
    intro v hv
    have hm := List.mem_toFinset.mp hv
    rw [←input_list,List.mem_ofFn] at hm
    obtain ⟨i,rfl⟩ := hm
    exact all i
  by_cases hseed : seed ∈ S
  · right
    ext w
    constructor
    · exact fun hw => List.mem_toFinset.mpr (sub w hw)
    · intro hw
      have hx := List.mem_toFinset.mp hw
      simp only [List.mem_append,List.mem_singleton] at hx
      exact hx.elim (fun h => needed (List.mem_toFinset.mpr h)) (fun e => e ▸ hseed)
  · left
    exact Finset.Subset.antisymm (fun w hw => by
      have hx := sub w hw
      simp only [List.mem_append,List.mem_singleton] at hx
      rcases hx with hin | rfl
      · exact List.mem_toFinset.mpr hin
      · exact False.elim (hseed hw)) needed

theorem initial_live (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (first : ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y 1))
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ k t, k ≤ 14 ∧ (Live graph k t inputs.toFinset ∨ Live graph k t (inputs++[seed]).toFinset) := by
  have headEq : (execute C.gates inputs).getD 9 zero = seed := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal 9 r).trans ((first (sample r)).trans (seed_table r).symm)
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have out := get_rep (execute C.gates inputs) C.output
  rw [goalEq] at out
  have targetIn := out.resolve_right (fun hn => hn graph_proper)
  cases hgs : C.gates with
  | nil =>
    rw [hgs] at headEq
    exact False.elim (seed_nonzero headEq.symm)
  | cons g gs =>
    have eq0 : gv inputs g = seed := by
      rw [hgs] at headEq
      change (execute gs (inputs++[gv inputs g])).getD 9 zero = seed at headEq
      obtain ⟨l,hl⟩ := exec_extends gs (inputs++[gv inputs g])
      rw [hl] at headEq
      exact headEq
    rw [hgs] at targetIn
    change graph ∈ execute gs (inputs++[gv inputs g]) at targetIn
    rw [eq0] at targetIn
    have tailLegal : ∀ gate ∈ gs, gate.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ gate.inputs.length≤2 := by
      intro gate hg
      apply legal
      rw [hgs]
      exact List.mem_cons_of_mem _ hg
    obtain ⟨k,t,S,hk,run,hs⟩ := extract gs _ tailLegal graph_proper targetIn
    have len : gs.length+1 ≤ 15 := by simpa [Circuit.size,hgs] using small
    refine ⟨k,t,by omega,?_⟩
    rcases all_roots run hs with h | h
    · exact Or.inl (h ▸ run)
    · exact Or.inr (h ▸ run)


def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_neg (f : Row → Row) (a : Sig) : rename f (neg a) = neg (rename f a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (neg a)) = bit ⟨j,hj⟩ (neg (rename f a))
  rw [bit_rename,bit_neg,bit_neg,bit_rename]
theorem rename_bin (f : Row → Row) (d : Bool) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (bin d a b)) = bit ⟨j,hj⟩ (bin d (rename f a) (rename f b))
  rw [bit_rename,bit_bin,bit_bin,bit_rename,bit_rename]
theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {T k t S} (h : Live T k t S) (f : Row → Row) (onto : Function.Surjective f) :
    Live (rename f T) k t (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.induct with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @unary k t U a hp hf _ ih =>
    have fresh : rename f (neg a) ∉ (insert a U).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_neg] at fresh ih ⊢
    exact Live.unary (pp _ hp) fresh ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {T k t S} (h : Live T k t S) (none : t=0) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.induct with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih none
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      cases d <;> cases p : bit r a <;> cases q : bit s a <;>
        cases u : bit r b <;> cases z : bit s b <;> simp_all
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p

def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → ¬Live T k t S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {roots T L} (hp : proper T)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,t,S,hk,run,hs⟩ := reach_live hp h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k t (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : represented ([] : List Sig) v := by
    have avail : Available ([] : List (Wire Row)) (observe v) := Or.inr ⟨b,h⟩
    simpa only [List.map_nil,table_observe] using available_rep avail
  exact (hr.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {roots other : List Sig} {T G : Sig} (pT : proper T) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live pT hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega



def childOne (ws : List Sig) (a : Sig) (keep : Bool) : List Sig :=
  neg a :: kept keep a (ws.erase a)
def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : ∀ a ∈ ws, ∀ keep, neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      Impossible T (cap-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k t hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.induct with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let keep := decide (a ∈ U)
    have er := erase_fin hn a
    have rest : (kept keep a (ws.erase a)).toFinset = U := by
      rw [kept_fin,er,he]
      by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup := by
      have na : a ∉ ws.erase a := hn.not_mem_erase
      have nk := kept_nd keep a (ws.erase a) (hn.erase _) na
      refine List.nodup_cons.mpr ⟨?_,nk⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h))
    have eq : (childOne ws a keep).toFinset = insert (neg a) U := by simp [childOne,rest]
    have sc := (live_size tail).2
    have len : (childOne ws a keep).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact oneStep a am keep fresh hz len k t (by omega) (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := (live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {T k t S} (h : Live T k t S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → t=0) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {T cap ws k t} (h : Live T k t (List.toFinset ws))
    (hk : k ≤ cap) (hn : ws.Nodup) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (decide (ws.length=cap+1)) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  intro hh
  have eq := of_decide_eq_true hh
  have bound := (live_size h).2
  rw [List.toFinset_card_of_nodup hn] at bound
  omega



def Slice (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach (roots.map observe) p bank → Available bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m)

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available bank (restrictRows f (observe a))

theorem availableB_sound {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply f bank pool)
    (check : availableB d pool a = true) : Available bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with (hz | ho) | ⟨v,hv,he⟩
  · exact Or.inr ⟨false,masked_zero dom hz⟩
  · exact Or.inr ⟨true,masked_one dom ho⟩
  · exact masked_eq dom he ▸ supplyB v hv

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) :=
  if c.1=2 then neg c.2.1 else bin (c.1==1) c.2.1 c.2.2
def choiceOK (d : Sig) (pool : List Sig) (c : Choice) :=
  availableB d pool c.2.1 && (c.1==2 || availableB d pool c.2.2)

theorem pay_choice {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d pool c = true) :
    ∃ next, Reach roots (q+1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  have ok : availableB d pool c.2.1 = true ∧ (c.1==2 || availableB d pool c.2.2) = true := by simpa only [choiceOK,Bool.and_eq_true] using valid
  have ha := availableB_sound dom hs ok.1
  let z := restrictRows f (observe (choiceVal c))
  have hz : Reach roots (q+1) (z::bank) := by
    by_cases unary : c.1=2
    · change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_pos unary,obs_neg]
      exact Reach.one hp ha
    · have hb : availableB d pool c.2.2 = true := by simpa [unary] using ok.2
      have hz' := Reach.two (c.1==1) hp ha (availableB_sound dom hs hb)
      change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_neg unary,obs_bin]
      have comm (b : Bool) (v w : Wire Row) : restrictRows f (combine b v w) = combine b (restrictRows f v) (restrictRows f w) := by cases b <;> rfl
      rw [comm]
      exact hz'
  refine ⟨_,hz,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact Or.inl (by simp [z])
  · exact available_cons _ (hs _ hm)

def makePool (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK d pool c then makePool d (choiceVal c::pool) cs else none

theorem makePool_sound {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {result} (ok : makePool d pool cs = some result) :
    ∃ next, Reach roots (q+cs.length) next ∧ poolSupply f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

def poolCut (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB d pool)

theorem poolCut_sound {raw T d L} (slice : Slice raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut d L cap cs.length pool ws = true) :
    Impossible T cap ws.toFinset := by
  intro k t hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega



abbrev Move := Sig × Sig × Row
def shifted (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩
def backwards (d : Row) : Row := Fin.ofNat 512 (512-d.val)
def rowMove (m : Move) (r : Row) : Row :=
  if bit r m.1 then shifted m.2.2 r else if bit r m.2.1 then shifted (backwards m.2.2) r else r
def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)
def wordMove (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (backwards m.2.2).val) a)

theorem bit_shift (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (shifted d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [shifted,h,r.isLt]

theorem bool_mux (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp

theorem bit_mux (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact bool_mux _ _ _

theorem bit_move (r : Row) (m : Move) (a : Sig) : bit r (wordMove m a) = bit (rowMove m r) a := by
  simp only [wordMove,bit_mux,bit_shift,rowMove]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl

def movedRow (ms : List Move) (r : Row) := ms.foldl (fun j m => rowMove m j) r
def movedWord (ms : List Move) (a : Sig) := ms.foldr wordMove a
theorem bit_moved (ms : List Move) (a : Sig) (r : Row) :
    bit r (movedWord ms a) = bit (movedRow ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (bit_move r m _).trans (ih _)
theorem moved_eq_rename (ms : List Move) (a : Sig) : movedWord ms a = rename (movedRow ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (bit_moved ms a ⟨j,hj⟩).trans (bit_rename _ _ ⟨j,hj⟩).symm

def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w
theorem freeWord_ok {roots w} (ok : freeWord roots w = true) :
    Available (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr ⟨false,funext bit_zero⟩
  · exact Or.inr ⟨true,funext bit_one⟩
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (pG : proper G) (hL : Lower base G L) : Lower raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower base G L) :
    Slice raw T d L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  have obs : restrictRows (movedRow ms) (observe T) = observe G :=
    (observe_rename _ _).symm.trans (congrArg observe eq)
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←bit_moved,all,bit_one]
  · intro a ha
    rw [←observe_rename]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL

def witnessB (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)
theorem witnessB_sound {T roots a rs} (ok : witnessB T roots a rs = true) : Essential T roots a := by
  simp only [witnessB,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩

def checkEssential (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok _ hm)

theorem lower_count {raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live properT hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := (live_size run).2
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower base G L) :
    Lower raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT properG _ eq supp _ (essential_ok ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,moved_eq_rename] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext bit_zero⟩
  · rw [h]
    exact ⟨true,funext bit_one⟩



def selected (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none
def vars (m : Nat) := (selected m).map Prod.snd
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
def cube0 : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1
def cube3 : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1
def cube6 : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1
def subcube (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((cube0 (fixed &&& 7)*cube3 ((fixed >>> 3) &&& 7)*cube6 ((fixed >>> 6) &&& 7)) <<< o)
def fixRows (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none
def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)

def supportPairs (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,0,Fin.ofNat 512 (1 <<< i))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
def assertSize (m hints L : Nat) :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
theorem size_of {m hints L} (h : assertSize m hints L = true) :
    Lower (vars m) (graphGoal m) L := by
  simp only [assertSize,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (lower_count (proper_of _ h.1.1) _ h.1.2 p bank hr ha)

abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig :=
  if m=1023 then graphGoal m &&& ~~~seed else graphGoal m
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice (vars m) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  obtain ⟨z,o,q,s,L⟩ := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs s
  change (((properB G && checkMap ms (vars m) (chartGoal m) (vars free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def relabelOK (old rep : Nat) (swaps : List Nat) :=
  properB (graphGoal old) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)
theorem relabel_of {old rep L swaps} (ok : relabelOK old rep swaps = true)
    (h : Lower (vars rep) (graphGoal rep) L) : Lower (vars old) (graphGoal old) L := by
  simp only [relabelOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1) (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower (vars q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he


abbrev BoundPool := (Sig) × (Nat) × (Nat) × (List Sig)
def BoundPool.domain (v : BoundPool) : Sig := v.1
def BoundPool.bound (v : BoundPool) : Nat := v.2.1
def BoundPool.paid (v : BoundPool) : Nat := v.2.2.1
def BoundPool.wires (v : BoundPool) : List Sig := v.2.2.2

def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach (roots.map observe) q ws → Available ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach (roots.map observe) c.paid bank ∧ poolSupply f bank c.wires ∧ True

theorem build_valid {raw T d lb} (h : Slice raw T d lb) (cs : List Choice) {ws}
    (build : makePool d raw cs = some ws) : ValidPool raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩

theorem valid_exclude {raw T c} (valid : ValidPool raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB c.domain c.wires a = true)
    (buy : if paid then choiceOK c.domain c.wires choice = true
       else availableB c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible T k (choiceVal choice :: rest).toFinset := by
  intro t num ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach (roots.map observe) n out)
      (zs : poolSupply f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply out ((ws.map observe).map (restrictRows f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := projected_bound f (list_run run ws nd rfl) nc reach covered lo
    have cm := count_constants dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (isMaskedConstant c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact availableB_sound dom hs buy
    · exact availableB_sound dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have avail := availableB_sound dom hs (known _ hm)
      rcases avail with mem | con
      · have ha : availableB c.domain c.wires a = true := known _ hm
        have point : ∀ u ∈ c.wires, Available out (restrictRows f (observe u)) :=
          fun u hu => hc u (List.mem_cons_of_mem _ hu)
        exact availableB_sound dom point ha
      · exact Or.inr con

def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB c.domain c.wires)) && (!extra || choiceOK c.domain c.wires op)

theorem scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {raw T d L cs c} (slice : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he


abbrev Bits := BitVec 768
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 768 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 768 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 768 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 768 → Row) (x : Decor) := x.2 = pairSig r s x.1
def dneg (x : Decor) : Decor := (neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)

theorem ofRows_neg (r : Fin 768 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin (r : Fin 768 → Row) (d : Bool) (a b : Sig) :
    ofRows r (bin d a b) = if d then ofRows r a ||| ofRows r b else ofRows r a &&& ofRows r b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  cases d <;> simpa only [Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] using h
theorem faithful_neg {r s x} (h : faithful r s x) : faithful r s (dneg x) := by
  change x.2 = _ at h
  simp only [faithful,dneg,pairSig,ofRows_neg, h]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  cases d <;> simp only [faithful,dbin,Bool.false_eq_true,ite_false,ite_true,pairSig,ofRows_bin,hx,hy]

def codeDecor (op : Nat) (x y : Decor) := if op=2 then dneg x else dbin (op==1) x y
def defaultDecor : Decor := (zero,0,0)
theorem faithful_default (r s) : faithful r s defaultDecor := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : Bits).getLsbD j = (ofRows r zero).getLsbD j
    rw [show (ofRows r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
  · change (0 : Bits).getLsbD j = (ofRows s zero).getLsbD j
    rw [show (ofRows s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from ofRows_bit _ _ ⟨j,hj⟩,bit_zero]
    simp
theorem faithful_get {r s ws} (all : ∀ v ∈ ws, faithful r s v) (i : Nat) :
    faithful r s (List.getD ws i defaultDecor) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact faithful_default _ _
  | some v => exact all _ (List.mem_of_getElem? e)
def decodeBank (n : Nat) (bits : Nat) (ws : List Decor) : List Decor :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) defaultDecor
    let b := ws.getD ((bits >>> 4) &&& 15) defaultDecor
    decodeBank k (bits >>> 10) (ws++[codeDecor ((bits >>> 8) &&& 3) a b])
theorem decode_faithful (n bits) (ws) (r s) (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ decodeBank n bits ws, faithful r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      unfold codeDecor
      split
      · exact faithful_neg (faithful_get base _)
      · exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 768) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])
theorem coordinate0 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel
theorem coordinate1 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel
theorem coordinate2 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel
theorem coordinate3 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel
theorem coordinate4 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel
theorem coordinate5 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel
theorem coordinate6 : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel
theorem coordinate7 : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel
theorem coordinate8 : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel
theorem input_coords : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact coordinate0 r
  · exact coordinate1 r
  · exact coordinate2 r
  · exact coordinate3 r
  · exact coordinate4 r
  · exact coordinate5 r
  · exact coordinate6 r
  · exact coordinate7 r
  · exact coordinate8 r
theorem asRow_bit (cols : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [input_coords]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]
def rawDecor (m : Nat) (p q : Nat → Bits) : List Decor :=
  (selected m).map (fun (j,a) => (a,p j,q j))
theorem selected_entry {m j a} (h : (j,a) ∈ selected m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction
theorem raw_faithful (m) (p q : Nat → Bits) :
    ∀ a ∈ rawDecor m p q, faithful (asRow p) (asRow q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := selected_entry hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (asRow_bit p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm
  · exact (asRow_bit q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (ofRows_bit _ _ ⟨i,hi⟩).symm

def liftGoal (m : Nat) (v : Nat → Bits) : Bits :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
abbrev Cov := Bits × Bits × Bits

def addCov (z : Bits) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))

def coverage (d : Bool) (v : List Decor) : Cov :=
  v.foldr (fun a c => addCov (column d a.2) c) (0,0,0)

def takeOne (c : Cov) (a : Bits) : Bits := c.1 &&& ~~~(c.2.1 &&& a)
def takeTwo (c : Cov) (a b : Bits) : Bits :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))

private theorem cov_one (c : Cov) (a : Bits) : takeOne (addCov a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeOne,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl

private theorem cov_two (c : Cov) (a b : Bits) : takeTwo (addCov a (addCov b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [takeTwo,addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem add_swap (c : Cov) (a b : Bits) : addCov a (addCov b c)=addCov b (addCov a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [addCov,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [addCov,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl

private theorem cov_perm (d : Bool) {l r : List Decor} (h : l.Perm r) : coverage d l=coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (column d a.2)) ih
  | swap a b t => exact add_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2



theorem cov_word (d : Bool) (v : List Decor) {r s} (good : ∀ a ∈ v, faithful r s a) :
    (coverage d v).1 = covered d (pairSig r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (column d a.2 ||| (coverage d v).1) = column d (pairSig r s a.1) ||| _
    rw [show a.2=pairSig r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]

def delOne (ws : List Decor) (a : Decor) (keep : Bool) :=
  if keep then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) :=
  delOne (delOne ws a ka) b kb

theorem delOne_perm {ws : List Decor} (a : Decor) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha

theorem cover_one {ws : List Decor} (d : Bool) (a : Decor) (ha : a ∈ ws) (keep : Bool) :
    (coverage d (delOne ws a keep)).1 =
      (if keep then (coverage d ws).1 else takeOne (coverage d ws) (column d a.2)) := by
  cases keep
  · change (coverage d (ws.erase a)).1 = takeOne (coverage d ws) _
    rw [cov_perm d (delOne_perm a ha)]
    exact (cov_one _ _).symm
  · rfl
theorem delTwo_perm {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (delOne_perm a ha).trans (List.Perm.cons _ (delOne_perm b hm))

theorem cover_two {ws : List Decor} (d : Bool) (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (coverage d (delTwo ws a b ka kb)).1 =
      (if ka then (if kb then (coverage d ws).1 else takeOne (coverage d ws) (column d b.2))
       else if kb then takeOne (coverage d ws) (column d a.2)
       else takeTwo (coverage d ws) (column d a.2) (column d b.2)) := by
  cases ka <;> cases kb
  · change (coverage d ((ws.erase a).erase b)).1 = takeTwo (coverage d ws) _ _
    rw [cov_perm d (delTwo_perm a b ha hb ne)]
    exact (cov_two _ _ _).symm
  · exact cover_one d a ha false
  · exact cover_one d b hb false
  · rfl

def sameWords (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))
theorem sameWords_sound {xs ys} (h : sameWords xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [sameWords,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩


def keyWord (v : Sig) :=
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut p k rest op)

theorem closeChild_sound {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Cov
def preCov (ws : List Decor) : CovPair := (coverage false ws,coverage true ws)
def getCov (c : CovPair) (d : Bool) := if d then c.2 else c.1
theorem get_preCov (ws) (d : Bool) : getCov (preCov ws) d = coverage d ws := by cases d <;> rfl
def restCov (v : Cov) (a b : Bits) (un ka kb : Bool) :=
  if un then (if ka then v.1 else takeOne v a) else
    if ka then (if kb then v.1 else takeOne v b)
    else if kb then takeOne v a else takeTwo v a b
def opKeep (un ka kb : Bool) (a b : Decor) (ws : List Decor) :=
  if un then delOne ws a ka else delTwo ws a b ka kb

theorem rest_coverage {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (un ka kb d : Bool) (ne : un=false → a≠b) :
    (coverage d (opKeep un ka kb a b ws)).1 =
      restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) un ka kb := by
  rw [get_preCov]
  cases un
  · exact cover_two d a b ha hb (ne rfl) ka kb
  · exact cover_one d a ha ka

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    (opKeep un ka kb a b ws).Sublist ws := by
  cases un
  · exact (delOne_sub _ _ _).trans (delOne_sub _ _ _)
  · exact delOne_sub _ _ _
theorem len_keep (ws : List Decor) (a b : Decor) (un ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : un=false → a≠b) :
    (opKeep un ka kb a b ws).length =
      ws.length - (if ka then 0 else 1) - (if un || kb then 0 else 1) := by
  cases un
  · have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm (ne rfl))).mpr hb
    cases ka <;> cases kb <;> simp [opKeep,delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
  · cases ka <;> cases kb <;> simp [opKeep,delOne,List.length_erase_of_mem ha]

def movedDecor (op : Nat) (a b : Decor) := codeDecor op a b
def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)
theorem moved_full (op) (a b : Decor) :
    (movedDecor op a b).1 = choiceVal (movedChoice op a b) := by
  by_cases h : op=2
  · simp [movedDecor,codeDecor,h,dneg,choiceVal,movedChoice]
  · cases hh : op==1 <;> simp [movedDecor,codeDecor,h,hh,dbin,choiceVal,movedChoice]
theorem moved_faithful {r s a b} (ha : faithful r s a) (hb : faithful r s b) (op : Nat) :
    faithful r s (movedDecor op a b) := by
  unfold movedDecor codeDecor
  split
  · exact faithful_neg ha
  · exact faithful_bin _ ha hb

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len>cap then true else
    let d := len==cap
    let rs := restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (opKeep un ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (movedDecor op a b).1 :: (opKeep (op==2) ka kb a b ws).map Prod.fst
theorem evalMove_sound {raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb = true) :
    Impossible T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := movedDecor op a b
  let rest := opKeep (op==2) ka kb a b ws
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk h
  have hsz := (live_size h).2
  change child.toFinset.card + t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h hk ndc (pair_sep pairs)
  have ce : cap-1+1=cap := by omega
  rw [ce] at sep
  let d := child.length==cap
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := rest_coverage ha hb (op==2) ka kb d ne
  have hf := moved_faithful (faith _ ha) (faith _ hb) op
  have deq : decide (child.length=cap) = (child.length==cap) := by by_cases he : child.length=cap <;> simp [he]
  change covered (decide (child.length = cap)) (pairSig r s) child = BitVec.allOnes 768 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 768) = false := by simp [sep]
  change (if (_ != _) then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  have val := moved_full op a b
  change z.1 = _ at val
  change Live T k t child.toFinset at h
  have nd' := ndc
  change (z.1::rest.map Prod.fst).Nodup at nd'
  change Live T k t (z.1::rest.map Prod.fst).toFinset at h
  rw [val] at nd' h
  exact closeChild_sound pv lv nd' test k t hk h


def testPair (ctx : NodeContext) (a b : Decor) (d : Bool) :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
  let z := movedDecor 2 a a
  evalMove ctx 2 a a z false false && evalMove ctx 2 a a z true true &&
    bs.all (fun b => testPair ctx a b false && testPair ctx a b true)
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_unary {ctx ws} (h : testAll ctx ws=true) {a : Decor} (ha : a∈ws) (keep : Bool) :
    evalMove ctx 2 a a (movedDecor 2 a a) keep keep=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) (d : Bool) : testPair ctx a b d=true ∨ testPair ctx b a d=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1.2 b bm).1 | exact (h.1.2 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right
        cases d <;> first | exact (h.1.2 a haTail).1 | exact (h.1.2 a haTail).2
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail

theorem kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (un ka kb : Bool) (v : Sig) :
    v ∈ (opKeep un ka kb a b ws).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (un=true ∨ v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  cases un <;> simp only [opKeep,Bool.false_eq_true,ite_false,ite_true,delTwo,List.mem_map,
    mem_delone wn,mem_delone dn,or_false,false_or,true_or,and_true] <;> constructor
  all_goals
    first
    | rintro ⟨w,hw,rfl⟩
      first
      | exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
      | exact ⟨⟨_,hw.1,rfl⟩,hw.2.imp (fun ne eq => ne (unique_value nd hw.1 ha eq)) id⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
      exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1⟩
      exact ⟨w,⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem unary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a : Decor} (ha : a∈ws)
    (keep : Bool) :
    (moveFront ws 2 a a keep keep).toFinset = (childOne (ws.map Prod.fst) a.1 keep).toFinset := by
  ext v
  simp only [moveFront,childOne,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha ha,keep_mem,nd.mem_erase_iff,movedDecor,codeDecor,dneg,ite_true,
    Nat.reduceBEq,true_or,and_true]
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  by_cases e : v=a.1 <;> cases keep <;> simp_all

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d ka kb : Bool) :
    (moveFront ws (if d then 1 else 0) a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv := List.mem_map_of_mem (f:=Prod.fst) hb
  cases d <;> simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,movedDecor,codeDecor,dbin,
    Bool.false_eq_true,Nat.reduceBEq,ite_true,ite_false,false_or]
  all_goals by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap (v : List Sig) (nd : v.Nodup) (a b : Sig) (d ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a d kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_comm d b a]
  tauto

theorem node_sound {raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov ws,pools,links) ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k t hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    have eqS : S = {_} := h (fun k _ S => k = 0 → S = {_}) (fun _ _ => rfl) (fun _ _ _ hn => by contradiction) (fun _ _ _ _ _ hn => by contradiction) rfl
    exact out (List.mem_toFinset.mp ((he.trans eqS).symm ▸ Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  · intro v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    have hf := unary_front nd ha keep
    rw [←hf]
    exact evalMove_sound pairs faith nd ha ha (by simp) hc' pv lv pro fresh (all_unary checks ha keep)
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a≠b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPair (cap,ws.length,ws,preCov ws,pools,links) a b d = true) :
        Impossible T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      rw [←binary_front nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      exact evalMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv
        (eq ▸ pr) (eq ▸ fr) (testPair_at test ka kb)
    rcases all_binary checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [childTwo_swap _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro)
        (bin_comm d a.1 b.1 ▸ fresh) hh


theorem agree_inputs (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (input_coords i r).symm.trans ((h _ hm).trans (input_coords i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm

def composedOK (p q : List Move) := inputs.all (fun a => movedWord p (movedWord q a) == a)
theorem composed_id {p q} (h : composedOK p q = true) (r : Row) :
    movedRow q (movedRow p r) = r := by
  apply agree_inputs
  intro a ha
  rw [←bit_moved,←bit_moved]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]

def autoOK (T : Sig) (p : List Move) :=
  (movedWord p T == T) && composedOK p p.reverse && composedOK p.reverse p
theorem rotate_excluded {T n} {ws : List Sig} (hi : Impossible T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk h
  have run := live_rename h (movedRow p) onto
  have goal : rename (movedRow p) T = T := (moved_eq_rename p T).symm.trans ok.1.1
  have inv (x : Sig) : rename (movedRow p) (movedWord p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [bit_rename,bit_moved,composed_id ok.1.2]
  have back : (ws.map (movedWord p.reverse)).toFinset.image (rename (movedRow p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k t hk run

abbrev Packing := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)
def emptyPacking : Packing := (0,0,0,0,0,0,0,fun _ => 0)
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)


def lookupWord (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := packedAt data (a*sw) sw
  let row := (h/nb+sh)%slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots)%16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


abbrev IndexTree (α : Type) := List α
def IndexTree.leaf {α} (xs : List α) : IndexTree α := xs
def IndexTree.fork {α} (_ : Nat) (a b : IndexTree α) : IndexTree α := a ++ b
def IndexTree.read {α} (xs : IndexTree α) (i : Nat) := xs[i]?
def IndexTree.values {α} (xs : IndexTree α) := xs
theorem IndexTree.read_mem {α} (tree : IndexTree α) {i x} (e : tree.read i=some x) :
    x ∈ tree.values := List.mem_of_getElem? e
abbrev Forest := (Nat) × (Nat) × (Nat → Bits × Bits) × (IndexTree ColumnInfo) × (Array (List Nat)) × (Nat → Packing) × (Nat → Nat → Option (Nat × Nat))
def Forest.mask (v : Forest) : Nat := v.1
def Forest.cap (v : Forest) : Nat := v.2.1
def Forest.samples (v : Forest) : Nat → Bits × Bits := v.2.2.1
def Forest.cols (v : Forest) : IndexTree ColumnInfo := v.2.2.2.1
def Forest.autos (v : Forest) : Array (List Nat) := v.2.2.2.2.1
def Forest.levels (v : Forest) : Nat → Packing := v.2.2.2.2.2.1
def Forest.index (v : Forest) : Nat → Nat → Option (Nat × Nat) := v.2.2.2.2.2.2

def wiresOf (g : Forest) :=
  let ws := rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  let nonedge := dneg (dbin false (ws.getD 0 defaultDecor) (ws.getD 1 defaultDecor))
  if g.mask=1023 then ws.map (fun w => dbin false w nonedge) else ws
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a := by
  have base := raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  intro a ha
  unfold wiresOf at ha
  split at ha
  · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp ha
    exact faithful_bin false (base w hw) (faithful_neg (faithful_bin false
      (faithful_get base 0) (faithful_get base 1)))
  · exact base _ ha

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) :=
  if m=1023 then liftGoal m v &&& ~~~(v 0 &&& v 1) else liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  by_cases e : m=1023
  · have u := asRow_bit v i (0 : Fin 9)
    have w := asRow_bit v i (1 : Fin 9)
    have h := bit_liftGoal m v i
    change (inputs.getD 0 zero).getLsbD (asRow v i).val = (v 0).getLsbD i.val at u
    change (inputs.getD 1 zero).getLsbD (asRow v i).val = (v 1).getLsbD i.val at w
    have seedEq : seed = inputs.getD 0 zero &&& inputs.getD 1 zero := by decide +kernel
    simp only [chartGoal,chartSamples,e,ite_true,bit,seedEq,BitVec.getLsbD_and,
      BitVec.getLsbD_not,(asRow v i).isLt,i.isLt,decide_true,Bool.true_and,u,w] at h ⊢
    rw [h]
  · simpa only [chartGoal,chartSamples,e,ite_false] using bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 768) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def selectLive {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::selectLive (bits >>> 1) ws else selectLive (bits >>> 1) ws
theorem selectLive_sub {α : Type} (bits : Nat) (ws : List α) : (selectLive bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold selectLive
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)

def storedDepth (_g : Forest) (depth : Nat) := depth
def readNode (g : Forest) (k i : Nat) : Nat × List Decor × List Decor :=
  let raw := wiresOf g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*storedDepth g depth
  let width := len+raw.length+depth
  let recp := packedAt data (i*width) width
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := decodeBank depth ops raw
  (ops,bank,selectLive (recp >>> len) bank)

def getFieldV (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)
def chosenSteps (bank : List Decor) (ops paid : Nat) : Nat → List Choice
  | 0 => []
  | n+1 =>
    let more := chosenSteps bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (getFieldV ops 8 2,(bank.getD (ops &&& 15) defaultDecor).1,
        (bank.getD (getFieldV ops 4 4) defaultDecor).1) :: more

def buildRule (g : Forest) (ops d : Nat) (bank : List Decor) (idx paid : Nat) : Option BoundPool :=
  (g.cols.read idx).bind fun ci =>
    materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases e : g.cols.read i with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply materialize_sound _ h
    exact cols ci (g.cols.read_mem e)

def getPairs (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := packedAt data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: getPairs data w v n (pos+w+v)

def stateSet (g : Forest) (k i : Nat) := (readNode g k i).2.2.map Prod.fst
def linkedSet (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (stateSet g k pair.1).map (movedWord (perm.map swapRows).reverse)

theorem linkedSet_sound (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))

def nodeVerified (g : Forest) (k i : Nat) :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let values := ws.map Prod.fst
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t u lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    have eqS : S = {_} := h (fun k _ S => k = 0 → S = {_}) (fun _ _ => rfl) (fun _ _ _ hn => by contradiction) (fun _ _ _ _ _ hn => by contradiction) rfl
    exact hT (List.mem_toFinset.mp ((he.trans eqS).symm ▸ Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact linkedSet_sound g _ names (prior (by omega)) h


def block (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => nodeVerified g k (start+n) && block g k start n
theorem block_at {g k start n} (h : block g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    nodeVerified g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [block,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)
theorem block_merge {g k start a b} (h : block g k start a=true)
    (h' : block g k (start+a) b=true) : block g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [block,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,block,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩

def checkedTables (g : Forest) (top : Nat) :=
  ∀ k ≤ top, block g k 0 (g.levels k).1 = true
def graphValid (g : Forest) (prior : Nat → Nat) :=
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 768) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.values.all (fun c => colCheck g.mask c prior) &&
  g.autos.toList.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact block_at (rows _ hk) i (by omega) (by omega)

def indexedRoot (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && sameWords (stateSet g k i) ws
theorem root_index {g top prior k i ws} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

theorem lower_discard {g prior ci hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck g.mask ci prior = true)
    (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (vars g.mask) (vars g.mask)=true) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (poolCut_sound (col_sound ci prior low ok) [] rfl nd cut)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {old L m relabels} (previous : Known old)
    (main : Lower (vars m) (graphGoal m) L)
    (ok : relabels.all (fun v => relabelOK v.1 m v.2) = true) :
    Known (extendKnown old L relabels) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact relabel_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known [] := by simp [Known]
def lanePlace (v : Nat) (upper : Nat) := 2^769*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^769 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
theorem lanes_and {α} (f g : α → Bits) (xs) :
    combineLanes f xs &&& combineLanes g xs = combineLanes (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_and,ih]
theorem lanes_or {α} (f g : α → Bits) (xs) :
    combineLanes f xs ||| combineLanes g xs = combineLanes (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_or,ih]
theorem lanes_xor {α} (f g : α → Bits) (xs) :
    combineLanes f xs ^^^ combineLanes g xs = combineLanes (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [combineLanes]
  | cons a xs ih => simp only [combineLanes,place_xor,ih]
theorem broadcast {α} (a : Bits) (xs : List α) :
    units xs.length * a.toNat = combineLanes (fun _ => a) xs := by
  induction xs with
  | nil => simp [units,combineLanes]
  | cons v xs ih => simp only [List.length_cons,units,combineLanes,lanePlace,Nat.add_mul,Nat.mul_assoc,ih,Nat.one_mul]

def fullMarks (r packed : Nat) := ((packed+r) >>> 768) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (769*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^769)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 769*(i+1)-769=769*i := by omega
      have ge : ¬769*(i+1)<769 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 768 = (a==BitVec.allOnes 768) := by
  by_cases h : a=BitVec.allOnes 768
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^768-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^768 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (769*i) =
      (f xs[i]==BitVec.allOnes 768) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^769*u+x+(2^769*v+1)=2^769*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^769 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬769*(i+1)+768<769 := by omega
      have di : 769*(i+1)+768-769=769*i+768 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)


abbrev PackedSig := Nat × Nat
abbrev PackedCov := Nat × Nat × Nat

def packedSig {α} (s : α → Signals) (xs : List α) : PackedSig :=
  (combineLanes (fun x => (s x).1) xs,combineLanes (fun x => (s x).2) xs)
def packedCov {α} (c : α → Cov) (xs : List α) : PackedCov :=
  (combineLanes (fun x => (c x).1) xs,combineLanes (fun x => (c x).2.1) xs,
   combineLanes (fun x => (c x).2.2) xs)
def packedColumn (d : Bool) (a : PackedSig) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2

theorem xor_meet (a b : Bits) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem packed_column {α} (s : α → Signals) (xs : List α) (d : Bool) :
    packedColumn d (packedSig s xs) = combineLanes (fun x => column d (s x)) xs := by
  cases d <;> simp only [packedColumn,packedSig,column,Bool.false_eq_true,ite_false,ite_true,lanes_and,lanes_xor,xor_meet]

def packedOp (full : Nat) (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=2 then (full ^^^ a.1,full ^^^ a.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else (a.1 &&& b.1,a.2 &&& b.2)
theorem top_xor (a : Bits) : BitVec.allOnes 768 ^^^ a = ~~~a := BitVec.allOnes_xor
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 768).toNat) op
      (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (movedDecor op (a x) (b x)).2) xs := by
  by_cases un : op=2
  · simp only [packedOp,un,ite_true,packedSig,broadcast,lanes_xor,top_xor,movedDecor,codeDecor,dneg]
  · by_cases one : op=1 <;> simp [packedOp,un,one,packedSig,lanes_or,lanes_and,movedDecor,codeDecor,dbin]

def takePacked (c : PackedCov) (a b : Nat) (un ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if un then (if ka then c.1 else without1 a)
  else if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (un ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) un ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) un ka kb) xs := by
  cases un <;> cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (movedDecor op a b) ka kb
def combField (c : NodeContext) (d un ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov (getCov c.2.2.2.1 d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 769) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (769*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [onMarks,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 769) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs,packedCov (fun c => c.2.2.2.1.2) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

def availableMasked (p : BoundPool) (m : Sig) :=
  m==zero || m==p.domain || (p.wires.map (masked p.domain)).any (fun v => v==m)
theorem available_mask (p : BoundPool) (x : Sig) :
    availableB p.domain p.wires x = availableMasked p (masked p.domain x) := rfl

def constantLoss (p : Decor → Bool) (a : Decor) (keep : Bool) :=
  if keep then 0 else (p a).toNat
theorem lossBound (p : Decor → Bool) (ws : List Decor) (a : Decor) (keep : Bool) :
    ws.countP p ≤ (delOne ws a keep).countP p + constantLoss p a keep := by
  cases keep
  · simp only [delOne,Bool.false_eq_true,ite_false,constantLoss,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [delOne,constantLoss]

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b (un || kb) ≤
    (opKeep un ka kb a b ws).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  cases un <;> simp only [opKeep,delTwo,Bool.false_eq_true,ite_false,ite_true,
    Bool.false_or,Bool.true_or] <;> first | omega | simp [constantLoss]; omega

abbrev QuickPool := BoundPool × Nat × Bool
def summarizePool (ws : List Decor) (p : BoundPool) : QuickPool :=
  (p,ws.countP (fun w => isMaskedConstant p.domain w.1),
     ws.all (fun w => availableB p.domain p.wires w.1))
def fastCost (s : QuickPool) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) :=
  if !s.2.2 then false else
  let p := s.1
  let un := op==2
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := choiceVal (movedChoice op a b)
  let zm := masked p.domain z
  let zc := isMaskedConstant p.domain z
  let cm := s.2.1 - constantLoss const a ka - constantLoss const b (un || kb) + zc.toNat
  let free := zc || zm==masked p.domain a.1 || zm==masked p.domain b.1
  decide (k+p.paid+(!free).toNat < p.bound+cm)

theorem fastCost_good {p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws)
    (h : fastCost (summarizePool ws p) k a b op ka kb=true) :
    scalarPoolCut p k ((opKeep (op==2) ka kb a b ws).map Prod.fst) (movedChoice op a b)=true := by
  let z := choiceVal (movedChoice op a b)
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let free := isMaskedConstant p.domain z || masked p.domain z==masked p.domain a.1 ||
      masked p.domain z==masked p.domain b.1
  let rest := opKeep (op==2) ka kb a b ws
  have ck := keptCount const ws a b (op==2) ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b ((op==2) || kb) ≤ rest.countP const at ck
  by_cases all : ws.all (fun w => availableB p.domain p.wires w.1)=true
  · have hav := List.all_eq_true.mp all
    have ready : free=true → availableB p.domain p.wires z=true := by
      intro f
      simp only [free,Bool.or_eq_true,beq_iff_eq] at f
      rcases f with (zc|za)|zb
      · simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
        exact Or.inl zc
      · rw [available_mask,za,←available_mask]
        exact hav _ ha
      · rw [available_mask,zb,←available_mask]
        exact hav _ hb
    have extra : (!availableB p.domain p.wires z).toNat ≤ (!free).toNat := by
      cases hf : free <;> cases he : availableB p.domain p.wires z <;> simp_all
    have hs : (rest.map Prod.fst).all (availableB p.domain p.wires)=true := by
      apply List.all_eq_true.mpr
      intro _ hm
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
      exact hav w ((keep_sub ws a b (op==2) ka kb).subset hw)
    have opOK : choiceOK p.domain p.wires (movedChoice op a b)=true := by
      simp [choiceOK,movedChoice,hav _ ha,hav _ hb]
    simp only [fastCost,summarizePool,all,Bool.not_true,Bool.false_eq_true,ite_false,decide_eq_true_eq] at h
    change k+p.paid+(!free).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b ((op==2)||kb)+(isMaskedConstant p.domain z).toNat) at h
    dsimp only [rest] at hs
    simp only [scalarPoolCut,hs,opOK,Bool.or_true,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
    change k+p.paid+(!availableB p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
    cases hc : isMaskedConstant p.domain z <;> simp [hc] at h ⊢ <;> omega
  · simp [fastCost,summarizePool,all] at h

def quickAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  (c.2.2.2.2.1.map (summarizePool c.2.2.1)).any (fun s => fastCost s (c.1-1) a b op ka kb)

theorem quickAt_good {c i j op ka kb} (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length)
    (h : quickAt c i j op ka kb=true) : checkAt c i j op ka kb=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
  have closed := fastCost_good (mem _ hi) (mem _ hj) ok
  have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut p (c.1-1)
      ((opKeep (op==2) ka kb (contextWire c i) (contextWire c j) c.2.2.1).map Prod.fst)
      (movedChoice op (contextWire c i) (contextWire c j)))=true :=
    List.any_eq_true.mpr ⟨p,hp,closed⟩
  simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
  repeat' split
  all_goals rfl

def fallbackAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  (if i<c.2.2.1.length ∧ j<c.2.2.1.length then quickAt c i j op ka kb else false) ||
    checkAt c i j op ka kb
theorem fallback_sound {c i j op ka kb} (h : fallbackAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    next yes => exact quickAt_good yes.1 yes.2 h
    next => contradiction
  · exact h
def batchMove (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,u,v) := b
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if len>k then true else
    let d := len==k
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp (r*(BitVec.allOnes 768).toNat) op a b'
    let cov := if d then v else u
    let mask := fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fallbackAt c i j op ka kb) mask xs

theorem batchMove_at (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n)
    (pass : batchMove (makeBatch k n xs) xs i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1))
  let d := len==k
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 768 then true
      else if !properB (movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((opKeep (op==2) ka kb (contextWire xs[q] i) (contextWire xs[q] j) xs[q].2.2.1).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,len,d,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := if d then packedCov (fun c : NodeContext => c.2.2.2.1.2) xs
            else packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn d a) (packedColumn d b) (op==2) ka kb |||
        packedColumn d (packedOp (r*(BitVec.allOnes 768).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have chosen : cov = packedCov (fun c => getCov c.2.2.2.1 d) xs := by
      dsimp only [cov]
      cases d <;> rfl
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j = BitVec.allOnes 768
    · apply fallback_sound
      apply marked_ok _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]


def batchPair (b : Batch) (xs : List NodeContext) (i j op : Nat) :=
  let f := batchMove b xs i j op
  f false false && f true false && f false true && f true true
def batchRow (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :=
  batchMove b xs i i 2 false false && batchMove b xs i i 2 true true &&
    js.all (fun j => batchPair b xs i j 0 && batchPair b xs i j 1)
def batchRows (b : Batch) (xs : List NodeContext) : List Nat → Bool
  | [] => true
  | i::js => batchRow b xs i js && batchRows b xs js

theorem batchRows_at (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows (makeBatch k n xs) xs js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    have check := @batchMove_at k n xs
    refine ⟨⟨⟨check hi hi hq budget arity allRows.1.1.1,check hi hi hq budget arity allRows.1.1.2⟩,?_⟩,
      ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    have both := allRows.1.2 j hj
    have opCheck (d : Bool) (pass : batchPair (makeBatch k n xs) xs i j (if d then 1 else 0)=true) :
        testPair xs[q] (contextWire xs[q] i) (contextWire xs[q] j) d=true := by
      simp only [batchPair,Bool.and_eq_true] at pass
      simp only [testPair,Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget arity pass.1.1.1,check hi hj' hq budget arity pass.1.1.2⟩,
        check hi hj' hq budget arity pass.1.2⟩,check hi hj' hq budget arity pass.2⟩
    exact ⟨opCheck false both.1,opCheck true both.2⟩

def runBatch (k n : Nat) (xs : List NodeContext) :=
    batchRows (makeBatch k n xs) xs (List.range n)
theorem runBatch_at {k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hn : xs[q].2.2.1.length=n)
    (pass : runBatch k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (contextWire xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [contextWire,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all

def contextOf (g : Forest) (k i : Nat) : NodeContext :=
  let raw := wiresOf g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := readNode g k i
  let start := num*(10*storedDepth g depth+raw.length+depth)
  let pos := start+num*offw+packedAt data (start+i*offw) offw
  let nr := packedAt data pos 5
  let nl := packedAt data (pos+5) lw
  let st := pos+5+lw
  let rules := (getPairs data cw depth nr st).filterMap (fun (a,b) => buildRule g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (linkedSet g (k-1))).toList
  (k,ws.length,ws,preCov ws,rules,ls)


def prelim (T : Sig) (c : NodeContext) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)
theorem from_context (g : Forest) (k i : Nat) :
    nodeVerified g k i = (prelim (targetOf g) (contextOf g k i) &&
      (if k=0 then true else testAll (contextOf g k i) (contextOf g k i).2.2.1)) := rfl

theorem makeBlock {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → nodeVerified g k i = true) :
    block g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [block,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩

def contexts (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (contextOf g k)
def header (g : Forest) (k start n ar : Nat) :=
  (contexts g k start n).all (fun c => c.2.1==ar && prelim (targetOf g) c)
def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  (List.range len).all (fun d =>
    let i := lo+d
    batchRow b xs i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (makeBatch k ar (contexts g k start n)) (contexts g k start n)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (makeBatch k ar xs) xs (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,batchRows,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := rowCut_at h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold runBatch
  rw [List.range_eq_range']
  exact go 0 ar (by omega)

theorem cutsBlock {g k start n ar} (hd : header g k start n ar=true)
    (h : rowCut g k start n ar 0 ar=true) : block g k start n=true := by
  apply makeBlock
  intro i lo hi
  let xs := contexts g k start n
  have hm : contextOf g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hn (cutsRun h)

def boxes (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => rowCut g k start n ar lo num=true
  | d+1 => boxes g k start n ar lo (num/2) d ∧ boxes g k start n ar (lo+num/2) (num-num/2) d
theorem boxesCut {g k start n ar lo num d} (h : boxes g k start n ar lo num d) :
    rowCut g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := rowCut_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v

def cells (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => header g k start n ar=true ∧ boxes g k start n ar 0 ar rows
  | d+1 => cells g k start (n/2) ar rows d ∧ cells g k (start+n/2) (n-n/2) ar rows d
theorem cellsBlock {g k start n ar rows d} (h : cells g k start n ar rows d) :
    block g k start n=true := by
  induction d generalizing start n with
  | zero => exact cutsBlock h.1 (boxesCut h.2)
  | succ d ih =>
    have v := block_merge (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v

def listPieces {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => listPieces f (xs.take (xs.length/2)) d ∧ listPieces f (xs.drop (xs.length/2)) d
theorem listPieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap
def g15d3 (i : Nat) : Nat := 0xf
def g15l3 : Packing := (1,0,0,0,1,0,0,g15d3)
def g15samples : Array (Bits × Bits) := Array.mk [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbaf3ea78de4d799d,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff450cc90c3c245919),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdf7ff8fe9f9b7ed5,0x20812421801324c4),(0xefbdbf97f9f6bf6a,0x102a401415600a0a),(0xf3a9d7437375f5ba,0xfc028ab620235b0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : IndexTree ColumnInfo := (IndexTree.leaf [])
def g15autos : Array (List Nat) := Array.mk [[],[33,48]]
def g15levels : Nat → Packing
  | 3 => g15l3
  | _ => emptyPacking
def g15index : Nat → Nat → Option (Nat × Nat)
  | 3 => fun _ => none
  | _ => fun _ => none
def g15 : Forest := ⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index⟩
def key31l6 (i : Nat) : Nat := 0x820007028af371d000003180048302e380000000003819155875690d58000003d
def g31d5 (i : Nat) : Nat := 0x84001e90fd02fd01fa00
def g31l5 : Packing := (3,1,3,0,4,4,0,g31d5)
def g31d6 (i : Nat) : Nat := 0x11a20bf
def g31l6 : Packing := (1,0,3,2,4,0,0,g31d6)
def g31samples : Array (Bits × Bits) := Array.mk [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdafffab2d55fb9f999d9ceeefacb357b78f9ce2bb554a3bac97b2a9d65,0x250142092220460600407048c382809c2160e048740030a88143281c44),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5dfed46f26fea572a7ba9effd7341aff97ad1ab5bd2d547d6793334b,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90aa211010d10141c4300836206168204010183680184d04682483210b),(0x73ef3f3c8ff8df3fe567b556c9567ffcd665219778a6bd6e36bfd946ac,0xc10d0c3000214920a0d648109801012344d60802686b04210115006a4),(0x7c7fd57b7ffa3476e74d6f3fc4bddbd44dc213c5eb8bdea95bf6ee7492,0x38022048645c06490200044a25241818912934541000824c322ae5002),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fe76ff6451fda6ff84b6daf38f5bb6f6a5ee88a4d6be3f71c64aa3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8076989008882001270e063010011622500c04308a174300141c40a239),(0,0),(0,0),(0,0),(0,0)]
def g31columns : IndexTree ColumnInfo := (IndexTree.fork 2 (IndexTree.leaf [(1,0,30,0,4),(2,0,29,0,4)]) (IndexTree.leaf [(4,0,27,0,4),(8,0,23,0,4),(16,0,15,0,4)]))
def g31autos : Array (List Nat) := Array.mk [[],[50,65],[66,16],[67,50,33,16],[67,32],[67,66,49,32],[33,48],[67,50,65,48],[67,66,65,64],[49,64]]
def g31levels : Nat → Packing
  | 5 => g31l5
  | 6 => g31l6
  | _ => emptyPacking
def g31index : Nat → Nat → Option (Nat × Nat)
  | 5 => fun _ => none
  | 6 => lookupWord 5 25 2 10 2 4 (key31l6)
  | _ => fun _ => none
def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩
def g47samples : Array (Bits × Bits) := Array.mk [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffddffff5cfaafae7dd35b9ce7bbffd6b6b7b7cfbb8d3b7ad85ddf257b56b575,0x2200a042011011800c00803812181c2009c1061c0107200c09440143143444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeebefed537937fcb8ab173daa7df7f7691aff9776b2b7dcb92a3f3678b2b59,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9149112428688034a38448020d64a21d120601022ea84882b022a624830919),(0x77db9fef67fc77f3ffe6e3dd55f86b6fffcab66472f7c57fb768dabfad4eae,0x820641080010508440806b120004c020121a4ec1002247c020840112806a4),(0x78ebe4ae9ffd0d576de696b3cff805db7d426c00d8ded437ed436ff6f66c92,0x71419416322f057a950700411b6b328381c4110e8d4580325370f22d66812),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0bf9ebdb2287acd4afec26dbb6d98eabb3768bb508ca4b7f1fdd1c709a3f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80f74f1424444852a26637058ca3a012d22680c12e48c8e17411561c608a3b),(0,0),(0,0),(0,0)]
def g47columns : IndexTree ColumnInfo := (IndexTree.leaf [(8,0,39,0,4)])
def g47autos : Array (List Nat) := Array.mk [[],[83,32]]
def g47levels : Nat → Packing
  | _ => emptyPacking
def g47index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g47 : Forest := ⟨47,4,fun j => g47samples[j]?.getD (0,0),g47columns,g47autos,g47levels,g47index⟩
def g55samples : Array (Bits × Bits) := Array.mk [(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbfffffdf7defdfafbfd3fcebcfdeffcebffefe76de77fed7f1773f95eb2ebeb,0x400028000010005000000400701010180030103060043200102204010904888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb7fbfbb9ad3afd94caf0b9db5bbdf7f7d39bfcdadcf77ec9eccd2fb9cf16b5,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2484444214284026a4e002420468a8a43140a00408d944460a4082569431231),(0xeda5e7e7b2fc29de4ffc371dba2bf0775ff12db9b18bb528fedad96afcd3c5e,0x12589919410293410206d0396285445a082c5d2bf0022b20f0895d2048c2c4e),(0,0),(0xf1cd79264efe956afa7a64bb677ab40beba463600362eda36f3357b7d763926,0xe3a8651b1a36a0acc57538a080f6ea703078a0c13c28dc34c91f3868663126),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe05fe74eda341d5872cbf684d5e2ed19e7e3bba5e964550dd792aec724f479,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fb53db1204342a549861b60b6727a22d48ac0b14da4445855161ae724b471),(0,0),(0,0),(0,0)]
def g55columns : IndexTree ColumnInfo := (IndexTree.leaf [(16,0,39,0,4)])
def g55autos : Array (List Nat) := Array.mk [[],[84]]
def g55levels : Nat → Packing
  | _ => emptyPacking
def g55index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g55 : Forest := ⟨55,4,fun j => g55samples[j]?.getD (0,0),g55columns,g55autos,g55levels,g55index⟩
def g63samples : Array (Bits × Bits) := Array.mk [(0xdabffdfdbdf61bfbfc7dcbe34f7f1b17917df75df7edd9eff77b6dbd3dcebed3cfbfaddba50fcabded46bc9b579eb7bd3d92776566ad4ad3debe36d74deb7f9faf189ad76da7dc1a6b4eaf21eb254de4ae1f7451bb34d9456fd18e934db17349,0x4400202400040800310000100084000ac0000102800a1100490002240004b2800a001b4000190000008108000574009200040400000594000190004218c0010840002890800550053044a00410008802d0060013000c004400188120c206208),(0xb6678efeffcbf5a9cad5bfd527a7a5bd74d1314b7915f5b2ffdec2fc5d978f8ab3b44b2b5add5b771711b15ce99bf2b3f5bce975ef94cd59a34e76ab937848a94ef6be6c9579db5905539ea703c87a7d4ae11fe2ae423fade4a3c3299b0724e7,0x499461811a200a55004cf88854029340027a680613c002ec00233c1096d01045025d0203d400243150030b7e4900b00499e023395882049d0206ec00041398010bbb1000b7310ad00cc0858112c8207810e917400e423d0034024309910504e5),(0xbfdd27bedf8fade4776ebf9d185bc5bd76aeffb29711f77d628e86e5fffdff6d1a52bff6da987348e3e147dcecdbcc68d1accc4e7d7d77b9734cfbbcefbc022d72eff5a31a72e32584dd5a72accb1256ede309af577ea6b3ab2be572a2769632,0x20983204990108b1910222a2810c12a8041040402e00006394000908008912a582448429aad10a21a0240190b504314209040621245140c82010e8812042049440841100c0c52080310832a5111106e902488a012c82618908a42202729212),(0x77ddb87389d95f9f7bbe7e8eb89e6e76fbf75ca7fd5bb3758b555b578affe964ae7e7fa493e06d03bebc4fb5cff51e46b2dd5bdbb1eab66f60f7d916b9c6944fd85b6f0fc30a2ae7d2afc9dc369ef80bb1b0b2dd52e9331e786f7a5d38e8c8b4,0x1482478012444200420888514440810c402202189081ecc814422aa4c048408050190921c0450c000a080254044021081134422900082c11250884167012813a48094aca870a3283708e41084282480000c012150640581c30655a55288040a4),(0xdca768aafb78ce8d2db2ec3fbdddfa4ec963339dbac7a8e05eccbf0bb99ddf5febcef6dc7762a4a79d9ad8f70324ba6e724754bded1eed86f695f276b70acbd73dc66e39a88d0cfed920a0ee10b5a4dd5893bba709bff6dc1ece388c561e1ed5,0x210938550593284a984457082a220ca002159526023c0223a02100100d271046aa46f2022bb0201ea5730921b3008e848a002106a7520082d20653c8040064810364a00030c5086c0c2084761035a077101508a009ba22e00b822088521e1c51),(0x77dad76bd4ced656e7ec247a694c9eb5b66dc4de71aac18acebb177a9bac7a62d6f3e3996dd9d62d6ecf7b18557229a30b5ebb1ef46b568a8f3400a7c2d3365caade63d0f2234a24623735bcfaee29c0664eddfc63b2a86915f817ca03dc41fa,0x88252894b2b3256598a758928465236453b27d28c68c4c28a24dcc0d24d500d4a845700845b04bd175706d345a20a0a24d641d897dd822a1d52444cad2629c8e732b305273362844202335b73c8d8150424e93e44a78286995ec17c803dc01f2),(0,0),(0,0),(0,0)]
def g63columns : IndexTree ColumnInfo := (IndexTree.leaf [(32,0,31,0,7)])
def g63autos : Array (List Nat) := Array.mk [[],[50,65]]
def g63levels : Nat → Packing
  | _ => emptyPacking
def g63index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g63 : Forest := ⟨63,7,fun j => g63samples[j]?.getD (0,0),g63columns,g63autos,g63levels,g63index⟩
def g111d6 (i : Nat) : Nat := 0x120ff
def g111l6 : Packing := (1,0,2,0,1,0,0,g111d6)
def g111samples : Array (Bits × Bits) := Array.mk [(0xeafcc7b96fc59ffd26c5e2bb3d7bd378fb35ff5dcb26f92afa5f57eff59a73b7aaa379b2fc8d7a99e2ef9efcf4defd4efabc9c89733cebade5579ad5abbcd64d8557ad3d63bd1c6a75510ce3b9bf05e462ee0edf6dfb2914efc74c7d31727465,0x4d00310a2003881269402d0c00406ccc142a8012908082d00025ac006a88036948003229000032d4001bf20024ec2018680000aaf2500325400423a6f02003840040a8016ea8106822700071012c01d500600ad401ea0010f407087831504444),(0xf771ad34ff2bcf4fbd7f5f5de52efaeb7ebbabfffefbf2eab7c7cf56f8ecea565ddfabcf87cb61db9d6ef4aecff7cebd76fe679cfb9935e6adabc77cdcdb677ed3da5e4f56b4cbe39cfd7aed1f519a6b999796b48a51f4f7b8ad91a66cc6d9cb,0x1204940050200482000010001c10308054448009004424020800871400ac0690000402004e0508404004081210450414000904018220d090010808000a44280600460810104d92040818880c1010088d8400200a10a1400808810604821909),(0xf5be76df5e79b8b5d13f5f6e3ecd176fbeee538a7cfb9f7f6b7fad9b13bb7fed97560ecd71f29f3f1e3ef959a338e3a9e32bd5e7cfc7b51df73d7e9e165479b3baa9a0d59e62e11eead3ad5c624777de8699f96d3766d64d1f3fa2ca8f3d2e52,0x8e4d19200884440101e4a802e100a0c04000830eb000289800c49240c1c411082c325a6812b0485430294040c52402008322a4b0e00c0021216842103a050a9080848145264020288841a770220547500211500d95204c05521120880b352452),(0xde2ebbc73c1cf83c4cedbed77297d7f5b666582db23d5c5d7bf4a54b37a75f4992f88d683d388ea5bafb57791a5deb9b257390777cf70e9d329773c24416edd93fe3d2909bc3b81d7e62dd94d70a759eb42b6b51587d63da2e7eea6ce78912bc,0x10b22099c5638280b403142808691e02bd9d04d1097a9640ce2041351e20e64283892100494815238b12089820999d9858901b4e1903515e001721098578a5416f515492d981d895722018845902b08a5c4a2a2248dd03d08c66ca64e48812ac),(0,0),(0x4a99db5e74fdf3bbfb83b4b12e735e58f515867b75942dba656f9eeac55739b971685432ece5b39368c30fbbb9f895ca9efa5eceda2fea7be4766f052ba5def635ccf928215f7640050f6846acafb2ca6efbba0bffbfdb9043d87d111c3c3ebd,0x12d68401de50564414b80023f49c0203c0413d800068400bbb08034f0177ac0427f40400f6de0023bcc009fc1201950403ff4900082ea08a2fc908010c8a4053de0011e801464d050407f806ac13f8026d9b800bfa055d40038875010c2c3ab9),(0x107b7e8791b6519a9ebd6f37d374faa298392ebad8b5e4afe6bd267679568b3365bebaabdf6ef4e9035a918e8ca50ef74769b2b74aea726a09a6c5e9463715fb76745a9b1b6212a1b9add6dec52a9ba55b57e399ab660ca6d0f217384af881fe,0xadc48a6a24248ac9294916cc74a18dce4988890976a839d0a90054480a8f001149b409fd5690d8d50882129489ae3083c83b5253565cd02541ca4550f495b985581508b28aaa022919a1e755a00eaaa54243a315f06a0c87d4f216384a7880f6),(0,0),(0,0)]
def g111columns : IndexTree ColumnInfo := (IndexTree.leaf [(4,8,99,0,4),(1,32,78,0,4),(64,0,47,0,5)])
def g111autos : Array (List Nat) := Array.mk [[],[83,32]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
def g119samples : Array (Bits × Bits) := Array.mk [(0xfab75f3dfbfa3756f92d9ff7baf5ff7dbfebb9b33bef7dcdf77fbffe7bbbf75546cedccfd6f7eb762bef3ffdd2ede7abbef7e4e4b775eb9be6ab6f4d5fde77f2b955ece57b3feb97c6d99b5cdd2fdd2ea315de5f3efbf8d44ddcaa7566eda9cd,0x20100000802449000a820000c1900042800052080010000098c000620802429000050a2000012e00000be20013404000082000047420011240000c8b8000110080002480036500158018000c4009400c9000c0062803a0400e00885042a10888),(0xaf7efcd6de9febfb57d6f5ddedde36f3db7fffeed79fdbfafcf255738c743cbbbff3e3b86b8f9fb9f5bdf54fbff79bd74f5afb3f7fba34f5bf5f9afae879ab5feefe93fa9ee6566f7bbee6bf67d426d75cfb2bace9344fabf72bd58e999b76b3,0x9300010000091004000400382060802420900110020801010208161810541520000000800198110400c004084880812115000049028020c0800220200009220a01801050108206a8408406120184808104430800802442850101410609083421),(0xd3aee9d1a16b8afb579b1b1a2ede96c634714fced4ed35afb8d86696aabedb2eada373270f48f3a9b93de8a90d87d8f6684756adef8eb40bf672fc78b9342c9c7aaa652b2aec9422dd38b32b2a5255bdcc3d35b2da5f372953f3c4ba3a70d996,0x2c07b23e74020fd2aa41748155856818d263d681015680dac92709c7448b08586eaf3a512642c64b613a9091954b38c222671d26711d023332d48951dd0691952839212f8b6888039910b9ac2a42653c283c65315b1b95185ae084b83270c996),(0,0),(0x759a506bc07865de6f37bc2fabe39a5e2705b6a3eec6bd3cca572e3ed72f0325f632aa43d8e0e833eaeab6f86ad5fa72dbaf9c83b9e70faa212acf122e177ae733d8fa39a0b0bb12b7915f7134c3b9a9ed98d75362b1d9c725676c3caf04637c,0x16e5f59c6d01a255c44806523c0cddb5529a2196d082e7c24415d298c0f10d071e6090549dc090f8ed501938009f3fb2169588d90b0b506d102e01343cb84ad135f45369a498be0a36011e712702bb816af81651c4b05c0701a6642cad046374),(0x6339c3e76f77dc41ec6c9766b8b0f93592cd6e58a17db2abb9eea5cd269eeae2dc2c1c9ec755bae6a2821f6b678c3538a75edaf56c57e97ff4e8b90d55c4e75ce36b37ac511be4c610c6f229b9ab77956345b3a117ef6f3608dd37697870ba61,0x84ef690f5888a6bc0049f9381c0ba0115db000874a075d2102333605e754184fe100105f739880fb92c019ec481f2d2102dbf2480954a0ad3f922114724920d57f80032e5018c6a22083e62199863ec06b43378157e41d3d00d937293850b261),(0xd5cc96ab2735f4eedbcfece9fd4d847149d75b8aa71ff3959066dc7566c66ecb75975abde9bb8d684d89311f3151135dd1ce4d97acd9737d0b4d97b62b1596cf57b51ab1b6b408593b67d5bb928b32dabad66fc43367241aeaae177095e247ea,0x481560b0cd924918c5323d4303992d88d1232e6a49f254a2454320824e8122936522ef3572424e688310332525616c12e023da92a435d213539c9243b254cc21b63548a8e4258841b361f1c95a017252ba1c47902bc1245a7a8e167094e243ca),(0,0),(0,0)]
def g119columns : IndexTree ColumnInfo := (IndexTree.leaf [(4,0,115,0,5)])
def g119autos : Array (List Nat) := Array.mk [[],[84],[98],[84,98],[101,66,16],[101,100,66,16],[101,84,82,16],[100,82,16]]
def g119levels : Nat → Packing
  | _ => emptyPacking
def g119index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g119 : Forest := ⟨119,5,fun j => g119samples[j]?.getD (0,0),g119columns,g119autos,g119levels,g119index⟩
def key189l7 (i : Nat) : Nat := 0xa81337040d4b600002948880000590cc33d41450272020001b1
def g189d6 (i : Nat) : Nat := 0x82000f487f40bfa03fa00
def g189l6 : Packing := (3,1,3,0,4,4,0,g189d6)
def g189d7 (i : Nat) : Nat := 0x1f5859bf
def g189l7 : Packing := (1,0,3,2,4,0,0,g189d7)
def g189samples : Array (Bits × Bits) := Array.mk [(0x76b7b935ad7f6fd4d735f26d2df10ff4361bcad97bdde979efcd6e58b7554d7ea7eff73e73de92e56562d7533a4ef3de34b1f6acf1d6e216666babd43dbaabce3ad8d545ed4e53771cb4e6d84ab365f9722155b0decf672135d0ab0e8aab3265,0x8404642124899480a2a81184400c4494a40542200633c0114901482008a100b4c40690c02a500485280025a8300be5004d078022244028e4a0122910034dd0088624c002500565400b4701a401901a06a801c60d40e430038408b0c08aa0264),(0,0),(0xb725f7b34edfbeffaf8e64c99fca263eeb8ebd6e6efba6759d07fff35f0d57cf0f1af1c8e8596f2d9f9a363b65aade972ff9af593499366f72b4e55d5e6f961954d5fce693a74e66d370dbbd59357a0ab5d8c2e2b4913d9ddc0ac963246654eb,0x2019084c910042485050a84580141012107000421c10cd02a29a004c0424911090cb1414ac1a4012048a60a1130c00921224ba8854044c203120d1318881010110848d88109408245548f0845c253042044cc0e02091152804424943044214c9),(0x6b3b37beb0d3b3db67cafb77eb9e1dd789aebdb18d1db77732f653e35977f97f4dd313687fb67a399a5d29e7c5c2df2ae361e9d1a8a6a7bdf9b41bf76bf3c59c972736ba642a6ec8e10ddd388a5d8a2fef454b2f6c5cd8cb4dafd1a5458caf32,0x84c42401462a8882042c15880121e0040f09501440a3008044047580824b00c92204cb801220a2e8d004050a8c13a8082552010080e322ce0002224042220e86c96110212062d680201609100358082de8010e0a0c4e080169249024018caa32),(0xeed4ecfef66eeb7efebdd9aee7077cf1671b7b7a97dfdfd372d0ed94ede3ade9c50737565e265d36d07689d4ac4faafe5abbfdc5676e89f79f8f9a623b38502f3db98ff0fa982b81b88d0790fae9d8d74f74351d5187af7a955e769667c1914c,0x112b0124099000041080680538580102a03620812918016ca82b084951200b0011391441e40a1406003a00a460640102802906c05910d52121d05c00b8012058249003c452192901d049060038a0e052051c011422a1a0780618649266411108),(0xd9cafe65094bbf5f7264b7bbce3ffbefdc6762cbb35969c8ac2ddbae62ff5a5f3ee2cea13be5ccd265ed5a725a1921f7f9e712e69e98fb2d45e97fd5f2e0abe4f3f7676b375491bf662220c7ec1235aaa52f7b260bfdf8f023b73c589c1c3f19,0x2215018860a440b0408528403b942810a5b0009c1c080302094a000184016510830b02e2ac10b810014a60046c8c012e120b028809b84c0105208c4e88802201101131880274018a550300819c02301e012cc3000b90a8a80382305084143519),(0,0),(0xe9cbc8feffb7f8e7b8d17ff4f26deb6af5fadcfef4fa8da189aed6c66eadfbba567e7aa58acda76b57bfee9d03799233ac5e277f4fab9af55d736c18d65d30adcab7ab9d1b9dcbcc02d24b67373e9182d29baedd99bcc115aa3d04dc337a48be,0x1420360100482d00252a00a2440945244a022b202187302c44004bb2035a00002400090800450025fa000d1a80010240a950404582409154ca522280124a1c0c672a40054909a2500214036203d800a092812c0514244211e81d048c33284826),(0,0)]
def g189columns : IndexTree ColumnInfo := (IndexTree.fork 4 (IndexTree.leaf [(1,0,188,0,5),(12,0,177,0,4),(16,0,173,0,5),(17,0,172,0,4)]) (IndexTree.leaf [(24,0,165,0,4),(33,0,156,0,4),(132,0,57,0,4),(160,0,29,0,4)]))
def g189autos : Array (List Nat) := Array.mk [[],[84,115],[117,67,32],[116,83,32],[82,48],[84,115,82,48],[117,116,115,114,64],[83,114,64],[116,50,80],[117,84,67,50,80],[84,115,66,112],[66,112]]
def g189levels : Nat → Packing
  | 6 => g189l6
  | 7 => g189l7
  | _ => emptyPacking
def g189index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 5 18 5 10 2 4 (key189l7)
  | _ => fun _ => none
def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩
def g127samples : Array (Bits × Bits) := Array.mk [(0x27ec63be833e95d9cd8b1b0f8c7b949b955ab7ff06f2f46fb53d19a8b89e2cf938ea5b637a679113a99b1a558cf5d3757100e2a2d92956b1df648864a3a84cf9f5aafcc4980f547cd2d2abacb351593072ded0ca36876c216b176a15583d3069,0x215000b22a840210400a1040082a19401000220004808d00802008c02014082088420800402688520818425544410445400040805130408104600820a3600c001020e0440008143510802b10a111102142440000168440214816081150281060),(0xd1272c7d4d43f0bd72e56dab39ddfe7c6a407c139e413a8c95b2f6c7134bd9d2e6151acc0f6f6e61aecc859cb80ab9d38d1f9c08bbd08127631b9fb156aefb042a9049abe4f27cdb8815184a3fa2b5dede495570df2830da3c38c46cf1426d13,0x806000d540888802080408280406213088804000000320c048631024209804006241648090164a10080940a08001912a8109004a2408004431a0101080453200880088a80c0004a880100481a02008819080040c10830122428406420422c11),(0x3757a63bdee4ba3fd3e2275cd925bbac4327c3605b6a92ba668b6b375f5956a61c0ee4c8b6382a0c726a8d674c1d24e187c7697b46618e9a3259ec9e635cb1935494676727a9c6a3df6b34450ca72f271676b8367562d5a985429aaa9a64d626,0xe190134200c030558e6885084d0788a40161e860830e0412a109c61098d030850809a9902628890c322a09e446182064058721691005078a1841cc5c6248a09654242521162044855722240404692506023498262462c48981029a8a9a244222),(0x7c12f7ae7cb67a121957d4766ab145360dad0baa714fd5dd4ad95b9245e39e4cff88a61691dd24ee5570ea624367b54a6aea5375c626bc6f4082772e38770d5a1955fa1dcb198b20afa8d659c70c9ab5dbb42b955b55e374e0f839c3068a9694,0x100b203118264280010702e3020864421484020c18c0438c4090018044060d7096401604915660c20151c00201478d0220604290c2020821402022221025140809114a0c4919231288809339110498f1918002911b15216460582041008a9494),(0x5f0ed2cab79191489f9794fa9f865222c0c45f4f23977137ba6ec87e2fb718cbcb3281372d8190b9e5b2713c276012285f3b185c628f375c96ee95cada25845527c7ad5b31bc018c667be7de6cdf9480211b73e5e0fc0e1e03a683a80feb2399,0x4e04900c0410144f3ce0e018c1840020605099a3823d30032c4ce03413c1e08c412481b32c810028f486342022205010179b1c44008d375c030cd5d908008055e282051134c40088667900c444ea04000013f960e0680e1a03a083a80f412309),(0x64ed11ab034e6565aa5f6f0a73fb2abb553e90eaf5f2056f4f2ad1a6a7112f3107edc462d825611a42150349a39be3bcbdfa3bf68749fd950e410251758bd0aaed7e1f93ab81b400f6cd22629068e5bc2da9dbde283bbf115009f3b1a197a662,0x46299909050b25a18c71e62a5095c63ecb8f04a3c26b60b927cda532c109201915ade64b3091412042050108b390e3bab9cb9877060097580a090251508bf2aae7571e1ba185a2088a6c00621068c596ada8d9f5a83bbf101009f3a0a197a602),(0xed72aa63cb994444b8dcf183254b4e7cee24db3ad729ab4a1ba98c700af5e5480459e832e1cc5750368c89edf172492ed4565f186db3259850f427f3943aea1f7b1d745054d56ed5059c9e36e00b68fdae413f628aa9c64ad98b04d0b38dd9ac,0x4400b2628be723745844a119668f0ccc9303b92a933d014173710ec9a0c0658c41596832a4cc13563c0629c5d4a2402c44020f584d31651810e10cda143b2c95631f726414156f15141896b3a1182c75a6e53b222aa1c648d9830490938dd1ac),(0,0),(0,0)]
def g127columns : IndexTree ColumnInfo := (IndexTree.leaf [(32,0,95,0,8)])
def g127autos : Array (List Nat) := Array.mk [[],[101,66,16]]
def g127levels : Nat → Packing
  | _ => emptyPacking
def g127index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g127 : Forest := ⟨127,8,fun j => g127samples[j]?.getD (0,0),g127columns,g127autos,g127levels,g127index⟩
def key191l10 (i : Nat) : Nat := 0xa2d43b28d7001ab368009df79a6668d8a485480048c00a24000002900046192841e000000005078511fa7b8000001d8000000000050332001c2200008044
def key191l9 (i : Nat) : Nat := 0xb5d65558d2140ea31b806b286019a820212fb2e35aa613228a5a077246e6fc20ca1a41bb2d080a9c3e39f318874648000323b01b537426ceae26842215792e4b19e71cc72290229e7cad73d5f333056000d205f83e366a30000000d49821b1f1088000bb771a5c8c0000000000eb0000e0cb6ac6bec3c000c1b800347e18451880000012040006004d1cd8e0000001866e151a0000282800081e2a5e9518b100010bc00000030815564ae0000000000000ba722a1a34000000e6c5a954a6f09e6780014941d61a7112de27d595e7f09e40be3dc9678ab0bf3d70002c438a3dd4912345fe50900b4e481ecbbcceb07786be83e621d46430465b9b583a98309000098f882ae3a444b1d707c001bdad01b2c800179a0001f6d90464c82da1658b094500004b589e042e51604dd58429e06b90ff614389938aaeb6d12bb049522a72f25c09129e0463116174d50c3960b150c0a182d435d81d03dcbc0b346f3525916e494182a5649d22c9002ab560902d0004c5bd2828ce425700001e0842090d9c2ec56f6a2934aac61902201440c3800d7464005040d9808000b00120008008026140608781000c78f2e086830a0c98000580830000a023a002141e004000c001040a00380
def key191l8 (i : Nat) : Nat := 0x18cd14b25011e7225b26001876a3412158c6fc726c2320d6e3243bdd05603f1613ebb0007f7c604089b00125f5892200bf9421800b5e245039f1cf3cb8436d7f2000047800310000002025492575bf0012c00000042000001b8021c00800c01d000c080081
def key191l7 (i : Nat) : Nat := 0x2c
def g191d6 (i : Nat) : Nat := 0x47d6448788a00
def g191l6 : Packing := (1,4,6,0,2,0,0,g191d6)
def g191d7 (i : Nat) : Nat := 0x1021aae2c480c58812165850610304200048200685020d100000000000200100000fce5cec0b2a49f918c877974664f4a45403b36312c2722140f0a0500fd51548d13edd3641903fd51544d03fe92540d02df57305d02ff10305d02df4179dd02bf5819dd02df5819dd029fd819dd02df5155cd019fe885c901fe92440901ff114409019fc8788a009bd849dd039f5819dd02ed6668ce11f56558ce119f47840a11f3a5591200eda668ce00f5a558ce00bb9841ca00fca3388a00fb24484600fd23384600fe22284600
def g191l7 : Packing := (28,3,6,0,2,8,0,g191d7)
def g191d8 (i : Nat) : Nat := 0x850910304081c2440c0e2128f09183458e0d563c424bf1e12406128b1c7846402045834a31022c1244b4112285081c2449f022410c0418818084041a2060210127868c180849614f082043003c28008103c00a001050011a0c10d03085c404064a2030a0610180108a409488504804aab1e40a0610805408d7f063c2499716b62841c098f1800a084818401971629005810a08556544b736241080077f04053c18a8a2824181120efe78c80844603045000e102828008e8b070510443840106263000efe5858a100024042202241d09811e292070e043021810a5c588002801000c0052e2c5001418110006003021810c08516144821810a085042001810afc7897e3c49e14f0a7850604482184f83a8258107f37d67c179c77f77274572070b6f66e16cc6bf6aa69568066b64e63962c61f61a60d5f85e35ce5b95ac59758256d55053b50e4f94d44bf4a247d45843b4264113e43d73ca3b53a039338635934432f3122d52c02b328e27925c24f22a21d1f81db1be1b11a419718217516815b14e13912c11710a0fd0f00e30d60c10b40a709a08d08007305e04903c02f02200d000ffa4c91ffd0548ffe93227ff41513ffa4c81ffd1640ffe83207ff49503ffa2a81ffd0540ffea2a05ff4d502ffae6817fd2340bfe89a05ff40d02ffa2e817fe7740bfe9b203ff51501ffa6a80ffd24407fe91a03ff5cd01ffa0680ffd72407fe81203ff4da00ffa47007fd13803fe89401ff88a00bfceea2dfe774d6febb247f74d923bfcee91dfd7644efebaa27fd45513bfcee89fdd2344efebb207f74d903bfaea81fdd3540eff3ba07f744d03fba4d19fdd168cfee83467f749633fba2b19fdd058cefeb9a05fe40d02fbc66817f41740aff3ba057f5cc02fbc66015fd7100afeba203fd45101f7c8880dfd73407ef19a037f5c901ff20480dfe77407faa2c23fd4d611fea4708ff503847fa81423fd00a11ff209007be44803fc81c01f78ce00ff205007f901803fb08c01fe4da00ff28b007f935803fc92401fe45200ff247007f913803fc89401fe1ca00ff445006de668cfaf2ac67f58ce11f7489007da33803f511401fc84600
def g191l8 : Packing := (100,2,6,5,2,12,0,g191d8)
def g191d9 (i : Nat) : Nat := 0x180327c7c11a70600f8f1304b1c05f0c3c541303017c38f1204e0ef8f13040180df9e0e080325463418a006077cbcf0238c0ef961b3c041381be3e0900df9e30006fcf825f86eb1755933dd9099319085000ff517fd35ff48ffd13ff40ffd02ff00bfd01ff803de33fd847fa00
def g191l9 : Packing := (12,1,6,7,2,9,0,g191d9)
def g191d10 (i : Nat) : Nat := 0x1f3c11ff
def g191l10 : Packing := (1,0,6,4,2,0,0,g191d10)
def g191samples : Array (Bits × Bits) := Array.mk [(0x6acfda3c2cb83a92b793db4cbe83faea9cb2634793e21db352fb83fe8df2bc07a86d83614e9e1d6652f73c866931a299021d0d35cea03b8bca899a3ae9b0852968ae39aed598c502d3cc66c95e3918558ba9636cd1546c95b4522b12e41c6251,0x8027018c1220821109402382a0c04040242201142810004800310a01021028020024504420900008134444101889108100844480011218a0808a088000429588a002494484002118004005c4110108908c2000154441190520210a0142200),(0x7913ceb593e8bd03514889e55f4c93639759259376fb3230720c9a865196f27cc74c193b9b758265cc3f7b6a39d891145642471fe1a3e402ed12036d66f3fc532a7d00122732be1cd6f8a0d631223ddb153772d463789a2c383ce02e7842d163,0x88036081c60419a2c82401d04754b2b302101402821d5c654204040641a4c69d42c491108805a675482c4b1a3210132646402113b58224122512010966d1b044833550122312b410427aa086012a6ec1101538c042289a0c282ca02a5842d161),(0x557693cafd0fd9424efb95e75ddf8ed5bd78c8ecb52fa208a8d45cb3574ccaab77d93b1e650b4399e9518160864e914bee471a4d6078d8cd3710b8c5462d299957d5836e24a95a7b253cdb2e6196070b78eaa32a2b4a267149c447650cd138a6,0x10c082401088400012d0c4008000004018ca8080142020182010002082500860100b028600824082a011044180428040210612040030c884904098c2002801191040822880a108c8040449084010010648220108084220210140474504110882),(0x9c642d62a2f2f7ba22bc048df67d49f5212576be5994f8cdc5e270babb8959b792802cb3e87f90d4054ae918d4ab1ce241d9cf541d5d16b72277276810cef58c9e0f2a3137066d66292bcd81a96583d025d9fd03afbb585aa2b81e898b063d44,0x8024093988519a8e002822a41919198600217873085849c0c483198871885081c08060615e498874054ab3104029780240914c50140c132321226228088464808a9608100702c12708ba84812c642a102598ac01a5195852a098180889063544),(0xd23eefb5d75806b89dcda38864b64661c9f5e2babc176a70b2d3a56f26f32e727e31fe7789e6e58a36284c9dbcb30e74d59821a10b67441120e71511dbf31ab50b42210b3baf1a3e4c47734dcff8958cfd1109f7ce27c18a062741ac46d7cd91,0x7413208444084451d48501104604c068b3980408840422121160844600658c78341c18180024668a9220480b8c940760b50821038273441010c51501633a18440140258228a50a1044455344031a81ae1001013e42228188062541a446c1c891),(0x44ee3263ec00331534507b30f50239085a477dc26fc97fafdd3677e1adedabf5a6627a917685fed951e16b05c441608531a6eebab7bf0ffa2c9d6923c000425ae070ded9cbf43ff0702d561449016826463c1cddf881bbc98109fdb0912bda0a,0x5c9601812402000310c10a308504200a188ca4d220b13a418220c4ac1700cc49329049900289169c4a408a09044020043184b638a739649c2011540242004250a0701ac901871eb02048c310010048264632184cec01aac801096da0110b580a),(0,0),(0x3ab08ab4b6d74c50e56bc9651caf5894b179e03465572acbdca5615696769c27053d6dc580568c9318a62a712d4d06df8fcf0933a8a96615b24c8891d85dee28deccf746ecda09546a23c7138dbf2215a9d969340b49504d34d905859a5a4fc,0x8020482e4971b288ed202044508b9ca5050108094844412451461041282e3192c9648008d0242841110660a6538444294c484083188002614b0e00011891a8820d8e45006648e00548a230c32acf32918089829300b41504d204901848a4a474),(0,0)]
def g191columns : IndexTree ColumnInfo := (IndexTree.fork 19 (IndexTree.fork 9 (IndexTree.fork 4 (IndexTree.leaf [(1,0,190,0,7),(2,0,189,0,8),(3,0,188,0,5),(4,0,187,0,7)]) (IndexTree.fork 2 (IndexTree.leaf [(6,0,185,0,5),(8,0,183,0,8)]) (IndexTree.leaf [(0,8,163,20,6),(10,0,181,0,5),(12,0,179,0,5)]))) (IndexTree.fork 5 (IndexTree.fork 2 (IndexTree.leaf [(4,8,163,16,5),(14,0,177,0,4)]) (IndexTree.leaf [(16,0,175,0,8),(0,16,166,9,6),(1,16,166,8,5)])) (IndexTree.fork 2 (IndexTree.leaf [(19,0,172,0,4),(24,0,167,0,7)]) (IndexTree.leaf [(16,8,163,4,5),(8,16,166,1,5),(25,0,166,0,4)])))) (IndexTree.fork 9 (IndexTree.fork 4 (IndexTree.leaf [(9,16,166,0,4),(20,8,163,0,4),(32,0,159,0,8),(1,32,30,128,5)]) (IndexTree.fork 2 (IndexTree.leaf [(35,0,156,0,4),(40,0,151,0,5)]) (IndexTree.leaf [(48,0,143,0,5),(56,0,135,0,4),(128,0,63,0,8)]))) (IndexTree.fork 5 (IndexTree.fork 2 (IndexTree.leaf [(130,0,61,0,5),(4,128,27,32,5)]) (IndexTree.leaf [(136,0,55,0,5),(160,0,31,0,7),(128,32,30,1,5)])) (IndexTree.fork 2 (IndexTree.leaf [(32,128,27,4,5),(161,0,30,0,4)]) (IndexTree.leaf [(129,32,30,0,4),(164,0,27,0,4),(36,128,27,0,4)])))))
def g191autos : Array (List Nat) := Array.mk [[],[84,115],[117,67,32],[116,83,32]]
def g191levels : Nat → Packing
  | 6 => g191l6
  | 7 => g191l7
  | 8 => g191l8
  | 9 => g191l9
  | 10 => g191l10
  | _ => emptyPacking
def g191index : Nat → Nat → Option (Nat × Nat)
  | 6 => fun _ => none
  | 7 => lookupWord 1 3 0 6 0 2 (key191l7)
  | 8 => lookupWord 17 64 6 11 5 2 (key191l8)
  | 9 => lookupWord 68 242 7 13 7 2 (key191l9)
  | 10 => lookupWord 9 46 4 10 4 2 (key191l10)
  | _ => fun _ => none
def g191 : Forest := ⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index⟩
def g251samples : Array (Bits × Bits) := Array.mk [(0x7c5b1073c997e37379da30f398119ee6fb6b9ec3f472bcb960b6e16b764eab308775a6f93b85666e9d3190b2b24d642ca5712b6de7ab3f7906c1699135342a691b3ae0a5aa4ef7bb316cf861cfcc30541d6a6cc4992b1a999615c8e8d911c1e1,0x2118206040004a02130d09680103a002090a061080141a8c00302460220208340600a251588102029c90b010225400202065234404234e080480294178042009180840240246b20a0024c060c50410001a48a084882a181106058840c1114140),(0xcce5a5f376b735aeaefe578ced15d32ecca61663a9af3bd1860bc21b19116b79223f9d41251db7915d2d676e62aaa4f819f9d341f91890478f7c179edecb18b88452ff03ce59b2503e9c1117dab8cd95ebc956b7a216470f30e3a2b3ec2d18bb,0x4842cb022293909020208080c0985104462050200a232050248f580a09002349282c0500277025a04229050a00aa2098018840837118b0c40a78400806c358a084123a0140090810bc8810142aa8e601010152222014470a10a222b02c2818b9),(0,0),(0x615f43b7c5899d56d0ed540d07e5651da134ed341e9bc1f74f237fc0ae8a342e74d0d54381c29b89aafb968c73300f2ad24e70d94c925aaf7c71d97b8e42ee34b1eb0d1c78f57307cdbb8ab0333b96f243ce283ea4988c525a6cf93575cb22d6,0x600508638c1a9f0381c44ce96aa5f40532886e32158a42c5402a7e6c4a89343c9410964685c08b09acb0120c353c06229a6c00c94c92de87444159522882ae0499430c1549527146cd2ac810537252985246622c84980c521a4cf835558922d2),(0x743743261165c64a5893c74b56706899b56f313d76fa70640bd59bea9f4cd6cd40c9796a92725dcea2baccf628444b5fc70e36349d152cf473b98c6d967cf8571ea4949a30a5a9a67c52f2db3fa12e66e966315b35ec80fa603e034c2e56ad7c,0x8e228200012500a04432a202145800c8c044118122412020998581138524c38140cb492802205484420a48e00002411d45001410a1402070b13084088559515204a0a28a24a10ca03050168720812c4621201151314480a8603203082a468c2c),(0xf3d9bb1a8ffcdc97c518eaf4c8cf14e122f0fafd99d5fdca7ef0f64eebb658a39d280ab679b66835384c18039df39cc970c09cab32e75b6d986af50aa1e14f67f56dcf6f41924d79e9e39f3990e7fa0a34138f4a5e417d209f607f101fc4fe09,0x9201861738918010c41062040c8818244620088911c0e1638783100880a45083c120082600262524204640020401ded90000982b30080131d06c4002816148a041658f0100904561e8880e0910f0e60220020e2216414120916065101cc4aa09),(0x8c34b489b6743f0cbbb4f14fa7d16d9fa49b993f9ba2b3789eb911d5e1cd7a6f64e2a177140a8013c504eb6dd8b5e7f7e94f5a351463882a81261e97691b96dcefd6ddbc37c1e3432aa0876640524995f6a595fd43d7d81429dbe94302afe942,0x269c30c1984c0e0408d2577d35632830a8c6a4165540daa693102041644d9ca647426045188a80110514e824d9155760ee46136c04410a2a918614976910825e2b85c52c35a0b36b4200852245520814f6b484dd43c398142959c9430287e142),(0x1bb2ab4aa0e85ba9e596de5ec3ce129b01134cce9757f2d674620576a8bd96bf3a893c9457f0a28da9ccac591d7731877093a6c205d64d4c2bcaa6363cd0b55e770f7a466dfb2a9c82572d4ce3aa90cf64d9c30549ce2fe50b809671629a567c,0xd9639e04222012901869c59f133e18908110146a61f169c201c69140019863c2e851098d7d900098988b54119762026501322c440c64c4e0e9086343c860556368a70222d632a1a145321c6e30c00cc44fdf181498e2ec50a809261621a5474),(0,0)]
def g251columns : IndexTree ColumnInfo := (IndexTree.leaf [(8,0,243,0,7)])
def g251autos : Array (List Nat) := Array.mk [[],[84,115],[99,65],[118,84,115,65],[118,81],[118,84,99,81]]
def g251levels : Nat → Packing
  | _ => emptyPacking
def g251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => g251samples[j]?.getD (0,0),g251columns,g251autos,g251levels,g251index⟩
def g255samples : Array (Bits × Bits) := Array.mk [(0x9b665c544a8481c32c829a3849d25a0c2e734bceaece0410b1910c9246b692285657c973ca335d593cb00f0546b90059eb43e97a932728851785431870f031165ac8b80393ba6e576270cc58c906b870841734e15dc89803598ab05c2460a6b1,0x104454110880808228020a2041d8002c08600a02808c02009111060244ac12008614a1024802115108904700443200508241c8821224200116051018407029164080a01212302c0942400010c90428108414142154888803090a9048202086a0),(0xf315668af28fdb1ca228365b7ccc05a0011317731e21482f697635c521d4e57b4580944cacd08190116899ef79421d834fcee4e488905930903982805fb1c61927af17aaf49049a676974192f0d0160363a1bd03830701b0dc1f8281c2dc6123,0x83112a82400c43108201140b24040542001210600e014836084820c40800442b4181104024900000902098cc210099010006246088901220003082011981800902040620cc814002101041843090160043212902810201b054050081825c2101),(0x380526282fa13ac851f4c9c505254980d6e8ec3804b3594a769d93b950ebc251b0d8e2a15610b8154799066089743516386914b45de9a6e1e91c2d64aa4bec2945782990b2d68e61aa4d3cd1b24a6ab680984b4c1298da14a63264e421a50a46,0x184000082381184051a442400021c800c760240c008201086414493150c8805030586481420228050588002082640402084818905528808149002d00020c144045280184104604602a043c40824a60b20098024012185a048212646400810a02),(0x96903da21572f2b1f1c959078994a771bc47364121282ac5966e24786e0f6b8886ae49c27124b27b7242ff2e0094e0b4b1b582696d3c94568c371a6b03b30075a8d6353ad9672c0089eb12ba6325f80dd24d451b8459a7c113618d0b812f118c,0x86100cb01034a2a12848198388d4226018030240202c8a411a0a044824066a838a240842212092185a40cf0a0080e094a530c6680a1400448645526011312024a0c7343889210800016b021a61259805924545098441a1c11120810b812e1184),(0xca830c6ee5a1c1ac77b2c4bb013b84b271c7189edce77b42164b82b2ec44ccc2202552493f52e619512b4f09e2177ba801c291327039cbf4fba1fd7ca29d36ceca40c4508827295a1b45be11b7c00687be220f65622167c80c13fe90c415919,0x1282044674a181cc515204830038803270c71014e5265b22464b9241a4004482002443590d10ca0850630203a411b2a000c201185038c3861ba0d078200d6480c204804048212d4a89449e11258006869a220d60222163c80c12ea00c414819),(0xadcb89db333a54791fc5b16de6a74b1fbdaa5224c4caa060c8434905e130b3e50875189fa3aee40ebf67487ce98db2673644923b555505294552488c144494c2312ef3656d2d51ee39b1b44e04f3d3ec4d148000ab72771f011403179f478e82,0xa991884a13221d3803c5e045a0014312e78660240442614040424905201081f109410899826ca6043646807ca808b20b342020284941850001124c8410049440302c118d6904416438b533460072d3ec490080008b50771c0014031517470802),(0xccf1d170b069949f14600d7679a83ea985e068495997ad010287ff4ea745b576050c4fa9e8e0fabd2497448bd27a5aa8acea4ac0268e4d44dc2df9de452a225ad1457b3d721818b9bf9e05034d50ecb938aed67098a522a72856072e55b8d214,0xce85130b040942f1560095449a91aad8dc0e80b5196a18140955b282345b194266c47298868eeb9221d4601c27a00e8acf04a8036004c04cc8c58ecc43a23d68161791d311c0cb9abcc24434d40e8b9388ed67018a522072852072e55a0d214),(0x442aa5b9d884c622461c21eaaaf556fac8da8923687abbfb99c9c28096422e0eb83cb34c1d8918aec8c55d99f53bc2670104934ee2f27258616b2c55a56fa8970e02486406e9b92b5242282d15890d903f02672424a3e96d3ce1d022fa0aa8e8,0x460a679588446000a40a01aa08c414e80818810338389a92898982c08602320ec02091061180118a88016c815113416481048146a2821250206d8051a4632a958802cc600689381b004a400915810c003602652424a380613ce19002e808a0e8),(0,0)]
def g255columns : IndexTree ColumnInfo := (IndexTree.leaf [(64,0,191,0,11)])
def g255autos : Array (List Nat) := Array.mk [[],[84,115],[117,67,32],[116,83,32]]
def g255levels : Nat → Packing
  | _ => emptyPacking
def g255index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g255 : Forest := ⟨255,11,fun j => g255samples[j]?.getD (0,0),g255columns,g255autos,g255levels,g255index⟩
def key383l12 (i : Nat) : Nat := 0xf8400002630000023000000000000000000b83d5688000000000341000030000000000814000015d0000000210344000018d003b10000000000e080000000e70005c3803500091000000000008
def key383l11 (i : Nat) : Nat := 0x404c001fd7a0dd080d1200990f207c017043e0ac430a491c9aec7438f32422a414035a0e000e6f384202824e3e5491f317a0090ee161490000d0e481ce32000c4b9104c1860ad6100030920000000003c06000000722ae38f1200000035c780290bd08d23d219503209024ec0512fd44dc0985ef07266b48508d728f004824e9809324688ad260642ee33843c9e425582082c2260138002f8f81ac0c0002216a57414583e222000012800202204f00400024f34c01300e78608380c041012080080846040
def key383l10 (i : Nat) : Nat := 0x8a7028008f8208641c25de616202731427f0aa3ea6a9bc18603a40bac46606be46000184a7c7d25a0000000b98af69a264a6b01ac3b3a21709000001146294f5b28f5117b2b2368000000119a0000000503689a2858e10b056a96282c8039064ce4000005a1824c4b68b4a1ca0160003a96c1c5108908a005faaaa16a13000042ba8544116a040004b6aa18802880c23178071841517e2559911705a04117c6495c00000000085d314e242a96a0880000a01fc56687256502c84968668866a1180000003d68390f815a1fa922000012b8020000c2a6caf0234475dcf201fa032887c28e092c47a60725df80221bc02a000007a61e192100d1c1f61f683d817642e40874ab202e012c0cd05141d60b104cb094626909c0000000c0e573a858d7326a6285e00010ac0007468e22e50bc16f60921b5c8f41249001273800322800110cb04e0005728622182280ff076809bc29a93800081a596455d1053c0607cc3a5870000108081400524002801c04219100c0821c60cc13c0c2030a201001e00285000001f020030024000800c08280
def key383l9 (i : Nat) : Nat := 0x6977b1303806491384c288005f480044300b4273a470aef249bb09d0238c000000000000000603688ce51876813ab9e6c881d7b37687df408050502a181c84000606800000000000000424bbbaa9612800409100800346576b8a520800702905aa985610b9a10486080010008502020c0020a18085
def g383d8 (i : Nat) : Nat := 0x7c610014028800000000000000302080140040000000a09b827d78736e69645f5a55504b4637322d1e19140f0a0500cef45d94a2103afbaa93760801f7445d0744d03aaf69017618038fb68a9960d01ad76949760c01af34a89760c01af64289760c01adb6943760801aeb69037608018fb6683760801af94683760801afa42837608018ef690988ce009fcaa9190de009fa68a9944e009deaa99504e009deaa99520e009ee690988ce00be6690178ce00be6690918ce00be6690988ce00bf84a83784600bbc6989384600f749de3384600
def g383l8 : Packing := (25,4,6,0,3,8,0,g383d8)
def g383d9 (i : Nat) : Nat := 0x2dd0028c0601f18c02041010022160ac183c0004580028bb3c71c058816e807460680741c30700441602883bd0180c08009e92a09189248391a905315048c4c0a178c440a1c344e20480c5e3ec8c4124f1f67a1c70097c7d918050801b86cae3f18d8123489e81e3f187030392c68303e84a0683078305e30e0607e38f83c60f060a511f174250341f8c5e031010ee21078c3c161c0cee22050c28801004142c00504800c7c3000f402160a08ae97100120112003c70a082689408970b120030209083000c003000838e14007c610001c70838e1020020212004000023e3ec8cb8e14489e2f1a14a23e23d15c47a2b88f457115cca2f195c5e3ecf438e4f9debbcbf80ec1d2799709dd3b93626add2d9db38e63c8786afd5e3b876b2cad6ca75446864ec9992b24646c8990d60abf57bcf1dd3b7e6bccf98f3075e0b6565abd55ea85452734dc95d24a3b45a858ff9f13c6754e39b9356698cc18a2f85dcb916d2be568a61472724d08e918226438650b3138214370570800a4005ff65c1840f7fa2f442077fd9720d01dfe9bd1080dffa6537006ffd329bc017fd9704e009fe44a2e81ddf6541840f7ea300c2077bd94a2103ddeca51081cff6468840ffb20e89a07fd41844d03def4422681cff6241700f5fa2ec3007afc1761803d7e8cb0c01cff65d8100f7ea2ec08073fe99604039fe44a6e80cff65d834067fd32c1a03bdd8320d019fec4a0680cff64e884067fb121b8033fd9760c01dee9bb0600ef70dd830067fd32c1803bdd9760c01dee4bb0600ef7a65830077da6ec1003bec37608019fe44a6f005ef65037802fda521bc017f5190de00bfc8486f004ff22513802efb2a09c017f90904e00bfccba07007f644d03803fb20719c013fc988ce00bfcc9a03007fc406118027f93108c017f8894de00bfd4ca6f005fe46437802ff32e89c01ff11744e00bfc44a27005fea6513802ff32e09c017f99720e00fec89907005fe64483803fb26f19c01fd9138ce00bfc4c467007f645e33803fb02f19c01fd8918ce00fec4c467005fe64c81803fb46640c01ff11384600fed19c23005fe26211803fe26f08c01ff03784600ff849c23007fc8ce11803fe13108c013bd94a210397f4cb0c01cf7a6583006f73281bc017e9290de00bf88c86f005de65413802ef32a41c01fd23384600
def g383l9 : Packing := (91,3,6,5,3,11,0,g383d9)
def g383d10 (i : Nat) : Nat := 0xb1c029771ece80316e3a8b78f40771ca00d1002da03a69a8d16d01d28d4d3292968b98ba7f8c288f4271a30301042b0c2ce3d9d0c753d16f1a58de8639cbb8c715c8d44b554a1a9a3e0a89a12200921586544f91de7c3c6840c59058fc73e70a427a578082339c40459aa8af185209a7d34148d4cb55354aae60605689f215010071ece816c5e382c02c0800b78f67401b1c150a01655c62e06083462ae3d9d02d06c70541505820071ece801e380c14030a8b4a07c8d48497c63f8e66a4b4202e31fc73a14025b571ece863a00201e95c8d50005c7b3a084978e980d957652718d2b8da90a038f655cc3ed026a4b80d9d0683120b8d0ca07c4503e24b0080e3d9d0c73a100400171ece863a2041f8deb9e05d31c9dc29ad59e194d8397a571169d5a94d53c132d2591c5050edce08cf4b60acc9f89047f075c62859452044c3f83242b025c208114003ff45d03ffd1840fff06103ffe8840fff44d03ffd1700fff05c03ffd37407ff60d01ffc83407ff40d01ffe88407ff4dc01ffc37007ff4de00ffc37803ff44e00ffc13803ff8ce00ffe11802ffa2103fdd1340eff60403bfd83406ffa2101bfd83007fe40e00ff901803fe4de00ff837803fe44e00ff813803fe20e00ffa33803fe20600ffa11802bf61803bdd83006fb60801fda33803fc84600
def g383l10 : Packing := (41,2,6,7,3,12,0,g383d10)
def g383d11 (i : Nat) : Nat := 0x540b1d9a02e3804632e686a85e3b342382008507c4a8582c71cf98063b342397069da95ca003fe81ffc03ffa03ff007ff007fa00
def g383l11 : Packing := (6,1,6,6,3,8,0,g383d11)
def g383d12 (i : Nat) : Nat := 0x11b280e4ff
def g383l12 : Packing := (1,0,6,3,3,0,0,g383d12)
def g383samples : Array (Bits × Bits) := Array.mk [(0x22c0d3a3723e453b61b292904161c19166ba4156452239cb2ce776d1285888036922ca069735ba1c39466bb49cb80c880d6801ee650cd2ea8938a452f08d3169a1612a59384753bad95626662c63076161205bac29b905015369815a61884cb1,0x22a042a308281022412222104041018102a0455c0820218028210490004898014122a802062510400900403480940c80084001804506910881200012c0203148e041211030641239500420000c630440212052a0291101014268811220880c80),(0x3e4782180591e1e8ca415c93fb0e30440ddb7b080a80044a5e58703417b0ed0da2975b6df4e0151155ba1024096257dc7280e61c3739c9924483ab0a0d0a407f268250f5cf15b48886f76ba0ccf46838068d8de07060e07838bc1a040b61c283,0x9028018810161088ac0504223081040850928000290004c425070241b00400822080144b0c0241004a20000482053184202c40808184882448102000d0800b3040a404084018c8080110220c214483800898940502040781814120409604201),(0xc3b0d0243e2c92704a6d0bb89a642e3e324709614c855ba1b03c2574c53f0c84bca3b709607618aaaaca1686a79e094292d1a5b2e1a729d1ef4c761d2455891cd68664af136132ce19aaa19e6c55a2caed1460758145348a6cc923aa16a49516,0xc22070243c088a32102908b09820ae3610c20125cc051d809026055084360c62d8a3320940364922a8484682858e00c384d420b061233141a94434152055010c599024a50348105611a2a11e2441a2c2e41460350145348264c921aa12049512),(0x4138264952b1d12493a4452d72585b389605825093cff11edb60090262cf75191c382db2876b8a708e04945dba40fc5c0117030382d504a579e551698e39d387601c521a9a75d96750089c8958b895e01b82b803f01d0be08606741604bc230c,0x1080c0b03b031008084040c42504188060180103100c00a0a40008040890111041009902b010250040410442a404c140103030210c08ca050a00048c0a8c022200c1018d83149210000148108b815200b021800b00809600202141404b82204),(0x7a0c641d50044e150338db871c0d9c6d8b49b017941b1c71c485efc79a14e6ae159b09d8c200cd085276a758cd18f3623c4db7d00870524c281de7f5fe3e2adc1756b294808a0882ea6a1f2df107bc01d0df010f4d40469e2105ef94c107b239,0xd004201450464809021899a3188eb82288483003841b1c31c500f247991664ae92090048c000c90e723223084509b040f48cd45008304046281cf3843e140e8407928284000804822b6a8b24f004a801d0dd010f4440469e21056a80c1079039),(0xcc62da0a5fa8f5e2c996caf343c42faac6de9a345ff56a94813a6425060416282f4d23c281526277465dd835f65817a533b901ad51024edaaa84a94a69219208d911c25be8aad34a7f39eda22807bafd8e8540012ec5ecf42900c6dcd341c02,0x8452d0021128d5c8c9144a91d1c007ab845a00141d69e1982122246c02041428290423d28902225305595421e41c17a5023985a908040a15a0c4800269208200d9018058b1aa90485c38f99a2803baf58c8040010ec1ece00900c4d4d341002),(0xdaef1c77688221978d1e0c4ad4cf460c43747468370c9781a044ccfb808507cfc7550e6f05834be93d3c1e4e94918217a4e0da637baa95002472c84f89f63e421033ad28de7ab208228bfb0281a229d272553696158289b300da2c9976c32464,0x92e959624882001701040c005417432c02544069252c9701a0048cc280a00e56d4150e31071309c931151f4c9213080304e00a4233c09500a002c04d90b29c403071012c5a3a310c128ab91220a221c27244349605808983008a2c9966812464),(0,0),(0x941a1aee99450a81362f36506691ad42486aa7b56b55a36c2710c35afdccd2f0604110c2892f54d343a9228b60c516b3ea6e18394813263b179331842a516d8adc29c7c000c846f164b52014130d4016a078833106127956c94690a3b81ad1d8,0x4120210904c02803268a2402080b401402a07040a01006405204110294490a020401002d0205402c22800a1400c2280a20c04a14813021a0411310009012188c000460020c0069060300020050540108030832102126010c94480229002c198)]
def g383columns : IndexTree ColumnInfo := (IndexTree.fork 29 (IndexTree.fork 14 (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(1,0,382,0,9),(0,1,332,50,7),(2,0,381,0,9)]) (IndexTree.leaf [(0,2,312,69,7),(3,0,380,0,6),(2,1,332,48,6),(1,2,312,68,6)])) (IndexTree.fork 3 (IndexTree.leaf [(4,0,379,0,11),(5,0,378,0,7),(7,0,376,0,5)]) (IndexTree.leaf [(5,2,312,64,5),(8,0,375,0,9),(0,8,99,276,7),(12,0,371,0,8)]))) (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(13,0,354,0,4),(14,0,369,0,5),(16,0,367,0,11)]) (IndexTree.leaf [(17,0,366,0,8),(18,0,365,0,7),(19,0,364,0,5),(18,1,332,32,5)])) (IndexTree.fork 4 (IndexTree.leaf [(24,0,359,0,8),(25,0,358,0,5),(28,0,355,0,7),(20,8,99,256,5)]) (IndexTree.leaf [(32,0,351,0,11),(33,0,350,0,8),(32,1,332,18,6),(35,0,348,0,5)])))) (IndexTree.fork 15 (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(34,1,332,16,5),(44,0,339,0,5),(49,0,334,0,7)]) (IndexTree.leaf [(48,1,332,2,5),(33,16,326,8,5),(56,0,327,0,5),(64,0,319,0,11)])) (IndexTree.fork 4 (IndexTree.leaf [(65,0,318,0,7),(66,0,317,0,8),(67,0,316,0,5),(65,2,312,4,5)]) (IndexTree.leaf [(70,0,313,0,7),(34,64,29,256,5),(256,0,127,0,9),(0,256,23,104,7)]))) (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(264,0,119,0,6),(256,8,99,20,6),(8,256,23,96,6)]) (IndexTree.leaf [(268,0,115,0,5),(260,8,99,16,5),(280,0,103,0,5),(272,8,99,4,5)])) (IndexTree.fork 4 (IndexTree.leaf [(288,0,95,0,8),(289,0,94,0,5),(40,256,23,64,5),(304,0,79,0,5)]) (IndexTree.leaf [(320,0,63,0,8),(322,0,61,0,5),(258,64,61,0,5),(352,0,31,0,7)])))))
def g383autos : Array (List Nat) := Array.mk [[],[84,131,98],[101,66,16],[100,131,82,16],[82,129,48],[101,100,131,98,129,48],[100,49,128],[101,84,131,66,49,128]]
def g383levels : Nat → Packing
  | 8 => g383l8
  | 9 => g383l9
  | 10 => g383l10
  | 11 => g383l11
  | 12 => g383l12
  | _ => emptyPacking
def g383index : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 17 68 7 12 5 3 (key383l9)
  | 10 => lookupWord 57 200 7 14 7 3 (key383l10)
  | 11 => lookupWord 30 108 6 13 6 3 (key383l11)
  | 12 => lookupWord 6 61 1 10 3 3 (key383l12)
  | _ => fun _ => none
def g383 : Forest := ⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,g383index⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low3 : Lower (vars 3) (graphGoal 3) 1 := size_of (hints:=1) (by decide +kernel)
def maps3 : List (Nat × List Nat) := []
def known3 := extendKnown [] 1 maps3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid3 : Known known3 := extendKnown_ok baseKnown low3 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low7 : Lower (vars 7) (graphGoal 7) 2 := size_of (hints:=257) (by decide +kernel)
def maps7 : List (Nat × List Nat) := []
def known7 := extendKnown known3 2 maps7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid7 : Known known7 := extendKnown_ok valid3 low7 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom15 : graphValid g15 (boundsBefore known7) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s15_3_0 : block g15 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl15_3 : block g15 3 0 1 = true := s15_3_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables15 : checkedTables g15 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0 = true)
  · exact (rfl : block g15 1 0 0 = true)
  · exact (rfl : block g15 2 0 0 = true)
  · exact bl15_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low15 : Lower (vars 15) (graphGoal 15) 4 :=
  lower_forest (g:=g15) (i:=0) (hints:=8449) (before_sound known7 valid7) geom15 tables15 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps15 : List (Nat × List Nat) := [(15,[]),(23,[32,67]),(27,[16,66]),(29,[65,50]),(30,[64,65,66,67]),(39,[32,67,84]),(57,[32,65,82,83]),(78,[64,33,67,84,101]),(99,[16,33,66,83,100,101]),(135,[67,84,101,118]),(156,[64,81,83,101,118]),(163,[16,66,83,100,101,118]),(165,[65,50,83,100,101,118]),(166,[64,65,66,83,100,118]),(172,[64,81,82,67,100,101,118]),(177,[16,65,82,99,118]),(198,[64,83,100,117]),(281,[65,82,83,101,118,135]),(305,[16,65,82,99,118,135]),(312,[64,81,98,83,118,135]),(326,[64,66,83,100,117,135]),(330,[64,65,82,100,117,135]),(332,[64,81,66,83,100,117,118,135]),(344,[64,81,98,83,117,118,135]),(353,[65,82,99,116,117,135]),(354,[64,65,82,99,116,101,118,135]),(396,[64,81,82,83,100,117,134,135]),(424,[64,81,98,67,116,101,134]),(480,[64,81,98,115,132,101,134])]
def known15 := extendKnown known7 4 maps15
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known known15 := extendKnown_ok valid7 low15 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low45 : Lower (vars 45) (graphGoal 45) 3 := size_of (hints:=8965) (by decide +kernel)
def maps45 : List (Nat × List Nat) := []
def known45 := extendKnown known15 3 maps45
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid45 : Known known45 := extendKnown_ok valid15 low45 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low51 : Lower (vars 51) (graphGoal 51) 3 := size_of (hints:=1) (by decide +kernel)
def maps51 : List (Nat × List Nat) := []
def known51 := extendKnown known45 3 maps51
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid51 : Known known51 := extendKnown_ok valid45 low51 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom31 : graphValid g31 (boundsBefore known51) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_0 : block g31 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_5_1 : block g31 5 1 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_5 : block g31 5 0 3 = true := (@block_merge g31 5 0 1 2 s31_5_0 s31_5_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s31_6_0 : block g31 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl31_6 : block g31 6 0 1 = true := s31_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables31 : checkedTables g31 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact (rfl : block g31 4 0 0 = true)
  · exact bl31_5
  · exact bl31_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low31 : Lower (vars 31) (graphGoal 31) 7 :=
  lower_forest (g:=g31) (i:=0) (hints:=8449) (before_sound known51 valid51) geom31 tables31 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps31 : List (Nat × List Nat) := [(31,[]),(167,[83,100,101,118]),(313,[81,98,99,84,118,135]),(334,[80,81,82,83,100,117,135]),(355,[82,99,116,117,118,135]),(428,[80,97,82,99,116,101,134])]
def known31 := extendKnown known51 7 maps31
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid31 : Known known31 := extendKnown_ok valid51 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower (vars 47) (graphGoal 47) 5 :=
  lower_discard (g:=g47) (ci:=(8,0,39,0,4)) (hints:=8449) (before_sound known31 valid31) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps47 : List (Nat × List Nat) := [(47,[]),(61,[65,50]),(94,[64,65,66,67,101]),(151,[67,84,101,118]),(173,[48,65,50,83,100,118]),(181,[65,50,99,84,118]),(185,[16,65,98,83,101,118]),(188,[64,97,98,67,84,118]),(227,[16,66,99,116,117,118]),(230,[64,65,66,99,116,101]),(301,[48,65,82,100,118,135]),(331,[80,81,66,100,117,118,135]),(339,[66,99,84,117,118,135]),(345,[80,65,98,67,84,117,118,135]),(346,[64,49,98,67,84,117,135]),(358,[64,65,82,99,116,101,118,135]),(369,[65,98,115,84,118,135]),(422,[64,81,66,99,116,117,134]),(440,[64,97,114,67,84,117,134]),(454,[64,66,99,116,133,118,135]),(460,[64,97,66,99,116,133,135]),(482,[64,49,98,115,132,133,135]),(484,[64,97,82,115,132,101,118,135])]
def known47 := extendKnown known31 5 maps47
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known known47 := extendKnown_ok valid31 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower (vars 55) (graphGoal 55) 5 :=
  lower_discard (g:=g55) (ci:=(16,0,39,0,4)) (hints:=257) (before_sound known47 valid47) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps55 : List (Nat × List Nat) := [(55,[]),(79,[64,65,66,67,101]),(103,[16,66,100,101]),(115,[50,99]),(143,[32,67,101,118]),(174,[48,65,50,83,100,118]),(179,[65,50,99,84,118]),(206,[48,50,67,100,117]),(286,[48,33,101,118,135]),(316,[48,97,66,84,118,135]),(327,[64,65,82,100,117,135]),(348,[48,97,66,84,117,118,135]),(364,[48,97,99,116,118,135]),(376,[48,97,114,99,116,118,135]),(398,[48,65,50,67,100,117,134]),(433,[16,49,98,115,100,117,134,135])]
def known55 := extendKnown known47 5 maps55
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55 : Known known55 := extendKnown_ok valid47 low55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower (vars 63) (graphGoal 63) 8 :=
  lower_discard (g:=g63) (ci:=(32,0,31,0,7)) (hints:=8449) (before_sound known55 valid55) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps63 : List (Nat × List Nat) := [(63,[]),(95,[16,66,101]),(159,[32,67,101,118]),(175,[32,83,100,118]),(183,[99,84,118]),(231,[16,66,99,116,117,118]),(317,[32,97,82,83,100,118,135]),(350,[96,33,99,84,117,135]),(359,[16,82,99,116,118,135]),(366,[96,49,116,118,135]),(371,[98,115,84,135]),(377,[48,97,114,99,116,117,118,135]),(429,[80,97,116,134,135]),(430,[96,81,98,83,116,134]),(441,[16,97,114,116,101,134,135]),(444,[96,113,114,99,84,101,134]),(462,[96,98,67,116,133,135]),(492,[96,113,115,132,133,134])]
def known63 := extendKnown known55 8 maps63
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known known63 := extendKnown_ok valid55 low63 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom111 : graphValid g111 (boundsBefore known63) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s111_6_0 : block g111 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl111_6 : block g111 6 0 1 = true := s111_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables111 : checkedTables g111 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact (rfl : block g111 4 0 0 = true)
  · exact (rfl : block g111 5 0 0 = true)
  · exact bl111_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low111 : Lower (vars 111) (graphGoal 111) 7 :=
  lower_forest (g:=g111) (i:=0) (hints:=16785665) (before_sound known63 valid63) geom111 tables111 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps111 : List (Nat × List Nat) := [(187,[16,97,66,83,100,101,118]),(190,[64,97,98,67,84,118]),(215,[67,84,117]),(222,[64,65,66,67,117,118]),(238,[64,65,66,99,116,101]),(243,[16,66,115,100,101]),(318,[64,81,66,83,100,118,135]),(349,[80,65,98,67,84,117,118,135]),(365,[48,65,82,116,135]),(378,[64,49,114,67,84,101,118,135]),(413,[48,65,50,67,117,134]),(437,[65,50,115,84,134]),(455,[96,98,67,116,133,135]),(476,[64,113,66,115,100,133,118,135]),(490,[64,49,114,99,132,133,118,135]),(497,[65,114,131,84,134,135]),(504,[64,113,130,67,84,133,135])]
def known111 := extendKnown known63 7 maps111
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known known111 := extendKnown_ok valid63 low111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low119 : Lower (vars 119) (graphGoal 119) 6 :=
  lower_discard (g:=g119) (ci:=(4,0,115,0,5)) (hints:=16777473) (before_sound known111 valid111) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps119 : List (Nat × List Nat) := [(119,[]),(207,[64,65,66,67,117,118]),(380,[48,113,66,84,101,135]),(414,[48,65,50,67,117,134])]
def known119 := extendKnown known111 6 maps119
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid119 : Known known119 := extendKnown_ok valid111 low119 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom189 : graphValid g189 (boundsBefore known119) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_0 : block g189 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_6_1 : block g189 6 1 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_6 : block g189 6 0 3 = true := (@block_merge g189 6 0 1 2 s189_6_0 s189_6_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s189_7_0 : block g189 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl189_7 : block g189 7 0 1 = true := s189_7_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables189 : checkedTables g189 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0 = true)
  · exact (rfl : block g189 1 0 0 = true)
  · exact (rfl : block g189 2 0 0 = true)
  · exact (rfl : block g189 3 0 0 = true)
  · exact (rfl : block g189 4 0 0 = true)
  · exact (rfl : block g189 5 0 0 = true)
  · exact bl189_6
  · exact bl189_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low189 : Lower (vars 189) (graphGoal 189) 8 :=
  lower_forest (g:=g189) (i:=0) (hints:=536879876) (before_sound known119 valid119) geom189 tables189 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps189 : List (Nat × List Nat) := [(189,[]),(347,[65,66,115,84,101,118,135]),(486,[16,66,99,132,133,134,135])]
def known189 := extendKnown known119 8 maps189
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid189 : Known known189 := extendKnown_ok valid119 low189 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low250 : Lower (vars 250) (graphGoal 250) 5 := size_of (hints:=1366507616) (by decide +kernel)
def maps250 : List (Nat × List Nat) := []
def known250 := extendKnown known189 5 maps250
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid250 : Known known250 := extendKnown_ok valid189 low250 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower (vars 127) (graphGoal 127) 9 :=
  lower_discard (g:=g127) (ci:=(32,0,95,0,8)) (hints:=16785665) (before_sound known250 valid250) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps127 : List (Nat × List Nat) := [(127,[]),(223,[64,65,66,67,117,118]),(247,[115,84]),(375,[98,115,84,135]),(381,[48,113,82,135]),(382,[112,49,66,115,84,101,135]),(415,[48,65,50,67,117,134]),(446,[112,81,114,83,100,134,135]),(478,[112,65,114,67,100,133,135]),(493,[80,113,50,132,135]),(499,[65,114,131,84,134,135]),(505,[64,113,130,131,132,133,135]),(508,[112,129,66,115,84])]
def known127 := extendKnown known250 9 maps127
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known known127 := extendKnown_ok valid250 low127 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom191 : graphValid g191 (boundsBefore known127) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_6_0 : block g191 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_6 : block g191 6 0 1 = true := s191_6_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_0 : block g191 7 0 13=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_7_1 : block g191 7 13 15=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_7 : block g191 7 0 28 = true := (@block_merge g191 7 0 13 15 s191_7_0 s191_7_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_0 : block g191 8 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_1 : block g191 8 7 61=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_8_2 : block g191 8 68 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_8 : block g191 8 0 100 = true := (@block_merge g191 8 0 68 32 (@block_merge g191 8 0 7 61 s191_8_0 s191_8_1) s191_8_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_0 : block g191 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_9_1 : block g191 9 3 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_9 : block g191 9 0 12 = true := (@block_merge g191 9 0 3 9 s191_9_0 s191_9_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s191_10_0 : block g191 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl191_10 : block g191 10 0 1 = true := s191_10_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables191 : checkedTables g191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0 = true)
  · exact (rfl : block g191 1 0 0 = true)
  · exact (rfl : block g191 2 0 0 = true)
  · exact (rfl : block g191 3 0 0 = true)
  · exact (rfl : block g191 4 0 0 = true)
  · exact (rfl : block g191 5 0 0 = true)
  · exact bl191_6
  · exact bl191_7
  · exact bl191_8
  · exact bl191_9
  · exact bl191_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low191 : Lower (vars 191) (graphGoal 191) 11 :=
  lower_forest (g:=g191) (i:=0) (hints:=536879361) (before_sound known127 valid127) geom191 tables191 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps191 : List (Nat × List Nat) := [(191,[]),(319,[65,50,135]),(351,[64,65,66,67,101,135]),(367,[80,81,66,100,117,118,135]),(379,[81,98,118,135]),(431,[48,65,50,83,100,134,135]),(445,[48,97,82,134]),(487,[16,66,99,132,133,134,135]),(494,[96,65,98,67,132,117,134])]
def known191 := extendKnown known127 11 maps191
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid191 : Known known191 := extendKnown_ok valid127 low191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower (vars 251) (graphGoal 251) 8 :=
  lower_discard (g:=g251) (ci:=(8,0,243,0,7)) (hints:=1358970881) (before_sound known191 valid191) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps251 : List (Nat × List Nat) := [(251,[]),(254,[32,67,117]),(471,[16,66,67,100,133,134,135]),(501,[16,33,50,131,100,133,118]),(506,[32,49,130,100])]
def known251 := extendKnown known191 8 maps251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known known251 := extendKnown_ok valid191 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower (vars 255) (graphGoal 255) 12 :=
  lower_discard (g:=g255) (ci:=(64,0,191,0,11)) (hints:=553656577) (before_sound known251 valid251) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255 : List (Nat × List Nat) := [(255,[]),(479,[64,65,66,67,133,134,135]),(503,[16,66,131,100,101,135]),(507,[81,130,118]),(509,[48,129,82]),(510,[128,65,130,67,100,117])]
def known255 := extendKnown known251 12 maps255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known known255 := extendKnown_ok valid251 low255 (by decide +kernel)
set_option maxHeartbeats 0 in
theorem geom383 : graphValid g383 (boundsBefore known255) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_0 : block g383 8 0 23=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_8_1 : block g383 8 23 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_8 : block g383 8 0 25 = true := (@block_merge g383 8 0 23 2 s383_8_0 s383_8_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_0 : block g383 9 0 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_1 : block g383 9 9 75=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_9_2 : block g383 9 84 7=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_9 : block g383 9 0 91 = true := (@block_merge g383 9 0 84 7 (@block_merge g383 9 0 9 75 s383_9_0 s383_9_1) s383_9_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_0 : block g383 10 0 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_1 : block g383 10 5 16=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_10_2 : block g383 10 21 20=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_10 : block g383 10 0 41 = true := (@block_merge g383 10 0 21 20 (@block_merge g383 10 0 5 16 s383_10_0 s383_10_1) s383_10_2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_0 : block g383 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_11_1 : block g383 11 1 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_11 : block g383 11 0 6 = true := (@block_merge g383 11 0 1 5 s383_11_0 s383_11_1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem s383_12_0 : block g383 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem bl383_12 : block g383 12 0 1 = true := s383_12_0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem tables383 : checkedTables g383 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g383 0 0 0 = true)
  · exact (rfl : block g383 1 0 0 = true)
  · exact (rfl : block g383 2 0 0 = true)
  · exact (rfl : block g383 3 0 0 = true)
  · exact (rfl : block g383 4 0 0 = true)
  · exact (rfl : block g383 5 0 0 = true)
  · exact (rfl : block g383 6 0 0 = true)
  · exact (rfl : block g383 7 0 0 = true)
  · exact bl383_8
  · exact bl383_9
  · exact bl383_10
  · exact bl383_11
  · exact bl383_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low383 : Lower (vars 383) (graphGoal 383) 13 :=
  lower_forest (g:=g383) (i:=0) (hints:=12901687553) (before_sound known255 valid255) geom383 tables383 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps383 : List (Nat × List Nat) := [(383,[]),(447,[65,50,131,84,118,135]),(495,[80,81,82,83,116,133,118])]
def known383 := extendKnown known255 13 maps383
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383 : Known known383 := extendKnown_ok valid255 low383 (by decide +kernel)
def hashdeadl14 (i : Nat) : Nat := 0x4592c8500000000002800049a6c68a83340e9800000aa00684000000054a001bcc7001e180000682000000000000001d46a1840000003a00000001c
def hashdeadl13 (i : Nat) : Nat := 0x301a0007b2f00e0aa2992094818000e2e0000000269e056438000000000d33e40e4a200074d00000000000003b10001e0240a9bd45d962582900000000000001430001e1400000fc03b84a000614e69108a1108000810000d04c9d0000000408800000160f24180010b9d040003080001e0c000000000001997f401183740ee12000000000080d312c00102c00000000012070000000001d35000308c000a4c0001b30000000cb3800183000070f0000001abcc008002c8cc133000000000000000000000020b000000064ec0a00000f8000cc5000105d8204160001a38001c1c467309c000000a7700000016de30f80000008380b08e000d3001
def hashdeadl12 (i : Nat) : Nat := (if i<1 then 0x7b02c3200425d610a000042a0327300000000106b33757005e04600006037d811679d009461963480703e1077f067f2582384275d80a540a20109b59b4006305d00000000ab6dfb0bf59ec084c806986b30597776440b146b100c50a956520000878e0000747c463e108bc029e7600000395ef090d06800000000f0550000d0b1e4af00000000f324d141840ca4380000000051505017000067300000e779907b0000e77730641201ea62a089a48ff0924111e9a7a041b2a180aee462f29d9b47b01eb0427030e02a5973605b9086f08d5081d04bb014363000006038c0b6d110106cc731308e0023a07fb1305601ba1839b4c088a10b88011043e427e75a600831464016903d3ba52b1ec095000ec050b011b0730478f11a0000755e331ef63db004a00a000069a91680e225f60f90092a9d0000764650a40000c591f95ac03baa33c5a1283d11871a6d2772c01c1057280f201f5012328b908232a5505e000fe02b507cf0809817c267c05c9528506d997696872194b206264030ad402d007d586d7228701d30605840f67838625a51443ce034d47ed45f704cb08730a1794e1252000070330000b56f0000b0b4000000000000a842e047609d406ae26b67b08a4de12aa0a34019000000000000b664342c50b50000c0af924dc9aa401870366002b26d00000000841e0000000060986614000000000000783ae10d980ee051d0ab4022a615808f0000a0832619a148d81500007000e007d616b032d01b483f163f00104028276b2015141030631049a027580cd0a7a05ab977802fb09ff07a97899053b0a80816e83be0790a1b809b8b460a4f0000178b0000847be03cf139a1170000b07850b3605408416262696b908af0aa7b1f5b446070d024601a42492101d496f4b4e035922127ab0000e18600008284831c00440000f031500310656013b071b045b25b4113766b5b4c6b0800008291b4888a50000000000000e38b0000225eb04d807230618425c0b097ae226f809e00000000f00d93480485e88728040000b11c3039204e9432711f445c905f004a300b97ada05680211292f09a7b1a696f3106704f19748066703f00000204d074ba20a118f025458794596091a06f000065946020913b783e342dd08c819b5b452076c21dc075e0991a4a183c3b19d7a750a68058c8379643a487b408d0523762d062b422e0b2d47fc0ac224a46231a5dca3b6069a4390000768a5433e07e0000da410b00003102090604000a010a1f88080000080d030b0c310304001300040113030203141f0c0001000232030b0801010a010007110002020208010605020401010119010b0304070203070506000210070d110100150b0a0504051d050002020b05000c0402003d0e1500260200020108040b03090500060204000d0602010100180501000001030f04 else 0xe0a0512830933085c048e216509713746026a02ec09cb040548400000268f701103ac254729fc29e8096145a39ab47552144806e00019612b7b4491ea44bc1)
def hashdeadl11 (i : Nat) : Nat := 0x5b144463e05aea749a36008e0000f05f008fc82400000000057a08357304bb42c02b0000807cd1701823000007095811411b96631031e07218223334c77b980e8010305dd000180820521064ca3ef0420000409b626cd483a833f03ac022e048a008f80a513f0000db73410f3393ca38834018881012b081c465a02c6142704300002631809700000000715300007115b00dd054b2886014000054161b183099000000000129f0870000a24110110427972915960000477d5b457113518aa01a00007134a023d08a1053002d678ef06b604a6076520f5468b025698fe62d5060c1370000e07eb793c95be02a510198285417000000000000000000005b72220ea00f9098e036e09602120000503908396112556c56084a3a211d0342f0784635707b4293308d0624205556235211962a72516903a0190235010e7765e07d5784f16feb3c248834149073d088b0134091f720f0803275f0052809446ed494b01b1b0305939136b20cf495111aba390000db890950e9807026e609a0205015880ba66b8778d4967988f077f007110cd289d0160000e278401d0000000000000000f032027400000000a08c6209804c4030102eb368a33f3b1d798e0000538a70215061a44e228300000000000000000000d01710838075e4517067406f00000000609a00003253a089a4002093b00a8125000090790000c0599583180c00000000c0411830f1160047224900000000906992725046700b000050511a67544b00000407c35bb06d0000504d3821ca470002762e0000cb1760948827b10a603b4009e06552019464444f9688a0286169097ab82524185057db2feb3d000e6303670ac01e70822426b090d664c05cf764008be03c365d6a2549347068706a71244461f086277c5780380d698dd120b27c20626037d807f403502fe1110000ea6e5071301cb0388044704f411c809595011003b20deb1a98372208b0561092820a91190049704bb03ec070670890335001a03f64504063613c50294b430832441aba46e146c8120193598c103df8314066401fd460e0745084044c100c7760b24b824f4006205b0000563070507a7c9058000000006a440000506e3040e97d006cd027646a6207807fb0450138e56fa018704e8482e0356085662f762c5b3be05eb81f1004f836000000000000000046203a6ac89692730000b034807a613d00008145702433536a79b0407805012a04e80082c50a0c0e782286421a0e4c00400004833a1491a02243880c0851202004211c6408c1835c192e081800c39681005000c04e408002001860c34c8040000000400008087400400100892c38005148410524200800478080001438126000000020022
def hashdeadl10 (i : Nat) : Nat := 0x1c05302000382d2ecf474c3a08f618409ea54931a0a2272b385214e934380040192451090d15cc0564307983441ce005970002c06068f08a82680cc070001a2c5d4a1440400018207150002808001022205d856c41e1700072d518800084a2900000a334a12801820030b1a27
def hashdeadl9 (i : Nat) : Nat := 0x202e0
def deadd8 (i : Nat) : Nat := 0xa24b7baf6624ad253281df927589c4d52540d02
def deadl8 : Packing := (2,6,7,0,4,3,0,deadd8)
def deadd9 (i : Nat) : Nat := 0x17a6100d01602e1f830400f202c200003405840f980801c0010720e8006a183c001d000f8007c00200001509fc5a0b0071b79b2bc5ba99429c459e8d258238d84a14078280a00a7becc495a4a6503c6fdb66689a4d50287fcbc661a544d029ef9c6aed1840d02bed9c626d3540d02ff49184d52540d02ff489c4d52540d02d7f11826d1540d02ffc1184951340d029f6cbc4a1354950195fdc7aed2564d01ff49384d52540901ff61384951540901ef4935496aa40d02df49b54951340d02f7493549503a6502bf62cc4951540901ef6125456aa40901f7612545502a6501fb61284612545600fbc1284612344e009dd9c7aed258ce009ee9c6aed1888a009df1c7aed2584600ff42558ce2284600
def deadl9 : Packing := (25,5,7,1,4,9,0,deadd9)
def deadd10 (i : Nat) : Nat := (if i<1 then 0x2693540b3fecd1349aa055ff26d1a4d502cffb30d2a26815ffabb4610340bfec8c26a81a05ff626d3540d02ffd23092a06817ff1184550340abff5da6b4ca059ff4d5a1a65029ff9569426a80cffdb8aa9354067fed95549aa03fdb4a13549501affb7092b2680e7fda849593407bf69424ac9a035ffaed2564d01cffab15532680e7fd25aa993406bfedc26ac92035ffaed3564901cffab0d1b2480e7fd38aa9924073fe9ad54c92037fe6e13540901fef2b09aa0480ffd9384d502406ffd5da6a81203ffa4e12540901ffe2708aa0480f7f95864d02406bff5da714ca03df74e135a6501affd769ad3280d7febb49699407bbe9aa4b4ca035ff6e123a6501efda5091d3280d7fdb548e99406bff5da474ca039ef495a4a65038ffb63553308167f9b0aa998408bff5dd54cc2053bf6daaa461028ffb6a4d2268157fabb6610340bbf4cc24a81a055fe26d1540d02cff33155206816fd935aa90340b7f492d5481a057f66d51340d02ff924a89a06816fdaaa44d0340b3fcd42074ca05df64d503a6502efd24a81d328157fabb40e9940bbec89a074ca059fd461a1a65029bfb6f5524a80c7febb6a1934063fedc554c9a031ff6d6aa64d01cf7b695532680c7fdb2aa9934073fcd8554c9a031ffaeda8649018ffb6ad1b2480c7febb68d92406ff55da4a81203fda4d52540901fee34a8aa0480f7e92564d02406bfd5db2681203bfa496aa40901dfe22b5520480e7f993aa902407bf492a054ca03dfc45502a65019ff36755251004ff9b1aa928802ff55da5092c01efa4a11849600dfd2515524b007f692849515803fb88c24a8ac017deaed2545600def55492a2b004ffabb6a123802ff55da5091c01efa4a11848e00dfd25155247004ffabb6a1138027fc55a5089c01afe6a12844e00bfe5768c227007bf128461138027fd5db4a89c01bde6952544e00dfe23155227004ff9b8aa9138027fcdad5489c013fe6caaa44e00ff925091a27007fd11848d13802fed5da4689c01bf6aa92344e00bfb57692c67005fdabb45633803fac92a2b19c013feaeda844a009ff370d2a25004ffabb695128027fcdc346894013fe6d5a344a009ff576d1a25006ff1a844d12802ff95da2689401bf66963344a00dfe22755225006fda33aa912802ff55da71114017faaed1888a00bfd3709ac45007fc9384d622802ff55da6b114017fa6e11388a00ffc23089c45007bea8844e22802ff4daa27114017faaed1388a00bfe5769c423007fd1384d611802ff95da6b08c017fcaed2584600fee26a92c23005ff1b848e11803ff09424708c017fc6d52384600bfe57691c23007fd1588ce11803fe89446708c01ff44963384600ffc27111423007fe13588a11803fa49aa4a81a05fd849515409019bf36f5524b007bd2888ce11803df14444508c01ff08ce2284600 else 0x4000888405e986c113905805080340b02e1f06087905c2003f080d05c2010004400c0288128f50060048004020800804100127c503a3f6c170230c990618643002074409038882341900e30020304004060800870140c00228180045c08224a09086c45817020801a183810008ad48702001100108e2b0c1c0800456383810230b0200117dff6de0be2c10281f00a20021f8a108140c707c503e3f8bed83901520010dd505020c988c1183426000e000e00086905c20a40d058002020340034003c1834002fd2040bdb798060306e1b00c84f01a5f8a10bc3024202bf0c090605c00880505210010fc506e1cc0693effc5f6de600097e28190cc11092183f1414080603412860a40cc6004380038003800340034003c003c0020e00107000f000801c0020e00100f78ee2192287800ec3041c003c00361820e001f8a1e001e001e00100000b0411ef1dc4377ae886cc5917b60fc50f000d8e083e2840000016a420f6c1b1c100000b521002c30416383f1420003e284000100c4aca220cd523db61a02c91b20b40600a0dbf169c61a02c9f6de60578fe2fb6f303f8bedbcc0fe2fb6f303d0acfaceacb9c93c83c68c63c53c38c1dc02bd1bb6b9bb96b70b4ab24b09aeeac8aada92a77a5ca41a31a169fb9eb9e69e19d19b69a698b97096094593591a8ff8c38a889887284c81b80b7f07bf7af79f78f7747597497397297197096f96de6b867c64b62560a5ef5df5ae5725415315164fb4d54c54b54a549548547546545545044043b42b41b4164114013fc3ec3e73cc3a639639138137136135c34c33c32c31c30c3073022fd2f82e82cd2b229728727726725725224223d23823322e2292192142041f41ef1ea1e51e01d01cb1c61b61b11a119118c18718217216d16810009807204c026000affd7692d3281defdb6)
def deadl10 : Packing := (156,4,7,5,4,12,0,deadd10)
def deadd11 (i : Nat) : Nat := (if i<1 then 0x86120d08111f407ad1db072b1c206d11ab867718d8613174859115b85231388497118042910183c50e603570c082b709d822b07a8195055010902a80410003ffd1849503fff6692540fffd2546503fff4613540bffd9a4d502fff2693540bffd1a4d502fff4619340bffd3546502fff4d69940bffd9a4e101fff6a135407ffd284d501fff4a935407ffd9a4d501fffaa935407ffd3849501fff4e925407ffd9a49501fff56123407ffd9a48d01fff56193407ffd2864d01fff49593407ffd5864901fff4e192407ffd3564901bff6a11940f7fd9846503dff6551940effeaa46503dff4a51940f7fd25a6503bffaa99840b7fd1a66102dffaa99840b7fd9a46102bffaa91840bbfd9846102dff6619340affda564d02dff6559340affeaa64d02bff6951340bfdd9344d02ffe6a10340bff99840d02ffe4610340bff9a540d02ffe6550340bff91540d02ffe4690340affda846502dff6611940affda346502dff64d1940bff90346502dff6629940b7fd93a6502ffe40e9940b7fd18a6502dff4d69940b7fd13a6502dff66935406ffeaa4d501dff66925406ffeaa49501fdf4d525406ffda864d01dff66193406ffeaa64d01dff561934077fda864d01dff4a1934077fda564d01dff495934077fd2a64d01dffaa993406ffda864901dff66192406ffda564901dff65592406ffda364901dff64d924077fd3864901dff6a1924077fd3564901dff68d92407ff95840901ffe4e102407ff9a840901ffe66102407ff93540901ffe69502407ff99540901ffe68d02407ff99340901dff4e2994077fd35a6501dff496994077fd23a6501ffe4e928803ff91a4a200ffeaa928803ff9a849600ffe46125803ff93a49600ffe46925803ff92845600ffe4e915803ff92a45600ffe6a123803ff91848e00ffe69523803ff91548e00ffe46923803ff9a844e00ffe4a113803ff9a544e00ffe49513803ff92a44e00ffeaa913803ff95844a00ffe4e112803ff9a844a00ffe4d512803ff9a544a00ffe68d128027feaa661029ff2693540a7fc9a44d02dfe6610340bfd93540d02ffa4950340affaaa40d02ff644d0340a7fda8a6502dfe40e9940a7fda3a65029ff6869940a7fda864d019ffaa9934067fda8649019ff68d924067feaa64901ffa49502407ff11540901dfe64d02406ffaaa40901dfe40a99406ffaaa4a200ffa4a125802ffaaa49600bfeaa915803f792545600bfe6a123803fe92848e00bfeaa923802ff9a844e00ffc46113802ff9a544e00bfeaa913803fd92344e00ff649633803fd9158ce00bfe6a112802ff9a544a00bfe68d12803ff11344a00ff68cd12802ffaaa44a00ffa4e222803fe91888a00ffa4d622803fe91388a00ffc4e211803ff13584600ffc49611803ff123846009ef6929940fbea8888a00ff48ce11803fe22284600 else (if i<2 then 0x6718d1b071686b63b38c6ac837ab208143ea5f4a804c20460a84911c7405186a093027a82ae19d57d066c694fa70dcc0ac4ea478ce31a1ecaeaf303c8c241ac2f19b38c69c83fbee47302190238ea2305424c6856399d2085637d12388c0c16cbeff1d208076416c80b40c0049e29d5208144b23f46802b201800c183275231bc58d5919c2ba9ed854030806003067bf9c352078df64634afd056e600c20020b418eaf319c182b832c8683382f1c2de703e3ac80ac412003efc19433aad06707f7f38754282036168bdf159a0ce09fa590158824f17a919786904bef86bc33ab209458f7dd8e39c8904deff5232b9120958e0b701b7e8611b1e288d8776dd9609e2b1c2f1582105b80098e0b90124824976d090cd009250909820be81c002d484d8f144c3068ea08444c12222609117812260911961224208de83785dd4e900b63480dfc5edb981b80c307224fbfd4f301f09477d2a0d202e2010188cddb353cc69017202256222f7fb60add5a80164f6c116903054660bb98d200c6e0e18f8afa73037818602100ed9a0d20beff8bdb752d00186f7fc5ea78e6e01e33bfe2f534770c056718d202388c2401066f7fc5ea68ee1b388131a6862ef8df646718d182bf7fa963ac8ce31a3fbfe2f6dd4f31c70187010d8f7c2b7561a05a04ce121581816fbfdb3530d74005590a1982b682c8ce0be2f6dcc0184f14410307c705b875e98d59067d2d5c686717058176d8d1b06f7c92f17b6e602d3634e457030b7007d2a0b20be2be9500fdf0b7b6c68d029b1803bfe2d415c1bc57d2a01fbfc3600ead415c1bdf363c5c6a8eae0d8d3915c0fdfe0b00ed9a9a81c83fbfc3600ead40dc1ba9e3b0e77f1ab22b839c4d4e356457053ab00682c8ae0bdb341640fdfea700682c8ae0dd49c58d1bc4ea782c02c87d1a03753c751d873bf64634dc23dfe0a86c03b6755a03fbfd4e0164340dc1a82ea786c03c57d1a03fbfc36015c3aad01bdfe3a8ec3ab86a71a7211eff5380570d03906f7fc5edba9e1b82040ec751d87590fa7538d71ddc2586a198ec1bdff16b8ea71ae195efb915c7ab8d74068ed23878d423198bda2f18b3a2a189fa24788e221f881a1e387521a785ea14384820fd83ba0cb82a2071816203f8099ff97ee1f8b7d29f137b21e9179b9e377829ddd76c1d8d7581d3373c9cb17239c6170f9bfd6f41ba36e01b536c99af96b31a9f69c9a4568619f5665990f63618ab610981f5f517935dc17435c0969959b163558495c7566954f54b14f552f949151914374f393a14ce130b4b2929349c124347e11cb46c9185456112143a90a941c9063415103b4088ff53f70fc33ea8f9b3e30f7d3d68f4b3cc8f233c50f053bd8edd3b38eb53a70e8339d0e5b3930e3d37a0da73570d2f3368c7b3160c0d2f30b952d50b132af8a3727d89ab2580901226 else 0x6c244e0445e2e80648bc5050262048e47300a0565ed8f60346f5d8ae98260a0c0068580a0c27015b807c906026158e08c030604c2b2a82103cee10cc378bc503c5a1a381a3a2d03cb121b082409e29104f14d80b00b29b02601632490481068e0401093981802127303093987200a0aca00c1820060c1003060ba9e62b81ec8b40d15c753cc0a26ae1d5e606624740ac47cc0483c9bdf72398ae02b28b1eff6cec705e2c44719c65bd0520ccbd4b702a0c67030651f4282f8a37f6c0f90083dbc507c95c01a2901847d2a015c7efbab500764fd1d5a800524460a84613d40171bdf12bb67568e07cc1703e060df4d22a00b883dd40220c2777c2ed22a06e0defe90110884fd1d5a800526915008831e748a802e219d5c0560f91f4ea40c1509ef89ad00884fd0566800c25702b3400611df1500c10c813b1c0f00a44001e0b8625494a83ec3b7532876c0fa40c07c018307cf7fb66a40f0d782d231a682c8a82a1e8185ce3c519b1a206a008183e7be5a8cd9c5ab50287af14281809827bfc7))
def deadl11 : Packing := (183,3,7,8,4,14,0,deadd11)
def deadd12 (i : Nat) : Nat := 0x226c48bbfb654c3991828d28cddfe2ea731865c0891b87a0bb538ea405a3487b1d9bfa906e3a90b8064694310477f6ca947523051a4f7f6c2ed4a3a91828d23bfa90b0351c15a42e0191a577f8ab8d4e631c0c3f7e91b6d4c6b1c0c3811c4dfe2ea51d869c41234a020c7bed54772271048d2408d8efaa71cc89c4123490277f528e4932271048d27e9c5d4a830c011d1fe8c8d4907400c377f8bb6d4e1b04223bd3538ea46e23461177f6da950523047efedb538ea4608191a477f8ba94761a711a3f7f538e644e0191a3f7f5398d032019383963e9c516e8018413c39e9a98d63991b83b6205dfdb2a635a0646093df6ac6b41c816ae0f00efedb52a0493230488077f8ba95061970704f7f531ac732112b842091d02eff176da98d61b04a4140bbec8db6a6358ec1250d06eff1571a98d6830c994a8fd8b08517fb7ae74f70b6c76686125bc5665224e74a34684243d739334f30b2c728322d1e919c15810b0ac056000ffe92a07ffd1940fffb30817ff46102ffe9aa05ffd9340bffa26817ff46502fff4ca05ffd38407ffa6a80fff49501ffe91a03ffd93407ffb2480dffa6503bfecc205ff90340affd32815ff64d01bfec9203ff902406ffd3280ffe4a200ffc92c01ff915803ff247007fe44e00ffc89401fda33803fd445007fc84600
def deadl12 : Packing := (32,2,7,8,4,12,0,deadd12)
def deadd13 (i : Nat) : Nat := 0x22dfc5b6a90e86821a4efdb54c724410d1f7f16a63a18e01069005bf8b6d52351d0d049cf924d00ffd03ffd02ffd01ffa00
def deadl13 : Packing := (4,1,7,5,4,8,0,deadd13)
def deadd14 (i : Nat) : Nat := 0x17e2b6526070604013ff
def deadl14 : Packing := (1,0,7,2,4,0,0,deadd14)
def deadsamples : Array (Bits × Bits) := Array.mk [(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)]
def deadcolumns : IndexTree ColumnInfo := (IndexTree.fork 63 (IndexTree.fork 31 (IndexTree.fork 15 (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(1,0,510,0,12),(0,1,460,50,8),(2,0,509,0,12)]) (IndexTree.leaf [(0,2,440,69,8),(3,0,508,0,9),(2,1,460,48,7),(4,0,507,0,12)])) (IndexTree.fork 4 (IndexTree.leaf [(0,4,369,138,8),(5,0,506,0,8),(6,0,505,0,9),(4,2,440,65,7)]) (IndexTree.leaf [(2,4,369,136,7),(7,0,504,0,7),(5,2,440,64,6),(8,0,503,0,12)]))) (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(0,8,227,276,8),(9,0,486,0,8),(10,0,501,0,8),(12,0,499,0,9)]) (IndexTree.leaf [(8,4,369,130,7),(4,8,227,272,7),(14,0,497,0,7),(10,4,369,128,6)])) (IndexTree.fork 4 (IndexTree.leaf [(15,0,480,0,4),(16,0,495,0,13),(0,16,486,9,10),(17,0,494,0,11)]) (IndexTree.leaf [(16,1,460,34,7),(19,0,492,0,8),(16,4,353,138,7),(21,0,490,0,7)])))) (IndexTree.fork 16 (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(21,2,424,64,5),(24,0,487,0,11),(8,16,486,1,9),(25,0,486,0,8)]) (IndexTree.leaf [(9,16,486,0,8),(27,0,484,0,5),(11,16,484,0,5),(24,4,353,130,6)])) (IndexTree.fork 4 (IndexTree.leaf [(29,0,482,0,5),(26,4,353,128,5),(32,0,479,0,12),(0,32,94,385,8)]) (IndexTree.leaf [(32,1,460,18,7),(1,32,94,384,7),(35,0,476,0,7),(34,1,460,16,6)]))) (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(36,0,347,0,8),(39,0,344,0,4),(40,0,471,0,8),(49,0,462,0,8)]) (IndexTree.leaf [(48,1,460,2,6),(50,1,460,0,5),(56,0,455,0,7),(64,0,447,0,13)])) (IndexTree.fork 4 (IndexTree.leaf [(0,64,189,258,10),(66,0,445,0,11),(2,64,189,256,9),(67,0,444,0,8)]) (IndexTree.leaf [(66,1,396,48,6),(70,0,441,0,8),(69,2,440,0,5),(74,0,437,0,7)]))))) (IndexTree.fork 31 (IndexTree.fork 15 (IndexTree.fork 7 (IndexTree.fork 3 (IndexTree.leaf [(74,4,305,128,5),(80,0,431,0,11),(83,0,428,0,7)]) (IndexTree.leaf [(96,0,415,0,9),(96,1,396,18,6),(98,1,396,16,5),(128,0,383,0,13)])) (IndexTree.fork 4 (IndexTree.leaf [(128,1,332,50,7),(3,128,344,36,6),(132,0,379,0,11),(4,128,347,32,9)]) (IndexTree.leaf [(133,0,378,0,7),(134,0,377,0,8),(132,2,312,65,6),(133,2,312,64,5)]))) (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(136,0,375,0,9),(128,8,99,276,7),(140,0,371,0,8),(132,8,99,272,6)]) (IndexTree.leaf [(138,4,369,0,5),(144,0,367,0,11),(152,4,353,2,5),(160,0,351,0,11)])) (IndexTree.fork 4 (IndexTree.leaf [(160,1,332,18,6),(162,1,332,16,5),(164,0,347,0,8),(36,128,347,0,8)]) (IndexTree.leaf [(172,0,339,0,5),(176,1,332,2,5),(180,0,331,0,5),(192,0,319,0,11)])))) (IndexTree.fork 16 (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(198,0,313,0,7),(256,0,255,0,12),(258,0,189,0,8),(260,0,251,0,8)]) (IndexTree.leaf [(264,0,247,0,9),(256,8,227,20,7),(8,256,151,96,7),(268,0,243,0,7)])) (IndexTree.fork 4 (IndexTree.leaf [(260,8,227,16,6),(273,0,238,0,7),(280,0,231,0,8),(276,8,227,0,5)]) (IndexTree.leaf [(288,0,223,0,9),(256,32,94,129,7),(32,256,151,72,7),(257,32,94,128,6)]))) (IndexTree.fork 8 (IndexTree.fork 4 (IndexTree.leaf [(296,0,215,0,7),(40,256,151,64,6),(304,0,207,0,6),(288,16,198,9,6)]) (IndexTree.leaf [(273,32,78,128,5),(56,256,135,64,5),(320,0,191,0,11),(256,64,189,2,9)])) (IndexTree.fork 4 (IndexTree.leaf [(322,0,189,0,8),(258,64,189,0,8),(324,0,187,0,7),(324,8,163,16,5)]) (IndexTree.leaf [(321,32,30,128,5),(388,8,99,16,5),(168,256,23,64,5),(224,256,23,8,5)]))))))
def deadautos : Array (List Nat) := Array.mk [[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
def deadlevels : Nat → Packing
  | 8 => deadl8
  | 9 => deadl9
  | 10 => deadl10
  | 11 => deadl11
  | 12 => deadl12
  | 13 => deadl13
  | 14 => deadl14
  | _ => emptyPacking
def deadindex : Nat → Nat → Option (Nat × Nat)
  | 8 => fun _ => none
  | 9 => lookupWord 1 3 0 9 1 4 (hashdeadl9)
  | 10 => lookupWord 17 61 5 13 5 4 (hashdeadl10)
  | 11 => lookupWord 124 434 7 16 8 4 (hashdeadl11)
  | 12 => lookupWord 137 475 8 16 8 4 (hashdeadl12)
  | 13 => lookupWord 26 148 3 13 5 4 (hashdeadl13)
  | 14 => lookupWord 7 47 1 10 2 4 (hashdeadl14)
  | _ => fun _ => none
def dead : Forest := ⟨511,14,fun j => deadsamples[j]?.getD (0,0),deadcolumns,deadautos,deadlevels,deadindex⟩
set_option maxHeartbeats 0 in
theorem geomdead : graphValid dead (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead8_0 : block dead 8 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead8 : block dead 8 0 2=true := sdead8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_0 : block dead 9 0 12=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead9_12 : block dead 9 12 13=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead9 : block dead 9 0 25=true := (@block_merge dead 9 0 12 13 sdead9_0 sdead9_12)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_0 : block dead 10 0 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_6 : block dead 10 6 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_42 : block dead 10 42 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_78 : block dead 10 78 35=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_113 : block dead 10 113 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead10_149 : block dead 10 149 7=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead10 : block dead 10 0 156=true := (@block_merge dead 10 0 149 7 (@block_merge dead 10 0 113 36 (@block_merge dead 10 0 78 35 (@block_merge dead 10 0 42 36 (@block_merge dead 10 0 6 36 sdead10_0 sdead10_6) sdead10_42) sdead10_78) sdead10_113) sdead10_149)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_0 : block dead 11 0 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_4 : block dead 11 4 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_40 : block dead 11 40 15=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_55 : block dead 11 55 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_91 : block dead 11 91 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_127 : block dead 11 127 29=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead11_156 : block dead 11 156 27=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead11 : block dead 11 0 183=true := (@block_merge dead 11 0 156 27 (@block_merge dead 11 0 127 29 (@block_merge dead 11 0 91 36 (@block_merge dead 11 0 55 36 (@block_merge dead 11 0 40 15 (@block_merge dead 11 0 4 36 sdead11_0 sdead11_4) sdead11_40) sdead11_55) sdead11_91) sdead11_127) sdead11_156)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_0 : block dead 12 0 3=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_3 : block dead 12 3 14=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead12_17 : block dead 12 17 15=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead12 : block dead 12 0 32=true := (@block_merge dead 12 0 17 15 (@block_merge dead 12 0 3 14 sdead12_0 sdead12_3) sdead12_17)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_0 : block dead 13 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead13_1 : block dead 13 1 3=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead13 : block dead 13 0 4=true := (@block_merge dead 13 0 1 3 sdead13_0 sdead13_1)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sdead14_0 : block dead 14 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem alldead14 : block dead 14 0 1=true := sdead14_0
theorem tablesdead : checkedTables dead 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block dead 0 0 0 = true)
  · exact (rfl : block dead 1 0 0 = true)
  · exact (rfl : block dead 2 0 0 = true)
  · exact (rfl : block dead 3 0 0 = true)
  · exact (rfl : block dead 4 0 0 = true)
  · exact (rfl : block dead 5 0 0 = true)
  · exact (rfl : block dead 6 0 0 = true)
  · exact (rfl : block dead 7 0 0 = true)
  · exact alldead8
  · exact alldead9
  · exact alldead10
  · exact alldead11
  · exact alldead12
  · exact alldead13
  · exact alldead14
theorem dead_start {prior : Nat → Nat}
    (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid dead prior=true) (checks : checkedTables dead 14) :
    Impossible graph 14 inputs.toFinset := by
  have noRun := root_index (g:=dead) low geometry checks (k:=14) (by decide)
    (i:=0) (ws:=inputs) (by decide +kernel)
  have tgt : targetOf dead=graph := by decide +kernel
  exact tgt ▸ noRun

def hashf2758l10 (_i : Nat) : Nat := 0x302ab045c86f00006031a0564055f8cce84a000000006833a065c844480c104660350000004b883d7029a8080000303ce8118000503a8000483100001007506ba853f8017861886a8838883c000000000000000020188000000000180000702ca85e582e000000002852b805d0120840184700001806182c1830a837a0cd28ca484d20667835885cf81580106b619027682b806c401ef843e84f8034e01d2044e80b5851084c280ba062b809402f483ec8639813980fd070480290413866905448145839f056902460248059685de817a86ff819680cd034786b284a88695847f051b84e000070252826000018128000000000006841f8be084988383050203a5807d06db02780004014b828000000000000d80d8000201e7859d85f4811480e00007037780e802278296863180a80005848205f80002036e060f82a381638a100002003301f88434820d83fa05b1040c062783f4003986a680a00003849606d3019e8f00000384b580d483bf826a030304cc86ce820784280000861101b3848e032000020600000602fb036105c1058c8577815105bf017382d602ed8b41823301d98a9d832e857c867505d183b6870e06e0050e025c800281ae810a858702b385af86890454869902df864e01c806780002053582148520000000000005804205a60681833206eb004800000000000001f00004806901c6802381b9a4ba039485e8065000048642808d02288055046f03e4054c821c8424016c81a204da03d8000384f280f70132828b001e8551809d84e800028238003806020000003008041413008140600020744e03038041e00008240a0a030580401000001600080040000000180004000040201010001e1f000000404008100a06040200801018b40208000041a01038a41e010108802040b8280004030000204
def hashf2758l11 (i : Nat) : Nat := (if i<7 then (if i<3 then (if i<1 then 0x8000800003600400000b002800200c0034072005000002c064001002000c0440410010004002018007800000800100000e800e004001001c024006003000405c00300080b800000a00100800140000018008000008000805006c02a00080b0000000002006801c0030000004024004003805800003a0098030006000000005801400000e8034004014009000c004003000800c09c0040018018008002012004000001b002800005a018000004400000d0158004008012006007401c002000000400200b004005c000001004800000000800180cc0020000000010000007006801800000e000800804a006004801005e007000003800401c000000c000004001001401e003004808c00a0050018044002001002000000c002019002801a030004000000c0020030000000006004807400001c0000020014004009800000a01d000005800004f00100140000060000014006000016000000c006006802000a00200180080040120018018002002003004004a0000000020018014007800804a006009800c00202602e802000400100a0000000015004800000000f0010000040003001801800e00f000000003e019000002400c00400180000040020020000010000028000001c0000078010002016009801800600d00600ac01e00f0008018000023008805c04e0000018024016003002806c0b000c000800000601200f803402c0060000108030003001803c00001b0000000000008000000400600402900040100060000008002018000802801a000000000400000000180000040000048004000001004800000201a000003802600500980480000060008008038000000000800000d0030018000006003801002c008010801004200c0048000008000000000000000800380000060060000048068002001802800000400c801401000600d0000000019005000403001500e801002a029005003c0220070018030006006000003c00200400780000640030000014002003005002008600000b006c00401200480300080000008004000008003001000201b001000003400f001000000a0230000000018009000002003c005000003000e008001801c0040080010008006002003000001c0030008028012001000001002601e009803400000000e80080000010030000018006000802c00000f002800000000300000100420060030014002000001000400a00300000000020000058000008014005003001e00c001001401e00200580a400600b000007400600a002800c00a00500c000400000100c800c002011000001400c005001801000a008033802800000000000000020030010018002000006801c01c00d008001800c0040000028022002000000003004501800200020030030004002004003003401000200c8018030003013004000801c else (if i<2 then 0x101300000000020010064006018001800c0080290060008030006001800400c00e00f0008000011000000000201700f80280060010010000006005000002802400b0000000000002004800000000700b000400a0060038014072003020000c0020010008000004002003800400a00000280a8006021006802800400100b802c04e0000028008004002001808000000200080000000030040008014001000001400200600e0014000000018004800400100280c4006000000800800000c009000400400a000000402c00a015000800e004000800c00c0000008030000004002800c000003008001400600000000000060010000014014009009000000202200200280100030018000026002000003c00e00000000b401c0010000024004010001800c0060160148010000000002001c004006001801000400e00b803c008024005800802600000d800800200f010002c002001009000402e014003000c00000100000000000160008014002000005800c00000000000240020050008048004007005801003c01b004000c0140060018004006001000000c000001001004c010005003003401000000c000001c00e0030064018000006800c0000070010000024001003000c000016000000400a005014800400a003000800400c006000002c000009012802c0100060000000000011000006800001f00180000040010050084000000006800002a0000000074002017001000800002200200180280010040010004004000009400400c00080480000000000000000007003801400c00c011006400000100a001c00400d003001000000100500800020070168018002000001000000600400d0020000000022000c022002007001000e00000a80d8018000000000000400b00380880120110108020000002001000002000300300b400c0010068008000007003000800a000011003003e001000000400200b003008c0500010040004002002006002c02601e002000402001f001804c002001000800402200a00480000000010018020002000014800001c00301d0018000016010004c00c001000003400400b0008000000000001805400600300000040020000030000000001004000800400200100000040140010008000005005001800600500a0054002005007000400200000d0004000005003800402800b0030000010009000002400800200280b8024040001803c00600600480400040090038010002006000000400a005000800801c000005800000000500900000180010000008000000003801803e01100980040000140000000002008002801002a00702e805c0080000050018000003008000001e00a00300040060000008044006009003800400000000000400000000160008000000002001400000b0018024014006004000000202b003800 else 0xf07e1127817d1638f6e33d70174600001419680000082b3442bef811ada125d408e0e082e09576a025b606f7c0258a04b640fc880074001c64117ca14ace080a60406e0ba08043e000008039c00001010b140e22c2b5600000000000000020db54004e032cae0073a0026400d1617996095b20bf320831c0ec5a158563357830f7a2fff40cbaa16e000000c192000fdc0000001052e049a00000000000000000001c106a000002121f418862149cc0114e125900485812e4695740000000cde21118e076ba0836c11bda11f8000000000062089209bba18550097000001802b1217a722e0d60f794065e60a92213d68088e40bc6a138901670e0edde0b39c16b500d53e030ae161ae0885a195da2ced6002ea16728156c00349018a5e325440b95a116ce16318133d2098f208bbc0c21811bee07afe12f260cce81978005c003064a0ae180445a0cd480a9dc0ac3212d6602bdc0c79814f6a107cc0433611644088800babe00a940be2605d020f9d80fd90008a4153720e7200000000006099c2514d71155c06fc00000019492385ec03062090d8133200000613ee00000e0110e05cb5110e61174000000147d614d2c0701e1216c0ce8e09a96027360c0102e45a143b41720c181f0105000000c0081e004400000000016054ac0f0a42055a1971d18f620d0002a9ea17bce03e8a3340e07f800001e15e020a98805be0000000767813a000000c168e413d0a329d41428a01b960adf40e36a142301261c0952a0af360eda00000815512163de096d60ddd831f8000000000180dee0000061024618ee00001c3136203a301832e133665149809800000141605e9583c234f80cd140c180000041020e11fdc17f340458608048225120312814932369e0089de513c009c3e0ad2e11eae18e4e18432039a212aa20d18c0369a16640cae800001e95c02198f2191be39b122b5a0000000001e0e0960e02608ae0000000000a0ad0000018053680df3404af200170041ba3260c0ec3c0c2da05dc0075602e246013e2143000001c0da9c0dfe00000000006079dc252000000000010304d812e200001c00bfa08342300540a31a21a780a6d22ac5e301de08b5e05a9c0c500000160ffe00f1c000008063ec2ba200eca20d4a8334d811d4000c360516014c62146fe1451807810189d201d7c37fdc05fca197aa0c6e0193cc18e20147b819906168760920e042be17b062ed4403d502fe70277480362a0ee1017c1823e540924016e8a0d0c00a18033120000102e3fa16f5a04cb038d400000e02b6604f9c1306e018200001c15dea2a0d201b5e314de15e54150e4137ec0558214890008ce158aa13176278be0e1e203b2c11b6a515da1958614d9c06de42572031dfc149500dae614326179400000b808c00c00000200180140000070018008002001800000800)) else (if i<5 then (if i<4 then 0x99001cc004eb6058d00f81c1087e0091018eae181a20b480003f40f6523620a1154c12c740107e18924278963756212b2811e66182260fec8339ee092a81082a0e54200e70166a40c9840557c0b0362b36e0cbec185fe2133a129a203f34119a402d742b7ba01376062e007744002400000e145320da04126e0046f801e1415da408e620630805274082400001a12d56174c20344000002117ee1578801bc0060fc17bf403c40000ae1103c0144a12ac00001608114174e0000000000204a80000160aa4807878104800462292102072141272000000197442b4ba02f021729e080901232010d7c1800c09f7a228602bd400001002c8000010140160a8dc2aa862bf3a02ce027f2000018396a21410a0cf6000004335e20337c103a8072ee055580326815276101e00000613f00000000001c0e9020a76000010105a4121a0123de02abe510d20dcb2031c4199f40c5900df04224f495ae013f8e09542020480e27c0653207fac15f760c9d80ae240d3d00819e049da03d9e2b820120640661008b8c1412c0ffac36bac03de61074e0f480143e6163e415570b6b7c00e840094a00d521707c0e0ca2b6ee2609e0d59c51470169b8197600001a0cb2218f9421b2e0d0760ce600001c01580000060398c044c02b080047381828c0a90207d74177960afba0c47801eac09aae306d403dd414b641620c90aec199c8310b0149aa151e251570178b806c880fc5c15f800d10402e9a15eee2aa0a02364e78441367213b561346410fd8162440e6620e8723336000016161000000606b1e0e6980d8600000e167d80c32002b5202ee0000120576c127c6181820aff40b66029eca0170c01db019070160602ed2e0afde22880318fe0257208566008e0046981835a14ec406f800000c052820634a1847417e44eae120bcb20d9f60e782029000dacc09a340d6fa160e00000e0a3b012bd4118c804fe000af4025100a1160597a15c0a18694130cecaea60b7782dd4a1069a0ffdc309ee140e00000a3901af00b80b26808a000000e18afa114c007ec4021480c76606a7212dda09cce05a4a15984184d400e2e128ee0f4ce145901235c182e8197c6e73221128809380000000000eb70dc14a3814eec042d8134140cb0a2e04a162f401968072c0000000000000000000000000c0bf80173180738c153aa2aed8078a60623a0154a13e5c100800cf00000000001e0ba60023320642619a0211080000101863e173c410f3a2c7122ab1809ea013dd617efa143c0000000000a3578c08a4406f5010d5c0c70807fda06fa60b34e179f62afd20cdb803a8e02be816e4418d000000a0d0ec0f514144ae0e4c00000c0d70e07282178e80319815ce215b9c00d78016b06363e0230c024cc03e68112c206372164340f200157ea37f8e0fe3418a1a17e8e0987e0b12e116a2 else 0xf712077ee16f6e17f7c0c0de02c3c00f360d4282c99c0628207b7015236075da117141581004f3a0600804ee60dfd610ae4006000000c028ea0f6e0000000001831120000020ec02b313e9572c071a018d6816480000000bacc1105e061ac0adbe0fd7613da82ace608d4000008134a0d01360093e0b8be12660d00340e5ae0e640000000000407daa0d97e09c6c12ca61566a097d00b25405da8323cc07c800000e18b70191ce015780e2800001a0a6962fc800001e339a0225f41695201bae04570087b2085580fc0c0cc6610b98050ca2c2e610320000162e4cc08cbc0e84000000000000001e113aa0e8200001003600000000000e047d01901818c800001604ad4051a0000080ed0a13940000060becc1370000000001e00000e2dfe60e3c01559e179b800fba0461a0a2e009734d00c00000006d4e1564000004152c40cee0007e6030d401c200001211fbe0e31401bf6088a20f0e015cc633ace01fb414c1c14e56197e000000136580fdb004e500b3d00c6280f94c0e180cae46067f40b16602fe608f0a127540daac0e8b409882018ca0a85004ec40225e0ed20005cc0a20e0371a04540040f69585c077760928692eb204a760ab220702e03ece2ac2606108138b60d1ea044e20fdfe0590615ba00000000014020ac15fe00000e07df405d84300ea1157e1784c048d40fc2e05e4809b7e016f00997a1845e1455a111600000e0f01c0f842043000000a23a7434008929ba0f1001966a35e820eccc11b5603786128a20c1a80eff20b6f602fb210cf81645e01020000000000c2d3ee043ac17d72094e000008134800f164103de0a9603803c0abe000000000000001e18a7416dac093fc1237417d48b7d12eae200000a0d440000180b51632dde001a00000a2e34016fdc0a5ea1320a1363a052580eed8192ba033e80c49e0c29e154dc03bec10abc1616a0cf5217e000001a055a63650c05926167f20174a086aa113980b89c16ce4094460d65e0e9ce026080304c1660a0fd020ef0a06bb40798e0b9220f32e58f240ca5c103fc03a4815420000020df4c212fa0c56c079060e17c0826a15c9803e141772419a242b46605e120282a1011a09d2e01b060849c3343005f8617dcc020180992c162641290612a9c1985207fea13fa6ccebe13b100942e09dc60e20000004083a00001e2e500000020b7de1167001018183c00001003c6815ac0000161183614d7a0da6818bfa227c0000000001c03f183635816c720842002f8013080000000000817912022b01195c13606068522b0c6039fe14c88133520f8f00b1101510a0a7bc1262e13df207c5c169ce067200bdc0000060a8660a06e225a2028c000018165e00000001620000121725e186e00001a19622031e013a343236e2bdea04d2000000000061315c02ba60255236e98161320b) else (if i<6 then 0x96641121826b9411b3804cf202ac8258780ce3c0ac56177c4319fa1629e0f3f21257805df206c3c1456a01fd00f14e10a26092cc16be295c3c0ad900ef5a18c0016c2e2b3f202a8e0985e08fb009bce0a46007b0a1712012b02046c2015d20f13217fd00e5600000a08b0000016089000000000000000180d5a000000000000000000006094be254640bb3c06d8a0f77609a400000212c900e8e60dcd80897a13b2e07b3e089a2054e2009ca07ad20794808160000000000000002513ec196140cb980c1260dec206e5014de40586204b1c2a97c048e004d16029502128c12c51115dc0710801d5801a72165a02d8e60b520000100d1482cef802e460cc180a0400001810efa113fc08be00000e0ff8a180a8121060678000f60000000001c096880b7fe0a51c1249a151860c9360c1000001402d9a05b621221810dba0bbc20e3ee0a402051940efde0acb014bba11d061037802f20000061956000000106560e4a00277615020000000001e0511a21a9809d70036fe0c6ae09c9403f7e132660782000000000000000718f4401044123ee091600001a184862bf8819b4a092ee07152199622c66005b3c0023813f4005c400000727c98190de069922ea600001c02a24005a60c756517e0000000001e119900f83e06a4a0612621bf412daa0aea606e1e10d300323e018be18ba82c9dc178760b18000010119000000e1827417cea36790101722efa80d1781067c151d81295403ae0069de2f43e004761124000012164f617504118000000e0aaca018400b9b201d3608abc01af81072000012038d40a0a00001e166da05d56026c0000101803c0bd1e194ca0900a019ba0d76010c6000016d02760cc2a112ba19b80000000000200a020173223462025f20fe00000000a0d009b1809e4a08d2418f00000000000408c6e0b9e8379f8037602aa200001c102780ead80302a119c407a200000a0873c13ad417778123b000fde18da00001c06e3a068b4138c000000000121376007e4807600000080bcec11e16114840545607d9a0176c195e615a380ea514f6400001c1301403bba0b2a406cbe157261655a11e261897208cc00000c0f0320043411ca4173f6127ac195200000a0a3640dc000001a18d4a13c28186ac0b6820f90214460cae2a17fae152403795401c14021f40575c0874a14a6c06ec00a7e8162a0000000000c05d322e07821c021496000000000120cf8753128040d0101aa136b8032c6126b001e2000010188200001409cf2000e210bd40aa2418b98106260ef86016c403b960771016cc215f3811e9543fee05fa000016013c000012144000000e052c00000b20a9a193842f3a011766078e00001e16f240014e13d9204890156f036ff210cb813e34168d2159ce2ab3ab0dee029c000014175c40de6000012171ea0ae7a335b819b2 else 0x801fe2182c0000000001007850041f410c50059a603fe0000000000e0d7c0000060aa1c0d4800000c0de0a07bd2030fe167ae137a00d30ac9fc611a79113400001a0fada191fe15c2000010139de04c0e029f00f2ea18caa0b09e0b7ba0402006b2a08a3a094800000016adc10920000000000e0f47811f2a1999c00664053420a58e0fa1208872194740062000014e5d000001e0d798082b00a020147e81726000002058800001017f162061431400000000001406e800000911560000160fcac14e80000000000213820000000000c08efe065dc10e5e115ae1540000000000000000237be80cd900b8da079a0000000001816aac2fb8000000000000001213ca411ee4130200001612f6a1898000000000000001c05e8a155f2000c202cc00000a0c4e0000000001c15740000060f97a17da000006381600000000000000060505e136ee18a96150a00000e038280178e0a4fa01094160ca01d1c1684e08664397a6010c004cce0e958186d40549a07bf02e42010ec00eb00000000343c2c3d00e6a20ca20091ee17f4a0a2c000018176cc07bac0feee0c8701717014cf40c3a00001604c8a0dcf8230c00000e06800000000000c0f9b23658a5141405b8000000000000001e1734000004018720db8e1328c030000480e037a00000ae41961402a14980000000000601b280dbe2085ee0b3e00001a05024138e000014121820e756255600000e0199209e0414448020660aa900c25a187740a8080f2a218500000000001e192500c6dc167540d9c00494210b50182a6065400001410c000000000000000000000000000000000000c0de4000000000100f8ae188a000006179ca0fb40000025142004b8c0fae00001a03cb20779e0803619b0817a2a0356818a2c02ea4010a00483c0d500000000001e03d7c0dc3202fd62e1c00001a0d83a155ae2c3fa0b78000000082111109c3730a046bc0ef7c0caa80a320143400001e0bc48122be0f38c198ac150cc1090e02a680751a3857e10a8601a02035ec05ce417a16204200001213a620dda00000a06d2c192800001206320129600ad6202287112e016dea02818116e4190a4014963292e0ba80000100b8580b1ae021b021a560735a1379ce602c159fe145ea24f760c9140a3581188e0a42e0d2b00195a257f4045f413ed40476c03bc00123a39c1601800000000001a176860f9fe046600000a1553015a760ca6c2507e195400001206ce00001a1836806ee61703b11414133160e06011600000020ca8e24b9e136c207a18157c0146340509c0f1820389e11a5a12b7a15a800001c2a5b80b2e00001639a6a0e2bc25a58086e0075b000bbcc44200000e04da000010118aa363a000000000102e480009f0012a6e65d400080000000000000000000160d9aa13f78129983581215d34067c00b4000))) else (if i<10 then (if i<8 then 0xa1993a08ade025c00001c0a5240bd64707d812b8a069fa0374c1212205f280f0561601200db80c4a013c8036a800001a2efcc99100000140d8e000000000080c6460c5a42d7a212d9a11aec19bea0e772081f6188400000a13d5a003200001016fe00ab0e0f35405c7c1293e387a40bdfe026a60793418b2000000000141280a078da0353e01e760d9361618a11b8609c500d26200de22ae9a1131002a0a03adc2e12a053b8133a40b4da259bc0d3a208dfa12f4c15b2a0570012a3011f5030c3e081a812e1815bce12836140640fa3a0f1a209408505da03678124e60db020b72c0d21a0880a02c760a6600000a0b3b215060003000000030540000000001e1765c12cd60364e91b5203a600001e08e40000000000a08c44151ae05a2a0c0f20cd7211c6000000000000001e1242e0a13c3567c1381207680000060730016380110d60f634124da04e141733c080fc178d00b6c8029b0029823130015ae01265e06a022fc18028600617414caa18e660c156073c401cbb6455c01f8214cc02413403860057ba05ebe1816c0f08e0ea700068c05ba616770188da2f6460262c0864e19adc18e04063da0752c137ce1767e007ca18d2c1568e03216190200000a0429e00966006ca2df38105521098c17aa20c898303d606c7c18f2a0425e15c60164020755013966115d0021dc171da0e2e60f750091ac16b86022d008126172e8076de04ba60659a0bc84005621594a11a0009e38187ba1807005ad8054260b3047078e066940eb2c070e60d680000060ec8a1162c15d900b0a4100721479a000600e80611dc40c2700f73c0cac60930a0ccc2066a00000a0b07a1228407e1a2f1a01608814bfa14dce13eba1926e0c538024600001205ff0171403307405120000000001200a20000000000c14eba2a80000000172da128da074ce104060338c02b8603c9e115fc10f50055c015d400001484bc0000002c6e00000a13a40000116390c2fc361310a14194057fc11b0c0440016f120b006156aa0d7e0092660b91e0bb00000081918000016260e85068402880000000000415766105940ee762658205f7b7582605bc20573a088c20dd4015820304a200d841813612fd0175840d47a0499e0f364193ba0876a0437c1989209c1609f5a15bea024842bfde0e622135e00001a1983021aca18c2a0d4cc0baf014b1400c90096560f4fc10c200001016a3a023a00001718f000000051300000000278c018f80ed820ba2c2f2861096a0f4a0000000001a0f5e00000a017a000017115840aef62d6c404180000060f61400136047be148c0000061209c17c8000002086d81015a097a619b7c1820000006035da1070e10358148400001a22900000160e15818faa0c94209afa1374e0f7da0990c1668816a68023400001810de60071804dc9113c0000 else (if i<9 then 0x10124600000e0328c07cea033000000806b7413f2e0a4461029c065080150a0a5460138000014027a000004146720df9e0b63a935c8152a2185d0102a20cdce01a9c0adc6168ac0fa8e060c603e2212ff2160340eae0105f6180da110f62a98612a7400cca0937a23e8837a02108ba03ebe15098038ae10d82122d20c1fd721220641e176f60cf2c031162ac0807efe514b20671c041102aeb6181d209e8a0748207dd61288c04bc805664302fa1516c0d60415fca035a616784230fe0275c15126169e2040a61415216c8002b341146a0dfba053de11d7003a0e0b5d811cc00ee351146c18884071d4228a405cc8076f01591610030011d404bf80fd3e18618956be93d94183aa12efe087ec0c8382790a1857e061ca08d625150417c562f5000000402d4a127e21112811e4a092261651c14f9e14a000001c019c000000001920b57a0839812140000140918000000000000000000010185340b750160b437ba683902073380df600000613452131a00001e30b000000000010133f0162ca07c000000000000000060cd2c0905a0fba0000060f2c00000605b400000a107b00064c06056152e00001a141c00000406638158c00001004e2000016154b808f4200f8015e9610a440aaa000010070c2188f000dc6059c00000205f58163a0000000000431f3012a56187cd64ce0000080be44260741312c0496418752361ee00eea1200200000000160a754127685144a085a00f8600000a090ac1426a16d460c39c035040bd520d7b2154600001c1505e32f6802d360fd400001c09ec00001211a200001e0947400e400001c5154000000000000000e064b816e3c17974c5eba0f29a174549564a158983085c0e89812cf20c8be08f3c0143e07a4e18f6a04f7e0413609b2637bc6179320dd2630456112e609fe0104e60dbca07b4a082d02fa1c189ec0eba414b880bd9a1088e0b5ec17620000000001a301200000000000000040bfbe19300000000000e2fd200561e14fe0000000000217c2000002140d002ec0074aa034d80b1ea2b3de0580a059400eb5616dc40a29000b4005b040be64071f007f701936e0b0f40cea217a9e2b5c2122342e3b4319482a9500578410f000001209f00000000001205a000000a09984194fe061402a9060e2c00fb800000604918024a6091563676614612114fa9570c012042131c0e4981689619a8a120c219126028a611ba00001a314480599e91fec13912173b60e5ee08ce0000060b6080e41c0dd0c01f721483a10f78244ce22ff432e200001017cac2ee12034f4033d618fd210bf016536098ae14f420a7c6227e00001c114ba148660fb380f69e050ec31eca1622419afa011b80fc66100e495b0c15a5806c000001c070b80ce5816c4000008134e00001007d2000000000000000a124a00000000000 else 0x1c02e72159a00001c0908c16d6e07b8e031b2084d617e2a0c9e000014090e00001c0f44000000000180a940000123262c0d94406b8000000000000001a12a1e139a00010a148b40e3be0bf60000180ad460c8fa0b2800001012388014bc0fe4c09740219c0000000000601e52102f40fa5e10e9c12e8a1810a10ff40aa7c034b20354808f6606f000000000006071200000000000000180e1200000e0d892037c00001612d0418800000120ae8c178961060808b3e19416142f20fb70166e81830a19c220c66210bb407c360e6c00001a06dbc17eaa1972e0f0d604f12004000000c008540ec600fabc0b3640da2e0a6f4120ae0a4a000010100cccf8000001c098de00cb009a16043400000a1030e39722131c00e0162770000006e7cfe15ea2047e00001416902131e2790420d2400001411ce0000162fa20000121965200d20000040f2540c0701736e05858011f00af7a1173a169221490000008144dc06d62182560421603c16125ea024f60beea0b580000080d74411d3230360000121477416bba2570015a0a0d1c00000e00f580861e1545616c101230607f200c42e17b9813ab4189420439e196a20abd618b1417740000021001c06bde05d6c0d134082280ae46102d0004b21632404510045d811c1014e0e15d74166600000e0d3ee0ac8616d140f312063aa00aac061f2057d4090220020214ab00b9cc21aa80f27c1094c026e8cae0a199b615006012620cb482c2141646718f3413c761078419112171a6119ea05e7e03cd81386213528069ae02f7410d0e0208a068ee105c411582183e0b73060332000010033b20c17c2dc980a25e37a80af65e251100618a0c3461373c041400000a0741e51080000000000c2bd800af40000161004000006068c0043ce2f4a427fc00000c010f4085c00000c16838004800bbbc153e00000414e6a08ece0c54c014f8108d209df800a401244a0e9e404b4c08e303833818e800c1cc18ff8134cc0396a0cc800000609fde05a600000801f000000a08d9e11f0a142aa34220000000001c06264023f80038c0c2300358c0f410142121697c06ab2038f60fa6406214ad3fa086360719c0b46409da418bda083d407caa13fd409126037240a72a0e5de00bda0789c03f54132c0d44300f22a10394164c40a8a015b7e2f9d610764005220a3d018f5e0141a192e8135c20bda20d23c15f000001e1203e00b20153820e1100f5c000002187f6193f201282117a00687615dde0e7ce090681530c0807630be4007aa148e4006a8161e00c5c0003b4093d231b301240a0871a11ff6000200000c0f93813a9e016400000000006089f013c020abb02ebd483ae6020ce02c180765c0bcde0f3ac0956e0c7a00001a1864c0d320000100aec00001e001dc051de2f2a2055000452818de42f0b2165c00000000)) else (if i<12 then (if i<11 then 0x923631f7c066c8242b20e05e1808c1701208fea0c456056220976a0b8640d1bc0b0ce1278c08dc0074ec135a4077ca116980a1521659013180198040bb6600e1a0fcd0121d2109ba0112a130ba95625249e4367e20de80176b007d5215fbc0f7ec05f0c01a400000018d800001e087cc07588127000001800c1c16bc218c6000008095de17d3c0a5c60727a0b6ba10ea80f6be05c3e06b460fbda12b52003540c7c0000140b9600000a09b80000000000a119200001821386170e4017fa14b40000160e600000020f1e8083ee172a00001606dcc02e0000004064e0056c0045a20a82a041742022207440000000000c05ae6170580bea0000042c1f40ed70033400000c00c4c161c6d1c600000811500000100814214e2613c40000140f56406896385180f8c8032e20a00ad9a4c175fc00b8af003a10dd40796818b4613558180f614a48089562c4221699e0d5f6027e02779c1780a0c80c0a8f818aa40d676141e02c80806e700994e1528a51346643760dba417d9c195a00001801f441439e0fb0a10c920bf1003944191660e8c806c4213cd806fea0ea0000008154800001c13b682f54417532054c801e9c020ea05ec0000180d03e1437818906072a23269c1392e0c3ec11340000120e9660a71213ce000000000000001e03082044640316000006142c00000000005111040147638da40e3460d2c0000000000000000000162c16a0079a0202616b1e0050211018059f80706a03b040507c1287a15e64012f42fafa12fae2c5e026aa0000000d81e0dd8a0478e0892a31f000000e174820ca1204754185aa17ffcc62260c0800001814f280c0200000a130400000000010164ae0ed440bc22073ea163480a39e12d3e37a4404d9cd14a41417a111b611de606ac00001e0e7080d8c4021100427404fbe04d4807f4a098200ab520e0f61251a17a54029242bd3203c200000a077320a3ea13d200000e0f528382dc0a5a20be8600eb0151400001827baa11224184e608c2012c040b42c0606c03b794d3e802cb8081c60858c2dd00000080b04a0e9a8159701943004f50170a404aa603fde0118e0083004a4000012047061110000016174000ea2c17550055e0000000000011c36056f6015ee08fc00f59c2e1aa1723c125400001a14d1e0d5cc2acca0221203d242afa05153806a84067620d09216d3007d1e039140c3000001418dc001dc41554004b20000060fea0000060801202ae20b6581879c02262058a40f42c0c9b417ada109fc155c00000c2b3b2f0076361800000ed005a165600001816b7c021760409012dea958de193281323007e20060981871e015aa35fae09f2c92fba157a202840000000000a0252832f980314a0833c111fc0c40e0e51c194a40af8c38faa09a6e0c3c838f460393237e9811c4e0690000000000120b14c064c else 0x5e084b0140560d6b20e934170dc0c5e40d8b802d0417e6201240d006e175b01756e16afa19aa21593e097820ebe006460177a21106a122762ab4a0746201c8c07c68091000000000002708600001c0a27c19a6409b42140800c2e2060be2a7f436bde107e411858122400000607a8e023c0000060dd7e0b3280ab96304881951e1142e2c79f1149a012c6956d600a7a0b554053e21338000002026800001a0692e106e60a6200000000000000000000c36b60000000000a076380b2022ab8612840000000000600c7e364a00000a063800000808a60000182a4c000000000029212ec4182958920e7e02ad1a0f67e104da09ef80521c0ff4e152000000651b9802700156000000214a9214c200001417ec00001812ea40eee0000000000403b40000140b2c00000a194400001a003c0000160d57e33a760ff220b4f808688044940fcf010a600001036c54064581080819bb62559a0e6e4146c20da4202f400001004de0000100267a394c00000000000000000a4c00f6c000012177fe0717638122649dc0e4f015b4e16ee801eca0845e04e6e065a0000182fe9a00cf60a09812ec20708e0d36005640000020eb7c036c403f800005c0b4ae16fa000012b85000000009d4000000000001987e09ca8361be0222c2cc60000083424a3806c0c97e04a24142580ef260b82c16b2c04c7007e740dc8a154e8140ae0a1e80962e12ae40eeb83419e06a3205c820d4f61084a07cc60c0be0b4520cfc413e000189e10fba132e017af202c4e0130a0882c58f52013a416e6a0b1dc04a10080c0cfffa0eb9418c5601a340d4000001a0b23c08ea00001e0054a13be00de2000002046460a1d615ece135660fbe80f88e13980027c00001c1662418400000120aafc096180be0a1448a1013c03ce013e66196e000010097e02503e157180f3ca0d38432c2602a40000000001a510e2062ac0dc600001c513200001404c3e1133204d6e053020e99e1153a16caa0296a0a2a00001e01c540bf4403e461742e0a9e000000000000000c093a4186660e43c0d340000180a486135860d2e4094de0cae2066e010230111c212bf41783408536104400540818ac818724104b0101dc2ac800000a126c0000000001414ae00000c067b606ae664a16149e41252000000085140ff0c16eae1771814d4821656184a00000e072420e2580c8d6051fe069720bd3425c40014d80134800b0614b380c7e00000614da017de0000120ecf81636e05e26022f4044bc0db760a0f0003760fe9012f00073a20a57c0cfa601ab40e38e0b5a2093541995c10cda023821804cc658809fa0cb1fa04fdc105602ed8e01dea0ee800001c00594d5b1e03aa41197e0d99a31ee20704e02180000000000c0a6400000a2e54127036146a2075e405476037f81114808a9c077ba0840800864013261) else (if i<13 then 0x1464806d080385c7085609592129d2ca0bc0c37e191560f5aa0244a0c7340161c004d0011601718401ada14fdc1145e71ac2515f201ee210b2a19a5d11300019e202db61615c120e6073600bfd011a8a096a2055200001e0a6b81814400ff036a4815ca0000141204c122fc09d9813bbc2e1ee0f986333bc08e90332cc16a882b9ec14752139f00d0b0110aa11aac185900493c0bbfa0243c1047407e9a2ef5415d1a0240e002da2fbac141b413e8c1563e095ee0db20066460212a0efa00001839a0c03d000000000010193400001411ec000000000180e44a07ea00000c0324e189a6056800000430c842e3200000238d220743603470016880099a3796417f860cb7c0bc0c0ac1a22614048ae049f40ceca16f820c6020167406820130eac5d9e158e250d8000000000062c7d4005e00001c14fa29948000000000000000000000000000001010ade0d6dc041c0000020cca01268000014062c00000608bce18cee09f8e16818135000423001b72079f617b5c144ec058ec0515e10e38321e60486e03db22fa57585100089691ae00ea9a0cc4a0ff6401d9c113c015b180d850052be0c84831cba0401e1042007a78132a0125a203ee612f9e05ab4c5c3a118741738402de80bff4363fa2eb600e5800625a17ccc380122ea940edf22fdead00a40a22c084760d62c10a1e332f60500c009be0dea6153dc2c48c0d7221587c07aba15f400fe600722e09d0a08d0000014099f60e46200b780eaa40153a13b9c17b7412c32106dc16d840a16437d0a0af1a09ad80acc408dbe0b8f006bf216a400404a312a4026442aa600000000000000160acf6147080a9b80d054198d019c0a0657413bd8042f612bb20e1ac0933c00f10330e22b51015aa414f02050a40c04c0e7be0a7800001614bc0000000001a0695c03800000120602208f8614814091dc18eca0d91e0674c19bc215e3216edc017c41343c0c4cc30d2a16a0817b2c0b8000000e0d544138500dc400000ec603615322145a00000e315c214c401711e1534000000000040d29a388200001401f30096e233bcc06ea001cf610f9a0e32211d9c0583e10b7a087980f55a109cc27b1c08b60000161324000000108e000012089940ce00000000001006cd2176100ee46339381018e064940dde00001e006e8170862a5763828c183980ac7e04e8000010002a00001000ad6190e00001e846ca084e4082800001009e6020d0000000000000000405eea0950c0a60a0b7160666c06f2611da8056aa0ebc011786129ec02e200000c10e0c113600a88200eda0c69e11c8c145c00000a196d017c7402dd801902099bc052e0000020cffe0c2a609be00000a95c40146940e52a10e720443c0ab6a13692100bc0e1ca0e0b419040000180ba4031d66114060bb9a0340412e6608c90147201442c192c80bb else 0xe036bc25b04052240cbd0174a40076004c4e05390002901908c0f7be3288213ffa07f0817ba6053380a1a615c5c18cca032bc2b62408c0a118fc0192803fa613ae611f6a))))
def hashf2758l12 (i : Nat) : Nat := (if i<5 then (if i<2 then (if i<1 then 0x1b00100000400500200200800200400002f00900b00302100000200000200001300300100000400000400000000900000900300301600a00100101100100004200000002404200200101500301100e00800100303f01d00d00702400500000100600000100000000900100100200900000200b00200200900100500a00300200000a00400000900000900100200200100900b00000b00100401b01f00103900500403700b00100900700100d00100201a00500000800b00000000300c01400201e00c00400800a01000300300c01a00000400700500500200900a00000300800100c03700000a00700201202a00600000100004800001a01d00000400801600200300200009200000e00200000800600101f00000000100000300000100002400000400300600000100202300400006000700500800001200600401100000600301c00904200c03000900000006100202900400100401d00000000200e00a00a00400000000400600000200400400700000000300000000000e00200000200701902a00001900100500600602704200000e00400200202900000200000000101f00201700101a00600200500100200000700000f01300102a00200100000000000001200101001a01300300300b00100200000100100100100d00200000f00400100100300000000000b00100001500000000400300400100703400b00501102100000d04201a00003400000400100b02000001a00100300200000500600200000001100200600300101f00300900000800200200500900200200000900400800201300100400602800200a00200100100701a00600e00000001c00600300200000000000800100000300600500100000302901401000c00f00500200800200b00000300400400103c02200000600100100100400000200700e00900002300100000000800100b00003302202300000a03200000402500300600500600900400c01001700f00500200000600200700000300400000400101800100001101500400000001a00000702000100b00200500b00100300900c00202000500201403000101700100000602501200700000f00c00c00400001f00f00000c00000000602700300100c00700700000000900100500700001700200300a00000300100000600500800000200601500000200104600001c00200102900201c00000601500200200000103300800700a00000f00101000000b00001400900200000000200300800900303600300f01400002a01e00b00800200700400001a00000000000701802b00603600000a00500300100000201600700100000100200600400000000400800000400a00800000300e00900500100601400000001100b01000300200400000000400c00601600100400e00400000000300500a00900200000602f021001 else 0x75c503b640983b03cae0107f03429076e002ab6085500000a04fc102558025d006fd504c88032e906d0213cf212b9105b04071b90354a014ed01bc006ade02b970788303b18019d10294b14c78069e503fbd096f104b05060df04cf500340000000000d051e60856f03e0408bd304820000000000d014c300ad811e200000a048e812f800000200300000050660807140046e404ffb041941052f05e700000c0160202e45054cc03af80977e043ac15354110b507e080895000000000000000613886063dd07a63077170610108fe000008078c00665502aaa1866f021ad02894091d4102f1088ec00b3004a4200fb0011511311e021600000e024670949c03b2502093088dd0150b05cc108faf059200000b03eb504e6503368051bc152880109600e3a1085505f92004940179f050dc01624096700676007d9100f1912ca8036890530b02579090ac07ca705da2119790497507988076460510116cfc0132d0416a0669f083781261705e9506e6a079cf0239000000056e60972508d69058200000b045880804406b800000d047a90260200102127720199f089ad03f3a06438048900154548a500000e0848908e66068bb0833a07ec104391188a00000e04f500000d089600000000009007a904d130516603c0f037e5045b800bd00000603c3041f9401bac03a5a03e4605e27138360920000007674b1038ab08af000008170a50536e00117003d6003ac02325006b7034b608ae003d510951505cd001b8c00d4a07049054bc076300722403d200000207c250740003a0106412081ba03d100759f04f100000600b5000009062900000a049b2087aa07b4171b5502da1163c503c70000000000000000000000100001002100000201c00000301400001501201000f00700101100901a00200e00000000100100600000901900000102400700000a00600000700700000000900200300000d00300000800600000501d00100300100200000700200f00000700900700700401000100300e00a01f00100200100200600000000401f00000d00100800000301000200000400202b00c04900300a00d00200700000201200300003500100300000b00000502d01100800400000600900500000500000200600000000600801400002000000e00e00600903201100700100f00100000500a02500001200e02200000500900300000900100901f00102601a00701300800400002100400200000000400100700300000100001000100700201601100c00400201400100200300e00800e01300000300c00200100000800000700400000100d02900000c01500000102800800c00200400900601e01400000500300600000300400000201700600001e01300400202b03a00300d01100600000800400000100000900a00901f00201a01600100201600300a0190) else (if i<3 then 0x305c1501a8406a200000167f7606d5c08fbd012100000e00e2000006023df040880266621fc00000285d40052d00000f02939086fa16f12017c4106cf0926505f8702305489a00000e02d08088f9636e4048d0048b11864a07fe707d0c05f2c0869001d1507c92039780056907f0018e5304ec30803000006097c907b18003740614b096e0000070144000007052090389a01d3604e9000000000090321404790026d604310000000000b098800000b033e402fed047d80022f08dc00000b0475c0515102520060e60946b060f104bea05c77033b30091f038c107aa301e6e0737507ef00864804c1000000000020893603560075451536c024f20545f1769504bd10575e08e100000007b800000f07c7e05d8c09848051dd01cee07abd041ce1387c093800000c01ab600e8504920000000000309305065790793d03e5105ae00716600fc605d4d01e0e091700000106af70224c049000000a00ac0000000000d02f180207b0897613cd0000000000a01080000000000f03ad408004056fe01988000700000d01380000050912a084f7041700000b0816a00a28575f3081a305e5a01160000031251e037f41541109828001b7016e000005070b000001083900000107861054800000506f300785a020f006c200000b0366e03cfc002060652618654007880508f042d00000508da7074f000b200000f0913206bdc08b9608ee2028df01a34082db08e88040fa0038100a8a0649e0828804c60000090750f000ea006720663c107df091fe05d2006960000000017b07122046b702155043bb43b200664c02fce02a4a108d000006079b00000b11f300000116ce3010e2067e903d46021fa02988123d90683901b78248df04a8001db8003b006d6406e50000070701b02ce603eab043d2184d806c5a2491e01252077ed006e801bb4057f800d6701410000090093912aae0777211ef000004076d00000004b5805e64009500000001c2e05e0c047c708d84063a3047800349000002000a516be000002095f4126000000a02c9d07bf3073a5008a40906f02b44038df07060090800000e0772000000000090341000004013fd092c706c310595204ad0002ea08b7a063bd022b2016c0000000000000002035140284505ecc124150974d16c2c025aa066ce12dd0017d00062701ec100431075b00000b01cd0000000000100d2014d7903eea0118f008230713f042280455906ce3047260637c0496b04ba0050a00148c072c00000d04fe004778063200000d07c66082be052220438506d300000b01cf005c9403f18045a9085300000605710001c0005c2068cd0137c01976084c312e070549013244038f8093290735f0518b0598905c6d006a307a4f08d2b03c860065e051f310fa200eb000006044e5041000000800afe0066b013b506f43059c40 else (if i<4 then 0x143901ac0139e7087df18e94019cc06c8a0921e0958502341123c00965c02c5a0827f170fc039ac014dd04610000020569000007126cd017a4047e401d8b032d501ed6027cc011960806907fb000004055900000e03f8f09050000011656000006007d112f50000000000106b4001ff313d080890614d6103e7408c7407b6405dcf04f2c0493e07330000040654407559003f9094f00000b092ba05f000000000005001401787e01d4e05cf30627b095d706f661728a001d806c4e08253072ab04fb1029e000003034a60238a005dd078e100f31062c90029b05f1c08f8000002004890885b12ee000003026b106fef00dae07ffb083d409614084d80423203ace000290646501e1307dcf01568068d009625185e200b1d0441d01ad605fd102dbf1235302701013ec063940697000008080210483f070cc047f0000001547002fb1024200000d01e4302e1c0931f03f6308629058ae0283d050e801820000000000a177740787000007085400000012b120570d04268062ec0924c793ab00c80000000000000a9e0743f086b5081c1138a508a8d72c20000000000800c110114f736e80914c0751502470000000000504da108360000000089f03c500000b1254000004005b205a5e010b100ee9022390617707a0108b4603f7b0724d03e2708f5f06b981533c10aa102f6f05b3b02ccc068a709484128560314e085cd041bd13a8e069d00237d067a00245b124cb00a400000b065000000907d80000070424e095a802360000060736216b71097900000c018f30942319127065ba08a4b03871015fd070d724815047b0000000000905211028a00000000003124f907a97011f00000b06e3b083c0000000000a08a2c05dba0622107dd303b5806c7500a5307da00000f05d300000e0766a089b10009907b310711e13430000080553e07ad202a80000000000b02e70000000194100bc609270082ca03bf40523a068250954e02ad000006027d705be412b0a07c800000007ac3027e00000000000000070742c0268703b9f08ab206cb000000000000000717e0d01800048f603e30180cc01fe500ea00918d062a40768f00f5208c0d048ca08ff607fa61377c046df000b6080e307f2c0850d0430b02c2b08e300000b03021034db078d7029a50106212cda13dca0978e01d7107e2001835064fd00cd00000602627400ec01220097b000007030f0000000000805bb0000000000802f4000000000000000300d700000000000000000000d047680413c0450312c4a0929f02bc304d3611d00000000000d0323000000000001023000008007600000005c810941900f28030e006534032c80789b05bde0028408a060027402353058f7082f1176e00000d10d8b01cb00000d1229c06f8a0026c016d512abf002d00000009856003100000905e8000000000 else 0xb5104cb1053e50702c02e6c06b500898700cca08c3900ce310a4d024ef05d0f03dd80168b0287b0004107342074bf04aaa13df000000000000000007f4f00ba00102b08baa0600d137a80675607153048a408dfc0824c00060000091267208ac000003026e0065d30267b04cc000000060ce429b3002f00000e045f903bbd052ce030000308e004dc031fa03ef60810d077c103a1809695019a2185d201c4303e8d05e4302c3d01fb204c3603fd60501002b2a036b905bfe053500623503ab0000050542800b7e02b6d056870178208bb203e6d078400000206bc0000080420f0399707a35094d0000000000e07571001e113ca802e3000009042fd0874217d1000000000000000c0299d0457200efa10fe8029700879d05a4404e8d051cb0813a02138080d602bb6001fe0964f170300000f01aab03a31002c000000039b00000000004044200000505df51687f08e200000902aee0583000000000040445500038002b805af0124da065160634e0312400d8d01ef501de40940000003009200000f08aa00000c0658c138b00000916b9502ac70877801ee603283028f448a1602fae026a6020a808cce00582040da0453d06fa4172ac0169c01c900000c0447e035c0188dc0128210b310184104b4d064c207e9a11d7701f8d00fe1019600434706eac019e60694303db80047908a99000d600df002cfe08f38069be075a214cbc0282c023a6051a70747000005085d76249a07e8601c3206d10190db02a07010aa03c2c02c0307be202b060767012cc5019bd00b480739c044a30685c0586a09335837c40495707100024c00000d1284701e3f0378513c5c02861022df04e070250b02d260481e01f5a0073a0723713a6f07e6805259151a50963f16976017390256801a23025ce1256605d1d04ac405441073e807f8c1760404dd400b0f01f1904d0605ab6046449823c02cd9008c606e25097e9142c406d220231000001108600000a0618508d5b0606004ee20166e0602d062fd074541050b0730104bc6055e508bea0973c129c2151b012f6900edd06312003960233d093e4088c202dd015c8303d0611ca705b27074ca004141295a1258000002035d31944f042b5042740695b0385908b6008d0c004f4091b801010000040174000002001a402be51080f08300054a0066a7067f5072f403a9402eae03f5e16b69054ff08ce90596f023f701c5c13c8312462118a2059f4008db01a71012d9198a3035f402c4b03bab0820a03c110761900c59081eb05a3e135700000c0619b050c1013a600597043c10376000002108b505506009000000b0251906d4f003e00000904b6962c90020ee065aa0703f0612306150004c7034040527302dce098920394e07bc50391b04dfe05caa072500000000007055a006b0708a3b033441379002bd003d7e00463))) else (if i<7 then (if i<6 then 0x8067dd06a630799108f1d089f902f0000006021e01004406c9600d33031b4081550163009470000000000e00f6d059b30444803181150f401a51073880421508e4c12757076a0000073018e04dc0000000000000000000000000400c2d0502b04d8f0538f036700000d0753c116cf012c2053dd05f54011c00000609454014bf094a00000d08ad00000708cdc02b8100f4206fb501b64033c00778f015b000005086070678d0689109346077d303dc2082e204a3606e7406ee212c5000002069211872000000006350674f060bd05ed1046ac0395a009f00337d0443a014930468d04654079f105413220f60870901e8d1245a7746700ff000007089e0192c411a8c022c90593f00d05018d00000a06b1203c6a00555087560086c054600000a0589c12ec7126600000d03696098070081d018b6093a00000d0812d46838129330910e1545b10e120384801ead031a00000701399036da06f5a090cc04a5701df0000000000e030ab0801007a500000a12aff012f3000100000801a9300ecd030c000000000070382d04c4b0403c0428303d30000000000000000000030175914d95605c00000903c900000d07b70000000000e0172604a1e053fb07a20000000000808f610071c06030000000000d02851032f000008040a1022e0000000000f02eca04fd305eb207f5e126e7041e202690000000000805528091c7069f000000000000000311ced0112e096c11296e025f217ff00000b03254064dd086c00000c090900000307af002c850613d08d14093620429d065c11719408f900000104a0504f7908a100000102e9908f790415c04c760498a0295400e1302f3f1398b018ed15986138cf61f390358105e31060500000900b81071f1066ff084a305ef704e770889001dc50807000000000000000f06bf003ed50463f029f00000000000000000000000000000051286f0922200c340070e0863008ca8039660050c064700000906a700000904ea000001075800000b094c4031c3009400000c05f3206db10275904121137670333d03bdc086da02aff0181504f95053b202e0101a130347d16cd207316011120176805f4406cc60503d0159e01522820ea590b485d5d08910039d10975100c72146ee0025f11c9d05eaf12b2f13d490381e06da9070851053504db70867a090230818701bd7058e303a80000000000501f410849a0036d12940000060491306ebb08d3006de203cc2118dd01b5e0146b035900000f141300000000000000000796e0153e0681f03a7d07e1807e3f00a300604305549040be0051b17bf60842204bbf04ce31198d089ce05ce3059e206a8739847014f704b9c124b90717006a181328e03a200000a052b8088700000212cbd0072801f25027700000300d500000000000000000000a05fed0700107751058d60607d02 else 0x90b208c94028e806487169b708114040160888b16c7d0064d002170861803aa706ef0000080671000001000c1045e00000d85d30000010797b08a700000204e4c0024000004023bf015c706b2a03447129e00383c0432c024950679708a5132158074ee0943d03aea0099000004056b808224061cd0599201d65043f00000509037086630655711d96009600000d10a70000060225b032a301da815dc202a91153200000702a51089d0000040872000000000050319301f0801e700000f0925f077f00000d0726e08e0e0219c057aa0732000007074d00000c522e7078341040c0480001b340161817958067c700cff0547316f89021ce096ac02cbd05d94087c302d53086e10326e02f7a029ce04eb0000090281e02d7d08b3306be011f100000304520165f3031e2063ec0045c00de7085b303622069c5039200000b07e7e222840068305b130437a06a3c065f80537012d87071ab2479d066dd110f0000070858c0097c075f6039fc07dea110a948a62078050380a013d4073db005ea0956f0705b030de064b507c36086a5079e406cfb076b201b42118850838d0084708bff038e51119e0960d096b605045076f400dd708dd4024b70832e04d4a08b86065950636607b92080f20140304c2c051170126050e1206e1103b80007590831306ca1036e904f32011df0633408ed5044830709d0557a16cc8004bc06e9001872038660986006a96108980531608e7403a470393d0494e087ec025bc08cb7055bb01574035b207cba07d2b111ae00fd412bb210588050f606e44009d005fb5069aa046270939e08090028cfa90b706e890572b06df643b05026440499f0033e0843c042ca083fc04e3607ae50814f00a62005a6065e80158b05ff0058c6082ab07f7204f4101eb90436605b44041f30529b092dc128914013400ca30254e02e2d07d6908b2c06aef010ca010d90100d1513403ff6011e106d8f04000088a8009860204112c23153d313d1a0770e01bfd1734c015ed052e801047021b406d9a02b3c06c1c18182066e60821a0578f059af030b7052f505b5b04a60705c804e5902d4c06baa01c700000605f600000f06c6308cf403dea066b803d8c04ef816bd10357000000000000000802a3b0361b057c9044c000000053c81524117a400000a13ae2072de0976000000000000000301fd00000000009002a00167e03f2d077b0000080346a078200000a011350668705841096d302d12007fb01c0c083be01f3804b230259d0781900740000000000d07f600628f00320000070040c02c100000402794079d6031300000f085a000004031db0301e0673303b3000005098ae044b806b35012930834c011000000604f6d094e00000d041d000003072b0000080899218be600f00000000000301d5b029160507c00d9c014a00000104d70037a) else (if i<8 then 0xb803f97154480170c015a9017bb02584062de0402017b6f039040155d04c51128da11f2000006036fc042a00000f00dca0808a01c100000c052400000d0774405d7d12e400000908e5501ca50363311b5605946093500000106b69033050015d0288913cec07ba00000c016f1046c0000000000c0741300c0b03bcb010fe0563508a600000000002077ae0587d64025063500000f012ba0191d008770272a0792d13c60064500000f0201008e9007ed604d550500d0042407e5201b11022ab088be071d00000112aeb070710588c063c112c6e0186304d6618a27014210662000000000040271e05e10000070303000000000000000502ca712d400000a153e814e391210f076000345b0406904405137e2078fc0414b0123d03f0a0884106675081700000d02ed503d9c0460d02039109930852d02c6d07eba08f0f0220202c7912db9078b00083304181064ac00051136e00000bb3d9312d520374a06f100000607566141c800160000080871e054d308eb3094400000d0214000009040c606b700000000000000090882d068f0000000000b02f200000c057331120804056070ab07d5607b011835208b5000008088100000803553116150052696c0206f0706f7e033870661702bf30008b007e90883907bd900f8500c90000000000403708050bc0911800770000000000e05c480729408927074900000208473774510306b059d9045c209553095000000312ea602eb0028000000c011b00000212e9d037100000b101b0067200000b061e7000fd12ba00000b05a2b02a791313a00db10534408de10377102533000000000e05a6608f4605ba407df004f0f00b6c07d7807cec179dc06dc000000021d106abd081d600bf301be818fb00000f068e00000c041180327905d54042521083604a7d05816018a00000401e9a0331b37d350085301c85087300000b080ad08460013360769d02b1f05ad702481060a605647064e7023cd012af11214063f3004ed0776f020b1091e3036c9097d8083ad07e4504faa072ef008ec006d913d390857c05767027be04a9217ca50151005170012ef071950952307b2d07c1d1680a061620900f08260090df07eec04ab10206d05b7c08dbf037d0073c30044c033fd09281097060317a01f930124b0177c04c02003c50558b070f208655035e90718a04335057b702df100351058b70228c035200000806f9605a0b024d0000000000508684045400000608eca01c68067700000507a10081f3046fb0626f0923004ae00000106fc801d0e0585d0195a004a5070ed0485400a0c06bb80971d0200307c020878905c24040900000012310088000981a0456b0316a10b2d62c2000008190e00000111e6108fd00000f02fda02d8403ec413bf700ab602403092a000f70013c300c411110d06d790241402027005fa0 else (if i<9 then 0x80c000000000000000e04e2602de506425067b216fff09531124a007c47009e201e28045d602a17022900000b09378074800000513a10000000000000008096600000a02f5a171240574000003152b600a78034fe0211c2485e056740210905c5000000000000000000001024370620601dd000008185f10688000003071e908862137b0000060373f019f7051940580271f3c0957802f8717bbc0512200a180466001fa00684d073b1008fc07521018550907507ea8075d405d610987000000000000000c04cde020d206a500000501b00000070959305dec0451608c6205c350315c18150000001521a0894c0217400e5207659056d6084481244c03e9f0145a0876e0795f08c8f095ba03480000090687e0762c02d940134f06ec701a4d065600054012c77037b372b920449410f6b0305d11b4c0505706aa508b1b026c604043042e4188e90746c07949176d101364057e6039ef053ac012750079a008be0365802a200000000cb0000000000d0773e04070036a9032be055fa043e00000101f7d0540b14ef508bc602efa074a80164006908061bf0117303727041a11594e094ba0263e006f6090f0134280193508d4200d1b0532107a83091ae05ace022f000009049db04bff07cf00000207cc00000a00e000000c04e1000000000070307316a100000a061d70360712f4000001091590691e07f39820f212500000000000505a7f0088d01d9e080b000003068650309b06ff6048600000b136f0000000000a007b000006072100000000002075ec1096b0591b05a920069a092e000003052a5026f705b900000c08c520364a095e60278602656011af02b761406c07d4605a85092f90526b02ff90487402272106a701a6c61b5712ceb0467705067007cc02f9507f1b25d4c0474f0459a006c30790d02ee10130402a6712cf600e9b1924262b9400aa7056621287d039810608d03fc501afb039c00791906edf03df504afa063000473e043580509618b700000000005085ef02441093fc221ee0019505b6c018840720b049e0082940320f00181067000000000000000000000000000027a10296b08f2b009c5056ad078a00000f07443035ab064440103105a1704b7402e5d07cd303cd81860210ced04dee029b608199044d207bb708ea3044f907280000020311902081091900000000006001200579c176a7033a70053000005056c700132063800446e400df054e81730304881049f0000030304c08c1a0218a03f4703cb4040ef03b420565505fcf05cb30727f1510903531097f9073f60189700bbf00c6d005750609f48a7e028b401b2c033d1017f403fa00916f13c050332c00e60a6775071c103c4902d6004f840205d023ea08c2d05974084e701ae308b0e0851b05434090e50131e0845e0693d0560d0375f08c4e06a4a152af016 else 0x60528304ca506dd000000000071644403224008000000000003020c9085f901fc414ecc02bae0666406211029200000d068010470406f2418d6d0261c07db000005087b40533000000000000000900b9b05ddf093b207d3e027600000a00e7505f7907b5803da9069900000d03100000000000000005009be0601e049a00000604b3a079a908ef408d7108409038b916d4703a690805a05623047100000706acb024ad01203018c0093d0076c20388a05aa0000000000c0551104ed00835c151c106c0c087f707fdf17900000050555e0513c04d9a167d20343b0329000006083e6046940190e12a200000000000061a1009a4173d8084191966f220e703ced07fcf977a3015df097a20779507f9c08d990379d006160904e0023711d8b0823c037ca096830859809015057de017e6029d81672802d360212501d290135802e8c0339312b6507a76016a5533230335000002084b0000070273707c5d00fa4034e60561e1394f04b1b01b93017100000604b8604a2b0060606982061f2034ca0165601a0b0350905c0000009062bd0556d029050147400ae108fcb06241055ce06a0b095c804c900000a06e08010510324a1192703b7901e5c02744b3b3400e48027f20590406cd50226a0221b025e500f9b198500000a04d200000b01cc2123e30484d13164055df00be00192d0514d05bc405fa411c800000f03be6093c2129711098e062500539703b0a07d1b03fee06400000090611e0577503d6e022281511005b8c10d3a1380001f6a03e16184800000005ee8049c6))))
def hashf2758l13 (_i : Nat) : Nat := 0xc0300000304f00008058b0645071714f0000e090000070ab000060360000003c5141e06fb052f001d068207ab07ea06e604c0000e0170000505a3094b07800000003a0424028b08be044907f00000007402c701900004041006900a3709b00a2f093b0ac3016b034d05c00adf084f023c0b44029708d602e00009031b045f00b0000716331230040000000000000308a709c1062902440a9005510a6d026115e1081e04e0000412a0000003eb0370000314c202f9121200e616b6033403be14080b090630000206d201a0000211ad107713d70a800000000c00c306bf01cd0880000000f6060a01fd005e050307450a47092f038902bc083411e10960000d08000001015209fb13fd07dd1163104e051801e611f2072809aa05d20aec16210a74002903d50590086e0758021307c7098e048a08e6043f07060498046900a1004f0615082005fb03990897054f073602d50a59032910ff06c208ca0b23097007ba035f0b5000000004095001180a1e014704bb056a1660000302ae0b3e01d40af903a4027f067507780760013305e5125508570b1a00800121099b0477018501b000030877164d057f14770aae02200003009000030799006d09d3145006500000000a0910000000000000000a09eb04a0000000000009053a03fd0100000000070a0b04d60208066f06ab000d10e0000613bb00da025805bc1690000c08f020015000101030000050000030f0003040600000301010a000b04060005010d09110002040701021016030000000332000705060103000724020a061d0000040006100002000200040208
def f2758d9 (i : Nat) : Nat := (if i<1 then 0x41006b3c30677699654820087bcedd98d294a904018df0b7305a669520802dd63a9554cd08a61005b6c752aa9de114c20097d8ea598d3c22984016f31d4aaa5584530802d1f3ac655113ba410042fe76ecc6a0a848200b7d0ea55511422984014eb9d4aee6668d208029b73a95dceed1a410052ee752bba21a348200a79cea5772ab46904014d78d7729b520d208021f73a966374c1a410043f676ecc68ca348200973ceb195444aa904012e78d6722aa95520802dce1a2d32cb2aa41005a9e758caa225548200d6b860ceed34aa90401ab70c1a21a6955208025ee3a36634d2aa41004bea752cc69a224c200b6d4ea5553bc44984016ba9d4aaa8888930802dd53a9554cd112610043ee752cc6e8814c200c1fc5d19344302984018eb8b6712aa605308029be1a2dd16ea92c1004bf4345ca2ca3358200cc7c644eedb2a6b04013ae8d871953889608021f73a96637441261005b2e752aa9de664c200975cea598d3ccc984014db9d4aa9b7085308029773a95537010a610043ee752cc6e8214c200a75cea554db042984016bb1d4aaa88845308029f33a95536610a610053ce752aa6d4214c20087dcea598dd0a29840107f8dab30b9545308029b73a95536e40a610047e6750cb609314c200bf60eb18498a42984011fd0dc6e13148530802e7a1b34430298a6100627e32e8869d734820087f86db8355302904016fc0d169a3388920802ddc1a2d32c7112410063bc2d9c1aa98148200d578d438c50b02904014bd8db6a2336052080293f1b6d44eec0a41004bf8746cc69a2248200b574eb1954444490401b748c954e335492080357c1834434d11241005bb234da658e224820097746e34cb1c44904012fe0d172986889208029de3ac5d302a8a410053e6750ba8cd5148200a76ceb17519aa2904014bf0db6a1815452080293f3ae5d51098a4100437e75ccb6a13148200f5b0d42a4c0aa29040189f8cba21a75c52080357a350e1942c0a41006adc6a1c52858148200a6ec6db4f19ae2904014eb9d42ea66545208029773a85d510a8a410052be758baa215148200a57ceb175442a6904016e70d169a5558d20802dcb1a6d34aab1a410043be758cb6995348200976ceb194a9c66904016ed0d1699638cd208029cf3ac5d4aaa9a4100633e32e776996348200a6f868b753bac6904014cf8db69e665cd2080359b1873bb4cb1a4100539e36da69556348200a7b868b752aac690401acf0c19dda658d208025db1b8d32cb19a41004bf4345ca5da334820097e868b94c3466904016ed0d1699658cd20802be91b6b9aa6a92410077522dcb354d5248200b7a868b4d2ac66904012ed9d632a888cd208025db1ace455519a41004b7635dc52ea3348200b56ceb1954446690401add0c19dda68cd2080357a1834434d19a41004bf4746cc69a3348200 else (if i<2 then 0x784520802d5e3ac6551108a41004b7c35dc52ea1148200c6f865ceed3422904012df0dc69d73845208025f63a96634708a410053dc36da69561148200877ceb598dd306884014f39d4aee5568d108029d73a95dcccd1a210043ee752cc6e98344200a73c6b3752ab06884010ef8dc6ea6660d1080299f1acdd4eec1a21004b9e75acc6a25544200a67c6db513bccc884012e78d57298799910802d8f1acd44ef2aa2100536e752bb9dda344200a5dcea57744346884012e78dc6a266955108029de3ac5d30298a4100537a75cba5493148200a76ceb17519a62904014fd0db68d814c5208037ac38f2a94290a41006b7871da52852148200dcf14438e50a42904014d79d72ea554c52080299f3ae5d4cc98a410052be758baa213148200a73ceb1752aa62904018f58cb955a34c5208031bb1973bb4698a410062f632e8868d314820097f06d38e98a42904016ee1d632931485208035f819519ae290a41005df0365a34c52148200ebb05caa4a8c229040177c0d98cd3148520803dd834cb1a6290a41006fd0955c32852148200dde14438650a42904013fc2dd70ca1485208037b838f1994290a41006bd832a555c52148200d6f06530eb8a4290401abe0caa21714852080297d1a4dd510b9a210053ae359a86d03244200a73c6b350da864884010ef8dc6a1b60c9108029de1acd436219221005b3a359a89de22442009774eb598d4444884012ee8d672982889108021bf1aee5b4a992210043be359cb6a1324420087dcea598dd264884014af8d6729b80c91080299f1acd436e192210062be319b86a03244200877c6b396d4064884014f70db6a152545108029fa1b6d4466a8a210053bc36da89995144200dbb064aa5112a2884012df0d772952845108025fc1a4e52e708a210053f836da88895144200b7346b3512ac44884012ee8d672985889108025dd1b8d44cd11221004bea752cc68e2244200c7786598cd42a2884016ec8d66a233889108025dd1ace530711221004bb6359ca61e3344200976ceb598d4466884012fc8d2729738cd108025eb1aae530f19a21005b96359a89563344200976c6e35133466884016cd8d66a2778cd108021f73a966374a9a210043be359caaed5344200a77469375332e6884010ef9d632eaa54d108025db1ace530719a210053bc359a86c45344200877c6b396d40a6884014cf8d76ea66549108021bf1b8dd4eea92210043be359cb6a15244200a6ec6bb7519aa4884014eb8d66a1b4149108021df1b8d436c292210043be359cb6a05244200a67c6b3753bb04884010fb9d432eaa609108021df3ad66374c12210043be371ba999824420086fcebd98dd2a4884014ed8d66ea33609108029cf1acdd4aac12210043be36dc8aaa6648200e4f858d113bb4c904014df1d1aee77699208025cf1aae530f332 else 0x178008000000000001e040801e04080000000000000920825c20f02040042080000000005e0020001c0817020431410000004e002001a0426810e608268108000040041021f0204d02134085502104084106100070410000000017810800000000003c081040841e04080d02104084000408406810e6082081083c081f02041e04080000000003600200000000000000d001f0204000000000000003c081b0205b021dc0040006608200660839820e60839820833041cc107306107810201f083c081702041a820800d810f810200000e040800000248200781020f0207c081078103e0408000000005c08400000000000000000bc005f0010000000000fe7fbbf4fd7fa5f37e47c3f7dee7da7aff55e97c9f8ef13ddfb976ded1d8faf759ea9d3fa5745e67c878e70ae0bbcf776e9dc9b7f6d6d5da1b2f5ceb4d5faab4c686ce99bf35665cc196f24e44c7f8b70de09bef7caf6de8bad712d95a0b1d5f2b5558aa753a9e537a654b694523a3d46683d029fb3e279cee9d33926fcda9912da58c9f9352223b4718d916a2ac4386307e0d4087ecfc5efbda7aaf41e5bc6782ef1dbba5740e6dcb391718e1dc137d6f0dcdb735c694d15a033b66ccc596327644c758c31361cbf1752d858cb055e2b754aa814da894ee99529a4e4788a90c2134027bcf51d838c704d79aa34a64cc097c2ee5c8b695b2ac544a614726a4c095919228408780eb1b231c610bd1702cc570a9148248468881061f83c8740de1a8328600b61582884c0740a01181e0320500780a00a0029fc1b6d344508a41004bf8371a854a1148200a7e86db4d19c22904014e78d56dcb66a1108021df1b6e530f33221004b3e75acc6a27744200a5bc6ab754430e884012f70d57298))
def f2758l9 : Packing := (226,6,7,0,4,11,0,f2758d9)
def f2758d10 (i : Nat) : Nat := (if i<19 then (if i<9 then (if i<4 then (if i<2 then (if i<1 then 0xaf79ca2e25548200eb7aaaa225548200eb78baa225548200eb78caa225548200af78c1aaa5548200af79c6aaa5548200af78c8aaa5548200af79c8aaa5548200af79c1aaa5548200af78c3aaa5548200af79c3aaa5548200ed78a39de5548200f97a889de5548200ed78a89de5548200af7acc69a5548200bf70c169a5548200ed78a19de5548200af78ca61e5548200af78c869e5548200eb78a1a225548200eb78a3a225548200af78c169e5548200af78c369e5548200eb7a8869e55482008ff9c82ea5548200ee79a66156548200ecfa776996548200cbf8baa2255482008ff9c32ea55482008ff9c62ea5548200bef0c169965482008ff8cb69d65482008ff8ca6dd6548200eaf9a6a216548200cef8ba69965482009ef8cb6996548200cdf8ba9dd6548200af79c62ea5548200af79c82ea5548200af7acc2ea5548200af79c12ea5548200af78c32ea5548200af79c32ea5548200ee79a65965548200aff0c169a55482008ff8cb69a5548200dbe8b2a225548200af78ca5965548200dee8b299a5548200cef8ba99a5548200af79ca2ce5548200ee78a399a5548200bd79c72ce5548200fe6a662ca5548200fb6a882ca5548200ee7aaa99a5548200ee78ba99a5548200fa7a8899a5548200fc7a7799a5548200ee79a799a5548200cbf8b86a1a3482008ff8cb6a1a348200afd8c36a1a348200aff0c1699a348200afd8c3699a348200af79ca2c65548200bf69c12ca5548200bd79c72c655482009fb9c4aeda348200bf69c22c65548200af78c369a5548200eb7a8869a5548200e778c969a5548200ed7a7769a5548200af79c769a5548200ef70c169a5548200af78cb69a55482008ff8cb695a348200bfc1c32852148200aeb9c4aaa664c2008ef9c62e953482008ef8c66e98744200cdf0b19dda6482008fb9c42e951482008ef9c62e951482008ff0cb6a15144200afe0ca5c52148200afd0c169a33482008fd8cb68d3148200ae78c66a255442008ef8cb6a266442008fb9c4aeda64c2008ef9c6aeda8442008ff0c16e97648200afa9c4aaa224c2008ff0c16e96348200afe0c169a2248200aef0c169965482008ff0c16e986482008ef8cb69965482008ef8c66e2aa482008ef8c66e982442008ef9c62e931482009af8c86d953582008fe8c26e973442008df9c72e931482008ef8cb69963482008df8c76e95244200aed8c66a233442008df8cb69d7348200afb1c4aaa114c200af70c169a55482008df8cb69d7148200acf8c66a277442008ef9c62ea8848200bde1c728521482008ef8c66e98344200cbf0b1a21a6482008fb9c4aeda3442008ff0cb69a11482008f78c56e987442008bf8cb6a18148200aef0c16996348200aed8c36996348200aee8c66a222442008fb9c4aeda3482008ff1c1aeda648200aaf9c62ea8848200 else 0xddf2772c5a648200cff1a72c5a648200abf9c32ea8848200abf9c52ea8848200eaf9c62ea8848200abf8c12ea8848200abf9c12ea8848200abf8c32ea88482008ff8cbaaa88482008ff9c32ea88482008ff9c52ea8848200abf9c72ea8848200abfacc2ea8848200baf9c62ea8848200abf9c6aaa8848200abf9ca2ce8848200bbe9c22d68848200abf9ca2d688482008ff8cba21a748200bbe9c22c68848200abf9ca2c68848200abf9c3aaa8848200abf8c5aaa8848200abf9c5aaa8848200abf8c1aaa8848200abf9c1aaa8848200abf8c3aaa8848200cbf8baa216548200cefabb999a348200aff0c16d9a348200a7f8c96d9a348200ecfa77999a348200eafa88999a348200e6f8b9999a348200cdfabb9dda3482008ff8cb61da348200cbf8b1a21a348200cdf8b19dda348200e9fa889dda348200cdf8b89dda348200afb9c4215a348200aef9c6215a348200adf9c7215a348200aff1c1215a348200afe9c2215a348200afd9c3215a348200adf8c76d5a348200a7f8c96d5a348200cef8b5999a3482008ff9cb215a3482008ff8cb615a348200cf79b52d5a348200cbf8b5a21a3482008ff8c8aeda3482008ff9c8aeda348200afd9c3aeda3482008ff9c5aeda3482008ff9c6aeda3482008ff9c7aeda348200afd8c3695a348200cf78b5695a348200adf8c7695a348200afb9c4aeda348200afb9c4295a348200aef9c6295a3482008ff8cba21a348200cbf9b82e1a348200a7f8c96e1a348200e3f8b9a21a348200cbfabba21a348200cbf8cba21a348200cfd9c3aeda348200cfb9c4aeda3482008ff8c5aeda3482008ff8c1aeda3482008ff9c1aeda3482008ff9c3aeda3482008ff8c16e98348200c7f8c96e983482008ffacc6e983482008ff8cbaa983482008ff9cbaa983482008ff9c52e98348200eeda6668ca348200ebda8868ca348200afdacc68ca3482008ff8caaed83482008ff9caaed8348200ef5a5568ca348200abf8c868d83482008ff8cb68d8348200cf78ba95583482008ff9cbaa883482008ff8c16e883482008ffacc6e883482008ff8cb6998348200cdf8ba9dd83482008ff8cb69d8348200cef8ba9998348200cef9ba9998348200aff0c16998348200de79b6954a348200ed7a77955a348200cf79b7955a348200eb7a88955a348200a7f8c96c5a348200cf78b1955a348200ee7a66955a348200cf78cb955a3482008ff8cb955a3482008ff8cb595a348200cf78b8955a348200e778b9955a348200cf7abb955a348200dcf9b7998a348200cef9b6698a348200cdf9b7698a348200dd79b7954a348200cef9b6694a348200cdf9b7694a348200d9fa886dca348200cdf9a86dca348200cff1b12c5a348200dafa886d8a348200cef9a86d8a3482009efacc6d8a348200af78caa225548200eb79a82a25548200) else (if i<3 then 0xcbf9baa217648200aef8c3aaa6648200aef9c3aaa6648200aef8c5aaa6648200cfe8a36c88548200cfeaaa6c885482009feacc6c88548200cff2aa6c48548200cff1ca6c485482009ff2cc6c485482009fdacc6cc8548200cfd8a36cc85482008ff8ca6cc8548200cfdaaa6cc8548200cfd8ca6cc8548200cfd9ca6cc8548200cff0a36c485482008ff9c32e965482009ff0c16e965482009df8c76e965482008ff8ca6e165482008ff8cbaa965482008ff9cbaa96548200aff0c169975482008ff8ca6e17548200dfe1c26c48548200cef9a6aed65482008ff8caaed65482008ff9caaed65482009df8c76e98548200adf8c76e985482008ff8caaed85482008ff8cbaa985482008ff9cbaa985482008ff9c32e98548200cfb9a86d0a548200ee7a66694a548200eb7a88694a548200deba666d0a548200cfb9a66d0a548200dbba886d0a5482008ff8cb69d8548200cdf8a36dc8548200cdfaaa6dc85482008ff9cbaa88548200cfbaaa6d08548200cef8a36d88548200cefaaa6d88548200aff0c169985482008ff8cb6998548200cdf8ba9dd85482008ff8c36e885482008ffacc6e88548200cef8ba9998548200cdfabb9dda648200cfe9c2aeda8482008ff8c3aeda8482008ff9c3aeda8482008ff8c1aeda8482008ff9c1aeda8482008ff9c2aeda8482009fe9c2aeda8482008ff8c36c6aa482008ff8c56c6aa482008ff9c6aeda848200afe9c2aeda848200c7f8b9aa9a848200c7fabb2e5a848200afb9c42c5a848200adf9c72c5a848200aef8c66c5a848200e3f8c96a0a848200abfacc6a0a848200cff1b12c5a848200a7f8c96cda848200aff0c16d9a848200a7f8c96d9a848200a7f8c96c5a848200cfd9b32cda848200aef9c62cda848200ffc15388a114c200ffc0b388a114c200ff625588a114c2008ff8c36e2aa482008ff8c56e2aa48200ffc23388a114c200fde27788a114c200efe1a788a114c200fbe28888a114c200efe0a588a114c200fee26688a114c200efe1a688a114c200adf9c72e2aa482008ff8c86ceaa48200afe9c22d6aa482008ff8c36d6aa482008ff8c86c6aa48200afe9c22ceaa482008ff8c56ceaa48200aff1c12e2aa48200afe9c22e2aa48200afb9c42e2aa482008ff8c86d6aa482008ff8c36daaa482008ff8c56daaa48200b5f8c96a27748200cbf8baa2187482008ff9c32e98748200e9f8a3a227748200e9f8caa227748200adf8caa227748200cbf8b1a21a748200cbf8b3a21a748200cbf8cba21a7482009f78c56e9874820097f8c96e987482008ff9caaed8748200e9f8a1a227748200cbf8b5a21a6482008ff9c3aeda6482008ff9c5aeda648200cff0b161da6482008ff8cb61da648200cbf8b3a21a648200dbf2882c5a648200cff1a82c5a6482009ff1c1aeda6482008ff9c7aeda648200 else 0xd3f8b9a21824820097f9c12e58248200eb78a89558248200d778b99558248200d6f8b99998248200bed9c62963348200bdd8c76963348200bfc9c22d63348200afd8ca6163348200bf99c42963348200ef59a52963348200eed9a799a3348200fada8899a3348200eed9a899a3348200afd9ca2d63348200eed8a599a3348200fcda7799a33482009fd9cb2163348200afd8ca9563348200eed9a65963348200afd8ca5963348200ef58ba9563348200ef58ca9563348200bfc8c29563348200bed9c62163348200bdd9c72163348200afd9ca2163348200bfd1c12163348200bfc9c22163348200bf99c4216334820097f8c96e16248200bde8c76e15248200b7e8c96e15248200afe9c8aa95248200b7e8c96a152482009fe8cb6a15248200afe9ca2e15248200bde9c7aed5248200bf68c55895248200bf68c56095248200cfeabbaa952482009fe9c1aed5248200dde9c7aed5248200bf68c56a15248200ebea8869d5248200f9ea882dd5248200dde9b82dd5248200f9ea889dd5248200ddeabb9dd5248200bde8cb9dd5248200ebe8caa215248200dbeabba215248200afe8caa215248200ddeabb2dd5248200f3e8b9a215248200ebeaaaa2152482009df9c7aed5248200d7d8b98cd6248200ded8b358d6248200eb78a5a215248200d3f8b9a21524820097f8c96e15248200d6f8b95956248200aef8ca5956248200d3f8b9a216248200d6f8b958d6248200aef8ca58d6248200d778b9955624820097f8c96d95248200af78ca54d5248200af78c568d52482008ff8cb68d52482009fe8cb6095248200ef58a58cd5248200d7d8b98cd5248200aff0c16995248200af78c569952482008ff8cb6995248200af78ca9555248200ee78a59995248200d6f8b999952482009dfacc6dc8348200ecf8a39de6648200f8fa889de6648200ecf9a89de6648200cbf8b86a1a5482008ff8cb6a1a5482009df9c7aeda548200eafa8869e6648200eaf8a3a226648200eaf8a5a226648200aef8ca61e6648200aef9ca61e6648200aef8c369e6648200cdf8b76a1a548200cef9a86d8a5482009efacc6d8a548200dcf8b7999a548200af7acc694a548200cef9b6698a548200dafa886d8a5482009df8cb9dda548200d9f8b7a21a548200af78c56a1a548200aff0c1699a548200af78c5699a548200cdf8b7699a5482008ff9cbaa986482008ff8c36e986482008ff8c56e986482008ff8ca6e176482008ff8c36e976482009ff0c16e97648200edf2772c5a648200cdf8b39dda648200e9fa889dda6482009ff0c16e98648200cff0b32c5a648200cff0b52c5a6482008ff9cb6a17648200e6f8c96a26648200aefacc6a26648200aef9c1aaa6648200eafaaaa226648200aef8c36a26648200aef8c56a26648200aef9c5aaa6648200aef9c8aaa6648200)) else (if i<6 then (if i<5 then 0x8ff8cbaa963482008ff9cbaa963482008ff9c52e963482008ff8cb6a163482008ff9cb6a163482008ff8ca6e163482009fe9cb20d5248200bf69c528d5248200bee9c628d5248200bee9c620d5248200bde9c720d5248200afe9ca20d5248200dde8b72cd5248200bde8c76cd5248200b7e8c96cd5248200bde9c728d5248200bf68c568d52482009fe8cb68d5248200bf69c520d5248200bf68ca54d5248200ef68ca54d5248200df6abb54d5248200fb6a8854d5248200f768b954d5248200ef6aaa54d52482009fe8cb5cd5248200bfe1c120d5248200bfa9c420d5248200bf68cb54d5248200bf6acc54d5248200afe8ca54d5248200faea889995248200f6e8b99995248200eeeaaa9995248200fcea779995248200eee9a79995248200fce8b79995248200b7e8c969952482009fe8cb6995248200bde8c76d95248200deeabb9995248200bfe0c16995248200bf68c56995248200df6abb2955248200bf68ca9555248200afe8ca5955248200fe6a665d55248200fe6a669555248200fb6a889555248200ef6aaa9555248200bf69c32955248200fe6a662955248200fb6a882955248200fd69875d55248200fb6a885d55248200df6abb5d55248200bf69c754d524820097f8c96d93248200ebd8a3a213248200d3f8b9a213248200afd8c369932482008ff8cb69932482008ff9cb699324820097f8c96e13248200dde8b76c55248200bde8c76c55248200afd8c36a132482008ff8cb6a132482008ff9cb6a13248200aff0c169932482009fe8cb5493248200efc8a36093248200ebe8a86093248200b7e8c96a22248200df68b55493248200d7e8b9549324820097f8c96d53248200eed8a39993248200d6f8b999932482009fe8cb6093248200ef58a39553248200d778b99553248200bf68c58cd5248200b7e8c98cd5248200ff497354d5248200efcaaa8cd5248200dfcabb8cd5248200ff49538cd5248200fd6a7754d5248200ef69a754d5248200fd68b754d5248200ff498354d5248200ff48b354d5248200fe6a6654d5248200f7c8c98cd5248200ff49758cd5248200ff48a58cd5248200ff48c58cd5248200d7e8b96c55248200b7e8c96c55248200ff4a558cd5248200fdc8b78cd5248200fbca888cd5248200f7c8b98cd5248200feca668cd5248200fdca778cd5248200efc9a78cd5248200b7e8c96d95248200ff48c29563348200fe5a669563348200ef59a69563348200bfc9c22c63348200afd9ca2c63348200ef58a19563348200ef58a89563348200f758b99563348200ef5aaa9563348200fd5a779563348200ef59a79563348200fb5a889563348200cbf8a8aed8248200cfd8b368d8248200abf8c868d82482008ff8cb68d8248200ebd8a88cd8248200d7d8b98cd8248200abf8ca60d8248200aff0c16998248200 else 0xeed8ba99a3348200e7d8c969a3348200afd8cb69a3348200afdacc69a3348200afd8c569a3348200edda7769a3348200ebda8869a3348200afd8c5aaa3348200afd9c5aaa3348200afd9c6aaa3348200d7d8ba2e63348200afd8c1aaa3348200afd9c1aaa3348200afd9c12ea3348200afd8c52ea3348200afd9c52ea3348200afd8c8aaa3348200afd9c8aaa3348200afd8c12ea3348200e7daaa2e63348200ebd8caa223348200afd8caa223348200ebd9a82a23348200f3d8b9a223348200ebdaaaa223348200ebd8baa223348200afd8cb6a23348200afdacc6a23348200afd9ca2e23348200afd8c16a23348200e7d8b96a23348200e7d8c96a23348200cdf8ba9dd53482009ff2cc6c48348200cff0a16c483482008ff8ca6c48348200cff2aa6c48348200cff0ca6c48348200cff1ca6c48348200cfe9a76c88348200cfeaaa6c883482009feacc6c88348200cfe8a16c88348200df6a556c88348200ddea776c88348200cff1a76c483482008ff9c52e973482008ff9c62e973482008ff9c82e97348200cbf8baa217348200cbf9baa2173482008ff8ca6e17348200dfe1c26c48348200df72556c48348200ddf2776c483482008ff8c16e973482008ff8c86e973482009fe9c2aed7348200cef8a16d88348200dcfa776d88348200cef9a76d88348200cf7aaa6d48348200cf79ca6d483482009f7acc6d483482008ff9cb69c8348200cdf8a16dc8348200cdfaaa6dc8348200cefaaa6d88348200cdf9ba9dc8348200cdf9b769c8348200cf79a76d48348200cfb9a76d08348200cfbaaa6d08348200de79b69548348200cfb8a16d08348200df3a556d08348200ddba776d08348200cf78a16d48348200df69c26d48348200dd7a776d48348200dd79b79548348200cf79ba95483482009f79cb9548348200e9fa8869d7348200cf79ba9556348200aef9ca6196348200ecfa776996348200eed9a660d6348200ee79a69556348200cf78ba95563482009ef8cb6996348200cdf8ba9dd6348200cdf9ba9dd6348200bef0c16996348200bed8c36996348200cef8ba69963482008ff9caaed53482008ff8ca6e153482008ff8cbaa953482008ff9cbaa953482008ff8cb69d53482008ff8ca6dd5348200cbf8baa2153482009df8c76e95348200adf8c76e953482008ff8caaed53482008ff9c62e953482008ff9c82e95348200aef9c62e953482008ff9caaed6348200cf78ba9557348200ecf9a799973482009ff0c16e96348200cef9a6aed63482008ff8caaed63482008ff8cb6997348200cdf8ba61d73482009df8cb61d7348200cef8ba9997348200cef9ba9997348200aff0c169973482008ff8c56e96348200eaf9a6a216348200cbf8baa216348200cbf9baa2163482008ff8cb69d63482008ff9cb69d63482008ff8ca6dd6348200) else (if i<7 then 0xfe69855962258200afe8ca6162258200b7e8c96962258200bee9c62d62258200f6e8c95962258200eee8ba5962258200beeacc5962258200fbca888ce2258200fed2336056158200fe72556056158200fcf27760561582008ff8cb69d5158200fee2226056158200faf1826056158200faea888896158200bef1c10c96158200beb9c40c96158200feca338896158200fe6a558896158200fcea778896158200dcfa776d951582008ff9caaed3158200fe71655c55158200edf1a75c55158200dcfa776d931582008ff8cb69d31582009fe8c26dd3158200ded9b68cd5158200fc7a775955158200de7abb5955158200fe69658895158200dee9b68895158200fe59658cd5158200be79c50c96158200adf9ca5c97158200edd9a78cd7158200ed79a79557158200fa7a889556158200f8fa889dd6158200ede9a78897158200efc8a58ce2258200fdca778ce2258200efc9a78ce2258200cdf9a7aed7158200ff4a558ce2258200fec9658ce2258200fc7a7795561582009ef9cb0c96158200beb9c41496158200aef9ca1496158200bcf9c70c96158200baf9c80c96158200aef9ca0c96158200fcda778cd6158200fada888cd61582009ef9cb14d61582009ef9cb1496158200bcf8c75496158200fe5a558cd6158200cdf8ba9de33482008ff8cb69e3348200d3f8b9a223348200aff0c169a33482008ff8cb69a3348200d5f8b99de3348200c7faaa2e633482008ff8cbaaa33482008ff9c52ea3348200cbf8baa223348200c7f8b96a233482008ff8cb6a23348200cef8ba99a3348200afdacc2ea3348200d7d8b954e3348200afd8ca54e3348200afd9c72ea3348200afd8c82ea3348200afd9c82ea3348200d778b99563348200cf78ba9563348200d6f8b999a3348200eed9a658e3348200afd8ca58e3348200edd9a75ce33482008ff8cb68d5348200cf78ba95553482009f78cb61553482008ffacc6e853482009fd8cb60d5348200af78c568d53482008ff8cb69953482009bf8c86d953482008ff8ca6d95348200cef8ba9995348200aff0c16995348200cef9b669953482008ff9cbaa85348200dbea886c85348200cfeaaa6c853482009feacc6c853482008ff9c62ea33482008ff9c82ea3348200deea666c853482008ff9cb69853482008ff8ca6d85348200cbf9baa205348200cef9ba9985348200aff0c16985348200cef9b66985348200afd9c62ea3348200f5d8b99de3348200edd8ba9de3348200afd8ca61e3348200edd8a19de3348200f9da889de3348200edd8a89de3348200afd8cb69e3348200ebd8a1a223348200ebd8a5a223348200afd8c169e3348200ebda8869e3348200afd8c869e3348200bfd0c169a3348200afd9ca5da3348200afd9ca61a3348200efd0c169a3348200f6d8b999a3348200eedaaa99a3348200 else (if i<8 then 0xfde27788a1158200efe1a788a1158200fbe28888a1158200fee16388a1158200ff625588a1158200fee16588a1158200efd1a78ce1158200edf1a75c521582009df8c76d52158200fec9638893158200aff0c369e1158200fed1634c521582009ff0cb4c52158200dedabb58d3158200de79b695531582009ef9c66d53158200dee9b68893158200fe5a5558d3158200fcda7758d3158200f9f2889de1158200aff1ca14e1158200bef1c654e1158200fe725558e1158200fbd2888ce1158200fed1638ce1158200bef1c614e1158200fb72889561158200fe71659561158200fcf2775961158200fcf27758e1158200fd72779561158200ef71a79561158200aef8c2aaa664c2008ff8ca6e1624c200afb9c4aa9624c2008ff8cbaa9624c2008ff8cb69d624c2008ff8ca6dd624c2009fd8c36e1624c200afb9c4aa9724c200afb9c4aa8824c2008ffacc6e8824c2009ff0c16e9624c2008ff8caaed624c2008ff9caaed624c200cdf8ba9dd624c200cef8ba99a224c2008ff8cb69a224c20097f9c82e6224c200afe9c82ea224c200afe8ca58a224c200d6f8b999a224c2008ff8cb699324c20097f8c96d9324c20097f8c96e1324c200afb9c4aaa224c200d6f8b9999324c200afe8c2699324c200bfd1c12cd824c200eed9a799a334c200afd9ca5da334c200afd8c269a334c2008ff8cb6a1a24c2009fd9c3aeda24c200fcda7799a334c200ecfaaa9de664c200e6f8c969e664c200aefacc69e664c200afdacc69a334c200d5f8b99dd634c20097f8c96dd634c200afe8c26a1a24c200cef8ba999824c2008ff8cb699824c200afb9c4aa9824c200bf99c42cd824c200cfd9ba2cd824c200ded8b3999824c2008ff8caaed824c2008ff9caaed824c200afe8c2699a24c2008ff8cbaa9824c2009fd9c3aed824c20097f8c9aed824c200afe8ca60e2258200b7e8c968e2258200bee9c62ce2258200eee8ba58e2258200beeacc58e2258200afe8ca5ce2258200ef69a79562258200fb6a889562258200ef68ba9562258200afe9ca2ce2258200ef68a39562258200fd6a779562258200f6e8c958e2258200afe8ca8ce2258200bee9c614e2258200afe9ca14e2258200efc8ba8ce2258200efc8ca8ce2258200fec9638ce2258200fe6a5558e2258200fcea7758e2258200faea8858e2258200bee9c654e2258200afe8ca54e2258200fec98358e2258200ef68ca9562258200afe8c369e2258200ebea8869e2258200ebe8a3a222258200ede8a39de2258200f9ea889de2258200afe8ca61e2258200afe9c52ea2258200afe9c82ea2258200cfd8ba8ce2258200ebe8a5a222258200ebe8baa222258200afe9c32ea2258200afe9ca2d62258200fcea775962258200eee9a75962258200faea885962258200fe69659562258200afe8ca9562258200 else 0xdaf9b6a203258200cbf9baa203258200cbf8a56e03258200cef8a56d83258200cdf8a56dc3258200d9fa886dc3258200cbf8baa2173582008ff8ca6e173582008ff8caaed73582009ef8cb61d63582009ef9c5aed6358200cf78ba9557358200cdf8ba9dd83582009ef9c6aed83582008ff8caaed83582008ff9caaed7358200cf78ba95583582009ef8cb5958358200dcfabb9dd6358200fc7a779556358200fa7a889556358200f678b99556358200fe5a5560d6358200fcda7760d6358200bedacc60d63582009ef8cb6156358200f8fa889dd6358200f4f8b99dd6358200de7abb9556358200de78cb95563582009ef8cb9556358200d778b9955a358200be7acc6156558200f8fa889dd6558200dcfabb9dd6558200cbf8baa225558200fc7a776156558200fa79876156558200e9f8a3a2277582009ef9c6aed87582008ff8caaed87582009ef8cb61d65582009ef9c3aed65582008ff8caaed8558200af79c82ea5558200bd79c72ce5558200af79ca2ce5558200ed78a39de5558200d5f8b99dda358200af79ca2ca5558200be79c62ce5558200eb78baa225558200af79c22ea5558200af79c32ea5558200f97a889de5558200eb78a2a225558200eb78a3a225558200aef8ca5cd6358200afd8ca61e3358200afd8cb69e3358200ebd8a2a223358200afd9ca2d63358200f9da889de3358200edd8ba9de3358200afd9c52ea3358200afd9c72ea3358200afd9c82ea3358200ebd8a5a223358200ebd8baa223358200afd9c22ea3358200bed9c62d63358200afd8ca9563358200fe59855963358200fcda775963358200fb5a889563358200ef58ba9563358200ef58ca9563358200bedacc5963358200afd8ca6163358200b7d8c96963358200fada885963358200f6d8c95963358200bed8cb5963358200fcda7758e3358200cef8ba6d95358200cdf8ba9dd53582008ff8ca6dd5358200de79b66155358200dcfa776d95358200baf8c86d95358200abf8c86e953582008ff8caaed53582008ff9caaed5358200daf9b6a215358200cbf8baa2153582008ff8ca6e15358200cef8ba5955358200cdf8ba9de33582008ff8cb69e3358200cbf8baa223358200afd8ca5ce3358200cf78ba95633582009ef8cb59633582008ff8c26e85358200cef8ba58d5358200ded9b660d53582008ff8ca6c85358200daf9b6a205358200cbf9baa205358200bbf1c80ca1158200aff1ca0ca1158200bfb1c414a1158200bf71c50ca1158200bef1c60ca1158200bdf1c70ca1158200ff52558ce1158200fed1658ce1158200fdd2778ce1158200bef1c614a1158200aff1ca14a1158200bdf0c754a1158200bfb1c40ca11582008ff9c5aeda64c2008ff9c7aeda64c200ffc23388a1158200aef8c5aaa664c200afb9c4aa9764c2008ff9c2aeda64c200)))) else (if i<14 then (if i<11 then (if i<10 then 0xddd9b754c214c200ded9b68cc214c200cfd9ba8cc214c200df99b454c214c200dafa886d8214c2008ffacc6e8214c200ffc1624c5214c200ffc0c24c5214c2008ff8ca6e0214c200afb9c4aa8214c2008ff8c86e8214c200fbd2884c5214c200dfd1b84c5214c200f7d0c94c5214c200fed2664c5214c200efd1a64c5214c200fdd2774c5214c200cbf8a86e0214c200cdf8a86dc214c200cdfaaa6dc214c200dbb9b4a20214c200cef8a86d8214c200cefaaa6d8214c200d9fa886dc214c200cbf8ca6e0214c200cbf9ca6e0214c2009bfacc6e0214c200cbf9baa20214c2009bf9cba20214c200cbfaaa6e0214c200afe9c62ea224c200dcf8b758d5258200cef8ba5955258200cdf8ba9dd5258200ddd8b78cd5258200cfd8ba8cd52582009f78cb54d52582008ff8ca6dd5258200d9f8b7a215258200cbf8baa2152582009df8cb9dd5258200cdf8ba2dd5258200cdf9ba2dd52582008ff8c36e85258200cfd9ba8cc5258200deb9b458c5258200cef9ba58c52582008ff9caaed3258200df99b48cc5258200ded9b68cc5258200cef8a36d85258200daf9b6a205258200cbf9baa2052582009ef9cb58c52582008ff8ca6cc5258200dbba886d052582009df8c76e15258200aff0c16e982582009ef9c6aed82582008ff8caaed82582009ef8cb5958258200cdf8ba9dd82582008ff8cb69d8258200afd9ca2ca3358200ef58a29563358200fd5a7795633582008ff9caaed8258200d7d8b98cda258200d778b9955a258200cf78ba95582582009df9c7aed52582008ff8caaed52582008ff9caaed52582008ff8ca6e15258200aff0c16e95258200adf8c76e95258200fad98358d82582009ef8cb58d82582009bf8cb60d8258200cef9ba59572582008ff8ca6e17258200cfd8ba8cd82582008ff8caaed3258200dd79b79543258200db79b89543258200cf79ba9543258200cfb8a56d03258200dbba886d03258200de79b69543258200daf9b85943258200cef9ba59432582009ef9cb59432582009f79cb9543258200de79b55943258200dcf9b75943258200deb9656d03258200cbf8baa222258200df72556c43258200def1656c43258200cef8ba58e2258200cf78ba9562258200cef8ba5962258200cff1ca6c432582009ff2cc6c43258200df3a556d03258200cff0a56c43258200def1c66c43258200dbf2886c43258200de79c66d43258200cf78ba95532582009df8c76d532582008ff8ca6d532582009bfacc6e032582008ff8c56e83258200cef8ba58d3258200cbf8baa2132582008ff8ca6e13258200aff0c16e93258200cdf8ba9dd32582008ff8cb69d32582008ff8ca6dd3258200cbf9ca6e032582009f7acc6d43258200cf78a56d432582008ff8ca6d43258200db7a886d43258200cf78ca6d43258200cf79ca6d43258200 else 0xebf0baa22114c200ebf0caa22114c200b7f0c9a22114c200bfb1c4216114c200bfd0c360a114c200aff0ca60a114c200aff1ca2ca114c200aff0ca54a114c200aff0ca58a114c200aff1ca20a114c200fdd2778ce114c200efd1a78ce114c200fbd2888ce114c200ff52558ce114c200fed2668ce114c200efd1a68ce114c200bdf0c754a114c200efe0ca88a114c200b7f0c988a114c200aff0ca88a114c200efe0a888a114c200efe2aa88a114c200efe0ba88a114c200bef1c614a114c200aff1ca14a114c200ff515354a114c200b7f0c94ca114c200bfd1c314a114c200bfb1c414a114c200ff518554e114c200fe7266956114c200ef71a6956114c200ef72aa956114c200fdd2772ce114c200fbd2882ce114c200ef70a2956114c200aff0ca596114c200bfe1c2216114c200bfd1c3216114c200ef70ba956114c200bfd0c3956114c200aff0ca956114c200bfd1c52ce114c200fbd28854e114c200f7d0c954e114c200bfd0cb54e114c200fed26654e114c200fdd27754e114c200efd1a754e114c200b7f0c95ce114c200b7f0c960e114c200ff52552ce114c200bfd2cc54e114c200b7f0c954e114c200b7f0c958e114c200afb9c4aa9214c2008ff8cbaa9214c2008ff8caaed214c2009fd8c36e1214c2009ef8c66e1214c2008ff8ca6e1214c200ffc222605314c200fbd182605314c200dfd1b5605314c200b7d8c9545314c2009fd9cb545314c200afd8ca5c5314c200cbf8baa21214c2009df8c76d5214c20097f8c96d5214c2008ff8ca6d5214c200dfd0cb4c5214c200bfd2cc4c5214c20097f8c96cd214c200cdf8ba9dd214c2008ff8cb69d214c2008ff8ca6dd214c200cef8ba999214c2008ff8cb699214c2008ff8ca6d9214c200fed266605314c200fdca77889314c200fbca88889314c200f7c8b9889314c200dfc9b5889314c200feca66889314c200efc9a6889314c200b7d8c9889314c200afd8ca889314c200bfd1c1149314c200efc8ca889314c200dfcabb889314c200bfd0c1889314c200ffc0c1889314c200fdd277605314c200fbd288605314c200fbd0b8605314c200fbd186605314c200efd1a6605314c200fed0c6605314c200bfd0cb605314c200bfd2cc605314c200afd8ca605314c200f7d0b9605314c200efd0ca605314c200dfd2bb605314c200dfd2bb4c5214c200cfd8a86cc214c200cfdaaa6cc214c2009fdacc6cc214c200cfd9ba54c214c2009fd9cb54c214c200dbda886cc214c200cf7aaa6d4214c200cf79ca6d4214c2009f7acc6d4214c200df59c36d4214c200db7a886d4214c200cf78a86d4214c200dbd9b854c214c200cbf8baa22114c200afb9c4aaa114c200df59b58cc214c200cdf8ba9de114c2008ff8cb69e114c200dbd8b3a22114c200df59b554c214c200ded9b654c214c200) else (if i<12 then 0x8ff8cb689a14c200aff0c1695a14c200eee8ba99a224c200b7e8c9a22224c200afe8caa22224c200bde9c72e2224c200ebe8a1a22224c200ebeaaaa22224c200ebe8baa22224c200afe8c8aaa224c200afe9c12ea224c200afe9c52ea224c200afe9ca2e2224c200afe8c1aaa224c200afe8c5aaa224c200afe8c869e224c200ebea8869a224c200e7e8c969a224c200afe8cb69a224c200afe9ca5da224c200afe8c569a224c200edea7769a224c200edeaaa9de224c200afe8ca61e224c200afe8c169e224c200afeacc69a224c200ede8a19de224c200ede8a89de224c2008ff8cbaa9814c200dde9b7888814c200cfe9ba888814c200ddd9b78cc814c2008ff9caaed714c200dfc9b3888814c200dfa9b4888814c2009fdacc6cc814c200ddb9b49dc814c200cdf9ba9dc814c200cfd9ba8cc814c200ddda776cc814c200cfdaaa6cc814c2008ff8caaed714c200cef8ba999714c2008ff8cb699714c2009df8cb61d714c2008ff8ca6e1614c200afb9c4aa9614c200cfe8ba889714c200afb9c4aa9714c2008ff8cbaa9714c2009fe8c26e9714c200cbf8baa21714c2009ef8c66e1714c2008ff8ca6e1714c200cfb9b469c814c200cef9ba2d9814c200dcf8b69dd814c200cdf8ba9dd814c200cef8ba999814c2009ef8cb999814c200cef8ba2d9814c200cbf8baa21814c200afb9c4aa9814c200cef8b6aa9814c200cef8b669d814c2008ff8cb69d814c200b3f8c9a21814c200ded8b68cd814c200cdf8ca6dc814c200cdf9ca6dc814c2009dfacc6dc814c200cdf9b769c814c2008ff9cb69c814c200cdfaaa6dc814c200dee8b6889814c200cfe8ba889814c2009bf8cb609814c2008ff8ca6dc814c200afb9c4aa8814c2008ffacc6e8814c200aff0c569a114c200edf27769a114c200f9f2889de114c200eef2aa99a114c200aff1ca5da114c200aff0c269a114c200aff0ca61e114c200ebf28869e114c200aff0c869e114c200edf0a89de114c200edf2aa9de114c200edf0ba9de114c200faf28899a114c2009ff1cb216114c200aff0ca616114c200bfd1c32d6114c200bef1c6216114c200bdf1c7216114c200aff1ca216114c200eef0a599a114c200fcf27799a114c200eef1a799a114c200bef1c62d6114c200aff1ca2d6114c200eef0a299a114c200e7f0c969e114c200aff1c72ea114c200aff1c82ea114c200aff0ca5c6114c200aff0c8aaa114c200aff1c22ea114c200aff1c52ea114c2009fd8cb8ce114c2009fd8cb54e114c200ddd8b39de114c200aff0ca606114c200dfc8b388a114c200cfe8ba88a114c200aff0c5aaa114c200ebf0a5a22114c200ebf1a6a22114c200ebf2aaa22114c200aff0cb69e114c200aff2cc69e114c200ebf0a2a22114c200aff0caa22114c200aff1ca2e2114c200aff0c2aaa114c200 else (if i<13 then 0xaef9c620da244200adf9c720da2442009fe8c26dd314c20097f8c96dd314c200d3f8b9a21314c200d5f8b99dd314c200aff0c169d314c2008ff8cb69d314c200dfc9b3888514c200cfe9ba888514c200cfd9ba8cc514c2009ef8c66e1314c20097f8c96e1314c20097f9c82e5314c20097f8c96d9314c200b7d9c82e5314c2009fd9c5aed314c200d7d8b9aed314c200bdd9c72e1314c200bed8c66e1314c200b7d8c96e1314c2009fd8cb60d314c20097f8c96d5314c200d6f8b9999314c200d7e8b9889314c2009fd8cb4c9314c2009fd8cb54d314c200d7d8c96cc514c20097f9c22e5514c200d7d9c32e5514c200c7faaa2e5514c2008ff8cb699514c20097f8c96d9514c2008ff8ca6d9514c2009fd8c3aed514c2008ff8caaed514c2008ff8ca6dd614c20097facc2e5514c200afb9c4aa9514c2008ff8cbaa9514c200cef8ba999514c200afb9c4aa8514c200c7f8c96e8514c2008ffacc6e8514c200cfdaaa6cc514c2009fdacc6cc514c20097f8c96cc514c200d7d8b98cd514c200d7d8b96cd514c200d6f8b9999514c2009ff0cb605514c200d7e8b9889514c200cfe8ba889514c200bf99c42e1314c200afd9ca2c9314c200b7d8c96c9314c200bfd0c1695314c200bed9c62c9314c200bdd9c72c9314c200bbd9c82c9314c200d7d8c96d5314c2009fdacc6d5314c200d7d8b96d5314c200b7d8c9695314c2009fd8cb695314c200deda666d5314c200bf59c52c9314c2009fd9cb149314c200bdd8c7549314c200bfd1c1209314c200bf99c4149314c200bed9c6149314c200afd9ca149314c200b7d8c9689314c2009fd8cb689314c200bf99c42c9314c200afd9ca209314c2009fd8cb609314c200bfd0c1689314c200b7d8c96d5314c200fbd0c1a21314c200ebd9a6a21314c200f3d8b9a21314c2009fd8cb69d314c200bfc8c26dd314c200b7d8c96dd314c200bfd0c16a1314c200b7d8c96a1314c2009fd8cb6a1314c200dbdabba21314c200bfd0c1a21314c200b7d8c9a21314c200b7d8c969d314c200dedabb999314c200edda77699314c200cfdabb699314c200fcda77999314c200fada88999314c200f6d8b9999314c200f5d8b99dd314c200dddabb9dd314c200bfd0c169d314c200b7d8c9699314c200b7d8c96d9314c200f9da889dd314c200b7e8c958e224c200b7e8c960e224c200bfc9c32d6224c2008ff8cb6a1a14c200bfc9c32c6224c200afe9ca2c6224c200eee9a799a224c200faea8899a224c200eeeaaa99a224c200afe9ca2d6224c200eee8a599a224c200fcea7799a224c200cbf8b86a1a14c2008ff8caaed814c2008ff9caaed814c200aff0c1689a14c2009ef8c66e9814c200aef8c66e9814c2009ef9c6aed814c2008ff8cb695a14c200aff0c169da14c200aff0c16a1a14c200cfe8b2689a14c200 else 0xcfd9b368c5244200cfb9b468c52442009fe8cb6095244200cdf9ba2dd52442008ff8ca6dd52442008ff9ca6dd5244200cdf9ba9dd52442009df8cb9dd5244200cdf8ba2dd5244200aef8c66a15244200cdf8b76a152442008ff8cb6a15244200d9f8b7a215244200cbf8baa215244200af78c56a15244200cdf8ba9dd52442009f78cb54d5244200afe8c268d5244200cdf8b768d5244200ddd8b78cd5244200cfd8ba8cd5244200cfd9ba8cd5244200cdf8b769952442008ff9cb69952442009df8c76d952442008ff8cb68d5244200dcf8b79995244200cef9ba99952442008ff8cb61da244200cbf8b3a21a244200cbf8b5a21a244200e9fa889dda244200cdf8b89dda244200cdfabb9dda244200cbf8cba21a2442008ff8cba21a244200aef8c66e1a244200cbf9b6a21a244200e3f8b9a21a244200cbfabba21a244200cdf8b39dda2442008ff9cb215a2442008ff8cb615a244200adf8c76d5a244200afb9c4215a244200aef9c6215a244200adf9c7215a244200ecfa77999a244200eafa88999a244200cefabb999a244200a7f8c96d5a244200cef8b3999a244200cef8b5999a244200a7f8c96e1a244200bfd0c19563344200afd8ca9563344200afd9ca5963344200ef5aaa9563344200ef58ba9563344200ef58ca9563344200bed9c62163344200bdd9c72163344200afd9ca2163344200bfd1c12163344200bfc9c22163344200bf99c42163344200ef59a89563344200afd9ca2ca3344200ff50c19563344200ef58a295633442008ff8c3aeda2442008ff8c5aeda2442008ff8c8aeda244200ef59a79563344200fb5a889563344200ef58a89563344200fe5a669563344200ef59a69563344200fd5a779563344200eeda668cda244200edda778cda244200ebda888cda2442008ff9caaed8244200ef5a558cda244200cfd8b58cda244200cfd8cb8cda2442008ff8cb8cda244200aff1c114da244200cfd8b88cda244200e7d8b98cda244200cfdabb8cda2442008ff8caaed82442008ff8cb6a182442008ff8cbaa982442008ff8c36e98244200cbf8baa218244200cbf9baa218244200afe8c26a18244200c7f8c96e982442008ffacc6e98244200aef8c66e982442008ff8c56e98244200cef8c66e982442008ff9c66e982442008ff9cb14da244200cf78b8955a244200e778b9955a244200cf7abb955a244200ee7a66955a244200ed7a77955a244200eb7a88955a244200aff1c1215a244200afe9c2215a244200afd9c3215a244200cf78cb955a2442008ff8cb955a2442008ff8cb595a244200cf78b3955a244200aff1c120da244200afe9c220da244200afb9c420da2442008ff8cb54da2442008ff8cb58da2442008ff8cb5cda2442008ff9cb20da2442008ff8cb60da244200a7f8c96cda244200af79c520da244200))) else (if i<16 then (if i<15 then 0xcef8c66e983442008ff9c66e983442008ff9cb6a173442008ff8ca6e173442008ff8cbaa97344200cbf9baa217344200aef8c66a173442008ff8cb6a173442008ff9caaed7344200cff0a26c48344200df72556c483442008ff8c86e973442009fe8c26e973442008ff8caaed7344200cbf8baa2173442008ff9cb69d63442008ff8cb6a163442008ff8c26e963442008ff8cb6956344200cdf9ba9dd63442008ff8cb69d6344200cf79ba9557344200cef9ba99973442009df8cb61d73442008ff8c56e963442008ff9caaed6344200cf78ba9557344200ddf2776c48344200cfbaaa6d08344200de79b69548344200dd79b79548344200df3a556d08344200ddba776d08344200cfb9a76d08344200cf78a26d48344200dd7a776d48344200cf79a76d48344200cf79ba95483442009f79cb9548344200df71c16d48344200cfb8a26d08344200df6a556c88344200ddea776c88344200cfe9a76c88344200cff1a76c48344200cff2aa6c483442009ff2cc6c483442009feacc6c88344200cfe8a26c883442008ff8ca6c88344200cfeaaa6c88344200cfe8ca6c88344200cfe9ca6c883442009fd9cb2163344200ded8b358d62442009ef8cb58d62442008ff8cb68d62442008ff8caaed52442008ff9caaed5244200cfd9ba8cd6244200cdf9ba9dd62442008ff8cb6a162442008ff8c36e96244200cf79ba95562442009ef8cb59562442008ff8cb69562442009df9c7aed5244200cdf8b7aa952442008ff8cbaa952442008ff8c36e952442008ff9cb6a152442009df8c76e152442008ff8ca6e152442008ffacc6e952442009df8c76e95244200adf8c76e95244200cdf8c76e952442008ff8c86e95244200c7f8c96e952442008ff8c56e962442009bf8cb60d82442008ff8cb68d8244200cf78ba95582442008ff9cb6948244200cfd8ba8cd8244200cfd9ba8cd8244200cdf8ba9dd8244200cdf9ba9dd82442008ff8cb69d8244200cf79ba95582442008ff8cb6958244200cef9ba9998244200cf79ba95482442008ff9cb6997244200cbf9baa217244200aef8c66a17244200cfd9ba8cd7244200cf79ba9557244200cef9ba99972442008ff8c86e97244200cfd9ba8cc82442008ff9cb68c82442008ff9cb6a172442008ff8ca6e172442008ff8c36e97244200cef9b669852442008ff9cb6985244200dafa886d85244200dbba886d05244200cfb9a86d05244200cef9ba9985244200aef8c66a05244200cbf9b86a052442008ff9cb6a05244200cef9a86d852442009efacc6d85244200cbf9baa205244200cfb9a66d05244200cff1a86c45244200df99b48cc5244200ded9b68cc5244200cff1a36c45244200def2666c45244200dbf2886c45244200cef9b668c52442008ff9cb68c5244200deba666d05244200cfd9ba8cc5244200 else 0xef5a5568e3344200afd8c568e3344200cef9ba99853442008ff8cb6a153442008ff8ca6e153442008ff8cbaa953442008ff8ca6dd5344200cbf8baa215344200aef8c66a153442008ff8caaed53442008ff9caaed5344200cf79ba95563442008ff8c26e95344200c7f8c96e953442008ffacc6e953442008ff8cb69d53442008ff9cb6a053442009fd8cb60d5344200af78c568d53442008ff9cb6985344200cbf9baa205344200aef8c66a053442008ff9cb69953442009bf8c86d95344200cdf8ba9dd53442008ff8cb68d53442009f78cb6155344200cef9ba9995344200f9da889de3344200edd8a89de3344200edd9a89de3344200afd9ca61a3344200edda7769a3344200ebda8869a3344200afd9ca61e3344200ebda8869e3344200afd8c869e3344200eddaaa9de3344200edd8ba9de3344200afd8ca61e3344200afd9ca5da3344200e7d8c96963344200afd8cb6963344200afdacc6963344200afd8ca6163344200afd8c26963344200eeda666963344200eed9a799a3344200fada8899a3344200eed9a899a3344200bfd1c12d63344200afd9ca2d63344200fcda7799a3344200e7d8c969e3344200afd8c2aaa3344200afd8c5aaa3344200afd8c8aaa3344200afd8cb6a23344200afdacc6a23344200afd9ca2e23344200afd9c72ea3344200afd9c82ea3344200afd8ca54e3344200afd8cbaaa3344200afd9c22ea3344200afd9c52ea3344200e7d8c96a23344200ebd8a5a223344200ebdaaaa223344200ebd8baa223344200afd8cb69e3344200afdacc69e3344200ebd8a2a223344200afd8c26a23344200afd8c56a23344200eed8c66a23344200ebd8caa223344200ebd9a8a223344200afd8caa2233442008ff8c26e883442008ffacc6e88344200abf8c868d8344200cdf9ca6dc83442009dfacc6dc83442008ff8ca6dc8344200cef9ba9998344200cdf8ba9dd8344200cdf9ba9dd83442008ff8cb68d8344200cf78ba9558344200cf79ba9558344200cdf8ca6dc8344200cef8a26d88344200dcfa776d88344200cef9a76d88344200cf7aaa6d48344200cf79ca6d483442009f7acc6d483442008ff9cb69c8344200cdf8a26dc8344200cdfaaa6dc8344200cefaaa6d88344200cdf9ba9dc8344200cdf9b769c83442008ff8cb69d8344200cf78b2955a344200ee7a66955a344200ed7a77955a3442008ff9caaed8344200cfe9b22c9a344200a7f8c96c9a344200cf7abb955a344200cf78cb955a3442008ff8cb955a344200eb7a88955a344200cf78b8955a344200e778b9955a3442008ff8caaed83442008ff8cb6a183442008ff8cbaa983442008ff8c26e98344200cbf8baa218344200cbf9baa218344200afd8c36a18344200c7f8c96e983442008ffacc6e98344200aef8c66e983442008ff8c56e98344200) else (if i<17 then 0xaff2cc69e1144200d7f0b95452144200d7d8b98cd2144200d7d8b98cd5144200c7f8b968d5144200d5f8b99dd5144200b7f0c96e15144200b7f1c22e55144200d7e8b9889514420097f9c22e55144200d7d8b98cd7144200d778b9955714420097f8c96dd5144200d3f8b9a21514420097f8c96e15144200bef0c66e15144200ebf1a8a215144200aff0caa215144200ef70c56a15144200ebf2aaa215144200ebf0caa215144200dbf2bba215144200cff0cb6a15144200aff2cc6a15144200b7f0c96a15144200eef0c66a15144200e7f0c96a15144200cff2bb6a15144200d3f8b9a217144200fdca778ce2244200efc9a78ce2244200fbca888ce2244200efc9a58ce2244200feca668ce2244200efc9a68ce2244200efcaaa8ce2244200efc8ba8ce2244200efc8ca8ce2244200efc8a88ce2244200efc9a88ce2244200f7c8b98ce2244200efc8a58ce2244200abf8c868d81442008ff8cb68d8144200d778b9955814420097f8c96e17144200d7e8b98898144200d7d8b98cd81442008ff9cb69d81442009ef9c6aed8144200ff4a558ce2244200d5f8b99dd8144200abf8c869d81442008ff8cb69d8144200bef1c620d5144200bdf1c720d5144200aff1ca20d5144200bfe1c220d5144200bfb1c420d5144200bf71c520d5144200fb72889555144200ef71a89555144200fe717659551442009ff1cb20d5144200b7f0c96cd5144200fe72669555144200dfd2bb8cd5144200ff52558cd5144200ff51658cd5144200fed2668cd5144200aff1ca2095144200bdf0c76c95144200b7f0c96c95144200efd1a88cd5144200f7d0b98cd5144200efd2aa8cd5144200fdd2778cd5144200efd1a78cd5144200fbd2888cd5144200fe71865955144200f5f0b99dd5144200edf2aa9dd5144200ddf2bb9dd5144200b7f0c96d95144200f9f2889dd5144200edf1a89dd5144200b7f0c969d5144200b7f0c96dd5144200f3f0b9a215144200aff1ca61d5144200ebf28869d5144200cff2bb69d5144200def2bb9995144200ef71a85955144200f770b95955144200df72bb5955144200fd72775955144200ef71a75955144200fb72885955144200faf2889995144200eef1a89995144200f6f0b99995144200bf72cc5955144200fcf2779995144200eef1a79995144200cdf8ba9de33442008ff8cb69e3344200cbf8baa223344200e7d8c968e3344200cf78ba95633442008ff8cb6963344200def2666c45344200dbf2886c45344200cff1a86c45344200aef8c66a233442008ff8cb6a233442008ff8cbaaa3344200afd8c868e3344200afd9ca5ce3344200afd8ca60e3344200afd9ca60e3344200afd9ca54e3344200afd9ca58e3344200afd8ca5ce3344200eeda6668e3344200edda7768e3344200ebda8868e3344200afd8c268e3344200 else (if i<18 then 0xefca3368a2244200eeea6668a2244200cff1a66c43244200cbf9b869432442008ff9cb6943244200df71c16d43244200cf79b56943244200cef9b66943244200cdf9b76943244200cf79a86d43244200cf79ca6d432442009f7acc6d43244200de7a666d43244200cf79a66d43244200db7a886d432442009f79cb9543244200cfb9a56d03244200deba666d03244200cfb9a66d03244200dbf2886c43244200cff1a86c43244200df3a556d03244200dd79b79543244200db79b89543244200cf79ba9543244200dbba886d03244200cfb9a86d03244200de79b69543244200efc9a38ce2244200fde2778895144200efe1a78895144200fbe2888895144200ff61658895144200ff60c58895144200fee2668895144200efe2aa8895144200dfe2bb8895144200ff61528895144200efe1a88895144200f7e0b98895144200f7e0c98895144200ff625588951442008ff9cb69d31442009fe8c26dd314420097f8c96dd3144200d5f8b99dd3144200afd8c369d31442008ff8cb69d31442008ff9cb6a1314420097f8c96e13144200ffc2338895144200d3f8b9a213144200afd8c36a131442008ff8cb6a13144200bf70c58895144200fb72885495144200ef71a85495144200f770b95495144200fd72775495144200ef71a75495144200fd70c75495144200bf72cc5495144200fe71655895144200bf71c52095144200ef72aa5495144200ef70ca5495144200df72bb5495144200bf71c65495144200bef1c60c95144200bdf1c70c95144200bbf1c80c95144200b7f0c98895144200bfb1c40c95144200bf71c50c95144200ff61825495144200ff52335495144200fe72665495144200aff1ca0c951442009ff1cb0c95144200ff61725495144200fdd2778ce1144200efd1a78ce1144200fbd2888ce1144200efd23368a1144200edf27768a1144200ebf28868a1144200bfe1c220e1144200bfb1c420e1144200bdf1c720e1144200efd1a88ce1144200efd1a38ce1144200aff1ca5ce1144200aff1ca60a1144200efe1a588a1144200fde27788a1144200efe1a788a1144200ffc23388a1144200efe1a388a1144200ff625588a1144200bdf0c754a1144200aff1ca54a1144200aff1ca5ca1144200fbe28888a1144200efe1a888a1144200aff1ca4ca1144200aff1ca20e11442008ff9cb6a1214420097f8c96e12144200d7f0b954531442009df8c76d5214420097f8c96d52144200d3f8b9a212144200d778b995531442008ff9cb695314420097f8c96d531442009ff0cb6053144200d7e8b98893144200d7d8b98cd31442008ff9cb6952144200e7f0c968e1144200aff2cc68e1144200aff0c369e1144200aff1ca60e1144200edf27768e1144200aff0c868e11442008ff9cb68d214420097f8c96cd2144200d778b99552144200 else 0xebe8a3a222244200ebe8a5a222244200f3e8b9a222244200afe9ca60e2244200ef6a5568e2244200afe8c568e2244200afe9ca20e22442009fe9cb20e2244200afe8ca60e2244200afe8c868e2244200e7e8b968e2244200e7e8c968e2244200eeea6668e2244200edea7768e2244200ebea8868e2244200bde9c720e2244200afe8ca54e2244200afe9ca54e2244200afe9ca58e2244200afe8ca8ce2244200bfe1c114e2244200afe9ca14e2244200bfa9c420e2244200bf69c520e2244200bee9c620e2244200afe8ca5ce2244200afe9ca5ce2244200bfe1c120e2244200afe8cb68e2244200afe8ca9562244200afe9ca5962244200afe9ca5d62244200ef68ba9562244200ef68ca9562244200bfe0c19562244200bee9c62162244200bde9c72162244200afe9ca2162244200bfe1c12162244200bfc9c32162244200bfa9c42162244200ef6aaa9562244200ef68a39562244200fe6a669562244200ef69a69562244200afeacc68e2244200afe9ca2ce2244200ff60c19562244200ef68a89562244200ef69a89562244200f768b99562244200fd6a779562244200ef69a79562244200fb6a8895622442008ff9cb6a03244200cbf9ca6e032442009bfacc6e032442009bf9cba203244200aef8c66a03244200cbf9b86a03244200afe8c268d32442008ff8cb68d3244200cf78ba95532442009fe8cb6093244200cfd8ba8cd3244200cfd9ba8cd3244200cbf9baa203244200cef9b66983244200cdf9b76983244200cbf9b86983244200dcf9b79983244200daf9b89983244200cef9ba99832442009efacc6d83244200d9fa886dc3244200cdf9a86dc32442008ff9cb6983244200dafa886d83244200cef9a86d83244200cf79ba95532442008ff8ca6e132442008ff8cbaa932442008ff8c56e93244200aef8c66a132442008ff8cb6a132442008ff9cb6a132442008ff8caaed32442008ff9caaed3244200dfd2336c452442008ff8c86e93244200c7f8c96e932442008ffacc6e93244200cbf9baa2132442008ff8ca6d53244200cef9ba99932442008ff9cb69932442008ff8cb69532442008ff9cb69532442009df8c76d532442008ff8ca6dd32442008ff9ca6dd3244200cbf8baa213244200cdf8ba9dd3244200cdf9ba9dd32442008ff8cb69d32442008ff8cb6962244200d6f8b999a2244200d3f8b9a2222442008ff8cb68e2244200d778b99562244200cf78ba9562244200df72556c43244200cff1a56c43244200def2666c43244200cbf8baa222244200aef8c66a222442008ff8cb6a22244200c7f8b968e2244200afe9ca4ca2244200d7e8b954a2244200afe9ca58a2244200afe9c32ea2244200afe9c52ea2244200afe9c82ea2244200ebea8868a2244200d7d8b98ce2244200cfd8ba8ce2244200afe9ca60a2244200))))) else (if i<28 then (if i<23 then (if i<21 then (if i<20 then 0x97f8c9aed31482008ff8caaed31482008ff9caaed3148200fd6a7754951482008ff8ca6d95148200cdf8ba9dd51482008ff8cb69d5148200cef8ba99951482008ff8cb6995148200cef9a66d951482009ef8c66e151482008ff8ca6e15148200af78c5aa951482008ff8ca6dd5148200cbf8baa2151482008ff8cb6a15148200ee79a65955148200fb6a885495148200f768c95495148200ef6aaa5495148200ef69a75495148200df69b75495148200fd68c75495148200b778c95495148200cfd8ba8cd51482008ff8cb68d5148200df6abb5495148200df68cb5495148200bf6acc54951482009ff0cb6053148200b7d8c94c93148200df69b55493148200efd1a36053148200ebf1a86053148200cff0ba6053148200eed9a658d3148200afd9ca58d3148200efd0c168d3148200cfe8ba5493148200b7d8c98cd3148200cfd8ba8cd31482008ff9cb6a03148200ddea776c83148200dbea886c83148200cfe9a86c83148200df69b554831482009fe9cb5483148200df6a556c831482008ff9cb69c3148200cbf9baa203148200cbf9b86a03148200cf79ba9543148200cdf9ba9dc3148200cdf9b769c3148200ef5a5568d3148200cdf8ba9dd3148200cdf9b769d31482008ff8cb69d31482008ff8cb6993148200cef9a66d931482008ff8ca6d931482009ef8c66e131482008ff8ca6e13148200afd8c3aa931482008ff8ca6dd3148200cbf8baa2131482008ff8cb6a13148200cef8ba9993148200e7d8c968d3148200cfdabb68d3148200afd8cb68d3148200eeda6668d3148200edda7768d3148200ebda8868d31482008ff8cb68d3148200cf78ba95531482008ff8ca6d53148200cfd8cb68d3148200afdacc68d3148200aff0c168d3148200eee9a899a2244200f6e8b999a2244200afe9ca5da2244200fcea7799a2244200eee9a799a2244200faea8899a2244200ede8a39de2244200f9ea889de2244200ede8a89de2244200afe9ca61a2244200edea7769a2244200ebea8869a2244200afe9ca2d62244200afe8c36962244200eeea666962244200edea7769622442009fe9cb2162244200afe8ca6162244200afe9ca6162244200afe8cb6962244200afeacc6962244200bfe1c12d62244200ebea886962244200afe8c86962244200e7e8c96962244200ede9a89de2244200eee8c66a22244200e7e8c96a22244200afe8cb6a22244200afe8caa222244200afe8c36a22244200afe8c56a22244200afe8c3aaa2244200afe8c5aaa2244200afe8c8aaa2244200afeacc6a22244200bde9c72e22244200afe9ca2e22244200ebe9a8a222244200afe8c369e2244200ebea8869e2244200afe8c869e2244200edeaaa9de2244200afe8ca61e2244200afe9ca61e2244200ebeaaaa222244200ebe8baa222244200ebe8caa222244200 else 0xcbf9b868ca148200df5a556cca148200cfd9a56cca1482008ff8cbaa95148200dbea886d52148200d7e8c96d521482009feacc6d52148200deea666d52148200ddea776d52148200dde8c76d52148200fcea779992148200faea889992148200deeabb9992148200bde8c76d52148200d7e8b96d52148200b7e8c96d52148200b7e8c96952148200eee9a65952148200bfe1c12152148200bfc9c32152148200df6abb9552148200df68cb95521482009fe8cb9552148200afe9ca21521482009fe9cb2152148200bde8c76952148200bfa9c42152148200bee9c62152148200bde9c72152148200edea77699214820097f8c96cd2148200ef70a19552148200d778b99552148200d7e8b95492148200efd0a18cd2148200d7d8b98cd2148200cff0a16e121482009ef8c66e1214820097f8c96e1214820097f8c96d52148200ebf0a1a212148200d3f8b9a212148200efe0a15492148200ebe9a6a212148200f3e8b9a212148200dbeabba212148200cfeabb6992148200f9ea889dd2148200ddeabb9dd2148200ffc1324c52148200efd1a34c52148200efe0a14c92148200b7e8c96a12148200bee8c66e12148200b7e8c96e12148200efe1a32852148200bfe1c32852148200ff62552852148200dfe2bb5c52148200bfe2cc5c52148200ffc2332852148200ff4a558cd2148200dfc9b58cd2148200feca668cd2148200efe1a52852148200fbe2882852148200ffc0c18cd2148200fbe2885c521482009fe9cb5452148200ffc2335c52148200ff62555c52148200efe0ca4c52148200dfe2bb4c52148200bfe2cc4c52148200efe1a65c52148200fde1875c52148200fde1a75c52148200dfe1b55c52148200fee2665c52148200fde1765c52148200efc9a68cd2148200afe9ca20d21482009fe9cb20d2148200b7e8c968d2148200bf69c520d2148200bee9c620d2148200bde9c720d2148200fd6a779552148200fb6a889552148200f768b99552148200b7e8c96cd2148200fe6a669552148200ef69a69552148200bfa9c420d2148200f7c8c98cd2148200dfcabb8cd2148200bfe0c18cd2148200fdca778cd2148200fbca888cd2148200f7c8b98cd2148200eee9a658d21482009fe8cb5cd2148200bfe1c120d2148200b7e8c98cd2148200bfe1c114d21482009fe9cb14d21482008ff9cb6a05148200ff61525c55148200ff61526055148200cfd9b368c51482008ff9cb68c5148200cbf9baa205148200ff60c15495148200ff4a335495148200fe6a665495148200ebf1a86055148200cff0ba60551482009ff0cb6055148200cfd9ba8cc51482008ff9c82e93148200aef9c62e93148200adf9c72e931482008ff8cbaa931482008ff9c52e931482008ff9c62e93148200dfca336c85148200dbea886c85148200cfe9a86c85148200) else (if i<22 then 0x8ff8caaed5148200eef1a66056148200ebf1a860561482008ff8cb6a17148200cfd9ba8cc8148200cfd9b368c8148200cfb9b468c8148200ddea776c88148200df99b48cc8148200ddd9b78cc8148200ddba776d08148200cfb9a76d08148200dd79b79548148200cdf9b768c81482008ff9cb68c8148200df3a556d08148200df6a556c881482008ff9c52e971482008ff9c82e97148200dfa9b454881482009ef8c66e171482008ff8ca6e171482008ff9c32e971482009fe9cb5488148200dfca336c88148200cfe9a36c88148200df69b55488148200dde9b75488148200cfe9ba5488148200feca668ce2248200efc9a68ce2248200fbca888ce2248200efc8a18ce2248200ff4a558ce2248200efc8a58ce2248200b7e8c98ce2248200afe8ca8ce2248200afe9ca14e2248200efc8a88ce2248200f7c8c98ce2248200efc8ca8ce2248200adf8c7695a1482009fe9c26d4a1482008ff9ca6d4a148200dafa886d8a148200db7a886d4a148200cf79a86d4a1482009f7acc6d4a1482009bf9cba20a1482009bfacc6e0a1482008ff9ca6e0a148200cef9a86d8a148200d9fa886dca148200cdf9a86dca148200afe8ca54e2248200afeacc69a2248200ebe8a1a222248200ebe8a3a222248200efe0c169a2248200afe8c369a2248200ebea8869a2248200afe8c36a22248200e7e8c96a22248200afeacc6a22248200ebe8caa222248200ebe9a8a222248200afe8caa222248200afe9ca61a2248200bfa9c420e2248200bf69c520e2248200bee9c620e2248200eee9a658e2248200afe8ca58e2248200bfe1c120e2248200eee8a399a2248200faea8899a2248200eee9a899a2248200bde9c720e2248200afe9ca20e2248200afe8ca60e2248200dfc9b3548a148200dfa9b4548a148200df69b5548a148200efd233684a148200ef7255684a148200ebf288684a148200df99b48cca148200df59b58cca148200ded9b68cca148200dee9b6548a148200dde9b7548a148200dbe9b8548a148200efe152684a1482008ff8cbaa981482008ff9c32e981482008ff9c52e98148200aff1c1aa98148200cef8b6aa98148200abf8c8aa981482009ef9c6aed81482008ff8caaed81482008ff9caaed81482009ef8c66e98148200aef8c66e98148200cff0a1aed8148200ddd9b78cca148200cfb9a86d0a148200de79b6954a148200dd79b7954a148200df3a556d0a148200cfb9a56d0a148200dbba886d0a148200cdf9b7694a148200cbf9b8694a148200df69c26d4a148200db79b8954a1482009f79cb954a148200cef9b6694a1482008ff9ca6cca148200cf79b568ca148200cef9b668ca148200cdf9b768ca148200dbd9b88cca1482009fd9cb8cca148200cfb9b468ca148200dbda886cca148200cfd9a86cca1482009fdacc6cca148200 else 0x8ff8cbaaa8844200abf9c32ea8844200abf9c52ea8844200abf9c72ea8844200a7f8c96c9a544200c7f8b96cda544200a7f8c96cda544200aef8c66e985442008ff8caaed8544200adf8c76c9a544200e6f8b9999a544200cefabb999a544200a7f8c96d9a544200cef8b2999a544200cef8b3999a544200ecfa77999a5442008ff8cbaa985442008ff9cb6997544200aef8c66a175442008ff8ca6e175442008ff8c26e965442008ff8c36e965442008ff9caaed65442009fdacc6cc8544200cdf8ba9dd85442008ff8cb69d8544200cfe9ca6c885442009feacc6c88544200cfd9ca6cc85442008ff8c2aeda5442008ff8c36e986442008ff8c56e98644200e9fa889dda644200cdf9ba9dd86442008ff9cb69d86442008ff8c26e98644200e9f9a8a227744200adf8caa227744200adf8c36a27744200e9f8a3a227744200e9faaaa227744200e9f8caa2277442008ff8c36e97644200aef9ca61e6644200aef8c369e6644200eafa8869e66442008ff8c3aeda544200f8fa889de6644200ecf9a89de6644200aef8c56a26644200cef8cb6a26644200aefacc6a26644200aefacc69e6644200aef8c26a26644200aef8c36a26644200b3f8c96098148200efd0a18cd8148200ded8b68cd8148200dee8b65498148200ebe9a85498148200ebf0a16098148200cef8b668d81482008ff8cb68d8148200ef70a19558148200ebd9a88cd8148200cfd8ba8cd8148200aff0c168d8148200ebe9a888981482008ff9cb69c81482009dfacc6dc8148200bfd1c32858148200cf79ba9548148200cdf9ba9dc8148200cdf9b769c8148200cff1ba2858148200efe0a18898148200dee8b68898148200bf71c52858148200bef1c62858148200ebf1a82858148200de78b69558148200cbf8baa218148200ebf0c16a18148200e3f8c96a18148200cef8b669d81482008ff8cb69d8148200ebf0a1a218148200abfacc6a18148200aff0c16a181482008ff8cb6a18148200cbfabb6a18148200abf8cb6a18148200cbf8cb6a18148200aff0c169d81482009ef8cb9998148200abf9ca6198148200eaf9a82d98148200cf78ba9558148200eaf9a89998148200cef8ba9998148200dcf8b69dd8148200e9f9a89dd8148200cdf8ba9dd8148200cef8ba2d98148200cef9ba2d98148200edf0a19dd8148200cfd8ba8cd71482008ff8cb68d7148200cf78ba9557148200eaf9a6a2161482008ff8ca6e16148200edd9a78cd7148200e9fa8869d7148200cbf8baa217148200adf9c76a17148200ecf9a79997148200cdf8ba61d71482009df8cb61d7148200ecfa7769961482009df8c76e95148200adf8c76e951482009fe8c2aed51482008ff9c32e951482008ff9c62e951482008ff9c82e95148200eee9a68896148200eed9a68cd6148200ee79a69556148200)) else (if i<25 then (if i<24 then 0xed7a7769a5544200ee79a799a5544200fa7a8899a5544200ee79a899a5544200eb7aaaa225544200af79c82ea5544200dbf0b1a225544200cbf8baa225544200af78c8aaa5544200af79c22ea5544200af79c32ea5544200cdf9ba9dd65442008ff8cb69d65442008ff8cb6a16544200cff0b16a25544200aef8c66a255442008ff8cb6a25544200af78c3aaa5544200af78caa225544200af78c26a25544200af78c36a25544200eb78baa225544200eb78caa225544200eb79a8a225544200af7acc6a25544200af79ca2e25544200af78c2aaa5544200ee78c66a25544200e778c96a25544200af78cb6a25544200cefabb999a344200a7f8c96d9a344200e9fa889dda344200ecfa77999a344200eafa88999a344200e6f8b9999a3442008ff8cb61da344200afe8c26dda344200a7f8c96dda344200cdf8b89dda344200e5f8b99dda344200cdfabb9dda344200cef8b5999a344200afd9c3215a344200afb9c4215a344200aef9c6215a3442008ff8cb595a344200aff1c1215a344200afe9c2215a344200cf79b52d5a344200a7f8c96d5a344200cef8b2999a344200adf9c7215a3442008ff9cb215a3442008ff8cb615a344200cbf8b2a21a3442008ff9c7aeda3442008ff8c8aeda3442008ff9c8aeda3442008ff8c5aeda3442008ff9c5aeda3442008ff9c6aeda344200cbf8b86a1a3442008ff8cb6a1a3442009fb9c4aeda344200afb9c4aeda344200afd8c369da344200afd8c36a1a344200cfb9c4aeda344200cbfabba21a344200cbf8cba21a3442008ff8cba21a344200cbf8b5a21a344200cbf9b6a21a344200e3f8b9a21a344200c7fabb2e5a3442008ff8c2aeda3442008ff9c2aeda344200cbf9b82e1a344200aef8c66e1a344200a7f8c96e1a344200cbf8cba21a7442008ff8cba21a7442008ff9c3aeda744200cbf9b6a21a744200e3f8b9a21a744200cbfabba21a744200baf9c62ca8844200abf9ca2ca8844200abf9ca2ce88442008ff9c6aeda7442008ff9c8aeda744200cbf8b86a1a744200cbf8b3a21a744200adf8c3aaa7744200adf8c8aaa7744200cbf8baa218744200ecf8c66a27744200e5f8c96a27744200adfacc6a277442009f78c56e987442008ff8caaed87442008ff9caaed8744200cbf9baa2187442008ff8cbaa987442008ff8c36e98744200bbf1c12d68844200a7f8c96c9a844200cfd9b32cda844200cef8b62cda844200cef8b62c9a844200cef8b66c9a844200aef8c66c9a844200cf79b52d5a844200cef8b62d5a844200cef8b66d5a844200cef8b66cda844200aef8c66cda844200a7f8c96cda844200cfe9b22c9a844200abf8c5aaa8844200abf8cbaaa8844200abf9c22ea8844200abf9ca2d68844200abf8c2aaa8844200abf8c3aaa8844200abf8c26a28844200abf8c36a28844200 else 0xf7e0c954a1148200fde27754a1148200efe1a754a1148200fde0c754a1148200edf1a75c61148200ebf1a86061148200cff0ba6061148200efd1a34c61148200ff61525461148200d7f0b95461148200dfc8b28ce1148200d7d8b98ce1148200cfd8ba8ce1148200df68b554a1148200d7e8b954a11482009fe8cb54a1148200aff1c82ea1148200aff0cb6a21148200aff2cc6a21148200aff1ca2e21148200aff0c56a21148200ebf0b86a21148200e7f0c96a21148200aff1c32ea1148200aff1c52ea1148200aff1c72ea1148200aff0c3aaa1148200aff0c5aaa1148200aff0c8aaa1148200cfd8b368e1148200ffc1634c52148200ffc1a34c52148200ff62554c521482008ff9c52ea11482008ff9c82ea1148200ffc2334c52148200bfe1c74c52148200fbe2884c52148200f7e0b94c52148200fee2664c52148200efe1a64c52148200fde2774c521482008ff9c32ea1148200cf78ba9561148200d5f8b99de1148200cdf8ba9de11482008ff8cb68e1148200df68b29561148200d778b99561148200cbf8baa221148200cbf8b86a211482008ff8cb6a211482008ff8cb69e1148200dbe8b2a221148200d3f8b9a221148200bef1c62d61148200aff1ca2d61148200eef0a399a1148200aff0ca6161148200bdf0c76961148200bfe1c22d61148200faf28899a1148200eef1a899a1148200eef2aa99a1148200eef0a599a1148200fcf27799a1148200eef1a799a11482009ff1cb2161148200aff0ca9561148200eef1a65961148200aff0ca5961148200ef70ba9561148200ef70ca9561148200bfe0c29561148200bef1c62161148200bdf1c72161148200aff1ca2161148200bfe1c22161148200bfd1c32161148200bfb1c42161148200aff1ca5da1148200ebf0a3a221148200ebf0a5a221148200ebf1a6a221148200ebf28869e1148200aff0c869e1148200aff0cb69e1148200ebf1a8a221148200aff0caa221148200aff0c36a21148200ebf2aaa221148200ebf0baa221148200ebf0caa221148200aff0c369e1148200edf27769a11482009ff0cb69a1148200edf0a39de1148200aff1ca61a1148200aff0c369a1148200aff0c569a1148200edf0ba9de1148200aff0ca61e1148200aff1ca61e1148200f9f2889de1148200edf0a89de1148200edf1a89de1148200aef8c66d5a844200ed79a89de5544200ed7aaa9de5544200af78ca61e5544200ed78a39de5544200f97a889de5544200ed78a89de5544200af78c869e5544200eb78a2a225544200eb78a3a225544200af79ca61e5544200af78c369e5544200eb7a8869e5544200eb7a8869a5544200bd79c72ce5544200af79ca2ce5544200fc7a7799a5544200fb72882c65544200ef71a82c65544200af79ca2ca5544200af79ca5da5544200af79ca61a5544200) else (if i<26 then 0x7270722071d070c0707070206fd06f806e706e206dd06cc06bb06aa06990694068306720661065c064b063a06290618060705f605f105e005cf05ca05c505c005bb05aa059905880577056605610550054b054605410530052b05260521051c05170512050d0508050304f204e104d004cb04c604c104bc04ab049a04890484047f047a04690464045f044e0425041403eb03da03c903b8038303720355034403330322030502f402d702c602b502a40293028202710260024f023e0215020401f301ca01b901a8019701860175016401530142011900f000df00ce00bd00a0008f007e006d005c004b003a001d0000aff1ca58e1148200edf1a75ce1148200aff0ca5ce1148200aff0ca54e1148200eef1a658e1148200aff0ca58e1148200bf71c520e1148200bef1c620e1148200bdf1c720e1148200aff1ca5ce1148200bfe1c220e1148200bfb1c420e1148200aff1ca14e1148200efd0a88ce1148200efd1a88ce1148200f7d0c98ce1148200fdd2778ce1148200efd1a78ce1148200fbd2888ce1148200b7f0c98ce1148200aff0ca8ce1148200bfe1c214e1148200efd2aa8ce1148200efd0ba8ce1148200efd0ca8ce1148200aff1ca20e1148200ef70a39561148200fe72669561148200ef71a69561148200bef1c62ce1148200aff1ca2ce1148200ff60c29561148200ef70a89561148200ef71a89561148200ef72aa9561148200fd72779561148200ef71a79561148200fb72889561148200aff2cc68e1148200efd0b368e1148200ef725568e1148200aff0c568e11482009ff1cb20e1148200aff0ca60e1148200aff1ca60e1148200aff0c868e1148200e7f0c968e1148200aff0cb68e1148200eef26668e1148200edf27768e1148200ebf28868e1148200aff1c1aeda844200aef9c6aeda8442009ff1c1aeda8442008ff9c5aeda844200cef9c6aeda8442008ff9c7aeda844200efe1a688a1148200fbe28888a1148200efe1a888a11482009ef9c6aeda844200ffc23388a1148200fee26688a11482008ff8c5aeda844200af78c56dda844200aef8c66dda844200a7f8c96dda844200a7f8c96d5a844200cef9b72d9a844200cefabb2d9a8442008ff9c2aeda8442008ff8c3aeda8442008ff9c3aeda8442008ff9c1aeda844200cff1c1aeda8442008ff8c2aeda844200b7f0c94ca1148200b7f0c960a1148200ffc2332ca1148200ff62552ca1148200bfe0cb54a1148200bfe2cc54a1148200b7f0c954a1148200efd0a58ce1148200fed2668ce1148200efd1a68ce1148200bfe1c52ca1148200fbe2882ca1148200ff52558ce1148200efe2aa54a1148200ff617554a1148200ff60b554a1148200fee26654a1148200ffc23354a1148200ff615354a1148200ff625554a1148200fbe28854a1148200efe1a854a1148200 else (if i<27 then 0x1f971f861f751f641f471f361f251f141f0f1efe1eed1ee81ed71ed21ecd1ebc1eb71e9a1e891e781e671e621e511e401e3b1e361e251e141e031df21de11dd01dcb1dba1db51db01dab1da61da11d901d7f1d7a1d751d701d6b1d5a1d551d501d3f1d2e1d1d1d181d071cf61ce51cd41cc31cb21ca11c901c7f1c6e1c5d1c4c1c471c421c3d1c2c1c1b1c0a1c051bf41be31bde1bcd1bbc1bab1ba61ba11b9c1b971b7a1b5d1b4c1b3b1b361b311b2c1b271b221b111b001aef1ade1acd1ac81ab71aa61a951a841a7f1a7a1a751a641a5f1a4e1a491a441a3f1a3a1a351a301a2b1a1a1a151a0419ff19fa19f519e419df19ce19c919c419bf19ba19b519a4199f199a19951990198b198619811970196b19661961195c19571952194d19481943193e193919341923191e190d18fc18eb18e618d518c418b318a2189d188c187b187618711860184f183e182d181c18171806180117fc17eb17e617e117dc17cb17c617b517b017ab179a17951790178b17861781177c176b176617611750173f173a17351724171f170e1709170416ff16fa16e916e416df16da16c916b816b316a21691168c1687167616651654164f164a16451634162f162a16251614160315fe15ed15dc15cb15ba15a91598158715821571156c155b154a153915281523151e15191514150314f214ed14e814d714d214cd14c814b714a614a11490147f147a147514641453144214311420140f13fe13ed13dc13cb13ba13a913981387137613651354134313321321131012ff12ee12dd12cc12c712c212bd12ac12a71296128512741263125212411230121f120e120911f811e711e211dd11d811c711b611a511941183117211611150113f112e111d110c10fb10ea10d910d410cf10be10ad109c108b107a106910581047104210311020100f0ffe0fed0fdc0fcb0fba0fa90f980f870f760f710f600f4f0f4a0f390f280f230f120f010ef00edf0eda0ed50ec40eb30eae0e9d0e8c0e7b0e760e650e540e430e320e210e100dff0dee0ddd0dcc0dc70db60da50d940d8f0d7e0d790d740d6f0d5e0d590d480d370d260d150d100cff0cfa0cf50ce40cd30cc20cb10ca00c8f0c8a0c850c800c7b0c760c710c600c5b0c4a0c390c280c170c120c0d0bfc0beb0bda0bc90bc40bb30ba20b910b800b6f0b5e0b4d0b3c0b370b260b150b100b0b0afa0ae90ad80ac70ab60aa50aa00a9b0a8a0a790a680a570a460a410a300a2b0a260a210a1c0a0b09fa09e909d809c709b609a50994098309720961095c0957095209410930092b09260915091008ff08ee08dd08cc08c708b608b108a0088f088a087908680857084608350824081f080e07fd07f807f307ee07e907d807c707c207b107a0079b078a07850780076f076a07650760075b07560751074c074707420731072c else 0x37bf37ae37a937a4379f378e377d376c3767375637513740372f372a37193708370336f236e136dc36d736d236c136bc36b736a636a1369c368b367a366936583647363636313620361b36163611360035fb35f635e535e035db35ca35c535c035af359e35993594358f358a35853580357b357635713560355b355635453540352f351e35193514350f350a3505350034ef34ea34e534d434cf34be34ad349c348b347a346934583447343634253414340f340a33f933f433ef33ea33d933c833b733a633953384337f337a33753370336b335a33553350333f333a33293324331f331a330932f832f332e232d132c032bb32b632b132a0329b328a3285327432633252324d3230321f320e31fd31ec31db31ca31b931b431af319e318d31883177316631613150313f312e312931243113310230f130e030cf30be30ad309c308b307a3069305830473042303d302c301b30163011300c2ffb2fea2fd92fc82fc32fbe2fad2f9c2f8b2f862f752f642f532f4e2f492f442f332f2e2f1d2f182f132f022ef12ee02ecf2ebe2ead2e9c2e972e862e752e642e5f2e5a2e492e442e3f2e3a2e352e302e2b2e1a2e092e042dff2dfa2de92de42ddf2dda2dc92db82da72d962d852d742d632d5e2d592d542d432d322d2d2d282d232d122d0d2cfc2cf72cf22ced2cdc2ccb2cba2ca92ca42c932c8e2c892c782c732c6e2c692c642c532c422c312c202c0f2bfe2bed2bdc2bcb2bba2ba92b982b872b762b652b542b432b322b212b102b0b2b062b012af02aeb2ada2ac92ab82aa72a962a852a742a632a5e2a592a542a4f2a3e2a2d2a1c2a0b29fa29e929d829c729b629a52994298329722961295c294b294629352924291f290e28fd28ec28e728d628c528c028bb28aa28a528a0289b28962891288c28872876286528542843283e282d281c280b280627f527e427d327c227b127a0278f277e277927742763275227412730271f271a2715270426f326ee26e926e426df26ce26c926c426bf26ae269d268c26872682267d26782673266e26692664265f265a26552650263f263a26352630262b26262621261c26172612260125fc25eb25e625d525c425bf25ba25b525b025ab25a625a1259c259725862581257c256b256625552544253325222511250024ef24ea24d924c824b724a6249524842473246e245d244c243b243624312420240f23fe23ed23e823d723c623b523b0239f238e237d236c23672356234523342323231e230d2308230322f222e122dc22d722d222cd22c822b722a622a12290228b228622752264225322422231222c221b220a21f921e821d721c621c121b0219f218e217d216c215b214a2139213421232112210120f020df20ce20c920b820a72096208520742063205220412030201f200e1ffd1fec1fdb1fca1fb91fa8)))) else (if i<33 then (if i<30 then (if i<29 then 0x51bb51aa519951885177516651555144513f513a51295118510750f650d950d450cf50be50ad509c508b507a50695058503b502a501950084ff74fda4fc94fb84fa74f964f854f744f6f4f5e4f4d4f3c4f2b4f1a4f094ef84ee74ed64ec54eb44eaf4e9e4e8d4e7c4e6b4e664e554e444e334e224e114e004def4dde4dcd4dbc4dab4d9a4d894d784d674d564d514d404d3b4d2a4d254d144d034cf24ced4cdc4ccb4cc64cb54ca44c934c8e4c7d4c784c674c564c514c4c4c474c424c314c204c0f4c0a4c054bf44be34bd24bc14bb04b9f4b9a4b894b784b674b624b514b404b3b4b2a4b194b084af74af24aed4ae84ad74ad24acd4ac84ac34ab24aa14a9c4a974a864a814a7c4a6b4a5a4a494a444a334a2e4a294a184a134a0249fd49f849f349ee49dd49d849c749b649a54994498349724961495c494b493a492949184913490248fd48ec48db48ca48b948b448a348924881487c486b485a4849483848274822481d480c47fb47ea47d947c847b747a6479547844773476247514740472f471e470d470846f746e646d546c446bf46ae469d469846874682467d466c46674662465d46584647463646314620460f45fe45ed45dc45cb45ba45a945984593458e45894584457f456e45694564455f454e45494544453f453a452945184507450244fd44f844f344ee44dd44cc44c744c244bd44ac449b449644854480447b446a44594448443744264415440443f343ee43e943e443df43da43d543c443b343ae43a943984387438243714360435b43564351434c4347433643254320431b43164311430042fb42f642e542d442c342be42b942b442af42aa42a542944283427242614250423f423a42294218420741f641f141ec41db41be41ad419c4197418641814170415f415a41494138413341224111410c40fb40ea40d940c840b740a640a1409c408b40864081407c40774066405540444033402e402940184013400e40093ff83fe73fd63fc53fb43fa33f923f813f703f5f3f4e3f3d3f2c3f273f163f053f003eef3eea3ed93ec83eb73ea63e953e843e733e623e513e4c3e3b3e2a3e193e143e033df23ded3ddc3dd73dc63db53da43d933d823d713d603d4f3d3e3d2d3d1c3d0b3cfa3cf53ce43cdf3cda3cd53cd03cbf3cae3ca93ca43c9f3c8e3c7d3c6c3c673c563c453c343c2f3c1e3c0d3bfc3bf73be63bd53bd03bbf3bae3b9d3b8c3b7b3b763b653b603b5b3b563b453b403b3b3b363b253b143b033af23ae13ad03abf3aae3a9d3a8c3a7b3a763a653a603a5b3a563a453a403a2f3a1e3a0d39fc39f739e639d539c439bf39ba39a93998399339823971396c3967395639453940392f392a39193908390338f238e138dc38cb38ba38b538a438933882387d386c385b3856384538343823381e380d37fc37eb37e637e137d0 else 0x69536942693d6938692769226911690068ef68de68d968d468cf68ca68b968b468a368926881687c68776872686d68686863685e68596854684f684a68456840683b682a68256814680f67fe67f967f467e367d267cd67c867c367b267a16790677f676e675d674c673b672a6719670866f766e666e166d066cb66ba66a9669866876682667d66786667665666456634662f662a66256614660365f265e165d065cb65ba65a965a4659f658e657d657865736562655d654c65476542653d652c651b65166505650064fb64f664e564d464c364b264a16490647f647a64696464645364426431642c641b640a63f963f463e363de63d963c863b763a663956390637f636e635d634c633b631e630d62fc62eb62da62d562c462bf62ae629d628c6287627662656254624f624a62456240623b62366231622c62276222621d62186213620e6209620461ff61fa61f561f061eb61e661d561d061cb61c661b561a46193618e618961786173616e616961586153614e614961386133612e61296124611f611a6109610460ff60ee60e960d860c760c260b160ac609b608a608560746063605e604d603c602b6026601560045ff35fee5fdd5fcc5fbb5faa5fa55f945f835f7e5f6d5f5c5f4b5f465f355f305f2b5f1a5f095f045eff5eee5edd5ecc5ebb5eb65e995e945e835e725e615e505e3f5e2e5e1d5e0c5dfb5dea5dd95dc85db75da65d955d845d735d625d5d5d4c5d3b5d2a5d195d085cf75ce65cd55cc45cb35ca25c9d5c8c5c7b5c765c715c6c5c675c565c455c405c2f5c2a5c255c145c035bfe5bf95be85bd75bc65bc15bbc5bab5b9a5b895b785b675b625b515b405b2f5b1e5b0d5b085b035af25ae15adc5acb5aba5aa95a985a875a765a655a545a435a325a215a1059ff59ee59dd59cc59bb59aa59a55994598f598a59855980596f596a59595954594f593e593959285923591e59195908590358f258e158d058bf58ae589d589858935882587d586c585b584a58395834582f581e580d5808580357f257e157d057bf57ae57a957a45793578257715760574f573e5739573457235712570156f056eb56e656d556d056bf56ae569d56985693568e567d566c565b564a56455640562f562a56255620561b56165611560055ef55ea55e555e055db55ca55b955a85597558655755570556b556655555550554b553a55355530552b55265521551c55175512550d54fc54f754f254ed54e854e354de54cd54bc54ab54a654a1549c54975492548d54885483547e546d54685463545e544d543c54375432542d541c540b53fa53e953e453d353ce53bd53ac539b538a5379536853575352534d53485343533e5339532853175306530152f052df52da52c952b852a75296528552745263525252415230521f520e51fd51ec51e751e251dd51cc) else (if i<31 then 0x810f80fe80ed80dc80d780c680b580a48093808280718060805b8056804580348023801280017ff07fdf7fce7fbd7fac7fa77f967f857f807f6f7f5e7f4d7f3c7f2b7f267f157f047eff7efa7ef57ee47edf7ece7ebd7eac7e9b7e8a7e797e687e577e527e417e3c7e377e267e157e047df37dee7de97de47dd37dce7dc97dc47dbf7dba7da97d987d7b7d6a7d597d487d377d267d157d047cf37ce27cd17cc07caf7caa7c997c887c777c667c617c5c7c4b7c3a7c297c247c137c027bf17be07bcf7bbe7bad7b9c7b8b7b7a7b697b647b5f7b5a7b557b447b337b227b1d7b0c7afb7aea7ad97ac87ab77aa67a957a847a737a627a517a4c7a3b7a2a7a197a0879f779e679d579c479b379a279917980796f796a79597954794379327921791c790b78fa78f578e478df78ce78bd78ac789b788a787978687857785278417830782b781a780977f877e777d677c577b477a3779e778d778877837772776d775c774b773a77297718770776f676e576d476c376be76ad769c768b768676757664765f765a7649764476337622761d76187613760e7609760475ff75fa75f575f075eb75e675e175dc75d775d275cd75c875c375be75b975b475af759e75997594758f758a75857580757b757675717560754f753e752d75287523751e750d7508750374fe74f974f474e374de74d974d474cf74be74b974a874977492748d74887483747e74797474746374527441743c743774267415741073ff73fa73f573f073eb73e673d573c473bf73ba73b573b073ab73a673a1739c739773927381737c73777372736d73687363735e734d73487343733e73397334732f732a73197308730372fe72ed72dc72cb72ba72b572a4729f728e72897278726772567251724c72477242723d722c721b7216720571f471e371d271c171b0719f718e717d716c715b714a713971287117710670f570e470d370c270b170a0708f708a7085707470637052704d704870377032702d701c700b6ffa6ff56fe46fd36fc26fb16fa06f9b6f966f916f806f7b6f766f716f6c6f676f626f516f406f2f6f1e6f0d6efc6eeb6eda6ec96ec46ebf6eae6ea96ea46e936e8e6e7d6e6c6e5b6e566e516e4c6e476e426e316e2c6e1b6e0a6df96de86de36dde6dcd6dc86dc36dbe6db96db46daf6d9e6d8d6d7c6d6b6d666d616d506d3f6d2e6d1d6d186d136d026cf16cec6cdb6cca6cc56cb46ca36c9e6c8d6c7c6c776c726c6d6c5c6c4b6c3a6c296c186c076bf66be56be06bdb6bca6bb96ba86ba36b9e6b996b946b8f6b8a6b856b806b7b6b6a6b596b486b376b326b2d6b286b236b126b0d6b086b036afe6af96ae86ad76ad26ac16ab06a9f6a8e6a7d6a786a736a626a516a406a3b6a366a256a206a0f6a0a69f969e869e369d269c169bc69b769a669a1699c697f697a69696958 else (if i<32 then 0x980b97fa97f597f097eb97da97c997b897b397ae97a997a49793978e978997789773976e976997649753974297319720971b970a96f996f496e396de96cd96c896ab96a696959690968b968696759670966b9666965596449633962e96299624961f960e9609960495f395ee95e995e495d395ce95c995c495bf95ae959d95989593958e95899584957f956e956995649553954295319520951b95169511950c94fb94ea94e594e094db94ca94c594c094af949e948d947c94779472946d94689463945e944d94489443943e94399434942f942a94259420940f940a9405940093fb93f693f193ec93e793e293dd93d893d393ce93c993c493bf93ba93b593b0939f939a938993849373936293519340932f931e93199314930f930a930592f492ef92de92cd92c892c392be92b992a89297928692759270925f924e923d92389233922e92299218920791f691e591d491c391be91a1919c918b917a916991649153914291319120910f90fe90f990e890d790c690c190bc90ab90a690a19090908b907a9075906490539042903d902c901b901690058ff48fef8fea8fe58fe08fdb8fca8fb98fa88fa38f9e8f8d8f7c8f778f728f6d8f688f578f468f358f248f138f028ef18ee08edb8eca8eb98ea88e978e928e818e708e5f8e4e8e3d8e388e278e168e118e0c8dfb8dea8de58de08dcf8dca8dc58dc08daf8d928d818d708d5f8d4e8d498d448d338d2e8d298d248d138d028cf18ce08ccf8cbe8cad8ca88ca38c928c818c7c8c6b8c5a8c498c388c338c2e8c1d8c0c8bfb8bf68bf18bec8be78be28bd18bcc8bc78bc28bb18bac8ba78b968b918b808b7b8b768b718b6c8b5b8b4a8b398b288b178b068af58ae48adf8ada8ac98ab88aa78aa28a918a8c8a878a768a658a548a438a328a218a1089ff89fa89e989d889c789b689a589a0898f897e897989688957894689418930891f891a890988f888e788e288d188c088af889e889988888877886688558850884b8846883588248813880287f187e087cf87be87ad879c878b877a876987588747873687258714870f86fe86ed86dc86d786d286cd86bc86b786a686958690867f866e865d864c863b862a8619860885f785e685d585c485b385ae85a985a48593858e857d85788573856e85698564855f854e853d852c852785228511850c8507850284f184e084db84ca84b984b484a38492848d847c847784668461845c845784528441843c84378432842d842884178412840183fc83f783f283ed83e883d783c683b583b083ab83a683a1839c8397838683758364835f834e833d832c831b830a82f982e882d782c682b582a48293828e827d82788273826e825d82588247823682258220821b820a81f981e881d781c681c181bc81ab81a681958190817f817a816981588147813681318120 else 0x3830800cc27001043080084230615830f020411041e040800306198c0f02078103c08107020400e0408000c8208260420001984000000003308019041183080050a105c08400001a182000160c3c081034305a0c2001430560033061000011e100003061b810816003b0210860841876003b001d8008121820d8108478423c211e10000028609418400092080006860941040d041983080050c10950b41042543c1216860ec08760423001d810ec0876043b001d800f020423c3b021d8108c004a0020681a82081a0781033061000008c105c005a182d041a820b4105a182d0412850dc084010c198308000e040f02078103c08168e0f0207208390417810f0206a0834081e040f0204e042001c5040cc370210330819878243c081e040838243c0810830f04878243c121e090b41878243c121c82084384190410870832083904106410421c37021b810801b001686080108290a148608360021361d800b428520c3b021d810ec086e00290c106c0876042f00103c00400014284050c1a820f0207810209880801c12138309c6076003c08138508000000016c10704840cc3c121e09080170014850a4287824202290f04878243c121229091484e0020661070487810200043878103c081e040bc085e002001c0058242c121e090f02040066100000e040841842143c081e040f02040cc3c081a82081a07810200000d03c08100381020a820842878102124105c0041c1212850838243c121e090819852143c12101c186e0420000011e10460801082084107020400e040800000000000a1c200000d0c1000006850800d0a1686094284a182098308490563020e090bc08660433181b800849041302198c08000014307824330612850dc084130610000d0c100000000000702046183c12100000e040f0204a182000025c2001c1841080f01186c121e090420a0184085214203e1038e090420a0204187824338450a1085094087824280403e1e090a0104285824210a128509428421421061081084087824108280630e108208237048540c21821001281084305824250a1085094087824108280608407808c30810a428407c3c121402083084284a14210c1281080f878242805c1214029c459c409c2f9c1e9c0d9bfc9bf79bf29bed9bdc9bcb9bc69bc19bbc9bb79bb29bad9ba89ba39b9e9b999b889b839b7e9b799b749b639b5e9b599b549b4f9b4a9b459b409b3b9b369b319b2c9b279b229b119b0c9b079b029af19aec9ae79ae29ad19ac09aaf9a9e9a819a709a5f9a4e9a3d9a389a339a2e9a1d9a189a139a0299f199e099cf99be99ad9990997f996e995d994c994799369931992c99279922991d99189913990298fd98f898f398ee98e998e498df98da98c998b898b398a29891988c98879876986598549843983298219810))) else (if i<35 then (if i<34 then 0x18781020e040806003d021004186a0420e810f408417001b800f4084050610190838103d021582081a0c2d0616830801b0010900dc00400070207810211e10444041c081e0408320439021044407810200032042007020400c810bc0078103c081e040dc0041c0810001c0810038102007048400e040dc00400000000000d061000e0c20a810f02040000000e040801c081070206e0025101e040d4087a043d021e810f02078103d021002e0020002a043d021a81094407a042b0610000001c10400e04080e08200036042f0010141876003b0210001c081070204070011800a4504004813c2e810c4507810211e1e040c450622820004f0781020e0409c18407061e040f0204002820ec087604214e1b800dc0042183b001d820cc1046143b021e090801702103408000b810819840cc3b0410038103c121e090838243c081e09080008300800cc2005c0878102c121e090a43078103c1210118078242c081003810200000007048781020000e0c200038103c081e040f02078103c081a8108000e040f0204000740840d0610001c08138c0f0204e0c20a810800706100000c810e408720420701c810e40878103c081e040f02078103c081e040f4084278212e1e040dc0046083c0810001c08107020722839141c8a0f020781039141683080000702078103c081e040e45078103c081c8a0f02078103c081e0409c00781020b80080a14370210341050c02084103020781020030204000000004c306618330c108308381033061183082e04230e10340dc084a14211e1a820cc184007810f020660c211e1983080050a108f0800003428400034285a0c250a10000000000000002830800000000000a0c20287080a142d041000000000001428400042080a1421401682085007810330c1282081a143c081e040bc0076003b001d800838243b001e040801b001d800f0205a14207800b410781020b800b4285a082d04102c305e002f001682081a14200342878102000000e090847840124100260420841e090cc08660420e040f0206a0835041b800dc004030012800f0205e043c081e040ec0842a020d810847876043b0019800cc0041c1212850ec084248216a10920dc00423c37001d810ec087604216a108f0ec0878103c081e040f0207810245c148ee0411c00410c2084100c18781020e040800050104477020b8103c08108208260c3c0810038102b181e04081386e042700107020400000130619830800001c0040048e08198521820b810dc08423c20661e0409c00421839041e090dc08460c290c1000002c10330a43041c08148608060c2c0810a808000004b8c60923b8105c081e04080000000a0208615830f020781020e040f0205630208610001c081034284000000000c30419041000170210020040000007061000000000d0610000 else 0x2006c0041b0010001b0010704842403b001d800ac106e042004c104050215820ac1066082003c0866082004c10660833041e090f0484005820a148460c37001b800dc00400b800940856003c08100020c2018208410560020001600211e11800f020400b80080000001c0813810800001c1878102700138309c184e0c200000cc200019840000000000070610000000021821061087080000000000382420003810270610001c0810820f0207810209880800cc3c081281084185e042f021383080000000706138309c18407061b81080e18270c1e040f0206e0437001e040f02040cc3c081e040f02046082066100017001e090f0487824230210330822840cc20881003810270210400f02040cd8244000c10460c2056104a081985a183702103360915c0878103c081b800d048288b81024601e040ec1840ac330610704840ac2c1210380b048460c2c121e04081807810208010702078103c0810430800c8205611850f02078103c08138009c1078103c081211080b046143c0810460f02040080102c50417001e04082004002a1e040838102c08101a08262820e040f0204000000d4207c1e040801c121e090f02078243c121e090838242d061e090800b83c12100c084a043c121e0908000e09080000704878102001438400e09094284a0c20e090801c12107048400003810200a00f04878243c121e090f0205098204260f04878243c08106c0041b0011850ec08760420d80084e84608201810ec0050983c1215810801c121b810850078102b0215810dc0058102b021e040f048782421201e090f0205604201820cc28487c3c08107048782420e090801c12100000e0908c28407061e090f04878242d061e090f04878243c121000000143840007020400000a0c2d061e09080000038242504100004521286083824200704878243c121e090f04878243c121380080000001c121e09080070412290838243c12100000070487824200001c0810038103c08138c080000001c0810930f020421823021e040838103c0810380f0204001800819b048b8103c08100198417001b80082e043702107020781020e040f02056282704138209c104003820800003c085e042f021e0408000641000130419820f04850703c081e090cc1078243c121e040f04866083c08107020782420b800838103c081e040f04878243c081e090cc105e0420982090f8660820e040819040f02104c106608330414260cc1066083c1219820f04878243c1211870cc1040b00100000e810dc0040005c006e00210c107020423c3d02102c1078102b041070207810201800f40878103c081a81082e002000382420003a0420321e810f4084a1425001a810d4087a04211e1d80083a0420001a0c205820f020423c3c0810702078103c08100381035021054087a0420034) else (if i<36 then 0x200970bc005e0020e040f0204010410702040583c081e040f0207810213c198a0838102c0810702078103c0819850f02078103c081b800816142002c28400841090082104278211e103408c08781035041034083810331410160838102b141003810200340f048400000000000000000000000000001c184000000000005061286094184a1c20000e20200000009b080000341841c121e090800000000e090f048782420070487824203830800000026c3c0810000000000000e0c2000000003824200000000160833041000a042b0410820841041c0810704840b041b810dc0840000013041b810826083c121e040f020420c25021e040f04878103c0819820f02040cc3c081e090f02078243c121e040f048460037001e090801c121b800ac10400582080130419820cc104050215820ac1078242304100004481000000026082b0415820f02056082b0415820cc1066082003c08400982081e04330419820800000260820e090f02056303c081003810200000002c184240370010330801700183c08198781020070204e0820e04081c040f001780080090270410000f021e040f020781027041e040f0207810200117078102f00100000000000645078243c121c8a080000704840000019141e090832282066103208c0040cc200704840cc3c081001638202300810f03c1210704840cc200009840003360910010c20861001f84000330800cc2702104c0f020400000124200200bc084080200000000000000000341841c081001984000900f02040005c0078103c08122e0f02078103c0819830cc185e003c0810430cc1840b0610702041182700104308000e040ac60781027021000007a1e040cc6040742076104c6066302005c0840e02000c6041c0810001c08158c082e0020003810330619830cc184a043c08143008382420e090f048782420e090f048782420e090801c081e040f0206e00202810f02078103c1210820819b048b8103700158308c1841702101408423c370210041878103c1210000000000000000000000000000e0c20000a082506128708007101000086010000d06100000000a0c2001c40401041e04083810209860f04841c121e040838243c081682081e003c081e04082e002d041e040f02040b0c1b800838243c121e040800cc2001c187824200702078103c081082083826620400330f0204a0421061e090f04842403b001d800f04876003b001d800b41078103b001d800ec004011e1d810ec0876043c121b80084b8782433001d810ec0841c081e040800003c005a08207800801c0816820800f0019860f0204002820cc3078103c081e0408260433021d81080e078102006c087604209810ec0878102b001e040f020781023001e040f0204600250017800f02040cc3b0211820f02040b04100000b8008381 else (if i<37 then 0x3c081004104000000003418400000000038103c08101c18781020070204e303c0819850cc284628330a10302040000c1858103c081000002830801c121000002870f0205e04208c10021078102048e08004c2009e18a10382420003810200038103c081b8008000034304003830800068308000004f04118200000001c1840009e0b4305a0c21401000000460943040001430400686084f04a182506100000000e04200000000000097080000000000000000000000028708382420b800ec08560c25021583094304000000710101c404a082000000661e090f048782420b800f04840cc20000045212290f0486e0424521e090800cd82440e090f04878102078008438781021061e040bc0841c081e040b048400e040801c081070484140810820f0204070210330836003b001000000704876003b001000a18250e100000d800ec00760033101d800ec004e0c2066103c085e042f0213810802502f021e0909c0840cc2028308500400282094304000a0080000330819b04880cc25021e0409c0040003308000e040ec0076003b001d810ec0876042005c00660c20e090841076043b02100023c3b0213880800000360020000218200141841b021000004850ac0856043c0814850ac087810290a1000214208c1b800838102002c286628290a15810f02046283c081581083810204215810dc005214200850f0204010a1e040842841314198a0826283314158108010833141b810a42841b0010a80ac50760420000240331419800cc006628230012800841078102b141e040ac5056282b141e04084907604213a102c2850983c0810000f00107048782420e040ec0076003c081d800ec0072383c081e040cc2878103c08141c08000685081a0c200000001c00781027181003810200038103c0810702040d0206850b4304050c1014304000000d02000000034081a182000000e040f020781020000000702078103c0810050078103c081a820ac086a083c0810340f0204604250214850838102000010820042082107810200021078243c121e090f04840060908381020e0908010835041e040821841c081e040f02078103c08101c00404c2080102808c5078103c081000e0c24221e0409c0078103c081e040cc5040cc290a10009852142048508c0840cc206614850812142b1410001c0810023041183104102109c0841003c081e040802b4200702078103c08104208000e04080000003382700108e04215c0043382700158a091707810202c1e040f02078103c081e040801003c08158a0f020400e040f02078102009e0823078102c0813830f020560c21501e040a1307824200001c081e0408c1841c081e040f0206a083c08158a0cc18660c330616040f020781020034082106e003048109e0847846043c081a820dc0078102070118a0800a else 0x27820046082304278208c10001c121e040800000000000070610000068608000000000000000382420003824200038243c121e090f0207811e045c081e040f0205e002000381020004186e0037001033081985e0021417022e04084307810))))))
def f2758l10 : Packing := (3298,5,7,8,4,16,0,f2758d10)
def f2758d11 (i : Nat) : Nat := (if i<14 then (if i<7 then (if i<3 then (if i<1 then 0x5cd108027fcdd2e6884013fe6e983442009ff164d1a21006f7a5568d108027fc5d306884017be6d88344200bbf36e41a21004ff9ba20d10803dbd444aa884019fe2e5a5442009ff576d2a21007cfa779991080377d3334a884013fe2e985442009ff164d2a21004ff8b3695108027fcdd30c88401b7e9dda644200d7f510d3221004ff9ba5d91080377cd3ccc88401ebea226644200ddf35133221005ff0b1955108027fc5d4aa884013fe6e96544200def1752aa21006f78a8955108037bcd44aa88401bdeaaa5544200bdf36c42a21005df9b7215108027fcdd10a884017ee6d08544200bfe36242a21005fe9b221510802fecd990a884017fa6c853482009ff37429a41004ff8ba54d208027fc5d46690401bf62ea3348200d7f14b442c10057f8b98cd208027fc5d2e6904013fe6e97348200bfe36241a41006df9a75cd2080377cd32c6904013fe2e963482009ff374b1a41006fdaaa8cd20803fad2ac6690401bf62963348200fdb4cd19a41006fd8a18cd20802bfc5cac490401afe2a18248200aff172c1241006fd8a88cd208037ecd446690401df62e63348200f7b51119a41006fd9a68cd20803eed3bc6690401bf669e33482009ff576d1a41006f78a195520803fb4594aa904019fe2e5a348200dbf4eed1a41006bfa8868d208027fc5c34690401bde69e5548200f6f5112aa41006f78a895520803ebd3bcaa90401bde28e5548200fcf4cd2aa41006f79a69552080377d333469040177e6dc83482009ff37441a41004ff8ba60d20802f7cdb106904017fa6c88348200bf736841a41005f79b520d208027fc58b4690401bde955a3482009ff16ad1a41005df9b728d208027fcdd30690401bf668ca348200bdf36c51a41004ff9ba205208037f850b02904017be2d98148200bbf36e40a41004ff8ba5c520802ff4d9102904017ee6d08148200bf736850a41005f79b528520803df544242904017f66cca148200d7f350c0a41004ff8ba605208037f8d0942904017fa6c831482009ff37418a41006fd9a34c520802bfc5ca4290401dfa2e52148200bfd57690a41006ff0a1485208027fc5d2a290401bbe6996148200dbf34eb8a41007f6952545208027fc5d262904017fa6c851482009ff37428a41005ef9b628520803f75332a490401f7a9dd5248200dfd34ea9241007f68a554920803fb4a9aa490401fda9555248200fed2eaa9241005feabb549208037bc52aa4904015fe2e55248200dfd554a9241007de8b754920803df5442a490401dfa2e55248200ff9466a9241007fca33889208037f451c4490401fba99a2248200bbf36e50a41005bf9b8285208037f450c4490401bfa69a2248200dfb146992410057f8b94c9208037f45444490401bfa6a22248200f7d51111241004fb9b4aa9308027f858b4c904013be2d9a844200 else (if i<2 then 0x13fe2e98758200aff172d2ac1006df8a39dd60803cfd444eeb04017beaed63582009ff174b9ac1004ff8ba60d60803b7c5cac6b0401f9e9556358200f9f4eeb1ac1007afa8858d60803dbd444aab0401bde2ea5558200fcf2cb2aac1007d7a7795560802bfc5cb46b0401bde28a5558200def1472aac1005ff1b10c96080377cd3ccc98401bbeaaa664c2009ff374bb261007cfa7799930802bfc5cac698401bbe28a664c200ddf14b33261004ff8b1aa9308027fc5955498401ff888a11582009ff576d3261004ff8b2699308027fc5ab4c984019fe2e5a64c200dfd175112610057f8b9889308027fc5d44498401bfaaaa224c200dfd34f11261007bea88889308037f454444984013fe2e9824c200fdb4cd19a61006fd9a68cd30802fec59b04984015fe2e5324c2009ff174b1261004ff9ba20930803fe919c22b0401fba58e2258200dfd147112c1007f6a5588960803fe519c44b0401f3e9dd6158200f5f510b0ac1006df9a75c560803df544444b0401bfa2ea22582009ff175112c1006fe9a788960803f74b2c44b0401bfa2962258200fbd4ef112c1006ff1a784560803df944422b0401fb658d3158200fbe4ef08ac1007ef16384560803fb92ac22b0401fbc5961158200fdd444b0ac1007eda3358560803f3d2aac2b0401fbc6056158200bdf36c98ac1007e796554560802f7cdb2a2b0401bdeaaa55482009ff164d4221004ff8b36a1108027fc5ab50884013fe2ea8844200d7f55544221006bf8baa21108035fcd4510884013fe2ceaa442009ff16b55221004ff8b8aa9108027fc5955488401bbe2d9a844200cff172d4221004ffabb6a1108027fc5d30e884013fe6e987442009ff166d3a21006dfaaa9dd10803cfd444ee88401b7e2a27744200dbf3513ba21006bf8a2a21108035fc51d1088401afe29688442009ff576d3a21006bfa8869d108027fc5c34e884019fe2e5a744200ffc44508a41004ff8ba84520803ff098a4290401ff85c52148200aff17308a41006ff2aa845208037f85d422904017fa2ca1148200fdd4cc90a41006fe9a648520803ef53ba42904017fa6d52148200ffc14290a41007fca3348520803fb52aa4290401bfc68e1148200fee4ab08a41006ff0a5845208037f851c2290401ff854a1148200ffc16508a41007fd23384520803df94442290401bfc2a21148200dfe35108a41006ff1a784520803f793342290401bfc69a1148200fbe4ef08a41006df8a39dd108027fc5c346884019fe2e5a3442009ff576d1a21006bfa8868d108027fc5ab4688401bbe999a344200dbf4eed1a21006f79a695510803ebd3bcaa88401bde69e5544200fcf4cd2aa21007f70b1955108037bc514aa88401bde28e5544200bfd36441a21005fb9b420d10802fbcda906884017fc6c483442009ff374b1a21004ff8ba else 0x1119a21006ff2aa845308037f85d422984017f62ce114c200dfe15108a61007df277845308037f8d3c2298401efca22114c200bdf36c10a61005df9b708530802dfcdc042984017de6d4214c2009ff17508a61005fd9b308530802fdcda042984013fe6e2aa48200ffc44508a61006ff0a2845308027fc5c554904013fe2d6aa482009ff36b55241004ff9b6aa9208037f852c2298401fbc99a114c200dfe34d08a61007f725584530803fe919c2298401ff454e114c200ffa16708a61004ff9ba08530802fdcda1029840177e6dc814c2009ff37440a61005fd9b320530802bfc5caa2984013fe2e9514c2009ff174b8a61007eea66889308037f4d344498401f7a9de224c200dfd14b11261005ef8b6605308027fc5d30298401bfa286224c200bfb36a98a61007eda664c5308037ecd326298401ff2889314c200ffa26290a61004ff8ba48530803fe8c0a62984015fe2e5314c200bfb36628a61004ff9ba14530802fed5da6298401f769dd314c200f7b51098a610077d8b94c5308027fcd9d5490401bbe2966648200f9f4ef33241006ef9a79992080377c51ccc90401bde694a548200bdf36c52a41005df8b7695208027fcdd30c90401bfc2c5a6482009ff166d3241004ff9ba5d920803d7d444cc90401bbe6a26648200ddf55533241004ff8ba59520802ff8d890a904017fa6c88548200ddf34cb2a41006f78ba95520802ff4594aa904013fe2ea55482009ff37442a41004ff8ba61520802fdcda14a9040177e6dc8548200bfb36642a41005fb9b421520802f7cdb10a904013fe2d5a648200d7f17544241004ff8baa21208035fcd415090401afeaaa8848200d7f14344241006bf8a3a21208035fc52d10904013fe2c6aa482009ff36355241004ff8b3aa9208027fd5db50904013fe2c5a8482009ff166d42410067f8b96a120802ff858b4c90401b7e2867748200dbf1473ba41004ffabb699208036fd3bb4c90401afea21a648200cff172d3241004ff8b369d208035fd4434e904013fe2e1a7482009ff162d3a410079fa889dd208036fc544ee904013fe2e98748200fbb4ef19ac1006fd9a78cd60803ded44466b0401bf62963358200dfb14519ac1007f5a558cd60803f6cb2c66b04013fe6e85358200bdf36ca9ac1004ff8ba54d60802f7cdb0a6b0401bf62ea3358200fdb2c719ac1004ff8ba8cd60802dfcdc064b04013fe6e832582009ff174992c1005df9b70c960802fdcda064b04017de6d43258200bdf36c192c1004ff8ba549608027fc5d304b04015fe2e5a258200bbf16ea92c1005fb9b414960802f7cdb0a4b04013fe6e85258200fdb306b1ac10076f8b959560802f7d5dacab04013fe2e98558200f5f510b2ac1004ff8ba95560803f3cc2acab0401f3e9dd65582009ff166d3ac1006bf8a2a21608035fc51d10b04)) else (if i<5 then (if i<4 then 0x803ff4c1c4488401ff6605314c200ffb2e698a61007fd8524c530803ff51126298401ff64c9314c200ffb2a698a61005ff8b24c530803fecc326298401ff65d9314c200ffd2c711221007fd9b64c530803fecd326298401ff62d5314c200ffd10711221007fd9b54c530803ff4b9c4488401ff6695314c200ffd2a711221007fda884c530803ff429c4488401ff66a1314c200ffb17098a61007fd9b24c530803fecd3a6298401ff661d314c200ffb2ea98a61007fd9b74c530803fecb2a62984017fe6dd314c200dff34e98a61007bfa884c530803fed198a298401bfe2a1214c200bff36628a61007dfa774c530803dfd44242984017fe6e1214c200bff57698a610077f8b94c5308037fd55242984017fe2e1214c200bff576c0a21007fea2214530802ffcd90a2984017fe6e1314c200bff17098a61006ffaaa14530802ffcdaa62984017fe2d5314c200bff57690a61007efa664c530803feca8a6298401ff65c5314c200bff36e90a61005ff9ba14530803fecc1a6298401bfe6e9214c200bff36c98a61007bfa88605108037fcd3262984017fe6e9214c2009ff37419221006fd9a58cd108027fcdd2a488401ff888a11442009ff576d1221004ff9ba4c9108033fc5cb4488401fdc5495144200dfb14b19a21004ff9ba2091080377d33344884013fe2e93244200aff172b8a21007fd233845108036fd3bb44884013fe2e953442009ff374a9a21007fd233545108035fd4434488401bf628a3344200feb4ab19a21007f6a5588910803fb92aaa288401bfa28e2244200dfd14b11221007f7165545108027fc5d2a488401bfc69e1144200dfe34508a21006ff1a384510803ef93bc22884013fe2e1a244200dfd347112210057f8b954510802ff8d88a6884017fc6c43244200bf736819221004ff8ba8cd108037f454444884015fe2e622442009ff17511221006fd8ba8cd108037ed55466884017de6d43244200bfe576a8a21007bea8888910803bf85caa288401bfcaa95144200aff17298a21006feaaa88910803bf45cc4488401f7c9dd5144200dfd17511221005df8b754910802bfc5cb02884013fe6e96244200dfb34719a21006ff1a8545108037f4d4444884013fe2cda244200dfe34ea8a21006fda3368910803df9442a2884013fe6e85344200fde4cca8a21007eea6688910802f7cdb0a488401bfa68a2244200dfd34d11221006fd9a78cd10802dfcdc064884017fc6c45244200fdb4cd19a21006fe9a5889108027fc5ab4488401f769de3344200dfb34d19a21005fb9b4149108027fc5d30488401bde955a244200aff17290a21006fd8a88cd108027fcdd30488401bfa69e2244200dfb35119a21004ff9ba14910802f7cdb06488401f7a9de2244200bbf36e19221007fca3388910803ff1112a2884013fe6e97244200f7b5 else 0xe9dda648200dff350d3241005ffabb699208037fd5534c90401dfe2e5a648200bff36c19221006ff98769920803dfd4406488401bfe6983244200bff16ad3241005ff8b369920803ff858b4c90401bfe69d214c200dff174b8a61005ff9ba5c5308037fd552e298401bfe6958144200ffd44440a61005ff9b2205308037fcdd2e2984017feaed714c200dff34cb8a61007df9875c530803f7d332e298401f7e5d9714c200bff170b8a61005ff9b85c530803dfd442e298401bfe2a1714c200ffb466c0a21005ff9ba20530802ffcdb90298401bfeaa8814c200dff144c0a61005ff8b260530803ff51130298401efe609814c200bff36640a61005ff8b360510803fed1990298401fde9558144200dff34e40a61006ff9a360510802ffcda90298401f7e9dc814c200eff172a8a61006ffaaa54530802ffcdb2a298401bfe69d8144200dff374a8a61005ffabb54530803efd3bb02884017fe6e9514c200dff144a8a61005ff8b254530803ff8c0aa298401ffa889514c200fdf4cca8a61006ff9a654530803fed19aa298401ff66cd514c200bff370b0a61006ffaaa58530802ffcdbac298401efea21614c200fbf2e4b8a61007fda335c530802ffcdd2c298401ffa889714c200fdf2c4b0a61006ff8a258530803ff8c0ac298401ffa889614c200fbf4eeb0a61006ff9a758530803fed19ac298401bfe295614c200bff170b8a21007fe98788930802ffcdc2e288401ffa69a224c200f7f510b8a21007fea88889308037fcd42e288401ffa69e224c200ffd2e711261007fe98388930803ff458c4498401ffa58e224c200ffd2ed11261007fe98688930802ffd5dae288401ffa2d6224c200fdf4cd11261006ff9a6889308037fc52c44984017fe2d6224c200bff166b8a21006ffaaa889308037fc54444984017fe2e2224c200ffd17111261006ff9a55c510803efcc3ae288401ffa6a2224c200ffd2c511261007fe9a288930803fbd2aae2884017fe2c6224c200f7f510c0a61006ffaaa60530803efd3bb0298401bfe69d814c200bff374c0a61006ff9ba60530803dfcc130288401bfe2e9814c200bff16ac0a61007efa6660530803fed19b0298401bfe295814c200dff344c0a21007ef8b660530803dfcc330298401bfe699814c200f7f510d0a61006ff9a868530803efd3bb4298401bfe69da14c200bff576d0a61007fea2260510802ffc5c34298401dfe2e5a14c200dff344d0a61005ff8b268530802ffd5db0298401ffa889a14c200fdf4ccd0a61006ff9a6685308037fcd2b42984017fe2d5a14c200ffe2e2a8a61007fdabb4c530803fec4126298401ff65c9314c200ffe30298a61007fd9624c530803fecdc26298401ff62c9314c200ffd46711221007fd9824c530803fecd126298401ff6549314c200ffb44498a61007fd9634c53) else (if i<6 then 0x221007fd95308530803ff442c4488401ffa5962244200bff36a10a61007fe97588910803ff4d1c44884017fe6d5214c200bff16a90a61006ff8a548530803f7d3324298401f7e9dd214c200bff36c90a61006ff9a648530803ff8b8a4298401ffc4c5214c200ffb26290a61007fe96248530802ffcd9a4298401ff654d214c200ffb46690a61007ff28884530803ff4bb44488401ffc69e114c200ffe35108a61007fe9a588910803ff45ac4488401ffc2e2114c200ffe2ed08a61007fe98788910803ff85ac2298401ffc61a114c200ffd30d11221007ff18784530803ff8d342298401ffc5c6114c200f7f51108a61006ff9a784530803efd3bc2298401bfe2a2114c200ffb46610a61006ffaaa84530802ffc5c42298401ffa88a114c200ffe34308a61007ff18184530802ffc59422984017fe2d6114c200ffb2a708a61007fda3384530803dfd4434a90401f7e2dda548200bff36a99221006ff8a869520803bfc5cb4a904017fe2e1a548200dff350d2a41005ff8b369520802ffcdc14a90401bfe6a0a548200fdf4ccd2a41006ff9a769520803efd3bb4a90401bfe699a548200dff554d2a41007ef9a899920803fecb9a6488401bfe68d3244200ffb46699221007df9875d9208037fc51aec90401fbeaaa6648200dff34a99221005ff8b54c910802ffd5db4a90401bfe2953244200fdf34f33241007f7a554c910803f7cc3ccc904017fe2cd8548200dff146c2a41005ff8b161520803f7d3330a90401efe61d8548200fbf4eec2a41006ff9a661520802ffcdba6488401efea213244200dff15099221006ffaaa215208037fc50b0a904017fe6e88548200dff34e99221006ff9a761520803f7d3314a90401bfe6993244200bff36c99221006ff9a629520803dfd4414a904017fe6d8a548200fdf4cc99221005ff8ba61520803efd3ba6488401bfeaa98548200bff374c2a41005ff9b329520802ffd5db0a90401bfe6e98548200f7f510bb241007bfa8861d20802ffc59b0e90401bfe28d8748200fef4aa19221005ffabb61d20802ffcdd30e90401bfe2e98748200fbf5113ba41005ff9b50c910803f7d3306488401bfe6943244200bff162c3a41006ff8a161d20803efcd44ee90401bfea21a748200f7f55544241006ff9a688910803dfc5ad1090401fbe99a2244200bff16344241006ff8a1a2120803dfc5d510904017fe2e22244200dff350d3a41007bfa8869d20803dfc58d1090401efea222244200f7f16744241006ff9a888910803ff4c126488401bfeaa98648200dff34ec3241005ff9ba619208037fcd406488401bfe2cda648200bff37019221006ff9a24c910802ffcdc2ec90401bfe6a17648200bff374bb241007dfa77619208037fc52b0c90401bfe28d8648200dff16ad3241007bfa88699208037fcd3b4c90401f7 else 0xff8b12a288401efea203258200ffe064a8a21005ff9b80c960803ff8992a2884017fe6c43258200ffe104a8a21007ff18254510803ff8b92a288401bfe2943258200fdf2ca192c1007f7a550c960802ffcdd064b0401bfe69d3258200fbf4ee992c1005ff9b54c960802ffcdba64b0401ffc8895144200bff370992c1007bfa884c960803fecb9a64b0401fbe58d3258200ffd304992c1007f7a554c960802ffc5aa64b0401bfe2953258200fdf2ca992c1006ff8ba54960803fecbac66b0401bfe69d3144200ffb4ab19ac1007fd9858cd60803fec5ac66b0401ff66963358200fbf4ee98a21007dfa7768960802ffc5ab44b0401fde955a258200dff35098a21005ff9b74c510803fec59466b0401efea213144200bff36a98a21007fd9738cd608037fcd1262884017fe2ca3358200ffb34719ac1006ff8a58cd60803f7cb2c66b0401fde9563358200ffb34f19ac1006ff9a54c510803fecc3c66b0401fde9553144200dff14519ac1007fda334c510803fecd4466b04017fe2cda258200f7f510b92c1007ef9655c960803fbd2aae4b04017fe6e17258200fdf2c6c12c1007fda3360960802ffcdd2e4b04017feaed5258200dff374a92c1005ff9ba54960803fed19ae4b0401bfe28d7258200fbf2e6b92c1007ef9635c960803dfcc1b04b04017fe2e13144200dff34ec12c1007bf987609608037fc5d304b0401ff68cda258200bff576c12c1006ff9ba60960803fbd2ab04b04017fe2cd8258200dff146c12c1007ef96560960803efd3bb04b04017fe2d58258200dff14ac12c1007ff13284530803ff91142298401ffa6a22244200ffe0a508a61007ff17284530803ff8b142298401ffc54a114c200dff17155241006ff8b5aa920803ff49944488401ffa2e22244200bff17155241005ff8b5aa920802ffc59d5490401ffc20a114c200ffe4ab08a61007fe9a788910803ff8c1c2298401ffc596114c200ffe30b08a61007ff08584530803ff8bac2298401ffc2ca114c200ffe34508a61007ff18284530803ff54444488401ffc5ce114c200ffe2c708a61007ff153845308037fcd2c44884017fe6d4a848200bff36654241007f7a5588910802ffc59c4488401bfe6c5a848200dff162d4241005ff8b5a2120802ffc59d1090401bfe28e8848200f7f35144241005ff8baa2120802ffc5ac4488401bfeaaa8848200dff166d4241005ffabb6a1208037fd5535090401dfe2e5a848200ffd30511221007fe952889108037fc59d5490401ffa58a2244200dff34711221006ff9b66a1208037fcd9b5090401ff68ce2244200bff16ad4241005ff8b36a1208037fd5db5090401ffc696114c200dff15010a61007bfa8808530803ff52ac44884017fe6e0214c200bff37410a61007fe8b3889108037fd55042984017fe6cc214c200ffd30b11))) else (if i<10 then (if i<8 then 0x764c200ffb466a8a21007bfa8888960803f7cc3ac6b0401efea212144200fdf16ab1ac1005ff9b748510803fbd2aae6b0401f7e9dd2144200dff34e90a21007ef98358d60802ffcdc24288401fbe5cd6358200dff35090a21007ef98558d60803f7cbaac6b0401fbe9556358200fdf2cab9ac1005ff8b260d608037fc51306b04017feaed7358200fef4aac1ac1005ff8b560d608037fc52b06b0401fbe5958358200bff370b9ac1007bfa885cd60803efcc3ae6b04017fe6d52144200dff374b9ac1005ff9ba5cd608037fc5d2e6b0401fbe2c96358200bff37029ac1007bfa8814d60803ff51126288401ffc6053144200bff164a9ac1006ff8a254d60802ffcdd0a6b0401efea223358200dff34f19ac1007dfa778cd60803fec99262884017fe6c85358200dff14429ac1005ff9b114d60803f7cb1aa6b04017fe6e15358200f7f510a9ac1005ff9b754d608037fc5d2a6b04017feaed5358200dff374a9ac1005ff9ba54d60803f7cb2aa6b0401ff660d5358200ffb2e6a9ac1007f798554d60803efd3baa6b0401fbe6d95358200ffe2a298a21007dfa7760d608037fc51b0ab04017fe2c98558200dff144c2ac1005ff8b361560803ff919c2288401efe61d8558200fbf4eec2ac1006ff8a35d560803ff8b9c2288401ffc20e1144200fbf30ebaac1005ff9ba5d560802ffcdc2eab0401efea217558200dff374c2ac1006ff9ba61d60803ff8b9422884017fe2cd8758200bff576c3ac1007fd9538cd20803ff89942288401ffc54a1144200bff166d2ac1005ff8b269560802ffd5db0ab0401f7e9dda558200dff146c3ac1007df9a89dd60803ff8c142288401ffc60e1144200fef1652aac1005ff9b348510803fbd2aa4288401bfe68d2144200fef30f2aac1007fda3348510803fbc59caab04017feaed8358200dff374c1ac1006ff9a548510802ffc59346b0401f7e9dda358200bff16ad1ac1007f7a5568d60803fbcd3caab0401efea225558200fef34b2aac1007ff13148510803f7c592cab0401fbe61d6558200fdf30ab2ac1007ef8b359560803ff8a8a4288401fde6a25558200ffe2e290a21006ff8a295560802ffc59caab0401bfe28e5558200bff1652aac1005ff8b58cd60803dfd440a4b04017feaed3144200bff366292c1005ff9b814960803ff4b92a4b04017fe6e85258200eff17298a21005ffabb4c9608037fcdd264b04017fe6e93258200bff362292c1006ff8a314960803f7cb18a4b0401ff68cc5258200ffd304a92c1007df8b7549608037fcd3aa4b0401f7e9dd5258200bff36ea92c1005ff9b84c510802ffcdc2a4b0401efea215258200fdf2c6a92c1007f795354960803fed19aa4b0401bfe28d5258200fef2eaa92c1007ef96554960802ffc59aa4b0401bfe2e93258200ffe2a4a8a21005ff9b50c960803 else (if i<9 then 0x7fe9a788960803ff4c3c44b0401ffa6a22258200ffb467112c1007fe9a288960803ff8d12a288401ffa54e2258200fbf2e4b8ac1007fea225c560803f7cc3ac2b0401ff68cd7158200fef4aab8ac1005ff8b35c560803f7cb1ae2b0401fbe60d6158200fdf2e6b0ac1007ef95358560803ff8b2aa288401fbe6156158200fdf2eab0ac1007efa5558560803f7cb2ae2b0401fde9558158200ffb466c0ac1007bf98260560803efd3bb02b0401ffa14e2258200ffd467112c1007ff1a354510803dfd442e2b0401ffc6cd5144200fbf30eb8ac1005ff9b85c560803ff511302b04017feaed7158200dff374b8ac1005ff8b3485608037fd55104984017fe6cc824c200bff36241261007df9725c510802ffc58b0498401bfe285824c200bff37441261007efa665c930803efcb9ae498401bfe285724c200dff34cb9261005ff9ba5c9308037fd552e498401bfe2a1724c200ffd444b8a21005ff8b568930802ffc58b44984017feaed824c200fdf4ccd1261006ff9a768930803efd3bb4498401bfe699a24c200dff34cc1261007efa6660930803fec59b0498401bfeaa9824c200dff374c1261005ff9ba609308037fc5d304984017feaed624c200dff34e99261007dfa774c930802ffcdb264984017fe6dd324c200ffb466b8a21005ff9b84c930802ffc5c26498401ffa609324c200bff16299261006ff9a35c510803fecb9a6498401bfe699324c200fdf4cc99261005ff8b54c930802ffd5da6498401bfeaa9624c200bff370b1261005ff9b7589308037fcd12e288401bfe6e9624c200bff374b1261006ff8ba589308037fc52ac498401fbe58d624c200ffd304b1261005ff8b5589308037fcd3ac498401f7e9dd624c200fdf2ecb1261006ff9a868930803ff8a9422b0401ffc14a1158200ffe26508ac1007ff17284560803ff919c22b0401ffc6a15144200ffe30508ac10077f8b9699308037fcd3b4c984017fe2d5a64c200bff576d3261007ff03284560803ff911422b0401ffc6e15144200ffe0a708ac1007ff1a754510803ff8c3c22b0401ffc6dd5144200ffe26290ac1007ef96348560803fed19a42b0401ffc5c52158200ffe30708ac1007ff17384560803ff8a9c22b0401ffca215144200ffe30b08ac1007ff17584560803ff92ac22b04017fe2c9a64c200fbf4eeb1a61005ff8b558d30803fecb9ac698401bfe69d634c200bff576b1a61007bfa8854510802ffcdbac6984017feaeda24c200eff172d1261005ff8b868930802ffcdc2a2884017fe2c9634c200dff350a8a21007fd9768cd30802ffcdbaa288401bfe2c9a64c200fef2a4a8a21005ff9ba5d930803ff5112a288401ffc5c55144200ffe302a8a21006ff8b5699308037fcd1aa288401f7e9dd5144200dff34ea8a21007ef9a7999308037fcd12a288401bfeaa9 else 0x942290401bfe68da244200dff34ed1221006ffabb6a1108037fcd434488401bfe6dda844200bff166d4221007bfa8868910802ffd5db5088401dfe2e5a844200dff2ecd1221007fe88548520803ff4baa4290401ffa5952148200ffd30a90a41006ff98368910803ff4daa4290401ffa6952148200ffd4aa90a41007fe88348520803ff4b9a4290401ffa58d2148200ffd30690a41006ff9b368910803ff4d9a4290401ffa68d2148200ffd51090a41006ff96368910803ff4dba4290401ffa6a12148200dff0a6d1221006ff95368910803ff4dc24290401ffa69d2148200dff106d1221007fe98648520803ff4bb24290401ffa6992148200ffd30e90a41006ff97368910803ff4db242904017fe2ce1148200dff34708a41007fda3384520803fbd2ac2290401bfe69e1148200fbf4ef08a41005ff8b584520803ff4a942290401bfe6d5a244200ffe17108a41007ff1a884520803ff898c2290401ffc6061148200ffe2e308a41007ff15184520803ff4c0a4290401ffa5c52148200dff2cad1221006ffa5568910803ff4a9a4290401ffa14d2148200ffd46690a41007fe95148520802ffc5c42290401bfe6a21148200f7f51108a41006ff98568910803ff498a4290401bfe5d5a244200dff10ad1221005ff9b321520803f7cb2aa2b0401ffc6d95144200bff166a8ac1007ff186545108037fcd3aa2b0401f7e9dd5158200fdf36ca8ac1007fea2254560803ff8c0aa2b0401ffc5c55158200fef2a4a8ac1007ef96354560803fed19aa2b04017fe2c95158200bff36ea8ac1007ef95258560803f7c292c2b0401fbe4c96158200fdf2e4b0ac1007efa3358560803ff8c2aa288401fbe6096158200dff374a8ac1005ff9b854560803dfd442a2b04017feaed5158200fdf064b0ac1007efa2258560803ff8bb2a2884017feaed3158200bff37090ac1007bfa8848560802ffcdba42b0401bfe6e92158200ffd44498ac1007ff1814c560802ffd5da42b0401fbe5952158200fef4aa90ac1005ff9b348560802ffc5aa42b0401bfe69d2158200fbf4ee90ac1005ff9b548560803fec99262b0401bfe69d3158200fbf4ee98ac1007ef9b64c560802ffcdba62b0401bfe6e93158200bff37098ac1007bfa884c560803f7cb1a62b0401ffc61d5144200bff16498ac1007f7a554c560802ffcdaa62b04017fe2d53158200fdf2ca98ac1007ef85358560803ff4bac44b0401ffc58d5144200ffd4ab112c1007fe98588960803ff45ac44b0401ffa6962258200ffe2a6a8a21007fe98388960803ff4b9c44b0401ffc60d5144200ffe106a8a21007ff17354510803ff459c44b0401ffa68e2258200ffe466a8a21005ff8b3889608037fc51c44b0401fbe58e2258200fef4ab112c1005ff8b5889608037fc52c44b0401fbe5962258200ffe364a8a210)) else (if i<12 then (if i<11 then 0x200dff17498a41005ffabb4c5208037fcd18a290401ff68cc5148200dff174c1221006ffaaa4c520803dfd44262904017fe6dd3148200dff34e98a41006ff8a84c520802ffcdc262904017fe2e13148200dff35098a41005ff9b548520803fbd2aa42904017fe6cd2148200fdf4cc90a41007bfa8848520802ffcdb24290401bfe6992148200dff34690a41007fe932485208037fd19b4488401ffc4c52148200ffd2a490a41007fda3348520803ff4c124290401ffa5892148200dff35018a41007bfa880c520802ffcdb862904017fe6e03148200ffd44498a41007ff1814c5208037fcdd30488401bfe69c3148200ffd2a418a41005ff9b8485208037fcd4242904017feaed8244200fbf4ee18a41005ff9b50c520803fbd2a862904017fe6cc5148200f7f510c1221006ff8a558520803fbd2aac290401fbe6996148200bff36eb0a41006ff9a758520803efd3bac290401bfe68d6148200ffd444b0a41007ff18158520802ffd5daa290401ffa5496148200dff146b0a41007fda3358520803f7cb12c290401fde9557148200bff166b8a41006ff9a35c520803f7d332e290401f7e61d7148200dff34cb8a41007df9765c5208037fc51ae2904017fe6e16148200dff350b0a41007bfa88585208037fd552c290401ff68cd7148200ffd2a4b8a41005ff9ba585208037fc51aa290401ff68cd5148200ffd364a8a41006ff9a354520803fbcd2aa290401fde5955148200bff166a8a41007fe95254520802ffcdc0a290401bfe6a05148200f7f51028a41007ff17154520803fbca92a290401bfeaa98244200ffe302a8a41005ff9b854520802ffc5c2a290401bfe6a15148200dff554a8a41006ff9ba54520802ffcdd2a290401bfe6a18244200dff150a8a41005ff9b6545208037fcd32a290401fbe9995148200fbf4eea8a41007bfa8854520802ffcdbaa290401bfe69d5148200ffe34708a41006ff9b868910803ff8c1c2290401ffc2ce1148200ffe2eb08a41007ff16584520803ff92ac2290401ffc20e1148200ffe46708a41007fda3368910803ff8c142290401ffc14e1148200ffe2e708a41007ff16384520803ff8a9c2290401ffc61e1148200dff30ed1221007ff1a684520803ff8d3c2290401bfe619a244200ffe51108a41006ff9b6689108037fcdbb4488401bfea21a244200ffe30b08a41007ff08584520803ff8d2c2290401ffc61a1148200ffe2ed08a41007ff0b584520803fed2ac6688401bfe6cda844200dff166d4221006ff8b56a1108037fcdb35088401ff62ca3344200dff36ad4221007fd9658cd108037fd5551088401efe6a28844200ffb30b19a21007fd8858cd108037fcd935088401bfe2c9a844200ffb2eb19a21007f7a55689108037fcd2b4488401f7e9dda244200ffe26508a41007ff16284520803ff8a else 0x9838cd108037fcdb34a88401f7ea227744200ffb35119a21007fd8b88cd10803fed44466884017fe2cd8744200dff146c3a21007df9a89dd108037fcc3b4c88401bfe6a17644200f7f510bb221007df9875d910802ffcdc2ec88401bfe69d8644200fbf4eec3221006ff8a28cd10802ffcda906884017fe2e15344200fef4aa41a21006ff9a854d108037fc542a688401bfe69c8344200fbf4ee41a21005ff9b854d10802ffd5dae688401bfe6e97344200bff374b9a21005ff9b120d10802ffcd910688401bfeaa95344200dff14441a21007efa6660d10802ffc5ab0688401bfe2958344200dff34cc1a21007bfa8860d108037fcd3b0688401f7e9dd8344200fef4aac1a21007bfa8854d108037fd55106884017fe6dc8344200bff37441a21006ff9a360d10802ffc5930688401bfe2898344200dff34eb1a21007dfa7758d10803f7cc32c6884017fe6dd6344200bff370b1a21006ff9a858d10803dfd442c6884017fe2d56344200bff164b1a21005ffabb54d108037fcdd2a688401ff660d6344200dff34ab1a21007f7a5558d108037fcd1ac6884017fe2e17344200dff350b9a21006ff8a85cd10802ffcdc2e688401bfe2e95344200dff174b9a21006ffaaa5cd10803dfd442e688401bfe68d7344200bff576b1a21005ff9ba54d10803fbd2aae688401f7e61d7344200dff34cb9a21007efa665cd108037fcd4306884017fe2e1a344200dff350d1a21007bfa8868d10803bfc5cb4688401bfe2895344200bff164a9a21005ffabb68d108037fcd3b4688401ff65cd5344200ffb306a9a21006ff9b868d108037fd5db4688401f7e9dda344200dff34ad1a21007f7a5568d108037fcd30a688401fde69e5544200bff36c29a21007f7a8895510803fbcd44aa884017fe6c85344200fdf4cc29a21007f798795510802ffcdc0a688401fde2ce5544200fef1652aa21007f797695510803dfd440a688401bfe6a05344200fef30d2aa21005ff9b654d108037fcd934688401bfe2c9a344200dff4aad1a21006ff88568d108037fcbab4688401bfe595a344200fbf4eea9a21006ff8ba60d10802ffcdbaa688401bfeaa98344200dff34ea9a21005ffabb60d108037fcdd306884017fe6e98344200dff36ed1a21006ff98768d10803fbcc2aa688401fde9555344200dff170d1a21006ff9a354d108037fd4434688401bfe6d9a344200dff16ad1a21006ff9a654d108037fcc2b4688401bfe6d5a344200dff30cd1a21006ff97668d10803f7d332a6884017fe6d53148200bff16a98a41006ff8a54c520803f7d3326290401f7e9dd3148200bff36c98a41006ff9a64c520803fbd2aa6290401ff68cd3148200ffd2a498a41007fd9324c520803fecb1a6290401ff668d3148200dff34698a41005ff9ba609108037fcdd262904017fe6e93148) else (if i<13 then 0x90401bfe69d5244200fef4aa41a41006ff9a654910802ffcda906904017fe6d95244200fef4aaa9221006ffaaa60d208037fcd3b06904017fe2e98348200bff374c1a41005ff8b3549108037fc5d30690401f7e9dd8348200fef4aac1a41006ff9a360d20802ffc58b0690401bfe2958348200dff34cc1a41007efa6660d20802ffc5ab06904017feaed6348200dff374b1a41005ff9ba58d208037fc50ae690401fde9557348200dff346b9a41005ff8b15cd208037fc542a4884017fe6e16348200dff350b1a41007bfa8858d208037fd552c690401bfe2e96348200bff174b1a41006ff9a854910803efc5baa4884017fe6dd5244200bff370b9a41005ff9ba5cd20802ffcd890690401bfe2848348200bff576b9a41005ff8b85cd20803efcc3ae690401bfe6997348200fdf4ccb9a41007bfa88549108037fc542e690401efea217348200fbf34eb9a41007dfa778cd10802ffcd990a88401bfe69e3344200dff34d19a21006ff8a261510802ffc5ac6688401fbe99a3344200bff36442a21005ff9b85d5108037fcd42ea88401bfe2a17544200dff554baa21007bfa888cd108037fc54466884017fe6e97544200dff34b19a21006ffaaa615108037fcd430a884017fe6e98544200dff14b19a21005ffabb615108037fcdd30a88401bfe69d8544200bff166c2a21006ff8a361510802ffc5930a88401fbe9998544200f7f30ec2a21007dfa77615108037fcd330a884017fe2e25544200dff3512aa21007bfa8895510802ffc5c46688401fde6156544200bff166b2a21005ff8b2595108037fcd34aa884017fe2ca5544200dff55519a21007f78b895510802ffc59caa88401fbe99a5544200fef30b2aa21007f7965955108037fc51aea884017feaed6544200dff35119a21007efa665d510803dfd442ea88401f7e61d7544200dff34cbaa21005ff9b859510803efd3baca88401fbe6196544200fdf2ecb2a21006ff9a7595108037fcd42ca88401efea216544200bff36eb2a21006ff9b2695108037fd4434e88401bfe2cda744200ffb30f19a21006ff8b869d10802ffc59b4e88401ff65da3344200ffb30d19a21005ffabb61d108037fd5530e88401bfe6a18744200f7f510c3a21007fd9a78cd108037fcdd30e884017fe6e98744200dff174c3a21006ff8a2a2110803dfc5ad1088401ff66963344200bff16544221005ff8b5a2110802ffc59d1088401bfe28e8844200f7f16744221005ff8b869d108037fcd434e88401efea21a744200eff172d3a21007fd8b58cd10803dfc59510884017feaeda744200ffb2e719a21006ff9a869510803dfd4434a88401fbe61e6644200bff16519a21007fd9538cd10803fecb1c6688401bfe69da544200ffb34719a21006ff9b369510803fbd2ac6688401bfe5d9a544200fbf4eed2a21007fd else 0xff34c51a41006ff9a354910802ffd5db0690401bfe6e98348200fef4aa51a41007efa6628d20802ffcda94690401bfe694a348200dff36ad1a41006ff8b568d20803ff4c12a488401ffa5c95244200dff36cd1a41006ff98668d208037fcbb34690401bfe615a348200dff344a9221006ff9b168d208037fc58b4690401bfe955a348200dff10ad1a41006ff97568d208037fcb2b4690401fde61a5548200bff174b2a41006ffaaa4c9108037fd552ca90401bfe2e96548200bff576b2a41006ff9ba59520802ffcdd2ca904017fe6e16548200fdf34cb2a41007ef98659520803f7cbb2ca90401f7e9dd6548200f7f510b2a41005ff9b7595208037fcd3aca904017fe6c48548200bff37099221005ff9ba5d520802ffc5c26488401bfe6a13244200dff14642a41005ff9b221520802ffcdc2ea90401fbe9997548200dff146baa41006ff8a15d5208037fcd32ea90401bfe2a17548200f7f510baa41007df9875d520803fbc5c4aa90401fde6a25548200fef1512aa41006ff9ba4c910803fbc5d4aa904017fe6e93244200fef5552aa41005ffabb4c9108037fcd18a488401fde69a5548200bff36629221007f798795520803fbd444aa90401fde69e5548200ffb46629221006ff8ba4c9108037fd554aa904017fe2e25548200bff1752aa41007f798559520802ffc59aca90401bfe28d6548200f7f5112aa41005ff8b3955208037fc51caa904017fe2c65548200fef2cb2aa41006ff9a695520803f7d334aa90401fde6965548200dff150a9a41007bfa8854d20802ffcdbaa6904017fe2e15348200bff370a9221006ffaaa54d20802ffcdc2a690401bfe69d5348200fef30aa9a41007f7a5554d208037fcd1aa690401fbe9995348200fbf4eea9a41005ff9b654d208037fcd32a690401fbe6196348200bff16ab1a41006ff8a558d20802ffc5c2a488401bfe69d6348200fbf4eeb1a41007ef9a658d20803fbd2aac6904017fe6e95348200dff174a9a41005ff8ba54d208037fcdd2a690401bfe68d6348200ffb306b1a41005ffabb54d208037fc5446690401efea223348200dff34f19a41006ff9a88cd208037fc5d2a488401bfeaaa3348200bff17119a41007dfa778cd20803fbd2ac6690401ff668e3348200ffb2e719a41006ff8a58cd208037fcd346690401fbe99a3348200bff16b19a41005ff9ba14d208037fd552a488401bfeaa85348200dff142a9a41007fd98354d20803fecb9aa6904017fe2c55348200bff37029a41005ff9b214d20802ffcd88a6904017fe2ea3348200fdf4cc29a41007bfa8814d20802ffcdb0a690401bfe6985348200bff36eb1a41005ff9b720d20803f7d332a488401bfe69c8348200dff55441a41006ff8a160d20802ffcdd10690401fde5d55244200fbf4ee41a41007dfa7754910802ffcd9106)))) else (if i<21 then (if i<17 then (if i<15 then 0x5208037fcd430290401fde9558244200f7f510c0a41006ff9a660520803fbd2ab02904017fe2cd8148200dff346c0a41006ff8a560520803dfcc330290401fbe9998148200bff16ac0a41006ff9a328520803fed1994290401ffa548a148200dff146c1221007f7a5528520803dfcc1b04884017fe6cca148200dff346c1221005ff8b3609108037fd5530290401efe6a18148200dff174c0a41005ffabb605208037fcdd302904017fe6e98148200ffd2a440a41005ffabb5c520802ffcdd2e290401f7e9dd8244200bff36640a41006ff9a320520803fed1990290401efe61d8244200f7f510b8a41007df9a75c5208037fcd3b0488401bfe2a17148200bff370b8a41005ff8b85c5208037fcd42e290401ffa8898148200ffe142c0a41006ff9a560910803ff4a930290401bfe28d8148200ffb466c0a41007bf98260520802ffc5ab04884017fe6d48148200fef4aa40a41006ff9a660910803efd3b902904017fe6dc8148200fdf4ccc1221006ff9a7205208037fcd294290401fde9553248200bff370b9221007fe9824c9208037fc52a6490401fbe9993248200bff36a99241005ff8b54c920803ff4a9264904017fe6e97244200ffd34d11241007fda3320910803ff54444490401bfe2853248200ffd35111241006ffaaa5c910803ff4d8aa490401ffa2c55248200bff57699241006ff8a85c910803ff4a9aa490401efea217244200ffd466a9241006ff9a85c910803dfd44264904017fe6d93248200dff34c99241006ff8a84c920802ffcdc264904017fe2e13248200dff35099241007f7a55685208037fcd1b4290401ff68cda148200dff34ad0a41007dfa77685208037fcd334290401fbe999a148200ffd2a4d0a41006ff9a260910802ffcda94290401ff68cd8244200f7f51050a41005ff9b828520802ffcda90488401bfe6a0a148200ffd30711241007fe88388920803ff4b1c44904017fe6cc8244200ffd30d11241006ff9a320910803ff4d1c4490401ffa54e2248200dff350d0a41007bfa88685208037fcd3b4290401bfe6948244200ffd0a711241007fea3388920803fbd2a90488401fde955a348200dff576d1a41005ff9b6149108037fc52b4690401fbe999a348200bff16ad1a41006ff9a568d20803dfd440a4884017fe6e05244200dff36ed1a41006ff98768d208037fd4434690401bfe6e1a348200dff170d1a41006ff9a814910803fbc58caa904017feaeda348200dff554d1a41006ff9a614910803fbcbb4aa90401fde2ce5548200fdf4cc292210077f8b968d208037fcd3b4690401f7e9dda348200dff34cd1a41007bfa8868d20802ffc5c34690401bfe6a1a348200dff150d1a41007f795354910802ffcdb14690401bfe28d5244200f7f51051a41007fda3354910802ffcdc14690401bfe6a0a348200d else (if i<16 then 0xe586dd86d586cd86b506ad06948687066e864b062d060f05f685ee85e105d905bb05a805a0058d0574856c85598551852e051004f204d984c104ae0495847d0464844c0444043104290416040303ea83d783c483bc83b4839c038e837b83688350033d032a0317030982f682e382d082bd82b002a802a00292828a8277826a0257023e822b8218820581f281df81cc81bf01a6819901860173016001580150013781248111810980f680de00d600b800a50092008a0066805e8056804e803600230010000800006ff9a3549208037fc51aa490401fde54d5248200bff166a9241007efa66549208037fcd42c488401fde9555248200ffb466a9241005ff9b858910803ff5552a4904017feaed6244200ffd576a9241007fe98254920803ff4b12a490401bfe2855248200fdf2c6b1241007fda3358920803ff4c12c490401bfe28d6248200fef4aab1241005ff8b3589208037fcd1ac4904017feaed5248200f7f510a9241005ff9b6549208037fcd32a490401bfe2a15248200f7f510b1221005ff9b854920802ffc5c2a490401fbe9997244200ffd2caa9241006ff9a65c910803ff4c2aa490401ffa5d95248200fef4aab9221006ff9a55c910803ff4d9aa490401ffa20d5248200ffd2e6a9241007fe96354920803ff4c1aa490401ffa2cd5248200ffd346a9241007fe8a354920803ff5442a490401ff68cd7244200ffd36ea9241007fe8a854920803ff4dc2a490401ffa2e15248200ffd350a9241007df9735c910803ff4db2a490401ffa6995248200ffd30ca9241006ff9a35c910803ff4d3aa490401bfe28d7244200ffd30ea9241007ef96558920802ffc59ac488401ff669a3348200fef4aab1221007fd9878cd20803f7cb1ac488401ff669e3348200dff346b1221007fd9868cd20803fec52c6690401bfe6956244200ffb30b19a41007fd9a58cd20803fecbb46690401fbe5956244200ffb16b19a41007fd8ba8cd208037fcdd2a488401ff6aaa3348200dff14319a41007fd9638cd20802ffcdd2a4884017fe2c63348200bff576a9221007fd8a88cd20803fed19ac488401ff6a223348200dff344b1221007fe98258910803fec5c46690401ff66a23348200dff146c1241007bf98360920803fed19b0490401bfe68d8248200dff14ac1241007f7a5560920802ffc59b0490401bfe2858248200f7f510b1241005ff8b5589208037fc52ac490401bfe6a16248200bff576b1241005ff9b758910802ffcdc2c4904017fe2d56244200ffb16319a41007ef97658910803fed2ac6690401ff62163348200ffb2eb19a41007fd9658cd20802ffd5db0490401bfe6998248200fdf4ccc1241005ff8b560920803dfd4430490401dfe2e58248200fbf4eeb1221006ff9a758910803efd3bb0290401fbe2d98148200dff14ac1221006ff9a76 else 0xd628ce28c628be28b0a8a8a8a0a898a88b28832880a8732870a868a860a858a850a848a840a838a830a828a820a818a810a7fda7f027e827daa7c7a7bfa7b7a79f2797278f27872779a771a764275c27542746a73927312723a716270e270626fe26f626ee26e626de26cb26c326bb26a8268fa67ca66f265c26492641262e2626260da5faa5f2a5eaa5dd25c4a5bca5a9a591257e2576255da5452537a52fa527a51fa517a4ff24f1a4d3a4c624be24ab249824852472245f2457244f243c2434242c241ea40ba3fe23e5a3cd23bfa3aca399a386a379236ba363a35ba348a335a3282315230d22ffa2e722cea2bba2b3a2a6228da27aa26d2249a236a223a216220321fb21d7a1ca21b721af219c2194218c21792166214da13aa1222109a0f6a0de20c5a0b2a094a081a074206c20642040a022a0049fec1fd39fbb1fa29f9a9f821f7a1f619f491f411f391f311f189f001ef81edf9ecc9eb41ea11e889e7b1e629e5a9e3c9e191e061df31deb1de31dbf9da19d839d7b9d739d6b9d639d561d489d3b1d229d0a1d021cef1cdc1cc91cb09c981c7f9c671c541c3b9c339c101bec9be49bd19bc41bbc1ba91b961b8e1b7b1b629b4a1b2c1b191b009ae81ad51abc9ab49aa19a891a761a5d9a451a2c9a0e99f619ee19d599bd19a49991998999819979997199591951193e1936192e191b190d990598fd98ea98c718b418ac18a4188b9883987b9863185b1848181f17f617d817d017c817a49781176e176097589745973d971a171216f416e116d916bb169d167f166c1664165c1654164c16289615960295ea15e215c995c195ae95a6958e1570156815601558155015481540151c950414fc14f414ec14c894a514921479946c1448942a9422941a941293f493d113b313a01377136f1367135f1357134f1341932e9326931e9316930912f092e892d592c292aa12a2129a12871269126112591251122d922011fc91f491d111ad91a01192917f91671159915191339110110810e490c690b910a61098908b107d9070106290551047903a102c901f10118ff90ff10fe90fe10fd90fcb8fc38fa00f980f900f880f800f678f5f8f470f3f0f2c0f240f0b8ee80ee00ec20eba0eb20eaa0e970e790e710e690e560e430e300e178e0a0df18de40ddc0dce8dc10da88d9b0d880d750d620d4f0d368d2e8d268d0e0d008ce80ccf8cc78cb48c9c0c890c760c5d8c558c4d8c3a8c220c0f0c070bf40bd60bc88bb58ba28b950b878b7f8b778b598b3b8b1d8aff8aec8ae48ad18abe8ab68aa38a9b8a7d8a650a470a2e8a1609fd89f009dd09d509cd09c509b209a48997098409660958894009380930091d090f890788f488e188ce88bb88a88890087d086a085708440820880d87f507e207da07cc87bf07ac07938780876d875a8747872f0711070906)) else (if i<19 then (if i<18 then 0xc7bbbfbbb23baa3ba23b9a3b923b8a3b823b7a3b723b64bb5cbb54bb4cbb44bb3cbb34bb2cbb24bb1cbb14bb0cbb04bafcbaf4baecbaea3ae23ad4baccbaca3ac23aba3ab7baafbaa7ba9fba97ba8fba823a7a3a723a5f3a573a443a3c3a2eba26ba1eba16ba0eba06b9f939f139e939e6b9deb9d6b9ceb9c6b9c439bc39b439ac39a9b9a1b999b991b989b981b979b96c39643956b94eb9413933b92bb923b91bb913b90bb8fe38f638f3b8ebb8e3b8d638ce38c638b8b8b0b8a8b8a0b893388b387db875b86db865b85db855b84db8403838383038283820381838103808380037f837f037e837e037d837d037c837c037b837b037a837a0378d3785377d37753767b75a37523744b737372f3727371f3717370f370736ff36f736ef36e1b6d9b6cc36beb6b6b6aeb6a13699368bb67e3676366e3660b658b645b63db635b62db620361836103608360035f835f035edb5e5b5ddb5d5b5cdb5c035b2b5aab5a2b595358d35853577b56fb567b55a3552354a35423534b52cb51f3517350f3501b4f9b4ec34deb4dc34d434c6b4b934abb4a3b49bb493b48bb483b47bb473b46bb45e3450b4433435b42db425b41db4103402b3fab3ed33dfb3d7b3cfb3c233b4b3b233aa339cb394b38cb384b37cb374b36cb364b35cb34f3341b339b331b324331c3314330c330432f6b2f432e6b2deb2d6b2ceb2c6b2beb2b6b2aeb2a6b2a4329c328eb286b279327132693261325eb256b24eb241323932313223b21bb213b2113209320131f931f131eeb1e6b1e431d6b1ceb1cc31c431b6b1aeb1a1319931913183b17bb16e3160b158b150b148b140b13e3136312e3126311e3116310e310630fe30f630e8b0db30d330cb30c330bb30b330a5b09db095b08db085b078306ab062b055304d3045303d30353027b01fb0123004aff72fef2fe72fdf2fd72fcf2fc1afb9afb1afa9afa1af99af8c2f842f7c2f742f6c2f642f5c2f4eaf46af392f2baf23af162f08aefb2ef32eeb2ee32ed5aec82ec02eb82eb02ea2ae952e87ae7fae77ae6a2e622e5a2e522e4a2e422e3a2e322e24ae172e09adfc2df42dec2de42ddc2dceadc6adb92dabada3ad9bad8e2d7b2d6dad65ad5dad55ad4dad402d32ad2aad22ad1aad12ad0aad02acf52ce7acdfacd7acca2cc22cba2cacac9f2c972c8f2c872c7f2c772c6f2c672c5f2c572c4f2c472c3f2c31ac242c1c2c0eac012bee2be0abd32bcb2bbdabb02ba2ab952b8d2b7fab722b6a2b622b5a2b4cab44ab3cab2f2b272b1f2b11ab09aaf6aaeeaae6aad92ad12ac92ac12ab92ab12aa92aa12a992a912a83aa7baa6e2a662a5e2a562a48aa40aa332a25aa12aa0529fd29efa9e7a9dfa9d7a9ca29c229ba29b229aa29a2298f2987297f2971a969a961a959a951a949a93c2934292c29242921a919a90c290428f128e3a8 else 0x9acf8d4f854f7d4f754f6d4f5fcf57cf4fcf424f3a4f37cf2fcf27cf1fcf17cf0fcf07ceffcef24ee4ced74ec44ebc4eb44eac4ea44e9c4e944e8c4e844e7c4e744e6c4e5ece5c4e59ce574e4f4e474e39ce31ce2f4e274e1f4e1cce14ce074df9cdf1cde44dd6cdc94dc6cdc44dbc4db44da6cd9ecd96cd8ecd814d73cd6bcd694d5bcd53cd4bcd43cd3bcd33cd2bcd23cd1bcd0e4d00ccf8cceb4cddccd04ccdccc04cb84cb04ca84ca04c984c8acc7d4c6fcc5ccc4f4c474c344c26cc1ecc16cc0ecc014bf94bf14be94be14bd94bd14bc94bbbcbae4ba64b9e4b964b8e4b864b78cb70cb634b5b4b534b4b4b3dcb35cb2dcb25cb184b0acb02cafacaed4ae54add4ad54acd4ac54ab7caaa4a9cca89ca81ca79ca71ca69ca61ca59ca4c4a444a3c4a2eca214a194a114a094a0149f949f149e949e149d3c9cbc9b8c9b0c9a3499b4993498b4983497b496dc965c95dc955c94dc9404938492ac922c91ac912c90ac902c8fac8f2c8eac8e2c8dac8d2c8c548b7c8aa48a24894c88cc87f4871c864485c48544846c839482bc81e4816480e480647f8c7f0c7e8c7e0c7d347c5c7b847aac7a2c79547824774c76cc764c757474f47474734472c4724471c470ec706c6fec6f6c6e946e146dec6d6c6cec6c6c6bec6b6c6aec6a6c69ec696c68ec686c67ec676c66ec666c65ec656c64ec6414633c631462946214619460bc5fe45f645e8c5e0c5d8c5d0c5c8c5c0c5b8c5b0c59dc595c58dc585c57dc575c568455ac547c53fc5324524c51cc50f450744ff44f1c4e444d6c4cec4c6c4bec4b144a3c496448e4480c4734465c45dc450444844404438442ac41d440a43fcc3ef43e743df43d743cf43c743bf43b743a9c39c43944386c37ec376c36ec3614359434bc33e43364328c320c313430b430342fb42f342eb42e342db42d342c5c2b842b0429d42954287c27fc277c26fc267c25fc2524244c237422f4221c219c20141f941ebc1e3c1dbc1d3c1c641be41b641a8c1a0c1934185c17dc175c16dc1604158414ac142c135412d411fc1124104c0f1c0e9c0d6c0cec0c6c0b940b140a3c096408e4080c073406b40584050403d402fc0224014c00cbfff3ff73fe9bfd6bfcebfc13fb3bfabbf9e3f9bbf8e3f863f78bf6b3f633f55bf483f403f383f303f283f203f183f103f083f003ef2beeabee83ee03ed83ed03ec83ec03eb2beaabea2be953e8d3e853e7d3e753e67be5fbe523e4a3e423e3a3e323e24be1cbe1a3e123e0a3e023dfa3df23de4bddcbdd4bdccbdca3dc23db4bdacbda4bd9cbd94bd8cbd7f3d773d69bd61bd59bd51bd49bd41bd343d2c3d243d1c3d143d0c3d043d01bcf9bcf1bce9bce1bcd9bccc3cc43cbc3cb43cac3ca43c9c3c8ebc813c73bc663c58bc50bc433c3b3c333c2b3c233c1b3c133c05bbf83beabbdd3bcfbb) else (if i<20 then 0xfd61f561ed61e561d7e1cfe1c7e1bfe1b7e1afe1a7e19fe197e18fe187e17fe177e16fe162615fe15d61556147e13a61326124e11ce114e10ce0ff60f760ef60e760df60d760cf60c760bf60b760b4e0b260aa60a2609a608ce084e077606f60676059e051e049e03c60346026e01ee016e00ee006dffedff6dfeedfe6dfdedfdc5fcedfc6dfb95fb15faedfa15f995f915f895f815f73df6bdf695f615f5edf5c5f545f4c5f445f3c5f345f2c5f245f21df19df175f0f5f075eff5ef75ee9dee1ded9ded1dec45eb6dea95ea15e93de8bde7e5e70de635e505e485e3ade2d5e255e17de0fde025dfa5df25de4dddcddd4ddc75db9ddb1dda45d96dd8edd86dd795d6bdd63dd565d48dd40dd335d2b5d185d15dd085d005cf2dceadce2dcd55cc7dcbfdcb7dcafdca7dc9fdc97dc955c92dc8adc82dc7adc6d5c6adc62dc5adc52dc4adc42dc355c27dc1fdc17dc0fdc07dc055bfd5bf55bed5be55bdd5bd55bc7dbba5bb25baa5b9cdb94db875b7f5b71db6f5b675b59db4c5b445b3c5b345b26db1edb16db095b015af95af15ae95adbdad3dacbdac3dabbdab3daa65a9e5a965a8e5a865a7e5a765a6e5a665a5e5a565a53da465a3e5a365a2e5a265a1e5a165a0e5a00d9f8d9eb59e359db59cdd9c5d9bdd9b5d9a859a059985990598859805972d965595d595559425934d921d914590c590458fc58f9d8f1d8e9d8e1d8d9d8d1d8c9d8bc58b9d8b1d8a9d8a1d899d891d889d881d879d871d869d861d859d851d844583c58345826d819580bd80957fbd7f3d7ebd7e3d7e157d3d7cbd7c3d7b657ae57a6579e579bd793d78bd783d77bd773d76bd763d75bd74e5740d733572b571dd715d70dd705d6fdd6f5d6e856e056d856cad6b7d6afd6a7d69fd697d68a5682567a5672566a5662565a564cd64a5642563fd63d563ad62d56255617d60fd607d5ffd5f7d5ea55e255d4d5c755b9d5a6d59ed596d58ed586d57ed576d569556155595551554955415539553155295526d519550bd503d50154f954f154e954e154d954d154c954bbd4b3d4abd49e5490d488d480d478d465d45dd450544854405438542ad422d41ad412d40ad408540053f853f053e853e053d853d053bd53b553ad53a55397d38fd387d385537d5375536d535fd357d34fd347d33a5332532a5322531a53125304d2fcd2f4d2ecd2e4d2dcd2cf52c1d2b9d2b1d2a9d2a1d299d291d289d27c5274526c52645256d24ed246d23ed236d22ed226d21ed216d20ed20151f951f151e951dbd1d3d1cbd1c3d1bbd1b3d1a65198d190d1835175d16851605152d145513d512fd11cd10f5101d0f450e6d0d950cbd0c3d0bbd0b3d0abd0a3d09bd093d08bd083d076506e5060d058d056504e50465038d02b5023501b5013500b50034ffb4ff34feb4fe34fd5cfcdcfc5cfbdcfb04fa84f else 0x991c11c8a1c361bc0f80c124d040b85619c468ec124714e22c3780703824ce32c3781c12a38ae32c3781c12a38be07c042ec12450a15040e840582295c678151d824be01c460918870f81c122a0760dc468ec12450e1f02a381d0d4305c5388b06e0747609338a711631c0e092b8a711e01c0e0928a51506201710260a53100b88118210cd184cd1c6201710260a53100b881334718805c4099a38c402e20850f81719824620c2108c68461f81f0182461084b60908c4084634230f0498808c310a1302113661c1e046260919c230e1181e0cc403008c308462818046204207811876164160918420781187617048b0484214030840f0230cc30460783314634230ec2e09101308130e0908c210a1c121081c0c1e0a01585c122a061181c282c124085824230c2318c07833140e8230c2103c08c3b0720b048c5408e07430742a042a304846084490582442a24103a18a811c0e872085460918830828083415023b04905408e0743b0720b048c1406c1c82c12370de0704c8e22860b8a710e0647609284207811861081e0461a8508a7710891c0c8ec12610c102c150e108de0647609238891d8247e07c002e188508810ecb66cae6ca66c9e6c90ec836c706c62ec556c47ec3a6c2cec1f6c11ec09ebfc6bf46bec6be46bdc6bd46bc6ebb3eba66b98eb90eb88eb7b6b6deb65eb5deb55eb4deb45eb3deb35eb2deb25eb1deb15eb0deb05eafdeaf5eaedeae5eaddead5eacdeac5eabdeab5eaadeaa5ea9dea95ea886a7aea72ea6aea5d6a556a4d6a456a3d6a356a2d6a256a1d6a156a0d6a0aea086a0069f869eae9dd69d569c7e9bfe9bd69b569ad69a569a2e99ae992e98ae982e97ae978697069686960695869506948694069386930692869206918690ae8fd68f568ed68dfe8d7e8cfe8c268ba68b7e8aa68a2689a6892688a6882687a686ce86a6862685a6852684a6847e83fe837e835682d6825681d6815680d680567fd67f567ed67e567dd67d567cd67c567bd67b567ad67a5679d6795678d67856777e76a6767e75fe7526744e73ce734e7276719e711e709e701e6f9e6f1e6e9e6e1e6d9e6d1e6cf66c1e6b9e6b1e6a46696e683e676666e66666658e650e648e640e638e630e623661b66136605e5f2e5e565dd65d565cd65bfe5b7e5afe5a2659a6592658a6582657a6572656a6562655a6552654a6542653fe532652fe527e51a65126504e4fce4f4e4ece4ea64e264da64d264ca64c7e4b4e4b264aa64a26494e481e47f64776474e4676459e446e439642be423e410e40363fb63f363eb63e363d5e3cde3bae3ad639fe397e38fe3826374e3676359e351e3446336e32ee326e313e300e2f362eb62e362db62d362cb62c362bb62b362b0e2a8e2a0e298e290e288e280e278e26b6263625b6253624b6243623b622de2206212e20ae1))) else (if i<24 then (if i<22 then 0xc0b8ba2b4468131c0b8ba2b4468131c0b8a638170a018190819082709800e8ad106081868107463040e8500cc103a140316b826408a020140d8390382450100c86c1e091403032116d826408a020c19152224083a28860a820a86081908140a860d8eb19a2ac06095106b0d207048a02019081908350c19915222c3481c12683322a44586903824d61b048a01e8ab198254410c623c1219128a2944281074671da2b44681074506a1504150c114fa234098e05c571ce32c5588317824d62ac4581f008b8b824540a01b8e71962ac4686317824e0d42a082a0c221422082e0a1e0a0ce0914031041106106a131c8b840d34318e412405c1f03e01170fc0e091503b1ce23436092287082e0e097030b86e07c00b54480b8a218205820b821302309531d824c419c343c1219514a21c3281c12650c1d15a22c138cd03824da2b44386b1da07049b0243c160914021400f0540f4558ec12a2086391e080c8745688d0382454150ca8a510e0d40e0932830b8cd15a20c728bc12671ce31c0609140587828042281e0a01b8087820782804e0e1e081e0a016048782c090f058121e081e0a0160914020782805824500ac1f8151d82482082218220c20703e011e091e04260a0439e0304988308608830887088208b1311e001e1010045078084982480703e07048a818860d8eb196011e12c758c70f6034560932870d8eb19e06c06092a820a860a830c18c122a0763ac6580711824a21c20742a3b048461842078118720823609184215b82447102303c178151d82423101e046108208a7078207828041085688ec12490582441181e0421d859058247616416091f80b158246e0ec568ec124506150c108ce0d41609228e078270d62b476092585711a3b04914387c058ac12371962b04a8e2388d1c0f07e03048a01b8cb158254711430443841f2090a03f010ba126092780711824620c2e23c003c1b8e719e05c06092d83478271da281d0fc0e091503b068f046311e094105430426780d0a620171426780d0a620171426780d0a6201714267801406201717c060914030381f03824540fc0f80c1231041f02e33048c0e0426780d0a6201714266853100b88133c00a03100b8ae1ec668ac12407a0ed048382781f018241c11c043c1388f000f06070220822183e03048a01b8087821250f042481e0a81b8cb10e006703c2b878782140623c003c2085081c0f80c1228066311e094387c0d8cc123071e011e0c1d18807033100e81c0cc403a07033186201803821880740e066201d038183a3100e06258c303a184c07025bc0986074608d824210c2304230c12c9e07c002e1a830e8205c208c2e45e07048a8184cd1c6201712c36091503b0d824500c2304219a3f01824500ec378151d8249619c1f81d1d824aa0c2e29c4586703a3b04994284138443842420 else (if i<23 then 0x38242638c68461d86f03e030493c0f80c12308d0f0433b048461f81f01824604c32141c6091a83098ec126202311c40ce0783038103a170d0f04e306718ec1240381f03e03048e0e485b078249e01c46091a820d86719a2b0492c138cd1582480e81c09430541841e040e05c00ad4580f080f023082303845de001e15c043c10870f81b1d82460ec1e03819860740e06638c6846198e31a11860702a1c263904846181c0a3c0f80478231c634230f048381387b1da2b04901d8384120f480f01c082802607c3f001191e0cc720908c390a0e846391e08c0041007c06091403f00890170c1c6091781b1d824621820e85409c3781f01824907242d83c1243186341c0c1e06c123c109e3040e81c10c760908c3b048f04e39c6586f02e030498c718d08c3c126381c0ec323c1781b1d824620c2e39c6586701a2b049ac323c118e0600e060703e05c660918130a870f81f018247e07048a81d86f03e0304930498e070313c638c6846238cd1463b0490c718d08c370d63b45609241c90b60f0493c0e09150370f61bc068ac125f03e01170cc522e10860a870b8e71962b43380c12671ce31c058ac125b0be01c4686c125071a18c703c2038d0c6381e101c68631c0f080e34318e078405c1070258c703c20300f8108d8242111c758ad0d8248a08221c220c3e0423609084491d8244904622830b88f01a181e13c0609140371962b436092609b0a8b868b943383c1243148b840e04b18e0784060108c0e343187078508c0e04af8030e0f0c254c383c1833d0c82460b820b82e29c458ed0ce070499c538870363b0495c6781d0c63b04954184c08417054286436091486078207828050ba43585c12408c8b943609202e0c2e90d82460fa468501a863140e861302318a074485d61643609242e90d617049217486b0b82480f9048501f8108d23825914185c658ab1160547609338cb15622c0e0951c650c11501181d0c1d04611800f80c122807e03048a018860e09150280762b47188c124b15e00c4609258ab11605476092e0908c30460e34118807440702a0c403a2583c1228061301c7810744104108c0a4210c1c0a83100e89824230c1183008c63025901c6823100e880e3411880744071a08181880745071a08c403a2083084cf00623049023609310108810b0498808c4b10a3b048d428543054184428423609f0210882183e07c060918850886084841211c60f02309428543060ce09140351ce32c40ce317824de03048a0182708860d8c711826471043844286c638891d8248a1c3824230c11b8e719a2b44586c12a2cee39c668ad1161b04a8b3e8ab0de0304a882a830a820e8ad11619c6609d026432a2944383503824c6181d0a01e091402032130c0e8500d1e045aa19514a214082e301908b5d15a04c702e298e05c28060643a2b4468131 else 0x122c121c12170782448e82e0b04891760916090b870e097002078145ca1b048ec1041a041a070258211860e040e04098309860a860801a04c186c3870206c3e0415870682042108c108c63840d028903826c109c087048702582118309860e040a2ec12250e1b058244e0c3824225b0489c306c12301182172206040e047062448e0458241c09c60513070484c18541870487048704844f6091609700245ca344118c2881e070487020517609160970e2716170182448bb04890e05c185c3e09138bc12202290e0971027101c1210781c12184c184c184c150e1c128c056151708c386130517609103c098209830e040a2e84c200aa3182c0810841050130e1c08130c10681c081018c08a83182702115010846202e00382420316150c1c08a085810260c38120889418547040e0026182a18261420700103811242700102870e04b06250a13062a0426c225c3811c08912051209e1046c082c08170214481c08102820e040834084c0e040d8b0d8009860a860e04b042137600560036002e1c211828903812c108c28542842105c387022821224b0427061b0489046142a14261c261c210ac00a4707023851604b04270d810560838103620362036043812c1084784230423044d86c5846758015880a830a86088f0d81098b08ceb0223101833604429c230813845389e10923162c096084890260c2618229ec0884de0915800e090a2e0c8a0702b0b824411b0488480704844f03c16090e09083c09870e090e090a870e04848212b8245825c00ac2a30128209820e090e090e04146230c1c128c05812120a13041e041c609158570182460e1048917070486450704841c60916048482c12150413041c121c121c12113d82448b946881c0704851758a16090c3c098ec12245d8245824382420f02a0820f030f030f030f030f02a0c261c3824322b0209c0e0915800e0970e29156004295c06091b80172245d82448983825c089c5e0916097102b0107048a43826c10b04d82128309830d800d8245c250e130e170f8245600307028bb048b048517096c123b00130a1c1262048b8382438243824382430702280260c382428bb04894186450461609083c08a00c2ec122c12185d8245825c00b04c1c8603c09090461c20c9048b0484c107048617609103c083c0e090983083a0c86b0b8107810381030ba468b020702070205c30702041760916040e04083c080c5070238016040c2e90d82460bb04881760911820e040e040a247022c0810781c08170d81058102005d82440c081706105c1c081c081c121c081c081c081c081c121c12185d21b048ec1a8d12870a86c12285d21b048f0487048617486b0b82480c828b8261c361e0e0a130423609160909870a2eb06290d824460c211b048a4303c10380e040e090e09082e0e090e0908a083862060f0)) else (if i<26 then (if i<25 then 0xc145e1c08130c150c1c081b04130615061c081c0815161d0215101b04114e89058101c081228233832283092450a1248a1186088a04829141c081c08104819141c081914113c228120e1206120450061205c18740b861038c122849228500f02045048a10a08482848184828856002618360917084ae091046c12231c130a150a112b824563b0488c728d12850d8ec12214b82448bac709438456d80118309850e090c2ec122c126384294c76091e0970221258245824382428b838243824381038243824c70b020b9160908a5c122b001c12130e185d23446143826c00b0498e16090c2ec1223061c082e448b8382438243600223c382436042a0c28b9468b04d811183089b31d82478243825c00b04861205c1061205c705c34241038048214109040d43824c588c18618419c1360490903091c10b0205c184c60450424118c0824089e04828481048e005090500a120612070206120a0138c0b8384823041c13604460c3824c58b04d81160419a290b8120e0f048704d82860302c130e1915810460832281c09c5e091604088fc122839214582432170241c198c088a071810623f048b0483814853182318170182440e028bac58a42e048383b0411118105073020b020456e041005698e118e088816a29158104618322823084960416040e040e0409820a820d800e8109830a830892c082d02102880e040e09088f0d800e0411e20981b061839810407026082a08223c3a06c30ac30740d86141c0e810a8208380a8130c2d02103800e040e810e09088f0a81306251017001510106040e040702d02150c13041504130c1838e184e002307408943060e060e054404478460e81158c0e8108900b8e098608b70820e060e04c304c10426046098c12860a880c1c0c1c0b820e040c1cc082c121184307408a0e6041386c08216a1c13a0440e0260830bc260c30bc2a2c3a06c1890c8941046038211f810424b020826070207020381288098e0a8209860a86098209830d820d868382d0210981700111e10641d021c12111e1448150c1c081b04151017001150103800c8ac082d02106040e810814305c004c604c30740841c18c168108240a88c09608781022d7026811e0408a7c082c081c081c0815061c081c09608423c226c20d0217001c081d02103800e040a88080c185418702045405c605c00740b831681083070624321839810433a1208c186120645070205c1060e60416040802304c1045aa2f12830e040e81b0c251610701d0218398104a08307302094404c306c7070206c7074084496041681088f0e810e81088f0d8e0a86098e0e040e81098708920b800e810c240e810e810e8109860a8608921118107a04260c2a0c28bb048b04b8212240b82c12271d8245824382420d020d021182e1c261c260c26182e0b0489148456b80122ec else 0x811c00f0206c00448070487020a016040a1c0a820a2409830a830a241242038008000b0c8704e003810500b0484c1054106c0861258111880c2413c28482784282c08a120a0b02330613041c081c121b021b02184960440f0261c36002a1c360038103600287020c13600427ac08b04840600289028902620261c20f0309820c813094104c1061741c160970027001c081c12185d073048e13070483814260d830b80089e070270e144810701b06100380b8608380b8b0d830d830b880a2413ce047824382428a42e0f04891d041e0418102e002870225cc60b020704851e05c060916090e0408380e090e090e0970e20781c1214481c121c121c12e204e2f048912070204c185418702070205c084c509e1604082e0e040e0408c2702108c1c1214481c121c121c081c08184c1c0960c5810211838102a384d89c00543870204c3870206476041482c082c081c0829c520b020853e04118a0e0908c208d8104e18211a41084760408c3905810581023085398a1585c082b0b81042944d882304230702070206c2870207020423070206c2e0410380d85c08208c102830d8a08a7314219c26c5628362830f03628262820e038102a183628229cc5085404c307048467604109b08ce13c2136e044a18360436283628211ac50b0204540453d8112860801c0704842305c084c3041c042307025831604b062150e00411b022821a1c0e040e0409870e0408460e040e0409880a870b81098a13c2000026c225c211b0488230401182e3020706170d8105811c30a0e04236041604706251d8104003800b8008a7702251c1710170e114ee0442b5c009c3841811c1882305c405c585c185c18704870205c18458b8116047042c081448e044872c388502241030238316040b820b8c0c1c083808ad31c208d810429dc0882360451c3c12118463822820e604182408c2700130c18381b0f07040802e2c38103810381038103810211b020b0204616040e040e040e040e040846c122c08108d82458102e0422b438102309c18702070204470421386c082c081c08114e62858102e00229c261830983812c28b025851380b0a251d812c28cc18702042305c384230423042318a104608380846314208d8104e042e0c38103810381020e0261c36143812c28b02042360403837181c08e0c5810209038102618381022784b8a120412061204500412380148a089e0482848130418481c081c081c081c081914109819141d021848280509050081c42416040c24c082c0818492284282120a120a014240e810c249142048280429e12084f02414240c24098308ce136284818481914113d228509245084502414249142c1218482805092450a0188a0482318130418492285090260c2278450241e040b8c0e040e817062d0217061432107060c5a0420c081c081c0817) else (if i<27 then 0x8c1841c06c2e0412241242b0b811c00c5689b12240d850842c082c081b001c0815061c08191d810460c381022b6c00853a1908c3c096084e1c2a1420d02872c70b0207020702096128709830d8e0e040d8e0e040e040b810a870e0409870c82083048461002304210ad118a08a7314208c108c106810604083408460e04081c3604904300460b880d82c12245c258258c011820084e005812c10b023839043c08e185812c10b048617096c12314e27858243824260c38243812c1081c0452b80c123c12e005825c38b04870487025821385c082c090b84258258ac1045438b1386c082448102c1085825c00c210a5c123c12e045824261c3824382438102e042a183810200681c08108c1c121c081c121c081c08e0440d021083824382438102e002e07048b04b88138bc122c12131c1185824382428a42e0f04891d070485c4041a050e06c0844a06c0844786c086c084c084c40454380100026c26304b881c604160408aab00230e1c08150c13062a0426c36302a182a1436302a1c363026302e1c20060909830e090e045042c081b058244e0420e022a1c009c38547070258216040a82b06230e10681b02130c150c1b06130c150c130a10381b062b0611506304a1c20136a38461c38102a08381026304b8b020418242003810b81098809830a8309870b80080c0841824381020d038243826c08ac08702054387025861380b0c2c0961842a03812c308c387025861604b0c212d8244295476041a830b81b0c2c09618460c2258c1890e070258312850e0408a8700230a1098130625840e302081a07025831604b0627021b061136a3842944d891206c36041586c08250a1c082584e00361b023801830209610a80d86c0824481098144827840e0c6094105c00702070484c307020400c12130a15061702248403061b02111e1c12150a191c2a058264708c2854386c086c084160422d420d038102e002e00226e470852e0916040a8508a5136230e11362385238323b02080a1c323b020847042158608380d860a24b0c25041306144961840e0360036302a1c2872c60ac3054386c006c3050e04c404c12240a83084c0e04089709860a8609820a240b800811209211870d830d8309870d81098609820a24b06230414396184e1c2618360d12081c041c0543044f58115860d8c0d8c098c0d8c0c2413c28496044620262c225cc658118a0b022848282c08e1209e10380b8708900804804c305c585c406c0050e04c4580101c00448051206c0054105c1850e04c104c184c3054305c304c384125801580081d08307062c08e085062c00800901c0a0e061204c1040891c088c60513041c60915860b8b098c081c085c3851205c385c384c305430512061209210a0b16214162c462030904f0ac406c40541042604c386c360416040a870d86c082b0d else 0x24760912860c8209860e0491c214160442a24118c1e0491c284827842081a085389e1482150211d8105811c0894284c0c82158109880a860d8109860e09b022c09208540f0248e148ec08291c150e1848280523b0208c386c704c186c70426070206c706c707020702045407020702070207048702070206c70455070207020702070204c707020702070206c7609108e318250c1150190460446182e0430902e0020902a3838242e203810360420038b08240830706230da08581038114109428418102614381020848170e1b021b02170e102860c820e040e090a830e0409860a850d8109830a830d810e0414e28482785810260c2e141809c005c18702383138c082c3e041188098809830e0408210c2408ce1362018a0a830b800988080c4045004061838242a0c26282628260c3824381038102a183810381020d038242618211821182280381038103810381022b44d8856d801002306c2e091585c0827001c08111c108426cc70943844d84c386c0042304c507020702054304181023)))))
def f2758l11 : Packing := (2443,4,7,12,4,16,0,f2758d11)
def f2758d12 (i : Nat) : Nat := (if i<1 then 0x467c193c64018245dc17345a0164455a14b451e13ec4ba12ac488116c4240fb43b60dd43660cbc3020b5429409c424e08341cc067c190051411803ac0a001cc046008c000ffe54920803ff96248200ffe68520803ff93248200ffe60920803ff95348200ffe58d20803ffa3348200ffe14d20803ff85148200ffe54520803ff83148200ffe4c520803ff96148200ffe60520803ff8a148200ffe5c520803ff88148200ffe69520803ff97648200ffe61520803ff8a548200ffe61920803ff9a748200ffea2120803ff9a648200ffe61d20803ff98348200ffe28d20803ff97348200ffe20d20803ff9a348200ffe5d520803ff88548200ffe95520803ff96548200ffe48520803ff97244200ffe20910803ff95244200ffe58910803ff98244200ffe14d10803ff95344200ffe68910803ffa3344200ffe54510803ff97144200ffe48510803ff93144200ffe60510803ff93244200ffe14910803ffa2244200ffe0c910803ff97644200ffe61910803ff98544200ffe69510803ff98744200ffe6a110803ffa1148200ffe69d10803ffa8844200ffe20d10803ff98344200ffe58d10803ff97344200ffe68d10803ff97544200ffe21510803ffa5544200ffe59510803ff8a848200ffe58d30803ff98358200ffe68930803ff97358200ffe54d60803ff9a64c200ffe5d930803ff9624c200ffe4c930803ffa224c200ffe68d60803ff9824c200ffe20930803ff9724c200ffe5c960803ff98258200ffe60560803ff95258200ffe0c960803ffa2258200ffe14960803ff93158200ffe48560803ff85358200ffe8cd60803ff97158200ffe68960803ff95158200ffe4c530803ff9a848200ffe14530803ff9614c200ffe54530803ff9a558200ffeaa920803ff98758200ffe84530803ff9a758200ffe08530803ff98558200ffe95560803ff97558200ffe20530803ff9814c200ffe68530803ff9a858200ffe48530803ff93258200ffe5c530803f7a5544200bfe28960803ff21144200ffc54510802ff8a544200bfe69d60803bfa8858200bfe28d60803fda3344200fbe58d60803ef96558200bfe28910802ff9a244200bfe29560803fda3358200bfe28d10802ff9a344200fde95560803dfa7758200ffa88910802ff9a544200bfe68d20802ff8a348200ff64c530803f7a5548200bfe28530803fe95248200bfe28930803fea224c200ff68cd20802ff8a548200efea2120802ff9a748200bfe2a120802ff9a848200bfeaa920803ff2114c200fbe99920803dfa7748200bfe69920802ff8a844200efea2110803ef96158200bfe6a110802ff9a744200bfe69910803efa6644200ffa88960803dfa7744200bfeaa910802ff8a148200fbe99930803fea2248200ff68cd30802ff9a64c200ffa48520803ff21148200bfeaa930803ff21158200 else (if i<2 then 0x8c46398c6003c20990e70142c12c4184c81380a15880b8d0e30ec370145412627988607800f0b0e30cc731945301049c460e3800f08c75141d0e046203a0e09c08741c0c9e62181e003c288504b102310b562a09623806042e3c324916b4570104910782781e002e2432c331cc65154441245a219a2a886198ca06093b1504b10c0f0017198e6318a622868258b3c5cc5310c750cc0c12725b81e02090b8a2345dc0d0d04b1c6e002f28071750cc731104944c11a8663a09620cc670343412c7158ca2a88a0609638d0c9254531d0491060f0a0143345510c131940c127a2a88812816382e34334551140c12c71a8aa2182a043a2915447001e1288e003c1d154430d4087458668aa2380a042e331cc6115443001e1b800f0a01d11c0078321b81e02090b8a2331147412413046a198a0e8ac47014307840e22ea198c62a093700179403e048e82446216f0c924c731945301049109118388bb80a183c34124589e501038812866383c296d0c925453190491078668aa22810e8ac7515445021d14460e204e028661c3c3c5cc2f0143311049b81e02090b890491024940411a2ea198e62a09343345510c331d40c1278b98e6318aa1980824f4531904c784208223071c007842142463038824a41844f6398ca2a882a0a022e094d150cf00504124418860d15c030d04c78522888204196188b282094114441020cb185041272082c751423412420c345511c030d40c131e1c860b0dc051504928aa2281632098f0d4531cc651112412459e8a63a098f08c65141c412461b81a3a09210c12182ee018a824bc0b07474124214241702c641242083437031731d04978161a8e8248418588a3a091b18217024bc124718870d1cc44123e044623a09250dc045cc541256058a6228e824a21319c0c1247158a62181a38a0824c438685e01888263c2c08447001e128ae01888248c7318c0514544126623800f06c47001e0e8aa228163a098f0d45300c731904c78611838e003c210a1a198162b808b988824fc088c47412482781e002e2314c4303433165041272398a11a0923154708d049381e002e1d11c007838fd63b48e6e3648cde3008afe292891e21a87661ac85d6152846e0ee828e07680fdffe7f1dfa47dddf547c9def07abde827955e0a774dd9c75e5d42742dcca729dc7a7135c166fa5bb26e3db586cfdb126b95aae6a2da54684d9dc66bd982655593c648d8e2632587e61458245fdd7b65dd57345bf56b25a1566258d5612576d5ae558d51853ad496512d40a4efd3744cf52fc4b652a2498522a47a51a8463d144440d0c2422d05e40ed0043f0cf823d7cf3c3c14ed83a84e7438cce10378cd84350cd16337cc943174c262f6cb9a2db4b402bfcab429a4a3c28b4a0027249ba256c91a242c8d421fc83420947f81fa479e1e3c7621c846d61aa else 0x118a8e0609238a53b14c430247412682446108c4b7024741251198823a09230cc1f034741256198a6228e606093409c0d1c17104c0e204e06826183a3c08c50742310460e18362a8e824d02314c688c41198662a8e824ac451c1e0c4661588a3a092c08210782310422b49b6318a8248e3c08c387823118311b81a3a092b18c531047412c5984c60d88a3a092c081d08c362a8e82588211d0488431328e825882314c451cc0c1251089b631888248e330cc451d0492041098d11882113652b19c0c12471c4c8128e6202e2b0c23703474125e048e0e861c409413101d144c0e381a083a2b06c53114730304988e824461b1945412c7118e8258811890e304c651504949e623800f090e30ec751504958c634381c38c33194541251183c1439c0514171085810380f084eb1cc63001e16041183c188c1c70102078511838283808103c3438c331d454125811820e8382702c74122312046398d1188c587826203c10990e30ec651504983c0e050e30ec731945301049c460e3800f09027001e0))
def f2758l12 : Packing := (182,3,7,12,4,14,0,f2758d12)
def f2758d13 (_i : Nat) : Nat := 0x3028e048d1580048f088a4460102091e190d81c00b8125966d3200ffc90401ff910803ff2c1007fe4c200
def f2758l13 : Packing := (4,2,7,8,4,8,0,f2758d13)
def f2758columns : IndexTree ColumnInfo := (IndexTree.fork 41 (IndexTree.fork 20 (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.fork 2 (IndexTree.leaf [(128,0,383,0,13),(64,0,447,0,13)]) (IndexTree.leaf [(4,0,507,0,12),(32,0,479,0,12),(1,0,510,0,12)])) (IndexTree.fork 2 (IndexTree.leaf [(2,0,509,0,12),(8,0,503,0,12)]) (IndexTree.leaf [(256,0,255,0,12),(320,0,191,0,11),(17,0,494,0,11)]))) (IndexTree.fork 5 (IndexTree.fork 2 (IndexTree.leaf [(66,0,445,0,11),(192,0,319,0,11)]) (IndexTree.leaf [(160,0,351,0,11),(24,0,487,0,11),(132,0,379,0,11)])) (IndexTree.fork 2 (IndexTree.leaf [(0,64,189,258,10),(0,128,347,36,10)]) (IndexTree.leaf [(33,0,478,0,9),(256,64,189,2,9),(6,0,505,0,9)])))) (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.fork 2 (IndexTree.leaf [(96,0,415,0,9),(264,0,247,0,9)]) (IndexTree.leaf [(12,0,499,0,9),(32,128,347,4,9),(129,0,382,0,9)])) (IndexTree.fork 2 (IndexTree.leaf [(65,0,446,0,9),(136,0,375,0,9)]) (IndexTree.leaf [(4,128,347,32,9),(3,0,508,0,9),(130,0,381,0,9)]))) (IndexTree.fork 5 (IndexTree.fork 2 (IndexTree.leaf [(2,64,189,256,9),(1,16,486,8,9)]) (IndexTree.leaf [(258,64,189,0,8),(260,0,251,0,8),(194,0,317,0,8)])) (IndexTree.fork 3 (IndexTree.leaf [(280,0,231,0,8),(67,0,444,0,8),(140,0,371,0,8)]) (IndexTree.leaf [(19,0,492,0,8),(70,0,441,0,8),(36,128,347,0,8)]))))) (IndexTree.fork 20 (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.fork 2 (IndexTree.leaf [(49,0,462,0,8),(164,0,347,0,8)]) (IndexTree.leaf [(40,0,471,0,8),(161,0,350,0,8),(134,0,377,0,8)])) (IndexTree.fork 2 (IndexTree.leaf [(25,0,486,0,8),(81,0,430,0,8)]) (IndexTree.leaf [(9,16,486,0,8),(322,0,189,0,8),(10,0,501,0,8)]))) (IndexTree.fork 5 (IndexTree.fork 2 (IndexTree.leaf [(0,1,460,50,8),(5,0,506,0,8)]) (IndexTree.leaf [(328,0,183,0,8),(352,0,159,0,8),(448,0,63,0,8)])) (IndexTree.fork 2 (IndexTree.leaf [(35,0,476,0,7),(156,0,355,0,7)]) (IndexTree.leaf [(177,0,334,0,7),(162,0,349,0,7),(83,0,428,0,7)])))) (IndexTree.fork 10 (IndexTree.fork 5 (IndexTree.fork 2 (IndexTree.leaf [(98,0,413,0,7),(74,0,437,0,7)]) (IndexTree.leaf [(2,4,369,136,7),(2,1,460,48,7),(480,0,31,0,7)])) (IndexTree.fork 2 (IndexTree.leaf [(133,0,378,0,7),(1,32,94,384,7)]) (IndexTree.leaf [(1,2,440,68,7),(8,256,151,96,7),(7,0,504,0,7)]))) (IndexTree.fork 5 (IndexTree.fork 2 (IndexTree.leaf [(268,0,243,0,7),(324,0,187,0,7)]) (IndexTree.leaf [(321,0,190,0,7),(8,4,369,130,7),(21,0,490,0,7)])) (IndexTree.fork 3 (IndexTree.leaf [(289,0,222,0,7),(344,0,167,0,7),(198,0,313,0,7)]) (IndexTree.leaf [(193,0,318,0,7),(14,0,497,0,7),(50,1,460,0,5)]))))))
def f2758levels : Nat → Packing
  | 9 => f2758l9
  | 10 => f2758l10
  | 11 => f2758l11
  | 12 => f2758l12
  | 13 => f2758l13
  | _ => emptyPacking
def f2758index : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 87 286 9 16 8 4 (hashf2758l10)
  | 11 => lookupWord 1277 4522 13 20 12 4 (hashf2758l11)
  | 12 => lookupWord 951 3343 12 20 12 4 (hashf2758l12)
  | 13 => lookupWord 75 255 8 16 8 4 (hashf2758l13)
  | _ => fun _ => none
def f2758 : Forest := ⟨511,13,fun j => deadsamples[j]?.getD (0,0),f2758columns,deadautos,f2758levels,f2758index⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem geomf2758 : graphValid f2758 (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=5) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_9_0 : block f2758 9 0 64=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_9_64 : block f2758 9 64 64=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_9_128 : block f2758 9 128 64=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_9_192 : block f2758 9 192 34=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allf2758_9 : block f2758 9 0 226=true := (@block_merge f2758 9 0 192 34 (@block_merge f2758 9 0 128 64 (@block_merge f2758 9 0 64 64 sf2758_9_0 sf2758_9_64) sf2758_9_128) sf2758_9_192)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_0 : block f2758 10 0 50=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_50 : block f2758 10 50 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_114 : block f2758 10 114 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_178 : block f2758 10 178 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_242 : block f2758 10 242 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_306 : block f2758 10 306 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_370 : block f2758 10 370 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_434 : block f2758 10 434 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_498 : block f2758 10 498 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_562 : block f2758 10 562 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_626 : block f2758 10 626 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_690 : block f2758 10 690 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_754 : block f2758 10 754 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_818 : block f2758 10 818 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_882 : block f2758 10 882 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_946 : block f2758 10 946 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_1010 : block f2758 10 1010 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_1074 : block f2758 10 1074 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_1138 : block f2758 10 1138 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_1202 : block f2758 10 1202 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_1266 : block f2758 10 1266 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_1330 : block f2758 10 1330 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_1394 : block f2758 10 1394 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_1458 : block f2758 10 1458 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_1522 : block f2758 10 1522 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_1586 : block f2758 10 1586 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_1650 : block f2758 10 1650 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_1714 : block f2758 10 1714 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_1778 : block f2758 10 1778 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_1842 : block f2758 10 1842 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_1906 : block f2758 10 1906 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_1970 : block f2758 10 1970 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_2034 : block f2758 10 2034 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_2098 : block f2758 10 2098 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_2162 : block f2758 10 2162 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_2226 : block f2758 10 2226 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_2290 : block f2758 10 2290 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_2354 : block f2758 10 2354 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_2418 : block f2758 10 2418 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_2482 : block f2758 10 2482 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_2546 : block f2758 10 2546 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_2610 : block f2758 10 2610 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_2674 : block f2758 10 2674 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_2738 : block f2758 10 2738 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_2802 : block f2758 10 2802 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_2866 : block f2758 10 2866 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_2930 : block f2758 10 2930 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_2994 : block f2758 10 2994 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_3058 : block f2758 10 3058 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_3122 : block f2758 10 3122 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_3186 : block f2758 10 3186 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_10_3250 : block f2758 10 3250 48=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allf2758_10 : block f2758 10 0 3298=true := (@block_merge f2758 10 0 3250 48 (@block_merge f2758 10 0 3186 64 (@block_merge f2758 10 0 3122 64 (@block_merge f2758 10 0 3058 64 (@block_merge f2758 10 0 2994 64 (@block_merge f2758 10 0 2930 64 (@block_merge f2758 10 0 2866 64 (@block_merge f2758 10 0 2802 64 (@block_merge f2758 10 0 2738 64 (@block_merge f2758 10 0 2674 64 (@block_merge f2758 10 0 2610 64 (@block_merge f2758 10 0 2546 64 (@block_merge f2758 10 0 2482 64 (@block_merge f2758 10 0 2418 64 (@block_merge f2758 10 0 2354 64 (@block_merge f2758 10 0 2290 64 (@block_merge f2758 10 0 2226 64 (@block_merge f2758 10 0 2162 64 (@block_merge f2758 10 0 2098 64 (@block_merge f2758 10 0 2034 64 (@block_merge f2758 10 0 1970 64 (@block_merge f2758 10 0 1906 64 (@block_merge f2758 10 0 1842 64 (@block_merge f2758 10 0 1778 64 (@block_merge f2758 10 0 1714 64 (@block_merge f2758 10 0 1650 64 (@block_merge f2758 10 0 1586 64 (@block_merge f2758 10 0 1522 64 (@block_merge f2758 10 0 1458 64 (@block_merge f2758 10 0 1394 64 (@block_merge f2758 10 0 1330 64 (@block_merge f2758 10 0 1266 64 (@block_merge f2758 10 0 1202 64 (@block_merge f2758 10 0 1138 64 (@block_merge f2758 10 0 1074 64 (@block_merge f2758 10 0 1010 64 (@block_merge f2758 10 0 946 64 (@block_merge f2758 10 0 882 64 (@block_merge f2758 10 0 818 64 (@block_merge f2758 10 0 754 64 (@block_merge f2758 10 0 690 64 (@block_merge f2758 10 0 626 64 (@block_merge f2758 10 0 562 64 (@block_merge f2758 10 0 498 64 (@block_merge f2758 10 0 434 64 (@block_merge f2758 10 0 370 64 (@block_merge f2758 10 0 306 64 (@block_merge f2758 10 0 242 64 (@block_merge f2758 10 0 178 64 (@block_merge f2758 10 0 114 64 (@block_merge f2758 10 0 50 64 sf2758_10_0 sf2758_10_50) sf2758_10_114) sf2758_10_178) sf2758_10_242) sf2758_10_306) sf2758_10_370) sf2758_10_434) sf2758_10_498) sf2758_10_562) sf2758_10_626) sf2758_10_690) sf2758_10_754) sf2758_10_818) sf2758_10_882) sf2758_10_946) sf2758_10_1010) sf2758_10_1074) sf2758_10_1138) sf2758_10_1202) sf2758_10_1266) sf2758_10_1330) sf2758_10_1394) sf2758_10_1458) sf2758_10_1522) sf2758_10_1586) sf2758_10_1650) sf2758_10_1714) sf2758_10_1778) sf2758_10_1842) sf2758_10_1906) sf2758_10_1970) sf2758_10_2034) sf2758_10_2098) sf2758_10_2162) sf2758_10_2226) sf2758_10_2290) sf2758_10_2354) sf2758_10_2418) sf2758_10_2482) sf2758_10_2546) sf2758_10_2610) sf2758_10_2674) sf2758_10_2738) sf2758_10_2802) sf2758_10_2866) sf2758_10_2930) sf2758_10_2994) sf2758_10_3058) sf2758_10_3122) sf2758_10_3186) sf2758_10_3250)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_0 : block f2758 11 0 3=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_3 : block f2758 11 3 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_67 : block f2758 11 67 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_131 : block f2758 11 131 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_195 : block f2758 11 195 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_259 : block f2758 11 259 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_323 : block f2758 11 323 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_387 : block f2758 11 387 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_451 : block f2758 11 451 64=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_515 : block f2758 11 515 41=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_556 : block f2758 11 556 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_620 : block f2758 11 620 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_684 : block f2758 11 684 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_748 : block f2758 11 748 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_812 : block f2758 11 812 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_876 : block f2758 11 876 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_940 : block f2758 11 940 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_1004 : block f2758 11 1004 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_1068 : block f2758 11 1068 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_1132 : block f2758 11 1132 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_1196 : block f2758 11 1196 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_1260 : block f2758 11 1260 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_1324 : block f2758 11 1324 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_1388 : block f2758 11 1388 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_1452 : block f2758 11 1452 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_1516 : block f2758 11 1516 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_1580 : block f2758 11 1580 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_1644 : block f2758 11 1644 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_1708 : block f2758 11 1708 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_1772 : block f2758 11 1772 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_1836 : block f2758 11 1836 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_1900 : block f2758 11 1900 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_1964 : block f2758 11 1964 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_2028 : block f2758 11 2028 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_2092 : block f2758 11 2092 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_2156 : block f2758 11 2156 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_2220 : block f2758 11 2220 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_2284 : block f2758 11 2284 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_2348 : block f2758 11 2348 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_11_2412 : block f2758 11 2412 31=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allf2758_11 : block f2758 11 0 2443=true := (@block_merge f2758 11 0 2412 31 (@block_merge f2758 11 0 2348 64 (@block_merge f2758 11 0 2284 64 (@block_merge f2758 11 0 2220 64 (@block_merge f2758 11 0 2156 64 (@block_merge f2758 11 0 2092 64 (@block_merge f2758 11 0 2028 64 (@block_merge f2758 11 0 1964 64 (@block_merge f2758 11 0 1900 64 (@block_merge f2758 11 0 1836 64 (@block_merge f2758 11 0 1772 64 (@block_merge f2758 11 0 1708 64 (@block_merge f2758 11 0 1644 64 (@block_merge f2758 11 0 1580 64 (@block_merge f2758 11 0 1516 64 (@block_merge f2758 11 0 1452 64 (@block_merge f2758 11 0 1388 64 (@block_merge f2758 11 0 1324 64 (@block_merge f2758 11 0 1260 64 (@block_merge f2758 11 0 1196 64 (@block_merge f2758 11 0 1132 64 (@block_merge f2758 11 0 1068 64 (@block_merge f2758 11 0 1004 64 (@block_merge f2758 11 0 940 64 (@block_merge f2758 11 0 876 64 (@block_merge f2758 11 0 812 64 (@block_merge f2758 11 0 748 64 (@block_merge f2758 11 0 684 64 (@block_merge f2758 11 0 620 64 (@block_merge f2758 11 0 556 64 (@block_merge f2758 11 0 515 41 (@block_merge f2758 11 0 451 64 (@block_merge f2758 11 0 387 64 (@block_merge f2758 11 0 323 64 (@block_merge f2758 11 0 259 64 (@block_merge f2758 11 0 195 64 (@block_merge f2758 11 0 131 64 (@block_merge f2758 11 0 67 64 (@block_merge f2758 11 0 3 64 sf2758_11_0 sf2758_11_3) sf2758_11_67) sf2758_11_131) sf2758_11_195) sf2758_11_259) sf2758_11_323) sf2758_11_387) sf2758_11_451) sf2758_11_515) sf2758_11_556) sf2758_11_620) sf2758_11_684) sf2758_11_748) sf2758_11_812) sf2758_11_876) sf2758_11_940) sf2758_11_1004) sf2758_11_1068) sf2758_11_1132) sf2758_11_1196) sf2758_11_1260) sf2758_11_1324) sf2758_11_1388) sf2758_11_1452) sf2758_11_1516) sf2758_11_1580) sf2758_11_1644) sf2758_11_1708) sf2758_11_1772) sf2758_11_1836) sf2758_11_1900) sf2758_11_1964) sf2758_11_2028) sf2758_11_2092) sf2758_11_2156) sf2758_11_2220) sf2758_11_2284) sf2758_11_2348) sf2758_11_2412)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_12_0 : block f2758 12 0 59=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_12_59 : block f2758 12 59 64=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_12_123 : block f2758 12 123 59=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allf2758_12 : block f2758 12 0 182=true := (@block_merge f2758 12 0 123 59 (@block_merge f2758 12 0 59 64 sf2758_12_0 sf2758_12_59) sf2758_12_123)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf2758_13_0 : block f2758 13 0 4=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allf2758_13 : block f2758 13 0 4=true := sf2758_13_0
theorem tablesf2758 : checkedTables f2758 13 := by
  intro k hk
  interval_cases k
  · exact (rfl : block f2758 0 0 0 = true)
  · exact (rfl : block f2758 1 0 0 = true)
  · exact (rfl : block f2758 2 0 0 = true)
  · exact (rfl : block f2758 3 0 0 = true)
  · exact (rfl : block f2758 4 0 0 = true)
  · exact (rfl : block f2758 5 0 0 = true)
  · exact (rfl : block f2758 6 0 0 = true)
  · exact (rfl : block f2758 7 0 0 = true)
  · exact (rfl : block f2758 8 0 0 = true)
  · exact allf2758_9
  · exact allf2758_10
  · exact allf2758_11
  · exact allf2758_12
  · exact allf2758_13

def wNot0 : Sig := neg (inputs.getD 0 zero)
def rawRest : List Sig := (List.range' 1 8).map (fun i => inputs.getD i zero)
def baseC2758 (b : Fin 9) : List Sig := rawRest ++ [wNot0, bin true (inputs.getD 0 zero) (inputs.getD b.val zero)]

def perm1Moves : List Move := ([118, 130, 81] : List Nat).map swapRows
theorem perm1_auto : autoOK graph perm1Moves = true := by decide +kernel

theorem live_perm1 {k t S} (h : Live graph k t S) :
    Live graph k t (S.image (movedWord perm1Moves)) := by
  have ok := perm1_auto
  simp only [autoOK, Bool.and_eq_true, beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow perm1Moves) :=
    fun r => ⟨movedRow perm1Moves.reverse r, composed_id ok.2 r⟩
  have h1 := live_rename h (movedRow perm1Moves) onto
  have hG : rename (movedRow perm1Moves) graph = graph :=
    (moved_eq_rename perm1Moves graph).symm.trans ok.1.1
  have hImg : S.image (rename (movedRow perm1Moves)) = S.image (movedWord perm1Moves) := by
    ext a; simp only [Finset.mem_image, moved_eq_rename]
  rw [hG, hImg] at h1
  exact h1

theorem perm1_in_inputs_b : (inputs.all fun a => inputs.any fun y => y == movedWord perm1Moves a) = true := by
  decide +kernel

theorem perm1_in_inputs (a : Sig) (ha : a ∈ inputs) : movedWord perm1Moves a ∈ inputs := by
  have h := List.all_eq_true.mp perm1_in_inputs_b a ha
  obtain ⟨y, hy, heq⟩ := List.any_eq_true.mp h
  rw [beq_iff_eq] at heq
  exact heq ▸ hy

theorem perm1_w0 : movedWord perm1Moves (inputs.getD 0 zero) = inputs.getD 0 zero := by decide +kernel
theorem perm1_w5 : movedWord perm1Moves (inputs.getD 5 zero) = inputs.getD 1 zero := by decide +kernel
theorem perm1_w7 : movedWord perm1Moves (inputs.getD 7 zero) = inputs.getD 6 zero := by decide +kernel
theorem perm1_w8 : movedWord perm1Moves (inputs.getD 8 zero) = inputs.getD 2 zero := by decide +kernel
theorem perm1_neg0 : movedWord perm1Moves wNot0 = wNot0 := by decide +kernel
theorem perm1_bin (d : Bool) (a b : Sig) :
    movedWord perm1Moves (bin d a b) = bin d (movedWord perm1Moves a) (movedWord perm1Moves b) := by
  rw [moved_eq_rename, moved_eq_rename, moved_eq_rename, rename_bin]

theorem dead14_imp : Impossible graph 14 inputs.toFinset :=
  dead_start (before_sound _ valid383) geomdead tablesdead

theorem isoInputs_bool :
    ((List.finRange 9).all fun i =>
      (bit (absentRow i) graph != bit (presentRow i) graph) &&
      (inputs.all fun v => v == inputs.getD i.val zero || bit (absentRow i) v == bit (presentRow i) v)) = true := by
  decide +kernel

theorem l2758_core14 {k t S} (hk : k ≤ 14) (h : Live graph k t S)
    (hs : ∀ a ∈ S, a ∈ inputs) : False := by
  have hEq : S = inputs.toFinset := by
    ext a; rw [List.mem_toFinset]
    refine ⟨hs a, fun ha => ?_⟩
    rw [← input_list] at ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    have cut := List.all_eq_true.mp isoInputs_bool i (List.mem_finRange i)
    simp only [Bool.and_eq_true, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at cut
    exact raw_required h inputs (inputs.getD i.val zero) hs (absentRow i) (presentRow i)
      cut.1 (fun v hv hne => (cut.2 v hv).resolve_left hne)
  exact dead14_imp k t hk (hEq ▸ h)

theorem l2758_noLive {k t S} (hk : k ≤ 13) (h : Live graph k t S)
    (hs : ∀ a ∈ S, a ∈ inputs ++ [wNot0]) : False := by
  have formed : represented inputs wNot0 ∨ witness inputs wNot0 :=
    inv_rep (get_rep inputs 0)
  obtain ⟨l, v, U, hl, run', sub'⟩ := pull_gate h formed (fun a ha => hs a ha)
  exact l2758_core14 (by omega) run' sub'

theorem l2758_noLiveOr (b : Fin 9) {k t S} (hk : k ≤ 13) (h : Live graph k t S)
    (hs : ∀ a ∈ S, a ∈ inputs ++ [bin true (inputs.getD 0 zero) (inputs.getD b.val zero)]) : False := by
  have formed : represented inputs (bin true (inputs.getD 0 zero) (inputs.getD b.val zero)) ∨
      witness inputs (bin true (inputs.getD 0 zero) (inputs.getD b.val zero)) :=
    bin_rep true (get_rep inputs 0) (get_rep inputs b.val)
  obtain ⟨l, v, U, hl, run', sub'⟩ := pull_gate h formed (fun a ha => hs a ha)
  exact l2758_core14 (by omega) run' sub'

theorem slice_x0 : Slice inputs graph (subcube 1 0) 12 := by
  have h := col_sound (m:=511) (1, 0, 510, 0, 12) (boundsBefore known383) (before_sound _ valid383) (by decide +kernel)
  have hv : vars 511 = inputs := by decide +kernel
  have hg : chartGoal 511 = graph := by decide +kernel
  rwa [hv, hg] at h

theorem slice_x0_x4 : Slice inputs graph (subcube 17 0) 11 := by
  have h := col_sound (m:=511) (17, 0, 494, 0, 11) (boundsBefore known383) (before_sound _ valid383) (by decide +kernel)
  have hv : vars 511 = inputs := by decide +kernel
  have hg : chartGoal 511 = graph := by decide +kernel
  rwa [hv, hg] at h

theorem poolCut_two_x0 {k t S} (hk : k ≤ 13) (h : Live graph k t S)
    (a b : Sig) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hca : isMaskedConstant (subcube 1 0) a = true)
    (hcb : isMaskedConstant (subcube 1 0) b = true)
    (hav : ∀ x ∈ S, availableB (subcube 1 0) inputs x = true) : False := by
  obtain ⟨ws, hws⟩ := Quotient.exists_rep S.1
  have hnd : ws.Nodup := Multiset.coe_nodup.mp (by simpa [← hws] using S.2)
  have hEq : ws.toFinset = S := by
    ext x
    rw [List.mem_toFinset, Finset.mem_def]
    change x ∈ ws ↔ x ∈ S.1
    rw [← hws]
    exact Multiset.mem_coe.symm
  have hcnt : 2 ≤ ws.countP (isMaskedConstant (subcube 1 0)) := by
    have haW : a ∈ ws := List.mem_toFinset.mp (hEq.symm ▸ ha)
    have hbW : b ∈ ws := List.mem_toFinset.mp (hEq.symm ▸ hb)
    have hperm : ws.Perm (a :: b :: (ws.erase a).erase b) := by
      have hbE : b ∈ ws.erase a := (List.mem_erase_of_ne hab.symm).mpr hbW
      exact (List.perm_cons_erase haW).trans (List.Perm.cons a (List.perm_cons_erase hbE))
    rw [hperm.countP_eq]
    simp only [List.countP_cons, hca, hcb, ite_true]
    omega
  have hcut : poolCut (subcube 1 0) 12 13 0 inputs ws = true := by
    simp only [poolCut, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
    exact ⟨by omega, fun x hx => hav x (hEq ▸ List.mem_toFinset.mpr hx)⟩
  exact poolCut_sound slice_x0 [] rfl hnd hcut k t hk (hEq ▸ h)

def caseBR (b : Fin 9) : Row :=
  if b = 1 then Fin.ofNat 512 ((1 <<< 1) ||| (1 <<< 4))
  else if b = 2 then Fin.ofNat 512 ((1 <<< 2) ||| (1 <<< 4))
  else if b = 3 then Fin.ofNat 512 ((1 <<< 3) ||| (1 <<< 5))
  else if b = 4 then Fin.ofNat 512 ((1 <<< 4) ||| (1 <<< 5))
  else Fin.ofNat 512 ((1 <<< 6) ||| (1 <<< 4))
def caseBS (b : Fin 9) : Row := Fin.ofNat 512 ((caseBR b).val ||| 1)

theorem caseB_bool :
    (([1, 2, 3, 4, 6] : List (Fin 9)).all fun b =>
      let w10 := bin true wNot0 (inputs.getD b.val zero)
      (bit (caseBR b) graph != bit (caseBS b) graph) &&
      ((rawRest ++ [w10]).all fun v => bit (caseBR b) v == bit (caseBS b) v) &&
      isMaskedConstant (subcube 1 0) (inputs.getD 0 zero) &&
      isMaskedConstant (subcube 1 0) wNot0 &&
      isMaskedConstant (subcube 1 0) w10 &&
      (inputs.getD 0 zero != w10) &&
      (wNot0 != w10) &&
      ((inputs ++ [wNot0, w10]).all fun v => availableB (subcube 1 0) inputs v)) = true := by
  decide +kernel

theorem inputs_cons_rest : inputs = inputs.getD 0 zero :: rawRest := by decide +kernel

theorem l2758_caseB (b : Fin 9) (hb : b ∈ ([1, 2, 3, 4, 6] : List (Fin 9)))
    {k t S} (hk : k ≤ 13) (h : Live graph k t S)
    (hs : ∀ a ∈ S, a ∈ inputs ++ [wNot0, bin true wNot0 (inputs.getD b.val zero)]) : False := by
  let w10 := bin true wNot0 (inputs.getD b.val zero)
  by_cases hw : w10 ∈ S
  · have hc := List.all_eq_true.mp caseB_bool b hb
    simp only [Bool.and_eq_true, bne_iff_ne, List.all_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨⟨⟨⟨⟨hdiff, hag⟩, hc0⟩, hcn0⟩, hcw⟩, hne0⟩, hnen0⟩, hav⟩ := hc
    obtain ⟨v, hvS, hvDiff⟩ := live_row_difference h hdiff
    have hv09 : v = inputs.getD 0 zero ∨ v = wNot0 := by
      have hm := hs v hvS
      rw [inputs_cons_rest] at hm
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | hR | rfl | rfl
      · exact Or.inl rfl
      · exact False.elim (hvDiff (hag v (List.mem_append_left _ hR)))
      · exact Or.inr rfl
      · exact False.elim (hvDiff (hag w10 (List.mem_append_right _ (by simp [w10]))))
    rcases hv09 with rfl | rfl
    · exact poolCut_two_x0 hk h _ w10 hvS hw hne0 hc0 hcw (fun x hx => hav x (hs x hx))
    · exact poolCut_two_x0 hk h _ w10 hvS hw hnen0 hcn0 hcw (fun x hx => hav x (hs x hx))
  · apply l2758_noLive hk h
    intro a ha
    have hm := hs a ha
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
    rcases hm with hI | rfl | rfl
    · exact Or.inl hI
    · exact Or.inr rfl
    · exact False.elim (hw ha)

def isoCR (b i : Fin 9) : Row :=
  if i = b then
    if b = 1 ∨ b = 4 then Fin.ofNat 512 1
    else if b = 2 then Fin.ofNat 512 (1 ||| (1 <<< 7))
    else Fin.ofNat 512 (1 ||| (1 <<< 8))
  else if i = 1 then Fin.ofNat 512 (1 <<< 2)
  else if i = 4 then Fin.ofNat 512 (1 <<< 3)
  else if i = 5 then Fin.ofNat 512 (1 <<< 7)
  else Fin.ofNat 512 (1 <<< neighbor i)
def isoCS (b i : Fin 9) : Row := Fin.ofNat 512 ((isoCR b i).val ||| (1 <<< i.val))

theorem caseC_bool :
    (([1, 2, 3, 4, 6] : List (Fin 9)).all fun b =>
      ((List.finRange 9).all fun i =>
        (i == 0) ||
        ((bit (isoCR b i) graph != bit (isoCS b i) graph) &&
         ((baseC2758 b).all fun v =>
           v == inputs.getD i.val zero || bit (isoCR b i) v == bit (isoCS b i) v))) &&
      isMaskedConstant (subcube 1 0) (inputs.getD 0 zero) &&
      isMaskedConstant (subcube 1 0) wNot0 &&
      (inputs.getD 0 zero != wNot0) &&
      ((inputs ++ [wNot0, bin true (inputs.getD 0 zero) (inputs.getD b.val zero)]).all fun v =>
        availableB (subcube 1 0) inputs v)) = true := by
  decide +kernel

def nodupB : List Sig → Bool
  | [] => true
  | x :: xs => (xs.all fun y => x != y) && nodupB xs

theorem nodup_of_bool : ∀ {l : List Sig}, nodupB l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: xs, h => by
    simp only [nodupB, Bool.and_eq_true, List.all_eq_true, bne_iff_ne] at h
    exact List.nodup_cons.mpr ⟨fun hx => h.1 x hx rfl, nodup_of_bool h.2⟩

theorem baseC2758_4_nodup : (baseC2758 4).Nodup := nodup_of_bool (by decide +kernel)

theorem f2758_imp_b (b : Fin 9) (hb : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 6) :
    Impossible graph 13 (baseC2758 b).toFinset := by
  have tgt : targetOf f2758 = graph := by decide +kernel
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · rw [← tgt]; exact root_index (g:=f2758) (before_sound _ valid383) geomf2758 tablesf2758 (k:=13)
      (by decide) (i:=2) (ws:=baseC2758 1) (by decide +kernel)
  · rw [← tgt]; exact root_index (g:=f2758) (before_sound _ valid383) geomf2758 tablesf2758 (k:=13)
      (by decide) (i:=3) (ws:=baseC2758 2) (by decide +kernel)
  · rw [← tgt]; exact root_index (g:=f2758) (before_sound _ valid383) geomf2758 tablesf2758 (k:=13)
      (by decide) (i:=0) (ws:=baseC2758 3) (by decide +kernel)
  · exact poolCut_sound slice_x0_x4 [] rfl baseC2758_4_nodup (by decide +kernel)
  · rw [← tgt]; exact root_index (g:=f2758) (before_sound _ valid383) geomf2758 tablesf2758 (k:=13)
      (by decide) (i:=1) (ws:=baseC2758 6) (by decide +kernel)

theorem l2758_caseC (b : Fin 9) (hb : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 6)
    {k t S} (hk : k ≤ 13) (h : Live graph k t S)
    (hs : ∀ a ∈ S, a ∈ inputs ++ [wNot0, bin true (inputs.getD 0 zero) (inputs.getD b.val zero)]) : False := by
  let w10 := bin true (inputs.getD 0 zero) (inputs.getD b.val zero)
  have hbL : b ∈ ([1, 2, 3, 4, 6] : List (Fin 9)) := by
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> simp
  have hc := List.all_eq_true.mp caseC_bool b hbL
  simp only [Bool.and_eq_true, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨hiso, hc0⟩, hcn0⟩, hne09⟩, hav⟩ := hc
  by_cases hw : w10 ∈ S
  · by_cases hn9 : wNot0 ∈ S
    · by_cases h0 : inputs.getD 0 zero ∈ S
      · exact poolCut_two_x0 hk h _ wNot0 h0 hn9 hne09 hc0 hcn0 (fun x hx => hav x (hs x hx))
      · have subC : ∀ a ∈ S, a ∈ baseC2758 b := by
          intro a ha
          have hm := hs a ha
          rw [inputs_cons_rest] at hm
          simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hm
          simp only [baseC2758, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
          rcases hm with rfl | hR | rfl | rfl
          · exact False.elim (h0 ha)
          · exact Or.inl hR
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr rfl)
        have hEq : S = (baseC2758 b).toFinset := by
          ext a; rw [List.mem_toFinset]
          refine ⟨subC a, fun ha => ?_⟩
          simp only [baseC2758, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with hR | rfl | rfl
          · simp only [rawRest, List.mem_map, List.mem_range'] at hR
            obtain ⟨idx, ⟨hlo, hhi, _⟩, rfl⟩ := hR
            let fi : Fin 9 := ⟨idx, by omega⟩
            have hne0 : fi ≠ 0 := by intro e; have := congrArg Fin.val e; simp [fi] at this; omega
            have hfi := (hiso fi (List.mem_finRange fi)).resolve_left hne0
            exact raw_required h (baseC2758 b) (inputs.getD idx zero) subC (isoCR b fi) (isoCS b fi)
              hfi.1 (fun v hv hne => (hfi.2 v hv).resolve_left hne)
          · exact hn9
          · exact hw
        exact f2758_imp_b b hb k t hk (hEq ▸ h)
    · apply l2758_noLiveOr b hk h
      intro a ha
      have hm := hs a ha
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
      rcases hm with hI | rfl | rfl
      · exact Or.inl hI
      · exact False.elim (hn9 ha)
      · exact Or.inr rfl
  · apply l2758_noLive hk h
    intro a ha
    have hm := hs a ha
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
    rcases hm with hI | rfl | rfl
    · exact Or.inl hI
    · exact Or.inr rfl
    · exact False.elim (hw ha)

theorem l2758_perm1_sub (u : Sig) {S : Finset Sig}
    (hs : ∀ a ∈ S, a ∈ inputs ++ [wNot0, u]) :
    ∀ a ∈ S.image (movedWord perm1Moves), a ∈ inputs ++ [wNot0, movedWord perm1Moves u] := by
  intro a ha
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ha
  have hm := hs c hc
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
  rcases hm with hI | rfl | rfl
  · exact Or.inl (perm1_in_inputs c hI)
  · exact Or.inr (Or.inl perm1_neg0)
  · exact Or.inr (Or.inr rfl)

theorem l2758_or_0_not0 : bin true (inputs.getD 0 zero) wNot0 = one := by decide +kernel

theorem l2758_pair (p q : Nat) (hp : p < 10) (hq : q < 10) (h09 : p = 0 ∨ q = 0 ∨ p = 9 ∨ q = 9)
    {k t S} (hk : k ≤ 13) (h : Live graph k t S)
    (hs : ∀ a ∈ S, a ∈ (inputs ++ [wNot0]) ++ [bin true ((inputs ++ [wNot0]).getD p zero) ((inputs ++ [wNot0]).getD q zero)]) :
    False := by
  have hcomm : ∀ a b : Sig,
      (∀ x ∈ S, x ∈ (inputs ++ [wNot0]) ++ [bin true b a]) →
      (∀ x ∈ S, x ∈ (inputs ++ [wNot0]) ++ [bin true a b]) := by
    intro a b hh x hx; rw [bin_comm]; exact hh x hx
  have hnorm : ∀ (u v : Nat), u < 10 → v < 10 → (u = 0 ∨ u = 9) →
      (∀ a ∈ S, a ∈ (inputs ++ [wNot0]) ++ [bin true ((inputs ++ [wNot0]).getD u zero) ((inputs ++ [wNot0]).getD v zero)]) →
      False := by
    intro u v hu hv hu09 hsu
    have hmem : ∀ w : Sig, (∀ a ∈ S, a ∈ (inputs ++ [wNot0]) ++ [w]) → ∀ a ∈ S, a ∈ inputs ++ [wNot0, w] := by
      intro w hh a ha; simpa [List.append_assoc] using hh a ha
    have hkillOne : (∀ a ∈ S, a ∈ inputs ++ [wNot0, one]) → False := fun h1 => by
      apply l2758_noLive hk h
      intro a ha
      have hm := h1 a ha
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
      rcases hm with hI | rfl | rfl
      · exact Or.inl hI
      · exact Or.inr rfl
      · exact False.elim ((live_proper h one ha).2 rfl)
    rcases hu09 with rfl | rfl
    · interval_cases v
      · apply l2758_noLive hk h; intro a ha
        have h1 := hmem _ hsu a ha
        have he : (inputs ++ [wNot0]).getD 0 zero = inputs.getD 0 zero := rfl
        rw [he, (bin_laws _).2.2.2.2.2] at h1
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h1 ⊢
        rcases h1 with hI | rfl | rfl
        · exact Or.inl hI
        · exact Or.inr rfl
        · exact Or.inl (by rw [inputs_cons_rest]; exact List.mem_cons_self ..)
      · exact l2758_caseC 1 (Or.inl rfl) hk h (hmem _ hsu)
      · exact l2758_caseC 2 (Or.inr (Or.inl rfl)) hk h (hmem _ hsu)
      · exact l2758_caseC 3 (Or.inr (Or.inr (Or.inl rfl))) hk h (hmem _ hsu)
      · exact l2758_caseC 4 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hk h (hmem _ hsu)
      · have hs1 := l2758_perm1_sub _ (hmem _ hsu)
        have he : bin true ((inputs ++ [wNot0]).getD 0 zero) ((inputs ++ [wNot0]).getD 5 zero) =
            bin true (inputs.getD 0 zero) (inputs.getD 5 zero) := rfl
        rw [he, perm1_bin, perm1_w0, perm1_w5] at hs1
        exact l2758_caseC 1 (Or.inl rfl) hk (live_perm1 h) hs1
      · exact l2758_caseC 6 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hk h (hmem _ hsu)
      · have hs1 := l2758_perm1_sub _ (hmem _ hsu)
        have he : bin true ((inputs ++ [wNot0]).getD 0 zero) ((inputs ++ [wNot0]).getD 7 zero) =
            bin true (inputs.getD 0 zero) (inputs.getD 7 zero) := rfl
        rw [he, perm1_bin, perm1_w0, perm1_w7] at hs1
        exact l2758_caseC 6 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hk (live_perm1 h) hs1
      · have hs1 := l2758_perm1_sub _ (hmem _ hsu)
        have he : bin true ((inputs ++ [wNot0]).getD 0 zero) ((inputs ++ [wNot0]).getD 8 zero) =
            bin true (inputs.getD 0 zero) (inputs.getD 8 zero) := rfl
        rw [he, perm1_bin, perm1_w0, perm1_w8] at hs1
        exact l2758_caseC 2 (Or.inr (Or.inl rfl)) hk (live_perm1 h) hs1
      · apply hkillOne; intro a ha
        have h1 := hmem _ hsu a ha
        have he : bin true ((inputs ++ [wNot0]).getD 0 zero) ((inputs ++ [wNot0]).getD 9 zero) = one := l2758_or_0_not0
        rwa [he] at h1
    · interval_cases v
      · apply hkillOne; intro a ha
        have h1 := hmem _ hsu a ha
        have he : bin true ((inputs ++ [wNot0]).getD 9 zero) ((inputs ++ [wNot0]).getD 0 zero) = one := by
          change bin true wNot0 (inputs.getD 0 zero) = one; rw [bin_comm]; exact l2758_or_0_not0
        rwa [he] at h1
      · exact l2758_caseB 1 (by simp) hk h (hmem _ hsu)
      · exact l2758_caseB 2 (by simp) hk h (hmem _ hsu)
      · exact l2758_caseB 3 (by simp) hk h (hmem _ hsu)
      · exact l2758_caseB 4 (by simp) hk h (hmem _ hsu)
      · have hs1 := l2758_perm1_sub _ (hmem _ hsu)
        have he : bin true ((inputs ++ [wNot0]).getD 9 zero) ((inputs ++ [wNot0]).getD 5 zero) =
            bin true wNot0 (inputs.getD 5 zero) := rfl
        rw [he, perm1_bin, perm1_neg0, perm1_w5] at hs1
        exact l2758_caseB 1 (by simp) hk (live_perm1 h) hs1
      · exact l2758_caseB 6 (by simp) hk h (hmem _ hsu)
      · have hs1 := l2758_perm1_sub _ (hmem _ hsu)
        have he : bin true ((inputs ++ [wNot0]).getD 9 zero) ((inputs ++ [wNot0]).getD 7 zero) =
            bin true wNot0 (inputs.getD 7 zero) := rfl
        rw [he, perm1_bin, perm1_neg0, perm1_w7] at hs1
        exact l2758_caseB 6 (by simp) hk (live_perm1 h) hs1
      · have hs1 := l2758_perm1_sub _ (hmem _ hsu)
        have he : bin true ((inputs ++ [wNot0]).getD 9 zero) ((inputs ++ [wNot0]).getD 8 zero) =
            bin true wNot0 (inputs.getD 8 zero) := rfl
        rw [he, perm1_bin, perm1_neg0, perm1_w8] at hs1
        exact l2758_caseB 2 (by simp) hk (live_perm1 h) hs1
      · apply l2758_noLive hk h; intro a ha
        have h1 := hmem _ hsu a ha
        have he : (inputs ++ [wNot0]).getD 9 zero = wNot0 := rfl
        rw [he, (bin_laws _).2.2.2.2.2] at h1
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h1 ⊢
        rcases h1 with hI | rfl | rfl
        · exact Or.inl hI
        · exact Or.inr rfl
        · exact Or.inr rfl
  rcases h09 with h1 | h1 | h1 | h1
  · exact hnorm p q hp hq (Or.inl h1) hs
  · exact hnorm q p hq hp (Or.inl h1) (hcomm _ _ hs)
  · exact hnorm p q hp hq (Or.inr h1) hs
  · exact hnorm q p hq hp (Or.inr h1) (hcomm _ _ hs)

theorem close2758 (pins : List Nat) (h2 : pins.length = 2) (hlt : ∀ i ∈ pins, i < 10)
    (h09 : 0 ∈ pins ∨ 9 ∈ pins) (C : Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C)
    (small : C.size ≤ 13)
    (correct : ∀ x : Fin 9 → Bool,
      let w := List.ofFn x ++ [!x 0]
      C.eval (w ++ [GateOp.or.eval (pins.map fun i => w.getD i false)]) = edge x) : False := by
  match pins, h2, hlt, h09, correct with
  | [p, q], _, hlt, h09, correct =>
    let sup : List Sig := inputs ++ [wNot0]
    let g : Gate := ⟨.or, [p, q]⟩
    let z := gv sup g
    let w := sup ++ [z]
    have hsup (r : Row) : sup.map (bit r) = List.ofFn (sample r) ++ [!sample r 0] := by
      simp only [sup, List.map_append, List.map_singleton, sampled, wNot0, bit_neg]
      rfl
    have zbit (r : Row) : bit r z = GateOp.or.eval (([p, q] : List Nat).map fun i => (sup.map (bit r)).getD i false) :=
      run_bit r g sup (Or.inr (Or.inl rfl))
    have eqGoal : (execute C.gates w).getD C.output zero = graph := by
      apply BitVec.eq_of_getLsbD_eq
      intro j hj
      let r : Row := ⟨j, hj⟩
      change bit r ((execute C.gates w).getD C.output zero) = bit r graph
      rw [← b_read, execute_bits _ _ _ (fun a ha => (fan a ha).1), edge_table]
      change C.eval (w.map (bit r)) = edge (sample r)
      simp only [w, List.map_append, List.map_singleton, zbit, hsup]
      exact correct (sample r)
    have out := get_rep (execute C.gates w) C.output
    rw [eqGoal] at out
    obtain ⟨k, t, S, hk, run, hs⟩ :=
      extract C.gates w fan graph_proper (out.resolve_right fun hn => hn graph_proper)
    have hp : p < 10 := hlt p (by simp)
    have hq : q < 10 := hlt q (by simp)
    have h09' : p = 0 ∨ q = 0 ∨ p = 9 ∨ q = 9 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h09; tauto
    have hz : z = bin true (sup.getD p zero) (sup.getD q zero) := by
      change bin true (sup.getD p zero) (bin true (sup.getD q zero) zero) = _
      rw [(bin_laws _).2.1]
    have hs' : ∀ a ∈ S, a ∈ sup ++ [bin true (sup.getD p zero) (sup.getD q zero)] := by
      intro a ha; simpa [w, hz] using hs a ha
    exact l2758_pair p q hp hq h09' (le_trans hk small) run hs'

end PEqualNP.Outside.L_meta_2758

theorem PEqualNP.Outside.L_meta_2758 : ∀ (x1 : List ℕ),   x1.length = (2 : ℕ) →     (∀ x3 ∈ x1, x3 < (10 : ℕ)) →       (0 : ℕ) ∈ x1 ∨ (9 : ℕ) ∈ x1 →         ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit),           PEqualNP.MetaComplexity.FanInTwo x5 →             x5.size ≤ (13 : ℕ) →               ∃ (x8 : Fin (9 : ℕ) → Bool),                 have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];                 x5.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x1)]) ≠ (x8 (0 : Fin (9 : ℕ)) && x8 (1 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (2 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (3 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (4 : Fin (9 : ℕ)) || x8 (4 : Fin (9 : ℕ)) && x8 (0 : Fin (9 : ℕ)) || x8 (0 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ)) || x8 (1 : Fin (9 : ℕ)) && x8 (6 : Fin (9 : ℕ)) || x8 (2 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (3 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (5 : Fin (9 : ℕ)) && x8 (7 : Fin (9 : ℕ)) || x8 (6 : Fin (9 : ℕ)) && x8 (8 : Fin (9 : ℕ)) || x8 (8 : Fin (9 : ℕ)) && x8 (5 : Fin (9 : ℕ))) := by
  intro pins h2 hlt h09 C fan small
  by_contra h
  apply PEqualNP.Outside.L_meta_2758.close2758 pins h2 hlt h09 C fan small
  intro x
  by_contra bad
  exact h ⟨x, bad⟩
