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
namespace PEqualNP.Outside.L_meta_3563
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
def hashf3563l9 (_i : Nat) : Nat := 0x2050000000508000
def hashf3563l10 (_i : Nat) : Nat := 0x60e4210de14aa13b80a0c0f840da0000a0b9e124c1656051014e4076615400014166000000000c2a0000c104e3720001a1380000000080aec18320b0a190c1754070e04860f100916159a16e0137404c000140220001c0fe0096e05bc0ef014000e320d4c16d0c1c4010e0ed41280000000140d70030e17d01442e2681a6a04360474095e1888040c1072067c04e819d6179c0cf607fc157c197400940ad606ac02641a9608d203b073320d2e2c9618ba039431e2278c0b7a150411a802ca112412d4018615aa11e00a2c1aaa07ce0336ec9c04bc02b60ea00792c1e6000e19fc10000b400000001e00361a2cec4a036a2ae208ec09a417f005c606d614860c7e17a010f638dacb4e0f6614d016ba0d1c9326176e1350060c087c18de0356cb08108c016000141022074000000000000000e601e00012126000020e6000000000000000140fc0000c12e00004052a09280a6a1926147815320064ec2e2c4e00be2cb419a215e00008044e11961a061320000e12a00016c1a0000000021600000000041700000c09821162028c0ba4054a0ab02b1622be03da0e924f5801d6073c10b40854020802500b3400d40fb408a803e00014c7800018069213e0000419481680001608200004180000100de807b8d1f21a5a0814014a12080dc000000a98cc4000000014114e09c4173c08980d90131a06f8e79a198a00500cc21108cca014200000001c0bc6187d0c520cac15c011d81234013e05f20e000018064c02f60a4000000c40001c0f5a0c00000000182dd80c8000100bf60f20063613c0000018f801aa056e09e00c2ccc0a18420580162030000002090580000002800412060383416091a814040400800120c00820020506800000311000000000024020000800040e17000000000834020000034b200170000c0103000200202050120000024600902880003f0286c0400
def hashf3563l11 (i : Nat) : Nat := (if i<5 then (if i<2 then (if i<1 then 0x1400000000000200000000100200000800000101a00300700000100200000100101700200201900500002500400b00200002d00001b00600900000901000001700000300f00300100400300000300201100000800002400000100b00000900200600e00200500900400200000100200100301000200000000702601a00000200201700302100000209e01800000100800400400200400800200000800000e00900600204801a04601f00000904800200d00500200400000b00200e07500200500004b00200002200100f00000601101200100400700601d01101600000700300200e00c01a00102f00301700700002500200800200004c00800000000f00000a03900300100101300400000000100600501300000001200200b00003402400503700100000100100f00000100800302b00306b00000000600400100100200001c00600100000003000202401f00300200900003400500000300300200000100000000000800a00000200400305605d00100300000004502f02b00300a00700000000101400000200500a00600000301300100000101c00e00102001501b00500300200302e00200000003f00200400400b02600200100200c02a04300004c00000000100900300000606100100200800c02200101400600001300600400b01200000000000100400200100000000b00600000200100400000400800400102000501300700200001607402100500100a00102500e00a00000402500100300f00906300800900201200104300000001300001600001802e00100e02900f00307100900100f00200101900402a00800000100200000a00100800700300500000303f00100000802f00c00300100000500300000700100000b00804100801200600200004c00002400400d04e00100601200200d00300100901b00600100a00202c00100c00000400000302301000500f05902e02900f02d01400800000200000500200200000100f00000200100700000b01001a00700600300000e06700102300800d00100500002101600301e00601400b00102604a00b00200300a00100000d00a01800700600102701601b00000f00400300a00200100000400600101e00100000600400300200402d01d00900000400000002c01500f00102100400b00300000400700100403701301700c02400000804500300102000100b00500000200000300001200000400800a00500e08700000d00101b01503400d00800d00500400101301e03000b05a00000005500c00001f00000000200002d00000000300000000602600e00001007000900200001101d00001900400b01e00100a02700300100b00007d00200300100500300000500001300800600100200101100100a000035000000040019001000034003004000002002007049034016011000006003000 else 0x188204a300000b016830110a1866208ef904ace04d03064e0053500000d02e68648fd057700672802925096e4040dd053b70913000009019c405813085a8063100000c02be000bf000000000000000f08d5b02d35087a90741614bb00022509a35090170353a27b08975800000c0269c04ba603b0000007054c808e460237f0109a03d35053d00119c0758301a9414dec00f9000000000000000f03a0b08639074000000c00870000000000071f440471104a6f08ec906e40000000000d015fa058700000b050d2044b601f45062890332709855070b6095bd01f2b05dd207b4e7680705a200000a08234655530146412a4808f270299d043ab0598f09a6a04cc00000613c8d066a2042900251508cb5769b70717f0529b2673316a270914701c1b05dbe0250057d060275e0157d07320081a001ab301f7206af007266b6d18032b46550108fc10634500f3706383097500000000001037ab0763302ee000007019a1045510782000003050e506da1067000000a0216003e61058ae008f6009e00000106d7605fe70062104b3b060380225309afc014d30184b014e205656000cd076e96848508c4007b55055c808dde970b600e05013300000d0563d190800000ab551b02b3f020d904a4000003077700000a088d70510d03c00000000000000002036fc07bd806447079e405f6901f5000008070700000000007004d0000050571d021c203565026f00000c1677700ba0073790814c071f1032100000100e3000003035ddb90800000000009019f00000000005023b5052df069ee08ae605a8f064c606fcc0349b0869105bb00000400deb0474a028c0028ed192300000e02c060639a05b5000001020f90286401a2b094be067560127408fd1091b3243800400501701a00300007a00000e03e00900000101300500100000300e00300600005300200200400705200d00100200b00700b00400100700001005a02900705c00400000a02300000102301301800000000f00500100000700000400000000100200200d00100501700103d00000301100a00000800000600100200100000600400700000b00200000000000600000f00000300b00000200b00f00a00a02f02d00901500400700103d00100002000000000100000100300002700a00900900e02400300001801700b01103400000300400300100104500400900102300000800f00002b00000003000c00302801101a00400004600100d04301700000600600401200400201600000100000c00500402400201c00500a00100000a00800104b00700d00000200101100e02400300c00000600f00400700000100000000400100500000000100000101500000100301300100100000100001500d00400000100200000100900700000a02000200000500800000000000000402a0000230040000) else (if i<3 then 0x1a005130073071460e0053e0674e008d90647f0472a046e80656a072ef0163b06735169a102c760391404f40099900000000000000090981b040ef093100000000004030c8042d4190b16319c08640000090213800bbd01dd3035a9022b7066fa08db00000c0399500ca9088c4083400000400e73653000000f05cc003790000000128b06fba06e300000f005c307a90000070458d97be601e1a03cd405e40089640531c04ef208a40000010501b144e806d15051c4077f1074d00000805c36028dc0952508cc5099b9684ad04ee705c4a07bfc02ed3148a276f2b0258408c39063e00000808a0903b8e07feb0658c014f503f8d0950f090390017a02fae032400000c013c000000000000000e0131302f7f036a9055d1048100000000006085500000b03b9605a6805ecb03360000000000b07e500000a08b9605030000010381738f590968e621600797c016fd053af06d200000c0056106d9506e900000b077e8083300000f00aa00000016f02022f000006016d6056900000c013af16a3f0666708df708a2c053400000a0547507892028110432208f8919591047c00000b084b000001026a0000090008b00b5008cff73350000000000f063fc0186c09bb700a58003d00000605c800000e044d706a5db926907bb8058e4748a600db5019350385706ab404a5000000000070125d037f6023200000d059c70555000002093fa03402093a3025f90989a0980e08c9407fa70418416eda00005096b3060cc07ed407d9e02f4508d44015ed0705a070330066b7339919939083da00f000000b01daa096900000d00a040657d0520606fe90021607de107d700000503f559867c1795d0747602631014ab01547071b413fa10313464b9376ad504bcb0686c06a20085bf11b92267b405afb122430893b11fd804925022c901d80091cb087dc66b0200f2001c21021700000214c970974004167061800377c04b150637d00c6b049170850500fcc05584169140444f05c62007d000c366318f08a9b0918b0941c06f9d0352c009ad032e703caa084790026a0988627a8f642d8652eb09b5f09b3800f6f05ee209a94097f504fda091ad0650f017b405911039600000d08d6802fbd051550434700e6409b10033a206b25086cf0234a07eb205460097ee02a52003b1043630400a00e9e0966a05cb416bbd05b6276977042500000b0301203a1a05e32868500000605a5b0115900d1a87fb10099007d5908c70000020261501a66044980935876bb3049770409b0720502c21043de0706b064b5631e206dcc052c5600300000614cb00000606c5402a000749000004046b10857b031d2070e8084e2069f20294707e0f003cd07a3e064810507666b4d1413b013f308adc06c080715a08351000f1063cc005720431b0320f050a5078ca01b1001c710502905b29 else (if i<4 then 0x4067b6031250239c0227d00f49867ad13498155560911103d10000000000505be000008041b9051bc057f901edf00d6c06ee000002007c248a7508f450372a02a4e0700b04d730278107adb1698157237063290953a06059031630998f06dfb01be7034c0000000000d01a47032de63151084000000a02f1a043000000b14bc90596000000099ff00e13037150212804357026cf080880388a092e807c1905f3000003092600000304ca205ce50689d08d25769e10254f01fad08c8f0562764001071ef065a803d8c14880000050725c06be7899f00000f08e8804618588bd01731012e70247d08824690f00000d65379096da089a6074a3084f0000000000c01de000007056e00000905a100000d01f000000508f7000003061b60383000007090bf01dca15116069380244a09389032ac0020b009b90459f0480c77074733d301408085f000000000090519d05252018900451602d6606bd30885813304075400000a02f2308521073bb07c0c023e00000802c900000602d5000000000000000e010c103f7e27e21080f0000080448000000000000000000000000000000000000000000000202bb0000030767802ec000000000000000907cb0000000000d04d3d0613a1846000000000000000f07cf8099c00000c06048068ed07b02080500000203ccb02c3007bad749700000905f74059fe03e7000002006e5007a90723a04e2a017010145c020900000000000038f000009071d00000f97ba00000701df8069d0000041339e00df0000000000708e3b0597d07124001b7061400828e038b504ad8082600000000003038411535000000000000000f016100000c045ec05d6e13a8e087e000001144b301db108fed14320000060554d0928300a4000000042a81190303a870285000000000000000206cf00000417080000000000000000000070615107fb000000000000000e03fe103b7000008095de195200000f004cd01389023600000904b70052700493e00078036cb005970680b77d81053ea041d807c40039ff0064806e6f0096f0339e0925a0159905a050272d0817406f8b0394b03ad8046aa056c528fa80049703a7301a5e0277d067d8098c9049cb023dc0270307d2a0082a04ded08c2e0019f0414a05fac04e5202f9d05cfa055e507f28060900433718fb506e190370b00c8a0374b03ddb07b9208f1008a6205f8b050bb05c0e0010a09070133f6091ea03d7d05d59647880871a04ec669a440663503fa10568e082b30266614f6706f070559f025b5048e909a57058f0065ca05ac900cf97677903aa7073670599309a040594504c85045d672a43063b00000e01786041900000a05df206cb00000604d14090c000000081f109a1303ea00919706680000090309f015d00000009550048c1057e307f910543208e65023c104bb204 else 0x1184668280333c015330949c012280856a147360922900eec0646c092ca16ee2015540359807812047a40415508a1c00e4b0441a02801062b508620642e6017cb090d0068b518fa80798f1132a025e70207207cea04a0b029d603c480962e05b4707e61066b7020e311fc7065e108a710135804fe80308807c8304405099aa02b770773f06c7c04cf703612648d505e5905b3901c410211c084d6075c4048a108d9f09ba10552e095f1044af04f3802cf205905097a201ad3018f207b1f038db01b9b0929b019be040c164e5f08223078bc013e3044e2098e319a42056b300fe501fb2013261478b027cc07c2500b0670031071400000f057340820d0509808eb1003f903be5052e0000000000d043700000a0734c03f9e029c705d1c05f0e07c7d002e20764b747140231c00ff00000b071af06a400000907115052b00000f045f000001021d00000000009007170939c0830301f1f04e6306d8a01f30000080160a0612c074f604bfd01505004ec06695060220652b0951b1849402db60946400ce6091de0540902c690825c0040c0729002a86090e1051f70121400a8d05893016a774780024a903cf106d410876b0061f61ca10039d0514a03f190691109375092ae086f3013d805e920386000000000000000f034200000c07db0000000000006000000000000c001800000e09b7714f7002e1d049500000a7683006c6811a3db933614e0002d747700b041c9070900000f07921084c00000205ba908757076c800dc00000900cdc052800000d07d3d001c0000000000a6700611e8c09aea145130050d00f5402569081b0078f300ed906d050523f09b4702da0000000000000007002c00200961d10000000000c03d600000000008006b00000508bdc77d000000401e500000114a200000507956077b000000000000000d04264007900000d0408002e23005aa02330000000000000001035c903fd6073eb07507061100000a0900902e8b150d304c4f061e2048b90032508ee0000000000102b8c09b8f00f7302bd000000000000000e05ca00000403bb503f6d057d802cdf04670000000000f025d0000000816f022d86677401876029520375501c8805aeb020bc02d4b00d700000602b2108925089540360501a1a039860692b009f30392c06c4808ea6000b8066e4016500000b16ac000006017700000d003a308ff3018d00000b0676802ef000002132100000a07ab1078de03df606f60000000000d036220721604dd8004a10098a0770202fdc05e8000000000000000c8674d0166302e7a0916c024b00000203b2502f0d01a0000003043c000006036de010700000c01b80000000000d001230841e0915e01c060276b012cd04ae806def086d008f0603d9c648a003b3501ffe05e100000000009b931902ffc0866f155210478007e970811))) else (if i<7 then (if i<6 then 0x6b0310f049a102f8e004450410b08b060001e0877b000d008b300306f9849f01cc00094e06a6f03731014c26234604427061dd0906b04984006a503e2706f4a0067508f90028280678e036be152b6052f60421c038c40108a6497f08274027440464a0249305b010867c04e7104aa0748fb049f60328a081ea0899f03cbf02d0701b020387907c9f0976f100300097206ea8021fd03ce8059560719707e76068331848f131e9017650530e06512023af01749065d1769f654bb801cd9690eb01a8d0948100235108c006b0608043037cd05f5000000000000000000000000000000d082fc01175036300000000001031570684e0921108e7f0933d7698f0047c0661e01f8604c650743604e380517f754d80438f027ba080c10556b038aa0738908b54024e7049db07f4517adb0838307c3e0105c752e107f6809087087f56424e08e5d015cf07a2a046f400b8d03470099160704b09b2207607075a104c7000000000040341a0003000859180f60971301677043f60265502600000060279000006007bd0447905d9a01b5104a110654e089100000904b920214908512007eb0956103170012a3073330671a00867646fc034e00000f06874076ae07a6767d07055ff060f477d7a05748039710289900f88055780068f06ff806ba96685303fb0000050983b0621e013446500402dd607ff307ac00000d03c1b095800000f005200000000009082e000000005890051107247066c204f0a07d64027d707af8006c7026740325f03c74140090016e032c20506005c5e00b9d02a7000001190f0061050582604fa60964106ca80222c73335066de1770d01813152a80810b06c3d058430791102f6c07da200358058b002df818e841214c07a16076d10890706b4c0137204a7b05708016ea784a302912070a90630f7210505ffa04e9b08af40942e04e4407ead097c00000100aec089d00000704fb303ed40496010e9000009073a708ed40069c018540334f07ae60376803f3b002b00000c0694f028f70768a091f2068c00909d08d0b096ae0842d0954704bec13d6a08c59094766532b14e2209a4605d4b02241008e605b740664c093400000c0845a03140000050766e059266910597dab0029901e72061f507b820818f08def0005a03bd0021a7047e574e6b0787504a8806d52012f8069c0000000000e05fde088bb0111e0775e0078f0319d06b700000600dac08378040b3030ed005f00000c05bd50245507f1b04d6803db102bc00000006cca07a7801b4e06e00000080836c052a5024ff061a027fb80304a040f304204093d900c530636801e4104f6207a8104c0408d8f346a7031190025c072f402b060642d06bc502ca800e5b0101e02a9e0453308c6a08137054ee069730253e990310287a07dd9039d606ce002fe3090fa0466309671099360 else 0x4c100000d05003059d5077a0000000000902dee0586801c95077d0000000000000007027fa0149d09ad6140e66471d971230655e082c7052100000804f7f07a58844c00000f00c1b08f30000000000000000000000000f146ab06b9703e800000704dfa00a3208b10048620411d084450902e11a550476904f200000401afe000a00000c01ca571d1000008119a816cb000005016c319108017a46543f04c5f0318f051d657de308a8a04cdc0095108329054ad0806c046d707f70000000000000000000000485a0567301bf000005038ef0182c028300000608a3c06f1404f12039a70545b09618055160708b71fe0037d8074b60307e094da0460508e24013040713f03de00000964d8e095ad0081e000600000101471001a3868320488f094ec01d26071c714c2c0382b134460401901907089f2042b3053c0016460229c0264103935066710608e0106c096f10390604f850662802b6f07599028ba044fb03454060ec061c30063c025ac01624075f0033d0001400439205667144550522904686050f41010101565003e60483b07b2a033800000a0623301d600000e07f5c00c750785d1517a058dd080900000b03bf00337901ae409b670802305efa00fb00000403bce0799361df3019250158f03dcf06f2998a770870a05f2b040551347a648c802ab608aca00a700240b08dca079f508b4300d500000205d700000e02902073d00000d04d800000f0142f041f4072b00089e00f1103c2d0354e029e81216301bc5089e0025c800b410175a004fc005b70880a01aa305c9900ccc055b501ee4057bd018370479a01e6107dc30624d008a104dca047b000000000090923b0465500777a92d00000e742ed03502018c00000b00cbe063a207790000000000402153076200000503660000000000a00d9f048d008290000000000f08499099eb0793e0649e044600000f076100000905fca680fa0995204abe02eb6042ff050510038000ac005e200843b031ef09177098d5064df022100000000000000030060f05ad707e200000a07bcd047db04a26019730210500ec001b7e013b00000d056100000505c7518a7805d0b06c9502625075da76c1705a7604e0f00dd7080a608978021900000e0735609b01078e90625a0769971ca000008088f5015a00000c06266051130633806019087bb074c8019e1027300000407ee962a4400c03031b00000106d600000e017e3026ecb935b083bf009cb0924104af00000f05a39390800000502e3b00bc00000f148cd03b4000005097be093be0868d00a6213aeb01140081c106652018bb07840000020932e07e33092d406ebe06aac0427d0722b065f20575414574067ca054b10204604ed01340300d3807571053220549501433238319823605186009df0443a00fdf022350172803b1506a9f06f7c00b) else (if i<8 then 0xb4d02a2d00a1d0116203c800000401cee00a9e02a33083e20894276bc667d780979704da605e600000801c6808ba70860000a25027ee03f0e08b6805bc406e87a92cc07d01026d0145040205b0203d08bf20583904dba0742c0091806fd7068d602484018ad0815e169f606bf406f5a0076202b100202d049e804e16092ff020a5072db029fa060630407504b0203fc9096cb07cdf08a5106bbd0380b000e607515079a3008470013308f600000e0473101fc000003087ce062f96339a0406808d17148da03b5907f8903ec7167f303a4f09a7700736029390331d01e00010b606a0424228021b1098b00000608bb60541a017f50300608b80000000000d06c86a98b207f3a07655047fe04b85085e00000d008cc0526c03e500622607e1013d8408d7d00b790920d0268c06454010ab03e040499803d4e0728f669ca0235201d3d051a405d8b015ba08079030aca97ef03ac7048240120807f07029a7011d2001fa0524607fc70389a095c8169bc0452e03eb6072a0622e80494907968030370034205d3c1896902d16057ca06a14011c00027a07520143dd0046002e930643905dc900e2202465076b4767f306b87070ff078ac57b0a0428e00c4b0585301f9c0103a06412028ac035f50620c0537d134f10424c062710284b073f8746fc03eee02cbe06e5c035e0024d805abe07ca000000019941502913835083aa04d2602fca0357b057800000708fb00997e07cca0745000000090a00000c6907e069bb14ae10220d011e3018e202a60040356317f05cd00000d0074f98dc003d0c08ab0045a6035100454f08895067ed037b41462203c920778966a10000062553204a9f04cbf02595082d7085c3056aa07941093e00000a0718000000000000000000007094fa078800000107022062a979072048f000004022e0000000000205c2000000000000000214e56027ae075e3046300000101a3e07fd100ea6044c00000407836004bc0886403f42001d00000a11d1402c550241a0136f61d5c0075005eaf01f6003aed0756207a0766b14088100000d01eb0000010688f033e0000000831a034f6085d4036e80126800af00000000008054dc04c2a02c8e07270000000000507e4d086580943a0696000002066020619206b58a966d006500000265576042cc0271401e9409a2b1503f0699000001150000000d148b000006722e4087220243000000000000000b03e9705eba02d8405daa02d200000e068f401230000000000c04d4408744684920423e040ac5739509ac401bd106b1609907099d506c210148501e300000b0945000007033b000000000020677c0330701b3501c5857e2905480000040009b970f0b565f06ec802b9106cd2084a374b9d0910301cf902ea104840000000000300ef8096000000d097390489e05d2e03f26077400000a else (if i<9 then 0xc088e802ae40786203b6f036880070f0080d050c8098fb00361043ea08c1d002870824d067f20327d034b20037807bed021e30640e05a4600c980169e03a97002a501519019520888f36c690344100bd90490408be703a32094c7097d3006f60959000ab002e0e0753702f3106eff0579f071670417302bac03ef6073c00000d01fdd0043000000000000000c0457b04ff00000d13504b913b112fb082a6039c800b32026bf190e3093c000003079d00000709863122ea08bc609844087800000d083c0000000000601bb00000000004031c0000090607309b900000204f5e08480000000000000000000000000e041ed38a760912b0152b0102d098724908904699667f000000022a207b6e03a6708e1d0072f04b2d07aa30402a01240000000000923fa703e18039e00000d0113914c6a05932014b000000007fa089800000002bfc08cef04b5a03bab08619002d70803c061770588308d3b03e360088800d08045ce03ab0000000000906e7903a2608876085960092f09a8602e4b062e306ae50252a057a901e8704bd30744700d4000003028860139f05fb2059ac000400000304778024250884e069a9245f6077c00000205f9106acc0326b092bf020cd029b0086b30041f011f6023000000909448063d708cdd023f7008b60305405f4d0364d1480706f3d04ceb01794149fc011a7632120322b0470a05f100054c01cbf0801306b60000000000808f5f080d708b700000306a3f05e7b035800000c0873801ef0000000790201fe803d2f04fc70681c0629c053f000000000010564e081d6070d0000000000316b3a0755b002f16517300e8e030da039b9017d506a71011210572408caa060d6056d2065b7622000000b04d52044550090b001500000b0206707ec6684627201f05603049b10129406d3207b780553000000037e0000000000709aa9064fd02b5a01a7f0542204f94088a405aa90450a02286030f501d710194c001e1003300000300fa407d401966b01b2f04e82079b3055aa76c4a0698767d8e094ac0218d034ac09ab901ea9046200000b090500972000001074e20653c0508604c30060a302aa00000907df60030000008020100000305de603697083f40257201003079c0000080982d0104602cec0533800d8000007012d00000b085300000401d000000e054f00000302d900000405c1100c29010e703e4b0879c02cc00031a0141202f5d060bf01c380512a071000000005ede04b6801ac40883f0296b025550772c06ade05e0a03afb01d40000000000416ff006828b58600000000007098a40635f0780000008119570821207767067900538d000200000f07a4406a81005e000000000000000f6908600b2000007076f00000502c49045610978e05167032fe010d208b2b0930c059b3077100000a09770032900731902 else 0xf48b9201d1b0413f0576f04044062ca64e600000303d50000000000a0343501baf03c56058ce0422803da4017100000800ade14ec7031f6690b5016b50580802a1c06db000004064a80550403676094070927b095e30701102ac9019d60746007d1638b9a086eb02e5e01eca6488e07e8b04eb708faf0191e0208401b6c6535307c5d00b180346500930000000000c001100000800836056fb00eb6045b60024a05b8d01d51031a6005d203959080b107481033fa02afb0144e034d6012b3169e604c9f06dd2068500000204d980055a08003099400000f053900000a068a2011bd080e0000000000f06ed0000000000564d000000103a59655ae07d8487b0105b150048c032310335f06b3f043b9018000000a085800000e14e3401e2b030200000008aa408e9f0690e085416230400d20000020544e02dc9042e511cab0196e069530297c062d1144c96698e00454035be06fa50970a0992600bef0504d089b207c6c010f503c3602c1506e2a033cf07b3b061630839305b9d02386035510042b647320378c05a9e0659b06c12019800000216fbf006d2086af0846000001051e00000608e09046c4029800000203ff50812b842250365002ad70412204eae03c62108dd059e7070c104b4407efb01d90024c008da50965709573053680475a0226e0487466ab40348309367089c60996209049030bf0963c067a508c0407395075b3072cb0819705bf))))
def hashf3563l12 (i : Nat) : Nat := (if i<3 then (if i<1 then 0xcd900000a21c00000303ab00600101d01000800002900f00b00300000900b00e00c00600400500003f00f00100201401801600200802700600000201102b03c00600201500800500400100000100600b00200200d00300400100000100a0100c301000401f00a00000201200700401900e01000400c00700200b02500006800300300201300601900100700600600d00701200508600000000202200203700100400000100600002b00000f02000300b00200f00000000104a00100800100000000300000100400901300800800001500300000000200a00400600600000a00400500b00f01600000000800000000d00800001a01100001f00900300300200001201d00500300500000000100200900200001900005200b01700002100301400000900300000000101500200000900000b00800100907200600a00500000f00100300000300a00100400200000907800300100400000000100a00100101000600100100000000000100300000a00300100500600e02e04500200100a00000100400500100300600100500000800000e00600100700600000000400001001a00101000201500101509c00302000100102a00a00000803c00700d00c00a02500000500603500200900000300a00100001000c01300200101600000101100c01200900604e00800000200000103600000500100001800401200f00200f00400d0010040080060010090000000000050aa00000000500000a04400100200000000300000303100000200701000e00700508a00b03800103200500009400101b00000700a00000000000000000001001200000d00102b00100a00200300000000402800100000102700006f00000b00000000000207602900600000600f00b09401c03c00500300000106900700005100002a00400004000a00800000600000502500001400900b00001900100102100700201500900100000c01100400102700100e00000000000e00701200000000001900000100700300f01d00c0bb0280050040020ac00100100001300000000100304201600000000300000003f06e00102903e07100001100a03200a00002d00101600000100f00001300700101301601d00402e00002001300600900001300c00100000900501c00000400000200401102201000600003d00c00000001800000000100700600201d00001400901501000500002500000700100400300100008801602200000000c02801e00400400100502a0090070000370000010060660b500700100700100000100d00404a01501600100100900100900202902500000300a01d01101f00000000101000203401200e02000f00200700d00000402a00100000e04105300000100200600d00900f00300800100201100c00000300301100001c00300300600000200e06e00100f00e010 else (if i<2 then 0x765fc00b3582a228125b0578e192a02da10514b125fc012a82c5b8074a01812037e00beb348520565c07480318b02be61720a0557c0f7d80b130127011d1c06e4802d501784062041a1e8596b01b4a064841ff602ba00bb5afab0816930645e013782c05036ae36a520068a19f901ba806c9208896152b58b5005728047cc0f3d42e9604d9c0d8f60cb3c172d01d3d0252c1135820c30092d0b99e14770368f04a0908590cc818348d00e8e0955e089d410ae85777040c419f0c174806ba80ca5e0f3303237828690ac0c158640b3e03a4217ee005400000580de2016ec160b03281049fb0c826158c027dd03ad90bf2418e941de60441200b7c1653001508c507040fc131481e3d80fcd0ce6c02ab82664807f666e6c0e5741a63822ed09382145800007061bd0187c15c481c7e0622004810139ec2d768409800e4e00bc0208e831a50577c085a80f280000d031820d3f40e7f027060cf4417a480094860600001c1990c07bc02a550909c1497c091c0c6000000e0719c27ed866dc09c4010340000685eeb09622031f8254380ae4086c000000012205fb900e2e1628000000000f0d6160c9cc0934816b0000000002404e20199000014000800002017a70da0cdad9412298481a0317017f2c1519024d20c31a0ae0c10600000b07bee0e01418700553e092400002410000000f099c00001c2f6300f9876f660acfd882601dc00001c1168c2f2002dd00000000000000000006013ee2d93c1f3901872766c80152c0700845c0000000001017c8000070ab1e25d841b4e824f0000140986035ec05a8a0b20000024227e801460c17a199f033cd8464a086980a84434fb01fdf00fae088659bc4027c40ad88072e9825e868620b12e1612e268d0627200d4007dec02c183892017d62db70100f85dd56844ecde6c12da81ad109a9a0c16c09fc03847162ce0c8102dae05b3800734099040a98332f6023241abf197da86b510353eccd61b65a02cb70309c108c811fa0332b6c3de17561b51f86cd9673281829c12d78b6a30157a1276447bf8133d0b5ec17eb4125c85d920206e0a124120e807e206fa40e28407f00512300ba20b9902b7cc4d6d086621a1d5d90285498033e0076980fe3029620d68808c4829408278906c6c075700c1e821fc17b0a11e91dc0a0175e05da41aecc2fc20565f029781b3302e1b0574702110188200ec30097d1a618142a0316b86a4a0d5542c96427fc80f550404808a90140a0064b009dc09b6c1047852680b47e18f34237a8b1330653228f241626050600c2dc07aa802b485bfc0b74805a382701012d50146e0fd540c7fb6acb078701b3800000000020adde15b402fb7034730164a05ee031b30027d00b32128dc0a578cae406320000000006092380a9a000024096481900000080de782ae9841a81cfe01a0000000 else 0x322833816f80000d060200000414c000008064a00000000048147b02eda0034414190573b06ccc065e426ee3b0930695e0d2400000833be0d18e2c8e02ad20391906f140c77c219483d64074bc1967021470362b0407c074501a0602fa50afea082f4223000004064300274c3084019ce0591c1a0c42566838d47cd40000282512008b801ce6178e9da06045040b7d206c15e11384b8a030080c8ec241505cf00046208400367d836ac083dc124242a93041c60a8760299c1df1865ca0856e10a701931013731708607920047201bd20a98602f6420b30057a095a61519c243184cba082a20dc98312f04d8d041d411f5807d086c6e08b24184c42a850494f00a280cc6428a8b6cf0000000000816128094000006043743589036b10d3200002006de3e20420e6c199b418b8000000000a0cab4002e85c0a034d614688000f8485000f94110c1dba684bff06f424fc00129404b4409f521b15c06c10491a0725806ea81d93039f506e181ae40195d88288025e21782c3564804b07614e06385b0b00000c085c4114800007031c00000000014310e00636037c00ff1c641206be00001414460270c8665c0059a176f1b54105192071000002c1c298b26c0c96370374259a352c00000a1adc0000400c8e051800000848400000509d4014f605bc980d3f08d9c1430d9502859d40c48403adc133fbc867038980ea84327783128045f21647c271f0541a0b6340a4600688000040ca60000000e84800e000018017fc1db0000020bdfa11d54289c8144a04d24183d020400000e0cb60000141d18000040346a13d90216d03e800c5200000e1bea8341c1615c05a4c3421064cb05100000080fb28098b614c00b02024060141b03cfa180483300000000001c0cf80000600af00001a1634000000000c03bbe0da28183c82daf005c603678209684f1000000000302a0086ae60613801c2013bd0651c6d88802254340b03d230a77c163f41b8b84cdc0a8e401244056c02a6000014174c826900000f01fb01741410d38025e70aa00000000020500d0879a077a00a6f050f206c200ada4052202ac56906206dbc15ff0339c007fa0bca80af2041480bcfa002e41f34006ca02a26005541b2682f8000dc00eed18db3016380aaec04e300ea5855120b076131941392810a00500400c7c1cc184bbc0c6980f8187680023b801d861077401c30254008494101c02f92815b50c8e00c8b415ea0041909320c29ed984a01b7c13f4e1a82dde028b183044b8f87b41e56058c80acfe0ed5c13df0638c08bdc1a9d418b382204020a421c742e2ab32dd00d38111e81ba7068ee0916210c6c36500529a09aaa08e38040a804cd053e6098d8249e85ac30aece03efc260983ebb01674e1408205702dc36852611fec1f090122e05eb819abc0047853820525ac487404618247)) else (if i<5 then (if i<4 then 0x70198586c0903908103ac03d3030db04dfe0b8fc163a0663207f2417a882ad832faa0c8620bfc000058b38e01ff002180000281a5000000000000000811ff0c12000011c498865a00000000014710306827037ee075a1dbf2819a803e4e09c742b480000a02900000300b700021f073200000000000000000000000000006819d0190aa15e3419b806582072c80ea240b9989b310c7ac16648254c86c83023aa14b740f4f823200001e31aa02bcb01b830d348137c0000401c50000121922c2578000030473a0e85c099205371063de30e002067052e401114148000000000000000803c0000078856c074e00000434b000005133200002c2b368406848cce01ac02300000000001c076f01b3903830000102e3f4090e81aed086a617de007480131a04bce04540000000000000000001034f0000000000000000000302d870b2e224a4c0b2901f80000000002020b8060770a55a0e5f81dc00000200200000000001035550279e0ec601fb80000c09e920bf4d9b6f828a30b4a000020178d3050066f76051800002003d648aa6011941d0000000000060aae42747808a7084ea06830013003f66020de0bb3d9810000080bb806668000030257b09f140db2c05c1827f908f2000008033d02cc409e6e1900000063e6b0000081320800c88077f0105e0fab806b90114705266f0a64028200a97096c00002c19e88299a03db8109980d0a05de30afb208cd010ca00bad0a7daccba01298019b50478cfb1adb6948279d0ac8808994067fbb13a022c4130b0032980352059f60c2100fa906932014e8088ec3171807360a9ea0ffec25ca0251e03e7819d8c07b7050e10c34000020071f8587106bfa5179012b480f350b316004d4222a84b7529ade0d4180bf80000e07f700d5982f9f846d7071800002c29a5347f00000000000000505f10000100b17198e000000000000000000068b3ce00ec611a9475160887b02558094180c8982e710b100000100d460535609144092a5a57281ee207cbe18c102626030c30c10212d6800604ca360381a07674362705e6102c0806b380141049e7226ac16c9801b08b30e0bea61176800200000509d7807840000585fef0d70e085159bef02c691223e123182b400000f0c7ca19dc000060890508ac00a0b82e5a0079e0b8e0000000005dc2ce003184184000048b9c0000020f5f80b7ebb7d20a74615a800003867b9045840f15009f30109209cd804f5c01e005c90000000002402398639b039cc337c41e738237601a1c0d5f000ec815d2030460267412fa0404f0a12000030098000001080600000c2af183949070c00000000063434006fdc28280000401f1008d000000000000000000006c41c0000383fd000000000342eb0000000001211a6418590178c1aa20000302e40000000001c0317197e00000409d else 0x3850c19308be20872c1a5a010ec024f8167fc2e3184fc50780c00c841d7c049630469a115480cc083246051f819a681a9383e4603872edcd40b0a832800b6fe049045bd90524576db40ecec46f084d3a084000001c09ce00f2408f122bde00cab3327904cb80312000e000cd9661ca106c431a9818550a5ec23910241a8085801848185e40a4d891e60899c1684428b90439707210001ac1364b96a204986093a4196c05fd56211ca6ee41ee981b140cdf21b0c40a7d031fe0cbce125e41d6283c4209cb018bd42826030fa062980bab025708586501de62c6a41374020d90150609abc23f002e8e09116053900ff5827ae0ab301a2182818814c900df409f8c2f2f0ea3807972da88044af844ba10e74187482dc18689b120940efc85be9852b8051bc1a98406a58e161689d2068a42995061e20b0260d3901226813ba0d306ee20c2e6a061960d79a0d81c1da1009ee0b352dad75d7e3055477647013464759d05e200c25616555605f01e870b2760814000008140a18440000341d77087ae0c2b4003c028c086a3207038f0d0d9e1184ec709de2045e810548655201aba1899c2de8000070ae042e8945c1c027320af520707405a585b67054f82c8b01db90246f8a16609d2c280c03d1e17320000001e9800005771200002c59200000015ffa0027418df01e6600f641671c003c00b64056ee1a34000068527d0792019d383310886f000000000140e680000b0874c0b89c2de60440d0c5601557c036b03d50000000001824480000209ebe166c000000181b0a040096400003010286d4000000000000000a0a3600001c0500847ca08ef80ddc000000000f0c9a00000419e181b500001212c0000000000f0704a11cb4356a8318f0d15618034064e84f7906012015642dde834d4099fa129e80bf385a7908ec00001c31b800009068540782800f20162802a9600ac427900000c020e403d30026a008d407b320a38000020422000000000000000000060cbe0136800002829b3767e00001c24a80000301c900dbc00000000000000000010643000007059c00003c1b6a829d306e600003843c80000d07d920396431ff817100001e11cc000000000b08604e41b4290800000000000001c25e4012b80b1c2023f429b182282055000003834e80000000000000241be000000000160ce8000018164101a4cdaf3414d48ecb000000000302ab5050b0000100400000000000e0448000000000486d3906bb00a1781a47857b5161200002012ed81dfd0159d2512004aa3bc2d0517c15adc04d38685a08a8c00c3416f1bc8350314e11c344444835c803ae60d68c230e8043509f24033942d6d8062d0ba980a50c425986b630a7e413c0c158000f1e144400002425ea85e1d0ceb22c6c425d7046360408413724042786a570424e0f21c01f28376a0cf141b) else (if i<6 then 0x4ee00001a0c110407101189078cc06e684c100000406b3e34cc0000084668052ac14734617e015fd0b4580e6fc08f4864f40c0800001812e00690105a2000000000000000000000002c18888068205b200003801b80000b1112603a8000018642b071c80c4e805dc84de304360000380ab0000020572834b40000000000000021a6c000010128205fd231ffc17580000a08a74121dc0f100000000010320ec161c9c5570689e0b5000d980000d0964804b9c065505fff0209e1040000060b55005ed003bbc179c840b004912004400007035100000a01780000000009047a00001005a982e0e084a00001c1b700000702b08c29400007020f304878131f0252e015a802cde061800005011000000000008286a5467f0c3ea06240000200bf00000219a281d3103d8b010fa2c3502a2e01522008a000000000000edb9798c135fc1dd382efb7643c144082e10333c7633180defc16b381f0208af22c0840000011cc0513a18a201a35060360da4203300000200c6107b5404d741fc382ad303d9aeddfc19af048f50274a0cbdc019880c140a9600001830280358704ec000011998701ab9008400b5fc27f4062aa02188069f41f49021db012022c2e818830671501c2c06d081721361a2054000abcc7624011b80893a0f780000000006014280ad74158d820910583e17120296000000000041617425f0000000475207ad414f782d0d035f61423df61a8623a045600003830140ea1205b74064d41ed903bd407348195ac033601cc805e800003c3060000000000e177c82e7303f300001efb2881d840562e062a2087a01ea50262e0d85611600733c014520101c06cbc00b905aa202416cefac0ffe03a900000e3af2c19a582fce0b41e0a438324889306001501911da415049a80d2a819fc5980c0016104d000002402400000904928195dd98060c0800a90a0b54000008b2de0827c18cc40d52062c80cfaed21bc2e8e0442b0594610ec029148462304b000000819f80000000004050c00000866ef08554261bc250982220056800cba04cc286d40176b21290000000000f00f12099800007849b0000001a53d9e0185f40000040d78435488142b09b7e072b02bf38580a0bae405b783359844e20d5000000000000235b06156024582240051e4083200000430a4b055a02f3615734217f0052602b9c13b6c17818111b045200003401d00000511072172a0130482a4e12280000301b2b846bf08b600003dc495046ed091c8cdf24087b010120d67402e400b9405f000000c095400004019e60b72811c64228d869c30842404db44dad8196100b96103ec17748c4d0000180110000078338d76792157e407c101fad0d44808d8c10be04c99087d007e501f120306f02ae816a643590000000001a0ee5c03a80000704600000345b9d8040a7c3a0000003 else 0x50ba57042600003033600000000016183a81ce00000965f0a1b2d0347f04ca4003400000c00de03ed6083e0000303493040570c2320f434299f048d2012d420218030c81947014b6333e8225181bb00001e100400006017c60870e17b78116c8672c0145e2176dc82000001093000a1d8199e81a400000a044fc0e11826be07b880e4d4403b035400000000034058781f4503c600000000000000004fac086000004847b5066d80d6c00de485a4e0744e18ef8169f00dd000000000341a2b02a9780c200f8c00658bbbea070fe11940000483c230a6200f34000078c0c71d9f005ab8001b05b0403f78100b0255d8159b16190020ec283a8b7c410bc40a5c0000733217007640d4f58939811200000616780000000008021600001020063b33f120fc0fd200b8105d8f00456ec90021f932ff9003fe13030108b039d00aeb415390155505eb6009e0000000000000000001e1a5dc233d029c00000015098350d8c0520c64014e60170d03fa8038fc19848030604377055c4090a81f9281349031b605dc41bfc82a22087a40c09c2d36068ba68b400001c1f7784d000000405b00000484a661d6a2cbf581f84805a00000e170400000000070a3ee00a6428280000609c840fc501cf28275d09874046800006002040bd1a05d102c9000000000000001c1f79060d00001c3b29407100000e060780358017b9057c80a4681afe429e00000f0b576072445c3800000000061952582b70053801cd80b24c1e0b838b10cba414c0830e00000d0d57a0bed426b38)))
def hashf3563l13 (_i : Nat) : Nat := 0xc054400b80210000000090710000304d0000000000000000e0202046a05ea06b0000b077000000008065202a9018e05700009729712400000642e039502c100ce13e4036105c6105a069a068000001210061e017106a0000c04bc03cf003a004007d10517629c043e05bd07b7005b07e405aa04200009129702de06c5049507fc013501f2034d060102e9032204f3140000040100023005f00000000c0260000d0143006d00ef0350000c024c0790000c074c0450000000000750000307020410000f052a028a02b505930720000e03de02f00002084003f0000661e204000007082f0830000571ee06e07210000500f406f40660000e776e73f0000401c0000e00000005742a081d05811420000913d3033000040640000413f601bc621212ed04a0000d00dc0099007810ab029003e663b102500000000504c00000000b04400000011005d00000000011e000000000000607390539022000000003143100140300000b062c07c0000d037106d663c00002055000000000000000000000000100a000000000067201e0000904e5002a01a7047f050000000000000c0480000803a4012000000003125c07a1016e176303be0568031003816766008763f5015c01d00000000f078000000002076f0634019d0800000000080270701010302090700060000000000000402070104111000010006090001040000070604000305011400010003010000010200010200050300000100
def f3563d8 (_i : Nat) : Nat := 0x294304fcc675ebb6a15246540c1af319d4aa9b85c53950286bde6aedc4aa9814e540
def f3563l8 : Packing := (3,7,8,0,4,4,0,f3563d8)
def f3563d9 (i : Nat) : Nat := (if i<1 then 0x72a061bf328b66c9814e540b35eea5545b3029ca8146fcda6dcb6605395020ff9b4e5b0a10a72a07d1d5d9655c5514e540f9b2c12a4c0aa29ca8107fddab31b548539503eacae4a92e2a8a72a059ed752aa605514e54083fe6d396c3ac29ca8147bdd4aa9b758539502cf6ba955302b0a72a059af752aa589614e5408afeebd98daa429ca8165bdd4aa9875c539503e9caecb12e290a72a051df369c86d4214e540c37e6518cdc2e29ca8167b5d4aa971485395030bf99463b6a90a72a051ef752aa6d5214e5408b7e6b396c2a429ca8107fcda72d854853950307f9946436ca9a52a0457f75ecc6e1525a540c3de65370aa2c494a8187bccaaed54609295030bf9945bb66a92d2a0553f75ebb58d525a54089feec598db2a694a8145fcda6e0b7549695028bfbaf5dd54a92d2a041ff369c3aed525a540b3ae6d306a9aa494a8185fda271ebb54969503ec5acaaa2c4a9252a04cbf361c654d624a540937e6d38ca9ac494a8167acda5518258929502cdd9b4b2b04b1252a0457f35dcb615325a540c3fa58b835551094a8107fcda72d854c9695028fb9b4e0b6642a52a041ff36dc1aaa884a5409adeebd98a9282b4a8185fcca31db854969503e39b0eb9b04992d2a0596f752aa5d9714e540e2be5d16ea9aa4b4a81f34d8354d8254969503e2db0ebab04a92d2a07d535cd535c9525a540f8aec3b0ab9aa6b4a8115fdd7b31b54c9695030bf99463b6a992d2a0599b359a89562246540c2de5d38e42a8294a8126ecdc6a26688919502c9d9acd44ef11232a061af2d9c4aa9814e540b25eea5553bccc9ca8145bdd4aa9b7205395020df9b8d436c29232a0517d345ba2dd525a540e19e5d5112aa8294a81c53cba9de55505295030f7174e010aa0a52a061eb2e9c2215414a540c3da5d38242a8294a81c3acbaa2222505295028f69b4e236242a52a0593734da89de664a540d2ba60ceed34aa94a81c72cba9562250529503857975444ccaa252a069ab32a66552224a540b1e669b514444494a81a3accaa215488929502cd99a6d44cd11252a059d9345a6956224a540c37a5b3835530294a8186bcba71885505295030f3974e190aa0a52a0706f2ea889dd414a540a36e69b745b30294a8143bdd42ea8854529502cb6ba9554ef08a72a058ed752aaa22114e540b35aea555334229ca8167a4da5522284529502ce6ba9554ab08a72a0513f36da89de6646540a39eea554da8429ca8146bdd4aa9b6085395028f73a95536010a72a0591f359a89de5546540933e6e351334aa8ca8125f4d7714ba84529502c7a9a6d451108a52a0417f35dc52ea114a540b3d2ea555114229ca81a7c4ca4c93148529502cba9a6d44ef08a52a069ad32a66552114a540b3e269b511142294a81a3b4caa215484529502cda9a6d44cd08a52a059d534da8956114a540 else (if i<2 then 0xc1ae3485f8ba16a2c04e88a10a2003d8760e21b0338620ba160298400760d81881e0320500780a00a0020ff9b6e42ecd1232a07c5761d855cd534654083fe6db90bab448ca8107fcda716bb609195020ff9b6e3acad1232a041ff36dc7595a34654083fe6d3875db0e8ca81a7f0ca605514c1295028fb9b4e136642a32a041ff36dc85d9a346540a3f66d386d910a8ca8185fcc7aa9b8549195022bfbaf66370a9232a0617f328c76e15246540c37e63576d42a48ca8145fdd7aeda8549195020ffbb566370a9232a041ff76acc6e1724654083fe6e576d2b048ca8107fcdc6e1a5589195028bfbaf5dd54a9232a061bf32d6568d624654083feee174c1aa294a8107fcdc6e1a75852950287fbb05d306a8a52a0557b349b761d3146540a3fae9974c0aa294a8165dcd36a1875c5295028dfbad5db4ec0a52a061bf6a1c6aed814a540a37e6db4e5b30294a8145fcdb6a1875c529502ad7bad5daa8c0a52a055af359b8551214a540a3faea974c0a6294a8136f9d6b31814c1295024ff1b4e42a298252a049fe760ca545304a540e36e5d30cb1a6294a8185fcba71c854c5295020ffbb85d30a98a52a061bf2e9c6215314a540c3fc5d38042a6294a8187dcba70c854c5295020ff9b8d436ea9232a0617f2e9c7215324654083fe6d39642a648ca8186fcba718854c9195030fd974e110a99232a061f72e9c321532465408afe6bb96c2a648ca8107fcda72d874c919503ea9ae6a9ae4a9232a0457f75ecc6d5324654083fe6d396c2a648ca8185fcca31db54c9195030fb974e190b11232a061bf2e9c62162246540c3fc5d38042c448ca8115fcdc6dd874c5195022bfbae65cab11232a0617f2e9c72162246540c3fc5d38042a648ca8187f4ba704854c9195020ff9b4e5aea99232a041ff768cba222246540f8e6c3ae6c12648ca8145fdd7aeda6549195020ffbb465b0ea9232a0599f359a85d55246540a2feebd76d1aa48ca8185fcca2ddb3549195020ff9b4e5b0ea9232a0517f369b82dd5246540a37e6b350dbaa48ca8145fdda2e0b754919502c9f9acd416ea9232a0517f36da82dd5246540f8b6c3aeac12a48ca81c5ecba2dd82549195024fd9b8d1b04a9232a059bb359a85c95246540f9a6c1aa6c12a48ca8107fcda72d82549195020ff9b8dbb46a9232a041ff371b868d5246540c2fe6596ed1aa48ca81c57cba2dd53549195020ff9b8db346a9232a061ef2e1c4aaa114e540a3fc6d30ad80429ca8116fdd632e88845395020ffbb566370b8a72a045bf75acc6e1714e540c3be6536ac28429ca8186fcca6d985085395030df98d55370b8a72a051ef752aa6e1714e54083feed196a93029ca8187bebb712aa605395020ff9b95db4ec0a72a041ff369c7aed814e540a37eeb577553029ca8146fdd6aeda7605395028df9b6d396cc0a else 0x1401080000000000360f080060384001b873090800880960210741e10000480b0381e83c2c0e0581c090381000000000000000000000000000000cc383b8004000001987041987040006e00100000ac382000000000004c0420000036080000000000000000b81003b010e6161000b610001b8004004c0400e83c200001e0504000000018840384041d80840000006408390b0801b80840000000000000360210001b800400000000000000000001b0108000dc042f01040000000000000080010000028840000000d079fb3ce74cdf9ab32e60cb795b28e4cc8f90b17e2ac4b8830de16c2383303e02bdf7aaf2dd2b9b6ead3da2b1f5f2bbd64abf56aa3d34a4343a7dce89c737a6ccd499f32a62cc09772da58cac94f28a4ec9892723a44c848ff1ea3ac708bb12a22c408770da18c1e83301a00bfc7eef91efbda7aaf41debb8766eb9d4ba473ee69cab906fade1b9b6e6b6d59a8b4c68ed099eb38666cb994b2463ec3183b025deb716bac457eae95aaa253aa2942a804da9a131a5e4b291920a3c46e8c916a1a42a808fe9ea3ca780ed9d63866f8d59a6342638c49842fe5e8ba9702d6598b095c2ae5109f93a26a4888e918226438849041fe3e87a8f01d6398708d))
def f3563l9 : Packing := (214,6,8,2,4,11,0,f3563d9)
def f3563d10 (i : Nat) : Nat := (if i<15 then (if i<7 then (if i<3 then (if i<1 then 0xe75ca58cd524a54097eccb609524a540b76cc5609524a540e67ca5999524a540a77cca955524a540a77cca54d524a540e774a1955814a540c7bcba551514a540c7dcba8cd514a540c77cba549514a540d73db4955514a540a7bcca6d1514a540c7bcba6d1514a540c7ecba889514a54087fdcbaa8514a54087fdca6e0514a54087fcca6e0514a540d7adb4889514a54097f4cb605514a540c7f4ba605514a540c77cba955514a54096fcc66e1514a54087fccb6a1514a540a7dcc36a1514a54087fdc32e9514a54087fdcbaa9514a54087fcca6e1514a540c3fcbaa21514a54087fcca6d9514a540c6fcba999514a540d6bdb4999514a540d3bdb4a21514a540c5fcba9dd514a540d5bdb49dd514a540b79dc3215414a540b7adc2215414a540b7b5c1215414a540c7bcba215414a540b5bdc7215414a540b6bdc6215414a540b7b9c0215414a540c7bcba955414a540d73ccb955414a540f33e88955414a540c7bcba5d5414a54087fccaaed875a54097bccb955414a540c7bcba615414a54087fcca6cc514a540c7edba888514a540d7adb4888514a540a7dcc36a0514a540c3fdbaa20514a540d3bdb4a20514a540a7bccaa21414a540f1be889dd414a540f2be88999414a540f4be77999414a540c7bcbaa21414a540e3bccaa21414a540c7bcba61d414a540d5bdb7550814a540c3fcba609814a540c7edba888814a540a7bcca550814a540c7ecba889814a540e3f4a1609814a540d6dcb68cd814a54087fdcbaa9714a540c7dcba8cd814a540d5edb7888814a540e7d4a18cd814a540d7adb4888814a540c5fdba9dc814a540d5bdb49dc814a54087fcca6d4814a54087fdcbaa8814a54095fecc6dc814a540c5feaa6dc814a540c77dba954814a540d57db7954814a540d73db4954814a540e7e4a1889814a540d6ecb6889814a54097bdc46d4814a540d6bcb6551814a54087fcca6e1614a540a7dcc36a1614a540c3fdbaa21614a540c7dcba8cd714a54087fdcbaa9614a54087fdca6e1614a540a5fcc76e9514a54087fdc82e9514a540d5ddb78cc814a540a7bcca551614a54087fdcaaed514a54087fccaaed514a540c3fcbaa21714a54087fcca6e1714a540a7dcc36a1714a54096fcc66e1714a54087fccb6a1714a54095fccb61d714a540c5fcba61d714a540a7bcca551814a540c77cba955714a540a4fcc66a27746540c73cba955414a540c7acba889414a54086fccb6a26646540a6bdc4aaa664e540a6ecc66a22246540a7d4c36a2114a540a67cc66a25546540c3bcbaa21544a540a7ccc36a2224a540a7e4c169a224a540a7acca552224a540a774c169a554a540c5f4b19dda64a540c3bcbaa21414a540a6dcc36a2664a540c5bcba9dd414a540a7b5c4aaa114e540c6bcba999544a54087bdc42e9514a540a7b4ca552114a540 else (if i<2 then 0xf2fa88999304a540f7a55488a114a540f7c63388a114a540a7f8caa21304a540f4fa77999304a540b7d9c3215304a540b7e9c2215304a540b7f1c1215304a54097f9cb215304a540b5f9c7215304a540b6f9c6215304a540f7665588a114a540f756558ce114a540e3f4a860a114a540e774a554a114a540f5d6778ce114a540f6d6668ce114a540e7d4a58ce114a540e7e4ba88a114a540e7e5a688a114a540f6e66688a114a540e7e4a588a114a540e7e5a888a114a540e7e4a888a114a540f3e68888a114a540f6ae66552224a540f72e55552224a540a7ecca60e224a540f66e66956224a540e76ca1956224a540f3ae88552224a540a7ecca58e224a540f6ce668ce224a540e7cca58ce224a540f74e558ce224a540a7ecca54e224a540e7cca88ce224a540f3ce888ce224a540e76da6956224a540b6edc6216224a540b7adc4216224a540b7cdc3216224a540a7ecca616224a540a7edca216224a540b5edc7216224a540b7e5c1216224a540e76cca956224a540e76ca8956224a540f36e88956224a540b7e9c0216224a540a7ecca596224a540a7ecca956224a540a7f4c169d814a540c5fcba9dd814a540d4fcb69dd814a540e3f4a1a21814a54087fccb69d814a540c6fcb669d814a540e5f4a19dd814a540c6fcba999814a540c77cba955814a540d67cb6955814a540c6fdba2d9814a540c6fcba2d9814a54096fccb999814a540c3fcbaa21814a54096fdc6aed814a540c7f4a1aed814a540a6fcc66e9814a540e7cca18ce224a54087fdcaaed814a54087fccaaed814a540a7dcc36e9814a54087fccb6a1814a540a7dcc36a1814a540a7f4c16a1814a54087fdcbaa9814a540c6fcb6aa9814a540a7f5c1aa9814a540e6eca599a224a540f65e66956334a540e75ca1956334a540c3fca8aed824a540e75ca8956334a540f35e88956334a540f55e77956334a540a3fccaa21824a540e3dca88cd824a540a7dcc36a1624a540a6fcca595624a540e37ca8955824a540a7bcca551824a540a3fcca60d824a540e75cca956334a540f4de7799a334a540e6dca599a334a540a7dcca616334a540f1de889de334a540e5dca19de334a540f2de8899a334a540b5ddc7216334a540b7d9c0216334a540a7dcca596334a540a7dcca956334a540b6ddc6216334a540b7cdc2216334a540b7d5c1216334a540a7eccaa22224a540e3eda8a22224a540e3eccaa22224a540e3eca8609324a540a7ecc56a2224a540a7ecc16a2224a540e3eda6a22224a540a7edca61a224a540e6eda899a224a540f2ee8899a224a540e3eca5a22224a540e3eca1a22224a540a7ecc569a224a540e76ca5609524a540e37ca5a21524a54087fccb699524a540a77cc5699524a540a7bcca551624a540a6fcca58d624a54095fdc7aed524a540a7f4c1699524a540 else 0x87fdc52e9314a540c7bcba549414a540e1fda6a227746540f3ae88889414a540f53e77955414a540f63e66955414a540c7bcba609414a540f6ae66889414a54087fccaaed314a54087fdc82e9314a54087fdc72e9314a540f72e55889414a540a7bcca605414a540a7bcca545414a54096fcc66e1214a540c3fcbaa22114a54087fccb69e114a540c5fcba9de114a54087fdc32ea114a54087fccb6a2114a540a7dcc36a2114a540c77cba956114a540c7ecba88a114a540a7f4ca606114a540c7f4ba606114a54097bccb552114a540a7bcca552114a540c7dcba8ce114a54087fdc52ea114a540a7f4c16a1214a540e3f4a1a21214a540e774a1955214a540c7f4a16e1214a54087fccb6a1214a540a7dcc36a1214a540a7bcca551214a540f7c5324c5214a54087fdc82ea114a54087fdc72ea114a540e7d4a18cd214a540e7e4a14c9214a540a7f4ca4c5214a540a7f8ca545304a540b7d9c3145304a540b7dacc4c5304a540b6f8c6605304a540b5f9c7205304a540b7d9c3205304a540e7d8ca4c5304a540b7d9c54c5304a540f75a554c5304a540f7ca224c5304a540f3da884c5304a540f5da774c5304a540f6da664c5304a540f7c953889304a540e7d8ca54d304a540f3da8854d304a540f5da7754d304a540f57a77955304a540f67a66955304a540b7dacc54d304a540f6da6654d304a540f3ea88889304a540f6ea66889304a540f76a55889304a540f7598554d304a540f75a5554d304a540f75953549304a540f7d1814c5304a54087fccba21a746540c3fccba21a74654087fdcaaed8746540a3fdca2d68846540a3fdca2ca8846540b2fdc62ca884654087fccaaed8746540e1fda8a227746540e1fccaa227746540e1feaaa227746540c3fdbaa218746540c3fcbaa218746540a5fccaa227746540a3fdc22ea8846540f5f277845304a540f6f266845304a540f77255845304a540f7d131485304a540f7d131845304a540f3f288845304a540f7d153845304a540a3fdc72ea8846540a3fdc52ea8846540a3fdc32ea8846540f7e222845304a540a3fcc56a28846540a3fcc26a28846540f37a88955304a540b7b4cb552114a540f3b688552114a540f5b677552114a540f57677956114a540e775a6956114a540f67666956114a540f6b666552114a540a7f4ca54e114a540e7d4ba8ce114a540e7d4a88ce114a540f73655552114a540a7f4ca60e114a540a7f4ca58e114a540e775a7956114a540b7e5c2216114a540b7f1c0216114a540a7f4ca596114a540b6f5c6216114a540b7b5c4216114a540b7d5c3216114a540a7f4ca956114a540e775a8956114a540e774a8956114a540f37688956114a540e774ca956114a540e774ba956114a540e776aa956114a540f3d6888ce114a540e3f8caa21304a540f1fa889dd304a540)) else (if i<5 then (if i<4 then 0xa7f4caa22114e540e3f4baa22114e540a7bdc4aa9214e540a7bdc4aa8814e54087fdca6dc814e54087fcca6dc814e54096fccb999814e540c6fdba999814e540c6fcba999814e540c5fda76dc814e540c5feaa6dc814e540c5fca26dc814e540c5fdba9dc814e54095fecc6dc814e540c5fdca6dc814e540c5fcca6dc814e540c6fcba2d9814e54096fdc6aed814e540a6fcc66e9814e540c6fcb6aa9814e540e4feaa9de664e54087fdcaaed814e54087fccaaed814e540a7bdc4aa9814e540c5fcba9dd814e540d4fcb69dd814e540c6fdba2d9814e54087fccb69d814e540c6fcb669d814e540c5fdba9dd814e540d5bdb49dc814e54087fccaaed514e540a7bdc4aa9514e540c6fdba999514e54087fdca6dd614e54087fcca6dd614e54087fdcaaed514e540c6fcba999514e54087fcca6c8514e54087fdcaaed214e54087fccaaed214e54097f4cb605514e540a7bdc4aa8514e54087fdca6c8514e54087fcca6e1614e54087fccaaed714e540a7bdc4aa9714e54087fdca6e1714e54087fdca6c8814e54087fcca6c8814e54087fdcaaed714e54087fcca6e1714e540c6fcba999714e540a7bdc4aa9614e54087fdca6e1614e54096fcc66e1714e54095fccb61d714e540c6fdba999714e540e5dca89de334a540a7f5c5aaa114a540a7f5ca2e2114a540a7f4cb6a2114a540a7f5c8aaa114a540a7f5c7aaa114a540a7f5c6aaa114a540a7f4c56a2114a540e3f4baa22114a540e3f6aaa22114a540e3f5a6a22114a540a7f4caa22114a540e3f5a8a22114a540e3f4caa22114a540a7f5c32ea114a540f73655506114a540f7a622506114a540a7f4ca4c6114a540b7b5c4546114a540f3b688506114a540f5b677506114a540c7f4ba486114a540a7f5c72ea114a540a7f5c52ea114a540a7f4c52ea114a540a7f6cc2ea114a540a7f5c82ea114a540a7f4c82ea114a540e3f4a5a22114a540f4f67799a114a540e6f4a599a114a540a7f5ca2d6114a540e6f5a899a114a540f2f68899a114a540e6f5a799a114a540b6f5c62d6114a54097f5cb216114a540a7f5ca216114a540b5f5c7216114a540b7b5c42d6114a540b7e5c22d6114a540a7f4ca616114a540e6f6aa99a114a540a7f5ca61e114a540a7f4ca61e114a540e5f4ba9de114a540a7f4cb69e114a540a7f4c869e114a540e3f68869e114a540e5f6aa9de114a540e5f5a69de114a540a7f5ca61a114a540a7f5ca5da114a540e5f5a89de114a540e5f4a89de114a540f1f6889de114a540a7f4ca546114a54087fcca6dd314a540c5fcba9dd314a54087fcca6d9314a54087fcca6e1314a54096fcc66e1314a540c3fcbaa21314a540c6fcba999314a540c7dcba4c9314a540c7ecba889314a540c7f4ba605314a54087fcca6d5314a540c77cba955314a540c7dcba58d314a540 else 0xf7c63388a115a540a7bdc4aa9764e540b5f4c754a115a540b7b5c414a115a540f5e67788a115a540b5bcc7549415a540e6ecba58e225a540f4ee7758e225a540f66e5558e225a540f36e88956225a540e76da7956225a540f56e77956225a540a7ecca54e225a540e7cca58ce225a540f74e558ce225a540f53e77955415a540e7ccba8ce225a540f3ce888ce225a540f5ce778ce225a540d6ddb68cc525a540c3fcbaa21535a540c5fcba9dd535a540c77cba955535a540f47e77955635a54087fccaaed535a54087fcca6e1535a540e3dca5a22335a540a7dcca616335a540a7dcca956335a540e75cca956335a540e3dca2a22335a540a7dcca61e335a540f1de889de335a540c77cba955735a540a77dc32ea555a540a77dc22ea555a540e37cbaa22555a54087fccaaed855a540c3fcbaa22555a540a77dc82ea555a540e37ca2a22555a54087fccaaed735a54087fcca6e1735a540c3fcbaa21735a540e57eaa9de555a540f17e889de555a540a77dca2ca555a540f35e88956335a540c5fdba2dd525a540c5fcba2dd525a54095fccb9dd525a54095fcc76e1525a540c3fcbaa21525a540d1fcb7a21525a540c5fcba9dd525a540d5dcb78cd525a540d3bdb4a20525a54096fdc66cc525a540c77cba955525a540d4fcb758d525a540c7dcba8cd525a54087fcca6e1525a540c5fcba9dd825a540c77cba955825a540c7dcba8cd825a540f55e77956335a540e75ca2956335a54087fccaaed825a540c77dba955725a540a5fcc76e9525a540a7f4c16e9525a540c5fcb7aa9525a54087fdcaaed525a54087fccaaed525a54095fdc7aed525a540c7faaa6c0214e540c7f8a86c0214e540c7f8a56c0214e540c77cca6d4214e540c77eaa6d4214e540c77ca86d4214e540a7bdc4aaa114e540a7f4ca606114e540a7f5ca5c6114e540a7f4ca5c6114e54087fccb69e114e540c5fcba9de114e540a7f5ca606114e540c77dca6d4214e54087fcca6d5214e54095fcc76d5214e540a7bdc4aa8214e540c6fdba999214e540c6fcba999214e54087fdca6d5214e540c6feaa6d8214e54087fcca6d4214e540c77ca56d4214e540977ecc6d4214e540c6fca86d8214e540c6fca56d8214e54087fdca6d4214e540a7f5ca546114e540a7f4ca61e114e540e5f4ba9de114e540e5f6aa9de114e540a7f4c869e114e540e3f68869e114e540a7f5ca61e114e540e5f4a89de114e540a7f5ca5da114e540e6f6aa99a114e540f2f68899a114e540f1f6889de114e540e5f5a69de114e540a7f5ca61a114e540a7f4cb69e114e540a7f5c82ea114e540a7f5c72ea114e540a7f5c52ea114e540a7f4ca546114e540a7f5ca486114e540a7f4ca486114e540a7f5c22ea114e540e3f6aaa22114e540e3f5a6a22114e540e3f4a2a22114e540a7f5ca2e2114e540) else (if i<6 then 0xe57ca19de554a540e67eaa99a554a540f27e8899a554a540e67da799a554a540a77ccb69a554a540e57e7769a554a540e67cba99a554a540f63e66955544a54093fcc86d9534a540c6fcba999534a540c77cba955534a54087fcca6dd534a540c5fcba9dd534a54087fcca6d9534a54097dccb60d534a540e3dca5a22334a540e3dca1a22334a540a7dcca61e334a540a7dcca60d534a540a7dccaa22334a540e3dccaa22334a540c3fcbaa21534a54087fcca6e1734a54087fccaaed634a54087fcca6dd634a54087fccaaed834a540c5fcba9dd834a540c77cba955834a540c5fcba9dd634a54087fdc62e9534a54087fdc12e9534a54087fcca6e1534a540c77cba955634a54087fccaaed534a54087fdc72e9534a540e37da7a22554a540c7f6aa6c4854a540d7b5c46c4854a540c7faaa6c0854a54097f6cc6c4854a540c7f5ca6c4854a540c7f4ca6c4854a540c7f8a16c0854a54087fccaaed654a54087fdcbaa9654a540c3fcbaa21654a54087fdcbaa9754a540a7f4c1699754a54087fdcaaed654a540c7f4a16c4854a54097decc6cc854a540c7ddca6cc854a540c7deaa6cc854a540c5fca16dc854a540c6feaa6d8854a540c6fca16d8854a540c7dca16cc854a540c7eca16c8854a54087fcca6c4854a54097bdc46c4854a540d7d9c06cc854a54097eecc6c8854a540c7eeaa6c8854a54087fcca6dd654a540a77cc12ea554a540a77dc8aaa554a540a77dc7aaa554a540a77dc62ea554a540a77dc32ea554a540a77dc12ea554a540a77dc6aaa554a540e37ccaa22554a540e37cbaa22554a540e37eaaa22554a540a77dc1aaa554a540a77dca2e2554a540a77ccaa22554a540a77cc82ea554a54087fdc32ea554a54087fdc12ea554a540c3fcbaa22554a540c5fcba9dd654a54087fdc82ea554a54087fdc62ea554a54087fccb69a554a540a77cca596554a540a77ecc2ea554a540a77dc82ea554a540a7f4c169a554a540c6fcba99a554a540a77cca616554a540e6f5a799a114e540e3eca5a22225a540a7ecca61e225a540e5eeaa9de225a540a7edc52ea225a540a7edc32ea225a540e3ecbaa22225a540f1ee889de225a540a7ecca956225a540e76cca956225a540e76cba956225a540a7edca2d6225a540a7ecca616225a540a7edca5d6225a540a7edc82ea225a540c3fcbaa21325a54087fcca6d5325a54095fcc76d5325a54097bdc46c4525a54087fccaaed325a54087fcca6e1325a540c77cba955325a540c7dcba8ce225a540a7ecca60a225a540a7ecca54a225a540c3fcbaa22225a540c77cba956225a540c6fcba58e225a540e76eaa956225a54095fcc76d5215a540f57677956115a540f5d6778ce115a540f5ae77889415a540f72e55889415a54097ecc26dd315a540f756558ce115a540f7665588a115a540 else 0x87fdcaaed874a54087fdcbaa9874a540a5fdc7aa9874a540a5fdc5aaa774a540e1feaaa22774a540e1fda6a22774a540e1fca1a22774a540a5fdc1aaa774a540a5fccaa22774a540e1fccaa22774a540c3fcb1a21a74a540a3fdc7aaa884a540a3fdc6aaa884a540a3fdc5aaa884a540a3fdc32ea884a540a3fdc12ea884a540a3fcc12ea884a540a3fdc1aaa884a540b3bdc42c6884a54087fccba21a74a540c3fccba21a74a540a3fdca2d6884a540b3bdc42d6884a540a3fdca2c6884a54087fdcbaa9864a54087fdcaaed854a54087fccaaed854a540a5fcc76e9854a540e4feaa9de664a540e4fda89de664a540f0fe889de664a540a7dcc36e9854a540c6fcba999854a54087fdcbaa8854a540c5feaa6dc854a54087fdcbaa9854a540c3fcbaa21854a540c5fcba9dd854a540a6fcca61e664a540c3fdbaa21764a540a6fdc8aaa664a540a6fdc7aaa664a54087fdcbaa9764a54087fcca6e1764a540a7dcc36a1764a540a6fdc5aaa664a540e2fca5a22664a540e2fe8869e664a540a6fdca61e664a540a6fdc1aaa664a540a6fcc56a2664a540e2feaaa22664a540a3fcc52ea884a540a7f4ca956114e540e774ba956114e540e776aa956114e540b7f1c0216114e540a7f5ca596114e540a7f4ca596114e540e775a6956114e540a7f5ca60a114e540a7f4ca60a114e540a7f5ca20a114e540f67666956114e540e774a2956114e540a7f5ca2ca114e540b7e5c2216114e540a7f5ca2d6114e540b6f5c62d6114e540a7f5ca616114e540f4f67799a114e540e6f4a599a114e540e6f4a299a114e540a7f4ca616114e540b6f5c6216114e540b7b5c4216114e540b7d5c3216114e54097f5cb216114e540a7f5ca216114e540b5f5c7216114e540a7f5ca58a114e54087fcc16d6aa4a54087fcc86c6aa4a54087fcc56c6aa4a54087fcc56e2aa4a54087fcc16e2aa4a54087fcc86d6aa4a54087fdc72ea884a540a3fecc2ea884a540a3fdc72ea884a540a3fdc52ea884a54087fdc52ea884a54087fdc32ea884a54087fdc12ea884a540f7665588a114e540b5f4c754a114e540a7f5ca14a114e540b6f5c614a114e540a7f4ca58a114e540a7f5ca54a114e540a7f4ca54a114e540b7b5c414a114e540e7e5a688a114e540f6e66688a114e540e7e4a588a114e540a7f4ca88a114e540e7e4ba88a114e540e7e6aa88a114e540a7bccaa21544a540c7bcbaa21544a540e3bccaa21544a540a77dca2c6554a540b57dc72c6554a540b73dc42c6554a540f1be889dd544a540a7bcca615544a540a7bcca595544a540f33e88955544a540c7bcba619544a540f2be88999544a540f4be77999544a540f47e7799a554a540e57eaa9de554a540e57ca89de554a540f17e889de554a540e37da6a22554a540e37ca1a22554a540a77cca61e554a540))) else (if i<11 then (if i<9 then (if i<8 then 0xa7ecca60e2246540e76eaa9562246540c77cba9558246540a7edca5d62246540b7e9c02162246540a7edca596224654087fccb68d8246540e7cca88ce2246540a7ecca9562246540a7edc52ea2246540f1de889de3346540e5dca89de3346540c5fcba2dd5246540f2de8899a3346540b5ddc72163346540a7dcca6163346540f4de7799a3346540a6fcc66a2224654095fcc76d52146540e3dca5a223346540e3dca2a22334654087fccb6a12146540a7ecc26a12146540a7dcca61e3346540f55e779563346540f35e889563346540c5fdba2dd5246540f65e669563346540c3fccba21a24654087fccba21a246540e75ca29563346540b7d5c12163346540b7cdc22163346540b6ddc62163346540b7d9c02163346540e75ca89563346540e75cca9563346540a7dcca9563346540e3dccaa223346540e3f5a8a221146540a7f4c869e1146540c6fdba9995246540a7f4c26a2114654095fcc76d5324654087fcca6d53246540a7f4c56a21146540c3fcbaa21534654087fcca6e15346540c77cba955524654087fcca6dd5346540d4fcb7999524654093fcc86d95346540c5fcba9dd5346540c3fdbaa21724654095fccb9dd5246540c5fdba9dd5246540a7ecc2695214654087fccb6952146540a7dccaa22334654087fccb6a2224654087fccb68d2146540a7ecc268d2146540c5fcb7699524654095fcc76d95246540c77cba955324654097dccb60d5346540c77cba955534654087fccb6a15246540e67e66955a24654087fccb68d514654087fdcaaed824654087fccaaed8246540a77cc56a1514654095fcc76e15246540e57e77955a246540a77cc56895146540a77cc56a15246540a6fcc66a15246540a77cc568d5146540c5fcb76a1524654087fccb6895146540a7edca60a2246540e76e5568a2246540a7ecc568a2246540a7ecca60a2246540a7edc82ea2246540a7ecca54a2246540a7edca54a224654087fcca6e15246540c7dcba8ce224654087fccb6a15146540a7ecc868a224654087fdca6e15246540e6ee6668a2246540e3ee8868a224654097f4cb605514654087fccb615a246540c6fcb5999a246540e4fe77999a246540a5fdc7215a246540a7edc2215a246540a7ddc3215a246540a6fdc6215a24654087fccb6962246540c3fcbaa222246540c3fcb5a21a24654087fccb61da246540e2fe88999a246540e1fe889dda246540c5fcb89dda24654087fccb955a246540c77cba9562246540c3fcbaa215246540c77ccb955a24654087fccb68e2246540e37e88955a246540c77cb8955a24654087fcca6dd5246540a7f9c0215a246540a7f5c1215a24654097ecc26dd3146540d1fcb7a21524654087fccb595a24654087fdca6dd5246540c5fdba9dd8646540c3fcbaa21874a540a5fdc8aaa774a540a5fdc6aaa774a540 else 0xe5f67768a114654097decc6cc8546540c6fcb2999a346540c6fca26d8854654087fccb615a346540c7ddca6cc8546540c7dca26cc8546540e4fe77999a346540c6fcb5999a346540c7deaa6cc8546540b7f1c02161146540f3d6888ce1146540a5fdc7215a346540c6feaa6d88546540a6fdc6215a346540c5fca26dc8546540a7ddc3215a346540e775a59561146540a77cc5689524654087fccb6a1654654087fdcaaed6546540a7f5ca5d61146540a7f4c268e1146540a7ecc86962246540a7eccb6962246540a7edca2d62246540e3ee88696224654087fccb68d8146540a3fcc868d8146540e5ee776962246540a3fcc86898146540e6eda899a2246540a7edca5da224654087fccb6898146540f4ee7799a2246540e6eda799a2246540f2ee8899a224654087fccaaed5246540a3fcc869d814654087fccb6958246540a7edca616224654087fdcaaed524654096fdc6aed814654087fccb69d8146540c5fcba9dd824654095fdc7aed5246540c5fdba9dd8246540c6fdba999824654087fccb6958146540e6ee666962246540a3fcc86958146540a7edca61a2246540c3fdbaa218246540a7ecc26a1824654087fccb6a18246540a7eccaa222246540e3ecbaa222246540e3eccaa222246540e3eda8a222246540b5edc72e22246540a7edca2e22246540a7edc32ea2246540a7eccb6a22246540a7ecc56a22246540a7dcc36e98246540a6fcc66e98246540e5eda89de2246540e5eeaa9de2246540a7ecca61e2246540e5eca89de2246540a5fcc76e95246540e5ee7769a2246540f1ee889de2246540e3eda7a222246540c5fcb7aa95246540e3eeaaa222246540c3fcbaa218246540a7edca61e2246540e3eca5a222246540e3eda6a222246540c7dcba8cd8246540e3ee8868e2246540e5ee7768e224654087fccb689824654087fdca6d48246540c77dba9557246540a3fcc86898246540a7ecc568e224654096fccb595624654087fccb68d624654087fccb6956246540e6ee6668e224654087fccb6a16246540c5fdba9dd6246540f56e779562246540e76da6956224654087fcca6e17246540c6fdba9997246540e76da79562246540a6fcc66a17246540f36e88956224654087fdca6e17246540c77dba954824654087fcca6d48246540e76ca89562246540f66e669562246540a7eccb68e2246540a7ecc868e2246540e76da89562246540b6edc62162246540b5edc72162246540f3ce888ce2246540b7adc42162246540c77dba9558246540b7e5c12162246540b7cdc32162246540e7cca58ce2246540f74e558ce2246540a7ecca6162246540f6ce668ce2246540f5ce778ce2246540a7edca216224654097edcb2162246540a7ecca54e2246540e76cca9562246540e7ccba8ce2246540e76cba9562246540e76e5568e2246540) else (if i<10 then 0xa7f5ca14a1146540c3fcbaa218546540a77cc56a1854654087fcca6e1734654087fccb6a18546540b5f4c754a1146540f1f6889de1146540c5fcba9dd8546540a7f5ca54a1146540e775a89561146540d2fe886d8524654097eecc6c88546540a6fcc66a05246540f7c63388a1146540a7f4c868e1146540c3fcbaa213246540c77cba9557346540c5fcb768d5246540f0fe889de6646540e4fda89de6646540f576779561146540c7edca6c8854654087fccb68d5246540c7eca26c88546540a6fcc56a26646540e3f68868e1146540e67e66955a346540c5fcba9dd5246540e3f68869e1146540a6fdca61e664654087fccaaed5346540a7f5ca61e1146540a6fcc26a26646540e2fe8869e664654087fcca6e1324654097eccb609524654097f6cc6c48546540c3fdbaa205246540e4fe77999a546540e5f67768e1146540c7f6aa6c48546540c6fcb2999a54654087fdcaaed8546540c7f8a26c08546540c7f4a26c48546540c7faaa6c08546540e7e5a288a1146540e7e5a388a1146540f7665588a1146540c7eeaa6c88546540c7ecca6c88546540a7ecc268d5246540e7e5a588a1146540f3e68888a1146540e7e5a888a1146540e7e5a788a1146540f5e67788a1146540e5f5a89de1146540f47e7799a5546540e67da799a5546540a77dca2ca554654087fdca6e0524654087fccba21a346540f27e8899a554654087fcca6e05246540e57ca89de5546540f17e889de5546540e67da899a5546540a77dca61a5546540b7e5c22161146540e1fe889dda346540c5fcb89dda346540f5d6778ce114654087fdca6c88546540b7b5c4216114654087fccb61da346540c3fccba21a346540a6fcc66a25546540c3fcb5a21a346540c3fcb2a21a34654087fccb6a25546540e37da8a225546540a77dc82ea5546540e37ccaa225546540c3fcbaa225546540a77cca6165546540a77ccaa225546540a77dca2e25546540a77dc22ea5546540a77ccb6a25546540f756558ce1146540a77cc26a25546540e37cbaa225546540a77dca61e5546540e37ca2a225546540a77cca61e5546540e57da89de5546540e57eaa9de5546540e3f68868a1146540a7f4c868a1146540b7d5c32161146540e37eaaa225546540e37da6a225546540e37da7a225546540e2fe88999a34654087fccb595a346540b6f5c62161146540d5dcb78cd5246540a7f5ca2161146540b5f5c7216114654087fccb6895246540c5feaa6dc8546540a7edc2215a346540a7f4c568a1146540a7f9c0215a346540a7f5c1215a346540a7f5ca6161146540e37e88955a346540c77cb8955a346540e57e77955a346540c77cb2955a346540a77dc32ea5546540e7765568a114654087fccb955a346540c7dcba8cd5246540a7f4c26961146540c77ccb955a346540e5f6776961146540 else 0x97fdcb619324654097fdcb5d93246540b7ecc2a213246540f5dd875cd3246540d7ddb55cd3246540d6fdb658c5246540e7dca85cd324654097fccb9553246540a7fcca9553246540c7fcba9553246540e7ecca6093246540a7fdc7aaa884a540e7eca56093246540f7cd736093246540a7fdc1aaa884a540f3ed876093246540d7edb66093246540c7fcb1aaa884a54097fcc5aed3246540b7ddc32153246540b7edc22153246540b6fdc62153246540c7fda6aed874a54097fdc6aed874a540c7fda8aed874a540c7fcb1a21a74a54097fdcb5d5324654097fdcb595324654097fccb5953246540b7f9c02153246540a7fcc1a21a74a540b7f5c1215324654097fcc8aed324654097fccb54a114e54097fdcb614214e540d77dc86d4214e540f5ed735c95246540d6fdb6614214e540c7fdba614214e540a7fcca614214e540e7eda35c95246540c7fcba545214e54097fdcb545214e540f7e5625c5214e540e7eda65c95246540e7eda85c95246540b7edc85c95246540d77db5614214e540a7fcc869e114e540d7ddc26cc854a540c7fcbaa22114e540a7fcca61e114e54097fccb61e114e540c7fcb869e114e54097fccba22114e540b5fcc76c55246540f76d535c95246540d7bdb4614214e540d7ddc16cc854a540c7fcb8aaa114e540d7f9856c0214e540d7f5b55c5214e540c7fda76d5214e540f76d536095246540f3ed83609524654097fdcb615214e540c7fda66d5214e540e7eeaa5c95246540d5fcc76d5214e540f76d756095246540c7fcca6d5214e540d7edb56093246540e7eda3609524654097fcc86d5214e540c7feaa6d5214e54097fccb615214e540e7f4a85c5214e540e7f6aa5c5214e540c7fcba605214e540f5f5765c5214e540e7f5a65c5214e540f5f5875c5214e540c7fcba595214e540a7fdca5d5214e540c7fcba615214e540c7fdba615214e540a7fcca595214e540a7fdca595214e540c7fcba5d5214e54097fccb60a114e540d3fcb860a114e54097fccb616114e540a7fcca616114e540c7fcba60a114e540c7fcba61e114e540c7fcba616114e540c7fcba5ca114e540a6fcc66a17546540e775a79561146540a6fcc66e98546540d6ddb68cc5246540f376889561146540d3bdb4a20524654087fcca6c88546540e7765568e114654087fccaaed854654087fccaaed3246540b7b5c414a1146540a7f4c568e1146540c6feaa6d85246540c6fda86d85246540b6f5c614a114654096fecc6d85246540c3fcbaa21734654087fdca6e1754654087fcca6e17546540a7f5ca5ca1146540a7f4c86961146540c77cba955834654087fccaaed7346540d6bdb49985246540c5fcba9dd8346540c6fdba998524654087fccaaed8346540a7f5ca60a1146540e3f6886961146540a7f5ca20a1146540c6fdb668c5246540)) else (if i<13 then (if i<12 then 0xb7f9c02153146540b7f5c1215314654097fdcb60d2146540a7fcca61d325a540c7fca5aed325a54097fdcb54d2146540a7fcca6d5325a540d5fcc76d5325a54097fdcb615325a54097fecc6d5325a540c7fcca6d5325a54097fcc5aed325a540e7eeaa5c9525a540f5ed735c9525a540f3ed83609525a540f76d53609525a540f6ed635c9525a540d5fcb76c5525a540f5f5875c52146540f76d535c9525a540b5fcc76c5525a540a7fcca615325a540c7fcb5aaa225a540b7f9c02152146540f7cd73609325a540a7fcca549325a54097fccb616225a54097fccb956225a540a7fcca956225a540a7fcca616225a540c7fcba616225a540d7edb5609325a540a7fcca955325a540c7fcba955325a540c7fcba615325a54097fccb955325a54097fccb9552146540b7ddc15cd325a540f3ed87609325a540f5dd875cd325a540d7ddb55cd325a540a7fcc16e9854a540c7fcba6162246540a7fdca2162246540a7fcca6162246540c7fcb8696224654097fccb6162246540a7fdca6162246540c7fcba2162246540b7edc22162246540b7f5c12162246540b7f9c02162246540b7ddc32162246540b5fdc72162246540b6fdc62162246540b7bdc42162246540d6fdb6618a54a540a7fcc56a22246540c7fcb56a2224654097fdcb618a54a540c7fcb8aaa2246540c7fcb5aaa224654097fdcb58c524654097fcc1aed854a540c7fcb569a2246540a7fcc86962246540d7bdb46185246540c7fcbaa222246540c7fca1aed854a54097fccba222246540a7fccaa222246540e3fda861d854a540e3fda661d854a54097fdcb6185246540c7fdba6185246540c7fdb2aa9854a540a7fdc1aa9854a540c7fdb1aa9854a540c7fdba5d9854a540c7fca16cc854a540d77cb554a114e540c7fcba54a114e540b6fcc66c5854a540c7fcba6c9854a540a7fcca6c5854a540c7fcba6c5854a540a7fcca9562246540c7fcba9562246540c7fcb568e224654097fccb9562246540d6fdb66185246540a7fdc7aa9854a54097fccb596224654097fccb60e2246540c7fcba54e2246540d77cb554e2246540a7fdc6aa9854a54097fccb54e2246540c7fcba60e2246540d3fcb860e224654097fccb58e2246540a7fcca6153246540c7fcba6153246540b7bdc42c5874a54097fdcb615324654097fccba213246540c7fca56e13246540d5fcc76d53246540a7fdca2c5874a540b5fdc7215324654097fdc1aed874a54097fdc3aed874a540c7fcba2153246540c7fcca6e1324654097fdcb215324654097fecc6e13246540a7fdc5aa9864a540c7fdb7aa9864a540a7fdc7aa9864a540a7fdc1aa9864a540c7fca86dd324654097fdcb61d3246540a7fcca61d324654097fcc56d93246540c7fcbaa213246540c7fcca6d53246540a7fccaa21324654097fecc6d53246540 else 0xe7f5a7605614e540a7fcca549614e540b5fcc7549614e540c7fdba61d614e540c7feaa6e1614e54097fecc6dd614e540a7fcca605714e540c7fcba605714e540c7feaa6dd614e540a7fdca61d614e540a7fcca61d614e540c7fda26dd614e54097fdcb61d614e540f57d875d5525a540b77dc15d5525a540c7fcba615525a540e77eaa5d5525a540a7fcca6cd525a540d5fcb76cd525a540c7fcba60d525a540c7fcba6cd525a540b5fcc76cd525a540d3fdb861d525a540b5fcc76e1525a54097fecc6e1525a540a7fcca6e1525a540c7fcba6e1525a540c7fcca6e1525a540e5feaa2dd525a540d5fdb82dd525a540d5fcc76e1525a540d5febb2dd525a540d5fcb760d525a540a7fcca609525a540c7fcba609525a540f75d7354d525a540b77dc154d525a540e7ecca609525a540f3ed87609525a540f76d75609525a540e7ecba609525a540f5ecb7609525a540f75d8354d525a540f67d7558d525a540a7fcca54d525a540d6febb58d525a540f4fcb758d525a540c7fcba54d525a540d77db854d525a540f57cb754d525a540e77cca54d525a540e77cba54d525a540f5dd875cd535a540f75d855cd535a540f37d87615535a540b7ddc85cd535a540a7fcca6c9535a540a7fcca6d5825a540c7fcba6d5825a540c7fcba6c9535a54097fcc5aed825a54097fcc2aed535a540c7fca2aed855a540a7fcca6c9855a540f6bd86595414a54097fcc2aed855a540c7fcb2aaa555a540f1fd87615735a540b6fcc2955635a54097fecc6e1735a540c7fcba615735a540c7fcba5d5825a54097fdc8aed525a540d5fdc7aed525a540f5dd7354d725a540b5fdc7aed525a54097fdc7aed525a54097fdc1aed525a540c7febbaa9525a54097fdc3aed525a540c7fda2aed525a540a7fcca54d725a540a7fcca955825a540c7fcba955825a540f1fd875d5825a54097fccb955825a540b7ecc2955825a540f3dd8354d825a540b5fdc15cd725a540b3fdc85cd825a540f1fd875cd825a540a7fdca215214654097fdcb2152146540b6fdc62152146540b5fdc72152146540a7fdca6152146540a7fcc8695214654097fcc86d5214654097fccb615214654097fdcb6152146540b7bdc42152146540b7edc22152146540d6fcb558e225a540c7fcba956225a540b7f5c1215214654097fccb54e225a540d77cb554e225a540b7ddc32152146540a7fcca54e225a540c7fcba54e225a54097fccba212146540b7f5c16153146540f5ed72549715a540b5fdc7215314654097fdcb2153146540f57cc7549515a54097fdcb6153146540b7becc549415a540f76d72549515a540b7bcc2955415a540b6fdc62153146540f7cd824c93146540d7ecb25493146540a7fcc56a1214654097fcc56e1214654097fccb9553146540b7edc22153146540b7ddc32153146540) else (if i<14 then 0xe6fda72d9814e540c7fdba5d9814e540e6feaa2d9814e540d6fdb72d9814e540c7fcba549814e54097fdcb548814e540c7fdba548814e54097fccb5cd8146540a7fcc568d8146540d5fdb7548814e54097fcc8aed714e540c7fca8aed714e540d7bdb4548814e540d7edb2548814e540b3fcc854d8146540e5fda861d714654097fccba217146540d6fcb6549814e540e5fd876957146540f3ed824c98146540a7fcc56898146540b7f5c154d8146540f3ed82549814654097fccb5498146540b7f5c15cd215a54097fdcb54d215a54097fccba21314654097fccb955215a540f5f5875c55146540a7fcc86895146540b7f5c160d5146540f76d82549514654097fccb6095146540d7ecb2549315a540f73d75549415a540f7ad72549415a540f5bcc7549415a540d5fdb761d3146540b7bcc5889415a54097fccb955315a540b5fcc7549315a54097fccb61d314654097fcc86dd3146540a7fcc868d5146540c7fcba6dd814e540b6fcc66dd814e540b5fdc85c97146540a7fcca6dd814e540a7fccb69d814e540e5fd876897146540a7fcc86897146540f1fd876097146540c7febb69d814e540f5ed72549714654097fccba21514654097fdc7aed814e540b6fdc6aed814e540d5fdb761d5146540d6fdc6aed814e54097fcc2aed814e540c7febbaa9814e54097fdc6aed814e54097fdc2aed814e540a7fcca605514e540c7fcba605514e540c7fcba5c9514e540c7fcba589514e540d7f4cb605514e540e7f6aa605514e540e7f5a7605514e540e7f4ca605514e540e7f4ba605514e540c7fdba5c9514e540c7fdba5d9514e540c7fcba5d9514e540f6f562605614e54097fcc2aed514e540a7fcca6c9514e540c7fdba609514e540c7fcba609514e540c7fcba6c9514e54097fccb609514e540f6f4c6605514e540d7edb2608514e54097fcc5aed214e54097fdcb608514e540c7fdba608514e540a7fdca5d9214e540b5fcc76d5214e54097fecc6d5214e540c7fdba5d9214e540c7fcba6d5214e540f775525c5514e540f3f582605514e540f77552605514e540e7f5a6605514e540f3f586605514e540b7f5c85c5514e540f775655c5514e540f5f5725c5514e540f5f5875c5514e540f5f5765c5514e540e5fda661d714e540e5feaa5d9714e540e5fcba61d714e540e5feaa61d714e540d5fdb85d9714e540f4fd76595714e54097fccb589714e540e5fda25d9714e540c7fcba595714e540c7fda66e1714e540c7fcba6e1714e540b6fcc66e1714e54097fccb9558146540a7fcca6e1714e54097fecc6e1714e540c7feaa6e1714e540d6fcc66e1714e540a7fdca6158146540c7fcca6e1714e540f4fd76589714e540d6fdb7589614e540e6fda7589614e540d5fdb761d614e540e6feaa589614e540e6fca5589614e540e7f6aa605614e540 else 0xc7fcba609814a540e7f4a1549814a540e7f4a14c9814a540c7fcba549814a540c7fdba595824654097fccb549814a540e3feaa61d8246540e3fcba61d8246540c7fcbaa21714a54097fccba21714a540a7fccaa21714a540b5fdc7619714a540c7fcba615714a540e5fda661d714a540e3fcca61d8246540e5fda861d714a540e3fda661d8246540a7fdca2d58246540b5fcc76d58246540c7fcba2d58246540b7bdc42d58246540b6fdc62d58246540c7fda86e1714a540e3fda361d8246540f1fd875d98246540c7fcba6d58246540a7fcca6d58246540c7fcba619514a54097fdcb61d314a540c7fcba61d314a540b7f4c1a21314a540a7fccaa21314a540c7fcbaa21314a54097fdcb615314a540a7fcca615314a540c7fcba6c95346540d5fdb761d314a540c7fcba619314a54097fccba21314a540b7bdc7595414a540c7fccb61da246540f5bd875d5414a540b7bdc2215414a540c7fcb5619a246540f6bd65589414a540f5bd875c5414a540a7fecc61da246540f6bd76595414a540f73d85595414a540c7fcba955314a540a7fcca6c95346540a7fcca955314a540c7fcba595314a54097fccb955314a540b7ddc85cd5346540e7dca260d5346540f5dd875cd5346540f75d855cd5346540f6dd8658d314a540c7fcba5d5314a540b5fdc7215314a540b6fdc6215314a540c7fcba215314a540c7fcba615314a54097fdcb215314a540b7f9c0215314a54097fdcb5d5314a540b7f5c1215314a540b7ddc3215314a540b7edc2215314a540a7fdc85d9a246540a7fcca54d514a540c7fcba54d514a540c7fcba58d514a540a7fcca60d514a540c7fcba60d514a540d7bdb4549514a540f73d54549514a540d7bdb4609514a54097fccb609514a540c7fcba609514a540d7bdb8551514a540a7fcca615514a540c7fcba615514a54097fdcb615514a540d7bdb4619514a540c7fda8aed8246540c7fcbaaed8246540a7fdcaaed8246540c7fdcaaed8246540f67d86595514a540f67d76595514a540b7bdc85d9414a540f5bd875d9414a540a7fdc2615a246540b7becc61d414a540a7fdc1615a246540b7bdc1615414a540e5fd875d9a246540b7bdc2615414a540e3fd87615a246540f3bd87615414a540a7fdc2215a246540f7b554605514a540e6fd76595a246540e7f5a7605514a540e77d85595a246540e7f5a8605514a540c7fcb85d5a246540a7fdc85d5a246540e5fd875d5a246540e6fd86595a246540a7fdc7595a246540a7fcca6c9814e540c7fcba6c9814e540f1fd87615714654097fdcb6157146540b6fcc66c9814e54097fccb549814e540c7fdba549814e540d6fcb66c9814e540a7fdca2c9814e540a7fcc868d7146540d6febb2d9814e54097fdcb60d714654097fdcb54d714654097fccb60d7146540e5fd8768d7146540)))) else (if i<22 then (if i<18 then (if i<16 then 0xf7d953605304a540b7f9c8545304a540f7f181545304a540d7ddc16cc8546540b7f9c8585304a540f7f181585304a54097fdc1aed8746540c7febbaa9874654097fdc2aed874654097fdc3aed8746540c7fda3aed8746540c7fcba6c98746540e5fda561d7646540a7fcca6c98746540a7fcca6cd8746540c7fcba6cd874654097fdc5aed8746540a7fcc26a18546540a7fcc26e98546540e3fda861d8546540e3feaa61d8546540c7fcb2aaa884654097fdc6aed8746540c7fda6aed8746540c7fda8aed8746540c7fca2aed854654097fcc2aed8546540f6f8c6605304a54097fccb61d6546540a7fdca6197546540a7fdca61d6546540e77da76156546540e6fda76196546540b7f9c85d9304a540f5f9875d9304a540e5fda661d7546540b7f8c1a21304a54097fdcb6197546540f37d876156546540e3fd87615a346540e5fd875d9a346540c7fcb2615a346540c7fcb85d5a346540a7fdc1615a346540a7fcc26a25546540c7fcb2aaa5546540c7fcb26a25546540a7fdc85d9a346540c7fcb5619a346540f7d97654d304a540f6f965589304a540d7edc36c88546540f77985595304a540d7edc16c88546540c7feaa6c88546540b7facc605304a540c7fda36c88546540f7d953549304a540d7eecc6c88546540f6f976595304a540b7f9c2615304a540e5feaa61d7546540f3f987615304a540d5fdb661d7546540e5fda861d7546540b7f9c7595304a540f6f986595304a540f5f9875d5304a540a7fccaa217546540c7feaa6e17546540a7fcca615614a540c7fdba615614a540d5fdb761d614a540a7fcca61d614a540c7fdba61d614a54097fdcb54d614a540a7fcca54d614a540d7bdb7551614a54097fdcb5d5614a540d7bdb8551614a54097fdcb61d614a540c7fcba61d8246540c7fdba61d8246540c7fcba54d714a540a7fcca60d714a540c7fcba60d714a540a7fcca6dd8246540c7fdb869d614a540c7fcba6dd8246540a7fcca61d8246540a7fdca61d8246540b7f4c1a21514a54097fdc5aed8246540c7fcbaa21514a54097fccba21514a540a7fccaa21514a540c7fda7aed824654097fdc7aed824654097fdc6aed8246540c7fda6aed8246540d7bdb461d514a54097fcc5aed8246540c7febbaa9824654097fdc1aed8246540f7b554605614a540f6bd54589614a540e7f5a7605614a54097fdc3aed8246540c7fca5aed8246540c7fda76e1514a540c7fda3aed8246540c7fda86e1514a540e3fda861d8246540c7fdba5d58246540a7fdca5d58246540b7f5c5285814a540f1fd875d58246540c7fcba5d58246540c7febb6958246540a7fccb6958246540a7fdca6158246540c7fcba6158246540a7fcca615824654097fccb595824654097fccb9558246540f3bd54609814a540e7f4a1609814a540a7fcca9558246540 else (if i<17 then 0x97fcc5aed634a540c7fca5aed634a540d5fcb76d95246540a7fcca6c5834a540a7fccaa21734a54097fecc6d9534a540c7fcca6d9534a540c7fcba6d9534a540e5feaa2dd5246540a7fcca6d9534a540d6fdb6619534a540d5febb2dd5246540c7fcba619534a540d3fcc86d9534a54097fdc76d9534a540d5fdb82dd5246540d3fdb861d524654097fccb61d5246540c7fca1aed534a540b7ddc160d634a54097fcc1aed534a540c7fca16e1534a540d5fcb82dd524654097fdc76e1534a54097fdcb61d5246540e5fda82dd5246540c7fcba955824654097fccb54e114a540c7fcba54e114a540c7fcba60e114a540d7bcb8552114a54097fccb60e114a540d5fdb661d7346540e5fcca61d734654097fdcb6197346540c7fcba6157346540a7fcca6157346540f1fd87615734654097fccb61e114a540a7fcca61e114a540c7fcb869e114a54097fcc2aed5346540a7fcc869e114a540c7fcba616114a54097fccb9556346540a7fcca616114a540c7fcba61e114a54097fccb616114a540c7fcb2955a346540a7fcc2955a34654097fcc2aed8346540a7fcca6dd8346540c7fca2aed8346540e6fd86595a346540a7fdc7595a346540e6fd76595a346540c7fcb2595a346540e77d85595a346540a7fcca61d8346540c7fcca6e1734654097fecc6e1734654097fccba217346540c7fcbaa217346540a7fccaa217346540a7fcca6c98346540c7fcba5d5834654097fcc8aed7346540a7fcca6e17346540c7fca8aed7346540c7fca2aed5346540e7f4a1615214a54097fdcb215214a540a7fcca615214a54097fccb615214a540a7fdca615214a540b7bdc4215214a540b7ddc3215214a540b6fdc6215214a540a7fdca215214a540b5fdc7215214a54097fdcb615214a540e77ca26155346540d77db66155346540a7fcc56a1214a540d7ddb660d534654097fcc56e1214a540f37d87615534654097fcc86d5214a540e7f4a1a21214a54097fccba21214a540a7fccaa21214a54097fcc26d95346540d5fdb761d5346540f7ad54589214a54097fdcb6195346540f6ed65589214a540a7fccaa22114a540c7fcbaa22114a54097fccba22114a540c7fcba61d5346540c7fca26e15346540e7f4a154d214a54097fccb955214a540a7fcca955214a540b7f9c0215214a540b7edc2215214a540b7f5c1215214a540d7bdb5551214a540e7f4a160d214a540d7bdb8551214a54097fdcb5d95346540d6fdb66195346540e5fd875d5a346540b5fcc76c98546540b7f8c8845304a540f7d953485304a540c7fca26cc8546540f7d9854c5304a540c7fdba5d98546540e3fda661d8546540f1fd875d98546540c7fcba6c98546540a7fcca6c98546540d7ddc26cc8546540b7f9c85c5304a540f5f9875c5304a54097fecc6c88546540f3f986605304a540 else 0x97fccb58d5246540a7fcca54d5246540e77cca54d5246540c7fcba54d5246540c7fdba6195246540a7fdca6195246540d5fcb76195246540b7bdc7619544a54097fdcb5d95246540e5fcb76995246540c7fdb76995246540f73d85595544a54097fdcb6195246540f6bd86595544a540d6fdb65d95246540a7fcca6cd5246540f57d875d55246540c7fcba6cd5246540d5fcb76cd5246540b5fcc76cd5246540b7bcc1a21544a540a7fcca6155246540c7fcba6155246540e77da85d55246540e77eaa5d55246540f75d7354d5246540a7fdc7aa9654a540e7ecba6095246540a7fdc8aa9654a540e7eda86095246540e7eeaa6095246540e6feaa619654a540b6fdc7619654a54097fccb61d654a540e7ecca6095246540c7fda86dd654a540f5ecb76095246540f3ed876095246540a7fccaa21754a540d7edb66095246540f76cc56095246540e7eda66095246540a7fdca619754a540c7fdba619754a540e7eda76095246540e5fda861d754a540e5fda661d754a540c7fcba6095246540a7fcca6095246540b77cc56095246540b7eccb6095246540d7eccb6095246540a7fcc86895246540b77dc154d5246540c7fcba61a554a54097fccb609524654097fdcb6095246540c7fcba6c9654a540e77da7615654a540f37d87615654a540e77eaa615654a540e6fda7619654a540e6fda85d9654a540c7fcba6cd654a540b3fcc86cd654a540a7fcca6cd654a540f67d76615654a540b77dc1615654a54097fcc1aed834a540c7fcba6c5534a54097fecc6dd5246540a7fcca6c5534a540f75d855cd534a540c7fcba6c9534a540a7fccaa21524654097fccba215246540c7fcbaa215246540b7ecc2a215246540d5fcb7a215246540e7dca160d534a540a7fcca595534a540c7fcba595534a540e77ca1615534a540d77db6615534a540b77dc2615534a540b7ddc760d534a540d7ddb660d534a540c7feaa6dd5246540c7fda86dd524654097fcc86dd5246540a7fdca615824a540a7fcca615824a540b7bdc42d5824a540c7fca5aed824a540b6fdc62d5824a540a7fcca955824a54097fecc6e1524654097fccb955824a54097fccb595824a540a7fcca595824a54097fdc5aed824a540a7fdca2e15246540c7fda66e15246540a7fccb6a15246540c7fdb66a15246540c7febb6a15246540c7feaa6e15246540c7fcca6e15246540c7fda86e15246540c7fda76e15246540d5fcc76e15246540f37d87615534a540a7fcca6d5634a540a7fcca615634a540e6fca5619634a540d5fdb761d634a540c7fda56e17646540c7fcba955634a540e7dca560d634a540a7fcca955634a540c7fcba5d5634a54097fccb955634a540b5fcc76d95246540a7fcca595834a540c7fda76d95246540c7fcba5d5834a540c7fca1aed834a540c7febb6995246540)) else (if i<20 then (if i<19 then 0x97fccb615624a540c7fca56e1624a540f3dd8354d824a540a7fcca6e1524654097fdc7aed5246540d5fdc7aed524654097fdc6aed5246540a7fccaa21524a540e77ca5a21524a540d7bdb8551524a540d7bdb6551524a54097fdc8aed5246540e77ca5619524a54097fcc8aed524654097fccba21524a54097fccb54d624a540a7fcca54d624a540f6dd8358d624a54097fdc1aed5246540e6fca558d624a540f7ad54609624a54097fdc3aed5246540f6ed65609624a540b6fdc654d624a540e7eca5609624a540c7fdb8695624654097fdcb5d5814a540c7fcba5d5814a540e7f4a1615814a540a7fcca615814a540c7fcba615814a54097fccb955814a540a7fcca955814a540f2fd86595814a540d6fcb65d5814a540e7f4a15d5814a540a7fdca615814a540e3fcba60d8246540e6fda72d9814a540e3fca560d8246540c7fcba5cd8246540b3fdc160d8246540a7fdca2d5814a540b7bdc42d5814a540a7fcc568d8246540e3fda7619814a540c7fcba60d8246540a7fcca54d814a540c7fcba54d814a540f2fd8658d814a540c7fcba5cd814a540e7f4a15cd814a540e7f4a154d814a540b7ecc29558246540b7f5c154d814a540b3fcc854d814a540d6fcb654d814a540e7f4a160d814a540c7fcba6cd8246540a7fcca6cd8246540e7f4a1955814a540c7fcba955814a540b7f4c1955814a540f3bd86551814a540c7fcba60d814a540f6bcb6551814a540d7bebb551814a540d7bdb7551814a540b3fdc85cd824654097fdcb6197246540c7fdbaa217246540c7fdba6197246540a7fcca6157246540a7fcc86957246540c7fda86e1724654097fecc6e0a14a540c7fda66e17246540a7fccaa217246540c7fda36e17246540c7fdba6157246540f5dd7354d7246540a7fcca54d7246540c7fda76e16246540c7fda36e1624654097fcc56e16246540d6fdb65957246540c7fdba5957246540a7fcca60d7246540e5fca85cd7246540d5fdb85cd7246540f3dd8358d8246540f1fd875cd8246540c7febb69d814a540a7fccb69d814a540a7fcca54d8246540e3fda861d814a540e7f4a161d814a540c7fcba61d814a540a7fdca61d814a540a7fcca61d814a540c7fcba54d824654097fdc7aed814a540c7fcca6e17246540c7fda8aed814a54097fdcb614a14a540c7feaa6e17246540a7fcc56898246540f3dd8354d824654097fecc6e1724654097fdc5aed814a54097fdc3aed814a540c7fdb668d5246540e5fcb768d5246540e77d7568d5246540c7fcba60d5246540a7fcca60d5246540c7febb68d5246540a7fccb68d5246540a7fcc868d5246540c7fdb768d5246540c7fdb868d5246540d5fcb760d5246540d77db854d5246540e77cba54d5246540b77dc754d5246540f75d8354d5246540f57cb754d5246540d5fcb758d5246540 else 0x1120110e10fc10ea10d810c610b410af10aa10a510a0109b10961091107f106d105b105610511032102010010fe20fc30fa40f850f660f610f5c0f570f450f400f3b0f290f240f120f0d0efb0ef60ef10eec0ee70ed50ec30ebe0eac0ea70e950e900e7e0e790e670e620e5d0e580e460e340e220e100dfe0dec0dda0dd50dd00dcb0db90da70d950d830d710d5f0d4d0d3b0d290d170d050cf30ce10ccf0cbd0cab0c990c870c750c630c510c3f0c2d0c1b0c090bf70be50bd30bc10ba20b900b8b0b790b740b6f0b6a0b650b530b4e0b3c0b2a0b250b130b0e0b090b040af20ae00adb0ac90ac40ab20aa00a8e0a7c0a6a0a580a460a340a2f0a2a0a250a130a0109ef09dd09d809d309c109af099d098b097909670955094309310912090008ee08dc08ca08b808a608940882087d086b0859084708350830081e080c07fa07e807d607c407a507930781076f075d073e072c071a070806f606e406d206c006ae069c068a06780666065406420630061e060c05fa05f505e305d105bf05ad059b05890577056505530541052f052a0518050604f404e204d004b104ac049a04880476046404520440042e041c040a03f803e603d403c203b0039e037f036d035b0349033703250313030102ef02dd02cb02b902a702950283026402520240022e021c020a01f801e601d401c201b0019e018c017a01680156014401320120010e00fc00ea00d800c600b400a20090007e006c005a0048003600240012000097fdcb615324a540a7fcca615324a540c7fca56d9324a540a7fccaa21324a54097fcc56d9324a540b6fdc6215324a540b7ddc3215324a540b5fdc7215324a540b7edc2615324a54097fdcb215324a540c7fca56e1324a540f75d8354d524a540b5fdc7aed5246540e77cca54d524a540a7fcca60d524a540e77ca560d524a540f6ed65589524a540f7ad54589524a540f7ad54609524a540f3ed836096246540e7eda36096246540a7fcc568d624654097fccb9556246540e6fd6568d624654097fccb54d6246540b6fdc65cd6246540a7fdca615624654097fccb6156246540c7fdba5d56246540e6fda75956246540b6fdc65d56246540b6fdc654d6246540a7fcca595324a540a7fcca955324a540b7f9c0215324a540b7edc2215324a540b7f5c1215324a540e7eda76096246540e6fd656896246540f3ed876096246540e7eda56096246540e7eca5609324a540f73d65551524a540e6feaa595624a540f67d85595624a540c7febbaa95246540b7edc2615624a540e6fcca595624a540d7bdb8551624a540f6bd65551624a540d7bebb551624a54097fccb955624a540a7fcca955624a540a7fcca615624a540e3fca560d824a540a7fcca54d824a540c7fcba6e15246540d7bebb551824a540b5fcc76e15246540a7fcc56a1624a540) else (if i<21 then 0x340f33fd33eb33e633e133cf33bd33b833a633a1339c339733923380336e335c334a33453340333b33293324331f330d32fb32e932d732c532b332a1328f327d326b3259324732353230321e320c31fa31e831d631c431b231a0318e316f315d314b313931273122310330f130d230c030a1308f307d306b305930473035302330112fff2fed2fce2faf2f9d2f7e2f6c2f5a2f482f362f242f052ef32ed42ec22eb02e9e2e8c2e7a2e682e562e442e3f2e3a2e352e232e112dff2ded2dc12da22d902d7e2d5f2d4d2d2e2d1c2d0a2cf82ce62cd42cc22cbd2cb82ca62ca12c8f2c7d2c782c732c612c5c2c572c452c332c212c0f2bfd2beb2bd92bc72bb52ba32b912b7f2b6d2b5b2b492b372b252b202b0e2b092b042af22ae02ace2ac92ac42abf2aa02a8e2a7c2a772a652a532a412a2f2a2a2a252a202a0e2a092a0429f229ed29e829e329d129bf29ad299b2989297729652960294e293c293729322920291b290928f728e528e028ce28bc28aa28a528932881286f286a28652853284e282f281d2818280627f427e227d027be27ac279a27882776276427522740272e271c27172712270026ee26dc26ca26b826a62694265b263c262a2618260625e725d525a9259725852573255425422530251124ff24ed24c124af249d248b246c245a2448243624242412240023ee23dc23d723d223c023bb23a923a42392238d23882383237e236c235a2348233623242312230022ee22dc22d722d222cd22bb22a922a42292226622542242223d222b2219220721e821d621c421b221a0218e217c21432131211f211a210820f620ca20b820a62087207520632051203f202d20011fef1fdd1fcb1fb91fa71f951f831f711f5f1f261f141f021ef01ed11ebf1ead1e9b1e891e771e651e461e341e221e101dfe1df91de71dd51dc31db11d9f1d8d1d7b1d761d711d5f1d4d1d481d431d311d1f1d0d1cfb1ce91cd71cc51cb31ca11c8f1c7d1c6b1c591c471c351c301c1e1c0c1c071c021bfd1beb1bd91bc71bb51ba31b911b7f1b7a1b681b561b511b3f1b2d1b281b231b111aff1aed1ae81ae31ade1acc1aba1aa81a961a841a721a601a4e1a3c1a2a1a0b19f919e719d519b619a4199f199a199519831971195f194d1921190f190a190518f318e118cf18b0189e187218531841182f181d180b17ec17da17c817b61797178517731761174f173d172b171916fa16db16c916b716a516931667164816361624160515f315e115c215b0159e158c157a156815491537151814f914e714d514b614971485147314611435142313f713d813b913a7139513831371135f134d133b13361331131f130d12fb12e912d712c512b31294128212701251123f122d121b120911f711e511d311c111bc11aa11a51193118e118911771172116d115b114911371132 else 0x5349533753255313530152ef52dd52cb52b952a7529552835271526c525a523b52295217520551f351e151cf51ca51b851a6519451825170515e51595147513551235111510c5107510250e350d150bf50ad50a850a35091508c507a506850565044503f502d501b50094ff74ff24fed4fce4fbc4faa4f984f864f674f624f5d4f584f394f274f154f104f0b4ef94ef44eef4edd4ed84ed34ec14eaf4e904e8b4e794e744e6f4e6a4e584e464e414e2f4e2a4e184e064df44de24dd04dbe4dac4d8d4d7b4d694d644d524d404d2e4d1c4d0a4cf84cf34ce14cdc4cca4cc54cb34cae4ca94ca44c924c804c7b4c764c714c6c4c5a4c484c364c244c124c004be14bc24bb04b844b584b464b414b2f4b2a4b184b064b014ae24ad04abe4aac4aa74aa24a904a7e4a6c4a5a4a3b4a294a244a1249f349e149dc49bd499e497f496d494e4949493749254913490148ef48dd48cb48b948b448a24890488b4879487448624850484b48464841482f481d480b47f947e747c847b647a4476b4759474747354730471e470c46fa46f546e346d146cc46c746b546a34691467f466d465b464946374632462d461b4616460445ff45fa45f545e345de45cc45ba45b545b0459e4599459445824570455e45594547453545234511450c44fa44e844e344de44cc44ba44b544a3449e448c447a44684463445e444c443a443544234411440c43fa43e843d643c443bf43ba43a843a3439e438c437a43684363435e435943544342433d432b4319430742f542e342de42cc42ba42b542b0429e4299428742754270425e424c424742424230422b42194214420f41f041eb41d941ba41b541a34191417f416d416841634151414c413a41284116410440f240e040ce40bc40aa40984086407440624050403e40394027402240103ffe3fdf3fcd3fc83fb63fa43f923f803f6e3f5c3f573f453f333f213f1c3f0a3f053f003eee3edc3ed73ec53eb33ea13e9c3e8a3e783e663e543e423e303e1e3e0c3dfa3de83de33dde3dcc3dba3da83da33d843d583d393d1a3cfb3ce93cd73cc53cc03cbb3ca93c8a3c783c663c543c353c303c1e3c0c3bed3bc13baf3b9d3b8b3b793b673b553b433b313b1f3b0d3afb3ae93ae43ad23ac03aae3a9c3a973a853a733a613a4f3a3d3a2b3a193a0739f539d639c439b239a0398e397c396a395839463941393c393739253913390138e238d038be38ac389a38883876386438523840382e381c380a380537f337e137cf37ca37b837a637a1379c378a377837663761374f373d372b37263721370f36fd36eb36d936c736c236bd36b836a6369436823670365e364c363a36283616360435f235e035ce35bc35aa3598358635743555353635173512350034ee34dc34ca34b834a63494348f348a34853473346e34693457344534333421))) else (if i<26 then (if i<24 then (if i<23 then 0x77cb77b977a7779577837771775f774d773b7729771776f876e676d476c276b0769e768c766d765b7649762a7618760675f475d575c375b1759f758d757b755c754a753875267514750274f074de74cc74ba74a87496748474727460744e743c742a7418740673f473e273dd73cb73b973a7739573837371735f734d733b73297317730572f372e172cf72bd72ab7299726d725b723c722a720b71ec71cd71bb71a97197718571737161714f713d712b7119710770f570e370d170bf70ad709b70897077706570537041702270106ffe6fec6fda6fc86fb66fb16fac6fa76f956f906f7e6f796f746f626f506f3e6f2c6f1a6f086ef66ee46ed26ec06eae6e9c6e8a6e786e666e546e426e236e116dff6ded6de86dd66dc46db26da06d8e6d7c6d6a6d586d466d346d156cf66ce46cd26cb36ca16c8f6c7d6c6b6c596c476c356c236c116bff6bed6bdb6bc96bb76ba56b866b746b626b506b316b1f6b0d6aee6adc6aca6ab86aa66a946a826a7d6a786a666a546a4f6a3d6a2b6a196a0769f569e369d169bf69ad69a869a3699e698c697a69686956694469326920690e68fc68dd68cb68b968a7689568766864685268336814680f67e367c467b267936781676f675d674b673967346722671d6718670666f466ef66dd66cb66b966a7669566836671665f664d663b66296617660565f365e165dc65ca65b865a66594658265636551653f652d651b650964f764e564d364c164af649d648b64796467645564436431641f640d63fb63e963d763c563b3639463826370635e634c633a6328631662f762e562e062ce62bc62aa629862936281626f6250623e622c621a620861f661e461d261c061ae619c6197618561736161614f613d612b6119610760f560e360c460b260a0608e607c606a605860466034602260105ffe5fec5fda5fc85fb65fa45f925f805f6e5f5c5f4a5f385f265f145f025ef05ed15ebf5ead5e9b5e965e845e725e605e4e5e3c5e2a5e185e065de75dd55dc35db15d9f5d8d5d885d765d645d525d4d5d3b5d295d175d055cf35ce15ccf5cbd5cab5c995c875c685c565c515c3f5c205c0e5bfc5bea5bcb5bb95ba75b955b835b715b5f5b4d5b2e5b1c5b0a5b055af35ae15acf5abd5aab5a995a875a755a635a515a4c5a3a5a355a235a1159ff59ed59db59c959b759985986597459625950593e591f590d58ee58dc58bd58ab58995887587558635851583f582d580e580957f757e557d357c157af579d578b57795767575557365724571f570d56ee56dc56bd56ab5699568756825670565e564c563a56355623561155ff55ed55ce55bc55aa559855865581556f555d554b553955275515550354f154df54cd54c854b654a454925480546e545c544a544554335421541c540a53f853f353e153cf53bd53ab538c536d535b else 0x9eca9eb89ea69e949e759e639e519e3f9e2d9e1b9e099df79de59de09dce9dbc9daa9d989d869d749d629d509d3e9d2c9d1a9cfb9cdc9cbd9cab9c999c879c759c639c519c3f9c2d9c1b9c099bf79be59bd39bc19baf9b9d9b8b9b799b679b559b439b319b1f9b0d9afb9af69ae49ad29acd9abb9aa99a979a859a739a619a4f9a3d9a389a269a149a0299f099de99cc99ad999b9989996a9958994699349922991098fe98ec98da98c898b6989798789859984798359816980497ff97ed97db97c997b797a597939781976f975d973e972c971a970896f696e496d296c096ae969c968a96789666964796359623961195ff95e095c195af959d958b9579954d953b95299517950594f394e194cf94b0949e948c947a94689456944494329413940193ef93d093be93ac938d937b9369934a93389326930792f592d692c492b292a09281926f925d924b9239921a920891f691d791c591b39194917591639151913f912d911b910990f790e590d390c190af909d908b906c905a904890369024901290008fee8fdc8fca8fb88fa68f948f828f708f5e8f598f3a8f288f168f048ef28ee08ece8ebc8eaa8e988e938e818e6f8e5d8e4b8e398e1a8dfb8de98dca8db88da68d948d828d708d5e8d598d478d358d238d118cff8ced8cce8cbc8c9d8c8b8c6c8c5a8c488c368c318c1f8c0d8bee8bdc8bca8bb88bb38ba18b8f8b7d8b6b8b598b478b288b168b048af28ae08ac18aaf8a9d8a8b8a6c8a4d8a2e8a0f89e389c489a589938981896f895d893e891f890d88fb88f688e488d288c088bb889c888a88788866885488428830881e880c87fa87e887d687c487b287a0878e877c876a8758874687348722870386f186df86cd86bb86a98697868586738661864f8630861e860c85fa85e885c985b785a5858685678555854385318512850084ee84dc84ca84ab8499847a84688456844484328420840e83fc83ea83d883c683b483a28390837e836c835a834883368331831f830d82fb82e982d782c582b382a182828270825e824c823a821b820981ea81cb81b9819a81888176816481528140812e811c810a810580f380e180dc80ca80b880a6809480758056804480328020800e7ffc7fea7fd87fc67fb47fa27f907f7e7f6c7f5a7f487f367f247f127f007eee7edc7eca7eb87e997e877e757e567e447e327e207e0e7dfc7dea7dd87dc67db47da27d907d7e7d6c7d5a7d487d367d177d057cf37cd47cc27ca37c917c7f7c6d7c5b7c497c377c257c137c017bfc7bf77bd87bc67ba77b887b767b647b527b337b217b0f7af07ade7acc7aba7aa87a967a847a727a607a4e7a3c7a2a7a1879f979e779d579c379b1799f798d797b7976796479527940792e791c790a78f878e678d478c278b07891787f786d785b7849783778257813780177ef77dd) else (if i<25 then 0xd0c07241e280e483c5a0f0e83c301c9078a03920f1683c3a0f0e83c301c90782c4720f0a83c0d00b11c07018a202b02d85b00080483e020f8083e0208050270908008120ec003b000f8083a0f0e83c3a0f0a07018a2f010741e140e283c4f000f8083e020e83c3e020f8083a0f0d808203870408210801e0208007040f808360f080e08138206e021f0104e081f0107c041000000001e020e83c3a0f080007d0640b41e150782545a0f04a8b41e0951089812a2d0782545a0f04a880007808200301020410840c040800001c103e0208180c10583c20602041e0208000f0104e081f0107c041f0107c041f01040001c1037010f80820060dc002b010a01820230ac0428060dc043e020ac0420cc0808c20b20f80820b20f80824010b01820120814424070801824070801820510ac04241204d8980810301820000003708080e100c0404040800060207c0410301820f0104e081b8087c041f0104e081f0107c04100004040901824150904820030102c060dc0428040f8082004080102404080e020bc0600880c1f0104608118206e021019840a2140304041c081442812080f420028840a210090402e140904608101e82c8403d08c04203d0901c2083058880a2102887c0410238408e1409050241021850241043070641c190500c1c190706410430500c1d010408060805020270a018202d0f8082b040901c3e020ac10208608261619858500c1d010500c1094d0c840f01048081f010500c1580840281f0107c0414030560c1b800560c100b840a21f01058240b4178083e020ac1828060ac0420120ac0420340901c3b010ec002013080482400082bc16c2f01048081009040a21d80040a212038460210100460c1010048081d800480214030500c10098581412008480e12008500812038480c12020480c14030500c12038500c1605050081009048081abbfabadab9bab89ab77ab65ab53ab41ab2fab1dab0baaf9aacdaabbaaa9aa97aa78aa66aa54aa42aa30aa1eaa0ca9faa9e8a9d6a9c4a9b2a9a0a98ea97ca96aa958a946a934a922a910a8fea8dfa8cda8bba8a9a88aa878a866a847a835a823a81ea80ca7faa7e8a7d6a7c4a7b2a7a0a78ea77ca76aa758a746a734a715a703a6e4a6c5a6b3a6a1a68fa67da66ba64ca647a635a623a611a5ffa5e0a5cea5bca5aaa58ba579a567a555a543a531a51fa50da4fba4e9a4caa4b8a499a487a475a463a451a432a420a40ea3fca3eaa3d8a3c6a3b4a3a2a390a37ea35fa34da33ba329a324a312a300a2eea2dca2d7a2c5a2b3a2a1a28fa270a25ea24ca23aa228a216a204a1f2a1e0a1cea1bca1aaa18ba179a167a155a143a13ea12ca11aa108a0f6a0e4a0d2a0c0a0aea09ca07da078a059a047a035a023a0119fff9fed9fdb9fc99fb79fb29fa09f819f629f509f4b9f399f1a9efb9ee9 else 0x6881540c8100e001f0107c041b80848241f0104e0610001e0208000860a0103a020f8083e0209c18330e08013040a01020587040000082a160306e001603040005c042004c1023080dc043e020814437000814423040b0102c060dc0020190f80820f01040a21009840a2102886e001f010741e10098415c0b2101443a0f0814420140818240b2130c820bc05a8bc041987022440230b01820130804c3b010805024060804824060f808206204b081780b51301820bc05a8980c16030580c101184024111302545e02082f016a20258480c1f0105e00178087c041f0105e0210001e02090483e020f808205798702d460b405f0bc041b80040b00b51004c20330578ae021f0107c04120306e021f010400b80041d010f404200740420074043d010dc003d010f404203008c002012080c020300f4043d010f4043d010f4043d01080c0201800400c858721611818400010bf61a238004e06101c0035010f0283c0a08000e808400c85840002c0c3d010dc003d010f0282030080c020e8087a021002e00106c003e020f4042001807a021e80840014080c03b000801d01083c1e08a100a42018007a02158006e00158005606100987a02158007a02101806e001e8087a0210000601409048001203056001009040601f07f42c166329210bc16226040580810148585e0b1130203f0004782d47e02090483700080d815a2b8006616103d8210402f08c00241204b02c477010dc0420120b0bc1622014848081f01058101602040241f0106e001002e0010104820b800400002e021b8007c04178007c041f0107c041f0107c0410001e020f8082005f848240960588c024100e8408120dc0420140b0bc162260186e001f0104028100e840461f800250164323210042b0108002410178413008b2178ee001b80040a80a71008c2b010a0482b06080bc2c0f04c02d47701080482025080483701080582012080bc2304081ec0b9b0b05f10024101784028160782e8401208048201608048202f0ec002c0f05a8802411808460c1409041e020f8083e020f8082f000bc04240408004150f808200780833060cc183e020904833060cc1820360bc003e02090103e020f8083e020b0102060207c0410001e0209c103e020f808270409c103e020808241b800417000dc0020020842412090482000007a1028850381024040a2118085038140e040a2140e050380b210144281c08120209d0598900c10000b0b0a0182b0b081443a0f03f02d86014080003d08c043e02080d815a2b8007c0408305a8c0920b21101c3e020f8083e02080d86162015048081f01041080bf100183e020f808280608018240709010241c050881420b5100503e020a0182051080f50380c11a83d064280e04e021d078254409508070301c03e8a038180e06038180e06038140e283c402)) else (if i<28 then (if i<27 then 0x828160a0482418090482816081982002e0482e14178505e14178505e12008404010f808205818404810009c202709c0c3e020b09c164298183305e020f8083b000804820270dc003e020f80820140ac0c37000dc0420270904820f010561c08b178083e02080102027080102700082e001209072161f0107c041200841e020f8083b000ac002000261c089100a424030ec042005c00202090404e12090760210009c23040f8083e0208004270590ae0210090580616018484e0b51000061382d440240800c200642c200642c20078082012080dc16220005c20002e021f0104170008002413820403a1f01048021f0107c04102602cc47090f80820f0107c041f0104e121f0107c041078082020904170008000f0107c0410000000c07c04158007c041f0104008161382d4470e0458bc0410331c240bc33841c101543c85841e02083c041f0104004e0598bc041f0107c041003c041b8085806100b8661c08b1300c20b808584e0b511c1020387022c4c2705a88e1c08b1300c270e0458800040806020120dc003e020f8083e020f808200040401010002020b8004010100000270802020240904820120e09c154200406e001f808204166329220482812080202000406e0214090400030f8082001c243e020f8083e020f8083e020901c2401080170008080010000b00083c0412090400f010400004040241d80041e0208c0c2028080a02001406e00100004e1d800404010800241f010402e1003c041f01041e020f8082038205024138207c041003c041003c04118187c04100000f01041e020dc0027040dc042024083c041f010400014841e020f80820200846001000006105c00200783c108207808205605a0807040f8083e0209c1020078082038486e00140907c0411800404e1f0107c04101387c04101385600118406e001d800408120800061f01040620b21000c20580046001f01046081f010405210001020120809c20180040000204802102c0020040904820f0107c04122307c0419880404e1f01040081f01040241000608100b86e02101c3811223841c1014c33870224470e044880620b2178083e02080742005c00204e0598bc041f0107c04101882c440f010404e138482f84704046018063030ac0020180804837000ec003b000ec0020120805020140ec002020a8580c1d8007600106c002f000bc043e020f8083e02090183e0209c18205605b0b600138704e081383040261009040a2120004000101c370108144208505a880a21f0106e001b80050241d8085e0010098407412038760216020404120ec0424040808081f010400382048241b80841e020f8083e020801e020f8083e020f8083e0208000f0107c04138204e08138207c041f0104824100304010100204008100304010100a07c04178007c0410260328404d04 else 0x2105e840a812020406c102a0424610a9841401d0784250118704810101b040a8101e8460610a9842a61c85840704081a42700081a4230809020202309c043906090bc2023084b8240808c40341208164203d08c50206f191bc046098081bc64621818685f4121024862620440c8c40230a0bc282f0a0bc2308081702b0e0808c203d0a04828120a0bc2b0108c0c242f0a048282f080f4206609c242b0408c1020c102e09024120904e00103905024100b040001c2420987040018704e1a120a86e021010040b61b808461a102d86e0214100482a101004e0210918485e118a0585ec1210c5033090821c2038804e201984866161602076021d80848521380050241617b04843251898804610100585ec1211048241d0828c231309c003310090543700090c0341c0a0a4202909c00370009c00206da0a88860101484160161830484c150d054206d1948960010120482a11200411e1a848400a8486a12100900202d0f0283c0a09070360f0d83c202d080a42000261c140e0502a10120405a11820460616018502a11859c2443030ac0c2b0009c0c341518a0903c1418040fec15101b46522001b4652f001827c628205006861412130702031090c024300a0c02003384000a9866201010483c0a0f0283c0a09048240808c202116080d82412090a82b040a0c0242a081d020e050486014180422c101b04164153170283c0a0e42c20360e42c20b209c0c3c0a081502303090102304081a43c0a088982226088982036090742c04080d8281c0e0703415081b7038204b846081b8004e00120a840f811200688d42110c40203800482e1582048541020702139081b465222180482e141806a12121805034140d04480108b042a6101c0037000901828270904824170ac20205c090482827081d9606202a046521d81876061d8184824138484808158204e1215840560810908460c15820481014090504e1603040ec12138406e100a84242140904062102e114440880a0482c0608105e138086a2010578402e12138504e1582040ea329104842414081e022260a09c20209840e814138402520905c281a09c18381c089002c040e07024120e07020880b07010a240d04181c081db038202d0410a120a04079b091302023140907423040a06820970909c2075c0e0824210908407000dc0021210b02022400909c281a0e83c24140b01020d840407090ac18230408190381c0e070281508214626201b8500c118a0424211200703870411c18381c3820861010388ca440660819827000819828120905c33100805820c104c0817000cc38330e08198240808898282f0907420620ac20206f19188e001020482070032096101027cc0c57000906c208c0800de141086e0010390400a408230205c08c202c2f04c080b8160406e00100b04002109c0028160904) else (if i<29 then 0x905c2c040847c20840a0e02c04080fc0e8241c044a4138004830140d8503216030688d41210c102c04081d688c240e040ca1c0e0c4c4082080b42c27609081041129040ea329101542313d078823e103a86e00118ecc384c06082c823060b018330e7840823e118a0582530e1209c2074081a10a2203421444b080889827090e83c21210a07824170ac002088090742b0808c0c2408081c50a221290482e1042840b8140184e06118186e00160184e121c0904e1a140186e021b8004181c18a08456140f0484e140e050321184050381604058061000c43c0a0845824120904820bce0508179c0a110482085e0508062160184e12120204e1211820403080a01821160f02823030823020b2b808824210590c2c40880a146e1020440504e16018401160f02820bc21508062104404e1c100220212109c24270e09c0027080a07141e260186038140906e0010919c3440170909c20640830341e202de83c4076194881642521207141e0c51825b41e203882205c0a0e83c22520f0283427a090863e31d130702062082612198806c1e100c74636220184806101b86e00158184242140a8406e1601846061044040f0120904824100d850361d07844a4138484e0c109084247b0113c0027090a00c2808080d824030ac0c2b030e04828040c07241e2820058381129078141613b0485a0f08198281c020080ec3291210020500cc3820b142008e1210260741e11290741e70e1109c2c276090882e14090423e120e8502410440411013870423e10440423e198805024141004832141006e001a09041700090482306081d420af081c420880a07c209318a08242140a8502411820684f412170282088d808811150314c2c2c1c04089808140d840cc101b8406e14090482412288408270d0482020904048100b840f0103a81704088a818900c12138404614030500c141185024109486e001b800504010970410a138485040120a86e00138406e00120904e00101204824105d817040370dc0021233868804812138408e108f8410a118304110103f04110120b8405a108f840901034066161b800410a70e1012428040d40c61629830463f8121054c330b082f0281c082202048081a0330e0b00c20002ca0382042840e381c101c7038203f0411810440703807d1047c2088081c00c8203407024120e0407a1023848321046050241094850241038840a2104b4c104017080f420880a04820370b048241208016410948661610a98406210428406c103c84e1a102485e0010613c0047040ac10270d0a06c37010813028080e048270e09c243812090bc20230ac00203609c0423230a048206f090482408081bc646201b0406c1d800720c1609050241617b048406f0a08c20c1048090241091848081194824043080b02028120ac1823080cc00e122d800560 else 0x310f0282c040f02823040e83c22260e83c2031088982c04081402075194bc00602d090642804082f16082b8085608109187602120204250103604250198804824109405024120d84e1c1090878141e050444c11130741e100f841681281048c3b010b0102f01187090a219808684f412100c43903080e0810590760210288482e1602040a21014868141380048081d80858081028107044270824c628203a8ca441210814439030cc38330e081fc652200c202129084a02051081dc4a42e05058081d8084102c1c10c2430400b01034120847c28230a01820170808c205c1918811010590c2c4b010a01824120d83c2c12985898081413840a8120904824120206616120e040aa14118416430b1208c28060a018200440461015808500c10583c28060a08c2306082c9e02220e04110104404252198804242140905024120b84810101b860a370811054242708240281208084e140f84116118204242140904832160406c1e1091dc0440044504840230909c20370a018202309048201d0a09c211f08006e1428e0484c2760908808100c50208819189838088102a83412588096201413848321040d0484029090203412082402b000d83c20290ac4020b078560011290484e10168483814090482415800561c10908688d4121511a82421825c0441210cc1037000909c2700080a4341c09c0027060805c28270cc383700089002414080a4207a08130205c0cc242b0e081e020240829c2b0e0800be13848407090904828120a06c204c0905428270809020182046101204040a8102d04608102e2c3855100806c21297800b60215870414e100c046121b07842521d808460c101684658314101c1038282004a4402d0909c205c1948904e102c002c060dc043a0f0b0182252081402129089482c27609098241184048241e05048241602078141e05040ea1215040f0120c05855b08110482415080a42123081fe8242613b04840b0080dc281b081d420b1094a100681c)))))
def f3563l10 : Packing := (2492,5,8,8,4,16,0,f3563d10)
def f3563d11 (i : Nat) : Nat := (if i<11 then (if i<5 then (if i<2 then (if i<1 then 0x88969503adf3ba82b4a81df38ce225a540efac6708ad2a074fe779993950337ed3ccc9ca811ff6e9814e540cdf94533272a047fcb269939503bf311422b4a819bfaaa664e5408ffb74bb272a047fdba215195023fe5d30a8ca815bf6d88546540abfb6e42a32a074fe779991950337ed3ccc8ca811ff2c9a546540cdfcccd2a32a057bdb4215195033be5d4aa8ca811ff2ea5546540cefb512aa32a0677eaa95519502bf6d910a8ca815f76cc8546540aff36042a32a057f5b12151950397f444cc8ca811ff2e1a746540c7f94544232a047fdba61d195031ff4434e8ca818ffaaa8846540c7f97544232a063fca5a21195031fed35108ca811ff2e987465408ffb74c3232a065fe776991950337ed44cc8ca811ff6e97646540cbfb513ba32a065feaa9dd195038ff444ee8ca8197f2a27746540cef9512aa32a063fe88689195023fe5c3448ca819bf999a246540cbfceed1232a067dca58cd19503b6f334668ca819f728a3346540eebcab19a32a047fcb5689195023fedd2c48ca811ff6e972465408ff974a9232a047fdba549195023fedd3048ca819df955a2465408ffb7441232a047fcba60919503aef3bc668ca811ff2e1a346540cef9452aa32a065fe7768d195031ff443468ca819df69e5546540e6fd112aa32a0767e6695519503abf3bcaa8ca819bf999a3465408ff974a9a32a047fcba5cd195039ef444668ca819f72a23346540cefcaad1a32a047fcb568d195023fe5d3068ca811ff2c9a3465408ffb7440a52a067f4a160529502bdeda10294a8157f6dc814a540cfd94311252a077ce3388929502b7e5b30294a811ff2e9814a5408ff974b8a52a073be8850529502bdeda0a294a81daf999414a540eb7ceea0a52a047fcba545295031fe52d10b4a811ff6e8514a540af7b68a8a52a0775e558cd295033ee52c6694a818ff2a1824a540cfb94319a52a073de888cd295033ee5446694a81db799a334a540ebbcef19a52a0677ca5549295033f652c4494a81dbb99a224a540ef5aa911252a0776e55889295033f65444494a819fb6a2224a540cfdb4d11252a073ee8888929503b9f2aa8294a81cfea21304a540efcc4508a52a076fa664c129503afd3ba6094a81ddd956114a540cfe94b08a52a077d63384529503bdaaa42294a811ff2d5a846540efe42298252a047fcbaa21195023fe593508ca81df654d304a540eef4aa98252a077d9314c129503bf51126094a81dbd99a114a540ef6a8308a52a047fcba845295033fb5542294a819fd2ea114a540ef5c44a0a52a063fda8a21195033fa50a4294a811ff2e9314a540e7ed1108a52a067f5a684529503afb3bc2294a819fd6a2114a540cfeb4f08a52a067f4a8845295023ee59b5094a811fd2c5a64a5408f7974a0a52a047bcba5512950237e5b3508ca811ef6d2aa4e540 else 0x819fd68a11465408ff97499232a067eda788919503beb19c228ca819fb6a22246540cfeb4f08a32a047fdba14919503bb72ac448ca811ff2ea2246540cfd97511232a056fdb6149195033fad44228ca819fbaaa2246540cfdb4711232a073f688845195033f6d14448ca81df38ce2246540cfdb4b11232a076ee66889195033fad1c228ca81ddd9561146540cfd94b11232a067f5a584519503afb3bc228ca8157f2dd5246540af7b6829232a067eca8889195031fe52d1094a818ff69a884a5408ff970d3a52a063fca1a21295023fe5d51094a811ff2c5a84a540c7fd5544252a063fcbaa21295031ff4434e94a8197f286774a540e3fd113ba52a047fcb5699295032ff3bb4c94a811ff2e9874a5408ff962d3a52a065fca89dd295032ff554ee94a81d7d9de114e540cfeb4f08a72a076f666845395033fad34229ca819fdaaa114e540cfe97508a72a073f688845395033fa544229ca819fd296114e5408ffb6d55252a047fdb7aa9295023fed8d5494a811ff6d6aa4a540cfe94508a72a0777655845395023fedc55494a81df988a114e5408ffb74c3252a0677da7955295039bf444aa94a819df69a554a540eafcef2aa52a0677cba955295023fe5d4aa94a819df2a2554a540cefd552aa52a0767e66955295023fe5d30694a81dcf955544a5408ff974a9a52a047fcba58d295039df442a894a819df286554a540ed7cccaa252a075be7755129503a7f3bccc94a819bf69e664a5408ff974c2a52a066fca59992950337f554cc94a811ff6e9764a540e5fd1133252a066fda8999295023fedd10a94a815fd6c4854a540afdb6442a52a047fcba59529502bfcd810a94a815bf6d8854a540abfb6e42a52a057ddb321529502bdeda10a94a811ff2ea114e5408ff974a92d2a047fcba609695023fedd0a4b4a8157f2dd525a540cfb94b19ad2a075de778cd695033ee51466b4a81dd7956335a540adfb6c292d2a073ee88889695033f755444b4a81d7b9de225a540cfdb4f112d2a047fcba4c969502bdeda0a4b4a819fb2ea225a5408ff975112d2a047fcba955695023fe5d30ab4a819dfaaa555a540cef9752aad2a047fcba61d695031fe51510b4a81c7fa22775a540cbfd553bad2a0737e8895569503b3f2aac6b4a81d3f9dd635a540e7bd1119ad2a047fcba54d69503abf3bcaab4a819df69e555a5408ff974b9ad2a0677ca2955695033f652c44b4a811ff6e9714e540af7b6840a72a047fdba545395023fe5d2e29ca815bf2d9814e5408ff974c0a72a055fdb7205395023fedd1029ca811ff2e9514e540aefb6a10a72a056fdb608539502bfcd80429ca815ef6d0214e5408ffb7490a72a047fdba145395023fedd0429ca811ff2e9214e540ef5c44a0ad2a0773e5550569503bbb2ac22b4a81d7d9de115a540eddac7112d2a0776e55) else (if i<3 then 0x6a99252a067fca54c929503bf6a926494a81dfba22224a540efdacb11232a067fca14c929503bf72ac448ca81dbf999734a540affb6c52a52a076fe6629529502bfedc14a94a81cffa20a54a540affb6252a52a067fcba61529502bfe5d30a94a815ffaed854a540cffb74c2a52a067fda85d9295039ff442ec94a819ffaa9764a540affb70bb252a075fd875d929503b7ec3ccc94a81ddf9557146540efbc66b8a32a067fda35c5195033fed2ae28ca81cffa217146540cffb50b8a32a075fd875c5195033ff5510a94a815ff6cc854a540affb70b8a32a057fdb121529502bfe5c2e28ca815ff6c8854a540cffb4ec2a52a073fd87615295033ff5530a94a81cffa21854a540ebfceec2a52a057fcb1615295033fe50b0a94a819ff699854a540edfcccc2a52a067fda25c5195039fe5ad1094a81cff2c6884a540eefcaaa8a32a075fe77545195033fed3aa28ca81cffa215146540affd76c3a52a057fdb7545195033ff4434e94a819ff68d5146540cffd5544252a057fdb12a129502bfe5d51094a815ff2d6884a540cff94344252a073fcbaa21295033fe52d1094a815ff2c6884a540cff974c3a52a057febb54519503bf7112e28ca815ff6e15146540ebfd113ba52a075fd725c519503aff3bb0c94a819ff295864a540cffd54c3252a067fda7619295033ff5530e94a81cffa21874a540aff974c3a52a067fda8545195033fed330e94a815ff2e15146540ebf9513ba52a057fcb161d295033fe50b0e94a815ff2c6554a540aff96ac0a32a0777d8595529503bbeb2caa94a815ffaed834a540e7fb04c0a32a067fda5605195033fe50caa94a81ddf2ea554a540ebfceec1a52a057fcb8955295033ff554aa94a81dbf999834a540cff9512aa52a067fda695529503b7f334aa94a81cffa22554a540e7fd10c1a52a067fda360519503bbf2ab028ca81ddf5da554a540eef9632aa52a077be8855129503bdebb2a894a81def615544a540ef7b0eaa252a077bd8655129503bbe544aa94a819ff6898146540eef9712aa52a077bd6555129503bbf444aa94a81ddf61e554a540eefb0d2aa52a057fcb260519503bef19b028ca815ff2d5834a540affb70b9a52a076fe665d5295033fe542e694a819ff699754a540affd76b2a52a067fdba595295033fe50b0694a819ff285754a540ebfb0eb9a52a067feaa5d5295033fe5090a94a81dfb8898146540e7fd10baa52a075fd875d5295039ff442e694a819ff2a1754a540cff974b2a52a075fe7759529503bbf2ab0694a815ff6dd654a540edfb0cb2a52a057fcba95529503bbec2aca94a81dbf5d9654a540e7fd10b2a52a057febb5c519502bfe5d2ca94a819ff69d654a540aff962c1a52a067fca560d295033ff552ca94a81df988a1146540e7dd1111232a075ee77889195033f6d34448ca else (if i<4 then 0x9503b7eb1c44b4a815ff2d6225a540cff94b112d2a0777e554c969503bfab8a428ca815ff6e1325a540affb62292d2a057febb4c9695039ff44264b4a815ff2d5325a540cff94a992d2a075fe774c969502bfedaa64b4a81dbf999824a540aff96ac1252a073fe88609295033fed330494a819ff295824a540e7fb06c1252a077de3360929503bbf2ab0494a81def551824a540efbacb19a52a077de558cd29503bee42c6694a81df75d6334a540efdac711232a067feaa60929503bf6c1c448ca81dfb5ce2246540affd76c1252a057fcb160929503b7eb1ac494a81df78cd624a540eefcaab1252a077bd5458929503bf6c12c494a815ff6e1524a540aff970a9252a057febb549295033ff552a494a819ffaa9624a540affb70b1252a067fca160929502bff5dac494a819ff6a1624a540cff94ab1252a076fd65589295039ff442c494a815ff2d5624a540efbb06b1a52a057febb54d295033fe52ac694a81ddf955634a540cff974a9a52a067fca854d295039ff442a694a815ff6e1534a540aff970a9a52a057febb58d29503aff3bb028ca81ddf955734a540cff942b9a52a073fe8858d29503b7ec32c694a815ff2d5634a540affb6eb1a52a075fe7758d29502bfedbaa694a81cffa218146540efbb0f19a52a067fda760519503bef4446694a815ffaed8146540efdaa711232a077dd858cd29503beec346694a81df75da334a540edfccca9a52a0777d8554d29503aff3baa694a815ff6d9534a540eefcaaa9a52a057fcb154d295033fe50aa694a81df760d534a540efbae6a9a52a067fcba60529502bfe5d30294a815ffaed814a540cffb74c0a52a077ed76889195039ff4430294a819ff69d814a540cffd54c0a52a067fda860529503bf65ac448ca815ff6e0a14a540efdac711252a077ed53889295039ff4414294a815ff6d4a14a540eefcaa50a52a057fdb728529503aff3b94294a81d7f9dd814a540efdc44c0a52a077f4a160529503bef19b0294a81cff609814a540cffd5440a52a067fda720529503aff3b90294a815ff6dc814a540efdb0f11232a067fda6605295039fec330294a81dbf2d9814a540efdb0d11232a076fe6660529503bbf2ab0294a81def551814a540aff96ac0a52a067fca560529503bf6b12a494a815ff2c5524a540efbc66a9252a077ed82549295033fe50aa494a81cffa21324a540affb6c99252a057fdb84c9295033fe5426494a815ff6d9524a540cffb4ca9252a067fca8549295039ff442a494a81d7f9dd614a540ef7aa8a9252a0777d5354929503b7f332a494a81ddf955524a540edfccc99252a077ec8588919503bf6c2c448ca81dfb5d62246540efdb0d11252a077ed8588929503bf72ac4494a81dfb60e224a540efd90b11252a077ed6588929503bbf2aa6494a81dfb609324a540affb else 0xf2d6114e540cff94b08a72a067fda784539503aff3bc229ca819ff294214e540affb6a90a72a057fcb5485395033fed32429ca81dbf999214e540cff94a90a72a057fdb508539502bfe5aa628ca81dfd5c5214e540cffd5410a72a077f48584519503bfac2c228ca81dfd5d61146540efbb0f19ad2a077dd858cd69502bff5db04b4a819ff2e9825a540efbaeb19ad2a077de558cd695033fe512a6b4a81cffa21535a540ebfceea9ad2a077f65584519502bfedc2a6b4a81ddf615535a540efbae6a9ad2a057fcb254d69503bbf2aaa6b4a81df760d535a540edfac6b92d2a077de335c969503bbf2aae4b4a81d7f5cd725a540affd76a92d2a067feaa54969502bfedc2a4b4a819ff6e9525a540cff974a92d2a073fe885c969503aff3bb04b4a815ff2d5825a540efeb0f08a32a073fd87609695033fe52b04b4a81df78cd825a540cffd54b92d2a0777e55609695039fec1b04b4a819ff2e9535a540ebfb0ebaad2a077f572845195033ff552eab4a81cffa21755a540cffd552aad2a057fcb2955695033fe514aab4a81cffa22555a540eefb0b2aad2a067fca261569503bfa994228ca81dfd14a1146540affd76c3ad2a077f62284519502bff5db0ab4a81d7f9dd855a540aff964c2ad2a077f552845195039fec3b0ab4a815ff6e1735a540e7fd10b9ad2a057febb5cd69503bfac1c228ca81d7f61d735a540edfcaab1ad2a057febb54d69503bbf2aae6b4a81dbf5d5635a540cff944c1ad2a0777d8795569503bfaa9c228ca81dfd20a1146540efeb0508a32a0777cb2955695033fe52b06b4a81ddf955835a540efeae708a32a075fe7760d69502bfed9a428ca81dfb54e225a540efdb07112d2a077ed7388969503bbf2aa428ca81df78cd715a540ebfae4b8ad2a057febb5c569503bbf2aae2b4a819ff68d2146540efda65112d2a077de3348519503bf6c1444b4a81dfb54a225a540efdb0f112d2a077ed7588969503bf72ac44b4a81dfb2d6225a540efdb0b112d2a077bd5250569503bde29282b4a81def955415a540ef7ae4a0ad2a077be2250569503aff3ba62b4a815ff6d5315a540affd7698ad2a057fdb74c569503bdebaa82b4a81d7f9dd515a540eefcaaa8ad2a077ee225c569502bff5daa2b4a81df78cd515a540efdc44a8ad2a077f57154569502bfe592a2b4a81ddf549515a540efbc67112d2a067feaa14969502bfedc0a4b4a81dfb5c9525a540efed1108a32a073fe8814969503b7eb18a4b4a81df78cc525a540efea6290a32a057fdb314969503bf6c12a4b4a819ff69d525a540ebfceea92d2a073fe8854969503afe5baa4b4a81ddf5d5525a540eefaa6a92d2a077de3354969503bbf2aaa4b4a81dbf58d525a540efdc4490a32a067feaa88969503beeb9a64b4a81dfb609325a540e7fd11112d2a0777e558896))) else (if i<8 then (if i<6 then 0xa32a073fe885d519502bff5daca8ca819ff6a16546540ebfb0ebaa32a076fe665d5195033fed18a48ca815ff6cc8546540cffd5442a32a077de3314919502bfed98a48ca815ff6c48546540edfccc29232a057fdb2215195033fe5110a8ca819ff69c814e540ebfcee40a72a057fdb720539503bfac0a628ca81dfb8893146540affd76b8a72a067fdba5c539502bfed91029ca819ff288814e540cffd5440a72a076fcb660539502bff5da428ca819ff69d814e540ebfceec0a72a067fda6605395033fe513029ca81dfd5453146540edfcccc0a72a057fcb260539502bfedbac29ca819ff69d614e540cffd54b0a72a057fdb858539503aff3bac29ca81dbf589614e540efeb02b0a72a067fca5585395033fe512c29ca81dbf999714e540cffd54b8a72a057fdb85c539503bee992628ca819ff2e9714e540aff970b8a72a067fda65c539503afebb2e29ca819ff2a1714e540ebfb0eb8a72a067feaa60539503bf711242b4a81dfd5c5215a540affb6690ad2a077de3348569503bfa98a42b4a819ff6952146540efeae708ad2a077f57584569503bfb2ac22b4a81ddf955215a540aff96498ad2a077dd324c569502bfe5aa62b4a81ddf955315a540efdc4498ad2a057fdb548569502bfe5aa42b4a815ffaed215a540ebfcee90ad2a073fe88485195033fed42428ca819ffaa9764e540affb6e90a32a057febb605395033fe5d3029ca815ff6e12146540cffb74c0a72a057fcb8485195033fed3a428ca81dfd5ca115a540efeaa508ad2a077f55384569502bfe5aa428ca81dfd14a115a540affb6a90a32a075fe7748519503bfa99422b4a81dfd88a115a540affd7698a32a077f57154519502bfedc2628ca81dfd61e114e540efeb0d08a72a077f4b584539503bf7112a28ca81dfd5da114e540efeb02a8a32a057fcb84c519503bfab8c229ca81dfd546114e540cff94508a72a077f58184539503bfa90c229ca81dfd2e2114e540efed1108a72a057fdb74c5195039ff442628ca81dfd14a114e540efec4508a72a077f56284539503bfaa94229ca819ff6895146540affb6e54252a057fdb52a129502bfe592a28ca81df78cd5146540efeae508a72a077f57584539503bfab2c229ca81dfd616114e540efe90b08a72a077f65584539503bfac14229ca81dfd20a114e540efe96508a72a0777d5254519502bfe594229ca819ffaa8514e540affb6428a72a077f57154539503bbf2aa628ca819ff288514e540cff97490a72a067feaa48539502bff5da429ca819ff6e9214e540efeb02a8a72a067fcba54539502bfe592628ca815ffaed514e540cffb74a8a72a067feaa54539502bfe592a29ca819ff289514e540cffb4ca8a72a076fe66545395033ff554229ca815ff2e2114e540affb6a98a32a075fe774c5195033fe544229ca815f else (if i<7 then 0xaff3baa48ca819ff6a18246540e7fd10c1232a067fcba609195033ff553048ca819ff68c8246540efbc6641232a0777e5520919502bfed99048ca815ff6c48246540cffb50b9232a067fca85c9195033ff552e48ca815ff6e17246540efbc66c1232a067fda2609195033fed1b048ca81cff60d8246540cffb4ea9232a067fda5209195033fe529048ca819ffaa88246540affb6a41232a067fd7668d195033fe52a648ca81cff2ca8846540cff94544232a073fcb5a2119502bfe5aa648ca815ffaed8746540cffb74c3a32a057fdb54c9195033ff4434e8ca81dfb6093246540efbae699232a077f9214c129503bfd08a6094a81ddf9553246540cff94b44232a057fcb2a21195033ff555108ca815ff2d68846540ebfceec3232a073fe884c919502bfedba648ca819ff69d8646540affb70bb232a075fd875d9195033fe542648ca819ff6a17646540e7fd10bb232a067feaa61d195033fed430e8ca81dbf9993246540cff974c3a32a073fe8861d19503aff444ee8ca81d7f9dd3246540cffb4cc3a32a057fdb64c919503bfab142294a81dfd54a114a540e7fd1111232a077f58284529503bfa9942294a81dfe61d304a540cffb5111232a077fa884c1295033fe544448ca81dfd596114a540efecab08a52a077f48584529503bfabac2294a819ff69a2246540efeac708a52a077f55384529503bfac1c2294a81dfd5ce114a540eff2a498252a077f9814c129503bfcc126094a81dfe589304a540eff10298252a077f9514c129503bfc28a6094a81dfe5c5304a540eff2c298252a057fcb888919503bfcc2a6094a81dfe619304a540eff2ec98252a077f8854c129503bfd2aa6094a819ffaaa2246540eff2ea98252a077f9654c129502bfe5c2648ca819ff6a25546540cff9512aa32a067feaa95519502bfe5c4aa8ca81cffa225546540eefacb2aa32a057fcb295519503b7f334aa8ca81ddf6165546540cffb4eb2a32a075fe77595195039ff442ca8ca815ff6dd6546540edfb0cb2a32a057fcb2595195033fed30a48ca81dbf5d96546540eefb0ab2a32a0777d7695519503bbe594aa8ca819ffaa85246540eefb0d2aa32a067fe8868d19503bf6c12a48ca819ff619a346540efdae4a9232a067fd8768d19503bbe5c4aa8ca81cffa205246540cff9452aa32a057fdb6149195033fe540a48ca815ff6e05246540eefb0f2aa32a0777e88955195033fed40a48ca81cff61d8546540ebfceec2a32a073fe88615195033fed3b0a8ca819ff6998546540cff944c2a32a057fdb114919503b7f3330a8ca815ff2c98546540cffaecd2a32a057febb61519503b7ec3ccc8ca815ff6e13246540cffb74c2a32a067feaa615195033fed430a8ca819ff2e98546540affd7699232a067fda85d5195033fe542ea8ca819ffaa97546540affb70ba else 0x214a540ef7aa890a52a0777e5548529502bfedbac294a81df78cd214a540cffb4eb0a52a067feaa54529502bfedc2a294a81ddf955314a540cff974a8a52a057fcba54529503beeb1a6294a815ff2e1514a540cffb4ea8a52a067fca54c529502bfe5aa6294a819ff6a1514a540cff950a8a52a073fe88545295033ff5524294a81dbf589614a540efdc44b0a52a057fcb848529502bfedc24294a81df78cd614a540efeb02b0a52a077ee224c5295033fedd2a294a81df74c9314a540affd7690a52a077f5814c529502bff5daa294a81dfd616114a540efbb06a9a32a077dd7354d19503bbec2aa68ca81ddf9555346540aff964a9a32a067fda354919503beec3c668ca819ff2895346540efbd1119a32a057fcb854d195033fe542a68ca819ff2e95346540affb70a9a32a073fe8854d19502bfedb2a68ca81dbf9995346540affb6ea9a32a075fe7754d195033fec3b448ca819ff619a246540edfccca9232a067fe88689195033febb3448ca819ff615a246540cff90ad1232a067fda654919502bfedb2a48ca81ddf9555246540efbb0b19a32a077dd868cd19503beebb4668ca81df72163346540efbcab19a32a0777d7554919503beebac668ca81df75963346540edfcccc1a32a057fcb560d195039ff443068ca81d7f9dd8346540cff94ac1a32a067fca260d19502bff5dae68ca81ddf9558346540aff964c1a32a067fc8568d195033febab468ca819ff6895246540cffb0ad1a32a067fd6568d19503bbea9aa48ca815ffaed8346540cffcaad1a32a077de3354919503aff3bac68ca81dbf6196346540e7fd10b1a32a057fdb758d19502bfe5aac68ca815ff2c96346540affd76a9a32a0777e5558d19503beec1ac68ca819ff2a17346540e7fd10b9a32a057fdb85cd19502bfe5c2e68ca81d7f61d7346540affd76b1a32a057fdb858d19503b7f332e68ca81ddf9557346540cffaead1232a067fda8589195039ff442c48ca81d7f2dd5246540affb70b1232a057fdb758919503b7ebb2c48ca815ff2d56246540cffb4eb1232a075fe7758919503b7f332e48ca819ff6957246540e7fd10b9232a067fda65c919503bbf2aae48ca81df78cd7246540affd76b1232a067fda35c919503afeb9ae48ca819ff2e95246540cffd54a9232a067fdba54919502bfedbaa48ca815ff6e15246540cff950a9232a073fe8854919502bfe5c2a48ca819ff6a15246540eefcaab1232a067fda3589195033fed2ac48ca81dbf5956246540edfac6b1232a077ed8258919502bff5daa48ca81df78cd6246540cffb44b1232a075fe77609195033fed33048ca819ff69d8246540e7fb0ec1232a076fe66609195033fe52b048ca81ddf9558246540aff96ac1232a067fda560919502bff5db048ca819ff6e98246540cffacad1232a067fe5568919503)) else (if i<9 then 0x77fe5548519503bff4426494a81dff54d6246540effb0ca8a52a077fd5360529503bfec2aa294a81dff609814a540effb0690a32a077fd5248519503bfeb2aa48ca81dff5d9514a540effaa690a32a077fd7348519503bfec12428ca81dff60d6246540effae6b1232a077fd6360529503bfe9930294a81dff549814a540effb66a9232a077febb54919503bfea9c44b4a81dff6096246540efeaed08a52a077f58184529503bbf2aae294a81dfb88a114a540ef7aa8b8a52a077f586845295033fed2c448ca81dfd4c5214a540efea4308a52a077f58784529503bbf2a90294a81dfd4c6114a540efeae308a52a077f4a5845295033fe5290294a81dbf999714a540affb6a40a52a057fcba84529503bfa5ac2294a81d7f5d9714a540efeaa308a52a077de3384529503b7f334448ca815ff2d62246540e7fd1108a52a057fcba5c5295033fe52c2294a81dfd2a2114a540eefcab08a52a077f4b8845295039ff442e294a815ff2e1714a540aff96b08a52a077f688845295033fe542e294a81dfb888814a540cffb4f08a52a057fdb220529503aff3bc2294a819ff6a1714a540efbc6640a52a057febb5c5295033fed442294a819ff68e2246540efe97508a52a077bd54205295033ff5542294a815ff2e2114a540cff94b11232a067fca884529503bbf2ac448ca81def552114a540ebfb0eb8a52a057fdb3205295033ff552e294a819ff699714a540affb70b8a52a077bd4148529503bdeb8a8294a81def605414a540ef7aa4a0a52a057febb4c529503b7f332a294a81def545414a540ef7ac4a0a52a077be5550529503bdeb2a8294a81ddf955514a540ef7b04a0a52a077ed8288919503bbeb2aa294a81d7f9dd314a540affb6e98a52a073fe884c529503aff3baa294a81dbf999314a540affb6c98a52a057fdb654529502bfedc26294a81df78ce2246540cff97498a52a067fda6545295033fe5426294a815ff2e1314a540affb6628a52a0777d52545295039ff440a294a815ff6c8514a540efbc6628a52a077de33545295033fe540a294a81dfd5c5514a540affb7028a52a077ecb888919503bf7112a294a81dfd605514a540cffb5028a52a077bc8550529503bdec2a8294a81dfb58a2246540ef7b68a8a52a077bd5454529503bdebaa8294a81def5d9414a540efda6511232a077be8850529503bf7110a294a81def619414a540efdaa511232a077bd8750529502bfedaa6294a815ff2d5214a540affb6a90a52a076fe6648529503bf7444448ca819ff295614a540cff94a90a52a067fda6485295033ff550a294a819ff2a1214a540cffb5090a52a0777e5558529503bdeaa2c294a81cffa21214a540efda6490a52a077ed62485295033fed42c294a81df78cd714a540cffd54b0a52a057fdb8585295039ff442c294a815ff6cd else (if i<10 then 0xb2648ca81dff6155146540effb6ac3a32a077fd6388919503bfec3b0694a81dffa213246540effacac1a52a077fd7560d29503bfea9a4294a81dff6c5834a540effb64c1a52a077fd5254519503bfeb9aa28ca81dff60d5146540effaecc1a52a077fd8254519503bfea9c448ca81dff54d5146540effcaab1a32a077fd8754919503bfebab0294a81dff615814a540effb62b9ad2a077fd855cd69503bfeb2b0294a81dff6d95246540effcaac0a52a077febb60919503bfedc2e6b4a81dff61d6246540eff96ac0a52a077fd5354969503bfedb3048ca81dff54d614a540effae6a92d2a077fd535c919503bfebb30294a81dff6c5525a540effb6ec1232a077fd8760919503bfec12a4b4a81dffa21714a540effb0e992d2a077fd8558919503bfebaac48ca81dff60d814a540effaeca9232a077fd8754529503bfeb9b0294a81dff9556246540effb0c99252a077fd8554919503bfec2c44b4a81dff956225a540effaeac1ad2a077fd854c969503bfebaa64b4a81dff955324a540effb6a992d2a077fe8854529503bff2aa64b4a81dff549325a540effb0ca9232a077fd854c929503bfeb2a6494a81dff215324a540effac6b9232a077fdb254d69503bfea9b04b4a81dff6197246540effd1050a52a077fd7360969503bfec3ac294a81dff5cd8246540effb06b92d2a077fd855c969503bfea9b048ca81dff58d8246540effb62c1232a077fd855c529503bfec294294a81dff595714a540effb06b8a52a077fd535c529503bff442e48ca81dff5d5825a540effcaac12d2a077fd8760529503bfedab04b4a81dff6c5535a540effb0cb8a52a077fcb560919503bfec3aa4b4a81dff61d535a540effaeab0a52a077fdb754969503bfedab048ca81dff6cd525a540effb06a92d2a077fd7660919503bfec1ae48ca81dff60d614a540effb0ac1232a077febb54969503bfed9b048ca81dff6157246540effb06c1232a077fd535c969503bfec2ac294a81dff5d58246540effb70a92d2a077fd6560919503bff2ab048ca81dff5957246540effb0aa9252a077fd6354529503bfeb2aa68ca81dff595524a540effb64c2ad2a077fd7654d19503bfe5c2a48ca81dff6e15246540effae6a8ad2a077fd5354569503bfedbaa48ca81dff60d524a540effb64a9a32a077fd5354929503bfec1aa48ca81dff6c55346540effaa4b8ad2a077fd325c569503bfeb9aa294a81dff54d715a540effb06a8a52a077fc8548519503bfeb9aa48ca81dff4c9514a540effb66c3ad2a077fe8854929503bff2aa62b4a81dff615525a540effaea98ad2a077fe8854919503bfec32a494a81dff549514a540effaa6a8a52a077fd3254569503bfea92a2b4a81dff6195346540effae4a8ad2a077fd8254529503bfebaa428ca81dff61d5346540effb6ca9a32a else 0x540effaea90a72a077fd6548539503bfebb2429ca81dff6d5214e540effb0cbaa32a077fd625c539503bfec2ac494a81dff6197346540effb6cb9a32a077fd8548519503bfeb2ae68ca81dff6157346540effd10b9a32a077fdb160d19503bff442428ca81dff6c98346540effb70b9a32a077fd6354919503bfec3a428ca81dff6c57346540effb0ab1a32a077fd5358929503bfec3ac68ca81dff5c9315a540effaa498ad2a077fd7558d19503bfebaa42b4a81dff54d215a540effaa490ad2a077fe5558929503bff2aa42b4a81dff60d624a540effae690ad2a077febb60539503bfe5ab0494a81dff6095246540effaa440a72a077fd5260539503bfeb2b0494a81dff615824a540effaa498a32a077fdb65c539503bfeb2ae29ca81dff6c9714e540effb70b8a72a077fd6254919503bfed8aa48ca81dff955824a540effb6ec0a72a077fd7660d19503bfec1b0494a81dff5958346540effaeac1a32a077fd5360929503bfedb3029ca81dff54d5246540effb64c0a72a077fcb260539503bfec3b068ca81dff6dd8346540effaecc0a72a077fd654c919503bfea9b028ca81dff9553246540effb04b8a32a077fd8584529503bfeb9b028ca81dff6093246540effb06b8a32a077fd624c919503bfec2ae28ca81dff60e114a540effaa708a52a077fd535c519503bfec1b028ca81dffaed8746540effb6a99232a077fcb161d29503bfec2b028ca81dffa22114a540effaeac0a32a077fe5560519503bfebaa648ca81dff4c97146540effaa4b8a32a077fd8784529503bfec2a648ca81dff2153246540effb04c0a32a077fe885c519503bff444448ca81dff6162246540effb66b2a52a077fc8588919503bfec2aca94a81dff61d654a540effb0d11232a077fd3260519503bfec32ea94a81dff6dd654a540effb70b2a52a077fe885d529503bfed92ca94a81dff61a554a540effb6ec2a52a077fd8761529503bfec314a94a81dff60e2246540effaa499232a077fe5588919503bfea93028ca81dff6c9854a540effb62c2a52a077fdb661529503bfeb2c448ca81dff5d9854a540effd10a8a32a077fd655cd29503bfec3b0a8ca81dff615734a540effb0a90a52a077fdb661519503bfe42a4294a81dff6dd8546540effd10b9a52a077fd3254519503bfedc2648ca81dff595214a540effb0cb9a52a077fe5548529503bfebb30a8ca81dff616114e540effac629232a077fd8284539503bfec3c229ca81dffa21214a540effb6ab1a52a077fd7284539503bfed8b0a8ca81dff6c98546540effd1098a32a077fd5284539503bfec324294a81dff61d634a540effb0690a52a077fd864c919503bfed8b0e8ca81dff6c98746540effb0e99232a077fdb760d29503bfedb2648ca81dff6cd8746540effb0ea8a32a077fdb661d19503bfeb)))) else (if i<17 then (if i<14 then (if i<12 then 0xcbca8bc34bbf0bb4cbb08bac4b9f0b91cb8d8b894b850b7acb708b6c4b650b60cb598b524b4e0b49cb458b414b310b1dcb198b064afc0af7caea8ae64ae20addcad98ac94ac20ab4caa48a9a4a900a8bca878a804a760a6bca678a574a530a4bca358a2b4a240a19ca128a0849fe09f3c9ec89e249db09d6c9cc89c549c109bcc9b889b449b009abc9a7899a4996098bc97e89744970095cc958894b49470942c93e893749240919c90c8908490108f9c8e988e548e108dcc8d888bf48ac08a7c89a8887487a0875c8718864485a084cc8428832482e0823c810880c480507f1c7ed87e647e207dac7d087b747a707a2c79e87944790077fc772876e475e0750c74c873947260712c6ff86fb46f706f2c6ee86ea46e606e1c6ce86ca46ba06b5c6a8869e46880683c67f867b4674066fc66b8667465d0655c651864d463a062fc6228618460e0603c5ff85ec45e805e3c5df85db45d705d2c5ce85ca45c605c1c5b485b045ac059ec59185844580057bc5778573456f0561c55785504549053ec528851e450e0506c4f084e044dc04d7c4d384cc44c504c0c4bc84b844a80497c4908483447f0471c46d846644620457c45084404430041fc412840b44070402c3fe83f443ed03e8c3e483e043dc03d7c3cd83c043bc03abc3a48391438d0388c37e837a436d035fc35b835443500345c341833d43390334c330832c4322031dc319830943050300c2f082e642e202d4c2cd82c042b302aec2aa82a0429c0291c28d828942850280c27c82784262025dc253824f424b0246c23f823b42340229c2168212420e0209c1fc81f841f401efc1e581e141d101c3c1bf81bb41a8019dc18d8189417f0174c16781604159014bc144813d4130012bc11e81174113010bc107810340ed00e5c0cf80c840bb00b3c0a38099408f0084c07a807640630052c04e803b402e0023c01f801b40170012c00e800a40003bfebaa6294a81dff595534a540effb04a8a72a077fd7654539503bfe42a6294a81dff6c9514e540effae4a8a72a077fe554c529503bfebb2a694a81dff6156546540effac4a8a72a077fd8154539503bfeb2a6294a81dff615314a540effb0e98a52a077fd8758539503bfebaac29ca81dff549714e540effb02b8a72a077fe884c529503bfec326294a81dff6c5534a540effb0d2aa32a077fdb254d29503bfeb92c29ca81dff549614e540effb0498a32a077fd8654d29503bfec3b028ca81dff6153146540effd10baa32a077fd7148539503bfea8a429ca81dff2153146540effb0a10a72a077fd7558d29503bff444229ca81dff615634a540effb0e98a32a077fd8614919503bff2aac694a81dff605214e540effcaa98a32a077fd754c519503bfec3aa694a81dff608514e540effb6ca9a52a077fd8759519503bfedb2429ca81dff615214e else (if i<13 then 0xdc789c745c671c5fdc589c4b5c411c33dc149c105c031bfbdbf79bf35bec1be4dbdd9bd95bd21bc4dbc09bb95baf1ba1db979b8a5b861b81db7d9b765b721b6adb669b625b5e1b59db559b515b4d1b48db3b9b375b331b2edb2a9b265b1c1b0edafb9af75af01aebdae79ae35adf1adadad69ad25ace1ac9dac29abe5aae1aa0da939a8f5a8b1a86da7c9a6f5a681a54da509a4c5a3c1a31da249a205a1c1a17da139a0359ff19f1d9ed99e959e519e0d9d699d259ce19aed9aa99a659a2199dd993998f597f1971d96d996959651960d95c994c59481940d93999355931192cd9259918590b18fdd8f998f558e818ddd8d698d258c218a2d8959885587e1879d872986e586a1865d85b985758531848d844983458301822d81e9814580d1802d7fe97fa57f317ebd7e797e057dc17cbd7c497ba57b317aed7aa979d578d1788d77b977457641759d7499745573b1736d72f97285724171fd71b971757101708d70196f756f316ebd6e496dd56d316c8d6bb96b156a7169fd69896945690168bd6879683567f167ad66d96605656164bd63e963156241610d5fd95f355ec15e4d5dd95d055c915c1d5b495b055a915a1d594958455711569d5629555554e1543d53695265522151dd51994fd54ea14d9d4d594d154c414bcd4ac949c548f1487d48394765472146dd469945f54521444d43a94365432142dd4269413540f140ad406940253fe13f3d3ef93eb53db13d6d3cc93c553be13b3d3a693a2539b138dd389937c53781373d363935c534c1347d33a932a531d1312d30e930152f412efd2d692d252ce12b7d2a492a052991294d2909289527c1277d26d9266525f125ad2539240523c1231d22a922052191211d20191fa51f011ebd1e791e051d911d1d1c491bd51a4119cd19891945187117cd1789174516d1165d161915d51501145d135913151211119d112910e510110fcd0f290ee50ea10e5d0db90d750cd10c2d0b590ae50a1109cd098908e507e1079d07590715064105fd05b904e504a1042d0359031502d101cd00c90084ff80feacfe68fdf4fdb0fd0cfc38fbc4fb80fb3cfaf8fab4fa70fa2cf9e8f974f930f8bcf878f834f730f5ccf588f4b4f470f3fcf3b8f374f300f22cf1e8f0e4f0a0efccef88ef44eea0ee2ced58ed14ec70eb9ceaf8eab4ea70ea2ce988e8e4e8a0e79ce698e5f4e550e44ce3d8e394e2f0e2ace208e134e0f0e0ace068e024dfe0df9cdec8de84de40ddccdd88dd44dcd0dbfcdb58dab4da10d90cd838d7f4d7b0d76cd728d6e4d6a0d65cd5b8d574d4a0d45cd3e8d3a4d360d25cd188d0b4d070d02ccf58cf14ced0ce8cce48ce04cdc0cd7ccd38ccf4cc50cbdccad8ca94ca50ca0cc9c8c894c820c7dcc708c694c620c5acc4a8c434c3c0c37cc2a8c1d4c160c05cc018bfd4bed0be8cbde8bda4bd30bce else 0xef45af3e6f342f2fef2baf276f202f12ef0eaf016ef72ef2eeeeaeea6ee62ee1eeddaed96ed52ec7eec3aebf6eb52eb0eea6ae9f6e9b2e93ee8fae8b6e872e7fee7bae776e732e6eee6aae666e622e57ee4aae436e362e2eee21ae0e6dfe2df9edecaddf6ddb2dd6edd2adce6dc12db9edacada26d9e2d93ed89ad7f6d722d61ed57ad536d462d3bed2bad1e6d1a2d0ced08acfe6cfa2cecece8ace46ce02cd5ecceacc16cba2cb5ecb1acad6ca92c9bec91ac8d6c802c78ec74ac706c632c55ec51ac4d6c462c35ec2bac276c232c1bec11ac076bfd2bf5ebe8abe46bd72bd2ebc2abb56bb12ba3eb9fab9b6b972b92eb8eab816b7d2b72eb6eab676b632b58eb4eab3e6b3a2b2feb22ab1e6b112b09eb05aaf86af42ae6eadcaacf6acb2ac6eac2aab86ab42aafeaabaaa76a972a92ea8eaa816a772a72ea6eaa646a5d2a52ea4eaa446a372a26ea1faa156a112a06e9f6a9e969e529e0e9cda9c969c529bde9b9a9b569b129a3e99fa98f69882977e973a960694d2948e938a928691b290de900a8ea68e628e1e8daa8d368cc28c4e8b1a8aa68a02898e894a88d68892884e880a8766872286de860a85068402832e822a812680527f7e7f3a7e967df27d7e7c7a7c367bf27b1e7a7a79d67992794e784a78067702762e755a74e674a2736e729a722670926f5e6e8a6de66da26d5e6d1a6cd66c026bbe6b1a6ad66a62698e688a67866742666e65fa646662d2628e624a620660a2605e5fba5ee65e725dce5d2a5b365ac259ee59aa59665922581e57da57965752570e55aa5476540252ce519a51565052500e4fca4ef64e224dae4d6a4c664bc24abe4a7a49d6484247fe472a465645b2456e449a4456438242ae41aa4166412240de409a40563e623e1e3cea3c163b723a6e39ca38f638b2386e382a372636e2369e365a3526345232ee324a3206313230be2fba2eb62e422dfe2dba2d762d022cbe2bea2ba62b322aee2aaa2a6629c228ee281a27d62792271e26da269625f2257e250a24c62452237e224a217620a21fce1eca1dc61d221c7e1c3a1bc61b221a7e19aa18a617d2175e16ba167615a2155e145a141613d2135e131a12a61262121e11aa11060fd20f2e0eea0e160d720cce0c8a0c460b420afe09fa08f607f206be05ba0576053204ee041a03d6030202be027a01a600a2005e0019ffd5ff91ff4dfea9fe65fe21fd4dfca9fc65fb61faedfa49f975f931f85df759f715f671f4ddf499f3c5f2f1f21df1d9f105f061ef8def19ee15ed41ecfdebc9eb85eab1ea3de969e8c5e881e7dde799e6f5e6b1e5dde419e345e271e22de1e9e1a5e101e0bde079dee5de11dd6ddba9db65da61d92dd8e9d8a5d861d7bdd5f9d585d541d4fdd4b9d3b5d371d26dd199d125d051cf7dcf09ce35cd91cd1dcca9cc05cb91cb4dca79ca35c961c88)) else (if i<15 then 0x40809040483c05e03e0106444040804050183e03e0106434080b85b84b80f8041915c3bc054420c8800814040f07b85b84b80c8860519c124410c87c1ee09e0322181454080f80c882190e4410c908c7c1ee132218144b068321507c190b83ec2d443028941f06420408321707b87585e05110103c05e03e00864470443210020683e0c8404e1003084610786284c04b0588191e83e0c8418a13011012c16218006470408321707b84f8002310c2d0c8410a1421306160a25b06c0a4321f07f800230ec194420c87e006128643006084283f00e05e0240289b83ec1bc01c27028a0421510e0f70ec0ab0b60c3701780f8021913c050c90a468101007080304018200810010f80f800178fd0d7d033d01fcfabcf07ce93ce1fcd7bccd7cc33cbbfcb1bca77ca03c95fc91bc847c7a3c6ffc65bc587c4e3c40fc33bc2c7c253c1afc10bc037bf63bebfbe1bbd77bd03bc8fbbebbb77bb03ba5fb9bbb917b873b7ffb78bb6b7b613b53fb4cbb457b443b3cfb38bb317b2a3b22fb18bb147b0a3b02fafbbaee7ae73adcfad5bacb7ac43abcfab2baa57a9e3a90fa83ba737a633a4ffa42ba387a2e3a23fa19ba0f7a0839fdf9f0b9e979e239d7f9d6b9cf79c839bdf9b6b9af79a839a3f999b98f79853980f976b96f7962395af947b93a7930392bf924b91d7916390ef904b8fa78f338e5f8dbb8d178c738bcf8b5b8ab789e3890f886b87f78723867f860b859784f3844f83db833782c3821f817b810780937fef7f4b7ed77e937e1f7dab7d077c637b8f7aeb7a777a03798f78eb787777a3772f765b75e77543749f742b7387731372cf725b71b77113706f6fcb6ef76e236ddf6d6b6cf76c836bdf6b0b6a6769c3691f687b67d7676366bf661b65776503648f63eb6377633362bf621b617760a35fff5f5b5ee75ea35dff5d5b5ce75ca35bff5b8b5ae75a7359ff595b58b7584357cf575b565755e3556f54cb5427535352af520b516750f3501f4f7b4f074e934dbf4d1b4c774c034b5f4abb4a47497348cf482b47b746e3463f45cb44f74483443f43cb432742b3420f419b40f740833fdf3f0b3e673dc33d4f3cab3c373bc33b1f3aab3a073993391f38ab383737c3374f36ab3607359334ef347b33a73303322f318b311730a32fff2f5b2ee72e132d9f2cfb2c872b832b0f2a6b29f72983290f289b282727b326df266b25c72523244f237b233722f3227f21ab21372093204f1f7b1f371ef31e7f1e0b1d971d531d0f1c6b1bf71b531a7f19db1937186317ef174b16d7169315ef157b14a713d3135f12bb124711d3112f108b0fe70f130e9f0e5b0db70ce30c6f0bcb0af70a83097f090b0837076306bf05eb054704a303cf032b02b70213013f00cb0056ffe2ff6efecafe56fdb2fd0efc6afb96fac2fa1ef9aaf936f862f7bef71af646f572f52 else (if i<16 then 0xc2f013104321f80f802190fc07c010c8760688c2f0090b4321b82423090103e01216864370084611800404828101404080a84020280c10883090cc051200306c230290c87c1fe018146124f018328291a030644383ec3b029c26830c008170e510832823200e84018281019104321388607b87605585b061bc050c90a4781ee13e0008c40210a0921788c2d0bc581f60de00e1381454080a020404c20281036f00085f0109601c0c00514780b8704400e0420289900c381ee1d6178144f0070908801c0cc0513607b88585e051004820361e0fb0e709c0a27802192118d44383fc041089c1fe02084308c08805a30e0512a0406c130290c87c1ee17814e1361cc2260190987419080701542202b8144110c0701b04832120306c120c84a2061d0643510e0f70eb0bc0ab09b0160c4585d84d80a192149405c28081b01c0a43218090783ec2fc03028c24b617e0061286440120e097078441848211783cc2426810880301e0fd0304ac1c3090423707e81838e0e1848211b83f40c1c7070c24108c44da060e20c861208460120817840a4206010120980050102e20e1da17a12a1b06464030e85e84e80f804191404c3c1fe01814846441c4154461f07b87685e84e80e051881c07c203410120988223080c0206010170a0e20aa230cc39118403a14030d88707d87580605211990710551187c1fe018148464c0aa0f8231e05507c118fc020c908c60601710e0fd0bd09d01042300d84078280614040809040482024102009808408c213004c12008c40120817841c419811810080e20cc08008c406604f04004620090404820241012080b0611a08e42e0c89047217064384682314234118b02983d08c7c1fa17a13607a02e1d814782390b8321e85e84e80f802191608e1184e2181ee1d61761381461a7b0bb09b0143242928090500c20061846823120921788048202410170f07e13e0e1848211783f09f070c24108ae0108c2b0990b432429200185c27c0142e0c88024130e446101387c07c010c8683888c2e0fc27c1c30904229136138321848211783d09f070c24108bc1e0a8612084470884610040500c20241f018328291a0e2230911828081015080e84048303908d046390bf00309432200906c42c3bc06c010c8a83888c2b10e0fb0ec0a709a0c3204050203e03e0106430080b84f80285c1911c3bc04c420c88808181c446120187c07c020c86008101208090409c202410120f80f804190c048204e171070ef0170083228040500c2e20e1de02e010645f01f00832180d8783ec39c27028960888c2710e0ff010422384f80285c191009c203c1f01f008321a0407c07c020c860081019080184048200c10120824f078971840948460231d0183e032208643301081184080360d06420120985c1909442c1a0c87c1e08e08615e0a207a640 else 0x5217611c1e836164581c70814138918618d0703038181c709140e3868a83e0705e03e0141e1904a0f81c103bd07e81b80b85d87384c192207283c460c1406080e780f800641010007032c604610510d83059082203304e1a13090d83584a19214902610702c8661360c845a2016c57040f80185865828c191583d0704c1e83828120842c0e02885a9204820a225218038120b80078082616838164341c0a818440600c2610702d0682961086415a4b06700109708f84285d11c00202a130b3090b2184b18598486005915c2426161e020e81f80b8721910c1028081b04701c0a0c02183064430284e1160981418044060d078607283dc27028300a119038e1181418054080c88582384e05060164420a905430088101910c0a158584c390702f060fb8140801804910c0a11870683c2e081e020b8705c243c041e02704120e05c1240c4e021a0f0c0e605384507860142301f6071c10103028300e808181cc0a0400c9238405119c04480c17040c2040e08c3a0701442d49024108881230e0510c82c09041c41460702c8802e10510f80e880640c1702a0561a84414e1804b0d0d868308658c47c300c2432c861a61219637000d8006c0036001301863b000bd0c31d800783e42ec0026030ca62061ce1062908c541c0bc0b51a0e12905f0f83ec3b02a1182c8a11016a230809840948600c06c213ee001963412c0a0cb0c8270105c00260c1406080a85c04361c83825c18647040b830609cc10461c101b0c13e050847c2c6c0032c981417a16437088320c71a090388618d04b02b442c24320a1300a3038164405109820501826101404098304074207b04e1863b000f07e0542306191c20304e1862b090a02040fb02ac242c8328b61761286418e405bb0941c0cb25800414432160e28381864015098405048260c1406098304c103c04170109296880640e09c30c5217610e0883818654060982060702610105cb04e0241c0bc0b5312940e090203609a0686415e4e02b0417015820889a07040b92176108381865c0a8461094b8689c183025e03a20190430e70d81c0cb218706408263c04c3a07032ca1941412082e485d8420e06195c20303861c16a37080894b8009c2426061c0a84611820430207032c761c14080d874882190579383ec274402d4802614060a030410207032c761c0ba19634060e054230ac38261c196284081c1204040602e00181c088fd84d80860065941ff83f028c84d2cc24c0a21075e0f323c0a34b30931899868658ec04381560014a1864051080d84c182808103ec0a0cb41c0b52b81c230b83ec41c270289c1ee1de03814620541c4464231f80485a190c068203e141c8461780f802190d0701190a460241e0fb03f0170ec0a281384c411184118251c1e6062460d80847f0090b4321a0e2230bc07c010c86e1108))) else (if i<20 then (if i<18 then 0x107bf0041242f0b529840423302a09c30c941e1408098205010360c86415a3b060a02041cc1cb0bf04b03dc101fec2e103029460810210b808501020fe08016a33040839994e051a9820150bd0482582c4904e18270b8705054282a10a9815e05e0f0b7281206071c385038e0824030a0a86070304ee08209ef004230c82062f802118641342dc003142f88606181c084f7802118641302983c2dc68396202b100b07987685e84863170c342f02ac0f83c1fcca708f0461095e0083882a88c4b03e0fc0a842423283f860080a4282b620281509820609c2e0016c16e34040c0a850c10c82dc702a10a9015f0060f0c4281684c4383c1082bc8e20141c4300af1a0ad87090710c02bc660614030a0ad82084e50544806182741c138186057816c4383c2bcb04ee0628150c80af18a5c0a88c0c304e1710e0f0420af2056588587419211950543a16481a1217c482741c10561881874192119781683c2bc613d039a17a1217c581c0e054190578d00c229682a282741c13818609c2e0614040c2940a8a09d07050a502a2c0a0c10c31a0e0514905444808382827c0a142320e4858e42c2c82dc708c24a14015e484682190b1a090608618c901070504f81424150988050542e1c17040b82050543217e01047064481290b8230be2684c8585f0e08e42c318708c2a704617e484682190b81c24237804118591211a08642e070280310d08ce1d216e01046164690b8230be1c234108a11a08450422a628468210a00af242320e0a11a084408ce0015e16443030c1185909072c0c482686086415e41394153030c80af2994f07e858599880211a09dc20560682a24132404320c42581a0e0983c09c30c64808380841884067e0fc0ab0e423280d85c00282a106dc30329310d0bd09240c230424994f07e8583f988021181d342f426c410c8a838130e0e057802192119209cc0c4861c1f62082a164570ed0bd097000c6285b78050786211056c0c56061413f00c0a0c4218205010303817000270c31854f80419062104a10842802bc9c0a480188341509820501024810382b03d01d0b70ed09832318484c10261010150a020489907030078141c0a083db82780c88219160702e09c05038370481c140e38709119071c0460b96100a2180441c092020e0a40ec23028300860c160f30941c0c0258086c04361360212d22086453090c0148838458260506014c2020ff814252180405c910b040510c0283c58482886011c23028300680c1c0a0b21280c0203c211184860110103c1e616612e098141646472208b010982041dc948072c2ec07c00328f41fa06119039e0217c64040d07c0e080b428101a0f81c140e780f8006410c2024a50641803c0a846142040e0901824a5038207781c30bf00a0f0ca318206c244a4300741f038281c0850be1c139848a071c else (if i<19 then 0x50784f0649283c2860702d490381300d141e16a508c81ca0f0a10b52d0786005d0e83c3002d466101a0f0c815078628650e83e0c8300741e16303816a408c81cd10a0f0b52f8020e213859101002e840ef41e16a33080e835822110661102020b9e0083884e16a53080d8205119c0446061446b0417010406c308d6022846123b011c23090b8870798705d981fcc242ec66061413b034320af218718685d8c1d6c042ec6e1a1703082e58720e21385915c243025a0c11ae121625c0ab04f010810b32c09384f80023062942cc167c04cb0204108c08ae1de0304416257080d818500c2e0288c24618644080f8082a18806411c002e101054b034220cc204ff079949a582115c003c04101b080a8500c26061221863446098185c360702a82e49e01a1619038460846683588384c19141702a0482488c190341230905c0cc200b86073c04304318808b62161c84419854080a0e22305d0ccecc5304b09ec4383dc24109161c1121b010800b5220958083c05d9383cc7cd2c108961c1b034120960b1220e12905f0ec3907109c2d49606838224041c08c0c10be2f0798221386191118265210384f83861208464030a0a58421905692c19c004e0013008c1624a0f0270c31d0787c061002e8602810900c10c51a01850bd0482582c4812c12985e646116111e000a408c9c0a1160b40c32583584a1921491c00202a14030d07e0504d8dc0426061c2f325c0f096b094403290464585d84a1905692c2d0bc2d4612c12866985e116111e000a408c9b0b0840e0798a9a9823142d8c8fc00220148118c80814030d80050490bc2e860e60df85ee1181e13063708d08098270b2101004c202042132570904632930d2a0406c19c24260240ca4a13011682485e4128821102338005005b92119070280310908c838204602141c0b222090478618e1190705042e1c28468217041c2341088c0c203921704616443040c23410c85c0e1211a08642e070908dc1fe0104616453040c2341085005b9211a084504f814241290b08f0c32209586a178f0284ba09c2c8985f825815610129e0011064781f08ca0230f07e054230619025030c4610101f0c10b880a11a084508c83823040b81c108b83f02a09c30c8620184641c1423410b818ec1c1a609c30c8e0004e186308cc0a8460c3238005c242e081827c0a13868409c30c461017000f010500c26161e020b8405c202e1d81504e1864a0f0b8185c0c2e021e020838a0e0618c28dc0207032c811010b0246120a219063030c13e0509c402e1c17010f0105c102e081e020b8185c0c304e1862303083d82e585a1785f14304c2cc382fc8166e001641304a0f0a0184058282485e17e3f01f000c10bf20608510b03f0282502cc2c81c4c07a1303084403fe83f8005a9741c1b82e4682413085e16a43030a01840842e02 else 0x107c07c003206166e21e02e0017c5a0ff01f000c8240e04c0c20b960761da16154864681c0a0186071c2046101408081686073c07c0032090381446701f0081c0bb2a2340e081fe071c43c042f8b0381045d0670e709310832301f409384f80285865191183025a0d620e12190570e70d7098220c02c09780f80064101c6049c242f89e0083882a88c4076075446121e0ff000bb3987060703038e12281c70d138240e0a071c1040fe0b3e02652192084681c70e122340e3808d11a0704608122681c140e0501028061240d0b0be1c0e04c0c2e0902412c162471070ef0181c0ba282e1885822110601604bc07c003208e12e03e0103816a507f074f01b104322c0e78068586412048231c382d48838184681cb011984c0e05d8e070948508ce20e1d038176530409818607023342c2f8908d0396023b010890bb1a04060703a0d62161ce1306453080915988187384c1914484948200328908d038112176444681c140e04116049c3bc04c402f8c8256020d81764846123103f994e13f0784082c8a9821201da11848783fc002ecd08c24215417647000aa0bb19820407c308c1b100d8818720e06192c40288c86416e3b100a0e588084a048420030c882562161c186162505960f30ef010c6281484173c010711188102172207f05932cc27c1c081153042403ae05581e13840e0e384c21210203c0413080e8358182a587384853a191e118282418a186303fb0941c0c3202305d881190702ec60ed6021763076c27c12b03e0f07f329d0bc0a842542320e0ac042d04a03008e001015080f84167c04324ca4c40a88c14040f0104c103a0d6060a8e1d6121088647c27c1c081b10b09c0a3213866080f9c25c07c020702d4d0256060b8e09a1617c67000984e83581a11066178082048105cf0041c446220958184606191072c0c5606141c05408c2520c6298185a0618c106c42c3907030ca810142741c0c3198858702ce0538498de231202107020b9610844180405442208b0b1212958820e0c06c282560611e1724404084658821385910150c24c403208e1ce1ae1303818654040b818500c2e081304085998a6095876055887079a5e235062805021180ff606e1da170646708d068320c72120384c0e0c165c3bc05c00318b41e0c617e381cd10a0f0b5240e050102606105cf0042741c0bb298206c243038105924081c70ef010c63584c85a1906392118486c4383ec3ac002ece62861a17634080a0958683005d9048ec34562161d60083888c5309427b10a0c0cc2a2340e0807436001708092040e08054288de0103817647010a886050ac0c3814160f0d07c0e0588dc22c0d07030c90384a416219044080b8087809c104e08170e0a2321905b8d83d0704c1e838241c0a2020e083160c810032481100e341fa061810646a0f07d8320c9240e)) else (if i<21 then 0x112920e5858c17036096060da652441c0d880489907048396202096b0b138705054288c612246305c70410552230a98c2f01d640cc388134164838370144681c185e01f4819871052e054488d038e1a305c329103a850721182ac708c838207532c7003292046488605028102ae070417861c838308c41c1213e050a08454c2c868381642a630cb44041c1a0e485c2304c102310704854132941c2401860847b07824902b0c505221814e10390b09984681c20a5a0a8a11a08642dc3a070a0b8e102910c0a70903e205e024a81987101c583d070616411f08c838430e8468211a2340e3848e119c420842c881118140923045442105984640e0c231c0511a070904e8542840226142320e082582c84118c1e838307105c12818249848e09c23f02860a862104e330e70107544620613868618949209c23f028608a4802076827112920e4230919090107054c611264616430880c160f06b26052880440359107036096060ea652441cb03118483b4230dc34261611290f0158309070c3826032c8e121704b0341c0c320442190600cc182e001b060a0e044b82824140408a9842601242302d480a217040b808600658f808360dc048383446b0311820780ac1840a214040a090780ac184e101b00098404c102e1014080d8306c190c82b460f660c1681804e02b061020a0905d06012c19070425c23e10a1744708b06e02d1041c0b53060a09581a2305894c18213012c82417e4e02b0641c0b221840501028101b030a09780b8705f91c2032c444c838190180441205b0cb18108783c4a42c860922a617e381c12e0b2184c40e18585910173c05442088324b038110180370109835010388591026c11832460b9025a0761617c506b30b81c0b5270104173c060883249c0417010960b21c0e0607144028432c903817000c0e060702682c8612c164208cf0081c0b2220e581880d42042140809840507183c3203008a061101803b04085a18209486012c11070483814080894b8004c05910124c38c2c3208e101e02083f8590813012504ac2c2f8a12d02417c30c80894041c42c8461c83816a30985100be1985c110600c9010705025a216161904b040835c0918586510c402138e1d616a21064508cf0081c0b2218206440223028300861617080a02050102042105cb0e41c0b42204050481ec3007616141c0b516050507302828461646161803412b0b3090c00b52a0e06c2c1a82c8612c6121801644b0b0a0e605060860124402fc58141153b091290c0260506c2ec250c82b480e28381643075e0ff000b2240e040f420a2130b01c0b219840406c28081304082602484c20e05a950203c04105182707b0b221858440600ec2c26101088c0a0c01a0e58588c2cc242c870381d03e0f0b91a8180e044060101ef028220458300b0381642e020880b51f else (if i<22 then 0x6704183b9290a118901070761160c0de646403142a118803b08306c182406003e309118448188307028164664a6282098096119718a08c5026200ec88c3059427c0a1c81f012150c1bc2177038e1a322641c122340e12909192071c3841180fa838c1f8140a0606f334701323203a18720e0c1bc2116646222681c111340e08c8dc344e0288d038308c41c8461c0e382084ba09c150c4080e3c0560c304541c846186092040e0e09d072c00688d0382827098b001860a0e701583103041c583d070904e131600341c846158458018e98a10304902070623e63a230884613847015830e118115108685508c224081c70e182a120082f6c0016460b760cc18308c81c138240e0815302a118704ee116003708b0315818583cc4c4e096062b0107533918599a58948c1b1119c26c0c811e0a908c3b0e70911a598988ce4c4c40b8e1161c3510c0a102e701582384901d4cec4166252676e0048127091060a0e5818c3049020706e096062c0a0598461a88605081d420ea672206c44612819a5b868948f029c2209c619708103830b305c33b7002065c0e4200949302820ea67220bc42a103a99d89c22102070611f04f8140a840c124081c185a01f1858e101c260706179c04854344670d1231838d83091184a107061820f760c305b700b061e0538408948c4c40b760ce203446c0a103a8609c898418360c130303e70930b198485892940e10304143028688d038e123446c0a118a05c00902070617044d038344681c118a042f4114c386674628224081c70d183ac1388cecc50483888c25030b881c7001c0e3840894a0705038e1c205060fc0a0c141c292940e0889b02846080b304e30bd04530e1846413a0e6051094a071c34704f8140a830c141cb031c13a0e0a072c06119c108e00166652309870e118482e0911942c900c50829682a11830963230b2183aa2309c1380825876116060ec30ac314138005542309190220258c8c60e861c8383076446104b307d85a0e10ca5070900683962020a30b23231532223210881d82610e0020673104151d80384089010541f0708c24620aa84670e192920e082a8ca5c34618413016625240c044041c183c3824230c0f894840ea61c0b83415b0313825818a149c3a05460f882a224081c70e1a15420089020704e100b8281c704112040e09119c24508103941e384003ea0f1c0e1130911907054c615703820c50b607c81520555883848e145c22c1a048818a48102a30a3153112020e0914ac41054629682b620308c41c122320e1290919111b02841961302523851812104c0a989485904b1428507048381961303b10708140ab870a055c104612e00208e815122340e082c828c54dc2480b8e08232941514b185b0a5a0a8c260259c3ac2c80da658e0065240760a0e05149054415488ce1a246441cb10 else 0x9870e81c183c507c0e0c012ce1a207170481c184c03988261c405c040e3038370d0cb81c1d8083ac230c2c8258460c0e612c30b281c096184640e082860702c47616109809670eb0b206499484c0c1ccc2ec0060fae1103830c57090b281c2038507c0e0c17111ac11c2480e10380818144710b0b104b58588307028150618a4a503830453087008462046413c0e60510171c22c3860e665c62030c10730711c0e1130819ac0c541ee1d0383708b06112940e0a09c11702860b8e136063704a0f81c19858608398e09d0a8408a884208c81c0b10cb206082e5820c2301c283e07086962462072328100261c38412c135370d10608390ac39c2441921646a63b010a2340e3848d118c50504f814281c7014460ab240e0460a072c01c2078144a42827c0a708191340e088acc504e0288c838312e82704531026051200a11a07094848c8c1e0a083813c484681c3092521232c234108590a9c0e1423e11a08642c2ca070d08d603038e1c484682170e1847c2320e0cc4211a0847206e09422382184)))))
def f3563l11 : Packing := (1750,4,8,12,4,16,0,f3563d11)
def f3563d12 (i : Nat) : Nat := (if i<1 then 0x80d1006440101c1fc0205309865118dc000e0461c0aa17c01848322f01a200c8783e057010844421920c3d1006408c783e0e510613028bc04190291e0f814c2423510864844fc068830e0644e000700a84620040e0fa21c060543208468f2e3638c722d58a0e247882e1c4859e115833a08780d5ff97e9df6b7c91eb179d5e2376edd7f7489cdb7225c216f11b726d05ae46a75a2a678d98664d18d762158335f5979a5d217175b4166858595cf559d4ff530d45b4fa138b4ce52fd4ad925948751cb461113d435508340c4fd43e34f463b78e973914df33684d653420cc13190c122f00b792c9cad529e0a1b282c9da25f495724c4900233c8bf21e085220b07fb1ed078e1cc47001b3c6bf1a3867e18dc6061728557151c51613c0493120c4260fd43ae0e2034c0c142f50b102b409b4247082c1e5064c16d04c410b02e4088015c04700037fd754a540dff595295037fc854a540dff955195037fd854a540dff215195037fd734a540dff5d5195037fe554a540dff595195037fca54a540dffa21295037fd6346540dff54d195037fe114e540dff2a1295037fd864a540dff5d9295037fd8346540dff5cd195037fd874a540dff4c5295037fd214a540dff145295037fd614a540dff545295037fd8746540dffa21195037fd8646540dff845295037fd7646540dff5c5295037fd824a540dff589295037fd8546540dff58d295037fd534a540dff605295037fc814a540dff285295037fd524a540dff4c9295037fd825a540dff5c9695037fe2246540dff605195037fd535a540dff549695037fd3246540dff5c5695037fe225a540dff149695037fd325a540dff4c5195037fd5146540dff61d695037fd834a540dff485195037fd855a540dff60d695037fd735a540dff5c5195037fd755a540dff955695037fd515a540dff205395037fd714e540dff609195037fd814e540dff585395037fd214e540dff085395037fd514e540dff145395037fd764e540dff485695037fd5246540dff589195037fd315a540dff149195037fc8246540dff5c9195027fca2465409ff689195035fe7746540dfd845195027fda7465409ff699195027fda5465409ff295195037ee22465409ff68d195037de3346540dbf9991950377e55465409ff699395036fe664e540dfd845695027feaa4e5409ff285395027fda84a5409ff2a1295037f6114e5409ffaa9295037bd415a540d7f9dd695027fca55a540cffa21695027fda75a540ddf955695027fca25a540dfb889695036fd635a540df78cd695037bd414a540dfd845295037ee224a5409ff285295037f9304a5409ff2a1195033fe88465409ffaa9195027fda846540df78cd295035fe774a5409ff699295033fe884a5409ff69d295036fe664a540def551295027feaa5a5409ff2952950377e554a540 else (if i<2 then 0xc108d04b07d10814c24210c83e0f84f071848422f0161c300190402e0fe02c420e446084682580b07d03e02258460424078612c070792361c118e2202e096038c38289a0960fa2102864309330960294b80123038118e2ad8750b1180c8b0be0970018303c4c0463888178071848512e0f6170728840a612618183d8730b61244205432196c3542338050b4a40c8a2ad8830e60142d20032391fc1ec3a051106130c9060cb4d10616220600322851e0383c4412822102860220960f092231858423412c1fc004b309180118e25a09510c1ec3985c0a1742c9383d8840a61210a1920c88c882583f8040a84e321849f07f00612118822209602c1e262880a108c862183d8730961a118c4ba0930ec1e22185929221028602828e0f612442050c0360f6162c980b0922102860220960f61302821446190741ec2585b01a209486003240ab41ec3b80d101180c8f83d83510814c26190b2389882583f803081422302320428980a2070231428e0fe024a48840a1807e021ac19040208ec1ec403e40a0466a1742680e0f61d02a11c466209c1fc042a40a865119881f8012381583c2c846350ba12c128088ca1a2ae118324d0ba134058860f61d02a11c464f0011f42d200322b1021628307b0e60054c1184648b2a1742680e0f82b02862446620a82583e85d09a02c0c620424700a1742680a401880c8fc0034859038118bc0307c0a1301642318a5b10c1ec004740a08408d1c04465104a40c8b83f8003681423c970463f00c1e52e050c804661181f38040a046148c2ad8850ba12c392042321a0c92c401b60f61cc00970463d0ba134058860f846108e23285d09a030c307c230848e0183c59098046118d04b8009804c240231a0942f61d0298830008d03c5d2707b09814c4219446342f61302b8041281e118f0be0970081e258290463c1285f03e050460802fcf0483886608c100b0484c42f6170282140f16a88241ee0788c616108cc3a07b0b0a50482040a61a814183f8008f2a608c231f07f016210282143288c7613c03079232a6118c42c5070003823c118463c12c1fc058188c0d8108f04b07854119029880c66128c1fc042cb0e8150ca2331040030c0a62142c191307f0162102821432419119183f800461d0b0640a47c000e01508c4814c3a8583220040e0fe0302a1931088c6e0142c190f8050b0643c1ec2780046260fe0302a1904288c6e000c8118e17b0181504984f0081e119183f8002308c4025c078002f20060c0aa20c241910040617c0a825c0207846340ae03440191085f00046070231685d09a02c4307b0e81508d0644650040e0fe010281190190290463a1742680e0f81508c2144640030d0ba1340707c0a846c4223220570006408c942e84d01a1b08c191a8830b0643c1f02a8843208c5c1e14780c1c221028c018283f else 0x21707898e03070880423e0f61cc2e05309865441088b54e0fa061c60e3090846825c070788c88))
def f3563l12 : Packing := (133,3,8,11,4,14,0,f3563d12)
def f3563d13 (_i : Nat) : Nat := 0x107e020e22005160fc070002832118c85a1280c1f800141188c80bc12c070003c0a3000173294a00f005ff4a540bfe8ca817fd69502ffa72a01ff46540
def f3563l13 : Packing := (5,2,8,8,4,9,0,f3563d13)
def f3563samples : Array (Bits × Bits) := Array.mk [(0xf854605d026923a5a16008862c9d18d42fd85e54d221898f1e440284a107a02910c3e03c06c40d2642ca74f54627022c11e389d9b43b30c961ca72386ce81500aa210d1ba1a121108a6c99348979d054ac200727ac054c0970110780155ad581,0x6844620d0040231585204884208800c4270824141201090814040082a10700282003e02402c4084602ca04a440240a1091218919100a2084314a220840a00480aa210819a02120100a4409048968c05484200702a805440920100380144a9480),(0x80b20c31f72bfc4e1481d27000d43c9c5bd438a9c5e0286040f054f111d001ce10920229bde170b8d339029e2bcac4cd494fb74d1052452141a61c5b9ca1e642f40c600258428f0e5c00df481e03202a204cd465e10fe01206e82c7b03150603,0x80100c30e6089040109182600012282018c41889c5e0204002b0604000c009861080028b1c2120a0d12000120908c00d005a724402504200402010501c01c208540860025840090e1400964816012008204cd0254102a00206a0247b01150201),(0x12ce100c308544478a85796a2341d206e4242e31335abb35943abb40be28c8e05c4c115123137950052a02a9ba0d31c096458c656cc338623e92230683d8962194d5145c2aa62229438824d8e06246d0cd124850733918c390189888a426380a,0x10ca0000108540870900790a0240900460282200221a991490081a0028289000cc41010021184410080a0a28a20020c0200184206c0128621092200a03d8103080d5145c02a2022143880090804206d04d100840322918c190088800a4221002),(0x8628ebbd17000228c83c0291b729e17b3643984a392a815889878936d04e41b82b8e28807cc302855ead3105d9868885c748c2b0724ae81086518e259124cd4278a18b4aa01db88524c3a3435a0814469349110c18f0c24c2a8052bd88818268,0xc2206a1d05000020401c0090e509051303449848110100480001811490070429238c000818c508010485900541c68805c240409012420000024186258024450270208b02a00da0842041a3414a08100690490104085040042a8052bc00818028),(0xbc8ccda8781e4d8151cd3cf93a4a0a01509a42078c1bc4a783ea4aec6c7bbbd02ef85be130b1750bcd872a062d01842a34826040203d5b99ac8899721d47b82106b4f88001d04ee6f42e103eb14e0a090b95e84905a08ef7a2230402e2b14bc5,0x148981a0109a5c8210c1a4690a42220050930202c418c4a7837a48680e50b9d00c601bc02020f518c9002a002c1124282402304220255b598c9019921c51b8010494708001d04e62d42a103a30060a090b94e84905a08af280230402e2304b45),(0xd3b19712becef4647857054f8773c68492608a46265cd6cd0106c449284294958830b40e8328a4102841c46a63b66493288c7290c714876750b08cb0eb0a532e014ce7e24f9c08720240400006971f885be46b00080a21145aa7f52cf42a8012,0x92218c003e8654007015040a0c73c50280c0084821449285810a8400004080918c301008002824100801c000230200c0688c40804110046300b00cb28307502a0004c5624f9c086200004000021315805bc46800000a00145205f42ce0200002),(0x3145d24845746a93b60987114c89950ee90ab5809889781e716b0d141d9e036fea797f20c896480c8b565809c5575a81eabcad03980701be24b7e8d7401960b32336416db2f0c4c050f169960250e8b311988b92828b0074bd455ad232c2112c,0x2307720c00346283a400011d4c09950fa108a4001a095004514a0014181e2261ab3d3060c0d6480a2ac41009e4571880ea848181d90321bc24d38a860208103323340169a2b084c040f169960050c8b211800b9082890074b8455a803282012c),(0x49615339cc24bb41a658244591d020101222d0f578b5376254a121290a30cd5c4e2ad1d6dabfa9e032f022500c91031b32331a7a9ace0ca4e96243014a4009cd0d2a3210b66014de852533c420acc80ff443ad9cc5d0f4808cd621151170ac54,0x4900539a4030aa408668006591882010120251355ca1242200a1212102144d6e020a42d6d2878b6832b420400cb9813312321a4a924e408ce04943054c0001c10d2a2200b040149c8425334420acc80fa003859cc5d0e4000cd201111150ac54),(0x2108654280dbc21c532263cad6a2ab60a053058994f658a43b3dd89384745a04932387065124c385d01899e2cc083e3c1e3327061d61ca921a4965c8583262f4485320b5c04953298d1f02098424a39520b6148b236021a80528c3236c545ab4,0xc0001428049001c03a04a4012802a200013019184320c200a34088304a0580410028702010083a440180cc2080827381411260a0400ca0098085048489022c408432094004053098d0e0008842422012032140b21202188052801030c545a90)]
def f3563columns : IndexTree ColumnInfo := (IndexTree.fork 102 (IndexTree.fork 51 (IndexTree.fork 25 (IndexTree.fork 12 (IndexTree.fork 6 (IndexTree.fork 3 (IndexTree.leaf [(128,0,383,0,13),(64,0,447,0,13),(16,0,495,0,13)]) (IndexTree.leaf [(4,0,507,0,12),(32,0,479,0,12),(1,0,510,0,12)])) (IndexTree.fork 3 (IndexTree.leaf [(2,0,509,0,12),(8,0,503,0,12),(256,0,255,0,12)]) (IndexTree.leaf [(320,0,191,0,11),(17,0,494,0,11),(66,0,445,0,11)]))) (IndexTree.fork 6 (IndexTree.fork 3 (IndexTree.leaf [(144,0,367,0,11),(192,0,319,0,11),(160,0,351,0,11)]) (IndexTree.leaf [(24,0,487,0,11),(132,0,379,0,11),(80,0,431,0,11)])) (IndexTree.fork 3 (IndexTree.leaf [(0,16,486,9,10),(0,64,189,258,10),(0,128,347,36,10)]) (IndexTree.leaf [(256,64,189,2,9),(6,0,505,0,9),(288,0,223,0,9),(96,0,415,0,9)])))) (IndexTree.fork 13 (IndexTree.fork 6 (IndexTree.fork 3 (IndexTree.leaf [(264,0,247,0,9),(12,0,499,0,9),(32,128,347,4,9)]) (IndexTree.leaf [(8,16,486,1,9),(384,0,127,0,9),(136,0,375,0,9)])) (IndexTree.fork 3 (IndexTree.leaf [(4,128,347,32,9),(130,0,381,0,9),(2,64,189,256,9)]) (IndexTree.leaf [(1,16,486,8,9),(258,64,189,0,8),(260,0,251,0,8),(194,0,317,0,8)]))) (IndexTree.fork 6 (IndexTree.fork 3 (IndexTree.leaf [(280,0,231,0,8),(19,0,492,0,8),(70,0,441,0,8)]) (IndexTree.leaf [(36,128,347,0,8),(49,0,462,0,8),(152,0,359,0,8)])) (IndexTree.fork 3 (IndexTree.leaf [(164,0,347,0,8),(40,0,471,0,8),(134,0,377,0,8)]) (IndexTree.leaf [(25,0,486,0,8),(81,0,430,0,8),(0,4,369,138,8),(9,16,486,0,8)]))))) (IndexTree.fork 25 (IndexTree.fork 12 (IndexTree.fork 6 (IndexTree.fork 3 (IndexTree.leaf [(0,32,94,385,8),(322,0,189,0,8),(10,0,501,0,8)]) (IndexTree.leaf [(0,2,440,69,8),(0,256,151,104,8),(328,0,183,0,8)])) (IndexTree.fork 3 (IndexTree.leaf [(352,0,159,0,8),(448,0,63,0,8),(416,0,95,0,8)]) (IndexTree.leaf [(64,2,440,5,7),(35,0,476,0,7),(64,4,305,138,7)]))) (IndexTree.fork 6 (IndexTree.fork 3 (IndexTree.leaf [(64,32,30,385,7),(156,0,355,0,7),(128,256,23,104,7)]) (IndexTree.leaf [(177,0,334,0,7),(162,0,349,0,7),(56,0,455,0,7)])) (IndexTree.fork 3 (IndexTree.leaf [(128,2,312,69,7),(83,0,428,0,7),(98,0,413,0,7)]) (IndexTree.leaf [(74,0,437,0,7),(2,4,369,136,7),(2,1,460,48,7),(480,0,31,0,7)])))) (IndexTree.fork 13 (IndexTree.fork 6 (IndexTree.fork 3 (IndexTree.leaf [(32,256,151,72,7),(8,256,151,96,7),(32,16,454,9,7)]) (IndexTree.leaf [(32,1,460,18,7),(8,4,369,130,7),(21,0,490,0,7)])) (IndexTree.fork 3 (IndexTree.leaf [(344,0,167,0,7),(198,0,313,0,7),(4,2,440,65,7)]) (IndexTree.leaf [(296,0,215,0,7),(256,16,230,9,7),(256,8,227,20,7),(256,32,94,129,7)]))) (IndexTree.fork 6 (IndexTree.fork 3 (IndexTree.leaf [(132,2,312,65,6),(320,32,30,129,6),(130,1,332,48,6)]) (IndexTree.leaf [(288,16,198,9,6),(160,16,326,9,6),(160,1,332,18,6)])) (IndexTree.fork 3 (IndexTree.leaf [(160,256,23,72,6),(192,2,312,5,6),(192,4,305,10,6)]) (IndexTree.leaf [(384,8,99,20,6),(136,4,369,2,6),(264,16,230,1,6),(136,256,23,96,6)])))))) (IndexTree.fork 51 (IndexTree.fork 25 (IndexTree.fork 12 (IndexTree.fork 6 (IndexTree.fork 3 (IndexTree.leaf [(260,8,227,16,6),(260,64,185,2,6),(10,4,369,128,6)]) (IndexTree.leaf [(10,16,484,1,6),(66,1,396,48,6),(66,4,305,136,6)])) (IndexTree.fork 3 (IndexTree.leaf [(68,2,440,1,6),(65,32,30,384,6),(20,2,424,65,6)]) (IndexTree.leaf [(24,256,135,96,6),(20,8,227,256,6),(34,1,460,16,6)]))) (IndexTree.fork 6 (IndexTree.fork 3 (IndexTree.leaf [(24,4,353,130,6),(17,2,424,68,6),(40,16,454,1,6)]) (IndexTree.leaf [(17,32,78,384,6),(18,4,353,136,6),(72,4,305,130,6)])) (IndexTree.fork 3 (IndexTree.leaf [(96,1,396,18,6),(5,2,440,64,6),(96,256,151,8,6)]) (IndexTree.leaf [(6,16,480,9,6),(268,64,177,2,5),(276,8,227,0,5),(266,64,181,0,5)])))) (IndexTree.fork 13 (IndexTree.fork 6 (IndexTree.fork 3 (IndexTree.leaf [(273,32,78,128,5),(19,64,172,256,5),(26,4,353,128,5)]) (IndexTree.leaf [(104,256,151,0,5),(29,0,482,0,5),(448,32,30,1,5)])) (IndexTree.fork 3 (IndexTree.leaf [(21,128,330,32,5),(265,16,230,0,5),(450,0,61,0,5)]) (IndexTree.leaf [(21,2,424,64,5),(328,16,166,1,5),(386,64,61,0,5),(324,8,163,16,5)]))) (IndexTree.fork 6 (IndexTree.fork 3 (IndexTree.leaf [(296,16,198,1,5),(289,16,198,8,5),(388,64,57,2,5)]) (IndexTree.leaf [(14,16,480,1,5),(388,8,99,16,5),(51,0,460,0,5)])) (IndexTree.fork 3 (IndexTree.leaf [(88,256,135,32,5),(146,4,353,8,5),(56,256,135,64,5)]) (IndexTree.leaf [(50,1,460,0,5),(98,1,396,16,5),(44,128,339,0,5),(162,1,332,16,5)]))))) (IndexTree.fork 26 (IndexTree.fork 13 (IndexTree.fork 6 (IndexTree.fork 3 (IndexTree.leaf [(162,64,29,256,5),(74,4,305,128,5),(69,2,440,0,5)]) (IndexTree.leaf [(133,2,312,64,5),(78,0,433,0,5),(84,8,163,256,5)])) (IndexTree.fork 3 (IndexTree.leaf [(145,32,78,256,5),(81,2,424,4,5),(138,4,369,0,5)]) (IndexTree.leaf [(193,2,312,4,5),(194,4,305,8,5),(38,128,345,0,5),(147,0,364,0,5)]))) (IndexTree.fork 6 (IndexTree.fork 3 (IndexTree.leaf [(200,4,305,2,5),(224,256,23,8,5),(200,256,23,32,5)]) (IndexTree.leaf [(112,256,135,8,5),(196,2,312,1,5),(168,16,326,1,5)])) (IndexTree.fork 3 (IndexTree.leaf [(472,0,39,0,4),(102,128,281,0,4),(488,0,23,0,4)]) (IndexTree.leaf [(418,64,29,0,4),(484,0,27,0,4),(404,8,99,0,4),(85,2,424,0,4)])))) (IndexTree.fork 13 (IndexTree.fork 6 (IndexTree.fork 3 (IndexTree.leaf [(401,32,78,0,4),(87,0,424,0,4),(114,1,396,0,4)]) (IndexTree.leaf [(120,256,135,0,4),(390,64,57,0,4),(412,0,99,0,4)])) (IndexTree.fork 3 (IndexTree.leaf [(449,32,30,0,4),(178,1,332,0,4),(275,64,172,0,4)]) (IndexTree.leaf [(181,0,330,0,4),(179,0,332,0,4),(169,16,326,0,4),(15,16,480,0,4)]))) (IndexTree.fork 6 (IndexTree.fork 3 (IndexTree.leaf [(202,4,305,0,4),(31,0,480,0,4),(39,128,344,0,4)]) (IndexTree.leaf [(197,2,312,0,4),(270,64,177,0,4),(340,8,163,0,4)])) (IndexTree.fork 3 (IndexTree.leaf [(141,16,354,0,4),(356,128,27,0,4),(297,16,198,0,4)]) (IndexTree.leaf [(154,4,353,0,4),(329,16,166,0,4),(53,128,330,0,4),(232,256,23,0,4)])))))))
def f3563autos : Array (List Nat) := Array.mk [[],[118,130,81],[100,131,82,16],[118,133,100,131,50,33,16],[116,83,32],[118,116,83,130,49,32],[118,133,33,48],[82,129,48],[118,133,116,83,82,81,80],[116,50,129,80],[100,49,128],[118,100,83,130,81,128]]
def f3563levels : Nat → Packing
  | 8 => f3563l8
  | 9 => f3563l9
  | 10 => f3563l10
  | 11 => f3563l11
  | 12 => f3563l12
  | 13 => f3563l13
  | _ => emptyPacking
def f3563index : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 1 11 4 10 2 4 (hashf3563l9)
  | 10 => lookupWord 81 297 9 16 8 4 (hashf3563l10)
  | 11 => lookupWord 939 3332 12 20 12 4 (hashf3563l11)
  | 12 => lookupWord 675 2397 12 19 11 4 (hashf3563l12)
  | 13 => lookupWord 59 237 8 16 8 4 (hashf3563l13)
  | _ => fun _ => none
def f3563 : Forest := ⟨511,13,fun j => f3563samples[j]?.getD (0,0),f3563columns,f3563autos,f3563levels,f3563index⟩
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem geomf3563 : graphValid f3563 (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=6) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_8_0 : block f3563 8 0 3=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allf3563_8 : block f3563 8 0 3=true := sf3563_8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_9_0 : block f3563 9 0 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_9_36 : block f3563 9 36 17=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_9_53 : block f3563 9 53 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_9_89 : block f3563 9 89 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_9_125 : block f3563 9 125 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_9_161 : block f3563 9 161 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_9_197 : block f3563 9 197 17=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allf3563_9 : block f3563 9 0 214=true := (@block_merge f3563 9 0 197 17 (@block_merge f3563 9 0 161 36 (@block_merge f3563 9 0 125 36 (@block_merge f3563 9 0 89 36 (@block_merge f3563 9 0 53 36 (@block_merge f3563 9 0 36 17 sf3563_9_0 sf3563_9_36) sf3563_9_53) sf3563_9_89) sf3563_9_125) sf3563_9_161) sf3563_9_197)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_0 : block f3563 10 0 21=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_21 : block f3563 10 21 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_57 : block f3563 10 57 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_93 : block f3563 10 93 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_129 : block f3563 10 129 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_165 : block f3563 10 165 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_201 : block f3563 10 201 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_237 : block f3563 10 237 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_273 : block f3563 10 273 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_309 : block f3563 10 309 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_345 : block f3563 10 345 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_381 : block f3563 10 381 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_417 : block f3563 10 417 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_453 : block f3563 10 453 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_489 : block f3563 10 489 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_525 : block f3563 10 525 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_561 : block f3563 10 561 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_597 : block f3563 10 597 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_633 : block f3563 10 633 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_669 : block f3563 10 669 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_705 : block f3563 10 705 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_741 : block f3563 10 741 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_777 : block f3563 10 777 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_813 : block f3563 10 813 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_849 : block f3563 10 849 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_885 : block f3563 10 885 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_921 : block f3563 10 921 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_957 : block f3563 10 957 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_993 : block f3563 10 993 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_1029 : block f3563 10 1029 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_1065 : block f3563 10 1065 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_1101 : block f3563 10 1101 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_1137 : block f3563 10 1137 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_1173 : block f3563 10 1173 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_1209 : block f3563 10 1209 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_1245 : block f3563 10 1245 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_1281 : block f3563 10 1281 30=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_1311 : block f3563 10 1311 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_1347 : block f3563 10 1347 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_1383 : block f3563 10 1383 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_1419 : block f3563 10 1419 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_1455 : block f3563 10 1455 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_1491 : block f3563 10 1491 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_1527 : block f3563 10 1527 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_1563 : block f3563 10 1563 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_1599 : block f3563 10 1599 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_1635 : block f3563 10 1635 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_1671 : block f3563 10 1671 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_1707 : block f3563 10 1707 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_1743 : block f3563 10 1743 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_1779 : block f3563 10 1779 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_1815 : block f3563 10 1815 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_1851 : block f3563 10 1851 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_1887 : block f3563 10 1887 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_1923 : block f3563 10 1923 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_1959 : block f3563 10 1959 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_1995 : block f3563 10 1995 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_2031 : block f3563 10 2031 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_2067 : block f3563 10 2067 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_2103 : block f3563 10 2103 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_2139 : block f3563 10 2139 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_2175 : block f3563 10 2175 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_2211 : block f3563 10 2211 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_2247 : block f3563 10 2247 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_2283 : block f3563 10 2283 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_2319 : block f3563 10 2319 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_2355 : block f3563 10 2355 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_2391 : block f3563 10 2391 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_2427 : block f3563 10 2427 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_10_2463 : block f3563 10 2463 29=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allf3563_10 : block f3563 10 0 2492=true := (@block_merge f3563 10 0 2463 29 (@block_merge f3563 10 0 2427 36 (@block_merge f3563 10 0 2391 36 (@block_merge f3563 10 0 2355 36 (@block_merge f3563 10 0 2319 36 (@block_merge f3563 10 0 2283 36 (@block_merge f3563 10 0 2247 36 (@block_merge f3563 10 0 2211 36 (@block_merge f3563 10 0 2175 36 (@block_merge f3563 10 0 2139 36 (@block_merge f3563 10 0 2103 36 (@block_merge f3563 10 0 2067 36 (@block_merge f3563 10 0 2031 36 (@block_merge f3563 10 0 1995 36 (@block_merge f3563 10 0 1959 36 (@block_merge f3563 10 0 1923 36 (@block_merge f3563 10 0 1887 36 (@block_merge f3563 10 0 1851 36 (@block_merge f3563 10 0 1815 36 (@block_merge f3563 10 0 1779 36 (@block_merge f3563 10 0 1743 36 (@block_merge f3563 10 0 1707 36 (@block_merge f3563 10 0 1671 36 (@block_merge f3563 10 0 1635 36 (@block_merge f3563 10 0 1599 36 (@block_merge f3563 10 0 1563 36 (@block_merge f3563 10 0 1527 36 (@block_merge f3563 10 0 1491 36 (@block_merge f3563 10 0 1455 36 (@block_merge f3563 10 0 1419 36 (@block_merge f3563 10 0 1383 36 (@block_merge f3563 10 0 1347 36 (@block_merge f3563 10 0 1311 36 (@block_merge f3563 10 0 1281 30 (@block_merge f3563 10 0 1245 36 (@block_merge f3563 10 0 1209 36 (@block_merge f3563 10 0 1173 36 (@block_merge f3563 10 0 1137 36 (@block_merge f3563 10 0 1101 36 (@block_merge f3563 10 0 1065 36 (@block_merge f3563 10 0 1029 36 (@block_merge f3563 10 0 993 36 (@block_merge f3563 10 0 957 36 (@block_merge f3563 10 0 921 36 (@block_merge f3563 10 0 885 36 (@block_merge f3563 10 0 849 36 (@block_merge f3563 10 0 813 36 (@block_merge f3563 10 0 777 36 (@block_merge f3563 10 0 741 36 (@block_merge f3563 10 0 705 36 (@block_merge f3563 10 0 669 36 (@block_merge f3563 10 0 633 36 (@block_merge f3563 10 0 597 36 (@block_merge f3563 10 0 561 36 (@block_merge f3563 10 0 525 36 (@block_merge f3563 10 0 489 36 (@block_merge f3563 10 0 453 36 (@block_merge f3563 10 0 417 36 (@block_merge f3563 10 0 381 36 (@block_merge f3563 10 0 345 36 (@block_merge f3563 10 0 309 36 (@block_merge f3563 10 0 273 36 (@block_merge f3563 10 0 237 36 (@block_merge f3563 10 0 201 36 (@block_merge f3563 10 0 165 36 (@block_merge f3563 10 0 129 36 (@block_merge f3563 10 0 93 36 (@block_merge f3563 10 0 57 36 (@block_merge f3563 10 0 21 36 sf3563_10_0 sf3563_10_21) sf3563_10_57) sf3563_10_93) sf3563_10_129) sf3563_10_165) sf3563_10_201) sf3563_10_237) sf3563_10_273) sf3563_10_309) sf3563_10_345) sf3563_10_381) sf3563_10_417) sf3563_10_453) sf3563_10_489) sf3563_10_525) sf3563_10_561) sf3563_10_597) sf3563_10_633) sf3563_10_669) sf3563_10_705) sf3563_10_741) sf3563_10_777) sf3563_10_813) sf3563_10_849) sf3563_10_885) sf3563_10_921) sf3563_10_957) sf3563_10_993) sf3563_10_1029) sf3563_10_1065) sf3563_10_1101) sf3563_10_1137) sf3563_10_1173) sf3563_10_1209) sf3563_10_1245) sf3563_10_1281) sf3563_10_1311) sf3563_10_1347) sf3563_10_1383) sf3563_10_1419) sf3563_10_1455) sf3563_10_1491) sf3563_10_1527) sf3563_10_1563) sf3563_10_1599) sf3563_10_1635) sf3563_10_1671) sf3563_10_1707) sf3563_10_1743) sf3563_10_1779) sf3563_10_1815) sf3563_10_1851) sf3563_10_1887) sf3563_10_1923) sf3563_10_1959) sf3563_10_1995) sf3563_10_2031) sf3563_10_2067) sf3563_10_2103) sf3563_10_2139) sf3563_10_2175) sf3563_10_2211) sf3563_10_2247) sf3563_10_2283) sf3563_10_2319) sf3563_10_2355) sf3563_10_2391) sf3563_10_2427) sf3563_10_2463)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_0 : block f3563 11 0 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_6 : block f3563 11 6 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_42 : block f3563 11 42 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_78 : block f3563 11 78 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_114 : block f3563 11 114 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_150 : block f3563 11 150 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_186 : block f3563 11 186 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_222 : block f3563 11 222 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_258 : block f3563 11 258 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_294 : block f3563 11 294 19=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_313 : block f3563 11 313 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_349 : block f3563 11 349 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_385 : block f3563 11 385 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_421 : block f3563 11 421 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_457 : block f3563 11 457 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_493 : block f3563 11 493 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_529 : block f3563 11 529 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_565 : block f3563 11 565 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_601 : block f3563 11 601 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_637 : block f3563 11 637 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_673 : block f3563 11 673 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_709 : block f3563 11 709 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_745 : block f3563 11 745 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_781 : block f3563 11 781 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_817 : block f3563 11 817 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_853 : block f3563 11 853 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_889 : block f3563 11 889 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_925 : block f3563 11 925 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_961 : block f3563 11 961 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_997 : block f3563 11 997 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_1033 : block f3563 11 1033 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_1069 : block f3563 11 1069 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_1105 : block f3563 11 1105 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_1141 : block f3563 11 1141 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_1177 : block f3563 11 1177 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_1213 : block f3563 11 1213 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_1249 : block f3563 11 1249 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_1285 : block f3563 11 1285 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_1321 : block f3563 11 1321 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_1357 : block f3563 11 1357 11=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_1368 : block f3563 11 1368 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_1404 : block f3563 11 1404 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_1440 : block f3563 11 1440 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_1476 : block f3563 11 1476 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_1512 : block f3563 11 1512 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_1548 : block f3563 11 1548 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_1584 : block f3563 11 1584 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_1620 : block f3563 11 1620 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_1656 : block f3563 11 1656 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_1692 : block f3563 11 1692 36=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_11_1728 : block f3563 11 1728 22=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allf3563_11 : block f3563 11 0 1750=true := (@block_merge f3563 11 0 1728 22 (@block_merge f3563 11 0 1692 36 (@block_merge f3563 11 0 1656 36 (@block_merge f3563 11 0 1620 36 (@block_merge f3563 11 0 1584 36 (@block_merge f3563 11 0 1548 36 (@block_merge f3563 11 0 1512 36 (@block_merge f3563 11 0 1476 36 (@block_merge f3563 11 0 1440 36 (@block_merge f3563 11 0 1404 36 (@block_merge f3563 11 0 1368 36 (@block_merge f3563 11 0 1357 11 (@block_merge f3563 11 0 1321 36 (@block_merge f3563 11 0 1285 36 (@block_merge f3563 11 0 1249 36 (@block_merge f3563 11 0 1213 36 (@block_merge f3563 11 0 1177 36 (@block_merge f3563 11 0 1141 36 (@block_merge f3563 11 0 1105 36 (@block_merge f3563 11 0 1069 36 (@block_merge f3563 11 0 1033 36 (@block_merge f3563 11 0 997 36 (@block_merge f3563 11 0 961 36 (@block_merge f3563 11 0 925 36 (@block_merge f3563 11 0 889 36 (@block_merge f3563 11 0 853 36 (@block_merge f3563 11 0 817 36 (@block_merge f3563 11 0 781 36 (@block_merge f3563 11 0 745 36 (@block_merge f3563 11 0 709 36 (@block_merge f3563 11 0 673 36 (@block_merge f3563 11 0 637 36 (@block_merge f3563 11 0 601 36 (@block_merge f3563 11 0 565 36 (@block_merge f3563 11 0 529 36 (@block_merge f3563 11 0 493 36 (@block_merge f3563 11 0 457 36 (@block_merge f3563 11 0 421 36 (@block_merge f3563 11 0 385 36 (@block_merge f3563 11 0 349 36 (@block_merge f3563 11 0 313 36 (@block_merge f3563 11 0 294 19 (@block_merge f3563 11 0 258 36 (@block_merge f3563 11 0 222 36 (@block_merge f3563 11 0 186 36 (@block_merge f3563 11 0 150 36 (@block_merge f3563 11 0 114 36 (@block_merge f3563 11 0 78 36 (@block_merge f3563 11 0 42 36 (@block_merge f3563 11 0 6 36 sf3563_11_0 sf3563_11_6) sf3563_11_42) sf3563_11_78) sf3563_11_114) sf3563_11_150) sf3563_11_186) sf3563_11_222) sf3563_11_258) sf3563_11_294) sf3563_11_313) sf3563_11_349) sf3563_11_385) sf3563_11_421) sf3563_11_457) sf3563_11_493) sf3563_11_529) sf3563_11_565) sf3563_11_601) sf3563_11_637) sf3563_11_673) sf3563_11_709) sf3563_11_745) sf3563_11_781) sf3563_11_817) sf3563_11_853) sf3563_11_889) sf3563_11_925) sf3563_11_961) sf3563_11_997) sf3563_11_1033) sf3563_11_1069) sf3563_11_1105) sf3563_11_1141) sf3563_11_1177) sf3563_11_1213) sf3563_11_1249) sf3563_11_1285) sf3563_11_1321) sf3563_11_1357) sf3563_11_1368) sf3563_11_1404) sf3563_11_1440) sf3563_11_1476) sf3563_11_1512) sf3563_11_1548) sf3563_11_1584) sf3563_11_1620) sf3563_11_1656) sf3563_11_1692) sf3563_11_1728)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_12_0 : block f3563 12 0 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_12_36 : block f3563 12 36 15=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_12_51 : block f3563 12 51 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_12_87 : block f3563 12 87 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_12_123 : block f3563 12 123 10=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allf3563_12 : block f3563 12 0 133=true := (@block_merge f3563 12 0 123 10 (@block_merge f3563 12 0 87 36 (@block_merge f3563 12 0 51 36 (@block_merge f3563 12 0 36 15 sf3563_12_0 sf3563_12_36) sf3563_12_51) sf3563_12_87) sf3563_12_123)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_13_0 : block f3563 13 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sf3563_13_1 : block f3563 13 1 4=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allf3563_13 : block f3563 13 0 5=true := (@block_merge f3563 13 0 1 4 sf3563_13_0 sf3563_13_1)
theorem tablesf3563 : checkedTables f3563 13 := by
  intro k hk
  interval_cases k
  · exact (rfl : block f3563 0 0 0 = true)
  · exact (rfl : block f3563 1 0 0 = true)
  · exact (rfl : block f3563 2 0 0 = true)
  · exact (rfl : block f3563 3 0 0 = true)
  · exact (rfl : block f3563 4 0 0 = true)
  · exact (rfl : block f3563 5 0 0 = true)
  · exact (rfl : block f3563 6 0 0 = true)
  · exact (rfl : block f3563 7 0 0 = true)
  · exact allf3563_8
  · exact allf3563_9
  · exact allf3563_10
  · exact allf3563_11
  · exact allf3563_12
  · exact allf3563_13

def w3563 (b : Fin 9) : Sig :=
  bin true (bin true (inputs.getD 0 zero) (inputs.getD 4 zero)) (inputs.getD b.val zero)

def base3563 (b : Fin 9) : List Sig := inputs ++ [w3563 b]

def iso3563R (b i : Fin 9) : Row :=
  if i = 0 then Fin.ofNat 512 ((1 <<< 5) ||| (1 <<< 4))
  else if i = 4 then Fin.ofNat 512 ((1 <<< 3) ||| (1 <<< 0))
  else if i = b then
    if b = 1 then Fin.ofNat 512 ((1 <<< 6) ||| (1 <<< 4))
    else if b = 2 then Fin.ofNat 512 ((1 <<< 7) ||| (1 <<< 4))
    else Fin.ofNat 512 ((1 <<< 8) ||| (1 <<< 0))
  else Fin.ofNat 512 (1 <<< neighbor i)

def iso3563S (b i : Fin 9) : Row :=
  Fin.ofNat 512 ((iso3563R b i).val ||| (1 <<< i.val))

theorem iso3563_bool :
    (([1, 2, 3, 6] : List (Fin 9)).all fun b =>
      (List.finRange 9).all fun i =>
        (bit (iso3563R b i) graph != bit (iso3563S b i) graph) &&
        ((base3563 b).all fun w =>
          w == inputs.getD i.val zero ||
          bit (iso3563R b i) w == bit (iso3563S b i) w)) = true := by
  decide +kernel

theorem f3563_imp_inputs : Impossible graph 13 inputs.toFinset := by
  have noRun := root_index (g:=f3563) (before_sound _ valid383) geomf3563 tablesf3563 (k:=13)
    (by decide) (i:=0) (ws:=inputs) (by decide +kernel)
  have tgt : targetOf f3563 = graph := by decide +kernel
  exact tgt ▸ noRun

theorem f3563_imp_b (b : Fin 9) (hb : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 6) :
    Impossible graph 13 (base3563 b).toFinset := by
  have tgt : targetOf f3563 = graph := by decide +kernel
  rw [← tgt]
  rcases hb with rfl | rfl | rfl | rfl
  · exact root_index (g:=f3563) (before_sound _ valid383) geomf3563 tablesf3563 (k:=13)
      (by decide) (i:=3) (ws:=base3563 1) (by decide +kernel)
  · exact root_index (g:=f3563) (before_sound _ valid383) geomf3563 tablesf3563 (k:=13)
      (by decide) (i:=4) (ws:=base3563 2) (by decide +kernel)
  · exact root_index (g:=f3563) (before_sound _ valid383) geomf3563 tablesf3563 (k:=13)
      (by decide) (i:=1) (ws:=base3563 3) (by decide +kernel)
  · exact root_index (g:=f3563) (before_sound _ valid383) geomf3563 tablesf3563 (k:=13)
      (by decide) (i:=2) (ws:=base3563 6) (by decide +kernel)

theorem close3563 (b : Fin 9) (hb : b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 6)
    (C : Circuit) (fan : PEqualNP.MetaComplexity.FanInTwo C) (small : C.size ≤ 13)
    (correct : ∀ x : Fin 9 → Bool,
      C.eval (List.ofFn x ++ [false, x 0 || x 4 || x b]) = edge x) : False := by
  let w : List Sig := inputs ++ [zero, w3563 b]
  have hwbit (r : Row) : w.map (bit r) =
      List.ofFn (sample r) ++ [false, sample r 0 || sample r 4 || sample r b] := by
    simp only [w, List.map_append, List.map_cons, List.map_nil, bit_zero, sampled, w3563, bit_bin]
    rfl
  have eqGoal : (execute C.gates w).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j, hj⟩
    change bit r ((execute C.gates w).getD C.output zero) = bit r graph
    rw [← b_read, execute_bits _ _ _ (fun a ha => (fan a ha).1), edge_table]
    change C.eval (w.map (bit r)) = edge (sample r)
    rw [hwbit r]
    exact correct (sample r)
  have out := get_rep (execute C.gates w) C.output
  rw [eqGoal] at out
  obtain ⟨k, t, S, hk, run, hs⟩ :=
    extract C.gates w fan graph_proper (out.resolve_right fun hn => hn graph_proper)
  have subB : ∀ a ∈ S, a ∈ base3563 b := by
    intro a ha
    have hm := hs a ha
    simp only [w, base3563, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm ⊢
    rcases hm with hI | rfl | rfl
    · exact Or.inl hI
    · exact False.elim ((live_proper run zero ha).1 rfl)
    · exact Or.inr rfl
  have hbL : b ∈ ([1, 2, 3, 6] : List (Fin 9)) := by
    rcases hb with rfl | rfl | rfl | rfl <;> simp
  have hInS : ∀ a ∈ inputs, a ∈ S := by
    intro a ha
    rw [← input_list] at ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    have h1 := List.all_eq_true.mp iso3563_bool b hbL
    have cut := List.all_eq_true.mp h1 i (List.mem_finRange i)
    simp only [Bool.and_eq_true, bne_iff_ne, List.all_eq_true,
      Bool.or_eq_true, beq_iff_eq] at cut
    exact raw_required run (base3563 b) (inputs.getD i.val zero) subB
      (iso3563R b i) (iso3563S b i) cut.1 (fun v hv hne => (cut.2 v hv).resolve_left hne)
  have hk13 : k ≤ 13 := le_trans hk small
  by_cases hw : w3563 b ∈ S
  · have hEq : S = (base3563 b).toFinset := by
      ext a
      rw [List.mem_toFinset]
      refine ⟨subB a, fun ha => ?_⟩
      simp only [base3563, List.mem_append, List.mem_singleton] at ha
      rcases ha with hI | rfl
      · exact hInS a hI
      · exact hw
    exact f3563_imp_b b hb k t hk13 (hEq ▸ run)
  · have hEq : S = inputs.toFinset := by
      ext a
      rw [List.mem_toFinset]
      refine ⟨fun ha => ?_, hInS a⟩
      have hm := subB a ha
      simp only [base3563, List.mem_append, List.mem_singleton] at hm
      exact hm.resolve_right (fun e => hw (e ▸ ha))
    exact f3563_imp_inputs k t hk13 (hEq ▸ run)

end PEqualNP.Outside.L_meta_3563

theorem PEqualNP.Outside.L_meta_3563 : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => x1 (0 : Fin (9 : ℕ)) && x1 (1 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (2 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (3 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (4 : Fin (9 : ℕ)) || x1 (4 : Fin (9 : ℕ)) && x1 (0 : Fin (9 : ℕ)) || x1 (0 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)) || x1 (1 : Fin (9 : ℕ)) && x1 (6 : Fin (9 : ℕ)) || x1 (2 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (3 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (5 : Fin (9 : ℕ)) && x1 (7 : Fin (9 : ℕ)) || x1 (6 : Fin (9 : ℕ)) && x1 (8 : Fin (9 : ℕ)) || x1 (8 : Fin (9 : ℕ)) && x1 (5 : Fin (9 : ℕ)); ∀ (x2 : Fin (9 : ℕ)), x2 = (1 : Fin (9 : ℕ)) ∨ x2 = (2 : Fin (9 : ℕ)) ∨ x2 = (3 : Fin (9 : ℕ)) ∨ x2 = (6 : Fin (9 : ℕ)) → ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (13 : ℕ) → (∀ (x7 : Fin (9 : ℕ) → Bool), x4.eval (List.ofFn x7 ++ [Bool.false, x7 (0 : Fin (9 : ℕ)) || x7 (4 : Fin (9 : ℕ)) || x7 x2]) = x1 x7) → False := by
  intro _ b hb C fan small correct
  exact PEqualNP.Outside.L_meta_3563.close3563 b hb C fan small correct
