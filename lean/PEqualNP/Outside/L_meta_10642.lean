import PEqualNP.Defs

-- The signed circuit and cofactor framework follows L_meta_10802, L_meta_1674, L_meta_670,
-- and the checker in L_meta_1667 (Apache-2.0).
-- The verified restriction bounds and monotone witness below concern this graph.

namespace PEqualNP.Outside.L_meta_10642
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem nrm_false (a : Sig) : nrm false a = a := rfl
theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)

private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)
theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
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
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

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
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
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
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)

def supply {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a

def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
theorem Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : Available u bank a)
      (hb : Available u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : allowed u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
theorem avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R u} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)

theorem available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

theorem extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (combine op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
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
theorem comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
theorem extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply u T (comb op a b :: kept ka a (kept kb b rest)) := by
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

theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
theorem restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

theorem projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
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

theorem obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
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
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl

theorem available_rep {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (bit_table _ i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (bit_table _ i).trans (bit_one i).symm)
  · have := table_inv a
    refine Or.inl ?_
    rw [←nrm_neg,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem reach_live_sub {u} {roots : List (Wire Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,table_prime] at sub
    have rep := prime_rep d (available_rep ha) (available_rep hb)
    obtain ⟨k',S',hk,run',sub'⟩ := pull_gate (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩

def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem reach_live {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (h : Reach u (roots.map observe) p bank) (hit : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  unfold Repr at hm
  rw [nrm_id (by simpa [plainWord] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,table_observe]
  rw [e,nrm_map nR] at hs
  exact hs

theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfffffffffffffffefffeffeefefeeca0fffffffffffffffefffeffeefefeeca0fffffffffffffffefffeffeefefeeca0fffffffffffffffefffeffeefefeeca0
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
 (x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 5 && x 6)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
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

def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply bit_ext
  intro r
  simp only [bit_rename,bit_bin]

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
theorem live_rename {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (rename f T) k (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      subst none
      rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
theorem reach_up {R u} {roots : List (Wire R)} {p bank} (h : Reach false roots p bank) : Reach u roots p bank := by
  have up {bank : List (Wire R)} {a} (h : Available false bank a) : Available u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using Reach.ind with
  | start => exact Reach.start
  | two op h ha hb ih => exact Reach.two op ih (up ha) (up hb)
theorem lower_down {u roots T L} (h : Lower true roots T L) : Lower u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (reach_up hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h

def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {u roots T L} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible u T L roots.toFinset) : Lower u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv

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

theorem lower_slice {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower u other G L) : Lower u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT nT nR hh ha
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
  have supp : supply u (other.map observe) ((front.map observe).map (restrictRows r)) := by
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



def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
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
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

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

theorem cover_sound {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
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

theorem cover_required {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  simp

def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))

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

def poolSupply (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (restrictRows f (observe a))

theorem availableB_sound {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply u f bank pool)
    (check : availableB u d pool a = true) : Available u bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,masked_one dom ho⟩)
  · exact masked_eq dom he ▸ supplyB v hv
  · have h := avail_inv hu (masked_eq dom he ▸ supplyB v hv)
    rw [obs_neg] at h
    have e : inv (restrictRows f (inv (observe a))) = restrictRows f (observe a) := by
      funext r
      simp [inv,restrictRows]
    rwa [e] at h

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) := bin c.1 c.2.1 c.2.2
def allowedB (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem allowedB_ok {u d} (h : allowedB u d=true) : allowed u d := by
  simpa [allowedB,allowed] using h
def choiceOK (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  allowedB u c.1 && (availableB u d pool c.2.1 && availableB u d pool c.2.2)

theorem pay_choice {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (c : Choice) (valid : choiceOK u d pool c = true) :
    ∃ next, Reach u roots (q+1) next ∧ poolSupply u f next (choiceVal c :: pool) := by
  simp only [choiceOK,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := comb_prime (allowedB_ok valid.1) (availableB_sound dom hs valid.2.1)
    (availableB_sound dom hs valid.2.2)
  refine ⟨_,Reach.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal,obs_bin,restrict_comb,e]
    exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)

def makePool (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK u d pool c then makePool u d (choiceVal c::pool) cs else none

theorem makePool_sound {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (cs : List Choice) {result} (ok : makePool u d pool cs = some result) :
    ∃ next, Reach u roots (q+cs.length) next ∧ poolSupply u f next result := by
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

def poolCut (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB u d pool)

theorem poolCut_sound {u raw T d L} (slice : Slice u raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool u d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut u d L cap cs.length pool ws = true) :
    Impossible u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply u bank ((ws.map observe).map (restrictRows f)) := by
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
theorem freeWord_ok {u roots w} (ok : freeWord roots w = true) :
    Available u (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext bit_zero⟩)
  · exact Or.inr (Or.inl ⟨true,funext bit_one⟩)
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {u ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available u (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {u ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (nT : plainWord T=true) (nR : raw.all plainWord=true) (pG : proper G)
    (hL : Lower u base G L) : Lower u raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT nT nR pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {u ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower u base G L) :
    Slice u raw T d L := by
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
  plainWord T && raw.all plainWord && xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok.2 _ hm)

theorem essential_plain {T raw xs} (ok : checkEssential T raw xs = true) :
    plainWord T=true ∧ raw.all plainWord=true := by
  simp only [checkEssential,Bool.and_eq_true] at ok
  exact ok.1
theorem lower_count {u raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := reach_live properT (essential_plain ok).1 (essential_plain ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := live_size run
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {u ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower u base G L) :
    Lower u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 properG _ eq supp _ (essential_ok ok.1.2) _ L low
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
def typeWord (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)
def varsX (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [typeWord (m/512-1)]
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
 (x 0 &&& x 2) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6)
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

def supportPairs (t : Nat) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let r := if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := m ^^^ (m &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def rawMask (m : Nat) (c : ColumnInfo) : Nat := m % 512+512*(c.1/512)
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let raw := rawMask m c
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (varsX free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (varsX free) (varsX q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {u} {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice u (varsX (rawMask m c)) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := fixRows z o
  let raw := rawMask m (z,o,q,s,L)
  let free := colFree raw (z % 512) o
  let G := movedWord ms (chartGoal m)
  let xs := supportPairs (z/512+80) s
  change (((properB G && checkMap ms (varsX raw) (chartGoal m) (varsX free) G) &&
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

def carryOK (old rep : Nat) (swaps : List Nat) :=
  (properB (graphGoal old) && plainWord (graphGoal old) && (varsX old).all plainWord) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (varsX old) (graphGoal old) (varsX rep) (graphGoal rep)
theorem carry_of {u old rep L swaps} (ok : carryOK old rep swaps = true)
    (h : Lower u (varsX rep) (graphGoal rep) L) : Lower u (varsX old) (graphGoal old) L := by
  simp only [carryOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound {u} (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower u (varsX q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he


def essOK (m hints : Nat) : Bool :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs && (xs.map Prod.fst == vars m)
theorem plain_low {u} {m hints cap : Nat} (ok : essOK m hints = true)
    (a : Impossible u (graphGoal m) cap (vars m).toFinset) : Lower u (vars m) (graphGoal m) (cap+1) := by
  simp only [essOK,Bool.and_eq_true,beq_iff_eq] at ok
  apply lower_impossible (proper_of _ ok.1.1) (essential_plain ok.1.2).1 (essential_plain ok.1.2).2 _ a
  intro v hv
  apply essential_ok ok.1.2 v
  rw [ok.2]
  exact List.mem_toFinset.mpr hv



def target (x : Fin 7 → Bool) : Bool := decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or, [0, 3]⟩, ⟨.and, [5, 7]⟩, ⟨.or, [4, 6]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [0, 10]⟩, ⟨.and, [9, 11]⟩, ⟨.or, [1, 6]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [3, 14]⟩, ⟨.and, [13, 15]⟩, ⟨.and, [2, 0]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [18, 19]⟩], 20⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 7 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 14 := rfl

theorem noNotReuse {gates : List Gate} (fit : ∀ g ∈ gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (h : ∀ g ∈ gates, g.op ≠ GateOp.not) :
    ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨ops,arity⟩ := fit g hg
  refine ⟨?_,arity⟩
  rcases ops with a | b | c
  · exact Or.inl a
  · exact Or.inr b
  · exact (h g hg c).elim


def sevenInputs : List Sig := vars 127
def sampleSeven (r : Row) (i : Fin 7) : Bool := bit r (sevenInputs.getD i.val zero)
theorem sevenList : List.ofFn (fun i : Fin 7 => sevenInputs.getD i.val zero) = sevenInputs := rfl
theorem sevenSampled (r : Row) : List.ofFn (sampleSeven r) = sevenInputs.map (bit r) := by
  rw [←sevenList,List.map_ofFn]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem sevenTable : ∀ r : Row, bit r graph = target (sampleSeven r) := by decide +kernel

theorem sevenEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates sevenInputs).getD i zero) =
      (C.wires (List.ofFn (sampleSeven r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sevenSampled]
  rfl

def lowRow (i : Fin 7) : Row := Fin.ofNat 512 (1 <<< ([2, 3, 0, 1, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 7) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([2, 3, 0, 1, 0, 0, 0] : List Nat).getD i.val 0))

set_option maxHeartbeats 1000000 in
theorem allSevenRequired :
    (∀ i : Fin 7, bit (lowRow i) graph ≠ bit (highRow i) graph) ∧
    (∀ i j : Fin 7, i ≠ j →
      bit (lowRow i) (sevenInputs.getD j.val zero) =
      bit (highRow i) (sevenInputs.getD j.val zero)) := by decide +kernel

theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k sevenInputs.toFinset := by
  have goalEq : (execute C.gates sevenInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (sevenEval C legal C.output r).trans ((computes (sampleSeven r)).trans (sevenTable r).symm)
  have out := get_rep (u:=true) (execute C.gates sevenInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates sevenInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : sevenInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ sevenInputs) : ∃ i : Fin 7, sevenInputs.getD i.val zero = a := by
    rw [←sevenList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = sevenInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run sevenInputs (sevenInputs.getD i.val zero) sub (lowRow i) (highRow i)
        (allSevenRequired.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply allSevenRequired.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k,hk,eq ▸ run⟩

theorem replaceShort
    (lower : Impossible true graph 12 sevenInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 7 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 7 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 14 ≤ gates.length
  · exact ⟨smallCircuit.gates,smallCircuit.output,witnessMonotone,(by simpa only [witnessSize] using big),witnessCorrect⟩
  by_cases mono : ∀ g ∈ gates, g.op ≠ GateOp.not
  · exact ⟨gates,o,noNotReuse fit mono,Nat.le_refl _,correct⟩
  push Not at mono
  obtain ⟨g,hg,hop⟩ := mono
  have lt : gates.countP (fun q => !isNot q) < gates.length := by
    rcases Nat.lt_or_ge (gates.countP (fun q => !isNot q)) gates.length with h | h
    · exact h
    · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
      simp [isNot,hop] at eq
  have legal : PEqualNP.MetaComplexity.FanInTwo (Circuit.mk gates o) := by
    intro g hg
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using fit g hg
  obtain ⟨k,hk,run⟩ := physicalSigned (Circuit.mk gates o) legal correct
  change k ≤ gates.countP (fun q => !isNot q) at hk
  exact (lower k (by omega) run).elim


def paidSliceChoices (d : Sig) (pool : List Sig) : List Choice → List Choice
  | [] => []
  | c :: hist =>
    if availableB true d pool (choiceVal c) then paidSliceChoices d pool hist
    else c :: paidSliceChoices d (choiceVal c :: pool) hist

def zeroSliceOK (m s : Nat) : Bool :=
  let fixed := m - s
  let moves := fixRows fixed 0
  properB (graphGoal s) && (movedWord moves (subcube fixed 0) == one &&
    checkMap moves (vars m) (graphGoal m) (vars s) (graphGoal s))

theorem zeroSlice_sound {m s l} (ok : zeroSliceOK m s = true)
    (prior : Lower true (vars s) (graphGoal s) l) :
    Slice true (vars m) (graphGoal m) (subcube (m - s) 0) l := by
  simp only [zeroSliceOK, Bool.and_eq_true, beq_iff_eq] at ok
  exact slice_correct ok.2.2 ok.2.1 (proper_of _ ok.1) prior

def mixedPairs (support hints : Nat) : List (Sig × Row × Row) :=
  (selected support).map fun (i, w) =>
    let j := (hints >>> (4 * i)) &&& 15
    let r : Nat := if j < 9 then 1 <<< j else 0
    (w, Fin.ofNat 512 r, Fin.ofNat 512 (r ||| (1 <<< i)))

def mixedColumnOK (m z o q support hints L base : Nat) : Bool :=
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (graphGoal m)
  let xs := mixedPairs support hints
  let count := (xs.map Prod.fst).toFinset.card
  properB G && checkMap ms (vars m) (graphGoal m) (vars free) G &&
    (movedWord ms (subcube z o) == one) &&
    (if q = 0 then checkEssential G (vars free) xs && decide (L ≤ count - 1)
     else properB (graphGoal q) &&
       checkLift (fixRows (colFree free q 0) 0) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ base + count))

theorem mixedColumn_sound {m z o q support hints L base : Nat}
    (prior : Lower true (vars q) (graphGoal q) base)
    (ok : mixedColumnOK m z o q support hints L base = true) :
    Slice true (vars m) (graphGoal m) (subcube z o) L := by
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (graphGoal m)
  let xs := mixedPairs support hints
  change (((properB G && checkMap ms (vars m) (graphGoal m) (vars free) G) &&
    (movedWord ms (subcube z o) == one)) && _) = true at ok
  simp only [Bool.and_eq_true, beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have h := ok.2
  by_cases hq : q = 0
  · simp only [hq, if_true, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2.trans (lower_count (proper_of _ ok.1.1.1) xs h.1 p bank hr ha)
  · simp only [hq, if_false, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2.trans (lift_ok h.1.2 (proper_of _ ok.1.1.1) (proper_of _ h.1.1) prior p bank hr ha)

theorem mixedBaseZero : Lower true (vars 0) (graphGoal 0) 0 :=
  fun _ _ _ _ => Nat.zero_le _

abbrev BoundPool := Sig × Nat × Nat × List Sig
def BoundPool.domain (c : BoundPool) : Sig := c.1
def BoundPool.bound (c : BoundPool) : Nat := c.2.1
def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1
def BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2

def ValidPool (u : Bool) (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach u (roots.map observe) q ws → Available u ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach u (roots.map observe) c.paid bank ∧ poolSupply u f bank c.wires ∧ True

theorem build_valid {u raw T d lb} (h : Slice u raw T d lb) (cs : List Choice) {ws}
    (build : makePool u d raw cs = some ws) : ValidPool u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩

theorem valid_exclude {u raw T c} (valid : ValidPool u raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB u c.domain c.wires a = true)
    (buy : if paid then choiceOK u c.domain c.wires choice = true
       else availableB u c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible u T k (choiceVal choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach u (roots.map observe) n out)
      (zs : poolSupply u f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply u out ((ws.map observe).map (restrictRows f)) := by
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
    · have point : ∀ v ∈ c.wires, Available u out (restrictRows f (observe v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact availableB_sound dom point (known _ hm)

def scalarPoolCut (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB u c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB u c.domain c.wires)) && (!extra || choiceOK u c.domain c.wires op)

theorem scalarPoolCut_sound {u raw T c} (valid : ValidPool u raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut u c k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB u c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB u c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (u : Bool) (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {u raw T d L cs c} (slice : Slice u raw T d L)
    (h : materialize u raw cs d L = some c) : ValidPool u raw T c := by
  unfold materialize at h
  cases he : makePool u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he


abbrev Bits := BitVec 1024
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 1024 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 1024 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 1024 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 1024 → Row) (x : Decor) := x.2 = pairSig r s x.1
def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)

theorem ofRows_bin {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    ofRows r (bin d a b) = bv d (ofRows r a) (ofRows r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  simp only [faithful,dbin,pairSig,ofRows_bin,hx,hy]

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
    decodeBank k (bits >>> 10) (ws++[dbin ((bits >>> 8) &&& 3) a b])
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
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 1024) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 1024) (j : Fin 9) :
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
 (x 0 &&& x 2) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 5 &&& x 6)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 1024) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 1024) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide)]
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
  let n := v.toNat % 2305843009213693921
  (n*(n+971)) % 2305843009213693921
def keySet (xs : List Sig) := xs.foldl (fun v x => v+keyWord x) 0

def closeChild (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut u p k rest op)

theorem closeChild_sound {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild u pools links k rest op = true) :
    Impossible u T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Bool
def preCov (u : Bool) (ws : List Decor) : CovPair := (coverage (!u) ws,u)
def restCov (v : Cov) (a b : Bits) (ka kb : Bool) :=
  if ka then (if kb then v.1 else takeOne v b) else if kb then takeOne v a else takeTwo v a b

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) :
    (delTwo ws a b ka kb).Sublist ws := (delOne_sub _ _ _).trans (delOne_sub _ _ _)
theorem len_keep (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    (delTwo ws a b ka kb).length =
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]

def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 1024 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChild cov.2 pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem evalMove_sound {u raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov u ws,pools,links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := dbin op a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h (pair_sep pairs)
  let d := !u
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (coverage d rest).1 = restCov (coverage d ws) (column d a.2) (column d b.2) ka kb :=
    cover_two d a b ha hb ne ka kb
  have hf := faithful_bin op (faith _ ha) (faith _ hb)
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1024) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1024 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact closeChild_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h

def testPair (ctx : NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem opsOf_mem {u d} (h : allowed u d) : d ∈ opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [opsOf]
  · cases u <;> simp [opsOf]
  · simp [opsOf]
  · simp [opsOf]
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair ctx a b))
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (opsOf_mem hd)
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx d a b (dbin d a b) ka kb = true := by
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
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,mem_delone wn,mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto

theorem node_sound {u raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov u ws,pools,links) ws = true) :
    Impossible u T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Decor) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : testPair (cap,ws.length,ws,preCov u ws,pools,links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←binary_front nd aa bb ne']
    exact evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (testPair_at test ka kb)
  rcases all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)



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
theorem rotate_excluded {u T n} {ws : List Sig} (hi : Impossible u T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible u T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k hk h
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
  exact hi k hk run


def compactNext (path : Nat) (ws : List Decor) (hist : List Choice) :
    List Decor × List Choice :=
  let a := ws.getD (path &&& 31) defaultDecor
  let b := ws.getD ((path >>> 5) &&& 31) defaultDecor
  let d := (path >>> 10) &&& 3
  (ws ++ [dbin d a b], hist ++ [(d, a.1, b.1)])

def walkCompact : Nat → Nat → List Decor → List Choice → List Decor × List Choice
  | 0, _, ws, hist => (ws, hist)
  | depth + 1, path, ws, hist =>
    let next := compactNext path ws hist
    walkCompact depth (path >>> 12) next.1 next.2

theorem walkCompact_faithful (depth path : Nat) (ws : List Decor) (hist : List Choice)
    {r s} (base : ∀ v ∈ ws, faithful r s v) :
    ∀ v ∈ (walkCompact depth path ws hist).1, faithful r s v := by
  induction depth generalizing path ws hist with
  | zero => exact base
  | succ depth ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hb | hz
    · exact base _ hb
    · obtain rfl := List.mem_singleton.mp hz
      exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def rowWires : List Decor → Nat → List Decor
  | [], _ => []
  | v :: bank, mask =>
    if mask.testBit 0 then v :: rowWires bank (mask >>> 1)
    else rowWires bank (mask >>> 1)

theorem rowWires_faithful (bank : List Decor) (mask : Nat) {r s}
    (base : ∀ v ∈ bank, faithful r s v) :
    ∀ v ∈ rowWires bank mask, faithful r s v := by
  induction bank generalizing mask with
  | nil => simp [rowWires]
  | cons v bank ih =>
    have hv := List.forall_mem_cons.mp base
    unfold rowWires
    split
    · exact List.forall_mem_cons.mpr ⟨hv.1, ih _ hv.2⟩
    · exact ih _ hv.2

def compactPool (m : Nat) (domain : Sig × Nat) (hist : List Choice) : Option BoundPool :=
  materialize true (vars m) (paidSliceChoices domain.1 (vars m) hist) domain.1 domain.2

theorem compactPool_sound {m : Nat} {domain : Sig × Nat} {hist : List Choice} {pool : BoundPool}
    (slice : Slice true (vars m) (graphGoal m) domain.1 domain.2)
    (ok : compactPool m domain hist = some pool) :
    ValidPool true (vars m) (graphGoal m) pool :=
  materialize_sound slice ok

abbrev CompactGrid := Nat × Nat × (Nat → Bits) × (Nat → Bits)
def CompactGrid.mask (g : CompactGrid) := g.1
def CompactGrid.top (g : CompactGrid) := g.2.1
def CompactGrid.pos (g : CompactGrid) := g.2.2.1
def CompactGrid.neg (g : CompactGrid) := g.2.2.2

abbrev CompactTable := (Nat → Nat) × (Nat → Nat → Nat) × (Nat → Nat → Nat) ×
  (Nat → Nat → List Nat) × (Nat → Nat → List Nat)
def CompactTable.count (t : CompactTable) := t.1
def CompactTable.path (t : CompactTable) := t.2.1
def CompactTable.live (t : CompactTable) := t.2.2.1
def CompactTable.picks (t : CompactTable) := t.2.2.2.1
def CompactTable.bucket (t : CompactTable) := t.2.2.2.2

def chartAt (g : CompactGrid) (t : CompactTable) (k i : Nat) :=
  let bank := walkCompact (g.top-k) (t.path k i) (rawDecor g.mask g.pos g.neg) []
  (rowWires bank.1 (t.live k i), bank.2)

def wordsAt (g : CompactGrid) (t : CompactTable) (k i : Nat) :=
  (chartAt g t k i).1.map Prod.fst

abbrev Domains := Array (Sig × Nat)
abbrev Perms := Array (List Nat)

def selectedHistory : List Choice → Nat → List Choice
  | [], _ => []
  | a :: rest, mask =>
    if mask.testBit 0 then a :: selectedHistory rest (mask >>> 1)
    else selectedHistory rest (mask >>> 1)

def poolList (m : Nat) (dom : Domains) (h : List Choice) (picks : List Nat) :=
  picks.filterMap (fun j => dom[j % dom.size]?.bind (fun d => compactPool m d (selectedHistory h (j / dom.size))))

theorem poolList_valid {m dom h picks} (valid : ∀ d ∈ dom, Slice true (vars m) (graphGoal m) d.1 d.2) :
    ∀ pool ∈ poolList m dom h picks, ValidPool true (vars m) (graphGoal m) pool := by
  intro pool hp
  obtain ⟨j,_,hj⟩ := List.mem_filterMap.mp hp
  cases e : dom[j % dom.size]? with
  | none => simp [e] at hj
  | some d =>
    simp only [e,Option.bind_some] at hj
    exact compactPool_sound (valid d (Array.mem_of_getElem? e)) hj

def applySwaps : List Nat → List Sig → List Sig
  | [], xs => xs
  | p::ps,xs => xs.map (movedWord ((p::ps).map swapRows))

theorem applySwaps_valid {T k xs} {p : List Nat}
    (ok : autoOK T (p.map swapRows).reverse = true)
    (ih : Impossible true T k (List.toFinset xs)) :
    Impossible true T k (applySwaps p xs).toFinset := by
  cases p with
  | nil => exact ih
  | cons a p =>
    have := rotate_excluded ih (((a::p).map swapRows).reverse) ok
    simpa only [List.reverse_reverse,applySwaps] using this

def linkedCandidates (g : CompactGrid) (t : CompactTable) (perms : Perms) (k tag : Nat) :=
  (t.bucket k tag).filterMap (fun code =>
    let name := code / perms.size
    if name < t.count k then
      perms[code % perms.size]?.map (fun swaps => applySwaps swaps (wordsAt g t k name))
    else none)

theorem linkedCandidates_valid {g t perms k}
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (prev : ∀ i < t.count k, Impossible true (graphGoal g.mask) k (wordsAt g t k i).toFinset) :
    ∀ tag xs, xs ∈ linkedCandidates g t perms k tag → Impossible true (graphGoal g.mask) k xs.toFinset := by
  intro tag xs hx
  obtain ⟨code,_,he⟩ := List.mem_filterMap.mp hx
  dsimp only at he
  split at he
  next small =>
    cases eq : perms[code % perms.size]? with
    | none => simp [eq] at he
    | some p =>
      simp only [eq,Option.map_some,Option.some.injEq] at he
      subst xs
      exact applySwaps_valid (autos p (Array.mem_of_getElem? eq)) (prev _ small)
  next => contradiction

theorem cachedLiveSize {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega


abbrev NodePool := BoundPool × List Sig × List Sig × Nat

def cacheOnePool (u : Bool) (front : List Sig) (p : BoundPool) : NodePool :=
  (p, front.filter (fun a => !(availableB u p.domain p.wires a)),
    p.wires.map (masked p.domain), front.countP (isMaskedConstant p.domain))

def maskedAvailable (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) : Bool :=
  let m := masked d a
  m == zero || m == d || pool.any (fun v => v==m) ||
    (u && (let c := masked d (neg a); pool.any (fun v => v==c)))

def cachedPoolCut (u : Bool) (a : NodePool) (k : Nat) (rest : List Sig) (op : Choice) : Bool :=
  let (c,missing,bank,maxCon) := a
  if c.bound + maxCon + 1 ≤ k + c.paid then false else
  let z := choiceVal op
  let con := c.bound + (z::rest).countP (isMaskedConstant c.domain)
  if con ≤ k+c.paid then false else
  let extra := !(maskedAvailable u c.domain bank z)
  (decide (k+c.paid+extra.toNat < con) &&
   missing.all (fun w => !(rest.contains w))) &&
    (!extra || (allowedB u op.1 && (!missing.contains op.2.1 && !missing.contains op.2.2)))

theorem cachedCut_ok {u p k rest op front}
    (sub : ∀ w ∈ rest, w ∈ front) (ha : op.2.1 ∈ front) (hb : op.2.2 ∈ front)
    (ok : cachedPoolCut u (cacheOnePool u front p) k rest op = true) :
    scalarPoolCut u p k rest op = true := by
  let miss := front.filter (fun a => !(availableB u p.domain p.wires a))
  let extra := !(availableB u p.domain p.wires (choiceVal op))
  have know (w) (hm : w ∈ front) (hn : w ∉ miss) : availableB u p.domain p.wires w = true := by
    by_contra h
    apply hn
    apply List.mem_filter.mpr
    exact ⟨hm, by simpa using h⟩
  dsimp only [cachedPoolCut, cacheOnePool] at ok
  split at ok
  · contradiction
  split at ok
  · contradiction
  change ((_ && miss.all (fun w => !(rest.contains w))) &&
    (!extra || (allowedB u op.1 && (!miss.contains op.2.1 && !miss.contains op.2.2)))) = true at ok
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true] at ok
  change ((_ && rest.all (availableB u p.domain p.wires)) && (!extra || choiceOK u p.domain p.wires op)) = true
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true]
  refine ⟨⟨ok.1.1, ?_⟩, ?_⟩
  · intro w hw
    apply know w (sub w hw)
    intro no
    have contra := ok.1.2 w no
    simpa [hw] using contra
  · rcases ok.2 with h | ⟨allowed, ah, bh⟩
    · exact Or.inl h
    · right
      simp only [choiceOK, Bool.and_eq_true]
      exact ⟨allowed, know _ ha (by simpa using ah), know _ hb (by simpa using bh)⟩

def cachedClose (u : Bool) (pools : List NodePool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) : Bool :=
  pools.any (fun p => cachedPoolCut u p k rest op) ||
    (let ws := choiceVal op::rest; (links (keySet ws)).any (sameWords ws))

theorem cachedClose_sound {u raw T} {pools : List BoundPool} {links k rest op front}
    (pValid : ∀ p ∈ pools, ValidPool u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible u T k (List.toFinset xs))
    (nd : (choiceVal op::rest).Nodup)
    (sub : ∀ w ∈ rest, w ∈ front) (ha : op.2.1 ∈ front) (hb : op.2.2 ∈ front)
    (ok : cachedClose u (pools.map (cacheOnePool u front)) links k rest op = true) :
    Impossible u T k (choiceVal op::rest).toFinset := by
  simp only [cachedClose,Bool.or_eq_true,List.any_eq_true] at ok
  rcases ok with ⟨c,hc,cut⟩ | ⟨w,hw,eq⟩
  · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hc
    exact scalarPoolCut_sound (pValid p hp) nd (cachedCut_ok sub ha hb cut)
  · rw [sameWords_sound eq]
    exact lValid _ _ hw

abbrev cached_NodeContext := Nat × Nat × List Decor × CovPair × List NodePool × (Nat → List (List Sig))
def cached_evalMove (c : cached_NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 1024 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      cachedClose cov.2 pools links (cap-1) rest (movedChoice op a b)

def cached_moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (dbin op a b).1 :: (delTwo ws a b ka kb).map Prod.fst
theorem cached_evalMove_sound {u raw T r s ws} {pools : List BoundPool} {links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : cached_evalMove (cap,ws.length,ws,preCov u ws,pools.map (cacheOnePool u (ws.map Prod.fst)),links) op a b (dbin op a b) ka kb = true) :
    Impossible u T (cap-1) (cached_moveFront ws op a b ka kb).toFinset := by
  let z := dbin op a b
  let rest := delTwo ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := cachedLiveSize h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold cached_evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h (pair_sep pairs)
  let d := !u
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (coverage d rest).1 = restCov (coverage d ws) (column d a.2) (column d b.2) ka kb :=
    cover_two d a b ha hb ne ka kb
  have hf := faithful_bin op (faith _ ha) (faith _ hb)
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1024) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 1024 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact cachedClose_sound (op:=movedChoice op a b) (rest:=rest.map Prod.fst) pv lv ndc (sub.map _).subset (List.mem_map_of_mem ha) (List.mem_map_of_mem hb) test k hk h

def cached_testPair (ctx : cached_NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := cached_evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def cached_opsOf (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]
theorem cached_opsOf_mem {u d} (h : allowed u d) : d ∈ cached_opsOf u := by
  rcases allowed_four h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [cached_opsOf]
  · cases u <;> simp [cached_opsOf]
  · simp [cached_opsOf]
  · simp [cached_opsOf]
def cached_testRow (ctx : cached_NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (cached_opsOf ctx.2.2.2.1.2).all (cached_testPair ctx a b))
def cached_testAll (ctx : cached_NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => cached_testRow ctx a bs && cached_testAll ctx bs

theorem cached_all_binary {ctx ws} (h : cached_testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → cached_testPair ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → cached_testPair ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [cached_testAll,Bool.and_eq_true,cached_testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (cached_opsOf_mem hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (cached_opsOf_mem hd)
      · exact ih h.2 haTail hbTail

theorem cached_testPair_at {ctx a b d} (h : cached_testPair ctx a b d = true) (ka kb : Bool) :
    cached_evalMove ctx d a b (dbin d a b) ka kb = true := by
  simp only [cached_testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem cached_keep_mem {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ kept k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [kept]
theorem cached_mem_delone {v : List Decor} (nd : v.Nodup) (a w : Decor) (k : Bool) :
    w ∈ delOne v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [delOne,nd.mem_erase_iff,and_comm]

theorem cached_unique_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
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

theorem cached_kept_value {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  simp only [delTwo,List.mem_map,cached_mem_delone wn,cached_mem_delone dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (cached_unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (cached_unique_value nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem cached_binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (cached_moveFront ws d a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [cached_moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    cached_kept_value nd ha hb,cached_keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,dbin]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem cached_childTwo_swap {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : allowed u d) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    cached_keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_flip hd a b]
  tauto

theorem cached_node_sound {u raw T r s ws} {pools : List BoundPool} {links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible u T (cap-1) (List.toFinset xs))
    (checks : cached_testAll (cap,ws.length,ws,preCov u ws,pools.map (cacheOnePool u (ws.map Prod.fst)),links) ws = true) :
    Impossible u T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : Decor) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : cached_testPair (cap,ws.length,ws,preCov u ws,pools.map (cacheOnePool u (ws.map Prod.fst)),links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←cached_binary_front nd aa bb ne']
    exact cached_evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (cached_testPair_at test ka kb)
  rcases cached_all_binary checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [cached_childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)



def compactNode (g : CompactGrid) (t : CompactTable) (dom : Domains) (perms : Perms) (k i : Nat) : Bool :=
  let state := chartAt g t k i
  let ws := state.1
  let words := ws.map Prod.fst
  let pools := poolList g.mask dom state.2 (t.picks k i)
  let links := linkedCandidates g t perms (k-1)
  decide words.Nodup && (!(words.contains (graphGoal g.mask)) &&
    (if k=0 then true else cached_testAll (k,ws.length,ws,preCov true ws,pools.map (cacheOnePool true words),links) ws))

theorem compactNode_sound {g t dom perms k i}
    (pairs : properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg))
    (valid : ∀ d ∈ dom, Slice true (vars g.mask) (graphGoal g.mask) d.1 d.2)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (prev : 0 < k → ∀ j < t.count (k-1),
      Impossible true (graphGoal g.mask) (k-1) (wordsAt g t (k-1) j).toFinset)
    (check : compactNode g t dom perms k i = true) :
    Impossible true (graphGoal g.mask) k (wordsAt g t k i).toFinset := by
  simp only [compactNode,Bool.and_eq_true,decide_eq_true_eq] at check
  have out : graphGoal g.mask ∉ wordsAt g t k i := by simpa [wordsAt] using check.2.1
  by_cases hz : k=0
  · subst k
    intro n hn run
    obtain rfl : n = 0 := by omega
    exact out (List.mem_toFinset.mp (run.1.symm ▸ Finset.mem_singleton_self _))
  · have f : ∀ v ∈ (chartAt g t k i).1, faithful (asRow g.pos) (asRow g.neg) v :=
      rowWires_faithful _ (t.live k i) (walkCompact_faithful (g.top-k) (t.path k i)
        (rawDecor g.mask g.pos g.neg) [] (raw_faithful g.mask g.pos g.neg))
    apply cached_node_sound pairs f check.1 out (poolList_valid valid) (linkedCandidates_valid autos (prev (by omega)))
    simpa only [hz,ite_false] using check.2.2


def chartBlock (test : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => test (start+n) && chartBlock test start n

theorem chartBlock_at {test start n} (ok : chartBlock test start n = true) (i)
    (a : start ≤ i) (b : i < start+n) : test i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [chartBlock,Bool.and_eq_true] at ok
    by_cases h : i=start+n
    · simpa only [h] using ok.1
    · exact ih ok.2 (by omega)

theorem chartBlock_join {test start a b}
    (left : chartBlock test start a = true) (right : chartBlock test (start+a) b = true) :
    chartBlock test start (a+b) = true := by
  induction b with
  | zero => simpa using left
  | succ b ih =>
    simp only [chartBlock,Bool.and_eq_true] at right
    simp only [Nat.add_succ,chartBlock,Bool.and_eq_true]
    constructor
    · change test (start + (a+b)) = true
      rw [← Nat.add_assoc]
      exact right.1
    · exact ih right.2

theorem compactAll {g t dom perms}
    (pairs : properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg))
    (valid : ∀ d ∈ dom, Slice true (vars g.mask) (graphGoal g.mask) d.1 d.2)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (blocks : ∀ k ≤ g.top, chartBlock (compactNode g t dom perms k) 0 (t.count k) = true) :
    ∀ k ≤ g.top, ∀ i < t.count k, Impossible true (graphGoal g.mask) k (wordsAt g t k i).toFinset := by
  intro k
  induction k with
  | zero =>
    intro h i hi
    exact compactNode_sound pairs valid autos (by omega) (chartBlock_at (blocks 0 h) i (by omega) (by simpa using hi))
  | succ k ih =>
    intro h i hi
    exact compactNode_sound pairs valid autos (fun _ => ih (by omega)) (chartBlock_at (blocks _ h) i (by omega) (by simpa using hi))

theorem compactPairs {g : CompactGrid}
    (yes : liftGoal g.mask g.pos = BitVec.allOnes 1024) (no : liftGoal g.mask g.neg = 0) :
    properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg) := by
  intro i
  constructor
  · rw [bit_liftGoal,yes,BitVec.getLsbD_allOnes]
    exact decide_eq_true i.isLt
  · rw [bit_liftGoal,no]
    simp

abbrev SliceSpec := Nat × Nat × Nat × Nat × Nat × Nat × Nat

def specDomain (s : SliceSpec) : Sig × Nat :=
  (subcube s.1 s.2.1, s.2.2.2.2.2.1)

def certifiesSlice (m : Nat) (earlier : List (Nat × Nat)) (s : SliceSpec) : Bool :=
  let (z,o,q,support,hints,L,base) := s
  ((q == 0 && base == 0) || earlier.contains (q,base)) &&
    ((z == m-q && o == 0 && L == base && zeroSliceOK m q) ||
      mixedColumnOK m z o q support hints L base)

theorem certifiesSlice_sound {m earlier s}
    (prior : ∀ e ∈ earlier, Lower true (vars e.1) (graphGoal e.1) e.2)
    (ok : certifiesSlice m earlier s = true) :
    Slice true (vars m) (graphGoal m) (specDomain s).1 (specDomain s).2 := by
  obtain ⟨z,o,q,support,hints,L,base⟩ := s
  simp only [certifiesSlice,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,
    List.contains_eq_mem,decide_eq_true_eq] at ok
  have lower : Lower true (vars q) (graphGoal q) base := by
    rcases ok.1 with ⟨rfl,rfl⟩ | he
    · exact mixedBaseZero
    · exact prior (q,base) he
  rcases ok.2 with ⟨⟨⟨rfl,rfl⟩,rfl⟩,h⟩ | h
  · exact zeroSlice_sound h lower
  · exact mixedColumn_sound lower h

theorem compactDomains_valid {m earlier specs ds}
    (prior : ∀ e ∈ earlier, Lower true (vars e.1) (graphGoal e.1) e.2)
    (ok : List.all specs (certifiesSlice m earlier) = true)
    (matchDs : (specs.map specDomain).toArray = ds) :
    ∀ d ∈ ds, Slice true (vars m) (graphGoal m) d.1 d.2 := by
  subst ds
  intro d hd
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp (List.mem_toArray.mp hd)
  exact certifiesSlice_sound prior (List.all_eq_true.mp ok _ hs)

theorem compactAutos_valid {T : Sig} {ps : Perms}
    (ok : ps.toList.all (fun p => autoOK T (p.map swapRows).reverse) = true) :
    ∀ p ∈ ps, autoOK T (p.map swapRows).reverse = true := by
  intro p hp
  exact List.all_eq_true.mp ok _ (Array.mem_toList_iff.mpr hp)

theorem compactRoot {g t dom perms}
    (pairs : properPairs (graphGoal g.mask) (asRow g.pos) (asRow g.neg))
    (valid : ∀ d ∈ dom, Slice true (vars g.mask) (graphGoal g.mask) d.1 d.2)
    (autos : ∀ p ∈ perms, autoOK (graphGoal g.mask) (p.map swapRows).reverse = true)
    (blocks : ∀ k ≤ g.top, chartBlock (compactNode g t dom perms k) 0 (t.count k) = true)
    (existsRoot : 0 < t.count g.top)
    (root : wordsAt g t g.top 0 = vars g.mask) :
    Impossible true (graphGoal g.mask) g.top (vars g.mask).toFinset := by
  rw [←root]
  exact compactAll pairs valid autos blocks _ (Nat.le_refl _) 0 existsRoot
def readCompactBits (table : Nat → Nat) (start width : Nat) : Nat :=
  let i := start / 4096
  let j := start % 4096
  let low := table i >>> j
  let result := if j + width ≤ 4096 then low else low ||| (table (i+1) <<< (4096-j))
  result &&& ((1 <<< width)-1)

def compactIDsFromBits (bits width : Nat) : Nat → List Nat
  | 0 => []
  | n+1 => (bits &&& ((1 <<< width)-1)) :: compactIDsFromBits (bits >>> width) width n

def samplesP21 : Nat → Bits
  | 0 => ~~~(0x4046 : Bits)
  | 2 => 0xeef6
  | 4 => ~~~(0x20b0 : Bits)
  | _ => 0

def samplesQ21 : Nat → Bits
  | 0 => ~~~(0xbbde : Bits)
  | 2 => 0x1214
  | 4 => 0x280a
  | _ => 0

def compactPerms21 : Array (List Nat) := ([[], [66], [32], [32, 66], [64, 66], [64]] : List (List Nat)).toArray

def compactDomains21 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray

def compactWords21 : Nat → Nat
  | 0 => 0x7
  | _ => 0

def compactCount21 (k : Nat) : Nat := match k with
  | 3 => 1
  | _ => 0

def compactPath21 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => 0
  | _ => 0

def compactLive21 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => readCompactBits compactWords21 (0 + 3*i) 3
  | _ => 0

def compactPoolIDs21 (k : Nat) (i : Nat) : List Nat := match k with
  | 3 => let v := readCompactBits compactWords21 (3 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords21 (3 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket21 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP85 : Nat → Bits
  | 0 => 0x6ff5337f9aab64
  | 2 => ~~~(0x20201f6882356c : Bits)
  | 4 => 0x7bee8f38fe559c
  | 6 => ~~~(0x807a3101acb94 : Bits)
  | _ => 0

def samplesQ85 : Nat → Bits
  | 0 => 0x104208a4100844
  | 2 => 0x22001602480282
  | 4 => 0x4806050840510
  | 6 => ~~~(0x76fe7ef6dfffd6 : Bits)
  | _ => 0

def compactPerms85 : Array (List Nat) := ([[], [100], [66], [66, 100], [98, 100], [98], [32], [32, 100], [32, 66], [32, 66, 100], [32, 98, 100], [32, 98], [64, 66], [64, 66, 100], [64], [64, 100], [64, 98], [64, 98, 100], [96, 98, 100], [96, 98], [96, 100], [96], [96, 66, 100], [96, 66]] : List (List Nat)).toArray

def compactDomains85 : Array (Sig × Nat) := ([(subcube 1 0, 4), (subcube 4 0, 4), (subcube 16 0, 4), (subcube 64 0, 4)] : List (Sig × Nat)).toArray

def compactWords85 : Nat → Nat
  | 0 => 0x849a7d7b0bffc0ff03fc0ff03a2e225a114d6b1e8eff03fc0c2027c47211728d2090050090051a27f80af65a8d49d2f7acef7db51ffc07f80ff0174b7fc0480eff008a936d5af40ff00bc5290bcbb86c3ca0593574e3b8469fe03fc01e27634dda7ffc07f80c45e011b495263a5e820682e002372293fd7de805904904803fe0147f2cffc028dff03f5efcf895ff03070fd0060e4f
  | _ => 0

def compactCount85 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 1
  | 4 => 3
  | 3 => 2
  | _ => 0

def compactPath85 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords85 (18 + 12*i) 12
  | 4 => let v := readCompactBits compactWords85 (193 + 12*i) 12
    (readCompactBits compactWords85 (181 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 3 => let v := readCompactBits compactWords85 (938 + 13*i) 13
    (readCompactBits compactWords85 (890 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | _ => 0

def compactLive85 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords85 (0 + 4*i) 4
  | 5 => readCompactBits compactWords85 (30 + 5*i) 5
  | 4 => readCompactBits compactWords85 (229 + 6*i) 6
  | 3 => readCompactBits compactWords85 (964 + 7*i) 7
  | _ => 0

def compactPoolIDs85 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords85 (12 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords85 (4 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 5 => let v := readCompactBits compactWords85 (43 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords85 (35 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 4 => let v := readCompactBits compactWords85 (253 + 4*i) 4
    let n := v >>> 2
    let bits := readCompactBits compactWords85 (247 + 2*(v &&& 3)) (2*n)
    compactIDsFromBits bits 2 n
  | 3 => let v := readCompactBits compactWords85 (982 + 4*i) 4
    let n := v >>> 2
    let bits := readCompactBits compactWords85 (978 + 2*(v &&& 3)) (2*n)
    compactIDsFromBits bits 2 n
  | _ => []

def compactBucket85 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords85 (49 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 10)
    let v := readCompactBits compactWords85 (51 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 4 => let d := readCompactBits compactWords85 (265 + 4*(i % 10)) 4
    let off := ((i/10 + d) % 39)
    let v := readCompactBits compactWords85 (305 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 3 => let d := readCompactBits compactWords85 (990 + 2*(i % 3)) 2
    let off := ((i/3 + d) % 14)
    let v := readCompactBits compactWords85 (996 + 14*off) 14
    if v >>> 6 == (i/104729)%251 then [v &&& 63] else []
  | _ => []

def samplesP93 : Nat → Bits
  | 0 => 0x5efffd970ef729fde7bdd9d59e893467bedeeb8e4b185c2b6d88
  | 2 => ~~~(0x2408811a651e80020aa90d613035f7222cfa58013952da555bc : Bits)
  | 3 => 0x7a3ebaeba74c01cffdfa567237420111ffa7b513f88500ffc014
  | 4 => 0x777fcff0fe98e5f27ffebdaed9344e61f3f935ec363227659668
  | 6 => ~~~(0x100000a20e8e240045105d209c3c246590b0310e6a3a566bae48 : Bits)
  | _ => 0

def samplesQ93 : Nat → Bits
  | 0 => 0x210804409108950404240a240190090928424108411440286108
  | 2 => 0x2440911240160a1110331000200125085200845080192128a02
  | 3 => 0x5d12d444813ffca4083bb6ca7a14485ff0520122135f6ffc010
  | 4 => 0x8a1200a00620a4022508048a402a00252901080142024c51440
  | 6 => ~~~(0x6ffdffdffd7bffef77f7fffffff3ffdffff779df7fffffffff5a : Bits)
  | _ => 0

def compactPerms93 : Array (List Nat) := ([[], [66], [32], [32, 66], [64, 66], [64]] : List (List Nat)).toArray

def compactDomains93 : Array (Sig × Nat) := ([(subcube 8 0, 7)] : List (Sig × Nat)).toArray

def compactWords93 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount93 (k : Nat) : Nat := match k with
  | 7 => 1
  | _ => 0

def compactPath93 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | _ => 0

def compactLive93 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits compactWords93 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs93 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits compactWords93 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords93 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket93 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP87 : Nat → Bits
  | 0 => 0xdeffe6c59ed2fefced6d735301c71f6fcfd0f0c491ad5b08
  | 1 => 0xecfa7d99e740e7f7f6baa5989a002ff676636e192a3f8094
  | 2 => ~~~(0x42024040f67302042625259adb6b341ad65140d92be1abbc : Bits)
  | 4 => 0xfbffdd767e35df8fff678cf4f92b8cd9f41fd9c06e622c7c
  | 6 => ~~~(0x80005950e140480c16a8055b98788656402f8c4fe2e5c5c : Bits)
  | _ => 0

def samplesQ87 : Nat → Bits
  | 0 => 0x21210902410d80408d119084802066680a00c04888a94208
  | 1 => 0x1341ca24103fe180237193a241148fc21420284b9ebf0084
  | 2 => 0x4210c040a432502242600328104a09842108140316161402
  | 4 => 0x480000900c0040c10000000068010114012010000002850
  | 6 => ~~~(0xf7f7ff6ff5fff5eefffffffed7feffff7f3afdffffff7ede : Bits)
  | _ => 0

def compactPerms87 : Array (List Nat) := ([[], [100], [32], [32, 100]] : List (List Nat)).toArray

def compactDomains87 : Array (Sig × Nat) := ([(subcube 2 0, 7)] : List (Sig × Nat)).toArray

def compactWords87 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount87 (k : Nat) : Nat := match k with
  | 7 => 1
  | _ => 0

def compactPath87 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | _ => 0

def compactLive87 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits compactWords87 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs87 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits compactWords87 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords87 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket87 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP23 : Nat → Bits
  | 0 => 0x5eff31efd7bc8ee2
  | 1 => ~~~(0x130c29f084bea0fa : Bits)
  | 2 => 0x79fde8dfadcea7d8
  | 4 => ~~~(0x80100c3010c86c0 : Bits)
  | _ => 0

def samplesQ23 : Nat → Bits
  | 0 => 0x21284c0606144c82
  | 1 => ~~~(0x6cb1bea3eeab00fe : Bits)
  | 2 => 0x61602292080b350
  | 4 => 0x8800080c800002c
  | _ => 0

def compactPerms23 : Array (List Nat) := ([[], [32]] : List (List Nat)).toArray

def compactDomains23 : Array (Sig × Nat) := ([(subcube 2 0, 4)] : List (Sig × Nat)).toArray

def compactWords23 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def compactCount23 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath23 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive23 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords23 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs23 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords23 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords23 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket23 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP79 : Nat → Bits
  | 0 => 0xed7f5fefd30781fffba7a52b3bdd9c2816ffbbce59650455a4fd560
  | 1 => 0xf5bfeafd667c06fa9fffd9cddce622c12ff6f47371ba58825eb6a90
  | 2 => ~~~(0x214008cc5252e7029001d185b24537e5a0241b5261a3daa2f425afc : Bits)
  | 3 => 0xbe7efddc3dd360f7f4ff57b7b62343c48fed4f30efe6c2225d6b28c
  | 6 => ~~~(0x400400d2505000000a6052b1ca20ac816c0e420596644575cfa780 : Bits)
  | _ => 0

def samplesQ79 : Nat → Bits
  | 0 => 0x1290a42020c85ca1880490740a32820464bc82c000630a4464e5440
  | 1 => 0xa428582090271c8048112e3023c11180e325011500009d07696210
  | 2 => 0x214901c81210a35042122283d08d20a08b432028041441b91b1a102
  | 3 => 0x41a12060c0248e360060a014d883840311cd0c00a903422d0969088
  | 6 => ~~~(0xfbfbfffafbfeffffcef7fffffffff7bffffffef9fd77ffffffff7da : Bits)
  | _ => 0

def compactPerms79 : Array (List Nat) := ([[], [49], [16, 50], [16, 33, 50], [32], [32, 49], [48, 49, 50], [48, 33]] : List (List Nat)).toArray

def compactDomains79 : Array (Sig × Nat) := ([(subcube 1 0, 5), (subcube 2 0, 5), (subcube 4 0, 5), (subcube 8 0, 5), (subcube 5 0, 4), (subcube 10 0, 4)] : List (Sig × Nat)).toArray

def compactWords79 : Nat → Nat
  | 0 => 0xd61c3a1f08531ff01cd3fc1fe0c19fcc9a92fcdd26623bfc0296580912e12e1005d8672bc45fe05137a9771fac72eaff83fc0358037088a04bcdcdb987661098494880294300814880288c44a5a33fae6e689c7592d9a2e458cb705a1186bc1dfe008c93bcf530900a5307d4b97d5e0c7bdc51cb0bf93fe00499b8233b6be673fc07f80a195fe00a677f80ff01d90ffc07f803257fe032267f80e59178effc07f80ff0166dbfc07f80ff01e1350cb3b022729fe03fc03b07a58e2697fc03ac5f449fe020c668a6ea412e5d820f421df7aac7c2f288ea0a066b800020002366850a50983064900c90a04c8c806ffbb77ff7ebf7efdf9285ca27289ca1728040432908a412900a4804404401ff07f80a85fe06d27f83fc0e6fff07f80febfe0445c31ffc05f3cfbff83fc1fe02836327fc1771a669ab3551008321403124098325401ffffe0110110068ae11f
  | _ => 0

def compactCount79 (k : Nat) : Nat := match k with
  | 7 => 1
  | 6 => 3
  | 5 => 10
  | 4 => 3
  | _ => 0

def compactPath79 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | 6 => readCompactBits compactWords79 (26 + 12*i) 12
  | 5 => let v := readCompactBits compactWords79 (552 + 14*i) 14
    (readCompactBits compactWords79 (516 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 4 => let v := readCompactBits compactWords79 (2137 + 14*i) 14
    (readCompactBits compactWords79 (2065 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | _ => 0

def compactLive79 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits compactWords79 (0 + 5*i) 5
  | 6 => readCompactBits compactWords79 (62 + 6*i) 6
  | 5 => readCompactBits compactWords79 (692 + 7*i) 7
  | 4 => readCompactBits compactWords79 (2179 + 8*i) 8
  | _ => 0

def compactPoolIDs79 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits compactWords79 (20 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords79 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 6 => let v := readCompactBits compactWords79 (156 + 9*i) 9
    let n := v >>> 5
    let bits := readCompactBits compactWords79 (80 + 4*(v &&& 31)) (4*n)
    compactIDsFromBits bits 4 n
  | 5 => let v := readCompactBits compactWords79 (810 + 7*i) 7
    let n := v >>> 4
    let bits := readCompactBits compactWords79 (762 + 4*(v &&& 15)) (4*n)
    compactIDsFromBits bits 4 n
  | 4 => let v := readCompactBits compactWords79 (2203 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords79 (2203 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket79 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let d := readCompactBits compactWords79 (183 + 2*(i % 4)) 2
    let off := ((i/4 + d) % 25)
    let v := readCompactBits compactWords79 (191 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 5 => let d := readCompactBits compactWords79 (880 + 5*(i % 18)) 5
    let off := ((i/18 + d) % 73)
    let v := readCompactBits compactWords79 (970 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 4 => let d := readCompactBits compactWords79 (2209 + 5*(i % 8)) 5
    let off := ((i/8 + d) % 31)
    let v := readCompactBits compactWords79 (2249 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | _ => []

def samplesP83 : Nat → Bits
  | 0 => 0xbbf9856f7b86ce2
  | 1 => ~~~(0x2430a74a09871ea : Bits)
  | 4 => ~~~(0x80888c43066670 : Bits)
  | 6 => 0xeffeaafebc67778
  | _ => 0

def samplesQ83 : Nat → Bits
  | 0 => 0x445242a822aac42
  | 1 => ~~~(0xdb6d5bdb3f553ee : Bits)
  | 4 => 0x90008510800184
  | 6 => 0x120011021400228
  | _ => 0

def compactPerms83 : Array (List Nat) := ([[], [100], [16], [16, 100]] : List (List Nat)).toArray

def compactDomains83 : Array (Sig × Nat) := ([(subcube 1 0, 4)] : List (Sig × Nat)).toArray

def compactWords83 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def compactCount83 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath83 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive83 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords83 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs83 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords83 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords83 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket83 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP91 : Nat → Bits
  | 0 => 0x5ebffc91a6fc277bbdfce6cd9542424efdfae9e52688165bc584
  | 1 => ~~~(0x1040c00942cda801054086ce165a774885b38cc0478c579555b6 : Bits)
  | 3 => 0x7c7edbff634487bfe7eb5b6636091925fd139eabf90528bf4a12
  | 4 => ~~~(0x4801812a156e02a008f4a45204b99b83052b129ab553a8aebd2 : Bits)
  | 6 => 0x77ffff4ad9dfefef5fd78edf6a5ab59bb6f7b558c3545384f1f2
  | _ => 0

def samplesQ91 : Nat → Bits
  | 0 => 0x214445604901de08211529ac0e210516b88220842a9c8a5ac104
  | 1 => ~~~(0x6fafbef6ff7b736ff77efe7bf3afaffdd7bbafddff6f75b777be : Bits)
  | 3 => 0x3891440940b7324840caa38a2822285d41108091a2d44b74210
  | 4 => 0x4a110022052210112288210a008802947080240402144a51408
  | 6 => 0x8020014022000424040000000040840002085108000000020a2
  | _ => 0

def compactPerms91 : Array (List Nat) := ([[], [48, 65]] : List (List Nat)).toArray

def compactDomains91 : Array (Sig × Nat) := ([(subcube 1 0, 5), (subcube 2 0, 5), (subcube 8 0, 5), (subcube 16 0, 5)] : List (Sig × Nat)).toArray

def compactWords91 : Nat → Nat
  | 0 => 0x41c9f
  | _ => 0

def compactCount91 (k : Nat) : Nat := match k with
  | 6 => 1
  | _ => 0

def compactPath91 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | _ => 0

def compactLive91 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords91 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs91 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords91 (13 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords91 (5 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | _ => []

def compactBucket91 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP27 : Nat → Bits
  | 0 => 0xbbf8f1bfbb341bd2
  | 1 => ~~~(0x20006184a0341252 : Bits)
  | 3 => 0xf3f7627cf7c167e8
  | 4 => ~~~(0x10300240134161a8 : Bits)
  | _ => 0

def samplesQ27 : Nat → Bits
  | 0 => 0x448b26282954ab82
  | 1 => ~~~(0xddfddef6ebef56de : Bits)
  | 3 => 0xd2988b082cd16c8
  | 4 => 0x1060805640091454
  | _ => 0

def compactPerms27 : Array (List Nat) := ([[], [48, 65]] : List (List Nat)).toArray

def compactDomains27 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray

def compactWords27 : Nat → Nat
  | 0 => 0xf
  | _ => 0

def compactCount27 (k : Nat) : Nat := match k with
  | 3 => 1
  | _ => 0

def compactPath27 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => 0
  | _ => 0

def compactLive27 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => readCompactBits compactWords27 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs27 (k : Nat) (i : Nat) : List Nat := match k with
  | 3 => let v := readCompactBits compactWords27 (4 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords27 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket27 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP31 : Nat → Bits
  | 0 => 0x7daff4ff85feae1f7df77fdd780a5af02f2feeeb94dbd5538a285fd2c2
  | 1 => ~~~(0x21400052059b1f800920271e309012ea2fa9040d0691995bcb2c925aea : Bits)
  | 2 => 0x7adfdfde2bb9799fdb7fe72e73b3756a0abbfd776a33b909cb2586eea8
  | 3 => 0x774feb77d6cb501fafebf9569ddda3a0505dff9c2fc4dfa01053bb5d10
  | 4 => ~~~(0x1080400482e8680000434944590b61205a60e8322842d5a19a730fc790 : Bits)
  | _ => 0

def samplesQ31 : Nat → Bits
  | 0 => 0x25213104a0011c50191040d04362183400ca0e00098149286105f0202
  | 1 => ~~~(0x5eb7fdecfaf6faf9cfb7f97be31fdf7fdd7d2f2fefb9dfef726db35afe : Bits)
  | 2 => 0x5212403900286328024429038c8c400910359064801012009a700eca0
  | 3 => 0x8b4358420142af90c028839211edd2c043d2f002400caae122db35810
  | 4 => 0x1080808400e048084200382001001820085006098320000c1008a0104c
  | _ => 0

def compactPerms31 : Array (List Nat) := ([[], [32]] : List (List Nat)).toArray

def compactDomains31 : Array (Sig × Nat) := ([(subcube 8 0, 5), (subcube 0 8, 5), (subcube 1 0, 4), (subcube 4 0, 4), (subcube 2 8, 4)] : List (Sig × Nat)).toArray

def compactWords31 : Nat → Nat
  | 0 => 0xe47fbfc3fff05bca2404bd4153fc369bcbfe3fc5ebff1fe192503dffffc02202201401a9f
  | _ => 0

def compactCount31 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 3
  | 4 => 1
  | _ => 0

def compactPath31 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords31 (23 + 12*i) 12
  | 4 => let v := readCompactBits compactWords31 (224 + 12*i) 12
    (readCompactBits compactWords31 (212 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def compactLive31 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords31 (0 + 5*i) 5
  | 5 => readCompactBits compactWords31 (59 + 6*i) 6
  | 4 => readCompactBits compactWords31 (236 + 7*i) 7
  | _ => 0

def compactPoolIDs31 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords31 (17 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords31 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits compactWords31 (85 + 5*i) 5
    let n := v >>> 3
    let bits := readCompactBits compactWords31 (77 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 4 => let v := readCompactBits compactWords31 (243 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords31 (243 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket31 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords31 (100 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 10)
    let v := readCompactBits compactWords31 (102 + 11*off) 11
    if v >>> 3 == (i/104729)%251 then [v &&& 7] else []
  | 4 => let d := readCompactBits compactWords31 (245 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 5)
    let v := readCompactBits compactWords31 (247 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | _ => []

def samplesP95 : Nat → Bits
  | 0 => 0xbedffff556c3eff698bb0ff7cfeff6bb9f7d75f14bae88c39c43761f1ecc8884eff7d3fadf657e3729dfca732caf841535b239e90c088651837733dfd66fc5e55a23724899062121a82cdd54cc10
  | 1 => 0xdf5fd6fffafe739c1ed41ffeffb67fdde3c7873e73f7c78ce0739863ec200258f6fefe3ce787cfdfcee3f183d0f0f9c7c3c3ce01a23318020cbbbd7b678c7878343dc38f2258464641b69a691224
  | 2 => ~~~(0x29010a0106961128e9bc000412421131145461860c7a64686699e5746b7eade44004418e2248c02234bf52360d5cd16ba82ed31ab7bfb6bad2026525165d76cba2d829c3f5d4e4eef3c315b5efc : Bits)
  | 3 => 0xfaaffbebade9f52fa101cffffb7fe94b74cb5a5beddfb6164ed827c4c1c12000ddfffc4bfafeaa69ffda95156753db365a4463720042380828efdff6d8d08f1ea8649efca6010a0243dd75b11048
  | 4 => 0xf7bffdbff53fea5bc78eefa9fffdff37dbb6eeadfe4d776a132cdf1b0312c93aff8dfdb5a47ebdbe373f2c6aaacc67aaaa2ba59573b0c161c0f46ee07d737246ab9ba1345134145c3478238261b4
  | 6 => ~~~(0x100000012482e20c918400208a004009c28200214b0fd78a5852770b894889388084982084462a3d0c928853aeeaf3a7436323c176b29c51caf719e046da68562833f36cb336377771fcdfa5f134 : Bits)
  | _ => 0

def samplesQ95 : Nat → Bits
  | 0 => 0x41210812812410086544aa10080c1040b0a234081c610100420480c0210317326c54100241002810090549001d9044a330500718120201081462321e462004a008030048290d2060482cd0540810
  | 1 => 0x20a4098204010821a109ec200182084010b41058b80c2822108021100091b106626c86048480020a004029465402c78010501d040900a090401b2819648410480420c1000108e15449268a610204
  | 2 => 0x29081a4104840028a8b450422010585021440d0a08e044004090c024014e84c832aa900101101248080264e600a8b440301182480201221201d8921a8182011010028028200c99511830ea0a002
  | 3 => 0x5520234c21200505ef613c8806001b5a642e4a205e04001812050200a2e4ef99d937049204400412400c628a999186fa32742786008404602e4d7e698008a04004412242a350aa932d975901040
  | 4 => 0x848020048800580103010814410403004408022010000142842000494280081108140200022140012328020800110088026404000450400098044c0114240022210001040300208225021024120
  | 6 => ~~~(0xefffbfffdfff5dfbfffffffdefff5dffffffffffffff6d77ffeffdf6ffbfffffffffff6ff5f73f7fbff7fffffffffffffffffffffb6ff7ff7ffffffffffefeff2f77fb7efffffffffffffff7fb76 : Bits)
  | _ => 0

def compactPerms95 : Array (List Nat) := ([[], [32]] : List (List Nat)).toArray

def compactDomains95 : Array (Sig × Nat) := ([(subcube 2 0, 8), (subcube 8 0, 8), (subcube 16 0, 8), (subcube 1 0, 7), (subcube 4 0, 7), (subcube 64 0, 7), (subcube 5 0, 5), (subcube 65 0, 4), (subcube 68 0, 4)] : List (Sig × Nat)).toArray

def compactWords95 : Nat → Nat
  | 0 => 0xbaa013bf0a5a0030907b488a80a804823a4e533fe1e69a4ace5fe05e7fe1fe1fe16ad2a3b6153a264039768e0c95eb4412f017d93a7698ed410c33ef85713b630827d811ceefdfffff5fd1179854c2202931501500bfca7ffcff289ff3222d7602140db37a95e52106ba394fffd01500b0b1a23f
  | _ => 0

def compactCount95 (k : Nat) : Nat := match k with
  | 9 => 1
  | 8 => 2
  | 7 => 5
  | 6 => 1
  | _ => 0

def compactPath95 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => 0
  | 8 => readCompactBits compactWords95 (30 + 12*i) 12
  | 7 => let v := readCompactBits compactWords95 (270 + 13*i) 13
    (readCompactBits compactWords95 (246 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 6 => let v := readCompactBits compactWords95 (833 + 12*i) 12
    (readCompactBits compactWords95 (809 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | _ => 0

def compactLive95 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => readCompactBits compactWords95 (0 + 6*i) 6
  | 8 => readCompactBits compactWords95 (54 + 7*i) 7
  | 7 => readCompactBits compactWords95 (335 + 8*i) 8
  | 6 => readCompactBits compactWords95 (845 + 9*i) 9
  | _ => 0

def compactPoolIDs95 (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let v := readCompactBits compactWords95 (24 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords95 (6 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 8 => let v := readCompactBits compactWords95 (156 + 9*i) 9
    let n := v >>> 5
    let bits := readCompactBits compactWords95 (68 + 4*(v &&& 31)) (4*n)
    compactIDsFromBits bits 4 n
  | 7 => let v := readCompactBits compactWords95 (600 + 10*i) 10
    let n := v >>> 6
    let bits := readCompactBits compactWords95 (375 + 5*(v &&& 63)) (5*n)
    compactIDsFromBits bits 5 n
  | 6 => let v := readCompactBits compactWords95 (910 + 8*i) 8
    let n := v >>> 4
    let bits := readCompactBits compactWords95 (854 + 7*(v &&& 15)) (7*n)
    compactIDsFromBits bits 7 n
  | _ => []

def compactBucket95 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let d := readCompactBits compactWords95 (174 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 7)
    let v := readCompactBits compactWords95 (176 + 10*off) 10
    if v >>> 2 == (i/104729)%251 then [v &&& 3] else []
  | 7 => let d := readCompactBits compactWords95 (650 + 1*(i % 3)) 1
    let off := ((i/3 + d) % 13)
    let v := readCompactBits compactWords95 (653 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | 6 => let d := readCompactBits compactWords95 (918 + 1*(i % 1)) 1
    let off := ((i/1 + d) % 1)
    let v := readCompactBits compactWords95 (919 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | _ => []

def samplesP115 : Nat → Bits
  | 0 => 0xddfbfad617e3be7f7bcba3ac16147b4e3ef61e281ba79644
  | 1 => ~~~(0xa0062511e3424012dca033d975c6044557253299bcabe56 : Bits)
  | 4 => ~~~(0x410091d42178180c0a27227c58fac10932938d9f1785cfe2 : Bits)
  | 5 => 0xeefef75db9137fbdefa75270507a37317533fd99161e8d82
  | 6 => 0xfbfdfdf16e7ffdcfbc7e2f5d89c8edcdd3dbc10781c96a72
  | _ => 0

def samplesQ115 : Nat → Bits
  | 0 => 0x2284210848152008588c1412012099402214103222a50604
  | 1 => ~~~(0xf5ebdfeeebeaeeddf773ebd6fbf7e6d777fef7cddd5afede : Bits)
  | 4 => 0x41208840216a42410212814048506682444021488c1a3008
  | 5 => 0x110888a2022a08902212814482812610112085488c1a8082
  | 6 => 0x4400204808084048000000030060005008a400000004850
  | _ => 0

def compactPerms115 : Array (List Nat) := ([[], [84], [16], [16, 84], [64, 81], [64, 81, 84], [80, 65, 84], [80, 65]] : List (List Nat)).toArray

def compactDomains115 : Array (Sig × Nat) := ([(subcube 1 0, 5)] : List (Sig × Nat)).toArray

def compactWords115 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount115 (k : Nat) : Nat := match k with
  | 5 => 1
  | _ => 0

def compactPath115 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => 0
  | _ => 0

def compactLive115 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => readCompactBits compactWords115 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs115 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let v := readCompactBits compactWords115 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords115 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket115 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP55 : Nat → Bits
  | 0 => 0xbf7fff90eb7bcfff7df17fcf634587ec2fe63b9af0f8a66c386ef42
  | 1 => ~~~(0x11809809c123ec024111734a3224c7ef0441128e92cca76f3107fca : Bits)
  | 2 => 0xf8ffd9ffc2e627fecf7ff0beba2640e337df36e5be4407630775688
  | 4 => ~~~(0x841010222f20c180060c88da34294f8838223e028727e68b66ce70 : Bits)
  | 5 => 0xddbfbf6b35b30bdbf3fccb49b7fa94189ff9c3ee0bf27808b78f870
  | _ => 0

def samplesQ55 : Nat → Bits
  | 0 => 0x408410251080221009818110208060100a060300c080c2102848442
  | 1 => ~~~(0xee6fe3d77efd54fbdfb65aefdc4f7dbdd4eb7fafdbdf2dad9387fde : Bits)
  | 2 => 0x7024e002409d988841034440b780c04a5982484180018635635280
  | 4 => 0x86100820230046302024802c00010881060180903052004818210c
  | 5 => 0x22494280484454c050265846c848012154e94022005528259387810
  | _ => 0

def compactPerms55 : Array (List Nat) := ([[], [81, 64]] : List (List Nat)).toArray

def compactDomains55 : Array (Sig × Nat) := ([(subcube 2 0, 5)] : List (Sig × Nat)).toArray

def compactWords55 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount55 (k : Nat) : Nat := match k with
  | 5 => 1
  | _ => 0

def compactPath55 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => 0
  | _ => 0

def compactLive55 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => readCompactBits compactWords55 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs55 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let v := readCompactBits compactWords55 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords55 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket55 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP119 : Nat → Bits
  | 0 => 0x6f7ffffcf5c2f6f95d8fdfe7fcffee9b77fb4fb133c06ec184e7d1e6816cfbff52ffa3ebfac3f495be6493b197532d147006f03580f38be5c9ac9e6ba57c031c24211a87a0c7ab3210
  | 1 => 0x7b6ffb3fbb9c3f9e482fee7ff7bf7ae5b8f5b5e60f0f13c7eb80fa404487fef4fb3cbf37cf8dcbe24ca96d1f2a74f03a087101080f26ef7fd78751c8c2b1e4d8cbc424183bd4900d24
  | 2 => ~~~(0x2030013030401b5bed840820041838e1305a412309c543e6ce35d47eedbc020011992c2388c510b88f45b8970a74f91f5ef7d9cf8f9284211e8e746ca5a8ce1eefc6679fe20db5bf7c : Bits)
  | 4 => 0x7ebff7f71afbcf7ae5d3f9ff1fff17fbf33ef2af84738d7e46175c3e1417ff8b5d877cf742ff3fec3746f42168acd5d08bb0c841e23f94babe2d60743ee43e256000e4e866194540f4
  | 5 => 0x779fedfb6777397da643fffbeff8fdf63ccec95bc88ce3b61d78a4a02907e7f8a7fb7c4bbd7ff31b8b518adecc78ca2d0446008e0c5f7fb92652bdb4050bdf1a8d8203151e2f60ac08
  | 6 => ~~~(0x2002000039224384448004300a0469230a48081860aafd705c2f8a61540e08042263043420be3473e60c739ec78c434a976e03dee270bb8e72599f00675371deda1befd3ed76b6cb4 : Bits)
  | _ => 0

def samplesQ119 : Nat → Bits
  | 0 => 0x10880081020908048252180080841010480290104c008108411002013010924002808008c003049600c01c00812010018800080811028841c80092080160020028410404a084883010
  | 1 => 0x49080e104228041a75304121010b1526a129010a0204820040c00953932da64081408020480823624c01c44856ab084420084224022ca57848041404010a0102955144cb1d4800904
  | 2 => 0x2034027010401113658581004222ab6233104404004402048220443e4d2b69328020121022202020b5088146245be0c2042410410869631e0141081210050080019c19691972424002
  | 4 => 0x141080460042080182860440c00400084600260008810011840814082c40488450220a000480841080220a90000030800492084009414a010242020220014234400409006090500a0
  | 5 => 0x8604a148880420258acc20900484a2095604664111104402081080ac6cd25980048444101005141990aa1ab2011434810804310225d35a8220004840402410b448849b10e2b600408
  | 6 => ~~~(0x7dfdfffffeeffbd7ffffff5fdefefffffffffffefdfddf6dfffdcffffffffffecffefefbe7ebffffffffffffffffffffdeedffff7bffffffffe5fffe7777f7bfffffffffffffef7dbe : Bits)
  | _ => 0

def compactPerms119 : Array (List Nat) := ([[], [81, 64]] : List (List Nat)).toArray

def compactDomains119 : Array (Sig × Nat) := ([(subcube 2 0, 8), (subcube 32 0, 8), (subcube 1 0, 7), (subcube 16 0, 7), (subcube 34 0, 7), (subcube 4 0, 6), (subcube 64 0, 6), (subcube 3 0, 5), (subcube 5 0, 5), (subcube 6 0, 5), (subcube 17 0, 5), (subcube 18 0, 5), (subcube 20 0, 5), (subcube 48 0, 5), (subcube 66 0, 5), (subcube 96 0, 5), (subcube 65 0, 4), (subcube 80 0, 4), (subcube 21 0, 4), (subcube 35 0, 4), (subcube 50 0, 4)] : List (Sig × Nat)).toArray

def compactWords119 : Nat → Nat
  | 0 => 0x10620100805df920c143022e180830101f880448b88205c1062b0a00c822030c80fc43f801890802140400cfc12c240418080fc10624b203f241851820441ac04403110701f82246163f80483080c156100441f860b0040224b00c00a01f9004b090a2060411060600800fc112584080510403407e0d692200560023002bf24fe02c2030286020c0407e0860558fe0050c0961220fe0050c484010641f8080b091655003ac246d516366a0075848b2a8020392586d5163100d8724216123401510841cd888058c1a801cdaa3068b1b1d0039654b1131246802a0e4a0081460d96341e00b246002a0f0109a3658c401268907bfbfffbfffbdbedfbfbfdfffdfdfffdfbfffbffffebffbbffbfebffdfdfdfdfcfdfdedfcfdfcfd84c284c05cc05cc054c004c104c0744574c374c24865446544654845444544454cc344c34cc244c2340534c5644564c52445240524c51865146518451445140518c514c51464140314c3180214c2845805802445405403402401045ec0e335597a45ff03b1f023fe0ff07f83fc082a4c43510b1efc0ff03b8c9c5c09f99ff814a34dab9f712dcd2fc4746608d07700608056bb2a808c1216116bd4c190c02c20d7b546608056432f52846504b16a88d208ca0c411630aa60941640a5519820b32a22982305b051565206102b1fffffffffffffffffdc458454450458054054038024024018393f
  | 1 => 0xf2fbdcfe773b9fcee5f3f9fceedf6fb7ceef77db6dbedf7d9edf6fb7e9fcfe5f3c9f5fe6f6fb7df2fe3f9fcbe7e7f9bdbedf4d9c0cce256700d19468cafce27e7117380488a244576704938249cc84e046734538229cc4ce026701339830ca14650a3286114288a14450e718538c29c534659a71cd38a69c0d8656a32b7391b9c8dce36e711d014f1ca74e53a7301194118a04c502728119168cab4055a62af39569cab4648222c2316098b04e54a22a5015298a9ce54a72c62a00c32a00c22a00c01200a62a01a62a01262a00a61a02a61a00a61202a61200a32a00a32200a22a02a22a01222a00a02a01a02a01202a00a01a00b0826e0c0674095d923626a7e5b544ff80ff01fe037984f3e9d8bce682ddff80ff01fe03c501ca8e51a32f700c6b33ff00ae9d61ccbb7425ecc2bfc06285431dfe03a9d601baf5a1867fc05492ff01fe03fc01603e891a6e37c27f801521b47bfc06025ff01fe01dd8b2016954ee9a3467f80ff01672728a7f80da8059368ca9da43a1eaf1894fd71c5e43fe037a0ff80ff00e70bfc02132f19456a6c9fd0c35478fa2c70990c7a95cd32ffc04c1742599e015e2660783220e6c060260040642865466a01315a85a41e9fa8f97792bb55d12df96b2b459974c155e2ade55d2a564fca58d26e8c941b1f68e6e6c732c175cad04e82348f6866c2d812b07e42d00e6044000b8106001407e3040
  | 2 => 0x922f9a5c13270f248e9ff01a1ece2bf22d76b294a5902c061cc9ba42b152fd39cf5879ea17be19fa0097037fc01c928ea56847fc026edb74d67072aa35f9a095d240700f05a7c49fe01e85ff80a941a0da90d248ca06e5c73fc02d3d6e89fe004336682ff01fe0073c2d8822bb7aaffc054e77c71606224eeaccadaa7daa4342c474eb0266d7402e2305c120cdfb7566566541cfefb1905cff003cf3fc07f80146ab303fc042f1452d784f95f5707309e0188203044500891014131090c5806c007800041739e4d104238418438277d16c36a566364560f52350f4253e936136b2c528722b18118b0e708cfcaf26ed2dacce6c84c40c42c22c0eb22b04ac4a88a069a496e8828648287a872270868a5ec5244e64824644243ee3082822662061a61460e6084044000c020c06045a0cad28072604240b03000a040d26ad280c0a042402360425283400d82c1c1420420437280004242c1c345804580401282528240e143604ac2020360e052825280e10243604363420ac360f2834041024252834840e20142010341004040efc002c3421281c1c30c42cfc8100c42c1c04041cd42462885464d8584862b02628620e05282430800e1c302001283424ac5c8044b62416360e16363016042c345c24dc16442cb60e21284234801c35280e421258360e123681003612042c31debddfbedd6ddceff5faed6faf97dfe5f6f97dfe5
  | 3 => 0xba38978bcaf93a82bfc00289ff017c7d4c3ed82ff00a898a82aed5a8367e47b423eaf33a0f4eb5e7c49d32435cfd55ca7c7ee62b95245c5e285e842a57dd6e7d92aa2870042baa23ac6ab2116ba1401005004d0012096038440000422cd4ab42850a332744891224678f1e3d72d1a3564a52a13870e1c3878a1524204081028000000003401a814644862343034dc24acb636b61616dc2c365936cf936cf97c6b936fc9e27c97679972dd9e655bea5e93e7a9765e9bc6c9f27c9ea72bae4db3ccf9f274bb2ecb7c4f9765f1ec6b936ceb3e3f412ea00ed04b2802740908cb35030232811940a060d079202c940e4a00b4055e83411960a0705072a3297410ba06ad021a728e4146a0a24653232d5015ba08dd026e8011014898a4ce52272c540a2a0e7d043e8105116880acd046681b340339919500739911500739530d00739530900739131500639519100631600900631500d00539a19500539a11500539530d00539530900539519100539500d00538d01500538231500531600900531530d00531500d00519130d00519100d00501530d005015309005015191007fc07f80c7fbfe03b5d7f80ff0145cd5511f8373d9eb8ade8d64539900657fc07434bebffe03fc006dbff01281bfc03046e9bdfe0143ab3c3ff01d82627780b0c4332f2e8e12c31ff01d94de3e130f701c2acb36b77bb18d63c5ce0a2cd0399d209c31
  | 4 => 0x7adee989b2a2a360876842a3ceaff0ff09c0ff0ff0f75ff0ff008c9f100920cac0044ddba726c4ec1592d2744ac9948d2028d228a4ef49aa029d20d07405464401ce54644c34019054644034015054644034015038e54644014e54644c34014e5464403401d7601659340a080d17b5cd32c63ac15b8b549ef0bff80ff01fe03fc03e8fb949fe03fc04f25ff017c43fc03758a9a43c0e68a278d829beb317037f802c384b58115ff80ff01fe0028cc49ef887c92ffc07308778942dd1db5b4699598a883ddb532349dcecf494fa93ff01fe02adf6820f93062391cd448baaa604
  | _ => 0

def compactCount119 (k : Nat) : Nat := match k with
  | 9 => 1
  | 8 => 10
  | 7 => 39
  | 6 => 63
  | 5 => 45
  | 4 => 7
  | _ => 0

def compactPath119 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => 0
  | 8 => readCompactBits compactWords119 (20 + 12*i) 12
  | 7 => let v := readCompactBits compactWords119 (1224 + 16*i) 16
    (readCompactBits compactWords119 (1116 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 6 => let v := readCompactBits compactWords119 (6719 + 17*i) 17
    (readCompactBits compactWords119 (6239 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 5 => let v := readCompactBits compactWords119 (13942 + 17*i) 17
    (readCompactBits compactWords119 (13078 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | 4 => let v := readCompactBits compactWords119 (17704 + 15*i) 15
    (readCompactBits compactWords119 (17368 + 48*(v >>> 12)) 48) ||| ((v &&& 4095) <<< 48)
  | _ => 0

def compactLive119 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => readCompactBits compactWords119 (0 + 6*i) 6
  | 8 => readCompactBits compactWords119 (140 + 7*i) 7
  | 7 => readCompactBits compactWords119 (1848 + 8*i) 8
  | 6 => readCompactBits compactWords119 (7790 + 9*i) 9
  | 5 => readCompactBits compactWords119 (14707 + 10*i) 10
  | 4 => readCompactBits compactWords119 (17809 + 11*i) 11
  | _ => 0

def compactPoolIDs119 (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let v := readCompactBits compactWords119 (14 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords119 (6 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 8 => let v := readCompactBits compactWords119 (705 + 11*i) 11
    let n := v >>> 7
    let bits := readCompactBits compactWords119 (210 + 5*(v &&& 127)) (5*n)
    compactIDsFromBits bits 5 n
  | 7 => let v := readCompactBits compactWords119 (4162 + 13*i) 13
    let n := v >>> 9
    let bits := readCompactBits compactWords119 (2160 + 7*(v &&& 511)) (7*n)
    compactIDsFromBits bits 7 n
  | 6 => let v := readCompactBits compactWords119 (9917 + 12*i) 12
    let n := v >>> 8
    let bits := readCompactBits compactWords119 (8357 + 8*(v &&& 255)) (8*n)
    compactIDsFromBits bits 8 n
  | 5 => let v := readCompactBits compactWords119 (15333 + 7*i) 7
    let n := v >>> 5
    let bits := readCompactBits compactWords119 (15157 + 8*(v &&& 31)) (8*n)
    compactIDsFromBits bits 8 n
  | 4 => let v := readCompactBits compactWords119 (17907 + 3*i) 3
    let n := v >>> 2
    let bits := readCompactBits compactWords119 (17886 + 7*(v &&& 3)) (7*n)
    compactIDsFromBits bits 7 n
  | _ => []

def compactBucket119 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let d := readCompactBits compactWords119 (815 + 3*(i % 5)) 3
    let off := ((i/5 + d) % 22)
    let v := readCompactBits compactWords119 (830 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 7 => let d := readCompactBits compactWords119 (4669 + 4*(i % 25)) 4
    let off := ((i/25 + d) % 98)
    let v := readCompactBits compactWords119 (4769 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 6 => let d := readCompactBits compactWords119 (10673 + 5*(i % 40)) 5
    let off := ((i/40 + d) % 147)
    let v := readCompactBits compactWords119 (10873 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 5 => let d := readCompactBits compactWords119 (15648 + 5*(i % 29)) 5
    let off := ((i/29 + d) % 105)
    let v := readCompactBits compactWords119 (15793 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 4 => let d := readCompactBits compactWords119 (17928 + 4*(i % 5)) 4
    let off := ((i/5 + d) % 19)
    let v := readCompactBits compactWords119 (17948 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | _ => []

def samplesP63 : Nat → Bits
  | 0 => 0xbfb7fffa7fb93bf7cb65ec2abffbffbf3d7ff6fcf2ed02d55fee01a30f6b9f07e3673047dffe7b55cdf37f63f64fe7117bdcded0853adc036e4505ce045a9b04b95efebf29c8ba4988e6764cf4140e1b84d4120bebcda02
  | 1 => ~~~(0x114002000970094363064f6500108122006452a0b84821810b84513f6e078bc265ff3544910810188661544a4482c1b1f15e4e95e5ac1645437615c734dbbbc5889832c630acd288dcccb2e9c6371f3be5dd66652dede9a : Bits)
  | 2 => 0xfcdbfe6ffdf277cf345e00f73ff79f6fffbc3fe33cf8e79b7f90f34c3e0fa0d61b840505f7fbf7f9f3ecdcb9cf8fd8f3f02e1f0f607d0fc3c0fa06d1100218c79f8f79ded774378e741c79e0c2010718e088e1e374b5408
  | 3 => 0xfb57f7f5df7d9cf9771237293ffdf3fedecdc9e5dd1f79efa7af3c375225c7e82c98800bb9ffbffebe27ecdef3b1e72c94d72673eb8470dc831e3b6060a5200bebb7f7e23e9cc1b03fa99667486210600323ee2dad12190
  | 4 => ~~~(0x8900440108814e5045d243b8040000c158d00c5108d4058662239e4132de6372b3ce86c00e22014f1040880f20da32f9cc5175309335cd3aa59267266e77e2c0306e8ba06d0a3fe32285e44f96ed67a97e7c1abe39f3f0 : Bits)
  | 5 => 0xdfebffdfbbcecd67ec8d4f55ffdeedfff7e7529fbbcffd78ea7459fce1946a3365786862ffeffc9ef75d13ce7cfeb9af8d4141951da316753b71f43626c1662146f8aafff6a3c2fed2488a99b12ed022154545f403e82f0
  | _ => 0

def samplesQ63 : Nat → Bits
  | 0 => 0x4048200981444400100a02c54880103104c0310032120531200102103084401000904582588202544000602206400012840cc02005442c009141032018210400a15288a0094082400086004c081a0a048424120b8304202
  | 1 => ~~~(0xeebefcfefedff6feddfdb8bedf5fb7f77fbfecefeff1cbfedef7bff9f7fef77fdae5fbbdbb3efcffd77ff5efdfd7efc5bdfbbb9fbcbffbfe4fdf7eddff6fef7feeba77ef72edffdaffdebeffdfe77debb3ddeef5adedfbe : Bits)
  | 2 => 0x3241392040880104ba0fd00b44402022010c658844d3840c19a042041100120806b1a598761a52083080481000300ac62110fc06210510f2aa8d400014421201a0d615ad6042408600828004060d01868cac1a074b1400
  | 3 => 0x4a8441aa082020280cd8894cd0101801285a402a2504370cc50818880023000422479b139123c4a002600408100a280847989061404685a47c116458400c006aab255a2308041001a00142208433840819caa25ad00110
  | 4 => 0x8920420300010640455003a031a004009050023402042020e601840022802030804a024201c58810450800c080047410860000798098050440208442202020b44a0160520081800851080900285206111102c54084080c
  | 5 => 0x201480a0141120880130302a1200a404411040694421080202a020010440844c1001820c822cc080100111005094094528000281a8199104080a4800400808514408224d422100920040020192a44029304044d000e80a0
  | _ => 0

def compactPerms63 : Array (List Nat) := ([[], [64, 81], [50, 16, 84], [50, 80, 65]] : List (List Nat)).toArray

def compactDomains63 : Array (Sig × Nat) := ([(subcube 1 0, 7), (subcube 2 0, 7), (subcube 16 0, 7), (subcube 32 0, 7), (subcube 4 0, 6), (subcube 0 4, 6)] : List (Sig × Nat)).toArray

def compactWords63 : Nat → Nat
  | 0 => 0x3076223f
  | _ => 0

def compactCount63 (k : Nat) : Nat := match k with
  | 8 => 1
  | _ => 0

def compactPath63 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => 0
  | _ => 0

def compactLive63 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => readCompactBits compactWords63 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs63 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let v := readCompactBits compactWords63 (24 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords63 (6 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | _ => []

def compactBucket63 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP127 : Nat → Bits
  | 0 => 0x519e1a8a5293cd7bc5cba00c1f2283873ca6006965c501c3f705cbb065054100835cebe66f9dc7f5ff57a3e5e51d3ffce06afecb8cad782c633f972e90a31e8f45868f8d01829c546e0687356409c1add05807401660c1062600d6e4ae3199b67f97a9c516b90a79a153468674182325a81201820658275209046d2f9a648820
  | 1 => 0x7f31f3507f651fbc98fcf403ec2c3444c0e731f21ea01f183ab94044000a98913c0f8dfb3df5f9dfce9f4a3f51f1878d27d39733f61bd14fb5f2c1fce21c609a920dd036b81d2907f4e0758749307ad001e4c081c1830220501f21cbb33cf0ea7366cf58660ea3872a0e835340f44599c1c4ba083080d0814ccd4c88a4826444
  | 2 => 0x8c5e747d9447ebd2ff201eac38d86889f9186247e802e58d08ad9500401022060233de7fe7fe73fafceff3ce9f623cc79c92eb7c47a39fd2783b7ac144a6bb6083d0bb60d46039ea07b086f88e6381169e810a080800980681a0ae5fc7d87f8d3eeb576885c3304e4cd0b9245f86303e040840b3070e042070f1e79262480203
  | 3 => 0xf667879fe778b21f0f4ee772c0138f308e1a3c0470cffa1041322788886800200418f79dfbbf7d7ff7f97c70e67bd819d8fd529c7b5419fcbec3bd360758c2731cf943871f69c230383b3880b07e0e18e3006002210f041900423b8ddbdf9b3fc49db68e98103d900fad0a398718f9c44261044058001885f716b93430831088
  | 4 => 0xa9e9dd6baaecf16435bb5870e1c173783345c7910535c22396c20c2315804215088fffe7de5bbeae97a9dd951a9ec0e2ff757d2b0f5566335fcc56e968c01d0ca5670c4ae1f3606851c5582a5b8a364d2c51889cc070214007842bf67c6f05798978f135e8aac401d1a5754790071ec224904901a09740681f2a10f141280364
  | 5 => 0x7ec1eca47d9a1ec362f70b83122fc87b00e0c98c9b5a1ce42d42b07882031448d01f7efcb1ebfee7297eb43aa9ee677227ac08c7f9feae8fc9fd29d31d1f8095680a2039461ed6878b186a4736c47d2201ba3061260004b868181d337c82eed5fd780ea2794553e6d40804a8a8eb8661912734040860a902a2fa024f48157010
  | 6 => 0x83be2bf789bf64adfa1401dd07d4148647199e3a8238207ec05c7ac73af4adea61f7311bde668f197bf68fcb7e85fb3f5b0fa5f4b0eae7f18604ee18bb6165607a3074d02a840799804f8158819580e37e261536189c7ac19861543801e76642828778130374cc383272f8d82b61c81a1a08827cc121021c0001924095108d9b
  | _ => 0

def samplesQ127 : Nat → Bits
  | 0 => 0x218045003094a204c00040812001000882400214100024300008240818122e0d00880b826804c41188512020050500040008504084040000630002089084c010439640020086a2201606009214004058310018800100240140211280a83180864284894110010a08200100860000230048150342008820920904680c92048020
  | 1 => 0x60c54301003482004408084800800a0220108000410880060102820a8c500640818a09522504a1098c040a0010500281020002022202400800a08080349450481282020600c5a08102020296020120c8090804102048100409000048a228c0822242cd084200810502008201404400010014222a0484609108854488a0804404
  | 2 => 0x524faa01c02118091528810081060020048005200024104010500033a5e0d0d0cd53d07c07a0334a64a64108800214001402010840810500000a20012479196834081b2c0a610981a8881e452a21b5804c040020840240500450045d07887a09346b5600850200404840202012800014006034384726452160d1879260480002
  | 3 => 0x70834307880385c82a41000102040c4010100090c100008040118547283798d5830b6854a324c7652d110504200801080c40010080010a09001010581608511c51c48a058120328345c3460fc904510f0138040101001209000b2855955132cc49d308008102400050808100410908048414d4051090c665512b93410021080
  | 4 => 0x4001036094040f202c4020202180400480208408240008060244004420d012232242401905b08a4130884040888004060102400011020120400502641020481802000c07518044a40502020c09602038030200308808080200269225046057089102014008840008084410080020c021482480098118844162a106101200240
  | 5 => 0x10028806814140a31140041404401100100c10022080430080800081012c80322645402890c91280212a800020206102012008051000880408540042400b08a02020114827280c42c8800801002692030420410400240a0200840d3204822c5119200220200010a2100004080828006094a210108a3281002268024348012010
  | 6 => 0x120204800a01100206080000308010a0001000000000000000000000000000000008300000828080180a00068024100000c100000000000000000000000000000000000000000000002084201000802080000000000000000000200640010003210402101400800000000000000000000000004100909
  | _ => 0

def compactPerms127 : Array (List Nat) := ([[], [64, 81], [50, 16, 84], [50, 80, 65]] : List (List Nat)).toArray

def compactDomains127 : Array (Sig × Nat) := ([(subcube 1 0, 10), (subcube 2 0, 10), (subcube 4 0, 10), (subcube 8 0, 10), (subcube 16 0, 10), (subcube 32 0, 10), (subcube 64 0, 9), (subcube 3 0, 8), (subcube 5 0, 8), (subcube 10 0, 8), (subcube 17 0, 8), (subcube 20 0, 8), (subcube 34 0, 8), (subcube 40 0, 8), (subcube 48 0, 8), (subcube 0 4, 7), (subcube 0 8, 7), (subcube 6 0, 7), (subcube 9 0, 7), (subcube 18 0, 7), (subcube 24 0, 7), (subcube 33 0, 7), (subcube 36 0, 7), (subcube 65 0, 7), (subcube 66 0, 7), (subcube 80 0, 7), (subcube 96 0, 7), (subcube 21 0, 7), (subcube 42 0, 7), (subcube 12 0, 6), (subcube 68 0, 6), (subcube 72 0, 6), (subcube 1 4, 6), (subcube 2 8, 6), (subcube 16 4, 6), (subcube 32 8, 6), (subcube 64 4, 6), (subcube 64 8, 6), (subcube 7 0, 5), (subcube 11 0, 5), (subcube 13 0, 5), (subcube 14 0, 5), (subcube 19 0, 5), (subcube 22 0, 5), (subcube 25 0, 5), (subcube 26 0, 5), (subcube 35 0, 5), (subcube 37 0, 5), (subcube 38 0, 5), (subcube 41 0, 5), (subcube 49 0, 5), (subcube 50 0, 5), (subcube 69 0, 5), (subcube 74 0, 5), (subcube 84 0, 5), (subcube 104 0, 5), (subcube 17 4, 5), (subcube 65 4, 5), (subcube 66 8, 5), (subcube 80 4, 5), (subcube 96 8, 5), (subcube 70 0, 4), (subcube 73 0, 4), (subcube 82 0, 4), (subcube 88 0, 4), (subcube 97 0, 4), (subcube 100 0, 4), (subcube 98 0, 4), (subcube 23 0, 4), (subcube 29 0, 4), (subcube 30 0, 4), (subcube 45 0, 4), (subcube 81 4, 4), (subcube 98 8, 4)] : List (Sig × Nat)).toArray

def word127_0 : Nat → Nat
  | 0 => 0xffff7fd7fffff6ff29c729c329c0e8ccf9c6f9c6e9c6f9c2f9c2e9c2f9c0f9c0e9c1088d09cb09c909c709c509c2714c694c694c710c690c690c68cc708c688c688c684c79ca69ca79c869c879c669c679c469c479c269c2b08ca88ca84cb00ca80cb9ccb1cca9cca9cca80ab9c4a9c4b9c0a9c050cc48cc504c484c480c49cc484ac88cd00cc80cd9ccd9ccd1ccc9ccc9ccc1ccc848d9c0d9c0c9c0914c894c910c890c90cc88cc888c884c900c880c99cc91cc89cc89cc888a880a99ca89ca89ca88c8884899c889c88886880699c689c699c089c0314c294c30cc28cc288c304c284c280c29cc28ca288a284a29ca284629c6110c090c108c088c080c09cc090a08c80848080809c80886084409c508d00c88c88684884480c808804802beb7f81d49854f7a7cb33bb0bb4bee4d211fe0333cf6d3597b027f81fe07f8018eeb8782d9623fe07f80123968bfe016bffe07938be55547beb858c04c3085fe0102010070eb9eb36acf25f1ed19e9370c507700053610181013e74d9728106361420302027ce9b2e5060414d8406080cf9d3664b0018d85080c1019f3a6cc9618017386c305060804f9b300ca084c30506067cd966c20a386c305080404f9d2e5020670d860a101809f3a68194088860a0c0cf9b2cd821018e0536101829f3a6cc0e000ffffffffffffffffffffc23223403203212202221a11201200e163447f
  | 1 => 0x72a97be100d5e489b38a0cd3330072a9e9c96203fc7c411bf5ea09b39c60c0401c211bea01e683729c6cc9e372e9a03c2100c495e9738a0cd33312e749e9c9bc6a1c431c2115e96c5380dc605c22fbea036112c0a08062e03c7c5c3be361e692934a036381a115eccaf3848000acdbe2c36101f289f34a0363818115eccad389e0c08062a0248cdc5c32837be5e1e2d34a038361210cd5ea738789a74cc460c0a0810024bc7c52c243643be1f29329f2e4a9bc2740e0c3736a161332f2c9ea09a99c7c233c00ec63737329f2e4a9a05c2740e0c369936a16133312e05c69e9c9a1e3dc469c20ea0364099376036980dc603c5c3c02ea00f2b615e0a0806040fc7c5c329c12a2e3134a01c0e3836b13735332ca09e9821c69a29c0380e42bc3736389a01c609c2260e37289c98036009c3c00e36152a9d600e0c0a0605c6552bc3c036261535333040a09e9c501fc63bc4380e36989a533602729a043801c24022360e992960480c0a0807c7c44c1fc2360e22117fbfdffffffbffffff7fffffeffffdfdfeff7fbfdff7fffdfeffffbfffeffffbfffdffff7fffdffff7fffdffffffffff7ffffbffffff7fffdffff7ffffffffffffffafffffdfffffffbffffff7ffffffff7ffffffffffffffffffbfefffff7fffffefffbffdffff7fffff6fffffdffeffffbffffffffffffff7ffffffafffffdffeffffbffffffffffffaffff
  | 2 => 0x72fbe403a94a09e9c249601c6104649c437be42941e1e76220d2a394a72a076735f309d2e9b2895c41fc32c3423bd2a4838c94bc761329e4a9b2e1fc2220d2a494a36a1c761329f2e9bc32a322236c74a76061e38220c772a9b4a72a076735e07329f309d2895c7c41e212c3e9a2239bc6b2a434a48767360364440940c05c603c423c3bca01f2a7672395e0dc605c5c2483022a1bd2dc761329e4a9b2e001fc2220c372c492a954aa1c761329f2e9a952dc22e232a36c34a7277600a8d5e08060073c7c5c3bc23c7609e9a0dc24440a0232d609e9c9a300c49c695c5c24422412bbca01e7673615e440a0806400023c7c5c32c31bc1f2a7637309473c4020a222dbc381f2a9e7334a1309d2e9bc41fc32c2a223638949f2a40bf4a0d5e0801c5bc3822a09c9a0a9449c42c23c244384019bc9e1e772c72235e440c0806400049c5c23819bd2a1e2d348ca1329f2895c69a1e20443828232bbc42bd4a36382202764405c60827bc8c372c9c0d600a760601c7c3bc223622089a95604827c257bc1e9c36767236440440940249c607c42239bc1f2a9b3442a1329f309dc61e21c52c24223836949b2a40b94a0d5e084a01c439bc9a22a09e9c1207c6944839c44422412bbc9a1e0d600a0673c7c23694229a0e10016049c24c3622941e9e369b2a97c3be100d5ecc4938a1312e792a9c9a969ea1c435c2cdbe115ec939c6cc9e3
  | 3 => 0x80605c7c401c273c097282ecc020e9e9c9a99c7c5c3c07230962fc69e9b324b2fc274260d2b4e36a1608d329f2e9aa12895c7c21e3dbc272a6c454e36395e0c09c7c3c031bca02731c69e9b324b2e01c274260d312a36954ea161329f2e9b2c99c6a1c3c02e2637312a94c34f600a8c075e0400a1c7c3c1bc269e4a9b5e4898940dc675c277c1bca0272b31608d5e0c9e309a983295c7c3c1bca07e27600a06040026315f31c7c3c1bd2a3334a12e9b2c99c3c02a263837312a949ebf4e0d600a064801c7c3bc26367648a09e22049a95c7c3bc8c2698360d600a07c7c2369426a1609e0e009a9815c7c3c036549427c6cd329e06372a97be140c9b5f3ca0cd32072d2a9e9896203fc615c0a1be9b5f3dc6cd329f2e4a9a3603c2140d5e973ca0cd332e752c9e9a99c7c2a031c0155e96c53c0dc7c2082fbea03615302e0a060205c7c3c129be36329134a038361418cd5f3cac76736036784440740c0407c7c5bfbca01f2f2d2e0604001e780c36947448a1c761329e072a972dbe3a2e372ec272052e0d61c60695c47673bca03a4878767473608e8d5e040a080201c72c07c5bf2fbc3a480c464440421ea09e9c960dc6944847c445be41bca0421e7876747360475e440a0802400049c7c52f2dbe43bc1f2c9f2e9c96940c04067876727448a134a03a263836ba8c040096725237be1e3a40956006720c0a0803c72c01c43
  | 4 => 0xdbc300a0605c603c237bf2c0c2ecd5f329f309d2a972895c7c405be060c3c3e49bc4b2c9acc9e0c9607c695be6dbc9a68787404cc475e0a6c08020007c7c52dbe9a43bc68cc9e9c960695c6492dc5be4441bc9a1ecc9e9a0c03c695c26dbc966804cd5e0a6c08060003c7c5c32dbc9668cc9e9c9a02482295c72dc5c2304441bc961e0c01c697c237be1e3c4094040a080603c72c01c5c237be403c942e9601c7c3be3668941fc7c23c49be360c10015e08cc0605c40279c20bc1bf28349e0a07c603c201be37283200cd5e420a080403c7c40621c00dbe3f289bc60a080603c49801c237be0c1e3d28000b5e0807c605c403c275c0300d2896389fc5c073becc0c2f309d2e9b2c9897c52bc27801c0720bbe2f28349f5ecc01c40bc3c02fbe35289fc7c3be362e0c15329f2e9a972bc7c20801be362e9c332809c7c2002fbe32369d28cd33312dc69e9c992a97c5c0004a0673be3e2f289bc7c3be362e0c100d332e2f2a97c605c26801be363c9873282e0dc60401c241be68369929c7329f309d2e9b2c99c5c201c07402722f2830960008cc0605c403c20bc073bf289e2ecc0a2a9c9a9897c5c3c073be34822e9e0a07c603c201be37282e149e2e9a980897c7c3be329c9000cc0a0805c603c407c073bf289a2ecc06249e9c987497c67dc5c04a7335bf282e9a0a07c60201c3be3699282e2e9605c7c3be68369872cc0a0
  | 5 => 0x840d631a560828d06bff00395fbff00039b5bd16a0cff3970ea194a3377fc00ff003fc00ff003fc00ff0008834525cded84b217bfc000443f293d361aae0a8043a49d71893b2b47f30333fc00697951c71ff0003856ff002306502200022854080623565824001000a2e0090800104022800000001820a08c0402002004000fa604040003c34d0b240c302525c005106001206281931010194180808100080080074181000800120406ce1c0e080060000100100120a0c00000040001a001135600402080802b0a282810000285121030a202028000012011800082071efcdee2becd7e9ece874e5f0e3ece270e072de2bdccfdaead9a8d8b0d6aad572d32fd150cf49ce34cbacca27c950c74ac615c367c291c06cbef4bc6fba90b88ab74db5afb3d3b16bb00aaecead0fab2ea974a6eca571a353a0ed9f509d539aef991296cb956f9389926f908f8eb28c708a72882a86ed854a841281cd802f7e4e7c9679c778f076f6742f7248714b6ff16dd06bc96ab56810660e644b62f95fd25d8f5bb35950574e558a545351f34f8f4db54b084a1147f4457542ce410b3fad3e123bd6390a37d135aa346c32ee31322eee2d322aec296f2792254a240d226a212b1fca1e901c8a1b5418cc1750154e1394110d0f6f0d880c910a6b090b07ae05f3038d01ef00004cd5e0a080201c7c407be0c9bbd2c203e0b5e080603c601c5c2752
  | 6 => 0x73e81651933d4c6c9613d291986391d968be5abfc005c4a0b08b4e7c9fcabff003fc00ff00348f6ff003fc008f309d855ff00358bb217125c3eda68ad061513ba6cdbf32aa959e68647fc00ed4487dd3ff002dcc50a7415cf7445ae1c7e3d2fbd5a9ec24c35e0c517cb4798d0e4c99a5b3016cd18d42f1872651de10165031161ab1e3c5e962a750adcb8d536840945d1b798476e0a66c672d68525867079df57a467ac9166182d3cd9dac0339c463a4ad5176e55c095a3296da9cc83d326b4919c1991538072dfac194d1487cbda24a52d901d09f0963a574a4c43ef8254c054a15cec2baa389c18fe53a3cd8c59297ad9fd2785380b1026ad5c70d44591ef004fcb5787b111e143d3048e1137c706a9e2e44f3fc00e130e296d3c1907087a781b7c42ff00279776876528adbd144748163351a5df1a7c6595cc71db295790616ba0f594eb58ea0b755c8bfff0028c59e60fd25ceea60bfc005d24bc837ff003489fa0721c9cb5c20ffc00105b389642039a3160173969db7e713bccb2ba1c0ae0dba2c07d6eff001f915ee07ea92f59231140e154fbcc5cff003c4d2d771bfc00ad0c3d9ccff003fc00d80cbfc00ff002ec6f1206bfc00d708d48b94180e2d313a20a3831804cc19a61f623fc009e79061ad4d6c404d3ff0027454786fffc00ff0010dbbae364c127ff0001c2d0d5e7717d4604f5187b11cf2d1fc43ca7d6f
  | 7 => 0xc90fbe6201f8482f2f090cad402b042a81062415ea954b747a6f05d91c51f383fc0033088a9972e59c3c5dff00145e854763fc007b125c9f9af514108ff452df58a3506d85a8e628a852aff001d110ff003fc004d48c88e38a35bfc00ff001d850831f6514e65636a57ef41d3a9eeed49bc1d61e81658d7ef3606937f228dd547440da592ef87b030b66a4505ce7577aaf8014229b25d18d013fc002c4ee480fff002c4a02d51114035d60ffc0026094299604822f47c932d7fc001a7d69cedaa7019c4bff0009824ff002ad5dff002cc636b82ffc007a507fc00e74d7fc00ff003fc00ff00045e3b4189984083337fc00a955bfc00e22cc3d939b00030336537288a7f16cef1af497fffc00f640e40a9e37ddc174c362e342cc66fbfc006418245ba75129bc75730e3fc002c387fc00ff003fc00ff003fc006409bfc00615d5a1210d16324145b57c04f0ea5f3fc00f36939c69805eced5a4641ffc00384e6a98064227fc000325d609dff003fc00ff003fc00797a5b97fff0002853092848161a11e0c98191729903ab300ae086ff003fc004d64bfc0008340842e097f7fc00ff00001464a3ac588d07708900db7044a1d4c426da59576496c5531d53fc569ff00035dca7811f0904281d0cf30d3382c7b81259545bb3624459b202291cc1b432d586eff00049aa8e7c20dedf501ed8158375ffc00d625724af6b46ffc007f
  | _ => 0

def word127_1 : Nat → Nat
  | 0 => 0x40675a0cea419d2833a5067490aeb415d282ba50575a06e940cba23174062e9cc5f418ba8317d002fa0e2d2985a330b4461680c2d3985e830b5061688a2d0145e828b505168862d00d8253304666088cc1099820330d0660a0cc11158682b050561a06c140f39910f39909339908b39508b39501b39108b39101b38d11b38d08b38d01b38909338901b38511b38501b38111b38110f38109338108a39910e39909239908a29908a29901a29900a21908a21901a21900619908a19901219900a11909211901a11900609901209900a01910e01909201908939910d39909139908939901139900939900539508939501939500939101939100538e11938e01938d11938d08938d01938d00938a01938909138901938900538511938501938109129908929900921900521500519908919901919901119900919500919108919100511a01911910d11909111908911901911900911900511508911500910d08910d00509909109908909901909901109900909501109500909110d09108909100508d00908900501910d01909101908901901101900901900501509101508901100500d08839910d7dcd9450000410f4b5e8c6474b3cc28896d131a70f56d4410a623b2c454137a18dfbc7260c06ac77a5c2f1122161db971a2d8d59076a8117d20ee38babb63b6116635c934c7e22c651a00e79bb12453775799c912930df3cc3b
  | 1 => 0x6c480d8941b128262403c4a00db406ca5359466b288d6509aca8359445b2a0b6540e9a81d3502a6a034d4029a83abd0356a06ad4095e80ab50156a0f3529a6a82cd5029aa03354026a83a58a64a94c952992e82a5d054aa0a974052e80a55014ba0e71298e2331cd0539a012129a42334850590a072140a4280485072514c49298925312866248cc49198922312d0524a0a4b40c9281925070d14c192983253064660c88c191183213065050ca06194060253404668084d034160681c0d0181a00911192203245063294c65198ca1319406329cc67418ca83104a62088c410988203104e620a0cf1299e2333c4467884cf1019e6833c50679a06f340462230c40618a0cd1199a2233440669a0cd1419a222b4d0568a0ad3405a68050505a0a07414068280505075494cab4155282aad0354a06a940552802a50794a0b2940e5280ca50094a0e6d298da331bd0537a066f400de801bd070b14c152982a53058860a90c152182a33058460a88c151182a1305d050aa0a174102a8205d030aa0615409fc433f4867e90cfd119fe823fd047ea08ff409fe813f5025280ca54191243224664484c89019127322d0644a0c8b4046c530d4a61a90c361986a330d4061a9cc374186c830d5061aa0c352146a028dd051aa0a351906a81828a60494c092181433024660484c093981283024850484aea299d2533a486750cce9199d2133a
  | 2 => 0x68cc4d1989e829350527a064d40c9a80135070f14c1d2983a53074860e90c1d1983a13075050ea061f4043a80c14668284d0740e0a81c1d0283a05074060a809140622a0c811990681a0d0141a031d11a3a81c75028f20f1d41c52530a446d488da9402c67358502b0a0f1340a268344d0289a00011180273005000120e3d1187a130f4e61ea0d6d29ada335b446b684d6f41ada835bd05b6a0b6d406aa8155501aaa0eb341162822c50259a00b14016483ac507a4a0b4940e928152501a4a0f3d40a7a80cf50751a08a340146839e4a63d10c79218f2331ed053da0a7b410f6819ed033da0256298aa53154a62b10c55218ac33154662a8cc55118aa8295d042aa085540cae80155008a94d1511a2a82c55038aa05154062a83884a61088c2340b425368466d0a0ba14134281e8500aca0b5940eb28156501aca0f0b4161681c2d018494d0a21a12434246685a0b0b416168242d0385a070b40616801a42635a0c694181a53034460684c0d0181e73034e607a0c0d4181a8303d020720e0d41f3c4367486ce88d9d09b3c0367406cea0d9d4133a803e4467c84cfb419f2833ed004688c8d0991a830e4a61c90c3919872230ece61c9cc3b41872830e5061c88a394147232654a6ca8cd9511b2a1365506caa0b9540cc23318426319cc61398c68318506308c861090c68218d010288c050180e8301506028878921b12236242
  | 3 => 0x77119ae282dc503b8a0287415c682b8d0471a04e34059e82b3d0367a0351412a281515054e90c9f4153e8227d0196a0a75298ea331dd053ba0051218a22366504cca079940b3280bd4867a88cf7411ea823dd037aa06f7405ea80e4505c8a0791405da533b4e577a058529b0a82e1504c2a0585405aa53354866a88cd5395ae82b54e46ba08d7405ae8035d00bea0b7d40efa80b14a6629cac538d8e805d4a6ba90d75416ea825d503baa04b929972432e4465c9cabb4157682ae5055c9c8bb41176822e5045c9c6bb40d7681ae5035c9c53141662824c50398a033141e62839f4663fa0a7f40cfe839fd072c90c59218b433164662c8cc59118b282965032da0459408b680165008c90d194163282465038ca031941e3283898a61294c252984a4309486128cc250984e828950513a062540c4a8089d071320e2541c4a83e9446d280da540b4a8057502aea035d402ba83c34468680d0f40a1a8143d0086a010d11a1a0343d0287a050d40a1e8043d0086a001101826830490608a0c11418248384507c094d8121b023360426c0a0d814170281b24a66490cc91199213324e664a0d6a29ad2535a486b50cd6919ad2135a506b4a0b6940d6c532d4a65a90cb61996a332d4265a80cb63996a732d5065a9cab54156a71ce5019ca013941d3680a6d014ca029b41e4a334950592a092540e4a80495072714c4d2989a53138662
  | 4 => 0xcffb7effbfedfbfef7fdddff7fdf77ecffdff777deffbfcff3fcff3fdff7fdf77ecff7fdff7eeff9fe7fbfeff3fcffbfcffbecfffcdf77dfbffdffbff6ffbfdffffdff7deffbfeffbfef7beeffbfcff3fcffbdefb3fcff3fff7fedfffefdbfeff3beefb7effb7eff3fefdbbfeffbdefb3fcff3ffe7fcef7bddf77dfe7fcdf7fcff7ff5ff7ffe7bfef7beeff3fcffbbcff7eeffbfef7becffbdcff3fdff7ddff7f4ff7fffffddffffeffdfdff7ddff7f4ffdffffdffff7ffffffdffffcfffdff77dff5dff7f7fdff7ddfd3ff7ffff7fdffffdfff77ffff7ffffbff7dff77dff7f5dd7fdff7fdff6ffbfeff3fcff3fefdfdffd7ffb7fdff7fd6f77ddf7efff7feffdbfdffafeffbdeffbf4ff3fcff3fff7ff5ffbbef7bf4ff3fef73fcff3fefd7fdff7edfd3ffff7ffff7fffffeffdbfdff7fdfb7f4fffffff7fdffff5fd3ff7dff77ddf7fddf7fddf7fddf7f97f7fd7f7fd7f7fdff67fbfe7fbfeff3feffbfcffbfffd7ffdffbffbff6ff7fdff7effbfefdbfeffbfe6fb7effbfedfbf6ff97effbf6ffbff7fdf77fdff7f9bf5fdf77f9bfeffb7effbfefbbf4ffbfeff3fedf3feff3fcffbfff7ff6ff7fdff7f4fffeffbfcff9bedfb7eff3fe5fb7eff3fe6ffbfef7beefd3fcffbdcff3fcff3fb9d0173a018d4071a80e35006fa0cdf409be80de505bc9c77940ef2335e505bca0b79412f281de503bca00bf3957e82afce35fa
  | 5 => 0x41504a86deb780780e1200a0d960079c69781e1200c0200613414a1c1202960ba37ade1c60300801c141228704960deb780781e0300a0204b058210500658286ba37ade1c20300a02416580490528670b7ade01f3fcff7fcff3fd7f7ddff7feff7feffbfcff3feff3fcffbfdffbfdffbfcff3fcff5fcff3fcff3fcff3fcff5fd7f5ff7f7fdff7fd7fdff7f5ff7ddff7f3fcff3fcffdff7f7ffff7ffff7ffff3fcff3ff7fbfdf79fcff3fcff3ff7fdff7fbfdffbfdff7fffd7f4ff3fcffdfeffbfdfd9fe7f3fcff3fcffdff7fdfeffffdffffeffffdffffeffffdffffeff7fddf7fdfb7fcffffdff7fdff3ffdbd6f7bfef7bfeffbfedfbfedfbfef5f7fddf7fdfb7fcffdffffdffdfd7ffffedffffdffffffb7feffffeffbfeff3fcff7fdfb7fcfffffff7ffff7ffffbfeffbfcffbfeff3feffff5fffffff7feffffeffb7effbecff3fcfffffdffdffbbfdffbfeffb7effbfefb3fcff3fffffffdfffffffeffdbfeff7feff7feff7fdfd3ffff7ffff3ff7f7fddf7fdfd3ff7ffff7fdffffdfdffffdffffffdbff7dff77df775dff7fdff7fd7f7fdbfeff3feffbdcf73feffff5fff9fe7fddf7dddef7dcff3ff7fddf773fe7f7dcff7de7fbdcffdde7f7f4fffdffbbfdffbfeefbdeff3fcff3fcff3fdf77ecff7fffffddffffeffbfdff7fdf77ecff7ddfb3fdff7fcfffdf77ddff7fddf77dff77dff3deffbdef7bdef7bfef7bf
  | 6 => 0x86de0900500e9502615412029600dc102c1c69780c0180504960028550437aa1b787180a7241270c107005c1516019066a19c61505c03006014130416071864a18660e0041296001c100837aa1b787084b05806721c613c10701601605a151c2a18b24d256078a026a880d874ba840e1a921080e14aea3382ea2036559361c936bbaec0c1584c9301d37aa22ea07a860e872370501d288a18ce0e8481c80e14b86e089ee009c958b21081ea2072a1aea03840e18523380f0581e00c14a2036102ea4db7a0100c028080183b05c14a22e8a1aea10042ba9c47080ea42e8a182210272978381c89a719c403a90720b2348400e1c210822a1a721ca5e00a890487203a52720361025ebaa8904a520bae808836038dc9c8725580ea202f058310500504a86de1561cae826a8803c12a187208ae89782226a52ba2881c80104a8697b78100020b2521c80e100c0088360e1c69787294ae80a8220d838039c69c8405489a03c12a183808ae89789a9482c1c80104a869783830040de002948720389a0e036101c29784294ae8090220e00e708361014c9ca58959c470ae8a184cdeb780d1601225a961c67112a4a020deb78582860f84812bb1048480380c7203607a5e5804a03c16040225600d04a86720489804a03bb104822030100db7a559c89ba721cc16ec04c02808080060100200414a1c12ba37a12378ec00a080060241612
  | 7 => 0x83480e7084209a760e28697a88ba9c105928948260bc1203c109d9560da880b80e9d8310580904c10de28655aec269c803a8904a8609aec979c7049c20d874a180e9782672417049c60c1c3041c031a5e1f9c80ca864a026de2880c2520c89a09c160025f04c1031a86de0020700e948260e0362c1c6979c00982a03c100d8389d9522c09a03c120e28609aec979c8098369781ca19280e0b071866de0740082803a52268bc108260e03670a5e720120d8bc26a5e0e2860a12870b781683603814a196097a6472412ba1c8709c003814a196097a64ec0740c80e00417048c6941c80d814978367080e052865825e991c8ba1c6701c803814109c2a196097a645807470831058150480e56286993b01d03003c160bc1202410de958a1aecec02e0c8430589800c1104a5e0d8c62437a0001c03a50580362c01471a5e70819048145800ea19409925e0da76de0389937aa180c151607225e9d9c8959c2951c0a1b789937a0d054583b00504a038c7058260305504c107203697a5e0da760e006de1c29937a58286030547225e9da5a71a54701c870b780828658264de8540f9600384a05159058260305504c10a19c8993b00384a09c160305504956de9c8050369dbb0029c80d820018040080105c1215410deb78a1c1671c12129c20d80ca18547225f05a76031c7049c3041c0de1c8a1890153b0028200185401416dec13042
  | _ => 0

def word127_2 : Nat → Nat
  | 0 => 0x412a1c8a026410038725802e97c150402a979c5049c2700c8209600d0724a9c60bb7a10898ec4130400e0d82e97815059c60b9c21d1c1048c6978324a9c4de890264101c80e581c20ba5e0941671c1471410700725803e4a82e979c21d37b048980d83c4a872979c0de86905c121d4100b830578a01541704c103182e969c6959c2951c01d00e578080c25e713b00b80e0c0c70580904c10579c497868719c47081e0b8d096a589587457830038041ca5e7000803c1671b7b04874709c00b83097c109fa80579c49780eec2f00d80a08006010020041704c10de95ede37a57a800241671c121d1c3041c0de054241c497b7a719c21d280014170482e9fb7857872703b0028060803600801058490495edeb7807b7a7187470a800104d05c14714121a15e70073042e8702520382e4a836dea8855936c00c632412dfc10df0342c09a2600ea2286e18de0c8c60a1349584a280bc26836a2074bab862f382718284d2582d0a01d020272860e2ec10b869400e4a3784d8bc0c038562861d2e87000ebaa920b936a2156108361d136bbae855a504caea4b378a20200a2861d0dea1a880a04a038742f3862f38227aea95c10df0982d07408288a180e10b860382000038a1936de0bc0d80e09a76a1838979c9041c8ba9c27000e09a76a183897a880c80e00c17048c6948267203697836269c2038260e276a1a5e7209b041c6701c
  | 1 => 0x1360c0a0a1b7810898ec04a03412009370402e0d8a0dec160283608006014121d4100ba860c13231a5832032718342709e979360e036a18320396031b862c132319c63209e0cb864d8384b83670832a1960038c6e18bc1a92e269c21d08012b864dc170487e008260c1c24d92a0c928a1b78318150582e1d1c0004124d9280c92a2437a31c1704a864b07e038544c84a4b936240360e254262e80d2865800e32386e089ee009c9509a348b428160a1ae80803e7080e10b862684a0307400412a1936ba0302837810898ec04a03003048364dae80b8a0dec1602808080060141504874a1ae80b8304c868ba2543203c718480d0981c89e979364bae89503c0f848261c21c84a26874979360d838ba286039601a3860e0369509a1d2e870a865800e10b87048002c8364a93607928de8d01004203bb007803048400d8d04db7b05bb0028360182104a86deb780f04803c10030725802e2825f05410712e8700001c8349400e0b960321c697a860003403c14944103202e581c69784a03bb10480c0d82e050a097c16719c3048001d0320382e0da50319c497bb00c80e00417048c69402e0d9c49784aba0d2711c00006a5803e1d0729400e0b9c29784a03bb0034120d82e2825e04417050a01a1c6711c2004121d2500d83c038987007297bb0004160f00e94068264121002e0d9c097c1670ae905000030020ba5003c121d031
  | 2 => 0x260711c29b82c0401ea1a7c33048982ee0402d0482ec70369ba7c558724c0460b8490531d0480a0db7855aee07b1d04810a182c122ee9802cbba601200104a86c737807838060344d2523204828096eb8cc2b2e6e2036940100f13407b1c4a13857b78bf038060304d25a310482809e330acebaeee2036950101202ec737c4b13857956bf2ecba9304b95607b78c70680615ebf0c4e037e272e63201e26886eb810333883304a044120b0c803287039c81226096252711be4a020a1b780f8cc1204a03049049c8c7036de01e96256711c2de05ea19be0c0cc122ee1282d0480cc71560d9c89ba7c1c8020031ca1c0e17b78120080800600aee1241504c0ea1b1cde01e0780c0200212c1408006a1c0edf378331c21200c0200617c1400c12a181ede0cc6f836940100f13407928c713857b78bd836950101202e4b138df31c57956bdb82e009e270c40801eb986aeb81033388268480400c11a86109c8082601e00c0d9c8de0740787803037039c81c8741207802809050020028703874de0481200a02003058470528703b781081e964140d84802b78331c60781e1200c020021e0470500aa1c0edf378331c60300800c141228703b783301e1200c028081d043058023341407a86bab786f89a01b7c124160d84303aea100380d9600d00ea18c8e189ae089f0437c26036348b4708a0580200f80ea1842e189a12874034120
  | 3 => 0x18120a02b388b98344c8c4948c8980967193827b88120380c034310c84ca522589e333aeb99c6e20303100c333ae04848280a6e22e60c12e3125298138259c226b8812038108a00c03e520c44ba522589a333aeb99c2e22ee1a036ba83007804940100312c57928310a012138de2e60d83807830eb8cc040c4e20ac311c6708c827830e20484e0380d92e079c20c3ae3301031388298c47089a0c38812138134164cc141292e0413104868578c44e0487181003412122867d02e2826104c0e0b836709be002500d28604048321c6981f41e0000d010944123240e0ba8671a60001c67102e6fa50a1810121c298069058100000c0141294037039464b02e120a02800d0580004250014124b40e518361a1c60d9c20002ea1a500c010120c46fa603202a711c26fa60a18344b0720b9c6df024719c46fa601203ea192c1c9c20bb7c120c4039c6711c2982860c12c1c9be0bb7c0d9c2949bea18c81a01002848981c6949c6711bea18680400698048709c60d9c2a18c40406800a60121be0d9f40182000c12a180b03b78718680d8020184703a86de04270c167d00a0d8200180304a8607b781a1be708070583703c121a37c10036940100f13407b1c4a15e4e378bf836950101202edf31c4b13857956bfb803237a270960801e1bbae040cce20cc0d010014129bc0e32254a182c121c8981c4721be5226e0b01007a861227c33
  | 4 => 0x612c14582860037cde820b91c22709607820eb81033048e200c4e0010495ec70a0de01e0d81eeb83033010120c4e200c4e00457c0ec702e120a0df00257c0ec73781a01e0d8380d01eeb810330c8e20ae321c22683412138e202c1a413038044e12c5783412128de0c80d8384a9be0d01e333ae040c8e20ac311c2321be2583412138e205e1a4144c4121292e4a8110395e321381203812034333ae068c82bb880d8480e01e0d3ae33010323881a31d0580c4e00057aea283780783626aea07bae330300404831388c700c4e00457aeb0382e120a0df002c715f03aeade06807a70eb80c3301a120a02bb88718344ca563226027aea4e09ae2048280460e03e9c034321329589e26bae331c6bab882689e0f820e213871848e037a270960783e11bae040cce20ae718c81209e0fb884e020268960f820e21386f84826b82e009e2701e0f842ba896eb9be33010e20a6311be120960fb884e0200d86e57b781a81e1a036709be078040d28604254120c871a601a01e011c6711be95010a184870a607187804287039f41a2600400505c129503d038364a0400e0480d0cc063ae320ace2148333ae0484829b880d83894896122e607834333ae040c8e209e272e62681e080cceb9c204048e2068c74124e00c0015eb98a0de01ec7138030050495e1202eb98a0df036c700a020200180305c141a41257ae6de01e0c0c4033ae330
  | 5 => 0x110c60db7a5804b058301dc1208958df28608bb0028200180105877048361137b032860880c018001d8450483703160dea860300a0004a08821058365840cdea86088040e0769ca5472072108300e076ba8725604801a881daea1cb7a1204808806a20441037aba81ea2094088721db7b03272ba8482504800a8903044102eade81e088040a0740e254de8bc10a6e0da727112a098760e2ea0d94e1109408876a237b030449c836ba8480e045050430312aba840528b4088a012a529c12a1caea2e288de8361004a9c0244d0b80ba56280c226a88de836ba8720e03607a88a1b7c09022de8722e0b82789c4d382e02501c81ea1b7cb928808842978220912a018940109a528722e12c0e036de840b903826836baa88578221da7257844104160fc14a201f0304aba822deaea0c3af030385637c1d0380d84a26aeaa215e0882e1ca720e3ae0200600414a22eadf37b0304a088061280c0280015c16a2036dec0cba95e2681e128000e15e081bc9c84a0300a0200613416a241457aea0892a2680705839050481140cba840949c470a8610160088341ca7296a58719c41c8407203e08286b9022582721cbb00b82207c120dae430840de96012c160b9581cc12b9286088c2df022ec00a0202001c161cc1400412a1840df37ab90941c82c10036582e455022de822030080180a1cc140004104a865837cdeae47180c028090580
  | 6 => 0x836b9288de81e1c934100360e01ea1a88088be52934131304b82305412df286de94aa20601c8400e036a20220315e9c9c80d838a215e088769c8761c95e11041050350481f03288088c8de8761cbaf050310315808838df03600038579bc0880ca2272720360e15ea20221ca721d872eb82202006004150480aa237cdec0cbb87a0880a1d80c0180015c1253836a240cbb95e1c80c0e0080184d0541257a880892c1201803044a2041031c807a680b076031587226e0e27c1c8380200600876004121ca88dec0c120480241401800114121040cdea880784803008018021c840004150495e079bca237a4d14a6f0a0b929208aea1d042dea880d84452aee9526e08aea4b37c0c038562861d0bc27aea958944d3830337807874a2022a18430304495294709bc5182209b7c9ca760e076a1a890582200c120c88c948c6721709c8760dc0c11254719c8109bc0e286098769d88ca22526f0270588d032761d8361108c098570487608c0c9da86df28894876724160241223286bb0440888c1d97009c0c9ca86bb416111c60c412709bc31c0c720324b08c1da86df026a20300cc17048050307631a86df1bc088260b0441dc0c0d8389d9542c05672273030446f01c0e2864b0b071866df002088289488c1102703038108362f37c9c9c2709bc11286580221da7296a50718366f076720200f822582869c8221dbb00c81f04c0c
  | 7 => 0x4150480a2709b03094281601137a1009e7181e03417050062789d03094281601137a1009a7081e1089a0189400bb0280221040c1141207b7a268065802200845034124a830df040ec00a020200180105b7c28415048441040cde81e1237c08c15048a00300a9c89c26894bc16103044de89e718401237c08c142800c01a730589e27094bc16103044de89a70840011600084504c0c4a83cdf04096256711c2941bc9c960de8221d80a718720dbb104b7a2815e12022ec41202076dec0c11272579c4969c696020712506f1601d8749cb7a08806708721227208c150480a711c3031bc5837a11040718761c82207bae02006004150480a5837cdec0c7187a08bb0028200180105877048361137b0315e1227208c1401c16719c5031bc5837a1104070838eb8080000612c1470960df40cde82070806580444ac0d0483c10022ec00a0202001803058001cc150495e078406f37a0b0301d8389ba7c560721d89408872a240c0b272122ee1202c250021140c10288de81e0a934940c80d0bedf0a025038a1b7ab90724d14a088a09492a1cb7abb8bea2036102ea95022528480c038bb92c56286df0720a934968be0b8a03089ea237a0daee1caecbaa88bba86120221c94a529304b8a0bb2ea94872a237abba860a8400d83807b7ca202a1ca8608b7a2f8c82802a1c840528be2fb80df8c82709adf286a237a0788208872250480
  | _ => 0

def word127_3 : Nat → Nat
  | 0 => 0x3c10022df00c1d839032721c818280300094694b7c0e0221da720d1c632072eb80208c14df03494831030c80e272121c612822a2412030489c8302815ea2416088020c4120ca523193e1da72579c408838030721dc0c0c0489c81228417051c6009c40c1bc0e0770325251874df0229c83e70872eb830008220fc1494842df40c1a8389c84870c120c1bc0100c0092c1cc0c1da521d146120a09c818711c3030c86f0344b1c6df0921d8749ca9904816bc40c578304fc161202671c12709bc31c0c0c0321d15e4b0767137c9cc0c6f0480f86a0e12c70b7c1d2881ca72a60110495ebc0304e417054121200e719c4708c21d02e5792c1c9bc0c37c2525058286df034b937a120c812822ec4120314a0d8a01237a040360e0949404807b7c58286b9034de8223209e2712e03382e02502681e28286df160b91c20884212842ec4122500c00836b90a007b7a129600312a01412a1830122e42837cec00a0202001c16df001050a104a86deae4078c80d132df2502516027b7aa1ae4718729780c013b1048220b8a04b09452872308361037ab9042253b10480230836b937a078384a83407b7a58076028c871872969c6962527112a941bc081601d81e1d37a019c21c808018021d801048725837b0304905bb01580a008200180104836dec0c1215e0280800c14580001db7b0307208416ec04c02808080070515f049bc1202203
  | 1 => 0xaec00a020030587305000a1c0edf840b900c0d838a1ae45803a030380200202872004141040ea1960b91c60300a024161c96105000a1b7e6fae4100941100c00841032882837a07c1403076014130303828072df00801c1428038000450484103288de81e0e0361d81edea880d022578c82c0c87137c270341214a1d82d0314a011bc4b0760d12aa2072de8c81c8360e12807b7ca21bc0d15ede822320bedf0c86f0940d04852872124144c0390312807822a20c8528604c10c08c15048784bc0c4a076de94a1ca88120380d84807b7a5803408a863209a2792e2500ce0837033787081e580a008a861084a10bb104894030030301e2837a0d84a5800d0480412031030a0a1b7cec00a0800600417048362837b0301ea1a882500c00844102eb030a0de81f0580c0e41401077032ea28072df00a024162800600414a2044102eb0337a078380da880795e0f8221a8760e036a201e5783e0886a1c80c0e04801800a2044bac0cde84001022951609c87650034320727184a08bb10480cde8489c83628016ec412088040cb7a950c69b8769c836711c69b842079c4b91bc011601d87408a549c83e4e87270af00340c6f0a058044971c60f14010022a18940606c9c81e1a40cbc16050042253b10487608b7a1140c07a720daf00340c6f0a058044971c20f13a100729507425012a181e9c961032f01093a011609504504c0c4a8
  | 2 => 0x185871a87039bede1c22400505c127040ea0b78241c0992f105c1207c0ee0379059f40280608001049bede09105c127028200854719c2a1b786f890960360502ec7130e015e4f156bf0c4dfb7c260c826ae6eb892050cce30780100c01876950750312e1c8a0128045816a9504503c0c0f12e102f00340c6f0a058044971be0f13a10286100121b01e58069032f01d13a1e00c0d8742837e120101180c4b804a184303ae4080a0df078030060d87503ae4078a0dfbb000800a1c0e0eae41200a024162800211c140028703842b901e320344ca502528627960b90787187203004ec4160b8a04b07230836df840b9256ec40e0e8a0110410304807b7e1e00a020030515f039bc1d048ec40e110410337e1200c01006118441040c1081edf8a00280800c1600414118450384103042078485780611c0c1081edf92e01bb0df40e110410337e1212e018485784703042df81e0e836ec00a0200600c161cc1457c0edf81e103b105844df8402801eec40e110410337e2801eec40e0b8761c83a30848ec001038761cc0c0e8489592ea2074df836230442e8264d258312860c0382809c23074bb076bb93210ae44a2881da860988c110743109e2501ea22860e876230360e290a19601003a0d0781c846109610582f052860840eb90c21cb7c1cbb00b81f03836b90c21037e0e036a4160a18400e8301d07200a8614c0e0e8481c83
  | 3 => 0x62ea2583e10bae331be0538c298c46f896e313c1a8200d86e1a95ede03e0e0425203eeb812330a029b8c0e03694896b98cc0d3ae050c8e304ac741203000b9832578a0de096e0b7c9489e2609a082e60f8cceb8a070814e304ac700d049280202f042e6578a0e0416c700a0182104802014102415eb98320e030030c4333ae060a02b38cb993294830310c80d09671a644f09ee30380c034310c84ca522589eeb8ccb99c6e30380c00c310cceb812280a6e30a0b992e948303103e1093c259c29909ae3038108a00c03e520c44ba522589aeb8ccb99c2e30360e030eb8cc050c4e30ac311c6708c82793ce30920e12e0d9c20c3ae330143138c298c47089a1a8424f38d05875048000382e4f1280c13057b80314165787e050544cc121092f0412c310904f04a051c70480c7d2860b8a0994130384a708366f8009402e0d014a18c871a647d0780003405412940c90382ea19c69904b05c120200c0013103a500d82e0c814280a00300905930004120b8329440e0503612800719c06fa500f814a182e70a647184a708360002e0c014a1a50311be990821e0c80a9c2701be990344c2860b9c6e007c091c6701be0f930a1a640b9c2e00747d412052866f82e994161d4130400e719c2700c40c130a19be0bb8096a5471a526f83205006991c22425a71a5610a54708c40c81400a646f8900d8020184703a86de04270c1670282
  | 4 => 0x37aa19c61da729dae899a541105632416b940c72272280220d88c1d899058221d0b20101e72076230a0098361127705822564121d2ea7207628016a188c09a66562ea079c803004719c256ae46f0a02608cba076a18770589f0484226c0c2503c1b08ca1a761103625038b92860980c5827672256951c8709c025286b90260d1609dbb012c165682f04c100dae430826de83801836252e470a8658026032767225a951c67009472020b903ea1826582765804b0583104a86b902656380ec026028200180505c120007f0437aa1ae40980c0180402c120006658410dea86b91c60300a014160184a5800104286de820b91c297a649dae4941c82805471a5e99276b92503205505c130415abb874baae8051c8150362800e09a5e97a649dae4941c828054979c299276b92501a8421541656412bb80e1d2ea720542828605026994170482e7200e1d0c215014280260da76bb9c6ba84a708360000ca1894b9054721c803000bb9c656074ba9c2ba1c01fa5e568a0a189415264b925f0582e1509f0484226c101f898b90c29da86242f07225e0da64028000e05425160a189eb91c61985504c107182a2805c26898b9064582862f866bc1c80e0200da645400600160252e415286269c2168389589a0daea0c0cceb8143138cc700c022eb0395e4f02e2838105b1c0280601002bac0e24032268a025b8c4f1be0f84226b82df09e2
  | 5 => 0x360800601417048550415e098270589e1d41212842268b3030042501e1b15e11098702761d84a120442680705874eb803034120992ae00300bc1627c121289a10836000745789430a766f13028026028200181e0100105c121d4101db7ae040c1fb7a0c0444f8769d86c7009809b7a0c0324f07e0b8c29d9bc25026dec162789a10a822800c014120c895032f0230981115e70280111c0260561b41627c12268420d8322800c002f0578946f07ea01c01f9bc25090308541b1c670a5a95a506f37a07a761d032098041d95e700c21fa5a71a5670a5470276de8a00987457832001bd059c670874014120c9bca0c0c1f95e1d9c0ec00a0182000416124120db7b0301e579c6a00747080415c1704c0c6f06c579c01dc1671c12708740c800579bc1f826ec00a0800601417048001fc10de95e6f2800041671c121d1c30407e70054579bc24134968c20b82a280be27a88e0036bbb7a0e0364d380a22860a826de8be2f8a01f82a4d14e308c8280be53882308bedf89adf098322e4a188209b80a237a1f9340e036a2286098be53a5e1505c9b064198be0a82653a569426e721c20d9bc1202607834a19609d84aec4120c8760995ade83696a5071a6e0d9bc121c8098200f81ea19609d96012c160c4121202656380a1c16ec00a08006004120db7b03048a181e1200c0180019c120dc0c5837aa180c028001281e084160d96103
  | 6 => 0xc70276061c270076321bc0d13071b8024a760f8384c07470b801aa7705c1205875032f0578304fa7608c1671c1270c0c6f06c1d83c1d15e4c1c00c3809dc17048141d2f0578304f27705c130400e719c2700c25782e1d1306f030e04160984b048740314e0d8322837a050380d89e942e4e0160a1834de8263214e10c161280c1d41200c100d832b90a0deb82df250a1b80b91600f8261a84253c161280c1d0090483104286b90a0e000d0587e27c121089b04098252861d2e40c8a0de87e02820018050580104c101d286b90320e00c0bb80a1b7a580a0309c6e037ab91329402e308c8252760d14e278c23202e0d1329409427b8058286deae471c170494ebbaea09a5e022524c0320b8740312a0d8c22837ab93b09780c020260b8a1059310494e0c8c20db7ab912e30a501a82e0f9c2250749d84a5389a53aeeba826992580080c0c02e1d1304aa86280c2e02e40e036e0026a182ede960308be309c6de8c82794e208380d92e70b8009a865802ede8c22e074309c2de86a1289a5387d05c1253802038304a82e4c286e00c30589f0489a10836a182e538c3059330492e1283609a863094e97854703801f82e098903094f05c12a192c098544c84a4bb7abc14eb90909686c71a5670a506f0742801e098765780470276969c6959c20d8261d02e578009d8c26f3b01580a08006008010584904836dec0c0795eec00abc0
  | 7 => 0xbbaea0d95a0c00e2715e0ba5e71068bb836ba8300395e26072979c0028020ba5e54aec712ea70ae870082a015c258ccde09e1cae671a5e03a7e0ba800c09627ae671a5e03c14258020289d0489b040482603033280b989e9f9c6719c29f8822785c248ac979c6708747000800aeebaa805689c259c4b98909780e9f82ea00302589cb99c49780f058020209f0484a268980c410a00969f89c57ae6711c470280270542e890979c6711c00b80600aeebb2e81c896de0cc26ae6708749784a9fa800c09626874b99c30509c2580201c10120980c2803304ab989a9f9c27184a70a7e1f09a1386a29a5ea000400aeebb2ea2615e25868702e61c8380db7a5803409a863214e10c161280c1d41200c0c0c8a00db7ae0b785803e09a861a84253c161280c1d00904831030a0a1b80034161f89f0484226837030940c87428286de87e0282001801058370487503032a192e10a540f03e70874120989d84a5389a1d8380db7a0f286099601b0380d8b41d286580200988c10c162781f0484226c0c250361b08c1128705bb0028200180011036dec130303ca1c1602412030021d4104c0261dc0c948300c8a0a215e2800c0213000c17048260c033042530302612410033801d839030309d812280a10440c00b801da520e0269d86a0f9c21d030283ae230020983e94c1103042e00381aa76708741204a0c00209a761d95e0f2524f86
  | _ => 0

def word127_4 : Nat → Nat
  | 0 => 0x49c0a0c0ede072bb0790502e06c1103872333782b82eeb8080780400c141cc1001c0e11b78332eb05b1c0280201c0ede2ea2431c0095e01c0e1a37807aea0e0090501e0107233007043780b842bac14bb410ba40eb986e570780b8249d09ede072331c62407cbb836b995abaa740909cde15e0b9c41a2ee0dae6baa740915e263781c9c054aecba2e602806711c06f8cc5709e1cb78269c6ba878094141f09c120982580602c100fc0e3309a27a7eba87871a747187c7000801aeeb99be56b782709a712ea240250589e0dc0e258060203e2695e271c4ba87d0509d04048260060083e1f0cc268969f9beba874094140f87d040781c89a0baea1d048268061cc101b82f03aea1a9f40100808006028020002f05412a19c703ae820b780d80a020070582e00800119c30504303a86de0207d00a02020018020041705412a1ae86fb780bae6572860406827872981c654ae602804711c26f95c262861a2e8279c61c94cb9806011c6711be26286de06826ae8708730583d048000dc0e4a2e81c95d0501904c10330720bb782b31c09c1224410b995e0b8bade002208080181e0100a0002f05412334101cae671b780dc16c700a080060100000c130409057ae6de00aeb8080081e01006004170502e33410082e670b780db1c028080800600c16004141a41257ae6de01f05413042ecbaae8570303300e1c89e0ba5e71c1624412
  | 1 => 0x8001d2870481e6fb780f2ef04b1c578327102ebbc1257b1c101c00bc121e01503a860b83471a64bb836b983e4a2502702e959302695e0cb78712eae037c26048018381e2560b89a0f8ccbaa7e0d806958142686e5786a0faea4f038e037c26048018cc9587403a7e26aea0f937048101e2870382e0d1c698036709be1e2e60f28694128262544c86827b780d072ba1c6719c46f8680f2500f928262869512e26b78ba072709c60bc12a183c7d068de27eba00d05c120f037038724a2e810382bbb7eba8364a0749409c25a524c15e0c82e0c378712e6bb8680daea1d1280f2502615e0ba524b0961cb780c1c0b9c12c7006080040080b03b78bb890eb8080780400c140bc1002c0e08378332ee0095ec700b03868de01ebbc1402006078050480b040723302ede2ee20aea0dae656aee0d27a0a89c0bb78579c4bb836baae60d27a0a89857b781c9c00ac122684a0d80a0240e25834a109e5789c712ee20882710727028427064240b10509c2780a01c10120982583503a84128ccbb89a9f9c29f87c129c2268621b8af0509d040981200a0083433284278966faee20a7e708826f896170922b02001804008007d0370482f0440ea1882de00a014160b8360080011c1010c0ea1b78081f402836080060100105c126fc10de2860baea1e2e8b995c0c81427a647189054882ba878ba00a021c2b99bea095c272ec279c6244170
  | 2 => 0x16c700a0d80600aea57c0e0806826806c7416df0401140cba8481b89a018450306aba84105c14018022789d03094120cc26896111beba841054125701e028022709b030943309e1b096b99c61a1c671012bbaecb91bc120cc11040078a70589f0509c0780600c0c250cc1b09a25ae61a1c212838961c4012506f0cc1b06a4b012950681d37c29c150480a711c3031bcb98cc1b1c61a06c1a02c0f3ae02006028010500304b7c331c7032e62100305b1c028200180104837032e61b15f059c7051c401c0c6f0cc1b0687087402bae020060080105c147084a3340cdf2e608416c700a0d82e008200195600412df15e1a2e66f03c1237c9c92cbb2ea061c470ae46f0cc110402b048df27208c15048960080a2709b0309433044b989e718401237c9c92cbbaec049c6712e46f0cc1104029848df27208c142580201c162789d0309433044b989a70840011c6712526f9c2a18484b0240f2e42e254df0720b0087d0200180202c140007304a8703840b91c6028090584a00807050460028610c0edf020b91c2089f402808080070587305412002866fae41000c002861e1f503a5cde03c71bae1181e01003040070383ede0ccba8361b80201c0e57b781aaea0d86e0095e019c103b781aaeaeb80807804080cd050070403ede042ba9c60d8060800200078a1c127d40ede03c9700c01836008007084703a86de042028360800600
  | 3 => 0x24a9648fbc91069206d23d9a474b48dc7119cc2309645bac8ac611409225da44524881610eac21a5842eb884f69084b20dd64163481f4102ea2035c3ffb07f370fcac1f6583e6b47c060f68b1ea523d02c79560f1281e05a3ba3876668eb2c1d3583a0b473450e5471c8d038dac71060e0891bede376286e278da6a1b250360c86af58d48d1a5d8345ac68040cf0919bd4332a865b70c9ae18fd8319ac62890c2cc1829a2feb45f070bc4e175102e6305c058b6ab16a962cfa459678b0ec15ed42b8b856360aaf0151d429ec852b70a3b11430e282c44f4489d6f1371026a404c450974912c6424fb049390903111c2222fbc45078882e10cde2123441770812f0fea01f52c3df607a6e0f1521de403ac4074880e7161c8b0385506f6e0db5c1afb435248692a0cfe0197b83215062ea0c350182b02f9685d8d0b7d016bac2cc6857e90ad981552c29f68524e0a11413d24271604cae095dc124b823b80456e0875c107c01ff503eae079da0ed341cd60382d06d180d42c19d7031ec060d80bbbc168602b8f0535a0a0381326824b104514085340fd681e09039d806db00cf60186802ed8057a80a560132c0235a04028076680d2e016e20253403d4006af0099600dbc00c60000000ccebb7d0303e10836010021bc0e57b7c0806b05c145601e258020189e2740c250cc1b09a6faea1a038eb808018001d2eb050ccdf40c10c
  | 4 => 0xf54999b53265263894c4da983352f94a5e0b4b96096aa92cb82576c4abd6952352975a518b4a05c939a526a4a4c2b49596925ad2406a46724885890ab1209623fac47c5a8f2251db523a2d4711c8db291ac7233cb464e68c03d1717a2c4c455968a5c513a5a25ea4496288a2910a5a1fee43c62870310d462190f42e5a8564509b52122b421a283aad06a720b8b4145a8224103482048e4059880540ffaa1fcd43f4947e438fba39f66b3ea207cc3cf8989ef0e3da9e7adb4f4e49e8b13cd1079628f2251e30e3c29a77eb4ef069dc693b69c7662cec139d74e3ab107522ce9979d1483a08e73db8e6d51cc6a3964e72940e4271c68b38a5670f24e1561c12c37f5e6f738de069ba6f3711e6dab8da769b34b363d46c2acd7a49ae30358586aab0d4971a76f34b1069234d1759a18a3409c67a30ce8619b89334ce6661ccc549978a32c9465434c9b41926a322526403cc71798c4b315de62444c374985cd3085060cacc0e61804e2fd125f5b0bdf597a8a2f29c5de2cbb16174b02e5545c5c0b7b796d892d8d25ad24b515168e72d01259ba0b2f69644b2c5d4586b8aff495eca2bb16570acad65959682b0d255d30aae8153c82a596545a4a82414f4f29ad253118a5c7149cc2909051d28a304944e72881a509b0a07593f8b27c5e4f1289d869396e26f544d9b09a78132f3261124bda8971592cc82579c4a8289467926ed
  | 5 => 0x4eb6a9d638baa4f750e2e9941d227ba26e74156e7d55ce5539b7373210e6041cb05394d3724cee4649c7a538e1071812e2bb9c4943882d70d10e1631c2073824d7015cdfba1bef537cad6f61ade5bdbbc7b75ac6e85cdc9c1b83736eac6da50db0a9b578b68c96cf60d96b1b216362ae6c1d6d7e35aef7b5c0e6b492d64b9abb7355b46a660d44b5a7c934d4969850d2cada4e53488c68e14d1729a2453434e68320cfe359ef7b3c0d674e6ce0419b07b3432663d4cc2ad97a9b2ce66585eca92194a8b273164a1cc8d3590d731fea63d5cc73b98d96b198a6308cc5e198b6731509627d4c4ab98874b0fcf61bd4c32b18596309ac61054c1ba982d7b03ce60422bffb97f152fcec5f6d8be7b17c36af6ca5eb1cbcf3979072f0485de90bb94176242eb495d45cba1b57366ae5345c560b82c16f57adcd15b556b65296c052d6c85ab9cb502169832d24a5a216b3ea967382cc6c595dab25296406ac66e58954b0db960d82bfa857d52af6295e242bb4d5735cadfa95b57ab4cd5665cac5b557e62ae4d5595caabb154b42a86f54d16a94b551c4aa26c541d0a7fa54f6529d8c53816a6ab14c96297aa52cd8a53ad49c42928b52254a3fa14776a8d4c5179aa28ad44652878750d54a15b941d4282aa502d2a013d3f33a7d884f9109ee213d442798e4ef969d9a93a95273ed4e4949c42937e3a6eee4da4e9b1393546a68ea4c
  | 6 => 0x103c00681004101034007c0000040418280018281000002c040444040814300820140808001000086c1c586c10080400001c0810000020100c0030541c1418000418000804041014600020500010000000143828302c481024043404dc1c44082cb000141400284800600040880c1400180000107010182408240020280c30bc1c2000089804001024180000080028002800800c081408580c1000000c080034001808303c34cc18241c20000404040c00640cc12408000048040000001c001004086c3064100434000410000410001400041c0414240c000c240404040034000c001c480c3800644c04000420005400000510040800000418080000181c2c1cc0044404000c1c3808001434044800002c101400042c30581c280814340010240c0410040c00000834180008003004f101a61fa8c3d2c877570e92a1c844381086c230cfb61928c303085c590b2ca1536c28cc84e9f095c611a7c217383e1f074ce0d68418d082da10533e0975411ac8205303c2a06e6c0c2d815190243603b3c068780b53012420147400cb7fedeff625fe39bfa117efd4fdaa9fab9bf3137e156fbd39f6c4bec6d7d59cfa431f3c8be5697c8a4f8821f087bdf287bc5cf71b9ed573d8eb7af22f55a1ea353d32f7a292f40a5e786bcd717969cf2631e4093c5d3786e0f05bddfc83bd8b77854eebc5dc683b6cf769d2ecf3dd8f7bb00975dd
  | 7 => 0x200c0418d8140864dc3400acbc1834601c003804006c141000d4041ce800100808001c245008441c0c24bc4c385d14000889c0c8040004e03c00303c04901c0400041808741444003404040804d0187404300800800c1804040818000d60000094001038080c2010003c38000050509c20280000445800040c100054100834340418000470140408019404004424603c007804042c00bc008c202804a440a84858b91800007448501c1014000ce02c0028140804bc34ac1c100858000800040c800408302420002c8c00140000000890080054001c0000502004000414049c0c184848141800003410100804045d08001c18d838048c00087c3c240c803c18ac002c2004440c240c48350c001c000820380400003c2c00441524082c08040800000018008020f80c0014001c1078846400002c001050580000502c10cc0070044c043c142008202cbc00240000001814280c3018683ccc0c5824101c28d014342468003800143400001818186c10000400001000040010102820200074000068040018002c3094504800645420203c0c140c100c04548c5874041c4054100000180c081c380004041c0c005c0000383c04080068102ca808041008481810101014042008045844000c0c48481c2028147410100c00041c380004205890640404142000342414081400240c0c140000082c2824442c0888280000100400240008
  | _ => 0

def word127_5 : Nat → Nat
  | 0 => 0x8334c87cdedc85c084400e66c5731d9eae416227dc7a339049ee59221667ef105b0c68d23c08e09141a4f6d502f70cd721c46845848b91bc781cf962ffe522539999fa6cd195836e3993de9278cb5e4b285257c8604289d1cb9fc72557cc27cc2c4cd395c1ce5d7b0e9790e21346dcee97eea9035010dac2d2e228ef5c4d50d17020aa7025a052edc86d0f8da250c72a9788bcc743d684b67f7fc0003cc3048b9645926acfcb1069bfc0022a3b6d4cd3fc001f64361815848e2dde8ec04a7cb05bf761a2e9744bd23be9ff529e97fc0002a4f2182e88aadd7631a26c3c7640df11537e1b4fe057b49e3b0bb559fe9e19a99dd03fc002e99d28d094ed938c10b7fc0031c64c6847bfc003d47bd98e7f7a050193743298cbc5205e20d40c45b03e78112804d2798ba3ac3fb59391d837410424ad47d9262cb4fb9a59b7fc001e251bfc0018da9fbaa468a81e55b4b1cdb9f2653b4c255c77bd005995087b91765134335dfffc002926791cff521323b411956010a0093e0357a0c38baae8b44734a151c412dcac591a6608e7006817bfc000287d3fc002d5b3ffc00209f1654a5bac10ac6573fc002ce15c0c7590cd29ec2ccc08042c70104c880c040001b050045c20040c00081c0c247420040010d0f02000f401042118ec280050001d24008a0d00240c00018040000c10000c0800881828ec1c3c40342434404c5c18202000
  | 1 => 0x3927ac8cd1098a1f2d3824531e20d2dad77c51844486e8fe5b7fc001617b0bac2bfc003fc0012d72ffc003fc0039db7cd44ffc20a42161bfc003fc003fc0007532ffc0019c60b6dafc4552bfc0022d467fc003fc002d110a196d5ec95e763f3fc003fc003fc003fc002c8ecdfe833fc003d658ffc002513d3de1f57a37d8277ffc0003eb1914cebfc003c8c2d2deab38a67fc00386b2234026502359ea7eb1d4c8d7846a4bad981bfc0035420c2c8676d191a1898482907c62661c5ffc003fc00238cec2640945e74954d915423fc0007e6ca52b464e43b30663fc003fc003fc002589a8826ee5489bfc003fc001726abfc0003e354f5d0a8a4743cb4f889cb6675d5dd6cd661a6cdc178dc9b4d68fe2244a39e606e7789de9625a9dfc88834110b0fd6bf469738edb50d08081443404c0eacc2a496b80487c29f13b235ffc003fc0005c493057a25a59f70bef307a02167b6cba8e4d4205673fc0031a607fc003fc00142affb628b60e5de008bfc0020c2c4cd9e744cbc0c3b7fc001dc843fc003393e111093607f3fc0021251e4aa533c29e589db594ba5d85a8a5db79586c4c8eddb0351c7b5e99981ff2958a8f8d54d9043b50effc003fc001d49f846515f069d7ea4a9902c98018ac7e8dea24d9443a2059e2815fe50fd0667390686a9d69532795953244e7358d4feb14061ffb1dce603591143cdcc82a26933126b7e7
  | 2 => 0x1e3fc8dea53199ee17ec04be380ec2485cbfc003fc0035c36f984a448dad501484893b705a2c5b7b9ebc84e9a7e83c92ce44fe097d6ac2fd0ccb296d45b8b89d0fbd65bb998269347fc003fc000124a554ea1c5e870925acd7bd00d9c9d831363dd9a9d80dfec01bbc325021a29409883fc0010caa305ccffc002cccabfc0019a96b89da3fc0028d683fc002f5eaef1f63fc003cc74856206dddbffc000ad95eccabffc003fc000b520f42379b2b611c68d619fe9a38bfc0026c42148e1e59d8f754fefa33c5a949e88a351c720a558a89c2c9ffeb4298e65e4c642766a8da16350cd5efc8b3366f185d44be26a54b0ac12a3fc001e668ad9914667dbfc001722bcc64faa9c05d60760956bac4165223bac4f4606ce82bae40dbfe1f547674249fcf456fffc003fc0007a2d4bca29b2552bd5c980072223d115eb26c3ce50c1bb0b73483a5f8ad57e848f06c1f0f67fc001d081a386895db14494b1c40cffc002c85751687ea1f9aec8690627c51937411fcad6ce9562818f23b478ffc001469051debf3477db42a59c67ffc0029a154ea14ec0534a294ebc2b09097278de0c9cf326c2ea56f0656b5208134851b2969e367b25907115a99202aa36b657533bfc00010d8b411c6c0580b821e70eb6c4ef3d92a4599e2f885f4df7fcde38d60727d66ca085816ab8bca14a0e2bfc002787868411520cdb5c2c8d0e6dee603544c
  | 3 => 0x9a66016b1385f62e84672bdc3e06336547a8a38cc3a040a9735709d149cadf82b5167490e0911f49a358a91d4355990c637fc00044563de149d9e6f2a4202ebfa962e6e0693fc003fc00015c1ea2a77fc002f5978d111e0ea0cf2ada244e38e1866848df5e1f45417fc00008eb3fc003fc00288805e80f00ebc3ccd6ef89b28a9cd6961e5c606104d49a04d46174f587f5caff484ca5d2954135cb269a0a9bc2d721801f3113069033e249b45c0b2c24529c05e38461c939d2aa5cd976f3e68dce9896e4f73dec86e9f3b857ed4ce40ca048d54320d489cdcffc001f54005971fd940bd6bbdf23270cf1d728c4ae1c6d27c7fc0020093c31bdf7165dc929d4ea1d3e1ad35462c179130f6a6a27674f5b82c5d1e73b606d73442a3648dd0fa9194e4657a7fc0036c327fc000a636db5e2edc69461aa52438c649345d51611baf1276df5081768f1869207e4064e1be36183fc001ea82bfc0037959e255f81a281b9451198032cd00de8a2e955014fa180a26320b1f025f11ee8cdcec8ebc6e9131ec5b5f190b5ebf354b37393a4e4e53509cdbd7c9bd2436238e123f9a2ba75c925087c0211815445a2de6360eae5c59b6160dce5dd1cf63603c7a1aef092aa62acee6b6d9c0faea42e50fd56557a12696303324ac60fd483414f0d865b1cbfec00f7b887021cf9cac056011fdc39df13e5a58cc6847734bb3cc440fd6f6c91d2
  | 4 => 0x4a2a5e2b3d5b9ba2af36bebfc003fc001f6278b20decd3f6b1b98dea40b4f9151780320bdc5e3284f4d9e802d04332587a423e2dd677768ab82750019e89278cec817e5cdfd5aaca998972bff19fa64194c0c0ba4844635a5d407e1a186588c37fc001d594811c5b4ac36e65cd450601a2f48196406197fc00239efae88c7fc00174fb661231d80551e56ffc00268c4dca548bcae4c5d2c315dffc000d6bd08c39a8d67f7dc6e0c18506333fc000a4bd012888dcd200276bfc003a5023a0593fc0026975c601332a496c8176f9d685622ffc00170960e899ac8e13fc000997c2b5cfda1016dd836447ab902e550f8e255d7fc003a4595be376ccc68a49fffc002a97b4764eaa0aae71724c062f5489cc179e91cb9da0c2d22dffc001b5f1d840997a5933443bfc003fc003c9e5dbd77b3c2420dcc974ffd69250648f0d0a4fa19903242b850e928c12b0012047d9f88866e368992129232e60b7ab8cf93a6210c6319574a4cbaf6c5f874e0ec0360d6599b18e26444f6080e4ab2a48e4a10511b577678e3e750124e5f12e0da3dfe54a2650254014464b542f20570899d4a467be04d3256a629d5041366b47faa4fd0ddd9aaa895614aac5fa01a160a12f95652978143ac71a0ccc1096268d10fad1d82d6a86124a0a09e14e66dd14ac6863fc00341b850ac6ed8023fc003fc0010442ffc000d055ca1c0e65f8e1e25d48dc78
  | 5 => 0x15e9b51a30768165dea17e8930411e446ab42c717fc003fc0029d7b8fd16e385e4a196fc0b88e17667a5e075a2db85c795486482145a5fc1c23da2c4564c0a8693c59317fc003fc002ee037cc334bcb2138cb35a0f9ec81e641e2701571170779f6f362a768d810d51869be68eaa2f091f1509deab5922983e4acfea3c0a29c410f311a4e5e48e809d886092de5cae3df0b7915b1ddf2ec22c418eb4128a92677485baf9f3e6561624febfc00034cc849137751f350212f58d3fc00219319d8ff3fc003fc003fc0021266631549f95e528b93fc003fc003581f7fc0002da1b9ce1b6e5d0864eee441bfc003fc002dcbdbfc003fc003fc0031c74cc61084616ffc0003ac6415a0298822601e7fc003fc003fc00020b4bc95c668383fc0039824d3d5f76c6d800ee10ec3b255cf4a8a64d4342e8901265a0c68291fd230de7fc003fc002b0f13fc00264527fc003fc00345711848effc003fc003fc000e54fbfc003fc0027c620ba99275a0bfc00018a86be761be8050ea72a99c890e57fc003fc001e20cec026abc0e65515c04758ed17f296e815a4ffc0032a575acc797e247fc002a56c3fc003fc001ba720c53ba30fa5518873a2e1d28fea47a7fc0033e90d28d7a8c6c7d98179abeef0a61312f20868549ac442c23beb3c5d46e652d6e07c5bc45ccd701b87824d8cb4901f88e8435e7edea99898faf2bd7d6a07d8dd110
  | 6 => 0x1ed0de38301e6483fc00102567fc002bc0cb68a101ea0bfc003fc003fc002ccef996ab3b23f5ad955b29601d06ea93039c397b0173791a7fc002647ac753508cf03fc002395e322881f8a402eaf53980b6621bfc0020952d3d105ec76dc89762475226640b827c15f42666dcc9d379dfb0aab5ddd399f65adbc6501e8b97653a1ab4e1d0af8426d9c92814263fc001de9187472ad8457097dbfc00398a2f1dc6580f416d2d0d0110d49642487b58b8f8e8f850d3aaca6ffc001e10c206b2f0140ce691ffc003ad96b418b9d875c01473fc000e92441a6c4b29398d2cdec49492733fc002a291084b67e11b8d1acc6c98cbc32dcd3282903cec253388f98873661c52c598fc91a3154c08cc6e2cee75164d484f3e44d99909b5c60d9dd282a92fae7f2b123d98f5d0a11dca2506438bd2616b5612e45f3702bece455763eb45454169a179024a90e495379964dbfc003b4b77fc002d4f9404846c02082d267fc003fc003fc0015d95bfc0012677489995ae1d1fab93fc000ea36526acbb809d9ce5ba8af93a597fc002ba8757dd631cedbfc0008c8bffc003fc001321df3d5ea9d45fc455a01d5e30f481e2540a953fc003fc0012c7b575669559f7fc003a07b249690e976bfc003943e1e56d19d7166653c093a022727dc0e971d14a4051ccea831c8fdd0fcbdf5ffc000e9201060c96843fbcbc1ae73465896e6535f4e03fc0
  | 7 => 0x402461d263cdf44a0a1ad423a8c120d4e6a45abffc003fc00224f1bfc003d93ed21842de2b2fc54d6a74d7508d019ac88049381dffc00149d33099b0b4a0bfc0038084c25d7ec6b8695127fc0031e6baa45ebfc003b8669056fa2828df0aeac66e1e99ed144bbe608e798a5e5f27fc002589849431c60c01a15316aa386c4be11f4bfc003fc0033d046b9fafa85aaf82dd8044821b3a48727d243c123094c539b64b21d3fef1d93fc003fc003fc0021cfe7cd55991eff497d02593ffc0025a86fe0efffc002c0709645d7fc001a836baac1490bfb98d5b68ac6fd2bffc001fa09bfc001ee05eda4a8c4514924bffc002a827b4d8729d59179a449d38572b307623ffc000be01da93afea3d87ab73e8917fc003fc00010b5b72029618291897b7098a50877cdbcef680adca98c862bcc7458d62d0a12c56be010f2f08b2e3946b2d82c402c37cb69f15b364e7bfc003b07ddecd1d24fe1e820599b2b4ab7fd264b16b76ad7fcc27e8e19f2d5729e5b1e4a0b9453715a84c92aa7fc003fc003e95274ccb8be06e455d04a1dbfc003e564bfc001b61eb1d280dab06c8e0a91276986c9156ac8917ba2c4c69f7ac010208bc9c8e2410085012734cf53415d93a80c65b8d30c61a8a70b963c42191f079f12ad578f7ba2af0cd753291f978f3e66341b62084919451123fc0026ea65f299c3622aa87f5d850f253b46c364f0ecbfc00
  | _ => 0

def word127_6 : Nat → Nat
  | 0 => 0xcbe9140dabd74e1d115e0aaa3e717121b9c69d029dd20171bfc003fc003aca7a8670d0e7b9d98ee081fb710f17dd43863bfe5433c8008b2b7a99d07a25effc003fc002866309665e3e972727b408df0865798944ee52995eb82869dd880ec15806f1b80ea9f41dc768858981e0ffc0013667e294e9a17e3460086dae714aa73e1b2ba1c1587057c9f72191df6334e9ca23499479f2bfc003fc000acab82cac90c585f0a8ace8d44e0b7fc00244a74e053ffc003fc000ec946bc489dda87fc0014cc98d44ebfc003fc003fc00111e0954b5f027e3fc003fc003fc00149b6bd42e33cd66c154eddb73825cbfc0014d163c62cffc003ea508ba10edc0deb66fb7e0d4e91857cea5f591af27aaf45ffc12b54079bfc003fc003107c889773fc00248de8d0aee1807ed061ffc003fc003cab405231148147969254a8100c7569064ad0848219da86ae71691489bf2ed0bd70c1664f097e467fc000866f6fcad3fc0019663dfa6affc003fc00160a57fc0007e946f0fdf1644cc29acd833868163e548ffc003fc003228e702abffc002d807a348e7fc00290219fe58921f20719dd869e3a2afac920585c9af1c7d7ea35a0d0c657cefd53b4d3aabd0a72e5c4266b000e429234e0e5a655df5240aa8e0d0e09218813a41be068a3470fb10647906b0bfc000b5da5ad018c24cb3a5544d8aef537de14c989234842329ca039a636ec0d6
  | 1 => 0x9fa40861f619e5d112f0e142922d0943a3aa81665c36661f7a6d46d9cffc00318deed526d0d0c5fcb19080e3fc000a67bfb2346d0f9fe981c68a2172bb2ec9a65124d942b42eb56fa8da3424a64065e1b565e0326c5ac48ed1c02da1a857fc001f9ef3fc00271623fc0021629e4e87bfc003fc00264061854452d96250a5e29fd578b3e162f8d827710d2a21dd7dc0bc5a6b7fc002f62c53279c76bcffc0023c35ffc003d22c9a60ef68952cd9bc369335c0ae0a07ffc002797d782321a95671e5ebfc003fc000a0dfbfc00398edf3de1378bf1be77bfc0034dd27fc0007651259a3a681b841fb7ad9c09983ffc00318ddffc003fc003fc003fc00101fd8167f9fc88ffc00249065eaa6bfc003fc000be73ffc003fc003fc003fc000418b3fc000567a25a6da19d8118b11619b846639d05db55cc69d8fe146b181b27950a0b621cf48b89e1f278083922401830bfc00239e51e402bfc00085b7566198543d2f116be615a9231609605d8891ec6fa146b56616a84a820d9104e085b09bd1601a9819d2ccaef66a08d0740a72ec602e064991ea96d91e84cdd9f266cea866d938e2048129fbf75c36a0eefbd650e5e346028368c58be793ce1c8fd07d2a1a7ad0fbd414d356433905e76459c958f0e2d094d975c98151f85d88341dc2cc15605450a783ba3c71d69a3300bbb1c390d4e6198272fa9b2a5477fc0030086f989567
  | 2 => 0x7d703dbfc0007224abc6beade5bfc003fc003fc000aa287fc003fc000a55fffc003fc001c42a3fc003fc003aaa8aad49bfc003fc002be7e7fc000a5522e857bfc000852dffc003fc0001c567fc003fc003fc003fc000255ec282bbdd8dffc003e01fe3a7d7fc001446015e441eeaae1eb8ffc001a2b51883b0d57e5e029668b42cd13c701283eb27fc0023a987fc003fc000d96e26cee9414bedc347fc000c1dac4ababfc0032819bfc0034213dba977d86bb3c710ae680da8cbe65b8262edf0387fc003fc001a218e3da1cd4a6aed4117e9aafe711065aaa51a83a82c3d4934eb1fb5863213cfb5e66beaee6918dc5cf7b52f40a55ec28b23d6a1d912cadfdcea5f4968272c53355fba45d3e0a261b631c428c21c894846f67d7f878c881d34b855aec9bf94803639d5ad93950e3d4428e3dd6c76d83af2401c9e021e505b50aac6a2ae1874fc7ce0d58a54cf548150d6858f0db181eba5588e8130da483b19c8bbc645018f23d7f29034ab6764a4d91c68afd40d006a326d856ed089448033e07be27581925e6a1e1b56db3ce72d801f8abb4f6445e921f69f910a1443118ab0f0fbc88005f94a01ae0ea91fc58cd48ff507fe196de10b819c9106592fa1762e80321c9e5c24e2c046df85e2fe083b4f761a6d1f8f56e8d98b4ca5bd05b8955f782d5249c7ade714df7648ca0e056df5f0c82c0fd9278b14dc794e26d256ce
  | 3 => 0x521fc369644b0a3ffc003fc00075425369ef9c7918632bfc000f2a3ef100224cd7fc003fc0018d654ec1a9b5de0f533340f0581229657dffc003386108e13bfc003a900bfc00206bbbfc000c40fced1ef8dbff308aa22b68893dbfc003fc003fc003694042018088b00e9c17fc002a22b446b4be1b4551ecc15c03fc001517ad1cb15c9ee7822ba25ea3ba0ff96007e9029067c2f0b7dc849ffc0000cc7efe0ae86b121ce06a973c9e45cfc30e6cb6f4a93551663682024c73b0831a45e191cd4c127a4327d3fc001245d2886affc003fc0031e0029a1ec60d7441bab79c55aa6eaec4ec9cd3d940391d8b7fc00169507359728241231e46d64fd4c99ffc002e536a3a92921ca71a1196dd38541be14e3962705fd6bc66b88ec5cffc003fc003784fbfc003e9b4d41cc0e4d3415944ecc40984ae38dd469337cc654e0b56ade6b36942955f390d841847c4804640f7cd10f7fc001b203b54be786a23dd9426a2a8e54d3fc0020da0d74dfe98c07a86abfc000849417520885cb3c29c87403c28d44305effc0028402d36c3054e93d890b6a7fffc0018e89a68969e14ef153c88e69f36022f270a95d641472d7ced4c49affc003fc0026551c7662aee819d03eef6625ae299f6995cd0333c70e3666b964701cb84c2ba1911cd4528570b24615a0f960331d4bfc000c4733493fbfc0008a685fa8cffc003fc001a190385355c43
  | 4 => 0x19e23fc003fc003fc003105c3fc00070a93fc0006c28802837fc002d5e4e98b51dccf2407d7b2853baa6d5234b485de68453fc003d679bfc003fc00281c47fc000de487fc002f2430d0d53fc003fc00044789c4bf518503fc0028c04e9da91d0b07b4db7fc003fc003fc0033818802670c278a65ee3fc003fc003fc003fc002686ffbc3e808bd558d07fc001f4b99c12feb46e3fc00201a4bfc003fc0007e86ab81a3fc003e186de9eef5c1ebfc001f07950d0c9c8f37fc0001dd97fc00314fccd8af6b0a4b897f7fc002bd75669d13fc002e6143fc002d13bd1e4a3fc003fc000f8832d04c74ddc7403dffc00164c225d573fc003fc0019006aaa064edce5729e74936eb6c68a55bd09e7b713624e72bfc001d9f2fa85a7fc003fc00288f8b0c743fc003fc000f8126cd824c816a327c8c1deefdcabfc00319b214a75536a9e95f6a41929668878955494ebbd90b2c4e8f7ec43090db8ce9fc4ab431609611c2f5742b1923fc002b5b2c79eda1133f0930a9e3c9d8484f08c91434f0a56ae18c3da352cd638f88cca2bdbacdf6e1418aead1a48acf0555b54d545d77fc0035652c18411c8905383fffc00095b9e0466de87689c2f1d20c7fc00222583fc00088d33fc003fc001e0e4ebe0277e964ce54d1cb47fc0025df03fc001c65b10690b6e7968c16c1e609fd1728a60e8ac48cdb6e5097ffc000f608bfc003fc000fc30
  | 5 => 0xd1ad81ffa1eb9f45458308248c0a449c97444b624e76a11392e47d422c30a03d9a88e65c929d8c59865c903bdca83d154a56caf17c94d095a495577ad34d326c11989258bbf569c1b6b9bd4b3af061665a8cb65bc2cd624241fb1cb520ba5ad90dda784c20a080f2661a2a5ddab941048a8bc7aa2f454c7964620e83a8246fbc0b55df4e90f8174265b8f854129141d577e12b6c56805e26353eadd81336c268d84dd89d7dda95e1d1b2150cc2b951cfc7fc002423a69e533fc003fc003fc003fc00031de7bd19bfc003cdc3ffc0000900575e9d1950294c5518a8c0c6ed028ebadb960eac664721e9a6d24ce2de955123a014d0bfc001426104928c706a39c3c0ae4b7d0bdd113f0c2aabe59041ec53ce2715ca0c3cc50997ea91f3382372ad9336927e3a1faf4fbee93d445bec6e3aa70fae41698623ed61c269548929e57fc003024ad9aae3fc0029c41fac9489d103fc001548e07585e8a179f0f3a05547fc00195b93b135bfc002349eaba017fc000e13125d2da2988bfc003fc00040373fc0034e172b62db812e6a088820a50d5d23fc0010d079649ba68760cdfe3fc0031ccde8a1a8706a7fc00281f9c587eedec1ffc003fc000dd8a01a2ea9620354b63b9689851dc31e3d893c4193c20e488f9de901c852025572748b1ddac5049d23e4761e598e3180d1b44f73fc0033c4a9c859ca1f73fc0023c1eeb48a7fc002
  | 6 => 0x3cf708f41cc97fc000a8fd8588daf4c1e54b1d9eb36503ab74ac19ea864a5a3b43aea8c492c4ded5b596040fa9975f4fc061a34998e4507e529f890e30084287ca069adeb68d2affc003fc003fc003ae093fc003fc0039103b0abe5a8d8cd8f462476466585a0a9cb0adffc003149f16d3dffc003fc003c664ffc003e911bfc0035da059c63a09ba4d55134ccc524d7f7189c055b6b8ab35eb3ba48dfd9ba1a2213fc001d8135b2b0150353fc003fc0028dfabfc003fc00122223fc003fc0004166691869ce9feb1dde2556ffc002ce89de0b314e71e3df537a17ffc003fc0025df36901c86921a91035727713e46a589d1691cbfc002edbb5d8e37fc002107b98aa4ffc002c5a7f5061acd694f69ebb45495604979b05a073fa0cfeb97c6402fbfc000d895948c651914fe80a2a200ffc000bd0bbbc83ffc003fc001a1f6720bc64e3b97297819cd735d848a8f45180f0521508040f29ba9e6a582873fc001f21cf2541c8006cc5733fc002f001788b9dde6475482d2a6bd4a6fd3d6cbfc003ca30ec855115448b096c46490ec15ec03d73175b0568e79db7fc003fc003fc0027a3c60d19fc18f7fc00258ae3fc003fc003fc003fc0007e5fbfc003fc003a882bfc000dc1a5a4f2ac4ebffc0014de05462f3fc0000891aa6655cde8e747024d53f4c2ac895958d70e69f580e8b7d22141a044c64ddb5ef6414ce7e822b94b68
  | 7 => 0x1508909901100509501100509110d08901b39909101b39508901b38d08901939909101939500901939100501938d00901938900501938109101921500501919500901919100501911500901910d00501909501101909500901909100501908d00901908900501901509101901508901900d08901509100501508900500d089006cc99044a47fc003fc0019c6f3fc003fc002baa633244aee1d7fc0031dc9d28da7fc003fc0026852971f1871147fc002816e7fc001c8c5c0c37bfc003fc001b5b0e8150bfc002582eeb018d9597f79a4211a6bfc00249df809b5e2cf9aae3630ea0281a3e7e958b178e5dd7aa54940813fde4cf1cda8e85063017f7224df94a28eb0c3d4af39be97a8df659fac6a7b54ffb18c3d914f61a41b258db1aa587e71a0dadca5b65251e3092c671d7089157e8902689a2f2840b5479c59c581c82ac4b008fec4d38af8ada89429e9bf4018bd2c095edcbe3104d04ef5d500d242fd00a30b9bd56963218f15ee85fadf39d9e9aa2745726e5ea18930e886490d9a3b1c9e175a26d948c0a42cdb0c9360e8030cce1d6effc00070642f585209b41217ab1449822166f052f84e9bb53b3fc003fc00035b62f8bcf04ec7025636c40bfc003fc001e1b0bfc0003407619796255ab98c9e8da630629309736941da02a54cd9847c63e2e95d655362e49ffc002e9799fc51db5f07363ae822a3a08b69d821ee
  | _ => 0

def word127_7 : Nat → Nat
  | 0 => 0x1939538501939538109139138d01939138501938d38901938d38501938d38109138938501929b38909129b38501929b38109129939500929939100529938909129938900529938501929938109129919900929911500929909908929909900929909500929909108929909100529908900529901908929901901129901900929901900529901508929901100521b38109121939900521939100521938109121919100521909100521901909121901900521901100521539100521509100521501100519b38111919b38110d19b38109119939901119939900919939500919939100519938109119919100519911901919911900919911500919909908919909901119909900919909100519901909119901901119901900919901900519901100519109108919109100511b39508911b38d08911b38110d11b38108911a01908911939909111939900511938909111938900511919500911909909111909908911909900911909500911909108911908d00911908900511901910d11901908911901900911901900509b39508909b39108909b38d08909b38909109b38110d09b38109109b38108909939901109939900909939508909939500909939100509938909109938900509938109109919108909919100509911508909911500909910d08909909500909909110d0990190910990190110990190090990190050990
  | 1 => 0x941939100541938909141938900541938109141921500541919500941919108941919100541911500941910d00541909501141909500941909108941909100541908d00941908900541901509141901508941901100541739101941738909141738901941738511941738501941738111941738109141539100541538501941538109141521900541509909141509908941509901141509900941509108941509100541501909141501901141501900941501900541339508941339501941338d08941139900541139501941138501941109908941101900540f39501940f38511940f38501940e21900540e11900540d39901140d39100540d38501940d21900540d09909140d09908940d09901140d09900940d09100540d01909140d01901140d01900940d01900540a39908940a21908940a01908940939909140939900540929900940909909140901900540739501940739101940738901940738111940601909140601908940539901140539501940529900940521900540501909140501901140501900940339909140339508940338d08940219900940209900940139909140121900540109909140109908940109901140039910d39938909139938109139919100539911500939910d00539909500939909110d39909108939909100539908900539901508939901100539839910d39539101939538d019395389
  | 2 => 0x1d10d00741d01909341939100741909100741901509341738110f41539908b41539900b41539100741538d01b41538a01b41538900741538501b41521900741519900b41511909341511908b41511900741509901341509100741508900741501909341501900741139900741139501b41138d01b41138501b41101900740d39908b40d39501b40d38501b40d21900740d11909340d11908b40d11900740d09901340d01909340d01900740939909340939901340939900740939101b40909909340901908b40539901340539900b40539501b40539500b40538d01b40538a01b40519901b40519100740501901340139909340138d01b40138901b40111900740110d00740109909340109908a41d29908a41d01909241d01509241d01508a41939100641909100641901509239938109229b38109229939100629938109229909901229909100629901909229901901229901900a29901900629901100621b39508a21939900621909908a21901900619b38109219939100619938109219909909219909901219909100619901100611901900601b39508941e39909141e39908941e21908941e21900541e19901141e11909141e11900541e09901141e01909141e01908941d29900941d21900541d09901141d09900941d01909141b39508941b39108941b38d08941b38110d41b38109141b38108941939508941939500
  | 3 => 0x4c1b4a60da4306d218370cc1b4660da3306f49436a4a1b523494532492992494c924864924324919925a4a925254969224b48d24a46ed4a676a333b5099dba4aed52576a91bb7488c684c6350631a93069218349cc1a5260d242cb149258a432c520962944b14a102a4881d2840c942054a0d894c6cd25362929b148e3ca491e5218f2904794a23ca505c4862e6940ae2985694c2b4a615a430ad218570cc2b46615a330ad49456a46138a609a5304d2982690c1348609a3304d09826a4a13523b7a535bd19adea4b3152598a924c548e62a433152098a943fd019ffa4affd247fe923ff48dffa44ffd227fe903ff481fe94cff4667fe92bff495fea4affd247fe91bfd48dffa44ffd227fe90195298ca84c6540632e83196418caa0c6550632a935a521ad284d69406b4a93395299ca90ce542672a03396419caa0ce5d2672a93395019cba4ce5d2672c93395499caa4ce512664a433251999284cc940664a8332749992a4c0b4464cc942644a1eda40f6d279c2334e111a7084d38526b8a235c5498eaa40759281de928ef48c0c94c064464a25325349528a4a94d234a291bc34940294c0144600a7300741802a0c01d2600a930054980288b5d446aea0357539abaa4c004460027300349800a4c004433fc9410f4945294c2946614a928a548c2294c114467ee92bf7492cc88d66426b320359949b41d11909341d1190074
  | 4 => 0x25ad25356921ab48cd5ad25ad292d69496b5a475a5236a453351299a9a0ad45056a692b53491a9a44d4d226a6903534829294d49d05a4a82d2549693a07495255ca532e741572a0ab9d255ce922e740d72a06b9d2007a5303d2981e90c0f48607a1303d4941ea480f5287da033ed019f69ccfb4e67da903ef49df7a4efb527352909a9480d4a4e5ad212d6938992184c8cc0d48606c9426d219372509b1287c2133e3485f1a4f3e4869f2334f901a7ca4d2952494a904a549e52a51295283b2921d9480eda50769283b2941a5298d3a4a6952534e919a548cd2a411a5248d29046949e34a511a52829a4314f4a0a7a50088a6042530212981090c084860423302349410a4a08d23042918214a12b14c954a64aa532552192a90c954664ae92a554952ba4895d234aa91db929adc8cd6e406b7292cc149660a4930523982904c149e60a50f240679692bcb48de5a40f24a6792333c9019e5a4af2d2579292bcb48de4a46f2d2032203193418c920c64506322831914980490c024e60169300a49804a4c0252601242d7921abc80d5e4e6af293371299b890cdc4066e273372419b8a0cdc52626233131018989cc4cd062628313141899a4c4c526612433091998480cc24e66128330949a48a492452192293c914a0dea486f52137a94199298cda4a665253329199948632a49195218ca93c654a09c90c4ed212769086e298369
  | 5 => 0x90c2529a128cd0950584e92c2749212a0726522392919c9488e4a42504a6286929434847094c384661c6928792983c8cc1e4466ca2336748db3a42bf4a65fa232fd4157fa4abfd2154a532a511952a0aa9d2554a81aa748cbc94c5ed252f6908b92985c8cd6a521a229290919885a400e4a6072530391981c88c0e446072918394a1f488cfa4067d2733eb494f6a467b5212ba530912981894c9ad217ba031e1488f0a4e3e4a61f6900892984494c22446112938252981294c0944604a2302509812a42095284c25326109931a40f44467a2033d1399e9a46f4d237a293a0948d04a425d4a6162530b24a02894c1444680690d0929a8488d42406a12930f119879a400746603a2301d1180e84c0752878a233c5019e29ccf1d210922333348627a4b13d2589a92d91486c8a416452771693d49486a4a415252763e90ab141559a4aac50351282a8940d44a030b50585e92c2f49216a06cbd2188692c4349620a4b60521b0293d3d4869ea4f394a69ca334e5496e4a4b2552492a911c7490e2a4871d2238a911c548640a4a674a633e9299d494cea466752127a4313f48630a4a374a61ba330df4943a90c1d446ada92361219b088cd8d246c690d59495a094cd0505686915314917c90cbe4465f2822fb4917da42b64a65b282ad940e44a4a6d4a636e929b5494daa46454a622a33117482b514d5a4a6ad24356921ab5a0b5a5
  | 6 => 0x2981494c0a4860524302909814a420a5287aa033d5399eba46f5d237aa938eb49523a509e44610a430851992fa50614a624e928c919a09a4b04d21b62235b149a6aa4d355049aa924d54026aa40bcd258a692d8529ac2a49505243d6921e9490f4a447a52090a92c8548cada48404a620233103495c090ce0d2368a53345199a2a0ad1d2562a433154126c94ca04a65023328141541a4aa050323e92aef4956094d0dd253a4938e74968ca4abdd258ae92dad29ad6a496b524b5a905ad482aaa495552012a531c249c3894c1c5200e4940714a00894c0444649e9424f4a1dd24f324a6992234c909a6480d32506992934c948246a452352191a9412e2189690c368861b2430d91186ca4836d201b29045d11a2ea45175218ba9405d11a0f10d0748683e9241d4920fa41075206ba4335d119ae84cd752653a2329d0994e80ca752616a5340748c4e90c274667ca131dd490efa503d4861ee928f748d2c90cf3d2579e92bcd495e7a46f35236ea53375219ba88cdd4e66ea833754989a88c4d50626a930d52986a8cc355251aa91c1b494468cc1946401a231292186890c1644682a43355219aa88cd54266aa932991194c84ca6406532931234946094c30466182928c148e05a4ab850356e91ab540a18a070c50186690a95298f8a447c527b1a5358d298b094c58d252c690a91298f2a44795272a6908fd2987e8ccded2361e
  | 7 => 0xa432f52097a93cbd4a1de84cefce677a733bf49ddfa4eef92777a93ccd09a6680d3350699a934cd48266a508552819a530cd218668cc3352519a91bad299d690ceb42675a9320349c8890c2a4a615243277495fda4afed2496a924b54865aa508352441a941b9298dda4a6e52537291c7d4923ea431f528302430c62986294c314a618a430c5218630cc3146618a330c549462a47034a681a3340f49606a4b0352373253399219cc84ce652695a924ad48656a412b52795a941f749cd7a4a6bd238ea924754863aa411d5278ea9416f49c5114c284a6142430a1218510cc28466084530412982090c10486082130414865ca4b2e52497291cb94853880c9cd254e691bf3495f9a48fcd247e6913f34891884c8c4064629338d099c680ce38e671a7338f499c6a4c8748643a3321d0990e80c8750643a9344b48a1fa452a5248da92157486bea415f5276fe91d394829ca4ec4d214fa5327d1993ea0a9fd244fa81c2929a148cd0a50585692c2b49214a070ad228569149d490e6a487352339a90945298a290c51d2528e9087d2983e90c1f4666d24336b491b5a46dad216025330121980a0ac0d25606923034867a94d3d486552532a921954a0aaad25556922ab49154a06aad232fe908bd2985e8cccad216569032b48294a074a466a521352948e94a434552557a82abf4955fa48afd2457a81abf48d5fa04afd2057e90029
  | _ => 0

def word127_8 : Nat → Nat
  | 0 => 0x48647a2323f492d094d68486b422322d29917a0a8bd22ac25356121ab09cb58525ac290d0521a8288d414e49da434ed11a769c93b5249da434ed11a76a48ea52375690ba948567a4ab3d2559a92acf48d66a468ed2347690a2529913a4a89d2144e904e929909a48e8d2474292337490fda488d48646a23237492ca94d654e5b2a5359521aca88d6552472691a2929915a0a8ad22aba4355d392ae94d57486aba72d5d495a5a40884864422322341111a4953486a9a2354d392a6a48c8d254325321b4150da0711d2588a92d89486c4a4f62527a8a90d4549ee6a4b73524b9a92c714908290c4146670a4338748d8c90d474865ba432dd1996ea0ab7d255be922dd40e6e90ca148650a3328541543a4aa1d2450e9228540d6290d0ed2587292ca1490d1a4a68525342919492184094c2048610233571486b8a4f5c5276da435354869aa4f4d52760a432ad2995690cab50555e922ad40ee0a4b70524b8290cd129a68a4d345059a292cd140e11a49084a684282c2349611a4908503846900612995094ca84665420345b4822ca414b5255d6924f149547a48a3d22232330552982a8cd4b525a5a92aeb49575a48bad035d281cf149678a073c4a69e2334f101a78a4b3c5259e291a8f41546a0aa3d2551e9228f49147a06a350351e9128f4880a94c054a602a430152180a84c0552102c9381549eda84d6dce6b6a93db549e5e
  | 1 => 0xe5fcff97f3fe7fce7bdf79ef6de5bdf7bef7dedbdf7beefddfbbf27edfdbdb7f6fe57d9fbff2fedfdbf9bf77eefcdfb3f77eefddfbbf3f66edfdbfb776dedfd9df2fe7fcff97f3e66eddf99f67efddfdbff3beefddfb7f7f2fecedbbb7f6eedbdb7b7f6ff5ff9df77edfdbdd7f2bf4fefddff37f7eebddfbbf77ecbdd7f2bf4fefddff2fe7bcff9ef3f67acf79ff3de5fcff9ff39f77ee7ddbb9777eefddfbb777eefdbfb7f6fc9fdbfb7f6fafd9bbaf77ecef97f3e656fafb5fabfc7fedf5ff3fe7fedf5bfb7f6fadf5f6bf57f8ffdbebff3defbcf7b6f2de7bdf79ef7defbcfbbf73eeddcbbbf77cefddfb3fe7f8ff5feb7d7fafb5fa3ff7eaffdbeb7d7fef75efbf57ecff9ff3fc7fcff9bf3fe7fcf71ef3f74fedbdbb37f6fedf9beb7e6fcfb9fa3ff5fedfdf7bf67fcff5febfe7ecff1ff3fe7f8ff9ffb7f77efbdfb3fd7faffeeb3fe7f9fd1ff7b6fadf93fb3dc7fff9bf6fcdf9f79ee39ef7defbdf7becfdfb9fe3be6fcdf97f3fe5fcfb1be77e67d9fbfe3be5fcbf9fc33fd7be7bcf7bef7de7dcea3fc6fcf79f73f47f74e923a5491d3a40e95206769233b480c5a4a62d2173e90acb496cea43405259fa43167494b3a42d6d2267e922d74916ba48b5524aca43565485a7a4154486aa2235514928690d43446a1a922bb4955da46ec52376690bb148569a4ab4d255a292ad348d68a4690d2348690d2129a909ca8f
  | 2 => 0x37e7bcfb1ff3de7dcfd1ff8ec77f5bed75efedbfbea6fcdf9e5b7f77eefddfbbf7eefedff3df77edfdfd3bb6f6f3de7bdf7bec7ff63f87dd73be7bcef1fe6fcf79f63fe7bcfb9fa3fd7be7bcf7bef7d8ffbeefbefbcff9febfebef77cffcfedff777eefdebef77cffdefbbf777defef3fe7f9febfd6fcff6ebdf7baf7defaff5fef75eeadd7bef7deebdd5febfdefbdd6febfd7fbdf7badfd7fb7f5fee7f5febff3fe7f1fe3fff3ff5f7bcf7f6ff5eebfb6fedf7bfb3fedffb7f6fcdf9bf355ef5d7dbebff6ffd7ddf3bfe7befdef3dfebdd7fcff9bfbaff7defdbef7f67fdef3df3ff5febfc7f8fe7fe3dcea3fe5fcf79fa3fff3ff5fdbfd7baff9bfb7defecffbf79d4fdcff1ff3fcfd9fd1febfcfd9fd1fefeefdbfbbf77f6fedf99febff6fcff3f73fc7fcff3f63fcfd8ffbfb7f4fe8ff6fadf5bef7d6fbdf7bcb7defadf7bef7def3df5fcb7defbdf5bef79ef27f7bef7d7fafe4fef7dbfafd4fef7defb7f5febf9efb7f6fea7fcfe9ff3fe7fcff9fd7ee7fcffb7f2fcff5ff3fe6fcff9ff3fc7fcff9ff9ff3fcff9febff6fef75efbf57ee7f9ff3fd7fcff1ff9fe7fcff5feb7e7fcff5fbef79efddebbfe7defddbfb7f6becff8ff7f67f8ff9fff6feeedf7d6bbfadf6bebb7f72fcff9ff5ecfd8ffbb77aefc9fb7b6fe57dbfb3f7f6ffcbfbbf77efedbdbfb6f6fedfd97b6fe57dbfb3f7f6dfd9fbef3fe7bcfd9eb3f
  | 3 => 0xe7ef3fa7f9febfe7fbdfcff3fd7fedf9ffbf73fcff9ff3f47fcff3fef7cffbdf7ef9ff3fe7f5fe3fd7fadf9ff3fd7fcff9ff3fe7ecff1ff3fe7fcff5ffb7d6fcff9ffbdd7bfbde7bf77aeff9ff3bf77edfb9fe7fc7fbfb7fabfcffdfb9ff3fcff8ff9ff3ff7defd9febfd7e8ff9ff9ef2de7bdf7bee5fcdf9f63fd7ff57ef7d6d7f9ff3beb7d7d8ffdbf3ff6fadfdbfb7d6fafb1ffb7f3defbcf7b6f2de7bdf79ef7defb9ff3fc7fcff9ff2fe6fcfb1fef7dfdbfd5fe7fd7fbdf7bef7dfdbfd5fe7fd7ff7bef7f6fadf7bef7df7befddebbfe7fcaff5bebfd7defd5febfcffddf3bf7dcfbefbdfabfefddfd9ff3fcff9ffdbfbbf7defd9febfc7b8f76bed7fbd9fd1fefbcfe8ff7f7df7bedfdfbb7f73fe7f9febff6fcffdeebddaef5defbdf7bef5d7faff7bef5defbd75eebfd7fbdf7aedfd7faf75fed7dabbdf7aedfd7fbf75eedfd7fabff3fe7f5ffbf57ecf79ef3de7bcf71ff3fd7fedf5bf3fd7fcf7dfabf7def3dfbbd77fcff9bfb7f67fdef3df3fdbb87faebd6fb58ffcdebdf378ff1ff3dc7fa7f9febfe7faff3ee3fedb9f73eedefbdf73ef6dedbdb7bee7dcdf9f7b7d7defbddfb7f7deefdd7bef7deefdbfbbf6ddcfbd7b1ff9fdbb9f73ee3fe5fcff1ff3fc7f8ff1ffccf5ff3bff37eefdf3deeabfc7fcffd7fbdf7defd9febfd7eaf75f63ff3be77cf79ef79efb5f7bef3baf75f63ff3bc7f8fe3fe7f8ff9ff
  | 4 => 0x1c1c81725e50c08a6c4c20e53084125e501c9bc44d80e408a6c09a0f5e2007726ccdbf80714c0e598a6c4ae06c1000715605c0c1404d89ac1d3c46620e403a6c4ae9ac09011072298532574a00e535bc44d80441092909801c088126f25d0268940724e470ae40382980da570400900781b128090ec40d4d7030078ac12af105840c726069058241582545840c03ee4d048244ac28104b8026e4c12b09d412e009b930156250ec3c481a06935a0b048094041392e8132140111c801c4a0065c80e455c590364dd2bc5901e091c98043b000de240d81801505824851164113c481b0301200660003ca1b7f04c97c123930302c1c00264bec001240d02ef10a1b3304c011800037890360639300acce3fe7f8ff9fe3fc7faff5fe3fc7f8ff1ff5fdbfb7f1ee3fe7f8ff9ff57cffbfdaff5fcffd7fafe7fddfbef9fe3fe7fcff1ff3fe7fcff5febfebbcf7cff9fd7fd3faff5ff3fcff5ef5feafcff3fe7febfd7f9ffdf7beefd7fb5f6be9fd9fe3fe7fcff1ff3fe7fcff5febff3faff5ffbf6bea7f1ff3fc7fb7fcff9fd7ff3fd7f4febfd7f3fefbf3fcff5efd7f6fd7fabf3fcffbfdcff9fe7faffaff5fe7f9ff77f9fe7fcff1ff3fcfd9ff1fe7ec7f9ff3be3fdadf5bef7d6df5f5bab7d6fbddfb7f6f6efdd5beb7deefdbfbfb6f6efdd5b1ff3fdafb5febfd7faff7beb7decfd9ff1ffd7cfd9ff1ffd7fbdf5bbf7f6efd9ff3b
  | 5 => 0x6f00303303806c0180200200206c0c600e4c032094100180800f81b03001802600e4c0302a05c825040323780cc152606620b0168271c809c1602d0063901502a04a09d3033105a0b07202a04e9819882c05a3907201041001801b311c20941382c05a00c030e1662390718381c007c2804c2e80e45589a02eb91ca01b5d6f141003907403c1d03901e19c2cb9407203ca1bc50030341001d3860e40339400a011c98200420e5380214be9aca240d02e0e45585901ee500d82078a26d281754e00e40c0202889ade28390cee5135bc500e081758394e2019ca14378a0800e80500800c01001000e51c9bc5789036060a97885d04a0390dd0302c84c0b2984342520180e4a226b00e4d1bf84c0b2984772520120e53594400e4c5bf8944a001ca22577889ad05839098e522c80702205c72174128de41c9395c82ac0da570402ac0c01700e511c9bc407295d058070dc5d00c01715699c1720b412125e206e2e80e837174030825e20274168241abc40dc5d0088590725102683d726f1003a0b6fe0552ba5000e25054bc40389ac1c8071520e52ba6c036080038ab02e061361404d6f101cb332ea01c0aa570729ac08a6c2724e52b9754a20541ca6c6669ac1000702295c0a8394d89ac54839156054101391522a5280414d69b008bc407205826007022055bc974128080300e30724e5720a90360712b8394d850c088208180
  | 6 => 0x601c1281b4ae018724280144ecbb0250263900382a0c6b922d8068b22ae2c01b4ae4e00f82a27601c0980a04a969358061c82a49d81a14c4ec0fa0b00a824080030540700d803004004001d87270360600541638c9d8e10060a89902509c50c31c0c1c200d0481025e4ec708031c80a812895818e4c708031c84bc150251286f0a1932054dfc0793200a0400184807e009c139325e0a99800627604c2400600a82c719430908247082a6fe01c021438b04ec2702a2645d80800600638504a7a6683802445b168e2c244596689e8a19430908247082a026000a18940544bcde1320489481500504894904810006e4c02a0b055164ec0030050360639300a82d05a097261210400541200c1540c2861210481072600d05810412e4c242080069e866c0c00516e2cc0d410120124288b2f1807c0d818824de00305450c2425a4c61610482a09c069358b08190340980725e0295402a4d62c12d33301401d318135500a98001b25eccc1526b254c00072a86feccc71a080900a9998e34d60aa0612a600014243330c69693181a0b0c01358076fe0a98001a286dfdc982a0302c1c13000550340bb332860a9800030050360639300accc170320660147202a6660c81982a05c3919982e0660c87202a6660b8190331c80a80333300a38c7220800c0147182e0640cc028061c6ccc720e10703800d02a05c0cc1900660050c1502e064
  | 7 => 0xa801c0bb820302b09902e412f182497681a01d2ba672865d80c13270409d0583578c5d82429c37a9440505a5386f52880a4124bc5606f032824050630906f400a5a4d676003b7f0900c935a0881a6f42402c4d68220684037a1222c84c4d28201c8486ff16403a091600292d12f4d6aa1bf8635500640b93f2e8c000dc0d090ccc31a540b0de12d00000ec0135b7f6629400530000e4a12b932286bc05601802e01c9fb00726f19998ac4ae38424b930142c1c133101c0322c80a6f05d8580071c6b94a185814095c9913b00e4c8a1b006fe0187212f276029c139300c2c07212f02650c9930000c3907003f00c121c980203800d8003f0901603192f09c0681292b0484a81506309c82c0d02a4d698d2d1d80c616031a0b6fe0689785e6fe07c9793227601d98943600dfc030e425e4ec053317042c1c98061c84bc09b3160050c990061c83801f806090e4c0100566200d8003f0909800301f02095c15263160e4c030a01c839105bc68185d80d0ac1c895c4aa630540685839341716e2c82a26418c0980a00e094a1a5700c391800132ec0949900a1c801c150ac0c6b962d8068b3160a1a574ae0a9318b000c275c98e478c39104c0c27007d2b9381583904aa6305407c5839341228104b820344c84eb8203e4c92b82a15601935a5a3b03907220b78d034bb01a1563912b8940547600d26b4b482e2dc590544ec3180a02
  | _ => 0

def word127_9 : Nat → Nat
  | 0 => 0x6f29b13583a0270301d021032062061bc662384098130c640c0c8182809b13584d8180e998a630305000a0074d89ac2f03a662dfc2f2634a801c1d26b6f20053637f04296606014012b907202d0120b53181409a04c72259662a74168ab4b2cc45581437813416ae41c20d6060400d2251bc01900e000a193260018dbf92f1c2060050b07262b1c101802ec0002393158f18260196000060686309016031b7f25e138500ac412255c10320905d20692901418cde84e41601d359d801418d2d37f0b0dfc0c86325e17904b7f0804bc1d018026824de92f032de09426b0c6cc5bc01900e0018014326418dbf92f6623840c0b0014e4c563826620600bb00008e4de30ac09806598b00003034318486621bd728e137a2542d33125e08470b930142c1c13c400e06058257726030503821c8255c10ac26482de201812a2b1288074aee4c5820b70516e2c86f6620640c3780c69400380a25095d729432642b18003a0320600380a1c85da2dc5915818dbc2e528695c990ac78801c0c2577260245809d704390722097041bc708217880604a8ac4a201cc12577263845820970495c70807030029c98b0158e08500ac412e089904913a8241a9321c205c0c0ac05ce4cec0e478c39105bc62ec9505601703001cec3934aef1905c5b8b218c3781703001cbb00415850d2bc2807405c560181c801c31c5b009164bb45828695c379bd4
  | 1 => 0xa00e0600b98005c82424bc60825d80383a4ae9a0a19762ec06104bc607409d0583a06af181f17637882c2683a00e98d28a9d4104a4000ab0744bcde14378c134a239300edfc1989481838c0503a0420047093200e50dbc8130c6dfc70894818135048214c60e897b798b2084700ab378250a1a6325e2500003a008e4c0c40c78c3900984d07e0e9c9b82001031bca630300644a0130302510583f81838c708948181350482125ede62c8211c00fc4a1bc2866f1280133789401d04d25e2ac0ca6353a8200983a37850c0006303082cde03f81804c1f84d00e511bfb9306612504c0c378824de40c09a0e8168354130302004d3789a22c83a4100fca19bc00e82131a6c03604c97aa86fe9b135aa8027030de0e3032062061bc66638c09b7f0c60640c013280aa13626b818ccc31a634a8161bc8070029ad3637f660944038132524ec0da574d82ac0b81800e5013626b78cccc7000702695d360154d62a49d8a91564ec208ab4ae940548e008204d3626b01c01c098156f25d871ae42760705481b0b095dbf9434d804e0600741005ca192f0269b131a630824bca03934d8f181f81309a01d3637f7260301980e0263913181301d0317200c1c80cd31a5c1560cd31a5c01cb90de0e31c60cd721bc09238531c0c12882c09a634a81393583a038dfc1082141001c0d8131dccc54ea6c25e98c1d12f4d605136331074dfc8185e
  | 2 => 0xc52ec4a00c0100742b04d05e00e6f40094472670e060210bc1681d010288001c98218180700db93728084202e5074bad3026c28617a060180742b02d010038e4c2f3c61368204a83a28605d362ae0741793639304201d7593b6f2064038012869b031b7f25e380098174d850c55817030e4d36004156f180c01907f0304a0180321341fa6c726002060630b018e0604e1522ade3094818252060332eb030940130c66f02720b09c98d2a1444d601c06063268dfc2c37f03218c9784e4c695135807012510319316fe17904b7f0d24a42012f07498c1d0173781210412f032de49481b0c64ed98b7903201c00a6c28618dbf92f6f23814eb3102605d3614315605d988187269b0023c61560600c83f8182500c0196621341fa6c726002060630d204c273310740849dc0c128de5363930010303480715605d2ba6b288391e30942762ac4a0ab4a001c0b9444ae9ad05c5b8b316198019026de49d8630749440381725295c0dae4156e500c80702605c721768b716431b795c84ec5581b4ae5d4558691288241d13b1c001c09a5702e9aca20ab1522ac9d8411c001cbaa0902e04d2b9444d62ac5303a1564ec1f2570541210401902e04c0c0177262ac170e4288f187220b78c5d92a0ab03005c0394472695de320b8b71649d86303005c1d0072ec010a18ab4aee500c0ab02e3900393b0c60122dc592ed160a1a574c61a49d83
  | 3 => 0xa0902000d0581041200d9803f090cc02420b05438c7633001c38904b3000a0107182a0900fc0200541638c150af0903847127a0903819903971e1b90437f8b70322cb9081acc8150484123845792f0001bc9f89407e6f0578e302eb95058391c003c0100541638d04816072cc0078411c0014010e34160407000f00400d048e10491680100f008760018050020017fa0b81b031980396640d1058261c6cc8078e002ccc90480f1c00140120b1c60981a03d004015058e36ff035c820a8b716606048660cc80ea0b664040078e0006009048e125e1bc0003d27e250de0af6600e5e340d0345d8558170c80680b8501342aca226b5d6601e33c781a064bbae415605c3181902e1404d3940362ad7598078e01c0b818158055e301a02e5d85580a78e8202401902e5dc558320725d055c0d2530344d1c34a201cde8000c61905589a37801c0039438650e0680e00e18c320ab158039ca39300eaa0e1832090822069c337a0000701903401ce180e3871662c00603806c01802728e4e06c0c0786fc1d9be00e04c31c0c0326f01d3c52ea029e286f41070cde8170540ecdf3c52704ac9d85a02004c1d01c042e4c4cb934d80501081f0de064280631341780c0252862b13603a78abac281750742682f01809ae4c5601c78c085759860321403189a02e0e8128ab72806de2aeb252168128ab0a05da0601400850dca3c50740e8083
  | 4 => 0x181902e01d358633b099dbfb320c806431b7f25e0d5048250804bd33813030824de92f032de1359280c60e81a8e26620940f8e14ae2c1338697881b8038e10744bd9880802e068039d80c89ad2c37f4160d00f01a4a082c3225725e38c1ca0904a3800fa501c24bc1c81e02e01d358343b099dbfb30030cc49409502e06403a506f09457283a28695c318346620902837812a0e80f0072e84a0a18174a09440c2575ca0e50404c60001dbf84802e069050155ca388100170348200aae51c00e40a86403438d998416fe01c978e31603862c06e12a6f420b330821300b8073b09adbfb3003282c052e51c6121980e3090b94dea5a8b21b851a086fc99d9937f600cc403b7f0900e80b81f414049728e204005c0fa08024b94700394106f5988e1090b94090e26fe07c70b3107c01c978b08b01b84a8e137a0f99883a072078040345ca38c1c8e037a130718345ca381729bd0983841a02a3b005d7f81841618c320e24a84b5058e30c60b933a685fe761990631d8191bf80e25e0d41d37f0284bc1a2e44a44b41c8e3074948958e10724bc3406f12ade4008af81a05c1cb3002e060173321c605c0c0074ae4bc0b8180083847140d07405c0c13f2802bc710e2008015058e305ccc87084100a010718494163880392f01c95d3020815f0340240c1c404003a5725e051058054168240282e0211600100100000c0d9d881b0317f
  | 5 => 0x9c2e62e62680413712c250283cb0366f80b81e13802055ae426e2584a3de15ef2c122e62ea09cbbc0e26e4a80780837897c041be0127100404d37c0f0722e400c06e2b8390744dc0e05a160041500007270301081703001505c5900c06c0180281a762062a000ae4d05a0b412104028490321341f8b072600206063032c0000c0d09018c0e0036000fc2400e0340140389966626ce1819160e4c0040c04218c0cb00662006068480c60158002109017834c0c386250268e15d60044d81881800505aeb0801341d09b1c2121982eb00026c2d3305d61000009b4124eca003a37a8240cae40902544a0634d60ed7300500e264038054162641514307e8244b8480200ed7309b00601d0489709a16858393788cc4082a00010301081703001505c5900ce4c02003005034ec3c4818a8002a0b416824208050920443401e0682c026bc407ae4c00333818070020037260f580034074169e20b0662041c980081808402804600e4c108340721a0dea51098a710485a37a9442629c0c00e5359d804001d758043b000de2002727036060054160780c86300e50d800176fe828039436000800bb7f41099c0530003401c32143264dfd99863034191bf92f4ce9585180860001c32143260dfd998344101809437f0844bc1ca670300301c9bd0928249781a6f0190940b01400280b81a00e7603226b4b4dfd05863032069058644ae4bc7
  | 6 => 0x495c0c00800dc98fa068ccc02c0e0083e8018050000d1c980141703197a5f5c85dc4b3c581cb98ba89a0481901201a02e1404d2ff31c2ad763c52fe4e1731771340209b896128141e781b37c05c0f09c0102ad7213712c251ef0af79e04a071770630389b92a01e020de25f0106f8069c40101342ba0926e4c02b20940e4dc983875e80682786425a059c98240cc4f9c03310344b40b04f0c84f9c9866048e00c701a0100580b8e45c91643237a2ef15c9f0ab4d60e52c01b048260c700f8180313597e78e4c0004572866f1ef0394be058de3c305ef0c1a1294beb90b989609e12c4d41404807006018034a6c120502ee1582584f0cd09e0a137378a7c131c078e0d096c0e786b98b989a0481901201a02e1404d18e156bfd763c32fc2680413712c250283ce0366f80b81e13802055ae426e2584a3de15ef38122e62ee01cbbc0e05c5d6071372540d006173068030bb89753a03c041bc53a97c041be53a030e20080921360a2ea6fade5e181078f09e0a1c056c0e8df8080aee009b9300ac825c00182603903204f72607c03066818091988641c80600304f72619997c0c0480900798e04a4f9720161c8020bbc5900c19055a6b8ae0e52c02537c391720068ae06def03926e09002003000e4c0e40c01e63817a5f048061c9866700090078182870315b02402e50d2fab605e01001c0e000e4e062b6002cbd2fae42e6258
  | 7 => 0xa0714837c27504bc22906f81c811040071c98040060080080081b038ec3c201e2717626a828cc40789c3780400180841225d0480101081c4a82f06802000a0712a0900b81a5fe638322ec068091e29bc068f149c12b6f69801204d4be0d1bc0e1048e000780870003c0402431c05de181a5fe19176034048a7cde0347860bc94ae71480901a2e42ee091721750489a20a04d146091740344160984cae8068824520975d08240280841626413034010015058998b682a2cab2076f0d762e802000c0420912e4c0a1c576946f80b8a30484c22cc571540581a1be2860909801a6f04a032062412090980e370096070824662e005180870028c0401b41281dbc0a32502581a008034b99282524d6090322584160d1bc0a325025905a0a02e81c042e64a094935a580488250583c02e02135ae68ae99d110344b0189c00184b038c1237a1c209199834036cc4283784a02580b818010018df1282864a831024260cbd9981a6f006d98b2f25c4c13281514650c1c89602e6f9c00a3010e0051808025038122e61c60e59883403ede19981b65e4b89826202428ca183912c05cdf0395cc384df0121c6e0051808146021c001800f039730e30720d031333036cc40c12e26050c1c81700e258df257072b98719be00e18851b8003002070ae637c060043800480d1300e14a64b4018231c294c018211c294c120e3068944968e106894
  | _ => 0

def word127_10 : Nat → Nat
  | 0 => 0x842c40e09c0ee07096146e500c8138b6390bb0460764ec31b795cc06c110961469846f25201804ca203b2689ac4b261146379290090265101d1314d6e50720118b6de4230040771662b1764c250c110181c628c4b40e416061058b837d03819a0b092826070b837c0e80c2091706fa0702d06a826070b837c0305c26301c04c7225c1710380700c066b98720a306c9715425c01c0cc5c1be5cc38c248e181c28c4b02140c0449c9cb0263b81d01b4c69b009a6c0c60640c1400749ae0703b66217998a634a8045363790020e935c0e0420ec0c01a12a2b128811160e4d30a0b2700600f895158944088b0726985048a0412528df09d2946f81d8110440700180100006cec40d726060722e5038de8ba83b1580e41082402204c712e54c2de8ba81c14e0e80d82104a185c40170a01714d039094e520681b78a080110e403e065ca3c54a425857a610300652881112a2b1e2a6c3ae9847209604a4a80bb942722be0682065c09472011728f14eb80441498415b94022095e280615e984088257290340dbc503e2bc15825022060a23c55febbc15b9400a0940dc0d00000de2aff78a094030117282bc102eb04c09408bc50305117faec04c095e281172801857a6104d0340280481ce51e28035fe0940d8393b003c30a6b3902b17281703425430bc27262c1288394169849c0ac5ca05c0f8950c2f09288b0726825308a0412f
  | 1 => 0x80e5e1007072060bb8ac81c4a89b82e0745d60713725417c0aa9a034140bbc0e09413ca240d4d60e4308170a017d4d039094e5206bc70360801000f036e4c0e3c27280f6071bd01e0e44d2e54e00801000f0be9c157c0e12a97c102e54be5dc4d2705ca080078061340441c80f00c0804d02612e00dca14381a0142fc0e78e3900339401f034579390305117f8ac81c39001c0d000e51e3805036bfc32261034e500580615f0344f8e40440680c8644a4259ca0af4c2044030ac3ae061362611c80600ca51022254561d74d89840883b5ca9b00d06407229c1203f37c985030183ae9b05609b159038209be26ee50040af0341920689c1c8019ca32e15e03e069395fecb80c14481c2b072004007035ca40e5fe00002b2e78e1900d0962540e40b8af7284e41040d65ce50eb8e40560f4720113aee500220a4c2070018010000f5ca01b81a75c1583d414090bb804036818eb81c7280f41303d40c000158a70220edca00615e9840883b03629c0d39415e0ac0883b14e0617f9445de0ac1eb940060ee06800036015e3aff072045ca0200342bd758260720440c2ff288bb01303902201857b944c303413005008e5001c0e5fe0f5e393e5ca058720112ee0181d8ac0c807130b8707209213bc78ad03a068100a02e031b881340640c26c0742b01203b286f141d05070e2680c0ac038e4de302178a2b00889a37a004a239381c
  | 2 => 0xc838c0d81e2820ed8004a01850d7801b0b4de81d300094024a1aed0220600d03b4d8191343333af0383201a0484e41da68272059031be0769b00d3792520e4320242720e40881a048190a2018416bfc089445fe061048210420600881f4d80ed343313ae061bc92912c045731440c806928a5207682c1c8216f24a44b0182880457303b07407d28a524120e44b0de4a4030a22e62680ec1c8496620900d00c5cc389c4a5c8ac1bd99a6a4d10380c02403282c0983b5cc38c10818048065048135cc3841d049412531731be1c604c71c0e41628c0883a06a024122e61c40e81aa7437cb98709444170397fb2e0300e41240e02e01c1cae641638c0c03a0420601201741201c1cae61c2825731be09238c038e31462580ba0b4ce0d5731be29838451ae60949acec20b784a8007ae60949ade100c3b0721500240302c00d39381cf083200f00ce4c0200381a000ec40e540015e120b048f089440d03c7601c8a30c2b9935bc23b0b98253c2018185359c804013d5020b3b0b982502201e984012a004401001c0d000761058050400ec5840d00a38c1ca5f07a828078e30080f41103b60000e0680000a06d999d707a8180040d07201402300007038ebb3307a0958000581a0000801b006cc4eb82581a0140240e60075d988030200440d01603039172b7a2ee0ed3086427c2b00e3870724a0120500c82680d0180382b20739304
  | 3 => 0x72681c200df00600470b31058cc4a18e1090384018482861019881d41681e0604509082d03a09264e081220b41297c9938231409135a0b82081e061bc1c003d048244d682d049bc8203820600f40e0700d8030040140020b0910307d3936608206f80500212071b93002015058e30548247094309050c6f801282cbc240106608206f803002824240e1020e4c008031c282408b336621102402a412384a1848000251979bc091041e1ae82e62682806403405c2809a31cbfc5597e5dcf0c4d00a130250283ce0367000b8190142b57209e130251ef0af79cba0bbae400e05cbf1771560b8bac100924b14e8490147014e9be0180282484d82cba9beb79020f1de1c2782cad81d1bf37c02851a6b3b00781e3c204516c10c5704103e2b02485005e2b94a0721840e9370265d9361430321414d84e0961181d83a0c40e9c98180a0071e30460420e80e80600a0840181b044001ca40f72608c0b86172694d3001a12e0e6070b00360e53580f3b005c958610424e00c0977262c01cc0e65e0e40e820008008008007270380e3c23b00e40e81c00a01001800784761c9c0f0400e4033002860760782003a01001001000e4e0701c784c020703d12e00c3240d00ae51e3a7441403c0209804803c0220a130090df20601e0004a02401e0010309401e128061d83909ad5000f00c00e068050007615001b416e4c0d03b81a090580390
  | 4 => 0xc0300199885056c75c0c86238d0302801f0420615b0043af0403100f78618802ab6006008ebb3307e9a20b331030ad8021d782018807bc30c401401ab600475d9883f03e0842686202e061772e84165240bae84128257704913c95c03a675c8bb81a89e5cc1210582a132b982420914825d04ae600a0284c82a09002802a0b1320a85784813c25c082e6006029048974f4121770968b628d04459790ac9e1aee04accda5457286064e013202e99c1e4598ae0380c9c0264068a19286f0288320372641890484926438c12b8203e968708250a0de1280986660640db2f03e028031c002e4a096143264cc598b8203e029c101f0141880bb82030969bc0e36660959881b0a09404c018014019bc1c002e064941432581889932f04a05dbe0e1078191bc33366206d9781a25c4c93281513005ca19c04ca0547189838050d33b33148e080d00a7040680533302e07c094105d038c24378666cc40db2f03e4b8992620242600b943380ba0709c002438c1f38203e028090e107c260e033128699dc101f014cc5c9b2f82005c7d03a6945e009c598b0120a1b7865e29c0b9324af0400c0075d082c718178b61201d4592f018999b310360609700713005ca19c04ae37d741c01c601c71b8203082c0525700e99d979c013099d2b8df00e260e032f28637ce00e15d0e080c00a412de8018211c294dbd0e309094496b7a1c21212892b
  | 5 => 0x10000fe069d8784e4c1983f416014168104125c80183372604c030b078498c0983360005de11435e004dc9bc202e2c17903f06600c0140d600e4c003c22644edbf8e400e1409793b7043900505025e4c80b8130c21401f806000f082504c02e121e100009496931aa0054969e102a5404c89db7f1c801c2812f276e087200a0a04bc990170261842803f00c001e104a09805c243c2020000252574c6f082802a41695d31bc20541901500a00e04d2b8e40a116c15459264f1c1d3c5380390050071302557285028604d2ba574c6f082802a4ae824ba8214c6f08152574b494105a574b49420680a0261849d8e40a116c1545915a1847203a01401c0d8130a04ed2b93b00e04c308e40a0a80039c00be068990070940001501304a50c56b7f7841700901f020128000e425e0a81281300ee4de140d4c61400301309417c030151c8a80ba81000c048722a002e0150584f05450c2403f4121349d8070b450e2c1c078400606848562131bfc5b0b316558b8b286a69998e40540cd4f97805405d998610663840d0000944ec170320a00b8190150a017c0300602a1401703202a0182f8500421341104c0820a9300a8534cc4bc02d53a3905402d0063847202a0549814d33115039016a642f09817c017662184168102e805c01b3109a07c003c2094f79504108aef1407c0c7bca822cc1001ef0e0601800c1400c9d756c188e340
  | 6 => 0x81305c0c80a82e00c00dc9802784001ca03207e2600a84d07e29c09841026104099c002a04c0a813038e500dc0d726001e10410786fc1c9be0265dc4d01300c2680303f13417c150970065c9ca40d286015e382e2ee01801802728e4de3832066090098240300684a8ac4a22c1c9a63416c001281803316e2c83b380b94560ad02650c9c01803e255288ac160e4d04a63140824249c013a0d4e0033026090030b072698c198136000900c9435e004c12018160e4d7903304800e0680060006dc9bc400413007c5b074aa456a5f1c9034088464c206c110130a04ed0583b4c298de202b0c916ce00e407602c0889812a985728500264cc2314300c058722a007a07802a0b09e4ec1105a8ac0f4a19c0003034a1b0002e4ec30c0d72605c5813b0c3040720030050340e393000c01e10a215a0689d8980660fc098ad03404c4c20b4d604c569d878498c510ad417034209bd1500f8deb31286c000b93b0c3035988b072605c9d8618203900280260103598803726f080026003e04dc986102e030580064c7040500e41c882d3181a0262b03081703425528b937842c131a0b8b7164568255ca50c0b8130c2c00128178b62b0569c08b2b962c14378418409b930c205c0480616098c4ec101c83910493802698c0f9381581840b81f12a945c9bc2160825318a0413040209c013a0d4e003f02682c028100268240181c03600c010
  | 7 => 0x4017042015803c2006cc42403507c29c308185d005d05c5b091164a08a700e0600b89838050c30a5714e1052b8074d0b941d0a707c0150584f03629c26803090168e0143002f0a0686100e29c268030026f5e13934162644b80381a0fc0039378482c0289900a82c4ca0900625c08007380f084b8a7072b990582a1320e5730050262641503f0260150589905450c538970200e5730030268244b82a2868244b8481c69409682a03404009178054825298034c1034000de15e01401810036818eb83f05470c1da0838c0fd0300004406801330098088a08e00984ed9801a000cb82514107e3782513b65ce41c8bc87160e92912b1c20ec71a5025a940958e10740fc1d8e000a00871a0b04803c01c0d0007600daff07a03d9800200a82c7193b07a1bc7000215e5062b03b6600740800f1c000c012091c20fc6f00500038d0581207e04d3193b03404009a632760481fa6081a0006f0af07e82c0283307e82cec00300503402aff65c000082091bc00d05b3002a825980de00a0007180000a82c7182a15e1219703f4123841f8de0004ec378af8b0505970e1020cc009010660378018004123853d0481c0cb9c886e410e2e2dc1072116606b2e8210342801509e1284d29a02e0682817702a12827c102889ae06bc781a6f54f89a0a005c3081981a2b40db94380a7d4d0070c2701e381778e4b41503937cf1c1f92d0267000a
  | _ => 0

def word127_11 : Nat → Nat
  | 0 => 0xdb0006ce4c1d05a0202c010804820e4c10b0000a00c0d8006620d9c980f00a82c2781b09a00c1b05a00250e069d80060140020b81a06c0f393048140030098b00ec9da6c0311580c9c04b20902809f4a22600c01300cde4e003a03c4a49603b15e0d9980250420900f2631c20e998b300761919701a25c0304c1c04b8125c5a5c0deccd3526882007c9726c0122601d1c006a9649d83b2f002e2d83a8b2de40c45615e27e2db338b25e01b3796631599701e25c0ec08a611300e80c1c015e0840f209022ba07083a0928242c8e05d0700718111c60f4e501e4162889d8111c00f4378af1307019803b0740d42c8e05d07007093b2825e00545b075165bcc5815e0604f45b8b3160bc061666cc59801725c2bc03898074060e025704205d048075d03841d2091bcba0e00e309201c719ca02e82c5125700e9a1971c01304ec6f0070de2bc4c2684ae7019703a1bcba0a39c01c20d453c5b04a1400300a0740600cc598b0b94a193200600a068003b0015e13934160fc1fa0b0920e90480500c1400b943032c0030c0d81a7600c84878428a0681a01c6f5e11720320e80c81f784050de9720740941aa9a03e29d4e861030ba1e10172eef1de285002695c032513804b00c01902e2604a83a286b9430bc204a1840b97507405dc98041610403084c02e121c9802784c0001b3300a1203204114e085988177262c0024100c20842
  | 1 => 0xc2601207282008175410139050e24c40f905000128a740501706e2bc1abc513c0d14e80806e05c5783906af144e037000b905783507c041048030360707d00278881dc98008181050484140e0040b8054171653380700ce4c020fa006f1000805000cbe0620b4168242080541204001a0b0208241f00300a07471a9f00a04471a9f0720d1300e353a5dc0786000605870a9d00604470a9d0205d070a9d53806854a6b03c0e505bc43ae2b933817414f0d5b40c006008002b600b030eb84166612020a0a008040032b600a008003c34ce00e061d766299de1a686660a94fa9b53e5d87129f2e83801c84100a04c71a9f0ba05ca001809e4fc7184f1c238ca00180482b9e184f0cd0307184e03001d2b92f0b21300c25700e4bc150240980fc0980566613dbfb8f720f0d98177090a6c7185866000407173536dfde1b9078ef154f33207205ca001809c4fc71208090138713c31c213c0c0074ae4bca001804a2b5e184e15f0307105801c0054d97305c13406004092cc82712f6644fde18001280e94da9d2ec3894e9741c00e40805e002050b9a9b07c00c098e153a1740c2506626f0128250b21300c2503788200a0015365cc1281007e04c01b3109adfdc7b907860e4bb83453638c07860002058b9a9b002074b9a9b007034028003b006d0583f7260fd058490748240281107a0781b004820e4c5803d03c0d81e81c006000
  | 2 => 0x1802803000ad9e1825036cc4eb97900c01402002662f0c0182556c75e070100240582e2620240449c8a502c5e41c80600800de13931f4015998200400e4088067260107d003004cbc0280081c82de101c00800c003938183e80f004006f1000805000e4c7d20b65f0300f03a4a0decde01f078251bc29d03e251bc01f4cecca2bbde01f030c001000c008008004ce070ebc0c56c05c0220a4ce01c03458006008002b6003030ebb2f4148200204804a5080d0ad15e13a060e20820b82480c008cc82713d27ef1c20b320002500d25037809412859098069281bc04a040070036621342084e034941e39bc0b21300d25037803800b2f0964f4a117709a13dc6b8f724f1c1f01041200c0e0fa40e06dc98008181050484140e0040b8054171653380700c0047d0030040140032f818e4d05a0b41210402a0902000d058104120f801975020f10028141c6a7de205d00a04c71a9f048504eb13f26482dc11d13ac8250397678c0e41e29d2ec3894e9741c00e40805e00a05071a9f07c0900f8ae0cc13e0603c1c60f80f8ec0241602c84c03e9880913a0909819817753a38c7603e0b0cc00180e2eaa75c53c578ef0d4f3320720f80f8121d81600f8ad15e13a060e207c0f82c01001c00d4e9750620dc06804664138138350120119904e0740f82701f4a0f14de05909807d281bc4101740980353a5d41283e03e05c2701241407
  | 3 => 0xaa85eb48bc48176902e90c5cf20b968170d42dc945b458b531166222c3ac57c28aeee15a522b01855a28aaa81534a2a42453f60a66f149062909851b28a2c6144062869450828a06613f58278904ed309ce71380e26ca44d060988a12e94258244a74093f0123d0243a047f388f0411d0e23694468008d0011a0a2319045f308b26114c8227a44464887a810d48218a04291884c11095020e984175081ad100241f7203e6307c0b0f54a1e8103cc4078860ef941da343a79072a20e4d41c48c3861870620e0461bf2c373186e0a0d9881b1283585069cc0d08e19d9033728664a0ca0a1919031f4062e50c490185103062860230bf9417a182ee305d040b90e16ea42d43859a60b1d615e282b25055070a84414f9429a4052490a24a1421427f304f2909c0c13518264304bc60960812a1424f4048e4090ce11e1823650458108ac6114202204043070844c105a0203383f8707d520f6101e8683b63076060eaa81cb50382706e920d8a81a74033e70661a0c59418618306c05dd80b5a4162882a2a051ce0a01c13930266704b16090a811738220a0419207ea80f3401d660395006ec80cb3018a802f5005aa80ab40146b0261004824087900ea201cd0035a4062400b460150c0272404590066c009ce0101801a380269002940002b6006014003c3036ccc211d706c109050040360715b001786818eb842068818000420200
  | 4 => 0xbdc417a8a2f28e5e19cbbc2976e92eb8a5d49cba24173462e5105c628b82316f872dd4c5b798b69396c472d6cc5aa94b503169452d15659d10b363166052cad059194b1e5162842c40e58494b041160432bfd85798caf0215d832ba4a5720cae1315b672b50a56790acb5958052aed055994aae3155022a99254e9ca967950e62a04853ea0a75394dc929944531a4a5a514a062929651f9ca385945a428a4c511a0a1b3142a72839650188a01513ee727c0a4f5b49de293b282744e4e5189c441378626d9c4d43499b6931c3262d44c08897f312f2b25b924b29895f412ae9253904a31c93f4926c724bce4941492349234424588489089100921e524288483288fc291eea23b50472b08d95119ea2315045e948b85115c522a484529889f39130422512445c8879810d272189042d10856510985211ce4202083829066920a9a40ebc80e2101442018c400187fa28fea71fb843f6087ea68fba61f5c63ea307c830f84b1edd43d6a47a430f3c61e60c3c92478918f0c41e0983bb1477138ed451d94a3b01c75938ea481d28c3a20874238e76b1cc143932471d48e2881c3023859070748dfce1bc0a375a06e338db871b54c3679c6c820d8831b04635f106ba28d6aa1aad834f9869948d2091a1d833dac67058cca71978e32b9465220c9c51924a3222463b40c66718b0e3129462028c366185483089c60a28c0a5180162f
  | 5 => 0xb85a35ac468568cb2d18b2230e3461168bcad16e622c4e455148a5291405a26a944b108922111c42228a44290881210fa421e4a43a0e870b50d46a18e64304a85e390ae1a156242a48852950a02a13664254e8471108a2210c3420c48409107d1a0f4341dd08379106b220ce3419088300d05d120b624164c8299504e3209064108e81d990353a05c240b1a80f9101b2a02c440486807c8ffd89fd8b3f84c7ed8cfd8a1f8903ed067d88cfae31f5113e5c87c994f8e19f1663e15e7bb10f7231ed833da467b318f6021eb843d60a7a990f4f41e8ec3cec679c04f3731e62c3c9467911cf1b71e1a33c2887830cf0319e0033bf4277e10ef829de6d3b99476e44ecb49d8493ae4675b10eb219d5e13ab8a754b8e9b19d3053a4cc746b0e8139cf4e39b067348ce6629cc233978672d84e5a21cac4394887270ce4b41c86538f8871d14e3551c56a3884470fc0e0f51c0a937f0e6fa98def29bd4a378066ee84ddc19bb273749c6e20cdc129b78336e466db0cdb309b64a36a126cf90d9b61b1e5362906c118d7c29aee835bce6b41cd6121aba7355866a990d4f31a9253510e69eb0d3129a58434a0c69120d1a59a1e4342da67f14cf9619da73399466e18cd6319a063328e661accb841960732a5464f94c9a5991e8321dc63ca8c6f418ce93178a62c94c545989283105461ba8c2d518468306d26093cc03a17de52fa8c5f22
  | 6 => 0x52fda25facebf2297da1afae65f448be6917c922f8a35f08abde957b82af6665eb4abd4197a222f3c85e592bc6b977f12efa45de4cbb9cd76022eb835d64eba95173e22e7505ca90b911171e22e3465c51eb828d70232df885bd08b78156eb6adbc85b5a2b62916c132d7665ad50b56916a922d4a55a80ab4d9569642d1c55a24cb419967d32cee659c54b33a965d5aca47592cab231564132c76958c8cb16156272ac4455874cb0bad60c32c0cd57e46afb155f12abd8457a08af20d5e142bb255750cae7215c642b7cc56c92ad4b159d5ab24556358ac0b157562ad2755894aac2554f2aa9455514ca9f9553a3aa66b54a10a90255174aa1c95414ca7fb14f31a9e0853a0ca71254d972996f52f12a599d4ac42948852712a499948d3290e65204ca3d9d4744a8d6a5184aa2e1d4552a8a0851212a1fa14376a8543509d2a0f214165a816a5004c9fd993f55a7d434f9d49eea93d35279304ee449dbb13ab2a74c34e8cc9ceb53906270824e08c9be11378226e834dc4a9b6153673a6c054d6d49a89934b3268a94cf14999253294264294c60e9889130d3260e54c09097d1d2f33a5d8b4b85896a912d14259294b00c95d192b42256084aa0e950a12995a51c74a1ce9401d279524dee4984e92d3924c52484a48e0891a0d23172446b48616906b91ff323f2547d0e8f6991e7323c26476d08e98d1d01a39a54720a8e1ad1
  | 7 => 0x9eaa73acee7239cd653998673190e5f15cb943962772a8ee5199c9d9b91457214ce3f8dc7c438e8371c50e348dc663b8be37170ae2bb5c4a13890471106e208dc3e5b866970a84e141dc211b83c3706c8e0b95c122b81a57020ce0111bfe3b7ee56fc86df789bed137d6a6f84eded21bd22b79a66f1c8de199bbd2377256ed06dd891bad3b74c86e78edcba9b8d0b71876e14cdbf85b7e2b6f256dd0cdb70db6b5b6c046d706dac99b532369e76d212d9f91b3b3b66846cc14d931db1f6362666c34ed830db032b5fc26bf0cd7b09af4135e436bbd2d7309ae4135c436b7c4d6e8dada135b026b580d6b21ace0359c56b240d6489ac71b58836b054d5ba5aae1b556a6a85ad4a29a8a2350c36a0ced3e1da75334de8699c8d31bda543b49af68f88d1d15a354b45866898cd1025a172b4243683cad0519a04333fc367ececfa1d9ed533c6367814ceb159d15b38c966f5ccd7a99a53333ec664cacc70d98b2330e4660d6cbc119742b2de765a0ecb09995b4b2a466530cca3199402b276364e06c9a919312325a6649ccc909991b2b22c3644c8c879590a33208763f64c75958e63b1be363708c6c1d8d173186662f46c5d098b85b15a462a54c4f998992b128662388c45198844b0f6361e0ec389d86a2b0ca461848c2e91859130ae36150cc27158494b080660e92c189982b3304a46084ec0d1d8134b014a60006bfe997f7
  | _ => 0

def word127_12 : Nat → Nat
  | 0 => 0x16002000040c020004000602000404022402405c0e00022c1600000400000818000012101204000600000800060c000406020800081e0006000402060c000e060e002666062c04380a18100c0408020600001e00120012120210000000060a00020202060000060000000010000014042208000a0442020400000004021000141808060a02100c5c0a0008141a043800040e000200040c001a100602021606041c06983589069220ca2418cb82edb057120aa2414cc8269f045a2083640ee581c8b0368e06a340c8b8164702b3204a2408c980f4d01b9e0302405868098d0101a01a2c02a48044b006120082400887ff08ffc0dff573fce47f8c6ff015fdb3bfa867f38efe39dfc023f7847ee0cfd925fa92bf4867e78cfcc21f903bf1257e10efbe9df7633ee067da8efb195f5e33eb077d44afa619f462be8287ce54f9795f2a23e4ca7c708f8c0df157be0c47c086f7f95efa23dec47bc8cf7619ee623dc447b790f6b21ece4bd8a47b058f5a99eaf23d5647a9ccf5099e9b1bd3097a3caf4519e8443cf8479e0af3999e6d43cca6797ccf2c95e544bc9657918ef1f99e392bc68478c0cf1519e242bc3e67864af0a1de0d23c1257810ceff11dfa4bbe2677ad0ef18dde043bb0877412ee391dc343b76976c9aed2c9d933bb18c7600eebca5d7063ac937544eea51dd433ba78a74c8ee95b1d1f8ba1c7741cce8099cfb33
  | 1 => 0x4e1c0e0602002600066c001c1000000000000e1a0a0800001a140402000e0202220a1a0a062a001004105e040214081204020462001400001404000204027a020206001e000c2a3206282a26160e72120400020e000e000002120c4802080408420820240402080c10321a1a1602061c4c2816021a02241c50000c1a040c04081000007a0e3a6e1014001600080a1600361c0a040018000810001c0e02180000381804540220020002542202044e000e1a00240212160212160c1a02001606061e0430000c5604880000001e021e00000c0c00084a08280e20221456080832000000002600041a0e12160e3002083a12080c000a068a0806040c1602023c000022601212041a140a1a101a22001002040200042612060a00001c220e2c1a0610280c0406800008160004042802061a10160a0426020200020004021402100004000a0010081e3618046008100e160e000a0210001834080a000200020a2c08060c3a021c0800042a2410003c000c06020402002c0210001004262606140006060000000a34040600142a00001202000e34060200000000080c0a0c06160200020402060e0c10000e0206001a020608180000080024301022000c100c020002020460220002101a061200021a0c0602460208000c0404081a020400004402040a10000200001002060e0004082a020e020208020c2408002e1e1e08060c0000
  | 2 => 0x63406000a5600060804660642760002000200520e0830007604082c00041c00022a000414040e320204002a000a2c4000020e3a0200103cdeac963ab600121c14001c0c00080a0e2c123650006616024c420c280040002274008a082c0a0c04002ed00a020a02062604366a0200400402240800040600600006022c14000c080028380e0e04146a160004022002001876120010120e00123c06ac38060c2e0a0404320800200002040a3a02000200220c1a04160002080010024400be0a1802000220000854061c1a0602040e181816020014120e240a1810040000ba0612002082742202101e020602260a040a740406001a00024604040800020004102a3026185a0a0450001a3606024e1e1010040000200030002414000c1c000a020e3a0610023c02080e0e1c0000420e023402100e02065e022c02001618081818080a04000002061a080e00040e080e042606064a1c1800161e0286240200142814000c14000a060e00060a021c74000e0e02142c000a08441a06068200140002241a0632460c1e22021060122e000204220a06000e2e20081c00220a1a16000400001800001e0e0602180406140e120a00d800040004020404020212681002000a0400742e2a0e26041430102a2c000a08040e00006400000c1a02080a0054020e102402061a3e060c1a080402003a0c140c00081200001a8220021c08001e021604
  | 3 => 0x41675d3f5ee0cf5cd9cba6356260e10c42a84512116aceef1477f8003188014201c3903f6f49416d7a478e85ff0003caf61dd20dca65c02686a74010783f0c067ec7445dbb35c4853db65c89c236933bdba9ba74e2e1230d6c5ae10ca0e500110ac75a0a377bfc00188b49b219fed0c77fc001fe000af55d4a010cc8a23fe000d039fd9006004afb6297bee04ce89f6b8c34430e63676c4ce944d651420c364a2a14001e1e040a00a09a028c00b00412b21a88042201149e0422043a364a1e22042c0c340068080402041604280e700070080800483808401e1000001a241204360a3a28041cb20c38640a4694060806280014000614020004228ae6101c04004e10367a160e340268020840dc02120c5e082cc4280c283cde042a6a001a201a0c06040a002200180518000a186e100c12540a160a0202302400081c000e0e0a0a1a8e085e166610440200200200043c3c220802365a5006de0200363e1034040006182a28163a0016101e0004140a08580200483a001e0012222028020654000404002a3e56a21a0c003620005c1402000666000234041a0000222a50341c00022c36029a2200600c300c003c260000b40e0a6a5600020210002c041e0c280a000024045c040200223a700010240c02020006021c1a00160a060a00000a42460a08001814040004080800640a0434000e0600041600221824186e50002e022e
  | 4 => 0xe4f4533e2ddd0c5044a8ff0007f80001a0cec061d99404c302a8c40a79271b3b46b6889389a4f8530bc2f87ef737ed662d26e8fa0a8c2c91032fd062e4b42a84a97f8003b1e95df25bb936dc6b643a5069151f3a56ace2bd6d3428f28d56f52a589803b10a8a88de3db11c343213494fde04eb7692235079dd0d7fa2a9bcf0dd49c53d2575e42b4aa6321051bd7658e3f30d4ff00006415565f15fe000884ab7c14b2706719e9b4a004a7c07a57db2d9423c1669a362ceffc001e232eff0007f8003fc0004902ca386c7f8003fc000171ccff0006d0037355ddfe000ff000769371418cdfe000b29307f8003fc0008ad3d5b85296b49590311fe000ff0007f8003fc000106cdff0007f8003fc001fe000f912b5432f720ce7fe000550a089aec3fc001fe000c1682c4329d28e787cde5771d99403c79471abc8eb742717f800329c9b70d88ae3c07f8003fc001fe000f55792e0c4b6dc3ae08f0311e71b2942d9d72b68b74a6b5ff8002f9da7fe0005b609c620b814f7bfe000986fa831dadedbb5fe000ff000249e1bfc0015c45c0e0e4e31452b9961150495d0c2ff80038cb141001dff0006ca988784c51c655ff000790990e8ca9a086ffa65c0a8168249b3fe00062668721787240610eb2b1a8887a3a9a4c012728021685a8fb721d0b92ba9258e0177d3cecec091905ca454c1123589089787c65d034bd72c60fc4d74e
  | 5 => 0xb485741cca7a9465b25377978ee83d9b2efec257d9ecb824e18ffe0008195ee1c1926cbed1ec8fd4445318da3fc00031117ff0006b2cb5f5707100f0ff00045168bfc0009e1bc4c8cdb3074e262618320c8a7ebd3b5bffc0017e7d100972c82c5e0cd0e06359025ef4a9b86b5c15fe000a64b85f03884caa8b655665384b93c75f4c95c6bfd736d1538c25b8d0a952d7e8201e788d1c1a55fe0009c90db0145d3d4a7482f20e7664eb73ac243e64ed4372bfc80fee389a05a98a096ae072e77fc00002aa90f46586b712d06731302eb8505e645e4604cd7e80ffa00de4c85ffc000db226a68153a24ecede8740024ff000491cc348115582dfff00052cb43e244bfe0004d04aff80001846ececefff00025c94eb9c49fe000ff0007f800254ba7be861f63f6633e02a1975fe000ff000533a7f7e2a1390d00e031bbb2da048a69d1ff5b3af7c490cd9a604e49b1827e821b11e55a36703f6729014b4dc2de5c7f12a624725422ac28e1a40389f54a99a33927e15c480368964fb5c93d585b170df361574a318be995779ae7fde427c7c551e82557c8f3b655b33cab828c31605fa244820147e872342a48545f8ca06b2d6d4dfea413ec053ecdaaf15c493fe000d043e299a2a48aa5fe0009b1bfc13fcaee377cee94a93de7f8000b5f41fe000cf8d1ef44fcadece74e46aa353fb1503452fffe000ff0001bc4cccdb3dee2d36
  | 6 => 0xfc0017d2acbc739b443be61736fa50c5062bebb8f3fc000210fca129f3f982428f10d6e5a265e3158d8a7a468010e4cb257b0af2020550d063eff0005b21378dbac4674fed743443615ba43bb037dbe566fbbe1719913c8a8d1e79fa696d5697386cc2943864ff80007d5e0523d36a879922bafd5025fe0005a2d7e1110424ade109eed0754ff8002f1c9e831ee906a2c8c0f4a464bfe000d52812e9374764535059a055cb2c108fc8975890bde360f23921eccd704c278ea29150ba8bfc001851ec677ba7c9b797960514180350ff2b0cf2d4b4f0e0cd663ec6fa803fc001fe000aa0e67f8003fc000c67af3a0607f8001c221fb480d896f42b2cbf8cc893e298ff0007f80036440998ee2ff000590b342125ae51f4ff0001f92ffa1223c713a2187bff8002e14c770930c28dbca8e12bc474f07e60a4fd7a02e7e03ac94181ff00071c860a8dcc4e367a0235471bb37c6cc90127a86de7f8003e5c07fe000ff0007f8003fc000ce72d9028aff8003fc0012a3a3f44121c20bf28d7738f8326837c13f9f9d1a2a4ea4a85a77f80031d5c7fe000ff0007f8003fc0009851dff00015c62404b7ffe0003380e0c8d43fc001fe0000c3aaff800294b8af03c59075bff8003fc0001895eff0000624385a1f5fe000ff0007f8003fc0004e64eff00013261a14e69141f78674b7ca377b21ddfe000b48bae98dcdcc8627426b507db6
  | 7 => 0x2c4f7fa65e4dbcaea9178428ce134682244fa5ca4f18a6bed242378fc8b02776d09eed151b3925f0c1d3caae6522d98824a2d45bdd50cda35b0619a26a1f3dc326ce52e7ff800249f6f7c55f39389e4b66bfc00080657244642b45562513ab64b12f57296b9a37d3d9fe00092374ff800304e23fe000ff0004fa269c9b505c519de3d8ff8000f88a83672b526fb722e7ffc0008417498965d8198518e59e87cbaa050633e41b56b0a30976a808ff8001f0521fe000c368721302e9ce714a1cbfa02ac30911824f420cc3829457f8000f9766e70bbff0007f80016d90566abf9518816ae3f84a6e3ca47ba3e2472c6d18bbd5630edb6deb43757fc001e721c113b47f8003d5b257a008f91fec9a9a7fc0013866fde25bce82083637ffe000a15e5ff8001909d9080d2e43ee309a0c944af5b299ff0007923dffc000362c1ff000501c87fc0009c419a45b5d1c8a2e64f2b2af5ff0004a128cf48be4404cd38455aa2cffc00108e1ad723e449458586f1fe000ff00016240ffc000b52373541f02235cd8649206e4608961e3c0c4cb2600491994fa0246427a03dca0752b2177f8001783e504f9fff00043ba0fbd572a06adc051c3e84df09efc441dfab22143075edc5b21498fd782def885d15f9290a964585963a05ae064f26d24a94e648059bfc001fe000f59053838a1a0b87fe0007c6546e3b6df199b3ca4a364c81c8f07
  | _ => 0

def word127_13 : Nat → Nat
  | 0 => 0x966990bbee60107216c3f27926a21b5ab138fb4d4680770b89871b5964c72e2b66d6a2bd7a3c291c6f3ecc14d7ab8073e529b926ab84f1fc1a7cfa58b4c9dea534eff800044501e2a07ff00056a960509673e15aa90bf9cc18ef228bdf140852ef89c559d4f7ff402d922ddc394d0ba48bf2479405145e1dce0444a826f7e18e94b92f654687fe000a66bdeebb6a80f071a28b79020b407c54e44e3c1d89b78153b02b754f5e90a48b7092eb507dd61c4436ead457de8bd491ff41cfbd769241508712622beaa76ad0b6512bdcc5e446abab3450e7f8003fc001f2064704d3b7aac3fc00079134148697f80036c50950cc04718f4bc401f02c114196100e424a0ef664fb51113dd7da072891e926ae834735812274147e8e094e41fc248c3e22b50d9c7b692c8169c134a2101de22b081d1297b982b9241baa06366445aee92abb142ebede628141f9961e4cb83fe000b3703ff8003a931cbed8ddd82d4c94c371cb792ca5c6708f614947539bfe000ff0007513a4d1c77caa667961a2c1812416ad88529df33c13b5bbfc001943e8db53e481a12d64e1d6ad3be0b5a0a3bbfc001fe000e86f7ff800175c4256908dd092918187424ae80f273a3a66e327bb143e7e054c57b0102e6219e4da69f5ef16950ba499090a62b7f3458e1e3357e8ad54d1516e7f6384a3995f62ba9193348a811881cd1eae2eaeab31bf31f777d354
  | 1 => 0x6fa06bfc000306f37831e82b93a88910ba1b5ff0004081d13538c80e6d6b8377f8003fc001fe000a42ee52a753fc00004ecadb3d1eb993268d7c6663fff0007f80000c697fe000a26da6849affc001a20c32696e910cbdfdcfc40a904d3d5fac21bfc0004021aef750963e1afd6a9c10daff0007f800198063fe000ff0007f8001960792c462d27ee1094a900f29fe000ff0001413c3fc0002b235db2327f8003fc00126507333a77f80037087384e151828d93adfa49ce92a02667860ff80024a310bf098da65a7b402a95bdc3902dcc0f2ff8002dc4619017c63431cdbdfffc001287ccff0002024e8a41e802e6f9f278d6bcc920d2510e084c13184a4f1fe2c9fe000ff0004b441a2cae7fe000b054965833241565fe000ff0001db72e05beea23ecea527f128e4380e296dd0bc8a34eaa9e9182bfe000761ff7a86a09ddf63465ecc11b7f8000b210f601b65a0ddff8000683bd367a92a722ff80035d60024b5dd224b1da8f5ad9184d176928c0f848cfbc423521192957d1c8a86b05669c38cb35c0de49cd2cb476e4e1291f2ec2eed40357a626ad917619aa73b9ac9b0eb8083353fae2d3d6625a7b90c5c549318ffc001fe000cd46f721cd7e48fecef8ee0476719a3561eea98503f14fcd2c75e3594762c559d5c6d50969e99d566fdf24612faafa381e0d0617100359b0ad01890fa2e14f037eb4a800a122869ac2d
  | 2 => 0xd6473b846e7f2515442d2f2153fe0006274ec0a7129a0b1fe0006c53a0dc1956433046193ce8923c1e3bfc000bed0c09088ff8003fc00160a9ae2148bc0a3ffc0005e617ff0006002bfa90f0d6a12ff00016a2b355937e0566a561829499c79727fe000de32dff8003865733322c01820c905642c8aab40cbff0007f8001fcb51a2da3ea106ff800231cfa00311ff0007f8003fc0008ae39ff0007f8003fc0012a9f1147f57f8003fc0017925c235c12896ebc96d25ebcfcd91d6ea627fc001b09dfff0007f800151b7082950ff0007f80012256e92376d9613ff80015db01fe000ff0007f8003fc00134354e622b52a653848dea81eac80147f80037e297fe000c1758523e687d531e4268653113f4644c953c44872509613c1f43d8b80c481dbc20106878aec1481ec76410b1d6a964c238d621fca44fb75835875d8e329c0422cccd33882576917276ff0001997a605be13a728f615130a1fa9155be2decca7f6e893f904e8e0825f9304e240b2ffc001c1093057683825d53c80bc27c9ad2eed4b52da585cfe0045c578f60b9ed8ffead220ff0000a2cca8e0135062ad38fe948eebfc000d2629e63ad72bbdcb5c90b11a8b261e0849d2fe234b900dea1d3000952145deac4f95c4afe70a7231d59022c0ff0001e22f7fc001c32c3822c5ff80023567bd21a0ff0006fc44a90131a27b81d80bd79807fc0005c396ff000
  | 3 => 0x3567e75f6f6924ac1cc229fe000aa4601c3e654a1e3a413c745bc6f9e68e8781fe000c2393203d073833b6039554681809c551db09fe0007b5321b14f7197248453f9f2a501c92c81dbe8ae47e91a785c23818ead7b1d51b19b02916ca1c60e506bb112e2a243ef84e20ef55d0085e240c809316a0bd9a71f487b018f55cfd001247765ff80011cd8e6c2c45a70619bbff08b374efa9bd4557f80030208ffe000ab268f4b943fc001a8992ff00026c35ae99a5ec089253043089edc46d3fe000ff00035994426549fe000ff0007f8002c60c3fe000e95e3d5c415961ed16ea0d60f7c71c79223f20f280a00cfa91d1389f55803aa1117de399c93d059a4c9a3727c30857bfc001fe000ff0006cafefce4033299a1b3aec498efa011b580277694f0a0f5b9459454921ff0003a471ffc00042889da60bc11adb6827222b39c36e2c51d93fc001bb272e556b2bb61b9c3e84cbcc3c26acdc49498324f4abe81920b142e29904b44fa20a3147f800159ed7c8a33e8710720affe47e3b0ceb426c798c7596d795a67310e2f9af17dffc001ca2812a1edcab9c3fc0011a876362139e9e9b163c91cd0f467b898bc72ede5a6e6f01230a5ca90d5164126c12ff0001a1a886a426e21d0f75388f19153dffc24e511590f7f8000986ea471b3b243f90039860d97cecd1831ddff8000b2284731d85b29434429a6995fcb17891345c581a
  | 4 => 0xaff000168bf58ccc482ee7736748f434e253616c3a88a5be00aad4322b8dc1b3d403ba6b6aca4a5dac37a1b44e6935fb66326a8650e97ce84491b4a4448c45dff00012b3c348b1c564e6873c0eb931bfc000231215c69adbc5c286215bedd71d3d02a3b1744dc4bac68bc298ff80032091dfe000777ea6a84a46d6524e7d354764d98ba00082002b4f9b8210a2cbae528bd6ee5ef8dcad40617c56266d297a50df883d8f880f2489e03685f947422191b771291b4a4b23fd6511631e9e6cf89af611c80081fea2e6997dd2fa47cc05ad22718208c5e210557a4ef427e15b8b1982fdd09c5aad04baf4dd68412239ad0b86d87067cc937936c69320c888e177072513fc0001c29bf874657344ffc001d2926bb076ff8001fd09532f491d1f2578202dc6daead15cf5d46336c64d95770d225215cf63a7b49107dd1e36f63d6d939d25387e8b1d911207f8002fd4d9bc532db517ba4868f5c4dfe000ff000582d874608bfe0006a9168a253ffc000c685a5721e20c0018c4947c66dcd26b1db8aa9572ebe019474c2939d5d1d41ebec4bf05019d14408587cdb0568f80130822d2d67803153831825702170d268061323b15f29169245263950803205af19aaf15a01f3027730b86e40775c3a22b204cb1bf6e2e99ece1112a558b938d6b86eb0df44ee7bf9101ff80038d3ad6ab3e5e38040c5fffc0014e010da187f2029c710f
  | 5 => 0x589126b40fb678ac2c26363ab80028c2338c1f993d0ba1b281a16f22d6333520b6aa218dc09390a0c46075420d71d23dfe000fa16eff8003fc001032a19a25f3fc46c1e319ec3f82a8e6f7c4e61cd2728c61ed6918b9f3bfc001965417b1649d8510a616100923ff00071ad8ffc001fe000ff0007f8003fc001a2b15220b97f8003fc0011ecdff98667f8003fc001fe000ff0007f8003fc001fe000ff0002248414e363fe00048238718bfb10cc0f03199c45a78b9c6b0dbf8c9730a121a51efb0c8f76648fab4b3d01fdd8cf3954bc29e6798aabf06055b92b62b42549c8ef030108da5b8460c5294254a19e9c6b7a001999ebd5dd1227b622738410d6caced0f77645641f7eaa391b1c417fd2be20c4738ea0054589f269f82d33b113b79200784ca0e8b45c2ca06cfa283ac741a08cae2bec0618fd44be63c6248da2312d990c106a367326e004ef56443224d0814125c9098083116a486c7c7baa12d804322c3300a52d5a0de595c9738155f3634979ce945f399d08dd223ea4a0608409f8890b1d6520b084afd341b694258524c82790f41e59411a8941bda448f5096bd6e6ada34d0cb5f0988d766dd46b86225ad709dc53c8fe50a923ab2ee1ed9520a7c11331a69bfad5915328f7930756e21e7df934a809ae273c53ec03ce88255b2683d02c9c274bfc0010cb80c850130b10a95b5e6ac64c4627300e6be874a26b6
  | 6 => 0xc2f0794e45d48a28683b66ffc00134b232c83d69163db24f1d26d5722f45cab2791765e6fef686fe092b56250ebfe000cc29271be24a882f3f11428031293e4609d74623b1772527a4153fc0007e1dd4b239cdb7fd6ceb2bad2ee604952c7c465cf8a7172e6711691de790bcfec4765e67af0afe4f197284235a577503ba0001186f25099271f86c82f8160f000461b92919276a0d33dce77ad4522729d88cc1c8d02f09409c75325ac997cd6f81bf423189c7124e65a6561f50b6bca917c516d8b0c8be010d1b7653e034f433ec369fd6a160817e43e5919c4f38c1c8e59ab651126db93691035faa1b766d1b1a95ffd4b869a522e849d3032c67472f9d426650d5a10100b120b1491ad8f0fa467d8bbf39c0a88d1269112cef90eb8d5b6e340321288ee747399cadbbeb71dc272a09059189af9ed119d94bc7167350055d26c1dc3544caa888d4c2f8d4d1a56a1e1a9ae8c67589fbae2751d36cc7c1b87220cef69e2d0328415703e891431288c2e82cd90b34eb3c828e1aa3f6e2076888c98e02025aa7cfdfa696b599c918ec92e76e1ca384acc4104ff8003fc0000a96cef81b5e06647cc0b94d5a9f953d60a17fc00044d4fff0000cc98bd21d486fca113f4a21b434c30f50addf9436f08e50c9b537a85dff0007f8001b5c5d32093de7ecf0a6ec0a3557eb79ff0000f2e8c8db3bfe0008a2779a9dc43def6ce8675e20
  | 7 => 0x2df2fde6c965248974a966b96bcd6a46e2c1a81741c3dce75ad89e6884f5551b6b414d261b7dab4e68c2a0c2bb642954c3ab311c47ba66ef381f5f01c406604286c86ff0005a08fbfc00008866726ec0fc80f3ddd708279ff0001cb62f3423b5e518ff0007f80031c789fe000b151ff481f742158fa746ec4a6f21e12cc1cab6848ff000022f17fc001fe000ff0007f8003fc001fe000ff00007c1c024bd5b0e9cff0007f8002c0a77fe0000c760f400f6e039e74be9584ae721180e217dfe0004f6627996c73226c045381126220c69895dfa40991e830d4e0553c1f7e66e8ea16b54a36096114e2abf5e1261ba2807fc000b4117271016823a4ad50a92a5b9e826d6096e99ede9aa5fcf24862ae53d8f2b02e135344a8829ec31343bc789ff0007c4a378a0eab71f7ff00044857758cd0ca663ba41800844d98ee866358ff0004190cbfc000f05c60f47df3029b1d43dde014c6007aa373189a3f1d19fff0007f80024a0815ed4eff0007f8003fc0019ce1f863407f8003fc000631bc7d2bbe18233fc000b0b5f3b0387f8003fc0003a22a2508f76457f242c954647a3351a6b99e612f2da377ff000608af26129dfe000ff0001a00cda168d60cce12693da48bf9a40bfe00012888f5c2cd9c721fe00078530452030216cf43287d63e3010e0bfc000632d18220dcda7cb4de256ec3a2447f793cbf5131bb642444770219f
  | _ => 0

def word127_14 : Nat → Nat
  | 0 => 0x1371157b19fd98cea8a0eb2ff0007f8003fc00080a5c9069b0f4221b97a766aa506316d891960cb5520d486b706e315c3fc0019aec33e92c30268cbce7bd4750393b94a973219da50f01b2a8a239103455f87fe000c92ebff8001e053eae17391130389fb6e63e0ee42a825b77f8000dd55ffe000f609716a843fc00124b09ff0007f8000f840ffe000430e97f80038c2d3fe0001c564479ccc59ca9b300bd807bfc4a30c4bffce45a8f4a0bdafc5b0fea1a964673cb2cbf8a087c788f4ba25a3e7050b6d9fc2a665a67eef0b988392c5bc1c0f13ade18d96f5a99a420fb1449a0a261140bf4a52d6d8f4d42eab48e73be9401e37e9d138ec9cf1310fbf744bdd4b6881c686c7ac09951ef0c0639c70a0f68116ccfc0cd1ba19f7292e2409442c4c445b922442b785aaaa11e9b5fa5e84c50a24e02a6cd153afacf0a7c69073b6ea0d10ac8177ed0cae21044a9364108bf50137f21d015d609c88efed94e09caa3521d216b105a61b23b31e1621092707ad8ba2f0a4de5bcfd82a4076844a43b1f0810789274c6c3fd3d7dbc496e305f8c5f0b2b376254da48da0232f32fcb055e24e371ed092cabd42d8e9cab2303e3f7944e1a90a12d138f291f025e3c317ac0567ac67a993dc426f0c83dbced6645369470b8ad4eb8fefffc15a6180cad189a93b1374007de347d7294751d0e1381f8143e135510872a783e2dee504d4c9c
  | 1 => 0xdd5eac917843662da50832347437021aae58a3e6a4998e2c3558bf70283daa027451e791476eacca10b38ef9af8f09696ee555647ed7f8000510237c959476ca0988239c5a3c2695b42128b0e6caa1fcd0ef29d8460d1167fc0007aa79368e273aa5d0c9b5c0c92dd2667f800130ff92a69c2c91dbb3f63fc001fe000ff00033488e8d775fe0006159c7f8002d8d53ac44b1b847a93e4e65ab1d52248491e03953bfc001fe0009b2e885160a64b217ee88ff0004227751421ffe000ff00019911835e35fe000ff000132d5da18d510aaa9b8143cb369a62d7fe000ff00049b2b5c64b3dc78c807f30745fbaa1d0e81907b834d80145e016c952bc402fe56a931e1f4796307155a6f890faf031226bb72827e5913cadc0ca2202fb09187c40215db26ba4dfd95725c3502c5e8bfe000704c22fbf21d24bd3870c2004184036e74d22609a69a8b288ae958d588f0d2fd0457524663fc000d5286255631f420b142bffe0009f481162e6bfc000520a89662da8216eed3d3fe000ff000480c87ba571ee8ccff0007f8000adfb7bc28cf934c62ac215dfd0ea8dfe8648683843dc6830f09cec66dd50d11ddd1212860875277f8001c06b59c7227252594130460677fe00023033e820a18c598804c72a49c2d9f91f4f51c4d18d917b3ebfef8018aba2f3ff0007f80034550558c312b47e4f13cd58994863dfff00065238bfc001e88
  | 2 => 0x374c246a233ff0007f8003fc0017434cff00027256f6218dfe000ff0007f8003fc000aafc691120ff800045812ce5b0ea4e8ff8003fc00170438b804fff8003fc001dcc04ff000364a11cdba40e6b4e3320938b97fc00118d47db186fca4afc9ca4c6e6c115c39a9f8fddaa9fe000e170b9d1818b8db9fe000190b2a5c7e2d17adbcc87b181583acded475ee3202df8297f8002946559e5e59f5769fa72a44f900e34672231e7c14235dc7262e07464c5bb15920889eb2002212c550eb19d46b5e0c73b16101996bfc0002e31bff000270f2ffc001fe0003575e6a10d4a12aa62c241a05970b2febddabfe0003524a860fbab8e7710d5f930fb5117e0e1753a481fb1350c201bbd58deb68192c115ef3467a1cecdae9b9883bb3c21368322a00dacd4b91630f60855504149ce04437ad6dda0f9e81c59b287728588c1ad3267f4241810126703518e9e69e9a62cc8a21c0dd1bfe000711262f0949e1d6c9b1bebf5bbb10fffa513676273746cc1521391e061b9295d53180231ad01ee6d6f6d8f8b7b80c8914e32782260b7d3a5933f3d94104907629068e2156a61945238bff000623808013fe0c41c8e596099708dc15616b25ff00008ae55acbdcc450552303afb6850d294a2a0d555a0d6c12961e37be0a3ca0a5ea82ceedddfc0797175a1d903780d95d4687b090bd8eb08bfc001269e27630cae08c599edcf65218a3
  | 3 => 0x5212cbd1df1a9ff8003fc000441b9b691b6c4611225a738bbe9663dbe3e6304ae40aad7ff0007f8002e83b848ec0ff0007f80020246546e33e865d89c6819400692b342f22672c430a00779712255395618840fd26e980a9b105e6ea5bf948435836131959052795f2581202a0bb3b0c5b8709410faa398ce4e16eb1feb146ffe0004c127ff80013a47ffe000ff00008aef418528490f08c48b1d8a9ffc00024457ff00040424b8d0554e6e31d2430ac6bbfc000c63293f34623462bfc00071029ff000220612cd2b584b12ff00034405bfc001fe000ff0007f8000f9429eb1c0ff0007f80037d6f7fe000822b5ff8003fc001dc5f11846d7f80034900ffe000ff000344a60e8085b605b5b96caaac4ffc001ece49b0035de8efb4536ec692aff0007f80019c9f5c4308e257c27c18a18773fe0009345d0ab9130d17dfe000aa3db369c5ce132adaf82032e3e5958ffc0001e886228ac5e01d9152cc5ee2b3d64bab8a94cd1032a712733bac906f97007ef076ec90390c8c8c4642d881861b382d741a3a9e6708e82ff00049bd1e3576a000be6a601839a96d93b9c21242682cdd26a7fc000461fd24915c10ab96d63dfe000ff0007302e0ec930b8f78ff0007f800028a3ffe000cb64cf2451ffc00034c73da7e1669e4b3dace951c27090a7f80015e45c3cc79da1e94031319801768aaeb968e8090b715629fe0005e27aff8
  | 4 => 0x4a0b775be59063cc9ebd5f271b7f800301595fe000934b0e930d6196e546b73ca16a75cb4bfc001cee1e597631e2220b120bfe0009c23a9b2e22b9f0ffe000706e7ff800060a155c59e783eacd14009e02a42793133c17f8003fc0007e320915987f8000e5194d02b7d960c901024906e1447b47778fad8aafc919ffe000ff0000d30e641ec7fe0006345da3254468de9fe000ff00074290a551a8bcceedb41d403fd0a442b8a37b6a6dcc7aebbb8c4c2693d2f143598e85013c2067fe737a44f034fa9c98ca35fc71349aa3e7952f9432bb05881c61d9f403c9825abc58a49c9203514caa2ba4590b7ac2cfffc001fe0003d5947f80016df119a31f840d7c188b6b5ff02254fff00004929f89cf4c8f3d1c144ec4b8f1caf2fadd13f621ff8003fc001fe00079327ed10eda056bb46fc117f1b23eedc5dc9d4a5ec75e238294bfc001fe000ff0007f8003fc001fe0001827d84af7ffc0007f05cff00077af6901be40e303b587a58c19b419c2f86ed8f2ca1c41d984c43fe0007b5426d1c959439ca4c7dff000404977fc001ba80b9e6c1ecae159840d611f6ff00023b860180b15898c1c780ce87d7fc001e24ae67729f6c996846bd54c5fa50e18211402825f146b1d53c3971783700e7a2eaf1f907ea9c580041d94ce70616dca8be085a87429aff182f2717b79c97124648ff0000193b7fc001aa9207b4fe68165a6a
  | 5 => 0x690d7b177b4cd6fe8a8056655b1fbf2137f5261bff0006994ebfc001fe0009336bde856f9822b121eeeb0d6033f83c2197fe000b51d6fc2fabfc001fe000330437f8003fc001fe0004f6a57f80012e2c55a1b2ea74c7f8002b8003fe0006a8263b85fa68383fe0009147c6d47a2c8247fe000ff000310c2e692205269029269a5b11fa428722ce00b6256b1755c9d0e111b6d28d97f8002c144bfe000836455c25fb9532c9a5333576be52c2b0a35a21166d11f6b5b8640ca038a4308221bf6200eb5ee14630626175d2441c955496ca8beb827c7425878281d40d95e2831a37a9c181a523de1635ab0baf8463c0c468fff0007f8003fc001fe0002a3d10b4b1c2c294dc53ce7836e69cdd847ef4f26f74758f84277fc0011cd28d3662ce0b561870bfe000107217630c891a39cf15a7e7670cb597fc00116b06053b57f8003fc000e674aff0000380975c918b67aa3b845e7b45b09e6deb2c4af32fb4b5cfcd4230c429ff00022c5f5861b3fe000b8755861b38782f5842cf95518ae1e6e6d6069c7360920579ad15b62d4370f9f72f90782ed5443c62fa1694923fbd91756e8fc83c933a69a26db050a3303c3437b2ff80023cec774bd7220f1ff8003fc001c0dfeb72580141fffc001d0b27ea196d58d8e3e4cce01dbec25a10c4b56e1be4e35c2b4b5e74b3e9a54b6e34eaf7dc4d29c3fc0002a468096f0bc2427fc001fe
  | 6 => 0x1125b931196c339c0e3d19d483da632a8f60e2858bb1174072ee8c2b1a4d1360a544e1e578b6d9b5e751932169f9aeea6f060a73002b015e170060eee6dad880546d0442a1a3815b2b62583fc000a2451036ee8f28171c2661699fd56998ea23efe3cefb2a6ff0004b8eff5a5244a6d49c8487f8003fc00140a67a80eabac2458d53bdce4a216e37f8003a128ffe0005c4f6ff800365e802a069a86200c06a9b92dd867eaff0007f80001a4244e1201460dff8003fc00034c94d934bbc1a09f448ff52dcff00032b8dffc0010e9c1578ea4287a3fc001fe00059577ff8001543e794e840f8f0ff8001c014371119173d6c489401cb72570b9a61d111aca8243b310b9e9b730a5b14790185fe0002f802b43107fc00032f461e6be8298c818b6f3e7d4aa54a4e25617a5acb6fabff000682d20ea23922a73584e5ff8003856a49d2d8ff00035176bfc000ce9f31c853f7c07fe4619fe000440cf3093099cfaffe000256732014d8f82b9e65db8f09b7f8000358dbdf161f178f343729355fa8c00cf66d30523c8a0a844a17dd88730e2a5404af69c297240deab08b3fc00038cfd824287f800161b4fa6ae1950bc043f87fc001fe000d020d094929fdf4c606027d50ee04aac85b141001fb52bb414019dced3fe000ff0002d43472d98dcc499ff00073897bfc001fe00017469ff80037e151fe0004b5a803a10b39916be1825c
  | 7 => 0xd675a4a46dc5ad3a9dfe12369850afdf3751f08baf551f190a3777071c95a1fa56c02300991f3db8768be3caec77b3b8b70b2428bd6ed0d261e7440279a183471f603269672e84151db13fc0e6746a347208e9e94cace83ab2b8067f800154e1e1805d5e003ee15c7c4b782c7cfe10b560a44af40cd5ea750a526811697c23d5f12be245e1fc9a6c4d77f6efe41b466d3465fb54332e09d335e816a36419e261923dc03978136ab39bb93085e253c7c5aade8cca754213530fca1143f18a7274401d21a933c6af58b3155102694515817115e563e61683c83c5f4a684c84dbe7992534b7235c9264a86ce5602452ff800230e4e9e5cb9e3018a934bfc001fe000ff00019ca6d94695907b0cf4c06d245ffc0002e4450e224260d75fe3a3fe00090362ad99c32dcbdfe0007f4e74d20196435da6e25ff0007f8001600bdfe000ff00004037c3df678080eba83998bd8621a0f7c7c561338ff8000a47b5fe00086132e8accf261073d152ff0007f8003fc001fe000963a12e8129d473b6e9b57b0c669199d489b6184783b50d1da833fc001231601d1f7e787ea0e36a70052ff000691448840b90ca26dd84d9e32751cc80a867d038b67f800244245491a7921c941bd3cb649cec9368f20a3a4180dded8d62c83f6d8171d96e42af92313df31604b5ea24449be776b90cbb5919a2207298477b92cff22355185ff2edbfc22f5af
  | _ => 0

def word127_15 : Nat → Nat
  | 0 => 0x46aa163326492b4a13effe0003c3603990ccfcc1ffe000a56a9d4452160577a206dc17fb53395ef8b07527539033fd325d3fc001f00498a6498d0f18202ac1b0add53fdb9abaae25bde1177f63d72b3023fc0012ad7f1631e3e99bb65f8e8adbee174bef3638358cbfe000ee7d47201839a40e64ed8c763a51be5caa50b2238e4072fc11b3eca39fe0faf9510ea3a1e8b4e056a1a7ac1e8a09c6ace06be673e8555884b5d99d3b7f4d3b311a01ac6792c42de09a84b4d5ad132dc18775a9c5115700983fc1557aef2b40a36eabc64ae5d4664493d7665dd0b3895cdc5e01a5791c1ea3122db647ecc10f92f9ac53710cd292cb7e10dbcc81fdd8b24cca8c2455440c77a059012917cd3587ff800351623fe0003f96ad03e347d722a30ba892adec3a3dc9cb8bb1017e42977289ebe5409026df8705ddb411585b86c017f121edf9139d0d024f026ff0003190e90034906f2c740f0270ce9394d1f078d1e3335aa3aa12454b87a7ff000798d23fc00020360f00a63d9187fc00124c91ff0005e1e17463bbfe000ff0007f8001b57e1fe000f76e1a8a947fc001fe0001a1384a9791419a9cc36ac44997f8003bd859fe0005a7fe95b90f1927e684135e8994989fa10a09fe000c75357c1becc1959fe000ff0000e9c904c3389b296c06e00e2437724c784ec87a3643b825cbc5d41b1eb37565a2ac3320d602cba7a164e1d91d1f
  | 1 => 0x5d607a533d64dc0a023c23a29c36db38ad9fe0004d603d8ae640093e4ea917007033880734e16952899d2493721dc3422cd2857c37cda1b6b2d8fb37c0c17121660a07a40444710250b96a0a13d3e19a75a26153056aec215b1bbffe000391857f8001ca0aeb80c436255e02743fc0005d0c2ff0007f80034234936c0f5a0e5118d6cacfadfe000ca63e7cc03bfc001fe0004858fe948fbfc0019f0e7b11b59c0d5685945eb29d694becf9283fc001fe000742db7f800330cf8ed0f8ff00072388ffc0014cc62113707f8003fc000f0c05d646938455c41eb5d6292382c4a94b6fa5c6458081d537cd638ebfc00010e0fff00066b4287d4bbfe0000f229198ec2bc34d0d118f17807f800379b486e6b27805efa9f2994808702324247436813515a893886b9a223db0f8be8135aeee89b6179020dbb93d56ee9ab81be1f985758784b83153f4a44ca14ffc001a2c23ff0007f8003fc001fe000ff0003eb44b86069dcbeb7294598c3fcfd2290719aff00029a363a9f5dfe000a4550440bc5cd40de4ed9ff0005f90a194659e02186b2d97f800014368c8332db8366d866ac8cea9a107db678e9bcf1a9d4bfe000bb92d1ac53aa8a8dc0239af3f93208ef180d9fe000c1372ff8003fc001f0c38526e17f80001d9f9fe000c7576138e06647d4e8de9d9904e58fdb518ef6ad5dff000153788a878e4f03ae9364d68a64002b00
  | 2 => 0x6c6bde162dc1053ff000722858a01cffe000ff0007f800221333de36cff0007f8003ea442ca7c06601d06abfffc0017d08927640898b1ffc0001f046ff0003b9f7d182a3a517b7c543c91927e9bf06837268003210c68accf6a61ff1e885f8c9d7fc001fe000b8090a9888c68685fe0002158c92b6ed0106538351be4aee8340bfc0006ccccd94c3e00cd42492942175ff000382c06ba2d03a9fd28895bb3239850820d1ac589515d2d9341303ea88eff0004ab9dffc001fe000538edff8003fc001042ed7438fbd49fffc001fe000710007f80017c7386cdf9ff0007f8003fc000acdfd97098f896982dcd22e471ec6740b3b47b92037a56ebf4087f8001706aeaf1da6e89dd23a9d34a3d010e3a64cdff800335a85fe000ca579e345671c7f802cfabf748c5a24b759f180016670d0e2a2908171d660ead23850f26f5b006a1a6d36122f3bc9f91c60b3460bff0004287104a504002870471ab19f97fc0003cc4d24077ab02d32c9d0561b0d54728b891bfc0005c02988250f11a53e55073072944295e5c3804ddf5eefd1cd84fb82b6bd4ec004a3b0f6ca8c851411359ac8a0f189c77c3b4f9890d4056098107f80029d773fe000328ee63b9af28559ea6d19d8d4ff8003fc001fe000ff0004e8bd3e5f7854e14dd88f8b1b19a825935249e242e6113b834acb4e6e8d26ed9916d04c56dfe000ff0007f8002b143126c2a2
  | 3 => 0xc058c887b55923f19a9bb91413be7ee1727b6e0e0f7116034882b5749e0a0e2ba53f010b15a8ff52baa2ac6c8c6535673797f800208f86d0f76174b2ff8002255b84c034544634d9382c55d014997b3801ed27afc5be35c4c0d830811a130791ff68b21eb76b23b7374c902906daed4361214239d0e9850dd8d0c686023ffc000cf0432513ff186a7fc00146a577202bae3e4bfc001fe0003c03c7f80016d00b091b8818607f80016dc0b306273f69f2ba0ff787cdee420561a6fb2ffc40c5c9ea404c7fe5f06e16445190e068715c1ba6faa1183c92e6ae0f09d0f31510ada0e27947b3771f8a00630de31c99838882e8b397c07286acf4cefa984cd1a590607b530bb6a3f3f289bcb67f1166837f80036ccf3fe000a33a8ff800064df1fe0006f72c8841ecd112cda3f3617625d958b9205f380050e92aff8001b41444e134ff0004eb67e492a9e207c3021fe2c70efd2ed4409165886ff8001222db2682d121b8dc907990711fe0006b04b4ba73c8158e6c118b215a288f3eb625d36cf2de2117f8001ac93dfe000734768f4b1bc9bd61b037d150455a0a4283377ed2b1f11fac33fd4151cf676f65515e71391415bf732ba819042f0ae9b1503e8a549d1cf06c81928ef0a006fa01a2c8a757fc0009e8a326861da4b93fc001fe000ff00005a02055b037a337ff0007f8003fc001b2ae2c316d38a5de38f8e3a277ff0003
  | 4 => 0xdae81ff0007f8001063f8be77ebf31d721f37ccf4b7e4363f07afb12effc001fe000b8315dfadb1ad8a850720de84cff8000c55b2f107e5948eafb424ba30d0a66cb33c5891d0f09de05cc26da0f330c4bc7111a7e3148779548baf6dd7a9a66acf32a9bcca3ca14459710e9371f13a8aac07f2c1173c815365a01288045dabf3223ce8110be6918af018b8542f852e2762240b2b86a3397031fa3a950c403bd6c2cba1bda564c9728267a87bd7a460b49348bd0e2f7567c546f73918410a560e25928110f3d5b1b0dc1351d9394288a44e4b66fe037b543c4a3557b6b474b4475ddc45765e17e772562b8a5149ddde577836cc98379bd93bf0493dfac71408928dc274ef59d9242f7981683c0045d4fe64e387af88f264aabddb23cc31744941cb4005a0c4764699918adcd2a4c95057732ad2283ccc1fe9a22e3b31090b45323c1d0351730ad01840df858af49502ee6153615b454ba4025aaa04c95e6234bd2e31785c79864d9903d4e051a9d66d92fee0c413a50886f8f67b6a2eb941325bad766333826bdff0007f8003741d99af51a15d0ccc717fc000204b6ea2f66ea057fc0005cf23ff00005c0cd547ebfe0004b72c799b33fc000fe1b1a10f5ff80021cd5ffe0007d50aff8001f4db2c2c789f3e1351f4b451c6e620ba080cff8002b4bc5641f0a13fcbbcabfd960bd022fd55b83396a7e5fd2028e0ff0000db99a
  | 5 => 0xb768bb5c8475daa3b2ec2c512980a8870609c3c963131e6f583614425602e60251dc30c992203a9905a0862e6882b78661af223d740318a7208130e1d16943da8ecbb426ab56a7c67fd2e63adc8dd39e3df9292fce4bc6ba402512d2502a9948bd0702384d2afe0fd0ed6cbe334ea94bf30e386ff00077155ffc001907f8f68c6f6119ffc000b4edc376537f8001d9c1214fad43562ce936376503a66b9ff000480a7531e8494aabe381c7f8002c61eaecd10261c9c7aa0126209c4e8aac6b0eccad5e1093ecd8cf9720ff8001298188891b01767ff8003fc001fe000ff0003d2253fc001fe0004f559ff8000a8015fe0002e8cb58880018ba4cef9571023b333b77cc147a183267df69bb37a5c5f710a1795c84cc7c94c4d8eea897784a194723fc00102800932457f80008a3a6c2c6eff0004f946bfc001ea0a59310fa1463e619ecc91b0ec8092c0f42fa5cefc2e4636af51208f38be9730107a4b6e280f870f49387983d2d766007bcc5f3fe0000c12a8d01aaf923920d2dda252e621cffc000b012ddf016783a67fc00166dfade8af560cc581ce5fe000f7560b2be511129764cd8ff0001917392c2c26caa3ff0007f800364a4da444aa75bedf044a4889f110abf8321cc0e9175bc0fc81c812ff4e32c7fc001fe000d6478ff8003fc001fe000ff0003a83bbfc001fe0009b37b2e0883fc0007e5860892660b8c4bc19d
  | 6 => 0x66adbc495334afb22a629adaa9abd9ac92afe138dd759074c8e0d5891aec35bb7a88d21ac0b0e953a82eddab0db88808718e1b075c88ac3a575a151c91d3f01598014a063bc4ff6b3afc7c379a089a607b2ff000138ac909067fe0002d378b90548702364c9b18f102ed95a756027fe0004b88b7a260c9d080902295b8677816200dee5ca3916f8d2b104c078cb3cce8bff0004f187f3e527acf770a35e2eac9bfc001fe000ff00002959d08d5c5a3fac95a8ff8000195a1fe0008842cc23ba6853e044ab4ff0001b4b3a7c1d06d0231b3770102403d40944e3d8d6bbff800035a920a5432e0ca3901e7fc001383f42468a5c0499fd631fe0005608fa72f27fc001df0ebef75f958ca060c2c820ba9009d4ea3d30049096050c92f79cab6c0c4f55e09bd9560492ec7ae3008c2c5b76e3f580df25f6bc8701b575561c688bdec5a914cec12cff80031d0dcc293ec381141840eae3f654434cf5f7d7a9dffc0018c5a11151e7f8001f0ba15c2fa0f0bcaf0c5a98d85ca748f922c4e02791cbac2cf8c3f5056f994905c81bae2c95659ff80034034bb69adc168f11b9e47ddbbbd13d5c174a7c61e18d1010f53ea8b395478a587155289f9c57cf3a9cbe8733e8ff9652070c120dd951572ef37e245c0a722e05aefa56063264de3d3b19133fe0005056923038dc5a4dfe000e87fbfc9b9ca5f975307d5e3a48733deed8c13018f
  | 7 => 0xa0a84880280da0a84480280da029ca80480da028c880280da009cc84880d20e80a84880d20e80a84480ca0c90a80280ca0c8ca80480ca0c84a80880ca0c84a80480ca0c84880280ca0c84680480ca0a9c880280ca0a9c084880ca0a84880280ca069c880280ca0684880280ca019cc84880ca019ca84480ca019c684480c9ca9c084880c9c69c084880c90a9c880280c90a8488022509cc8c880224ca0a9c88038e635912fae58917fc0005667a1e4591aa11ee56898ad1af810a4d8828110878aa2918381ed9d9a551cda639f5d30f3ca66161543a6814ff00016a5c6052449c5fdd28e5751335b07520eff3e57a26e0a5a5e41cc27de6a4c9ff8003fc0009e406ee5bada9b0d6208830939ff00045b0df285f9fe000ea6fa3083cffc001fe0009c8e081948c8451a442422996fa9320dc0eb092ccf32494eb8b0c1963522dae4b0fdff8002e0b7cccf17b46557f80007cdd65cd9cf14e49a84fef9e1d3e770e66141e97c0f11c3fe000ff00061031bfc001a6b5e718efd32783fc001fe000ff0007f8003fc001fe0002f803e8c86558741424ce3f80a00063bfc001bcfac339206b0734614fffe00090244fc2ab1892d4dcbe7d433baa02dee819edc7b7165103f330971e0f06b66ff0007f800169014ea11cff0007f8003fc00158380467e67f80020d219aacd9d6773472c2ffc001fe000ff00065071bfc001fe000d1137
  | _ => 0

def word127_16 : Nat → Nat
  | 0 => 0x894c9cc84880294c9cc80880294c84d9c084894c84c9c880294c84c84a80494c84c80880294c80c9ca80494c80c9c880294c80c88a80494c80c84a80494c80c84880294c80c84480294c80c80a84494c80a84480290da0a84880290da028c880290da0084c84890ca0b9c084890ca0084c84890c9cc84880290c9cc80880290c84d9c084890c84c9c880290c84c9c084890c84c8c880290c84c80880290c84a80880290c80c9c880290c80c9c084890c80c8c880290c80c84880290c80a84880290a84a80880290a80a8488028cda049cc8088cda0088c8028cca0c8088028cc9cc8488028cc9cc8088028cc88c80c8048cc88c80c8028cc84d9c08488cc84c9c88028cc84c8088028cc80c9c88028cc80c84880288ca0a84884488ca099ca84488ca099c684488c84c84a80488c80c9c480288c80c8ca80488c80c84a80488c80c84680488c80c84480284da0c80a84884da0a9c880284da049cc80884da0088680284d20e80a84884d20e80a84484ca0c80a84884ca0c80880284ca0b9c484884ca0b9c084884ca0a9c880284ca0a9c084884ca099ca84484ca099c684484ca069c880284c9cc84a80484c9ca9c084884c9c69c084884c90a9c880284c90a80880284c80c9c880284c80c9c084884c80c90a80284c80c84a80884c80c84a80484c80c84680484c80c80a84880da0c84880280da0a9c880280da0a9c480280d
  | 1 => 0xc8802a4684c808802a4680c9c8802a4680c8ca804a4680c848802a4494c80c804a43a0a80c848a43a089ca80ca43a089c680ca43a049cc808a42a0b9c880ca42a0b9c480ca4294c9ca804a4294c88a804a4294c80c808a4294c80c804a4294c80c802a4294c808802a4290c80c802a4290c808802a4280c9c0848a4280c84a808a4280c84a804a4280c80a848a41a0a84c808a41a0684c808a4120e80a848a4120e80a844a40a0c90a802a40a0b9c288ca4094c848802a4090c8c8802a4090c848802a4084c80a844a0ca0a9c8802a0ca0a848802a0ca069c8802a0c9c69c0848a0c90a9c8802a0c90a848802a0c90a808802a0c8c8848802a0ba049cc802a0aa0e84c808a0aa0e84c804a0aa0884c844a0aa0880c802a0aa0680c808a0aa0680c804a0aa049cc802a0aa0484c848a0aa0280c848a0aa0280c808a0aa0280c804a0aa0084c848a0aa0084c844a0aa0084c808a0920e94c844a08a0680c802a07a049cc808a07a009cc848a06a0e90c802a06a0e84c804a06a049cc802a06a0484c848a06a0280c848a06a0280c808a06a0280c804a06a0090c802a06a0084c848a04a0294c804a02a0e94c804a02a0090c8029cda0a8488029cca0a8488449cca0a8488029cca068488029cc8c88488029cc84a8088029cc80a8488029cc80a8448029cba049c880c9c9a069c280c9c9a029c680c9c9a009c680c94da0280c80
  | 2 => 0xa0c84a808a4ea0c84a804a4ea0c80a848a4e94c84c804a4e94c84a804a4e84c84a804a4e80c80a848a4da0a848802a4d20e94c844a4d20e80c848a4d20e80a848a4d20e80a844a4ca0a9c8802a4ca0a9c0848a4ca0a848844a4ca0a848802a4ca069c8802a4ca06848802a4c9ca9c0848a4c9c69c0848a4c90a9c8802a4c90a848802a4c90a808802a4c84a808802a4c80a848802a4ba0c9c8802a4ba0c848802a4ba089cc802a4ba089c680ca4ba089c280ca4ba049cc848a4ba049cc802a4ba009cc848a4b20e80c848a4aa0f08c848a4aa0f00c848a4aa0c9c8802a4aa0c848844a4aa0c848802a4aa0c808802a4aa039c880ca4aa039c480ca4a9cc848802a4a9cc844802a4a9cc808802a4a90c848802a4a90c80c848a4a90c80c802a4a90c808802a4a84d9c8844a4a84d9c4848a4a84d9c0848a4a84d9c0844a4a84c9c8802a4a84c9c4802a4a84c808802a4a80c9c8802a4a80c90a802a4a80c848802a49a0a9c280ca49a069ca80ca49a029ca80ca4894c80c802a4880c90a802a47a089cc802a47a049cc808a47a009cc848a46a0d9c0848a46a0c9c8802a46a0c848802a46a0c808802a46a039c880ca46a039c480ca469cc848802a469cc844802a469cc808802a4694c80c808a4690d9c0848a4690c9cc802a4690c9c8802a4690c80c848a4690c80c802a4690c808802a4684d9c4848a4684d9c0848a4684c9
  | 3 => 0xda449c89c280da42a0a80c809a42a0a80c805a42a0a80c803a42a0680c809a42a0680c805a42a0680c803a428cc80c809a428cc80c803a428cc808803a40a0f1cc849a40a0e80c849a40a0c9c8803a40a0c848803a40a089cc803a40a069cc809a40a049cc803a40a029cc809a4088c9cc803a0c90a9c8803a0c90a848803a06a049cc803a04a029cc8092509cc8c88032509cc88680325094c9c880325094c9c480325094c84880325094c84480325084c9ca80525084c80a84525080c8c880324ea0c80a84924ea0c80a84524e94c80c84524e94c80a84524e80c80a84924ca0a9c880324c80a84880320ca0a9c880320ca0a84880320c90a9c880320c90a8488031cca0a9c084914da089cc80314ca089cc80314c9cc84880314c9cc80880314c84d9c084914c84c9c880314c84c9c084914c84c80880314c80c9c880314c80c9c084914c80c8488030cc84d9c08490cc84c9c88030cc84c9c08490cc84c808802a5120e80a848a5120c9c8802a5120c848802a5114c9c8802a5114c9c0848a510cc9c8802a510cc9c0848a5094c9c8802a5094c848802a5094c808802a5080c90a802a5080c8ca804a5080c84a808a5080c84a804a5080c848802a5080c846804a4fa0c80a848a4fa0a88c848a4fa0a84c808a4fa0a80c848a4fa0684c808a4f14c848802a4f14c808802a4f0cc848802a4f0cc808802a4ea0c90a802a4e
  | 4 => 0x50a1da810ed46876a143b5000080c00526002a10025245490c2a4660524328750b5290da9426d4a036a541a15a8b0ad44856a0c2b502aea8c35466a9aa354d480c929039d45cb2533bf50da1a8a629483aa531d75143288d55546726a18f75143688da509cc80a845a5094c9c8803a5094c848845a5094c848803a508cc9c8803a508cc848803a4ea0c90a803a4ea0c80a849a4e94c9c0849a4ca0a9c8803a4ca0a9c0849a4ca069c8803a4c80a848803a4ba089cc803a4aa0e84c809a4aa0e84c805a4aa0e80c849a4aa0c9c8803a4aa0c848803a4aa089cc803a4aa0884c845a4aa0680c809a4aa0680c805a4aa049cc803a4aa0484c849a4aa0280c809a4aa0280c805a4aa0084c849a4aa0084c845a4a9cc848803a4a9cc844803a4a9cc808803a4a8cc80c809a4a8cc80c805a4a88c84c845a48a0e84c805a48a0c9c8803a48a0c9c0849a48a0a80c803a48a0680c809a48a0680c803a48a049cc803a48a0484c849a48a029cc809a48a0280c809a48a009cc849a48a0084c849a489cc848803a489cc808803a489ca9c280da489c69c280da46a0c84a809a46a0c84a805a46a0a84c849a46a0a84c845a46a0a80c809a46a0a80c805a46a0280c809a46a0280c805a469cc848803a469cc808803a44a0e84c809a44a0c9c8803a44a0c9c0849a44a0c808803a44a089cc803a44a0880c803a44a009cc849a449c89c680
  | 5 => 0x90d09d408f6a22d149256a42ead47646a0ac949565a8ab25238e6a259921a78a886a544352a4159298ada8a565452b2a1cd55108890ce348671ea1b1121a80a886e5442da5316f514b6a8a5b54324a431275072a94d95486772433bb511dda86eed41c245361129b08a8b7848667a4333f5159fa88cfd4125ea08c5298628ccf3d4479ea0bcf51da9a88d4d41ba292dd148c4a94c254a612aa2a750993ba85044268221341139a089cd04541826a3955298aaa8a555493ba431dd218efa890348681a8340f50c9ea4c4f54698ea24c751366a89b3541d9aa055951a5ba8ccbd4197ea24bf51360a89b0541d82a04f9510d8a88594a62cea2965514b2a873754422a43395219cba86c54869daa21a1510a894c54d452a2a295150c8690c244a612243091199c490cc348680a534cf5172080d90545bb69258f492c7a45a34a67b6a23db50deda82f6d40c82a2b5b515ada88d6d416b6a05db496eca4b76d24bb691dd948ec7a4963d22132530992984ca8a034a601a5300d09806a8b5c4a6a32a2d195068ca8146548a32a4a7f5153fa849fd404fea4a7d2993fa8a9fd424fea027f5260c84d06426832034190186e90c374860e2430712183884c2e4a6172430352981a90d48544a42a0d2150147a85ab486d5a136ad01b5720dab506876a243b50e1da830ed4006a530352981a90c0d48606a136ad01a95a4d4a540a52a4c3b
  | 6 => 0xd416e6a3ad54916aa44ebd4764ea0acd49567a8ab3523b3a4311f5071c90d6c486b62235b15112fa83724a6b9282a2f50b1890d69486b4a235a541199a835d4a6a1aa23fd21b4ea88ffd437fa433ff50db5a8b42949d0a535cd29ae7a0b73505b0e9158529ac2a8b61d044dea1bef41529a879d4a6c5a5362f41716a0b5ad244369257d2984490ce148670ea0b6d299b6a4b2ad4109a132a509953a88a9521d72036b901b5ca811bd468dea2299484aea8052541a82a3541506b0a8d5854100a431815002e90d1fd4453a926c551362a81b1547aa2a355148258a40edd4752a92a9548e3ba89af540d7aa3ce5510caa886594832aa4145298a3a8a5154528aa1909219c090cc1486936a2505510dea885c4a62e6a2971514b8a864a486cba5365d219e090cf0d44786a1e1629b0a94d85545bca43345219a3a8ad1d440ea5340129a0080d32d45b12a283d2981e8cda24a6d12033d350de9a80f4d476aea0589496c4a8a024a601253009516b680d45540a2aa45155253da809e4064f6a041501a0a80d054e682a734155020ba8e504a6282a2942524a0a92764863b2431db5135090da8d06a4aa2d2551292a8f49548a4aa4c0921a05a0d025062769313a4989ca4c4e526272a31855003490c1a4863e2431f121a2680c0b4a605a431e9298f490d47544a3aa051d51d45a810bd4385ea042f51cf02929cd404e6a0025218f2
  | 7 => 0x2435115075484daa8e6d52734375044e90c274660224328350a0fa82add44916a248b50959a8920d44906a123750d35a87a64a6bba535dd19aeea0b77503672922dd4916fa87944a6b42435f521adc90c96486cfa5367d21b1a94d8d545b5a431c15112290c91d44cda5366d21b1094d8854541a4320f512f690d60d24b02a0a2b50515a804dd411b2530d9199b3a82bc5255e6a2af148d79a8789545ace92d67492b3a475ed24af6810852196094cb0486942434a351251a8611486c0a0360539b02a8f1ad468d691c6b50a35a8312d404629364929afc90c98d43d025323b50f3094d4d540a6aa453151a98a80a44a6a8aa318e51f68a814e54019a530512982888d0f4a687a0343d4195494caa446552132a941954a8c404861624301d11b64a88f5d4320a431ed21a19a86e9d431fa430ad2180c88ce6d433fe919fb50e2fa8299d43d2a5364529b228cd9150543e9230148d6da86b6522c9a5312351491a837c446b6a2325511b3c94d9e446b522324111b3494d9a446412235e91187894c3c4666125330911a5288c124465c6a199d50ccea8316d4135aa11ad51c7c94d154a68aea2c57510cca843b4a6102530811195e94caf44693a2349f50c5294c10446c022360101b009cd805478cea346751633a8919d238cea0ae750ea4a8c6954334aa08612983088c3a4660fa2349511a4ba8a0e44640ea09f751511a824c
  | _ => 0

def word127_17 : Nat → Nat
  | 0 => 0x7d3bc3bdb3d3b93ed3edb6dba9be5bed3edaedba5bf93f93f9af9bb1bf5b74b75bb4bb9b78b79bb8bb9f3c77cb7c7bcba9be9f69fa9ef4bf4f74fb0ff0fe5be5de5f65fb97b87b9bb8bb9f38fb0fe9fa1fe9ee9fb0ff1ef1fb8fb0fe9ee1ffcb7cd7cba9ef4bf4f74fb0fe57e5be5f65fa8ffad2af73f3af2ee3c76dd6d77b73c73d73ae28fedd6ceb8e951a84be4866f6a037750177a8abbd43796a1b4f514e9a8674d41b82535c3415fc90cbd486396a11c750975a8abad4378ea1b4b5170690cdf4a6b7a535bf415fa90d8248639ea13e350647a857f48649a4324f50f3890d8a46642a4317f514bba8a8f48647ea1e6521b0c8cd86545402433df505d9a82ecd40656a0b2b5017fa8921d4490ea22492190890d11d457ca533e551b4894d64d2404253595515f9a82fad417e6a0beb50513a82164a67d2033635070ea8b71d24b8e82dc5416e3a07715030f2432b92995c90d4b4a6a5aa352d5162894d14d451c2434910986490dad541a7aa04635006890c154a60aa4344101a20a0cab4a655a432ad09956a0cab5469a2033a1219d1a86c7486182530c12199ba833f54436aa2169298b5a8a5a5452d2a1ce15108c90ce748673ea1b19219afa825e4a617a530bd2985e90c2f486986a26b151358a832ed449eaa2163514b1a87365449d2a214f5144690cb1486c7aa2dd74905090c054a602a4342350c5a90c0c4a606
  | 1 => 0xeab7baeabf2bf29f6bf2cfb6f36f2cfaef36f2ef36f36f2ef36bb6f36f27f2bf36eb3eabeb6bb6f36f33f2cf74facbf4be9be9df1bf1de97e4ff47f4ef1ef1ef5eb4fa5fb5ba9df17e9df47f4bf1bf1bf1bf1bf4fbeb3e3af73e3b73abf3af3af2bbb3f38fb1fb1fa8fe9bf7b3eb3eb2afabf28fe9f78bfbb3ab35b77b27b67f25f6af73f33f2db77b37b35b67f25f6eb3eb3af3af3eb2eb3eb3eb3eb3eb3eb2fb2cb7cb7cb6cb7cb7cb7cb7c77cb7cb6db6dd7cb7cb6db7cb7cb6d76db7af33773f23f67f3af3af33773f2bd6bf29f6bf33f2bf3f33e33f33bb2fb2bb67b6fb3bb3bb37b36b35b74b77b35b7f33f337b37b3db3cb3db37b33f2f72fb2df2bf27f37b33f33f3733f33f33732f33bb3bb3ab39b78b73f3e73eb3c77cb6bb6bf29f6bf27d67f25f75b6fb3bb3eb3cb67f35bb7b33f2dbafb37b2fb37b35bb7b2eb3eb3af3eb2eb3eb3eb2eb3eb3eb2fd3eb2cbbcbbcbacbbcbbcbbcbadf3c7bcbbcbadbaddadf3cbbcbadbbcbbcbad7adbadf2bf3af3af2bbabf29fabbabf33eb3ebf33e33f33bb3bab7b36b35bb4bb7b35bbf33f337b3db3cb3db37b33f37d3732f325bf1be5be5f65fa8fe8fedb65bf1be5be5f65facb7cb7cb6cb7cb7cb6cb7cb7cb6dd7cb6cbbcbbcbacbbcbbcbbcbbcf3cb3cf3cbbcbb17e1ff5ba5bf5af5bb5eb17e9be9de9f69fa9be97e9be9f69fb1ef1ef9af1ef1ef9bb9ebd37c37d3
  | 2 => 0x2ad8522b52ec4dc50de8005c97d73e9ef2be3fa3fa97e9de9de97e9ee9ef4ef1ef2bf2be9eedea97e9de9de97f4bf27f4ef1ef2bf4be9ee9f71ef697ab6bd76b76b7ab6ab6eb7ab6bd76b76b67b7ab69f6eb6ebaeb6ebb3b63bf1bfab7ab64ff47e4ff47f5bb8fa1fe3f63f65f65f69f78fb1fa9f65bf5af1ef1ef1ef1efeb3e73eb3c7acfad7bc7ad7bab71f7ab63f69fa9fbcb7c7bcbb4fb0ff57b5bb5f31fa5fb1fbcb6dd7cb78778b6db6cb7cb7cb6cb7cb7cb6cb7cb7cb6dd7cb69f793f9778779b78b63be5be5f63beeb6eb6eb6eb6ebaebbeb3eb23bf3afcb7c7bcba5dfab7a7baba9f72f70ff0fe3f7cb7cd7cba9ee5f73bb1bf1ef3bb1bf1eebda9df47f4ef4ef1ef1ef6bb6baedb67b6bb6bb6bbabb67b6bb6ba7bb6bbabbababbb67b6bb6ba7bbababbb6bb5ba5fa9ef9ea9ef8ef8ee9ef1ee9ef1ee9ee5bf1ef9af1ef5bb9ebeb3e73eb3ababbabdbabb3db1df1de8ff1de9ee9f64ff0ff6676d6bd7676bd7676cfa8fec7ed7be72af7c7a5fa9fbc77c7bceb47f4fb0ff57b5eb5f31fa5fb8af8b78ea7b6bd7ea7cb67d6dd78af8b78eadd73ce9decf69df47f4bf4bf1bf1bf6eaedb6eb67aeeaeeb6eb6ebaeb67b6eb6ebaeb67b6ebaeb6ebe6becbe5becbaebaeaf4fe6be6ad77e67c77e67c76d76db7e6be6be73ee3e73ee3aeabdbc77aeb3cf3db1df1de8fe97e9bf1de9f6d5e8ffc7bc7b87b8ebecbee3a
  | 3 => 0xccc4941f4c06005c01d29de80f18e4df4c01d605604f10384124028cc578d7482c154016178c01dbdc00ce4c00c00c00c00c00c00c17800ce4c00c00c00c00dbdc98c01c390e4c01954018c06895c18d16c0680a92cc18cc0018d16dbdc06895dbdc07c95c178b95bdc98c01c391aa4e4d54001976007c019aa40684c9bd807c4c801c391bdc9689ac0199e018c06895c18d16c0680a92ed2a818d0a018d16dbdc06895c07c95d76007c06818c04c02801c0943909ac018e2007c0684ec07c4ec00c01d165aa400ce4c00e0cc00ce4c00d78e0cce4c00c00c00d164059aa116516c075aa62b02c12cc0a80682811662b4c012a80a80692ec2a44a8014015f4c015728015c2df4c4a9c2c014dfc01dc2c18c98c06801cc00dfcdfc01c18c96806801de809acdfe2b00180a8e4d54006973e2b40180a850de8006973c0180b80cc0a83900a9f4c0cc0c80b83900b80c80a83900a9f4c0c80cc0b83900140140140c80cc0b80b800c00c00c00e19a2b40180b8c000c80cc0a978c019f4e2b40180a850c0c80cc0b9e800180180a80b800c04000c03c00800c00de80008e4c00c0a80b9c01f440b40b009c39009c0b4980391c01f440b00b409c3900b00b409c09c00c00c00c00c00d9740605d5bfc511c2cf101b9bdc2ad85060401d2ec1b806005e19219005c06001c9b129cccdc2c0e619001c6585d1970aa405c50c00dbd90a0
  | 4 => 0x300018544a0038121aa03b9aa0de400018c06401dbdc05daac9ac18cf1494018d16d16c18dbdd2ec01c06495c18c10095c1a4de41a44ec1044ec0f84ec01c06005c0b8e4c2acf1979018c18d16c18c0b98592e0e5018c60003895c0e81a405095c0e81a406005c06129c05c60001c95daa41241040b85d80ba1980b801c0b80e80e8061aa5aac0d40f809c5da19809d2800e8a762b0001aa51640fc9b12ec2a40fc0fc18c01c9acdfdc2c18dc3050003801d3e0dfc0c8121160de4038ccc1600c8cc0945f4c05c06001d29dc30f189adf4c01c04c2a40545d84ec2a44ec1042a404c10416001dbdc4c9161f4c98c50c05c98c104f18501c30e4c97098c2ac0cc97098c03803a2b00000e8a783b9f4440df45f440b42adf440502adaa44bd1658504a4038179720824e4c06406001dbdd540e0818c95c120f1094418d16c18dbdcc0178c01c06495c18dbdc10095c178b9418daa4e4c06406154001dbdce081bd605aa41244c80d44c805c0600b8e4c2b0f199e018c95c18d16c18c0b98592dd78d0a018c60003895dbdc05095c1bd97405c06005d29c0604c801c95daa41240b85d80ba1980b801c0b80604c8f19aac0d4f1809c5da19809dcf0121cf1284aa9cf1284825c2dc2c005c2d03418103419dbe8ccc2c1c2c2811658505d001c18cc0001dc2cdfc01c18de804fc0393e1c2c01cdfc0cd164de003801cccc16095c0c
  | 5 => 0x9780b1d58ad800c010031e180ec0685100e5e1950de1950c05c0900140605dc2b009094000e2b800d4d5bfde1530026808008097c08000c17e2b903801801406c29c06801a0d02bc29c060bbc044018bfd7912c46f95fa0d00694ec2be2b9f4c0ccaa003a2ba2b60d219406c07c0182bc061790bbc04401a1952c4bfc6f80195fa0d00814ec2be1899700d1e200d116d16516428d721aa428cde150c28c28c28c02028c0216046f950c28c02004898828c020de160c6f950c06006002001c95d604b986f8060020de175d4d0f1575cf1e2b85dcb9185c4dc4a897ce1c961164e1c9600bd3bd0300d00bc94575d9719800d00984b409a19e18cb9175d4d0f0c091e185dce1d85c5de2b985cb918544dc4aa2b80d1cf497d03103904000cad800dd599800a000dbd800ce1c961164060960ad9bfc06178d74097c50c061d5975cf0ce1d85585d0384dc4aa2b897df41f40000984064125aa573c4bdaa43b57204bcde00681a573c4bc0604bc8240e81a43b5bc00681041043b4de1f41035e1407c0f80e80f83b4de11601a40e41a005c06010412482000d2c000c1200fd16d165aa40fc00df480d00f516d165aac0e40f405c0602b02ac0685d9aa00645dc121aa012001c6f46f0121aa070c6f5165aa06f46f006406800516000c00c00d43daa06f0f141bd160bacb9405c18cb90f1400c00c5d80600e84c916197050c05dc01c
  | 6 => 0x12400c00400cf1c0dc0d5cf400c1040900fcf1c1240f800c0149a09a8df9041bf0971aa53e560070160de200787280442883b80453e560070160516c505f392e12e1f380b94e1aa41255f870160de2005c28929c01c95c3b801c0b81bc0d55f851c70160400c03806810005010007c00ce4c00c1040f80140fc0080000080000fc1bd165164701cfdce9980f1c05c18405c70219c4b40e59780fc0a84b40a804c01010400c00c00c26800c018014019aa41247000d47000602c0018bca0cc04c060bc8065541500e4c2a0e4c185e1554005c98c2b40682b406916c2b6188c012cc2b516de14104b940f82a0b95aa4e4c185e1554005c98d76007daa41047000d470001a2c001a18805c2c20cc018bc9f4c01804d540e4e18805d50000c00000000c98dbdc01c1412cc0a93c21880a93c098dbdc01c1409692a804c184390140a807001691640a80cdce9f4c5e0391cfcccc0a9f4c0cc0c80b81400b80c80540c81400180b800c00dc000b5ce9f445e02a03909900b4981c00be1f440b400075c00c00875c00c009e21e1812116d1651640ddaa412407c07d510068028068029f4d6047000f807c07c0482880f80480c407c029f445055fc70160c06006002929c01c95c01c0b95fc701604ba0060029aa482482c82482c82578c110cc5604ba185de1005c5dc2ac2ac05d87985d8541240b84b00ba2c1cf412504103903800d
  | 7 => 0xa68c8518c229145008a01140228045008a01140228045008a01141a2524466880d0e9a1a2430086110a0214641c08385069a0a1412481c1038207140c081850282051408480890011fe33f667e00fc01f823ec67cc4f909f103e207c48f781ef03dee7a08f319e323c2a770ceca9d493964724ce301c62388e6f48dd91b9636686bccd611aa035446a18d1219e133a26700ce099b13342664ccb29911320263c0c7898e3316861c0c38986230806104c1918122fe45f48bd917912f025dc4bb297112e105a0cb2916312c44580cae895c82a8254c4a91150129ec5254a209432282250049f893e127a24f049d893a227024dc49b0935725c64acc942124523ea46a089190f3218242c884b90231fe63f147ba8f221e043b8476c0e521c6438486f88de01bc237406e88dc01b8236c46d10d811ae235886a08d311a4434046788ce019c433086500ca2190032046388c64184430045fa8ba017422e405c80b9017202e485b88b6016c22d405a88b4216422c485780af215a42adc5210a27136426544a1092511a2231044308240fcc1e043b887610ea01d4839887210e201c4438086f00de21b8436986a70c66181c2c885820ac015842aa05100a22140427904d2096412402480490092c10d01fb039007240dc41b0835106800d04198832106220c1815002a105220a1811181f103c207400ec8142024a034406080b600aa00
  | _ => 0

def word127_18 : Nat → Nat
  | 0 => 0x8180e50142028c0467fc0ff85fe8bfc17f64fe45fc0bf707ee0fdcdfa03f427e42fc49f793ed47d24f9c1f38be617ca0f945f20be327c22f819ed43d267980f305e593c9278e2f181e33bbf876eeec05d78bae075c2eb45d60bab17542ea45d403a8274c0e98dd18ba217422e809cf139c27342e651ca9b9227204e391c51b8737086e049bf937d26f64de45bc037826ec6dcc5b9137036da4dad1b38b6616ca4d8cdb01b5d26b64d649ab9b5416a62d489a80b4f169c0d385a68b4c26942d249a38b46168a2d109a11b3f56748cd899a1332465c2cb45960b2b16542ca45940b274646ac7858e8b1c26342c6498b931526264c44588130e061c2c341868b0c16164c24983930516082c0c98092ff25fa4bec17d8afa15f20be417c92f715ec0bd857a8af415e60bcc17982f315e42bc49778aee05dc2bb41768aec25d46b9cd7202e445c04b7816f1adb45ae0b5d16992d115a04b385668acc4590ab0cd6002c005802afc55f1abb2572aad015a02b405680ad055982b305664ac455812ae35560aac1558aaa75462a8815112a0253caa64d4b229225204a389460a8b75082a0c940aa7c44f089d0939127064d4a9945320a6314c4298492f9a5c54ae295852a825504aa095412a825514a84948129025214a209445280a4f149c2934126924b14940928125024a049429241248a4804908910122423c447028dc51b0a35046
  | 1 => 0x208c043c010300400040080000080340800008041a2600800041101004080105830040109018080101828000d0081800000180c00001d0042a000500000000180800170000c06020000002020100c0402000a42403020080205038780e000183804100000000157c6af0d5d1ab8356c2ad855b0ab6156c2ad8d5a0ab435646ac05581aae35582ab05560aac3554aa98d520aa435446a805501a9e3539aa42d431a8494f8a9e25384a6894c16958d2a5a4a548ca90ad1c1a36346868c95172a2a145468a15121a22344028805101a1e3438287050e0a1c34346860d0b1a14142868485090a12342068385071a0c14182831d033a0093f067d84fb09f6b3d867a8cf419e633c86788cf019de13bc67704ee09dc33b427684ed09da33b06758cea39ce139ca72ace079b23361a6914d0399a93256621cc1797452e0e5a84b5296612cc65914b0695452a1a510ca11940327c64f249a392e72512480c8f191c9228a440c87190cf1fc63f1c7b08f671e0e3a947318e431c42388c7018df119ca32a46108c23180230145e18ba1174a2d8c5a18b2316062b8c5618aa315022a0c5328a211446280c4f38987124a2394453884510061f9c3c187670e021c0c37586430c4618242c085870a42148429085230a02140c27184c10986128425184810906118423284210842108c20383a706920b241218223040a070c0d1818302c605140
  | 2 => 0x480600030000e10068440a1d0002c08390182014000c00020020002402003680000010402002000185c1e0203800183701000101403000020d1e800080c008280003000180e04008c816020002c2e032200008020080c00001e8080e2a0080000010100402130081c060700808541a01068001a0001406090303c000400800120801004140309800060400014020800000120210004060200808060000004040201800123d0080026110500008130a00802000200c0c000a80800010001808030c0080015000040012138140a00000040c2902828bc000c80024000480410060280408100203c040e0005c1000121401600028000a0302054060902018000e030c80a0001814221004000080400004341e000046c050582c040601008140c0000000000000000000101006070d8180a00000080c030081c02510800000280a8300206018fc14000b000080c0f80404000e804020503010020701800040015818101003804000a000540800008106802008000002000000c01070300003018080000008081c000081008020003804030186c021a00004040202818001a03018bc010000012000f81c00000000400170002c0a0a0182c040f0401400190600c0a01030000201000040002018141200008000001068140607000180a0001008000d0398804000b004003e0181000020101c06000c8000a000181c04010800000000
  | 3 => 0x1a346c7f80000b0988571578ed7f8007f8007f8007f8007f8000003602098044a1f0710404000005c0010190908c130380400340d800900003844003304020320601818045527820360b010000a09008200a00001ac082e0100c50040b030040204844740107830141a1f0300400008201e670600c04050801c00000302c2203028640003150586a03018184c0122004041d03830140c810349600138480a00050000a0d000205023260400e0c048100200018040c00128200a1e0a82800640301c12040810000020414c2c000000c2e39010001c100086088060101c02002c8180c030002416371180c3c02020b804330c05804000b13c08050f1348e07240000a04018385a0f188040e040605016040009402220480008660900808070b00c020a0000c0009000400802050540003030001e030700018090780004040483012110006c2e02098000c060004404020581408000500c00020f83000020e85404041f84c08002908c20061081400016f800120e0000400010302c180714024060205004482f058185a091100804100000400050081c04080b80c120600048001905888000a018200c00060a8300201004080b0001c2e060400400090782c1e0d1080406020202c22020100c02210083000040181808020203c2c0b1185c023e05838040d0a010040a000040800090000e010880c780a010000216050002a05000
  | 4 => 0x3d9d10ad2bad512fc4c759ad1643b323a25a213f7a3b5b4c57a451cc605bff8000019d10080fa0127f8007f80062510f6839bf37910dd09c4935587ae2077f61d1caac2ec3587f8007f80005bc35b2caaf4ef455ca8b1287f8002a866118d1035632e42f01d9a7f8002a098ec0cf093f76308a3ed00573ae77c79d2a7e8454cee37b06af0f88b9c296fca01bff8004ac7210cea12121a318f3c824c31c35411d1047b7f8003518d3a55c88d3c130f17f800609a740839181f4eec84a841d38d807f8001e4d08b1fdff800183e6f004331bba124e2532afc730aaaa53f7552e7d5daa19251b2dcf01dc526e7d51f9cbc859d6f891800114103b9006a635cdd594d60a6d6a943eeff8002e0f8eb9d2ac2beb432f7f800771210f466ef5c4f3b6baedb9435938099a2eb667f80072d457f8007f8002f96754db02957aaa563be0b97500a77000de0e72ca342a1127f8004eaa5ff80068a1c2c852bcd07598344782a6c8aa2eb9a98c92b4c6efd518ce0e6405a3d98b569c6333132bcd6dfa1095d96eb2588a9d7fff8002a01916bd2ff8004959fddb2088af8649e796851ff8005fb89ff8007f8001e1bd1013114b9ef14087f80023d2e651f26dc78eeb4e31047bf91860af101d86f1a3024caa79105339777f80021d3eff8003c375ff8007f8004320c815cd30976ff8007c51162d3a3ac800aa93c7cb6ef3e6612617f80061a6
  | 5 => 0xc405cfb875d0480ba3719c3b85a1e575097f80064224d6c951c20e71be76c0f2c7114343050b079e39e1898d4ff8003dc418eddc2f24f0cb6cc61d92e8dcf40b71b2a8882fe9b1b1cf56d65099b9316b951f021f4432e0ff8006f9c17f80044c1e8fc4014b884f8aea8808f58fb1e961b45d7b74960eb3e23992862f5a8a1a02da4f3895772809f0329d4fea31a2cb5cb0ea3266c75e925b2915b738861e9aa6a4ee543bd10a059a9acf8d68c4560565c6ff80032dbd862b75d4b87f8002b3827cd4c1c9e97f8000021a8d5979a3e898d74ff8007f80058142ff8004a1d6ff8006b2c3af34317d4aadd826292ad09ef9f8d3e637f7f8007f800581c69f0efbbd197f80040d25e741a9b42ba3a40615ccff8007f80048224055bb49c054e48c201ad32ca4618ef690d83e0c7ff8007f80010c1247c8b1a8c4724fdc85d6dfabbd75f6528facbb348897306275b7025300913c2cf598277f80029bff39c38e6b439a3373b5b859c55384badda25415d960c87d3b59eece34707f1645da8cffb70ab999b017274848e26504069da61f803f22399f458da01729ac7368ccb1b8ce081d6dcadcec4681cb11ab66d44c33433027b940a8fb835e127ac250b01158a958dc07f8000c3b0e88853fd5eff8007f80017db0ff8000a4f3f33cab444173129228776e07fa5968f39a88b52d73009d81ca46aaa86360834db08d80e3c4483250
  | 6 => 0xd557f8007f8007f8007f8003b4edfa2e65f59f359ed04ad32dbb632865af08754be3e80527f8004a3c0f1007af2a041d277f80042d9654b7776a95bcb1f7f8007f8007f8007f8006800d7f800782b7c9aebea2f4bd408cc0689c32c7f8001bb68ff80017dc7e2812ff80057ac07f80042acb650f0e752c3b9197f8007f8005f547c947dd55c47f8007f8007f80025841ff8007f8004c3d87f80051dcbff8007f8007f80066313d4806ff8003bccf410d7323a6e54177cd841793248a3dd1b854032562de95a1a1de3fe543f6ff8006085d9557d7f8003a935bb8e0f24d52617a8b227af236ff800751e7448fdff800511137f8005c9c74f0f21c0ca3f504513f10e137710caff8006dc06ee04e114f03e2d9032920c504ce454992d4faab4ff8000008c164198fcbcb5c24f3dbfe61ba34dbbf4d3350d143a3cfc7bccb6ba1aa8bbe9579ab0714c10e1ca3aff80079d6b4e48b96cf162079283a3798d9be89f5a5dd25d8c51c613b8626856455533a5d9411c9eff800742c31acafdf4a330212d69d36daee7f800364e1ff8000c5ee028673c460183807f8004bdc2b0886d390d6203dff800330c27f8000eac7f1c31ff8007f80005d282243deec86075588346d7f8007a32b65523e5df0b9824319149c94723d2501887b54d28b285ac88bf48e42f2ec5cc7c312089bc972e265ff8007f80029bd04241501a98e543fa30a8d
  | 7 => 0x7f8005b4bd933c7b5cb3c2cad59bda7f8007f8003ea11ee278f09abf4b93d23b22f1028ab4c352f701b3da51345e2ff795ebd3d4919bca72c1c7f800735028b0fc0324c745dacb088e445188d9d6f26d01d177f8007f8007f800642fa8911d9aa31ff8007f80072983a8d65dc154ff8001c089f2dbeff8000e826c708d9ac6aee24fd9b1cff8003f1d99b0b0ff8003a8bb7f800322e76aa7156c3aff80034ac87f800538c6ff80065993b4375209027f8007f8006634994a0d7f800012757f8007f80073cdf7f8005991b3412a7f800431bed0557b225d6e8ae02d3cf2c33870147f8001708aff80037223f8a8d1c07c7f80062436e3ca0ff8007f80031cdbff80045b0780d24ff8007f8002aa57ed185ed44888103bcd38a0a77da5f20a9d52f1fa383bdc89bf61b8e8116c902f6e250eff800504031ea8542dc0ff80023b73ff8006f4fcacaef9755f5230c7f8000342c22c9e5b3a5bd464239d00414627a8e0d28f9f4f4108884ea7dff800310a5b1970ce92db14c60850aff800434d7f89cd2b5a68b85f7f8007f8007f8002fcd1a5259aa337c240bf2944edc72ecab457531c59be60374ff800373d409ab91adedff800720f819a965bd07e6848c8b7c3bb61d0977e61f33412f471e45c2ed7f8000c5928b21841c61ff800232a6ff80059b3bb80d6ff8007f80045c13a29f6e1a41ff80059251fa381ff8007f80077
  | _ => 0

def word127_19 : Nat → Nat
  | 0 => 0xf44410bd2b9a11f3f8258303637a5cf86158b82705bae057abc7f8007f80068a55f99822cd837f80022d0caa10c98203460e2bed8d7f800143e9f00fcdf1f67f80037a992422b103172c094722e98904235b40b6180b523e6c45976509a6966ccd6f320b377a92fa3912c3697f800300b4831f556bb96421d60165f49379e2681bc6dc3248a937fff8002d3197f80077db12dc30acc667f8007286fe2c7abd1f8b9b03b6a987f8007f8007f8007f8007f8007f8007f80070ad52581600456c98897f8003ed1d7f8004f8f7ff8007f8001501e011c181d125f97a290af7f800160c4e3aacff800022fcbccc885023bf2ab918f75a0c77f8007f8006952d9990b6c3b7a88db885b4ff8007f8007f8007f8005414241d1eea190ff8007f800225ad28853ff8007f8007f8007f800199c07f8007f80015c59dd17023959b1babff80041915b6878819f74756a1cab6ff8007f8007f800759daff80006d704dc3b4b238ef3132880b21d6671bffb2a97842a40c3035fb00122480445cd2995d3a88acc2a472c0ff8004d47605aca563519edbc364c4ce54dc3c27184cafa02b72c7c94de41616ad3b213fabd2bc30741b6af8eb7f8002aa5349a4a47a01b0377c50ea3e2bcf41d463b7ce140431db78b57a4b8cffbcc6bfafbada196cc117f800371da25b3aff800450bd808dfac101990ee49920bb22d56a09941cf7f800321d5ff8
  | 1 => 0x5312b17c7a75468bbb113abea9bbdce1c230142ed4a22018b27f8007f8006ec09ff80062c1ce79a3691e57f8007f8004db0f6591e65b86d7106d622f48c9a2e920574b5141403c9cac6d5ab8c22bb2869bb8a2f48dafc566e4f582b1610df93759bf3bfce9140f8aad96900f79b325a0a9aa9ba50ba6e0014a8c1ed8a554bc49ea94dc1b2a5afa49069dfda7d25891134a1584afb330a132a4307d1e896355818d8d231c023940c174dc60c5e28b087ca6471803022091c4aaba32fc13fa45d7bf4aa796367a68a835233de53ddc5a1df2b5a803cb11b8ab1a06728a341487f8001028afcaf30752b058b3f15f708336d900654bdc3c0d058dae41a0d8f8d1820d67f80027272ff8007f8000c4b7f58f5a80fe463e57f8007f80034323f6956dcd6c550bd6987bff8007f8007f800569111cbf603b1bf2d28aebee7823557243161309f58ac5302ff8001f52ef2b2921d89c994935df8b407009b3cbab76d187edab422eb5bd25a0b7b9df836e2e4d064dc8f409cab9bd9886da1dbd379aec6c7073aa195286540c937b96d1385e9904f2035b188c96a8295c37f335342beb5cc1345bb8bca525699c7f800373a2d423168cb9e5d22d40825b18afc5613b526ae4c3ff80030db1a9c018f149ff8005e2e8a592cf239955ac5248e552b35b1b577c40fff8006dcb1a4da27515e8f5032db151a0368453e7f8004c06b3b5debf1f
  | 2 => 0xac0d224332416e36b6f7b371f3d75ac1bff58d7e1289369873d0a40d1d846ca7025d0033e03181c77419019864602d41b3b149e16db0dd78d97b1e86bdb776521aca2bc41b81c22054bd5732e36ea8bba3f3d7a6690b127c5923a5f3268b5b2b97db5e9ee88411c88ee14eff8004ddabe6506f8c659ab5feea332901f76a83351a63cda2e45653f1ea9a3f0e4c9d19c43f0c94ddad8db5ecf2bc910bc5954b7522b2f042d7414b9e38d6440b4ddb3bd938bb9f5984ab1c2cc3cd0b819b98b8dc555ec799f825d7b1b92e82585c03d3e14884f1e9bf964b02dd1530491235ab55c2b036420c57f8007f80018cbc7a883a893b89b090c2784d98c1b16d7f800241f0ca8b693811de4c063837578ad69b6508caf1990f9ace700987f138be50a7e04fe03d3b8f57eef1b257ca38121f7f8000e34d53c5a405aaa2301e1b953ad423b0be26b8e3fbc64ec00c2338ff80040d3aff8007f8007f8005a99aff8007f8007927f00de6ff8006ca3eff8006dae251bd4b8a1ba2cf334de0cb880711cfa94f0d3378b200da52801b58b36d8fcf34599871e51e2ff8000ebe0eba64ff8007f8006830f81453b95724739b24c9cc72aa4e110810136e94421097fd4201192545a5175bede6996063326cb4dbfd625880ead56e2fa7750148ca2159c1f91e30a7204fe89c4c1073a6c82752604f90113b47dbb72eb4ed0a2cf92842803e154d7c
  | 3 => 0x80017b0cb7b129288ecb18e89a719807e1997f12297149db7837ea1b2678d43934beb0c9beec3d6abb014c5bced16df97460230c304bff8001ba10bdb277f800695b65c524073aa7f80017175948da8f95a149831cb223d8a3ff8007f8002ab54e5579461241eb70d73999318d81a8b74b8ac320baa1c0a898970c3a058b87f8003450ff3353bfc2dae1f03f979b14daff80001bab4036d84a7397d563535db1dcc78b867bd2f6ebb3a65c1ff80062cefd02d3e2849902a4d94d22b4cdce12fff80035a62183db0a031ff80027a080a4a07f8007191a23bcf065767f80026d76f517ea286176029ff8007a59b59dd1ff8007f8007b25e4699b338d8ff80014a936b5e1bfc8ee290a7f8007f80022d51b0b32d2bfeb4cb4373c209d6492ccef00a0d5c8582ded7f8003f8bc50a21968e59acbb9c310ff80053c1a0f3f961505ff8002413eb73b2c5b063051820131ff80025bd1dc2ae62c2173ba3ff8004db4be8369ff800021ac33cf6893b1ac4c99b3c57f8007f8007f8007f80002b2bb733f473d0905747f800758f1d48df06adc9152cb0d597f8004a54a7f8007f8007f8007f8005c45c37dd9ff800464ca56b5f6dbfd9f916671bbb0a90e01c2c78a62e5754b39223391b1cdd9eabd9f9c645b058e1230444ed117c871c59a42b41197d4cdc9b429a5570dc87295ca8bfc907a8785595c5936472b0b8c3bf548f692160a
  | 4 => 0x6ed08973f0605b4c967b3fce51ba79718e2f6415c556b6aff8007f8002d5867f800051fb53b6a76d523525ba527363a91d9ca17d33918d235f5353cc2acf94322493ac9ccd90ceca0eebd8ffa6b5caf07401445861bae9d95084e9868752c4f727ad26bb4eb207ce20923a193274da4ade0303e82f49873c7e853df78d067cd1adb16dbb0818f4cc06df54680c7f8007a5db4aba8a92ff8e1cbbf5af7f8004f483acb8c0c8f57f8007bd381b5f6cedf7a44c17d435f85815e86aa45ae96b2c9fa22ff8007f8007f8007f8007f800635e2451a68e471bdc8166aef2f122ca4bb0d43e94a45b0028fabe4c24c80001074b00835089128c39489559468d5982545d673c68bba05b38b2d06d6402152861c02e5410b7f0228982e6c15cf6727f93359533a563ca4be54d17ae7ff8001a172ff800263c019d932b2360c3e9402295750dcd451028cc6ddba7b199aa918bcbc1be4075757187c82ce8adb1a70ff800779a9ff800345e39844ce0bf054b0d782a0bd17fecd783eabae59c3c04f2d6474f11e6d2bf37f8007f8003da270024c9e8948cb6ead82fb5d00ff80046d1e575a597885fa2a109af8aaaf47f80063151ff8003f044cd09826b98dec0acbab34bc6a47402e82cdd54220680ab545419dd3028ace4a42eda0e813cc7f800343b553b5d0c3f2ff8003793e25c1ddd8c86f4dd28ae12f910003ce9d9d2679a3c14f8ff
  | 5 => 0xbc40f4109df223069e2a52f9ebeb06f6299ddf93db2258ff80012916bf4d9ff8001335a385acff8000ea9a794e4e905b19822e3cb6591a4ff80027d4e7f80018ac9015517f8006029aff80069237ff80000bce6bad0ff8007f80043b1c7f80028b2d7f8007f8007f8003ca657f800209077f80051dd38f0997f800362eea25d503cfb7f8002a4397f8007f8003d002c44b2c10a6b882c85c6bebcba2a5ac6511a9406b9f962bc56bc1d9c0c36d45cb5aa16605c9a80153c2cc2bc470b3ba0ad090ab8bad7aad05b9bb52a2984927aa32e35207f8004f32af80d42d9279b0a173aa77f800402a9eec2cb2a910c46818821b09171c553d14aeb73198d0a2f895c8e31e8dddc9f390ff8007c2817d4258984dd7c27ff800551e27f80056da9ff8007f8006f2b8f31aa84dc802833d324e6e387d7b28a48aaa65a32b9cded9d71bcd8121e67f800199d384d34ff8007f8007f8005953f3e99feb91297188f28bf860b43222ab213fc3252bba968f8e8bf3147f8001aaea89ca25c442e7c577381acfc39ff8007f8007f8007924533c7d028e86ed909b318665e4970a4fc3832ac251c4a2ee44d76b5796a5f7f8003ab455d4be0b00e3b8d5932b13f53fd2994e85915dde708d132811be2d14ad2da92a0c7f800113c3dec267f8007f8007acb07f8007f800543d68027d3896478c35430c9fa9c97f8004d3258f3841aaa35abd26f5
  | 6 => 0x939c9cc2a825073614770ab21dcdc73f005d88beac923f7d43162d756b46a08b63cc3403c783520b209990f9bc7bbd64fcb94ad728e21dadc95ad5af871a4460bc9b12226d88324eb7bc53420304fc5b2c17116ce57f8007f8000ea9ebcdc3962475a5df9f2946c845e41eeff800580632ba99efd2aff8002090da8a5cb1311ec8ecda01837b8885cf5031750206c17a9523d3263559ff8003d1a7d841009bd96559e82a40b917b8b3f4794a95d4a558a6928db541d69868c2c63200010029834b0339cadda00556e8b8de358722d99399c470ac5bf0af8a3fd6bab091864e7c8981063af2cbfa4291edb4145f1ea14510907df463f93b17d12baed9e3d1ffff8002d167a0a3a0eb730e843ff8007f800752df00c5fd4ba97f80056b92a04e3804cb153d7ad895f9cc5f63741f02e7600f24141a39952702f7601eae8c065b5ac300be42d983a8f15d082b4587f800570a36bbd77f80009b42ff800424c5612a20693302cac6dbc2ea0e6a45e637893f6b2e1f1269b9bcaac2f822f3a05d4201e8b74cd1f97daf247900db1e93ac449c3e3cdd718b7f8007f8002fb1a2f2e94337aa4025e340cff800229e04a25dff8007f8007f80052314e626f0f5013738492cdfb523f01250903ebf7196bad87beb071a1352c0045d2412eb0e6851a724d75a8f67713b39df5d82ae912dc49013be5a8b937614c007f8007f8007f8001ec4
  | 7 => 0xf8006845ef20236a3967f8003b25754267a99a1689722357cb6de8ff8003720a7f8007f8002b8d0ff8007f80079b6b74c837f800632f510a387f800505397f8004289a973cb9648682ab539ccb98a427f800218a99ccacaf5adaf29fd8da40e40796350d4dd49fa6b16ad2c7a03ff8000cad1ff80042dea0c8b1ff8000555d1b05ea30e3cdda753437055498e3adff800464778e3a46124aa9bea7f8007f8003f30ea52107f8007f8007f80006432ea591822ddf9b4019a217f80011c9ddcd27bea0f3b037b49087f8000bb4b105bf1c06e98cf62bc408fa4d8685d75a907d015751ec72d41ff800590e97687a63de3108fa27d019d54289dcdff8007f8007f8007f8000143639308e6027d04e14a48c8c490bf9a5e89ab0d9d8e98b2e58da182557f8007f80029dbcaa0cd6b181ff80072c5ad8dbe42ca5b233c70324ff80068378263a2334c1ff8007f8002d4011b5c1545f991d5fd628180476e7126210c63fc7141974e88002506e03b3a785f0769ea30b7bff800293527f8005da39414c238b31e1a6774be2d344c638ce7f800121e3ff80028d36658de7f8007f8007f800155686049b43a3bff8000ea59573ad08b1d8749f19b3ee792d3b3809db7026268e61ada08c5b15dd8c4731b2c88b19f13cfa2d1cb5da07c95d85157d9024bdb5b8edbed4bd697f8007f800153bbd29044331b7f8007f800055f2dcce299a20
  | _ => 0

def word127_20 : Nat → Nat
  | 0 => 0x81b25bfa998c3efd84c736fe22d0622c9f3aa96402963c96f84c45c4478acecf1810ff80078b517f8005f4a67f80025bec8e5969d464dc2c4b359aff8007754700969ff8007f8001c3acce85fff8007f8001f0f4cf54b8625a74afde6cabff800488084ddaa56c7394b62ae95af8d5e0cae5ff800158bf5c9553d421d9b58eb5eb7910aff8004150b7f8000501a643648209e2add28a0b07f80007cbf7f8001a14dff8005346fc1ae2b73445980cf69f106c2836cd58b57f3bcfa8cc655825ea902df3830ff800188ff7f8003ddbaff8001228399469d399eff80038b497f8005d0dd223a4838687f8007f8007858ce41dc73ca87f80051a6df12ba652f07937d28a1fd7d73ed2ea5918fe794d2141b95403d9b7e13dce9200fff8002c070a05e2e41d4ff8001c0d37f800293ddc14917f800229afabb36401c22914b368e48c5c27f8007f80040534451c55daab7f8007f8002bc189916a7f8007f80066ce402dd175365c522308a9f670f06e18cc1532af578d04c0f32fd2794f77a2dc09b126b4f96d3b75b31295c9923ec5341fbb950c789bff8006503165baeab9e0ff8007f8007f8001c36c2b1dd7f8003ac52852db7f8004daec9ecff0fa110a955ea98e245e87f8007f8000e1dfac139d6875ff8002a217a7a79cc40dbd4eba927a14815ff80049a1509595d58077f80062529f78a1962ccc246258d7372327b88697
  | 1 => 0xf18a1b39c5c916a9e33d62aeabb66109c65a536b3814b0b1ecf926c991f40f1aa7402b95d7ab3ee98994a2ff654faf3f4dc1882691eaf0b8ec16bcdb674e4a9d6152f5c7fff8006f4679144ad98ddbe169631064143e37d99fc2edee214ff8002853797b8f984d167d77d9bc100d35fd02c4a97816b467f8000ebbed62876f0097f80062d0225157d4d3d5abe37f80019deeb62c6843897903849561ed93a5b276a4186d29b5532898795d7f8007f80058a8cd2c8a6f5d88f111b113d4ac04c0abf8c432512f92990ea619709a6638bba9023f99d67df58e7927b23905bf2fb38bf897198903550ecfba8adba50eacda9d5585e1348fd5530c19f7c046cfd2ce2494e441a52b4f803ce5fc34cd613013892d4954720a01bb4101b1e0dc4fd994fa4c97c69d08da7930018ca056e829c3037202125b626e9b067eba722f98478243e31b79fb6061028378b15c16874d0a75b23302a65dd11a5b4f7f80065416d6c1415a1b5d8e13a5c648076920267741810b1ad5519f45f856b973fc6b6390baad972fcd33ac4992485058a715a8ee7355a79917f80031b047f8003c04f6f5ef71c1f3e9c7cc45f5881150352ed2b6654311ac8f7f8007f8007f800630c0c11f1f2bb4ff8007f800278652e491b51a23508b7f800631b45a06ce59b4ff8003d3deff8007f80045513cd185794d3ff8007f80022cccff80075363ea27cf554b6d
  | 2 => 0x6b11fca31fff800675a047d3775bb777143ff8002f3b45a2848bcb8ef9edff80049113b4c872012e28df17f800511e30297b421657f800200932e24d2eb334fddbd9a56ff80028ba83bd2251ca6f2d304a99438014f4bafd80cbe181ffb1b08555b91d0c00dd67f8007f8007f8004e269accb4bb11f0dc17a1deaa829cc78e368b484f88d1da5667ba6562767f8007419bf7368468496ba62f0ac137973ae1c8ab9c86607b05d8f424f1b5082868411a18a412d7ae3268ebe27f80078017b088fc825fcc329ff80017416358fee454f2cb8f54c80f24f23c9dda53c888455eca1ce755b7f800395772ea0709a7e182e85e074d92134bd8509d1b1c5c3773b82e26a6f97c34b9cdede7f4ce95bd0d3a4d93426bff80000ba7bb99c9ebcd3ddb374b02328ac712fe73b4adf0643858bcca490f87df795748bef49bbe298c311b471ebc9dbc7b953f7d433465057e809a692eb4859cd5c2e51c0a77a87823bb5d2547c32426b2edf835101816086a4d1e48f5e5819e5e31ce99af2c51ec8f108e22c4775398752080947a0db9e243cb52e1dc8048135b0488e0fc4d909a08ba01288333637dfd0c178b5e41bf8682fc644fd0cc3494d413482ed43fb910e0668720c3dd348f35b4a1be4a7842e3d6866c43e1f1ccfa11eb624988c5df7cc62b139fa191c4741b5db3569001a929da71848ac14d4317cc48d2f3500abb99fdd225a
  | 3 => 0xdf12c709ee2aba9b039c7b1f2bbc38223d13f2b2758ec230a2395531a5674717d3a191ff80020defa7d0543b5e88c0edcdb5ff8007f8000c1199c50f155de7f8001655a3449fd2b799ea18fd124e84ec1f09078a177f800051b77f80048d103f8f396a19ff800054bfe9ad8639a83e8ed87816ec213f3cf4f84d8ff8004c51c2dd90268dec18551ad17d81d66542473a5c71d82dfadf9bbdbeb95be91b5a05b6b1b18f3d55ff8007f800632da74a12455e521819ff800644f7ecd7e3fdf382a6fcbb105791c844794a16317426ff8001a9af1b3b6a3a63e24671c0f9ff80066a49a9c288f896961d7b2481e5a3488be5d126ab52af63d293a1ef43c505ed216ed94fa5d75c1f9f30f96f4840a58ecb20ffca54e809d76d8a365c5a21fbd4ceaa190f2e83fa739a69962649ce7559dfacae15bd8d8531353615317e34d0e0c17902c3f2c8cdac315fb2cd7d3fb3082ad58c8a89decb0e1edab841aac122a3bf460fa4b3132b01fa82223efe119811a6c229fd65928f5da9130327ad57105266b96b11a609e8eb9224e9eb1d5d5ce63d446bd2a2a040d19dbb13bfcabaaecb980a41181d1605499d8178e91760723b148e7b7a0526da16f1565215dca07602ad59d1a947bf5721bb60dab7cbdf9aa5ab124b3db48ab48ae116f3528837598e4858f699e543da87322a5c06183e43b3a75e4ce7b0e9f2d5850da86f29b25838ff80
  | 4 => 0x282a72200a13203242a72200a03692a83212200a03691a83212a02203691a83212a01203683242a12200a03294483a02a12203293242a72200a03292e83212200a03283242a12200e0abe74ad47f8003ca847094cfa8cb0415ffc2286c13486b54294b22f229a527c78d6ca4bc72c8024bbe7a3af7cd0d2ff80069a8d8209ebe4fc37ba17f800209de4014c1d383960d503163e24e7d35838a23d00c1e08cf9b1982873d35e4c7eda7bddb7a18382ceb6225055a39b9249cc68bc464d66cbbd594145eac23e803bbb3f1abb3d3809c10df4fb40e71d039588f261faaf96c7a1ae6c2ceec48e75062ebb9e46bf262515309178d2c1b401c9390c5458dcb27aaa881669905bbd981d2fbccbd02412c9bcb1cd15ff8003c22a1d54ee49dcf2cb0ff8006d5ca7f8007f8007f8007f80067536844208689fce0833002bd7d44ff8007a3fc47c3c7f80074c50c9df452bbc898530bac67f8007f80017933cf884fa341ff800121b679baf7f80079b33a9129ff8004bc15ff8001b4091089d94b94ea3f59706080d45ff800772f9824521eb817f800143937b9277f80066bbc4b891ff8003380549a147f8005a9037f8007f8007f80032b9d43d1db2b5c560220c18bf00fd74a6cff8006704eb44eef69157f80054bde10b287f8001b2f2723715739f09a1ef1c94512bf51ab1ff8002a89b7f8003cbac4046919b44f48ab55bf982059
  | 5 => 0x9ad48901972b36a3a93242a12200ea3a93242a02200ea2a94203211a016a2a91a73212200ea2a91a73202200ea2293a13212a016a2290283242a00ea2273212a02200ea2273202a12200ea1a94203212a026a1a94203212a016a1a92a73212200ea1a92a73202200ea1a92a136712126a1a92a136702126a1a92a13272200ea1a92a13202200ea1a90a532032026a1a82a812132126a1a82a802132126a1293a83212a026a1293282a72200ea0a92a73202200ea0a92a03242a00ea0a91a73202200ea0a33273202200e93242a02a12200e92281a81273200e91a93a83212a014a4a43202a12200ca4253202a11200c93242a02a12200aa3e91a83212a022a3e91a83212a012a3290483a02a122a3290483a02a112a3242a12a02200aa3242a02a12200aa2a43213202200aa2a43203212200aa1a43273202200aa1a43203272200aa1093282a72200aa0a93242a02200aa0a53203272a012a0a53203222a01293242a12a02200a93242a02a12200a93093282a72200a92e91283272200a92a92203242a00a91e91283272200a91290a53203201282e92283a13201282e92281273200a82e91283a13202282e91282273200a82e91280273212273691a83212a02243273212a02200a43273202a12200a43213282e70212213293e83202a12213290483a02a12213290483a02a11213283242a02200a13203682a72200a13203
  | 6 => 0xc904004458c04302830400098541020c0000018021c00c000430002843140204800101800c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c8c9c0c0c0c0c0c0c0c0c0c0c0c0c1b8b8b8b8b8b8b8b8b8b8b9b0b1a8a8a8a8a8a8a8ab9188888888888888888980808179716a59514d22101010101011080900000000065c7f43e980380737b8038077aa3e9a53803e38c32198803f4800737bf918038070038038036a9754b473e16f473a5991ee0f70bb64bb25f06d1cf34daa6e5351ce8e7873e8e647a8cf9b2bc96c37565cb2a33e19ee2da9aa39d19f09fb8cae66ab2e59b25d86f273939e8cf4674b2b59f0cf867c339996ccae64f33999cccda66c3369972cdd25cb3659b26d966c3b659e8cae674b3e19f0cf867333b89b4cd866d3364b72ca39d16fe19d2cf1678b30e703fd1d5a71d2433948627ac6392186a530d4865494c0d2981a433f4867c90c3d298aeb1bb5248690c1921896b12cd6271a46312994a5317d6331a867f58e3a53424460a88caf59186a220d639488c5358cb6b1b1d456a90c6b586321325d678290d252180a53074a60894c0129a62032f5662094c41596225332d065aad0b55a56ab51dd063aa0c9d3993a7327d674dacef121926b0b34868090cd921a4243344861694c875965a13114a622acb15298f2831ed63509cca139946b3bd48647ac26f58cceb2884a60484c292184a4337d433
  | 7 => 0xe82eaa960f95c05fab480a2a97c6926acc6f5d087a4bf3973fc01acc5445f54c2821eb394900962d238b835fe004d82d5855d1228352ff007f803fc0187362cafc6a6f71a4a00068ae7f8024e2bfe0000ae879c3fc01fe00ff007f8007047fe00ff003c38ea45bfe004d597f803fc00e119ff007f802685ffe009d98f449c469a969f50af0732a9a556e43ff007f800260882756502c42c1f92d7879ff003fb4e5c21cceeca339bcd2ee7c171db327f6307429f9f351643df8901a36f6d5493d499dbfc01fe007eab6d813fc01c84bf0b03e41bb4a2f93f440bff801ad582e464031abb5e843ade5fff000b993fc011947ff007f80179e3e6564929ba243fc00d06cab5696293b0bbfe00ad998028f2143d24eeb75ff80379d5668ba20de115d09c0ab39d232e72e93ea30ad0ff0075b87d980a8d6496f61b53fc01a8735d50632b9dde6072e7994e3af55d4cc30cc46d7f8036a98a6c3ff001ccf42ec3fe00b69c4dca35985eab105176ab2d4c53d6ec6f0cb52ce8e04a31f4b3fd73ef24305659223a4901a00dd64f6a447ae02d7ca45117ae12cb4af19b7d03b615b88988fca8f01e9352b38adaeb61cdf698b6550f30d1a6477c9be84c8adb2e65e672dd1d2960abdd10d508e99825a071ce65377d00400084142c0270028646003c02c5a38580020000076010150a3c2831a1430506000089678001062000004100000a6
  | _ => 0

def word127_21 : Nat → Nat
  | 0 => 0xc216a022cc9bf119a08488107ebc397690650d2f25670043c39a13a407ebc99a55c57525227bb04271455247b717d1a110b16c1a782f7f1cd3a7d26a6bbff001441f7107ca7ef99e4a507fc004c72691165c3d857ffe0051797f803ae5bfe00ff007f803fc01fe00386707083fc01ef0bb934e32f3be464433726c504bcdec714fc7e8a2e9a8d47b5b302510ff802acd6903f1809d58511d991e124b894e1c41e7724d116b12db9ee592d44991747f801f4589c504888ff80179d29a77ff007f802c99ed9135a802dbfef58cd4c760578355f715710f02b0124b2209f3b54bd00397248b84fae61d236ff8034a8ca226506268d41745125538b01ff800454f7832ff00663b785
  | _ => 0

def compactWords127 (i : Nat) : Nat :=
  if i < 169 then (if i < 88 then (if i < 40 then (if i < 16 then (if i < 8 then word127_0 (i % 8) else word127_1 (i % 8)) else (if i < 24 then word127_2 (i % 8) else (if i < 32 then word127_3 (i % 8) else word127_4 (i % 8)))) else (if i < 64 then (if i < 48 then word127_5 (i % 8) else (if i < 56 then word127_6 (i % 8) else word127_7 (i % 8))) else (if i < 72 then word127_8 (i % 8) else (if i < 80 then word127_9 (i % 8) else word127_10 (i % 8))))) else (if i < 128 then (if i < 104 then (if i < 96 then word127_11 (i % 8) else word127_12 (i % 8)) else (if i < 112 then word127_13 (i % 8) else (if i < 120 then word127_14 (i % 8) else word127_15 (i % 8)))) else (if i < 152 then (if i < 136 then word127_16 (i % 8) else (if i < 144 then word127_17 (i % 8) else word127_18 (i % 8))) else (if i < 160 then word127_19 (i % 8) else (if i < 168 then word127_20 (i % 8) else word127_21 (i % 8)))))) else 0

def compactCount127 (k : Nat) : Nat := match k with
  | 12 => 1
  | 11 => 10
  | 10 => 132
  | 9 => 711
  | 8 => 1210
  | 7 => 765
  | 6 => 89
  | _ => 0

def compactPath127 (k : Nat) (i : Nat) : Nat := match k with
  | 12 => 0
  | 11 => readCompactBits compactWords127 (31 + 12*i) 12
  | 10 => let v := readCompactBits compactWords127 (1921 + 16*i) 16
    (readCompactBits compactWords127 (1801 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 9 => let v := readCompactBits compactWords127 (36054 + 19*i) 19
    (readCompactBits compactWords127 (33486 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 8 => let v := readCompactBits compactWords127 (241742 + 21*i) 21
    (readCompactBits compactWords127 (228350 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | 7 => let v := readCompactBits compactWords127 (543981 + 21*i) 21
    (readCompactBits compactWords127 (523005 + 48*(v >>> 12)) 48) ||| ((v &&& 4095) <<< 48)
  | 6 => let v := readCompactBits compactWords127 (679883 + 19*i) 19
    (readCompactBits compactWords127 (675263 + 60*(v >>> 12)) 60) ||| ((v &&& 4095) <<< 60)
  | _ => 0

def compactLive127 (k : Nat) (i : Nat) : Nat := match k with
  | 12 => readCompactBits compactWords127 (0 + 7*i) 7
  | 11 => readCompactBits compactWords127 (151 + 8*i) 8
  | 10 => readCompactBits compactWords127 (4033 + 9*i) 9
  | 9 => readCompactBits compactWords127 (49563 + 10*i) 10
  | 8 => readCompactBits compactWords127 (267152 + 11*i) 11
  | 7 => readCompactBits compactWords127 (560046 + 12*i) 12
  | 6 => readCompactBits compactWords127 (681574 + 13*i) 13
  | _ => 0

def compactPoolIDs127 (k : Nat) (i : Nat) : List Nat := match k with
  | 12 => let v := readCompactBits compactWords127 (25 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords127 (7 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 11 => let v := readCompactBits compactWords127 (1127 + 12*i) 12
    let n := v >>> 8
    let bits := readCompactBits compactWords127 (231 + 7*(v &&& 255)) (7*n)
    compactIDsFromBits bits 7 n
  | 10 => let v := readCompactBits compactWords127 (20701 + 16*i) 16
    let n := v >>> 11
    let bits := readCompactBits compactWords127 (5221 + 8*(v &&& 2047)) (8*n)
    compactIDsFromBits bits 8 n
  | 9 => let v := readCompactBits compactWords127 (143813 + 19*i) 19
    let n := v >>> 14
    let bits := readCompactBits compactWords127 (56673 + 10*(v &&& 16383)) (10*n)
    compactIDsFromBits bits 10 n
  | 8 => let v := readCompactBits compactWords127 (373027 + 19*i) 19
    let n := v >>> 14
    let bits := readCompactBits compactWords127 (280462 + 11*(v &&& 16383)) (11*n)
    compactIDsFromBits bits 11 n
  | 7 => let v := readCompactBits compactWords127 (585726 + 15*i) 15
    let n := v >>> 11
    let bits := readCompactBits compactWords127 (569226 + 12*(v &&& 2047)) (12*n)
    compactIDsFromBits bits 12 n
  | 6 => let v := readCompactBits compactWords127 (683031 + 8*i) 8
    let n := v >>> 5
    let bits := readCompactBits compactWords127 (682731 + 12*(v &&& 31)) (12*n)
    compactIDsFromBits bits 12 n
  | _ => []

def compactBucket127 (k : Nat) (i : Nat) : List Nat := match k with
  | 11 => let d := readCompactBits compactWords127 (1247 + 4*(i % 9)) 4
    let off := ((i/9 + d) % 37)
    let v := readCompactBits compactWords127 (1283 + 14*off) 14
    if v >>> 6 == (i/104729)%251 then [v &&& 63] else []
  | 10 => let d := readCompactBits compactWords127 (22813 + 7*(i % 149)) 7
    let off := ((i/149 + d) % 535)
    let v := readCompactBits compactWords127 (23856 + 18*off) 18
    if v >>> 10 == (i/104729)%251 then [v &&& 1023] else []
  | 9 => let d := readCompactBits compactWords127 (157322 + 8*(i % 901)) 8
    let off := ((i/901 + d) % 3191)
    let v := readCompactBits compactWords127 (164530 + 20*off) 20
    if v >>> 12 == (i/104729)%251 then [v &&& 4095] else []
  | 8 => let d := readCompactBits compactWords127 (396017 + 8*(i % 1541)) 8
    let off := ((i/1541 + d) % 5460)
    let v := readCompactBits compactWords127 (408345 + 21*off) 21
    if v >>> 13 == (i/104729)%251 then [v &&& 8191] else []
  | 7 => let d := readCompactBits compactWords127 (597201 + 9*(i % 978)) 9
    let off := ((i/978 + d) % 3463)
    let v := readCompactBits compactWords127 (606003 + 20*off) 20
    if v >>> 12 == (i/104729)%251 then [v &&& 4095] else []
  | 6 => let d := readCompactBits compactWords127 (683743 + 7*(i % 96)) 7
    let off := ((i/96 + d) % 342)
    let v := readCompactBits compactWords127 (684415 + 17*off) 17
    if v >>> 9 == (i/104729)%251 then [v &&& 511] else []
  | _ => []
theorem compactHalves {test : Nat → Bool} {start n : Nat}
    (first : chartBlock test start (n / 2) = true)
    (last : chartBlock test (start + n / 2) (n - n / 2) = true) :
    chartBlock test start n = true := by
  have eq : n / 2 + (n - n / 2) = n := by omega
  simpa only [eq] using chartBlock_join first last

def grid21 : CompactGrid := (21, 3, samplesP21, samplesQ21)
def tab21 : CompactTable := (compactCount21, compactPath21, compactLive21, compactPoolIDs21, compactBucket21)
def check21 (k : Nat) := compactNode grid21 tab21 compactDomains21 compactPerms21 k
def sliceSpecs21 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains21 : ∀ d ∈ compactDomains21, Slice true (vars 21) (graphGoal 21) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs21)
  · simp
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs21 : properPairs (graphGoal 21) (asRow samplesP21) (asRow samplesQ21) :=
  compactPairs (g := grid21) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos21 : ∀ p ∈ compactPerms21, autoOK (graphGoal 21) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c21k3p0 : chartBlock (check21 3) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev21k3 : chartBlock (check21 3) 0 1 = true :=
  c21k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded21 : Impossible true (graphGoal 21) 3 (vars 21).toFinset := by
  apply compactRoot (g := grid21) (t := tab21) (dom := compactDomains21) (perms := compactPerms21) pairs21 domains21 autos21
  · intro k hk
    change k ≤ 3 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev21k3
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound21 : Lower true (vars 21) (graphGoal 21) 4 :=
  plain_low (hints := 2) (by decide +kernel) excluded21

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound84 : Lower true (vars 84) (graphGoal 84) 4 :=
  carry_of (old := 84) (rep := 21) (swaps := [96]) (by decide +kernel) bound21

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound81 : Lower true (vars 81) (graphGoal 81) 4 :=
  carry_of (old := 81) (rep := 21) (swaps := [98]) (by decide +kernel) bound21

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound69 : Lower true (vars 69) (graphGoal 69) 4 :=
  carry_of (old := 69) (rep := 21) (swaps := [100]) (by decide +kernel) bound21

def grid85 : CompactGrid := (85, 6, samplesP85, samplesQ85)
def tab85 : CompactTable := (compactCount85, compactPath85, compactLive85, compactPoolIDs85, compactBucket85)
def check85 (k : Nat) := compactNode grid85 tab85 compactDomains85 compactPerms85 k
def sliceSpecs85 : List SliceSpec := [(1, 0, 84, 0, 0, 4, 4), (4, 0, 81, 0, 0, 4, 4), (16, 0, 69, 0, 0, 4, 4), (64, 0, 21, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains85 : ∀ d ∈ compactDomains85, Slice true (vars 85) (graphGoal 85) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(84, 4), (81, 4), (69, 4), (21, 4)]) (specs := sliceSpecs85)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact bound84
    · exact bound81
    · exact bound69
    · exact bound21
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs85 : properPairs (graphGoal 85) (asRow samplesP85) (asRow samplesQ85) :=
  compactPairs (g := grid85) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos85 : ∀ p ∈ compactPerms85, autoOK (graphGoal 85) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c85k3p0 : chartBlock (check85 3) 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev85k3 : chartBlock (check85 3) 0 2 = true :=
  c85k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c85k4p0 : chartBlock (check85 4) 0 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev85k4 : chartBlock (check85 4) 0 3 = true :=
  c85k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c85k5p0 : chartBlock (check85 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev85k5 : chartBlock (check85 5) 0 1 = true :=
  c85k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c85k6p0 : chartBlock (check85 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev85k6 : chartBlock (check85 6) 0 1 = true :=
  c85k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded85 : Impossible true (graphGoal 85) 6 (vars 85).toFinset := by
  apply compactRoot (g := grid85) (t := tab85) (dom := compactDomains85) (perms := compactPerms85) pairs85 domains85 autos85
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev85k3
    · exact lev85k4
    · exact lev85k5
    · exact lev85k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound85 : Lower true (vars 85) (graphGoal 85) 7 :=
  plain_low (hints := 2) (by decide +kernel) excluded85

def grid93 : CompactGrid := (93, 7, samplesP93, samplesQ93)
def tab93 : CompactTable := (compactCount93, compactPath93, compactLive93, compactPoolIDs93, compactBucket93)
def check93 (k : Nat) := compactNode grid93 tab93 compactDomains93 compactPerms93 k
def sliceSpecs93 : List SliceSpec := [(8, 0, 85, 0, 0, 7, 7)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains93 : ∀ d ∈ compactDomains93, Slice true (vars 93) (graphGoal 93) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(85, 7)]) (specs := sliceSpecs93)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound85
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs93 : properPairs (graphGoal 93) (asRow samplesP93) (asRow samplesQ93) :=
  compactPairs (g := grid93) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos93 : ∀ p ∈ compactPerms93, autoOK (graphGoal 93) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c93k7p0 : chartBlock (check93 7) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev93k7 : chartBlock (check93 7) 0 1 = true :=
  c93k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded93 : Impossible true (graphGoal 93) 7 (vars 93).toFinset := by
  apply compactRoot (g := grid93) (t := tab93) (dom := compactDomains93) (perms := compactPerms93) pairs93 domains93 autos93
  · intro k hk
    change k ≤ 7 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev93k7
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound93 : Lower true (vars 93) (graphGoal 93) 8 :=
  plain_low (hints := 24578) (by decide +kernel) excluded93

def grid87 : CompactGrid := (87, 7, samplesP87, samplesQ87)
def tab87 : CompactTable := (compactCount87, compactPath87, compactLive87, compactPoolIDs87, compactBucket87)
def check87 (k : Nat) := compactNode grid87 tab87 compactDomains87 compactPerms87 k
def sliceSpecs87 : List SliceSpec := [(2, 0, 85, 0, 0, 7, 7)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains87 : ∀ d ∈ compactDomains87, Slice true (vars 87) (graphGoal 87) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(85, 7)]) (specs := sliceSpecs87)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound85
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs87 : properPairs (graphGoal 87) (asRow samplesP87) (asRow samplesQ87) :=
  compactPairs (g := grid87) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos87 : ∀ p ∈ compactPerms87, autoOK (graphGoal 87) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c87k7p0 : chartBlock (check87 7) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev87k7 : chartBlock (check87 7) 0 1 = true :=
  c87k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded87 : Impossible true (graphGoal 87) 7 (vars 87).toFinset := by
  apply compactRoot (g := grid87) (t := tab87) (dom := compactDomains87) (perms := compactPerms87) pairs87 domains87 autos87
  · intro k hk
    change k ≤ 7 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev87k7
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound87 : Lower true (vars 87) (graphGoal 87) 8 :=
  plain_low (hints := 66) (by decide +kernel) excluded87

def grid23 : CompactGrid := (23, 4, samplesP23, samplesQ23)
def tab23 : CompactTable := (compactCount23, compactPath23, compactLive23, compactPoolIDs23, compactBucket23)
def check23 (k : Nat) := compactNode grid23 tab23 compactDomains23 compactPerms23 k
def sliceSpecs23 : List SliceSpec := [(2, 0, 21, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains23 : ∀ d ∈ compactDomains23, Slice true (vars 23) (graphGoal 23) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(21, 4)]) (specs := sliceSpecs23)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound21
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs23 : properPairs (graphGoal 23) (asRow samplesP23) (asRow samplesQ23) :=
  compactPairs (g := grid23) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos23 : ∀ p ∈ compactPerms23, autoOK (graphGoal 23) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c23k4p0 : chartBlock (check23 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev23k4 : chartBlock (check23 4) 0 1 = true :=
  c23k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded23 : Impossible true (graphGoal 23) 4 (vars 23).toFinset := by
  apply compactRoot (g := grid23) (t := tab23) (dom := compactDomains23) (perms := compactPerms23) pairs23 domains23 autos23
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev23k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound23 : Lower true (vars 23) (graphGoal 23) 5 :=
  plain_low (hints := 66) (by decide +kernel) excluded23

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound78 : Lower true (vars 78) (graphGoal 78) 5 :=
  carry_of (old := 78) (rep := 23) (swaps := [33, 48, 100]) (by decide +kernel) bound23

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound77 : Lower true (vars 77) (graphGoal 77) 5 :=
  carry_of (old := 77) (rep := 23) (swaps := [49, 100]) (by decide +kernel) bound23

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound75 : Lower true (vars 75) (graphGoal 75) 5 :=
  carry_of (old := 75) (rep := 23) (swaps := [16, 50, 100]) (by decide +kernel) bound23

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound71 : Lower true (vars 71) (graphGoal 71) 5 :=
  carry_of (old := 71) (rep := 23) (swaps := [100]) (by decide +kernel) bound23

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound74 : Lower true (vars 74) (graphGoal 74) 4 :=
  carry_of (old := 74) (rep := 21) (swaps := [16, 50, 100]) (by decide +kernel) bound21

def grid79 : CompactGrid := (79, 7, samplesP79, samplesQ79)
def tab79 : CompactTable := (compactCount79, compactPath79, compactLive79, compactPoolIDs79, compactBucket79)
def check79 (k : Nat) := compactNode grid79 tab79 compactDomains79 compactPerms79 k
def sliceSpecs79 : List SliceSpec := [(1, 0, 78, 0, 0, 5, 5), (2, 0, 77, 0, 0, 5, 5), (4, 0, 75, 0, 0, 5, 5), (8, 0, 71, 0, 0, 5, 5), (5, 0, 74, 0, 0, 4, 4), (10, 0, 69, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains79 : ∀ d ∈ compactDomains79, Slice true (vars 79) (graphGoal 79) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(78, 5), (77, 5), (75, 5), (71, 5), (74, 4), (69, 4)]) (specs := sliceSpecs79)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound78
    · exact bound77
    · exact bound75
    · exact bound71
    · exact bound74
    · exact bound69
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs79 : properPairs (graphGoal 79) (asRow samplesP79) (asRow samplesQ79) :=
  compactPairs (g := grid79) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos79 : ∀ p ∈ compactPerms79, autoOK (graphGoal 79) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c79k4p0 : chartBlock (check79 4) 0 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev79k4 : chartBlock (check79 4) 0 3 = true :=
  c79k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c79k5p0 : chartBlock (check79 5) 0 10 = true := by
  iterate 2 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev79k5 : chartBlock (check79 5) 0 10 = true :=
  c79k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c79k6p0 : chartBlock (check79 6) 0 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev79k6 : chartBlock (check79 6) 0 3 = true :=
  c79k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c79k7p0 : chartBlock (check79 7) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev79k7 : chartBlock (check79 7) 0 1 = true :=
  c79k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded79 : Impossible true (graphGoal 79) 7 (vars 79).toFinset := by
  apply compactRoot (g := grid79) (t := tab79) (dom := compactDomains79) (perms := compactPerms79) pairs79 domains79 autos79
  · intro k hk
    change k ≤ 7 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev79k4
    · exact lev79k5
    · exact lev79k6
    · exact lev79k7
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound79 : Lower true (vars 79) (graphGoal 79) 8 :=
  plain_low (hints := 4146) (by decide +kernel) excluded79

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound82 : Lower true (vars 82) (graphGoal 82) 4 :=
  carry_of (old := 82) (rep := 21) (swaps := [16, 98]) (by decide +kernel) bound21

def grid83 : CompactGrid := (83, 4, samplesP83, samplesQ83)
def tab83 : CompactTable := (compactCount83, compactPath83, compactLive83, compactPoolIDs83, compactBucket83)
def check83 (k : Nat) := compactNode grid83 tab83 compactDomains83 compactPerms83 k
def sliceSpecs83 : List SliceSpec := [(1, 0, 82, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains83 : ∀ d ∈ compactDomains83, Slice true (vars 83) (graphGoal 83) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(82, 4)]) (specs := sliceSpecs83)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound82
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs83 : properPairs (graphGoal 83) (asRow samplesP83) (asRow samplesQ83) :=
  compactPairs (g := grid83) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos83 : ∀ p ∈ compactPerms83, autoOK (graphGoal 83) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c83k4p0 : chartBlock (check83 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev83k4 : chartBlock (check83 4) 0 1 = true :=
  c83k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded83 : Impossible true (graphGoal 83) 4 (vars 83).toFinset := by
  apply compactRoot (g := grid83) (t := tab83) (dom := compactDomains83) (perms := compactPerms83) pairs83 domains83 autos83
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev83k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound83 : Lower true (vars 83) (graphGoal 83) 5 :=
  plain_low (hints := 68) (by decide +kernel) excluded83

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound90 : Lower true (vars 90) (graphGoal 90) 5 :=
  carry_of (old := 90) (rep := 83) (swaps := [65, 48]) (by decide +kernel) bound83

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound89 : Lower true (vars 89) (graphGoal 89) 5 :=
  carry_of (old := 89) (rep := 23) (swaps := [49, 66, 98]) (by decide +kernel) bound23

def grid91 : CompactGrid := (91, 6, samplesP91, samplesQ91)
def tab91 : CompactTable := (compactCount91, compactPath91, compactLive91, compactPoolIDs91, compactBucket91)
def check91 (k : Nat) := compactNode grid91 tab91 compactDomains91 compactPerms91 k
def sliceSpecs91 : List SliceSpec := [(1, 0, 90, 0, 0, 5, 5), (2, 0, 89, 0, 0, 5, 5), (8, 0, 83, 0, 0, 5, 5), (16, 0, 75, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains91 : ∀ d ∈ compactDomains91, Slice true (vars 91) (graphGoal 91) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(90, 5), (89, 5), (83, 5), (75, 5)]) (specs := sliceSpecs91)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact bound90
    · exact bound89
    · exact bound83
    · exact bound75
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs91 : properPairs (graphGoal 91) (asRow samplesP91) (asRow samplesQ91) :=
  compactPairs (g := grid91) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos91 : ∀ p ∈ compactPerms91, autoOK (graphGoal 91) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c91k6p0 : chartBlock (check91 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev91k6 : chartBlock (check91 6) 0 1 = true :=
  c91k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded91 : Impossible true (graphGoal 91) 6 (vars 91).toFinset := by
  apply compactRoot (g := grid91) (t := tab91) (dom := compactDomains91) (perms := compactPerms91) pairs91 domains91 autos91
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev91k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound91 : Lower true (vars 91) (graphGoal 91) 7 :=
  plain_low (hints := 4148) (by decide +kernel) excluded91

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound94 : Lower true (vars 94) (graphGoal 94) 7 :=
  carry_of (old := 94) (rep := 91) (swaps := [32]) (by decide +kernel) bound91

def grid27 : CompactGrid := (27, 3, samplesP27, samplesQ27)
def tab27 : CompactTable := (compactCount27, compactPath27, compactLive27, compactPoolIDs27, compactBucket27)
def check27 (k : Nat) := compactNode grid27 tab27 compactDomains27 compactPerms27 k
def sliceSpecs27 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains27 : ∀ d ∈ compactDomains27, Slice true (vars 27) (graphGoal 27) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs27)
  · simp
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs27 : properPairs (graphGoal 27) (asRow samplesP27) (asRow samplesQ27) :=
  compactPairs (g := grid27) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos27 : ∀ p ∈ compactPerms27, autoOK (graphGoal 27) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c27k3p0 : chartBlock (check27 3) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev27k3 : chartBlock (check27 3) 0 1 = true :=
  c27k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded27 : Impossible true (graphGoal 27) 3 (vars 27).toFinset := by
  apply compactRoot (g := grid27) (t := tab27) (dom := compactDomains27) (perms := compactPerms27) pairs27 domains27 autos27
  · intro k hk
    change k ≤ 3 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev27k3
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound27 : Lower true (vars 27) (graphGoal 27) 4 :=
  plain_low (hints := 4148) (by decide +kernel) excluded27

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound30 : Lower true (vars 30) (graphGoal 30) 4 :=
  carry_of (old := 30) (rep := 27) (swaps := [32]) (by decide +kernel) bound27

def grid31 : CompactGrid := (31, 6, samplesP31, samplesQ31)
def tab31 : CompactTable := (compactCount31, compactPath31, compactLive31, compactPoolIDs31, compactBucket31)
def check31 (k : Nat) := compactNode grid31 tab31 compactDomains31 compactPerms31 k
def sliceSpecs31 : List SliceSpec := [(8, 0, 23, 0, 0, 5, 5), (0, 8, 21, 2, 240, 5, 4), (1, 0, 30, 0, 0, 4, 4), (4, 0, 27, 0, 0, 4, 4), (2, 8, 21, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains31 : ∀ d ∈ compactDomains31, Slice true (vars 31) (graphGoal 31) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(23, 5), (21, 4), (30, 4), (27, 4)]) (specs := sliceSpecs31)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact bound23
    · exact bound21
    · exact bound30
    · exact bound27
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs31 : properPairs (graphGoal 31) (asRow samplesP31) (asRow samplesQ31) :=
  compactPairs (g := grid31) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos31 : ∀ p ∈ compactPerms31, autoOK (graphGoal 31) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c31k4p0 : chartBlock (check31 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev31k4 : chartBlock (check31 4) 0 1 = true :=
  c31k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c31k5p0 : chartBlock (check31 5) 0 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev31k5 : chartBlock (check31 5) 0 3 = true :=
  c31k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c31k6p0 : chartBlock (check31 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev31k6 : chartBlock (check31 6) 0 1 = true :=
  c31k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded31 : Impossible true (graphGoal 31) 6 (vars 31).toFinset := by
  apply compactRoot (g := grid31) (t := tab31) (dom := compactDomains31) (perms := compactPerms31) pairs31 domains31 autos31
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev31k4
    · exact lev31k5
    · exact lev31k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound31 : Lower true (vars 31) (graphGoal 31) 7 :=
  plain_low (hints := 4146) (by decide +kernel) excluded31

def grid95 : CompactGrid := (95, 9, samplesP95, samplesQ95)
def tab95 : CompactTable := (compactCount95, compactPath95, compactLive95, compactPoolIDs95, compactBucket95)
def check95 (k : Nat) := compactNode grid95 tab95 compactDomains95 compactPerms95 k
def sliceSpecs95 : List SliceSpec := [(2, 0, 93, 0, 0, 8, 8), (8, 0, 87, 0, 0, 8, 8), (16, 0, 79, 0, 0, 8, 8), (1, 0, 94, 0, 0, 7, 7), (4, 0, 91, 0, 0, 7, 7), (64, 0, 31, 0, 0, 7, 7), (5, 0, 90, 0, 0, 5, 5), (65, 0, 30, 0, 0, 4, 4), (68, 0, 27, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains95 : ∀ d ∈ compactDomains95, Slice true (vars 95) (graphGoal 95) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(93, 8), (87, 8), (79, 8), (94, 7), (91, 7), (31, 7), (90, 5), (30, 4), (27, 4)]) (specs := sliceSpecs95)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound93
    · exact bound87
    · exact bound79
    · exact bound94
    · exact bound91
    · exact bound31
    · exact bound90
    · exact bound30
    · exact bound27
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs95 : properPairs (graphGoal 95) (asRow samplesP95) (asRow samplesQ95) :=
  compactPairs (g := grid95) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos95 : ∀ p ∈ compactPerms95, autoOK (graphGoal 95) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c95k6p0 : chartBlock (check95 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev95k6 : chartBlock (check95 6) 0 1 = true :=
  c95k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c95k7p0 : chartBlock (check95 7) 0 5 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev95k7 : chartBlock (check95 7) 0 5 = true :=
  c95k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c95k8p0 : chartBlock (check95 8) 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev95k8 : chartBlock (check95 8) 0 2 = true :=
  c95k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c95k9p0 : chartBlock (check95 9) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev95k9 : chartBlock (check95 9) 0 1 = true :=
  c95k9p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded95 : Impossible true (graphGoal 95) 9 (vars 95).toFinset := by
  apply compactRoot (g := grid95) (t := tab95) (dom := compactDomains95) (perms := compactPerms95) pairs95 domains95 autos95
  · intro k hk
    change k ≤ 9 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev95k6
    · exact lev95k7
    · exact lev95k8
    · exact lev95k9
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound95 : Lower true (vars 95) (graphGoal 95) 10 :=
  plain_low (hints := 4146) (by decide +kernel) excluded95

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound126 : Lower true (vars 126) (graphGoal 126) 10 :=
  carry_of (old := 126) (rep := 95) (swaps := [65, 50, 80]) (by decide +kernel) bound95

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound125 : Lower true (vars 125) (graphGoal 125) 10 :=
  carry_of (old := 125) (rep := 95) (swaps := [64, 81]) (by decide +kernel) bound95

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound117 : Lower true (vars 117) (graphGoal 117) 8 :=
  carry_of (old := 117) (rep := 87) (swaps := [64, 81]) (by decide +kernel) bound87

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound118 : Lower true (vars 118) (graphGoal 118) 7 :=
  carry_of (old := 118) (rep := 91) (swaps := [32, 83]) (by decide +kernel) bound91

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound103 : Lower true (vars 103) (graphGoal 103) 7 :=
  carry_of (old := 103) (rep := 91) (swaps := [16, 50, 84]) (by decide +kernel) bound91

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound114 : Lower true (vars 114) (graphGoal 114) 5 :=
  carry_of (old := 114) (rep := 83) (swaps := [65, 80]) (by decide +kernel) bound83

def grid115 : CompactGrid := (115, 5, samplesP115, samplesQ115)
def tab115 : CompactTable := (compactCount115, compactPath115, compactLive115, compactPoolIDs115, compactBucket115)
def check115 (k : Nat) := compactNode grid115 tab115 compactDomains115 compactPerms115 k
def sliceSpecs115 : List SliceSpec := [(1, 0, 114, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains115 : ∀ d ∈ compactDomains115, Slice true (vars 115) (graphGoal 115) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(114, 5)]) (specs := sliceSpecs115)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound114
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs115 : properPairs (graphGoal 115) (asRow samplesP115) (asRow samplesQ115) :=
  compactPairs (g := grid115) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos115 : ∀ p ∈ compactPerms115, autoOK (graphGoal 115) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c115k5p0 : chartBlock (check115 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev115k5 : chartBlock (check115 5) 0 1 = true :=
  c115k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded115 : Impossible true (graphGoal 115) 5 (vars 115).toFinset := by
  apply compactRoot (g := grid115) (t := tab115) (dom := compactDomains115) (perms := compactPerms115) pairs115 domains115 autos115
  · intro k hk
    change k ≤ 5 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev115k5
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound115 : Lower true (vars 115) (graphGoal 115) 6 :=
  plain_low (hints := 68) (by decide +kernel) excluded115

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound53 : Lower true (vars 53) (graphGoal 53) 5 :=
  carry_of (old := 53) (rep := 23) (swaps := [64, 81]) (by decide +kernel) bound23

def grid55 : CompactGrid := (55, 5, samplesP55, samplesQ55)
def tab55 : CompactTable := (compactCount55, compactPath55, compactLive55, compactPoolIDs55, compactBucket55)
def check55 (k : Nat) := compactNode grid55 tab55 compactDomains55 compactPerms55 k
def sliceSpecs55 : List SliceSpec := [(2, 0, 53, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains55 : ∀ d ∈ compactDomains55, Slice true (vars 55) (graphGoal 55) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(53, 5)]) (specs := sliceSpecs55)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound53
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs55 : properPairs (graphGoal 55) (asRow samplesP55) (asRow samplesQ55) :=
  compactPairs (g := grid55) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos55 : ∀ p ∈ compactPerms55, autoOK (graphGoal 55) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c55k5p0 : chartBlock (check55 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev55k5 : chartBlock (check55 5) 0 1 = true :=
  c55k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded55 : Impossible true (graphGoal 55) 5 (vars 55).toFinset := by
  apply compactRoot (g := grid55) (t := tab55) (dom := compactDomains55) (perms := compactPerms55) pairs55 domains55 autos55
  · intro k hk
    change k ≤ 5 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev55k5
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound55 : Lower true (vars 55) (graphGoal 55) 6 :=
  plain_low (hints := 66) (by decide +kernel) excluded55

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound116 : Lower true (vars 116) (graphGoal 116) 5 :=
  carry_of (old := 116) (rep := 23) (swaps := [64, 81, 96, 16]) (by decide +kernel) bound23

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound113 : Lower true (vars 113) (graphGoal 113) 5 :=
  carry_of (old := 113) (rep := 83) (swaps := [64, 81]) (by decide +kernel) bound83

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound102 : Lower true (vars 102) (graphGoal 102) 5 :=
  carry_of (old := 102) (rep := 23) (swaps := [33, 80, 100]) (by decide +kernel) bound23

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound101 : Lower true (vars 101) (graphGoal 101) 5 :=
  carry_of (old := 101) (rep := 83) (swaps := [64, 33, 84]) (by decide +kernel) bound83

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound99 : Lower true (vars 99) (graphGoal 99) 5 :=
  carry_of (old := 99) (rep := 83) (swaps := [84]) (by decide +kernel) bound83

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound54 : Lower true (vars 54) (graphGoal 54) 4 :=
  carry_of (old := 54) (rep := 27) (swaps := [32, 83]) (by decide +kernel) bound27

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound39 : Lower true (vars 39) (graphGoal 39) 4 :=
  carry_of (old := 39) (rep := 27) (swaps := [16, 50, 84]) (by decide +kernel) bound27

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound98 : Lower true (vars 98) (graphGoal 98) 4 :=
  carry_of (old := 98) (rep := 21) (swaps := [16, 82, 100]) (by decide +kernel) bound21

def grid119 : CompactGrid := (119, 9, samplesP119, samplesQ119)
def tab119 : CompactTable := (compactCount119, compactPath119, compactLive119, compactPoolIDs119, compactBucket119)
def check119 (k : Nat) := compactNode grid119 tab119 compactDomains119 compactPerms119 k
def sliceSpecs119 : List SliceSpec := [(2, 0, 117, 0, 0, 8, 8), (32, 0, 87, 0, 0, 8, 8), (1, 0, 118, 0, 0, 7, 7), (16, 0, 103, 0, 0, 7, 7), (34, 0, 85, 0, 0, 7, 7), (4, 0, 115, 0, 0, 6, 6), (64, 0, 55, 0, 0, 6, 6), (3, 0, 116, 0, 0, 5, 5), (5, 0, 114, 0, 0, 5, 5), (6, 0, 113, 0, 0, 5, 5), (17, 0, 102, 0, 0, 5, 5), (18, 0, 101, 0, 0, 5, 5), (20, 0, 99, 0, 0, 5, 5), (48, 0, 71, 0, 0, 5, 5), (66, 0, 53, 0, 0, 5, 5), (96, 0, 23, 0, 0, 5, 5), (65, 0, 54, 0, 0, 4, 4), (80, 0, 39, 0, 0, 4, 4), (21, 0, 98, 0, 0, 4, 4), (35, 0, 84, 0, 0, 4, 4), (50, 0, 69, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains119 : ∀ d ∈ compactDomains119, Slice true (vars 119) (graphGoal 119) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(117, 8), (87, 8), (118, 7), (103, 7), (85, 7), (115, 6), (55, 6), (116, 5), (114, 5), (113, 5), (102, 5), (101, 5), (99, 5), (71, 5), (53, 5), (23, 5), (54, 4), (39, 4), (98, 4), (84, 4), (69, 4)]) (specs := sliceSpecs119)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound117
    · exact bound87
    · exact bound118
    · exact bound103
    · exact bound85
    · exact bound115
    · exact bound55
    · exact bound116
    · exact bound114
    · exact bound113
    · exact bound102
    · exact bound101
    · exact bound99
    · exact bound71
    · exact bound53
    · exact bound23
    · exact bound54
    · exact bound39
    · exact bound98
    · exact bound84
    · exact bound69
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs119 : properPairs (graphGoal 119) (asRow samplesP119) (asRow samplesQ119) :=
  compactPairs (g := grid119) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos119 : ∀ p ∈ compactPerms119, autoOK (graphGoal 119) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k4p0 : chartBlock (check119 4) 0 7 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev119k4 : chartBlock (check119 4) 0 7 = true :=
  c119k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k5p0 : chartBlock (check119 5) 0 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k5p1 : chartBlock (check119 5) 32 13 = true := by
  iterate 2 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev119k5 : chartBlock (check119 5) 0 45 = true :=
  (chartBlock_join (a := 32) (b := 13) c119k5p0 c119k5p1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k6p0 : chartBlock (check119 6) 0 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k6p1 : chartBlock (check119 6) 32 31 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev119k6 : chartBlock (check119 6) 0 63 = true :=
  (chartBlock_join (a := 32) (b := 31) c119k6p0 c119k6p1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k7p0 : chartBlock (check119 7) 0 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k7p1 : chartBlock (check119 7) 32 7 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev119k7 : chartBlock (check119 7) 0 39 = true :=
  (chartBlock_join (a := 32) (b := 7) c119k7p0 c119k7p1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k8p0 : chartBlock (check119 8) 0 10 = true := by
  iterate 2 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev119k8 : chartBlock (check119 8) 0 10 = true :=
  c119k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k9p0 : chartBlock (check119 9) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev119k9 : chartBlock (check119 9) 0 1 = true :=
  c119k9p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded119 : Impossible true (graphGoal 119) 9 (vars 119).toFinset := by
  apply compactRoot (g := grid119) (t := tab119) (dom := compactDomains119) (perms := compactPerms119) pairs119 domains119 autos119
  · intro k hk
    change k ≤ 9 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev119k4
    · exact lev119k5
    · exact lev119k6
    · exact lev119k7
    · exact lev119k8
    · exact lev119k9
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound119 : Lower true (vars 119) (graphGoal 119) 10 :=
  plain_low (hints := 66) (by decide +kernel) excluded119

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound123 : Lower true (vars 123) (graphGoal 123) 10 :=
  carry_of (old := 123) (rep := 119) (swaps := [16, 50, 84]) (by decide +kernel) bound119

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound111 : Lower true (vars 111) (graphGoal 111) 10 :=
  carry_of (old := 111) (rep := 95) (swaps := [16, 50, 84]) (by decide +kernel) bound95

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound62 : Lower true (vars 62) (graphGoal 62) 7 :=
  carry_of (old := 62) (rep := 31) (swaps := [65, 50, 80]) (by decide +kernel) bound31

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound61 : Lower true (vars 61) (graphGoal 61) 7 :=
  carry_of (old := 61) (rep := 31) (swaps := [64, 81]) (by decide +kernel) bound31

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound47 : Lower true (vars 47) (graphGoal 47) 7 :=
  carry_of (old := 47) (rep := 31) (swaps := [16, 50, 84]) (by decide +kernel) bound31

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound59 : Lower true (vars 59) (graphGoal 59) 6 :=
  carry_of (old := 59) (rep := 55) (swaps := [16, 50, 84]) (by decide +kernel) bound55

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound42 : Lower true (vars 42) (graphGoal 42) 4 :=
  carry_of (old := 42) (rep := 21) (swaps := [16, 50, 84]) (by decide +kernel) bound21

def grid63 : CompactGrid := (63, 8, samplesP63, samplesQ63)
def tab63 : CompactTable := (compactCount63, compactPath63, compactLive63, compactPoolIDs63, compactBucket63)
def check63 (k : Nat) := compactNode grid63 tab63 compactDomains63 compactPerms63 k
def sliceSpecs63 : List SliceSpec := [(1, 0, 62, 0, 0, 7, 7), (2, 0, 61, 0, 0, 7, 7), (16, 0, 47, 0, 0, 7, 7), (32, 0, 31, 0, 0, 7, 7), (4, 0, 59, 0, 0, 6, 6), (0, 4, 42, 17, 983055, 6, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains63 : ∀ d ∈ compactDomains63, Slice true (vars 63) (graphGoal 63) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(62, 7), (61, 7), (47, 7), (31, 7), (59, 6), (42, 4)]) (specs := sliceSpecs63)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound62
    · exact bound61
    · exact bound47
    · exact bound31
    · exact bound59
    · exact bound42
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs63 : properPairs (graphGoal 63) (asRow samplesP63) (asRow samplesQ63) :=
  compactPairs (g := grid63) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos63 : ∀ p ∈ compactPerms63, autoOK (graphGoal 63) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c63k8p0 : chartBlock (check63 8) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev63k8 : chartBlock (check63 8) 0 1 = true :=
  c63k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded63 : Impossible true (graphGoal 63) 8 (vars 63).toFinset := by
  apply compactRoot (g := grid63) (t := tab63) (dom := compactDomains63) (perms := compactPerms63) pairs63 domains63 autos63
  · intro k hk
    change k ≤ 8 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev63k8
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound63 : Lower true (vars 63) (graphGoal 63) 9 :=
  plain_low (hints := 4146) (by decide +kernel) excluded63

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound124 : Lower true (vars 124) (graphGoal 124) 8 :=
  carry_of (old := 124) (rep := 79) (swaps := [64, 81]) (by decide +kernel) bound79

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound122 : Lower true (vars 122) (graphGoal 122) 8 :=
  carry_of (old := 122) (rep := 87) (swaps := [65, 48, 82]) (by decide +kernel) bound87

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound110 : Lower true (vars 110) (graphGoal 110) 8 :=
  carry_of (old := 110) (rep := 93) (swaps := [16, 50, 84]) (by decide +kernel) bound93

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound107 : Lower true (vars 107) (graphGoal 107) 8 :=
  carry_of (old := 107) (rep := 87) (swaps := [16, 50, 84]) (by decide +kernel) bound87

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound121 : Lower true (vars 121) (graphGoal 121) 7 :=
  carry_of (old := 121) (rep := 91) (swaps := [64, 81]) (by decide +kernel) bound91

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound109 : Lower true (vars 109) (graphGoal 109) 7 :=
  carry_of (old := 109) (rep := 91) (swaps := [16, 50, 49, 84]) (by decide +kernel) bound91

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound106 : Lower true (vars 106) (graphGoal 106) 7 :=
  carry_of (old := 106) (rep := 85) (swaps := [16, 50, 84]) (by decide +kernel) bound85

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound120 : Lower true (vars 120) (graphGoal 120) 5 :=
  carry_of (old := 120) (rep := 23) (swaps := [48, 65, 82, 97, 33]) (by decide +kernel) bound23

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound108 : Lower true (vars 108) (graphGoal 108) 5 :=
  carry_of (old := 108) (rep := 23) (swaps := [33, 48, 81, 100]) (by decide +kernel) bound23

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound105 : Lower true (vars 105) (graphGoal 105) 5 :=
  carry_of (old := 105) (rep := 83) (swaps := [49, 84]) (by decide +kernel) bound83

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound92 : Lower true (vars 92) (graphGoal 92) 5 :=
  carry_of (old := 92) (rep := 23) (swaps := [49, 64, 96, 16]) (by decide +kernel) bound23

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound86 : Lower true (vars 86) (graphGoal 86) 5 :=
  carry_of (old := 86) (rep := 83) (swaps := [32]) (by decide +kernel) bound83

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound58 : Lower true (vars 58) (graphGoal 58) 5 :=
  carry_of (old := 58) (rep := 23) (swaps := [65, 48, 82]) (by decide +kernel) bound23

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound43 : Lower true (vars 43) (graphGoal 43) 5 :=
  carry_of (old := 43) (rep := 23) (swaps := [16, 50, 84]) (by decide +kernel) bound23

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound57 : Lower true (vars 57) (graphGoal 57) 4 :=
  carry_of (old := 57) (rep := 27) (swaps := [64, 81]) (by decide +kernel) bound27

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound45 : Lower true (vars 45) (graphGoal 45) 4 :=
  carry_of (old := 45) (rep := 27) (swaps := [16, 50, 49, 84]) (by decide +kernel) bound27

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound104 : Lower true (vars 104) (graphGoal 104) 4 :=
  carry_of (old := 104) (rep := 21) (swaps := [48, 82, 100]) (by decide +kernel) bound21

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound97 : Lower true (vars 97) (graphGoal 97) 4 :=
  carry_of (old := 97) (rep := 21) (swaps := [82, 100]) (by decide +kernel) bound21

def grid127 : CompactGrid := (127, 12, samplesP127, samplesQ127)
def tab127 : CompactTable := (compactCount127, compactPath127, compactLive127, compactPoolIDs127, compactBucket127)
def check127 (k : Nat) := compactNode grid127 tab127 compactDomains127 compactPerms127 k
def sliceSpecs127 : List SliceSpec := [(1, 0, 126, 0, 0, 10, 10), (2, 0, 125, 0, 0, 10, 10), (4, 0, 123, 0, 0, 10, 10), (8, 0, 119, 0, 0, 10, 10), (16, 0, 111, 0, 0, 10, 10), (32, 0, 95, 0, 0, 10, 10), (64, 0, 63, 0, 0, 9, 9), (3, 0, 124, 0, 0, 8, 8), (5, 0, 122, 0, 0, 8, 8), (10, 0, 117, 0, 0, 8, 8), (17, 0, 110, 0, 0, 8, 8), (20, 0, 107, 0, 0, 8, 8), (34, 0, 93, 0, 0, 8, 8), (40, 0, 87, 0, 0, 8, 8), (48, 0, 79, 0, 0, 8, 8), (0, 4, 42, 81, 252641295, 7, 4), (0, 8, 21, 98, 267387120, 7, 4), (6, 0, 121, 0, 0, 7, 7), (9, 0, 118, 0, 0, 7, 7), (18, 0, 109, 0, 0, 7, 7), (24, 0, 103, 0, 0, 7, 7), (33, 0, 94, 0, 0, 7, 7), (36, 0, 91, 0, 0, 7, 7), (65, 0, 62, 0, 0, 7, 7), (66, 0, 61, 0, 0, 7, 7), (80, 0, 47, 0, 0, 7, 7), (96, 0, 31, 0, 0, 7, 7), (21, 0, 106, 0, 0, 7, 7), (42, 0, 85, 0, 0, 7, 7), (12, 0, 115, 0, 0, 6, 6), (68, 0, 59, 0, 0, 6, 6), (72, 0, 55, 0, 0, 6, 6), (1, 4, 42, 80, 252641280, 6, 4), (2, 8, 21, 96, 267386880, 6, 4), (16, 4, 42, 65, 251658255, 6, 4), (32, 8, 21, 66, 251658480, 6, 4), (64, 4, 42, 17, 983055, 6, 4), (64, 8, 21, 34, 15728880, 6, 4), (7, 0, 120, 0, 0, 5, 5), (11, 0, 116, 0, 0, 5, 5), (13, 0, 114, 0, 0, 5, 5), (14, 0, 113, 0, 0, 5, 5), (19, 0, 108, 0, 0, 5, 5), (22, 0, 105, 0, 0, 5, 5), (25, 0, 102, 0, 0, 5, 5), (26, 0, 101, 0, 0, 5, 5), (35, 0, 92, 0, 0, 5, 5), (37, 0, 90, 0, 0, 5, 5), (38, 0, 89, 0, 0, 5, 5), (41, 0, 86, 0, 0, 5, 5), (49, 0, 78, 0, 0, 5, 5), (50, 0, 77, 0, 0, 5, 5), (69, 0, 58, 0, 0, 5, 5), (74, 0, 53, 0, 0, 5, 5), (84, 0, 43, 0, 0, 5, 5), (104, 0, 23, 0, 0, 5, 5), (17, 4, 42, 64, 251658240, 5, 4), (65, 4, 42, 16, 983040, 5, 4), (66, 8, 21, 32, 15728640, 5, 4), (80, 4, 42, 1, 15, 5, 4), (96, 8, 21, 2, 240, 5, 4), (70, 0, 57, 0, 0, 4, 4), (73, 0, 54, 0, 0, 4, 4), (82, 0, 45, 0, 0, 4, 4), (88, 0, 39, 0, 0, 4, 4), (97, 0, 30, 0, 0, 4, 4), (100, 0, 27, 0, 0, 4, 4), (98, 0, 21, 0, 0, 4, 4), (23, 0, 104, 0, 0, 4, 4), (29, 0, 98, 0, 0, 4, 4), (30, 0, 97, 0, 0, 4, 4), (45, 0, 82, 0, 0, 4, 4), (81, 4, 42, 0, 0, 4, 4), (98, 8, 21, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains127 : ∀ d ∈ compactDomains127, Slice true (vars 127) (graphGoal 127) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(126, 10), (125, 10), (123, 10), (119, 10), (111, 10), (95, 10), (63, 9), (124, 8), (122, 8), (117, 8), (110, 8), (107, 8), (93, 8), (87, 8), (79, 8), (42, 4), (21, 4), (121, 7), (118, 7), (109, 7), (103, 7), (94, 7), (91, 7), (62, 7), (61, 7), (47, 7), (31, 7), (106, 7), (85, 7), (115, 6), (59, 6), (55, 6), (120, 5), (116, 5), (114, 5), (113, 5), (108, 5), (105, 5), (102, 5), (101, 5), (92, 5), (90, 5), (89, 5), (86, 5), (78, 5), (77, 5), (58, 5), (53, 5), (43, 5), (23, 5), (57, 4), (54, 4), (45, 4), (39, 4), (30, 4), (27, 4), (104, 4), (98, 4), (97, 4), (82, 4)]) (specs := sliceSpecs127)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound126
    · exact bound125
    · exact bound123
    · exact bound119
    · exact bound111
    · exact bound95
    · exact bound63
    · exact bound124
    · exact bound122
    · exact bound117
    · exact bound110
    · exact bound107
    · exact bound93
    · exact bound87
    · exact bound79
    · exact bound42
    · exact bound21
    · exact bound121
    · exact bound118
    · exact bound109
    · exact bound103
    · exact bound94
    · exact bound91
    · exact bound62
    · exact bound61
    · exact bound47
    · exact bound31
    · exact bound106
    · exact bound85
    · exact bound115
    · exact bound59
    · exact bound55
    · exact bound120
    · exact bound116
    · exact bound114
    · exact bound113
    · exact bound108
    · exact bound105
    · exact bound102
    · exact bound101
    · exact bound92
    · exact bound90
    · exact bound89
    · exact bound86
    · exact bound78
    · exact bound77
    · exact bound58
    · exact bound53
    · exact bound43
    · exact bound23
    · exact bound57
    · exact bound54
    · exact bound45
    · exact bound39
    · exact bound30
    · exact bound27
    · exact bound104
    · exact bound98
    · exact bound97
    · exact bound82
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs127 : properPairs (graphGoal 127) (asRow samplesP127) (asRow samplesQ127) :=
  compactPairs (g := grid127) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos127 : ∀ p ∈ compactPerms127, autoOK (graphGoal 127) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k6p0 : chartBlock (check127 6) 0 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k6p1 : chartBlock (check127 6) 32 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k6p2 : chartBlock (check127 6) 64 25 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev127k6 : chartBlock (check127 6) 0 89 = true :=
  (chartBlock_join (a := 32) (b := 57) c127k6p0 (chartBlock_join (a := 32) (b := 25) c127k6p1 c127k6p2))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k7p0 : chartBlock (check127 7) 0 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k7p1 : chartBlock (check127 7) 32 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k7p2 : chartBlock (check127 7) 64 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k7p3 : chartBlock (check127 7) 96 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k7p4 : chartBlock (check127 7) 128 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k7p5 : chartBlock (check127 7) 160 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k7p6 : chartBlock (check127 7) 192 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k7p7 : chartBlock (check127 7) 224 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k7p8 : chartBlock (check127 7) 256 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k7p9 : chartBlock (check127 7) 288 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k7p10 : chartBlock (check127 7) 320 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k7p11 : chartBlock (check127 7) 352 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k7p12 : chartBlock (check127 7) 384 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k7p13 : chartBlock (check127 7) 416 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k7p14 : chartBlock (check127 7) 448 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k7p15 : chartBlock (check127 7) 480 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k7p16 : chartBlock (check127 7) 512 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k7p17 : chartBlock (check127 7) 544 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k7p18 : chartBlock (check127 7) 576 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k7p19 : chartBlock (check127 7) 608 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k7p20 : chartBlock (check127 7) 640 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k7p21 : chartBlock (check127 7) 672 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k7p22 : chartBlock (check127 7) 704 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k7p23 : chartBlock (check127 7) 736 29 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev127k7 : chartBlock (check127 7) 0 765 = true :=
  (chartBlock_join (a := 384) (b := 381) (chartBlock_join (a := 192) (b := 192) (chartBlock_join (a := 96) (b := 96) (chartBlock_join (a := 32) (b := 64) c127k7p0 (chartBlock_join (a := 32) (b := 32) c127k7p1 c127k7p2)) (chartBlock_join (a := 32) (b := 64) c127k7p3 (chartBlock_join (a := 32) (b := 32) c127k7p4 c127k7p5))) (chartBlock_join (a := 96) (b := 96) (chartBlock_join (a := 32) (b := 64) c127k7p6 (chartBlock_join (a := 32) (b := 32) c127k7p7 c127k7p8)) (chartBlock_join (a := 32) (b := 64) c127k7p9 (chartBlock_join (a := 32) (b := 32) c127k7p10 c127k7p11)))) (chartBlock_join (a := 192) (b := 189) (chartBlock_join (a := 96) (b := 96) (chartBlock_join (a := 32) (b := 64) c127k7p12 (chartBlock_join (a := 32) (b := 32) c127k7p13 c127k7p14)) (chartBlock_join (a := 32) (b := 64) c127k7p15 (chartBlock_join (a := 32) (b := 32) c127k7p16 c127k7p17))) (chartBlock_join (a := 96) (b := 93) (chartBlock_join (a := 32) (b := 64) c127k7p18 (chartBlock_join (a := 32) (b := 32) c127k7p19 c127k7p20)) (chartBlock_join (a := 32) (b := 61) c127k7p21 (chartBlock_join (a := 32) (b := 29) c127k7p22 c127k7p23)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p0 : chartBlock (check127 8) 0 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p1 : chartBlock (check127 8) 32 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p2 : chartBlock (check127 8) 64 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p3 : chartBlock (check127 8) 96 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p4 : chartBlock (check127 8) 128 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p5 : chartBlock (check127 8) 160 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p6 : chartBlock (check127 8) 192 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p7 : chartBlock (check127 8) 224 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p8 : chartBlock (check127 8) 256 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p9 : chartBlock (check127 8) 288 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p10 : chartBlock (check127 8) 320 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p11 : chartBlock (check127 8) 352 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p12 : chartBlock (check127 8) 384 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p13 : chartBlock (check127 8) 416 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p14 : chartBlock (check127 8) 448 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p15 : chartBlock (check127 8) 480 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p16 : chartBlock (check127 8) 512 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p17 : chartBlock (check127 8) 544 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p18 : chartBlock (check127 8) 576 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p19 : chartBlock (check127 8) 608 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p20 : chartBlock (check127 8) 640 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p21 : chartBlock (check127 8) 672 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p22 : chartBlock (check127 8) 704 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p23 : chartBlock (check127 8) 736 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p24 : chartBlock (check127 8) 768 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p25 : chartBlock (check127 8) 800 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p26 : chartBlock (check127 8) 832 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p27 : chartBlock (check127 8) 864 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p28 : chartBlock (check127 8) 896 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p29 : chartBlock (check127 8) 928 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p30 : chartBlock (check127 8) 960 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p31 : chartBlock (check127 8) 992 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p32 : chartBlock (check127 8) 1024 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p33 : chartBlock (check127 8) 1056 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p34 : chartBlock (check127 8) 1088 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p35 : chartBlock (check127 8) 1120 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p36 : chartBlock (check127 8) 1152 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p37 : chartBlock (check127 8) 1184 26 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev127k8 : chartBlock (check127 8) 0 1210 = true :=
  (chartBlock_join (a := 608) (b := 602) (chartBlock_join (a := 288) (b := 320) (chartBlock_join (a := 128) (b := 160) (chartBlock_join (a := 64) (b := 64) (chartBlock_join (a := 32) (b := 32) c127k8p0 c127k8p1) (chartBlock_join (a := 32) (b := 32) c127k8p2 c127k8p3)) (chartBlock_join (a := 64) (b := 96) (chartBlock_join (a := 32) (b := 32) c127k8p4 c127k8p5) (chartBlock_join (a := 32) (b := 64) c127k8p6 (chartBlock_join (a := 32) (b := 32) c127k8p7 c127k8p8)))) (chartBlock_join (a := 160) (b := 160) (chartBlock_join (a := 64) (b := 96) (chartBlock_join (a := 32) (b := 32) c127k8p9 c127k8p10) (chartBlock_join (a := 32) (b := 64) c127k8p11 (chartBlock_join (a := 32) (b := 32) c127k8p12 c127k8p13))) (chartBlock_join (a := 64) (b := 96) (chartBlock_join (a := 32) (b := 32) c127k8p14 c127k8p15) (chartBlock_join (a := 32) (b := 64) c127k8p16 (chartBlock_join (a := 32) (b := 32) c127k8p17 c127k8p18))))) (chartBlock_join (a := 288) (b := 314) (chartBlock_join (a := 128) (b := 160) (chartBlock_join (a := 64) (b := 64) (chartBlock_join (a := 32) (b := 32) c127k8p19 c127k8p20) (chartBlock_join (a := 32) (b := 32) c127k8p21 c127k8p22)) (chartBlock_join (a := 64) (b := 96) (chartBlock_join (a := 32) (b := 32) c127k8p23 c127k8p24) (chartBlock_join (a := 32) (b := 64) c127k8p25 (chartBlock_join (a := 32) (b := 32) c127k8p26 c127k8p27)))) (chartBlock_join (a := 160) (b := 154) (chartBlock_join (a := 64) (b := 96) (chartBlock_join (a := 32) (b := 32) c127k8p28 c127k8p29) (chartBlock_join (a := 32) (b := 64) c127k8p30 (chartBlock_join (a := 32) (b := 32) c127k8p31 c127k8p32))) (chartBlock_join (a := 64) (b := 90) (chartBlock_join (a := 32) (b := 32) c127k8p33 c127k8p34) (chartBlock_join (a := 32) (b := 58) c127k8p35 (chartBlock_join (a := 32) (b := 26) c127k8p36 c127k8p37))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p0 : chartBlock (check127 9) 0 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p1 : chartBlock (check127 9) 32 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p2 : chartBlock (check127 9) 64 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p3 : chartBlock (check127 9) 96 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p4 : chartBlock (check127 9) 128 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p5 : chartBlock (check127 9) 160 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p6 : chartBlock (check127 9) 192 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p7 : chartBlock (check127 9) 224 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p8 : chartBlock (check127 9) 256 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p9 : chartBlock (check127 9) 288 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p10 : chartBlock (check127 9) 320 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p11 : chartBlock (check127 9) 352 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p12 : chartBlock (check127 9) 384 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p13 : chartBlock (check127 9) 416 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p14 : chartBlock (check127 9) 448 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p15 : chartBlock (check127 9) 480 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p16 : chartBlock (check127 9) 512 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p17 : chartBlock (check127 9) 544 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p18 : chartBlock (check127 9) 576 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p19 : chartBlock (check127 9) 608 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p20 : chartBlock (check127 9) 640 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p21 : chartBlock (check127 9) 672 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p22 : chartBlock (check127 9) 704 7 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev127k9 : chartBlock (check127 9) 0 711 = true :=
  (chartBlock_join (a := 352) (b := 359) (chartBlock_join (a := 160) (b := 192) (chartBlock_join (a := 64) (b := 96) (chartBlock_join (a := 32) (b := 32) c127k9p0 c127k9p1) (chartBlock_join (a := 32) (b := 64) c127k9p2 (chartBlock_join (a := 32) (b := 32) c127k9p3 c127k9p4))) (chartBlock_join (a := 96) (b := 96) (chartBlock_join (a := 32) (b := 64) c127k9p5 (chartBlock_join (a := 32) (b := 32) c127k9p6 c127k9p7)) (chartBlock_join (a := 32) (b := 64) c127k9p8 (chartBlock_join (a := 32) (b := 32) c127k9p9 c127k9p10)))) (chartBlock_join (a := 192) (b := 167) (chartBlock_join (a := 96) (b := 96) (chartBlock_join (a := 32) (b := 64) c127k9p11 (chartBlock_join (a := 32) (b := 32) c127k9p12 c127k9p13)) (chartBlock_join (a := 32) (b := 64) c127k9p14 (chartBlock_join (a := 32) (b := 32) c127k9p15 c127k9p16))) (chartBlock_join (a := 96) (b := 71) (chartBlock_join (a := 32) (b := 64) c127k9p17 (chartBlock_join (a := 32) (b := 32) c127k9p18 c127k9p19)) (chartBlock_join (a := 32) (b := 39) c127k9p20 (chartBlock_join (a := 32) (b := 7) c127k9p21 c127k9p22)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k10p0 : chartBlock (check127 10) 0 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k10p1 : chartBlock (check127 10) 32 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k10p2 : chartBlock (check127 10) 64 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k10p3 : chartBlock (check127 10) 96 32 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k10p4 : chartBlock (check127 10) 128 4 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev127k10 : chartBlock (check127 10) 0 132 = true :=
  (chartBlock_join (a := 64) (b := 68) (chartBlock_join (a := 32) (b := 32) c127k10p0 c127k10p1) (chartBlock_join (a := 32) (b := 36) c127k10p2 (chartBlock_join (a := 32) (b := 4) c127k10p3 c127k10p4)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k11p0 : chartBlock (check127 11) 0 10 = true := by
  iterate 2 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev127k11 : chartBlock (check127 11) 0 10 = true :=
  c127k11p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k12p0 : chartBlock (check127 12) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev127k12 : chartBlock (check127 12) 0 1 = true :=
  c127k12p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded127 : Impossible true (graphGoal 127) 12 (vars 127).toFinset := by
  apply compactRoot (g := grid127) (t := tab127) (dom := compactDomains127) (perms := compactPerms127) pairs127 domains127 autos127
  · intro k hk
    change k ≤ 12 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev127k6
    · exact lev127k7
    · exact lev127k8
    · exact lev127k9
    · exact lev127k10
    · exact lev127k11
    · exact lev127k12
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound127 : Lower true (vars 127) (graphGoal 127) 13 :=
  plain_low (hints := 4146) (by decide +kernel) excluded127


end PEqualNP.Outside.L_meta_10642

open PEqualNP.Outside.L_meta_10642 in
theorem PEqualNP.Outside.L_meta_10642 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _oneNot correct
  exact replaceShort (by simpa only [sevenInputs, show graph = graphGoal 127 by decide +kernel] using excluded127) gates o fit correct
