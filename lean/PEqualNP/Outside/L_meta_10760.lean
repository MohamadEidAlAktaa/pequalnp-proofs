import PEqualNP.Defs

-- The signed circuit and cofactor framework follows L_meta_10802, L_meta_1674, L_meta_670,
-- and the checker in L_meta_1667 (Apache-2.0).
-- The verified restriction bounds and monotone witness below concern this graph.

namespace PEqualNP.Outside.L_meta_10760
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
def graph : Sig := 0xfffffffffffefffafffeffeefefeeca0fffffffffffefffafffeffeefefeeca0fffffffffffefffafffeffeefefeeca0fffffffffffefffafffeffeefefeeca0
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
 (x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 5 && x 6)
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
 (x 0 &&& x 2) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 5 &&& x 6)
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



def target (x : Fin 7 → Bool) : Bool := decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or, [1, 6]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [7, 8]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [10, 1]⟩, ⟨.and, [4, 11]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [0, 13]⟩, ⟨.and, [3, 5]⟩, ⟨.and, [6, 10]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [17, 14]⟩, ⟨.or, [18, 15]⟩, ⟨.or, [19, 16]⟩], 20⟩

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
  (x 0 &&& x 2) ||| (x 1 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 5 &&& x 6)
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

def samplesP91 : Nat → Bits
  | 0 => 0x5f6fffcd469bf67deef7f8f1b73799514afbdb7eba7949c901b2adad64
  | 1 => ~~~(0x11103200250b3e000415008197391d956ea2016ce33011fd81ba26c976 : Bits)
  | 3 => 0x7d5fb7bffd8d197eff9f972eeb993d84b566ff44e7aafe34924c7bca92
  | 4 => ~~~(0x46005804a855b00a8021f22a3172015b5805814ac4a6a7493de192ef2 : Bits)
  | 6 => 0x76bffff22b677a7fbd7f4f83977f669524bf7dbded563074819b167c72
  | _ => 0

def samplesQ91 : Nat → Bits
  | 0 => 0x20911052812408a82084491250b00388844a4a2088210a498850a92844
  | 1 => ~~~(0x6eebedeedbfde3cdbfddfebf83eef8ef9ff6a9eeebf77ff3f3a867d9fe : Bits)
  | 3 => 0x2a244420250228c9210189280e0a0a108468904420246439028638890
  | 4 => 0x4684484088143440448b2848142a80401b4a1c20090109230a846d108
  | 6 => 0x940828550088551090122442d030c0212313408214420942487145422
  | _ => 0

def compactPerms91 : Array (List Nat) := ([[], [49, 100], [16, 99], [16, 97, 99, 100], [48, 49, 67, 100], [48, 65], [64, 49, 99, 100], [64, 97], [96, 67], [96, 65, 67, 100]] : List (List Nat)).toArray

def compactDomains91 : Array (Sig × Nat) := ([(subcube 1 0, 4), (subcube 2 0, 4), (subcube 8 0, 4), (subcube 16 0, 4), (subcube 64 0, 4)] : List (Sig × Nat)).toArray

def compactWords91 : Nat → Nat
  | 0 => 0xff0ff0339b38c447f6452ff0ff082be51a00d04ffc1fe05749e23196566ff03544885fe0bd68f93a1ffe006fffd08900688d11f
  | _ => 0

def compactCount91 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 2
  | 4 => 1
  | _ => 0

def compactPath91 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords91 (26 + 12*i) 12
  | 4 => let v := readCompactBits compactWords91 (279 + 12*i) 12
    (readCompactBits compactWords91 (267 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def compactLive91 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords91 (0 + 5*i) 5
  | 5 => readCompactBits compactWords91 (50 + 6*i) 6
  | 4 => readCompactBits compactWords91 (291 + 7*i) 7
  | _ => 0

def compactPoolIDs91 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords91 (20 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords91 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits compactWords91 (64 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords91 (62 + 2*(v &&& 1)) (2*n)
    compactIDsFromBits bits 2 n
  | 4 => let v := readCompactBits compactWords91 (298 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords91 (298 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket91 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords91 (68 + 1*(i % 4)) 1
    let off := ((i/4 + d) % 15)
    let v := readCompactBits compactWords91 (72 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 4 => let d := readCompactBits compactWords91 (300 + 2*(i % 2)) 2
    let off := ((i/2 + d) % 9)
    let v := readCompactBits compactWords91 (304 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | _ => []

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
  | 0 => 0xdffb4f7fcd93bb4
  | 2 => ~~~(0x4020075441838b4 : Bits)
  | 4 => 0xf3e7a33c7f8cccc
  | 6 => ~~~(0x1403eb080d9c3cc : Bits)
  | _ => 0

def samplesQ85 : Nat → Bits
  | 0 => 0x204080920800224
  | 2 => 0x420006012400142
  | 4 => 0xc89186842a5c88
  | 6 => ~~~(0xeaf69edb6f5a3ee : Bits)
  | _ => 0

def compactPerms85 : Array (List Nat) := ([[], [32], [100], [100, 32]] : List (List Nat)).toArray

def compactDomains85 : Array (Sig × Nat) := ([(subcube 16 0, 4)] : List (Sig × Nat)).toArray

def compactWords85 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def compactCount85 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath85 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive85 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords85 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs85 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords85 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords85 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket85 (k : Nat) (i : Nat) : List Nat := match k with
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

def samplesP87 : Nat → Bits
  | 0 => 0xdfbfff3b167bd5ffbf3bab65be76583b9fd9bf3f43c39210f4e5ec8
  | 1 => 0xed3f47f6679d00f9fdfdd7db4c9845800bffd9d98db8006b0f77014
  | 2 => ~~~(0x4080440103d9c1008109c3248c9855a993806b594503806bfc872dc : Bits)
  | 4 => 0xfafffcf5d9f8caf7e3ffeb3ec18fe7a1cfa767d07f6781ef0c9a33c
  | 6 => ~~~(0xb0100365438de012030ab5b40066fb3c80195900be393ff0470f3c : Bits)
  | _ => 0

def samplesQ87 : Nat → Bits
  | 0 => 0x204820440904284010232086020824002141a028030082082444888
  | 1 => 0x12d13c489040ef7860086b87c279902649df085080a08e1f3f75004
  | 2 => 0x408414010290812408904a000051010908141084205008160230502
  | 4 => 0x520011024031081030484081402005016204500480520a0408a230
  | 6 => ~~~(0xf4fcf6edbfd7a96d7bbf7af62bdd757f7955fdfcebf6db5ea674fbe : Bits)
  | _ => 0

def compactPerms87 : Array (List Nat) := ([[], [32]] : List (List Nat)).toArray

def compactDomains87 : Array (Sig × Nat) := ([(subcube 2 0, 5), (subcube 64 0, 5), (subcube 0 2, 5), (subcube 1 0, 4), (subcube 4 0, 4), (subcube 16 2, 4)] : List (Sig × Nat)).toArray

def compactWords87 : Nat → Nat
  | 0 => 0x39627e522017650397e8058231d1f
  | _ => 0

def compactCount87 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 1
  | 4 => 1
  | _ => 0

def compactPath87 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords87 (29 + 12*i) 12
  | 4 => let v := readCompactBits compactWords87 (83 + 12*i) 12
    (readCompactBits compactWords87 (71 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def compactLive87 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords87 (0 + 5*i) 5
  | 5 => readCompactBits compactWords87 (41 + 6*i) 6
  | 4 => readCompactBits compactWords87 (95 + 7*i) 7
  | _ => 0

def compactPoolIDs87 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords87 (23 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords87 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits compactWords87 (55 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords87 (47 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 4 => let v := readCompactBits compactWords87 (102 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords87 (102 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket87 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords87 (61 + 1*(i % 1)) 1
    let off := ((i/1 + d) % 1)
    let v := readCompactBits compactWords87 (62 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | 4 => let d := readCompactBits compactWords87 (104 + 1*(i % 1)) 1
    let off := ((i/1 + d) % 1)
    let v := readCompactBits compactWords87 (105 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
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
  | 0 => 0xbeefffff5b5b0fbfdb3759cc3ff7cfeff6bdc7defb75fc665eae88c39c43761f1ef6660bfbfb9f4feb7d95f8dca77f8a58e58a7d0856a36ee43b3e846091b30dd7ccf56ee59bf1795688dc92271062048751152dd13b310
  | 1 => 0xdfabf59fffebf9ce7039ccb07ffeffb67fdef8f90f878f879fdfc78ce0739863ec0000b1fddffbf8f39e1f3f7f3b8ff1a0fa0f87f3e0fc1f07c1c00513260012eaef67f7b9e31e1e0d0f70e3c82080393886dbc9a1d4424
  | 2 => ~~~(0x24804120041a5844b1988cf000041242109844c0b460607030fa64686699e57469f22b8d100011063889230088d2ff510ec0daf1b16cb964575a30557beab548489c5c5245975db2e8b60a70ff1d0793bdf9f2315b577c : Bits)
  | 3 => 0xfad7fefebeb7a7d4bf4332273ffffb7fe945bd3d375a36ff677fb6164ed827c4c1c90083d73ffff12febfaa9a7ff69350b2cf59f370ec59148f46718042e0853be77bfcd663423c7aa1927bf28e11048088e6f175c64448
  | 4 => 0xf75fff73ffd4ffa96f8caa5bbfa9fffdff3bf6e7ccee4b7ff92d776a132cdf1b03062973fff477f6d691faf6f8dcfe4c54d56d62cf995a909734b9679b102383d59bde913f5cdc91aae6e84d1612c1b17060bc223e818b4
  | 6 => ~~~(0x108400001a920b8833277a3000208a004014f0b1040008665c2fd78a5852770b89666df100101260821118a8f4324b0848f5ef57e7c8f41986b07c07bb37339bd246360021b69a158a0cfcdb2e32e3bdfce67d0df84fcb4 : Bits)
  | _ => 0

def samplesQ95 : Nat → Bits
  | 0 => 0x411042012404904020c82412a410080c10404c2204340200e1810100420480c0210898604b089040090400a04024148900039882088863012000e18090200821820c812c218801280200c012091052018090150d0128210
  | 1 => 0x205502702210042087443247b820018208500437c8103619c02c282210802110008f8d0858cb7218121200082801004943ca80170fd01101608fa060401850806a4a4163b92104120108304000110e05709793c8a154004
  | 2 => 0x2482052404121000a10884d120422010582808088406411022a044004090c024015201900a24aa40040440492020046468c0054162080180209024002048240706222025206080440400a00a020084664244090e842802
  | 3 => 0x52880834508480140b88d984748806001aac98804e4488027804001812050200a30327507308dc12481100104900186141518c83029ea188e4047830080240b9035b60c46002281001104890922d04a84686c175820440
  | 4 => 0x8a2008409220016002341a04181441040281108118088a20c1000142842000494204286a4140500800088500048cb1030102108600308228c500c080441001605911c900450900088840004124680980148282216810a0
  | 6 => ~~~(0xef7befdbf57ffd77eef8addff77defff5defefeaaeff6fd5f7eb6d77ffeffdf6ffbdba7d4fbadffdbfd7dcfdfeffddefdebfdefebeadefddbf69f7d7d6fdfefff27fb72e77ffbfbfcbddfedfbdbafb6feefc7d9ff96fef6 : Bits)
  | _ => 0

def compactPerms95 : Array (List Nat) := ([[], [32], [49, 100], [49, 32, 100]] : List (List Nat)).toArray

def compactDomains95 : Array (Sig × Nat) := ([(subcube 1 0, 7), (subcube 2 0, 7), (subcube 4 0, 7), (subcube 8 0, 7), (subcube 16 0, 7), (subcube 64 0, 7), (subcube 0 2, 6), (subcube 0 8, 6), (subcube 10 0, 5), (subcube 18 0, 5), (subcube 72 0, 5), (subcube 2 8, 5), (subcube 16 2, 5), (subcube 64 8, 5), (subcube 3 0, 4), (subcube 5 0, 4), (subcube 6 0, 4), (subcube 9 0, 4), (subcube 17 0, 4), (subcube 20 0, 4), (subcube 65 0, 4), (subcube 68 0, 4), (subcube 24 2, 4)] : List (Sig × Nat)).toArray

def compactWords95 : Nat → Nat
  | 0 => 0x9058af2ce4c2749e8299a99d9a6c7e4b907674515674d5f72fdead3b2d5a8b4c5d2662910e5caa3054063d1e9c01434ff01ea14a5f83276916fce2f6bff803385fe03fc07f80be101a197027f80ff01fe0119ab1139240ad42267b995c253fe03fc017a330c5a07de90e50fff010085645806890c011bc048bc20604095573eb34d2951451050d2faaf14dcececc34aeaa489ca9268d07d864c59246640e3242f619800102802ec82c7661c1820c040172450c9700363b28ac434824d462f0814e005c1c515247018704180805c4891c286429c6448a0706180ae044898c046402e221cd18065a505061c30132017121e48c93041422e1eb8c071e59706123c0126810d8260141308c6c3830c047805c3cdae244c21b0a3c38324180935c1841b5c38318200430e480c3860a7060200b874804382840e0cc8c001977fdfffdef7ffffdfffdff7ffdfffffffffff5fffdfffffffdfdfccc099811301e60a48548ca9115662a4c5498a9111261acc249845214a32142428087310a6214c4284653042228cc5198490a8c8808804803fe0ff03acf417fe08819603c986b5ff030eca85fe0ff0511fc9ade1a77d54721c8d77011cfddc430e44e6f4770038c46080a4ceaf86b020cb6f63f01a5e6e9314e31183cd0332c30806e597418a438cc1e6f5803c5c290e316d9a5e4060ffffffffffffd21519109101108d0090070b1a23f
  | 1 => 0xf499fe0002839d05fe0104b718f7fe0050f52eafd2d80ab4e489fe0012949e777485208b2408ce4b8eea92ef968c485e16ece8c61ec4ce91fe012017fe00fc7fd446d02e3c67866bca9b242bbc0bfe01445b6ed54859d28e8a6f72adfe01b66866cf7833fe01fe0026a73ae6fccaba5dfe01e0cdfe01fe01121e3e9f9c43cc0f963f3802da0c1e5654010cf0ae362692d0146c87e8bf744edc1a7e659a543ec8a8db9480d0e8367266dc3e9dfe011e9754054607ee10c8d232d77ce5fe01fe01fe00fa6ca0fca026b6a5fe01c4d0b8de20f244bd1d079afedc3bfe0158e2f00106262001b231268811210000818010000238020b0b1a8a8a8a8a9a0a1989899909189808179707169615e282a19101011090000045000100002545450901011848022e0100230182c500cfef76ff773e7f7bbf4ff773bddefadf6fd7cfe7f7df77eafd7ef54ff5faf9fcfedf7e9fcfd69c47ce236711b380690b04e256712b38159c4ace256712838959c01ce50a72b5215a9ca5ce6267081214088a0ce5027281111c9cae4644a42a739529ca8ce416703d38989cb98a80998a80398880598480998480398090a98a80898880498280498090a90a80890a8048c880488a80888a80288880880880483546ddff8061a5cb182a47f806b035eebfc020977ebd0f0fcc6a0d4ff017d2a9f1ff80d3be789506982827bcd7d6d518dab64f3ba4dfcd
  | 2 => 0x28de93fe0b05c7a3fc064f253e24bfc1fe0ff07f828cbfe0ff029bbfc1fe0ff07f83fc1fe0f724d1abd5042ac9ff81805619d795755d51f61c4a429a0a282da019c098a8089ca98880488a8088048888088041013
  | _ => 0

def compactCount95 (k : Nat) : Nat := match k with
  | 9 => 1
  | 8 => 7
  | 7 => 26
  | 6 => 33
  | 5 => 5
  | _ => 0

def compactPath95 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => 0
  | 8 => readCompactBits compactWords95 (30 + 12*i) 12
  | 7 => let v := readCompactBits compactWords95 (973 + 15*i) 15
    (readCompactBits compactWords95 (913 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 6 => let v := readCompactBits compactWords95 (4949 + 17*i) 17
    (readCompactBits compactWords95 (4541 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 5 => let v := readCompactBits compactWords95 (8353 + 14*i) 14
    (readCompactBits compactWords95 (8209 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | _ => 0

def compactLive95 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => readCompactBits compactWords95 (0 + 6*i) 6
  | 8 => readCompactBits compactWords95 (114 + 7*i) 7
  | 7 => readCompactBits compactWords95 (1363 + 8*i) 8
  | 6 => readCompactBits compactWords95 (5510 + 9*i) 9
  | 5 => readCompactBits compactWords95 (8423 + 10*i) 10
  | _ => 0

def compactPoolIDs95 (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let v := readCompactBits compactWords95 (24 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords95 (6 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 8 => let v := readCompactBits compactWords95 (548 + 11*i) 11
    let n := v >>> 7
    let bits := readCompactBits compactWords95 (163 + 5*(v &&& 127)) (5*n)
    compactIDsFromBits bits 5 n
  | 7 => let v := readCompactBits compactWords95 (2789 + 12*i) 12
    let n := v >>> 8
    let bits := readCompactBits compactWords95 (1571 + 7*(v &&& 255)) (7*n)
    compactIDsFromBits bits 7 n
  | 6 => let v := readCompactBits compactWords95 (5983 + 8*i) 8
    let n := v >>> 5
    let bits := readCompactBits compactWords95 (5807 + 8*(v &&& 31)) (8*n)
    compactIDsFromBits bits 8 n
  | 5 => let v := readCompactBits compactWords95 (8474 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords95 (8473 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket95 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let d := readCompactBits compactWords95 (625 + 3*(i % 5)) 3
    let off := ((i/5 + d) % 21)
    let v := readCompactBits compactWords95 (640 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 7 => let d := readCompactBits compactWords95 (3101 + 5*(i % 24)) 5
    let off := ((i/24 + d) % 88)
    let v := readCompactBits compactWords95 (3221 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 6 => let d := readCompactBits compactWords95 (6247 + 6*(i % 31)) 6
    let off := ((i/31 + d) % 111)
    let v := readCompactBits compactWords95 (6433 + 16*off) 16
    if v >>> 8 == (i/104729)%251 then [v &&& 255] else []
  | 5 => let d := readCompactBits compactWords95 (8484 + 2*(i % 5)) 2
    let off := ((i/5 + d) % 29)
    let v := readCompactBits compactWords95 (8494 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | _ => []

def samplesP107 : Nat → Bits
  | 0 => 0x7abf2fefd4580fffe76c98cbfa8ec006feece7267402acb7e488
  | 1 => 0x5e7ffcbd6d8447dd3ffb73515d20252bfc573e9cf990517d5260
  | 3 => ~~~(0x841009dd004780c240c89115adec13a0454a5383597ac8d6cea : Bits)
  | 5 => 0x7dfff7d6db677faeffb5adbd1fd343bfa797897b31d7860e2d72
  | 6 => ~~~(0x108024264d434880032130c91da367a8a2870a0679d2d7363770 : Bits)
  | _ => 0

def samplesQ107 : Nat → Bits
  | 0 => 0x545511008a2f590a00c6a1c89102264ec8c21004cc89c378480
  | 1 => 0x21a045408253ae081245c078b1891013d442121020b199ed5040
  | 3 => 0x84910051004514200a82a04084281042a2008850c4804128214
  | 5 => 0x21000082408002409000000002408000001804a100000002122
  | 6 => ~~~(0x6f7dfb9dbefef5febbee7f9fcfffbb74eeefbbdf7fcefe37b7f6 : Bits)
  | _ => 0

def compactPerms107 : Array (List Nat) := ([[], [16, 99]] : List (List Nat)).toArray

def compactDomains107 : Array (Sig × Nat) := ([(subcube 1 0, 5), (subcube 2 0, 5), (subcube 8 0, 5), (subcube 64 0, 5)] : List (Sig × Nat)).toArray

def compactWords107 : Nat → Nat
  | 0 => 0x41b1f
  | _ => 0

def compactCount107 (k : Nat) : Nat := match k with
  | 6 => 1
  | _ => 0

def compactPath107 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | _ => 0

def compactLive107 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords107 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs107 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords107 (13 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords107 (5 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | _ => []

def compactBucket107 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP111 : Nat → Bits
  | 0 => 0x7d6ffd5fffff6c6cc32c675ffffff3d9edca3916fdf7bef98dedee19903099d10099c77ffff9f3ff3f2398df964310624670f0cf3e7f1eec479c10300f18c6fffe67299e4698d0673a00105a6ec408f5ef5220
  | 1 => 0x5f5bfffb4f3bb9c3f2c508dfefed3fff9f1dd9e35f1dcfa7c2f0967271ed70200a023fffb7ae9e3bdcbcf5fe9cbc62d4e9d9347a8b1c65519002610231fdfcbdbbb314e1e9d283cadcc9c000112adeb3348980
  | 2 => ~~~(0x44c08010cb1244263b66bd0060520000c8c81c15e0722d1a27cce385998c57feb7f80012408c21e222c80e09ebb4278a0ff88fc625e05697dfff3cbb5014031224d31ec499b41fa1fefe8a3b7fc1823aebffc : Bits)
  | 3 => 0x77affaffbcf19fbeec9e632fff3fecff13b5bfddfee761d7e00e19e5df88c5cee0027fffec59eec6e6dc1ff3f9b8df5ba67e888ce142e11b1023e2c884ffc77365dc276439371c7e25662820113b3964988c54
  | 5 => 0x7ef7ffedfdf677733972fcbfded7ffef6eeee7fb9e1bf75a333e660c6dd38e3e0b7c7fa57fcf5d3c637feaed7b3f82a891a7cb75449f85a1e8ec03c337237bde03ccdaf9910d63b118ade083a251e00bc235c8
  | 6 => ~~~(0x1020004801721920884c6430080000c9030039129c11c503c1ae3645f5e1989e0a9a072400491c20441018df113c92c2c770f04f8d1fe591d2ae63f23838c6de01f60ef1b11492673cedf05a7b7be8f5d3ddc0 : Bits)
  | _ => 0

def samplesQ111 : Nat → Bits
  | 0 => 0x29104a0800010921451982881031001124980392000a12812001004424824089d2004631c483201212000100604c22720018803212104150802020a4410c0f0e224098240080006060c084061c008e1a91200
  | 1 => 0x20a42088b88402280d1ae62d0480089078008eb0b4b4211a080241010802890ed1d92e5932a0081084084088832d499604539321257432414421082101d968a99b11004108508100100b4550a1ac9e93348100
  | 2 => 0x44c89022c21044023a643d648208204cc9214c09acd0cc120180c10011040156257f394c30500a01012040241720c108f4c263c4c9a58c800485080a2ae370e1582801024040a00a061a63d0a23e51c504002
  | 3 => 0x8520d200108600102611890e014002882cb0009020984a001218008200412310e2440a68c1080044080122114408221a1080c0a4883049c209001040c24855264402400112210500644282448422164880850
  | 5 => 0x10810020600880440840142124004400410104008400840444000a290200040200291004100450800442844001204000a04201400084800110084100202120400800228800120a10820820902014008420488
  | 6 => ~~~(0x6fdfbff7efadfeff77f7dbfefff79efddffff5fffbcfffed7f7bddbffb7eff7dff77f7f7df7dffbdf5fe7effd7f6fe7fffedeeffffbbddfffdfbdfbfeebef7fef7f7affbfd7fbbf7bffdbeff7ff3edfdfbdfda : Bits)
  | _ => 0

def compactPerms111 : Array (List Nat) := ([[], [33, 48, 101]] : List (List Nat)).toArray

def compactDomains111 : Array (Sig × Nat) := ([(subcube 1 0, 7), (subcube 2 0, 7), (subcube 4 0, 7), (subcube 8 0, 7), (subcube 32 0, 7), (subcube 64 0, 7), (subcube 0 2, 6), (subcube 0 4, 6), (subcube 3 0, 5), (subcube 5 0, 5), (subcube 34 0, 5), (subcube 1 4, 5), (subcube 8 2, 5), (subcube 32 2, 5), (subcube 64 4, 5), (subcube 9 0, 4), (subcube 33 0, 4), (subcube 72 0, 4), (subcube 7 0, 4), (subcube 40 2, 4), (subcube 42 0, 4), (subcube 65 4, 4), (subcube 69 0, 4)] : List (Sig × Nat)).toArray

def compactWords111 : Nat → Nat
  | 0 => 0x3820c05995005c80e325c0156a1419c624ccaf265654765158863914c146068185640a286020073016c24028c3629538c1cb22ad64451c60ab92721ac51c35802767191d3114b8e1668307146430a20d4f0d081401c5c4ca9120c5ab002b8a182ac98b560b89951a40e850871915061c1060200aae2040e0b3214a900e0c3015c541160864110911869516b8a130a34d3b0e0830100b880f2068c03264c2151e507c73c6020036b89c666352345e0971b2c658998c9198d68bcdb12a2ca131f188196874584066d89426146a40e0830136007ae1e6c818084d70f200428704509980e27feffffbffef7e6ffafe7e7efffffbffff7f7fafffeffaeffffffdfefeffafffeffff6606cc0c9815216a02dcc1f84b330e242cc25884b330da22b405490a9195612a425480ab315262a4c54888b30d261948528c87110a22140439885310a620464c44485464444424404403402ff01d47fc1fe0d61004e88bfe0091ff8302abc86007f83ad9eae797ff8174e98da84de045e1d0adb5ff802244206e1fce94d4ec7ea9692e85e67e498318198003388c1068a4ce2ee6d0a238780cde76d131768b851982023b58689773d5cbe0b443e2ede024cba8dc28ce230600d670d5938521c460bc1bce18b19483db81a6b2eb30cc1de92e9600710ceb1690ccb4060ffffefffbffffffffffd21519311111111109101100d0890090070b1a23f
  | 1 => 0x48f89e23826ccc48f11c2348590920e218822000000c0226088e0d1c260890901a8c2718e827483865422a1a080b22261b14652298f20ab82a08000c022a002a2c0026e826261e8ee826262a2a2a32074420083320b91a162a260a0e04260a260a0a0c020e040c033ff3f3f7b3df5faf937bf773f9bce9fdfa7fbed7efa7feb9ff9fedeefb5fafdeadbefa7fafdbefa7f3fbec138d99c634858a02c539579c6b4e32a428b38959c0848522428521689c6fce07e71bf382490b24059272b511139cc74853a028121408ca0ce502728111268cb34059a72b9215c8cae4057672b9394d9c398a8099888079868099828c998090a98a80898880698680890a8c890a88890a80890a8068ca8088c88068c880484a88884a80880a8c880a84880a808808806db067d427a2ff00467b71c6e304979d49ffc07f80ff01fe03fc052846737fe003ce84192b197ab3b97bf3f801012df8e1bba3a7353e994daae06f929fe02f52c918d323e20f79cbb178d67627e949330ee92a9c353d0858999525100e8e4882ff01fe01fd5873eca2caa4d05e820a565a62c8282cf42601636d0698ff80ff01fe00887ff803c0f2802ec0b0a0ba76886b2c00681398410608410410e11402c231f8cf667823b19ccae1c6ac3365890bcc581ab4d552a144eca51d1ae8693eb1de4dd464d2bb14509b443c1bd8b343fa12606480cc0010a85005d9058e0c
  | 2 => 0x259058ff87f83107f87f8129ff8014acd3b69b3e459d2e54402aad6b9f338ef1bc6e1f8e5a05b401a428485890b5214a42a42a12a02232a62201a32a02201a02e61a02202e60a32202a62201a02a322018ba23f50e6ee09d269bd427fe03c53ea43ff00bc45621568d57592712d0a1f8819129ec48d19749c96fd849ac21c0bff016d21b20e09aff01d6f9b5a0dafd2145ccbfc0159dff013917fc07f805c725ea529717835481a816f933faa184bfe02f59fd3d5b6aecaffc06bbf7d484d29290ff808b70b65bfc0108eff00dc01107b697ff01fe018cff5b00a21fe03e83d39eff005c655835d0c9e02cc575e5e3470d5a61aa0201c02020e00078054c10000a306695129e13c6714c3929165e03c1760ed5b4ad2564a4149a614a0941292304648
  | _ => 0

def compactCount111 (k : Nat) : Nat := match k with
  | 9 => 1
  | 8 => 11
  | 7 => 34
  | 6 => 38
  | 5 => 7
  | _ => 0

def compactPath111 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => 0
  | 8 => readCompactBits compactWords111 (30 + 12*i) 12
  | 7 => let v := readCompactBits compactWords111 (1496 + 15*i) 15
    (readCompactBits compactWords111 (1400 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 6 => let v := readCompactBits compactWords111 (6373 + 17*i) 17
    (readCompactBits compactWords111 (5869 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 5 => let v := readCompactBits compactWords111 (10123 + 15*i) 15
    (readCompactBits compactWords111 (9871 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | _ => 0

def compactLive111 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => readCompactBits compactWords111 (0 + 6*i) 6
  | 8 => readCompactBits compactWords111 (162 + 7*i) 7
  | 7 => readCompactBits compactWords111 (2006 + 8*i) 8
  | 6 => readCompactBits compactWords111 (7019 + 9*i) 9
  | 5 => readCompactBits compactWords111 (10228 + 10*i) 10
  | _ => 0

def compactPoolIDs111 (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let v := readCompactBits compactWords111 (24 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords111 (6 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 8 => let v := readCompactBits compactWords111 (889 + 12*i) 12
    let n := v >>> 8
    let bits := readCompactBits compactWords111 (239 + 5*(v &&& 255)) (5*n)
    compactIDsFromBits bits 5 n
  | 7 => let v := readCompactBits compactWords111 (4161 + 13*i) 13
    let n := v >>> 9
    let bits := readCompactBits compactWords111 (2278 + 7*(v &&& 511)) (7*n)
    compactIDsFromBits bits 7 n
  | 6 => let v := readCompactBits compactWords111 (8025 + 11*i) 11
    let n := v >>> 7
    let bits := readCompactBits compactWords111 (7361 + 8*(v &&& 127)) (8*n)
    compactIDsFromBits bits 8 n
  | 5 => let v := readCompactBits compactWords111 (10301 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords111 (10298 + 3*(v &&& 1)) (3*n)
    compactIDsFromBits bits 3 n
  | _ => []

def compactBucket111 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let d := readCompactBits compactWords111 (1021 + 4*(i % 7)) 4
    let off := ((i/7 + d) % 27)
    let v := readCompactBits compactWords111 (1049 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 7 => let d := readCompactBits compactWords111 (4603 + 6*(i % 21)) 6
    let off := ((i/21 + d) % 76)
    let v := readCompactBits compactWords111 (4729 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 6 => let d := readCompactBits compactWords111 (8443 + 6*(i % 23)) 6
    let off := ((i/23 + d) % 86)
    let v := readCompactBits compactWords111 (8581 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 5 => let d := readCompactBits compactWords111 (10315 + 2*(i % 4)) 2
    let off := ((i/4 + d) % 16)
    let v := readCompactBits compactWords111 (10323 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
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
  | 0 => 0x6f7ffffff3d70bdbe5bef46fdfe7fcfff7ccd9eff9dc7f7133c06ec184e7d1eecc3f1ff7dfd4bfe8fafeb0fd32bb6e32213d630af59a5d85380fc6b03e3e35e98b26b279ae95f00c7444410d417c81c367cc90
  | 1 => 0x7b5bffb1feee70fe7898127fee7ff7bf3d8f2ef0f6f3a7e60f0f13c7eb80fa500081ffddfd3ecf2fcdf3e372fc44f4545ed83e6567a5e00e04e00101cce7e7bfef5e1d47230ac793619380320682eeda2c0324
  | 2 => ~~~(0x200c001180c1006d6ece7020082004181c0f08e0590c062309c543e6ce35d47e66b700148004664b08e2314437186fa273846e0567a5f887aeef49f1ea6632080c7a39d1b296a3387dd78633e7ff89166e6fbc : Bits)
  | 4 => 0x7eafff7f9c6bef3debc6698ff9ff1fff0bffdbe73f2f896f84738d7e46175c2e1181ffffa2d761df3dd0bfcffd832fa2af4142f50a65a5f44563003c47fe3a5e76f8b581d0fb90f896c000f25a83990cd85074
  | 5 => 0x77b7fddfed9ddce5f6479d1ffffbeff8fe7fb4f8cf3d569bc88ce3b61d78a4b02631f63ffe29fedf12ef5ffcc3785ba970a6bd9587c59a0b828c09c19be9dfce1c994af6d0142f7c69178601a5117837522b08
  | 6 => ~~~(0x2300d00000e4890e1969d50004300a023cc90e0a6310141860aafd705c2f8be9db816010010898c10d082f8d8e37e302c7933f587c5850d55ef87bdc4a805ce039c9667c019d4dc77d7c1ff5f90f8cb53db74 : Bits)
  | _ => 0

def samplesQ119 : Nat → Bits
  | 0 => 0x1082000804082420120108841800808408008110012080104c00810841100201300011044000a020023000c122c0006001c0010012002000c4000102002204200b200248200580080050010201088082210c10
  | 1 => 0x4a4210f04108a0107474d8684121010d8b291b511358010a0204820040c008b3b34b5c4d50205020081202086ca34e001cac92096d6e051200224480c636525ea120105010042804052a90a338ec6da240204
  | 2 => 0x200d0025804100444cc4602301004222952310c610082004004402048220442c02a6c68218a00804840888080413210420120c40855d4060024840211509818740050420484014020003300c9a106469109002
  | 4 => 0x1504480318010820038925860440c002044060862401ae00088100118408150c449083922114088280012021820c2019605121320000b820090888022941a5814409080808800508e8c025044211904c84060
  | 5 => 0x84810a09222010808a82261420900482501024a600828a4111104402081080440cb420b0a0012111040401448314104a2151640010902a20801120453888aca00880012101009042a851004cc103825520108
  | 6 => ~~~(0x7dcf7afddffbbfef5eed6ae77f5fdefebf2bfbdefdaaedbefdfddf6dfffdcfed72efd78f5bb3ffbfbef9faffeff7697eebf73fccdf7d76efeedbffef77ab8fef4bff97fff9dddfdefbf775afdf58fcef73df7e : Bits)
  | _ => 0

def compactPerms119 : Array (List Nat) := ([[], [98, 84]] : List (List Nat)).toArray

def compactDomains119 : Array (Sig × Nat) := ([(subcube 1 0, 7), (subcube 2 0, 7), (subcube 16 0, 7), (subcube 32 0, 7), (subcube 4 0, 6), (subcube 64 0, 6), (subcube 0 2, 6), (subcube 6 0, 5), (subcube 18 0, 5), (subcube 20 0, 5), (subcube 34 0, 5), (subcube 66 0, 5), (subcube 96 0, 5), (subcube 16 2, 5), (subcube 32 2, 5), (subcube 3 0, 4), (subcube 5 0, 4), (subcube 17 0, 4), (subcube 33 0, 4), (subcube 36 0, 4), (subcube 65 0, 4), (subcube 80 0, 4), (subcube 22 0, 4), (subcube 48 2, 4), (subcube 50 0, 4), (subcube 98 0, 4)] : List (Sig × Nat)).toArray

def compactWords119 : Nat → Nat
  | 0 => 0xfdff5fffdffffefeffdffefefefefefefefe7efeda61da615a603661b661b261b660b260b6603660326002618260826002603a22be60ea22ea62ea60ea602a32ae22aa22aa22ae62aa62aa322e61aa61ae602a606442e262e232626262602442a242a232a262a2621c429a429a329c229a229e629c629a629a321a221e621a621a621a219e611a615262d26252604c42ca42ca22ca62ca224a62144292429432923296229422922292229412921292029662946292629262923216221222122212121662126212621621922192019661926192619260c222c2220a228e610c228a2288228e220a220e218a218a018e610861622621c22c11401400a32222a22221a01a01200822bb1c2e677158a5ff81606e9285e83f038cea093581cf8bfe07cc3fe036b08cb163eaccbba44cd938c983ff81fe03c2bfe06040728b511fe07f81c0b8827527d20a0a0b955d397233118f9adf8c76b0ea388b476e69455a3b02ba110009104c0e136c5e8a71d8460833de6c9a28c460819b4e8e5293016013abb0a730403da74e21446081891f37a74ca3384c0e8b7a690a3b04c0eedba4ac0eb690628c860f629db402594600bb4d219607374731461374fb4808728ec2307bcd8090ce17db700159462393aee34060ddcd0f78607fffffffffffffffffffffffff7ffd845445045464c44444c434434234038224228024028014014018393f
  | 1 => 0xcd0008141820c040360e5dd833ae02cf0e043002e4c28300180906c682090a304956b44b040a24a830c040162618280025cb172214b9119448b52a1468068108850a441840c04034224429b1a504950a448b806740342e5c9910a103012200bb4227491b065c89202142182e446840025a05061808900d0890221048b0a0c1001c180896afda8909387106a04283043820012683040a302096810a05060830112002349ee8009684c9830b3c10602740096814810186c8052a40289201080568008340a1001008140340a703100c2c80028102830b4410602008342014a05204018228180b4365c8033ae84842075a10260c04f2011b3a260ce8068185053a0830100d08103a489833a401120c049856809d1c201083a04704806840011741048238141829e1809c0041a10384448220442836818089383c31b0e04e9c0004cb53ed0b1fa0700013259a353ad430f1e0428e06086800cd5a1e38d430f4cd0fb50074e063c7c7b43a71a803c3c32646d0f9f74003236838f1f3d40e002ed071f74003176834f1f740030d2ed11806a05d111a8cb9ca2d400f3e74e0e1a783343e007230cd0f5fdfdfffdfffffffffdfffdbdedfdf7fdefddfdedffffdfffddffff7dfffdfffffdffbdfdffffffbdfdffffffbffffdffffffbffdfffdffbdfffdfd7dffffffddffddffffffffffdfffffdffffff5fffffdffffdfffdffdfffdffd
  | 2 => 0x540a7deef7cdafc88f21f76b07a867fc01616ffc02cce0165ffc03fc03fc03fc03fc025487fc03fc009ddbd41e797ffc03fc028609b8973656769948f1093d64a3fc037b1b266cb05311ef140ffc0369709617e146be878406c03c86d93188914ffc03fc0025582c0500728d20104a4c4181cc0e4036e38c29b1401122031c02800040654c700301810100100403d0150400c81000480820458a56a8b8a0ce8059ed27739d166f49ae263497d25b595a24e6920a466901a3a98c5a2b789122078656148831e05380a5f977c9deb67959df2775dd657461c997009be26f1db566bdda83694da28668d972655d8e462958575f8d7b85cd96d75999608561154a529944c4e093624d1130949d921b4589142448d0f2435109441550053ed0f723d54f0939c8e53389cdb33618d263328c223020b852ce4aa5295c9e825a88c521e07f61e6470a198c63b162050911ec3c80d202c809201c904f007700278b021800c1254d030418080182428704003011850d050808e030c040161270a8236180871618d81081401a08141820c0401a2050d00193838918267070c1e786023048521444d0193c3b52f01b379cf43090e7100418301820c04037121e03713383860a0048602108373854989388098718109840adc19308710050665b82021a700324c98518e099b7258202385c296021801726249971c6c11c0a08086344c610244
  | 3 => 0x1608931600931511131510d31500d31500931200931110d31100d31100930d00930a11530500930311130310d30111130011519510d19500d19310d19111119100d19100911711111600911519111511111500d11500911500511200911100d11100911100510d00d10d00910d00501500900d00900d0043090041150044a0da6a8540bfc002ee7fc03fc03fc03fc015f2ffc02c1354060875360e6e6887da3fc0015e6ae97330e7551662251e9ca538182cf59801bc87819e3fc03fc026f3ddcf7a337e5ff3a661e3ffc033c8bfc00a2dfb6189d96caece5079a24c637fc00fc37fc03fc03d0a7e499dc715d12255cb36d8a621083674702389a2ddebdcf150ab6d675c68e15b5a4b7282e349c84b950fffc0329605447787e46cd364f251c66d7fc03a9bcc1d1085c919b0f4fd6e9b9c5fd8e8417fc029db0f001b811d25bc57909183233e280adf3894b84c4966bfc015ea7fc02c0aab9204b664da736b33757fc02774bfc03fc03fc03fc03fc00b9562e1dc9435ac625faa44b62b8bc295c32e12b04f841683603c763fc0351aba977fc03fc03fc0376a0f59d664865d458917ad1de915103884ee2ff00ed59bb7ee3c0da871f4cdd49925cd609ccd86c8d84d07718c3d5dda7739d0fb64720cb02115f243a28aead0207792d2b7508bd88cec8ad04b151674cd2a525842695158679c29e013a7ec14931935eec213dcb7
  | 4 => 0x88af9395f2323e4e3359cad539956722ace02d10a59314da32334e3669cc63381367226ce34d9c0891951672a24e5459c0c938d927317ce42f9c4bd1957a71af4e61c8ca3b39a4a72494e26e9c6dd381ba7325ce22910a53314a2728a4648e8cb1d3963a7121444439c41f3143a72874e4848cb0a1161272c2444849c8a7381a271344e6239c8a33905a428b4c5169ca8d2151a22a34e5629c4c53818a73304e2609c2c138182733c4e45c9c4361946a328dce41b9c6373816271ac4e2589c0b13982422844450888b220964212c84e4909c6d9389b270364e6499c09338d267013ce17680aed315da72894851280a273144a6289ce5129ca251904e71c64458c80b193963271a0ce5401ca812150622a0445419ca833950672a00e5408c88338dca02b94e5728c8e53903232864050c9ca193901a3283445079ca0d3941a3203444068870d3961a32434e43e8ca7f394fa729fce43e9c87738c6670414e55a9c6b538866718cce0199c00138c0270008e67488ae9395d47308c451088a23395c272854650a9ca09194142282445051ca093941221824e2829ca0539731511331500f31500b31100f31100b30d11730d11330d00b30900f30900730519330111730111311511311500b11100b11100710d00b10d00631500e31500a21710e21600a21510e21500e21500a19500a11500e11500a11500609500931711131710d3
  | 5 => 0x1f83f07e4f89ea3bc6a0d5199322620c41883165c0b89682d05a4b09592a252c9a90c1d03a4720c01822e05c8b1152290408790e418c2682202004800093dd1c40c041819ac4c7008180400e60c4c720c0c0c18040c1401a41418040018045c00105e700000148000105c080c5c01b05c145c0c5da410005c000c1804140014001400001000140414101401a014100004000000004e140e700000d93c000c1414141671b4080000001009a8442689a00810013c0c141414180404000000049a748e7498048c7c988e767000e88e167074007c0044005c347044d4e844508c5c4434008c408c2c027f3f9fcff79779fef67b7b9feeef7dbf5def3f3f9fdbfcfeb9fcff773fd7cfebf3f9fcffcfb7dbdde7f779fede7fb79fcfe7f779fddeefd7bbcffaf3f9fcfeef7e9fdefcfb7bbf9f6f3f9febe7fb7bbddf6fbb9feee7f3fbdcfef73ff5eeef7afddcfef77e9fdeefb7e9fdeef7dbeddeef7fabbdeefd3fef77bb59fcfcfe7f7bbf4fefd3fdf5f7f5bbbdfaff5bbdddeef7ebbdeef7d3f9fd7ebfafddeee7f9f8fe7f5f3ffd5efe77bf9feaf77bfb7eafd7efb7ebe53fdbcff6f3f9fcfe7f77bf4fefb7dbeff2f975be4f7f37d9efe7f37dbefd6fbf4fe7f3f9fcfa7f2fb7d3d9c1153922a703f4e3329c24338c867340445809c04b3815e701c4457a9c03d1947e720fce0948cb2938e527027ce42a8ca551162272c44e07c
  | 6 => 0x57f803fc01a16e057288d0ffc016e2fff003325bfc016b453319a91415623760929292bce300175f024235c4872d88a31107e71e59550626f50af17d7f8028801ccfeff00095f7fc01c02d55c4ff803fc01fe00f49d7f803fc000942ff001d2c1f402e47a735a9cc829a7cdd1c92bb41d4bddc4a756ddbcd845f21f1fe00ff00770e0066ec2d5fa4312de3fc01fe0013c47f8015589fe004c4ca4c27fc01fe004e7b544901018e0158e4c1a46bfc001c76ff0066333003a53810d393f3002931408080002c3140201294842030208987150628625020020504654090210082020ce00006080101101011e24182060000b020c2001c00402160058c000009e001810d00140850000011000cb000404200140878900001060e1c103000800b28140000e08002282898000387101566a8550aa74e699520a434628c518a3146e80500a033ea744e99c732e58ca89512a2544aa9312624c498931266484919112224448990120a384738b512a1cc3185308210c188310620c41883304dfcbf07e4f85ed3ca774ea1d4ba3710e21c4b826e0dc1b83716d4d61ac3586b0d61ac3586b0d65a83506a2d25a0341670ce598331652c8190320640c858c319622c2580afb5c8b0160ab8570ae558aa8552a8150a98530a614c298532a4544a824e29a92ca504a094128a4849092520a394608c514a204448410821042084504208412804fc
  | 7 => 0x18a14eb23ed1f2905e1c088e127fc01fe00324e9e1d036e7e02137c2a70aeb8b7ba836a0f02bf4d1c3fe004b208483e32d0f37ba197c0b91dd925aedd33d8a8c441c1811fff003926ffc01d405a4612e2a7fc0053471a5e5aa6a08889c47b28b390f088147ead2b0d83438a6c0a0daff00305513d8ffe00ff000b0d405f7fe00ff0019bc1487b1cd4a26ddb843fc012058f6307f801788dfe007a259accada51fe002d2eff801092aea518d490a067fc009665b240c256ab9944b4949b26b2ff118c72f13c3eff8012db9084d9c5ec29bd40c76b84e979083fdec6f5077b16fc7bb3c5453cc5725451d57c0254e3bff004425ede0b5923ff0049ae3a1417c53ff0054b2f82892eefff000ac1ffc00d67ea8422bb7bfc0070e710a69bb65d6eb704c818c8b102b1631cceb5690f33e215f30ea02a31f1b59a29fe00b36871dc6dad29c0660aeff80168860493ae891b837fc01cf15ed38491e62c111c5a69800baee7673fe0013b3f35d390c528eb920122addd1d3d0fc5398cc83bb512a4183d92ff80342a6d765c15d7295c78cd90acf648518978504e8f7d337678f87147131da846e40808a45996b5324724139c949cf48f39df17288e3bab60fa5e929f026a24e828a7c8a9945cc8366e887c4a2c8da3209fca5f061a89110006c602b1a4f7deb09f0dd5a713ddf6075a6d3088c321f3ad188242c2819f2cffc0028750b9
  | 8 => 0x95e57943f1dc3f3e4f97c4f97c4f93e5e9ea5e9ea4f97a5f17a128caf28329a00ce81388caea8036a043e81b080a0a22ac80a0232a480a3232a088a2232079ca1a7286a0a1a821da0a9e811ba0a668040a0656802fa0046802ba008e8017a04d232b4a062a328ba0efa819fa041282e70222a00c72a01a00c42a32621c32a22a01422e61201c22a02a01422a01a00a73442a01a72e22201272e22200a72e21a01272e21a00a72a62221a72a61a01272a21a01272a21a00a72a01a01272a01a00a72661a01272261a01271422a00a32a01a00a22e22200a22a32222222a22200a22a02a01222a01a01222a01a00a22201a01221a01a01221a01a00a02e62201202a21a013e4323e800003c714290c92168dad84895ee5ff2c09fe00afa4409fffc0110b9ff007c5b39ac7c8f300c3c9bbbfc01fe00ff007f803fc018627ff004e08d5a5dbc22ff004842d9d1c9e914f61f89e2ab07e8699d2a3fda9d6998f6f2d43d48d039285d08ff001cccd56a3fe007860d6603fc00dcaa8130f22846c27fe009433da5cbfc01fe00919e7f8031a3c795eff000705acc3eaf8bf89dec377ce7fc407b70d54c6d3d5caf2ddbc317aacfe0274c811adc8c854ab200d69b7ad5053907fc736ccb0e757de6b853278b960497d5daf424e7e94a4203014b4e6448935905f959bbf306db6e293c35380106b61cd19642c5c7f579f42da22874d07d4
  | 9 => 0x68e7295ff8028515a68805d930ff00a079751d68cff010a83fc07f804015fe01b0965c59b4e66f3fc04029c28e3e5eaa4ab22f955e2e8200ccb54e3a78c5d86ff80f029fe017411bb6ff01fe000876f007c4c4b0e842ff80323f8d10fa5d209ff00eb07fc0092c0b81b6dcac269a1880e3cca24b77914467a4d1f926f030727bef4c03171b3f1f48bb7616d2d1c31aa664129c38ff018ebc79dff80ff007cfc6443215eb20039d2301d40845c62b8b15844310011020408102040810204084c183240810222040810204081020408102040810204854da6130e000d4000078753c7d1df276d5b56d6b5cd6b5e96b5e96b5f16e5b
  | _ => 0

def compactCount119 (k : Nat) : Nat := match k with
  | 9 => 1
  | 8 => 17
  | 7 => 111
  | 6 => 198
  | 5 => 38
  | _ => 0

def compactPath119 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => 0
  | 8 => readCompactBits compactWords119 (20 + 12*i) 12
  | 7 => let v := readCompactBits compactWords119 (2159 + 16*i) 16
    (readCompactBits compactWords119 (1991 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 6 => let v := readCompactBits compactWords119 (17182 + 19*i) 19
    (readCompactBits compactWords119 (15382 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 5 => let v := readCompactBits compactWords119 (35975 + 18*i) 18
    (readCompactBits compactWords119 (34787 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | _ => 0

def compactLive119 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => readCompactBits compactWords119 (0 + 6*i) 6
  | 8 => readCompactBits compactWords119 (224 + 7*i) 7
  | 7 => readCompactBits compactWords119 (3935 + 8*i) 8
  | 6 => readCompactBits compactWords119 (20944 + 9*i) 9
  | 5 => readCompactBits compactWords119 (36659 + 10*i) 10
  | _ => 0

def compactPoolIDs119 (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let v := readCompactBits compactWords119 (14 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords119 (6 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 8 => let v := readCompactBits compactWords119 (1253 + 12*i) 12
    let n := v >>> 8
    let bits := readCompactBits compactWords119 (343 + 5*(v &&& 255)) (5*n)
    compactIDsFromBits bits 5 n
  | 7 => let v := readCompactBits compactWords119 (9506 + 14*i) 14
    let n := v >>> 10
    let bits := readCompactBits compactWords119 (4823 + 7*(v &&& 1023)) (7*n)
    compactIDsFromBits bits 7 n
  | 6 => let v := readCompactBits compactWords119 (24094 + 11*i) 11
    let n := v >>> 8
    let bits := readCompactBits compactWords119 (22726 + 8*(v &&& 255)) (8*n)
    compactIDsFromBits bits 8 n
  | 5 => let v := readCompactBits compactWords119 (37111 + 7*i) 7
    let n := v >>> 4
    let bits := readCompactBits compactWords119 (37039 + 9*(v &&& 15)) (9*n)
    compactIDsFromBits bits 9 n
  | _ => []

def compactBucket119 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let d := readCompactBits compactWords119 (1457 + 3*(i % 10)) 3
    let off := ((i/10 + d) % 36)
    let v := readCompactBits compactWords119 (1487 + 14*off) 14
    if v >>> 6 == (i/104729)%251 then [v &&& 63] else []
  | 7 => let d := readCompactBits compactWords119 (11060 + 6*(i % 67)) 6
    let off := ((i/67 + d) % 245)
    let v := readCompactBits compactWords119 (11462 + 16*off) 16
    if v >>> 8 == (i/104729)%251 then [v &&& 255] else []
  | 6 => let d := readCompactBits compactWords119 (26272 + 7*(i % 126)) 7
    let off := ((i/126 + d) % 449)
    let v := readCompactBits compactWords119 (27154 + 17*off) 17
    if v >>> 9 == (i/104729)%251 then [v &&& 511] else []
  | 5 => let d := readCompactBits compactWords119 (37377 + 5*(i % 24)) 5
    let off := ((i/24 + d) % 88)
    let v := readCompactBits compactWords119 (37497 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
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
  | 0 => 0xc1f2283873ca6006965c501c3f705cbb0d61b0e00c1de3d7e5cdfe738ff8afdd57a3e5e51d3ffce06afecb8cad782c633f972f482871b42fa150686e2b00a0a362b46e01a879d6c80ab41aef40580e80b618862c035bca2de18c795b1fd967147145ae429e6854d1a19d0608c96b01100c080ca847aa209022da2763d92220
  | 1 => 0x403ec2c3444c0e731f21ea01f183ab94044002440311c0be5bfba7cfd7f3eefcfa7f4a3f51f1878d27d39733f61bd14fb5f2c1fe71478644b54480de80ddbc074d4807f4e8175c1e92701bad0002e1810e086020403c8795ea73e7e0753cf675c7d61983a8e1ca83a0d4d03d1166701c41e000e101b04158ccec99842d209844
  | 2 => 0xeac38d86889f9186247e802e58d08ad9500805098860135f3d7ebcf7fce7bf4f73b7f3ce9f623cc79c92eb7c47a39fd2783b7ac0a228cbdb5040dd09dd80ea18074f4a07dc2867611ce1a4113a7d8214204016068342b8bd74bcc3afc68f6ea6e9da2170cc1393342e4917e18c0f8080a405ce0e0e04100b0f0dce9194520103
  | 3 => 0x772c0138f308e1a3c0470cffa104132278b21a00050061c3ee9f7f16fefb3fff9fe97c70e67bd819d8fd529c7b5419fcbec3bd3303d70c13c1873f960e0f0fda789070380ec3848160ff40e1438700c01109e1190084ed1e733efc2b9ff189db19a3a6040f6403eb428e61c63e7110660a120130001845cb71b1723a0620c488
  | 4 => 0x870e1c173783345c7910535c22396c20c20160110a5080ffffe5fbf96f7cd7d93ea9dd951a9ec0e2ff757d2b0f5566335fcc56ecb43001a82e594e746124f0bcdc82c851f1558128b70b4b646cb85311260600800f08adeb9fc57855bce23799fa4d7a2ab10074695d51e401c7b08a89042806c126a03015f25220f8d80a0164
  | 5 => 0xb83122fc87b00e0c98c9b5a1ce42d42b07f08066308f21bdbcfe562fabfcf1f2e5feb43aa9ee677227ac08c7f9feae8fc9fd29d18e87f8049aba20a110f24347b2b5078b1616a21e6d841bd29002bc60c930017870307661db8a179e6adf178827a89e5154f9b502012a2a3ae198641259d03010d14882862f50054750855c10
  | 6 => 0x1dd07d4148647199e3a8238207ec05c7ac069c8a54a20f7ce31bfbf99d1f4f37efde8fcb7e85fb3f5b0fa5f4b0eae7f18604ee185dd8366b403ea303b3501561003db98023e81ae10314e40e95fd242a50c18e4190c15276845f3bd6a160e87efe04c0dd330e0c9cbe360ad872068560a203f10250030c34008f2548ab04229b
  | _ => 0

def samplesQ127 : Nat → Bits
  | 0 => 0x81200100088240021410002430000824082044b00d0008016808d0011880828414120200505000400085040840400006300020848208c008020d16200040021a4104016018004482800100540c20031000801014040490029018c004310484104504400428208004021800008c01101480a080108404a009020d00622412020
  | 1 => 0x84800800a0220108000410880060102820b33403980c0894125384c411434628d01a0a0010500281020002022202400800a080801a259502740c9020080d00716c458102408024da0420cd0c402a08080105040412000294a82346c04108c435c54210802041408020805011000040014341480914e0497088ac898425201004
  | 2 => 0x1008106002004800520002410401050003255814120acd1b207c00968066244612944108800214001402010840810500000a2000921e218b20150080cca80518410c01a88201e2145440aa58013000004420481008a010b840b8432a048d06a28980214080101210080804a0000500060191810e4684910a0d090e9114120002
  | 3 => 0x102040c4010100090c10000804011850c807c40d38302ac842910c89838c50b4110504200801080c40010080010a090010102c098082880e141c242804c048018483427034301f910105103c01700808000a08002c9085314a823165109c2182002040900014202040104242011040c3a0122080c36095111723202008480
  | 4 => 0x20202180400480208408240008060244004883a065213260c90072296e1091912c2084040888004060102400011020120400502720c0406402c0260413107a8600a21a40340e0901811700209e013040184010402005a44316443015b8623108320500221000202110402000830086a8342012702109240562522068c8080140
  | 5 => 0x41404401100100c1002208043008080008004a8006205429002812032224800204a480002020610201200805100088040854004120026085001002008520138a012202c880008004004522201410208200028202010834610088110c2886120000880800042884000102020a0018248a10808014630080022640044150804810
  | 6 => 0x204800a01100206080000308010a00010502100a90420444103406804014310a00a008300000828080180a00068024100000c1400411040560824041011204008c19000500c088200224500880900042210200804100206844200d08020a01c620080190004000c841008405002022022405240102100740086010889040209
  | _ => 0

def compactPerms127 : Array (List Nat) := ([[], [65, 50, 80]] : List (List Nat)).toArray

def compactDomains127 : Array (Sig × Nat) := ([(subcube 1 0, 10), (subcube 2 0, 10), (subcube 4 0, 10), (subcube 8 0, 10), (subcube 16 0, 10), (subcube 32 0, 10), (subcube 64 0, 9), (subcube 0 2, 7), (subcube 0 4, 7), (subcube 0 8, 7), (subcube 0 16, 7), (subcube 3 0, 7), (subcube 5 0, 7), (subcube 6 0, 7), (subcube 9 0, 7), (subcube 10 0, 7), (subcube 17 0, 7), (subcube 18 0, 7), (subcube 20 0, 7), (subcube 24 0, 7), (subcube 33 0, 7), (subcube 34 0, 7), (subcube 36 0, 7), (subcube 40 0, 7), (subcube 48 0, 7), (subcube 65 0, 7), (subcube 66 0, 7), (subcube 80 0, 7), (subcube 96 0, 7), (subcube 12 0, 6), (subcube 68 0, 6), (subcube 72 0, 6), (subcube 1 4, 6), (subcube 1 16, 6), (subcube 2 8, 6), (subcube 2 16, 6), (subcube 4 16, 6), (subcube 8 2, 6), (subcube 16 2, 6), (subcube 16 4, 6), (subcube 32 2, 6), (subcube 32 8, 6), (subcube 64 4, 6), (subcube 64 8, 6), (subcube 14 0, 5), (subcube 19 0, 5), (subcube 21 0, 5), (subcube 22 0, 5), (subcube 26 0, 5), (subcube 28 0, 5), (subcube 42 0, 5), (subcube 50 0, 5), (subcube 69 0, 5), (subcube 74 0, 5), (subcube 84 0, 5), (subcube 104 0, 5), (subcube 3 16, 5), (subcube 5 16, 5), (subcube 6 16, 5), (subcube 17 4, 5), (subcube 24 2, 5), (subcube 34 8, 5), (subcube 40 2, 5), (subcube 48 2, 5), (subcube 65 4, 5), (subcube 66 8, 5), (subcube 80 4, 5), (subcube 96 8, 5), (subcube 11 0, 4), (subcube 13 0, 4), (subcube 25 0, 4), (subcube 35 0, 4), (subcube 37 0, 4), (subcube 38 0, 4), (subcube 41 0, 4), (subcube 44 0, 4), (subcube 49 0, 4), (subcube 73 0, 4), (subcube 82 0, 4), (subcube 88 0, 4), (subcube 97 0, 4), (subcube 100 0, 4), (subcube 7 16, 4), (subcube 23 0, 4), (subcube 30 0, 4), (subcube 56 2, 4), (subcube 58 0, 4), (subcube 81 4, 4), (subcube 85 0, 4), (subcube 98 8, 4), (subcube 106 0, 4)] : List (Sig × Nat)).toArray

def word127_0 : Nat → Nat
  | 0 => 0x33253344332433433323332133403320336733473327332733222b202b672b272b272b2323222321232023672327232723221b201b671b271b271b67032700c530a530c430a430c330a330a230c130a130a030e730c730a730a730a328a228a128e728a728a728a320a220a120a020e720a720a720a118e718a718a718e708a708453025304430243043302330423022302130673047302730273024282328222821282028672827282728232022202120202067202720272022182018671827182718211067102710271423413403223221a13212211a11203202a02201a01200afc7fc1d4d0aedeae5afbba76e7b9e909fe066c3dd9acbb02ff07f83fc0199d70e0ccb19fe0ff0048cb53fe02daff83ca8be6aadefbc2d00526107f808100803872a72772476131e35af17f14f11ecf30c30930630330002840604060bf7ae5b04182840604060bf7ae5b0c082830410060bf7aedb02182840608006c17ef5db604d05080c101c17ef5db800305080c101c17ef5db8003190c10182037ef5db800a050c141820182f5d036c2110c141820382f5db8008040c142010182fdcb6081860a10100c17ee81b60c7860a10101c17eedc00381860a10180c17ef01b6086860a10181c17ef5c00301060a10182c17ef0bba000ffffffffffffffffffffffffffffffc23223413213403203202a12202221a11a01a11201200e163447f
  | 1 => 0xbffffef7fffdfffffffffffffffffff7ffffbffffff7ffdffeffffbfffff7fdffdffff7ffdffeffffbfdffffffffffffffffffefffffff5ffffffbfffff7ffbfffefffffdffffd7fffdffff7fffdfefffffffffffffffffffffffedffffffbfffffffffeffaffffbfffffffdff5ffff7fffffaffffbfff6ffffbff272f2727271f270f2705a335e72de72da72de725e725a725e71de71da71de70de70da70de705e705a706a336a72ea726a726a71ea716a704c434a434a434c334a334a334a234e72ca72ce724a724e71ca71ce714a714e704a70624362236272e2726271e2716270ac532a532a532c432a432a432a332c232a232a232a132e72aa72ae722a722e71aa71ae712a712e70aa70a42322232413221322032673247322732273267122712670a270c42342234403420346734473427342734202c6714271467042701c531a531a431c331a331c231a231c131a131e731c731a731a731a129e729a729e719a719e711a711e709a70d22354135213540352035673567354735273527350735202d21252025670d670d270d670567052703c533a533c433a433c233a233a133c033a033e733c733a733a733a12ba02be72ba72ba223a023e723a723e713a713e703a701453125314431243123314231223141312131203167314731273127312229212920296729272922212121672127212219671127116709270b45
  | 2 => 0x45628b6899800e140a979705d03824ab132904c163c5b0884a383730578555d901725e8b01c111429adc240b100e16c2636b047c5e0045a28048982c22075b17caa018b01228268988c16105b97c0c550280c02028b01229135b82cbe0b02148ba2812c4c20111697c0e3e1402c4ab7120b40c050180a2d145b44cbe0708044b3165e18576605d0e0be070414858228a8756e0b2f1756c2560964aa4100c5a2a0312c4c440b072dcbc430301408011580a2c038a8e226b70597882613017c065d8b4545026898381e0b2f01c863f140980cb702810160215c5a2ab68981cbc0e079487e012f100003e010f2280b0681d6c5d030140803008aa2c028a8e228b72e82ca4613000a2c5f2f454502612c50180d0397416421f8f8503c13094160602adc06041545a2ab68a1740e0c06dfeff7fbfdffffffbffffff7fffffeffffffdffffffbffff7f7fbfdbeff7fbfeffffbfdffff7fffbfffeffffbfffeffffbffff7fbfbfdfeff7fbfeffffbfdffff7fffdffff7fffbfffeffffbfffeffffbffffffffffffffd7fffffeff7fffdfffffffffffff7fffffeffffbfffefffffffffdffffffffffffffdffffffbfffeffffbfffeffffbfffff7fffffffffffbffffff7ffffffffffffdffffffbffffffffffffffffffefffff7fffffefffdffdffffffffdffff7fffdffffffffffffff7fffffffffff5ffffffbfffffffebffffffff
  | 3 => 0x87a050200802418b00e2a39892e0bc0c30980be0e2e00e2d15154484e0c5b1781043211047a29138180a5e02030022a8b455700e1144810b61c8187e3e028f00803008d22c028ac50b8b80617cbc0b00c58551429034185c04454be382f1740aba15ae454b803c50820b301022606142dd6cc130ae8705f5c979705d30c540f14899816e1c2c82d6c283bb0576605c8acbc078a10416065bad982523095576605c97a2cb82e97e28070544d6e1b0594842385b098ecc18b154c05f1c1762abb5d00c54b80382c8006899784ab75b304c2592aaecc0ba1c17d705d8b17a2a61038243eb78982c6a225b09583163017c705e5dae856b90101e2a5205c5082065b9756cc130aecc0ba1c17d725e8b1840e088a9743c528a02d6eb61a081823f1f0f1745e0345a2a008a44c34610581d6c050200c000230c5803151c452260b5b2dcbe5d030a2262603894c20b3017cbc068b1762a288a0984b1330864340b038fc7c281e0984a050200c040b8b45628075b44d6e190d2e0ba521081c15132a86016b6118e07e2639b0482bc30ae8be382f2e0bb155b81c13132a85c16b6110947c726090178615d0e0beb92f148aa0704456285d302dc2c0b102d85071608f0bc008ac500b13058540eb630154031502c50500b898516e600301006010145470058a44d6e6005984be5e029762b141309626140a82cc0075b82c782612818080301
  | 4 => 0x11521450c00c030d224b8152d98461212e8725f21ae4bcb72e0222b145c448380c302d8547761458c0b92f1722808150300cb85b308a4618b4516e5c04028a5120d8316c24210e4547661458c05f1c9716e088a90818061a448bcb8152d984612100d76605d0e4beb72e02013165c4543e0c891796cc21510818068b00a2a008a448c2081a2da2c345d981743915978beb9008222b14210300c2a5c2d8b8c230aecc0ba1c97c82b92f45810075c454a51406068b8b6151d584068b00a285715064191230ae00a040180002618b00a2a398a4496c0c5c180bc5c0345a29120409cc20c0c9700c0c8b452242730ad86808212e018050200c32018b4562912040d16cbc30ae8725f1f2dcb80804c542f120617970605b1c984425d0aa2a008a016240c0b0216c605e18574392f8f5725e0401e2a528a054185c5c1816c70610180803010d003151c81629125c18018612f97828052e456282a13c482c0c3002084b81381808030a004182a8a98229125b0202c425e18576608b17d6e5c04024bcb88903026525b09c726e610a801168a012240c090216c5f5e2ec84b92f45810075c450220c29ad84e393630884028b45008271203021125c17c0c050180802348b01229125c030be0c08010b9168a0a8a512090b8be082f8180a0c01840022a8b0ba2823892d810125e18576605d0e4bf160401e2a5207830b8b82f2d8d4c22181
  | 5 => 0x22f30c80612c95576605d0e8beb62dc58af1503824bcb80f8356f111a889862a1f8f878ba2b81a2d15014503511308340eb88b105766015979720003c501a065b90854b82db0cc3165d981745f1d2e4bd155c450ae195b834e8c3200140803001022d151d452220d0697c0c2813094400730980be5e0d01a2c5b144541b141289a22611001c84401f8f8503c1d8984a050200c000d8b45571140d2dc411103908aa3b5d00481158a0141a16888216e605e100c2ba1d17d725e5b81e2b1430148280d2dae0506f618180803004547514304441a2a3097cbc150b014b71506c504c2588880c00721100783b132e04a060200c2a00068a8c1158a2dc41110b01d6c5b03824aa528884c1a3c129b9863a2a80481168a0101a12888216e5f1f008af168a0101a118881d705f5c9796e558a01c145708034743b5c16c482635b0c0c550280c00578b450bf11068a8c2602f04424048b16c51140689622202f81c803e140940c0501844000d15458bf145b88222120396484402a8f4762701080022a8b00e2a0d888216e5e2cc5978615d981743a2fadc0e0929454440e06978b6b8129a5864303014082b0045a2a3a889781a2a30980be0f01c58b6288a8981b11101780e43211007eb8140ec4c0602810002a8b454bc0d07adc4111038180a04019022d151d450b60d15184c05e0583001162fc545114130941a5b0397c725e2e2dc1
  | 6 => 0x7018865d5cad988413095c04bb302e8beb72e458b31504820ba1e5c83a2434102d9882b5d174be2a5c00413152044c1c06218ad72b62e310c2ba2f971705d5cc54c20903c4c340e2cad85625209d58859034580715898ac320e30c49720502008000101c5a2a5989c481cb65c97cba068a9022629111841cb93017c325d2e01857168ac4c531211038c2b60490c823d148140802110041d168aae43313890256c575e185745f5b970b20904454bb120b038c0295cad84071622e8be5c5c1762ab9898240e152c838523d5b1804a706216406438a81626290705224b930018080201804b31502c4e24b930038c25f0a1740a5c8a8ae26228905c1c6004af0c2bb302dcb8402ec581208890481cb92fad8406d62164b8415e18576605c1762cb90481e2611070896c5f129b18806028e8040400c5807138917c1cb930980205d021722c2b14c4c451209838be092195c823d148ec445c018005716014541d1204ad8ba42030140802008aa2c038ac48ba0e5c984c05f0617005168a8ac5312110396c5d049640c3f02810040120c58071589971720e30980be0b2e8062d15898ac520f07170120515ae4bc075c450c00d032dc84c320185743a2fae4bcb62d95e2a075c450391106964c0b7151dd8716208e97660020ad725e03ae2280d0317d6ec3201856e558a2d8b6070514a221b069085476618ea2cbb3000d6e075c0340c4
  | 7 => 0x1456612f9756c5b8ac4e221c07968eec521974b6b60397e260f0310ca5111ab145661219496ebb30109705d5b16e2c5f30c4c0e0a8886c1eb911898ecc52f96d6c078a83c0c43889746ac51598486bb302e8beb62dae40e088b4543c0f889756ec51590c7eba0345a2a038986a22610781d72ba2f97454b80001e2a3507ade2606218ad725b6298486bb302e8be405c1762cb903c5626190796d6e2b3a3148656029500802001862d1589c441e5f2e96c0d13144444c0f0398434060796e262813444c2350390c7e0f0281034025b8022d155cc4e22071a90c0715898141e158881d72605e185745f5c17486b703c56261407980b6b9141bd8a062a010040021c5626608883c1e150b814b62b8989a22323001d78615d9816c5b8b01c10128883c4626369518abc30add76601dae0bb162f81c15130803c465b5c898d6c52d0180a02000d62c5f898e6220f0784426042d8aca428888c0be072d1080c56028ec08002045a2b112e83c1a0f010acb62813444585d039680c560295008021ac5a2b132d83cc2602f974000b070ae2d151444c4c0f2d81c0aba2f8a9705d04c548113300380cb95b31082618aae8beb82ec4d721c072d8b2776210c082a5c174b809898380c432fae56cc420984a5165d98084b82eadcb8592bc4c120a2fae4360e890856c2b3b31086411e8a4445c0300e2c008a83a2712308256cba2f80a2a090
  | _ => 0

def word127_1 : Nat → Nat
  | 0 => 0x46b630098e0c60300c04052b8062804898ee2460082e8ae610a178ba052e45226101208e24183002886061e8140403009062c04898ee245e082e8ae6130038ba038b172262411c4820132f0280c0501808022a8b01229122e841740c2f008b9162bc505c2389048205d050187c050180800578b012283b899716c105d02cbc012b974ab141689226110517020422016476431388082060100e2d1589444c2085c97c040101821704303109725c200a8c2575d17c04b95b16e2a080387571110d16454253a90570b901808000821818845b208a8c3162caecc0035b97171120e864aeb93a10004b90310e2c032dc548440889843a2a2a0080a040080170592bc580715892e6221d1501852271008810613017cb8068b16c54298a89e24208898444082190882401e8a47627028100220000aa2d155cae224228882170605c97cb85b03008064321100822a3095cb23b5e185745f5b97010408a87428b9890f5705b30080de595e18576605b16caf160401c3a1188894d8545d98006025b9722cb804028be1d89040aeb92d8ec40243580c02412d900763d88874b8222c8fc06060281000418b0062a5c5cc45700711184c05f0096c1b16154541e2913882225c04008005c1e900771204074b6202b95006065c01408012045801155cc48401d2d984c05f06038b8008b0a62a2a13c48445b0417cba5b5b01e2b1307818c1111ab
  | 1 => 0xba2ec456e2463984ae3b5d98174b92f2d8b7161b1740e088a078226188adc4ec712180bc5d5d8ad722a5c0000e418a0456e218981884ba2db1cc2bb302e4bcb82ec5a28ba3081e26190895cb6b7109d18e5602950065301000c3168a44e2211088185025120840e6130178ba068b068365b088a228258989222611081c7c28128e448055d0680602000462d1489adc43110386d78615c979705d5b81e29130a044c05b5d0a0dec7031580a03001022d1488974222f309801a5e0900a2c5b144504a1188884ba07031580a540180a2d148996c222d30980165e2e8400116144504b1312044b60702ae4565e2e2dc15140801a24605d2d98c573090d725e5c0ecbab72e02a29130e44820602bae96c77632de2c062bc50003a8906cc210052da2cbb3000cb8b7050400d122f2e96cc62b98576605c0ecbab72e02813160f84227122f2e8aeb6632ecc0b915978045c8b2dc1514084480cba120ed6cc63081976b98b2dcb9145d028101e890416c581d88048c68b154ae6020178ba3b8a2ec56b9152e0020a2144c4610032e96c5c63184ab165d980b8415c979703b2ec5174610501caf130d0416c23131d58c0501808000130c580914898ee24105b2ea2c602f1700d141208cc2108b064bc0608174b9148988c49123086cae0a1d090461002ae8320300c5805148995e24b60506d78615d1707ab92f2e0765d8a0280f130a840
  | 2 => 0x215c42198906d6c5f2caed74b88b180be5d5b9722b13000ac06408907c32b62f45a2b142ec4818190301976b90cadcb9160045068022bc483cb62017432060045804578a08224345b1762cbb302e8beb92f2e0bb158a00226410090032b60d17000040180a2a018a0162640892d8c01902850be5e2e9722b1489902241c28064c0000280c051600c500913204496c5f0c840c0192f174085c8b452241b1097cae001e81408028b0062a038990224b62f064b20307180be5d209722c4d8ac4c56405e4496c192f0000a04018062c028ac5224b60c97418192e00a2d14890d0ae5d200007e3e028f008030145a2a018a10226b62e064020b3017cbc5d8b456291320068b8192f978b9155d0ad72025bc50861403449765d5b328c257012e8beb92f2dcb91530822285d8907828bb5b0d040ca8a978baba2f8ad722a5c00628438990028065dad8b8ca30ae8be415c979705d3081e2b1489964345c0a2ed6c283ab280c058ac5226198918428bb0200c0400009840b158a44e24145b2ecbe2b2f0a8ba5c0345487142044e24610a2d976060c97cbc5d2e45629138918438500a01006020085032bb8ac5227125b07084060200c0401154540b148917428bb2b8a804610617cbc5c2045628488905840142e818780401808031502c52265c5d850aa013082cbe5e2ec5628471444c2a5c0a458c05e2daec56b9012d80f14208440c
  | 3 => 0x45a291388adc36012a81408020045a2a03899796f11030244a011d8140803100022d150107a2911032dcba08028100716010062b142044d6e190301003162fc5083132901834bb302e4bcb82ec596c5b8a104031321012221a5b86cbe558b006280429098461a0dc456e5f2ac5a2b132f4441e1a0301974b80d2d8b6018ac4c6a032cc456e5e2095434068b0062b130189445111aadcbcbb2bae973163017cbcb62dc562801011043d11150696e5d0200c04008a982284189c4434150d17838052dc4c4d11301640e05018e405160045083138897c341130178a45d0d8122c5b8a0a2262588868be072a81408020045a2b132f444340f0d00cb7131409a22352f01c0a3b0200e2c008ac50825d888681b163017cbc022dc5450268a096221a2e81c0a040180a2d158a106265b0d02e2c602f978ba190045450268a44c4a1a2d81e2d148990a24b60306c205d8b456281e890a96c060600008030145403142181627125b070c0000280c051600c5009132102a24b60d97c003d11014080200c5a2a0304c4c0d120fad8bc000281006018b4540514044480c1e5b174003f0281007160145403142081e261a032d8b8058ac4a28602044c0c195d17d725e5c174b9155bc508600899000b120cad8c01c004540b1489866241c5b1822d142fc4c8112080640c575d981725e5c174b8425bc5a28008990009120cad8be1b8b0022913
  | 4 => 0x744d1cad4700e1b93c6c711a958678b198c863ec189b460cd17cc05d3416ac058af15b545431148305098136544aef1245c463710d6040560f6583ad00e33c36ea0d6c433940c4442ef70b060290c09e2c262d0923c22b1082441e7406fb01a6c063b4174c0574c1377042380ecf033c00af30223c06ae013c402d6000010060500c54011421c4971110e01406041c00401168a44971110506c043d0281002008b454065e8901a22b80487c7e050200c05160045628415c4440e1a02810060200c5a2b14892e00c195d981745f5b9716c5b2c95c0d168a80a24030f07c551115ae0bc5e031700a5b8a4486d11300d004581b0100601000162b145c44a22601a17cbc5c028a82cb82dc5628270e44841113002004048b16e25141dc443c5f1380870050180400041a458bf14892e2220a13848365c02458b7148908222362f820b2600317007162dc486d112f0d08641010f45258028d808010000e2d155c448bc22888d054602f97006b82dc58b3158909c41112f020c05e00c58b7141b444b834010fc7c281e0984a052c010060000c5a2b145c444b8343017cbc0115034b7165c45628270d082225c040080c008b172283b890203c202d8d804050200d70018b0022b14890803c5b06064b8008b4504f121a16c10558b17a2b135b87e22061583c0803010162a008a10e26b788870aa050180808008b45085135bc44141b03
  | 5 => 0x748cbc230ea8bed22d318ac32298f89eae264b893b2236e8869e20d087b461cad86c2a19d485d3615a985242128e843560e2b833320b4c8274607ab8192e04ec80dc2016b80045fde97f329fb8e7e73df7f17d73df3f17c725f0b47b8a9ece97af55e92c79ed5e50879045e1ec781d1ddee770bdda4e76239d6cf753cdd28d743adcf91735b9cbb372555c6b571055c16a700b9be6f6f241ba8d6e3b9b7316d435b36f6c655aef76b059a95469b35a528690c9a1f467dc99d2b66f4599ab66145963165051918d63fc18df362e51891361ae983796013d7e6a5f4c17b325e3d9762e5d1c172705c1c16e6d5b3396b105a4396752594396353583b55f4f575b95bb15661d58b055ad953ef548594f51534d54a8b524c547105142d43b1506413f8f4f6b53c0f4e8e1372e4d5cd330e4c54d2ef44b1b52acb4a5ad28104982d24b34892d20ec47dc51d5546ab1192c45eb915eb4523512f0443c90eae433c10af841fc505ce4105d01333fb50fc4c3eb38f90a3df48f5923cd58f0943b830ec8d3abbce91439a58e3cd388c0e03337738dc103683cd82f3593cd4753474ccf70335b8cbb8322c0c6b331148c20b302a4bf912f5dcba8f2e2d4b60a2d344b2b62bfb8ae2c2b2b0ab322a3aca791295cca313282dc9dcc271409a5625e2c96312504c91b523c3c8d3122c4c88b5218348477206587ecb1f5bc7b8b1e8b078af1db50
  | 6 => 0x801fe007f801fe0026c054082854092c378c3b93a3c2c9b316c07f8004810c382d591cff801fe005b04ffe001c2aacb04b1985cc35cb215fe003a2c1fe00479e5b8ba7f801790ec404bce96820a15c8092368fcadff80018757f801fe004680dfe0078bbffe007f80064e96c08d027146abd685f850ed28eb0eb2a2073b245e0924488a33ed1dd1159eb0f89ed5a49d924c44225397d38951d87652faf798864fd95c94b0edc6422e0e048449a81bff801920d3b8e9fe004083c1ec47f80154e35b9eb52d8ff8007a77080b7fe002d8b21647f31adfe006cc3f1a1e2748770570b9977c04cd98a5ae15a20e029d1699e0c028e12e828c93bee42207109a0260d78c01a7d3799b88a042940930d7a327fe007b29a76d9b4c0b3c867f800742c388bca29f1e9e2067264815e455a5b9cce36d9811fe00168956c7cbd1e9cadf0d04002000008e8801f400d0004106182aeb92e78b0c0098321080029126016030010980002848102000002e340060e18082120b0001004080001820f080850d042c48100100040428480000000e0000a410614005045d28600403021818b8000200053c08007020c5000604c962c10006042c10300041060400511103420034000050a00103080003c0600081083839500000000a0c5910018284122028504002000a001b24b0d925c2476e916b244379052e3fef8f8463beb8ea42388d8dbb235
  | 7 => 0x7fe006a26afe57c708e9458153a3fe002ea5f206da3032a233f5857fe0045379fe005036a5e5c03420089ef613f502b4b83bd8b98fb9518cf2bafcb6113e235a43455477cec17f8014ef0d43a0e0e6ff8003edea2841fe006a020ecd05900540f537837b8021faedfe007f801fe0005c43fe0030bb400c6ae2293600352adfe002148eb84aa52b9fe0011a111a48f5388c86af6ab0e62e873e80e20ac3e65042122937644c906c14f712bae3d2679c1b2309aa3f0bc0b8fbdf08133c31e6cafd5b6e746958b2e241557b559258f84418718a3a62a20c79874bae3ebc3048787f80162554b87bfe007f8014681ff80086f1ff801067dc39a1fe0065a238a3ee5332587eff801fe0061b97fe007f8019311ff800d6aec4bc1e43309415b0ad618a4ea52ff800e8b4ff80082817f8002ad37f8003e647f801fe003d351a454c8c39fe00799d1fe00003566841f9b99fe002d975fe006f937e6ec722d7d09a4b338e45cff801fe005b96cf90ba50f2d216b4c4eec3830a87704b403021b136f267fe0054c009a5edb1bb67038b9ffc719d3c8d06f8eb16e806e06bffcc907f80050f8200a7ce898f9deca637f80092192aa478639ff8014692a4ae5eb05df376b0544b312c6fb498cbe66d198600e5aaa8f620d10814498ec88c538853849aeb6ceba2a928d6a937e784052c19fe0038069fe0077c9d20feb291beeb38fa1dfe007f
  | _ => 0

def word127_2 : Nat → Nat
  | 0 => 0xd16cf23f7a490418034c1d3c9b7cbe330c91895a6a3954f37f800c431f0ad8f0f290099e2dd5ea484c1cb9469b072c71d89c08bebfcb8bc020962c6feaa010a2d730ab52bf8e9a7fe0057497a427ff8014b111119288d0c19a3029969850869dafc36407f7705e3ca0822a61d1e87b37fe007f800004d7f800131b63261663a840e41821cf0bf6e14cdada406a798f91aa8eb2790824b707f382ba2b150c656b1c6305a76b0ac90cf0977147c342e1f1176627274bcf5483fe007f8002e067f801fe0053a7f821f3fbdbfe00291da1e93bd3717a8e90058f63523af5e422e9474a71c47460be916d41d4ed4ceaef0720163160f0b6133ec84863999ec3be806b52d7ad9eed31e01946f4b28d485ba6772a6c584ce5adee482610288322d89172c61a329ef6527f801c47482ad5225640386a607e50d29aef7f8012675c181d58095dc107242b9a2d40abd51f93640b44069ab8bcc7c70d2ab25cfb034522a1c9472c6bfe0008ba6f68babc7ee6272f3a96690a8c5888247f8012806b93d672f3ff800d724a9911e8464b8a942122eac85ac85d164a005fb3d978ee88930ec94cb905fe002ba8bfe007f800de848fa3080b1f53f5663fbab2330435115bc459c9026d11286a3d44c32817842f473a20f6e47b8c5fe0010373c8c6580463abaa4bf8860e7f8008a00f31293ce0ff801ae18ff8004843d69c29cbee534e188db845
  | 1 => 0x2201272200a71c23271c13271c03271a23271a13271a11271a03271a02271a01271a00a71413271403271213271211a71203271202a71201a71200a70c03270a23270a03270a02a70a02270a01a70a01270213270211a70211253211253202253201253200a43211a43203243202243201a43200a33413233213233211233203233202233201a33201233200a32a01232a00a32201232200a23403223221a23213223212223211a23203223202a23202223201a23201223200a22a11222a01a22a01222a00a22211a22211222201a22201222200a21a11221a01a21a00a13221a13211a13211213203213202a13202213201a13201213200a12a11a12a02212a01a12a01212a00a12221a12211212201a12201212200a11a01211200a03221a03212203211a03211203202a03201a03201202a21a02a12202a11a02a11202a01a02a00a02221a02211a02211202201202200a01a11201a00873221ff8001aacc4a70ac85ff80142c3c4ac42630fa80e480aff801fe003f20d4c6f050e3fe0024c6e084eac9381b142cb48c81c41a97d6ea9a83ef84f56885a201b049fa4a3ee21b54bda421f6af487b9f42474f455fe005a2cdfe003b3090c638d465b900cf285fe007f801a8e4ae9c1fe00239e7dd0f7f800dce2b0bf38d0ac02d1fe0016c1ed019ca31dfe007f800949bb20fc846c079438e2e1b258a8f9068f4fc364836c8
  | 2 => 0xb4222b4212b4202b4682b4282b423234222346823428234681346810aa530aa330ae730aa730ae830aa830aa228aa028ae828aa828aa220aa020ae720aa720ae820aa820aa218aa01e2a5362a3362a1362a8362a32e2a82e2a1262a0262a8262a81b0682302533023330213306833028330222b0682b0282b02223021230202306823068230682302823008230681b0281e73221e73212673211e73211673202e73202673201e73201673200e72a23672a13672a11e72a11672a03672a02672a01e72a01672a00e72223672213672211e72211672203672201e72201672200e71a23671a13671a11671a03671a02671a01671a00e71213671212671211e71203671202e71202671201e71200e70a23670a21e70a03670a02e70a02670a01e70a01670223670221e70213670212670211e70211473221c73212473211c73211473202c73202473201c73201473200c53211c53211453203453202453201c53201453200c43213443211c43211443203443201c43201443200c33213433211433202433201433200c23212423211c23203423202c23202423201c23200c13221c13202c13202413201c13201403221c03212403211c03211273221a73212273211a73211273202a73202273201a73201273200a72c13272a23272a13272a11272a03272a02272a01a72a01272a00a72413272403272213272211272203272201a7
  | 3 => 0x1a4341a4341a3341a2341e82c1e8241e81c1e8141e8121a5321a3321a2321e7321a8321e809925319233192231921319673192731968319283196818e4430e2430e4330e2330e4230e2230e6730e2730e6830e2830e2328e6820e681042530444304243044330423304423042230421304673042730448304283042428422284682042820468184281842816e4336e2336e4236e2236e2136e2836e2826e281ee2813d4233d2233d6833d6813d4433d2433d4333d2333d4233d2233d2133d6833d6833d2833d0833d6823d681bd6813d68120e8096a5316a3316a1316a7316a1296a0296a728bc530ba530bc330ba330bc230ba230be830ba830ba428ba228ba028be828ba320be8101c5301a5301a4301c3301a3301c2301a2301a1301a4281a2281a1281e8281a8281a2201e81ea4536a2536a2436a4336a2336a4236a2236a2836a222ea282ea281ea281394533925339433392333942339223396833928339242b9222b9682b9282b9681b968115233152231521315673152731568315283152229521295202956729527295682952829521215202156721527215680956809568380a4300a3300a2300a1300e7300a7300a3280a2280a1280e7280a7280e8280a8280a3200a2200a1200e8200a8200a21e6a2366a1366a8366a22e6a12e6a02e6a82e6a8266a81342233468334681342433422334213346833428334232
  | 4 => 0xa533da333da233da133da033de833da833de823de81bde81bde80bde80a12532122321203212732168321222a1272a16829725317243172331721317203176831728317212976828c2530c2330c2230c2030c2730c2328c2228c27282253022430223302223022130268302283022328222282212822226aa536aa336aa136aa836aa32eaa12eaa82eaa326aa81eaa80b9a32b9a5339a4339a3339a1339e8339a8339a12b9e82b9e81b9e808b4530b2530b2230b2130b2030b6730b4730b2730b2730b6830b4830b2830b2830b2328b2228b2128b6728b2728b2728b6828b2828b2828b2220b2020b6720b2720b283e7223672036728367222e7282e728267280b4a12b4e82b4e80b4e8034a3334a2334a0334e8334a8334a22b4e82b4a82b4a3234a1234e8234a8234e80b4e805f2535f2335f2835f222df282df2225f2025f2825f281aca32ace8254281d428154280d4283a928229681a96812928129280a9483a9283d0a82d0a81d0a80d0a83a6a5326e82a6e81ce2534e282ce2814e280ce283a2c5322a5322a4322e82a2e8122e80a2e80a2e83caa82caa81caa80caa839b2531b2331b6829b6819b6801b6801b68390c5310a5310a5310c4310a4310a4310c3310a3310a3310a2310e8290e8210e8172a5372a3372a2372a82f2a8272a81f2a8157a8257a8157a80d7a8057a83c1a2341e8141c5341a5341a5341c434
  | 5 => 0x731627316202966729627296682962321621216682166808123301213012030167301273016830128301222812028167281272816828122201212016720127201221e8a1368a0368a8368a22e8a02e8a82e8a8268a01e8a8036680b6213366833628336222b6202b6682b6232366823628236680b66805c2535c2335c2135c2835c222dc282dc2225c2125c2825c281ab68254a81d4a8154a80d4a8054a83a9a8229e81a9a81a9a8129e80a9a80a9c83a9a83d1282d1281d128151280d128051283cea534ea82cea814ea80cea804ea83a3453232532325323682a3682a3282a36822328223680a3680a3280a36839ba531bc431ba431ba331be829be821be80482534823348282c828248281c82814828048283914531125311253114331123311233112231168291282916819128187453072530725307443072430723307223072230721307282876820728187280f32537323373413732137321373282f328273281f3280d8282d8281d828158280d828058283c2680422534244342243422334221342682c268242681c2680c268022223224132221322203226832248322283222832228399a5319a3319a1319a0319e7319a7319e8319a8319e820ec330ea330ea230ea130ea030ee730ec730ea730ea730ee830ec830ea830ea830ee818ea818ea83eea336ea236ea136ea036ea836ea826ea81eea80bde81bde80bd
  | 6 => 0x317a7317a7317e8317a8317a1297a0297e7297a7297e8297e8097e800ca330ca230ca030ce730ca730ce830ca830ca228ca028ce728ce828ce818ce816b4536b2536b4236b2236b4136b2136b2836b222eb212eb282eb2816b280ba68115a2315a0315e7315a7315e8315a8315a2295a0295e8295a1215e7215e8215e80632536323363213632036328363212e3282e32126328263280b0e8230e805fa435fa235fa835fa22dfa02dfa82dfa225fa825fa812d2222d6822d68156a81d6a80d6a83aaa822ae81aae802aa802ac83aaa83d2a82d2a81d2a80d2a83cfa534fa82cfa80cfa83a54532525325682a56802568393c5313a5313a5313c4313a4313c3313a3313a3313e8213e804625346282c6281c6280c628388a5308e81752537523375282f528275281f52805a2825a2815a280da283c4680c425344443442434423344682c468244681c4680c46801aa531aa331aa131ae731aa731ae821ae818525305233052130520305673052730568305283052830522285681852818548385283f0c3370a3370a1370c0370a0370a8370a8270a81f0a803fa333fa133fe833fa833fe823fe81bfe80182531824318233182131820298682986818d2530d2330d6830d2830d2228d2028d2320d68002a226c2536c2436c2336c2836c202ec282ec281ec2803b2533b2333b6833b2833b202bb682bb681bb6801623316213166
  | 7 => 0xc4c5344a5344a4344a2344a0344e82c4e8244e8144e80c4e801024310223102031067310273106831028305a5305a4305a2305a1305a0305e7305a7305e8305a8305a8305e8205a8205e8105a8105c8385a83f12437122371213712037128371282712817128018a1318c0318a0318a8318a028345303253032430342303223032130367303273036830328303212836728368283222036816ca436ca236ca036ca836ca02eca82eca816ca80652136528365202e5282e52826528032680dca435ca235ca135ca835ca12dca82dca825ca812be815528255281d52815528055283d1a81d1a8151a80d1a8051a83a7682a768127680a3c5323a5323a4323e82a3e8223e8223e8123e8123e804b2434b2824b281cb2804b2839c4431c2431c2331c6829c6821c6809c683c8a4348a3348a8248a8248a81c8a8148a8048a8391a4311a3311e8187c5307a5307c4307a4307a4307a3307c2307a2307a2307e8287a8287a8207a8107e8087a80f3a4373a2373a82f3a8273a8173a80d8a8258a81d8a8158a8058a83c2e8242e8142e8042c5342a5342a4342a2342e82c2e8242e8242e8142e8142e80c2e801a2231a2031a6831a2830f68184a5304a4304a3304a2304e7304a7304e8304a8304a8304a2284a8204a8104e8084a80ef2436f2336f2236f2036f2836f2826f2816f280be6823e68117a5317a4317a3317a1317a0317e7
  | _ => 0

def word127_3 : Nat → Nat
  | 0 => 0x32534323343423432234321343682c3681c3681436814368143081436808fc230fa230fa130fe830fa836fa436fa336fa136fa836fa81efa816fa80bea333ee833ee81e7a4367a8367a82e7a8167a80b52533568335682e3a5363a4363a3363c2363a1363a8363a12e3a82e3a81e3a80e025360233602136028360282e0281e02812da532da331fa331fe829fe829fe819fe809fe80ca2334a2824a281ca2814a483ca28394a4314a3347a2347a81c7a8147c83c7a838a2530a22376a2376a80f6a805be735ba815ba83c5e8145e8345e8145e80c5e80002230027300280802800048386a2306a0306e7306a7306e8306a8306a8306e8086a8086c8386c8386a838da230da730da830da0283a1283e8161a4361a0361e8361a8361a02e1a82e1a0261e8261a8261a805e2535e2335e2235e2135e6835e2835e212de682de282de6825e2825e280d72825728157280d728057283d328153280d328053283a8e82a8e8128e804d2434d2824d280cd2804d2839e4431e2431e2431e6829e6829e2829e6821e6821e2821e6801e6801e2801e68394453142531444314243142431422314682c6a4346a2346a8246a8146a80c6a838945309253094430924309243094230922309223092130968289282896820928209681092810948389283f5a4375a2375a0375a82f5a8275a8175a805aa825aa81daa815aa80daa805aa83c4e80
  | 1 => 0xa80d9a8059a83c3a2343a1343e8143a8143e80c3a80c3a2343a1343e8143e8143a8143e80c3e80c3a80e4253642336421364203642836428264281e4280b1253312333122331213312033127331683312833168231271b1681b1680e0c4360a4360c3360a3360c2360a2360a8360a8260a81e0a812e2532e4432e2432e4332e2332e4232e2232e2132e2032e4732e2732e6832e2832e2722e6822e271ae681ae2712e6814da82cda81cda804da839ea331ee829ee819ee801ee83c722347282c7281c72814728389c5309a5309a5309a3309c2309a2309e8289a8289e8189a8189e8109c8389a83f62237620376281762805b280db283c522345203456814568006423062230620306673062730668306483062830628306681062810648386283e5a5365a3365a8365a02e5a82e5a81e5a805d4535d2535d4335d2335d4235d2235d2835d282dd281dd28155a8255a81d5a80d5a83aa2822a681aa281aa680aa280aa483aa283aa283a7a5327e82a7e814f2534f282cf2824f280cf283a445324253242532424324682a4682a4282a4680a4680a4280a4683a4683a4283cba434ba82cba824ba81cba80cba839ca431ce83c9253492434923349282c928249281c928392453122531225312243122431243312233122331268292681f4253742337421374282f4281f428174280d9282d928259281d9280d928059283c36814
  | 2 => 0x813ca8038682b8682386813868033e82b3e8233e81b3e8053a82d3a81d0282d028225e82a5e8225e809f2431f2331f6829f6821f68071a3371a8271a81f1a8171a8040681ed282ed281ed2816d2803be813be8069282e9282692816928036e80e624366282e628266281e628032e80b2e805da435da82dda825da81dda812c68120682a06823c22337e82b7e8237e8137e80b324333682b368233681b3680afa43562825628152282d228128682a868124a4324e82a4e8224e80cca82cca821da531da331de829de821de80132531324313233132237028270281f028170280bf2433f2233f6823f2823f681bf281bf680bf280eba236ba82eba81eba816ba80baa533aa72bae816825368282e82826828168280b5a5335a4335a2335a72b5e82b5a7235e8235e80b5e8035e8064a4364a82e4a8264a81e4a80b1a5331a72b1a71b1e80612536124361282e128261281e12812ea532ea432ea232ea72aee82aee82aea82aea722ee822ee822ea822ea71aee81aee81aea81aea714c282cc2824c281cc280cc2804c283cc2839d2331d6821d6819d6809d6839d683c9a3349a82c9a8249a8249a81c9a8149a8049a83c9a8392c4312a4312a4312c3312a3312a2312e8212e8192e8112e8388253082530844308243082430823308423082230822308213082820868188281882810868088280f4a2374a1374a8174a80d9a8159
  | 3 => 0xfdffff5fd3ff7bfef7bdeffbdef7bfef7bfedfb7edfbbfeffbfcff3fcff3fddf7fdfb7f4ffffdff9feff9fe7fbfe7fbfeff3fcff3feff3ffbffbfffbfdff7efbfffff7feeffbfdff7fdfffeffbfeffbfeffbbeefb7edfbeedfb7efbdff7fdff7fdff7fdfe6fdbf7fdff7bdef5fdff5fdff7fdbfeffbfeffbecff3fcff3ffffffdff7feffbfeffbfeffbfefbbfcff3feff3fcffbfcff7efffffffbbfffbff6fffeffbfeffbfeffb7edfbf6ffbfe5fbf6dfbff7fdf77fdff7fdff7f9f77fdfe5fd7f7dd7f6ffbfedfbfeffbfeff3feff3fcff3feffbfeffbfeffbfcff3fedfbfcff3fcff3ffeffdffbbfeff7fdfffdffbff6ffbfdff7fffbff6ffbfffb7ecffff7edff7f9bf6fdfb7fdfe6fdbf5fd7f7edff7f97f5fdfb6ffbecffbfefbbf4ff3fcffffdff7feffbfefb3fcffbbeffbeefd3fcffbbeff3fcffbfcfffeffbbeefb7edfbfcff97edfbfcff9beefb7edfbfcff9bfeffbecffbfcffbeefd3fcff77effbfefb3fcffbdcff3fef7beefd3fedf37cffb7cff3fb8e82b8e8238e80b8e8072281f2280f22337228272281f2281f2280f2280f228040e81c0e80eda336da82eda81eda80eda8069a72e9a82e9a80e9a82e9a8269a80e9a803768337672b7682b768137680e2272e2282e2271e2281e223362282e228262281e22802f672af682af671af681dea335ea82dea825ea81dea80a6682a6682412333ca82bca81bca
  | 4 => 0xcfffdfd7fdff3fddf77dffbfedfb7eff3fefdb7efd7bfedfbfcffbfcff3fcffbfeff3fcffbfcff3fcfff9ff3bdef7fdef7bddf7f9ff37dff3fbffbff6ffbfdff7fff7ff6ffbfdfffdffbbfefff9efbbfcffbdeff3fcffbbcff7eefb3fcffbdeff3feef3fcffbecffbfeffbecffbdcffbdefb3fcff77dff7ddff7f4ffffdffffff77ffffbfeff7fdff7ddfb7f4ffdfdff7ddff7f4ffdffffdffff7fffffffffffdffffcfffdf77ddff77ddf7fd77fdfdff77dff7ddfd3ff7ffff7fdffffdfff77ffff7ffffdf7fddf77ddf7fdfd775ff7fd7f7fdff6ffbfe7fbfe7f3fcff3fcff7fdff7ddff7f4ff7f6ff9fe7fbfeff3fcff3fcffbf7f7fffffff5fffffff7ffffedff7fdff5bdef77ddf77dfffffff7feffdbffffffeff7ffffffdff7ffffffeffbdeffbf4ff3fcff3fdff7febfbfef7bfefd3fcff3feff3feff3fffffdffdbfdfffdeff7fff7f5ff7fdff57ddf7fddf7ffffffdffdbfffffdeffff7ddff7f5ff5fd7f7fdfd7fdf56ffbfeff3feffbfcffb7cff3ffffbfedfbfeff3fcffbfcff3fcffffffffdffbff6fffffffbfdfffffff7ffeffdffbbffffbfdffffdfffdffdbfeffffef7bf4ffbdcff3fcffffdff7fdfdbbef7bf4ff3fef73fcffbbeff3fcff3fefdbfeff3fef73fef7bf4ff3ffff77dff7fdfb3ffff7fdffffffbbfeff7fdff7ecffffdff7ff7f7fdff7ecffdff7fffdff7fffb7ecff7fdff7ecfffffff7
  | 5 => 0x7f7fdff7ecffdff7fdffffdff7ffff7ffedffffdffffdffffeffbfeffbfeff3fcff3fcff77def7fdfb7fcff7ee7f9feffbfeff3fcff3fefb3fffbfeffbbeefb7edfbeffffffffbff6ffbfdffffdff7ffff7ffffbfeffbfeffbeeff3fcff3fcfffefffffdffffffffffdfffffffeeffbfdff7fffbbfdfff7dffb7effbfcffbfcff3fcffbecffbfcff3fcff7eeffbfefb3fefb3fcff3fdff7fdef7fdfd3fdef7fdfb7f4ff7fdff7ff6fdbfef7bfef7bfef7bfeddfdff7bdfd3ff7fdffef7fdff7fcffdff6f7fddf7bdff7f4ffdff6f7bf7ddf77dff77dfb77dff77d7f7fdff7fd7f7fdbfeff3fcff3fcff7fdef7fdfd3fdff7fdfd9fe7fbfeff3feff3feff3fcffbf7f7ff5ff7fdefef7fdfb7fdbf6fd7f7fd7f7bdff7fd7f7fdbfeefbfefd3fcff3fcff7fdfffffdffbfffff6ffffeff7fdffffffdbffff7fdff7f7efffffdbfeff7fdffffffdbfdff7bdffbfeffbfeffbfeff3feffbfcff3fcff7ffe7fb6efbbdef7bfe7fb5effbeef7bfedbfeefbfefd3feff3feff3fcff7fdfdbfeff3feffbf4ffbfcff3ffff7fdff7fdfb3ffff7fdffffeffbfdff7fdfb3ff7f7fdfb3ff7fdfdff7fcffdeffbdef7bdef7bfef7b7edfbdfdff7fdfb3ff7f7deffbfcff3fcff3fddf7ddfb3fdfbbfe7f9feff3fcff3fefb3ffb7fdff3bdef77ddf7efffffeffdbfeff7ffff7ffb77ffffbfeffbfeffbeeffbfcff3fcff3feffbecff3fcff3f
  | 6 => 0xf7fdfd7fcffdffffdff7fdffff7fdff7fdffef73ddf7fddf7fddf7fddf7fdff5fdff7fd7f7fdbfeff3fcff7fdff7f4fffffff7ffff7ffffbfeffbfcffbfeff3feffafeffbfefd3fcff3fcffefffffdfffff6ff7fdff7feff7fdffbfeffbfeffbfeff3fcff3fcffeffffffffffffffffffbff6ffbfdff7feff7feff7feff7fdff7fdff3ffff7fdff7fcffdfdff7fdff3ff7ffff7ffff7fdfdffffdffffdffbfeffbfeff3fcff7ecffbfeff3fcfffffffff6ffbfdfffffff7fdffffeffbfeffbfcffbfcff3fcffbfeffbfeffbfeff3fcff3fcff77dff7fcfff7dffffdffffeffffefff7ddf77f7f7fddf7fcffdffffdffdfffdfffffff7ffffffcfffff5f7fddf7fdff3ff5f3ff7fd7f7f7fddf7fcffdffffdffdfd7f7ffff7f7fdffbfeffbfcff3fcff3fdff77dff7edfd3fdf7bfeff9fe7fbfcff3fcffbdcf7bdcffffffffedff7fedfbfeff3fcff3fcffffdff7fedf3fcff3fcffffdff7feffb7effbdeff3feff3fcff3feffbfefb3fcff3fcffffffff9ff77dfe7fddf7dbddf7bdf73fcffdff6fdddef7dcff3ff7fddf773fcff9fdf73fdf79fef73fcffdde7f7edfd3fff7ff6ffbfdffffdff7ffffffeffbfff7bfdfffffff7deffbfcff3feff3feff3fcff3feffbbef7bfcff3feff3fcff3fcff3fdff7fdfb7fcff7fdfb7fcff7fdff7ff7f7fdfb7fcffdffffdffff7ffffffdfffffff7ffff3ff7bdef7bfef7bfedfbdff
  | 7 => 0x1f0a4028140201201804008014088540393118551104c028140480602504150514084b403931100eb80520285413c471122c0400c0500804806295021f50002b92144471122c0301404806150081350212d008b3931100f400540207f11c448a810210081404ae4c448a80e13b220581a060841fb54b998c3f8081350111b92bca2a048062107c1300940393118151122a02010145041522a12d00e4c46bc80f110541f01413500e4c471100c0281201855410514022ae4c4403836155041404b403931122a0380e158140204b4080614812e4c47112280300a04814025041550214228e4c4403cff3fcff3fdff7feff3feff3feff3fcff7fdffbfcff3fcff3feff7fdff3fcff3fcff5feff7fdf77feff7feff7feff3fcff3fcffbfdffbfdffbfcff3fcff3fd7f5fe7fb7edfb7edf3fcff3fcff3fcff3fcff5fd7f5fd7f5fd7fdef7fdfdff7fdff9fcff3fcff3fdef3fcff3fcff7fdff3fcff3fcff7ee7f3fcff3fcff7edff9fcff3fcff3fdff5fd7f9fcff3fcff3fe7f3fcff3fcff9fd7f5fd7f5fd7f5ff7f7fdff7fd7f5ff7fdfd7f5ff7ddff7fdff7f3fcff3fcffdff7f7ffff7ffff7ffff9fcff3fcff3ff7fbfdf79fcff3fcff3ff7fdff7fbfdffbfdff7fffd7f67f3fcff3fcffdfeffbfdfd9fe7f3fcff3fcffdff7fdfeffffdffffeffffdffffeffffdffffeff6fdff7fdff7f5ff3ffff7fdff7fdff3ff7f6fdff77df
  | _ => 0

def word127_4 : Nat → Nat
  | 0 => 0x500e8980a03d04050081504f408040439511c4489b94b62dcb9a2e8aa285b0800381a1fb921f444bc850b722c1c22a1e22e058f40381a1f228e4c44bbaf2200a4122da1f5021c01a03d0005880e4af311016010501304b1139203ada1f0bd408161d00f4008006c44bbb92068bc005001404a133931100e008162002cb68761001a3887d112e6bba2c202da068281f816e4ae6bc9941f0a42f0161fd0003c440687cbbb922f0800022d4004a133931100e0088005824b687e1001a1e0db112e6bba2ab68743f81a0807e05b92b9af2630781204c1f8780687d4000e1db9205af3110ae010508a84b11392038422f0161fd0003c4406878bbb92200bc000514004a8ab931100e05802202da2f2ee1f0768a040b68741281a1101c1f2281e016e4ae6bc988b82de15a2a8a0ba8b3920e016212eeb8ae08b22a2ea2804a2e0fb9205884bb87c158354000e05b92211a111504028080501201d02210054044711054e4ae48bae0e4a501c22a2e8120582e0422c2aaee1500c05008048068b502015001c08f11c44e48700887c2150003a2a05b9263c448a870080ab400843f816e498d118aa0281201d042104e0150111c44053920300a0522802504040561480540c4511812e4aee1322b410514004abcc4603c44e4adeb822a8a08511c44290381f054b8a2cb822a5b96c04c46214440f87c1516eb800c1404c12a2ee4c4403d04
  | 1 => 0x1cbbb94b602620802bbb233f87a1e0dc114461d07000016b604abb8821ea26112e2b8048d22268b0708a83c128108bb9405886bbae01504a2f0354087003886e51a005c4402814020100150421d02158061c4fe12c4711394b9348b80488bd021c22a2f2260402c21b9405a2cbb84a2f02a21a2d4087003b94658171102940a2c218713f816e51951185203014020860400540a2c018713f84b11c44e505a0300a12010015041f0073fc4711014e500c0281489808155040587c01d0311c4404394bd2f6b78401a2ee0580f3f806030c02f8402e84c8b850bb8bc30c471139403d0540806010c2300be20050130bc2ec471122603b94b8a2c2f2dce52265b01429087110361c04c292e2122e089a2ce50708a96e5b011118871103c1596eb80bc150574080c130508bb951100e02814025040400400801408873fc471105605008040040285741502134fe143951100e1f01e0587f4085602c4511aee04a2cb92e08bd028a8bc5b2260407e21c44e502c140bd4080a2184ce54448b00e0781cb980a21994e54fe1f85111af68b00c05008040054087e2180b3fb94144471122c0301402010010574084c8b4fee54440384c13cfe07856058091105311aee04a2ab90a8b8a2e8b2262f16c1c010e507f11024130874101001048130093fb95118151122a0300a0400415d04144fe8ab951100f415020122e8b22a1344415850e
  | 2 => 0x7ae6870e5974120b21f03a14010e4816e507a60b9a5e0781c3961217404ad82c810e4c440e87a12c50160c3130462f8c02c8aa420bc3c3928b3941480e1e87c0ec4605c45140c2118be1dc4c112de2000ee54460587c1017460ad80596c1c8f0e500e08c442b87c63a2ae4b9ae604c5d0ae60844b98162aada5bb94328201d4468a98c1db9ae60142a83a040ae1e04c05b941d9825e176e6b982fad9110102b87c8ab920e84a1f5023197a0380260876e48f05b0105b8451104a2f0001404ce4b951100e030080500401d0213050e4b951100e8b44612ade1e226c8a2a5e8c80581c29394108b2bd2ee1c070058013f88340aeeb604a1ea2e110a41d04ab7a268b0708a8163cb1c8b97a32044e5040070b2bbaf4208341f01c1e17abd0826804b40870e501c2ccfe2090c05af5118340c87cbd17a01878434ff1184a209a0e5000110ab4082eb60162081d1187c390c8bba2c2a8741104ab7a2f408708ab1c8987cc897a320b20581c1e840e52eebd22c0a8b2070785eaf41e996128b21f5021c394074fec707a05af51182a2c8285e806bd31c1e4473f84a1e996e5046058ab408b2c8c460707cbbb9411ad80b882008aabbb233f87c390451180020cfe1107b4107009ad80581d118dc1e0c8bba2a2a22e1104ab7a2c899902ab225e8c81e01ce504005870bbaf48a882b64fe0881c1122a1f17abd18e128162ab221d4461e
  | 3 => 0x88b4fe13447113960300a0400541056148093fc4711012e580a0485401d041e016120094044711010e5ae711a261dafae5854b72f91100e1f05a030508b8aeb7c46152dc8ba281da26e585a1f4440e050b9c46152261dafab72f9113960385a1f00c12a2eb88af11854b722c8ba265b012e58771107c0f84a29a2cbba28042fa122e215adeccaf80144403b9616a260322e29ae215ade8a22e5b96c044462c0771103c1200a018134107c0400400801404fe2bc471105a1680a048071181012005410514004b3fb971100e14850b70161f5013f84802c47112ee0522cb9048b78768b8be8a16c2b87c0439689c440b0501680c0480629810015001f00ae5cfe144471122c0301201810010488b50012cfee5c4403856040041280614cfee581311c448a00e048061507c1200540397118111122677179132dc308ae2ec441e880e48445e44cb78c21d8bd118b220b941039913070e58783197ab601660b92ba0f01f16c0d00f111a02084a1c3965d048208100e8b205b94201821e3985d870e58485d2d80407ce4c440e88212858300462f8bb13c4c42b922c8bc3c0af118540383ae501620c44300462f84513c4cb787603b942007b11816103966f177132de388c60b0761e8c1118502007c040bc8b3941039a1c3962f176608785ead8058b25b3923c00e0ac441e9968b04ae68aa1c396142e6e49821d0162cb940a07c650
  | 4 => 0x2f07c1c82232c44372e6bba28102da1c8bc058801f5008980e08c44bbb9611a261d84cb83247017a3288005820e5aeebe0aa8b8ae11884132e08ba281da26c94465e8ca05820e58aabbaf81f882058002ad0011836132d8080ec8bc461d0cabbb2411a261d84cb81c05e8ca20016083968a2eebe0aa8b8ae2104cb822c8b8768997a32820e5817118aabbaf81e31e1da2c11a28132e14010c5e8ca058201d39689aeebe22e2084cb85008a0163cb1e1d22e5e8ca11b9608040bbaf82c076b6228210762b882085000d0781187e5eaf86804c1e870000aa0584740030b6074080e71187ebb8ca8b22e11a281384cb80af400aac917a3287405820102eee5876be22cb62281dcfe0802b4022c118785eaf86584c1f8442a8173fa2d400766f446082eee5844b60302ad001d2ee009bd3f87e3984711800200a6118162a824b65001302036c46bb8ca89882058768a07abb8206db96051ecb705489876c94fe0584c030aabba2e2bcfe8ba281da26130aa0587ebb856152274000e2a80d3f8480522ebbb24e58067b2dc152261dcfe05228058aa1300cbba2e2badc1522d3fa2e1da260f84c048aa05878bbaec122e28b396b78568a0040501613226032ee8b848b8814b78568a03c0422e130b005a261daee0580a048062b81001505400781f8093f84d11c44e5a2e052de8a0ae938100b0aa05a2c1daee0301201810015001e00
  | 5 => 0x9c461304b1122e2380e0500804806040040080003d02e65013f8b223c471122e0500804810010074084ce65013f84b1100e300553fa265b96c033991104a1300e8b80604878130100150012398024ff118151122a020141581001502e60061e4ff118131122940d000122e8aa28e608e12c441300e898080500e0480615502e600413d000444711226100a53f8702f00014396e5444038801407ebb84036854bf04c608782004abb854100dabf04c6088215078e5228ba17ab60701301660afc3187e5b034039a111080e5870609765c8c2e6394b6080e48101e07f11024130a6e697660b948a17ab60165b0c60382a1e071111968b396b68502a8281f99429870299785cb9a30392e52d81c22c0407911024132e689876b81c0428160880f11396bbafa1f22e2bb9421080b62e0b9a2e8a0768996c03822e5c441f2fa141c042a261dae005c440880ee587cbbafa12a2e2b884202e08b22e1da26058f403822e5c441f2eebe84a29a2c8a2e01c882e50160880f1139689aeebea2e29a28b83945f0723181603822e5aeebe8b1110762f2dab80841007c05d002b80f3fc4408aeee58222f0401ccfe210014005012b971100e00870140160c2da1c8223287d110e6b9aee8b072e5040b80768ba285f2e62ba26140163180e0887ce5c44bba2cbe96c08828e5cfe1f2e6be994140a73f8161f44408aee14396008700584a09ada
  | 6 => 0x446000160c2d9118aa1f87010828290e66e2ee8a800200741c016294460b2d940d000a04038aee14226112d82a8174007e1d0286e0cb11aeee622e0807a8a4fe89851400e62a8a40c16e0a22a1c44611c462ad02058821f2ee0a1b6e622e075021c22a140ab3fa26390b20b8285b87a8a07d11d00140e28b8708a87a8a0902902c5b82889c46ca2e08a87001adc152268a07c05850032ee8badc152261f03e048502d0161eaeed22e01222a1c1eeb78568a07a01398898161400cbba2eb8048b7856d20708a87a8a0b20f050042268bb9805aef408540d0713f87c03850059a11122e05008048060400540d001c07c02cfe14447113981680c048061f010015001200b3fc4711014e600c0500804005408561c00b3fc4511812e600c898140480801d02138161500b4044711010e62eee6300c0ae28b8c22380ec0302b8840bb8680580f3f80a030be2f0402e84c12a2ebb8c030c471139803d03400c002804308be2f0801284d11c442eb9803a26b98c0e616e5b444038782900c1322ee60c0b7a28b72265b078050a5110361c04cb98c0b822a1c01201854b72265b96d113981e00e0304a8bae0152dc1e2265b0122d4440f87a12aee8a8707ba281e82ac08a4122e015ade01300e62271108e0380c8bc46bbb02122e01c22a15ade1ea28c00b28b81003b98294442383d3f96eb80554080ce604c8b84b1100f3f96e5b00c8
  | 7 => 0xb31288003876e6087118161044c2f8462a8c80b01220c4603c440587c38ae68a07ab8882133940582b1100ee62eec08a48b87a8a2e2b9878e5226058ca0382a2904ce6444bbb021c2e61ea2a1c226b88781290a2f4440582a03b988a2eec0a2eb8ae61e2261297e3d0160ac4403aeec08b4e607a8a8708a07ab88a41c88270b940582a89c4403b98bbb028bae21c8708a886e507a8a0b28b8c60580e0a8a4e62eec0c4414880e65034002a1c00f3f8b205b031122e058813fd020284c12c44e600e108bcb6a2e21841408174007a03cff1102abbb988b82a104fe2f001403981304b1100e208033f8700582eb68bc0a84511078392e6bba28b6cfe1c82a05879110cabb84ce6042b68bc200161ed000382b11076bbb981c016005020e50111cfeb60282c8ee8baee1450070a281eae2ca07e4302805850e62eec00a48bc47400861ea288996e14082e607e8a828293001c3282022a1c226b8c462a82805850e62eec007c8bad81416e2a87c0a3002d07b11a2a1c2281eae229075401c24302805850e6226bbb008b8b2142e3118741c22b400862087a8a0f22922e5e816898400a2eec03985bad88a0280d5013f87c1f97ac01a014050148820a39940d001c4fe2c816c0446058520d0325e80ac04461fcfe1407c68398bba2a1c500432281ecfe899c22016e144460a22eb62ef400503b8321c22a1ea28898b22822e0e16e0a
  | _ => 0

def word127_5 : Nat → Nat
  | 0 => 0x711d021f4443085140d013fae00c87e1c22ab7a28b722620016bb80b1107c0d22c0c8161c0341fae63b80a144fe1f447112ee8b05511d002087f110c213505400793f8aeb888215832b7a28b72261f8ec1308005870022ef110348a84e0c8160d0701f8ec6c8081e4ff11c44132ee8aae28b2e01c22a04adc038788987c202ee20c4405806128348a0ae1a22c1c22a8a0100c8f2b8848b82de20aee05804204440d226e68160500804806040054087f4007c02cfe144471122c1f878040041f50013048024fe054471122a020141581001502018793f85204c4711228202ee05d05400048b5028aa281284d1105003a261f00a020140381201d04155020104f4001111c4489c45134483b8385e0aab78c22f0b2e507d1308020978b88ab1205030c443007ce6044e52ee1584439082c185060840203925c0aa0482e1f0162098220979130462f8402e8ab1200f110161f044208413f8bc00398133951100f400b22085442c4c77087128eeba02c0e178142dc308e22b8ba20446e4c441f07a12aee15080c105060840388ba8ad002c8821e978b8c4c21c4a140c22044630076e60408a394b60166097aba0c61f16c0d00e1f9a111080145021c3965d04820b945c852770b2e60100b0162018340870e58485d0525cada1fb9511ad81f0111102c200502f847400bc1144c2cc4a2180f1182c2b817110e2388462fd00110bd130
  | 1 => 0x1c01614038b6cfe1f8343bc441f2e6bba2c1500c0587f11078bb834130c2b9882038782b8021f97405ada134440d2ee0d8703b22a1d8020597413036b687e118700d0783b444b9aee8ac4c1c05405d02030781f444bb8343084b415033fa2c1c22a00ae61e44c8980e1287cb6816208802f444bb83e0d229130021c0174083e1e04ab686a110bd3f87c0d444b9aee8a0688b0721c22ae50af132283c80e00882b6aee058800f4440d2261f8161f00e14444bb8354007e208161c2ee13034108bcb681620d001d80f112ee0d0b21422a1c22889ad85b96cb82df11adcbb8380388220444028ee8b2e21aa2cb80708aada3d2dc8996c0496e2cad803c46bb8062088111228d22e21a22cb80481c22ab783c3ca285b811118825b0c2b600e20004bbc448985003a2c0500804806040040080140d001c4fe238b311c442a80a0480604004e6801410034005b3f84911c440500602814020568a01001002005054087014cff11c44048042900a05008048060080141016152274084f404471101030cfe8a8501284cbb80e0350540804300bf400bc3084a1404d110ba8980e008065b8002f0500584a134ff4003403c442f006058001404a134ff4000e5b4460c80a05008048060416e010c3415021404d4004b3fc4403c46100320d00c03aee898ba05840bb817415003080c010c1408be2f39a1404a134462ec4403a273f8801c05
  | 2 => 0xf8aa2f0442e8411207003c460d8171107e3b0ba100c91207a0d87004c4603c44058783b081131bc2a8551204a144460e4441f0ee2044c2f8462e8402a8551200f1183805c441f0ee300462fc4f132de2f00e1dc46e50680584113054035020d04c00050e50c31100e028140201001007118c341502130513fb951100f131bc128aa20855120f40303e0baeb11850390c21f445134485d8aab78ee0e444300bc8b3942c87c0d974118ec1e0822fb94132ee129822f44c118be1ac5a42448100ba2a87a3d00e1483f118171107c2f847132de2f07631810e5446038162d0405e878324fe038021f1825b0f40496f1104412b9a104fe2f0001404ce544403b9a0fc460300805004040074084d3f850e5444038be11d002f0442ec4c2085712adc03b931183805c443b8c0118be0344f132dc2f00e30b921ea29110161144c2f50214034035001300012b9230c440384c028140201201805410c3408514004ae4c44038801a0eee483830050608babb8441003e8a082158ba129822f2ee2f847400bc1144c2cc4a3c8b021a2d1180e0f0161a0be11c4cb70bce4a28324440480e1e8b005845400001d8c66096e5b011118f210046115040450200982295003cb9210446e684b1180c0201401812015034004c143931100f13070150174087e034441f2ee0d05030d033fae71322a1c2260387e0088005adb11034bb8381f0ee8b002
  | 3 => 0x401a2e0b7b90b9a2e1c22a8a0b81f8180e00e1f2f01a2e2b8390b9a2c1c22a2e22e060120f80e1f078bc0721f87c0287802015410120180140803404481a391112e01f0701482b4099804500e407e060e11100c02014048060080a0007f4087d40448143908b4441e070089901fa2a04500e4018364441d079400201f8fc06390634481f00a1f8780480600808005041350112014e422b1100a0500e1580800806005041285340c4804b908a444e5aeebc390bcada39010292ef4122a152f1402f31204f11391130462f8402e8c22ac4803855110161f044118bf400442f2e2898bb1344a038c21d88215b99118161044c1500d4083413000e604a30c440381402012018100100b118c34084ce65013f84b1100e3b0ee8a8be1c038141821fc4c2f8465c8ba100c9120aa0e45a0381311c440587c3b8be11d004f0bc1122713087128c65c0381dc460400e05c443b8e21a0ee89c462e838141820a835404fe2018200a281f96e1f0385b051110ee145021c1754017215cfe5c054038b2058ee60d025d13d400545c0161f8865ccfe1f183110ee140bf400bc110ba102e02085712880154481f80ee5c460e017110ee1e0c0100bb13ae02f4488a00e308801507ae5c44058454144eb844a154481400c0d500004fe12b9630c440380a0480604004020c34105111d013f84ae5c4403a2c0e0ed11ae03bb961f8c0142ee131822
  | 4 => 0xbe124505dc4c0422c2a44807819110d43522c380e4301841900ee4450308d5130482fb94380e48b0111200e060651139a5d39829984b60182a0705b44404024e43946422ae68a65d398612dcba0181d0a85c0ca08448e43946322ae69785db98600468a8a82f80eeb3900601e053946139a5db98b72d8038a91244429b94078468a888228583501e060a46107213d054083c218113f01820c441c8321a08667c4820872020140380340882218073f44911056e52e0140720b5022187b3f010e50186644402014038021cd021e88601cfd1244414b94028860380341046170073f44911014e50440300a0500813504895021400712444e500ebc394bd058b78e00408a138be1200602cfc2e0542f448300111108a8b39540806008c0138482f85422af02e0bd1244489010e50482f0061505813cfce50401100c14a2f12444210134080c138868bb951101021082030873f3948b8801500a0500801d04038020008740882e54fd11054028140200e0085541053408453f39511010b80514080a13854e54448b010030140200e00d021e88602cfd1244414a2c050080380203502150448b4fce54440404c1580814845124448a812b92e28ba2c5c16c0387a8ac4420c480884421d04038021184e023953f448054448a80c0280e00d04150533f22ae54440400805006010440050213050e54491100e2f0071205540852114fce5
  | 5 => 0xee588412a2541010118073f449112280500c0280e00d0415852024fd1244404b960300a048074104740050128091244403b96bc396be2fcb80e4170108a2248b05c0e0b01550415adb4000c2c0473f22f12444050b0b884ab6a2c2fa245b228e58131103e15046b8856b78a68b0be8a16c03b96894440d055410120180e00801404fc29c441500a0480603803410b1404fc11c44042e4112de29a2e8a1705b00f1222d1102a118060480e00d00298b002cfd1122c1700e00856018533f397120131122802006048041280011d00143971244403af0142f65e0d4610c2bc050bd9843b9a435170e6072e5870b601829178613900403c5b444e544f13396b78ea0d178078c2352e829448038bce5444e6072e5874b72e8060a4613900c9711219ee517677974118c2e6072e580e07b9006394611845e010060d43099e5e1843506804448e61761cb961197467c44e40102900e07868e50c02f8485e44f130102a44807819110d4350c28a8a40381e5e1843a8c2351841a80e3544e3044c120be3ab90e50111200e0606b114505d8d513070b68e40782e2e448048c0e44448b3ac5db9a610a513072e5870b6390062e65b4440402c663948b4505d8d42944cb78e00782a30448038bc8b395111787797411b9a30072e580ee401e8b018e51846122c651985d8d4240111239a5e072e58465d19466444e40108b0a40389007b94308
  | 6 => 0xb822c8a2e88b8180402489444e5af0152fc2c5053f0240cd00e5ae8bf19e20504065001501029c44092f0e5d04005002c0711101029ae01c22e8a0180402489444e5af0bf22cb72e01f819400b08b0a6044fc09444bc396bc084610d8142fa13848bc0541384a11184120d8be8b0e52d85b0a71107213b9429832678ae1c8b05d8445cb94b600e29c440887213af06684414184be84836176613945f2d82104e29850062fa5b02c04444660728b3965e0445cb94b600e210a7110221c84e1204eb82291207e8922cc997c3281808396bc2f82150540018000720d874b64fc3b0208b8cabc085122e08b078892288b97c060ca08396702f0be084b6021414fd402f8120b013c48b80748b2281322e5f0183282070224e5884bc2f812085410774001829cfc081c0bc397412d83f03740074bc00470084124fc328ed122e08bc487a2248a17c060ca08396bc2f88b2d81fd000b0208b4fc2104e5f198122f829ae08bc488a0745f0183282089396bc2f88b0be021c000504b600540018080ca091713f17d3f2288922c0604e05084bc2e2b684a8b4fc89396138848b8180f8128a014bc2e2b78568b0468a0bebb084e5a568b8180383405224bc00a048060380341500020693f44413b96b92da1422f3f396890be048180ba280522cbc2e4b78448baec11b968a0be03a4c890180a8148b2f0030120180e00d00210088b4fd1104
  | 7 => 0xaa281a22e03834e6224062f015d020e3981cd013f0ef1206802014018134080e008734000b3f444e606803012018b01700e00d001180b3f44911014e600c050088a00e00d021105602c493f44404b982900c050080480612a254084d4000b1244403b98138be120c0028073f0b815448043982f444242282f8494000a0084e2f0542e0c1120911101089398158180b500034fc210ef1122eba054bc2e012ada8a0c08aa245b01221444e603e1517015854034fd403988b84f1101140ae015ade3022a8a16c03b988944421034150560b3993f5000308467a2eba3042000a0500804806038020050221399404fd110540500804806038021550213d013f39911010018122104e0380340046e60093f448054448acfc01a2413855110900422802014038034084401856e64fd1201311229400028a04e15444240108900c0280805006048041280140d00133991244403856bc05461084138ee690dc122fee6390b616c290b11107213b98e40a40c99e2b872e6176e504c5bb90b60b029015110261c84f138c0158102144809819110a4371765f390b6394061841396c0b084292fe044446622c1cb9a5e0c0e504c5ba2ce42d829014214440987213c50309768b45c0444809819110a4372e0ba2288922c04024bf0b0155042c500060040dadc32870150243b22f112e8bc0b01e2e08b2e8892280601009397112f0bf0541c0a6
  | _ => 0

def word127_6 : Nat → Nat
  | 0 => 0x178390c2bc054c1850391a03a872e5adce405406184ba8325c44867b98e50be120b91744c1f4465e0111202e06444390e4308120b978610ee308e46106e048e5130482f8ee1f4462e39804c48040181bc4422890250963902e0618421818015000e4fcb70840b0ee1522f112e8bc44c1f2d8b8a288aa24ba17e0b08406011112f0c139815503131eeb62e28aa28892e88b97a0b0180408511304e62f015086e64fc0b5000c884ba30467880e603940018214fc3bc44150185d05214502154fc02d0013c44e601021cfd4001821010154440b2f0e602c21854004fd4039813c44042dc080841c4fc0b04f110ca633982f2f0153025e0e0610c2bc054c086a11184381701cb961c082e52d8060a45e184e40100f16d11398b88eb1339620c4a0d1780a8c238448ba0a4038c0e64441cb961d082e52dcba018291840c9711219ee63907797411972110c21cb96e500e0ab9006398611845e010060e03099e5e1843806804072e58465d3941117267b90040a51100e0a868e60be120bd1344a040831202a06444380e030a2a2900e0a978610ea8a0ee308e0610b203b90380eb130482fc4a3b8bce60111200e060b3110c22f8491444c5ca280a8111201206444380d438228390bc6106403a2a23890248e00a81829184b82da12a28300728aa248b8120fb982c018bc056e65020e073400113f0ee1a44540ae011ade15b4a300728
  | 1 => 0x1c8b0ae1ca2a890540f8805c2280cc481a082150ea8b0728aa2829034201708903312228b62245b084b683911010bc00a150ee8b22c2122ab6a245b012b6010bc007112281550400d0015084890c2bc5054022cb780c8a0185b01003ad8210ea15002bc44430a241184430d040434b408ea00d00892f0050080480603802005028b500214fd11054028120180403802005041505d400473f449110140180a050080105403802005048a053408453f449110120080a05012018041500800504890514084d404491100e0e04e2f8482f4fc028b8bc4443b8c08b0100604f3f006308c0120be2e4442f2f08a0102f00741018010693f5001397111010305022f849400020d04e2f00f112f02e0ea89010120bc01d040600413cfd400100cc4802814020120197003803415034006813cfd11011120480650415500014fc138411206815ade8a050b6a24210eebc4440600a1522d4104d40444290c21550413019400ec6d0093f0a5112f013a2ab8ae00484ab68688b22a892f021444060068a054b8a2c15ade1a228bc00f110ea0608400854890080500604d022c00e00d0002cfd1122c1a0060484e038034108540046024fd120151122a020141580e00d021100614cfd120131122800808050060480412a24005034004c144491100e8a0074104f3f5001a041121701cb96e42d80617861394ba83c5b011113988aaf01530661
  | 2 => 0xc3008512b90b6c48040540e444060ef410731385712ada054494003711048e40ec153902e06913c4c030c0210482fada2f012040548a4483084a0644541057400680300013b9030c44045041a0481580c5b005400840c854e40c31200a05008048074100340d0013868e444404176305031307015c4a211848b00d12035110543a8c312391111763aada3b838bc0b8610c015502140eb1307020c4a150eeb98340e176b68b8610c1123911122c1a44f40c4c1c1722f085111848a00c0d448150ea30c48e44445c8eab6834bc1842e0bc155021104a30c4f130703a854b98345f83e5cada2e185110bce44488a184e607015b945f0101a2d8010340600c2116c5c054308eb113902f8482f1771308312a2c044480d019110ea380ea8b2283b854301840d00f41228300be1244f131720d44804012064443a8d43aa28150bc61034038560600d3f5008b084bc0540c8c3404fc0c8568a2240017d122d821018bc0381522c3b8ae0007221c48065020e2d9404fc0c8eebc0548b504158194000d3f0a40c820152f030d040050006036b60326d4fc2b8ec292f01522a1a0008b22a89084b617c15018bc4480f8328a0561a5040000c01500b60853f17c5c032150c23080c00504b60042bd005c4fc5f0688b0568a0685f0000c818b6084bc0540d2243a886150ee0a0ae1ca2a8a224200385c0328b4494108140018cb074bc0321a0
  | 3 => 0x214fd111843b855128bc154480403806444290ee8a44e304462e012044480f81815444295041580c00500290c3110114150003835110a43a855410574000c014fc29032150c3120120180e00d0430d013f44429011130bc2107d11b9512038154443bc4c2f848e50bc2e0841f447120100e055110183bcfd410680300013b9430c4404069138c140c4c2f848e52de2f0840400f1203406055110eb410681200c010853f3940c85430c48028140200e0080741502138693f395110111307c214460f80c8b2ea3902f12055110c28b395124445dade3b838bc0c0610bc15053130ee1f446ba83e0e176152de300bd1222d113942f0c06122c0483e150c1130482f87d118b8e50bc8b448040520f819110e48b0ee150c06103e04a2a120be151840483e370488a8ec150be6103e048bc2e224151840483e890b8b944e3044c120beb78bce54480404403819110d43aa24150b86103e0480805002038074084f3f06ee5444042e81a0568a224040042105511018b72f00e0ee8b5041581803501110a4092f0150c341004065000dadc290721204f110ecba2f08aae8010688b22a89010b7084062f11103e15228108868b2dd400182c4fc04444bc068b750540084060703f04e040cb112f001505402dc0f4fc1396c1044c1c0562e08512ada61391120540e4443ba281a44f130841c3905f83e61444078d41544830c4c2f848158b
  | 4 => 0x550540850e54fa1000eb85021504e02b95118408b010b92e08ba2b1239488858200760a05021000200773e858140561344814809118768a8122150400042e5015124fa130540300b410001422ae54fa1000f120122f00615502144fa103940380b4101402080160771180140840e500f122222b8708aa288b04006838202f22bae08b0708aa280f84004a2ee381a202f21d07e1e2e01c8561f03540d000388006b8e684480680a050080480741081408001dd00104471238e1c0282022c06998045001db8e100df1180c050080480602d0220076005011204111b8e8b05e100202a8806422a04500e381a35c46178761c8202b87c6380e8ad00e381a35c482a80a048060250417880005000544911a2ae380c028140200741057408520044911812e3a28bb8540422abc8514004d1200f11b8ee644c8a0bc210482f87d118b8048111203e0644415056034fc003994004e30c4404398b88c140c4c2f84815c4a2f0840400f1203406055110ea120560339940004214fc0c85430c48050080480603802028c34084f404fce6444040e63ba2a2f8720e054610848a0be120b9134fd11c480e07c04811110183b8e43ba29120bc151840e02c1a087404fc61004211700e0545b4443b8be120bd130831296f120380400f110183b8e03aa29120ee890b8151840e0554017215cfc5b850040b0060ee6106940975400565c8505b818
  | 5 => 0x8445bb94100705e0af132d8308b61ec4861b8e20044e644ce58561e2dc5e81a1f2ea0d17003986e3883120806804a34c4c15aea071791184a0cade308ae3a4482f0b2e5080e60742cb960481c20b9406b8e20186e6176109741db96102dc1f0131238e0708212c4f130be120b22b88203c460701b1208034c4e300482f8102bc4cb600e1eb8f1201a200451307014976e6b963217c102da0696e1d986ba82c1f0102038ee519911a2d13052ba81c5d8d2378282aade304482f0b21ea2ce507ce6874e58b20481ce507a06b8e1f1865e0425d040e68c0e5adc04c488b0762038e0704b1444c2f8482c8aa0387a0701b1207c34974e697c10078b681a5b98604024200ab11b8ee51908a974e6076b701a1c9701f18603823123942b98e8ab8ee6b9804baa6001ae501c2b8aa0538e1e186e6b98048801f38e070a8128700681c0116e018802f07a61970110d21d8405f446e38341f01a1e0573e80e6804b1234cb80428a8745baeab6c46158122184a0c8800007c1e4493e85612886148801d02c1d81b3e810664461f34c8b8748aaea14a222181a128121f2f2000861e4493e8521285e0300b410001f0071244610cfae5014108bc0180e0005614c4911a220480c02814025042907c018794084b1201311b942f0071205540cfa13394102e1408501300ce522e2000f4100a05008018034080021880e54473e85402814020001
  | 6 => 0xf2be87c2bae08b2220680e08a281f396bcafa2bae1120a806d0008cfabcb962b82201050128731200e210220b07c5f2e61dafa660501c876b822e8a4480680e088ae1f39688af2bea2c2a0021281a09ada1f4fa3282237072b9af28a2da1c876060ae1f2f3402220382312184e5846100a606820020042ad00200be329865c0243597d11b8f3eb248a01a888ae0e0142a84cbc88415808888aa2f80e21500034fb11a2e10c48052d88b4fa8883e13012068142a8aebc8140281201884005054007f3e8761324a1fa2ebb0428a0aa2b81a8b04c05076bc80c04806000854022d3e8761300c02809410560005311cfa1d81202884048074107810809402221344911814e5adeb622888b971185e200381f054b8ad88b0be5ba22e5813118801f03e155041f05e02808048060080140396204473e85402812018001550414500e5cfa1000e8ba281f0801782829850200001f4fa178501580014b9604c493e84a20504048060050010448038a88881a0107a212f2b722e200441f034210806804a15058068062139420446150540684a0187c1384111b94042da8ba2a2f16eb787a1f0762039511a2c10084100800b8761e8113e87c068e51185412a2c0184e10446e501021058118801ec46068760403b3e9081f2f2e50040688409adc1e8dc1dae8bc8448a8840887c1d98e1284eb701a214fa1c2f2e504e0e8554104a13d033e
  | 7 => 0xc2007d12076e38281444c2f8482c8862f0442bc4a03c460a01b12080378ee308de0a0506188037b99130b221c4a3b8482f8442f0af1200e2801a200700101a0a00a10171400c06182c378801d97d11b8f130be120c82a828038122081b1207c378d237a282f0281f050618805e1e0105021d17410d005c8521400e068de61978290421497206d025d5001d87d1238e61880143281f006e62282101a1400c202f28bad88883e140121f0b40687abc881408340687f4007c68448142de15a281e800e60548888406850032f28bb4cb80428a8742cade15a281eb981401a202f206814020120180b11880005021fd001f4fb120501780c048061f5000000b1244610cfae6014158013e87e160122900c050081f01201d021fd00888500684ab82d83022a5ba2204a2911b98210800f854b804d40b980304a8b8800380a05009120120180200502213994008111cfa150140244804806000554084b403993e84003885118014039810815124fa1300015876e6013124fa1280c05008048062050200076e6447400411200e88ae08a2231181a04024e5af2bf0aa200822ad000101a0dadc3b22eba080bc846b822c88c468a01a040242ab96bcafc20078208240d07e5eafc6804c20040b822eba2281fc4606810090802ab96bcafc8b222112e02985e068ab3e824bc87ee5882204460687a044fa09078bcb96b82288881a03822e5a
  | _ => 0

def word127_7 : Nat → Nat
  | 0 => 0x8ac465bad8888122100e01a28200140244804806008008b50340084204473e8542a80a0480601002005041550017843124fb118154100a8a014020034080014c473e88004d042900a050080480740885402221501a30a2a144fa1284cbc80e2f0063080e0101a1404b3e84d40171118102f006140040684a134fb4003403c481300a050080480712001410c21450212d013e8400381a150500150003cfa13041122e0b7a2a8a2d88888511af21f01a02a2c20008d55011222b11880308541f8c206c481e0083b1b53e876bc84c8aae2b822c8aad888812bc8851181a1f0068a0802101a1d814020120180b11800205034007d3ec4814446000841f50010815124fa1300015876148133ec481281a8a006135021404a03cfb400411201a1f00a050080480741081408001dc474004003c48888c0068040e0b311adc210ee8bae8bc8801f44cb8a288a8c8ba2231197e0b08406810bcb04e60800b0342107c5eb04680801439820d000e01a210813e8ef118541501a5d0534084e0287d11840e6010088853e8700b04e63b9811c4606876208113e82cbc87ce644c2c887128285e0de2b87020ad83b839118c3120b6e3880202f21507cc00506186a1107a37b94b717a069860d0805c00ee387d121a01f85037c4c21c4a1e8285e2e2208500c8c23a4482b8c0e6080780b21d39620b94e60540688061986109741497230b96e52d
  | 1 => 0x2e02f0b71100e1eb968a01a200441444eb844b1103403500e584a010813e8c31200e0281201808005043085112500e5cfa1000f132de2f0502139511838200ef130be122de2f07c2139403c480e01a200ef135020d00c14004e50813e8c31200e0281402006000c341502143953e84003c4cc884a0f80c2122c0baea39448308811244d110b45dade3b8382a8c02f22ce50b21f44c424442d8aa038520f87c0686a1ec4c2f8482b80e2d03e0686a2039a1500c020140180140850e54fb11840068840307cbc8800d05030ae603803122da068841f2f20e0ee8b0803080206838b6cfa1fc483b87c142e6bca2c0301a1f878bc8800d04c30802069741f836b6cfa6d0783b04cb98aebca2a0687c030848a080bc8540d0c341503130033eae68b22a0d22203c48212da1f01abc83e8a080308020683e12ada1107d3e8781ac48b9af28a07d4008406872bc84c0d0ae1201a1fd0220880b681888d00bcc4803834610821587a2dc4a142d9118841538e0e4483b883130be120562f0442d88512ad91180e1538e0e01b120ef138c0120be2144cb60bc0387ae3c488a01a150441344c0d5021500c1400412b8e3080f1204c028140201201811410c2140014084b40448e380f130b221c4a1e9761c050b60ee0e0ae2dc483038e8b08011505400023a04ee3c46040b2b7a285bc46210820e00e028ee8b0802cae21aae0b6af220a2c
  | 2 => 0x50312a2d3f39225444b8a2ce4a24ba0ba2980e2101c088720422abd00a010082100e008014104613a2b12cfce4c44052240300a0500941004005021404d12b931100e110ba01008308c0128b8158533f2f512b922fc4404a2a1285601d0214cfc0e8401144a20ae28b2dcb9a262e01c050a4e40360387e1c2f4292e0122268b0708ab901122e0703c040b203882bd00e02814020100100020d0400d021ecfee4045112e4b80488b87f408708aae62e226e401c040b20b00e8b2f40a0b33f81c1fb906544a0201411002040040280020d021fcff12850e422d112e429a2eb8a2c89ae62e3900407e1c01c0900e8aaf4028820081001008005041204d3fc4a053908ac440300a110140380800804000554107b40c4a0439089c44bbada100a836af4070122e002020c2300402e8533f856bd44b113902f8128ad022e002010c2300422f85215af512c442eb9004a261f2e22f44c120be2db988a44403884068801144d40834e600c0104a204fa30c4803814020120180a000c31250212b99404fa1000e1f8e65d0ee8a8742f838151862144c2f8485c8b632449110aa0e45f1180e0481a1f0ef130be120862f0442bc4a5b44603a222003806c483b8de3ba222d8382005461850155021d1754017215cfa5b00e2c81a3b9865d13c06d03400865ccfa5b085119861f08015082b80be15c4a2f0441f80f123960e01a200ee1e44e3
  | 3 => 0xae5adc152261da2c0700c20a2ebd0aeb705489876b68508901c2a87805038bd0862f804e5a262181c030828baf4b8a2cb6878bb0b08901c040740f0141daf4bb0beb705489802050561da2407086032f48badc15226bb0aa8b81c038140d0821e2f40500a04004038022cd0512cfe020af3f09b11396b922eb68501e2ec8b2242b81c040740b0141daf4b90b21ea2eb707689aec1d01c0382a0522c1e2f42180c050100100e00a2d128953f8093f0ab11396028540380341074120093f44b11010e580c028100107411d04144fe0244b1100ee584402004308c0128b93f05215af42f8bb12c4404a26e581c018861daf4b7a2e20840218322b880e488267856070042008740882e4c441581c120560105211444e4812108b8074fc20887112f4e4856108b8000573f04414b9311012070060b0801dadf110e2100c61eaf48b16d4082821b921e994148422e01d3f07a21c44bd39214adc8ba2c2e96cb60762087a8ab93110d811052110af410241d8133f01c1d0db112de2e076070ae048713f0ca41444bd39215d021483ab7cfc5b044100ba072e8210b204038bd0861e852115040fd0204cfce488407444b8ae0e4a2d40a2aba0ba8b81c038102c834212f42cd040cd022119f12881410b2028080500603802005022144b3f444150a4b8046933921ca2a2e80e0702a2c8101ea2cbd0842c81003014020040280e0080015
  | 4 => 0xa1100a010c2108be128b93f056bd0c02ec4b1101289b981585436afc620403baf4694fc5e44eb70ed11b900d824308caba8b1128142e8da1c39311172ecae8e4224072d85e1883183e048402c44420070890562a2fc151881e2f4131a03a84a624fcb7b901e2ea0717236c4a0c8b0678805d96e13390040242c01c2018867978101883681c04989129761316e04810200242c4fc2e04b13c4629813128242001d110da304fc128b913c4604c4a2c07007040890a86207838044bd04c6584b3f052e6b922a87e1f3901e2ea072de36a2c621721002912994e59785b84ce6b92e422c043961f0242a81c621888b19466976100da070133f0b8128ab1187e04a2d128242c01d110db140705ba242c0243144a0480e1f444070da5b04a2018804504018a93f44a369722b87621392b616c20880e5c443607a1117013882bd056be9883604412bb0158ae21080e4aea072de620325cb962099e2cc4ae417013b98e43922b80e2c88008882e581c621885d84e5c082e60aee4ad803880e5c441e822110ba100af12012210b3128222081d110d9138c0100bae5b91120121f0851101c2084a1c87a1d8525c04e100ba1407cbd2fa620d81104a5b052b78b20a07a650ac1f0b2e49701387a038ac08b960707c62450298b3120121ec4a0881d1107c36172100060380015852e5b91110131444e5c2262007231823128ac0481007444360
  | 5 => 0x502134fe1444b1100e5c807408533fcfc0f845128e31322b3f07c0b178b88b311b2a1d85230c4a30086e604062502e5cfcb7b901f2ea071722bc4a0c99e2c881130be10cfc2e04b180ae2cc4604c4a0b01d1108638877130422fcfc128b82cc4604c4a0708610172108400180f3f80140856e63911101340c4a070013f8380a4fcb60b23ba2e70af4218b22b8421fade898781f2253f17e8a81c0a44abd30021972b62240a5033fcfcc00861e852104fcb7a2a1f2248997e0702912af4c00b340850c00393fcfc070ee2cc4a072d91285140b0002cfe2187b3f39814cff40c4a1281d3f0b20a1c2bd399408328acfe8987c890ef3f22e0e1720a44a2c8280c83812d033f8073f0ef128b22b8b20001c2002cb6502148293f04038c4abd226bd4fc2605239a2e082261f2242a8305ca2a0a44abd4fc2405238a2e0622a1f2240b1728982912c4a1ed02070b21e1b0892f40a3988b81740a2a14cfe898e02a8b21e82a5c87c8902912ada134fc89a248a87c05036070b2bd0453f8874083804cfc0707a3bc442cada89a2a1f2241483c0401c21af54081c1f19e0e4ff3f0ef128b207014020100100e00d0221cfe1e80b3f44414b98030100100e008873f80b128473f44405398030140200e00d021385402cfd12c4404398030140201001502130873f80b12c4403b98110c002808308402e84a2e0573f2f512c44e60be04a2
  | 6 => 0x90ae1583c1a17289c4a20079128833fd021f0800732e892f40cd05408573f8168b22a898ea208342c8805ca240cc4b410aeb8cfcb722c89ada8916c052d804880218091122a208ae21ae08aada8916c1a012042f4b60051108220226050080400403802005028b4fe20cfd11056028060400403802005053f84821c4b3f4440500a050080180e0080141502138873f44b110100080a0500801810010568900141502130513fc4b1100e0705230044020ec100ba128b93f043112f42fa2a04842100c22e4fe0750201852110813f173110123081c3004231844010522fcfc128b804041112f42ea260481c12cfe2005340806114fc048331280a05008040045c8c34100e00d0214cfe110813f44404c4a1581c110c203008300402e84a2e0533f39abd44a2fc4404a2a1581d408c203004300422f844128b814cfce6af5128bb110128984b4085201cff3f03e1144a145028b0833f881110c215cff12850075021e80b3f087112f414a2c2bae33f2dcb6a2c89a24052f42088007087110088a8562bae2122e08aada8906820810bd08607081110048985607014020100100e00d0221cfe1e80b3f44414a2c15af4075053fcfc0222c2b88089a2411444148128a80a010102180e00d04118093fc4a124fc054448acfc015028aa2411444148ae04a261e80a0201403803410554084e014fd128111122600808050060101020a24
  | 7 => 0x8433f4462e04a2c0b20483c0706821cfcb944e1d8cab70bf1184a2e0684122b1281413812070711144c2f8421e2dc2e8c51107ce48120381c2084ae680c020140080e0105740cfc14844e4c4404c4e200be1d8861c0551203608b9112856364443b0701501c034fe2050221988e401e308571144f3f8142e8402e08615448b681210c6015b9112836074443b50513855122db3fc4a050860d842e44443b05610854100073f8800350200052e40c311013138c0108be5c077132da2e88604b9089c4a0705610054030805b00621cfe0c856e40c31280a05008040054144a008c3408533f880e444404885120ecb9834600361c174b68b82c8eb110be20b908a8781c00c0703430cfe2e0074084a620ea5c87a1117f113905c8421000603cfe000eb40852e4444048540744a1f0828b4fe030813f0320a056bd0c2005031287c074fe0e2d80c8b33f0ee21af415a2c1501c0344a21a2abd0323088312cfe2ba260017eb6080072f4218368a8823b44a2c801410793f81c0dad80c8422bcfc3b056bd22a894ff4080c0003201886b60833f1722017e158c20744a2080c21a273f03206056bd0c3408ae8a8008944a1a0873f2d85f81cbd0820f226200b20c800075040f2d82b84112cfc1a2f415a2612c4b3f4fe070802cb2ebd033408288acfe89a243bcfc0c838201728b0b312af40822d3f2263b2240d9728ac4a2baf4064fc8
  | _ => 0

def word127_8 : Nat → Nat
  | 0 => 0xe230077130422fcfc128b820c4604b991281c158401504a030833f88001b993f032158c31280a050080400403803128c340b993f844204fd110125c854100b8030013f0521139630c4404c4e302e02fcfc128b820c46e581221c4a070561050513ae0154480388712834e5cff1104a3a8561504a030873f88001b973f032158c31280a040040380202505128c214cfe114fce5c4404cfc214482e8401f8b8128b3118131283607444218ec104fc2e04b138c7118371844a04810070a5110ec4e8ba10085120c45b8820da241f44a0480f1101c3b054074fe205028b00d110820baf4158c33fd02070060e444b78ee1eaeabd0868b0aeba842898120188007083112f4218560dade8a8ec108402e4ff408873f01c1e813112f414884898805b04414c448a83e04a2a10086210b9412de1c81d3f0fc04c441c2f4e680c2b96c3084414c44b92260f812108062e2de1e818202f53f0401d813110c66100740852b7cff3f16c0f84513adc2e886e4c4a0dc44208ed13adc2e8b8128873f08311842e48131283607057110ec109722e00c004fc14844e48c3110121280c2080621b933f032158c31280a05008038020150430d02110533f3931101313a2a0f00c21ae8368242044a20c443087913cfc3b446ba03c600365d2dc2e8be1dc4a293928ac442b988e58725fa24e42d8048682083c0700c018865b0c2200565cc44e4c4c2f
  | 1 => 0xf12b8e1d01e11b9a2b04cb7b9207a2c6280e0ab8e5cc4a65b965c040e68c0e487e0522ce58a807b8e0818a2b0c21fc505d80e07a2d118a71282035c511397035ad8368140817c090a8298462d8bb11b8f12a271444e5c0a88980f11820078740444a35848150082f80e030b53fc4b11a2e10814b8ad8bb22c8ba220f04c0401e2d0141caf6b8adcbb22c8981e8b8148884c0c8b41caf6000721fcfa1a84c8baec07a262d3240507213028bd87e000722d4fa1904c0285541000020491284111cfae581002872040054107e108093fc4a8884d11814e5ae1408b40d0853e80e6844a200080500400502e48b511c4b3e880b92e0e4a2eba22a2e81e88876200100a22cbd8760201401001408b4e4cfa190854100010c4b3ec461381402d040500820076015031281111b921001e158061404d3eb9203c4ab8a2cb72262d8142938e078b40d870bdae2b80488b0708a8b60422e0f0a4e381e2d2f62a2e05c8540d5033f80e2d01ee39a1128a80201404005408002d4ff11b8e1a9720a0b42a19603cfee38ac078df128a8020140400402d02000b53fc461922ce380a2d0100100941048180013fc4a05446e3a2a028140250401054165020004f12c460438e89d05408b600004308c02f8561404d12b8e2ec4603a26b8855120ba100b812b993f4462084204c4a0d81c15c443b17210854100b93f88003399408013f04430c4404a
  | 2 => 0x62b0037b8ee5adee481e6297a0d07e5c80f129a02d050378b65e2e23a03230850300b4e6086e3b96e48ac1581e0a08662b8ee5b921f86a0a0b4140b42f8462ec4d12446038802182807c4a378e82d0c237850628860a0de3a0462f8ba0381e218b42b0c21fc5032c460a00e0544a07874378d637a2a2b0be1418a1f828308be11a27140a41cc4c5c4460a00e0401f128de338de898e22e850628294097410cfe5c0401400e2b01e2d0de62979408425d0405c01e1fcff1288662864378501fad889a2205036078a821af6b622a888a80f0500422607886bd8860e4fe079a01f80f3e8ee1444a9522a89a221401e21af6004fe1fcfa1a8502180c040040004802cff1284311cfae601403014025020000a1544a104473eb980400c050080400421d021fa233f85007adee384c0798abf0345c80e1fc4a680a8bd85462870bf04c5e0da118c2bd8546284c1c2fc678da118e85e0c02dc4eb744403b922a44a1c01e118701faf61418a130da11afc650debd8506287ebe04c358c25e046bd8506287ebe04c358ee690465e44eb60ec0d820308d611af6050b71187512b8e2eaf61598a1d2f8131783584630af61d056be04c6284635880b7b920784c62834e3af85c80f129a01fb9613170100c2e48142a39607b8e080ac6298a5d8405c0c2e62dee481512b8e1f82013046301791380e07c4a080a6358d6e58c05e44f120bab600
  | 3 => 0x98ec2f8321598a305022f847138a41cc4c89971118320381007c4a3a0ce3a226158542e83262d025d0433f970150560381e2d0e862d05408425d0545c01e5dcff118866286a3a05607ad8888142a03603886022f6158ec8aa2c8a81eb6222040a82180e012f6898568aadc8996f1183203886bd80015a223a0013f8ad3e8641580a0181001002005053f887128433ec460500a050080180200505408861044b3ec460400a2a0140250404005408873fa221581e050c28a8a4144fa132f6038c21281e01cfe1404d3e973118123081f3e804300be2d84c140babda26038061401f3f8353e84c03c4a0ccfe000ba130502d8e8bda22038013f850134fa1a80e078573f806144fa1300f12cfa1fcfe1a8c21401f3f87e028b53eaf621a2c89ad88881421af6078081a8563b22abda2c8aad8888102181e0106a89856b822ab705489af6158863a0c2078008886a004fe1fcfa1a85021d040004312814124fa13008050000150289c462d4fb128405c8073f850134fa1ac4a038080501001502000b53f80e8886a21ade89a220780e0ac4abdb022d04c2d2de8aa228981e0382b12af6c0886b7a2a89a222d02a0780ebdb022181f3f8382b30203cfa3b88712cfb3f84c028b4e600e194fe078ad3e82abd886e64fb3f84c018b51280e378700a0ee0e178b60c22d8b4e38861f842bd856628501c0863b046c01a2378ba21af615850
  | 4 => 0x8cae4adc2f8a912a2a0381407870118da11a2a3b0562f83c628102e8b60403c62a22158bb138c01cc4c118bee48a42dc46038408883c07c4a338e8888562d83c6281002015408001444b11cfa1a01f3ecfe0307e1aaf60d0503080207cfe2d038b687f3e8343bae6bd8868b00c07a2a21cfe1a8a4bd8560d0c33fcfab9a268880e00974b681e2186abd836158ec8a8840081e5d04c0dada294fa11c4a1f8343b2e6bda2a00a2c8aa2203ada2181ebd86a0f05689cfe1f81e1acfa1400ebd834218571384ce38362902035c4a1c0ec1c87513071118185f03c15b8e33887128c21d0b62185713855122d803c62e383607c4a118ec290b7138723044c118beb6446e38ba040861580e8983c3081f12835130554080c1404c01cfee380e30c4a0281402010010c3410014084c144ff12b8e03871130551200c8b06b1185015833128e8308e81c0325dad83b838300b62d38e8b0860303312887118c23a0a5118425d0e83b036bd98a2da2a2f857138e8b60ec0c9800d9742dc4a2f8702938f11a2a1c8741c44c0c80d11a26060ce218563a44a30a2711b8e3a2f6628b6150ba158a430c4e1cc4c1d0705c0e8b60325f03d118b62eb8f12a2662b96e480e00c4cb7854158340c81e0316e5c886308e912b8e5d8b42f8462ec6313081124460383207887128e8378e88b0b4300860c856628c1138ca0c80e0501f128743a0d63a22a8
  | 5 => 0x3340b1804cfc0eb8e2b8e9120805c0322c8113f076e38e81044a2bd0211ae01ca2ab63181000e1503ae38342cc4a208080506203803408582038f3f0540e83b1200a0500803803410b340876004fd12840e38a4b7846b80728aa4d1244ab607a038402c83a0aa2ce38440300805062038028b5021638f3f0520e80c050080380340876200008b4fd12840e38040080e2bd04018461dcfd1244ae381402880038020250411862004fd12c480538e8a80c0281402504205021404c0044b1238e0387eb8855120711139803c6215836078463b0ba118bf110b6e62260400e0f01e1a856033993f86a0184d3e8c203c4a300be118bb13055123981ac46038560c81f128e8003993f84d3e86a038ff110b60444a038480788629444030061406b3e8a430c4a0380e0c81e21c4a290e800050294fa1a80e1f8ba2dc44038b40d81e218ec2a4fb13c45128a40d80e0401e1d0ec2944e204485b222038371281e1c0ec1308615c4f128a40d8743b44ee4adc1c4442180f188560d81e118ec1400c1a806133933e8c31280e290722f8462ec4ce4add1180e158860c81f128e800050133933e86a038571383c030860944aba0da308a412174118ec2a036bd98a2ea2a2f8562a44eb70ecba03c600365d0bb128bee48a48a8743022c0403c62856e48462f8b60383c078b4218e28b0ee158c00f18a040742e8462fa2a0403c1598ab90c113
  | 6 => 0xa004481e80a050080180e00d04205021dcfd12810100874104e0e840308111205340844104fb128c20408740856038800d4fa0e84aba0ea15087415020c8842003a3a05421d0400085408813e83a1507ce5adee41721dc4ae60b2100df134461f0285e2e23a032308ae300b2e6080109741416eed9c0e5b902bb980e8540a0b2200425d0505bb96e4076e60800a07a10179130be120b8128af118100e8b20a080378de218ee100c2200a037c4d118ee2b8482f84a2e0102803a2c8801e071130be122243116f120100a03a2c80e1ec4a378cc5c8de890b81407a23828040523784112081408105e0425d4fc1416f128283785210502109753f0505b83a5e0762007a37840b7b8e5cb91128b220876139765b398e380e2107a08876110d8300b65e44f110102107c0e872128721d858110d81287a1f050be994378745cadc118e0112f813196128d61e04b3f50401854e5b8f128102bad8b9a2220814038840d874130af12842b822a1d31c038b21103220880000501300f124fa2080e0281402004005041ed022bcfb120448ba2ac7170b9a23120b21f80e110281407a000821fc493e850112e42b876b8ade1d22e8b172b7170b9c4a1fa220500f120201300c01006000511244b3eb901088341000e404312c493e84c0500c028140200601001410821ed021144a03c4888ae08a8722bb182c8400e838218801e852115041c8
  | 7 => 0xe42291107c02812038020180400504170554044c0439089c44bbaf8e42fab68ee16814bbaf8e42fab6814168860300401884b70833e972200c215d033f4fae680c8aa24888c213840b922c2c8101dc4a1286c0b8b21a0100f19a218042183cb704f3f4fa5c856104fa5ca222c84e1044a8903c04078012dc100760787d3e810208c41298a03086213902017e15cfa0785430c4913adb110860503712cfa20390120ec150480300414b90204fa308131204e159700300621840e44fa308111285621d0200080e44fa0e85402814020020050430d0214c4a104fae40102cc4f110ea3b2e60d1800d8745d2da2e0ae2fb9020a2a1e07403034308062bd02129723a87b12044e400c21b8e2101830c4a150481500c11172010533f38e048c31204a030860184f3f38e040c312d042180a050080183a03803408840044b3f38e1500a0500803803410c200053408453f44a0438f130731187c2b8b23b8385dad8300b68b086e3880030b341032308045c0803a07712840e383ab7887410c21004f3e8540444b4100a0500801d020005112cfa2000f4100a050080180e00887408853f44a8885414d02110413ec4a1500c0104a3080740852100453e8111280a0500803802000c341053408453f0413ec4a0404a1550214806100453e81112c485c80614d02110413ec4a151720185540852100453ec4a04080000501300f3ec481103
  | _ => 0

def word127_9 : Nat → Nat
  | 0 => 0x300202012018100107600224e650012cff1344403af8e6300c22e205098260460280c2f048100bb3f04c2e22ebe0c030c4d11014e6098120463000a018c2100bb3f04c2e2f9133982f015112281d854b683621cfc050206888311076010100380221cfe20807134fd11056e50040400e008861dcfe01c4c1ecfd11052e507a0280e00d041705401cfd13444043941100c028100108289504144fe01c4d1100ee52f4be394bfade3b88c0508c11806030c0120402ecfc130b88baf82f0c313444e50142304811806028c2100bb3f04c2e2f82f44c304440522ce52de15ada142e88a224e4a2c968200e01012054be50415d00b6836150753f014e482068c44b8ada12a2cba2248a03e048201239204054be5053f501134440422eb8ade158748b228e48ba95ae88b82015224038100d2f9410060480e00801404fc1d444152e4b78441d22e8a0bae480e890200a8108b2f913054030120180e00801400748b4fd110480300a010068a00e008014105614c4d3f393110121680c0281201d04010001450012c4ce4c44038aeb7adc152e6d3a2e8a07689b900800e118381f2f82bae2b7054b9a2cd387689b900f84604a2e0800e1f2f93fb4e2e2e01585403500128508bc4d1100e1f00a04806040040050400d002b8773fb9011c44018121180204004028001dd001f44d3f850e422d1100a1580204004018014105212cff13012
  | 1 => 0xe080473f00a3b8bc120402e84c2e444be0c08b015410bc018200204811cfd400365d444050c2080473f00630048100ba130b804c442f2f8052280d0c2038ab40224124febe0ea13444055042f0060804c11808124fd400140cc4c02812018105d0040380341500118af3f8493f4440544c2bd040450089846be4fcc384911014b78568a226142da892dc3baf8200211100a2b8368b2e2be22c8984ab6a24b7013110202b880018368a44d4100540075110c212504085000d874bb0046b0493f4441daf889ae28b056b78842ba28b72263a80e202f808444008460da240181203802005008b4fd110ae010101580e008073f84414c4d3f01311228018120100e0080141055402273f075110114100540046898af3f30f11048e6d0513500044fc124454150011cfc2bc44898140080801812010101d2240050012cfe1444d1100e5c2f81218cc0846380c21d178132f812302630e01184c1d0805e2e23ac480a834130c2382f8038c11307911398130ba10179120151302a2b021110e0380402e978b8c4a2f44805399110780804c15854e62da2bd000e4fe1d9a2054fc080ef112dc152da128aed387689a2404a2e1f83ee60aa082f8892de8a34eb70541da262b80e8b8aa080341faf8028060480e00801403993f4442b80c0180804004038020022815b993f845134fd11012020120180e0080015399404fc29c440405a0
  | 2 => 0x4405080118b821055122dae444c0e0ab110ee2b8762a84615854b68213fd00211811118ce403620055124442101e5f83ee40d4308ab130802e8402e08415448b6c4c05390080aa0e4443bd042a8af1385712855122db40036034fe12000e40c3110142e081138c1120402e900b68c2e4084150bc0544c04a28128202ac442a80a048060400400d05404fe2b848e44440508011885190551200c140aa0d44d1107e308eae42da0d22c3a87e3b850be18c118b8300382b847190505d8eb120eeb98340e2da2e07e3044c2ab911122d415013fb9815b9421392080142b98cb6008202da0d834030465b1743a8c3113902080c2ad001d8200d0c2022da1184c5d036630ea1d18111390200471904b11084154480d00c3501e2a879130ea30b90b684c0d0468a0ea12af8630b81e0562f0ae5c8eb122e60d17e0fada2e4442f0aa1e228e444c2a88712c480544c080351107e3ad042e841139728a4481e0142a8351302004c443aad88a2268916c15ade212dc142dabe038054442000a3ba2cb8a2cb722612ada8916c3088405012b62f801c44202293fae28b00cb7856212dc082288996c3a81403ad8200c200c44be2240539a02812018100100e008008b44d404ff3f076264440180a020100105603802005048a0533f845134fd11012048060380200504155013f0a7110100080a04806040041d80800504890514004b3fc4d11
  | 3 => 0x280565c8553f0505b9702b98d110ee2ba28212268901415c460203620021112f80e2e03ba2c100874022cb84fe210213f015112f80dd0410009402e0064fc1d2f8054440d984318802a87e21055124461e44ce507c0e4443b8802e8402e04ce508415449118ab1307c05038084443b8ae154460d80ce50013f046120c3110142008513b94b785512464050200387f134440d04c3a846028100380201805410af3fcfc1239511014200aa1e0551207d1187e0f80c2102f132ea3922d110c230a2d133940f8563baf830038630bc2a976b78ef1207d1187e1e2ea0f8382b8c1130bc8b3951118c210082bb98e4c46e42d80503e0800c5d0365b0c220444e50bc308c06322c0f8522f448100ba1f446130b88b394050522ac4c0f821110e48b0ee3018c1b8121304a2e2240f98c1e044890b82e840b92de2f4483139511014038201f84c350ea132242e18c1a812050120818c010100080e01cff3f048e506f110142309a8989e0503e080ae635041d856085011118c1d037128562f2dc2e04d194471301408039110763bd041d8361597511d00030013f046e48c3110142f44eb73922ea28304651184c2e0c20544c0483e084441d8751385712add190141f82003b93134440d04c3a80a0480603802015041d8c3400473f393110154100d404460803c308093f1741d036631801dc44e480604802038054103d400773f046e4c
  | 4 => 0x5c8533f97010050038ac298223798e5e05a1497210170088df404fe1f18e19872142deb62e88a22208810120382b080beae2b622cba2220f84804822040ac202fa2b00140446204fa150481022ec82e88a0222b0808b01012028be8721980c04806010ac005008b07311cfa120560300a015040005311cfa1c81204806200ac120051350111810e48404dadc152261db8e08842030acbea2eb7adc152281da26108aee38220e0acbe8064dadc152261db8e8a022108ac032fa8bae2b70548b0768983e10812e38ae088acbeb1ab8a2c01072e38a8898221080cbea2eb8a2cb78722c0a88a03c108108b87689b8e08afb1300a048068b8ac0400541500000733fc4610b8e1980c048062b010015001c8008b4ff11842e380c028100100615d04148013fc4d118128a38e0281201854015042a05e00501134460438e89856154460d80ce60013f046120c3110142f0808a055120402ec46130b830b981f013130142a83e210211107820084b8857128551201403b991944c0d0211104c3a81201810038020280430d0011b993fcfc12444055013fcfc630080c086200ae5d0385b4443b8ba100b8134fd120ab118381f44c05012084443b8e5130ee8a0562f18c1b8ba10225120c45bc4c0e01403879110203b8e03aa283ba24140b81f98c2c9e34017215cfe1d970154fc5b850050203b98c26444282263b838080ae635013f82
  | 5 => 0x29703a2d80c97c0f0a62d8bae38ae898722f0442e84f12936204488b00e2c88608833130e8378e88b0ee300321098e8a0ba138c9119724d8811200e0c82204c4c1e8e8348e88a06a108562f032638c02f045128c613a262997003c660c8221c811130e810d045dd005c8573f9701500e2b8223a18e16c4d41176159724d823404fe20170e6c463a0726384220afab8c4615adeb62220400e2b86c01226210aeb8a2cb7a28b72260888221032038003a222be80a020120180215001410a817d01130413ec460400e2b00a0181341010015013f8ae168222f0061404a02022124fb4003403c4c0281201c4604004000c3410514004b3fcfa1080eb886c8b2de8a44620ad888810be82201072898841cc4cb88e8b7adc8b2288988221446be8c20880010a220181212000010541f50089c4d11cfa100231307c0281201b9a0400541447400001ccfe03a2210872be84863850c0178308de1cafa12076c00506386c138de2c978b88e821c4a2087a2b881120840a032308de3044d11b981417214970100b220b942bb922139808828e398e638525c8405c072e5446e4c4c1f084e3828140bc110ba1388712c482b80e2c88008c4c0a0de378c22718e140285e0e83b8c2378281418e37887128442f0811204e2e8eee60b2e38ae038a008c4c2f04489c4a319702980e21028088101cc4c378de898e2298ba0a050638722717810d00
  | 6 => 0xba0d07e2f4fe3ab002c850e6a2e1ea288980e020022ab94e4b021f8a40a19c2e0bee422a1c0bc148b800808c0500100bb3f8ab13b91110be1ca2ae6a2ee58708ab920380600c442aa26c08b2668b82f3901ea281f5022f842048502e00201cfe100ba0a8862ab0214b902f3008a0a4bb984238100380400b9a8b872e58708ab941ea2824302660b8e40ba0a22631d0340010140b800804108be148bc1dc4e20300e44442ea262093c2f0442e8b615c4ab744403c4608b93130383b8b71100e1e8222a06a110a6300bc110ba1cc4e15c4ab700e20822e4833130e80281201c4c0100030d0540050e4cfa1080e210441384a150488a2fa1598e2e8bc2f04512a2c2c8860383c088b01b0c8038120887a110b01b0763044a110bc3d8b71180e298408883c0884e1cb9a1280c018120100140050e4cfb118422986c2087313c4615c4a212260617c0f0cee38c3130824f0bc110ba138b71185712855122d82100ee3823130383b8c02104e2ec4f122d82f00e308551338e1ea2808844298c0208442f07313c4712ad82e80e1b056e3a260884e02812018100144630d0400051404fe12c4ce380e300765dc4a210551200c0ca2c20c4d118c23a22ce398e108e83b850be8c02d8385d8e82c8871287a2b88112076b60ee0c8383044c2da2d11b8e208e81a8428a04abe856638b62f0a61cc4e15c4a0c80c2081833a27130e8308b11
  | 7 => 0x4e6a2ee58728a8951107ce4224c119a2e828e48bc8a0be108ba0100740cfc140b80b304c0086e48bc1ea28150c22f8422f05201002c05034002d1107e1f3042e8b889392142e67cade15a281eb902e00e0a00c293008bade1587a8a2dcb9a262e3901e028050a40d80e1c300b822a1c006b7054898b81e3908a0280322ec02dc15390b9a262e0780a0120f80e2d07ac02e01222a1c1f2b78568a07a010b829390898280322ec02e0122de15b901c22a1ea282e0b28b8280403c038a4c000e0500804806040040044f40803400b33f8a0e44441300c048061e00204004020014004913cfe053908ac440500815802040040180140c4f3f87804b908a444030140201203802018040005540c4e13d000439089c445d88ee58702c886e5080e49a4e422e0aaee308160a4441faeec0390c0ada8b8c21408e1fa2ac0b000a042140ec1c07cbb8522f300e4302b6a2e308502387cbb852143002d06e0a07abbb00e4302b6a2e3085023aee89b02b6840c00281406805d02e58873f8803103403a2e3a87e0a87c308500a300678b223816e5886e507a203928bb90c08c20ac4e0a08ebba2a1c1f28a07a89b020080ce5856e5054e4c44038282e3908b80e8b80c0088e0a44ebb99ee58708a8b221b941ea2820392898a0c09a4308b8e42ee05d034002a0080c140422f8b2148bd3f8402eb028b8b830c44c0390e408f408422fd0010
  | _ => 0

def word127_10 : Nat → Nat
  | 0 => 0x3400bc148ba100c2030021f87d3f838e6b10c00b81422423b0a8a050890b8c00b23a8ae21848b8056b7ada89010c00680a444010800e2262cd023a8a011ae08aade8a2dc8980ec002821c44200020e2254022821b10014fc890af110a020226020140181203802155021380513d013f01111226c022a21a28893100106940d013f0ae8988140a2b4022821cfe8988003b10008b3112242839a0080a020140181201010890014084d13d013f84b1100ec280e00b0140a2b404fe202262844e8a2242c8560e5013f084e482869444b8392b684a8a22aba0ba8922e0a0120f8102130140ae0b7856e4a2a8a2e82ea2e0a00e0d22404084c00573f0334008467c4e20008050060480e00c4f40885400053f4441539203012018841380e00d001180513cfd11014e480c0500803803408441580513cfd11012e4a2403014020120184b40d000104d13c4403b9340b9740086e53902b8733f02c6922ebc0c206028202f08a304b73000a0521006e2e81831d0021cfc0b0040422e200763082810300bc224c12dcc0028140ea06502e5d0021b94e44fc8b8aec10c20b0282002913b9621b948b80c010728aa28e4224c10ae690c22eb92200194082c0100c108be148bd3f0502e500c122e2e8c22bb0111393408422fd00148bd3f0502e03c1a07620300100bc148ba010081dd00140b8c04fc2bc4ee48bf110708aaf06209004810018
  | 1 => 0xa0813f2d80c838308c20300a5d80140d000a0320e4feb64fc0a44e158541f80d400868acfe204fc0c820c00c230d013f8ae8a226890013f07eb644e21828c00800da2a3b0001f829404fe0dad80ccfc2b8423b44ec022a2c8800c8541f0000a2d8c006e0fa282182815d0313d00030873f2260c818c00c3400c33f001138862bad80a3001a03c898800c8c2000280f2d82bd013f04113868c02262cd028aa2889801138860c828203000d2d8890eac00208a086898ec890365da2b138af408513f8800a3001e832c001d40a2a89cff3f2241b8b20c83e201768a08713b00060ae0f17620227138681487f3f8282007c893000cb0140d013f8168a8868a2263a8b20d0805da25138322bae012086b7856b6a24040281a00420226c00b33fd02b80463aadeb722a8a226038282188030802893000100a05008048068980e008001550213d0113cfd11010e6a240080a050080480604004005021350113cfe12c440382831d02108be21d00158533f0041d8bc140b8040c2100ba89b000a08021d0015cfe150ba310021f80e3a8b814224c050215852150bc0185021cfe200013f5000a16d138325d8c20a01402012018100100e00d03400873f881114fc2844f138400e30020068898ba0a4440c8500e0343ab00890b80a029408be10d002f0523080c010773f0502e39ac044e2e841112262404089b102eb001a44513d022f84
  | 2 => 0x1c453f0a0e48385cadc1003c0fa28200542eb00159942f086b90cb12c461c44e1a1040504e0a0421d8be108b81444c322dc2f446e487a8a444048282c052890b82f8422f052b944d12adc2e8c41a07c1fc44e480e0a051408be10d002f0522e050040b13f44e650401a008050060480203d021b44f404fd1103c2007015c4513055120aa8a10c5f83e2181ee40d430c4e6504210502158540350021800204fee403830c442008615c4a15448b6b91138151b0360a0423b05712855122da055000d8873f8c220391138423b08113448404442a854320c20484a0a07c148871305712adae444e1d83c0a0681019414d0215854030874016c028813f832e40c31399403502108bf400522f4fe100ba2e086203900e0c3110a005008048060400400d03400873f880e40382007a2e44421857128551200c0d0c23a87e5d2da0d0ea3b04c118b88a8701fb000d9942f8ae2c87a1d8ea20c4a214483b2e60d1800d974b68b9110be1c3908a87e200711144c15448030aa128351387c308ea1c0451144c3ac483eae60d17e0f8aa5cada2e07a2f328e42281f1703aada140340f0802e226c0054650ba1ca2a0d0cb1113820c4a2144840814130283a87e0d445130c814c482ac6c40012128283a87c2f8424e0bc14a2631c4c20c4a5c0760d44e04029110eb408be10939400822f0533f8ba1005003834650eb4080b4000c000873f976
  | 3 => 0x80805006048100100140802205001f4fee44441407c02812018021301001008005040cd00124fe053908ac440c80a0500800d04040040180012853408813f812e42291107c02814020120380201804005054086813d000439089c4540d013fb961c0b221b94e49a40d017112ee300800ca2d41043404fee6394e49a22b8341c0162f881112ee0ca2ae40682b870e6072e5b940d2ee05c442e880898b20380a00832bb994e58708a886e50828a392898a0c3444690c02e0808b390bb816c2832c30342e0c0e422cbb81740802028422fd002c8562f4fe150ba0d30c2e0c0e430a8b2ee8b22803b90280c02c8e00380800b98e539289b0c20032688b82bb902fa2a1c04203b0c2e0bee40708ad04300bc158b800809400542ec513fb0ae40bf110728a8428aa26c30be168d82baee8b0708aa260c80e01802e6396e4881110b82cb902f22820aee1580ec30342e0bc20b908a5022f8422e00201cfe150ba0d30c21b90158bcc2a28bba2c15a2803b90268bc1a8d42baee610688b0708a8828a00ec300400b981cb96e50b8e40ba8988010d021580d40086001953f3920e0c31108615c4ab7446053921c44e0d828108ed1144cb7446e487a0f8281b8531144c2185712adc03b921f8340a0503a853408561400d40086029953f3920c8c313d034000c0c8422f886148bc0a4fc140b8e49940e0c20cd0205008048060100e00d002
  | 4 => 0xa02228e4224c39a43022c2fb962bd0540226c3cfd11080e58501ed020e4fe201a5110860c80805004045021e80e00cfe018813f44414b941180a0400403803414fe120062bcfd11014e507a028140200e00d054084e018693f444043940580a05008040040cd0489502134fe018511139403d02e5b933fcfce406e690b20c81c20444bd0c021a2d3f09a10b98e4b9068b942baf4070be204440ca2a2bb981cb961a394e42f4074442e88089994e5b92e400a01a2a89a242cc44690c0200bc8b3942181d408422f8542e8b80180b3f83f3f0b22f0c0c2b9421a2cbd22c268148980801b98e422468c442fa2a2f3942b8c02e85401808c2d053fcfc2e4502f0722fc448a870e550540cfe0385601802208c0108be150bb140b22e0bd11224c2b94075033f8822189a204fc2f032e5056150bc0186b3f8801bcfc0c83ee55048ad001304e0d8a4e4cfc0c8fe68c440a0100500804806038028b03340d00014fc28444e480a04806038034104e0cd00010473f444053920700a05008038020cd0540852010453f44404b920580a05008048060cd0414503400041344403b922bb901c9a4bc0181a4443022c200ae65390028041ca2a8a224690c08b0682eb92200ae62390018048b0728aa25110ba1a3922f228200562e805410814006c104fc0c83ce487e1c0393f8801f032e41a51104e1f8702002268cfe3f078e4032364440c
  | 5 => 0xc5c8bd1139220228108288b4fd400b00f44465068e4d04b95001d8321a4fc3f4441c30ae480d4103d400773f0805b39210503133961c44ae5448e488620880b616c301762e2da0e0320d4448b39113b9912b95123921c084b60b8208805b2da5d0be0d8320d444e422a1ad0313071122d82e0820f96c2c8805c8bc0d2db11032e4228e606940874e58721c394208b80f2d85b0800cada5c0bb11034e422602808048060422a0100e008000cb99400473f8493f4440501c0181402010010320380200228e65033f844204fd110120600a010140201201a2603802000334084f403993f44404016028020500804806040040c800893994084d404fe12c4403cfc28042e5392e41a2e60ae0e3000a0be204440ca2ae60ae1cb961a394e4038c0029110ba20226c28bc158ba150c002809404ff3f0b914073110bee60708ab0010a2a20226c40be398af408be108ba150c0028073f8b80e4fcc430ae60bc20a28c030ae609a15a282f06e395022f843400bc15cfe2e854038c0028022cc502e444e60a089300c2b988a0a0890b82c8e141500094fc1d1ac36881110288b012018100100e00833404fe020813f0a1113960700a040048a00e00833410533f844024fd11012e58120180e00d040cd00020753f444043960580a04806040040cd04142254004b3f8091139603b9421b92e41a40daf8084443022c2b99428014e5086e48
  | 6 => 0x1d05408000d4fe14c4604a28e380a05008048060103541082005034004f11810e3a2612d03400b600004300be158bc1404ce38bac300e898420306c0050021cfcb94440f22d4108403500001043f0713f392b94448ad0540084062ec0f0740dcfd110546139605008040040380340cfe1eae401cfd11052e50040400e00cfe120073f06f11014e50080500e00d02138073f06f11010e500c0201401010b9502134fe018511100ee55054004c082e82904f3f44463036e48080500604a2d4086c038034000421cfd1103ce48060480e00d04b904f40046014fd11014e480c0201403802b95021100414cfd11012e484c030080500604ae540d000104a1444403b920d355400201c0853fc441318c0db90e6028214fe0ccfc1c4440db008a842033980a5001dcfc0cc4410300898401fd00e58873f8813f0388b0334150031cfc100a4898334007e0a22d3f4440d9942bb97412e540018294fc0d88031c44613960ccfc10b98e4878e403e212d85b0be5d0bcb78800dc448ab941ac4c01c481f446c2ade0a1942f4442183ee5073120ba15446018b821032b786e2f070e530b1383f134485b806208c0108be150ba1586e03816b7ae4608bcc2c44e550210d00060873f3920cc440e2f08b505400181c3933f03311036bc22a2ba2a1ca2889086e403cb616c302dc5d8682ec44200388b3922ba2c1ca2a890680f2d80f96c2ead
  | 7 => 0xf04ae6396e386a5bada2e8b2b71722f446e4a28208b340c4c2f847128bc15c440106c2da2c21adc0d0ba1a392c344f12c44010b61c2dc0d0462e884e4b0c1b44f40c4c1c8be11c4a2f0560396c01222202dc150160f1822eb92c34fe0b8aa1f4fa6c0e420c46028080480604004008000d22ae6500124fe10cfb11814004fe1fcfa1a81202804050080480600800898354084ee6500104fb118114087e0500804806040054007d3fa22140353fa28134fac339812872004fa2c84c000521ccfa1a8120d00a0480689801410480208340446104fae58100d00a04807410100107e10d00020833fa221301511b96128bc15808015002d8513eb0c2f8ba03a26e588012cfe02000300562f0542e8502f8b6c3222e580e000353f8793e8521280a0400400035410073f87c10c473eb940500a0500800504018354087d118413eb9404016028140201001035415021e0061f4fe8884a04c46e50bc018513f80e134fae50821d179400820dcfa688fe1dc47408760201401000e4cfa2c834e480020d01118433e84e0500014876e4cfa1a8120d00a020154101201d021d8054008311810e4840130be158ba015021404b3e80ee486812d0001000300be158bc130502e8b688b0ce480e138834022a080702b9a33f9b2e383435c474080805010010013fc46e38b20281201834040040250420d00000493f81511b8e8a80a0500804004
  | _ => 0

def word127_11 : Nat → Nat
  | 0 => 0x2f206d0340002028482f8562f4fa2d84e2c8b83022ce4040e639607a2c8ab90e3a22138b28a0d4105022e00201d04300482fcfa2d84ee40862f2281006cb80120122c1ca2a12ada890808a0545c01ce38d2b703d1202c050080480603802205021d8014022d3f040e380a048060380202505400001b0473f4480522ae380a050080380201d0415d0200052114fd120128a38e0680a050080480612d04145034000013448e380e0300221cfe2acfb119080fae48b00c1bcfe1c0853eae411a2a8a0873f81e2ac460fcfa0e05662b9815a28152261216e88d013f83610cfb11a2c055048b0548996e888873f85610cfb11a28050aa8b0568a16e88d054006c10cfb11a26055042a8ae8b0568a05489d005b8493f83711a2205000b94fe1e4fa128520300404002018001207d3fb953ec461080c0201400ae4018014087ce54fb11840b900805010015020187d3f8808884a04c46e5502020140181200a2c0050021c473e868e4800b90ab40042054fb1184e0201400d02000528a4473e868028140201201d054083c010774001111b921008211500218a53e8381fa2c0d0a41e8c93e8441e2280d0473f8ab3e8381f22c0d0793f88432b940dcfa1c22a0d0461ecff118342a83f3e87c6f108c33942aae41e0341d1b81c4fac33941183e1f4fe1e4fa1296ee504513c4b1138e0d0aeb696e2e836b70be1b175118841d3928ad020
  | 1 => 0x483000a0184f3f0b93e8b6e60bc20a2810054c102d40d003000a008482f8562f4fa2d84e2cb982e224102e2212da128048b228892d888b9609970372dd120680b008048060380200085404fc8b0773e84e0200a038020050415cfc14cfa1d812210001404b124fa1180e048060380341085400713f2220504ee5a2a8902ee438e8884e100e42c811408be124fc3000a0186c2e4fa2d8b28b0bce506941502680102e002018c01b0482fcfa2d8b2890bce5068020140080e0180140b942c4fc1ec493e8521180a03802005040186d3f44810cfae5014208001404d3ec481100f4107a028080500603803408b0e54fc04868120bc01cfc1604f408413eb9415396e402e8aa24e3a22138e42c841408482fcfc0180a2c8b93e8b6138bc300868b394100bc01d0213cfa1bb941050540806008c0120bf3e8b62c84e208b82f224e5040152dc6622a20a280aa2ce5886e538e88c4813b90100e004503400c0028021b0482f8b2158bd3e8b62e22ce40688b22a07b98e5b8e8884e8a040350b20450430502120be018021b4fa2d8862e0bce40688a056b8a2cb822a012d88887c1e01e5c0d4b7069120820080805006048041a390005021fd001f4fb120501f8780007d400433ec481301400056148793ec48128122907e1f00a1e00805504048060100140b914000e88c481a2f2e5886e502a1522a20a28e3a225c39013c483804015
  | 2 => 0x2e6bc2df502d5542cac02c2bc2bb402b35c2a7bc2a0402985028e34287b8280c0278a0274b026ecc2653025f582542424fac24a382433c23be022fa422b302253821e2c218b421244209d41ff301f9241f4b01eeac1e9401e1341dac01d2c41ca301c4281bf401b7381b03c1a8a01a4c419c44193b818cc41843417db8176b816fb0169bc1622415db41573c14fb414934142bc13b34134b012eb41283812144118c41103810920105340fea80f9b80f2ac0ed2c0e7a80e2b80dbb00d5b40cf200cb2c0c5a80c0a80bbb80b4b00aeb40a8280a33809c3c094bc08d2c087ac0823407bbc0743006e2c068b40622805d480543c04ca40483c040b8039a0035a0031c8028b0022b401c20018300122800d34006b4000502004481ecfa0f8520100203806004fce506f3ec4810ae4000501300f124fa1100805004038034086a1bc493f2220483f408482f8113f0b80180a1b0833e8b62f0c0e60688a05740d00680100080a1b0482f8b2158bd3e8b62e0c0e62241a0b2b684a89004b62221b06e5c02e392dc1a448218240280804806038021b22a01000e650011cfd3e8431201540a2b3f2240186c2ccfa888688a086018140200403802158008a502e60b13f0453ec4804d03400028a8b221a293ea22e606c890680680a0081402012018041a000893994084d4004b3ec480380a020140181203803408b0e65013f03c1a5022f8
  | 3 => 0x5b08ffc08f7c88eeb88e7b48e14c8d7b88d0bc8c9288c4408bc488b3408ab388a44089c288972c891c48893c881ac87c34875c086db48675085d3c855a8850c8847c483f34838e082ccc82354818a0814a0810ac80b588005c7f4e47e84c7dec47d6487cd4c7c3a07bfc07b7b87b0b47aa4c7a0a479c54791a878cd0782bc77b207776076b40763507595474ec8745b873eb8737c072fc472734720b8719a8714a870fb8708a8703e06f7ac6f24c6e8c46e0446d7c86cec06c6c46be386b7406af486a64c69cc0694cc68b4c681b467b2c675c066db0667c065fac65a34653bc64c406444063c406342462fcc6265c61ab46143460db8606c05fec85f5bc5ee445e5b45df445d6ac5d1485c83c5c0bc5b92c5b3c85aac85a1ac59c44593bc58c385854057d24578a0574c456c44563b055db8556cc54d305475853c54531b052bb0525c451d3c515b450f3c507b8500b44fa3c4f2ac4ed284e8284e3584d8404d04c4c6a04c2bc4bb3c4b3cc4aa3c4a2c8499c0491c0489bc4823447bbc47458469284642445fc0457b8450c44485043e404364842d484244c41ad0410c0408c4400543f5b83eeb43e8383e1403d9243d4b83cdac3c8303c2443b9bc3b2403aa3c3a2c439a34393b838cb43863837f403773c36fc0367c035fd0355bc34e3c346c033eb8337c032fc0327b43213031b34314b030eac309542feb02f8bc2f154
  | 4 => 0x834e31c0e29bce2238e1b3ce13b8e0cc0e04a4e003cdf8a0df49cdf138dea38de318de018ddd3cdd5a0dd1bcdca48dc150db72cdb1a4dad34da6acda128d9c2cd96a0d929cd8f44d86c8d7dc0d75bcd6e18d6b18d6840d6030d5a20d5620d5240d4a38d4320d3f24d3abcd332cd2dc8d24a8d1fb8d18bcd113cd09c0d01c0cf9c0cf1b4ceb38ce42ccdebccd730cd13ccc9b8cc2bccbb24cb6b8cafa4cab40ca32cc9da4c991cc95b8c8eacc8948c8040c7830c7228c6d40c653cc5dc0c55acc5028c4b1cc47b8c40b8c39a0c35a4c3120c2d18c2a30c2420c204cc16b0c10c4c083cc00c0bf8a4bf444bebb0be5bcbde38bd734bd0bcbc93cbc1a4bbd40bb548bac34ba5bcb9e44b95b4b8f30b8934b82b8b7ba0b779cb7430b6e38b673cb5facb5a30b5438b4d30b472cb41b4b3b1cb379cb3440b2c44b23bcb1c38b1518b1218b0f40b0734b00a0afc98af9bcaf240aea50ae040ad83cad0a0accc8ac3b8abca0ab8c4ab044aa7c8a9ec4a9634a8fa4a8b2ca859ca8238a7b34a74b8a6db4a673ca5fa0a5bc0a53c4a4b24a46a0a42a0a3ea4a3a3ca32b8a2ba8a26b8a1fb4a1924a14b8a0db4a0730a01349faa89f5c09edc49e5489dc389d5449ccb09c6a89c1c49b9449b0a49ac2c9a6b899fcc9963099044987a49834897a509702496bc0963bc95c4095454949c8940c49384093038929389223891b34914c090cb89
  | 5 => 0x4135d413553134f2934a293453933e3d336c132eb932799324b531e3d316a53124130a39303292fe212fa412f2312ec352e5b52df292da452d1ad2cc2d2c6ad2c1312bb292b61d2b2a92adc12a5bd29e392974d28db1287bd2803127a312743926d292682d262bd25b2d255b524f3d247b1241a123d9923aa1236ad2312522c9d229212252922039219312132520ebd207312011d1fda11f9ad1f4351edd11e3c91dab11d4bd1cd391c63d1bee11b2c91a9b11a3c119bb51954918c45183b917ca51784916f2916a3d1629d15f31159351529d14f35148ad1433d13ba513725132b912bb1125a9120b111a9d11725112a510e2d108ad1033d0fba90f6b90efc10e7c10dfb50d9410d1350cab90c3bd0bc3d0b4b10aec50a6290a14d097b1091bd08a25085bd07e2107a390733906c29067310613d059a9054b504e25049a1045ad0402d03aad0354102d290284d01eb1018b9011b900ab500444ffb9cff840ff020fec1cfe8a4fe41cfe0c4fd820fd430fce40fc62cfc0bcfb93cfb1b0fabb0fa5a4fa138f9a40f9244f89bcf8254f77acf7238f6b38f6444f5bb4f5554f4ac4f4230f3c58f3154f26b8f1fa8f1abcf1320f0f2cf09c4f0140ef930ef33ceebbcee43cedcb0ed6bcecf3cec7a0ec3b8ebcbceb538eae38ea720ea34ce99b0e93b8e8cc0e84c8e7bc8e72b8e6bb8e64b0e5ec0e56b0e50c4e4828e433ce3b9ce3
  | 6 => 0xd8d5cd8cc318c64d8bcd18b2d58a8258a3a589f35898c988fc9886c187ec58764186e2d868c1860c1858a58544d84ac1842c583a398333582cbd8254981c2d816b980fa980ab58042d7febd7f72d7f1c17e9c17e1bd7da2d7d4c57cc317c62d7c0b17baa97b5c17adb97a6b979fb9798c978fc9786a5782517784177035769b9762a975d9d75a297553574eb1748a9743d5739397322572db9726b971fad71a397132970e49705396fe416f6356efb96e8c16e0a56dc316d6316d02d6cabd6c3316bd3d6b5a96b0b96a9bd6a23569bc1693c168bc1683c167bb56753966e4966525660a165ca565825653a964ea9649b56432163f2963a396333162d35626a56222561db1617c160fa160bbd604415fc4d5f2bd5eb415e33d5dbc95d2a95cdc15c5c55bd415b54d5aba15a7c559f45596c158ec9585a1581c557945570bd569315633d55bad5564554dc5545215413d539bd5323d52ab9523c151bb9514a950fb9508b1502b54fc354f5bd4ee314e8294e3354dca54d8354d1b94caa54c63d4bea94b9d14afbd4a8214a44149c394954d48bc1483b547d45474c946ba546735460cd4573d44fc1447b54413543aa1436b942fb1429c54212941c3941525410b540a3d402c53fa293f5213f1313eb493e2353dbc93d2a53ce2d3c8b13c2a13bead3b94d3afad3aa3d3a2c9399ad3944138c413841d380c53784536fb536921365
  | 7 => 0xe0021dfc25df7bddf025deb9dde845ddfa1ddba5dd729dd239dcb2ddc5c5dbd45db4b5dae25da9b1da3b9d9cc1d94d5d8a35d83bdd7c39d7535d6ea1d6ab1d64c1d5cbdd5529d504dd46d1d3cc1d34a5d3029d2b25d26c5d1e21d1a31d143dd0cb5d0635cffb5cf919cf639cef39ce835ce1a5cdd2dcd7b5cd125cccadcc71dcc3a5cbf19cbc25cb7b1cb1b1cabb9ca499ca1a5c9d2dc97a5c932dc8db1c87b1c81adc7c29c771dc73a5c6f1dc6bb1c65b5c5f21c5b3dc53b1c4da5c4921c4539c3e21c3a25c35b5c2f25c2ac1c22a1c1eb5c183dc10a9c0badc062dc00a1bfc99bf9b9bf2b5bec31be635bdfa9bdaa9bd5b5bcf2dbc9a9bc4a9bbfc1bb7adbb221bae3dba6b5ba039b9929b9439b8d3db85b9b7eb5b784db6eb5b6835b61b9b5ab9b5399b50b1b4a99b47b1b41bdb3a29b352db2fbdb2829b2325b1eb5b1825b13b5b0d3db05b5aff31af931af339aec3dae4bdadd45ad4cdacb41ac345abab5ab445aabb5aa541a9d3da95b5a8f41a8745a7ec1a76c5a6e35a67b5a6145a58b5a5229a4d3da45b1a3fbda3825a33a9a2ec9a25b1a1fada1a3da12b5a0c4da02dd9f7399f0519e63d9debd9d7419cf399c8519be3d9b6b99afc59a7319a1419994d98fc9986b59803d978c1970a996bbd9644595bc1953b194dc59453d93da9938bd9313192b319253191f45916cd90d45904b98fdbd8f63d8eec98e5c58dd3
  | _ => 0

def word127_12 : Nat → Nat
  | 0 => 0x4cca343b233dce3345232a1e326c631e1e31aa2316c230ea230a92308b2302a62fe262f9be2f23e2eace2e1422d93e2d1c62c93a2c2362bbc22b3b62ad422a54e29bda290be2893e281ba27ad2270ea263d2259c62513a24a46241ae23c422344e22aca221da216ca20dca204b21feca1f5c21edb61e7461deb61d8361d1ca1c8b21c2c61ba421b2221ae3a1a74e19daa198ba191ba18aaa185a2181a217dc2175ae1702216c46163b215dba156be14f46146c213eae13946130b612a4a1211e11dce1144e10aae1053a0fe3a0f7360f0be0e9220e54e0dbce0d2420ca360c3be0bc1e0b8ca0afae0aa3e0a2ba09bc2093be08c46083ca07aba073c206bc60634205b46052a204e9e04b320453e03dae0382a0332a02e36027b2021b601b2a016320102600bba004cdffb39ff421ff031fea29fe541fdd3dfd5c1fcdb5fc72dfc1b1fbbb9fb49dfb131fab41fa329f9e29f9929f9421f9049f871df83a5f7f31f7925f74a5f7029f6b3df63bdf5c31f5639f4f1df4bb9f44c5f3c21f3815f35bdf2e35f27a5f2329f1e31f1831f1231f0c25f07adf0235efb9def835ef1b9eea9dee751edd29ed829ed341ecb2dec5bdebe2deb8c5eb031eaa41ea24de98b5e9239e8b35e84bde7d39e7639e6f35e68a9e63c1e5b9de5829e5329e4e1de4a99e47a9e42b1e3cb1e36a5e3235e2ba9e26c1e1e9de1b2de15b1e0fc1e0799e04a5
  | 1 => 0x36949aa944b693e3a9374692ec2926ba91fb691946910d2906be8ff368f8ca8efc28e7be8e0428d83a8d1328cb428c3468bac28b2ba8abbe8a45e898ba891d688736880c2878ba871ca868c2860be85936852c284ace8413e839b68333682cba825ba81ec2816b2810a280cc6804267ffa67fb467f2be7eb4e7e1ca7d8ce7cf567c4c67bc467b3d27a9a67a52a7a0567959e7925e786a678246779d276fb2769c2761ba75abe7534e749be7422673dc2735c672d227293e721be71a3a7133e70bc6703266fec26f6a26f2be6eb526e1566d6be6cf4a6c6626ba466b1d66a73a6a046697be6903a6894a6804a6774666eca665c265dca654ca64baa646a66423263c26637a66332662eca625c661d5a6126a6055e5f9c25f1d65e7465ded65d4525ca665bdd25b3c65ab225a74659eba597b2591ae58c1e588c658036579c6571525674655eca555c254dbe5462e540d2536ae5313a52a3e522c251aa2516c250ea650a46501ba4faca4f1be4ea424e2424da364d3b24cdc24c5c24bdca4b4b64ae4a4a5264a0aa49bd2491c2489be4823e47a9e4771e473ca46abe4632645ec2456be44f3244936442a243eba437b64312e42bb2425b241fb64193a4123a40b36404c23fcc23f4be3ed3e3e5be3de363d7d63cd4a3c4423bc3a3b5423ad223a93a3a22a39d3e395a63913e389ca380b637a3a3733a36c4a3633635cc63543e3
  | 2 => 0x36f0dcaf04ceefb42ef34eee9b2ee3c6edb36ed4ceecb3aec442ebc52eb246ea9baea2b2e9ca2e98b2e92b2e8cc2e84cae7bbae74bae6da2e69bae62aee5d2ee57c6e4f22e4b46e42cee3946e30b6e2a46e21c2e19c2e11aae0ca2e08cedff46df6d2decb6de642dde52dd442dcc42dc446dbbc2db3aedae26da9b2da3bed9c3ad953ad8e42d861ed82b6d7c36d75bed6e36d67aad62aad5dbed562ad5122d4d22d492ad4436d3daed3826d33ced2a4ad2152d1736d10ded0526d00cacf79acf4cacebbace49ece116cde9acdbc2cd3caccac2cc2c2cba9ecb73acb03aca94aca026c9baac96a6c922ac8d1ec89c2c81b2c7bc2c73bac6caac67c6c5f42c5746c4ec6c462ec40b6c3a36c33bec2c32c2632c203ac1932c1342c0b3ac043abfd3ebf5b2befaebea32be42ebdea2bdaaabd5b2bcfd2bc5bebbe3ebb6debab32ba52eb9fd2b95cab8caeb8732b812ab7c5eb70dab65d2b5bdab50ceb474eb3dceb3452b2a46b21bab1aceb1126b0ccab03a6aff52af526af0a6aec46ae3c6adb36ad4c6acc32ac64aabd22ab926ab4c2aacbeaa53ea9dc6a9546a8cc2a84b6a7e4aa754ea6bc6a634aa5a56a4fb2a49aea4436a3dc6a353ea2dc2a25c2a1daea1842a1042a0832a022a9fd369f6c69ee4e9e4ce9db4e9d1ca9c8ca9bfbe9b8669abaa9a6d699c26997c698f2298b4a9822297e529742a96f46966aa961da956b695
  | 3 => 0x828c001f0082008614018001818101058000020185000003030081140001808005858000818000808b810482000307018385018a000100008204850600008b0d868682000001860a8200800100010181000103880084850a878a0100810200000205010005008281168281858704008680871e8001818680009a02191485001480010180048c02012c8a010b000000848581838280910080800a0180850588800d1485820b000200000001800a87820380800b83808004800302050000018102040080028c8102800b810080010000008200028007800a010097010a8000820180848082838000850083070983008380041a800102000200010001030b8280028000070007000100010009818300818201010580008b0581150080800080018506028022028101018100a70106028003800080810c0300028007800102010001018404010080030101818c0083800006820000008182818000810100008082058f8008068001000100038a008002800200828001078004050101808487808000818002008100819a0b010104840880008301890400000a80800c0106028181800080030004000100010b06000680800000948102010002000f800006800387828084838280808081820100828301820097069d000000150001808e808200008382800085028000810100808000008000008007818680001ef1daef1822f14
  | 4 => 0x258300850e80028484010003000184910187890b81800605808f00248080000000028002038080830d000102800d81879e8f090481808a049283040358840081800300000083018a0806810518848080000900a60887053e03800b928100000c0094000f010001888c800787810d800a07860000038001898b1a8381018080038c028009010c9c8282800b078101010502829c800a000001008101828988008101018005010e0502839600018d028e83858201838107039228000f8a820e8580000884000a130501800085018981800000009000090a038781818007068300030701100a028182088482890480000383048300800a0106808890030802a201030089818002049984840600810082010000008e0083100201018201850009000a17009900008180808000800983838f0002008200008000048a8201048004850a0002808c0f01890000000080870082878e82008080898386080400000003810087000282008c81021682008002028c9800008083908101810181a182830002020002800900000000000680828685818306000c808003800416000000048c85810081000000028480018400800000048d1180800c800108000193000e008006018105800289040100810b028200800104000982000080000002008781080707820000829b0002800001911581950600018c8102810f8104808c000386000
  | 5 => 0x29fcbbc6aa060d5ef525fb7f80016e0b9ec3a75b437f8007f800598ceff80076c68926237f8000bc40818ea2ebbd7f8007f80077cfc1be3d41de30fe83a49053bcd7221b92cdc79630cff800436aeff80059384ba2eaafe792cced7f8001d43d29a8d953317f8007f8003d23e7f8007f8003abefff8007f80049e0f3e1ecff80040ed1bb2aa7f8007f80042be631132834d48dcb7150419ba2c4a94e4b638f0be57f800336847f80009242c18bcc03031487eaadb8e847dff800122897f80025d3eff8007f8000856e753366dd0aff8002308a7f8007f8007f8007f8007f800571f4143497f8007f80052d467984bed89402897c53cc3cd94de907ff8007f8004f24dff800535f0ff8006935e74a85183f9161e9a967dbc2cbc139f3d94ae7dac222dc598d9adab31a02869c55ff800396d691d3e429a73c0b9f89174e26fff800553f2276328238ba4a3d8717f14cc8b708457ba638589286117f80054325470359bde3ef3776a858a52266d1e12e67ffbdcd2a1a5ff80068a2fa78191010506b0800040061780058606bd80038112808c0400028480018488038800801406829c00000080070a0500988a9002908e801d810112028602890002022e8008358301018307040407000000028f0b0507810c10009f2f1f0a038c80020f83038207028193169f8088810a00021a0683af850b80010a880b0102138c020f0006808
  | 6 => 0xec9018b00427392d026865ed008fc2ac41fb004cd8451a8ec21f85eba94b50f919f7379ff8006e2a5ff8007f8007f800503ce7f8007f80000bf0f644e98dd9935ed2f504149d291a357f80049555ff800220c875d5d435d7a290fd0eab6213b1d37b8001991526c6caca74de8ecd7fa0f834c23d9e3cfc261b5ae159c5317b29e653007b1eff8007f80006d2a4d1835e82c0d0678e50723be396bf576c37a924ba661c6463a35cd62dac830629a1c6e5206e7001a4f3e5968b0ff8006b90da68ddd20b32706f9468f39809685e5ff80026c3b1b47aff800079b244ba5ea1cf9b8852f8197f8007f8007f800395723530f4cbf47f80035bdb8d5e23b93f7ae8cdb8e7ab12186149f685114afbc4525205413b53db43e022c5fa0ca4bdd5337aba43b45dd0c225b068551e4e51600a25db3d88297b0ae2c4b258c1ab0ccaf0b3e6491e92a9b6cb9e579a96383cfe8aeb66ab345cd6a580271d4fd77ab1f919755b924646bdabb074b6c7f800284edff8003ea4a72bf6e3d0555b1f7d0d46a0751d9ed2a969ce8820287a54c34ff8007f8000ebfd151aeba4347b4397f8001a98ba112f7f800324ee02a1502a53f60434814123e98b1214c185ec12ac3e616d5d34c7c9de65dc6259844c76ae68bf689cad9fc11e202d69e429c17f8000ed71bd191f26a043b04aedea7f8007f8007f800433adb463b7f80078956d195052de9875
  | 7 => 0xdb00a78a58009347106764ceb7f80025467b28320243575cd90e888db3826ac32c4ba85784dcc8a4d6c815606cff80074973cd5a45a578ff80058b3a7b421500c6445914918ea445658e9d472e7b68bbd80ff7f8007f8007f80005ca5ca5d1adbc5f116b7f800683a55c3187f8007f8006cb354db8aac3cdf21a27f80051d5f01934e9d4333854221d56ba7bdb868343389c3b38fb6d2107c5d282c4c7c7f80001208520e73045b21b408db5951e680ec9e99d1394bf7766377430a218de3431c5bd777f80055de67f8007f8006e275ef04ae7d6f578428289dcd05482024ff8007f800232aca9da3a2cff7f800568617ca9d35c9c948383b5bd68b94aeb504fbc7765fa8615f5e27d81b24bf9591a8f120b2bef49f052780ed879d8604d63ebb1ccb2e13ff8007f800672925180cff8007f8007f8007f80051a969ac093bd2dff80072012d22e1ff80062cdfd226e243d01c4359c13c80617221fffadac9ce45ff80008642621037f80035b3831afde2ab14a2da7f8005d90ea417ae2ecf25b214b9c0538ba435222e3fd97b3f7f8004917e678df279a4e3bfe03a90af8a53764ca483e75114a149bc0167cfbdda9005e325a5b03d53a0a1d41b358b4bd990ed90c65b63cf17097c043da35b0404fb27942d75bd0260998d7f8007f8007f8001cc6dff80079d73328ac7f8007f8002944d9a412ca0ee7f800748664b517fa92
  | _ => 0

def word127_13 : Nat → Nat
  | 0 => 0xcad1ff80035917c922e301ddd091363b14ef0bded2c05bbc3f619eff800235fc20241f44d2f7b60ff8007f8000e1f17d40369689f9955151cf3881dc394ef6c48c5e7996510ef9b3ff800245632fe91051d8cf40e7f8005fb9c4e9a437de57f80036b3b7f8006fe84eb58fac01c26aff110343c266ff8006d631820e3cbaf46f37cb650e305573369320488ca22b7c9d93038652afb485f2f2d0c23b34e84ca8664d881dabe511733ea6b9ba793a698b5b7c072c12f1b399b0e9315a0d93f11577662e787bd8e60a4e6a83428c8acdcf997b80bd19996e0b3dde6bb535c3e3e25e2aec51da83150d53d92ff8004294a7f80027c644f454ff800738cbc9be238e5568843c537102cfd8508da33160f5ec56c8992c7831e872817304853d8a5c9b8eb6beb81706bc38c50233d0f2ed3d4adc4af3c1d379256c09dc14539718dfde06302f641ff8007f8005920d12b5459c7b7f8005be82caaadd6003a442995d5045c79b54401fdd04b2915ad446a2ff9a18fff800414cf4632df495675d9e02bda90d89d6b7882abca100c14a4100c5caea499989c77b7a36b23edbc33be59531e600dc73de1056d0bb3c4f47a8a339baad2fe2e59d45ce85f21fd235a959ac05eba8620df957ac221a2ea94ab92b634bc5e6364a3ef730dfb916cfb4fa06e4779d3ae211e7f80056ed7ff8003d48dff800341757f8006ea11c111dccd8ec7109
  | 1 => 0xc7d356727f8000c96328139574e6e6389414441a4b5cccb0d8821ac0a2a24e52ee4320d7384df95723ea3b7512ccbe11a38356d2c3932d3d9bd6781b1866cdcf0ea4abccbbf224c4996fd80f7ec24fd1cd479c05d8e1e175a9aea7fee5b5c1e58efc2431b673ed6edfe00ff8002cb9ca2957938805b665516a8ff800759224516f668d707eca814838e8870619a4188285891216d5c6d950c586af28f030c170138eb898cdde49764f2a5a5f5c6cb9229f96ae753dff6dd6ff800193f06f0ab971e47b811d5d35de607a489a99c931ee8b41c8fd3da97f8006c2527f8001b1b35fa99aa24620d62ff800020d6ff8002e0d21cc6d63a24b1ac797a01696c016b2e0e27010920ab9fec2c47cf0388f3f67f80048287be570f5a17334c34c368d745a7f8003f8ffe1a63d92b714e2dd80d2cd901b46cd0b305c03af5fac6d49095f57de38ef835b8468b61bb173539f959452f1dc5196c3a09ffad91a9469bc492e9eabbabda16ab9ed24039846a2e39d29bdf4b8db6bad3d92ae2628ff800683de186735fb283e020cda06f58f2aa1bbf262cff80044374a10f357552beadd2521b1a9b58b1beb9603b9c437ae6c0533c7c381d1cad2854903df848ec4649104e486f10ecb384e041eb7f8006ac60f150e99bf87f80012a9e7f8003631a220a97cd2b4f1c27f8006f194f0af6add4a80a2129633083bdff80006c557f800112381
  | 2 => 0xfaea027a7ddb4605820ec8d0551aebf8e69cb24a3260886d7b089865191b7fd2c4cd8c84aa177ff8000449873999ae8e2581212c56bd9bbb3a5f6bca747f80065302ff8007f8003f61ae51d9ff8007f8007f8005de767f800503aeea93ea3d90f80fcff8004462fff800142233b31ab60d3ff8003cc307f80003d394a6b74732b02265230af7f80053bd1229fa549e37c5a4d2dd23d18e7f8003c2777f8004fe827f8007f8007f80022db3ff8001abd3afe967f80051eaaff80007ec3294c87f8007f8007f8007f800690caff80034a541d8797f80018e3b97cf9920d17f80035a807f8007f8007f80042ce468c7f05544d53d1bcb241e65eff8007f8007f800552e637e75ba1bb171797f8007f8006f3a0ff8007f80019b8d61157282eb93a38a284c7f8000d1e73e2e27f800475316d28e55687d45a77f8007f8001480d36b7280e5e7f8003f1ea0b2dfa961fff800345b0c5814cfcdc02055ff8003f327ff80067d609db4cc53bffcdc30a2a17f8005ddba334e5d83fb0232a7f8000a9ad3e6156965cff8005e51866e0305a3c5c3cb844d27f8007f80079c64d917d1446c144027f800242ce59c8aff80042c7315342ff8001b0e57f8007f8007f80051ac3ff8007f8007f80006817e05907f80065c45a7b449fbacafdd3a32ef689a8e02ddd52cc1d9038654b2dc41d2d96ff80056cbcf087acf60e639125305fc0515cc
  | 3 => 0xbbb2a1a19f35edeb78089b6dcc3088be88d0b4127a40ccad3801d5e4795b7cf203462077f8000d3508402e193cd18826a9059f9a3cdb4ff8d0db554a389dbb1d17baf337b3a7b26d08bda9aed1a96b3965bbc0f15b259b5ec4c5693a0e7f8005b46530d4851277fc4eaa36160108c5b2d3c4c1bd19c588ce1814a0ff8007f8007f8007f80076b2ca6c5f6a4e376b49c38da498ec07a2761864221767f8007f8002a9f9496c3a337eff8005acbdff8003ece2a647717564e3541cdb1405c4fcf136ff8005acc67f8000d8e9dddbdd863f5d4661eddca3c31f322df08659815d5e16580cdd6d44c1262aa0405695b45d1d72caa8bde68ff80000677ff8007f80079aa6b7aab2c908bc0863ee90e28e12a30c32bb602264d64ce9061eceb624a43fff80045360576622115ec010bef4f24c935ec00891491bf61cf389e1221366dd8688e0d2a8d5425ff139eb96359f65c482ae79952d233988353a0e2e66be4e76080eace9419120dde75daf4b21e918ed3a874d75b36ce66bd4eed01817444a4c83cc74df24ab87d2abb0ae379dcab6d9ba1c805a8ad6f65b3324d1dec48fab4b1cb1cb1f8181b1c711d3fc3163a31fc8f04c8f58f52be2ac15ceb09618aaf4baea045dd94c520be3a311cca56c266f9b0c7df1aad6e7a59e8d56174e19fbcd0f5369a67201f5bcc112474f42a30edccbf3a7b615fff8004b60991bb5d2b46b30
  | 4 => 0xe9b562e084c29931be605313e168122553d2c004af401130a9b04c39feca1e2437f800765427f8002edf67f80026e67ff8007f8004347ce4bcb660cc7f8006787736d1f35dd70662f7f8007f8005c8b17f8004c4377f800335847bcb2ff80037b59cad4e0d4f89d387b1da1e7286ff80005922c91461ca4f7f8005f6524142dff80028cca3c39412ab616b0fb6b52558aa7f8007f8007f800040e81c19d17c0d91a93ff8007f800334132216d2fe95a73d64f00f7f800322c45ac59bf40749292be0977d4bebe2f77f80013160d23ca55c01cf24875406613d256262ff8007f8003e3c9336a704579c1608ff8007f80009c6a43685ff8007f80064ebdba1080b44544aa872e8a0cecbd8ecb3aaa9cd0a8ff80036b4dff8005d84cff8005351b7f800161f6f98a4485a667ba748243ff8007f8002141aff8004d5d5ff8007f8004f59455b2f02ad51411676df8ff80022c597f80029e21cf5f4974f66fa606903989582ff8003741c7f80010ac8dad2f8a8f4402363b14be6a8b8d4dc8c06912ba1f82d12abe8d7b3bc1b1d185afe9c54421c610e049e42f828834c95af4328a7809b6981de28330ab7843b925bfc839db555b764bed66cf2f2e63b2ccb1c48e4bd3f8632a903dcead8da4ea461201ee3168cbaac1a30515de8545ec24ae4e478d6db1e3d58605c2a98f7334d8f034643977343bbe18554a3e9c20f0b66b03fd8
  | 5 => 0xe8c9be47e4c071cfd0b34a18660152bbdb695272e66e32023c80c05e4c25467cd0defcb8aebb41fba32d7b38c0c0063f94295e186196d99c2d66d3837d124213ddb0d8c107345cfaf625702a079905d0fdf9e3247ff80053e6e91a6216525cde54493aa4bb8f1d111138ab4780fff8007f80024a7e7f8006a8b204d168e2df7f8007c4c5e4b5bfd337751497f8004541e7f800709fdff80004b1ff2b908125c119987f800061e029c521e19cff80036e65b4a6ca88baff800618c357e28361cea1e642a4e4ff800751022cba13c676ff8007f800433cf8ccc29d835672751cb990b09d3ea5aff8005b5e1739de7916a568b917b64ccd50e04507412e1869a7f8005bd101d2a48fa9b3ebd864af4e29d2194db455aa9905690540e267e9b414f46a90468894648aa3ccdbebccc4a8c3517261922f4ab041a03c83107a048cbe09d948cfe345b8520b150dd83a044d591ed3069d7c708167ea3424cc87dedb3251e42d9918c2a3b2fad1f2ff8007902cd4817039375c351cc23f906b9f4233c8d0ca9e59ff8007f8007f8000250682d2e77bbe46e2d7692cc35e6f9d7e6d8d581336fd1671f4822254d9183ec492950426ff8007f8001a343ff8000b8043fe354b2a56dcb8ff8000b273f057c7f80008382ff8003e079da8bea1ec0841a80b671b6d22ae18a7f8002d6249b410941406c19572a9732de8fd5f52815359100b1bbe
  | 6 => 0x29c23c339da28213a3a6e17d1610d195dd050008b9b3da0eecb6de436475e316fbee3edd551c19a68409541505b06723394a1ebfcb86d626341e775d3cf2a962446ced32057013fad9a1bb0eae6e487f8002a5df4954ea844bfcc3db5e7bd16539000eab9d3f791bff8006d417a8b8e884cfbd98291ea285062e5a347f8007f8002e8b8991191894fe68d60de57233979e2714a40f3d5c6b140a41d7951b0ed8a2c9ea7231a9dff80065946ff8000b81143adcff8007f8000bae5ff8004a331ff800422cfec1e8f13c7c1053792b27b2dbf06d4f617699cc0fb2472a0c0b41d47f800069187511f50a67daabb809ef8aa593d8e1f33c5761558c3870eeb4f6ad852cf14140a85ed07289f4c66cb95203601375102dad144baa07f80042806c602de4a12ff8002e430ff800672db7f8007f800560015d1007f8007f800020bf7651dc1a8c8b375952d772c81ff8007f8007f8005e37849df37f8003ea7c5ec3b95ea3df3faff8007f8003f6408e48cf3036a6ebe59d6cff80076d59ef4f7badbc2e64c648fc299ab5d271fcb69e138a339657f8000c4aaff8007f8007f8007f800682ee425fa7f8004d309ff8007f800418a1ff8007f800189277f8007f8007f80017e2b2102539d597f8005da957f8005a3447f80053285ff8003eddaff8006fdc9d4a7d4e42bf895e7f800681b57d1af3d9202ac00421581047a0c02a799991
  | 7 => 0x7188bc441ba0648f1f4e548f597ff8004ea847f8002225359aa294af7ff8003d2127f8007f80043abb07aea133d3350e95925dff8007f8007f800206060f8cdbb03b8a57b35240a2cf452b9075530ee22184afaff8007f8003c2ed81622b2399ff80060669dea708924cec0d49686a913f16b4d68b1ed9ad5a609f9b28b5f025d19c90844c482bd6ef5067f80038e0b7f8007f8007f8005f07fd0e2098d688c3ecf0529166cfff80066e1f64be44b2a7ff8000024e049acff8007f8007f80060d7504433295d44d2d5dbb723b1adce3b0f7696e70a5f9b3cf85c205c4110d01864f6ff800399c77f80010c94a82d27f800616d206d33f460edc01cd6a19a62e2b8d1a3b0ade3b1e35a557043efb11c3f6b2392d4d0ec64ec9936dcedea26f620966bb26fb6809b17f1dc63e35d858b2ff8007b2981b6c8773c143beeff800028cd6c1248a2877f8001c9f7b701fbed21b488d45c25c069b8683dc639d648e68dc49eeaa3ff80015ac2d9c4d4d1e3ff8007abf7cbd9e83b6fec5819655fff80006692639288d1e50c315ff8007f80067e4483ed4482be439a0ff8007f80014a202722f07634cc5020eb61ff8005ecefa8dc5ff8003741109034ff80040b9daa41f7f8005ebf37f800099bd58098663b77015229aaf3d083dbe982c4fe430e60127e931a9d0e13599ca2f46938b6f4155abd1443d01460e8ac6599f315159a2260
  | _ => 0

def word127_14 : Nat → Nat
  | 0 => 0x7a0a607a292710af711a62c16afce7561f2786250d9d64f0cf038f9a36a0802e87f8004b95a5f546d1ab2ff80031193ff80068b696cc765757049158f70fe9a42cf284fd3d8e6a46f15d56be0233e64f88eb7ae6b337138111ff15ea6063c8118627f800482ece2d0338d2333e3235b0bea6a1c0beb2031b7f8007f80038e3dbd28f9a23a0a3ec092eb4d89e9135c7f8007f8002f968a0d8f1f5b9d469dff8005d3b6ff8005a9a11edbbfbbab8f4517f8006431d9d0f48c4b37f80019b090533066548af52858e382561bc7d9b7f80061606f1519708deff8007f80033e978cb52ee9f53113d4747ff98e5ff8007f8007f8001f54bad69505c4e4b65bff8007f800799338a5542a059573969851fa72f87f8007d443d286f7f8007584f7f800514a9aa6501990d03c52c0de065990580b84766646049d16c2bf2bf7f8004b367ff800734f3adadadfe21581ee7f8007f8004da447f8003c4ba07bc1a1566ff8003e022cd81833857f5c8b7f800679539f2fc6245c17c07afaa912b955c5927a3f1bebffff8006bec9ae6b8e550a176bf9a030f45b6db3d7314220127a15ae8f41c3e8df785646e4af89137920a9ef5e50bba3360322ff8000f59c7f80024880985e7a006552b4f8a1459eacf68b5fd15c5078e2f5ad798e414746af4c6587a45ff8006d90a72b2064680d7ea7ff8007f80036d9af82c66e960209d1812495e4
  | 1 => 0x54b918e11f984f5314f91e04530c426b073ff8004dc3f7f80021a3ae6a1e51b4a6c4857d27a85ec555147caa0ad1633ddacb6298967a5126ae520680396b979531aae01da0e8821c315b209f8c1fa81e503f49141385ba9013ebf497a3f21402c9f9be5f1c2038adce09985db41410c36fd5ffeb9fcff8005fc2b36d7b8c1669297c33d43842bd4494f428036b87d7f80052abc4ced6612c74764e818cfcd228efc364ad63ea943f4272ff80010cc7f3077ff80045ae76dc292be8eb4ac9b144aac48eed9246b21ae5ad360141b7576c4172029a7f89c93712c211ae025e1bf99bc26a12aa5b1e49adbb764f269b41f1fce6d62c9a6ce26f9b9e12c57a2cb27f8006ee8910e7adbd1c904a696cfcd14f1e53837f800009b09cd3a414be6be904291cff8004159db7104baa83d998f75cce44e147f800359a5032647f8003f1e2554477b9aa3db7d59557efdc053078afcdaff8007f8007f8005943ad7b7d8637b035e9664a363248801a3076d72464d1447242d7ec8af977561cc816aeb2ecd09a4a4632e6293542720b5567d45bf4f73b473b0dabff80046aa416d3f7f8007f8007f8007c9be7f8001b8c8d9a3bff80009d09e3e71683e37f8000658b270b1f5a08d039a0367083354d905c9888f18519c63262f9c0ff80000c0cff8007f8001419e455b297894bf033f7be97f8007f8004f037de5405ab3e3c202058d18c1b
  | 2 => 0x664ae6ad2c3c7086cc067171ff80050d9608d6d99e077f800245557a21cb7bd449d6fff8007f800061069bd39ff800704d57f80056e74ff80078ac27f80052542ff800779b89195be7b33490b38d8aacd114270a0dc064fc86375362c683186a6922583731e59f438b5ea83349541ea494af12141a63c2f73ed3ff8002e52402cfb0836a886bd5aa3101c5733baf8102a9bb7e2622a7d5add3b1bff800388298edfcff800300ce43ca42e67c1833fd136b976c692892c258cf3c7179d9fc0972a5c7595dca2f3fe9aa502ddfd00ba48c225231f0e0b85afddbf6450a62ca57807b7a864b9da0a35730e4621b70aa4a1f96a56b8bc7cda69fdb62ce86cd12a5ce0cd1923af3f3b1388cac5a862f9955d6240bb1ca3958d526a4d86148a63c85a01e908099742bdf54102c4960520bb628c499323f4e00d406acc62635a8ab0e4ab636c5d6b3bd03a9d4d170a6c85864b1c433ec9644d1de587768c44a9e7d2bba21a930a26aa22e09302f0ae9f7552663ca2f7a1f04bf59f595f565ae4c0b261b4d1a60d544b34c96dcd097f800100f96234b97dd4c893a5daa74259f02066c9a1c0a86ddddcb9fdbe7907cff80038281aa514a48161aaf00252cff800172b5ce2fd4c502ff8001e8407d345258709a9fabc1dca943e0a0f8b4234ace0c3e99297c02aa2f5e8b0517075c655e674f8222566445e2beb11d56a92a7653462ff800
  | 3 => 0xe0d02a6f7f800599f4ff800096cdb282078e14aa26eb28507f80076b4aacad600915a7ba8ff8003762267d2131d0fe560456255ff800382661b30ae1a3d048c3afae6dc574a4980909d845918961afe9d1d3c4c6c910404be7895cb783d9255a558a52ac66bff8005fc182ce30d38a3dcb71de209f6130cf3d2d0bff4f3e18937a8cbd0ce090a9032d908858caff0e5d2781adee1a629bfce37f1de4bc580736cb9ca2d07a03b34b6a2952ab8899ddc959393544ba37acb3aa9b695d2ec8cb4ff800154907c16ab165fd208e3ce8843eb280da7bedfbf69d1205aa515c8e31fd244eceb8109ba372ee02c5c08ff80025dc0e6c51df2bffbb6ebbcb040cda61341ff800168a77734d5199c7f80024090701d6ff80032cc95c0e32f8c951b01ff8002bcbb746c5f0d84d5307f321d6ec1c82e9922b938d3b15d2a25dccd6134b2e6ad7f8002fd53cc926555010e1e0ed2c4e9681ed182010937f8007f800509a2b494b0d5a35c2c93a4ec1d2b97f8007f8007f8007f80047232ce05bff8004946b521e6b0520c1217ff8005c35f7f8001954a2081b7f8007f8005380df9c1d7f8007f80036eccff8007f800379787f8005f95b7f80050851c72fa7f8001c2cd7868fceddd7f80059bc2d09f049a1dd461940eac8d0dbb4b18ff8007f8007f800745881f15cc5e49f733097e23be2ad5781d7f8007f8007f80049131a9998a68eb9
  | 4 => 0x494757f8007f8007f80023a39af8c70a3c4d5c487f80028954c6a8276588e12c5ff8002f32c172fecf4f5deb08194f4f0276989cdfb06a68a6d338051d3237cae04021005e3c2e983ff800582c3756bc3b1437f80049dda7f80006dd0e53ae7f8007f8007f8001ae857f80008e999b326b9c2367ad6c4237ff80068bfa7f800054867f8007f8004d4ea7f8002f26581a2bd0d8a0aab468dae5c5a0655e0b295c7f800740f3cbd47e3c677f8005c13bccbb9e184853123764d16fb3204c80a99cadd876ff800572898b6830594cb363aff800470302b3c8bedecd39d31f180302677057fca18cf38edc5d321a1eabac830ee242eb846c482978493140ed53b5765dfbd802da446dce0256ca7de02fbc18420c7bb102592e15c4d3c22a22d136134944ed3bceeaeea1536ff800346af12c66ff8007f800182f323a16b88b79ee947f8002662bff80046a74f5bdc7f8000494d480b6e01c2ff80009347ff8004eb276317fff8003063932612ff80041424824de346c20ab488a268bd06c7454fcf0b45ebdf366aa02e276c189e26c70807e21b4012e78e25c97f8007b89bf6d3523b58fc9b42761233c747f8002fce8ff80024b1077eadff8005b81ec155dff8001c8463947ee705e7f8007f8007f800729eecc80e3c40bff8007f8000dc8bfb2c57f8007f80017ce60a0c4ff8001faafe7ba47f800170fdff8007f8006c38b6d
  | 5 => 0x1e13b19fcd3d8cc77f8006369b7f8007aeba7c1e4ce98d814bfc9ea5c10f6f7348280fa0f65da55c879933554975eb1935bf2aae3e639947ac3258c265804eff8007f8007f8007f800081544d2040510f0025f6d5513d69c2f65a5f1ce70626184f083dd2a13dee1bf9d78dc7f8003fb0382926dd35cb664a4aa0086585a7cef47e4b114257f80027beae23b2fbb19c3a97ddce9ad39afcb35ba047f658091e19bc2994fb00f1a11644497f8007f80069d048b48d37bb454d4cbe40d5c4945c8c6ef22412a8ac83c251a9feb9c85da98d94702430e4d1cd7b3d7b43caaf02b1269a82b6e2c893f3e001a2a0da213dc9077f8005985a23e7b0487012461241dfc4ebef5a3f304281c1169330d9a05730e564759a214db9163f93355c815191a2aff8002907dde1c53c9598b34eb9184ff80069284b4a0f1f92f8c2f650e55bee0aff800033e6966817f80046b5d3de37834e9045c4fcd5bbc26a063b818b077f8007f800700afa8d477f8007f8007f80075a78a156585b89ff8002e4dd828dacbbc67f8004e19fff8007f8007f8005dade69a457f8002303ac826dff80040b010f06eff80052507ff8007f8007f800793582a3001dab8d9dddff80066d83ff80061e5838c61ce913889c6ec2fc891d5e8063998ef339798ddf21d68dff8007f8007f8006646eff8003be42c334e7f80016b9109050e3227ff8007f80067356ff8
  | 6 => 0x4fc605cb32d89fe736b68e5d31d21611498cb2aae109205d4f3c5feae577ea3511a1f8fb4cc1f242655a0ed9ec351ef0a88cb366a43dff70b4225c93bfe05a3a6c658d0228e03f403c652f431b7eddf1e692bd25eaf6b125ee75440a82320016c5384e1b01eb42c3d5345081b8cb09e91cf51c43eb1d20ca744b7d434744112cf171761c18183f043c07537074c3cdd64412383a1d7a18d28ca14dac028ddd549fae96fd05c7438611873f1064551506523a84c9e7b3a8bab6a86a9c55f3bc524cd9cb8bc083203c57bb7fb5807448766ed2e8380b54586a9d4830a7a217417c2a0a45d3b129cb1d031b73ff8005d5ee434d99997df10960c9c78a0ae3622d0ed8c7f8003b20b00d4c779427f8002a09546ece6c69ebb673efe2a4b4aa1dcbf0fe704dbc6f90003d0410a2a61c16621df5ff8003cd9cbb0dca2813ca0337748460044f1a59f16d1156afcc280f602d164d31496903574671cc7f8007f8007f80024e6b7f8007f80071477f121bebc99eae532cdc45e4e15ee948b60fb8d3b6842c39472ff8006f1d0d2556730891416e9b67f06230cf1b2cce1da55344b06898ce3eb2d452896ff80074961b326b8ad457a82bd0e478d9c8f9091ff80038c27de052ba17cdf140ff8002e672d080ad3be2e8ae43a5ab3ea94113a283bbf6c02154b92f783ff2daebc24eff80001538e9105d6002784467f8005ed3cc488a9f88
  | 7 => 0x40083652d590227b84d0cda13183939279e540fff8001d9b76f9bc53df47d39be8c22e89a6f618575d3327bab7f8007f800065eed44121b30439e0db282473995cd5d8ff8002e36339e4e52df757db558bceb6b66b90858864067409d484b3a5bf4a2babf175e6518d4b7c20bc9e90ee8d04a41cb6bd0a1051307f8001ed1b91d69a1b9855c18f5937a0dbfbd6d083a57982239e68e3f5beb05937a5cfd8311041e2e42ef9b860df9f60907b7f80054861ff8001218c75ad0ff80052be10bb98d2da2413b8da2d897b88778d361d7852d8ac04abeab6b28d3647549b78c5c4abeff80059bd5cd06d7cae9ab1b9ff800109683587f09215f39b645420aa8d838c978a5627f80079cd0ff80013a9f7f800402197f8000893644d5c8d4589fb667f8002d23b1dc1dd2b151fa9189c2e54558a13bad651eff8005fd5b16e7e4960a3bcebead372785adda10ea8375924b131e1d10b0763e8549e8300727f80039d3b956637f800502cc93a44c657f58a6154411c3d72c361d40db49a2509016e3329640910ed05dca29ca8419573d4d493a9787433b734099df03e735c2ecab5791d0f3a6438090e758a060d99669df02e5123a0c1aeb554645278bfc50b51b1dd4ea889fe6de9a6b004e7d69475bcb91cc5dff8007f8004e6b5ae0e474512ecdb901649209deb46a232a95cba36d1829496616320ce838e08dfe70111bb0aca7491
  | _ => 0

def word127_15 : Nat → Nat
  | 0 => 0xbfbe8b65f12f2b43fc70b296f90b7d069b5b1cc6a18f46c1a506b13b0d4f5137a220b05ad52987d602ee6ebf7f8002f6097f8004d18b1750dd8cf00c964ff800608447f8003f0b716c89065d905ac0b2e690ce05388f615de2dd2f26389b17254b08fd26e56986cc2199f5b91eb6b95bb27f1d3b37941ee4ba9916a68e376d3cb1109abb44207b28e8b4f37f8005cb5330962ff80025a2ea6a46e3db0640fbac13c17b743b5329a43997b258d05c2aa05c43655257ccacc50655e8d693e588eba1486c25be5b2220d7d4305b2f1bccde9cf23eda5661bc2c1af202951bf7a11aeb8710d38554048cdc79146bbe988fece11f9a9bf3cc1f0b4c5e887b6bb4828d7c5444be12dcc125f569737815fc9f5e390cb7c4288800ae878365baf318691377dd48c78178a6487ae4639eb13ff8007f8007f8001130b299b86808b7f8000d1db854176852c53ce239598e8567ff8007f8007f8007f80047895c75cd9846fbb416718dd7325ec40477f8006e10103e8c09268030a379415a0d5c3e139f14aec1652c828820bac1e19afc33e802810067441e67032d9345a2891255597eb5d93a8a900e80bdcb8f9666f5211b39b4f63c685b001c95c1e8ae4e7e18faeb38f43c34e27c24e0d41f3ff8001cd85319c9dd00b0fc00ef0f20f83622ae3ff800496d570eac67dbc8925e6505f14321ff8002a45bc93025b28b061960e527ca9888
  | 1 => 0x32a01213222a11213222a01213222a00a13222211a13222211213222201a13222201213221a11213221a00a13212a02213212a01213211a01213203211a13203202a13203201213202a11a13202a11213202a00a13202211a13202201213202200a13201a11213201a00a12e72201212e71202212e71201a12e70221a12a72201212a71a01212a71a00a12a22201a12a22201212a22200a12a11a01212a02211a12a02201212a02200a12a01a00a12671201a12221a11212201a00a03673212203673211a03672a11a03672a01a03672a01203672211a03671a01203671202a03671201a03273212203273211a03272a01203271a01203271202a03270a02a03232a01203232201203222a01a03222a01203222201a03222201203221a01a03212a11a03212a01203212201a03212201203211a01203202a21a03202a12203202a11a03202a11202e71a11202e71a00a02e71211a02e70a01a02a71a11202a71a00a02a22201a02a22200a02a21a01a02a21a00a02a12201a02a12200a02a11200a02a01a11202670a01202271200a02211a01202211200a01a11200883272a00882271200f6bdd7c3128f96bd88fb640fe5238cbf310832aed9a0f9b1887c67d5f69fd8b339e6c7b51701862efd0106fec17baf549d11f32b3e2a7ce9b13382caff80050576144fbb19c4edab04b81bfa856619287d16464ade86ba202c8f53
  | 2 => 0xa00a33672223233672201233672200a33671202a33671202233671201a33671200a33670223233670221a33670211233413201233273202233273201233272a01233272201233271202a33270a02a33232a00a33223203233223201233223200a33222a11233222a01233222a00a33222201a33222201233213202233213201233212a01233203202a33203201a33203201233202a11233202a01a33202a00a33202201233202200a33201a00a32e72201232e71200a32a70a01232a12a00a32a11a01232a02201232672201232212200a23673211a23673200a23672a11a23672a01a23670221a23273212223273211a23273202a23273200a23272a00a23271a00a23270a02a23232a01223232a00a23222a00a23213211a23213201223213200a23212a11a23212a01223212a00a23212200a23211a01223203221a23203211a23203202a23203201a23203201223202a11a23202a01a23202a00a23202201222e70a01222a11a01222a02a01a22a02a00a22670a01a22271a00a22211a01222202211a22202201222202200a22201a00a21a01a00a13673202a13673202213673201213672a11213672a02213672a01213672a00a13672201213671202a13671202213671201a13671200a13670221a13670211a13670211213273202a13273202213273201213272a01213272a00a13272201213271202a13270a02a132
  | 3 => 0x1a81202a01a81202a00a80e73202a80e73201280e72a23280e71202a80e71201a80c33201280a73202a80a72a03280a53202280a53201280a53200a80a03202a80a03201a80a03201280a02a01a80873221a80673212280671211a80433201280423201a80413201a80413201280073221a73271202a73270a02a73222a00a73222201a73212a01273212a00a73211a01273202a21a73202a12273202a11a73202a11273202a01a73202a00a73202211a73073221a72a72203272a71a03272a71203272a70a03272a22200a72a11a01272271a03272270a03272270a02a72211a01271a71203271a71202a71a70a03271a70a02a71270a03271270a02a53672211253672201253671212253671202a53671202253671200a53670a02253670a01253670212253670211253273200a53272a01253272211253272201253272200a53271200a53270a02a53233202253233201253232201253222a01253222a00a53222201253213211253213202253213201253213200a53212200a53211200a53203211253203201253202a11253202a00a53202201253202200a43672a11a43672a01a43672200a43670213243270a02a43233202243213202243212a11a43203211a43203202a43203201a43202a01a43202a00a43202211a43202200a42a72200a42a12200a42a02a00a33673202233673201233673200a33672a01233672
  | 4 => 0x83c73202a83c53202283c33202283c23202a83c13202a83a53211283a53202283a53201283a53200a83a32a01283a03212283a03211a83a02a21a83a02a12283a02a11a83a02a11283672a11283672a00a83672201a83671201a83671200a83670a21a83670a02a83670221a83670212283670211283272a11283272a00a83272201283272200a83271a00a83271202a83271200a83270a02a83232a01283222a01a83222a01283222a00a83222211a83222201a83222201283221a00a83212a02283212a01283212a00a83211a01283202a21a83202a12283202a11a83202a11283202a01a83202a00a83202211a83202201282e73202282e73201282e73200a82e72203282e72201a82e72200a82e71203282e71202282e71201a82e71200a82e70a01282c13202a82c13201282a72200a82a71a01282a71200a82a70a03282a13201282a11a01282a03201a82a03201282673200a82672a03282670213282272a03282270a03282253202282203211a82203202a82203201a82202a01a82202a00a81e72a23281c73202281c73201281c53201281c43201281c23202281c13201281a72a03281a71200a81a70a03281a53202281a13201281a03202a81a03201281a02a11281a02a00a81672a00a81670213281473211a81453211a81453200a81433200a81273202a81253201281253200a81203211a81203202a8120320
  | 5 => 0x273202e81273202681273201e81273200e81272a00e81272203681271a00e81270a02e81233201e81213202e81213200e81212200e81203212681203211e81203211681202a11e81202221e81202211e80a73202e80a72a03680a72a01680a71a03680a71a01680a71202e80a53201680a33203680a33202680a33201680a32a00e80a23202e80a21a00e80a03202e80273212680271a03680271203680223213680223211e80223200e80222201e80213211673232a00e73222a01673222201e73212a01673212a00e73211a01673202a12673202a00e73202211e72a22201e72a11a01672a02211e72211a01483a53211483a53202483a53201483a53200c83a03212483a03211c83a02a21c83a02a12483a02a11c83a02a11483232a01483212a01483211a01483202a12483202a00c73270a02c73212a01473211a01453672201c53233201453213201453211a01453203211c53203201c53203201443670a02c43272a00c43270a02c43223201c43223201443213202c43203202c43203201c43203201443202a00c33672a00c33670a02c33272a00c33270a02c33213202c33213201433212a01433212a00c33202a00c23672201c23672200c23671202423670a02c23670212423272a00c23272200c23270a02c23212200c23203212423203202c23203201c23202a12423202a00c23202200c13672201c13232a012
  | 6 => 0xaee90cbbc232ee88cbbe931f5250dea92b7aa47302534c08cd30292b2ba446b6832dfa4c2a233313a4005a22817251032934caa4c54e9108c8cc1ba328ec8cc1a23306888c1a6930688c81a6910ea84809a22826a444b690329a4a1fa3281e88a07a9149488a3de8343ca4a7649401094c04673011a0c0429301088a01a220048cc01673005a0c01221a07a4681a9419094c646928d294c34a3333c94c53a5314e8cc53a8314ea4c53e90ae68ccb9a132e7a4cb9a932e6a4cb9a919f3250c96922dba4802a2247294d1ca33001250aa692683a33202683a23202e83a21a00e83a13202e83272a02683272a01683272a00e83272200e83271a02683271202e83270a02e83232a01683232201683222a01e83212a02683212a01683212a00e83212200e83211a01683202a21e83202a12683202a11e83202211e82e70221e82a73211682a73200e82a71a03682a71a02682a71a01682a71a00e82a70a03682a43211e82a33203682a33202682a33201682a32201682a23211e82a22211682a13201682a11a01682a03211e82a02211e82a02200e82670a21e82273201e82271a03682271200e82270a03682270a02e82270a01682233201e82223213682223211e82221a01e82203211e82203201682202a11e81a72a03681a72a02681a72a01681a70a03681a53211681a53201681a23202e81a13201681a12a01681a03202e81
  | 7 => 0x3100a0cb92532e4a4c0322214da431b232a91a40a2690268a04f62923d8a04d5693354a04a3e90175a42ffa533fe8ccffa929dca4447a5311e8cc47e90434a4a68e9093fa40bd2532f488cbd2912ce94cb3a33131a407f29113094c4c233131a412725349c88d10a9297a94c49e903f8a4504223410a4c79a909e724e79a9396e94c496900b494c92a5331ba40e2a91119a40466903f088c912234ae90d2ba2330c88c52a3314a88c52e7314ba0c742921d1a44742911d0a42e6a92b9aa506ca531b3a50e2253388a4ae2291388a505625336ca4adb29410494c41694105a5025a5309694c25a23097a44faa533ea88c8da5323694c8da233c2a4af0a912fe84cbfe732fe9ccbfe911a920c6a2830fa8cc3ea230fa84c3ee730fa9cc3ea830fba4c3ea932ba94caec832baa0caee9329a88aa6e9127e94c9fa2327e84c9fe7327e9cc9fa8327fa4c9fa9327ea06e629119fa4a3722334288ca669212fa40eac94394a44e549437d25030a234c2a4530a434c288d30a924c2a44cba2332fa4600a9100325110293079a4c06a53229a4c76c94376a4adda91917a412b2534ac8cd2b2929aba0c04a5301308c04a23013a0c04c93012a4c04a4281288a04a91143a0d0ca029cca486ba531afa4a5524336aa4adaa9189090c2424307090c1c42307088c1c69307090b1ea430ee94c3ba330ee84c3ba129c694c66243384a4ae1291
  | _ => 0

def word127_16 : Nat → Nat
  | 0 => 0x32873a463c2530f08cc3c2130f1a0c3c2830f1a4c3c2930f084a3c692a0fa4683e9099a94c66e9299ba4236a530da8cc36e928dba46542531508cc54283151a4c54293151a4222a1308aa0c22e9308aa4c22a3288ba4651253144a0c51282945a4a7de919f7a4260253181a4a606908c094c302330c1a4a30691b2da4420a13083a4c20a93083a46ed2913b4a42ed2903b4a4eed294115a4a456900a314c28a530a288c28e9283314c0ca5303288c0ca2303284c0cc94032a50fba133ee84cfba92bbca44ef290bbca40ef293bbca5090e9024284c90e92a43a412aa234aa80d2ae734aa9cd2aa92bc6a46f1a913c6a42f1a903c6a4ef1a9430ba42c2c5330a94cc2a2330a80cc2e7330a9ccc2e92b0ba425225314888c5221314880c526731489cc52683148a0c3fa530fe84c3fa030ff9cc3fa730ffa0c3fa830ffa4c3fa9307688c1da030779cc1da73077a0c1da83077a4c1da930768caf92233e484cf92033e5a0cf92833e4a4c89a5322688c89a1322680c89e83226a0c89e93226a4d2022348084d202034819cd20273480a4d20222ad488cb52132d480cb56732d49ccb56932d4a4c3d2130f480c3d2830f48ca3d21280888c02213008a0c0223280888a02212808a0a022223e084cf82833e0a4cf8232be084af8282be0a4a87a1321ea0c87a32a1e84a87a8285a88c20691c96a430729284e88cb7693202a504025
  | 1 => 0x6908c694c31a331288cc4a692129a40d9a33366a4ad9a92366a46d9a91366a40d9a93b66a502ea3304894c1225304910c122430488cc1222304888c12692048a4612494048a512e4434b890d2e2234b880d2e6734b99cd2e290bcaa4af2a91bcaa44f2a903caa4ef2a94321a4ac822332104cc821332080cc86733209ccc8692b21a42d4e9335224c7a2919e8a425c253171a422da530b68cc2de9184294cfda1331c80ce329138ca42e329038ca4ee3294165a5046e900a50cc292330a488c2969183888c0e22303884c0e2908392500e2943f284cfca133bea44efa90bbea40efa93bbea5091e9024684c91e904b088d2c2034b19cd2c2734b0a46f2292bc8a44f2290bc8a40f2293bc8a50c3e91b0f0ccc3a3330e88cc3a0330f9ccc3a7330fa46c3e91b0fa46c3891c4d0cd1322344c84d1320344d9cd1327344ca4c686908de8cc37e9185e88d16290c20a467ea919faa4260a53183a42312530c48cc3169185094c142234c484d16290c20a47082931eba4611a5304688d2da92c8888d222034889cd222931e5a467969096a94c5ae9296ba422b2530ac8cc2b6928ada460fa5303e90cc520307a84c1ea0307ba4c1ea9307ba460d25303488c73a921cfa4673e9095694c55e92957a4240a4309294c24a33093a4a24e91afa88c51a5314690c51a3314688c51e83146a0c51e93146a4c1ca2307284c1ce93072a4c1ca
  | 2 => 0xf272bfca4a0da230372500da9401488aeea94386a50da29434114cd0253341a4ad0292b40a42bc2532f088cbc6932f0a4cbc2932f0a440f22301888a0629246480a64a530d48cc15a5333e94c21e91ae894cba2332e880cba6932e8a4cba2932e8a48ba29086ca0a9d69302288a08a910f8a0d152903dea48f7a803dea40d6e931e2a40fea531d724f0b292c9e94c5ca530b894c74c9395c94c2625302a94c8ee9423ba50c0c93a9c88af32533cc84cf32033cca0cf32933cca06d1e92347a4038e90345a40cc6918b090d21243210a487e4940aa8cc1aa3208e8cc03a2280f24e0a2228212507fe9198a94c62e928cc94c33233333a4aace90c52a42a2a81c18a469ae91a6aa04f6a933daa06f6a80b57a4cd5a81b56a02ac692a7294c962533b8a427b2911eda427b4939eca4f22a5348a94d22a90c1314d04a53412a4ae929017694c5de92977a4262692ae08ccab2532ada4a94a533b6a4677e919dea4477c939dea4ee3a92967a4a59e9092094c482334828cd20a91ad7a4713a5344ea4aa8e90baea44752921d4a46752911d4a42e7292b9ca4457a5315fa4a57e9090a94c42a3310ba4a42e9209c94c2723309c88cb42232d1a46b4690c6088ca7a5329e88ca7a82a9fa4aa7e90a6294c98a23262a0a98e92a62a0698e919a494c696929a5a42392530e48cc392928e4a46bda1327ba48ad692ab5a4261253185a4a61
  | 3 => 0x26a5302c94c0b24302c88c8f2534a4a44c169145ea4d0aa5342a84d0aa0342b9cd0aa7342aa4cf3a92bcea04d2692b48a0472e9013da4018a4306288c18e92863a4818e910b290c2ca4331884cc6273319a4a6c69289490c252433e890c8d2434a284d28e734a29cd28a92afc84cbf6732fc9ccbf692afda441d243075a0c1d2833e290cf8e833e2a0d1f24347ca4c3ca130f29cc3ca12c2708d09a134269cd09a1285ca500929425a80a96a928ce90d1aa92c38a4a95a433a6a40952433b0a48ec29139ea446de929b7a4458243161a48dc29210c8cc4369290da48b4a432d288cb4e922be94cafa82abfa44a0a53282a0a9924326488c99282265a4899281476a4b1129284494c112234b59ccc7a031b5a446d69415a94c56e9215ba4441a43107a4841e9423894cc0692301a44c0692300a48c0691300a443f2230fda0c3f2830fca0c3f6930fca4caf2532bc90caf2332bd9ccaf2732bca0caf6932bca4caf69128094ca023328088ca06732809cca0283281a4ca0293280a08a069226088a98281261a447269113a90c4ee9206090c18223060a481829116c94c5b69296da402ba330afa461025304090cfd292a49a4092253249a4a9269031680cc5e9007da460725301c90c0723301d9cc0727301da0c0728301da4c0729301d250072943e690cf9a333e680cf9e833e6a0cf9a933fc94cff2433fc8ccff2733fca4cf
  | 4 => 0xf12943079ccc1a7330724ec1a93bd080cf42833d0a4cd2a0334b20cd2a8334ba4c83294200a50dfa92b3494ccd233335a4ad8e912c5a40a928226ca089b691bdca4cf7281bdca02d6690359a4cd6693358a06d6691359a44d6091358a02d6690361a447ba921ef24e7ba939c094d2325348c94d2324341490d33a924cea40abe929e0a48784939e0a4e6fa531bfa4a5a2431a694c69e929a7a4239a530e68ccbe2532f88ccbe2132f8a4cbe291af8a42ade9298694c61e92987a42322530c88cd11a534468cd11a130a690c29a434b290d2ce7331090cc46733109ccc46918e090d31a91c5aa4d2fa92c98a4c82691a09a428229419494c65692995a42e0a43382a4ae0a918d694c35a330d7a4a35e9188908c22213089a4c22293089a46baa332eba4c81294113a4a8ce9425e8cc9422303094c0c223241a50906944a99ccc2493bd288cf4a033d2a0cf4e933d2a4cf4a80b4da4cd369042884b0a292b3ba411e29318c94c4e6928d08cccde92885a47282234a0a4ca4e90490a4524290486a4119a92c00a4a48a43123a4848e903b2a446ee92911a4a446900a090c2822347ea4518a92ac3a450ba92a87a40f52433d488cf52933d4a08f528134e90cd3a2334fa4cd3e92b4ea08d3a81141a401924306488ca569013490c4d692135a4014a4305288c6f6911bda404724311da484769003a90c0ea2303ba480ee91109a50
  | 5 => 0x4adca9210e94c43a3310fa4827a5309e90c27a232c094cb069144a94ca82532a090ca82232a1a4aa82822a1a48a1253284a0702a5326694c99a4326688c99e92a67a4a99a82267a4899a810e890c9f223364a42a3690271a4a9c6919328cc32a430ca88d12290a8da06a3281a8da42a3690424a490928142488c9c693271a4a9c692a71a089c282271a489c691a71a469c091a71a049c28120aa4682a9099694c65e908d894c362330d9a4616253277a4c5fa5317fa4e2fa530bfa4e1325304c88c93e91a4fa432f2534bc84d2f2034bc9ccc9e9021a88c86a0321ba4c86a9321ba4306a5341a80d06a7341aa4ceb294396a44e5a94380a50ce24333888cce292338a447c6913a8a4aea2903a8a4e70e93b9294ce4a92b92a40e4a9397c94cde292b78a40de29392ba4e2f2530bc94c12a5304a94c12c4304a90c12c2304a88c12a133c0a449321324da452ea534ba94d2ea034ba80d2ec734ba9cd2ea7332294cc8a03323a4ac8e91a2080c8869346e94d1ba0346f1cd1ba73217a4484a5321288c84a1321280c84e83212a0c84e93212a4c84e81c3a9c6dd292c30a4af5a533d6a0af5a92bd6a06d4253350a0ad4692b50a0619a5325c94c9723325c80c4da3305494c1523340894d0223340880cdba92b6ea40dba9402e94c0ba5302f08c0ba2302f24e0ba93bec80cfb2943eca508fa0323fa508fe944a79cd29a733c4a4
  | 6 => 0xbfdf7aff7deff5ff3bf77edfd7faff6feaff57fbee7f8df7fa3fd7f8ff1ffbed7fcff9ff3fe7fcff1debfc7faff7f7ef57fdfb7f6fedfcdfbbf67eeedfb9ff3fe6fcff9ff3e67dcff9bb77e7eefdd7bbf75febfdfb3d67ecff9ff2fe7ccdddfbbf77ecfd9dbfb7d7faff9bf3fe7f8ff9febfd7fcff9fe3fc7bcdf1ffdacfefb5bfa7ec7fbeded3ea7f6fe9ff2fe7e4bf9fd3af77ebfd17faaf5eefd97f3fc7fdfbf73be6fcff9f63f47f4ef9bf3f857fcffcfebff3de7b8ffaff77cff5febee7fcfb1ff3fc7fcff9fe37c6fed59bf37c6f8deae690279a406769098fa4a63e90c688cd00a331c5a4ab2e92a97a4b23a4341690c5e692979a42b36912c9a4cb269045c90d172232aba4d08a4342288c9be9326fa4a9be91af2a46bca90a31a468c690c3e94d0fa72a2e90c8ba2322fa4926a5349a90d26a2322494c89682a25a451d2534749cb1d292c1e90d07a2341e9c901a4340688d01a7240690d01a232eca48bb291aeca428b691a2da428725321da4a87690a1da410125322a90c8aa2349294d24a72c9294d24a4349288cb66932d9a4688a53223a0a88e9147094d1c272c70a4ab1e9021890c86223219a0915a4345688d15a722a7a4ca9e92a1494c85682a15a06d7a9235ea4314292c50a4f14293c0ea4b03a93c0ea4f332902e28ccd72923a2a4ae4292c36a410da93c36a4f32292ba0a4ae82911b9a4458a43372a
  | 7 => 0x7df7bf77f67fcff3febff3faffcea7fcffebfd7f8fd7fe3fcfebff1ee758febfd7f8ff7dfdf7ba9ffbef7f67f9ff7eefdfbbbf77efddfbbbf77efdd7aad75fe7fd5fbbf77efdf7bafdd7faff7bebfd7fbd57bef7d7faff6bafbdfbbfb7fadfdbfaff5feff5ff2ff5fefbd7fbf57eafd5bab755eabd5faaf557faffcfebfd7fe7fcfebfd7febfddf3fd7faff5ffbee7faff5ffafd7fedf9bf37d6faff5ff9fd7faffcff9fd7faff1efbed7faff5fefddfdbfd5fe7fdfbff5ef7deff9bfbefbdf7faf75ff37f6feefbcf6bfdfbbfb7fabfcffbfddf6bff7edf7bfb3fe7f9ff7defddfdbfd5fe7fdfdd7faff7defecff9fe7fefdfaffcffaff6eefddf7bef7fb7fe7fd77bef7bef7ddfbbf7fe7fe77defbbf77edfdbfbf57bdf7defd9ff3fd7febfdefbef7ecff9febfd7fdf7bf77f67fcff3ff6defbdfbbfb3fe7f9ff3fffcffadf7fcffcffaff9bfbfb7faff9bfbf577dcff5ffbbf7dcff5ffbee7feefdf73ff3abef3fe7ff3a87f9ffade7bcbf1ffb55fdddf3faff6fdaff9fe9fe7f9fd7f77f6fe9fdef7defbdbf93f6bed7ecbf9ff3fe7fcff7fb9ff3fe7f5fb2fe7f8ffe5eff57fdfb3f7eef5febfe7efd79de3f3fafeffcbf9df7beefddfbbf7eafddebbb77ef5defbdf72ef5fefbd7fbcf5debfd7fbcf5debfdf7aff4fefb9e73fe5fcebddfbaf71eefd77aff7fcefddfaff7defbdf7bed7dcebdd7bef5debbdf7b7f6fe
  | _ => 0

def word127_17 : Nat → Nat
  | 0 => 0xfedfdbfb7f6fefb5b7bef6debbd77bef7eefeddfbbf6febfd7faff7defedfebbf77edfd7faff6febfdf7b7f5feaffcfebff3ee7ddfbbf7b7beffdbdbdf7f7debabfdfee7f5ffbf6be9fd7dfef7eefeddfbbf6fedfd7faff6fedfddbfbbf7ecff9febfefedddbdb7f4fedfd3fbdf6fedfdf7a3fc7f8ff8ff1fc7fcff9ff2fe7f8ff9fe3fe7ff65f4bfb6f6e6fcdf9f63faef97f3be7e8ff9fe3fe7fcff9fe3ff5eefd9fe7fd7fcff5fe9ffbdd7bcfe7de5ff37e67aff9ff3be7abfc7fcfff6faff7defd9febfe7fadf5fabec7f8efea775f6fcffec7f0fb5fb5dfbade7faffcfebff3de7b1fe7fcffdf73fefbefba7f9ff3fd3fcff9fe7febfd7d6ffdddbfe7fcffcfedf9ffaff5fcffb75eeefddfbb7faff5fcffd7d6fedffbbe7fcfedfdbff7beefddebf9ff7df5fcffbfb6ebdf7bef75efadf5baf7d7faff7baf756eadd7bef7deebdd5febfdaebdf7badfd7faff7bef75bfaff6febfdcfebfd7fe7fcff9ff3fc7f1be7fcffe7f5febff3fe7ffcefdffaf6f77ef7df7bf77fabfcfff6ff7bcf7bef7dfdbfd7babfdfdb7f6fed7faff7defecff8fe7fddfbef7eeff57f9ff77f7debfd7fbfb3fe7fdbf3fedfdbffb7f6fcddfbf37eeefdf9ae77aeafddfdbfd5fe7fcffff5ef7deff9bfbfebdd7fcff9bfb7f77de7b7eefedfeaff3feff77defdbef7f67fcff3feefdfbbfb7fabfcffbefaff5fefbdfd9ff3fcffdef3df7bef
  | 1 => 0xf9dfbde7bdf7bef7defbfe57fefb5ff6fe9fdfdafb1fe7fc7fb7f7f4df9efdfabfedfdfd9ff3fd7febfdefbef7ecff9febfd7fcff9fedfcffe7f9febfe7fe7f9febfe7fe7f9ff3fe7ee7fcff9fe7fcff9faefdfe9fff7bcf7bef7ddfbbf77eaff1ffbf57f8ff9ff3fdfe9ff9ff3fe7fcffdfb3fd7fefd9ff3fd7fcff9febfe7fcff1fe3dfeeddfbbefbd3fcff9feff73fa7f9ffbdd7bef79ffbf47bf5fcff9ffaff3fb7f77eefbdf7fa7ffafe7fcffd7daff5fcfebfd7fe7fcff2fe7fcff9ff3fe7f9ffcfebfd7fe7fcff3de7bcf7fb7d6eefcffbbf3fe7f9efcbe7fcff9ff3febfd7fcffcfebfd7fe575eebdf3fe7f5febff7befb5febfd7fcff1ff3fdbb87fad75d79ef755fe3fe3fcffdefbf67faff5ff3fd3fafdbee7dc7f8ffcdebdf378ff5df3dc7f9ff3fe7fcff9ff3ffdedfdbfb6fedfdbff7def7decff9ff7ee7fdfee7fcfe9fe7fcffcff9fd3fabf9ff3fd7fe7fcfe7ff3faff5ff9ff3fbfb7f7dedfdbfbef7dedfdbfb3ffcef9ef7defb8fcff9ff3ff6fefddfd9ff3fcffabf9feafe7faff5ff9ff3fabf5febffedf5bbf73fcffbdffb7d6f6fedfbf73fe7f9ffbf73fe7f9ff3eff6efddfbdbf3fe7fddf3fff6f6ffdbbef7ee7fdfb9ff3fe7e8ffcf67bcf7d7d6fb5f5beb7d6fadf5bef6d7dadf7b6b7d6fbdf7bebfdefb7f5faf7dbfbdf7bedfd7fb7f47f8ffe7bdd63fd7d7faff796bed7dbdf5febfdc7aff5
  | 2 => 0x181a03e2dc684a15b20f8212805c6b827dca15c2888040429f40154103e2e4b6d7091407c07c0491601205c1f00716e0dc048087dcfb250cfa04c01c1f00903e88c1f2e05b8b867d01a9421081504700a0280200900600a7d801000fba50cfa08e018150479f6028020090073e81500294211004a800507240182805401c15028ab002a50cfb9f40a9f75580152867dcfa71c658e480418c46eac03f22b3ecba2fe506a00e4a2344402a508269f40f97f28239288d1100a5072867d02607c0a81455801445650cfb9f40aaad00a7d92867dcfa8ff1febfd7faffaff5fd3f8ff1ff5febfb7f6fe3ddbfbfdaff5fdbfd7fafedfddfbef9ff3fd7faffaef3df3fe7f5ff4febfd7fcff3fd7bd7f9fe7febfd7f9ffdf7beefdafb5f67fcff9febfd7fe7f5febff7ed7dcff9ff9febfa7f5febfb7f7df9fe7faf7aff3fcffbfdcff9fe7fd7faff3fdbfbbfcff3fe7fcff9fe6fcff8ff37e7fc7f9fda7f3fd9fb3f3fa7fc7f9bf67adf5bef7d67adf79ef7d6fbcf7bef7de7afd69ef3defbdf5dedfd7fbcf6fed3de7bdf7befbd77b7f5fedfdcff3fe7fbfd77efbf3fe7fcfebfe7fcff5febf57fcff9ff9ff5fabf9ff3fd7feef5dfbbe7fcffd7faff1faffc7f9fd7fe3d1ffcfd7ff3f5ffcf7baaff5ff4febfd7d8fe7f77befd5febfd7fdbfbfb3fcff8ff5fe3fc7fcff9ff3fe7fbbf77eff57faffe7eefdfeaffe7eefdfeaff5ffee
  | 3 => 0x2583b081288104fb2da5cc13065944178000289433e80380501401001802002002514a10513ee7d2e60bc36432178232b6c0603b0800f405cfb07002c5b80e03445dc785eab20f171c442f47281f0d072a088110b701605c0701522ce3c1f05e07956420c445c61c8bd1ca196741ca83c080094bbba0040191718410800ec05bed18e0957183e044b98638bd082088bd00b0400f863ca201c10571bed0442dc0581301c0462238f0bc104e811b22ab8c3717a39431c1f3950164645e8409440397183e7da5dc0596c04a1046383e7d6a041155971c0500b0b607032a512d80869fd718c24ff288c8a239445e80782b04d55e510289f73e9c78b70bc65ce5005aaebf88b1759f4b7c14d591942d81c4a20860593f8281849fd6e9732f7565712df22ca0c21ca200e0a27d0024fe02009006010028024a29f40aa7d8027d60a0428070281006503f070b605b4a107c0a01c00b9431142003e016100109ca0280fd71ca107c33c101730805e41c0200160580681422ce38201cf88a725718712f20ec6503e896080205580160480681088ae388d9cf22a7257186d2f23181fc4b07002c2003c5c6b605b4a12f20941f0228a20fa50c4508202c203ec07c0f0058412f2fb0070405c72841c00b2da1000680e88ae382f2e33920f8111792283101dc4b0400f80480808e0a80401f5c24501f01f0520200d01c5b22de508d00840f97
  | 4 => 0x625c4b0402d82b83b945154652d8016050e7ae39460f93f8391849fcb997d66e10971aeb0dd1142086507c094058405b2b7cb68140405de5183e0ed3ecbb85f07e0fd118265b817d9b87607e9294155813c274102e80be08c211805b802c0a4fb0ec099c797007817c328b717b1205e8b7890b8cbe0861c0b64058100780ea222d8036068b603f2e01d9c782604672c680410840ed6c82601606c0801a22ee3c119700795601fc445c61d8be1cb1a0745ca89e7d8b60058102d8195f717c078b8c11aed07472c118cb17a0e8658bd07408cbe00b13c4501001007928d71bee07a08c1d82607555c058180200548b38f079562221cb5c61ccbe0cb3a2e55f755810c0fddb03b020b8ce58659f60fc200e044609836865078100700264460f0118261c01014039645202d751770204641fae80a608c1e28045202d41177020465742820140708b8260140181300a04c024051cb4fe090032e15c0b667dcfa0140900504704c0181200a3960200f02600b28c0200900602001001000fba7dcfa05001c042da05a01c0e0085b40240381f50401c0280950001c0180750401416ca300802401808004004004fb9f40a8145589460227dcfa0485d4b70280153ea7d80700a01004803010008008007dd28e7dcfa1dce5430cfe3942f00d05e0793e86803e9420881d8650c61001e808944004104fb050180389cf1760580a4fb04032a
  | 5 => 0xfd760280800e01481402cfac9daec016100bb83f0700a5764fb5b0059f58400501000a0200513ec0e01944644c058140af560218160e2bb0203eb0e20ec6cbebab0bb16e80b086102220009f60801401807e051c781022e194ca38f4464548b865328e3c8aa230201827d91517a02c1f0200280a00ba7f01ce3c8982001c44c5e8b79f64500a3eb0513ec0b00c71e45c062ec02845d723eb17a341723eb9f6121c7ae47d65c45e8d022ee3d119130181827d8bd0160d27d87917a2dc32113600e3d1191405002005c4f07c0241ecfa00e9fc1400b0109fc0102a949560053eb9f73e8c001504c27a2c043948050020090060200100022e0067d3ed9f60256d80800e0788b805014010040020020027d4a47d800e7d91713d2902180a00802401cfb002001f58029f49fc0f00800e45c010062269fc0528100e0100427f00e0080528100e88c020084fe00815adb4fe0200102b94955c130099f73e8011130109fc0280a00802401808004004000259493ee7d047054018013eb22618c204450500fc100080240a003c4802201c1144800e0442997788a2441dca20443580883904128d410070821780885e0c71165180b07c0e42103e88ab8d780210ca0a0200141940ed6c0b69460f81403922c5f4b98392fa5cc4883b19415c059ca0400517183e9465f4b98ca19e5ccbe80b0300440a11671c0f8e8c45396b8c3997d1940e
  | 6 => 0x5cc0a841896bb67d2dd0c00f0110411c28899b03e5da0700bbec0ee3849e00b0825dc1e1730823840a87288a4f1f64fb0381dc1417707e3641dd5808602d3f8145d81dc38cfb0381e4b60770505dd760150805dc0d03f50088c0e44407c5b014077ab010010180016384434440000fdf681c9f61dc0ccfb17a2de7d87771e0a0303ed07e0867d8b717b3ec1f0140806001401c7d81dc6c8400406000583e8880000e3ec9f61dc5b8bd88a1e4100140333ec5e8b75f41801e8772e2e5c0e0143013ec1f0287d8366ac180016384433eb8880027d81c0ee0667d8bd16e1ddc78280f2050303eb0406027d8b717a24432d580c9112520019f61e6ac03eaaeb8c140387d802c0a03f88860070886080b600e01a2d81ddc78d007002c0e01403445ce603faaf111c7ae30ee6006803e72a3403c8b70806013f8d04fe0848a0bd02802d7183b07c0502c98007021870ad82d8014140409f67303c84030155cc04441c20a00c81a07e0f81c08608002d719cc00a3400c8d003445c05838888014c03950ee0fc141ccaaf3ed7183e4febb03c8403003644304004002c00114ab0386220149f60703b91316e2f67da7f041111760190282f45bca45d80641401400ae3e2201917a5c402b8f17a2de7d8200504546c8141b20a00e0194464541f113040100bb828226a041e814ab010d762dd4521802003b0400f821a807d602cbb8142320
  | 7 => 0x73e81a0019401f81e01118c46c6438e07e5d112558019280364a32ee5e4b680c0105e01d865ab019031ca47d60219c8010413ec3ccfb16efb031b8e00e0053f8c10142e8038045020211127f00e0085c03e39a11c4f0bf9f60167d4a4086e45110024fe0205c03b0ca18e510080021e4104fb8882d82f1140801e511ad90c888d6c8650c80eeac28208002c100344fe5ccbb840068b7d7191304444d6f9ca228105718915e41e41c823944218058402eefac0d0650bd1141d80b7d60f842cfa2da0a1f60072ee1e4430850800aa7d89e500b6c018599f60e170ae000b3e88b007010058290084fe0088a80a05001c0e2d901201c099770402dc0081966a0d13fadd2e65dc2003471cb68b8913226b68b7914082244bb87910c2de228019f61000cbeb13c0f970a805c13ec02cfa22c02005ae32ee05815559014010048039f73e8040027d73fa7e1cc0ab3e80e06166c1802f05907d28a228b70c802404017444b6031b8f04d3f832ca20bc18c004a49f401c0aa8010a0711101a051284b7174086896509742dc0f62302a0800a19a8d8ab018c044a40800ec1003f9fc0a8308ee72a1de260bc038068200d007d3ea508290ef3ec308ee07c7300284002d3ea50828076196ac0640c73f82000894808000cfb66c2da2206300e2d83197788a0e411ca20441480a8209488893fa225ba195408070c68893f80766c8896c27f0c6
  | _ => 0

def word127_18 : Nat → Nat
  | 0 => 0x1e01ce53c70461d40786194672000ca273401c078037342f0040070bc00c0380f01001c0600373401c079ca39801c078030180211100c5c0890040070180200380c010030078070bc2d80380f00e1785c0071840300380800e0302f2270c0020062225c00311200800e0300400701889c0400c0bc8899a228448cd19a3340c0b91701d60ee5cce538e67033d9c1736702ecb99d60c00300438e0c0e38b98b616c8899b22466ccd99b0600bccd2804fe07003d6f81502e180e505c9f85d42f4fa7342f00780739403c1580c0c00d40380c00e03ce68bc1782f1700073942f00402b01e01c1a9cd00e03c0380f4448a1702240540300402801e020060540483305dcfe448030014fa684889142e000e18512007054030040070688a00400c01001c060387247283f038724e48e43923941f81d03a720729c83903900e82a1cc0fc2e06303a720729c84a571d290060c80ca040092240a814c3f0b62e82e2504a266e03c039ca04601c1380a0460299b80701e300e41ca04601c1380a04601c078230a62f00380f39401c1a9c83940200382e3260640f55a07356421b8e44833cba556018104bd02c2de03002bee010180040017d4171c711744810c03193aad288201747dd564114a2aad3e81502806801c1f19702a070382da171280212e42e6e40b81759f4056500429f80f96f82822c69170ca09f401c030289f80280200900
  | 1 => 0xab4d583b01b22e0422203aab00081233d4488aaab2e83271188a11788c458b744688c1f81d44622c0ea2311488d1188a44672ca013f2820242f9750581c01601e28272c9f97200c0ca040092805d02f9750e00a6a094039601819408012506b905f27e5d0ba87055a01804aac3370a7111720e0aacba808396ab55600107e5c8e5aab3900b0196ad558032cdc700535c82f974065721558c2812ab55600007eaad1102c06517c14c3f283500b9006065020049740be4fcba9412dc07eb680a28266e16029ae417cba032b90aac60009027014028138075b6b848a04204e0a40505f01408803bea5b2b7c890422ecfa8b79755b2b7c8a1762560681400a0be0241280a02eb848a0170124599b80a01205e2805f02e0ac0502701202a5185f01408803b3702a01c8b0230460299b80702a09c0511400e09c0517622817c048250141088a2db01409cd0027046fa9f60032e73f27d00a04f3f0118032e6109f64fa01408cca4fc2253e9f600a05c0200482e01001c8a02901007c1100800eb7d6c99a0384496fad92ea07c8a0280100681280801356815558aac890040239f408c2997200e0548b02e0100548a00800e0b8128080122d8bd8070bc2e00380f01001c060b85ceb7d170bc44eb9d6fa2e1788899b4a01782e05b0610a4e3a520399460e81c00c19e0640f2249402d8ba0b89442f1c81ca9f85b8ba1cc9f85d0b70610
  | 2 => 0x90180211100c5c0890040070180200380c0100300a8070bc2d80381500e1785c0071840300385e01001c060075da1791298e0bccd80400c4442f19b2e00188919b00800e0319b00800e0300600844a0242f0070b2e5224cfe88a026524fa04b3f003859450b8511228722b85702e14482e40602a012020128097220240400c04401cb79755b2b7c8a17804a02415ca40395641cd5871c890ba5560ee0d0040037d8178040017d4170392de2e85e0382805bc5d0bc1170ee1800f8069f40a9f602201001c159170ee180bc04203401a7d02a7d45bd6cadf03e450ba80804a024159823980588b80c71d5600355619e1083bae408113015b8e22e890034a4ab1558c98402e9565712e15c045d404fa011290150014fc01d3f001006fb08a0090060048a28000f2900500401200e7e4fa002faa2405f17c640159930852902c4a071c15c0ca240a42d85c039326020060394440e5120390140a4040130100322401201112009008890452244480551208902a890452244485051316c0b62e81601555a0b00300d81203245dc7558070746231cb080b903b17e19f132ad058ab0002ab2220800e1700388904583f038890452244483261082c4a271c15c0ca240a62d85c0393261ce7e0e00be1082f8651702fa2305f0ca2e05f4460851188a44688d5680d81022e72eac03a2f81da223903a209c2107e1bd118892fe88c45223446
  | 3 => 0xfa7d8178040037d8178040030540d1709145b65c401829228b6c01822228b6c150345be5e0b89125b2b7cb79145b25d57038e3982e0c19750bc0a815450306024301780102d8bc02a1702dc0480802e0200638f60060cbaca29f8e40e50bc0541843bcfc89a2f00e01919e0aa512e405472cc82e40545d5c81cc9492885e00c2e82e05b06171c0e651ca019e0640f2240182da268b82e92925100e9f87327e16e2e93f0ba16e45c2f1702260beb811700c010888062e04480200622e9f4025a50087280200380c02e0242f0170121780480816c2e004809184020060080181780400c444b91119940b8b917000c448d280400c0100302f22301802003808944e68044a27341c9401742f01c14027e2e85e0214fe07c1803b97172e0700b1829f40a9f600c011110218608981dcb8b952f00700b02a3053e8213ea2f045015444018022220430180700b01922e732ac040aad119c72e40ee608210cf89810aac82a948b808b8084fd3e972043949560005565fe888202e066c2d8c08070c0cd85c33600e0540400701803004007170bb56fa2e178894112ed5be8b85e222671292500bc1702d83085271c0e65183a07010e5100c19e0640f22416c5d05c4a49402f1c81cc0167327e4fc2dc5d0e54fc2e85b83081500e731e38750460880a86139128c00ca47342e5cd0bc01001c300b900e0542f00800e0305cb9a00e054e60b
  | 4 => 0x8018108158c20332827e01c0541dc6102a941115800c217e0d00e4a04440a83bca02da5cc1a4a01845ccb68c2055114ca0c217e07c1502a068e38611c8054e38611ca44a6380400c00ebc9412270100322505e17c0adf7558aac3751201917d3f00e0770545e02102a2f010eac5562f03300b0344481081501c8885b03b875500070151780561dc063ed17c0a80ca82ab40aeac556448064290be22d11972114054fb2230be019119cb02b5009fa2200c17c5b01a0b8054b616d042038e403ba8272c1862216c1700d1412810329f85f00c720b60212da05407d40021086a080a5580b0e41725563002f81a55a0335606e80c068e42ab2e45e22f89a0385c85e0890750340a8154462f0451f702b7d88a83080c17d1116c0340320185c01a4485b02102a2dc1d5f5057086072220397dafb1f51720681017601417c2e00ca249f82fe7e55aab07340903a03355a220dd1908a99e80e9f80a9c811608015c0fc447dc0e5f6bea2e40d0203ec5cc0385f0b803289020390228890071169f82f8064fc03402e7e39022c101f50570701040d4447dc0d01cbed7d85c8202e30162f85c019448101c811244802c8b4fc17c0308a3904493f05fae12280a96d9715b6450150037d8b6c8a02a0064596f877504448152d92e25d56fa805b25bc8a2825001dcbc0155005e007842ab2b89709cd7dc9fa7d01a0540a8145580153f1f54
  | 5 => 0xe05b0800801400708003403020014010048030053f0144fc44601c200280e42f81f0c30de2f0140205f00a0038bc0400a01000700c2f00684004001c030281780241422350001c018b968e302ac0dc01527e7d84007d3f0134a417e0ee7e0409f6000e383f00f3f02003f01a1013e800014010048030053f01402aab3290105559f93ec048415b20980681b0240688bb8f2e00fe232e50ec5f8e58d0080745ca83f10c61cbcae508008c398760be0701402a00e0688bb8f07ce56231ca1a01081102a01a0448ab8f08555572c463940f863b950440e1ca8c30c22de7f38f1a02f00d0409f87281f49f0440ee7f03845e0a41f22a0280825106f89a058204fb1980825116f2ea058ba16e0282e01d829198101f4cfb0400a00383e01a080048402280f81000d0351201c2d95be0705b8401a13f01f44803407c5b8381a0b664f83e080a017284001aa0802820014010048030053ec008009f927c0600800e0200380c010309c70080193f17a3ec010309110b90060d01c8bf17b3e802cfc94877804a8001000c5ca804fc0045b807ab00a85f8bd0ee0167d4a4006a00048b95000053f00716e0200638f5be0aa510190553f00e0774462f4150340552891144731c0aa5116f2ea0d2511752df11d7082a0bcb800400701889c0400cab40ac035580c31180905203355a262ea4440a81a4442280aa220080191106102a722b8415
  | 6 => 0x51804006020010070020027ecfa09a12826a820568940282300e9f80084a5c128c054fa00c1640401e08612802ca300800c0400200e004003ee9fb3e82504309a0a5128060941340400200e0067d043946010120084fe0080c91771c10eac84108111ce48cf0400ac0701422ce381dae688e724200ca07a0801d8c6502080e484c01cb6cb781450410cbd4a10712857311707ab6c0e0b99f40a6509170845e8b781a1720f67d0225052840cc4c5b00705b04219eb98ba4fd5c00a88badf9fb3e8044a100aa083fbee2df3e9f502b012164251165c00aa508089fb3e80303d44ab800302a9f528414bee084129112e09fa064154a1084128150050140100180200e004004fd7dd3ea5084a00c0a82500a0093f4038019f40a8014a104e029408040880a5128074fc0040381100a028020030013f6508019f40a1f503fab2e380a01616c0e0652d89401653fae61852813f98e44a020090097220200380d0142e8038045020a91227d00e0005b02805401c0027d16c0fa7e0bf9f610002ca40541003a02a4fa5ccbc83e0340e222adf5053f02002a2d80a013cfe0e8194320019f727c0403e9f8b840282822c1001f4fe0c01dcb8b9703805a7d9827d81000681c02c0688b9cc085119c7ae50ee6081f0d072a1001416c0540f81e8409fc1841c0771780700d4fc1a00f81449f9fc10e7e83d0287301c04105007030b330ae1827
  | 7 => 0xc0e144ae448a8100c13f5f68bf01c15c89cfd17e2e45f8b99fa0800a0e17d73f40b00c72245d723eb17e0dc060e15d80580a1175c8fae7eb911c2b91f58161c2895c8913018181f5cfd17e0381a4fd17e2e48ab9144a44c5f8b99fa0841e8140520800aa7f016e44898d80c4e451291304002c898bf1733f53f8240105c0bb2da5c044c07029015558678770540700d8b65b0c58074a45cca04ba0cf0ee0700f0b65b003a522e64fe3193f99544a308caa258891103181f01276412b340a91105c83c0a91105b06388e0ac104fd0b01843b0bc0361b40c8cf89b2841c00802511c048120da2ec04012172162ab0cf1781b65180e4440027e8200c73fc3100812200e7e8380a91105b06388e65c1002132ee44369c9080d14101755d81019c040176100b79757221b40a0202de5d5c889102911ccb86d02911ccb8b90da080654fd2de5d4174fd0da5d4b78125c0724e68120540381480801c020092255b61b41023e080086ab38e0ca0e1704fd0da1506222504a9f85b01f080d14620cf5b608036ca3aac18848cfd942038100ca0da05eab282946188204fd01c08015c4732610410cfd2de5d4168403933f4ba96f0720ec14c4707c080e4bee00a020010070033ea7eca30080ac02cfd00e0067d043004fac024a300a020010439fb3e80082b7d401251a82056b7e7d4fd09445e5185709a10d6fcfa0153f651805504a0a
  | _ => 0

def word127_19 : Nat → Nat
  | 0 => 0x605c8430685b0b7a2508210010014042600074fd03cfac2183baac06410a810404e0074fd5e2fac218210320ac0e17a502051731150560800e27f028e44898400420508a8bf1733f540857056fac0d8107224582bb037d6895c89158a4ba2ab0857da2fa252f19fa1001a00c056e448b040068c0d12b912260e01082b2f4a040581a5cc4540c82b04006805b914fe44c201974fe189c8a2522a0840591517e2e67ea812f0189c8a2532e44c21cfd010008038019f4028023ed0553f40500400e0067d008004fac1c8619fa2143b83e1780700c8cf89a0a8218409420ec20043aac1867ec4d17806467ca404010004b490113e918021aac33e5080e178888000439fa080100b917f11c1c8219fa2e45f81c0295648b9ccaae60021877888e441e8290720808901494810c072e60702e41da7f2f0084892db0180502003d0720ee239130860845c8bf88e0ec104fd1722fe7e82822e03aacc4430155c0283daac73021ae60520840c91517e2e67ea81040064898bf1733f53f8e144b3f42ba814ff3f470a250800653f8e144b3f41a27f9fa3851283b9faa041f0595ba0580a0600e2bb11582008610eab4fd49a050203eb0800a41001c0333f512beb2260500a077038064c28439fa101f5cfd0420380a4520b205838aec7d610c108595ba03a220009fa10c100e1030041c89170203857601802845d743ed17e0dd740e1722ba
  | 1 => 0x8a00780744a03c1580806a01c0400701e2e4018c017d3ece60000b527e7e8084fe01c010b8050300378be39810e7dcfd00127c0127f0102e01400f05003cbb17022a44e7e80725403c1400a25403c1400817818573b913921867e8762fc2f00d81a046b9c1f8d00712840380f44a01c0780701e0fc5e0612f8e44e38619fa1d9738bc036068be0d007408c1fc9f020028e380a02071c0780744a0280381001401c0800701ecd40380f44acd405007020cd40500702089c0380f7293fc3fc4893f110044fb0493f5c89c772208ce4b9107e028081c701e0a0081c90140a00783f5ce0400380f44acd59aa2566a0e81183a44ab800382401089410835014080190085c13f67dca10800201d8055040800300a008008204a10640a80d01b16eb664f83f2e03401c2815ce10c0ba827da18c2e44701c0e00bbeb0c61942e4470800301e843aac2040c82b0373f6508767da0184286103c10c1502b9fa1001504303206c15cfd9401d9f702002955976019054c581080e0ec06c15cfd502fb810d56032018070145d80ae7ea7f0402f8218207da464074fd0560653f89d0840800a1809fa6a807076036fb4218200735596f00c2325e2292f101c9fc3b4fd17cfb410c4401c5b05cad80361003b2db72210d40841072b984280e0322e5811125b610dc88385e210c06021aacb900c80e0573f43b01b7d6a041cc440c29f80701e00cb
  | 2 => 0x40100103d00e0067e0290861027e80868ed1c2004301008180808178081808295f0c040e80800c2f1a384005410c20029010018100bc0528953f00116e01c7002a0761001eb4717a1001dcfc9fa000e3a255b618a518030c53f64f82a01010003a7d000014050040040f67e02200a00c010010000a27ecfc9400840c8745b6b840e0b90813f01ec9f0113f421d5912727e320192de1d0111750342e5f503d9f81000ea8200a0ec1000a00800c010070020027ecfc93e368b7bee7d53f0158090768918084000d3f41001d00a0280200300401c008009fafba7e49f00e03c2f80701e01c0780701e01c0780701e0ad1302388eb7c898237d711c0780788e01c078430c20ad1307438eb7dc89cb38ee44e4b9300e03c0380f5e201c07803056a045d0c00569fc5c0be1802f85c80300127e7e85a06a0293fa8100e0105d0084fe01c010b87260d5408c0174e4c1aa7f17c2e0600be9f73f42180093e0aeacd57050e7421b4c7269fc022810142e9c98024fe0205c2da2260ac0111122a0ad6c1702260ad6c16e7d6174038022ecb816d1132e0008139135b4008101135b4b608a8352e044c1aad82dd11c1c44707410e2391304711e2383808711c8ac4722711c0780788e03c0380701e10c1c0610ee2f00e01a1a00a02d49f070064e601c0c2ccc3005b0b410c2182144c0e03b8140c273002cfd93e0a00380f01e01c0400701e
  | 3 => 0x7118050100360fc3b8c04452825016d2e615d124a02e65b40d83f88ae38601c87241dc21823084e79c901b07f2827d03c88a0986022266cb848a2db2e2b6c8a029006b6c8a022006b7c892d92e25d56f9145b25bd402db006735708403580167d11601205c0381a7dc15c2803b4fe0142300950000c16a2600e9f800bec0bc0280185722cb86231145b65c6230030524516dc460060888a2db0ae45a232df2e24496c97588cb7cb79145b289a7f2805c09f9110089f478c152829fc8997027e444021404fa054a09134fe500b81110089f4784150bc0c25f1113380812901d0265da068be07507808c0dcfa1a20400522201401c0833604c0280822266c0280381066c89005007020e5224cfc10111404ca49f40967f02b0540ec6881c0ee5c05d17c0340fdf54fa00c0240506101400df605e00c184050057dc02830024010020120070980a80412d2280a81482401008803d5aab00eaab2e09f43467f0089f44b42e9175013fa7d008054b7d6c912054b7d6c914256068140080ba0241280807408c1d1165c00900411400e0900400904a0201500903efb81200401200c010070020027f4a19f40a81405700e2fa7e81e08727c14d590440827ed55054656ac81d0801d6aa8259f85d421d563261000e9749fc0e67d83e0287302b859038185998600b610c2003b0e810c0c8610813f6520200400a40403b0800740302001
  | 4 => 0x3a0059a1c804e021c80070222ec10a8200e0145d82100e015410bb012a0003803172101c828205a2ec2039000a045410bb05a138088055042ec20390006a00048b9222b60b882800e0500380901ca016d8035c226d700570000b4888425b45bc8a1115b05c420ad82de450270115d20500480e07226c10ae15c013a7f4fb0004442d8390c001c088610c016c5e0590ae73021cfd0820f4204fc0840ec0a019038185998600b73fa7d83907264c1d8219485c4168210808925204e2e2050e602d0660440380605a024018080040cc1084e0287301082800e138088060420100480301000a7f02802201c0a01100e0502f0070220440381402201c0a007086894202240222f01082802201c030bc09c084038060502f01683317831c0380600c044038bc05a0cc0880618e2f01982a0100cc270110220840e04e022a0802a8001200c270115040141080401200c040029f6004004fe93ece6ac4a4aac02011cfa5e0bcdc934a014319113ec07e028632229fcbd0788b900615c5f83b17b3ea7f005948a00018b9012a013f00116e01d110c61733f82b8505002e42b9cd0993f85f8bd00b3ea52390006a00048b90aee785c4feab02faab00869f3e81505773c0a9403900029f8038b70ae3185cb39ab408e7f5569440227d01b44528a5116f2ea15d124a22ea5bce601b71c7283085e01404111010014888134a218c00e510c60
  | 5 => 0x79fe3e40480301000a7d0019400980f00800e45e7f80a008020014fa006fb000ca01f245e7f80a00802401cfa7d600a5000101401d4080401001d3f80204c029408040900213f9c8004bb42933907e6048b80b0c25dc8b8150c201c0300194017010b379400042e007052cd81418108e1841f02966c6048b80b0c25dc14b3622e0543082966c01c030019401701483707a6048b80b0c25dc8b8150c201c03001940172500010b801cc001502845c3083f94610c2033a1a41d48b83807c0557180b05005030980940054059170c2165139819460e021ca207a1025091771c054058bb940051718b60c2b8c8b8470c205010876070b8c8b8470c2b8c0a02006802c0a1170c21a0068070c201c2e1c9010018069176733e80aad800ccd11122700a45cc08151a4164149800c245c02a279413ea7f80b5ba0199a2274440008b97701633c2ca220426001006122e002504ff08e45c038016687227f850390cd0008cf0b234a5004766c068bb80b0b211c21b360346040a9800161941f5580c7281138009f4fbc21d571001900483f9400962c4ff070cdce691701401c3a8040344559ba220ca02d6ea270420299a1c80020988a80a0360059a1c801200c0691466cb80e691766a0201a1175c0068e68070eab819a9cd22e5c40405d2d80040f1c866845ce50027d60202e9cd00e1d40101a226cd400ca000e17004801390cd012807
  | 6 => 0xd92e00200380d08ea0003a7e002164c2820226174c03eb0506208905c300faa2ec6094b160202da2de45021bea2ecb7d6c9702241016c9132dc10003a7e002009f591303a02404113006009401140109f80380200244df598010c44c01559080fac05281008005f511201a0340400700efa82805950045003bea0a0165401140a0448009800b3560429887d4fb00880a22afb13f807008005f511250202800804224fa803859228faa7fc6010ca022c45dab355e7d3ea00e16421bea7d844c0400d7d8020039120040053f91319a0dd110cb500165112e103e0705d8d29425c4c04fa7d80880382b0340705dca11a45c4211809f4fa8b79755b2b7c8a00904a0201581903956113b8e08433c6955608001c0280a008024018009ff28400cfa7d4fb0c10143000a41bca1004174043ea304050bc0613000a03ab39011284038020bb56651d5808728a500160ae0e6ab22722e0305dae416ce3830814080030679cfab010eab18222f3fcba0160760800a0615d80180e91767201806917672600c10161a40a41406122e01513ca19f4b913f05c0ae030109800c245c002220812867f9c966a009400d2081284204a102c0eeac8640c4000c02225c2734040345c2b819abec39acd88bca11760202e8b60064519b02b0052840405d39001c0180d228cd80b2d866a8881418066a89c310080340099a9c905001c2881e002fa82e11
  | 7 => 0x81a0381d41fcfa0fc018150610340703a83e9f41d431ca00c80edf580804010402cff04016404020014010013eb0b22702f0030ea1942086344e002504fa0400fc1582aab010df6d57080602ab01c44e065f68be9fe464158140400653f820072b78061192f116178a7f0ec0505f4ff7da0848a82b03e45010d590561840300cab010e221807d6066ab01c5c889c0a00c5c80ac0c81b0ecfac10a810c31116c0bb0720500304303c89cb6171068101f582b0540808981f300450200210333fc100145e20edf5d597da0e1f63eb0c20516c0bb00d11113819038068b61710861003abea032600890380ea069f502a0ea0697618008044df60437d61da223ea0365c97401017689c2bc585d0215f68be894bc67fd590500700a5570811101e98031006421d597daface683788955eab3ea03e5c82c81901c101730bb44e10c0c8217d807d4080e7264541001f4fe039c99130806017300e0422148a0bb44efb02c8570c89fdc9a272282ee7f91404215e2203903c5c97200c0802ed138340800d03239344e4500e0380280feab8408886001f188032faaacd58aae7343ac447da0e021bec7d6068b9059016b8c5d84044e06410cff034a04058387264540c82003402dc9a7f2261017180b0c4fa9138bb224bc4c000b042164428bb5c6fa9138380ae9fc3139344e4485dcff224084bc0400681888939331489c89bea2ecb7c892
  | _ => 0

def word127_20 : Nat → Nat
  | 0 => 0x611622c02839beb006060e53368a4380124a49413e978ca27dacdd4133644419404818006cd8e50210940280b8047da17c2f8655bf28940a7f4fe04401b363941342f80e032a040f85d01c1013f8093949fc2fa8122b5599b01003e3181ba8108128831a2866c0301b83403207c610404ff2881380a502020e480409a0254000350001d3f00100a0748b33800a0348b3380800d17091666c730040710060588a3360060348a3360127248a336080cd45b01403c0e4158ca50406650b380fcb7d9a1cb22a1019a1c9226b7e50186034458300070c045a501149406180d02b0543482c8609f44583285f03402d719770c61740d2e30165dc03ca030c458303ee89e01e2f4a00aefad6f916668730050737d60040c1c866913c7002494928a2f4a066ebc5f6b344441940c00166872010847014054023ed0be5dc108079404542fbed0fcb7ce591566c1019b1c9226004099c866817c0d3367d8a041582b0c61740d3364fe9fc09801668720158079406188a05e7d913c03c5e9401001a2df668b90e60c222c0203880102c7219a00104a7219a03b014a04101c9008a0003a7e002164218650c80f5f60090000a67d03405202650834014010038017d800c148340ca189f503e94201c000289f40d014007014010048039420081a0280bc00c3206200088a508585000a82182b9400704301f9f415c0528107e010218060560a830
  | 1 => 0xa91614c8c2962052420a406146a8283284fc509e5a1360826a284ca50980612e902597049670910e11eb423070444a0861c10510206483fac07c5a0f2481d2a837a806d540d5981a5483394062120bfa8175602d25059060b09c15a6029ca0510a09fb013310262a049c60922811a302289042ca0834c0f3981c0c03510066280c29815e302b060548c0a620144902654047a808528100401f0403d18074300dc301ad203138054180a2a011cc0208c03e3806e700c16012ac01a5801e8001ce0000067d92900180a0093f00102200e004158099480d0068067d40040500401200e7e00200e034bc80701c05834ae601a1a403ad95be894e48645beb6512a827da3e00d49f070bc803009006020010010153ee4faf2008fb40300a00802401cfb0020224f8025e4fac2f84344c7280f85f0cab7e23a260861745b44666c07e232f1ab1292ab0080473e8c2ca40426208a85f7da600c2ca40424542fbed0be0719b2810560ac3185d038cd93f9859480acc41140bcfb02f8655becd140a7f30b29028188224171f5180310730303ea0bd1622ec6094872c2680950000c118074fc004e5009942014099166712840281122cce0154a330e8f831985444a0a7d236604a0a7d0245009f91f18594672d9c1cb22acd99b1c92261000281322cce01501f0b2348304fa0864583285f03eb980717a0c61740fae601c5e82bae17d6cd8e
  | 2 => 0xc64420c881190fc221f0243d88879110ee221d4643904871110de621a4643304865890a85213c6426148471108a2210c64200c83d3106e220d4241a0483319060e2088840f1081a2102ca2030e4028c80250ff081fc163f2a87db70f9a51f2043e3307ba18f6e71ec0a3d5987a548f3871e5523c61078820f0831e0503bc9077528ee071da563af2075630ea071d25839e8c73a20e6c51cc483969872728e4461c70a38bac70c48e0651bf96379b06e720dc631b80636eac6d230d9841b20a361946be48d6b01a95a34c3068c28d0e21a15433d8467a18cee319d083381466b50cc24197563292464930c86918e903193862470c2c41848e3059060748bfcc17c8c2f6105e868bb6c173c82e59c5c428b7e916dac2d04458f30b12a15fda2b90c56f88abd21530a2a3b853930a66614b4e2931852020a3831464e2891850c689fec13cd4274a84df489aca1331c25f1c4b728964612b0c2532449d3892c8123882451048628902511f0823c14473288dc611a062329845f188b831164e229084508887e510e9a216b841f1083a7105882091040e2881231018a2009c3fa207ecd0fa4c1f1843e2287ba20f6c41ec8c3d6207a4c0f1841e2083c23877690ec921d4903a53073e80e5c41ca903918070300dc4a1b628362506b050d4ce1a64433b2066e50cc86197d8319c0602e0bcca177142e9485c160b29615f9c2b828566f0
  | 3 => 0x5df14bb94176232eb965d198b9d1973502e2965bfb0b73316da52da145af0cb5b216aec2d2c45a488b471168a52d00459f0cb3b1967022cd8259a84b341966232cb8259684b2c3964b32c4925848cb061160812c0c458084b00115fcb2bcca57714ae9295c832b84257004adf695a452b34656504ac90959112adc455a84ab41156402ac8055904ab10956012abc45568caaa0955222a9c455284aa449536f2a31e53eb4a70514cce29612527b8a4181462228bc651610a281944a42884c50d9ca14214204283065048ca0621404527f464fd149f5293e0527ac44f4909e5113c64277ca4ed289d04938e7270064de8c9ba09372326d864d9949ae293523269864d1a099b3132a3264884c70c98b093143261c24c308984193020260424c01097c212f0325d404ba80975012ea525c224af8c95c192b24255484a8a89471128a12510a49f8493e11278324e4249c1093419262124c064968c92a1924e3249044910c91f1123a32468448c0c915192241244404888890f192183242464830c90319200123fc047f888fd091f8223e8247c848f8011f0123dc84798c8f0111dc223b06474948e4191c212380246f888dd111b612368246c808d9091b002360246bbc8c8011905230c04618c8c021178222e8445c048b721166122c86457888ad19154222a02453888a50914822288644f8889d511261224884470488d191143221
  | 4 => 0xa88f9311f2243e3547c198f7d29ef083dc087b614f6711eca33d88c7ae0cf5921eaa23d4c87a790f4b19e9023d1867a180f4309e8423d01c79910f2e19e5613ca8279484f2819e4a23c8d278d08f1829e2643c3ca78514f0511e0633c00677e94ef821de823bc8477808eee11dd823ba86773a0edf31db223b5dc76494ec441d7883ad0a75790eab09d5523a626742b0e7969cd863998873154e4d89c78238e8271cb0e2d31c4f13858870914e0d09c186381a66f990def29bd43379c46f294de021bb85375d06e798dc929b883370546db9cdb021b58436a0c6d110d9e21b347364ca6c70cd8b01b161362846c408d8611b083360466bf0cd7b21aee235d486b898d6b51ac22357c86ad8cd5841aa0f350406a08cd3e19a76334e0669a90d3119a5c334ac469494d2421a4033474668d0cd1711a2a43444468784d0e19a161342886830cd0319a00233f8267e90cf9199ec333cc867794cea699ba33369c66610cc81998b232cd4654a4ca01193c3326c464c8cc961992633240264790c8b2990c3320c264114c7d918d6331a066328cc62218bc43169662784c4e2989213120462310c4209882430f4261e0cc391986c330cc661808c2e19856230a4661308c241984243074460d84c1a1982e4304ca60710c0a2180c4300865ffa4bf6117e812fcc45f890bed117d642f9c65f210be0117bc62f6045eb30bca2178c42f088
  | 5 => 0x15934ab14956052abc2556f4aaccf555d8aa5a954162a6af5499ca8c3550b6a9fd053b92a72ad4da529a085320ea609d4ba32968952acca529949f5292a85234ca439d480328f4a51c14a333d45762896651156a1d1543522862d50912a0dad4102a816550188a013d3f33a7d874f9469f1193dc327ac54f45c9e19d3bc5276494ea569cf253952a72064e2889c30d3831270244df4c9bb95372226dc84d9889b11935c2a6ae34d5089a81934a2268c44d08899f253352a66074ca44993953221a63ed4c496983913031a60014bfc497e8d2fa325e844bc06976b12e1125be44b6c296d092d80a5aeb4b310962112c01a57a54ae0a959852b21a55e64aa4c9519129f2253654a58a9488d28e0251c14a3469450d2871250a54a01293ba526e2a4d284984692f21256224a444938c9241d2415a46ca48b16910a12195241ec480cc8fe911f93a3e4247c1c8f1191dc523a44473988e1311b6323609469d28cf2919462310a45f8e8bba916d422ca94571e8a68d14a52280444f0c89b091345a252d4470a88b891152a2205442cc882990ff421ee643c508748d0e64a1ba743598865410ba1a16e242d5a854450971a128b4224884295080220f8341e4683b15071320d674191882c1d0512209ac4105081cd10253a03c44068680bad00c69fff03fbe07ef90fdb59fa033f3487e488fc719f88b3ee587d6bcf9e19f3633e6067c
  | 6 => 0x7c1b2f2865c46cb70d96b2b2cc465882cb0859601b2ba465646cab0d9531b2a0665286ca39594243274964c4cc9591927232464647c8c8d9591653218264284c8419902231fc563e48c7a9d8ee2b1d256390ec6e998d75319aa630d4c5c958b46b14e362906c509589c231305624d4c44b587c230f0461d06c389186d130d6361a08c32098621b0be26174ec2b1185233098461208c221184023078260e86c1b8983523062360b86c15b581e1b03656058ec07a580633000f5fc52bf40d7e56afb055f4c8be78d7cc22f9065f088bdf197b832f6465eb0ebd28d7a23af36b5e414bc32577d22ef2e5dae0bad9d7543ae9ad5d004b9f0d73b12e7225cdc4b9a8973332e5a55ca06b92817250ae4805c902b919d71c1ae3235c584b8a0571312e2215c408b86117084adfe65be4ab7a156ef2add485b88cb6e196d62ada245b34ab64116c422d8055aec8b5b916b322d5e45aac2b55096a822d4825a882b509169d12d3635a606b4a896935ad10a59f88b3d0167a42ce4259c06b368966b0acd43599c0b338d6641acc22597d4b2a9565052c8c459084b200963e1ac76158e86b1b8d63422c60558adab0f0d61b12c322585c2b0b156116ac08358046aff0d5fb1abf0357d44af9915ef22bd64579c6af2295da12bb01575c6aea115d01ab9a457246ae3095c412b84157044adf895bd1ab74356dc2adb0d5b31ab609569d0acfb
  | 7 => 0xabd00779e4ef3935e6543cbac79466f1f21e363bc5ea7894cf0f91e1b5bc20678298eff51dea4bbc277768ceea2ddc93bb84476f92eda99daf1bb5867698ced019d9a23b2c57644cec591d873bb00175fceebc1dd713bad4675902eb18dd6033ab4675512ea589d494ba80674e88e9b29d2c23a50474910e8e0dd1923a2aa742c4e84adcfe2b9f2373d96e75b1cdf339b2473550e6699cc7a39670728c8e4f91c9b6391e372316e409dc7a538e0471b0ee32a5c5c238b067148ae2691c492b888770f56e190dc2f5b848c70608e0a11c10238185701c6e0215bff237f656fd8cdf819bea3b7c666f74edeb0dbd32379e46f2cade311bc22b77b16eb0add3d1b932371e46e2c8dc391b83236fe36df06dbc99b734b6d4c6d792daab5b481368c46d092d9c99b333365aa6c8d6d8c11b143b61a26c2c8d8395b02335f856bdc8d798daf02b5d646b9d0d6f99ad93b5a446b38ad6495ac40358856afc4d5e91ab92b56856abcad5519aa43353c66a606d4a8da921b51ea6a148d408da7e234f4469d84d3a29a6a0b4d22699c4d3291a61a349a169306d248da463b47e268f46d1d21a322345c368ad6d100da1d1b434168644d0b8da141b42216840ad058da0823408667f86cfd8d9f8233e8667b86cf58d9e81b3ca467846cef3d9cf3b390367148ce0959bc13374b66bc8cd5959a623344466792cca959901b31a866146cc1199
  | _ => 0

def word127_21 : Nat → Nat
  | 0 => 0xc08107808000404080ca018180c0c00d8001c002c0018043400040c002c00303000180c14043c000004040800140038042434280c780804181c04240c142c14084c240818000c081000084c44040004280804601800002c0000107c0000080004541c140408141418080c003c00100024043c0c1800003010000008100010000000000008047c380044046c080c001000240c0820302034a00404000004a0180808040000001404003c000c0400000000400404080c000000202408080c0014043c00040c000030009c000c301818004004000840b414180c04006c04006400280800000004bc00240000000820086c05c5b0ba361671c2c84858070ae92159242aa7853990a1321362c262584b0d093061253c23c7845cf0881610b3420a783f8b07c860f83c1e2683ac9073960e2241bc7835cb069260c95c17c482e8905b120b24415468290d04f1a09844120a821890411607d3c0ec581c430381606b2c0cc58184d02da60526408c68100901e1203824068480c0d0151a024240404807170089a00b2400e68004affe29ff233fd867f98cff011fdc33fac77f3d4fe28dfc223f7c77edcefd815fab23f4e47e8ccfce99f972bf2477e2c8fc3a1f7f33ef247dd4cfb795f6a4bec237d792faaa9f4b1be9087d010f9c25f2f2be54a7c812f8badf0c1be1267c0d6f7c39eea4bdc2e7b4caf6741ebe53d68f7a950f4ea1e95
  | 1 => 0x200000383804c43084245000680c08011c301c001c1008081e5c042c00a47c4c2044346824000c242c900000080004540c78200c808c5c541134147c240048100c403474000084206134001c20081468fc08a44404002c9008a47410740014103c1c046c00600080384804247c10000c9808003874440030b83004204c600c1c00046410140c7400d400786006bc18343800009c60007c600c00b4040c0400380000080c001008301c2c000c0000005c0010543014a038000068280820046010a094080000682c000818182c04c000047010e0b404045808140c044004445008083c40005800080014300018a8000c482004242008083400c8000c0000d0080000500c241018380804000808085400b008340008003c353c446c8c200c080c181804441028002c2800e83c00040088040c0c0400002180640808480000005000245890b0781024001018f0046024741400c808114c0410547c20544c000c200070000b60183c1004004c04300064003800280004000c5c04180804340010443014080544085c0044401400000c00080000c018942054181c100c40c00c1c841810bc0000100c380400086458042c00081c0838009004000820301c280838006c241df43408080800092c2c1400080008382804145c0008080480240404000c0800700408080c8044880558000004a80c280004001800283c282c04801404041
  | 2 => 0xa3fc003b53ab8dd23fc003fc003fc001adfacb20035211f30ce3d42eb70090b2a74be287fc002a1477fc00326d45ccf8218eaddaafaf89d6a8c82b9b80c4962807ecf20c73ce586027fd40c73c493ac03c7ed2f588a2be4b43835d9c1e26072454196b04a7fc0017607e343e84cf3a327349565ffc00000239e5aa5b41c3fc0012408916a8849f6e1101ce1b9b04e3ab11a0d2250796aca95f2bcc7c4c88d196fbba76f164ad7e7a3248fbe47af7010ffc0005650706730c17463175ca45dcd6e4cc037dae80dec5773e1f5b9ac4f9dc5ba12f41b1f498ed65929fd47029beb916d42446179d9e702037158d16a14d4ef75519f62ac14414b15469cad112841c5ebc0cdf22ac1dd463d6fab121e65c90f786c3591a1052e891969d8c8ca5dada3d422e6cde7fc000c407c30d40404600c007c4c280c1c080000141c3af418fc3c21085c195d64349c005464600028041404000012ec100848a0140400b01c00200008582e4c0010080004b52120b40c0018301404041c1818180800000c0c1074000c202c00044890345060284800006c5000c804a42868082004086c00ac1c001810640850203c001c041c04f0185c243c2c04140c0014020c2cc42c4c0430201818f40920000028080c2054384010083074559454043000245c0c300034140c00d4011c0c0008141c0860141c0dbc0c7004240c4c11cc541c01300008158c0
  | 3 => 0xbfc001b2ddb5cc79642b851302be5abe2e01f63bf3eca4d512ffc001785199ddf032c48ae2ba55d9212cd288fe3285fb7eb5a257861c8c09d6bdfdc924936bfc003fc001366cbfc00060d5708d5310535c1e0bfc003fc0007d861b5f53fc003cdc3c9d094d278bfc003fc003fc003fc00062bdfd5febfc003fc003fc003de70661a13fc002267129dd076aa07fc0024ca9d9929fe5ef2d0ff7fc00392c36006fffc00135d58a09d0e02b62884b2c4faa567626c0be0b1ffc002c077d50588adf2e02102c8f5cec3b689516897ff723ae5a30ce970b6c164ce12a102bf2065b685bec9a95cd89892013047676121b862efc25f79c560beb93fc002f99088c4b4e6ce1e22d95ebfd980d2c44c3fc0032da62daa4b1dc50698b988f079c5e044aebfc00162375aa2cc08e27fc003fc0023aa5bfc00009e596ec57a910ffc000be97ac19df89348386ca8009a961fb308afcc4be12d93645cd82b33546f9e2970258486a5a3fc002f1b37fc0010c93d9c94d6ea6ffc003fc0020d8b00455de966a96682ac606080ba2ab4f3abfa202213ad24715561abe0c026bfc00301acec54457d88bfc003da0eefe5aca2c040e9625268a90dcce276b1a80664baa321c73640555009d08b7fc00218947fc0021da71a25d1e613bfc003fc002462e7fc003990dffc0033234d3d467fc0029edc57c25ffc001ea6695ad58c241e0dcf3c097fa60
  | 4 => 0xfc002b49db86894a2baffc001a531f6659318e63fc003c569dc0b2ed49ced864e8cc6cd90318633dec185e1404f4e8872035d8bef5a3db0603b6d5aa9d202541755c096e98de02a8f0470658ab7e8c8a9e9ea05b11000f55de37fc001622aec2d54813761d8a24e46f1d3dcfee83fc0022da285cebc889dcd0e5206c8f367441edd48183bfc0023c8f3d847bfc003fc00144a33fc003fc0029622559eebfc003d2b840a411745fffc0012c27bfc00382b66e4206a6ddc1126715a9fdda33a9de225235989e305239740e9554e41e752c9870cab265e21621256d1d66e0b4ea943bb42c2b00620d77c10d27a203e8c80665a4ce8c98f23ab14feb1c897843d8d982bfc003fc003fc003fc001a071cf2e0f15a00d10d5e61f06a88d0043d417dffc003fc003fc000aab959505f4d98520c39daa60252ef12aa53967ffc000583002d7bffc0008a94ec0b7a6273ffc0029c033fc003d286c3e33621738214a766606ae85fd1b384a92b44ff2ce7c33e3ba7148a259fa64389060417a449c92f618555eade6e0b42293818c77a7a388c445869b75751774e6166411c79905ed420b1d696aad581dabd11fb7a6f8f13dad4968d8f6b1d7e0dd7b646762b26843a9ff367480c60cf0e7a54a09e28f5c06dafde942a08c51655c032ffc003fc00066190ea1702a9d3fc001268e52d723fc001c421b8aabb0a58734ac3fc0010c3f93691
  | 5 => 0xc00128be8e2b4702e1581f0e166f6ecf2ee6463d5664c26c6f47e1e1e9c9dc73b9d0ca0626641a316cfa5c33fc2884087188df27bce058e6b0aac323ec6c3e2dce9f44762fdb61fce5e7ba015aaed1f05823dd7c628a97fc0031c9486509c50f8bfc000d189d7cf6c0e9a34c6b37a8d14ece489a471c3f33623bc1642882820c99caa83e4928098e81e83c5387f09916ffc003fc001e0587fc003fc003b87d0ce51ffc000f08460a904bd416ad6b4ade3bfc0016000cd0273fc003ae679d44dffc000753e598b125223c250b24059d600c3fc003fc003c9b1afdd27fc000f22776dc7fd0d70e90119dcff752d766e33c952dadc3b7a0620836f648788ac4311701846200ec697125cbd98ea29893d315aca8b8e2f4aea9c50b6ca41200936f19a07055a182c76c1cec78a131e2eb487c3d95b08e84e9c7b3fc000882fdc57b848e4bda847a81f6583240de7391619fc703186b47cfecd028874660e9c2fb11643d652ea2d5b6cbf3e4a6c4c358ce3e62e670e5ec9adfb14c4ab6629b0ea821373e42f39549ab6b49fd1dc8c3ee11f3dc900c85cb3fc003fc003fc000958c5657facadb001e83fc003b8a3cc8e3539d3fd062d3cc93fc003fc00205cf7fc003fc00124cdec6bb0252b5fdae3fc003802c6bc71771717c6080a139fc2d7d9141bfc002d22bef95b5f924019170ce06fd06f7d486dac891a463d6495586b07ad7cf
  | 6 => 0xd8536b7f6cc314de52f5818980ab295931e111b80e74dbac2211b19159febe64553835afcd8455e015f1a5d9586337c0e35e6da21d70ecd34b4d1c0e27b96c83d42a74591c62a7b3ab3bfc003fc002c239d89fce9979ca0cc6a040788bca8e77cac55ac88ef947fabd8fcc5f8e2c6e2468ebfc001a08bdc63ce99e5465017fc003fc000a0b3a029214160f053effc002be3f56ed167244006283b46ced91872c1ebfc002866c2b83c1a5582e9072a60f5894fb95ab10c04ca8d98e8451a0bf2f0b0ffc002e14357115f91af235c9e182272a0c0b63c975055c2bcffc00170f71b5773563eb9cbc73e24ba545750f519c2636a6dc45d368cad1601889648b150666d7a0a87b92e8f0cdfd5d278d348b15ed88e80da186ea45a9136def1e32930c562618c725d6cc7d9b8382c5f1134fc6a94ab956ebfc00099c1bfc003a6114a4b15d6a44985eddced3fc000fe54a10d618880098ede14925eeaf66c0797a39768b33fc003fc001cc6e679dfbd8d83a19f19ecb7fc001480f1b48a4c688105a3bc94c6407a9ae99d1163ffc003b0d58528550eacf68c22d4f10d937b8478cb48e8d412f6a29eda5ce9de135e428c42e241de8c1acbe6a2a3a27d164c645078d596ed2bf5d5efe4d5a6b593c30cc3fc00215f3bfc00290f1ee2a57fc00125c833e4e7bd22c91a84140ca65e03d61d21e944f54b17d5762d62eec16f145a79598bf
  | 7 => 0x2f9a6e54a5de3d2af944cf34d95d4f43dd5d65c61fb5ed5ec9968a1cce1895a446504a9a99be6c5d6ee4fbab6c23a9a2eb5076ce63571ba5b16a8ea1dee072f313be91babe41011c4b900052c47849a1201424bd91832a6997640008509502a078d01f56130acccb0ad81e624a8d76fda5c3c0a2218af3cf00dd853a22991a9a7989fa1dec9316a6b4cf7112738c9a4b986f0cdb6b23e14e08679ddb22b15f592529d5c39d75953f5f662c74592ec7fdecb3420e5c7245a21ff1f88605831860ef3d52ab4c48241f9049616090059476c1acb9915d2cc284f506ebd9661c7e7fc0012ed1bfc0003c6390ee09e201c5c00bc5adf0c4ad09aaffc001113b7714829c68eb4d1214dfccd95bfc003948fc744c54038742dbea4c14c4dbe1533791c43fc00146a9aa023565ab5b2e63fc0024688a46c50d092b84ae09210c11688aa9b3fc0020d5e1910bae22437aa67396e3fc000951c43d43f59d553a6387c7b471feca02cc2ada745b401640de2dd1e0af9c01c4753137cd7a66d705475824e77dc153fc002fa565a4cbe52500ad388fdc1079c07dde6f5c3fec8e478c8397e43a35ee03109b99144860914c645612c96966ce03ad6ca1d3576ffc000d5ed9e49c080e87fc0039e6b95c378a837014b75218164db7bd6b722ad0f48468360fda615a59fba02a4339f4fadee54132ffc00172422f96b8f9fa0d085280437fc00185
  | _ => 0

def word127_22 : Nat → Nat
  | 0 => 0x3fc002ce717fc003fc003fc003fc001fcaa3fc0021c510ea8aa30e57fc00241cc19a2a2742d951867a171ffc003fc002c1c647274ffc003fc003fc002484d03969a368c6a2bd7fc000197ca6867bfc00248dc68ed6aee0baf957219c6041799ccb4795f4b66647ba8430ad01064b9fc5b348f87fc003d47d77522aecf57fc003fc002e53f35664ca16c3fc003fc003fc0036954452a306e096f405828653fc0016ad8558243c6c18fe650b2257fc0014673aac9effc003b4b248aa727552a05a35d9136ad1e869fd114337fc003fc003fc003fc001942fb50c4e0ee41f49b2de315a53fdf5c2101b7fba8a500fa0840fa11be1a02d216430446bc2083378c2dd4bfe6425335fa6c830cba467a52331cb4b25cbd244f0e5048255fa5abbfb2c4c0a1b7e5d7f8a6e95d2456a7dfacb956c5b949693b8d048cd9e4c6dfae95f24e0bfc003a590e5298e40042d5486b8e4c0e78618e2b9e09d6e8af210dbfc000565fd92877b8958b2d8e0837536adb51fe3a61c2859cfa69c43d788d5b490e3429ab4002e7b92e7f59463fc00381518ac43819b2485ece743a2658aa9e7ef3d8b6d6cef7d835250d3ae9bab08550e965524716e148f8936e9223fc0019622ffc001e178ffc000a636e2c027a8eb8a00d436d36a11b2b5ad4d6017c4119c60ebfc00355579bd533fc0018d33eaa146fae1be21d849cd65d5cee021519bd47a296dd7
  | 1 => 0xf5f6778654c898b958911605db0a23fc00071046a0bbe86df4c59aea545decaffd0ab0b5478a91bdddf066dbb3fc000187351155ceca4bfc000da667fc000dec0f127d8710bd5e611e94492d133fc001e9b505deb3e00ef9e4d878e1082c9e6486784dec6819028c19d527e7cbf6ed398d0782b11699abaaa9b64d1812257d821ba10cd439d3cb06d3a420559cba27cb09457500ea279ed05e937f4475206292047096ca37924ee20f0b0e775e034e8a83528e6c014af78fa814885c44e45a066c01707d7f16045cc697f34cdac93c5cadfffc002e6498e685379296451b4dd902a5307d107cc43601639158a0008aac264f58e5c9e91a4ec1097e211ce8e1b987b7d8da4e83081f80e49e782b02fde2e383a8f8abb20be2a0da8251bad92e4442cacdd45467542d563cda205ac603a933a181ee1a7a3a35aa042901f59d54eee664a0d0b7fc003fc003fc0027890731b5e5dd7b509fffc003fc003c444bfc002641e7c10f9495e7fc0021cd19a9fc6a02e5f159744f17511f396599ca6f229e6a681ace43385dc584a0ad24a8760a2f14dc876657d631e82073d8df8e53674d1c2846c34dcd1dd163420d7fc003e65f3fc003949cbb8c43c67bcb9c30321534a2b17110848f1b8a849b9a7d06d2135ad246355ca66cd50ebc5befba7fdf1e33ce61e4cbdb85e1ec6ae0dc125ba61a1a742012dca98e3fc003fc00176b77fc00
  | 2 => 0x64306720423c0ace99990a85a0193ad96d68b6b657f96bcbbc5d205d81152d1d002e78539bc51dca576be959dd127fc0024ec3d8a8643d05b1eac60157f911236cf342c321c19fd1daa30c0b7165b7fc0004eca3aac5d29285c5a1e4ac9bfc003fc003fc002c2878d12a5a03bb8c3dd166951d96b89b14742af907f49803bfc002edb97fc0023620d22487fc00014b8b454f5619174839725ceae269304267b1dae19d18c0503047bffc002205b522e2ca452d8456be9f0bfc003d841a7234abcdae78e2cbdd09c9ffa6530ffc003fc00328d4ffc003fc003e08e04c1aa9679225934ced9bfc000415984c367086089ccf86eb88fd5ee5e8ced0d0bfc0012c5784223558309c2452e5a3f413c3fc00268f3fca953fc003fc003fc003fc000152ce989748c83f71ce09e2459258c8acdeb96cffc000c0003fc003fc0018a8c038aa57487f54c0ffc002744da7ea83fc002b1f5cd86c7fc0014817ffc003fc000d892dec6a5a542a8c68391c0ffc003fc0007a0e5b8e1b4e81c328f98c6360156eca51a9cc3c0e2016d973fc002e6d08114de89f37fc00068565d64a3fc000e0485d42b13ec97fc000e2aa33e1e692cae2890080eb72df01dce30b2187fc001855dbfc0030c1b70c8bbfc003fc0031d953047dc21933fc003801129cd2b3643fb59c7fc0020574969a54860086d3e2e9a5840733fc002e81ee969de2e80280c05
  | 3 => 0xa79d5c849fc3fc000e2de9c09436a02d00e8ffc003fc003fc00338b3d94acbfc003915dc6d45bfc003fc00012222f94d6f0a2859084354b6f903d9d3544ee1242497fc002b207bfc001de0b7797418de64a5fb37c3161d7c156a0ffc000ad6c7984e3fc0001652cd4b9f914d2b99ec81db19e0520d40ded8683904ffc003fc0020a60e71ab8f23f0e5c5db4b05fde9a12ccb668fcbaab199d2c49af7fc002f91d0acd30d204b6c86ae5a8f2173f0672da95c79594875ae4967fb690cbe8e9cba332f95248dd429550c640bc2993bfc00264162bd5353a14fc8e208d29001997fc000a962472b616a6591c8c8c6e596e7d66a3a4d4d499e9bebe218312c0b9f71f98ccd21645e9f1ee7782446ed60d1dadab019205ab8dfa3dc4c90bc014018a25724909a9fadc4ecc69cda0af780fa6f03e44de4e8d41f201b3da729c9ca248a7b8dbbb00809d99bedcad6d2d77b81bf227d0fe418619cbfc001e1e3e30d17fc000e8985221ac0c90fea5beb1a48ee597fc003e81b80a3503ddcb0e41545322327275194fd67ccd5023fc00358d212819c926a889793fc003fc0003085bfc003fc000288366861bfc003fc003fc0004cb63026a45d4cd600058075d8cfcfc1875964cdf5c54119eb7a4abfc001dee1d19abc88f0ec49212637e40c8f66e45f5defca5c658573a9aee6517f10fd2e15c1b8cca7deb75ca801c794fd638eca8e3
  | 4 => 0x4bb9a8b299990ea11cdc03fc002f534ee1a0d9a6e27ab543413ffc001e5403dd4c2048c7fc00088d0e5108321bf878b73604fde03cffc00380811a1caad18c3fc003fc003fc0015580f11cb68a9c9f1fbca4db3fc003fc003fc000e0ceca5397fc000fd541787770649db8fe5cd3eb35df584769a09ba84d6ccaadd4a5c0a93a0d16206473b9599c3963019f7bfc00124d3ea29c025b23e9f7d3870c0edafe48774a8b820998ddc0b59eed4230439b4c90f2389332e0d7d7974de10902d809c048972526f626ab43ca6db73cdb9f3ae6e7044e8a04f1d6f42161fc082de40dffc000320302a89c85fe695db7a40449e5157ae852ac65692b3fc001aa6ec0cc2505e4a55763fc000299a7e95b9703d278c1fbec2909502b532860df1041d274c12f2a7d3c5f3497780038ffc003fc00206d3370a1bfc00192cc0b1648681cbfc003fc00071e8b90d891c97b48699307c9cd13f5965b2aaffc85ca4e59e7135fe458c7ed3ed88aa1ec00318bd5ee5f2e2b7963c50566181a69947c620ecb3950b29a17413afad7576047e3dda38d6979a812c6b3596bb64d0619d72414c9ffc003fc0032e46bfc00135c87d59f521ef8a4a61c23ffb9dcffc0004d4c82cca1be977fc0001d408e120f30416193267806e592a0f8074253384eba42668f3292525780527837404ba8e9601d2b08fb3fc003fc001619aa3206a55bb7fc003fc002b0
  | 5 => 0x30ab0a792fab5f96767b3b8723700367247a791e2d9118e0181dc55184a6bc9cceb2361f9f9c94f31c4a7dc49705aaacce3fa8d0e5616c9716848a2299d13a95a7789b6cc8dc045a4021b2da1ec774a6761a26bcdda309a3a4015c5f29629aec2d7a4d7599d6f10cce851d5029f1c7ea20467adf4fc181026857ef682f5018d030a56b0178a06d0e4442f820d90595f25e8287cf5232f106aea11cd5ee3b51bde54a58f9dbba1634613b2c56e5a8295dd02ce5eaf6625d0176b9eaed09226b8acc9d29ada9038a9ed2583db6999b481835c29f46b9d1e45a27a83d4bc9cbe76841046cf1a0e9341b3240f6671678468d4de71f0a995d0a5d8c89c156da6558ae95490663336bc61cb23c2a4e5413bfc000a515374c60ca0de91a535a93d68e6ae4c8445443509f3a86a11c6871cc95d0070e23e64d956e11ed7a0472440c6991804dead88240ca902d1a81585500db85c57cd8fc94079c81bc32291470adf3524d14bc2940cf8de75c534089dff65d4c96871dc91f24b2bfc000aa05b21e5f5a15411ea49cc28552f1da82492e21708d06abd3a568cb0b5b10e65bd178b291d6013604744bc821b1713b4bdc9e28c2872b255acb098fb2863cdcac4d84c796fc646efde35faaa971e6a0590686e00cd526dca8a2585dbe040352c3aeecd41042c9ade2709c7750fce8531b2df2b6c7bfc0039151e7991190433fc00334de0683
  | 6 => 0x40548c9bcffc003fc003fc003fc00151d8fced53e474306b538e58bfc003c2c7ffc003fc003fc003fc003fc003fc000edc4ac2382243bf04c70e4b99b61eb666d7fc001e1e63a98041a26ffc001e41dbfc002c0cd7fc00265d9bfc003fc0029d11ffc003fc0007a0bcd08e6fc760ec8cde2859a8f99c92bffc003cc2762d491027bbcacdac6313fc00081eb8157d7b0eb1a9e281ceeebdf33fc0024c59addd8a799d37187cba546dec701053dcaa53fc0011e7b7fc002304b018df7fc0004e943e2640a5f8a5c5e510427e866f211039d9c1f27e9fe9e77ac26a82128a7f7a9a66bab7bb5c4e49c8d50f4999fb5965e3969119d9e0d015565d48e1aebfc002704776964570bcc4dcc86c67519b546da8348473a4b550ece9299b16648191a0b493cf560cf5c8f7756dc7e9483e476c0964c869db081deaaa9c1520a4d5f4466aaab9c29b8ed8cadd1bfd5423354b51c12047615f2c420203f49840ae242494f9578ccf059e66e54c38f286e7f36e36b80c76453d730ec149318f1e4372db56c2ed389b74ac84f53fbd6700bdff7d1384884e8547486a325dd6d3a501aa94a02183344116896040645608bae880b029a6e4597eb8dd6ed7aea88880c48df1551a5e20fab6869a9a603440938d768169ddd475e7e983b369b08f5b86554db0d5e9f24b27ad82e02586eae695043ae938f4bd252c8908799009f752b833c9156168
  | 7 => 0x6e07020aa810f1861a595dbffc000da7c7fc003fc000b48142a7183d53ce92baa53a7fc003fc0029aa2f68c5ffc002560cbfc001651e7fc0012523ffc000fd6a37695729c8bfc003fc0019ce17fc002bd1cbfc003d4a0ffc003fc0009d2629e0daea1343018dac5a988a3b553d2068bd20b67fc00155ca7fc002ed603662c7fc001e1cc7fc001d55be6637a4e2610e985c839a1039e760b074ca83dfd984ed7fc003fc00105451cc26ffc001760a7fc002669f75dc6fe170efd2fffc001a0d2d8d497fc003fc000489af60dd0b64cb88aaa50444a638df5c47fc0026a309ce2a56d27bd5e1968b93fc003fc003fc003fc003fc0005ea1afc14ffc003fc003fc003fc003fc0032d4302eb3d85f563208bfc001183e3fc003fc003c65739d157fc003fc00278981428dc311fffc000a0a6ffc003fc0014616ffc003fc0029ca43fc003fc000c48d7fc003fc003fc002e0da5145ebfc003e6a360419a9669f5a6d3fc002f1cdffc003fc003fc003fc003550c60954f1d8a7fc003fc00004faffc003fc0037e39bfc00202b2bfc001ae303fc003fc003fc0011e24ffc003fc003fc00094c47fc003c45c07408234085ae96ffc003fc003fc003fc000f080ffc003fc0035613dd4ffeae207fc003fc003fc0027d0a3428b0f9117fc00371213fc003fc003205a3fc00398bb7fc003fc002a970475128291dbe559cb46678202899277
  | _ => 0

def word127_23 : Nat → Nat
  | 0 => 0x8e856b6f7cec7fc00069143605d7fc00014af148b5ffc0034e56e3eb0c6067f6d8d5120fbfc003fc00084f60d8bb3fc0009423db59d5b8abfcc89bfc0008d0e06999134cd2f1f40d5c3562cb288fb53e48f0955a0e16129b63fc003300ae3db8bfc000dae75dd0f4e43127ebd981d3bfc00101ed3fc003e171870f8f460f1e0b83941454a264fcc68a882bfc001d9d9500ce7401fe3ab1f267080cf923a90ffc0037219bac6f182af3fc00125f9bfc0014aba3fc003fc002b282bfc00039e0748f5b297f7fc0028449b9914bfc003fc003fc002da76418aeffc0029c95ffc003fc003fc0012d9bbfc003fc0021280bdcf9f8012ab6dbbfc00078cbb5e4e0fdad8ea839dcba7fc001b549ffc0004d841d9cfbaad63fc0001cbba76c16c4ee0c50297e6fe52983944d754507d167209cd85496c564c3fc00212c2d401f2cd7a7fc000365560e288356b2ea3b4fa7a421fa9aa3841405585fc9c088342436364d331051f128bfc00386dc09c50f5a09a56194f1584f2c100582445c97fc003fc00311424e290bba1d5c81a76d03bd01d7fc003fc0015db47fc003fc003de25a0930bfc003aa3d3fc003fc0008c105bac1eb682234ea035ef480b19868ec0e19cecd464085ea8da3dd44fea55f857377dd1d1413310770ae4bc75bf5a2a6aec24f959a26dec1e63ec2679ef5d132c6d4ee67408dde45bbed66b60d42f22beb00fd9e
  | 1 => 0x27b0a07fc0017ab1bfc001d15f4666bc914b89478bfc003862c340f470a31808543fc00342cabfc003fc0020dfdf14990ac4a3fc001062d28474ef2dcebdddffc0038ed4a467e7fc003fc000f1da7fc003b9b90748dbfc003fc0021e8984d64f1525968a159a534264ff38a5052ad3fc003657a9649a804547fc003fc0023401bfc003fc003fc003fc0000de2724246ea07466175d05affc002ed28fcc208249be85ebc998e7fc00359bc778edbfc003d073ffc003fc0012cd93127c9c45f7852c6b667ffc00191d166244d3d20b368c81d4106e40958cf1fd82e302283406ab185c54603245c5950013049d6ea9315c769c29870256c8cfd4aa5c7c08d45c1f408dce8341a94e90d18b86447917677c4abfc00036338d1728a0fd6de130a1b5a0cfbc6d8f158067fc002e6e57fc0008d944c18cb60d867a9b7fc003fc0016aa1f2160bfc003fc0001ccb3fc0017cbf8fcfdd352eb0df1bfc00069f77fc003b893bfc003ba027b9887864dd6253dd518dd28d8846a980020a8e70c0710d50c16de8e444c8f07902a6739e3b2a10ef095640049660e4272d4f7a3668e5e56146d5c65eaebbb5c62badf699d0a7b911145ac0a17eaa1e87410ad598817e795dee28e617d6c952e09eb66323fc003751adf409dc2d4318a46d5c98c0ee6a4ffa199b65cd8cf6818f8efecd976a1c2600a73aa9d775b68c1f85c4c5836a87387e8b1
  | 2 => 0x8ecc7fc0013ab5ffc003d5ffffc0036e45ffc0022e6ce9642ea439034f7fda7591856f1431d9ee519a96bfc001a29aa7e0237d62af6373fc002e0a4f29dd2ee231c9f14f9846811969d14d58615140fc29af9c588d58ef9aebef9650cfd3632119a482dc2666246c45fae3ffc00180ac6d6dcbfc003fc00150b7ca45249dd01dcb8ffc003541cfbacf64029390c0979505c8933fc003fc003fc000717b176b983c01f195fe28b699eab7fc0019c3291682e2829fd5f62b547f8cd6bddb3ffc0006c05d9ad5d9821dd801179e0fb61ec4670f62c90697d092d6f1a00601de726b2d5016b64a748677030b012dce4f58f76598110bd4ec67208351d956984d6666b23456eeb6e25925a51d0889cf4e9c7a581b2bfc001483a6f0b85fec58ec69385cb85121c15d3089b0f62bf3fc0018cc52a6ac8564d7fc003fc002d977418eea4d193fc000e468be1216fecfe2595db1bf3fc003e510618514984f5742d56d48fe2d9ffc0014d4e2b8c03fc00102344990cc054f0be127b8649c687d56869018585a1bc0d08e4692e0e0e3fc000f9393d6d2ad580278e1cbe63daeae800307d5963fc002b26ac314fe34c665c697fc00159034a192ce2abffc003a5aaa0a2a8751d6b43548e273fc001fae37fc002a29377dd63fc003fc00160ece40e0ffc0013854f423a0c8ae7fc003fc003fc003d458391c14551f59c613fc00041b04b4f
  | 3 => 0x919901511100d19509508d00911b41909500511b40519500511b39909500511941909500511939909500511939901500511919509500511919501100911909901500511901b39500d11901919500911901908d00911741508d00911101108d00909b41938901509b40d09500909b40939901109b40901508d09a41d01508909941739901109940901500509939508d00909938938501509919508d00909911508d00909911101100909901938501509901909500909901908d00909740901110d09739108d00909539108d00909511101100909511101100509501108d00901b41938501501b41919500901b41909500901b41908d00901b41519100901b41508d00901b41138501501b40d09500901b40901508d01b40538901501b40139909101b39901509101b39511100d01b39508d00901a41d01510d01a41d01509101a41d01508901941d01509101941938501501941919500901941909500901941908d00901941738900d01941508d00901940339909101939901509101939508d00901939138501501938d38901501938938501501919508d00901911508d00901909508d00848d40539901448941d2990133d9d905ede80f77783d634e7f8091201510ea47dba21cd4ea7fc003fc00365943b9b023084cc675d4ed6524cb55e7e3fc0020aa3e2d794d0028fda18aa79b147548828d657e6b9e1749346de608447a
  | 4 => 0x9500548941b38501548929939900548929909900548929901900948741919500948740939901548541e39901548541e11901548541739901148541738901948529b38901548529939500948529911500948529901900948529901500548501909500948219938501541b39511100d41b39508d00941b39501108d41939508d00941938938501541919738900541919508d00941919501100941911508d00941909501108d41540d01900941540501900941241d01908d41141d01908d41140d01901541140501901541140501900d40d40901901540d40501900940b40539901540a41d29900540941d29900540941d01908d40941d01508d40940539901540940529900940940529900540940501901540641d29901140641d29900940541d29901140541d29900939b41938901539b41508d00939b40901508d39941101500d39940901500d39940901500539901511100d39740939101939340d38501939340538d01939340138d01929939901500529919339100929911101100929909901500529901b38901529901939500929901938501529901911500929901901508929901509100529901508900521901b39500d21501509100519b40939901119b40111900519b40111100d19941739901119941738900d19941101500d19940901500d19919739100919919738900519919501100919911901900919911101100
  | 5 => 0x41909501348d41909500b48d41501900b48d40539901748d40529901348d40501900b48d29b38900748d09b38901748d09939500b48d09911500b48941d29901348941901108f48941101901748941101900f48939138d01b48939138501b48541501900b48540d01900b48519b38901748519939500b48519911500b48519738900748141d29901348111939900748111909900741938938501741901509100740940539901739b41508d00b39b40d09500b39941508d00b39919508d00b39911508d00a4a101919500a4a101909500a4a101908d00a49d41901509249d41901508a49d29901908a49d29901508a49d01901509249901509100629901908d00a21901938501621901919500a19b40d09500a1190193850161190190150921190150910054a33990150914a23990950094a10191950094a10190950094a101908d00949d41901509149d29919901149d29911500549d29909901149d01901509149a41d01510d49a41d01509149a41d01508949941739901149941508d00949941101500d49938938501549911508d00949909739100949909738901149909539100949909511100949909501100949741939100549741909100549739908d00949641d01909149609919500949509b39900949141e11901549141901500d49101b39500d48e11b38901148d41739101948d09b39900948d01919500948a1990
  | 6 => 0x368660da2335509923a86df4a67525316d50cb6a821e446566a19292987c90c8444681a432af50cbda865ed412425312351491a822c4a6162330b351459a862542612ea30955184ba864c4a657ea197f50deea0cadd43642a10eb5145288ccf44667aa32f51197ba8cbdd455421307d1181a88c2e4a602253011119a684c854a616a5300d299a484c834a641ea2ac10180488c464462320311b3988c9cc46d062328311b4988ca4c15446456a28c12981094c084464425341909a0da0c1d4466b2131ab5147284c394061ce730e539872a4c0b4466a21342f39967a86234651c2130e1418708ca3842513a32899194e3a8077d403b6a014b50535a80da4a66d23326f501b694c44d405d6a327750087a8041d4022ea010b5007fa808e5222eaa10f5298c0a84404a684a530c5298cc94d074a683a1341d3995294c57948612a2b6129992a8a54d062a49315149a0290c24d465525315a521d8a904b4a64325337551b49941d01509349941508d00b49941101500f49941101500749940901500f49940901500749939508d00b49938d38901749938938501749919501100b49911501500f49909501100749541d01909349541d01908f49541938501749540d01901749540d01900b49540539901749540501901749540501900b49519901900b49519339100b49501b39508f49140d01901749140501901749101919500b48d
  | 7 => 0x75a5317150cb8a8237d4735ea08192980c88d054a682a034174183294c9cd404625316b5098ea8ac454515a530892982094cfe40603a530712985e94c054a602a23365299b280c87d438221341141963a80a74a6802530292983094cc3545652533295157094cb8d450ba533050181294cce5405e6a004d2996c80cb650608a5343101a1920d0c506772821bf50dd1a4ce8503006931b750cdba44dcd266e0912ef50973a84504a6192532d350129a88534a629ea294f5046a94c35466792433cb399e49cca1d45576a18512982888cb74065ba830a350cffa84ff4867fa231fb494fda8475d251a253069298d294c74d257b2a139d099cf9cce74e6416a122751513a84e54a672a829ef50947a8502ce6272531a129a1494d0a506596a1135298ce94d084a684673421418aba843cd44516a111d298ca94c1648645a03145298a3a8a4f4a60625333150196a805894766aa00cd2982494cb54a65aa032d5418e5a466ed43366931b350d32a468fd4347a913e129893a8a49d41782233891190288cfc4a67e2233851190088cf94a67ca231e5119da88ca5d434fea0a991998ca8ac65421da530ed19877a88f34464f253279119a288cd15465fa232ff5184288c98ce607a2324350dbc94ce94a62caa19655045488c8d446682233415197c88cbed465f6a1b0350c4088c0e44678a233c5019e39ccf14e662aa13155018aa8e
  | _ => 0

def word127_24 : Nat → Nat
  | 0 => 0xf5677677c3fc3f4fd4dfc774f74f7c77c779cf8ef8ef2f72efe3de75a7d87f5e74f7a3fa3f8bf4f78bfd3bd3dc3f8bf2bf9f38f78f75f34bf4f7b759f55f55f5a3df2de3db3d97d3f5f2de3db3da7d97d67d67d6f5f2de3de5dc7dd6d5edc2fc3d67d6bde3d4fde3be3da3fa7d87f9e74ef87f4efb7576db75b3d775775b75b75d75b3db75b75d75b3db75d75b7566f67bb2f73d775f35f65775b75f2df65d7557dd7557dd7587fd757a7b37b37f35f35f71f71d7557dd7557d5ed1efd75d759e79ed8ef8ef5e75ed4efd6bd75c7b6afa3fa3fe3de3dd753e7f2df55d75b5d3ed7d57d5f557d57d5f55f557d57d5fd17d57d57d5e2f2ef6cf8df2ef775775f71d7557dd7557d5bda7bd75d75f2bf2df65e6bd2ff33f35e73d375b7b75f71fa3fa9eabeabdabdabbabbabe754bfe3be3de75c3fa7b87fd75c7b4bfdb3db5cb7cb79b7d75c7b87f1effa9fd1dd5fc5fd1eabeab5f94fd4fd5f9779b79b7967da7d5f963f3f96f96f95f95f97b9bb9f39f39e3de3db3df39e3db3db79a7d9bbdb97b9db97b9d99f99f99bd97d98bfdb90ffe2fc3f2faa0d46326a1993505c894ce4d05316a118750927a8a93d4371a5338f414c7a84a4d404aea2b99299fa90cfd4463ea531f7509ea94c7a4a67d2433e9118f894c7cd427a2531c12992da8a97d453c6a03ef499dfa4cefd2577e823bd41003a4c01d256be919cf48d25a86e04a6
  | 1 => 0xc428a4cde06e030cdf55b336cde06f33602ccde9fa2e801d5554a200c05312003200d55a5c0054050054051558006050040050050040006fa506000217ce3906017c888cdc17ccded88448cdc17c01801c5cc9f8d84448cdc17c0180165c6d887204489f8cdf11230689a0545c82e8e48ccc944e489495583989f8ef89f82dc2e82e82e82dc2e95580185c05c08985c8ab08985c872071cef8ef89f89f82dc2e82e8ef42e82dc2e95585c11cc5c04449f49f9122b7311cb728985c8ab0b6c8985c93f13ed3ec02417c02417c5001c04fc1c050050450002eb7204e72071cef42dc2e82e8ef89f82e82dc2e95585c05c11c8e460c127c16d1cc9f49f800e17806a94400e00e4761760c200f2809449409447313380020f20800f22349440f20800f20411cd1cd1cd060232888aae72a5c60f28880f2aae0f272a5c60f2cdb336cda1a05c822f336cda1a05c822ecdab78b78050896b76b900282fa8961948962fa00605003eb72b7347f4f74f7a778f74f76f54bf4efa778f74f74fd4bfb35b3db3dd3d5f5b3dd3db3db3dd3d5f5b3dd3d4bf2bf4fda3fa6faaf8ef8efa6faaf8ef8ef6afa3fa3fe3de3d47f47fe3de75a3fa7d87fd3d4fdb3d73d73d73df39d3dd3d9bde3dd3de3be3de75c3fc7d4efa7b87f2fda3fa3fc7dc7d73de3d6bde3d6bde3d8fde3d4fd4fde3da7d87fe3da7d87f87f9cf4efa778f7a774ef8f7a7da
  | 2 => 0x498a481240920491240d1a68a2441a1450868114009fc0fe27e33d89e84f207903c81e40f207903c89e04ee27603b09d48e686f03789b84da06d03681b44d846a234099c0ce067232918c0c606313101884c206122f817c4bc05e02f01780bc65b22c89610a825312901484a2250028014049e04f027893809c04e126893049624a12489200900480240120090048024091c48c0460230914488243021810c484042120810448004002008fc47c03e11e88f007823b11d08e407223801c08dc06e23621a10c846242f11700b845a02d01680b445822b314288c44481e10e887142ea12108884041e00f107003801c00e4051020c0a005002881040600320088000009491cc00694800600733a5e2cdc8953e82329fe888236232c2905e72644ed892869fed88236c28726d8823623305ec24726d85286d84236c24d84314b782f0006004500500aae00733400606e71cab00b271d1231211cb33839a22f1cd1225c039ab7039ad891ca444c240531cc02a0c20a4c2222e0160c222e0160c222e0c31c844e444fa49fe0871cc03402a0160171c839a22e67b12022f12039a22f1ca5c022eb7094400200209c09c2e2042042080fa809c05a2e205a00a09c00600605004204200606605a17805a0069f4ab0ab12810614a54a0b725004fc5009f49f8ba00520400405c004000604aab2aaf05f2860049fb28200e9fb28355a080
  | 3 => 0xd030e0f021009000526060300000000020403071a010c05300d0500251c030900101c140c030810041106030f042b1214221000030e0f00090028070206000202010203130b020b0f2800000101032c000c070d0100090a0e00030e010400081e1a0800390809001b06050202020701101b000200000c080e000404080501100d00040903010000000200140706001505090e000500000b0400000902020314000300001205010cc86643323980cc066072e3960cb0e5432a1951ca0e4e31638a1c4ae107067803be8df06f69771bb15d16de36e1b685b42da36c1b585ac6d43692b3859c2ce1670b3859caca7620b10589eb65591ac15586aa7520a92538a987493a3151167eb3a19c9cd866a53349794b425a32c09604b0a543290948ca02503270939494648b1f18f047863a31c18d8c68a3031718b1c4c6241121888c4022030f0878c3861a30c086043061630a184842421210918404202103071830c1420a3040820410e024ff17f0bf45f80fc17d8be85f22f807c03e01f00f817b83dc5ec0f607b0bd45e80f407a0bcc5e42f137713b05d62ea0750ba4dcc4e4171838c5c42e107083841c20e10708b801c00e046e2b5c5ac2d526993445a04ce1668b305962ca06513201904c60631b0c5842c10608b001804be15ea2e45704b615aa2c4d5c4ac15582ac9522a82531a8c9420a1050927c93a69a14c925c92a493
  | 4 => 0x7eff001a4a5ff0039dc3f293012514d949ec26b340c90928027d2dc12aab4a430745cffc0055033b8ef352de65b78c824704e028fdd03cb8848846d1169c88abe9286245a985f0027fd03441d081312e9993025c05553959ba1a5a3665da02595b60ba1054732aace8f047148a34a6350a3ff00051c2ff0000592679d409dfff001414f92b5ac91f692709663ff0037c074b95134996676ed9e3215a7a8c7ff001d1ac92080dd7f001e96c97ff001b46b8c3364a703d0668d4cff003554272901bc150f75ef6e1ff000fc1dff0011041716eea02b0d65ab20651437fc007e4fc055dff0002956ce1710e532461804e64d1e442bd8d6827a3bff000b672ff000be44be8e5bc55af3f3b8ac91198d8741d6a145308f6728045803ffba41d73d7fc00802f8b8852c7f4e0fe9f4fa99ca6f51bc64a8d09cfcbcf76c68821ef1df80c95e12a1db59ea8a91487cae51d07548a111f11db696c18fa700fde03080a5a8a2527a7e216523419eebc68cdde5633a3cda163b4a0a79bd0a8445d9c26c5dfa55a7e723d535d0f1bd9f1cbc82c2c92001eacd583be43c76feb4586a7eeb93a5848516674e75a3c13f419f046138b2eb58aff001945e0200288d1675202346032803058a0906360806203e2b06012e000100022d0a80002f5e120c080007001a020b0108000000496b0405053a20077a000c13020b3d20000c0b050017111a042
  | 5 => 0xaa653fc00ff003fc00884d6da56c89da3454ff002d215ff003fc003e2cefd1697a6bfc00975e7fc002e5bffc006235dfa8d457d7fc00ff003fc006b019a4e1b23197da2003cfa53be411c707c529b7fc000082bfc00bc9fabc4928934e919f80b8249d1fa51767137488ee1aa28911c1fc3516cd7ec1ac911c88d0d461a4d3b962d896e59a9c5621a4cfaa9dea97922fff0006d8d29b7bfc00ff0001c24009732c64ad0a3fc004daed22e2ff0029d8e04772e95ce58d425847a5641838257e5d6362fa305e82187928d4ef4864324e033eea1ab1831710220f2a3e0d41c10e5d8b3d7fd845b4155f961ea08cfc486227f9fa89d70a5846f309933607ff003a1345b543e27cf452e3c90101c389233079fc637ee368b036708abb023f9943052a7a3750c692259d55319d3015e5e1fb31ba1393a133d0295a17d1b00ab033e4feb02874033755692ba1a30e522b1c4e50ec2b41b94d80f1a6f95900730989630e4c9f69ce9a3da2d5d39836151167f0bea83d75108eaf738fc100b435588f19405da068dc80d24405566788378d1e10925bd0063ecdc03b940a76cb3da2dd4248134aaab661e510dab41ae1ceb24c79ad4a965151eed962aa817a259029e60746990fb0a5d7c1a6e99aba17e037f1227c282cd088291a9ac1e056d2ca0e693e9d44cd30fbb82f0387d2c8016a0ef5de39298e9b9ff003dd7a632fc75ebad6a670
  | 6 => 0x9b396c9ff003fc003e349f1710f7dffc00ff003e04fff003fc00ff003fc00ff003994467a1f75498d553fc00566e3922d7228a34ad9d743fc00ff001d230db83054d0aa0151aacff003fc003756abccfa888df9aef08c7fc00440fd1cb511895c161ff0011487712cabd12ff000cc4da5669b4d948b80ec0fc49f6a25551329f1a582a38f93cff003fc00589d3fc00b417f9646a3b46fc0e1e46b11cbff003fc00ff003fc006357bfc00ff0035ec4113a7fc0090b18bc3270ad63901b75f7fc00ee1662141d142d02c5ff00064fdff00395b34263c492b804475ce7ff003fc001e6ebfc00ff003fc00ff003fc0020605558346abd3457ff003fc0088863fc00ff003fc0000378619b8c293fc00c233905dd9305bfc00d15a27ed9aa41505b6f1a8ffc002242711c5ff002dae3cc35ad0a013393a928caaaabcb4b6afcfcf863141d082c174df40bf98f1e6579723c98f64c593fc00ff003fc00ebae02a4920b21c41b564626cae529cd88cced1460c39a571ca97be645d146cf738aaa96f480049aa767562d823d0cc44e0c9a6565266c7da02b35f18bbc7deb61e942d01b50a402ba312d9853c210620d3076630f2c23b3a5ed8cac26a08c4a19b1d277989007be94bfc28bd149d8adb0b2e8f56d411fcc25d397cecc53f44548d0afa53711f416021bed7582ec20b80ea77fc0055323fc00ff0031adcff003fc00ff00275b2
  | 7 => 0x235014e64054e6d23506425404425444404423402406d23506425402406528ce6405424406465425423402ff0014dc6216230d4705ac5fd6a8a0716a5b470f58ceba1269dcbd813c08e4b958107a92981cd3e6179594bd2dc5035d0767b18fe1d8ea30512b424026523a794e10cdb1a2a536a1c076aa5292e630d4946373a25409420c46c70869831c97ead8a95f29a9e0a2260419a4422614966162883d38899a4f77a77a9232d5763456394484b645ca6801846ec34ee5490cdccb97eb5e1ae6f07adf0f26060f4015c98d33ff0011ee43573d008e63204fa901250e987153b0d76bedc477146551af2dcb0b57b3dceddf439f0f7e78510c46265ae7cd899a93fc00c94927c60ff0028245ff003fc00ff003fc0017882e9be7e4dffc00ff003de91e71d710443b22fb0cb7d789794a6e2455a26d56560177c691e227aad814f113ff0025ecaff0009cb1a246ffc00ff003fc005a0effc0083257fc00ef0c5583a30453fc00ff003fc00ff002b59e7a7a7fc000c8a7a536ff0012d75e99ad0a6f1d3978de6395b3fc00369ecf67813b4fc51c17a57fc00d1413fc004d4b122b7ff0037d0cff003fc00ff003fc00ff003fc005ba9bac00335b9cdcd742bfc4b6ff003fc00fa34ffc00964ba5d5bc82e5799d8c80471af3c995d669597bd540403abbfc00f3a8070f9e686deec198876859f6e5e029e8ff0017aab9358bfc008e
  | _ => 0

def word127_25 : Nat → Nat
  | 0 => 0xfcfff813ac192b5267f81fe03f37fe07ba6a65d7255819f92010ff802d17f801280a8bfe005c75c6b6852232841aea2b10508e833debd08272e75951472d9fd63ff8176eff81e620000304242580b555580000fa4d4d6a6a8e7716e0f61ce8e785bcd95e4b565cb2b8b4f8b535f90f0cff01c94cd4a62eb12758c294ccd4326b13f494da867d638223091191ac6ad638a2301119684c3465d45528406423402d43528406425402d42504507406423d42504503406405d42504501406405d225015074a6404ce6445d054234025464254444044025414a6406ce24055414a64064e54025414a64064454025225214a6406402504d
  | _ => 0

def compactWords127 (i : Nat) : Nat :=
  if i < 201 then (if i < 104 then (if i < 48 then (if i < 24 then (if i < 8 then word127_0 (i % 8) else (if i < 16 then word127_1 (i % 8) else word127_2 (i % 8))) else (if i < 32 then word127_3 (i % 8) else (if i < 40 then word127_4 (i % 8) else word127_5 (i % 8)))) else (if i < 72 then (if i < 56 then word127_6 (i % 8) else (if i < 64 then word127_7 (i % 8) else word127_8 (i % 8))) else (if i < 88 then (if i < 80 then word127_9 (i % 8) else word127_10 (i % 8)) else (if i < 96 then word127_11 (i % 8) else word127_12 (i % 8))))) else (if i < 152 then (if i < 128 then (if i < 112 then word127_13 (i % 8) else (if i < 120 then word127_14 (i % 8) else word127_15 (i % 8))) else (if i < 136 then word127_16 (i % 8) else (if i < 144 then word127_17 (i % 8) else word127_18 (i % 8)))) else (if i < 176 then (if i < 160 then word127_19 (i % 8) else (if i < 168 then word127_20 (i % 8) else word127_21 (i % 8))) else (if i < 192 then (if i < 184 then word127_22 (i % 8) else word127_23 (i % 8)) else (if i < 200 then word127_24 (i % 8) else word127_25 (i % 8)))))) else 0

def compactCount127 (k : Nat) : Nat := match k with
  | 12 => 1
  | 11 => 15
  | 10 => 296
  | 9 => 1752
  | 8 => 1489
  | 7 => 371
  | 6 => 18
  | _ => 0

def compactPath127 (k : Nat) (i : Nat) : Nat := match k with
  | 12 => 0
  | 11 => readCompactBits compactWords127 (31 + 12*i) 12
  | 10 => let v := readCompactBits compactWords127 (2475 + 16*i) 16
    (readCompactBits compactWords127 (2295 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 9 => let v := readCompactBits compactWords127 (76663 + 20*i) 20
    (readCompactBits compactWords127 (70951 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 8 => let v := readCompactBits compactWords127 (518519 + 22*i) 22
    (readCompactBits compactWords127 (496343 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | 7 => let v := readCompactBits compactWords127 (779502 + 21*i) 21
    (readCompactBits compactWords127 (766590 + 48*(v >>> 12)) 48) ||| ((v &&& 4095) <<< 48)
  | 6 => let v := readCompactBits compactWords127 (819936 + 17*i) 17
    (readCompactBits compactWords127 (818856 + 60*(v >>> 12)) 60) ||| ((v &&& 4095) <<< 60)
  | _ => 0

def compactLive127 (k : Nat) (i : Nat) : Nat := match k with
  | 12 => readCompactBits compactWords127 (0 + 7*i) 7
  | 11 => readCompactBits compactWords127 (211 + 8*i) 8
  | 10 => readCompactBits compactWords127 (7211 + 9*i) 9
  | 9 => readCompactBits compactWords127 (111703 + 10*i) 10
  | 8 => readCompactBits compactWords127 (551277 + 11*i) 11
  | 7 => readCompactBits compactWords127 (787293 + 12*i) 12
  | 6 => readCompactBits compactWords127 (820242 + 13*i) 13
  | _ => 0

def compactPoolIDs127 (k : Nat) (i : Nat) : List Nat := match k with
  | 12 => let v := readCompactBits compactWords127 (25 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords127 (7 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 11 => let v := readCompactBits compactWords127 (1598 + 12*i) 12
    let n := v >>> 8
    let bits := readCompactBits compactWords127 (331 + 7*(v &&& 255)) (7*n)
    compactIDsFromBits bits 7 n
  | 10 => let v := readCompactBits compactWords127 (52247 + 18*i) 18
    let n := v >>> 13
    let bits := readCompactBits compactWords127 (9875 + 9*(v &&& 8191)) (9*n)
    compactIDsFromBits bits 9 n
  | 9 => let v := readCompactBits compactWords127 (370523 + 20*i) 20
    let n := v >>> 15
    let bits := readCompactBits compactWords127 (129223 + 10*(v &&& 32767)) (10*n)
    compactIDsFromBits bits 10 n
  | 8 => let v := readCompactBits compactWords127 (662003 + 19*i) 19
    let n := v >>> 14
    let bits := readCompactBits compactWords127 (567656 + 11*(v &&& 16383)) (11*n)
    compactIDsFromBits bits 11 n
  | 7 => let v := readCompactBits compactWords127 (796653 + 13*i) 13
    let n := v >>> 9
    let bits := readCompactBits compactWords127 (791745 + 12*(v &&& 511)) (12*n)
    compactIDsFromBits bits 12 n
  | 6 => let v := readCompactBits compactWords127 (820488 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords127 (820476 + 12*(v &&& 1)) (12*n)
    compactIDsFromBits bits 12 n
  | _ => []

def compactBucket127 (k : Nat) (i : Nat) : List Nat := match k with
  | 11 => let d := readCompactBits compactWords127 (1778 + 4*(i % 9)) 4
    let off := ((i/9 + d) % 37)
    let v := readCompactBits compactWords127 (1814 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 10 => let d := readCompactBits compactWords127 (57575 + 7*(i % 188)) 7
    let off := ((i/188 + d) % 670)
    let v := readCompactBits compactWords127 (58891 + 18*off) 18
    if v >>> 10 == (i/104729)%251 then [v &&& 1023] else []
  | 9 => let d := readCompactBits compactWords127 (405563 + 8*(i % 1150)) 8
    let off := ((i/1150 + d) % 4079)
    let v := readCompactBits compactWords127 (414763 + 20*off) 20
    if v >>> 12 == (i/104729)%251 then [v &&& 4095] else []
  | 8 => let d := readCompactBits compactWords127 (690294 + 8*(i % 967)) 8
    let off := ((i/967 + d) % 3428)
    let v := readCompactBits compactWords127 (698030 + 20*off) 20
    if v >>> 12 == (i/104729)%251 then [v &&& 4095] else []
  | 7 => let d := readCompactBits compactWords127 (801476 + 8*(i % 242)) 8
    let off := ((i/242 + d) % 858)
    let v := readCompactBits compactWords127 (803412 + 18*off) 18
    if v >>> 10 == (i/104729)%251 then [v &&& 1023] else []
  | 6 => let d := readCompactBits compactWords127 (820524 + 5*(i % 11)) 5
    let off := ((i/11 + d) % 41)
    let v := readCompactBits compactWords127 (820579 + 14*off) 14
    if v >>> 6 == (i/104729)%251 then [v &&& 63] else []
  | _ => []
theorem compactHalves {test : Nat → Bool} {start n : Nat}
    (first : chartBlock test start (n / 2) = true)
    (last : chartBlock test (start + n / 2) (n - n / 2) = true) :
    chartBlock test start n = true := by
  have eq : n / 2 + (n - n / 2) = n := by omega
  simpa only [eq] using chartBlock_join first last

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
theorem bound90 : Lower true (vars 90) (graphGoal 90) 4 :=
  carry_of (old := 90) (rep := 27) (swaps := [67, 96]) (by decide +kernel) bound27

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound89 : Lower true (vars 89) (graphGoal 89) 4 :=
  carry_of (old := 89) (rep := 27) (swaps := [64, 97]) (by decide +kernel) bound27

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound83 : Lower true (vars 83) (graphGoal 83) 4 :=
  carry_of (old := 83) (rep := 27) (swaps := [16, 99]) (by decide +kernel) bound27

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound75 : Lower true (vars 75) (graphGoal 75) 4 :=
  carry_of (old := 75) (rep := 27) (swaps := [49, 100]) (by decide +kernel) bound27

def grid91 : CompactGrid := (91, 6, samplesP91, samplesQ91)
def tab91 : CompactTable := (compactCount91, compactPath91, compactLive91, compactPoolIDs91, compactBucket91)
def check91 (k : Nat) := compactNode grid91 tab91 compactDomains91 compactPerms91 k
def sliceSpecs91 : List SliceSpec := [(1, 0, 90, 0, 0, 4, 4), (2, 0, 89, 0, 0, 4, 4), (8, 0, 83, 0, 0, 4, 4), (16, 0, 75, 0, 0, 4, 4), (64, 0, 27, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains91 : ∀ d ∈ compactDomains91, Slice true (vars 91) (graphGoal 91) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(90, 4), (89, 4), (83, 4), (75, 4), (27, 4)]) (specs := sliceSpecs91)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact bound90
    · exact bound89
    · exact bound83
    · exact bound75
    · exact bound27
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
theorem c91k4p0 : chartBlock (check91 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev91k4 : chartBlock (check91 4) 0 1 = true :=
  c91k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c91k5p0 : chartBlock (check91 5) 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev91k5 : chartBlock (check91 5) 0 2 = true :=
  c91k5p0
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
    · exact lev91k4
    · exact lev91k5
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
theorem bound69 : Lower true (vars 69) (graphGoal 69) 4 :=
  carry_of (old := 69) (rep := 21) (swaps := [100]) (by decide +kernel) bound21

def grid85 : CompactGrid := (85, 4, samplesP85, samplesQ85)
def tab85 : CompactTable := (compactCount85, compactPath85, compactLive85, compactPoolIDs85, compactBucket85)
def check85 (k : Nat) := compactNode grid85 tab85 compactDomains85 compactPerms85 k
def sliceSpecs85 : List SliceSpec := [(16, 0, 69, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains85 : ∀ d ∈ compactDomains85, Slice true (vars 85) (graphGoal 85) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(69, 4)]) (specs := sliceSpecs85)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound69
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
theorem c85k4p0 : chartBlock (check85 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev85k4 : chartBlock (check85 4) 0 1 = true :=
  c85k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded85 : Impossible true (graphGoal 85) 4 (vars 85).toFinset := by
  apply compactRoot (g := grid85) (t := tab85) (dom := compactDomains85) (perms := compactPerms85) pairs85 domains85 autos85
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev85k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound85 : Lower true (vars 85) (graphGoal 85) 5 :=
  plain_low (hints := 2) (by decide +kernel) excluded85

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
theorem bound86 : Lower true (vars 86) (graphGoal 86) 4 :=
  carry_of (old := 86) (rep := 27) (swaps := [16, 32, 99]) (by decide +kernel) bound27

def grid87 : CompactGrid := (87, 6, samplesP87, samplesQ87)
def tab87 : CompactTable := (compactCount87, compactPath87, compactLive87, compactPoolIDs87, compactBucket87)
def check87 (k : Nat) := compactNode grid87 tab87 compactDomains87 compactPerms87 k
def sliceSpecs87 : List SliceSpec := [(2, 0, 85, 0, 0, 5, 5), (64, 0, 23, 0, 0, 5, 5), (0, 2, 69, 16, 983040, 5, 4), (1, 0, 86, 0, 0, 4, 4), (4, 0, 83, 0, 0, 4, 4), (16, 2, 69, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains87 : ∀ d ∈ compactDomains87, Slice true (vars 87) (graphGoal 87) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(85, 5), (23, 5), (69, 4), (86, 4), (83, 4)]) (specs := sliceSpecs87)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact bound85
    · exact bound23
    · exact bound69
    · exact bound86
    · exact bound83
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
theorem c87k4p0 : chartBlock (check87 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev87k4 : chartBlock (check87 4) 0 1 = true :=
  c87k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c87k5p0 : chartBlock (check87 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev87k5 : chartBlock (check87 5) 0 1 = true :=
  c87k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c87k6p0 : chartBlock (check87 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev87k6 : chartBlock (check87 6) 0 1 = true :=
  c87k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded87 : Impossible true (graphGoal 87) 6 (vars 87).toFinset := by
  apply compactRoot (g := grid87) (t := tab87) (dom := compactDomains87) (perms := compactPerms87) pairs87 domains87 autos87
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev87k4
    · exact lev87k5
    · exact lev87k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound87 : Lower true (vars 87) (graphGoal 87) 7 :=
  plain_low (hints := 66) (by decide +kernel) excluded87

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound93 : Lower true (vars 93) (graphGoal 93) 7 :=
  carry_of (old := 93) (rep := 87) (swaps := [49, 100]) (by decide +kernel) bound87

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

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound79 : Lower true (vars 79) (graphGoal 79) 7 :=
  carry_of (old := 79) (rep := 31) (swaps := [49, 100]) (by decide +kernel) bound31

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound77 : Lower true (vars 77) (graphGoal 77) 5 :=
  carry_of (old := 77) (rep := 23) (swaps := [49, 100]) (by decide +kernel) bound23

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound92 : Lower true (vars 92) (graphGoal 92) 4 :=
  carry_of (old := 92) (rep := 27) (swaps := [66, 64, 97]) (by decide +kernel) bound27

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound78 : Lower true (vars 78) (graphGoal 78) 4 :=
  carry_of (old := 78) (rep := 27) (swaps := [49, 32, 100]) (by decide +kernel) bound27

def grid95 : CompactGrid := (95, 9, samplesP95, samplesQ95)
def tab95 : CompactTable := (compactCount95, compactPath95, compactLive95, compactPoolIDs95, compactBucket95)
def check95 (k : Nat) := compactNode grid95 tab95 compactDomains95 compactPerms95 k
def sliceSpecs95 : List SliceSpec := [(1, 0, 94, 0, 0, 7, 7), (2, 0, 93, 0, 0, 7, 7), (4, 0, 91, 0, 0, 7, 7), (8, 0, 87, 0, 0, 7, 7), (16, 0, 79, 0, 0, 7, 7), (64, 0, 31, 0, 0, 7, 7), (0, 2, 69, 24, 1044480, 6, 4), (0, 8, 21, 66, 251658480, 6, 4), (10, 0, 85, 0, 0, 5, 5), (18, 0, 77, 0, 0, 5, 5), (72, 0, 23, 0, 0, 5, 5), (2, 8, 21, 64, 251658240, 5, 4), (16, 2, 69, 8, 61440, 5, 4), (64, 8, 21, 2, 240, 5, 4), (3, 0, 92, 0, 0, 4, 4), (5, 0, 90, 0, 0, 4, 4), (6, 0, 89, 0, 0, 4, 4), (9, 0, 86, 0, 0, 4, 4), (17, 0, 78, 0, 0, 4, 4), (20, 0, 75, 0, 0, 4, 4), (65, 0, 30, 0, 0, 4, 4), (68, 0, 27, 0, 0, 4, 4), (24, 2, 69, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains95 : ∀ d ∈ compactDomains95, Slice true (vars 95) (graphGoal 95) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(94, 7), (93, 7), (91, 7), (87, 7), (79, 7), (31, 7), (69, 4), (21, 4), (85, 5), (77, 5), (23, 5), (92, 4), (90, 4), (89, 4), (86, 4), (78, 4), (75, 4), (30, 4), (27, 4)]) (specs := sliceSpecs95)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound94
    · exact bound93
    · exact bound91
    · exact bound87
    · exact bound79
    · exact bound31
    · exact bound69
    · exact bound21
    · exact bound85
    · exact bound77
    · exact bound23
    · exact bound92
    · exact bound90
    · exact bound89
    · exact bound86
    · exact bound78
    · exact bound75
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
theorem c95k5p0 : chartBlock (check95 5) 0 5 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev95k5 : chartBlock (check95 5) 0 5 = true :=
  c95k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c95k6p0 : chartBlock (check95 6) 0 33 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev95k6 : chartBlock (check95 6) 0 33 = true :=
  c95k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c95k7p0 : chartBlock (check95 7) 0 26 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev95k7 : chartBlock (check95 7) 0 26 = true :=
  c95k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c95k8p0 : chartBlock (check95 8) 0 7 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev95k8 : chartBlock (check95 8) 0 7 = true :=
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
    · exact lev95k5
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
theorem bound110 : Lower true (vars 110) (graphGoal 110) 7 :=
  carry_of (old := 110) (rep := 87) (swaps := [97, 98, 48, 101, 100]) (by decide +kernel) bound87

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound106 : Lower true (vars 106) (graphGoal 106) 5 :=
  carry_of (old := 106) (rep := 85) (swaps := [65, 50, 80, 64]) (by decide +kernel) bound85

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound105 : Lower true (vars 105) (graphGoal 105) 5 :=
  carry_of (old := 105) (rep := 85) (swaps := [64, 99, 84, 98]) (by decide +kernel) bound85

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound99 : Lower true (vars 99) (graphGoal 99) 5 :=
  carry_of (old := 99) (rep := 23) (swaps := [84, 98, 66]) (by decide +kernel) bound23

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound43 : Lower true (vars 43) (graphGoal 43) 5 :=
  carry_of (old := 43) (rep := 23) (swaps := [16, 50, 84]) (by decide +kernel) bound23

def grid107 : CompactGrid := (107, 6, samplesP107, samplesQ107)
def tab107 : CompactTable := (compactCount107, compactPath107, compactLive107, compactPoolIDs107, compactBucket107)
def check107 (k : Nat) := compactNode grid107 tab107 compactDomains107 compactPerms107 k
def sliceSpecs107 : List SliceSpec := [(1, 0, 106, 0, 0, 5, 5), (2, 0, 105, 0, 0, 5, 5), (8, 0, 99, 0, 0, 5, 5), (64, 0, 43, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains107 : ∀ d ∈ compactDomains107, Slice true (vars 107) (graphGoal 107) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(106, 5), (105, 5), (99, 5), (43, 5)]) (specs := sliceSpecs107)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact bound106
    · exact bound105
    · exact bound99
    · exact bound43
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs107 : properPairs (graphGoal 107) (asRow samplesP107) (asRow samplesQ107) :=
  compactPairs (g := grid107) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos107 : ∀ p ∈ compactPerms107, autoOK (graphGoal 107) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c107k6p0 : chartBlock (check107 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev107k6 : chartBlock (check107 6) 0 1 = true :=
  c107k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded107 : Impossible true (graphGoal 107) 6 (vars 107).toFinset := by
  apply compactRoot (g := grid107) (t := tab107) (dom := compactDomains107) (perms := compactPerms107) pairs107 domains107 autos107
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev107k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound107 : Lower true (vars 107) (graphGoal 107) 7 :=
  plain_low (hints := 4149) (by decide +kernel) excluded107

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound109 : Lower true (vars 109) (graphGoal 109) 7 :=
  carry_of (old := 109) (rep := 107) (swaps := [48, 33, 101]) (by decide +kernel) bound107

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound103 : Lower true (vars 103) (graphGoal 103) 7 :=
  carry_of (old := 103) (rep := 87) (swaps := [98, 84]) (by decide +kernel) bound87

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound47 : Lower true (vars 47) (graphGoal 47) 7 :=
  carry_of (old := 47) (rep := 31) (swaps := [16, 50, 84]) (by decide +kernel) bound31

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound42 : Lower true (vars 42) (graphGoal 42) 4 :=
  carry_of (old := 42) (rep := 21) (swaps := [16, 50, 84]) (by decide +kernel) bound21

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound108 : Lower true (vars 108) (graphGoal 108) 5 :=
  carry_of (old := 108) (rep := 23) (swaps := [33, 48, 81, 100]) (by decide +kernel) bound23

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound102 : Lower true (vars 102) (graphGoal 102) 4 :=
  carry_of (old := 102) (rep := 27) (swaps := [49, 32, 83, 100]) (by decide +kernel) bound27

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound39 : Lower true (vars 39) (graphGoal 39) 4 :=
  carry_of (old := 39) (rep := 27) (swaps := [16, 50, 84]) (by decide +kernel) bound27

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound104 : Lower true (vars 104) (graphGoal 104) 4 :=
  carry_of (old := 104) (rep := 21) (swaps := [48, 82, 100]) (by decide +kernel) bound21

def grid111 : CompactGrid := (111, 9, samplesP111, samplesQ111)
def tab111 : CompactTable := (compactCount111, compactPath111, compactLive111, compactPoolIDs111, compactBucket111)
def check111 (k : Nat) := compactNode grid111 tab111 compactDomains111 compactPerms111 k
def sliceSpecs111 : List SliceSpec := [(1, 0, 110, 0, 0, 7, 7), (2, 0, 109, 0, 0, 7, 7), (4, 0, 107, 0, 0, 7, 7), (8, 0, 103, 0, 0, 7, 7), (32, 0, 79, 0, 0, 7, 7), (64, 0, 47, 0, 0, 7, 7), (0, 2, 69, 40, 15790080, 6, 4), (0, 4, 42, 65, 251658255, 6, 4), (3, 0, 108, 0, 0, 5, 5), (5, 0, 106, 0, 0, 5, 5), (34, 0, 77, 0, 0, 5, 5), (1, 4, 42, 64, 251658240, 5, 4), (8, 2, 69, 32, 15728640, 5, 4), (32, 2, 69, 8, 61440, 5, 4), (64, 4, 42, 1, 15, 5, 4), (9, 0, 102, 0, 0, 4, 4), (33, 0, 78, 0, 0, 4, 4), (72, 0, 39, 0, 0, 4, 4), (7, 0, 104, 0, 0, 4, 4), (40, 2, 69, 0, 0, 4, 4), (42, 0, 69, 0, 0, 4, 4), (65, 4, 42, 0, 0, 4, 4), (69, 0, 42, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains111 : ∀ d ∈ compactDomains111, Slice true (vars 111) (graphGoal 111) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(110, 7), (109, 7), (107, 7), (103, 7), (79, 7), (47, 7), (69, 4), (42, 4), (108, 5), (106, 5), (77, 5), (102, 4), (78, 4), (39, 4), (104, 4)]) (specs := sliceSpecs111)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound110
    · exact bound109
    · exact bound107
    · exact bound103
    · exact bound79
    · exact bound47
    · exact bound69
    · exact bound42
    · exact bound108
    · exact bound106
    · exact bound77
    · exact bound102
    · exact bound78
    · exact bound39
    · exact bound104
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs111 : properPairs (graphGoal 111) (asRow samplesP111) (asRow samplesQ111) :=
  compactPairs (g := grid111) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos111 : ∀ p ∈ compactPerms111, autoOK (graphGoal 111) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c111k5p0 : chartBlock (check111 5) 0 7 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev111k5 : chartBlock (check111 5) 0 7 = true :=
  c111k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c111k6p0 : chartBlock (check111 6) 0 38 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev111k6 : chartBlock (check111 6) 0 38 = true :=
  c111k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c111k7p0 : chartBlock (check111 7) 0 34 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev111k7 : chartBlock (check111 7) 0 34 = true :=
  c111k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c111k8p0 : chartBlock (check111 8) 0 11 = true := by
  iterate 2 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev111k8 : chartBlock (check111 8) 0 11 = true :=
  c111k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c111k9p0 : chartBlock (check111 9) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev111k9 : chartBlock (check111 9) 0 1 = true :=
  c111k9p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded111 : Impossible true (graphGoal 111) 9 (vars 111).toFinset := by
  apply compactRoot (g := grid111) (t := tab111) (dom := compactDomains111) (perms := compactPerms111) pairs111 domains111 autos111
  · intro k hk
    change k ≤ 9 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev111k5
    · exact lev111k6
    · exact lev111k7
    · exact lev111k8
    · exact lev111k9
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound111 : Lower true (vars 111) (graphGoal 111) 10 :=
  plain_low (hints := 4146) (by decide +kernel) excluded111

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound125 : Lower true (vars 125) (graphGoal 125) 10 :=
  carry_of (old := 125) (rep := 111) (swaps := [80, 50, 65]) (by decide +kernel) bound111

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound118 : Lower true (vars 118) (graphGoal 118) 7 :=
  carry_of (old := 118) (rep := 91) (swaps := [32, 83]) (by decide +kernel) bound91

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound117 : Lower true (vars 117) (graphGoal 117) 7 :=
  carry_of (old := 117) (rep := 107) (swaps := [80, 50, 65, 49]) (by decide +kernel) bound107

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
theorem bound115 : Lower true (vars 115) (graphGoal 115) 6 :=
  carry_of (old := 115) (rep := 55) (swaps := [84, 98]) (by decide +kernel) bound55

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound113 : Lower true (vars 113) (graphGoal 113) 5 :=
  carry_of (old := 113) (rep := 23) (swaps := [64, 65, 81, 98]) (by decide +kernel) bound23

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound101 : Lower true (vars 101) (graphGoal 101) 5 :=
  carry_of (old := 101) (rep := 85) (swaps := [98, 84]) (by decide +kernel) bound85

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound116 : Lower true (vars 116) (graphGoal 116) 4 :=
  carry_of (old := 116) (rep := 27) (swaps := [33, 67, 80, 99, 16]) (by decide +kernel) bound27

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound114 : Lower true (vars 114) (graphGoal 114) 4 :=
  carry_of (old := 114) (rep := 27) (swaps := [65, 64, 80, 99]) (by decide +kernel) bound27

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound54 : Lower true (vars 54) (graphGoal 54) 4 :=
  carry_of (old := 54) (rep := 27) (swaps := [32, 83]) (by decide +kernel) bound27

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound97 : Lower true (vars 97) (graphGoal 97) 4 :=
  carry_of (old := 97) (rep := 21) (swaps := [82, 100]) (by decide +kernel) bound21

def grid119 : CompactGrid := (119, 9, samplesP119, samplesQ119)
def tab119 : CompactTable := (compactCount119, compactPath119, compactLive119, compactPoolIDs119, compactBucket119)
def check119 (k : Nat) := compactNode grid119 tab119 compactDomains119 compactPerms119 k
def sliceSpecs119 : List SliceSpec := [(1, 0, 118, 0, 0, 7, 7), (2, 0, 117, 0, 0, 7, 7), (16, 0, 103, 0, 0, 7, 7), (32, 0, 87, 0, 0, 7, 7), (4, 0, 115, 0, 0, 6, 6), (64, 0, 55, 0, 0, 6, 6), (0, 2, 69, 48, 16711680, 6, 4), (6, 0, 113, 0, 0, 5, 5), (18, 0, 101, 0, 0, 5, 5), (20, 0, 99, 0, 0, 5, 5), (34, 0, 85, 0, 0, 5, 5), (66, 0, 53, 0, 0, 5, 5), (96, 0, 23, 0, 0, 5, 5), (16, 2, 69, 32, 15728640, 5, 4), (32, 2, 69, 16, 983040, 5, 4), (3, 0, 116, 0, 0, 4, 4), (5, 0, 114, 0, 0, 4, 4), (17, 0, 102, 0, 0, 4, 4), (33, 0, 86, 0, 0, 4, 4), (36, 0, 83, 0, 0, 4, 4), (65, 0, 54, 0, 0, 4, 4), (80, 0, 39, 0, 0, 4, 4), (22, 0, 97, 0, 0, 4, 4), (48, 2, 69, 0, 0, 4, 4), (50, 0, 69, 0, 0, 4, 4), (98, 0, 21, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains119 : ∀ d ∈ compactDomains119, Slice true (vars 119) (graphGoal 119) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(118, 7), (117, 7), (103, 7), (87, 7), (115, 6), (55, 6), (69, 4), (113, 5), (101, 5), (99, 5), (85, 5), (53, 5), (23, 5), (116, 4), (114, 4), (102, 4), (86, 4), (83, 4), (54, 4), (39, 4), (97, 4), (21, 4)]) (specs := sliceSpecs119)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound118
    · exact bound117
    · exact bound103
    · exact bound87
    · exact bound115
    · exact bound55
    · exact bound69
    · exact bound113
    · exact bound101
    · exact bound99
    · exact bound85
    · exact bound53
    · exact bound23
    · exact bound116
    · exact bound114
    · exact bound102
    · exact bound86
    · exact bound83
    · exact bound54
    · exact bound39
    · exact bound97
    · exact bound21
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
theorem c119k5p0 : chartBlock (check119 5) 0 38 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev119k5 : chartBlock (check119 5) 0 38 = true :=
  c119k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k6p0 : chartBlock (check119 6) 0 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k6p1 : chartBlock (check119 6) 48 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k6p2 : chartBlock (check119 6) 96 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k6p3 : chartBlock (check119 6) 144 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k6p4 : chartBlock (check119 6) 192 6 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev119k6 : chartBlock (check119 6) 0 198 = true :=
  (chartBlock_join (a := 96) (b := 102) (chartBlock_join (a := 48) (b := 48) c119k6p0 c119k6p1) (chartBlock_join (a := 48) (b := 54) c119k6p2 (chartBlock_join (a := 48) (b := 6) c119k6p3 c119k6p4)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k7p0 : chartBlock (check119 7) 0 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k7p1 : chartBlock (check119 7) 48 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k7p2 : chartBlock (check119 7) 96 15 = true := by
  iterate 2 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev119k7 : chartBlock (check119 7) 0 111 = true :=
  (chartBlock_join (a := 48) (b := 63) c119k7p0 (chartBlock_join (a := 48) (b := 15) c119k7p1 c119k7p2))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c119k8p0 : chartBlock (check119 8) 0 17 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev119k8 : chartBlock (check119 8) 0 17 = true :=
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
    · rfl
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
  carry_of (old := 123) (rep := 119) (swaps := [80, 65, 50]) (by decide +kernel) bound119

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
theorem bound59 : Lower true (vars 59) (graphGoal 59) 6 :=
  carry_of (old := 59) (rep := 55) (swaps := [16, 50, 84]) (by decide +kernel) bound55

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
theorem bound124 : Lower true (vars 124) (graphGoal 124) 7 :=
  carry_of (old := 124) (rep := 31) (swaps := [33, 49, 65, 80, 97]) (by decide +kernel) bound31

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound122 : Lower true (vars 122) (graphGoal 122) 7 :=
  carry_of (old := 122) (rep := 87) (swaps := [65, 48, 82]) (by decide +kernel) bound87

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound121 : Lower true (vars 121) (graphGoal 121) 7 :=
  carry_of (old := 121) (rep := 87) (swaps := [64, 99, 65, 82, 97]) (by decide +kernel) bound87

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound58 : Lower true (vars 58) (graphGoal 58) 5 :=
  carry_of (old := 58) (rep := 23) (swaps := [65, 48, 82]) (by decide +kernel) bound23

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound45 : Lower true (vars 45) (graphGoal 45) 4 :=
  carry_of (old := 45) (rep := 27) (swaps := [16, 50, 49, 84]) (by decide +kernel) bound27

def grid127 : CompactGrid := (127, 12, samplesP127, samplesQ127)
def tab127 : CompactTable := (compactCount127, compactPath127, compactLive127, compactPoolIDs127, compactBucket127)
def check127 (k : Nat) := compactNode grid127 tab127 compactDomains127 compactPerms127 k
def sliceSpecs127 : List SliceSpec := [(1, 0, 126, 0, 0, 10, 10), (2, 0, 125, 0, 0, 10, 10), (4, 0, 123, 0, 0, 10, 10), (8, 0, 119, 0, 0, 10, 10), (16, 0, 111, 0, 0, 10, 10), (32, 0, 95, 0, 0, 10, 10), (64, 0, 63, 0, 0, 9, 9), (0, 2, 69, 56, 16773120, 7, 4), (0, 4, 42, 81, 252641295, 7, 4), (0, 8, 21, 98, 267387120, 7, 4), (0, 16, 104, 7, 4095, 7, 4), (3, 0, 124, 0, 0, 7, 7), (5, 0, 122, 0, 0, 7, 7), (6, 0, 121, 0, 0, 7, 7), (9, 0, 118, 0, 0, 7, 7), (10, 0, 117, 0, 0, 7, 7), (17, 0, 110, 0, 0, 7, 7), (18, 0, 109, 0, 0, 7, 7), (20, 0, 107, 0, 0, 7, 7), (24, 0, 103, 0, 0, 7, 7), (33, 0, 94, 0, 0, 7, 7), (34, 0, 93, 0, 0, 7, 7), (36, 0, 91, 0, 0, 7, 7), (40, 0, 87, 0, 0, 7, 7), (48, 0, 79, 0, 0, 7, 7), (65, 0, 62, 0, 0, 7, 7), (66, 0, 61, 0, 0, 7, 7), (80, 0, 47, 0, 0, 7, 7), (96, 0, 31, 0, 0, 7, 7), (12, 0, 115, 0, 0, 6, 6), (68, 0, 59, 0, 0, 6, 6), (72, 0, 55, 0, 0, 6, 6), (1, 4, 42, 80, 252641280, 6, 4), (1, 16, 104, 6, 4080, 6, 4), (2, 8, 21, 96, 267386880, 6, 4), (2, 16, 104, 5, 3855, 6, 4), (4, 16, 104, 3, 255, 6, 4), (8, 2, 69, 48, 16711680, 6, 4), (16, 2, 69, 40, 15790080, 6, 4), (16, 4, 42, 65, 251658255, 6, 4), (32, 2, 69, 24, 1044480, 6, 4), (32, 8, 21, 66, 251658480, 6, 4), (64, 4, 42, 17, 983055, 6, 4), (64, 8, 21, 34, 15728880, 6, 4), (14, 0, 113, 0, 0, 5, 5), (19, 0, 108, 0, 0, 5, 5), (21, 0, 106, 0, 0, 5, 5), (22, 0, 105, 0, 0, 5, 5), (26, 0, 101, 0, 0, 5, 5), (28, 0, 99, 0, 0, 5, 5), (42, 0, 85, 0, 0, 5, 5), (50, 0, 77, 0, 0, 5, 5), (69, 0, 58, 0, 0, 5, 5), (74, 0, 53, 0, 0, 5, 5), (84, 0, 43, 0, 0, 5, 5), (104, 0, 23, 0, 0, 5, 5), (3, 16, 104, 4, 3840, 5, 4), (5, 16, 104, 2, 240, 5, 4), (6, 16, 104, 1, 15, 5, 4), (17, 4, 42, 64, 251658240, 5, 4), (24, 2, 69, 32, 15728640, 5, 4), (34, 8, 21, 64, 251658240, 5, 4), (40, 2, 69, 16, 983040, 5, 4), (48, 2, 69, 8, 61440, 5, 4), (65, 4, 42, 16, 983040, 5, 4), (66, 8, 21, 32, 15728640, 5, 4), (80, 4, 42, 1, 15, 5, 4), (96, 8, 21, 2, 240, 5, 4), (11, 0, 116, 0, 0, 4, 4), (13, 0, 114, 0, 0, 4, 4), (25, 0, 102, 0, 0, 4, 4), (35, 0, 92, 0, 0, 4, 4), (37, 0, 90, 0, 0, 4, 4), (38, 0, 89, 0, 0, 4, 4), (41, 0, 86, 0, 0, 4, 4), (44, 0, 83, 0, 0, 4, 4), (49, 0, 78, 0, 0, 4, 4), (73, 0, 54, 0, 0, 4, 4), (82, 0, 45, 0, 0, 4, 4), (88, 0, 39, 0, 0, 4, 4), (97, 0, 30, 0, 0, 4, 4), (100, 0, 27, 0, 0, 4, 4), (7, 16, 104, 0, 0, 4, 4), (23, 0, 104, 0, 0, 4, 4), (30, 0, 97, 0, 0, 4, 4), (56, 2, 69, 0, 0, 4, 4), (58, 0, 69, 0, 0, 4, 4), (81, 4, 42, 0, 0, 4, 4), (85, 0, 42, 0, 0, 4, 4), (98, 8, 21, 0, 0, 4, 4), (106, 0, 21, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains127 : ∀ d ∈ compactDomains127, Slice true (vars 127) (graphGoal 127) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(126, 10), (125, 10), (123, 10), (119, 10), (111, 10), (95, 10), (63, 9), (69, 4), (42, 4), (21, 4), (104, 4), (124, 7), (122, 7), (121, 7), (118, 7), (117, 7), (110, 7), (109, 7), (107, 7), (103, 7), (94, 7), (93, 7), (91, 7), (87, 7), (79, 7), (62, 7), (61, 7), (47, 7), (31, 7), (115, 6), (59, 6), (55, 6), (113, 5), (108, 5), (106, 5), (105, 5), (101, 5), (99, 5), (85, 5), (77, 5), (58, 5), (53, 5), (43, 5), (23, 5), (116, 4), (114, 4), (102, 4), (92, 4), (90, 4), (89, 4), (86, 4), (83, 4), (78, 4), (54, 4), (45, 4), (39, 4), (30, 4), (27, 4), (97, 4)]) (specs := sliceSpecs127)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound126
    · exact bound125
    · exact bound123
    · exact bound119
    · exact bound111
    · exact bound95
    · exact bound63
    · exact bound69
    · exact bound42
    · exact bound21
    · exact bound104
    · exact bound124
    · exact bound122
    · exact bound121
    · exact bound118
    · exact bound117
    · exact bound110
    · exact bound109
    · exact bound107
    · exact bound103
    · exact bound94
    · exact bound93
    · exact bound91
    · exact bound87
    · exact bound79
    · exact bound62
    · exact bound61
    · exact bound47
    · exact bound31
    · exact bound115
    · exact bound59
    · exact bound55
    · exact bound113
    · exact bound108
    · exact bound106
    · exact bound105
    · exact bound101
    · exact bound99
    · exact bound85
    · exact bound77
    · exact bound58
    · exact bound53
    · exact bound43
    · exact bound23
    · exact bound116
    · exact bound114
    · exact bound102
    · exact bound92
    · exact bound90
    · exact bound89
    · exact bound86
    · exact bound83
    · exact bound78
    · exact bound54
    · exact bound45
    · exact bound39
    · exact bound30
    · exact bound27
    · exact bound97
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
theorem c127k6p0 : chartBlock (check127 6) 0 18 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev127k6 : chartBlock (check127 6) 0 18 = true :=
  c127k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k7p0 : chartBlock (check127 7) 0 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k7p1 : chartBlock (check127 7) 48 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k7p2 : chartBlock (check127 7) 96 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k7p3 : chartBlock (check127 7) 144 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k7p4 : chartBlock (check127 7) 192 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k7p5 : chartBlock (check127 7) 240 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k7p6 : chartBlock (check127 7) 288 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k7p7 : chartBlock (check127 7) 336 35 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev127k7 : chartBlock (check127 7) 0 371 = true :=
  (chartBlock_join (a := 192) (b := 179) (chartBlock_join (a := 96) (b := 96) (chartBlock_join (a := 48) (b := 48) c127k7p0 c127k7p1) (chartBlock_join (a := 48) (b := 48) c127k7p2 c127k7p3)) (chartBlock_join (a := 96) (b := 83) (chartBlock_join (a := 48) (b := 48) c127k7p4 c127k7p5) (chartBlock_join (a := 48) (b := 35) c127k7p6 c127k7p7)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p0 : chartBlock (check127 8) 0 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p1 : chartBlock (check127 8) 48 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p2 : chartBlock (check127 8) 96 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p3 : chartBlock (check127 8) 144 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p4 : chartBlock (check127 8) 192 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p5 : chartBlock (check127 8) 240 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p6 : chartBlock (check127 8) 288 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p7 : chartBlock (check127 8) 336 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p8 : chartBlock (check127 8) 384 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p9 : chartBlock (check127 8) 432 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p10 : chartBlock (check127 8) 480 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p11 : chartBlock (check127 8) 528 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p12 : chartBlock (check127 8) 576 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p13 : chartBlock (check127 8) 624 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p14 : chartBlock (check127 8) 672 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p15 : chartBlock (check127 8) 720 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p16 : chartBlock (check127 8) 768 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p17 : chartBlock (check127 8) 816 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p18 : chartBlock (check127 8) 864 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p19 : chartBlock (check127 8) 912 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p20 : chartBlock (check127 8) 960 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p21 : chartBlock (check127 8) 1008 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p22 : chartBlock (check127 8) 1056 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p23 : chartBlock (check127 8) 1104 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p24 : chartBlock (check127 8) 1152 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p25 : chartBlock (check127 8) 1200 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p26 : chartBlock (check127 8) 1248 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p27 : chartBlock (check127 8) 1296 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p28 : chartBlock (check127 8) 1344 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p29 : chartBlock (check127 8) 1392 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p30 : chartBlock (check127 8) 1440 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k8p31 : chartBlock (check127 8) 1488 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev127k8 : chartBlock (check127 8) 0 1489 = true :=
  (chartBlock_join (a := 768) (b := 721) (chartBlock_join (a := 384) (b := 384) (chartBlock_join (a := 192) (b := 192) (chartBlock_join (a := 96) (b := 96) (chartBlock_join (a := 48) (b := 48) c127k8p0 c127k8p1) (chartBlock_join (a := 48) (b := 48) c127k8p2 c127k8p3)) (chartBlock_join (a := 96) (b := 96) (chartBlock_join (a := 48) (b := 48) c127k8p4 c127k8p5) (chartBlock_join (a := 48) (b := 48) c127k8p6 c127k8p7))) (chartBlock_join (a := 192) (b := 192) (chartBlock_join (a := 96) (b := 96) (chartBlock_join (a := 48) (b := 48) c127k8p8 c127k8p9) (chartBlock_join (a := 48) (b := 48) c127k8p10 c127k8p11)) (chartBlock_join (a := 96) (b := 96) (chartBlock_join (a := 48) (b := 48) c127k8p12 c127k8p13) (chartBlock_join (a := 48) (b := 48) c127k8p14 c127k8p15)))) (chartBlock_join (a := 384) (b := 337) (chartBlock_join (a := 192) (b := 192) (chartBlock_join (a := 96) (b := 96) (chartBlock_join (a := 48) (b := 48) c127k8p16 c127k8p17) (chartBlock_join (a := 48) (b := 48) c127k8p18 c127k8p19)) (chartBlock_join (a := 96) (b := 96) (chartBlock_join (a := 48) (b := 48) c127k8p20 c127k8p21) (chartBlock_join (a := 48) (b := 48) c127k8p22 c127k8p23))) (chartBlock_join (a := 192) (b := 145) (chartBlock_join (a := 96) (b := 96) (chartBlock_join (a := 48) (b := 48) c127k8p24 c127k8p25) (chartBlock_join (a := 48) (b := 48) c127k8p26 c127k8p27)) (chartBlock_join (a := 96) (b := 49) (chartBlock_join (a := 48) (b := 48) c127k8p28 c127k8p29) (chartBlock_join (a := 48) (b := 1) c127k8p30 c127k8p31)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p0 : chartBlock (check127 9) 0 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p1 : chartBlock (check127 9) 48 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p2 : chartBlock (check127 9) 96 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p3 : chartBlock (check127 9) 144 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p4 : chartBlock (check127 9) 192 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p5 : chartBlock (check127 9) 240 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p6 : chartBlock (check127 9) 288 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p7 : chartBlock (check127 9) 336 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p8 : chartBlock (check127 9) 384 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p9 : chartBlock (check127 9) 432 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p10 : chartBlock (check127 9) 480 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p11 : chartBlock (check127 9) 528 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p12 : chartBlock (check127 9) 576 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p13 : chartBlock (check127 9) 624 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p14 : chartBlock (check127 9) 672 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p15 : chartBlock (check127 9) 720 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p16 : chartBlock (check127 9) 768 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p17 : chartBlock (check127 9) 816 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p18 : chartBlock (check127 9) 864 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p19 : chartBlock (check127 9) 912 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p20 : chartBlock (check127 9) 960 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p21 : chartBlock (check127 9) 1008 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p22 : chartBlock (check127 9) 1056 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p23 : chartBlock (check127 9) 1104 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p24 : chartBlock (check127 9) 1152 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p25 : chartBlock (check127 9) 1200 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p26 : chartBlock (check127 9) 1248 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p27 : chartBlock (check127 9) 1296 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p28 : chartBlock (check127 9) 1344 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p29 : chartBlock (check127 9) 1392 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p30 : chartBlock (check127 9) 1440 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p31 : chartBlock (check127 9) 1488 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p32 : chartBlock (check127 9) 1536 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p33 : chartBlock (check127 9) 1584 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p34 : chartBlock (check127 9) 1632 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p35 : chartBlock (check127 9) 1680 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k9p36 : chartBlock (check127 9) 1728 24 = true := by
  iterate 3 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev127k9 : chartBlock (check127 9) 0 1752 = true :=
  (chartBlock_join (a := 864) (b := 888) (chartBlock_join (a := 432) (b := 432) (chartBlock_join (a := 192) (b := 240) (chartBlock_join (a := 96) (b := 96) (chartBlock_join (a := 48) (b := 48) c127k9p0 c127k9p1) (chartBlock_join (a := 48) (b := 48) c127k9p2 c127k9p3)) (chartBlock_join (a := 96) (b := 144) (chartBlock_join (a := 48) (b := 48) c127k9p4 c127k9p5) (chartBlock_join (a := 48) (b := 96) c127k9p6 (chartBlock_join (a := 48) (b := 48) c127k9p7 c127k9p8)))) (chartBlock_join (a := 192) (b := 240) (chartBlock_join (a := 96) (b := 96) (chartBlock_join (a := 48) (b := 48) c127k9p9 c127k9p10) (chartBlock_join (a := 48) (b := 48) c127k9p11 c127k9p12)) (chartBlock_join (a := 96) (b := 144) (chartBlock_join (a := 48) (b := 48) c127k9p13 c127k9p14) (chartBlock_join (a := 48) (b := 96) c127k9p15 (chartBlock_join (a := 48) (b := 48) c127k9p16 c127k9p17))))) (chartBlock_join (a := 432) (b := 456) (chartBlock_join (a := 192) (b := 240) (chartBlock_join (a := 96) (b := 96) (chartBlock_join (a := 48) (b := 48) c127k9p18 c127k9p19) (chartBlock_join (a := 48) (b := 48) c127k9p20 c127k9p21)) (chartBlock_join (a := 96) (b := 144) (chartBlock_join (a := 48) (b := 48) c127k9p22 c127k9p23) (chartBlock_join (a := 48) (b := 96) c127k9p24 (chartBlock_join (a := 48) (b := 48) c127k9p25 c127k9p26)))) (chartBlock_join (a := 240) (b := 216) (chartBlock_join (a := 96) (b := 144) (chartBlock_join (a := 48) (b := 48) c127k9p27 c127k9p28) (chartBlock_join (a := 48) (b := 96) c127k9p29 (chartBlock_join (a := 48) (b := 48) c127k9p30 c127k9p31))) (chartBlock_join (a := 96) (b := 120) (chartBlock_join (a := 48) (b := 48) c127k9p32 c127k9p33) (chartBlock_join (a := 48) (b := 72) c127k9p34 (chartBlock_join (a := 48) (b := 24) c127k9p35 c127k9p36))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k10p0 : chartBlock (check127 10) 0 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k10p1 : chartBlock (check127 10) 48 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k10p2 : chartBlock (check127 10) 96 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k10p3 : chartBlock (check127 10) 144 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k10p4 : chartBlock (check127 10) 192 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k10p5 : chartBlock (check127 10) 240 48 = true := by
  iterate 4 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k10p6 : chartBlock (check127 10) 288 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev127k10 : chartBlock (check127 10) 0 296 = true :=
  (chartBlock_join (a := 144) (b := 152) (chartBlock_join (a := 48) (b := 96) c127k10p0 (chartBlock_join (a := 48) (b := 48) c127k10p1 c127k10p2)) (chartBlock_join (a := 96) (b := 56) (chartBlock_join (a := 48) (b := 48) c127k10p3 c127k10p4) (chartBlock_join (a := 48) (b := 8) c127k10p5 c127k10p6)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c127k11p0 : chartBlock (check127 11) 0 15 = true := by
  iterate 2 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev127k11 : chartBlock (check127 11) 0 15 = true :=
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

end PEqualNP.Outside.L_meta_10760

open PEqualNP.Outside.L_meta_10760 in
theorem PEqualNP.Outside.L_meta_10760 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _oneNot correct
  exact replaceShort (by simpa only [sevenInputs, show graph = graphGoal 127 by decide +kernel] using excluded127) gates o fit correct
