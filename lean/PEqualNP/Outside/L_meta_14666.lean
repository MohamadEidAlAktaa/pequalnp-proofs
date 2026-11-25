import PEqualNP.Defs





namespace PEqualNP.Outside.L_meta_14666
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def limbs64 (ws : List Nat) : Nat := ws.foldl (fun v w => (v <<< 64) + w) 0
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

def inputs : List Sig := [(BitVec.ofNat _ (limbs64 [0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaa])),(BitVec.ofNat _ (limbs64 [0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc,0xcccccccccccccccc])),(BitVec.ofNat _ (limbs64 [0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0])),(BitVec.ofNat _ (limbs64 [0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00,0xff00ff00ff00ff00])),(BitVec.ofNat _ (limbs64 [0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000,0xffff0000ffff0000])),(BitVec.ofNat _ (limbs64 [0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000,0xffffffff00000000])),(BitVec.ofNat _ (limbs64 [0xffffffffffffffff,0x0,0xffffffffffffffff,0x0,0xffffffffffffffff,0x0,0xffffffffffffffff,0x0])),(BitVec.ofNat _ (limbs64 [0xffffffffffffffff,0xffffffffffffffff,0x0,0x0,0xffffffffffffffff,0xffffffffffffffff,0x0,0x0])),(BitVec.ofNat _ (limbs64 [0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff,0xffffffffffffffff,0x0,0x0,0x0,0x0]))]
def graph : Sig := (BitVec.ofNat _ (limbs64 [0xfffffffffffffffe,0xfffffffffffffffc,0xfffffffeffffffaa,0xfefefefe00000000,0xfffffffffffffffe,0xfffffffffffffffc,0xfffffffeffffffaa,0xfefefefe00000000]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
 (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 7)
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
 (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7)
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
  | 0 => (limbs64 [0x1,0x1,0x1,0x1,0x1,0x1,0x1,0x1])
  | 1 => (limbs64 [0x1,0x0,0x1,0x0,0x1,0x0,0x1])
  | 2 => (limbs64 [0x1,0x1,0x0,0x0,0x1,0x1])
  | 3 => (limbs64 [0x1,0x0,0x0,0x0,0x1])
  | 4 => (limbs64 [0x1,0x1,0x1,0x1])
  | 5 => (limbs64 [0x1,0x0,0x1])
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
 (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7)
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

def eightInputs := inputs.take 8
def sample8 (r : Row) (j : Fin 8) := bit r (eightInputs.getD j.val zero)
def edge8 (x : Fin 8 → Bool) : Bool :=
 (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 7)
theorem edgeTable8 : ∀ r : Row, bit r graph = edge8 (sample8 r) := by decide +kernel
theorem inputList8 : List.ofFn (fun j : Fin 8 => eightInputs.getD j.val zero) = eightInputs := rfl
theorem sampled8 (r : Row) : List.ofFn (sample8 r) = eightInputs.map (bit r) := by
  rw [←inputList8]
  rw [List.map_ofFn]
  rfl

theorem eval8 (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates eightInputs).getD i zero) =
      (C.wires (List.ofFn (sample8 r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled8]
  rfl

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([5, 5, 5, 6, 6, 0, 0, 1] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([5, 5, 5, 6, 6, 0, 0, 1] : List Nat).getD i.val 0))

set_option maxHeartbeats 1000000 in
theorem allRequired :
    (∀ i : Fin 8, bit (lowRow i) graph ≠ bit (highRow i) graph) ∧
    (∀ i j : Fin 8, i ≠ j →
      bit (lowRow i) (eightInputs.getD j.val zero) =
      bit (highRow i) (eightInputs.getD j.val zero)) := by decide +kernel

theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x)=edge8 x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k eightInputs.toFinset := by
  have goalEq : (execute C.gates eightInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (eval8 C legal C.output r).trans ((computes (sample8 r)).trans (edgeTable8 r).symm)
  have out := get_rep (u:=true) (execute C.gates eightInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates eightInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : eightInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ eightInputs) : ∃ i : Fin 8, eightInputs.getD i.val zero = a := by
    rw [←inputList8] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = eightInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run eightInputs (eightInputs.getD i.val zero) sub (lowRow i) (highRow i)
        (allRequired.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply allRequired.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k,hk,eq ▸ run⟩


def readCompactBits (table : Nat → Nat) (start width : Nat) : Nat :=
  let i := start / 4096
  let j := start % 4096
  let low := table i >>> j
  let result := if j + width ≤ 4096 then low else low ||| (table (i+1) <<< (4096-j))
  result &&& ((1 <<< width)-1)

def compactIDsFromBits (bits width : Nat) : Nat → List Nat
  | 0 => []
  | n+1 => (bits &&& ((1 <<< width)-1)) :: compactIDsFromBits (bits >>> width) width n

def samplesP164 : Nat → Bits
  | 2 => ~~~(0x4054 : Bits)
  | 5 => ~~~(0x10a8 : Bits)
  | 7 => 0xdefc
  | _ => 0

def samplesQ164 : Nat → Bits
  | 2 => ~~~(0xbdf6 : Bits)
  | 5 => 0x1812
  | 7 => 0x2424
  | _ => 0

def compactPerms164 : Array (List Nat) := ([[], [117], [82], [82, 117], [114, 117], [114]] : List (List Nat)).toArray

def compactDomains164 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray

def compactWords164 : Nat → Nat
  | 0 => 0x7
  | _ => 0

def compactCount164 (k : Nat) : Nat := match k with
  | 3 => 1
  | _ => 0

def compactPath164 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => 0
  | _ => 0

def compactLive164 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => readCompactBits compactWords164 (0 + 3*i) 3
  | _ => 0

def compactPoolIDs164 (k : Nat) (i : Nat) : List Nat := match k with
  | 3 => let v := readCompactBits compactWords164 (3 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords164 (3 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket164 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP180 : Nat → Bits
  | 2 => ~~~(0x210306300a4e315a : Bits)
  | 4 => 0x78fb921e6fcc1f0a
  | 5 => ~~~(0xa0812d0448d98aa : Bits)
  | 7 => 0x6fff76fddecfb9fa
  | _ => 0

def samplesQ180 : Nat → Bits
  | 2 => ~~~(0x5e7edbe7cf6b75de : Bits)
  | 4 => 0x74538ac4916df08
  | 5 => 0xa24124702025544
  | 7 => 0x1010010084400092
  | _ => 0

def compactPerms180 : Array (List Nat) := ([[], [82]] : List (List Nat)).toArray

def compactDomains180 : Array (Sig × Nat) := ([(subcube 16 0, 4)] : List (Sig × Nat)).toArray

def compactWords180 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def compactCount180 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath180 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive180 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords180 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs180 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords180 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords180 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket180 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP240 : Nat → Bits
  | 4 => ~~~(0x2010428051249618 : Bits)
  | 5 => 0xf3f6d2baf7a49f58
  | 6 => 0xbbfb6c3fdb4a2fa2
  | 7 => ~~~(0x10220c02824a2922 : Bits)
  | _ => 0

def samplesQ240 : Nat → Bits
  | 4 => 0x2048409228064164
  | 5 => 0xe08e918c4465d50
  | 6 => 0x4482b26903691e82
  | 7 => ~~~(0xeefdebdbef56fd76 : Bits)
  | _ => 0

def compactPerms240 : Array (List Nat) := ([[], [101, 116]] : List (List Nat)).toArray

def compactDomains240 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray

def compactWords240 : Nat → Nat
  | 0 => 0xf
  | _ => 0

def compactCount240 (k : Nat) : Nat := match k with
  | 3 => 1
  | _ => 0

def compactPath240 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => 0
  | _ => 0

def compactLive240 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => readCompactBits compactWords240 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs240 (k : Nat) (i : Nat) : List Nat := match k with
  | 3 => let v := readCompactBits compactWords240 (4 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords240 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket240 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP244 : Nat → Bits
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x89020c0c6,0xd466044404e618e,0xa66005e8f1010925,0x869a2ef27a325ab6])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x6f5ffdf9eb,0xacc23ffede7cf99f,0xe1e925287b77e96c,0xe3b726b23968fa16]))
  | 5 => ~~~((BitVec.ofNat _ (limbs64 [0x260090133,0x20daa0181010f017,0x1ce372d60444870,0x7b0536be3d8c3356])) : Bits)
  | 6 => (BitVec.ofNat _ (limbs64 [0x5eafbbcf37,0x1d701f7f77de707e,0x265e75081dfdcf35,0x7e5920b018bf7604]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x7affeff7d6,0x63deffddf9f3e787,0x9fe692e5f7cf58f3,0x9f8e1e4e679619f2]))
  | _ => 0

def samplesQ244 : Nat → Bits
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x776bdfad7d,0xfafb936ffafbd55d,0xd57dff77bda73bf5,0xaffbadeb76f35bbe])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x10a1024304,0x12185420904444b2,0xd02480483628140,0x822142652940ea10]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x260870130,0x204a924308004410,0x8541f4210d233005,0xc0216122714888]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x2152353040,0xc087ab0842813a09,0xa2f1b2423c9d4220,0x2818399286bf1404]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x508102009,0x821010420311009,0x30011010840890,0x502088204821122]))
  | _ => 0

def compactPerms244 : Array (List Nat) := ([[], [82]] : List (List Nat)).toArray

def compactDomains244 : Array (Sig × Nat) := ([(subcube 64 0, 5), (subcube 0 64, 5), (subcube 4 0, 4), (subcube 32 0, 4), (subcube 16 64, 4)] : List (Sig × Nat)).toArray

def compactWords244 : Nat → Nat
  | 0 => (limbs64 [0x1f60,0xff7fbfc16f28901,0x9645165bfe3fc7f,0x8c4768892503dfff,0xfc02202201401a9f])
  | _ => 0

def compactCount244 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 3
  | 4 => 1
  | _ => 0

def compactPath244 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords244 (23 + 12*i) 12
  | 4 => let v := readCompactBits compactWords244 (202 + 12*i) 12
    (readCompactBits compactWords244 (190 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def compactLive244 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords244 (0 + 5*i) 5
  | 5 => readCompactBits compactWords244 (59 + 6*i) 6
  | 4 => readCompactBits compactWords244 (214 + 7*i) 7
  | _ => 0

def compactPoolIDs244 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords244 (17 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords244 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits compactWords244 (85 + 5*i) 5
    let n := v >>> 3
    let bits := readCompactBits compactWords244 (77 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 4 => let v := readCompactBits compactWords244 (221 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords244 (221 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket244 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords244 (100 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 8)
    let v := readCompactBits compactWords244 (102 + 11*off) 11
    if v >>> 3 == (i/104729)%251 then [v &&& 7] else []
  | 4 => let d := readCompactBits compactWords244 (223 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 5)
    let v := readCompactBits compactWords244 (225 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | _ => []

def samplesP252 : Nat → Bits
  | 2 => (BitVec.ofNat _ (limbs64 [0x6f767fbf,0x9ff73ce3eaf9ea6a,0x4cc9ff1f7ffefdff,0x3d90df398ffc57cb,0x9ff087f883f6de2a,0xa83e88c247bf7be,0xfdf5bbfe8fe625f6,0x97fcc7c3288fb1c1,0xd7a43ae062bee690,0xfb31001c8507707f,0x3fbf4ecbfb29323b,0x805f94f85cf10823,0x30032bb8e1d65488]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x2094c002,0xc053313e048ba2f,0x85f7000c30006084,0x5c05c600887c488,0x1bc334ff83728ddc,0x2ecfefef3e018010,0x208603604a070164,0x14c781f9ee2db21d,0xd27d3cf871b78610,0x8f39fb9eb5f00451,0x861a04a292a9d33c,0xa6533e9d42f9ed3b,0x7b9bc0b5a565ffd8])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x7eda3ffe,0xfd9f4f5b334fa924,0x9194fffdf1f3ffbc,0xcfe7f5e1f38fcdb9,0xf8673461c71181cc,0xe0cc43210a7f9eff,0xefbe1fe3599f3f3c,0xfc3fb9f81f2c8e1c,0x3a7d7c03f1118307,0x840878823037fdcb,0xabd9f7af9087cf2c,0x17f01e1ce2886418,0x48987f94886da150]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x7b8fbfe7,0x7fefb7bfdc8e36c7,0x2126fffffe7fe7cf,0xf3f879fe3c0ff63e,0x1f98387e181e0df1,0x3f0f844a147feff3,0xf7dfe303fe1fc3df,0x7fcfc67fe030f01f,0xc3c19ffc01e1fc38,0x30831c04c7bef3,0xd5fe9bf61e79f00f,0xe600e39f03708920,0x3300b51f1762ca88]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x7db5ff7b,0xeefcfb3ff5f1d29d,0x8ef0fffeffbd7bf0,0x3e6f5ec64ff3aff4,0x7fef478763e92fd4,0x3573f1004267ff7d,0xfbea47fd6ff9d9e9,0x17f33fbcd74f4e21,0xd45a251f9cbf1950,0xfc0e3c034202ef7c,0xde5fad33e4a8cdf4,0x785f68e7a08e061c,0x8c1c1867fda56064]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x8020020,0x820c2b108122c4,0x880001040300108,0x3a20518007080730,0x1c3c0760439d0fe0,0x3103d10846020620,0xc11803830d980198,0x1738067e110ecc01,0xd7c03f0780b9f910,0xf43e3c1f4602386a,0x19dd8b031c29ec2f,0x505cc0fea0fe0e3c,0xbc1c391ed9e660ec])) : Bits)
  | _ => 0

def samplesQ252 : Nat → Bits
  | 2 => (BitVec.ofNat _ (limbs64 [0x1089a040,0x212c411454041485,0x3316494824280429,0x524a488aa0250898,0x2109280930212080,0xb405155118b2d398,0x8804804a81480100,0xb1841551124994a8,0xa0a80549208228a2,0x2180120b122b400d,0x230f0a4bc1210429,0x80c690404821202d,0x144a2a88e0d44408]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x2094c20a,0x60c1306e0188a07,0x85f3a8c84c823044,0x6994a402114ac80,0x8c83095aa260159c,0x121f4787066a48e8,0x5431c998041aa902,0x6315314d50e90246,0x62222b2084890221,0x1712f039304fe1a2,0x28a4c35548434ca3,0x438c110a38121064,0x9467f0a4a1a0022]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x125c803,0x2230b1246830129a,0x2e2bc24905816146,0x5c12024d08212610,0x45510b0ea0285c85,0x1a35789255751c32,0x8428db08140e1932,0x2137111404b02a8a,0x930a6251400b3212,0x2536506990cff103,0x8b51d08e0807c621,0x46841918a8a03111,0x288c7f90086ca100]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x470440d,0x8410104021514938,0xc8c9321200c022c2,0x881202549989340,0xc8c4458284809406,0x2504a24e34d0443,0x714249012e020a86,0x19400a44122844,0x51014830d4409551,0x9c1a44a00944baf0,0x90f011b01a026004,0x62004388211a0b50,0x2180951713228880]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x24a1064,0x9101048002022560,0x5004150090140019,0x60b0a2d488514a,0x2020900008120020,0x40800068a880a305,0x2bc0042000a10009,0x440020223069420,0xcc5040c33608dc8,0x8841010004100e5c,0x540a2c20a4080100,0x1811002500098e08,0xd4218065b5814044]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x77fdfedf,0xeffdf7f6ff7fdfbf,0xfffffbdbfdff77ff,0xffdf6fffebffbffd,0xffdfffdfbefbfdbf,0xfeff7ff7ffffdffb,0xfd7fdffbbfffbbbf,0xf7ff777fdefbffff,0xf3bbfffbfcdffff7,0xfffff7fbbffffbff,0xbbffdbffdf6fefaf,0xffdfdbfff9ff7bff,0x3fdeff9ffbfeedee])) : Bits)
  | _ => 0

def compactPerms252 : Array (List Nat) := ([[], [67], [82], [82, 67]] : List (List Nat)).toArray

def compactDomains252 : Array (Sig × Nat) := ([(subcube 8 0, 7)] : List (Sig × Nat)).toArray

def compactWords252 : Nat → Nat
  | 0 => 0x13f
  | _ => 0

def compactCount252 (k : Nat) : Nat := match k with
  | 7 => 1
  | _ => 0

def compactPath252 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | _ => 0

def compactLive252 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits compactWords252 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs252 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits compactWords252 (7 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords252 (6 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket252 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP254 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0x62b037f965eb4dcc,0xbc991dabfa9681f7,0x771dcc7d1ff82417,0xe7d2babe05bfe8ba,0x64017f40626000b8,0xf00f39e712a60f11,0x4400dc2ec40bc0c6,0x8f4f40002f503000,0x3e80140017000f83,0xfef7fe77bb8d2afd,0xd99e8c6bfe23f796,0xf4867d7c869e3e01,0xa3c15cf08a59004a,0x16074af071240360,0xe00181c80173aaf,0xfe41788194604304]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x86cbc34ffe3ef1b4,0x40fffa7d42642206,0xfffab59e60717ffe,0x5aa3d007ff759043,0xa2c2001ff8189f00,0x768c7e08c019de2,0x3c03200113f41f51,0xa080103fffa940c0,0xc0182007200c7003,0xff3f7f7fe7007fd2,0x2daff38c1dff0547,0xfe6191fff93180a2,0x45a403ed68802fb0,0xa0feb0a10e1f8081,0x8010c34000c7aef3,0xb178070659852410]))
  | 3 => (BitVec.ofNat _ (limbs64 [0xf8dffcb1903fbe3d,0xff1ce07e8d87fe39,0x384f3a0ff18ebce0,0xdd02ffd8e83a007d,0x107e06b03a35fc0,0x78908e090bba6003,0xc0fc00f14c400fa8,0x51f06fc7c0008707,0xc03848318007,0xffdbfbdafc5fb917,0x31f34fdfe26c39f9,0x73ab8e32e1c1b35c,0x619e001d161d63c,0x133803468f681c02,0x30e120201907f57d,0x648b0a6a0ae0004b]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xff21f83e1fc03fc2,0x6fe0ff800ff83fff,0xc0703ff07e0fc0ff,0x1ffd0fe70fc01f80,0x1fc0f941c43e00f,0x80f07010f44470fc,0x7fff00a187f000,0x7e0187f800060038,0x6701c080c2001b,0xdbfddffcffe7c1e8,0x3e3c53d3838ffe7e,0x8bd5efc31e0e401e,0xf81e0d06019ef840,0xec403c07f090600c,0x400e0480660fddde,0x591434a0671a08a0]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x9d4e37c685eb7233,0x33661dabf56941c8,0x889df3829ff7db17,0xf82d4ab9f5bff745,0x9a0170a07d9c00b7,0xf0f461812d98fee,0xbb80dc2e3a0c3f39,0xf4eb8002f5828c0,0x39181a07140c0e61,0xade81d977c75d4fd,0xe6512fb7fdd3c809,0xf7787280996e3de1,0x5c2152f774460035,0x1987750870c78351,0x8f10031b0024c33c,0x105eb05de0ec9710]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x79340b4ffbd58e4b,0x80ffe7d6bd9bdc06,0xffe74a6180717fe9,0xa55c2547faca6fbc,0x5d3c801f87e76040,0x767b81f6101921d,0xc3fc03d013fbe0ae,0x5030103fd0f6803f,0x7c000c8038003,0x303ee0efd8fa7f2f,0xd24ffc701dfcfaa7,0x99e11ff66c040a3,0xba5aa31a97202fcf,0x40f9cf5e80187c00,0x700f20a007024e03,0xeea7c7f7a11600c8]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x7ffccb06a14c1ff,0xdf030255727ffff9,0x7a2c5ffef8e8308,0x22fff5781245c002,0xfefa9fe0801cbf7f,0xf89001e6ed7e6000,0x3f0323dfec300057,0xa0bfefc010a15f00,0xc7e02ff823f071fe,0xc7c7a7a903ba8602,0xcfe0b02c621007f8,0xc7fee0d6031cf5c,0x1e6bc082ebfd183,0xef0080b90fe000be,0x1e0dc47f8f931c0,0x83a0c9181e19f827]))
  | _ => 0

def samplesQ254 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0x6a108109e0a91094,0x7d584f126a160882,0x256992d2d68004c,0x50d02a135cad4852,0x4061450a56868a28,0xa04200ac0a2bca49,0x42a4a4400854512,0x4c6cc2b29accaa32,0x9258b590012ae503,0xeeb6f677918428a4,0x9988090b5a05b682,0xe482cd7c928caa0a,0xa2c106d088990010,0x12538ab2200c4921,0x2c480854c0073aab,0xfe41288114400204]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x26881300ac0d3434,0x74c8db5949120016,0x965a8d05642b2a08,0x52b08301da897a50,0xe14983188a08c6ca,0x22881a62a8210344,0xd11838005094c358,0x8c821a19608e610,0x860a3c82c04bad17,0xbe3f673fa3002112,0xca6930910ff1107,0xa621959bd0858282,0x6188035468886330,0x90768a31040d0085,0x81341641287aee3,0xb148070259042010]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x884cf51314d41c98,0x3184483acd272cf2,0xb2001422218e1866,0x81a6a5024238111c,0x894285d080802b81,0x398b48a091081072,0x882c4c7650c165c2,0x204122c2cb075243,0x9b66001e51c88427,0xdddb9bca79029015,0x21b241c7e04539d2,0x73288e324300b30c,0x4a9885015043c618,0x91121302bd008d42,0x710881118ff57d,0x440a0a280ae00042]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x380dd03725cc0580,0x47cc010a81641dd0,0x9020356615a208fe,0x153ca3060a310216,0x7203e010132632,0x2a60646433807c5b,0x121b182080d0e3a0,0x2041d181865640d7,0x386a10ba63402167,0xd3e99df8ff8700c0,0x36985351030fdc5e,0x2041e6901704301e,0x7a0c0d40508f4200,0xc1003026f4110026,0x10c4298630fdddc,0x511030a0670a0800]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x104401200420201,0x26008090200448,0x801008202900022,0x904408801108189,0xc10202120310111,0x1121240000c02420,0xa05051288001021,0x1212104841320049,0x8204048001010a0,0x14008804c51d449,0x42010494a5004008,0x1158200009221404,0xc00402214020004,0x98050009040a440,0x9324020920204114,0x16904ca0a88500]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x200084082010044,0x220400988000,0x41528a0180004501,0x6000000130826081,0x260c70076c6c4040,0x8010921b04468104,0x458023012e081009,0xd6b6081800a8a100,0x4080260000060208,0x2004600500784f2a,0xc045ac200cb00221,0x896104520c00021,0x20210092008c2,0x488c58000c6090,0xf602252088700202,0xaaa5c55780140088]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x2200800000c002,0x8001000000004201,0x80401000008000,0x1106000400000,0x204100400400000,0x10801104040000,0x80000126080000,0x8000080000000000,0x100010c000000,0x280200,0x40202000000020,0x804000020104040,0x20300802001001,0x2400000002a00010,0x4000240008500000,0xa0401000115021]))
  | _ => 0

def compactPerms254 : Array (List Nat) := ([[], [67], [33], [33, 67]] : List (List Nat)).toArray

def compactDomains254 : Array (Sig × Nat) := ([(subcube 2 0, 8)] : List (Sig × Nat)).toArray

def compactWords254 : Nat → Nat
  | 0 => 0x27f
  | _ => 0

def compactCount254 (k : Nat) : Nat := match k with
  | 8 => 1
  | _ => 0

def compactPath254 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => 0
  | _ => 0

def compactLive254 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => readCompactBits compactWords254 (0 + 7*i) 7
  | _ => 0

def compactPoolIDs254 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let v := readCompactBits compactWords254 (8 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords254 (7 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket254 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP241 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x6edfff5db8,0xf1da7df77dcbbb59,0xb697760937f7dae3,0xc5b44c2d2ba6e64c]))
  | 4 => ~~~((BitVec.ofNat _ (limbs64 [0x230250029,0xb28a81120092aac8,0x9507374b00154888,0xe5566d2f2e9cc2ec])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0x77afefbeed,0xae48ff7fcbf3e69d,0xcd27934a79fd04bd,0xef7a252a2ddd2ae0]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x7b3fb7ef0b,0x3fb67fdebfb42be6,0xb1ddeca16f3ffd9a,0xb644ca8592f9d10e]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x2180020c88,0x2d5e004409212315,0xa095fea9212094b3,0x8620ceadbbe1234e])) : Bits)
  | _ => 0

def samplesQ241 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x1121048a42,0x604a450500268a1,0x88c81241546c040,0x8033406489268448]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x23824c009,0x90028c800a465820,0x8106c00b29c20426,0x108105a4c1232910]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x854704010,0x1a34a2001841018,0xf142681028b80099,0x4800858066d12a80]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x4c0d804a4,0x400950068408021c,0x74700240c2391900,0x640aa1026d85006]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x5e7df7f1ff,0xd7a3cef6dff7dd7a,0xf347eb7fa9faddff,0xdef195aff7f32bde])) : Bits)
  | _ => 0

def compactPerms241 : Array (List Nat) := ([[], [116, 101], [64, 117], [64, 84, 101, 118], [80, 118], [80, 100, 117, 118], [96, 84], [96, 116, 101, 118], [112, 116, 117, 118], [112, 100]] : List (List Nat)).toArray

def compactDomains241 : Array (Sig × Nat) := ([(subcube 1 0, 4), (subcube 16 0, 4), (subcube 32 0, 4), (subcube 64 0, 4), (subcube 128 0, 4)] : List (Sig × Nat)).toArray

def compactWords241 : Nat → Nat
  | 0 => (limbs64 [0xff0308ff0ae6,0xff03e4ff0279ff0f,0xf0ff0ff0802ff00a,0xf946802230ff01e1,0xb59cff2ff03c47fc,0x1f08ff07f8288557,0x35227f83fc08e916,0xfffd00900688d11f])
  | _ => 0

def compactCount241 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 2
  | 4 => 1
  | _ => 0

def compactPath241 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords241 (26 + 12*i) 12
  | 4 => let v := readCompactBits compactWords241 (305 + 12*i) 12
    (readCompactBits compactWords241 (293 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def compactLive241 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords241 (0 + 5*i) 5
  | 5 => readCompactBits compactWords241 (50 + 6*i) 6
  | 4 => readCompactBits compactWords241 (317 + 7*i) 7
  | _ => 0

def compactPoolIDs241 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords241 (20 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords241 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits compactWords241 (64 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords241 (62 + 2*(v &&& 1)) (2*n)
    compactIDsFromBits bits 2 n
  | 4 => let v := readCompactBits compactWords241 (324 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords241 (324 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket241 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords241 (68 + 1*(i % 4)) 1
    let off := ((i/4 + d) % 17)
    let v := readCompactBits compactWords241 (72 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 4 => let d := readCompactBits compactWords241 (326 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 14)
    let v := readCompactBits compactWords241 (328 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | _ => []

def samplesP181 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xf68ffad7961d,0x5843efdefb4de478,0x1bec58083dfecd5c,0x7c9bc12142ebd620]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x22500083f80c,0x5a78044c0045f720,0x9b805f0ec502011c,0xb11b67f95a08deba])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0xbc6fa7fb7986,0xc813fffd66f1d7a7,0x9e0201067f77e1be,0xa36f22c808dc7c0a]))
  | 5 => ~~~((BitVec.ofNat _ (limbs64 [0x48002101216,0x84900a8040210482,0x1c2f814750608198,0x4ecc02ce0d93454a])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0xefdfdfbffa7e,0xb6bbfeefdde73f82,0xfdbf8747f7eb9399,0xdfdc66de1d93cdda]))
  | _ => 0

def samplesQ181 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x97244e860e0,0x93b7420c389710e6,0x8373943634dacc38,0xc43470987ebc420]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0xddaef77657db,0xe5a6cf7bf46cbef5,0xd4fb65ed85c7fb94,0xfb3af6bd7e0edfbe])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x4390ce052229,0x34ece12448cc5d4c,0x2ca6b05aab6744ac,0x84690a7328dc7808]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x48802041012,0x400841300080c00,0x480010101053000,0x3100803028041a84]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x102400600500,0x41020840840000a0,0x8050408004808300,0x4210240806028512]))
  | _ => 0

def compactPerms181 : Array (List Nat) := ([[], [64, 117]] : List (List Nat)).toArray

def compactDomains181 : Array (Sig × Nat) := ([(subcube 1 0, 5)] : List (Sig × Nat)).toArray

def compactWords181 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount181 (k : Nat) : Nat := match k with
  | 5 => 1
  | _ => 0

def compactPath181 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => 0
  | _ => 0

def compactLive181 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => readCompactBits compactWords181 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs181 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let v := readCompactBits compactWords181 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords181 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket181 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP213 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x5ecffcf9fc58b4,0x17fdcf7fa52e43f9,0xfd8d017efdeee7a,0xc994a34181ae750c]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x7b2fff5e48677a,0x47ff7e97d6d0cf1e,0xb4ef01079fef011f,0xbfbb100c27f7c860]))
  | 4 => ~~~((BitVec.ofNat _ (limbs64 [0x8602c002c43b2,0x5005000586324318,0x36dfd1100342241e,0x8f90b34da636d46c])) : Bits)
  | 6 => (BitVec.ofNat _ (limbs64 [0x6f7fbfbfb7e797,0x97ffb3efceff323d,0xfb18fe15f3fbfc9f,0xf641a3e1d8bd9e8e]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x3001018106415,0x9018020204cc023d,0x8908fe118088c81b,0xf00123e1d8ad088e])) : Bits)
  | _ => 0

def samplesQ213 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x21322296230741,0xe542086383718624,0x4e2e4cc74ad4e079,0x188611163aa7108]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x4d144a2b59100,0xb9b624208954154a,0x1b52566694cb402b,0x249a15640be5c820]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x8682600a90192,0x506282b08025124c,0x146245559c104129,0x40cd440549c82890]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x1080c028400828,0xa8910082c804903,0x1110008212b0c80,0x920012e204158606]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x7cfbffe3bf9ffa,0xf9ffbefb997f37de,0xbff75fff9cdbedfb,0xf7df5d6ddbede8be])) : Bits)
  | _ => 0

def compactPerms213 : Array (List Nat) := ([[], [32, 118]] : List (List Nat)).toArray

def compactDomains213 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray

def compactWords213 : Nat → Nat
  | 0 => 0x1f
  | _ => 0

def compactCount213 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath213 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive213 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords213 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs213 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords213 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords213 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket213 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP245 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xde7afdffafb979b6,0x3ed8d90cb92fffdd,0xcffbf7f7f9b72cfc,0xdc2bfca1dc9d780a,0x550b62e256422139,0xffdf7ee75cfbb4fe,0xa795e7bd089d7251,0x347c3b5c4ce1c86a,0xf2ea91e88040bde8,0xebe5ff8fa9c792fc,0x1527628cf20a3482,0x4a22bdc58e2c6118]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x35100600a016ec6,0x6025354fcf00000,0x810995462a04049e,0x198070299f97ab30,0x150bbe74d6f73b80,0x941004818eca530,0x83811121eb097a57,0x3d2fa3c5cf83aa62,0x5a8895fff45bc261,0x4b000e1c21e654e4,0xa307961eda7bf7f2,0xcfbb818e166f75de])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0xfbe8fefa7ff727cf,0x2bed1644d64ff73a,0xffffbcc8ee8ef2db,0x5ffc73f9fb12a754,0x2dc09b31948508b7,0xfffbadfeafe7d7f0,0xdbe59b53cf21ec66,0x33a3e4e38c9f2e12,0xa94040474197bfb,0xcf3c9d775da45d65,0x8bc41c75cc30c270,0x81983b1c42d75046]))
  | 5 => ~~~((BitVec.ofNat _ (limbs64 [0x100a008020220190,0x33899d8910600400,0x4b00000f0b840e0,0x5e3000c1e01c3f98,0x65f203c399878d81,0x44802807cf021080,0xc305041e0fc18078,0x37c1c07c0cfe0f82,0xe2ffe68cf61dc908,0xcc2521c791e61c7a,0x1df878c5063ce6fc,0x8bdcea65ea3a5a5e])) : Bits)
  | 6 => (BitVec.ofNat _ (limbs64 [0xf797ffe7fbebeef9,0xf7832bd308effeff,0xb5ffd94733f8ddfe,0x3fb21effb06d2fb8,0x20bfbe56b886012f,0x6fedffeffbbce98b,0xefeb153ee3c08239,0xff0b835503f21fc6,0x7e8f848cd400ae5d,0xfe9b27def1fe449a,0xbdda9312061826e0,0xb1888ef717a901c]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xbf5ffffdfe76dfd6,0xd73ad5b974fffde7,0xffbdff3efe7d47a7,0xfbd5e14fe7969bb1,0xd77205cdc9319ebf,0xddf7fb59df4e3f35,0xd31f7cef3f4b19de,0xdc5c0acff0ea3a1,0xc1796213221f5b27,0x5d676afdb2623c62,0x6239fccf1a65c11c,0x84c56222be2b4ec2]))
  | _ => 0

def samplesQ245 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x2185120449424601,0xc021227342d522c2,0x8818309104c3583,0x416124813640305,0x80b11d0040ac9871,0xa510664080aa003a,0xb00e05c006b0a38,0x99824308091824e,0xc912611851983928,0x6261c98d09c18178,0x8026040d06a0413,0x9427d448e204110]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0xfcaef5d775ff95bb,0xbdfdaeaf13aeafa9,0xdddf7eadbdebee77,0xf7735abd6ad9d6ef,0x7beed7ebbb8bd455,0x795df1ca7ddfefed,0xd6b7dd3bbed8db55,0xaff776d6eada7f79,0xbf57deb56b76c67d,0x5b713e7d2f6f7cd6,0xa76fdf3ebf79bb5a,0xeff781be976f7dfe])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x4178124e008d210,0x440269a908b0b442,0x8044a21c90180c0a,0x30832682a1251120,0x9017480a4902b364,0x323328c0a8210292,0x4984304542182952,0x53108e10163800e0,0x8e30290812cab8cb,0x873418244880c92c,0xb00306444a05146,0x29883b1402d51040]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x100a418020100080,0x31088c8810288100,0x1024c04a0030a60,0x3201008020180480,0x4040024081030404,0x180d808800504844,0x1000012002100140,0x22402c4020a4031,0x2605840020040455,0x110163006000080,0xa005050020101940,0x20a1809a01452420]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x868049802940102,0x549404b50a4009,0x101014426b038260,0x8a68812048808002,0xb0000810251448a,0x48cc91224100a100,0x423000019848481,0x6641cd41067811,0x208d022100204614,0x188a2652b00e0400,0x448021200152aa0,0x902580ab710a800c]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x40a0201001c10028,0x885020603060820,0x440800010940a001,0x8470102840004048,0x2008802032884011,0x4140510014040401,0x80100c0218c08201,0x8c26000c0803a08,0x102108408000220,0x5841204920203002,0x2088080a492210,0x80460020942a4882]))
  | _ => 0

def compactPerms245 : Array (List Nat) := ([[], [64, 117]] : List (List Nat)).toArray

def compactDomains245 : Array (Sig × Nat) := ([(subcube 1 0, 7), (subcube 4 0, 7), (subcube 16 0, 7), (subcube 64 0, 6), (subcube 0 64, 6), (subcube 32 0, 5), (subcube 128 0, 5)] : List (Sig × Nat)).toArray

def compactWords245 : Nat → Nat
  | 0 => (limbs64 [0xdf13dce14,0xc3865ff03c1ff0ff,0xff0df3700b696f5,0x5a7c62c71413adbf,0xfdbdbdbe930dcc17,0x3044c11302195194,0x196d9ca5579fe188,0xff8ff05529540534,0x9210876432015697,0x89863421705fffff,0xc32a32832d11a23f])
  | _ => 0

def compactCount245 (k : Nat) : Nat := match k with
  | 8 => 1
  | 7 => 3
  | 6 => 5
  | 5 => 1
  | _ => 0

def compactPath245 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => 0
  | 7 => readCompactBits compactWords245 (27 + 12*i) 12
  | 6 => let v := readCompactBits compactWords245 (346 + 14*i) 14
    (readCompactBits compactWords245 (310 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 5 => let v := readCompactBits compactWords245 (644 + 12*i) 12
    (readCompactBits compactWords245 (620 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | _ => 0

def compactLive245 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => readCompactBits compactWords245 (0 + 6*i) 6
  | 7 => readCompactBits compactWords245 (63 + 7*i) 7
  | 6 => readCompactBits compactWords245 (416 + 8*i) 8
  | 5 => readCompactBits compactWords245 (656 + 9*i) 9
  | _ => 0

def compactPoolIDs245 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let v := readCompactBits compactWords245 (21 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords245 (6 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 7 => let v := readCompactBits compactWords245 (204 + 9*i) 9
    let n := v >>> 5
    let bits := readCompactBits compactWords245 (84 + 4*(v &&& 31)) (4*n)
    compactIDsFromBits bits 4 n
  | 6 => let v := readCompactBits compactWords245 (471 + 5*i) 5
    let n := v >>> 3
    let bits := readCompactBits compactWords245 (456 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits compactWords245 (665 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords245 (665 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket245 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let d := readCompactBits compactWords245 (231 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 7)
    let v := readCompactBits compactWords245 (233 + 11*off) 11
    if v >>> 3 == (i/104729)%251 then [v &&& 7] else []
  | 6 => let d := readCompactBits compactWords245 (496 + 2*(i % 2)) 2
    let off := ((i/2 + d) % 10)
    let v := readCompactBits compactWords245 (500 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | 5 => let d := readCompactBits compactWords245 (667 + 1*(i % 1)) 1
    let off := ((i/1 + d) % 1)
    let v := readCompactBits compactWords245 (668 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | _ => []

def samplesP253 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xfffd1fa0cfa4ecfe,0x85edc5dfc5ec6781,0x68ede2aea36e5fc1,0x36a77078fba6f380,0x150270787ea32920,0x208d685d8c0fbc69,0x610478c681f1507c,0x80aeb355943b6042,0x83214e4080008190,0x13ff5fe7775aef14,0xd7f8b8df19fa7d7,0x7d82f99e343e22c7,0x605fca029a6087c,0x714c4580f8a1221a,0x2002640820cb8d6f,0xd782c46833461180]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xf8bffaeb1dfdb317,0xfb11b1ee0abff819,0x3998fdd32d89a48b,0xcf53b990dedbbc43,0x238bd687804c2a1f,0x427034e66261e003,0xdea380076214adb1,0xe2431982203ebc8d,0xcc2000001e26041,0x3f7bef79e92ec7f,0xe58a766e4febb6a0,0xded8bf23db458903,0x98460f570a805f92,0x3a1fb017145c0404,0x21918004307d5b6,0xe170f8474488a208]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x9f7b60f3f2fa7c63,0x9e1e36f8734fbde2,0xbf1f0ecdd2f1f8f4,0xf07dc0ef1d1dc086,0x181c07190811d4bf,0xa301c128645001bc,0x1d2801780ea31c40,0x7d3c6e084fc05f10,0x700c00140e050606,0x7fbf7bfffe9f8a7,0xcbbde073b235d8bb,0xb9e90edb6d89b478,0x13983106b563a623,0x4021c22f25801820,0x9c2401c18403fbfb,0xa94171258c00027]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xbfc3bf5ccf5b537d,0x65f20d27b9e3867d,0x57f2127f5c6f9f3e,0x36da8f7764470f78,0xef088667142d6c0,0x1c0c97921bae4256,0x82d078b971086203,0x9140a59bc48060,0x1030a870181828,0x2bbefffdfeae17d3,0x7cf0aff1cda65b6b,0x6374f6e9b23042b8,0xe5e2c2b8161df040,0xf8239b8c240c0c1,0x1c082061813fedd,0xb02a21098d350450]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x5ffedfff30007f80,0x5fffa07fe1007fe,0x80fffd0fff901fff,0xc903ff807ff803ff,0xe000ff807ffc0000,0x3ff2001ff00fff80,0x3ff870001fe807f,0xff4003fa60000043,0x3c1870300e0e1c0,0xc35cbb3a6bf507e8,0x723f53fe0e47e3fc,0x81ff00f437c03d03,0xf80700bfc038007f,0x81f07e40ff1e030c,0x4203783020e26b54,0x543d06b5919a5a08]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xe1afee1429b7878b,0xfaaadeb8df72d967,0xc601b5303516e30a,0xfbfc467fa1befd3c,0xd9f7002f82301745,0xc0fe4e2115d00cf9,0xa0481fbf9c04f78a,0xe84f472954bffa0,0xa03c68ecd4150414,0x128761cfc93d3279,0x96427d19bef84c54,0xde276b3fc8bac9d4,0x63b91e48cec45789,0xc4558ae800617813,0xa9a4068c1c093028,0x8d4fbb86a66901e4]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x6654f50ff64f88fc,0x7a456b51249d7a9e,0xff664bf0caff6075,0xdac3f8f82617e01,0xe66d29d0858fe9fa,0xdd03bbc08bb01306,0x7c17e640fe4b0b84,0x117b8c0d6ab5039c,0x5c0291132b0a1a2b,0xede9cc58b447d98e,0xbbc59c8671583d0f,0x261fd544c847562c,0xc78e141715ba984,0xbeaa05570ba285e0,0x54588173c3348683,0x2ac148f86a34ec13]))
  | _ => 0

def samplesQ253 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x6ed14a004115862,0x81a9557110214100,0x6874aa42440ef840,0x20b706804c3b100,0x1081a6d00320eb85,0x62031285044e5093,0x1c10188181e10a38,0x9396a2a5214e2313,0x2c2121505508e43a,0x3ef5ce3530ac912,0x1778305f08ba123,0x7c82d282103ea213,0x202ed0012220018,0x71060080ec83a202,0x843054440c7856f,0xd382406830441100]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x328c122948257830,0xc93134b000a65020,0x8303ac4240bac18,0x580058324ad11851,0x19a492dca0454e09,0xca25b00122c48402,0x48492a1221c408d0,0x26848b8916530805,0x640104729154a81c,0x27e72e7786026407,0xa592064887e2a0a1,0xccc8af23c0158801,0x808647130a20c312,0x580f001244880642,0x22a908810a07d5a6,0xe110b84344082008]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x8e383143e4b84911,0x190d1453526d406a,0x521c1a0ec0a8e530,0xf2394a161d81894d,0x498c0e349a81e847,0x510f0020a1c3088,0x98a8984884840472,0x100d019d05ca066f,0x2264f0b007cc9892,0x47dbf79eff40d0a6,0x48bc2223a281d0b3,0x19698a49650c9258,0xa1902326b0298630,0x4924128e24850820,0xe2023110693fbfb,0x214151058c00022]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xb3093d3164791338,0x8c2c006733450039,0x4e2c305744e24f10,0x56591e320d409b94,0xc86b30290a5949,0x292456064c94c815,0x88212c534081049e,0x281700a382560866,0x4ed30601e4e298a,0xd7bcfbfdfc885612,0x7c10a7d0c9a4d329,0x910c6e811180239,0xe0c266a2921c8220,0x1d2231aa60488068,0x410a16060c13fedd,0xb02201098d110400]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x912490420080500,0x4682020a500488,0x28a440008a00180,0x1082802120008a,0x40404101108a1002,0x4100410c0002a4c,0x2180840854121005,0x8485412808084a0,0x8054100422000281,0x4010810828f102e8,0x100840b20804025c,0x35001023400008,0x30010028c0080065,0xb050081104480c,0xc500301220282a10,0x42d061481924200]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x4002c20001028000,0x2000000884008804,0x1000011100002,0x1800000000c4002,0x2432100b00440420,0x80800170b0200640,0x61440300321ad001,0x4405c005001c080,0x1002020100000040,0x800000000352049,0x8200580804500c44,0x8204211488800184,0x20100004c01080,0x40884000004515,0xa0848880a1280000,0xc49aa86022800c4]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x4040800012000084,0x200080000002200,0x8100012002000005,0x4010180000400,0x24130002002000a0,0x8201e010220000,0x41401800228c200,0x8100200060006100,0x100080800210000,0x40900,0x241180410180c00,0x2202100408004400,0xc08004001002800,0x8200040102222111,0x448040c1400000,0x8c040a022248811]))
  | _ => 0

def compactPerms253 : Array (List Nat) := ([[], [67]] : List (List Nat)).toArray

def compactDomains253 : Array (Sig × Nat) := ([(subcube 8 0, 9)] : List (Sig × Nat)).toArray

def compactWords253 : Nat → Nat
  | 0 => 0x27f
  | _ => 0

def compactCount253 (k : Nat) : Nat := match k with
  | 8 => 1
  | _ => 0

def compactPath253 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => 0
  | _ => 0

def compactLive253 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => readCompactBits compactWords253 (0 + 7*i) 7
  | _ => 0

def compactPoolIDs253 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let v := readCompactBits compactWords253 (8 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords253 (7 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket253 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP255 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x6113090108004040,0x818400408fbfffbf,0xededfbf3e38c3feb,0xfca3f1fcf9ff3c79,0x770eb71fed0a003c,0xc7b6bf4d263e46d,0x3e31988c61fc4567,0xf9d1efe0ba888f8c,0xdc115b8d4037001c,0x160b001c6062de09,0xd801473139107e84,0xe4ec18010830901f,0x8358110105202000,0x86202102831bfe77,0x11cd7ac17685f012,0x610d0163a2608900]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x9a0440024000028c,0x62003981ffffbfb,0xda7e5eeffb7efb7d,0x9f5cf8fb3dceff3f,0xa3e038acaf513f5f,0x6d983c8b0ace85ea,0x85dffe907e0b3e73,0xade431e4bb8300b,0x3f4ea3a05d08e1e7,0x4a3c06aad0074,0x5c8a048d40020992,0x16b803a25c81e42,0x2472001a82038000,0x3100d2010043dddf,0x3cab36bed9710825,0xb08033109a020604]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x8a00400078430,0x501c200fefdf7f,0xffb37f3f7e17f5fa,0xdfff3d17f70ddffd,0x4bc887122efff4a0,0xbda3845b3d111a67,0xc802617ff8b469b4,0xa45e18ff749e0bf4,0x206ebf76a24a1c00,0x481345a0805127f2,0xa168590001bd9060,0x76003ff4c140c1e1,0x4087c00400c00106,0x40c400040c07f7fa,0xa66e9d8f6b882f02,0x4e08ca8440891010]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x5800780900,0x7800e0002fffefef,0x7fbf9dfc3def5e7f,0x6fdbdfeec6f761de,0xfc164ff09172c5c0,0xc1c7b7e5e6cc1f12,0xf7ec0e31815f8ac8,0x2fa2b4cebf6250f8,0xc7971c3b07841d99,0xa3e0060f0f001880,0x1d1a2d05e4e2078,0x8101c1c1068321a4,0x6d0400e0080c1e09,0xb00181003bbbf,0xfb94ed74ac225160,0x156240a87800004b]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xe006a017803003,0xb00014eff7dff,0xfbdde5cbddfba797,0xf3bfefcbfef9bde6,0xc8f7b0e35288fa3c,0xf278d30ad4b3fb10,0x39c1974d9e63b19b,0xd62caf1185752f73,0xdbe9044cb830e202,0x15f0f813901cc109,0x2600b82ea6e04104,0x1a920600f0336e18,0x12a00e00301000f0,0x81000e06023efed,0xcf53c379974c0291,0x88a10c1d055020a0]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xe407b003a00382f0,0x7d003e61b31b476,0x5473a0ec05713c81,0xe01f06f43d30c2bf,0xdc1970af50a43f63,0x921c3f7423cd7a95,0x45de61627e74c070,0xf521131ef447c00b,0xe0b043ada2c0e1f8,0xe8075c206ad2207d,0xa37404b280027669,0x194603bda041e5d,0xd873e01b43c3c100,0xc6c0ec0203826114,0xd13d453101848bc9,0x8156bd2159a4d610]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x1500bb80c906900,0xb005a00087d21ec1,0xa8027f10ea9fca0c,0x35e06317cbe2cf82,0xb03f494d0cfd4bcf,0x4a24401b3d3ec59c,0xb2227bf7878b960c,0x11dd58e102f9f694,0x307ffcd259b50606,0x4e5cba4f15022f06,0x1a96694121ad8d1f,0x8c0cabce369f2000,0x8c17e0043c24e9,0x320140f0190683,0x46a01ace8a72a4fe,0xef0f446a69009c8]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x1ea85444f36c140f,0x482a5c1f6c4ce39c,0xb7cc821796e0c1f6,0xa649e29021f3241,0x7e1ce50f3078093,0x37c7c8a4c93020eb,0x4a3d848a01807f8f,0x4a23e4214907fd67,0xf80e052044b1a61,0xb1a801f095add082,0x442f924ede518283,0x7a735404096cc1a2,0xbf082804f8005a16,0x390d1ebd0ce49868,0x2852a002741b540c,0x721f02da054f6027]))
  | _ => 0

def samplesQ255 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x604c5d4104945070,0x362e40601fbbffbd,0xe5dcfb3389843fe3,0x16a350fcf8ef2c39,0x7306b610cf08802c,0x41b6fb4d083c469,0xbe31820460bc4553,0x4c52ace033108d18,0xcc001b844437041a,0x1043000c6031d680,0x9c008c3019021c04,0xe0e08c000010905e,0xc320390102200410,0xc12920458307fe77,0x10cd7a4176857010,0x600d0160a0408800]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x488cec1752204004,0xd26139701fddfafb,0xdafe5aadfb5eeb6c,0x9b55b8fb5dcad73b,0x2362108826502936,0x61992c88528a8c2a,0x858ade80ec0b3333,0x8d6021c59b8102a,0x574ea9a0cd00c94f,0x90a2c428252064,0xcc88142c49020824,0x529829c25499442,0x2660448828b0880,0x1104b2808013dddf,0x3cab36aed9710821,0x1080231092000404]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x380a61c7ca856851,0x8047ab313fe7df5e,0xfdb66f3f7a17d1ba,0xcf673d55f744df6d,0x61c083022e42c4a0,0x38ab859318119866,0x9082007fb8254931,0x241e387474920afc,0x21629f7081125c01,0x40116181005163a4,0xa0685c1403851860,0xb5081fb42448c0ca,0x4106800510a2212a,0x404610102807f7fa,0xa66e9c8f6b882902,0xe084a8400810010]))
  | 3 => (BitVec.ofNat _ (limbs64 [0xcde00ac0003f1a47,0x12c461022f7fafef,0x3ebd9ddd2ceb5c77,0x6e99cfe652f764de,0xf442164094228544,0x81c1b7e146c10f20,0xf3cc8a2488178ac0,0x2f06a0ce9f4248b8,0x43870d190e060d89,0x92e04a8724041181,0x9518090ce0e3030,0x91a0c89046112784,0x6100506a08000f08,0x121804101a23bbbf,0xfb94ed74a4204140,0x152200a878000042]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xa0e4258202f91c1d,0x1a24856aefe75f7,0xfbd5acc39df926b5,0xf2bfe74bfe793dce,0x89e632e30208b03c,0xd2e83108d491fd10,0x1881870dbe45a191,0xce3c234481140c73,0xd1a30004da144182,0x11f17a01803c5329,0x4509826e2042004,0x38804400c0733e8c,0x2a08800990040c2,0x80b0c0e03023efed,0xcf53c371970c0211,0x80a10c1d01102000]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x8020000801080000,0x880040a00000000,0x1004004200000,0x2008020000100080,0x8c18402510a41241,0x200004020442210,0x4044210002400000,0x9121010200454001,0x100008224020a0,0x200c0002020011,0x214000080006208,0x10600340002201,0x81042220144c240,0x280442200880000,0x41100110000082c8,0x8142940149241200]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x201000460000000,0x8011008040000000,0x2000042008008,0x140000001008200,0x19490c00954a83,0x8040002292c0084,0x70d20100100c,0x1081500100293204,0x2018604201800000,0xc0c000010002804,0x8214100208102,0x40c0244308c0000,0x60604445da021,0x842020a04d80000,0x20008a085284ae,0xa50f00206800188]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x10002000008180,0x0,0x0,0x0,0x1081041010000,0x404400401200081,0x3000000180040c,0x44010000a100,0x800400200080200,0x2000003001800002,0x2020000500081,0x202000008000020,0x1408210044100011,0x801000d05400000,0x21404,0x60140042044a4021]))
  | _ => 0

def compactPerms255 : Array (List Nat) := ([[], [67], [33], [33, 67]] : List (List Nat)).toArray

def compactDomains255 : Array (Sig × Nat) := ([(subcube 1 0, 9), (subcube 2 0, 9), (subcube 10 0, 9)] : List (Sig × Nat)).toArray

def compactWords255 : Nat → Nat
  | 0 => 0x312ff
  | _ => 0

def compactCount255 (k : Nat) : Nat := match k with
  | 10 => 1
  | _ => 0

def compactPath255 (k : Nat) (i : Nat) : Nat := match k with
  | 10 => 0
  | _ => 0

def compactLive255 (k : Nat) (i : Nat) : Nat := match k with
  | 10 => readCompactBits compactWords255 (0 + 8*i) 8
  | _ => 0

def compactPoolIDs255 (k : Nat) (i : Nat) : List Nat := match k with
  | 10 => let v := readCompactBits compactWords255 (14 + 4*i) 4
    let n := v >>> 2
    let bits := readCompactBits compactWords255 (8 + 2*(v &&& 3)) (2*n)
    compactIDsFromBits bits 2 n
  | _ => []

def compactBucket255 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

theorem compactHalves {test : Nat → Bool} {start n : Nat}
    (first : chartBlock test start (n / 2) = true)
    (last : chartBlock test (start + n / 2) (n - n / 2) = true) :
    chartBlock test start n = true := by
  have eq : n / 2 + (n - n / 2) = n := by omega
  simpa only [eq] using chartBlock_join first last

def grid164 : CompactGrid := (164, 3, samplesP164, samplesQ164)
def tab164 : CompactTable := (compactCount164, compactPath164, compactLive164, compactPoolIDs164, compactBucket164)
def check164 (k : Nat) := compactNode grid164 tab164 compactDomains164 compactPerms164 k
def sliceSpecs164 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains164 : ∀ d ∈ compactDomains164, Slice true (vars 164) (graphGoal 164) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs164)
  · simp
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs164 : properPairs (graphGoal 164) (asRow samplesP164) (asRow samplesQ164) :=
  compactPairs (g := grid164) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos164 : ∀ p ∈ compactPerms164, autoOK (graphGoal 164) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c164k3p0 : chartBlock (check164 3) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev164k3 : chartBlock (check164 3) 0 1 = true :=
  c164k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded164 : Impossible true (graphGoal 164) 3 (vars 164).toFinset := by
  apply compactRoot (g := grid164) (t := tab164) (dom := compactDomains164) (perms := compactPerms164) pairs164 domains164 autos164
  · intro k hk
    change k ≤ 3 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev164k3
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound164 : Lower true (vars 164) (graphGoal 164) 4 :=
  plain_low (hints := 538969344) (by decide +kernel) excluded164

def grid180 : CompactGrid := (180, 4, samplesP180, samplesQ180)
def tab180 : CompactTable := (compactCount180, compactPath180, compactLive180, compactPoolIDs180, compactBucket180)
def check180 (k : Nat) := compactNode grid180 tab180 compactDomains180 compactPerms180 k
def sliceSpecs180 : List SliceSpec := [(16, 0, 164, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains180 : ∀ d ∈ compactDomains180, Slice true (vars 180) (graphGoal 180) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(164, 4)]) (specs := sliceSpecs180)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound164
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs180 : properPairs (graphGoal 180) (asRow samplesP180) (asRow samplesQ180) :=
  compactPairs (g := grid180) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos180 : ∀ p ∈ compactPerms180, autoOK (graphGoal 180) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c180k4p0 : chartBlock (check180 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev180k4 : chartBlock (check180 4) 0 1 = true :=
  c180k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded180 : Impossible true (graphGoal 180) 4 (vars 180).toFinset := by
  apply compactRoot (g := grid180) (t := tab180) (dom := compactDomains180) (perms := compactPerms180) pairs180 domains180 autos180
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev180k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound180 : Lower true (vars 180) (graphGoal 180) 5 :=
  plain_low (hints := 539428096) (by decide +kernel) excluded180

def grid240 : CompactGrid := (240, 3, samplesP240, samplesQ240)
def tab240 : CompactTable := (compactCount240, compactPath240, compactLive240, compactPoolIDs240, compactBucket240)
def check240 (k : Nat) := compactNode grid240 tab240 compactDomains240 compactPerms240 k
def sliceSpecs240 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains240 : ∀ d ∈ compactDomains240, Slice true (vars 240) (graphGoal 240) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs240)
  · simp
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs240 : properPairs (graphGoal 240) (asRow samplesP240) (asRow samplesQ240) :=
  compactPairs (g := grid240) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos240 : ∀ p ∈ compactPerms240, autoOK (graphGoal 240) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c240k3p0 : chartBlock (check240 3) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev240k3 : chartBlock (check240 3) 0 1 = true :=
  c240k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded240 : Impossible true (graphGoal 240) 3 (vars 240).toFinset := by
  apply compactRoot (g := grid240) (t := tab240) (dom := compactDomains240) (perms := compactPerms240) pairs240 domains240 autos240
  · intro k hk
    change k ≤ 3 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev240k3
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound240 : Lower true (vars 240) (graphGoal 240) 4 :=
  plain_low (hints := 1148583936) (by decide +kernel) excluded240

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound212 : Lower true (vars 212) (graphGoal 212) 4 :=
  carry_of (old := 212) (rep := 240) (swaps := [82]) (by decide +kernel) bound240

def grid244 : CompactGrid := (244, 6, samplesP244, samplesQ244)
def tab244 : CompactTable := (compactCount244, compactPath244, compactLive244, compactPoolIDs244, compactBucket244)
def check244 (k : Nat) := compactNode grid244 tab244 compactDomains244 compactPerms244 k
def sliceSpecs244 : List SliceSpec := [(64, 0, 180, 0, 0, 5, 5), (0, 64, 164, 16, 983040, 5, 4), (4, 0, 240, 0, 0, 4, 4), (32, 0, 212, 0, 0, 4, 4), (16, 64, 164, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains244 : ∀ d ∈ compactDomains244, Slice true (vars 244) (graphGoal 244) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(180, 5), (164, 4), (240, 4), (212, 4)]) (specs := sliceSpecs244)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact bound180
    · exact bound164
    · exact bound240
    · exact bound212
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs244 : properPairs (graphGoal 244) (asRow samplesP244) (asRow samplesQ244) :=
  compactPairs (g := grid244) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos244 : ∀ p ∈ compactPerms244, autoOK (graphGoal 244) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c244k4p0 : chartBlock (check244 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev244k4 : chartBlock (check244 4) 0 1 = true :=
  c244k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c244k5p0 : chartBlock (check244 5) 0 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev244k5 : chartBlock (check244 5) 0 3 = true :=
  c244k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c244k6p0 : chartBlock (check244 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev244k6 : chartBlock (check244 6) 0 1 = true :=
  c244k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded244 : Impossible true (graphGoal 244) 6 (vars 244).toFinset := by
  apply compactRoot (g := grid244) (t := tab244) (dom := compactDomains244) (perms := compactPerms244) pairs244 domains244 autos244
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev244k4
    · exact lev244k5
    · exact lev244k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound244 : Lower true (vars 244) (graphGoal 244) 7 :=
  plain_low (hints := 606471424) (by decide +kernel) excluded244

def grid252 : CompactGrid := (252, 7, samplesP252, samplesQ252)
def tab252 : CompactTable := (compactCount252, compactPath252, compactLive252, compactPoolIDs252, compactBucket252)
def check252 (k : Nat) := compactNode grid252 tab252 compactDomains252 compactPerms252 k
def sliceSpecs252 : List SliceSpec := [(8, 0, 244, 0, 0, 7, 7)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains252 : ∀ d ∈ compactDomains252, Slice true (vars 252) (graphGoal 252) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(244, 7)]) (specs := sliceSpecs252)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound244
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs252 : properPairs (graphGoal 252) (asRow samplesP252) (asRow samplesQ252) :=
  compactPairs (g := grid252) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos252 : ∀ p ∈ compactPerms252, autoOK (graphGoal 252) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c252k7p0 : chartBlock (check252 7) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev252k7 : chartBlock (check252 7) 0 1 = true :=
  c252k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded252 : Impossible true (graphGoal 252) 7 (vars 252).toFinset := by
  apply compactRoot (g := grid252) (t := tab252) (dom := compactDomains252) (perms := compactPerms252) pairs252 domains252 autos252
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
    · exact lev252k7
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound252 : Lower true (vars 252) (graphGoal 252) 8 :=
  plain_low (hints := 589718784) (by decide +kernel) excluded252

def grid254 : CompactGrid := (254, 8, samplesP254, samplesQ254)
def tab254 : CompactTable := (compactCount254, compactPath254, compactLive254, compactPoolIDs254, compactBucket254)
def check254 (k : Nat) := compactNode grid254 tab254 compactDomains254 compactPerms254 k
def sliceSpecs254 : List SliceSpec := [(2, 0, 252, 0, 0, 8, 8)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains254 : ∀ d ∈ compactDomains254, Slice true (vars 254) (graphGoal 254) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(252, 8)]) (specs := sliceSpecs254)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound252
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs254 : properPairs (graphGoal 254) (asRow samplesP254) (asRow samplesQ254) :=
  compactPairs (g := grid254) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos254 : ∀ p ∈ compactPerms254, autoOK (graphGoal 254) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c254k8p0 : chartBlock (check254 8) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev254k8 : chartBlock (check254 8) 0 1 = true :=
  c254k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded254 : Impossible true (graphGoal 254) 8 (vars 254).toFinset := by
  apply compactRoot (g := grid254) (t := tab254) (dom := compactDomains254) (perms := compactPerms254) pairs254 domains254 autos254
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
    · exact lev254k8
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound254 : Lower true (vars 254) (graphGoal 254) 9 :=
  plain_low (hints := 320234832) (by decide +kernel) excluded254

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound225 : Lower true (vars 225) (graphGoal 225) 4 :=
  carry_of (old := 225) (rep := 240) (swaps := [64, 117]) (by decide +kernel) bound240

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound209 : Lower true (vars 209) (graphGoal 209) 4 :=
  carry_of (old := 209) (rep := 240) (swaps := [80, 118]) (by decide +kernel) bound240

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound177 : Lower true (vars 177) (graphGoal 177) 4 :=
  carry_of (old := 177) (rep := 240) (swaps := [96, 84]) (by decide +kernel) bound240

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound113 : Lower true (vars 113) (graphGoal 113) 4 :=
  carry_of (old := 113) (rep := 240) (swaps := [112, 100]) (by decide +kernel) bound240

def grid241 : CompactGrid := (241, 6, samplesP241, samplesQ241)
def tab241 : CompactTable := (compactCount241, compactPath241, compactLive241, compactPoolIDs241, compactBucket241)
def check241 (k : Nat) := compactNode grid241 tab241 compactDomains241 compactPerms241 k
def sliceSpecs241 : List SliceSpec := [(1, 0, 240, 0, 0, 4, 4), (16, 0, 225, 0, 0, 4, 4), (32, 0, 209, 0, 0, 4, 4), (64, 0, 177, 0, 0, 4, 4), (128, 0, 113, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains241 : ∀ d ∈ compactDomains241, Slice true (vars 241) (graphGoal 241) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(240, 4), (225, 4), (209, 4), (177, 4), (113, 4)]) (specs := sliceSpecs241)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact bound240
    · exact bound225
    · exact bound209
    · exact bound177
    · exact bound113
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs241 : properPairs (graphGoal 241) (asRow samplesP241) (asRow samplesQ241) :=
  compactPairs (g := grid241) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos241 : ∀ p ∈ compactPerms241, autoOK (graphGoal 241) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c241k4p0 : chartBlock (check241 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev241k4 : chartBlock (check241 4) 0 1 = true :=
  c241k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c241k5p0 : chartBlock (check241 5) 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev241k5 : chartBlock (check241 5) 0 2 = true :=
  c241k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c241k6p0 : chartBlock (check241 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev241k6 : chartBlock (check241 6) 0 1 = true :=
  c241k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded241 : Impossible true (graphGoal 241) 6 (vars 241).toFinset := by
  apply compactRoot (g := grid241) (t := tab241) (dom := compactDomains241) (perms := compactPerms241) pairs241 domains241 autos241
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev241k4
    · exact lev241k5
    · exact lev241k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound241 : Lower true (vars 241) (graphGoal 241) 7 :=
  plain_low (hints := 1074135045) (by decide +kernel) excluded241

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound229 : Lower true (vars 229) (graphGoal 229) 7 :=
  carry_of (old := 229) (rep := 244) (swaps := [64, 117]) (by decide +kernel) bound244

def grid181 : CompactGrid := (181, 5, samplesP181, samplesQ181)
def tab181 : CompactTable := (compactCount181, compactPath181, compactLive181, compactPoolIDs181, compactBucket181)
def check181 (k : Nat) := compactNode grid181 tab181 compactDomains181 compactPerms181 k
def sliceSpecs181 : List SliceSpec := [(1, 0, 180, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains181 : ∀ d ∈ compactDomains181, Slice true (vars 181) (graphGoal 181) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(180, 5)]) (specs := sliceSpecs181)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound180
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs181 : properPairs (graphGoal 181) (asRow samplesP181) (asRow samplesQ181) :=
  compactPairs (g := grid181) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos181 : ∀ p ∈ compactPerms181, autoOK (graphGoal 181) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c181k5p0 : chartBlock (check181 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev181k5 : chartBlock (check181 5) 0 1 = true :=
  c181k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded181 : Impossible true (graphGoal 181) 5 (vars 181).toFinset := by
  apply compactRoot (g := grid181) (t := tab181) (dom := compactDomains181) (perms := compactPerms181) pairs181 domains181 autos181
  · intro k hk
    change k ≤ 5 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev181k5
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound181 : Lower true (vars 181) (graphGoal 181) 6 :=
  plain_low (hints := 537330949) (by decide +kernel) excluded181

def grid213 : CompactGrid := (213, 4, samplesP213, samplesQ213)
def tab213 : CompactTable := (compactCount213, compactPath213, compactLive213, compactPoolIDs213, compactBucket213)
def check213 (k : Nat) := compactNode grid213 tab213 compactDomains213 compactPerms213 k
def sliceSpecs213 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains213 : ∀ d ∈ compactDomains213, Slice true (vars 213) (graphGoal 213) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs213)
  · simp
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs213 : properPairs (graphGoal 213) (asRow samplesP213) (asRow samplesQ213) :=
  compactPairs (g := grid213) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos213 : ∀ p ∈ compactPerms213, autoOK (graphGoal 213) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c213k4p0 : chartBlock (check213 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev213k4 : chartBlock (check213 4) 0 1 = true :=
  c213k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded213 : Impossible true (graphGoal 213) 4 (vars 213).toFinset := by
  apply compactRoot (g := grid213) (t := tab213) (dom := compactDomains213) (perms := compactPerms213) pairs213 domains213 autos213
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev213k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound213 : Lower true (vars 213) (graphGoal 213) 5 :=
  plain_low (hints := 537265926) (by decide +kernel) excluded213

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound117 : Lower true (vars 117) (graphGoal 117) 5 :=
  carry_of (old := 117) (rep := 213) (swaps := [64, 117]) (by decide +kernel) bound213

def grid245 : CompactGrid := (245, 8, samplesP245, samplesQ245)
def tab245 : CompactTable := (compactCount245, compactPath245, compactLive245, compactPoolIDs245, compactBucket245)
def check245 (k : Nat) := compactNode grid245 tab245 compactDomains245 compactPerms245 k
def sliceSpecs245 : List SliceSpec := [(1, 0, 244, 0, 0, 7, 7), (4, 0, 241, 0, 0, 7, 7), (16, 0, 229, 0, 0, 7, 7), (64, 0, 181, 0, 0, 6, 6), (0, 64, 164, 17, 983055, 6, 4), (32, 0, 213, 0, 0, 5, 5), (128, 0, 117, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains245 : ∀ d ∈ compactDomains245, Slice true (vars 245) (graphGoal 245) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(244, 7), (241, 7), (229, 7), (181, 6), (164, 4), (213, 5), (117, 5)]) (specs := sliceSpecs245)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound244
    · exact bound241
    · exact bound229
    · exact bound181
    · exact bound164
    · exact bound213
    · exact bound117
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs245 : properPairs (graphGoal 245) (asRow samplesP245) (asRow samplesQ245) :=
  compactPairs (g := grid245) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos245 : ∀ p ∈ compactPerms245, autoOK (graphGoal 245) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c245k5p0 : chartBlock (check245 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev245k5 : chartBlock (check245 5) 0 1 = true :=
  c245k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c245k6p0 : chartBlock (check245 6) 0 5 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev245k6 : chartBlock (check245 6) 0 5 = true :=
  c245k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c245k7p0 : chartBlock (check245 7) 0 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev245k7 : chartBlock (check245 7) 0 3 = true :=
  c245k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c245k8p0 : chartBlock (check245 8) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev245k8 : chartBlock (check245 8) 0 1 = true :=
  c245k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded245 : Impossible true (graphGoal 245) 8 (vars 245).toFinset := by
  apply compactRoot (g := grid245) (t := tab245) (dom := compactDomains245) (perms := compactPerms245) pairs245 domains245 autos245
  · intro k hk
    change k ≤ 8 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev245k5
    · exact lev245k6
    · exact lev245k7
    · exact lev245k8
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound245 : Lower true (vars 245) (graphGoal 245) 9 :=
  plain_low (hints := 537265413) (by decide +kernel) excluded245

def grid253 : CompactGrid := (253, 8, samplesP253, samplesQ253)
def tab253 : CompactTable := (compactCount253, compactPath253, compactLive253, compactPoolIDs253, compactBucket253)
def check253 (k : Nat) := compactNode grid253 tab253 compactDomains253 compactPerms253 k
def sliceSpecs253 : List SliceSpec := [(8, 0, 245, 0, 0, 9, 9)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains253 : ∀ d ∈ compactDomains253, Slice true (vars 253) (graphGoal 253) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(245, 9)]) (specs := sliceSpecs253)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound245
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs253 : properPairs (graphGoal 253) (asRow samplesP253) (asRow samplesQ253) :=
  compactPairs (g := grid253) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos253 : ∀ p ∈ compactPerms253, autoOK (graphGoal 253) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c253k8p0 : chartBlock (check253 8) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev253k8 : chartBlock (check253 8) 0 1 = true :=
  c253k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded253 : Impossible true (graphGoal 253) 8 (vars 253).toFinset := by
  apply compactRoot (g := grid253) (t := tab253) (dom := compactDomains253) (perms := compactPerms253) pairs253 domains253 autos253
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
    · exact lev253k8
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound253 : Lower true (vars 253) (graphGoal 253) 9 :=
  plain_low (hints := 537289989) (by decide +kernel) excluded253

def grid255 : CompactGrid := (255, 10, samplesP255, samplesQ255)
def tab255 : CompactTable := (compactCount255, compactPath255, compactLive255, compactPoolIDs255, compactBucket255)
def check255 (k : Nat) := compactNode grid255 tab255 compactDomains255 compactPerms255 k
def sliceSpecs255 : List SliceSpec := [(1, 0, 254, 0, 0, 9, 9), (2, 0, 253, 0, 0, 9, 9), (10, 0, 245, 0, 0, 9, 9)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains255 : ∀ d ∈ compactDomains255, Slice true (vars 255) (graphGoal 255) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(254, 9), (253, 9), (245, 9)]) (specs := sliceSpecs255)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact bound254
    · exact bound253
    · exact bound245
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs255 : properPairs (graphGoal 255) (asRow samplesP255) (asRow samplesQ255) :=
  compactPairs (g := grid255) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos255 : ∀ p ∈ compactPerms255, autoOK (graphGoal 255) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c255k10p0 : chartBlock (check255 10) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev255k10 : chartBlock (check255 10) 0 1 = true :=
  c255k10p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded255 : Impossible true (graphGoal 255) 10 (vars 255).toFinset := by
  apply compactRoot (g := grid255) (t := tab255) (dom := compactDomains255) (perms := compactPerms255) pairs255 domains255 autos255
  · intro k hk
    change k ≤ 10 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev255k10
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound255 : Lower true (vars 255) (graphGoal 255) 11 :=
  plain_low (hints := 268854613) (by decide +kernel) excluded255
def winningGates : List Gate := [⟨.and,[7,5]⟩, ⟨.or,[6,7]⟩, ⟨.or,[3,4]⟩, ⟨.and,[9,10]⟩, ⟨.or,[5,7]⟩, ⟨.or,[1,2]⟩, ⟨.and,[12,13]⟩, ⟨.or,[5,6]⟩, ⟨.and,[15,0]⟩, ⟨.or,[8,11]⟩, ⟨.or,[14,16]⟩, ⟨.or,[17,18]⟩]
theorem winningLegal : ∀ g ∈ winningGates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [winningGates,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem winningCorrect : ∀ x : Fin 8 → Bool, Circuit.eval ⟨winningGates,19⟩ (List.ofFn x) = edge8 x := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem asListed : ∀ x : Fin 8 → Bool, edge8 x = decide (∃ i < ([0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by decide +kernel
end PEqualNP.Outside.L_meta_14666

open PEqualNP.Outside.L_meta_14666 PEqualNP.CircuitLowerBounds
theorem PEqualNP.Outside.L_meta_14666 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _ correct
  by_cases hn : ∃ g ∈ gates, g.op = GateOp.not
  · obtain ⟨g,hg,op⟩ := hn
    have lt : gates.countP (fun q => !isNot q) < gates.length := by
      rcases Nat.lt_or_ge (gates.countP (fun q => !isNot q)) gates.length with h | h
      · exact h
      · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
        simp [isNot,op] at eq
    obtain ⟨k,hk,run⟩ := physicalSigned ⟨gates,o⟩ legal (fun x => (correct x).trans (asListed x).symm)
    change k ≤ gates.countP (fun q => !isNot q) at hk
    have low : 10 < k := by
      by_contra! small
      apply excluded255 k small
      have same : graph = graphGoal 255 := by decide +kernel
      simpa only [←same, show vars 255 = eightInputs by rfl] using run
    exact ⟨winningGates,19,winningLegal,by change 12 ≤ gates.length; omega, fun x => (winningCorrect x).trans (asListed x)⟩
  · refine ⟨gates,o,?_,le_rfl,correct⟩
    intro g hg
    obtain ⟨op,arity⟩ := legal g hg
    exact ⟨op.imp_right (fun h => h.resolve_right (fun e => hn ⟨g,hg,e⟩)),arity⟩
