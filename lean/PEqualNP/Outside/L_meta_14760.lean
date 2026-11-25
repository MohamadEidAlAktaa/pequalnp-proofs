import PEqualNP.Defs





namespace PEqualNP.Outside.L_meta_14760
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
def graph : Sig := (BitVec.ofNat _ (limbs64 [0xfffffffefffffffe,0xfffffffefffffffc,0xfffefffefffefffe,0xfefefafaeeccaa00,0xfffffffefffffffe,0xfffffffefffffffc,0xfffefffefffefffe,0xfefefafaeeccaa00]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
 (x 0 && x 3) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7)
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
 (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7)
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
 (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7)
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
 (x 0 && x 3) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7)
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

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([3, 4, 5, 0, 1, 0, 0, 1] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([3, 4, 5, 0, 1, 0, 0, 1] : List Nat).getD i.val 0))

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

def samplesP172 : Nat → Bits
  | 2 => 0xdffdeb7e7f71d9fc
  | 3 => ~~~(0x44218b442871d13c : Bits)
  | 5 => 0xf3e3f33dfcf10f4c
  | 7 => ~~~(0x100063005471084c : Bits)
  | _ => 0

def samplesQ172 : Nat → Bits
  | 2 => 0x20a0140a0c013894
  | 3 => 0x46289a2912253cc2
  | 5 => 0xc4ca0f440b64748
  | 7 => ~~~(0xeefbdeef5eedbcde : Bits)
  | _ => 0

def compactPerms172 : Array (List Nat) := ([[], [83, 114]] : List (List Nat)).toArray

def compactDomains172 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray

def compactWords172 : Nat → Nat
  | 0 => 0xf
  | _ => 0

def compactCount172 (k : Nat) : Nat := match k with
  | 3 => 1
  | _ => 0

def compactPath172 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => 0
  | _ => 0

def compactLive172 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => readCompactBits compactWords172 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs172 (k : Nat) (i : Nat) : List Nat := match k with
  | 3 => let v := readCompactBits compactWords172 (4 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords172 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket172 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP173 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x5e7ffeeef9,0x276c7e5ffecf87f8,0x6c7ce1c97fce924f,0xbf34701f45be624c]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x7adfbd7f32,0x7ed37ffb97fc7a7b,0x9705ca349f7f63f1,0x79e781e01b547db0]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x8303040b2,0x622b000106730239,0xc405cbf4884842d1,0xaa33c1ee1f3613f0])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0x6faffff1fe,0xd82a7fe57ff309bd,0xef8f01f469ffdff0,0xc63bc12e056b9670]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x2c00c2078,0x1c4e0240108c09f8,0x2f0c21fd01069360,0x5527f13f4548667c])) : Bits)
  | _ => 0

def samplesQ173 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x218100b104,0x4812d2020a100c42,0x7489120412ca1202,0x21104030d7962044]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x52082c188,0x8108b06080708e00,0x580e2440060f2050,0x480441216b446890]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x834124422,0x229291040a5a210,0x8826092045258828,0x1081150528494c0a]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x1058140601,0x24850c0511053098,0x8130400ae9304100,0x8429964600299620]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x7d3dfbcdaf,0xefb9bb77dbffef35,0xda6ebf6ec72ffb7a,0xfdbf7dad6b4d6efe])) : Bits)
  | _ => 0

def compactPerms173 : Array (List Nat) := ([[], [114, 83], [32, 115], [32, 50, 83, 117], [48, 117], [48, 82, 115, 117], [80, 50], [80, 114, 83, 117], [112, 114, 115, 117], [112, 82]] : List (List Nat)).toArray

def compactDomains173 : Array (Sig × Nat) := ([(subcube 1 0, 4), (subcube 4 0, 4), (subcube 8 0, 4), (subcube 32 0, 4), (subcube 128 0, 4)] : List (Sig × Nat)).toArray

def compactWords173 : Nat → Nat
  | 0 => (limbs64 [0x6b,0xb0aa66c754ff87f8,0x4e17f8115f28d006,0x9069335492c97dd,0xfe0f682fc7fc1fe0,0xd717f8024d7a4206,0xfffd00900688d11f])
  | _ => 0

def compactCount173 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 2
  | 4 => 1
  | _ => 0

def compactPath173 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords173 (26 + 12*i) 12
  | 4 => let v := readCompactBits compactWords173 (270 + 12*i) 12
    (readCompactBits compactWords173 (258 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def compactLive173 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords173 (0 + 5*i) 5
  | 5 => readCompactBits compactWords173 (50 + 6*i) 6
  | 4 => readCompactBits compactWords173 (282 + 7*i) 7
  | _ => 0

def compactPoolIDs173 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords173 (20 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords173 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits compactWords173 (64 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords173 (62 + 2*(v &&& 1)) (2*n)
    compactIDsFromBits bits 2 n
  | 4 => let v := readCompactBits compactWords173 (289 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords173 (289 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket173 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords173 (68 + 2*(i % 4)) 2
    let off := ((i/4 + d) % 14)
    let v := readCompactBits compactWords173 (76 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 4 => let d := readCompactBits compactWords173 (291 + 2*(i % 2)) 2
    let off := ((i/2 + d) % 8)
    let v := readCompactBits compactWords173 (295 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | _ => []

def samplesP73 : Nat → Bits
  | 0 => ~~~(0x110a : Bits)
  | 3 => ~~~(0x2070 : Bits)
  | 6 => 0xbf7a
  | _ => 0

def samplesQ73 : Nat → Bits
  | 0 => ~~~(0xebde : Bits)
  | 3 => 0x280c
  | 6 => 0x4212
  | _ => 0

def compactPerms73 : Array (List Nat) := ([[], [99], [48], [48, 99], [96, 99], [96]] : List (List Nat)).toArray

def compactDomains73 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray

def compactWords73 : Nat → Nat
  | 0 => 0x7
  | _ => 0

def compactCount73 (k : Nat) : Nat := match k with
  | 3 => 1
  | _ => 0

def compactPath73 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => 0
  | _ => 0

def compactLive73 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => readCompactBits compactWords73 (0 + 3*i) 3
  | _ => 0

def compactPoolIDs73 (k : Nat) (i : Nat) : List Nat := match k with
  | 3 => let v := readCompactBits compactWords73 (3 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords73 (3 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket73 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP201 : Nat → Bits
  | 0 => 0x6dfee99fceeca7d4
  | 3 => ~~~(0x4040182806823c0 : Bits)
  | 6 => 0x76f771eff9792be8
  | 7 => ~~~(0x230269f1483da0fc : Bits)
  | _ => 0

def samplesQ201 : Nat → Bits
  | 0 => 0x1220542a40a0c684
  | 3 => 0x480010124000032
  | 6 => 0x9182a0489091948
  | 7 => ~~~(0x5cb78f23ed9620fe : Bits)
  | _ => 0

def compactPerms201 : Array (List Nat) := ([[], [96]] : List (List Nat)).toArray

def compactDomains201 : Array (Sig × Nat) := ([(subcube 128 0, 4)] : List (Sig × Nat)).toArray

def compactWords201 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def compactCount201 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath201 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive201 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords201 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs201 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords201 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords201 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket201 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP233 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xef7ff7fedd5f,0x9d5ffde7bff9fdf0,0xaf754fd8b9fceb3c,0xb9deb383d79d4fd4]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x410000184019,0x8c0c0c800138e450,0x704fd0004c4a18,0x80dab201d7944fc0])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0xf4aff8bfce98,0xe403ffffe53e9e38,0xd0780cc03f5ffdc0,0xc0ffc001c6d7f300]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xf9cfbf5f3079,0x7a8fffde5bcee1cf,0x22f6433666ffd63f,0xa6b93e4411f28ce8]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x20f030069c58,0x77dc1146000e99a8,0xa2754ffec010b524,0xa0bd1fc7d71383fc])) : Bits)
  | _ => 0

def samplesQ233 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x108828000220,0x2080444022080000,0x9202800201840304,0x180900222084984]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x410102080010,0x880a011110100082,0x4200a00101220a2,0x1001049080032032]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xb5203ca2543,0x136f922205522ce3,0x65b050797c5b8c08,0xc26c44d8c5d7b200]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x63410e04cc6,0x470a08644c18478,0x608d30d06628dc18,0x661802440df08448]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0xdf0f46dd6bb5,0xb86a97f573b457e6,0x6ce1eaab141ab3b6,0xb5f5cdf19513a3fe])) : Bits)
  | _ => 0

def compactPerms233 : Array (List Nat) := ([[], [117, 48]] : List (List Nat)).toArray

def compactDomains233 : Array (Sig × Nat) := ([(subcube 32 0, 5)] : List (Sig × Nat)).toArray

def compactWords233 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount233 (k : Nat) : Nat := match k with
  | 5 => 1
  | _ => 0

def compactPath233 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => 0
  | _ => 0

def compactLive233 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => readCompactBits compactWords233 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs233 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let v := readCompactBits compactWords233 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords233 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket233 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP205 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xdcfefbe,0x7c2de8bfcf3ff567,0xaa1fcc0e13ff2e6f,0x6393ac24c06bb350]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x6408a0,0x668c2dc0000ea865,0x91e9ecf98602fca,0xc001ef65f0a033fa])) : Bits)
  | 3 => (BitVec.ofNat _ (limbs64 [0xf7bfdef,0xa69f55fe7ffea974,0x7dd6bec19be3dbca,0xd17e4b65b0a5c0fa]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x1080408,0x802dd0c003300176,0xa4d10ff01380100a,0x639e0aa5bf2bcc5a])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0xbe7fef9,0xc3ecb07db3ffcaff,0x85f913f003fcf59a,0xee8d02813fba7c0a]))
  | _ => 0

def samplesQ205 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x2309025,0x24217644022620c,0x344c522086d52220,0x42108423896aa210]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x6450b0,0x44880955089038ce,0x104a088209879004,0x8c20516a547c404]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x860090,0x11202812220818c2,0x2010841028908,0x11080114240540c8]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0xef7dbfd,0x7ffb3f777bbf7bdf,0x3f7f7bafffd7bbbe,0x7bdfdfb7ed6feede])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x4190407,0x281106a811050620,0xe484d00532784092,0x2005a0691ab83802]))
  | _ => 0

def compactPerms205 : Array (List Nat) := ([[], [114, 99]] : List (List Nat)).toArray

def compactDomains205 : Array (Sig × Nat) := ([(subcube 4 0, 5)] : List (Sig × Nat)).toArray

def compactWords205 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount205 (k : Nat) : Nat := match k with
  | 5 => 1
  | _ => 0

def compactPath205 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => 0
  | _ => 0

def compactLive205 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => readCompactBits compactWords205 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs205 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let v := readCompactBits compactWords205 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords205 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket205 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP236 : Nat → Bits
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x100040228c20,0x90800832004c0675,0x38391854818aa1c,0x30448cf28ca5c05a])) : Bits)
  | 3 => (BitVec.ofNat _ (limbs64 [0xdf7fdff3cebf,0x90bffdfb3e6f8e7d,0x1be39185edfbba5d,0x38df8cf28cafcc5a]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xfa3ff8be1ccc,0xe23f9e3fff8c77c3,0x9d800618fffcefe5,0xc0e4f10400cdf4a0]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x430010915cce,0x3c1940023838589,0x1d87e69a01a05a65,0xc083f1754f08dfaa])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0xf5be77fdfd62,0x1fffff6e1d385bd,0x6797e082dbbf5a3e,0xf70380714ff0db0a]))
  | _ => 0

def samplesQ236 : Nat → Bits
  | 2 => (BitVec.ofNat _ (limbs64 [0x100460020820,0x20110091500202,0x102000400621400,0x849000062a0a0924]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x209062041100,0x4929402101512292,0x124044021720811,0x80624262a0e8c48]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x5e083c4e207,0x1dce0e482625b095,0x2e38b88bf59c60c4,0x5160b5b840c5f480]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0xbcfdf72ebbb2,0xfd2dfb3db15ff7b6,0x79661fe621fe5e7b,0x8cf7fe776a0edfee])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0xa4889104095,0xb614a4540484984c,0xa888a3298a8d22ae,0x51011010d5f05202]))
  | _ => 0

def compactPerms236 : Array (List Nat) := ([[], [118]] : List (List Nat)).toArray

def compactDomains236 : Array (Sig × Nat) := ([(subcube 64 0, 4)] : List (Sig × Nat)).toArray

def compactWords236 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount236 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath236 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive236 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords236 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs236 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords236 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords236 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket236 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP237 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x7b9ffef7,0xfbfd5f39b7cb1ced,0x77ffdf3e7fffbe3f,0xafb9ff44fbdc8723,0xdcf4e0571afa1da4,0x42dcffff3e9fe63d,0x8cf9fb8f7cb8d339,0x823efbba8871183f,0x7a7a190cfb10086e,0xcbc97fe9e2942e4d,0x8b9867669b133800,0x9e626972ac669650]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x10440002,0xa08199430589563,0x44028000040fa476,0xc038264098020788,0xde8aa8941a938de5,0x4ee0304a0000c28c,0xf48a50d4428a03f,0x822af07b96e510be,0xdf509ddcff1b0ccd,0x441618ec3b6ac77,0x9706b070d1f3f94,0x9efa6cd33706977a])) : Bits)
  | 3 => (BitVec.ofNat _ (limbs64 [0x5f7bffff,0x3ef7e9bc7d7eebc2,0x4ffeb3ffff7ee5fe,0xc33db0ffdfe3e29c,0x5e8aba8aff459a45,0x4e3ffdfaebf1b9f9,0xffcda74dd36ca387,0xec21ac7717a595b6,0xc5559cd0041b0cdd,0xaf67a337af2ea173,0x2974185de60c3794,0x82d804957369017a]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x7d6cff1b,0xffde9fc6f9945132,0x63ffffffce8fbfc3,0xf3de3f871c1f3fc3,0x1f1f031c6083e182,0x801ff65fffe1c7ce,0xf7efff39fc7043e,0x7c0f3c3f07e1fc0,0x7f80000c3864307f,0x75fecbbed3e7d38e,0x34007b871ce24021,0x1c024f4737919880]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x10b0011,0x978028b19f4aa0,0x740001064a021808,0x839c390507412717,0x1f9f430b7b6a1386,0xe720c4000ae10141,0x8491a38398870731,0xec34bbc6e1749df2,0x65a21eff3875390c,0xcb4e0a3002ce838a,0x3d183466fee273ab,0x9edfd116af79f8da])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x77c6fdff,0xcf8bb0ffb2f98621,0x93fbedc7ffff587c,0xdcfe6f79a7637d1c,0xa38b4da11b3a0600,0x2533ffefdf6e5bc7,0xf793a5bfecbb2c71,0xf83e104ce7c4e0fa,0x85a2c6f30001017d,0xde5f7cde5cda8cb2,0x5d7ba4226d00038a,0x9d9e9a8f1e600a]))
  | _ => 0

def samplesQ237 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x4600508,0x24220820814a112,0x4a42004101c242,0x1002200684806040,0x201082804008203,0x18248c2904802200,0x8a0010240108c08,0x14204c0400608a8c,0x4088842000060200,0x82c9186820140240,0x8010440088120801,0x81c451308c241410]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x10448008,0xb00110420509023,0x28082108416003,0x40522842a0002480,0x9008808010800120,0x82e452004090120,0x400140200a02e441,0x1430440100489208,0x6440108022000400,0xa808a7128090008,0x1202103002020831,0x4351112448682084]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x20841040,0x4908044082001429,0x9220108420082811,0x40508a5021080802,0x140041100024530,0x208a611088501009,0x200804810026151,0x2090011122081010,0x2c41020880408008,0x290483150a022020,0x2804004140441130,0x4a11000562490148]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x2932074,0x50054019042b0e4c,0x9f84210806900894,0x85a0d219496c082c,0x24847042231c085c,0x65d03254eb0284c2,0x141c0a0184cc0192,0x28c2319a22952153,0x8a0361110d9111ff,0x7126418690e01506,0x420a984146455c2,0xc022e4333918800]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x7ef4bdea,0xffeb3fd7ef76b57f,0x9b6f7be77dcffbf7,0x5f57ae7ebfde7eeb,0xf3e9debf95d3ef7f,0x38eeff39cef9ffab,0xcfb7e3eefe12ef7f,0x7dfaeff56ee8ffbe,0x7eef97ace6ffcf0c,0xebcfdb7f3a5fa3fc,0xfb1e7cf7fffebbbb,0xdff55137ef7dfdde])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x8390b21,0x10644a08410661d4,0x6d51004a121486cc,0x3508018c0cc5c205,0x44242244a24d20cf,0x92519a8b52224840,0x910a288520c9180a,0x8a47288491a22986,0x39aa015492858f4,0xc45b740a54a09492,0x4528810221310086,0xa48cce9a85164002]))
  | _ => 0

def compactPerms237 : Array (List Nat) := ([[], [117, 48]] : List (List Nat)).toArray

def compactDomains237 : Array (Sig × Nat) := ([(subcube 64 0, 7), (subcube 4 0, 6), (subcube 32 0, 6), (subcube 128 0, 6), (subcube 1 0, 5), (subcube 8 0, 5), (subcube 36 0, 5), (subcube 132 0, 5), (subcube 160 0, 5), (subcube 40 0, 4), (subcube 65 0, 4), (subcube 129 0, 4)] : List (Sig × Nat)).toArray

def compactWords237 : Nat → Nat
  | 0 => (limbs64 [0xff3fcf,0xf3fc373fcd56c303,0x68dc139138d08800,0x90042b07e48e8a47,0xfc15420182b7fc37,0x1515ffc3fc3fc286,0xffc3fc3fc3fc3fc3,0xfc3fc3fc19cfe600,0x140008fd7add76fc,0x4be6ee7289ca2720,0x9c621159c9671a61,0x200a60c01001200b,0x9e1259ca4ffe032e,0x9fe0518ffe06cc63,0xc33a2bfe01365fe0,0x260a8afa6a3fe07f,0x803969ede778bf2f,0xc0c186b06cde1b7c,0x1c79d6280c525f57,0x49ffe0319854241d,0x7fe063bc3b77f80d,0xeeff8125064a7fe0,0x3ec3fe07f80812af,0x376d27f806b67c05,0xa2525174b447a4f2,0x4d38339138993b82,0x51d90290372e5db1,0x62cd4a956850a14e,0x3b872d58315aa539,0x92a4478241030852,0x841449249010a43d,0xa1010410c00af6fe,0xffdefefefeffefee,0xfefefebedefef67f,0xfaffdedff7fbfafe,0xffa60f4c0c984d10,0xde6144c589831301,0x621a4435986930d6,0x6084c40986130426,0xd4c5b0055308e61,0x9cc3284460088011,0xcc22985887807803,0x48068048020052,0x8aff0352ffc0b109,0x438883fc066db77b,0xa322ca3d1e24ff83,0xfc1fe0ff05209fd1,0x3833e77906021a03,0x3a9632a1d0b9a922,0xe2a8004263282463,0x486a8c6321418228,0xb611820ce29810a2,0xe19580cae202bb60,0xa7982a13b60fffff,0xfffffffffffc4344,0x3c03403802402002,0xc01401e21d8c843f])
  | _ => 0

def compactCount237 (k : Nat) : Nat := match k with
  | 8 => 1
  | 7 => 9
  | 6 => 27
  | 5 => 7
  | 4 => 2
  | _ => 0

def compactPath237 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => 0
  | 7 => readCompactBits compactWords237 (40 + 12*i) 12
  | 6 => let v := readCompactBits compactWords237 (997 + 15*i) 15
    (readCompactBits compactWords237 (901 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 5 => let v := readCompactBits compactWords237 (2955 + 14*i) 14
    (readCompactBits compactWords237 (2883 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 4 => let v := readCompactBits compactWords237 (3478 + 12*i) 12
    (readCompactBits compactWords237 (3442 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | _ => 0

def compactLive237 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => readCompactBits compactWords237 (0 + 6*i) 6
  | 7 => readCompactBits compactWords237 (148 + 7*i) 7
  | 6 => readCompactBits compactWords237 (1402 + 8*i) 8
  | 5 => readCompactBits compactWords237 (3053 + 9*i) 9
  | 4 => readCompactBits compactWords237 (3502 + 10*i) 10
  | _ => 0

def compactPoolIDs237 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let v := readCompactBits compactWords237 (34 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords237 (6 + 4*(v &&& 7)) (4*n)
    compactIDsFromBits bits 4 n
  | 7 => let v := readCompactBits compactWords237 (491 + 11*i) 11
    let n := v >>> 7
    let bits := readCompactBits compactWords237 (211 + 4*(v &&& 127)) (4*n)
    compactIDsFromBits bits 4 n
  | 6 => let v := readCompactBits compactWords237 (1762 + 7*i) 7
    let n := v >>> 5
    let bits := readCompactBits compactWords237 (1618 + 6*(v &&& 31)) (6*n)
    compactIDsFromBits bits 6 n
  | 5 => let v := readCompactBits compactWords237 (3116 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords237 (3116 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | 4 => let v := readCompactBits compactWords237 (3522 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords237 (3522 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket237 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let d := readCompactBits compactWords237 (590 + 2*(i % 6)) 2
    let off := ((i/6 + d) % 23)
    let v := readCompactBits compactWords237 (602 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 6 => let d := readCompactBits compactWords237 (1951 + 4*(i % 16)) 4
    let off := ((i/16 + d) % 62)
    let v := readCompactBits compactWords237 (2015 + 14*off) 14
    if v >>> 6 == (i/104729)%251 then [v &&& 63] else []
  | 5 => let d := readCompactBits compactWords237 (3130 + 3*(i % 4)) 3
    let off := ((i/4 + d) % 25)
    let v := readCompactBits compactWords237 (3142 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | 4 => let d := readCompactBits compactWords237 (3526 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 8)
    let v := readCompactBits compactWords237 (3528 + 10*off) 10
    if v >>> 2 == (i/104729)%251 then [v &&& 3] else []
  | _ => []

def samplesP253 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xb57ffb1e831ea5ab,0xfa13b712fadcd4dc,0x1547de655b4c773f,0x82655ac178feb5dc,0x70aa04c7e1fda524,0x10519726eee81dad,0x34811da64171501d,0x392b5df5298682e3,0x606bb9082001a40,0xa3a4fa7655d3c6d1,0x757898ace7a8fdf6,0x82b4bc68d6883171,0x80bdd46530f04371,0x849e25c079428c11,0x7000a3b344505383,0xd716a54b18c64c50]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xdf7f5ff3acb7edd4,0x5fec4597e16bef20,0xd5cccf5ba536a189,0x179ea7f290dd576f,0x8bc73788fe000843,0xe08e628d31198f20,0x5b78e007c214ade3,0xc291848261abf50c,0x319844007cb0e50e,0x3d7cf5ab8930f7d,0xb66766f3baaad0db,0x183947b7082244be,0x10c0eb935002fc89,0xd07bd8d691bc000e,0x80cd4c48098c96b6,0xe2e2441da3219085]))
  | 3 => (BitVec.ofNat _ (limbs64 [0xefe3b763cf6bd2e9,0x8e7458af8c74efef,0x1bf870fd9e89d8f1,0xe9e0e921ef1a5eb2,0x56b06812e4107397,0xb0e01c1145a94017,0xa29202d81ea31c10,0xfdce3b08be557870,0xc860036303430251,0x8b7a67fd9f4e3399,0x4ede07599d4b16a7,0x695ea5d9e16c9a04,0xe50301ecacdd304e,0x118e2ee83027440,0x6f1220263206eab8,0x92878ab6c20027a]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xb6efe5bd739d5a55,0xf59be851775c38d3,0xf4bfa1c4fcf357fe,0x7c75b73e77611cc3,0xa81dd12719ea24d8,0xf4188d890d6b24a,0xc96c1d79a1086202,0x3924a00116780200,0x1000c000c00a0,0x57dbfbfffa75facf,0xf38aff26b9df6aed,0xf4af6966c6512a89,0x7a4c3660c3ef8300,0x7a051939648103a0,0x2010008027fef3,0xb0458a464f5c2100]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x4f93fedffce000fe,0x13ffec7fa300df,0xea07ffba1fffa83f,0xff9a03ff807feb20,0x3f4001f801ffda00,0x1fbe6000ff001ff0,0x1ffe200017e801f,0xc6d001fec0000280,0x7843c001c301d00,0x1fff7a7efa9fd2e,0x88751fd741f47f07,0xff47d26f390fc43e,0xf2179a0300037e,0xfe03e007e3c0801,0x8040c3c004476d5f,0x547931b4806a5080]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x79bccdf85056bf3e,0x2fee8f6b9bb73b2b,0x2e301b3e61952f46,0x15fbfc0c7fa2e2ff,0xc432ce011e00d2e8,0x401fe5e30827608f,0x3c02035f7c84f7e8,0x6207677080f7d03,0x62c0f0e142e01b,0x20ef3cfbe2ec89e2,0x39a7f10f5e558d58,0x67d1ff9027d275c0,0xef31e809dc22bca6,0x24e4c22900c0f01e,0x18920c194213a54d,0x8e8cda1053900e25]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xfadc3aec3fe97f03,0xf1ed32fc048bd734,0xebfb2483e26adec0,0xea0f5cdf8f85a91d,0xe14dba7c02070d3f,0xef201b7e0256e050,0xc605fca0becb0be4,0x5fca08d7f08c1c,0xf819000f008d00a4,0x5e3d9d8d753e7436,0xcf99e8f86637a338,0x9fea1a9018b58b43,0x1f0e08162f1d4c91,0xfb0305178e4103e0,0x72d1004b9a9196c,0x299307e0b49da10a]))
  | _ => 0

def samplesQ253 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x1440690a80000841,0x8a02821100000008,0x11430a0080100630,0x800002c06801004c,0xa0034e00028070,0x50c0104828291202,0x5204010101610a09,0x265510040220810,0x30040080003200aa,0x82808a1000524041,0x53810a802a82072,0x2a4042006880030,0x804cc00040d00021,0x800100c068018c00,0x1020e01e08481082,0xd306054118044810]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x804a4800a510a8c0,0xc320c08300086201,0x41034189100298,0x30a80050324d4005,0x932090c52802141,0x44c49a0008130400,0x4002481201440890,0x522041880c804044,0x9004209009144232,0xca82cb5810110215,0x2620440130a010d3,0x819058002220018,0x20c462b140461808,0xc00b805221100904,0x1054482a210c92a2,0xe220440d22008084]))
  | 3 => (BitVec.ofNat _ (limbs64 [0xc22110250f42c004,0x446010002864c003,0x489041001a00900a,0x61e06014161a0401,0xd12282132512108,0x82220e0010504101,0x852208808040410,0x80280a82a00220c,0x4a30101190cca00,0x91261cc94042318,0x4242024180421405,0x491221c940041208,0x640025ec010c3040,0x41180a0e000a2040,0x225009202326ca30,0x28688a24200248]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x362e813cc541c85c,0xe230b10964355041,0xc471c38cac12d35e,0x20a4a47c320b3407,0x3481a0f140b21ca9,0x1524c4e031e24682,0xb8304c93c40104cc,0x5505801324e05285,0x11e547a729945a22,0xabd2fbffb84580ce,0x708a7d26b95a6284,0x308f6823c2400a98,0x305474a843641142,0xe32d196b209315c7,0x48050c227feb3,0xb0448a464f482000]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x4901965410c0432c,0x93d2c232710e4,0x4014e4bc0063b143,0x1035258022ad22,0x5200909024490e80,0xa2022082878021e9,0x84c82028a8921026,0xc922e270218a583,0x8a90d6de2010905,0x57d34a7ef88bd22,0x80440b5241044f00,0xd5408247594106c4,0x232040a050003d6,0xbe42809120c2021,0xab8101c084136d5d,0x45930b0806a1000]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x219404c000841708,0x88210c92811960,0x200090ac00c72940,0x413142100002bb2,0x424944000c201004,0x110403582008048,0x24a10600661ad042,0x1102610804c15a1,0x48181c24a0000501,0x146d142362a808a0,0x1885a0040c118908,0x2400d812314165c0,0xa1300029c008582,0x6a4400100001092,0x888214005491254d,0xc80921041900421]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x890228000a80302,0x100c004402000430,0x208002240492000,0xa10180301800920,0xc048560208088214,0x2010201f0408b020,0x20d032002a8c221,0xc01804c0168900,0xa08880084402141,0x42d040041225400,0x8911809846058028,0x8260121011118443,0x302080224014080,0x1080040084448030,0x123348418c0014c,0x993012090950102]))
  | _ => 0

def compactPerms253 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains253 : Array (Sig × Nat) := ([(subcube 16 0, 9)] : List (Sig × Nat)).toArray

def compactWords253 : Nat → Nat
  | 0 => 0x27f
  | _ => 0

def compactCount253 (k : Nat) : Nat := match k with
  | 9 => 1
  | _ => 0

def compactPath253 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => 0
  | _ => 0

def compactLive253 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => readCompactBits compactWords253 (0 + 7*i) 7
  | _ => 0

def compactPoolIDs253 (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let v := readCompactBits compactWords253 (8 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords253 (7 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket253 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP217 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x7daff5ef98,0xf678dfddff3b9eb2,0xf8dd28e0d77bfb70,0xf5c5a462b0e6d594]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x900000a68,0x607080095009aba8,0x706000c561215e64,0x808d6349b26c9fa0])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x6e9fabfe6e,0xd9601ffff2ef6969,0x747ac0053fe7f6ac,0xa9be4309027f6e20]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x5f5ffe7b77,0x22f1bf2f7ff5af9f,0x976131ca5dbddf5f,0x4a8b3844b57999c8]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x490206016,0x9269e00422270c13,0x945929ead400b318,0x6982bc66b47341dc])) : Bits)
  | _ => 0

def samplesQ217 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x252485023,0x80532104302c111,0x10a3140311531810,0x8140640ac0c4c504]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x908000948,0x50848028812424,0x80000840a00810a,0x3020808006122052]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x1160cc8980,0x228ea70e8001a5b5,0xa98a41305ec1e080,0x8ecd80967f6200]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x20a104a400,0x550a4920103c10c0,0xa1486a0024ac4244,0x4a00094519291888]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x7b6bff8beb,0x7fdea7befbb1afbf,0xef9ecfb77ec1fbde,0xfbeedfb0b67f63de])) : Bits)
  | _ => 0

def compactPerms217 : Array (List Nat) := ([[], [96]] : List (List Nat)).toArray

def compactDomains217 : Array (Sig × Nat) := ([(subcube 16 0, 5), (subcube 0 16, 5), (subcube 1 0, 4), (subcube 64 0, 4), (subcube 128 16, 4)] : List (Sig × Nat)).toArray

def compactWords217 : Nat → Nat
  | 0 => (limbs64 [0x1dfff,0x7d3fdfe0af946803,0x427d2ff8917fe158,0x20aff02e28c7ffff,0xd00e00500682e21f])
  | _ => 0

def compactCount217 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 3
  | 4 => 1
  | _ => 0

def compactPath217 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords217 (26 + 12*i) 12
  | 4 => let v := readCompactBits compactWords217 (205 + 12*i) 12
    (readCompactBits compactWords217 (193 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def compactLive217 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords217 (0 + 5*i) 5
  | 5 => readCompactBits compactWords217 (62 + 6*i) 6
  | 4 => readCompactBits compactWords217 (217 + 7*i) 7
  | _ => 0

def compactPoolIDs217 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords217 (20 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords217 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits compactWords217 (88 + 5*i) 5
    let n := v >>> 3
    let bits := readCompactBits compactWords217 (80 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 4 => let v := readCompactBits compactWords217 (224 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords217 (224 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket217 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords217 (103 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 8)
    let v := readCompactBits compactWords217 (105 + 11*off) 11
    if v >>> 3 == (i/104729)%251 then [v &&& 7] else []
  | 4 => let d := readCompactBits compactWords217 (226 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 5)
    let v := readCompactBits compactWords217 (228 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | _ => []

def samplesP219 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xfd97fe9eff9a7fd,0x57a69d1433fbf7f7,0xf3ebfd9cfac7d6f8,0xa7b2d30376231f26,0xd93c200e1ff3fbfd,0x36fe17a72ff99ffd,0x283a263a1d96cf83,0x6d1a6ca3a1034402,0xa7debf26f7b77660,0xfaa3ca2951a22320,0x42c84f54db31844]))
  | 1 => (BitVec.ofNat _ (limbs64 [0xbfbbffff97fd9c7,0x6bab653b2bffcbbf,0xff7cc0f0fff878ff,0xfbef3c19863cee98,0x79c304b1aefff57f,0xc79ffdf7d30e19ff,0xcfe7c3c0f2187003,0xd1e587418e6c8119,0x1513dbf7bbc84381,0x3d0e0fbf9e001cc4,0xf9c12daf801ac518]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x904000086684d0,0x3ac1f8d20014112,0xa40a0deb008f0,0x34008645261dbe14,0xed7794bb80210055,0x84a89002374a08ef,0x272cea2e5cc86e03,0xe7c587418f6f919d,0xc156d0228d1be7c9,0xb90686ec4161bcc6,0xfbedb499593ffd98])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0xeecff57ffe6f5b6,0xb75896a687ffff7e,0x6efef26bc5b7aff4,0x775ca2d4699b8d55,0x64f09001bdefaffe,0xbd799b4efecf65e2,0x3719dba5cc492e60,0xa7da139d8c481084,0x6bff52cf6f7eab59,0xa24db47468418086,0xe30015127ecf2190]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xdf6fffe7ef75e78,0xdbcc3bc9cffdffdf,0xbf877faffe78fb17,0x7c23c4e68edcb08e,0x873f411a7fbd5eff,0xcea3e65a37f7fe41,0xd0ac683e0be7e37f,0xc6e58a424113a239,0xbb77edf88c3bf5be,0x4d5285c0a13c3c41,0x6cca18733c9e20]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x48804060015124,0x530ab5328c008204,0x2204f008e040f214,0x63223092ceba8d8e,0x51bb611fcc80002a,0x613074602851571,0xd8bb43b08b17e363,0xc5fa0a83ad5be63b,0xa3130bc4222e7330,0x6e4b8d31b8be3fe5,0xe56ccd36669a9f74])) : Bits)
  | _ => 0

def samplesQ219 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x26849250821802,0x5920e1cc9a0410,0x301382cc0440ad10,0xd861280400c0a048,0x200159d150b2634d,0x42100504018043,0x895b204e9915300,0xaa001ee050600025,0x254ab12647830020,0x8801402810620066,0x5b184d509931004]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x404600202a00428,0x84101a84c0504288,0x4012140d48120c40,0x480002a051000004,0x8408d0420a98a006,0x4014080003021084,0x2808000a8820129,0x204922e881003440,0x2899232c04180,0x3404081200080968,0x49808ca680100418]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x9050000a348010,0x2841b0c21402005,0x8405421689a0048,0x400404024140a10,0x26840a2a488820,0x2201418080a04014,0x2480810042220a9,0x16921088a020090,0x8810a9130601014,0x28021010c884988,0x48005922a4400242]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x113019888180240,0x4827414939a18820,0x8143a026c93029,0x8544450180205002,0x3032ea864460af8,0x120020a180c0132,0x494928960521e484,0xc92295040010c900,0xabb95245043c0a01,0x8804060c6c484,0x202451107eca2100]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x2090208a1002085,0x2022c41212240042,0x30c011003011221,0x2116101800010121,0x4840222485051490,0xc80845000400620,0x7120448312088404,0x54028006208c0000,0x5234444888102408,0x405204808004a401,0x22462208522c8820]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0xfb777ff8efebeff,0xeef75bcdf9f7eeff,0x7bd37faffeff7cef,0xcfccfffdf5f5fb7f,0xef6ffeea6edeaaff,0x6ff7dfdf9fefd7fe,0xcfcba9feade7edff,0xe9fff7fdbbfefdf5,0xebbbdbd736ff7fbd,0xfedfedfbfcdfdffc,0xf9acddb6fedabf7e])) : Bits)
  | _ => 0

def compactPerms219 : Array (List Nat) := ([[], [113, 99], [64, 49, 118], [64, 97, 115]] : List (List Nat)).toArray

def compactDomains219 : Array (Sig × Nat) := ([(subcube 2 0, 7), (subcube 8 0, 7), (subcube 64 0, 7), (subcube 128 0, 7), (subcube 1 0, 6), (subcube 0 1, 6)] : List (Sig × Nat)).toArray

def compactWords219 : Nat → Nat
  | 0 => 0x3076223f
  | _ => 0

def compactCount219 (k : Nat) : Nat := match k with
  | 8 => 1
  | _ => 0

def compactPath219 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => 0
  | _ => 0

def compactLive219 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => readCompactBits compactWords219 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs219 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let v := readCompactBits compactWords219 (24 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords219 (6 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | _ => []

def compactBucket219 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP251 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xfc8d7dff8499ffb3,0x8426067f9ff6403f,0x27f8b27a803c4fff,0x255a0afd7f480f10,0x7f7efdf6a09080b7,0xdeb049a901b50ab3,0xda1f0ebbf1574000,0x35974cb59156897d,0x41cf838c0bb00470,0xc404e0e66c590eb,0x49a27ee2997784bd,0x7b624f3f9b680319,0xc1a077e8a02e7f40,0x4a0c3c8341ea0863,0x820821396aa49045,0x9da538296b965844]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x5ff0bf9bffdfcffe,0x6ed33f8974dc31be,0xcc37cdc194ee25df,0xd881bdc914ff92bb,0xb227e7b9f31f1f8c,0x710300761840f54e,0x2326101edca00f13,0xba88dfca2a81bea2,0xd05c1270400386,0x31f8bdf90b81b89,0xfc9bcd9befaad6b2,0x2ec09b85e405dd00,0x7e21827507a028e3,0x79a3e119a3d0101c,0x3c14de4601100afb,0x331f914250d18518]))
  | 3 => (BitVec.ofNat _ (limbs64 [0xf31fcebef377b7f4,0x7a7febf21c5f96c0,0xfcc0f25fbf27fa10,0xf67d4306dd230ded,0xb8ff01c05e380d60,0x7a0db51e1e6206a5,0x308c67e0208bb06c,0x442d000fd57e5008,0xff20a061803f1878,0xf0600ff6df27ae1f,0x315cbd14f6a7f263,0x93592df03b9202ae,0xca0c1efe0bac3c,0x30b03b61ae09e903,0xc3e101008442e3da,0x65468e158c000267]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x3f6ef2dd78bebe5b,0xbba5d582ffa9a903,0x5affb22543fbb7e0,0x23bbf67ae29bf6ee,0x40c67c0900eb7233,0xa54256b6e08a0c49,0xc55099444e54ff90,0xa52ad4590291689,0x3ec818104400e005,0x9c33b5eff2d776,0x8bbd52f5614b797e,0x9f3cded65727e056,0x4d54938846ddd080,0xf54400fe90041680,0x3012d0c0100bec95,0xa02a63898d7c2190]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x9fff3f7bff7f77ed,0xd10b38746b23ce7d,0xb3377fbe68d1dddf,0xff65bfb694f46abb,0xcda19a460c04e047,0x8efca0c9e700fbb0,0x339e01ea3080f13,0x8560d2304401a154,0x801f000c01800000,0xc000fffffff73f5,0xf6dbad6ceed9298d,0xcdbf346df8d5dee0,0x302169820150571c,0x65bde1a5dc00020,0x820384223fffc,0x8ac85d76510a4000]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xebf3dd667fe1e85f,0x7fd8c67de219fffd,0x27cf4d957f084a24,0xdaa648f96bb7f544,0x7f592005df600898,0x1fba0001bdf140,0xbce30fa11c2eb0ec,0x7983236a6a8c4577,0x13043818a4f0788,0x43224de97dfaecc2,0xbe6443df107cffc5,0x649fe03b64ba2119,0xbede6437582402bf,0x820fc3640033e05c,0x4805000328c75f26,0x4a702682a2e11e20]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xe4ffe3e58fee59af,0x85fcf98f81e67fc2,0xd9080deaffd7b02b,0xddef507ab4cf957,0x8798d23a21c7f748,0x1e04f41fe5f001e,0x4cc0f04103f140ef,0xc27c30902ff26a82,0xfe2024623400f803,0xb081b47bbb5d6d3c,0x4767b22b1f940f5a,0xf0e7f3ca80483ce7,0x831f9841b9d38143,0x8df004847e240780,0x5e20e8495193528,0x5491c0fc362ca08b]))
  | _ => 0

def samplesQ251 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x881608204981013,0x402000202104002,0x1000340004,0x2020400000710,0x220c80108828,0x21500ca90008040c,0x9a3c010412860000,0xc14b02004248c0a,0x4020201200000000,0x4082000000009028,0x8a230c299008438,0x10024f0100280200,0xa01020000a0200,0x4800000340060800,0xa122145c1a00001,0x9425002868945004]))
  | 1 => (BitVec.ofNat _ (limbs64 [0xd90080ac20a0502,0x2850002014448228,0x4805190200008489,0x8000904110008081,0x3000489604092900,0x304008102004484,0x882a220804222421,0x111094c30840048a,0x50460200000a8150,0x9008894680000101,0x208a8882c420c290,0x6c00985a0049500,0xa00025400802808,0x30a2880005508009,0x1e8844444080025b,0x1306914040800418]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x22080c1063048780,0x883922a0240e9208,0x2851d14621428091,0x2408111248212040,0x1822011018014411,0x182402044c206080,0x4180228a08013629,0x9000084988500240,0x184a14088c120915,0x16088b56ca240410,0x31100c1066226203,0x35100d01900848a,0x48008e82110c28,0x1030aa28a448c109,0xa0c04410004aa2da,0x21428a1104000242]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x324062541094a811,0x92080190e8220044,0x10f8428003c81250,0x10994538000b7008,0x90615480a50d454,0xa840da4a242c1041,0x5381016458110104,0xa84083852201a11,0x419008184713886,0xc0442906fb09642,0xb145075014b382a,0x8908545247024006,0x4400a18206541404,0x805440fc000c3b24,0x20103001184be884,0xa02822898d582100]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x953e1749a94322e4,0xcb1850f12527875c,0x8a5b778a05419bd3,0x5128759806113828,0xdd8a88c335482345,0x162170444a412971,0x4388c3e4205298,0xc3214492c09b70e5,0xa1341a094976fb4,0x343d9fffffff23d5,0xd609852422990185,0xccb53024b153cc42,0x940468860b105d1d,0x147dd82c0cd050a0,0xd46c02181207fffc,0xac85d56110a0000]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xc04291241821484c,0x4200d41900202145,0x8708028154005a40,0x13244c8822941808,0x1d9840103a41080,0x8003810221061812,0x2000982121180184,0xeb420012096030,0x8501c0e071812480,0x2434a935d26882,0x8444430900441844,0x600c802a40d24051,0xb4142c0059201087,0x24c410400002244,0x400510820e155d24,0x4810248282610820]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x402580a104605028,0x4084580500800980,0x820000208c002820,0x960008083500806,0x2888200a0a402a8,0x41225200143012a,0x20541000838c4010,0x444a220004868004,0x8320482412800408,0x16014291049482c,0x4061220818940540,0x3022a20800502060,0x9107080129008041,0x1080400122200c0,0x23038a85301520,0x4491402432248081]))
  | _ => 0

def compactPerms251 : Array (List Nat) := ([[], [113, 99]] : List (List Nat)).toArray

def compactDomains251 : Array (Sig × Nat) := ([(subcube 32 0, 9)] : List (Sig × Nat)).toArray

def compactWords251 : Nat → Nat
  | 0 => 0x27f
  | _ => 0

def compactCount251 (k : Nat) : Nat := match k with
  | 9 => 1
  | _ => 0

def compactPath251 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => 0
  | _ => 0

def compactLive251 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => readCompactBits compactWords251 (0 + 7*i) 7
  | _ => 0

def compactPoolIDs251 (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let v := readCompactBits compactWords251 (8 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords251 (7 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket251 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP246 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0x7d7bfffb,0xbdfcf7af6c7fdcbe,0x33bb7ffbf9fff77f,0xbaebfc59fabf2edf,0xa27d5056f6a17f5f,0x9f83d160ed9fbff1,0xefd97d974bfe7d5b,0xf05f3f7f83bd7982,0x3de82e85dc0597fc,0x55c7c80a91c5bb3e,0x25f73d9ca9ec1fc3,0xc5a0f11f531402e6,0x3e2c4966eb5328cc]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x10050000,0x1902c18084540aa3,0x71940010080021a,0x10ab805ce005e800,0x7c5c126c217e15,0xc02bc16cedc01041,0x820b2011c1b8c053,0x801db0078bf011f0,0x3886e285fe0595f8,0x5c7cb8a91f9360c,0xa0c2c4b828fd174f,0x5c07b8e1c17c2e6,0x3f2e6d273a11eaec])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x5fcebfff,0x7fc7e2eddfce2b89,0xa4753fffc7bf9ffc,0xfe9f87fff3e3fb05,0x70f30f070d77e625,0x433dc00c88de7bff,0xdfbfa77be383f0bf,0x8e7bff8e3df0b2f0,0x4787e1e3f683c0c9,0x8046038001bf6e9b,0xee4efe7f3cf12b1d,0x10d8cf81bc87c040,0x390a3c8b718dc268]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x7b173f75,0xdffbcb5eb6716831,0xb023fe5ffdfebbf,0x45f7fa6666bcdd26,0xdd7ebc5104d97898,0x6c422402001ffcef,0xf7fefa14b7fdc267,0xffdcd7704242457d,0xba105779db0668f2,0x542014042807f7dd,0xf5bfcdeb76efd422,0xdb4002fe94680500,0x413f6b2eb24110]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x152c061,0x401c20f422a799d,0x3b27c000011c0125,0xe857802362ba1807,0x3bc4594dffe0a,0x4fd7c71ffcc02880,0x414a0060247402f,0x8042577877f06ff0,0x779657bde026af8,0x507fd785aff80a13,0x6505094817ed08b3,0xdbc08791f46fc561,0xff5fc0cb69f25f7c])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x77f57fef,0xff3fdd93c3bed3c7,0x5f0cffdf3ffc7fff,0xf97f81bfed5ff8fb,0xf88fca8f80e9e02,0xc0ffcb1d7459ffdf,0xbe7fa0efdc7fcfff,0x81a7f0e1fff00ff0,0x7fe01e2e783f38,0x2819c381867bfe67,0xfbc1c3f8c31d00ff,0x2fc73f806c03c021,0xc716e7951870de24]))
  | _ => 0

def samplesQ246 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0x2840284,0x302005003000201,0xc4041100a0101010,0x45a8002459010121,0x2828000040000,0x60200018006500d0,0x6010048001220002,0x4001044500422a80,0x2101284000220ad,0x2000124004000302,0x5200d8480880240,0x80a0000940100474,0x1d0060a942008c]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x10051000,0xb10808080500021,0x608091004024020,0x5a1202841094040,0x420081008011004,0x8001004840052298,0x104404002402800,0x9020005008402a4,0x2212088022a0a1,0x3105000000200803,0x824290680020880,0x1814001022211414,0x901c00c0c1c80412]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x20314420,0x881c0d006020d066,0xb8aec2009240e02,0x3045b408048e4050,0x85a07048228082d2,0x1420f416308732d,0x580031204094094,0x9060a90818a50535,0x51a2044ac4308402,0x14202c9380846811,0x8a4eb04b2c202111,0x4088a298a59880,0x9842388a508d4240]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x4e8c187,0xa0443405488657ca,0xf0d5f282580c848c,0x58480c86bc66212f,0xb290312a7092a761,0x78c53b49f7ad862,0xf652a908749c0125,0xb228233a8c526d02,0xca98c4a63408495e,0x8e8845ba0bcff3dc,0xe51b44e856656504,0x430112e6081c416a,0x42433f2b2e324100]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x7ead37ce,0xdbf6bbf1b7f5966b,0xc6dc3b35f57a5bf8,0xddfb6dbcdf3fc3e9,0xdcffcbf34f27159e,0xf2eb2bf8c3657afa,0xe55746d6bbf36afb,0x6943defd2dde2fec,0xeefe97bf9cebb1af,0x75653b6dd7601b13,0xed2f6dcedbde0af3,0xfcf48f5df6ff7675,0xf65f00ebe9fa5ffe])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x80aa012,0x44002241c032c18,0x71024700408145,0xa000ac180201c08,0x1015000115302029,0x140470a280900c02,0x8869a80cc8040348,0x208509046109000,0x8809a820130c0300,0x2c84004580b9420,0x7081421041114426,0x2701150004084000,0x43a0c71500309820]))
  | _ => 0

def compactPerms246 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains246 : Array (Sig × Nat) := ([(subcube 64 0, 7)] : List (Sig × Nat)).toArray

def compactWords246 : Nat → Nat
  | 0 => 0x13f
  | _ => 0

def compactCount246 (k : Nat) : Nat := match k with
  | 7 => 1
  | _ => 0

def compactPath246 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | _ => 0

def compactLive246 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits compactWords246 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs246 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits compactWords246 (7 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords246 (6 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket246 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP243 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xdf6dffffb3efacb,0xfd3efbcf96564d3f,0xffdfdff7f8d9fef1,0xd7aa6ebbbe2fdf62,0xae6d86dec0d79fec,0x4e10643f7f7f3efb,0x8fbe3fe09ff52fea,0x1bff5b445eaecec9,0x74e6f3704da4e157,0x6ce8708812e2ecef,0xaf2fe55f9c0bc187,0xf0fd1a6337218110,0x676d47d9636e5960]))
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0x8180048000448f,0x108a00cc5640c00,0x1082410904820,0x44030ad8a30385e2,0xee360402c095bda3,0xa38644308480401,0x42b683a0d0850260,0x434618660eee7fc9,0x3ab487720b906013,0x4ce8778a1ca46145,0x8353874a1c478167,0x417c26e3796f8151,0x67edd558cb2cb9e4])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0xfcfc7f7b5fffdef,0x63a3ddba4f641abf,0xefbbffff1ef53d6e,0xc8dddf4dbdf3a7fa,0xce164919f7067873,0x382a12ffefeef76f,0x78fdc778ff87d776,0xf61f246b8f5ab50a,0xaa9d2d7f33d50228,0x611207038df775df,0x96d736f66bc64d69,0xc37235a1e85e1269,0x8080b70ad905f08e]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xefb23fdfedf579c,0x97cabe20a11d833f,0xf7fd7aafff8e77a7,0x64f37ad6e34ffd9f,0xe1b10de2388da220,0x8600203fbbffffb5,0x5276bbdff77cfa1d,0x5f6698161ee3783d,0x5b3460d8a6a6393,0x1c08300803fffbb1,0xcbdbbf2dd3b43096,0x453c06debe008110,0x6224fd72b6d42900]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xfadb3feffe7e6f7,0x1afde01c74a0f43f,0xfa7fadfff737c899,0xff17aff8cbb8fbfd,0x116e760104f85d83,0x4950c53bfefddddf,0xefe3fbbf48ab2ff5,0xe3c816a060340ff6,0x3b6498a26c935c37,0xd2e048e453fcd74f,0x73f9dbcb6c4bbe66,0x18cae27c41a16880,0xd49fc6c48ab8470]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x40e0400300602c0,0x12a2d8ba3614d380,0x218008300053481,0xc0906e008828fb1b,0x816d4fd934ce5a60,0x4f52f78822241000,0x8603b580f202f14,0x120b16005e328c3e,0x25e7782d6ce74337,0x7ffa78edd042d48b,0x28930056b8a7c86,0xd0fa127ca6b1fbb8,0xef6d276a70c74d7a])) : Bits)
  | _ => 0

def samplesQ243 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x2092020c4450024,0xc004102128a20a,0x22401104001e0190,0x284241448a18a480,0x4102012004200010,0x1248204424520e3,0x8022040010210000,0x1808b2042166c100,0xb581142021584160,0x80140002400224e3,0x2c2601510c000081,0x1008180030600a50,0x961c038903625140]))
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0xf7e7eff7f9fbbf5,0xffff5ff3be9ffff7,0xbbfdfffd7be87ff7,0xbbb6feff5dfffbff,0xf7fffbfffffacbfd,0xffdfbfbfcf78ffdd,0xffffdfebfbbf7b7f,0x7fede7fdfefdbfff,0xcebff77ff6b37fd7,0x777ffbfffffeff5d,0xdff3e7fa7dd7f5ff,0x5dffffeffb7fe2ff,0x6df7fd5fcbbdffec])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x303a0847080a10,0x8c0c0040b09b2460,0xa881808829285152,0xa022058500d3200,0x12a8900a01188280,0xc595212a8320a449,0xc4086129021302,0x60452025144d1192,0x421304434006842,0x5420093890d24509,0x96c220626080440a,0x415020a5c054a218,0x4c0a50a49056088]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x104dc8a11207841,0x2435098f5cc25cd4,0xc1888a1162a1cc48,0x45a9b62864840a28,0x86cc705c5340c985,0x14da5d79b9925f00,0x5114592b03145924,0x23620da29209004f,0x274e8931824a68d,0x566093e1a7f9db10,0x8199be2491949426,0x43444ec42929582,0x20a1fc72b4942800]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x524c13020a1940,0x65041a638a1509e5,0x9ca25031c01823,0x2b0143210e11102,0xa29c10c8f940c0cc,0x360938b20c28991c,0x1d054ba141043975,0x206104d144101899,0x401c824606a20a86,0x623b1a08ff4920c,0x5241c28a5087b462,0x492c2e440052089,0x863fc4448898420]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x40e0441100720c0,0x320248b00604d393,0x10284630004004a1,0x2110c2060c7089a9,0x80050a4150c24024,0x1a42869544584294,0x3308c100808c082c,0x4a08350e2308844,0xc288463102920501,0x308d084072c2854,0x4930459810449130,0xc01414209230043,0x2816581582389204]))
  | _ => 0

def compactPerms243 : Array (List Nat) := ([[], [116]] : List (List Nat)).toArray

def compactDomains243 : Array (Sig × Nat) := ([(subcube 32 0, 7)] : List (Sig × Nat)).toArray

def compactWords243 : Nat → Nat
  | 0 => 0x13f
  | _ => 0

def compactCount243 (k : Nat) : Nat := match k with
  | 7 => 1
  | _ => 0

def compactPath243 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | _ => 0

def compactLive243 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits compactWords243 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs243 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits compactWords243 (7 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords243 (6 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket243 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP227 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x6fbfbdff96f5bf,0x2fffe77bdf2fcef9,0xc975c785afefce2e,0x79cfb119db6b5b9c]))
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0x5000092108139,0x280520010c0fca28,0x8055c780024cc608,0x30ccb119db284a9c])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0x765fdeb7fabb21,0x7e5ffef6c4f395a,0xf1d44307f6dfb1b8,0xb0ff011949b9f490]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x7d6fefdbedc1d8,0xeffffaf58ab5f3a5,0x967b84f75bfe4fcb,0x66f0fc8293b42b4e]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x20700c01aef181,0xe800c2600a2531d1,0xd177c7f1008209aa,0x60f37d9bda3131de])) : Bits)
  | _ => 0

def samplesQ227 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x10444a02080840,0x415102022a160300,0x210820102d0a4022,0x2104240538425918]))
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0x7afe9f7dff7fcf,0xdaff6beff3fdfc7b,0x57f2ffffd76cd7bb,0xffddb8faefae6efc])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0x9a0a0e885148a,0xbe824921458058b4,0xcab289cfc2d19288,0x925143a843b9a480]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x292042c103287,0x10aa206440e10c28,0x50a21b8550648780,0xc6c0108247a42244]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x20780e44a25183,0xca6600a8e3755418,0x13124da6972c8291,0x8a48b02a2d8e4e20]))
  | _ => 0

def compactPerms227 : Array (List Nat) := ([[], [117, 16]] : List (List Nat)).toArray

def compactDomains227 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray

def compactWords227 : Nat → Nat
  | 0 => 0x1f
  | _ => 0

def compactCount227 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath227 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive227 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords227 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs227 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords227 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords227 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket227 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP231 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x7767ffde,0xffaef676ee1eb44c,0x54fffffcfbe5fdd3,0xb671ffaff5f227b7,0xc3376037bea34223,0xcea4008773dffefe,0xffc6e7fc0dc3bb5e,0x6ffd1f1c42f1c738,0x9e3b17ce181e7870,0x86816744007aee5e,0x3ceff9ae92342d1c,0x758f5d15ce384201,0x854abaf16d0d6160]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x7d3dfff7,0x73ff7c9c3f674f91,0x317ff6e77ffefe7d,0x391e9be9af3f7b7c,0xdc0aa5c90f8e7d8c,0x3bca41187ffdf7af,0x753ddcf9fe77e5f4,0x7713f3cae5cc10cd,0x6d6caa26b163d708,0x684e081041dfbcfc,0xf757574f2e0bb2cd,0x2e09b0eb3c81318c,0x62111b4cba6ad414]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x20120000,0x222202443556ad44,0x3140022440003095,0x3812cb80e4600230,0xf0e64ad0f8f5b2a,0x8e86419f00411222,0x50685646003c144,0x71313fc8c4f0c5f8,0xac3d2b86b12bf900,0xeecf6f5441912064,0x548532a69e3ab40d,0x2c0fbc714eb9738d,0xe75ba165ab4f7574])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0x7b9bfdeb,0xbff4bbe731ff8ae0,0xa9ffcbffffbf7b9e,0xfe9f63d956fcbcbb,0x2fcd260ecf4d8eb0,0x34350c027feb7b7f,0xe93a5be6f38bdbeb,0xff6bec2a9931e8f2,0x72af4dd6ae83a888,0x8080760aa23f736f,0xcfdb26becdce7cd2,0xa8060ef2cd528211,0x846235ad0bdaa188]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x1210102,0x10043c820a0e1ec1,0xcc0000028244a0a,0x24013289163a280d,0x4385a142ffcc8e81,0x7ae71c6a13084004,0x900489092c2a012,0x2f4bf53a93a5821f,0x5b2b4d669cc384d8,0x81fefe0ab6828a5c,0xac5a040aec057ada,0xa883519fcd52927d,0xd6f752c96f3aaf8c])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x6ff2ff3f,0xfe730fcbdfde3d47,0xe3fff3fec7ffeaf,0x6de3fe96fe6bca4d,0x7b84d9e071dc9b4b,0xcac210687f7fdff7,0x8fc7ad17f2fee417,0xb9ffb5f196a6871f,0x89116921d5e985d6,0x17e880014f78bf5,0xfcbcbef2fc31d22b,0x88f3f11d4200106c,0x52956743e7370e04]))
  | _ => 0

def samplesQ231 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x89880a1,0x830084910c10b30,0xab094120d00604ac,0x958205500068324a,0x804c8228411098c8,0x5032b502298d0e8,0x8d00750803012408,0x49042a1b145a8020,0xe90281288a0a05a0,0x19408a060b4a8416,0x3c6c488d10042314,0x210c500740306010,0x4c9a5ad0650c4140]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x2c21208,0xe10814280d0a06e,0xe2c0082e0422115,0x4c01466488ca8043,0xa4122c20008a5a,0x42130c3ab54310c,0x590134504202048c,0x44020c920a8d8002,0xa586248c94114304,0x9c009a84124a980c,0x924347470a008298,0x2308004f08823b00,0x56281a4c1a28c014]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x20124001,0x622024021c48944,0x1046010c2124198,0x4901031480201200,0x2044628080a8968,0xc02001329844080,0xcb2034808a201419,0x4040008812c20020,0x4884850406194404,0x5808cb04024a0c02,0x220a0d4901010a12,0x6148018720124910,0x1a005a981420020a]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x4640a0e,0x408914104600740b,0x5432044108811801,0x2468a32892c991,0x501208c092a06000,0xd0c8d0acd4432b05,0x2048822230848260,0x229c54009051953,0x61820c250a49a13,0x2212047024b57368,0x81912212c4520440,0x8812262084c096a4,0x8060a5250ad2a080]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x7ededfbd,0xafffcf6ff5f5eb7e,0xff3d6bf3fe77f5bf,0xfdefcf7dcbebf6ff,0xeefffebd799bbffe,0x8d73fbd7bbdff1ed,0xdf237ffbebebf4bf,0x6ff6ff9b3effade7,0xffaeffaddf3b6ffc,0xdfc9dbbf5fcb9e5e,0xbeff4fdf7f05ffff,0x63cf53ffeff77b7d,0xdfba5add7f3eefde])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x100d04e4,0x1084503402204290,0xf0d18e0004a08a60,0x92b6180114046098,0xc401205182214404,0x509ccf04502b8473,0x4a8801104c4242,0x20996325c4104b49,0x2490030686208b1,0x20930449603502d1,0x4cb490b0a0525021,0x8891241002680026,0xa0972503e1170c00]))
  | _ => 0

def compactPerms231 : Array (List Nat) := ([[], [16, 117], [80, 113, 98], [112, 81, 98]] : List (List Nat)).toArray

def compactDomains231 : Array (Sig × Nat) := ([(subcube 4 0, 5), (subcube 64 0, 5)] : List (Sig × Nat)).toArray

def compactWords231 : Nat → Nat
  | 0 => 0x8bf
  | _ => 0

def compactCount231 (k : Nat) : Nat := match k with
  | 6 => 1
  | _ => 0

def compactPath231 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | _ => 0

def compactLive231 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords231 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs231 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords231 (8 + 4*i) 4
    let n := v >>> 2
    let bits := readCompactBits compactWords231 (6 + 1*(v &&& 3)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket231 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP244 : Nat → Bits
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x100000601840081,0x104200411c1b03,0x601c88320506,0x105861e012a18328])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0xdf2ffefc5cfb5c1,0xfffe6fcf7dc3fe7,0x4240601fddffb52e,0x9c79f1e012ebaf28]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xfa4ff37fb89ca28,0x8ffc7f7f683fc1f9,0x838884c3fe77fbd0,0xf01f2e0204f37114]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x43506210389f34d,0xe02804602ebc05fd,0x30ee6fc14043918,0xf039afe2f70b31fc])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0xf5dfeff3fb473d5,0x6ffbdfe3ffbc1f1f,0x3d26623fbfbe4d1f,0x73f8e1e0f3bd93e8]))
  | _ => 0

def samplesQ244 : Nat → Bits
  | 2 => (BitVec.ofNat _ (limbs64 [0x100400211040000,0x422001200090808,0x1000001011010200,0xca00848840082846]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x20d12121e101a1c,0x5e040ca0c32da84c,0x1889aa0119e59028,0x104b54cc46caad20]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x5b08784670b4c7,0x3998b86481a06326,0x7f2f8676c567962,0x209e422326f35110]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0xbcadcd6f56e2ab6,0x1d3675d275bb7abc,0x748957301d556e19,0xda75bfb8e60b39fe])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0xa28141400a8462,0x8148c10438c04621,0x8412054686184553,0x20a0222039351288]))
  | _ => 0

def compactPerms244 : Array (List Nat) := ([[], [101]] : List (List Nat)).toArray

def compactDomains244 : Array (Sig × Nat) := ([(subcube 32 0, 4)] : List (Sig × Nat)).toArray

def compactWords244 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount244 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath244 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive244 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords244 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs244 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords244 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords244 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket244 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP245 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x6f5eff,0x7fedf7abceec7eee,0x75ac8d6ffff7bcff,0xefeff7e6df167f5b,0xc27fba0dbc97af80,0xb295257df46b0419,0x9fbffc7efec76e3f,0xbd99feb2f92dcf7e,0xa135f54264bf0eb6,0x13f97206afd66723,0x76404026faf61e9f,0x7cfe9cd2e15d17f0,0xa9378a66790c2282,0x355653dced899930]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x18400,0x1801000b750c0600,0x31841ca000000810,0x262a04a004024fc1,0x181e024cbf9575b1,0x95056cd14b061d,0x8181140400500c3d,0x4d1a6090680c2260,0xa415fd5e659bd8d2,0x33e0ea8625d00723,0x77c04c7849304499,0x4338b8c2f5516790,0x18365e46ed1fe2a2,0xb5d69918db89f9b8])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x7dba3f,0xbd97ff793f1e4bf7,0x83043a8ffbcf5fff,0xfe79c9ba26f96eab,0xff9e4fcdfb145573,0x4177c086138a0204,0x1ffff7ef5dfe97fc,0x7e9ff0dd7eaf3689,0xbe47e99c6348f959,0xe3e6cb8120118000,0x1800c5dfdfafcfb,0xab75ef5cd521e994,0x5e30745be613c020,0x8080ebb15aa6f088]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x77ed3f,0xdffbf9cff1bf8c79,0x3837170ffdffefba,0x3ffffe3d079f8ff4,0x1cfff3f23fe87802,0x7ce8067818738898,0x3fd77fffa7f8183f,0xdf6eff3f8fd1f7f0,0xc079fe1f980f0fe1,0xfc007c07d1e80432,0x780b7007df7de31d,0xcf78f3bf0e8e1e17,0x10361f8c7ce40303,0x3814bf599170a944]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x44a40,0x400c1408a2c087f,0x723e1b5000c004a8,0x4df9380711003a,0x44bc00011f9c5a02,0x7efdc0333ae3abde,0x2212004a00280214,0x308cf4190121d590,0xfa7dfb1c006d2f69,0xffa27803980f24fe,0x798f7d5880d4a00e,0x2c60c41f040f9997,0x1133b43f7cf7c33f,0xb8bd4271b5b0bfcc])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x5fc7ff,0xfe7fcf56ff6db71e,0x72da58fffef8fffd,0xf7fe3df9fd63d1ff,0x7dbc047fc79d52bd,0xe9dd923ebc42346,0x1ffb9fdffb79efd5,0x61fe65d9617ef9f7,0xfe9c1b7c05f1f04a,0x3fa2a8fa1c0f30cc,0x1840d5bed95e5ee,0x77abfce33453e18b,0x11cbf4378d13c03c,0x80a9dc22b7997688]))
  | _ => 0

def samplesQ245 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x10a104,0x8211281230038010,0x88115282a1304084,0x6060a41241ac0a0,0x81c2444023610030,0x4c02184200404924,0x2a349040c6408029,0x20006a046001c08e,0xdc0ce00146090c,0x20446084ec0940c2,0x4030e84a0920616,0x1c261c10e00c09e0,0x40058010681c00a3,0x62542d465881120]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x18402,0x8821000351088200,0x208014809014c221,0x20210004408c400,0x888841425214491,0x410084800420015,0x810c20816258108,0x80222424404582,0x4c80a8a0024208,0x508602064020042,0x460104c4a0c09240,0x2c060200480418a6,0xc480803120450889,0x20142e404240206]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x245e0,0x4a3c408690609402,0x3cfa44707a505802,0x12c49d48700604c7,0x86ce816412da214,0x4804b704c64e559,0x7946634c58c0940c,0x90353245382260a2,0x8c30cb4cb3844384,0x858f003608b30552,0x8c9544a4f462d87b,0xa2604b5440248ab0,0x5810c4daa2518e0a,0xcc0e3b14aa6a080]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x812d0,0x6084032006207126,0x4748a83c40c11018,0x499845800b253205,0x60201880c81e814c,0x1221e0a4e1a03602,0xd4c308b700982056,0x8670941990860270,0x62023000a1910f2,0x4022900b1270bf04,0x19f0110b5e2d6008,0xc158e02f04b02601,0x3a17c090204344,0x1892bd099050a840]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x7bb5be,0xdbf7ae9ff5dbef94,0xadd9f6aaf7bccef7,0x3f577f53ec7ecfad,0xd9fbddfce7736efb,0xcf929f5e9d5e7d35,0xeaf6daced6f59f3b,0x72cdefec6d61ffcf,0x96fdbff9ef56dfad,0x6f7e61eeed7f62f3,0xc72fcfe4a0f6f65e,0xfd66de39f80f9dfe,0xdda7f13f7fff5abf,0x3fa542f5f5bcbfee])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x203808,0x4803a28029008a1,0x8105a30b04090448,0x6000422508b00230,0xc70212c188000902,0x91212480309918a0,0x86a81c82a1082a40,0x4408019081841811,0x6382240208703820,0x70600e8880486825,0x1048900b09142584,0x518194a214932009,0x108220405286024,0xd02c1c02b1195408]))
  | _ => 0

def compactPerms245 : Array (List Nat) := ([[], [101]] : List (List Nat)).toArray

def compactDomains245 : Array (Sig × Nat) := ([(subcube 1 0, 5)] : List (Sig × Nat)).toArray

def compactWords245 : Nat → Nat
  | 0 => 0x13f
  | _ => 0

def compactCount245 (k : Nat) : Nat := match k with
  | 5 => 1
  | _ => 0

def compactPath245 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => 0
  | _ => 0

def compactLive245 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => readCompactBits compactWords245 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs245 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let v := readCompactBits compactWords245 (7 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords245 (6 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket245 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP247 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x7fbbd67fe75afd1e,0xe915fa1edd57ffb4,0x8092c7ee9b3db11e,0x4db64acd30fda7e8,0x5fc8d8d103109bb9,0xa12a626259294541,0xbb44d9a117e10f3a,0x6a085a21d46b858c,0x6307082119344104,0x4fabdf656df61,0x89fb45dbab9abfcf,0x8596c3bb0b404565,0x509bcda2c5933aa,0x74980b0fc3830442,0x402031154a966ee,0xf86668c0c5961300]))
  | 1 => (BitVec.ofNat _ (limbs64 [0xc7fc4bf37d9fc948,0x9fdb12b1b23fd706,0x7f7a3c91fabfc2a1,0xff7a015bc9fa5216,0xee7f3e10ac7a6a4f,0x1c07801006c6f247,0x52326f308806b2c9,0xe2ae04e2ff67002,0xe8d8345e22800a11,0x1b0b6c767e3e30f,0xe89e173cf0e4b475,0x6e89e53e50bbc03a,0xf132438a8b600674,0x7203e4591b108015,0xcb0d64a2811036b0,0xa61ab51aa2d140cc]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x7e5efd1efafeae37,0x7aeabf612958a75b,0x487eea3fe4c5edf2,0x1a5dfd24723578ff,0xb024016bd20f5444,0xed1419d30743a14,0x6c5b84cce0790411,0xb0d5079590806bff,0x9420c380c440b4ea,0x9e40fdafae7473fc,0x3b51be1355de2a72,0xdcc2bc63b480aa8d,0x2a1c4f35742fcc0a,0x806e35909c6803a8,0x3070884c0a45a7e7,0xd84982f1a00a413]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xf3dbafb79b35f2fd,0xd68e5dee2e8f8d4,0xf0adf7f11b445ecf,0xa9a9abb74fc3d857,0x1fc720ae1ce087b6,0x51cb9c61a15684b9,0xc4a5215e179ee8c6,0x5509a42028940470,0x60103050200b0000,0x618bd5f9fd2f5ca6,0xb7e67dc52d6947b3,0x756ff987e33c94a8,0xc6d630c411963441,0xeb1432ee2404f801,0x88d140220039acd,0xc0a9564c197c0868]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xbbe7b3cb7eff36a8,0x96a412af4d9f28ed,0x7fc53b6e1e3a3d51,0xf6c5f55eb6fbad96,0xf1b0c110b38509f0,0xe20c7f8c07b90846,0xadc86ecf6006bd34,0x8e231f902f098a02,0x8b000a201d500466,0x80404f77df9bbcd7,0x569d92e2deef7389,0x6b711b7dac3b3a17,0x92d83554a803180,0xde3d856e3690068,0x40283410622f95a,0x56c925b5a30a1410]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x9ced7cecdfeb79d7,0x73ffcdfa1fa70beb,0xb71b409b65d2673e,0x57e7b6f28d049769,0x601b605401b6401,0x387003ffce8a05aa,0x30e9230897142a8,0xf1d6b0ead03bbc39,0x1cef000140a4fb09,0xa24ef5ef998a9ba,0xc563e9ac5e31d8fe,0xb2bc3ed453446fd2,0xd0c18c22b47ecb55,0x4f1c0201c920796,0xb3000834508add1c,0x1b30c2305ce10383]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xed37fffda5e5d7e3,0xe4176d45f6e0543b,0x8fe59d44e5eb9aed,0xa01a5ea9ff0e6fa9,0xe91a4fee6de4b00a,0xc7b4bc02f801fbb8,0x10b110037e885147,0x1f4495f434453c5,0x1000c58e820b0090,0x741b3bfa1bed0659,0x7e2cea7fa317cd0c,0x9b7f46c80cc71140,0x3ee27029c381c8bf,0x9b0c0fa160847800,0x40f07088a9574931,0x21570bc3642ce824]))
  | _ => 0

def samplesQ247 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x610854714250d509,0x80009a3a14485300,0x8ad4a0015c42c,0xc004430c84868,0x16129050d104a003,0x687b2000a0288547,0xd411a0a281100983,0x252012a144d05248,0x28f420a2300160,0x6a60f0ad26460520,0x88a9059ba09a8542,0x8416403313408005,0x1147c121808030a,0x7004011f40070002,0x8882849509a526e6,0xe82608c0c0941200]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x40540003600c4c08,0x8042883010048400,0x2420ac0010204021,0x1106004008204010,0x9881c4408081120e,0xc88e00000100d02,0x4218029008000422,0x2c294100a2343021,0x22c0000a6188100,0x1040a08406416200,0x2098130840803440,0x6a80251a10224000,0x9010429809280200,0x1251902100021,0xe600048b828024a0,0xa600a50a8280008c]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x1a40041248861b,0x90008e3210181110,0x4818ac524000e424,0x81d104050416808,0x1201041014069289,0xd088a000081025,0x18090200a4220d00,0x84121a0e2a040a1,0xa0a85068b2340120,0x2248f0ad26245300,0x31012410414a2022,0xc880b4201100a009,0x201c5415380c8202,0x200e019b10212122,0x2224800e800526e7,0xc00980e10002012]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x2303052499103001,0x828428261093105,0x810c50e202408646,0x20e809211540190a,0x346000c074248a0,0x43250ca9c2261060,0xd00a528263b80c8,0x50380900410cc0,0xa901522040e112b4,0x22845439e9221824,0x954228c52d610331,0x4459885610880a1,0x4206944010901403,0x213452620424b1c4,0x82700503003924d,0x40a8524419580840]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x9ae5a382208620a0,0x24890044492300c9,0x934002240a881852,0xa66020a201108586,0x60a46a0602a10854,0x704401509930a08,0x3c41d1408886070,0x20c4c121906ac14,0x1d43008201437a00,0x85910f52d991a8d7,0x4614124016245289,0x23610148ac1912c2,0x4041810042003884,0x9f0c02081188849,0x55102140260ad918,0x12c92531230a0400]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x1ca028888d230024,0x67990140432108a1,0x8143002122801152,0x6460a6b281000182,0x4040238920504460,0x1000061853054010,0xa610090201c01c,0xc212041c19030010,0x1541019609415202,0x80830f52d918809a,0x4042c8241801089c,0x10280a8428081fd2,0x40c0800046425854,0x5b040200800148c,0x11011820145ad918,0x111042300c610101]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x84009a5804a10060,0x2485204180a00082,0xc0000085821090,0x400608a02060281,0x4030198360302410,0x300202043880c218,0x8062080701802005,0xc10602060400820c,0x450088301004409,0x80010b4210880449,0xa24c0228214c804,0x111a424008841242,0xc600020c2010824,0x82800800208a0c00,0x90392009704910,0x15700816424c020]))
  | _ => 0

def compactPerms247 : Array (List Nat) := ([[], [80, 113, 98]] : List (List Nat)).toArray

def compactDomains247 : Array (Sig × Nat) := ([(subcube 1 0, 8), (subcube 4 0, 8), (subcube 32 0, 8), (subcube 64 0, 8), (subcube 16 0, 7), (subcube 0 1, 7), (subcube 0 32, 7), (subcube 2 0, 6), (subcube 128 0, 6), (subcube 18 0, 5), (subcube 132 0, 5), (subcube 144 0, 5)] : List (Sig × Nat)).toArray

def compactWords247 : Nat → Nat
  | 0 => (limbs64 [0x1fe3fc7f8babfe1,0x6cb4300ed7b59dd8,0x66119ad034e64234,0x26c23426423021c3,0x37fc05d1aa4ff834,0x19fe05dbca3d38ab,0x73141502ee91fe0a,0x8cff83fc01470bac,0x20594d2202847061,0xb52262a306481112,0x41279489e51e7,0x2841c4bfdffef77f,0xbddef7f7fedffeff,0xdbfb4e159c6b38d6,0x71a0e309c6138a43,0x3442689cc5198a13,0x14e6c23826426423,0x26ff0225ff06339,0x203c2c79ff0ff028,0x8b61a8782f0b9797,0xb33007321ed0fbc8,0x3210e4c78fde4583,0xf2691d0c7832fe10,0xcd479832710edcf4,0xffffffffff826426,0x26c23423a23447f])
  | _ => 0

def compactCount247 (k : Nat) : Nat := match k with
  | 9 => 1
  | 8 => 5
  | 7 => 13
  | 6 => 3
  | _ => 0

def compactPath247 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => 0
  | 8 => readCompactBits compactWords247 (28 + 12*i) 12
  | 7 => let v := readCompactBits compactWords247 (624 + 15*i) 15
    (readCompactBits compactWords247 (564 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 6 => let v := readCompactBits compactWords247 (1500 + 14*i) 14
    (readCompactBits compactWords247 (1428 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | _ => 0

def compactLive247 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => readCompactBits compactWords247 (0 + 7*i) 7
  | 8 => readCompactBits compactWords247 (88 + 8*i) 8
  | 7 => readCompactBits compactWords247 (819 + 9*i) 9
  | 6 => readCompactBits compactWords247 (1542 + 10*i) 10
  | _ => 0

def compactPoolIDs247 (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let v := readCompactBits compactWords247 (22 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords247 (7 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 8 => let v := readCompactBits compactWords247 (364 + 10*i) 10
    let n := v >>> 6
    let bits := readCompactBits compactWords247 (128 + 4*(v &&& 63)) (4*n)
    compactIDsFromBits bits 4 n
  | 7 => let v := readCompactBits compactWords247 (1014 + 7*i) 7
    let n := v >>> 4
    let bits := readCompactBits compactWords247 (936 + 6*(v &&& 15)) (6*n)
    compactIDsFromBits bits 6 n
  | 6 => let v := readCompactBits compactWords247 (1572 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords247 (1572 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket247 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let d := readCompactBits compactWords247 (414 + 2*(i % 3)) 2
    let off := ((i/3 + d) % 12)
    let v := readCompactBits compactWords247 (420 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | 7 => let d := readCompactBits compactWords247 (1105 + 4*(i % 6)) 4
    let off := ((i/6 + d) % 23)
    let v := readCompactBits compactWords247 (1129 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 6 => let d := readCompactBits compactWords247 (1578 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 7)
    let v := readCompactBits compactWords247 (1580 + 11*off) 11
    if v >>> 3 == (i/104729)%251 then [v &&& 7] else []
  | _ => []

def samplesP239 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x8ffbef3fed9d1fdd,0xc7d707d0eebe07f0,0x1ff3f0e0077e13fa,0x6f0fc593ff07e64,0x7e7f17887d407a08,0x6c3fa070610be0de,0x4187e81fe720601f,0xe07458005fe3f41f,0x4019c0e0c0364341,0xe000800f9eab179b,0xd2a53bca34e0deb5,0xff0e9cdc3250705a,0x3198705e2e37816,0x5807863c07e1183c,0x408009d0b1254e14,0xcf24e5512aa85890]))
  | 1 => (BitVec.ofNat _ (limbs64 [0xfb5777e3fe1ff9fe,0x2fedb2af336d6bc2,0x45feed09f69f4f8c,0x71ffa38ff1aa5bd8,0xbdd9047ff1e3097e,0x107647000c301ea1,0xf61971a3ac130396,0x13153198a02c9380,0xb06230023c0800c,0xa00eef7effa2f,0xe1ff9e2bf8bfc9ef,0x8af60b1ea883d805,0x392473688703492d,0x80fc58b279c40181,0x80307028404277b7,0xa8e17c20c9650420]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xfeed3eb71ef21faf,0xf956cd5dd157fc2c,0x3b80afff889a16bd,0xff0837d6ebdf807b,0xb664f927020cb387,0xefc0064fd0dd5100,0x3b7289e0129c2048,0x29ca8ee584410325,0xff600c021c0920b2,0x8751d1adb7bf297,0xbf45b3b52f05abd9,0x69eb137349cc02a2,0xf414fc93217c8610,0x3fc017c86e1a0640,0x54586060298f72c,0xc2988a437452a105]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x7d7dd8f9cb7efc6d,0x7eb8fe22ed19d78f,0xfe0f4cfe0f65fbc7,0x860ecb343e0e755f,0xc1f8eed042b84430,0x6b3859fe9e2a01d5,0x8564561c15c2dc70,0x962847065992085a,0xb081d09d00001c01,0xd780e20df3fe6572,0x6adce77a8bdae5aa,0x30cd7e43f46c6d40,0xc2c300e4589307c1,0x97076d639600e03a,0x7a0a08112c0071f1,0xb12a538d241002da]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xf4d687ddf1ffe7f3,0xd7fa4aafdc8d6c3d,0xa5fd1209f1e0a473,0x88ff5c6fce55dba7,0x3da6fc7f8e1c8941,0x8049b88073c41e7e,0x81e8e43abec8389,0xec956e67002f6c60,0xb180000c0076212,0x815010decd7fdcc,0x1cfa5ddfc7bf3951,0xb4f9e4be9723a7a7,0xc53a7492840036c2,0x60fba08d81da1240,0xc081c081841ddb,0x44ce05be99586100]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xbbffb7ef7e9ef76,0xb96d355d3ef2b173,0xda737f567b1be867,0xf94714ebc06fad88,0x421bebd009b356ae,0x93827d8101d4af28,0x84a820fc4851fc26,0x48e2a1382750f58b,0xb4e6256000301dec,0x326a6a973f55a8ec,0xad1a40b4d0457626,0xdf12f7e9cc3012fd,0xac989693b5ce1ea,0x673868006825ed87,0x53a060a10210aea,0x36530a8282a41e45]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xf7aafdce3fe7f29b,0xfea3f9f203e29adf,0xe00c93b7fce5fd18,0x7fb1ebb015b1a6b7,0xcb8713aeb447a4d1,0x1485823fae23e003,0x7ac11700502f1fe1,0x170b90dbfa9c0af4,0x44c01a1f3fc88000,0x58014636dbcdf71,0x5723ec457f7a165e,0x4735e9a5439f8d18,0x3ce60a1e5cac983d,0x8800935790200000,0xba0570254e5aa84f,0x1915b07c5783802a]))
  | _ => 0

def samplesQ239 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x85012d0804991104,0x8013028001162550,0x400204003001520,0x40209414400868,0x48000100890069a1,0x1002244130020009,0x1bd410012124011,0x81490822032202b1,0x80158220088200,0x2a00098282091210,0xc00528c034e00ab4,0x908885808506002,0x304850080c06014,0x6b400011005,0x40008823a264c604,0x4b00e0502a205010]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x4a5113e09a0c91a8,0x5063084454b26c4,0x8cda8c44d2290680,0xa294839652e04809,0x251840625e122132,0xa60c4e4462080491,0x18cc33490a81490a,0x4051134814088190,0x261a85c81109b685,0x6490313ef3eb7207,0x20949e0918944923,0x88b60b0ea846d800,0x5804566081434241,0x82695290a3444291,0xd4a02024c0a077b5,0xa8e05c2048600420]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x6640ca10612080c,0xa102818cc10a244c,0x1d8a005582190400,0x6608909411c90808,0x44c04002065c01,0x6864021100b1088,0x807110c00c500019,0x181840e0060b8a08,0x4078598130c8300,0x2010611ad3293001,0xa24022a02804a099,0x212b1153284c4a00,0x3014041180484600,0xec0429066001204,0x46884166810e724,0xc2880a4164008104]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x68241011c842c801,0x2600542464088086,0x889b048c94298084,0xa210c10062842111,0x428444210241402,0x2890882604411610,0x9000828d84440d82,0x1800428818012808,0x330a8a0891202414,0x40d8203c71e26402,0xa58812a0218e00a,0x30c5520130048c40,0x508010a400110340,0x924d6102a2486098,0x18482490081031b1,0xa02a130904100288]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x30928254706464e3,0x52e810101c2040a1,0xa034060038e00893,0x81320141ca001007,0x148a188f44790010,0x89588382c6742226,0xa00a804e18504a0,0x6424910528d43500,0x5168202104406c6c,0xc18106652cd6cdcc,0x1caa1513830b1140,0x9450642483218029,0xc00a30220c0190c8,0xe01b000980ce204a,0x8b9110c0018118db,0x44605ae91582000]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x8c00621000650,0x1868005112200000,0x2204500208824842,0x1100046900028084,0x3a9800098248,0x140011001104102,0x4400002041208040,0x26a4200180541042,0x6060050cc24040,0x502010c1480e8,0x5024014c0010400,0x46000480462000bd,0x300023e04802a,0x4100080008000842,0x1120208050b084a,0x1411008280840841]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x918a600a01a12212,0x4888081210a01800,0x600401200884280a,0x901084100100604,0x82011889814082c8,0x1000209081246124,0x4700482030228060,0x8380a806a1a00463,0x40a0200144504042,0x102382010c148930,0x5121404445621644,0x4200a0a042a00129,0x462080a4c208808,0x4000804010230800,0x2031a49064e084a,0x1115a01413830002]))
  | _ => 0

def compactPerms239 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains239 : Array (Sig × Nat) := ([(subcube 2 0, 9)] : List (Sig × Nat)).toArray

def compactWords239 : Nat → Nat
  | 0 => 0x27f
  | _ => 0

def compactCount239 (k : Nat) : Nat := match k with
  | 9 => 1
  | _ => 0

def compactPath239 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => 0
  | _ => 0

def compactLive239 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => readCompactBits compactWords239 (0 + 7*i) 7
  | _ => 0

def compactPoolIDs239 (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let v := readCompactBits compactWords239 (8 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords239 (7 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket239 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP223 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xd9ecffff0dce7fd5,0xfaff9398fd9d2df6,0x17896f7cee256573,0xa7f02635b8373fb4,0xf7a03634fe7f91b4,0x28117b0ca992103e,0xe94046b0260ccc7e,0x342d4e040e536d93,0x2c60d3803000060c,0x9800280a37cdf6d6,0x7ef62fad4ccfe7a3,0x1d3f7778b296c4b6,0x600fadb31d910a9,0x8d3843a1906d1081,0xc80004141c20476b,0x93d6916a63306110]))
  | 1 => (BitVec.ofNat _ (limbs64 [0xfe7f1f8ffe0fcffa,0x7f0febff000ff200,0x17fe87ff1005ffec,0x7fff9c1ffc83fff,0x1ffc81f807ffe00,0xffe840ff6001fc0,0x7ff9003ff00f80,0x3fb005f1ac03ec,0xdc07c071f870,0x80c0101fffb8b9,0x3f0ff00e0ff381fe,0x8fd1787f42e907c3,0xf80702e4072000fe,0xfc07c01ff80000e,0x30c1f8686042707f,0x564be41401aa1460]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xe1b7ef7bf77f5f7e,0xdff9fd542fba53bf,0xe8117c2fbffa8db3,0xe9237ffadee9db3b,0x28edcc3b5780011e,0xb00e9bf10361e104,0x439c386388717100,0x3c4013db0104720a,0xdbf003801860180,0x220700e07ffffffa,0x7dbbfbc6ba997ac5,0x51ead3a35f49b101,0xb0451d015021bf41,0xd03fa9be06f00070,0x10c0183008cffff,0xa1242d368c050005]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x6f50b2fdebfbbced,0x4fcdfe65d7439c1c,0x79e2f8d1cffff25c,0xfe3c9e396071e3c3,0xcef1fbdc68420dc1,0xc8605a46198bce67,0x84e181a3530e9887,0xc3f0a8c01e438413,0xf25e23c02e08000a,0x55182b08a9fbbf65,0xd3d39cd78315ddfd,0xea2521cd9d90b658,0x398203aacce4c84,0x273d5cee964f101,0x8e12041093107b95,0x4cc34a2bb000099a]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xb7fbdc4ef1bdbfa7,0xf5fe57e2fa6ecde9,0x96751782e1c59a93,0x5fcfc60fc7b6fc48,0xf95e35cb71fc606b,0x78160ab4c6c1fb9,0x163e064cb8832279,0xc8124525ee509270,0xd380d0070061c041,0x6014053aaf6fee,0xa0e5cf79ff2a7959,0x6eedcef6aa760b2b,0xc5e6c618c6d6e050,0x7e84225160120e00,0x20a1e24040012fac,0xb41116d93cf08640]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x9ebf67f1fff2e13b,0xa276febb2df5635f,0xeceef85f55da37ad,0x104359c6050e0407,0xde12b7e5bf983ec5,0x705ea4f036342018,0xb880859d403ee70d,0xff8f077af0b82cc4,0x20ff2c1050080696,0xad0fc3725d704785,0x856c033af5649e3a,0xb1da9d03fd2e48b4,0x4bb83d65d931af36,0x200394400699e0fe,0x5152018d0c300850,0xc9383a814fc87885]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x7fcff9b61ef5f2df,0xbdb32d8fd2f0bee3,0xeb1f83a03a3a484e,0xf89ca1fe3bdfc0fc,0x370f4be28fa1c23a,0xd7a10510c0dfe0c3,0x7f037a5ec5c110f2,0x3c0f8ba01afd92d,0xdf0120688f963921,0x42f01485a616d95b,0xca1874f170fe2606,0xf616ae9c6501784c,0x3c7bc1862a0e530b,0xf1cc0a3e190a0f00,0x62c1a22a3cf9482,0x2aacc1c4d257822a]))
  | _ => 0

def samplesQ223 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x59646885054c3190,0xf880938800221d16,0x489130c04002092,0xa69000089c2f2088,0xa0b20a16185190,0x1841440263383122,0x122304b12e43558c,0x8225aa00010cf5d,0x120205061f00164,0x8081478364c7296,0x462628a10cce02a3,0xd0e4658120ec500,0x205d84040c90021,0x8d0401a190031000,0x58a0046590e0c56a,0x9396814261304010]))
  | 1 => (BitVec.ofNat _ (limbs64 [0xc24170592060a68,0x4c0900b100025302,0x150824e10488390a,0xa1029164696cd4,0x680060020a210,0x2440948d3408084,0x69141219440004,0x81044200442120d5,0x4089451074049163,0x381001805575b810,0x3903500406508030,0x8501304f428896c0,0xd80502a0022100a0,0x241382112204004,0x9b4088626020705b,0x5243601401001060]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x6002c5625162073c,0x3a9e14461a21587,0x242871462799358a,0x23870fb92e2bf9fa,0x402cd49a030822c4,0x410303d8b8e064af,0x4040884735210920,0x5030808923102a88,0x34851f1a6ca5b164,0x8c22272cffffffca,0x2d90cac62a9130c4,0xaa11a25ccab741,0xb0854c0940438620,0xc41f10b536600420,0x415441137208ffff,0xa1002d3688010004]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x2410126882a10844,0x6446400c5010088,0x606220428a8d5108,0x410d1a9122004b50,0xc445458001028044,0xc224289108848001,0xc008924040242a02,0x8114804555211022,0x6008452e84049400,0x466a100c9b38d60,0x909114428101c154,0xc20121058cc01250,0x9190041a00060c04,0x4031500c6a244104,0xa210891002193a95,0x44414a2890000908]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x8353880a60892401,0xa1761600432884c4,0x2030110642018081,0x3344080a0b120108,0x69305489434e4502,0x89a2a20300144708,0x98040a844002e632,0x5c83084e3248d122,0x1706100a00a8009c,0x46a2242aaa8a47ec,0x80648719b12a7909,0x4ae044a0a072010a,0xc24c0844520440,0xe41402c420163732,0x2084600404110fa4,0xa41016c93ca08400]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x828900102810c003,0x12080008542000,0x8004081000420224,0x404000000001,0x1000000028040423,0x2090802004020200,0xd84410080908010,0x4c12402004c0000,0x242008002024800,0x100000001,0x48011850200c08,0x3050880021000024,0x20200099002112,0x840000802292,0x2228805060000,0x828108106c82081]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x108820900c10d082,0x1000080210000020,0xa00800010200040,0x800a00400800000,0x200086080801021,0x30104420040a1000,0x782412082901088,0x40342000040400,0x60200100000200,0x101480000000001,0x4208202040040602,0x30148a1001010800,0x408010420005008,0x1080000201090080,0x22068881c60000,0x8ac800042560202]))
  | _ => 0

def compactPerms223 : Array (List Nat) := ([[], [64, 49, 118]] : List (List Nat)).toArray

def compactDomains223 : Array (Sig × Nat) := ([(subcube 4 0, 9)] : List (Sig × Nat)).toArray

def compactWords223 : Nat → Nat
  | 0 => 0x27f
  | _ => 0

def compactCount223 (k : Nat) : Nat := match k with
  | 9 => 1
  | _ => 0

def compactPath223 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => 0
  | _ => 0

def compactLive223 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => readCompactBits compactWords223 (0 + 7*i) 7
  | _ => 0

def compactPoolIDs223 (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let v := readCompactBits compactWords223 (8 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords223 (7 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket223 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP190 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0xdf5b5fcfdffd,0xcff8ff65e9996bec,0x2264fffdf3fe7fcf,0xfce71c73fe40fbff,0x2ff8bde55581f003,0x3ff86a3a7c4821e3,0x3e3fffddfbe41ff9,0x3bff0f3b71f8e6a7,0xffe83cee03e32e3a,0xb1007ff847c0f3c1,0xe00300f37dee7a9f,0xc9ffaf0d8f3e18cf,0x87043772c7108380,0x7e60b2f67729444c]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xfbd53ff3efbf,0xf0ff1f7e7e1e88f0,0xc38affff7e7f8ff7,0xfff81ffe07ff01ff,0xf1ff40ffe1fe007c,0xc0ff803f8030c604,0x3fc7fffefcffe07f,0xc1fff01ffe00fffc,0x1fffc00ffc000fff,0x41ff800ff800fc0e,0xc3c0703aff87fe1,0xfe0fcff1f8c01ff3,0xf807c07f380f0407,0x8186f74b843e6a90]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x992f0038020,0xacf80c38658f6cfe,0xf33f000060380303,0xf441181e46021df,0x601800fde9eff06f,0x3cfc3c3ffb3ef7f7,0x8001820040480049,0x199cc01c0e0c740,0x9dfb5f4f823c0fbf,0x81d7ffac6ec0ffcf,0xff3fc7f8000a4345,0x800a0948df381cff,0xc9c4cc7fc08fef87,0xfff7000b4f3d5ffc])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0xefe6afffbcff,0xbecfacf89de736c6,0x9511fff7fffbff3f,0x1f4def81edf1f7d0,0xea3fdfbc1863d3cf,0xc147cf09f061192,0xbfffbe37dff879c7,0x2f87ffefc7efff43,0x9c197f4c81fc1781,0xa2d0fc6c0ddf0381,0x9302c0caff7fdf7d,0x718978dec7047c14,0x47fcfc1dc680eb00,0x7051cded6e309168]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xbebacfffff62,0xfff0d09b77f1441b,0xfa00ff9aedfdffff,0xe316f38df7befdff,0xddc0a2daabfdec73,0x30e0150563a00004,0x3dffdffbe7db9e7e,0xf5f8ccd489f7d95b,0xfff60311021cc9c4,0x8dff7f87b620f00c,0xc380403dbd7e55f,0xb7fe1feb7739872b,0xf8c308ecc0ef0404,0x1045bb3cbd57090]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x24000000c00,0x12c09040181102c0,0x8200001000400c04,0x10000e000790d1f0,0x89e080be11f1c053,0xf0403004200186,0x61c1080b01876,0x21e6001e0100f803,0x1e3c200c01c00fc0,0xa1f87c4f9500f38d,0x8c3a04c209747c19,0x718d0e81e7041f03,0xf607307cc60f8704,0x7144d3e7e63060d8])) : Bits)
  | _ => 0

def samplesQ190 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0x20a4a4113012,0x2405049812249402,0xcd138c0505280899,0x1529420480a42084,0x9e0a0218a01006e9,0x1402945288a55408,0x9622531811400022,0x7a89004a32a80a0a,0x55442926a0204294,0x7408210526484012,0xae002e531582128b,0xc9440d05056e0942,0x81013332002005a0,0x24e4b2323328400c]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x42ac0443160,0x2d10c00080e15107,0x3821c2180002223b,0x4009202048626402,0xdc80a8c05e048c63,0x304008c09940185b,0xf012a38a82d0846,0xf1b80111060a0720,0x16040090a81809,0x7002105ce6242533,0xe010440f26482b20,0x680989b180c61cc0,0x5813806112042405,0x10eae64a843a0210]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x992f111c064,0xa5b9052825a76cbc,0xd23f5521340d621d,0xc6844498bcc404e5,0x4013a4e962cfb4e1,0x55d4ac53ab66a737,0x3cb435a4b6133cc2,0x72ea67431a3e6ba8,0x6528a8828459b11,0x846129d948aa5f56,0xb472cc57ffe134b0,0x15e1e6a6a14f2d40,0xb27191a477221234,0x240bfff4b082a002]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x101958044180,0xc118030360980919,0x22ec3262e0442200,0x4296302856034222,0x20b0080243869000,0xc35809056158a844,0x690508074e8169c1,0x426cd050912c120,0x208869912888148,0x832290208984250c,0x10d74004ea7c4d10,0x2008705aa0006414,0x16d4808cd204b201,0x11114dcd44109140]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x414532008497,0x400b2d4c200aa2e0,0x5de29a12c9c0440,0x1172169622111251,0x2269470820821184,0x4d11c63b201b43a0,0xf0dac4c341c02090,0x20244c298705819,0x2ee861770e4560c6,0x3598ca011431004,0x154219f0d997c04f,0x96b6124873182301,0x8240198440638998,0x831419b14bc57080]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0xfdbfff7ffbfe,0xedbfeffff7fffdbf,0xffffff7ffdff6eff,0xdfbffffdffefefef,0xffbfbefbffdfbfef,0xffdffffffbffff7f,0xffb77fbfffff7df7,0xffffefdfbffeffbb,0x7fdfbfbffbffdffd,0xffeffbffeffeff7f,0xfff7ffffffff7fbb,0xfdedfffff7ff7fd7,0xfff7bbfff76ef7f7,0x7dfffffff7baf3de])) : Bits)
  | _ => 0

def compactPerms190 : Array (List Nat) := ([[], [65]] : List (List Nat)).toArray

def compactDomains190 : Array (Sig × Nat) := ([(subcube 8 0, 7)] : List (Sig × Nat)).toArray

def compactWords190 : Nat → Nat
  | 0 => 0x13f
  | _ => 0

def compactCount190 (k : Nat) : Nat := match k with
  | 7 => 1
  | _ => 0

def compactPath190 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | _ => 0

def compactLive190 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits compactWords190 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs190 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits compactWords190 (7 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords190 (6 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket190 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP189 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x7dd9df,0xddeffec3efddfe27,0xd2e279b2bfffefef,0xfad7f4fcda3dda1e,0xebeddbf8b7e9fac4,0xe0ddc1fc31f28cc1,0x2478fff7dfbfd1a5,0xfaeff35eed5be3b1,0xef218ffed82156b7,0xb000f7b9cb723381,0x97020749bb7e72de,0x57eef4ae64315e36,0x71ec3a78790b0e01,0x7a846cd9bab2990c]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x773bcf,0xeff9ffbf9e63b84f,0x8f48c38e7fff19ff,0xffef877cffcfed61,0x4f9fff07ea021ab3,0x1bd23f60f30c321a,0x897fbfdcbffb7e5e,0x65ef8ff2f2a4c3ff,0xfcff138023c21b4d,0xf3f7084e21963a36,0x601dc011fd9c7f71,0xfefa9bc5983ee1c8,0x11f3d9f91f0002e,0x8419afe690dc4650]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x1048d0,0x82180010d91b84a,0x58c8fcc6c00401a4,0x60634f9a04800,0x4ed300e082351eb3,0xdb1d2060b2ffcf1b,0xf908220086008800,0x68e42c1c808083bd,0x32d7d877b01c1b1b,0xf2dfde1801943b37,0xfc9df6b420164502,0x52cc0685103bff09,0x81af8de47cf6d83f,0xbc5f20f5da48bff0])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x5f4f0f,0xfff799f333b98dfa,0x18042c643ffdffbc,0x75bfeaf72db2fd9f,0xd6d2c4efc7950434,0xd821a00b86e34900,0x507feeeffffca9bb,0xfcfc6ebd5e9f9dcd,0x1e964c75541d293a,0x46d8dc01c481cd00,0x88030a5ff97afa7,0x97bdeefd60c9bf31,0xee8385a46404d010,0x42ffb44263b0a0]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x7ee6bf,0xfe3fff7c4ddff7dc,0x64f9b644bfeeffff,0x9ffe7f3ff3ff1fe0,0xfc7b20f0f9fe3f7b,0xf0e061038fdcc09,0x297f777feedffe46,0x1f707c1f8fe3feff,0xf3c3f07fa03e87c3,0xf8ff073e303c0101,0xf41cc600fee7cd1b,0xe9cf3f3f973e67c9,0x80f0c3c07ef20821,0xbc04d1d76d48e950]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x40300,0x400183202498404,0x660232480080808,0x1080207c021f9d00,0xc008c000e1ca3a74,0x8c2871831e00cc9,0x2d00044408987006,0x146842124e03c0c1,0xcda307fc402307e7,0xf0f0052fe0320181,0xf71ec74898842a11,0x85aab82fe43c67f0,0x60d0339871fb0e21,0xfe84cdd620f2c95c])) : Bits)
  | _ => 0

def samplesQ189 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x22622,0x1610211c00204188,0x2514824508b00620,0x1a200c4026322880,0xa40e24005c142008,0xb0006830200b02a,0x1328385290a45003,0x8080034c100320b0,0x10229c0104234a06,0x430807c815240846,0x1000c0a9281a024c,0x50e450a404303800,0x700c041868070011,0xc19524d89a121104]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x8c431,0x1812024420945690,0x30a5345184614305,0x2e8000140243228,0xf81208484ee42d41,0x450142ad0440dc84,0x726425d805301a86,0xc505004474058819,0x70c21920490b7008,0x820246628038909a,0x1408512f3d143661,0x2c2994008186958,0x24161c0d21424024,0x82a9aee210d40210]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x1048d8,0x8a0c04105853840,0xd8483c82d242c10b,0x2403021810c05204,0x5950423a82405923,0xd044486090d74511,0xc8528529094aa788,0x422b04820d289808,0xc4c84098c884b118,0x20612020429a4131,0x29383302d74138b0,0xa412291aa24802f4,0x8c427083002822a0,0x122adb0224a5400a]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x20b0f0,0x802a63844cc65881,0xc1fbc399fc0a5301,0x62360f896a46c029,0x1650c50b0c6e981,0x51cc5ab1384ed2b7,0x2df4caa6acd0929a,0xd2710c4616398918,0x5f29e12931288370,0xc422689285829912,0x7b69572bff840c87,0x173da274e0d8ae51,0xa44655a9204d6805,0x442ffb40263a080]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x11940,0x40c8888294000822,0x8a02492a63060850,0x2002619418818107,0xa1432320014004,0x3074290050060340,0x84934205620b8008,0xa20541380a84042,0x5052094b0c400e0,0x3451181062404600,0x29a20a10c2e1c112,0xa9090609b0440200,0x80e0c28012301ac2,0x1c4051056508e840]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x7bfcfb,0xf9bff7dffdf77ffb,0xf9ffffdbfe7fdf7f,0x7eff5fbbfbeef67d,0xfb77defefff7fdef,0xfffd7ffffedfffb7,0xfff6efffadfaff9f,0xdfff5fdfffbff9fb,0xfffbfbfbfbbff779,0xeee7eef7cfbbf9ff,0x7ffbffbfffd53ef7,0xb7ffbb7ffefcfffd,0xfcfeffbf7befefad,0xb6ebfff636f7ebde])) : Bits)
  | _ => 0

def compactPerms189 : Array (List Nat) := ([[], [80, 50]] : List (List Nat)).toArray

def compactDomains189 : Array (Sig × Nat) := ([(subcube 16 0, 7)] : List (Sig × Nat)).toArray

def compactWords189 : Nat → Nat
  | 0 => 0x13f
  | _ => 0

def compactCount189 (k : Nat) : Nat := match k with
  | 7 => 1
  | _ => 0

def compactPath189 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | _ => 0

def compactLive189 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits compactWords189 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs189 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits compactWords189 (7 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords189 (6 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket189 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP191 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x4530fe3dcc6cf8ff,0xd5b2e86ff25fef7,0xa722e037fd33cf45,0x19e3ab853cf8ad1,0x603ffef4b380a46,0x46964814c5bb41b,0x3801e00dcb1ce3a3,0x669898643fc04140,0x82380e006a013e4f,0xcee674dd7d7982b8,0xcfd45525e795f9c6,0xe93e77c640301502,0x918f8dc1c7d99907,0x1c5e03ce0f8542e2,0x8042e4502437274,0xdb4b4d2a54958824]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x5fc70feaca3fd598,0xfeb4a05fc7c338fc,0xeb9c07eb7238fbca,0x53ffd50ffd3db213,0xb8700638f08007b8,0x1883986e26e5189f,0x70020ff635ba8040,0xb6e4003f80782a3,0x64800090003617df,0xbbb79e66d50feb13,0xf8fa61ff3ce9c47d,0xa06f7aa0b9ee1a18,0xe67880b801a81f70,0x7220ca791380801c,0x1039d10a086c26ef,0x96c5eac125242118]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xa17937c333cea8e7,0xf2a4dfe1a525c708,0xdbdf3843e93b35ff,0xfe1a3ff7ae2065ee,0x4404f800a0d5f014,0x204e1f1eb986e4a0,0xcfdc100104433c58,0x30307077c0180c1c,0x940716010c83be9,0xefffbf697476ffcc,0x8c3bfe01f9ff2939,0xd7882b39c6040ffd,0x3a7172000427e007,0xe3af3c040c780100,0x5c200a034fd7f3c,0xe0b20303ba285240]))
  | 3 => (BitVec.ofNat _ (limbs64 [0xfaffc8f97db10747,0x3d772ba607fac78f,0x7c2ffc7c7fc4c1f0,0x5e60de38d00e0489,0x8059f03d011bf1e0,0x3ff1e0b109281b40,0x9142400652441faf,0xc4c19f8800e07000,0x318e038a017fbf,0x3ffdeb9313baf1af,0x1fc3abdb8eae8f9e,0x72b38cce463be060,0x3d71f9c6063e,0x1c0c34717c0448e3,0xe0002051407eddcb,0x8551a41652c80027]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xb94ef13cb252ff78,0xcd6cdd7ef8daf907,0xd8d2dfb782cd36ba,0xa1e1257753c07024,0xf9a303d2b5260bb9,0xc4149b4152744064,0x26a1bf8a289b03a0,0x986687983c070283,0x1406008c0530ad7d,0xfddb7b2eeaa47cf7,0x213784c4d726f7e6,0x9dfdc736380c7a83,0x2d8e4c3fba207ec0,0x8391c3b08002b418,0x123810088133dbba,0x3c249289c0d70590]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x5eb80fd735bf2a18,0xf3cb5059383c38fb,0x146107dc8dc6fc35,0xadffeacfaef24d12,0x478c05c70e400c47,0xe3026790869ae71f,0x4ffc0ff9c1a57c1c,0xb912003c7000158,0x8348706070081fb6,0x554fdd96aacf1453,0xf6ed9bfa3b513a7b,0x5e50fd5939d185e4,0xd877728602560088,0x6dc0c986e3f90300,0xc060e841216a5d3,0x48bc1cf48d3a8a40]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xa687f006cfc157a7,0x29bf7b95adf0770,0x27fdfb8816ff0a0f,0xfe05c1c02d919b6c,0x3bfe08005eeff40b,0xdbbc006ef1010be0,0x803ff070be60c057,0xf50f6ffc0038bc24,0x7887811f85c6e0f2,0xf238e4f98fd10f6c,0x730c7e3e405a5681,0x2fc7900187c3e01f,0x4780834e7c19e1f9,0x8073340bf0023c05,0xe3c1c132ed898805,0x230a717c2b43748b]))
  | _ => 0

def samplesQ191 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x4449c60100625000,0xec75a000100,0x8302207414080545,0x1840540021010d3,0x4207001014120a52,0x242484600cdd50a4,0x8822000ccee02004,0xa2a8e81000204ea0,0x8c88006005092241,0xc0e2144d09008298,0x431055242194d080,0xc136230040340500,0xab810081c0019900,0x800e0bca00034002,0x120631152ac13234,0x5b03412814850804]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x45108a958b58580,0x40c1844145086a54,0x680e2ae113108012,0x452810527448c42,0x90904a017094880e,0x141a924812c0988,0x840042109a98911,0x9028a0113405005,0x2dcc0a02909a1386,0x9ab59440d408c911,0xd8aa219028014035,0x20235a806b6a0228,0x2259808801820630,0x26220a082680014e,0x8810912e106c2467,0x92c1a8c124200018]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xc796b0131bf1022,0xd68004c3c840c70d,0x21823867b278004b,0x908037c002004510,0x48062a80410c4088,0xa47b000211e18820,0x1008820f914704d0,0x9b1412088ca7487,0xee8820241909f3c9,0xeefa3c2864322c8c,0x813600151b90921,0x528828a0462e0b98,0x3a8156809006c803,0xe0071a980c211100,0x48a006b44f97e3c,0xe0900303b2001040]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x3a1229081c95094e,0x7cd5110881e84a97,0x2c854889e3d01092,0xd4020a199408c108,0x1140504c8308a020,0x4a1a2a045200210a,0x1304453210160961,0x50151281555e910d,0x3050e28cb8125dbe,0x3f1dea8012325126,0x4c088d9842a0c1e,0x320184ea0a4b22a8,0x123d1230c2421e,0x3480703124940870,0xc4108440453ecdcb,0x8450a41242480022]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xa90e631006023a1a,0x1424509a88600181,0x1181c40ca0493241,0x90800670d08a3089,0xf482494846044d0,0x820006134600c044,0x6108d20022104480,0xb04c11308c0a0498,0x9031a1b469016c79,0x654a6b2620043422,0x1050404d606b742,0x84d8812e00047181,0xc8614369060c80a,0x8194d0900026da10,0x108c00808113db98,0x2c240208c0d60500]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x2002004c0c000908,0x1471008213c18b0,0x845418809005030,0xc2a40139c662a04,0x84b8144b22e03424,0x49800191a0002443,0x62c431902008c028,0x4442008c41000008,0x10528681a0760c36,0x1105c19282cd0041,0xb46c8a4a0a402248,0xc40541b18c02060,0x32001202d00298,0xc8040046198862c,0x68404680900681c3,0x2c1cd4093a8200]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x80100280000001,0x8202000030000,0x30000000060800,0x2201000000300204,0x21000200021200,0x8400c028101401,0x80a220804400200c,0x600200c00010040,0x100002000000,0x1109c10240,0x2200122200400080,0x904000080008006,0x400000400c082040,0x40040090080400,0x224062102a000000,0x10a502409016081]))
  | _ => 0

def compactPerms191 : Array (List Nat) := ([[], [65], [80, 50], [80, 65, 50]] : List (List Nat)).toArray

def compactDomains191 : Array (Sig × Nat) := ([(subcube 1 0, 8), (subcube 2 0, 8), (subcube 4 0, 8), (subcube 8 0, 8), (subcube 16 0, 8), (subcube 32 0, 8)] : List (Sig × Nat)).toArray

def compactWords191 : Nat → Nat
  | 0 => 0x6163447f
  | _ => 0

def compactCount191 (k : Nat) : Nat := match k with
  | 9 => 1
  | _ => 0

def compactPath191 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => 0
  | _ => 0

def compactLive191 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => readCompactBits compactWords191 (0 + 7*i) 7
  | _ => 0

def compactPoolIDs191 (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let v := readCompactBits compactWords191 (25 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords191 (7 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | _ => []

def compactBucket191 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP254 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0xf556833ff32e49a9,0x19ed90fabf7d4543,0xce7357ece837fc12,0xdf5d1666f04efee,0xc5803e7ba0f3800f,0xc3060f79dd88534c,0xc0207c4e7101b873,0x39be8000bae7800f,0xe20001a300503e0b,0xe75ee5a7d1713fe9,0x1b85cd9fc3f68bf6,0x2699aa1597c01f4,0xe019c521e400c8c6,0xd03f9630e3c20803,0x5c060fe160292266,0xf9c3d4a344628a30]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x28995c195ff3fe26,0x207ffc7e8b53024,0xd7ffc5d7ac078bf,0xfe1b69dc01dffaf9,0xa598003ffe125f0,0x3ba89f3ec601db,0x3dc0800104fec794,0xd400c0bffd180670,0xd803e4807a9802e,0x53ebd7bcb013f87d,0xa0ff70e17ee223bd,0x308feddb06012acb,0xd203fa9004bfb028,0x7f0e48d037d003c,0x8058d00e82cd64d3,0x84b81c05e9d15085]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x7f5bbfe2a083d7d7,0x6ff9c707d0bac7fc,0xf2bc87da2fe8875e,0x309ea15ff6fa0d01,0xfc23602c0a1cd9f7,0x83c4508061055c20,0x161f01b1d32003e8,0x82493f5f00007980,0x78c0143806404f,0xfdcffbf6abcd8b71,0x7de0fafe9cbebc31,0xd5b12f0ca60e5403,0xca40f4f83583f06,0x59c01b4dec80f080,0x23a120000d0f78fe,0xbb0ccb181a10044a]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xafe44fc4befc27f8,0x913e07f8003bf83f,0xffc0085fd4ff07e1,0x3f5ffea3f927f01e,0x3eafd014620e07,0xfc00701f807ae233,0xe80ffe406840fc00,0x78e1fe00007000e,0x10070002c000399f,0x9fbcdb5fbcee147e,0xbe2e7b182f3d7fc9,0xeafe30f0798896dc,0xf4a1009bbe0c03f,0xa000e1f2d0200f40,0x18000f10501edf94,0xa511a5c193ac2320]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xdaa9733f4c2e4e56,0xe7d268fabf46ba83,0x318ca7b31737fbed,0xcdea2e9a6efceff1,0x3a401184408c7008,0x3cf98f6622082c8f,0x3fd07c4e0e81478c,0xc1b16000ba000600,0x580064000a80007,0xfeb7bdff6e7edf96,0xdb55b67ff3c944f7,0xfd565a5ed973e92b,0x1015dad058003701,0x2e3f68301c1d0004,0x800800020206bf7d,0x70dd22bea4541080]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xd766a0d95fddb1d9,0xfc07ff3d57cacfd8,0xd7ffba2850878bf,0xf3e4962191db1506,0xf5a64003ff1eda00,0x3ba7e0c13181d4,0xc23f03b084ff386b,0x2a40c0bf47e00180,0xa7839b40756402d,0xabf32e7b4f93e782,0x44fa8f017d1dd34a,0xcf0ff724a0812b34,0x2de2256e04bf4fd0,0x7cf1b420362f03b,0x6057200d0102d72b,0x4a661b4611aa0c45]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xc0bffce6a151b82f,0xfef838056fc53fff,0xf2837825fbdf8740,0xc2215ffd9e2112c0,0x3dddffc010127f8,0x7fc450001ef7be20,0x1e083bfbb1e0017,0x7c773f404418f871,0xf007c009f80187d0,0x7c7d7ec957ac608f,0xe71b05e68043fc0e,0x3ff0c50306f6d400,0xf3fc20b67b4700f9,0xf800048f3c8007c0,0x7a0d0f0bcf18989,0x562260786e0de11a]))
  | _ => 0

def samplesQ254 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0x502800811020212,0x21a982690d090400,0x1405024828525400,0x2500a04444645,0x1100248948350480,0x4040020a0a045484,0x4424208400005125,0x122888860402044,0x8554208028831223,0x614641a000310249,0x9054095009080e6,0x298a004a5c0051,0x6001450024001206,0x509a940005024005,0xd440440e2092062,0x38c0d0a140400830]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x2091011800608686,0x18406c5a8088400,0x4d13040400c00594,0x8001484080c10415,0x320420099100442,0x5010480044545184,0x28210005408c894,0x121048450ca604d,0x800002104286016a,0x41c852241001082c,0x208860811a220285,0x108cac80060d00c8,0xc4021280018c3020,0x1b0108443080214,0x4d4208e88d40c2,0x84881c01c9004084]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x909a72824a58393,0x218cc24b991a9629,0xd535000c0a42970c,0x1492cb4980414c50,0x62214521114402a1,0x9884b0c48490511,0x924528a654209151,0x4050a0a285ea2c4,0x91104692cec2126b,0x75cedbb680888b51,0x30a0185e103aa831,0x943124880a1e0449,0x4c824b408b181a22,0x1892385ce5046081,0x11890448099f68f6,0xb90cc9100a100408]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x2412d00ae2c80a0,0x41448009070b01b,0x4190889492298904,0x3e04ae60a1032808,0x240d0364a0406a4a,0x94912045a4190038,0xb0829410202c08c8,0x240c4505120a0780,0x1a89ca3b4200084c,0x96889a5fb0c01036,0x142a2b002f0d2f00,0x60d610b82100160c,0x60a024199088130,0x2a01617640281b98,0x500043021116de94,0x8511054093a42200]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x5160e44466046050,0x764ae81813d41049,0x308c91891e0fb801,0x164aa238622ae8ea,0x5884a09c42a1b839,0x94ea122a280a029,0x4c618a62a2020428,0xcadac2620f200a90,0x31bb59a21808fe15,0xbe37addb6a7ed582,0x8b45926ae1c04452,0xad40425ab9308e27,0x44c152c8010743,0x3e0720520c072840,0xacb210221202bf3d,0x705522be24541000]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xd04040c542102008,0x1640090040c44940,0xc0d08215090823,0x43602020203a2102,0xcca10402682c000,0x840310c101022240,0x201006110b850400,0x72d0212105201832,0x6089082000284894,0x8a3124490f026480,0x4452850044051108,0x4a021114a100ab24,0x144001e402341c0,0x2241020200401108,0xe012211504609709,0x4222024610aa0041]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x9004504640003800,0x9a401000008400c4,0x200302044000041,0x40008418281020,0x42901004021010,0x490a001828240,0x810004189830000,0x9800204001210810,0x2000004401184010,0x831240045042000,0xc210042080405008,0x30041018080c820,0x1074203240410048,0x8000000110810040,0x20303504600109,0x4222200824098102]))
  | _ => 0

def compactPerms254 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains254 : Array (Sig × Nat) := ([(subcube 8 0, 8)] : List (Sig × Nat)).toArray

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

def samplesP123 : Nat → Bits
  | 0 => ~~~((BitVec.ofNat _ (limbs64 [0x108200,0x26211e214040,0x2450322a40001804,0x8002800d2004e08,0x45e424720f0bf00e,0x88c0fc5170010370,0x8658001060702f41,0x83800e86006e00f3,0x80407ec08facf486,0x421bf911a978041,0x1727f19f18643989,0xb23826064be0e805,0xf007d9e3f22f9c7a,0xec02bd4aa8f42476])) : Bits)
  | 1 => (BitVec.ofNat _ (limbs64 [0x7bf4df,0xf72ffff9eec3ff65,0x85e19e9b4fff7fff,0x7f9f6b1fd799ff3c,0xf5627d1fff0e3aee,0x8c7fdcd470d20750,0x8247ed3dfffefbf1,0xd6793f83afeb4bf7,0xb3ee73d1c22cf48e,0x80fb87f5fa8391c1,0x1120711f7cce7ffd,0x776e711e42e9e44d,0x38a639f137e09c3a,0xec001f6b3a327452]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x202c30,0x20e001c00c17238,0x976d0ccdd0002400,0x30e0b1e01e101e0,0x800600fee122fec,0xf7c8ff80cf28756,0xfbc0412890000021,0x887c3e00ae817884,0x4038c03e0042f8ae,0xe0fb87fdfc02fbfd,0xf9e0717f808b2646,0xa05601c46ede778,0xb4c27e039e0bc3b,0xfffd10b66632ffd2])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x7e2baf,0xfefe2fe57d7df2b8,0xd30c31290ff8fdf5,0xfffefffe39e36ee8,0x5de4bb726efbd02d,0x78dc8da8ec308000,0x8207fffbf37bff61,0xfb84ff77be16fcbf,0xc5b840ae80ee0ce4,0x2429bf91796f87a1,0x1100010e3ffda7c7,0xbbbb7fb577e56872,0x77443a00fa008032,0x6c00f5b86c6db012]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x779e0f,0xcfdff6df9ba343da,0xa65144440ffffe7e,0x9f6fbc1fe665c7c3,0x6add66efbff02550,0xb602a7b00ed0602,0x1807d3fffffde4cf,0xa9fe3efc6fffb3c7,0xca518c1e3d50fb0f,0x40f407898412687c,0x84000607fef7bba,0xfa95eedf8af08730,0x8159c5ee39c02001,0x1348ff96a3b28a00]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x7def3f,0xfbffff3e16fd7c7f,0x3c7e2aeedfffbf8f,0xebfffbe0dbfe19ff,0x8fbfe4ffcf03ef8e,0x8780f7511f03fb74,0x65df7ffefcf73f3f,0x8fffce8ed0ed7cf8,0x7c60fe600f83f0b2,0xff03f87e1e94fa40,0xe6a7f091dbf3bc4f,0x8e7da66e4d0efb8d,0xca0fc7e3c02f1c48,0x80b7b8c6c4d465e4]))
  | _ => 0

def samplesQ123 : Nat → Bits
  | 0 => ~~~((BitVec.ofNat _ (limbs64 [0x6f7dff,0xbfef5dfefbdfbfbf,0xdfafffddfddfdff7,0xfbefe3fff1ffaff7,0xb5dbbf7dfff7dfff,0xff3ffbffeffeff9f,0xfff779df7f77ef7f,0xf3fffff6ff7f7ff3,0xffdf7ebf7faffbc4,0xfbddbfeefbff7bff,0xefffff7effe7f9f9,0xbfbdfe77fbefebf7,0xfbf7dffff3ffbff1,0xeb3bffcfaffcacfe])) : Bits)
  | 1 => (BitVec.ofNat _ (limbs64 [0x40b22,0x854030211141018,0x121a212485241041,0x402a0d480aa80801,0x58a802a404414205,0x23080029080850a0,0x3112a504a9c08a04,0x50d00a2024404202,0x301284c014404523,0x8840d22928c08498,0x80052a04540052a4,0x6464311a02484045,0xa099440164091d,0x24440b631a224042]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x202c30,0x9247000c00c51628,0x60d08cdd9800284,0x51a3826d00d00046,0x108282527424364,0xad09839801609312,0xd18630804e62c254,0x929253a405101450,0x1a84182464096104,0xa511b204a6020a9,0xa89233476401931,0x35309c2190420813,0x90328856525609a0,0x2102cf4989480028]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x1d454,0x301b85822420d03,0x2ce14e527a494190,0xa30122035454730a,0x8205e502f12205a2,0x9007315223c60d4e,0x4c6d5a79421b1503,0xa008f090930a3830,0x898d0b32a19510dc,0x452b009446190a64,0x26389162abdd8543,0x8b9a4aa471212130,0xb2504220f011e422,0x1892f498644db010]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x861f1,0x1d220928604c350d,0x5926b399f49b08b0,0x61670124302f2965,0x31c28e115202cbac,0xf11d511c65443c95,0xa6f741973525630e,0x91b856f01f281911,0xd8935494528828c0,0xe21c890aa0b7324c,0x620bf72e7fe76898,0x9285e45311e02311,0x9171caec50e2a0d1,0x8109ff86a3b08800]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x210c8,0x4201040a8008181,0xc180d40020518412,0x2800400260030220,0xa043011080341090,0x10241800a0140c09,0xa01084a10142122,0xd0012520d0880,0x8448420203041800,0x21040086800e1806,0x2140900209a2a048,0x80902440924a180,0x4844462100010440,0x8819308404942484]))
  | _ => 0

def compactPerms123 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains123 : Array (Sig × Nat) := ([(subcube 32 0, 7)] : List (Sig × Nat)).toArray

def compactWords123 : Nat → Nat
  | 0 => 0x13f
  | _ => 0

def compactCount123 (k : Nat) : Nat := match k with
  | 7 => 1
  | _ => 0

def compactPath123 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | _ => 0

def compactLive123 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits compactWords123 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs123 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits compactWords123 (7 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords123 (6 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket123 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP127 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x3bd07b6fff89f003,0x7515dff6863f9704,0xebb3bf81aa340f9d,0xef1b80dfe201b481,0xf4eee4449146606c,0x90f0adceed3b0086,0x13775ae082e729be,0x7001de70f40530e1,0x80780c401be62ced,0xfed41dbcb831e7c6,0xb043923d1ff387a7,0x93b1f057064d2825,0x7c3d1533b0fb0193,0x8038183c8dc21441,0xe11010d9f5826c8e,0x7b6453411b19ac24]))
  | 1 => (BitVec.ofNat _ (limbs64 [0xee1602ff8bd461ff,0x8e9f3da9382ff9d8,0x1e7e5c122fdd51fe,0x5a80dfedcd621e7a,0x4939e306e010fb3,0xe1bd0a00ff16100,0xedb90ed7050056c9,0x1fe1870a1a4400,0x3820103a357fef3,0x337787cd0ffc5f27,0xe97e83e7ae1cfd22,0xc53eaa20bdc1d506,0x1e1482e405691e0,0xfe4a1e771c4081a,0xe26e90200c437bd,0xc69c3d24c22d4288]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xc4687d70e1fe1f8c,0xa17e6fbffc0417d,0xe47d5bfe553eb21d,0x74fd7e10188529be,0xfb10182503b9d803,0xe9061f30308c9d07,0x1042e11878092301,0xaffe000801808b00,0x7c01b28c46fb3f7b,0xf7bed0efd61fa5f9,0x8e0e7f4e199f59e4,0xece4cda100b27ac3,0x8fc6a1505f04600f,0x7c071840fe3803a4,0xc8062408eceed7,0x583304a368e21043]))
  | 3 => (BitVec.ofNat _ (limbs64 [0xf87f9f800e1f9e0f,0xffe898b41fd17ef2,0x57801b1ff85ffc62,0x7f7ea3e0e0ffc640,0xf303e3de7cc0603c,0x3a46007c0120ef8,0x18011203ff48c02,0x33e00070806000de,0x744070139fefff,0xed2bea09eadf19be,0x4ff2bc77f2a21edf,0x16c730d9470400f8,0x1000fe8d83587e63,0x7038fe070c03e401,0xd101001082ff4b79,0xc48598d91d020134]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x3baf8490f069eff3,0x7aeaff49663e177b,0x73b3a461d5abefe3,0x909b7cdf1d004301,0x8ed1843ee461053,0x6cc8d2091224f079,0xee8824df42e6d642,0x4c01d0060a1a4000,0x2000380fddbef,0xcfdfeeb2b52ffa09,0xbfb15dbaf34fe75b,0xeb49cf56f98b571a,0x823a14cdaca481e0,0x800707bb02000800,0xc20e902007bd8e7,0xb3826a2c75d50088]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xd5e9e2ff742261fc,0xf1602256c1efeea7,0x9dcde3ec2fe2a1ff,0xa564df32329c1984,0x47c618891b88fcc,0xf11b2f500fce9e00,0xee468e28f8185934,0x801e3e0005843b01,0xc018e8043afd19e,0xbbef77724fc25cd7,0x56fd63d84de0fad9,0x393f5588ba30aac5,0xe1dea22000a96e1c,0xfdb41d881f81064,0x1814e11837b36a,0xa95ba156a232b040]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x797fd0f1ff79e70,0x85ff410ff9d0a88f,0xa84ee4ffd2c15e00,0x8be7212c077ae07f,0xb0007bb003fb780,0x166500fff04163ff,0x103df107851ba0fd,0xdfe021897061843e,0xf38c713c2d78f714,0x5cf9395771e0a278,0x718dec81e47d203c,0x7eda022e407e8538,0x7e014bd27f039e1c,0xf3c0e6007205e39a,0x32c7020c67199510,0x3468c69a84cc4f13]))
  | _ => 0

def samplesQ127 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x7d0061001801000,0x502b80280008109,0x4780008002341d80,0x1001001c02019d40,0x1042592c00010,0x9077b20122090181,0x3084400800a0a42,0x98a044021,0x9c00c70620441,0x96140c0410314040,0xb040020d12110183,0xb0c02706802826,0x8c05006190030180,0x187c00001400,0x2320150d84802c86,0x1b2050000b092804]))
  | 1 => (BitVec.ofNat _ (limbs64 [0xae488aaa881414d0,0x248420a102a43058,0x4656018022009054,0xa20491246880a54,0x42802aa481004235,0x20417092044824a0,0x40544c4a118140c3,0x9088ca9c0084a15,0x415802114743a6b1,0x312400c908984d05,0x286882418c107422,0x4516a02195401442,0x164482050522460,0x268c806025448028,0x879441030cc4271c,0xc61c1d0442280208]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x6ea1ef008c01d85,0x4b62c09ce00520d,0x46b108d482041681,0x546001141480f108,0x2aa0064120d24820,0x1206c43000500312,0x23c08839084b4b80,0x188441eb821c6021,0x840c927456732f69,0xd63600a582058160,0x8c0a290e088b40e4,0xe0e4282305a05a0b,0x8606256099026081,0x6c0088696c101120,0x208d261680e86e97,0x583104a168800042]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x80e88a22c4ea49f,0xa2e404315a851610,0x15390d9148c204,0x27288b4090306011,0x5808d0c008082b05,0x420801229510ca28,0x489081b214a00110,0x314a94a604a90244,0xd1637510795abbe,0x612b8008c2ca10ae,0x332b022c0a01e54,0x641389011041258,0x248be0403183423,0x24a9c283244ac008,0xc8094250027e4379,0xc48588c910020120]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x1082241160c3e005,0x9a224d50c85302a1,0x3081ec04d5056682,0x159826c5a813048b,0x2425500a3612b080,0xcdb8064172a15813,0x340901818c540404,0xe0a4720213e485e2,0x14869c4498bc594e,0xcedbce303426b208,0x15815db0730e8309,0xaa084bd248830b08,0xa618264ca12c0285,0x80430f8902122dc2,0x8203828223bd8e3,0x3182622835d50080]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x4801e0072026a030,0xf200027001df0890,0x200c67001902e02e,0x83083e42692c0284,0x1518a81209091140,0x258001c881a2a408,0x80612404130b419,0xc442260030a0034e,0x33b20403818cd096,0x29c973524d400c93,0x429440d00560a810,0x11030590780201c0,0x60c80a0400b80e2c,0x81d9028080cc4844,0x5452006019179168,0xa04aa15680329000]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x210112000200,0x1009004420520082,0xa800442200802002,0x6242101060002,0x1140018040180c0,0x800000840021000,0x140312004004b00c,0x420021010021102,0x1080008080085000,0x8c0310221002210,0x4005040020440008,0x18080108481a8100,0x3000009204208214,0x9040200010002086,0x1042080031019000,0x2040021284444411]))
  | _ => 0

def compactPerms127 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains127 : Array (Sig × Nat) := ([(subcube 4 0, 8)] : List (Sig × Nat)).toArray

def compactWords127 : Nat → Nat
  | 0 => 0x27f
  | _ => 0

def compactCount127 (k : Nat) : Nat := match k with
  | 8 => 1
  | _ => 0

def compactPath127 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => 0
  | _ => 0

def compactLive127 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => readCompactBits compactWords127 (0 + 7*i) 7
  | _ => 0

def compactPoolIDs127 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let v := readCompactBits compactWords127 (8 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords127 (7 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket127 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP255 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x15d3a272ec264c1a,0xd2e7003c050020,0xa323850403c00030,0x9000143f5c1938ba,0x5f387b1aad067516,0xfb1b513025ea33e9,0x627052a627393792,0x31bfb1fc2ad8259f,0x979c3b055a800c8,0x18b240188136e1ba,0x28a7016c887ae80a,0x32827801c43a00f3,0x806f050a0883c101,0x821ca16891280,0xa7490b4799e45346,0x88a452a2c584c110]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x68046dbd43800000,0x17d41887c00a80df,0x450000034048005,0xee01acff8fdbd,0xe46e356387f301af,0x2b203ffea841bf11,0x4bc9dc3bfd01ccf9,0xa998564be7480837,0xa2a1f52a204597bc,0x1da9c086480f0a,0x91043d1000299914,0x3e68007f22c0629e,0x478e100400341e02,0x6075c224280208c9,0x18f3afc531c0dea,0x4503224164502860]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xa0e080c0034c0daf,0xff09003800606700,0x188c000bc81301ca,0x41e100b7e65d6f5b,0x75fd77e9df2b2413,0xaa7dec17eeac21d6,0x9f0e47c04cef99e2,0x932516a6d6a981c4,0x368f19cda2606011,0x224757a103887e55,0x44690010df85060b,0x4001efe0389b1b01,0x6f0e80007480014,0x86820c11801461eb,0x2d5d97c5a0538209,0x480db90d10290205]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x170b13001817f255,0xe020074023901800,0x3783003a81e00,0x9610113cbfeeafb1,0xfcffeaf54aacd2f0,0x25ae54d70d1dc5bf,0x408f257d95662ebd,0x9a516890e8e692d9,0xcb0a1e70d83260e6,0x4d00060e28018001,0xfa92f067262a07e0,0xc2c6381c35c991c,0x596004f22003a1e8,0x9002008446080fb,0xd456f89c4624a1a1,0xb05455301000119a]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x22c418d0821b3e0,0xd20007000a00d0,0x440002c000046000,0x280e0a67ab96e6df,0xdb75cbdefee99d6a,0xd4cb0a27d7e7ca0a,0x3e7f289822aec72d,0x565ecebb3a374d7e,0xf532238f51879830,0x9555381752c611a4,0x281836eb70511001,0xfd5014003825e4ec,0x20100205d0001802,0x1074120021000476,0xfcf1a3933a011494,0x5621c43caf020c40]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x80046e42b4580000,0x1706e00000056020,0x3ac0400c803003a,0x4001001d3fe7d2e6,0xbad3bd7f77dceb2d,0xd4d49fc95251bce5,0xc9b6a37bdad1cb46,0x4587a90bcdb7f228,0x5c65f6958e159743,0xe20ad62085b10eb5,0x46440a80005266e0,0x197807edd006261,0xb80ee80800c80001,0x800a01d0100c1035,0xdba6ed3a8899e412,0xa5da8a4192850200]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x485a901ae5e040bd,0xe82d18905c001800,0xa810f90f346809c5,0x6b0848bf1ab5f44,0x2b82de8ff0d0bac5,0x4267a2e810b24256,0xb4e1b8044bd6701d,0x6ce0b765110e7e80,0x3fdeac42299a0809,0x3ae8a84e7830f042,0x9339c118d784d1f4,0x8083939e03448400,0x69111f00f346414,0x69000c0682818216,0x4aaa542344ca380d,0x320a048e6840f085]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xffb11c25129bbf42,0x828006883f0870f,0x504002f00010f600,0x29406b605077916f,0x878f84b439574ed8,0x1d90e108fb1e5c28,0xb510dfc7b0183042,0xee6a49541551ff63,0xc0d4484006486f06,0xc5a001f17c4f0048,0x5c2ce872984281f,0xc37c0c0004a31d02,0xf9010201f00002e8,0x1681d02149726d0c,0x3230446825224a70,0xbf029d20b3a042a]))
  | _ => 0

def samplesQ255 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x29222a80a8a0108,0x200050606a8020,0x1440840000430800,0x28a190234410081a,0x138130085021510,0x13010030244a1068,0x26052a620011192,0x301a10340280251b,0x9818021a800d0,0x24008828e6012,0xc00648000c00a,0x32000400001a02f2,0x8000030a00004502,0x100a2222d4131180,0x2149034199601340,0x8a012a045048010]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x444081909828081,0xc40ca1071000444,0x14c8560812c01208,0x305209a47680da8,0xe42c30610502000b,0x282010948840b501,0x948143141010818,0x9881003a5480011,0xa2a0d5202024a5ac,0x122c002080b18,0x9004041080288240,0xc28013462820282,0xa2a104000510f51,0x40208221380500c9,0x10e1a5c511c01aa,0x501220140002060]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x540ad012006480,0x8a101e1a632204ec,0x1640850040612088,0x8e2119b3c6582f1b,0x553d53818f010402,0x8a284402c48c0150,0x120c4400444c81a2,0x810104a604a880c4,0x308b182820a060b5,0x55182038a3014,0x4c2c0021c3008603,0x10002f60020b0aa6,0x660400882404010,0xca120809ac4041ea,0x255d13c5a0508009,0x4805b10800080204]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x52000449004d001,0x45424a2e81042c44,0xc0091010d0a4639c,0x8204219c8b6ca7a1,0xfc45e0f14aa40040,0x240c44c509050093,0x400301198560042c,0x8a016000e8649080,0xc3020a389000a126,0x901128620001221,0x7a801083060a0341,0x40c61254b00b80c,0x4a22246020119060,0x882088880040c47b,0x9416b89c4204a0a1,0x9044411010001108]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x42a0012420642700,0xa216200a04227820,0x481788714435a0b0,0x88221525a894e213,0x1b51cb9edae91160,0xc003082351a1420a,0x1435288022aec605,0x52164e880a03046c,0x5510208bd0821010,0x550580300d230a0,0x4a0832a902130023,0x9014b402182cec24,0x104616e3841002,0x21c001201808436,0xfcd1a1832a011404,0x5220c43ca6020800]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x8909d501c5601062,0x410d60800c102901,0x402d38d735840610,0x405e604c39a7d0e4,0xaac2ac7e70dce22d,0x44d49b481200ac84,0x4992214898904a40,0x484a90941155220,0x824460596139300,0x83608e0010310620,0x12405880005e20e4,0x51f900ec800a401,0x180638241088aa2d,0x208040d0010c0215,0xdaa2ec3a00896412,0xa55a084192810000]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xe008d40060100230,0x2009218004900313,0x124084504000002,0x4012024030835044,0x2820c0e3040aa84,0x42a20800304204,0xa48088000a022001,0x4060834010024800,0xc5020410c121000,0xb2e8880050118000,0x51c90010941034,0x92908200400400,0x800010490c2004,0x2104140400a82a04,0x4aa0442204820804,0x220a040628404081]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x280320000418005a,0x21008100110101,0x2020000408080041,0x5010004010031044,0x82040020104890,0x1190210022120820,0xa000824610103040,0x2460005010102b02,0x44004004500800,0xc22080301c010040,0x142480028040804,0x4042000004000100,0x2101090018000008,0x1180744440323800,0x220442004224a50,0x9008c209300402]))
  | _ => 0

def compactPerms255 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains255 : Array (Sig × Nat) := ([(subcube 2 0, 10), (subcube 4 0, 10), (subcube 8 0, 10), (subcube 16 0, 10), (subcube 32 0, 10), (subcube 64 0, 10), (subcube 1 0, 9), (subcube 128 0, 9)] : List (Sig × Nat)).toArray

def compactWords255 : Nat → Nat
  | 0 => (limbs64 [0x72,0x9c0ca86421b97530,0xfff40780fac688ff])
  | _ => 0

def compactCount255 (k : Nat) : Nat := match k with
  | 11 => 1
  | 10 => 1
  | _ => 0

def compactPath255 (k : Nat) (i : Nat) : Nat := match k with
  | 11 => 0
  | 10 => readCompactBits compactWords255 (40 + 12*i) 12
  | _ => 0

def compactLive255 (k : Nat) (i : Nat) : Nat := match k with
  | 11 => readCompactBits compactWords255 (0 + 8*i) 8
  | 10 => readCompactBits compactWords255 (52 + 9*i) 9
  | _ => 0

def compactPoolIDs255 (k : Nat) (i : Nat) : List Nat := match k with
  | 11 => let v := readCompactBits compactWords255 (32 + 8*i) 8
    let n := v >>> 4
    let bits := readCompactBits compactWords255 (8 + 3*(v &&& 15)) (3*n)
    compactIDsFromBits bits 3 n
  | 10 => let v := readCompactBits compactWords255 (117 + 8*i) 8
    let n := v >>> 4
    let bits := readCompactBits compactWords255 (61 + 4*(v &&& 15)) (4*n)
    compactIDsFromBits bits 4 n
  | _ => []

def compactBucket255 (k : Nat) (i : Nat) : List Nat := match k with
  | 10 => let d := readCompactBits compactWords255 (125 + 1*(i % 1)) 1
    let off := ((i/1 + d) % 1)
    let v := readCompactBits compactWords255 (126 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | _ => []

theorem compactHalves {test : Nat → Bool} {start n : Nat}
    (first : chartBlock test start (n / 2) = true)
    (last : chartBlock test (start + n / 2) (n - n / 2) = true) :
    chartBlock test start n = true := by
  have eq : n / 2 + (n - n / 2) = n := by omega
  simpa only [eq] using chartBlock_join first last

def grid172 : CompactGrid := (172, 3, samplesP172, samplesQ172)
def tab172 : CompactTable := (compactCount172, compactPath172, compactLive172, compactPoolIDs172, compactBucket172)
def check172 (k : Nat) := compactNode grid172 tab172 compactDomains172 compactPerms172 k
def sliceSpecs172 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains172 : ∀ d ∈ compactDomains172, Slice true (vars 172) (graphGoal 172) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs172)
  · simp
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs172 : properPairs (graphGoal 172) (asRow samplesP172) (asRow samplesQ172) :=
  compactPairs (g := grid172) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos172 : ∀ p ∈ compactPerms172, autoOK (graphGoal 172) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c172k3p0 : chartBlock (check172 3) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev172k3 : chartBlock (check172 3) 0 1 = true :=
  c172k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded172 : Impossible true (graphGoal 172) 3 (vars 172).toFinset := by
  apply compactRoot (g := grid172) (t := tab172) (dom := compactDomains172) (perms := compactPerms172) pairs172 domains172 autos172
  · intro k hk
    change k ≤ 3 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev172k3
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound172 : Lower true (vars 172) (graphGoal 172) 4 :=
  plain_low (hints := 538998016) (by decide +kernel) excluded172

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound169 : Lower true (vars 169) (graphGoal 169) 4 :=
  carry_of (old := 169) (rep := 172) (swaps := [32, 115]) (by decide +kernel) bound172

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound165 : Lower true (vars 165) (graphGoal 165) 4 :=
  carry_of (old := 165) (rep := 172) (swaps := [48, 117]) (by decide +kernel) bound172

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound141 : Lower true (vars 141) (graphGoal 141) 4 :=
  carry_of (old := 141) (rep := 172) (swaps := [80, 50]) (by decide +kernel) bound172

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound45 : Lower true (vars 45) (graphGoal 45) 4 :=
  carry_of (old := 45) (rep := 172) (swaps := [112, 82]) (by decide +kernel) bound172

def grid173 : CompactGrid := (173, 6, samplesP173, samplesQ173)
def tab173 : CompactTable := (compactCount173, compactPath173, compactLive173, compactPoolIDs173, compactBucket173)
def check173 (k : Nat) := compactNode grid173 tab173 compactDomains173 compactPerms173 k
def sliceSpecs173 : List SliceSpec := [(1, 0, 172, 0, 0, 4, 4), (4, 0, 169, 0, 0, 4, 4), (8, 0, 165, 0, 0, 4, 4), (32, 0, 141, 0, 0, 4, 4), (128, 0, 45, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains173 : ∀ d ∈ compactDomains173, Slice true (vars 173) (graphGoal 173) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(172, 4), (169, 4), (165, 4), (141, 4), (45, 4)]) (specs := sliceSpecs173)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact bound172
    · exact bound169
    · exact bound165
    · exact bound141
    · exact bound45
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs173 : properPairs (graphGoal 173) (asRow samplesP173) (asRow samplesQ173) :=
  compactPairs (g := grid173) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos173 : ∀ p ∈ compactPerms173, autoOK (graphGoal 173) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c173k4p0 : chartBlock (check173 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev173k4 : chartBlock (check173 4) 0 1 = true :=
  c173k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c173k5p0 : chartBlock (check173 5) 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev173k5 : chartBlock (check173 5) 0 2 = true :=
  c173k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c173k6p0 : chartBlock (check173 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev173k6 : chartBlock (check173 6) 0 1 = true :=
  c173k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded173 : Impossible true (graphGoal 173) 6 (vars 173).toFinset := by
  apply compactRoot (g := grid173) (t := tab173) (dom := compactDomains173) (perms := compactPerms173) pairs173 domains173 autos173
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev173k4
    · exact lev173k5
    · exact lev173k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound173 : Lower true (vars 173) (graphGoal 173) 7 :=
  plain_low (hints := 536872195) (by decide +kernel) excluded173

def grid73 : CompactGrid := (73, 3, samplesP73, samplesQ73)
def tab73 : CompactTable := (compactCount73, compactPath73, compactLive73, compactPoolIDs73, compactBucket73)
def check73 (k : Nat) := compactNode grid73 tab73 compactDomains73 compactPerms73 k
def sliceSpecs73 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains73 : ∀ d ∈ compactDomains73, Slice true (vars 73) (graphGoal 73) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs73)
  · simp
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs73 : properPairs (graphGoal 73) (asRow samplesP73) (asRow samplesQ73) :=
  compactPairs (g := grid73) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos73 : ∀ p ∈ compactPerms73, autoOK (graphGoal 73) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c73k3p0 : chartBlock (check73 3) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev73k3 : chartBlock (check73 3) 0 1 = true :=
  c73k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded73 : Impossible true (graphGoal 73) 3 (vars 73).toFinset := by
  apply compactRoot (g := grid73) (t := tab73) (dom := compactDomains73) (perms := compactPerms73) pairs73 domains73 autos73
  · intro k hk
    change k ≤ 3 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev73k3
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound73 : Lower true (vars 73) (graphGoal 73) 4 :=
  plain_low (hints := 3) (by decide +kernel) excluded73

def grid201 : CompactGrid := (201, 4, samplesP201, samplesQ201)
def tab201 : CompactTable := (compactCount201, compactPath201, compactLive201, compactPoolIDs201, compactBucket201)
def check201 (k : Nat) := compactNode grid201 tab201 compactDomains201 compactPerms201 k
def sliceSpecs201 : List SliceSpec := [(128, 0, 73, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains201 : ∀ d ∈ compactDomains201, Slice true (vars 201) (graphGoal 201) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(73, 4)]) (specs := sliceSpecs201)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound73
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs201 : properPairs (graphGoal 201) (asRow samplesP201) (asRow samplesQ201) :=
  compactPairs (g := grid201) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos201 : ∀ p ∈ compactPerms201, autoOK (graphGoal 201) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c201k4p0 : chartBlock (check201 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev201k4 : chartBlock (check201 4) 0 1 = true :=
  c201k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded201 : Impossible true (graphGoal 201) 4 (vars 201).toFinset := by
  apply compactRoot (g := grid201) (t := tab201) (dom := compactDomains201) (perms := compactPerms201) pairs201 domains201 autos201
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev201k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound201 : Lower true (vars 201) (graphGoal 201) 5 :=
  plain_low (hints := 805306371) (by decide +kernel) excluded201

def grid233 : CompactGrid := (233, 5, samplesP233, samplesQ233)
def tab233 : CompactTable := (compactCount233, compactPath233, compactLive233, compactPoolIDs233, compactBucket233)
def check233 (k : Nat) := compactNode grid233 tab233 compactDomains233 compactPerms233 k
def sliceSpecs233 : List SliceSpec := [(32, 0, 201, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains233 : ∀ d ∈ compactDomains233, Slice true (vars 233) (graphGoal 233) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(201, 5)]) (specs := sliceSpecs233)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound201
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs233 : properPairs (graphGoal 233) (asRow samplesP233) (asRow samplesQ233) :=
  compactPairs (g := grid233) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos233 : ∀ p ∈ compactPerms233, autoOK (graphGoal 233) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c233k5p0 : chartBlock (check233 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev233k5 : chartBlock (check233 5) 0 1 = true :=
  c233k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded233 : Impossible true (graphGoal 233) 5 (vars 233).toFinset := by
  apply compactRoot (g := grid233) (t := tab233) (dom := compactDomains233) (perms := compactPerms233) pairs233 domains233 autos233
  · intro k hk
    change k ≤ 5 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev233k5
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound233 : Lower true (vars 233) (graphGoal 233) 6 :=
  plain_low (hints := 805306371) (by decide +kernel) excluded233

def grid205 : CompactGrid := (205, 5, samplesP205, samplesQ205)
def tab205 : CompactTable := (compactCount205, compactPath205, compactLive205, compactPoolIDs205, compactBucket205)
def check205 (k : Nat) := compactNode grid205 tab205 compactDomains205 compactPerms205 k
def sliceSpecs205 : List SliceSpec := [(4, 0, 201, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains205 : ∀ d ∈ compactDomains205, Slice true (vars 205) (graphGoal 205) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(201, 5)]) (specs := sliceSpecs205)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound201
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs205 : properPairs (graphGoal 205) (asRow samplesP205) (asRow samplesQ205) :=
  compactPairs (g := grid205) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos205 : ∀ p ∈ compactPerms205, autoOK (graphGoal 205) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c205k5p0 : chartBlock (check205 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev205k5 : chartBlock (check205 5) 0 1 = true :=
  c205k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded205 : Impossible true (graphGoal 205) 5 (vars 205).toFinset := by
  apply compactRoot (g := grid205) (t := tab205) (dom := compactDomains205) (perms := compactPerms205) pairs205 domains205 autos205
  · intro k hk
    change k ≤ 5 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev205k5
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound205 : Lower true (vars 205) (graphGoal 205) 6 :=
  plain_low (hints := 536872451) (by decide +kernel) excluded205

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound109 : Lower true (vars 109) (graphGoal 109) 6 :=
  carry_of (old := 109) (rep := 205) (swaps := [48, 117]) (by decide +kernel) bound205

def grid236 : CompactGrid := (236, 4, samplesP236, samplesQ236)
def tab236 : CompactTable := (compactCount236, compactPath236, compactLive236, compactPoolIDs236, compactBucket236)
def check236 (k : Nat) := compactNode grid236 tab236 compactDomains236 compactPerms236 k
def sliceSpecs236 : List SliceSpec := [(64, 0, 172, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains236 : ∀ d ∈ compactDomains236, Slice true (vars 236) (graphGoal 236) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(172, 4)]) (specs := sliceSpecs236)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound172
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs236 : properPairs (graphGoal 236) (asRow samplesP236) (asRow samplesQ236) :=
  compactPairs (g := grid236) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos236 : ∀ p ∈ compactPerms236, autoOK (graphGoal 236) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c236k4p0 : chartBlock (check236 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev236k4 : chartBlock (check236 4) 0 1 = true :=
  c236k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded236 : Impossible true (graphGoal 236) 4 (vars 236).toFinset := by
  apply compactRoot (g := grid236) (t := tab236) (dom := compactDomains236) (perms := compactPerms236) pairs236 domains236 autos236
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev236k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound236 : Lower true (vars 236) (graphGoal 236) 5 :=
  plain_low (hints := 572548352) (by decide +kernel) excluded236

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound229 : Lower true (vars 229) (graphGoal 229) 5 :=
  carry_of (old := 229) (rep := 236) (swaps := [48, 117]) (by decide +kernel) bound236

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound105 : Lower true (vars 105) (graphGoal 105) 5 :=
  carry_of (old := 105) (rep := 201) (swaps := [48, 117]) (by decide +kernel) bound201

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound77 : Lower true (vars 77) (graphGoal 77) 5 :=
  carry_of (old := 77) (rep := 201) (swaps := [114, 99]) (by decide +kernel) bound201

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound197 : Lower true (vars 197) (graphGoal 197) 4 :=
  carry_of (old := 197) (rep := 172) (swaps := [48, 118, 117]) (by decide +kernel) bound172

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound108 : Lower true (vars 108) (graphGoal 108) 4 :=
  carry_of (old := 108) (rep := 172) (swaps := [118]) (by decide +kernel) bound172

def grid237 : CompactGrid := (237, 8, samplesP237, samplesQ237)
def tab237 : CompactTable := (compactCount237, compactPath237, compactLive237, compactPoolIDs237, compactBucket237)
def check237 (k : Nat) := compactNode grid237 tab237 compactDomains237 compactPerms237 k
def sliceSpecs237 : List SliceSpec := [(64, 0, 173, 0, 0, 7, 7), (4, 0, 233, 0, 0, 6, 6), (32, 0, 205, 0, 0, 6, 6), (128, 0, 109, 0, 0, 6, 6), (1, 0, 236, 0, 0, 5, 5), (8, 0, 229, 0, 0, 5, 5), (36, 0, 201, 0, 0, 5, 5), (132, 0, 105, 0, 0, 5, 5), (160, 0, 77, 0, 0, 5, 5), (40, 0, 197, 0, 0, 4, 4), (65, 0, 172, 0, 0, 4, 4), (129, 0, 108, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains237 : ∀ d ∈ compactDomains237, Slice true (vars 237) (graphGoal 237) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(173, 7), (233, 6), (205, 6), (109, 6), (236, 5), (229, 5), (201, 5), (105, 5), (77, 5), (197, 4), (172, 4), (108, 4)]) (specs := sliceSpecs237)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound173
    · exact bound233
    · exact bound205
    · exact bound109
    · exact bound236
    · exact bound229
    · exact bound201
    · exact bound105
    · exact bound77
    · exact bound197
    · exact bound172
    · exact bound108
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs237 : properPairs (graphGoal 237) (asRow samplesP237) (asRow samplesQ237) :=
  compactPairs (g := grid237) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos237 : ∀ p ∈ compactPerms237, autoOK (graphGoal 237) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c237k4p0 : chartBlock (check237 4) 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev237k4 : chartBlock (check237 4) 0 2 = true :=
  c237k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c237k5p0 : chartBlock (check237 5) 0 7 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev237k5 : chartBlock (check237 5) 0 7 = true :=
  c237k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c237k6p0 : chartBlock (check237 6) 0 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c237k6p1 : chartBlock (check237 6) 8 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c237k6p2 : chartBlock (check237 6) 16 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c237k6p3 : chartBlock (check237 6) 24 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev237k6 : chartBlock (check237 6) 0 27 = true :=
  (chartBlock_join (a := 16) (b := 11) (chartBlock_join (a := 8) (b := 8) c237k6p0 c237k6p1) (chartBlock_join (a := 8) (b := 3) c237k6p2 c237k6p3))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c237k7p0 : chartBlock (check237 7) 0 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c237k7p1 : chartBlock (check237 7) 8 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev237k7 : chartBlock (check237 7) 0 9 = true :=
  (chartBlock_join (a := 8) (b := 1) c237k7p0 c237k7p1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c237k8p0 : chartBlock (check237 8) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev237k8 : chartBlock (check237 8) 0 1 = true :=
  c237k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded237 : Impossible true (graphGoal 237) 8 (vars 237).toFinset := by
  apply compactRoot (g := grid237) (t := tab237) (dom := compactDomains237) (perms := compactPerms237) pairs237 domains237 autos237
  · intro k hk
    change k ≤ 8 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev237k4
    · exact lev237k5
    · exact lev237k6
    · exact lev237k7
    · exact lev237k8
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound237 : Lower true (vars 237) (graphGoal 237) 9 :=
  plain_low (hints := 536872195) (by decide +kernel) excluded237

def grid253 : CompactGrid := (253, 9, samplesP253, samplesQ253)
def tab253 : CompactTable := (compactCount253, compactPath253, compactLive253, compactPoolIDs253, compactBucket253)
def check253 (k : Nat) := compactNode grid253 tab253 compactDomains253 compactPerms253 k
def sliceSpecs253 : List SliceSpec := [(16, 0, 237, 0, 0, 9, 9)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains253 : ∀ d ∈ compactDomains253, Slice true (vars 253) (graphGoal 253) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(237, 9)]) (specs := sliceSpecs253)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound237
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
theorem c253k9p0 : chartBlock (check253 9) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev253k9 : chartBlock (check253 9) 0 1 = true :=
  c253k9p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded253 : Impossible true (graphGoal 253) 9 (vars 253).toFinset := by
  apply compactRoot (g := grid253) (t := tab253) (dom := compactDomains253) (perms := compactPerms253) pairs253 domains253 autos253
  · intro k hk
    change k ≤ 9 at hk
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
    · exact lev253k9
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound253 : Lower true (vars 253) (graphGoal 253) 10 :=
  plain_low (hints := 537330947) (by decide +kernel) excluded253

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound216 : Lower true (vars 216) (graphGoal 216) 4 :=
  carry_of (old := 216) (rep := 172) (swaps := [50, 66, 101]) (by decide +kernel) bound172

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound153 : Lower true (vars 153) (graphGoal 153) 4 :=
  carry_of (old := 153) (rep := 172) (swaps := [48, 115, 84, 114]) (by decide +kernel) bound172

def grid217 : CompactGrid := (217, 6, samplesP217, samplesQ217)
def tab217 : CompactTable := (compactCount217, compactPath217, compactLive217, compactPoolIDs217, compactBucket217)
def check217 (k : Nat) := compactNode grid217 tab217 compactDomains217 compactPerms217 k
def sliceSpecs217 : List SliceSpec := [(16, 0, 201, 0, 0, 5, 5), (0, 16, 73, 128, 4026531840, 5, 4), (1, 0, 216, 0, 0, 4, 4), (64, 0, 153, 0, 0, 4, 4), (128, 16, 73, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains217 : ∀ d ∈ compactDomains217, Slice true (vars 217) (graphGoal 217) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(201, 5), (73, 4), (216, 4), (153, 4)]) (specs := sliceSpecs217)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact bound201
    · exact bound73
    · exact bound216
    · exact bound153
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs217 : properPairs (graphGoal 217) (asRow samplesP217) (asRow samplesQ217) :=
  compactPairs (g := grid217) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos217 : ∀ p ∈ compactPerms217, autoOK (graphGoal 217) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c217k4p0 : chartBlock (check217 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev217k4 : chartBlock (check217 4) 0 1 = true :=
  c217k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c217k5p0 : chartBlock (check217 5) 0 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev217k5 : chartBlock (check217 5) 0 3 = true :=
  c217k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c217k6p0 : chartBlock (check217 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev217k6 : chartBlock (check217 6) 0 1 = true :=
  c217k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded217 : Impossible true (graphGoal 217) 6 (vars 217).toFinset := by
  apply compactRoot (g := grid217) (t := tab217) (dom := compactDomains217) (perms := compactPerms217) pairs217 domains217 autos217
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev217k4
    · exact lev217k5
    · exact lev217k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound217 : Lower true (vars 217) (graphGoal 217) 7 :=
  plain_low (hints := 805765123) (by decide +kernel) excluded217

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound211 : Lower true (vars 211) (graphGoal 211) 7 :=
  carry_of (old := 211) (rep := 217) (swaps := [64, 49, 118]) (by decide +kernel) bound217

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound155 : Lower true (vars 155) (graphGoal 155) 7 :=
  carry_of (old := 155) (rep := 217) (swaps := [64, 97, 115]) (by decide +kernel) bound217

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound91 : Lower true (vars 91) (graphGoal 91) 7 :=
  carry_of (old := 91) (rep := 217) (swaps := [113, 99]) (by decide +kernel) bound217

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound218 : Lower true (vars 218) (graphGoal 218) 6 :=
  carry_of (old := 218) (rep := 205) (swaps := [49, 50, 64, 118, 32]) (by decide +kernel) bound205

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound146 : Lower true (vars 146) (graphGoal 146) 4 :=
  carry_of (old := 146) (rep := 73) (swaps := [16, 67, 118]) (by decide +kernel) bound73

def grid219 : CompactGrid := (219, 8, samplesP219, samplesQ219)
def tab219 : CompactTable := (compactCount219, compactPath219, compactLive219, compactPoolIDs219, compactBucket219)
def check219 (k : Nat) := compactNode grid219 tab219 compactDomains219 compactPerms219 k
def sliceSpecs219 : List SliceSpec := [(2, 0, 217, 0, 0, 7, 7), (8, 0, 211, 0, 0, 7, 7), (64, 0, 155, 0, 0, 7, 7), (128, 0, 91, 0, 0, 7, 7), (1, 0, 218, 0, 0, 6, 6), (0, 1, 146, 72, 251719680, 6, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains219 : ∀ d ∈ compactDomains219, Slice true (vars 219) (graphGoal 219) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(217, 7), (211, 7), (155, 7), (91, 7), (218, 6), (146, 4)]) (specs := sliceSpecs219)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound217
    · exact bound211
    · exact bound155
    · exact bound91
    · exact bound218
    · exact bound146
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs219 : properPairs (graphGoal 219) (asRow samplesP219) (asRow samplesQ219) :=
  compactPairs (g := grid219) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos219 : ∀ p ∈ compactPerms219, autoOK (graphGoal 219) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c219k8p0 : chartBlock (check219 8) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev219k8 : chartBlock (check219 8) 0 1 = true :=
  c219k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded219 : Impossible true (graphGoal 219) 8 (vars 219).toFinset := by
  apply compactRoot (g := grid219) (t := tab219) (dom := compactDomains219) (perms := compactPerms219) pairs219 domains219 autos219
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
    · exact lev219k8
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound219 : Lower true (vars 219) (graphGoal 219) 9 :=
  plain_low (hints := 268501059) (by decide +kernel) excluded219

def grid251 : CompactGrid := (251, 9, samplesP251, samplesQ251)
def tab251 : CompactTable := (compactCount251, compactPath251, compactLive251, compactPoolIDs251, compactBucket251)
def check251 (k : Nat) := compactNode grid251 tab251 compactDomains251 compactPerms251 k
def sliceSpecs251 : List SliceSpec := [(32, 0, 219, 0, 0, 9, 9)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains251 : ∀ d ∈ compactDomains251, Slice true (vars 251) (graphGoal 251) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(219, 9)]) (specs := sliceSpecs251)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound219
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs251 : properPairs (graphGoal 251) (asRow samplesP251) (asRow samplesQ251) :=
  compactPairs (g := grid251) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos251 : ∀ p ∈ compactPerms251, autoOK (graphGoal 251) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c251k9p0 : chartBlock (check251 9) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev251k9 : chartBlock (check251 9) 0 1 = true :=
  c251k9p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded251 : Impossible true (graphGoal 251) 9 (vars 251).toFinset := by
  apply compactRoot (g := grid251) (t := tab251) (dom := compactDomains251) (perms := compactPerms251) pairs251 domains251 autos251
  · intro k hk
    change k ≤ 9 at hk
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
    · exact lev251k9
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound251 : Lower true (vars 251) (graphGoal 251) 10 :=
  plain_low (hints := 268501059) (by decide +kernel) excluded251

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound182 : Lower true (vars 182) (graphGoal 182) 7 :=
  carry_of (old := 182) (rep := 217) (swaps := [16, 114, 100, 101, 115]) (by decide +kernel) bound217

def grid246 : CompactGrid := (246, 7, samplesP246, samplesQ246)
def tab246 : CompactTable := (compactCount246, compactPath246, compactLive246, compactPoolIDs246, compactBucket246)
def check246 (k : Nat) := compactNode grid246 tab246 compactDomains246 compactPerms246 k
def sliceSpecs246 : List SliceSpec := [(64, 0, 182, 0, 0, 7, 7)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains246 : ∀ d ∈ compactDomains246, Slice true (vars 246) (graphGoal 246) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(182, 7)]) (specs := sliceSpecs246)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound182
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs246 : properPairs (graphGoal 246) (asRow samplesP246) (asRow samplesQ246) :=
  compactPairs (g := grid246) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos246 : ∀ p ∈ compactPerms246, autoOK (graphGoal 246) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c246k7p0 : chartBlock (check246 7) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev246k7 : chartBlock (check246 7) 0 1 = true :=
  c246k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded246 : Impossible true (graphGoal 246) 7 (vars 246).toFinset := by
  apply compactRoot (g := grid246) (t := tab246) (dom := compactDomains246) (perms := compactPerms246) pairs246 domains246 autos246
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
    · exact lev246k7
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound246 : Lower true (vars 246) (graphGoal 246) 8 :=
  plain_low (hints := 287376704) (by decide +kernel) excluded246

def grid243 : CompactGrid := (243, 7, samplesP243, samplesQ243)
def tab243 : CompactTable := (compactCount243, compactPath243, compactLive243, compactPoolIDs243, compactBucket243)
def check243 (k : Nat) := compactNode grid243 tab243 compactDomains243 compactPerms243 k
def sliceSpecs243 : List SliceSpec := [(32, 0, 211, 0, 0, 7, 7)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains243 : ∀ d ∈ compactDomains243, Slice true (vars 243) (graphGoal 243) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(211, 7)]) (specs := sliceSpecs243)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound211
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs243 : properPairs (graphGoal 243) (asRow samplesP243) (asRow samplesQ243) :=
  compactPairs (g := grid243) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos243 : ∀ p ∈ compactPerms243, autoOK (graphGoal 243) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c243k7p0 : chartBlock (check243 7) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev243k7 : chartBlock (check243 7) 0 1 = true :=
  c243k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded243 : Impossible true (graphGoal 243) 7 (vars 243).toFinset := by
  apply compactRoot (g := grid243) (t := tab243) (dom := compactDomains243) (perms := compactPerms243) pairs243 domains243 autos243
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
    · exact lev243k7
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound243 : Lower true (vars 243) (graphGoal 243) 8 :=
  plain_low (hints := 268501061) (by decide +kernel) excluded243

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound215 : Lower true (vars 215) (graphGoal 215) 8 :=
  carry_of (old := 215) (rep := 246) (swaps := [80, 113, 98]) (by decide +kernel) bound246

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound183 : Lower true (vars 183) (graphGoal 183) 8 :=
  carry_of (old := 183) (rep := 243) (swaps := [80, 113, 98]) (by decide +kernel) bound243

def grid227 : CompactGrid := (227, 4, samplesP227, samplesQ227)
def tab227 : CompactTable := (compactCount227, compactPath227, compactLive227, compactPoolIDs227, compactBucket227)
def check227 (k : Nat) := compactNode grid227 tab227 compactDomains227 compactPerms227 k
def sliceSpecs227 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains227 : ∀ d ∈ compactDomains227, Slice true (vars 227) (graphGoal 227) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs227)
  · simp
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs227 : properPairs (graphGoal 227) (asRow samplesP227) (asRow samplesQ227) :=
  compactPairs (g := grid227) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos227 : ∀ p ∈ compactPerms227, autoOK (graphGoal 227) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c227k4p0 : chartBlock (check227 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev227k4 : chartBlock (check227 4) 0 1 = true :=
  c227k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded227 : Impossible true (graphGoal 227) 4 (vars 227).toFinset := by
  apply compactRoot (g := grid227) (t := tab227) (dom := compactDomains227) (perms := compactPerms227) pairs227 domains227 autos227
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev227k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound227 : Lower true (vars 227) (graphGoal 227) 5 :=
  plain_low (hints := 268435557) (by decide +kernel) excluded227

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound167 : Lower true (vars 167) (graphGoal 167) 5 :=
  carry_of (old := 167) (rep := 227) (swaps := [80, 113, 98]) (by decide +kernel) bound227

def grid231 : CompactGrid := (231, 6, samplesP231, samplesQ231)
def tab231 : CompactTable := (compactCount231, compactPath231, compactLive231, compactPoolIDs231, compactBucket231)
def check231 (k : Nat) := compactNode grid231 tab231 compactDomains231 compactPerms231 k
def sliceSpecs231 : List SliceSpec := [(4, 0, 227, 0, 0, 5, 5), (64, 0, 167, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains231 : ∀ d ∈ compactDomains231, Slice true (vars 231) (graphGoal 231) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(227, 5), (167, 5)]) (specs := sliceSpecs231)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact bound227
    · exact bound167
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs231 : properPairs (graphGoal 231) (asRow samplesP231) (asRow samplesQ231) :=
  compactPairs (g := grid231) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos231 : ∀ p ∈ compactPerms231, autoOK (graphGoal 231) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c231k6p0 : chartBlock (check231 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev231k6 : chartBlock (check231 6) 0 1 = true :=
  c231k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded231 : Impossible true (graphGoal 231) 6 (vars 231).toFinset := by
  apply compactRoot (g := grid231) (t := tab231) (dom := compactDomains231) (perms := compactPerms231) pairs231 domains231 autos231
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev231k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound231 : Lower true (vars 231) (graphGoal 231) 7 :=
  plain_low (hints := 268436837) (by decide +kernel) excluded231

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound150 : Lower true (vars 150) (graphGoal 150) 5 :=
  carry_of (old := 150) (rep := 201) (swaps := [16, 114, 100, 115]) (by decide +kernel) bound201

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound210 : Lower true (vars 210) (graphGoal 210) 5 :=
  carry_of (old := 210) (rep := 201) (swaps := [49, 64, 118, 48]) (by decide +kernel) bound201

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound212 : Lower true (vars 212) (graphGoal 212) 4 :=
  carry_of (old := 212) (rep := 172) (swaps := [67, 101]) (by decide +kernel) bound172

def grid244 : CompactGrid := (244, 4, samplesP244, samplesQ244)
def tab244 : CompactTable := (compactCount244, compactPath244, compactLive244, compactPoolIDs244, compactBucket244)
def check244 (k : Nat) := compactNode grid244 tab244 compactDomains244 compactPerms244 k
def sliceSpecs244 : List SliceSpec := [(32, 0, 212, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains244 : ∀ d ∈ compactDomains244, Slice true (vars 244) (graphGoal 244) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(212, 4)]) (specs := sliceSpecs244)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
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
theorem excluded244 : Impossible true (graphGoal 244) 4 (vars 244).toFinset := by
  apply compactRoot (g := grid244) (t := tab244) (dom := compactDomains244) (perms := compactPerms244) pairs244 domains244 autos244
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev244k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound244 : Lower true (vars 244) (graphGoal 244) 5 :=
  plain_low (hints := 572982528) (by decide +kernel) excluded244

def grid245 : CompactGrid := (245, 5, samplesP245, samplesQ245)
def tab245 : CompactTable := (compactCount245, compactPath245, compactLive245, compactPoolIDs245, compactBucket245)
def check245 (k : Nat) := compactNode grid245 tab245 compactDomains245 compactPerms245 k
def sliceSpecs245 : List SliceSpec := [(1, 0, 244, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains245 : ∀ d ∈ compactDomains245, Slice true (vars 245) (graphGoal 245) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(244, 5)]) (specs := sliceSpecs245)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound244
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
theorem excluded245 : Impossible true (graphGoal 245) 5 (vars 245).toFinset := by
  apply compactRoot (g := grid245) (t := tab245) (dom := compactDomains245) (perms := compactPerms245) pairs245 domains245 autos245
  · intro k hk
    change k ≤ 5 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev245k5
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound245 : Lower true (vars 245) (graphGoal 245) 6 :=
  plain_low (hints := 537330949) (by decide +kernel) excluded245

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound119 : Lower true (vars 119) (graphGoal 119) 6 :=
  carry_of (old := 119) (rep := 245) (swaps := [80, 113, 98]) (by decide +kernel) bound245

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound115 : Lower true (vars 115) (graphGoal 115) 5 :=
  carry_of (old := 115) (rep := 227) (swaps := [116]) (by decide +kernel) bound227

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound103 : Lower true (vars 103) (graphGoal 103) 5 :=
  carry_of (old := 103) (rep := 236) (swaps := [112, 81, 98, 83, 115]) (by decide +kernel) bound236

def grid247 : CompactGrid := (247, 9, samplesP247, samplesQ247)
def tab247 : CompactTable := (compactCount247, compactPath247, compactLive247, compactPoolIDs247, compactBucket247)
def check247 (k : Nat) := compactNode grid247 tab247 compactDomains247 compactPerms247 k
def sliceSpecs247 : List SliceSpec := [(1, 0, 246, 0, 0, 8, 8), (4, 0, 243, 0, 0, 8, 8), (32, 0, 215, 0, 0, 8, 8), (64, 0, 183, 0, 0, 8, 8), (16, 0, 231, 0, 0, 7, 7), (0, 1, 150, 96, 267386880, 7, 5), (0, 32, 210, 5, 3855, 7, 5), (2, 0, 245, 0, 0, 6, 6), (128, 0, 119, 0, 0, 6, 6), (18, 0, 229, 0, 0, 5, 5), (132, 0, 115, 0, 0, 5, 5), (144, 0, 103, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains247 : ∀ d ∈ compactDomains247, Slice true (vars 247) (graphGoal 247) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(246, 8), (243, 8), (215, 8), (183, 8), (231, 7), (150, 5), (210, 5), (245, 6), (119, 6), (229, 5), (115, 5), (103, 5)]) (specs := sliceSpecs247)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound246
    · exact bound243
    · exact bound215
    · exact bound183
    · exact bound231
    · exact bound150
    · exact bound210
    · exact bound245
    · exact bound119
    · exact bound229
    · exact bound115
    · exact bound103
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs247 : properPairs (graphGoal 247) (asRow samplesP247) (asRow samplesQ247) :=
  compactPairs (g := grid247) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos247 : ∀ p ∈ compactPerms247, autoOK (graphGoal 247) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c247k6p0 : chartBlock (check247 6) 0 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev247k6 : chartBlock (check247 6) 0 3 = true :=
  c247k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c247k7p0 : chartBlock (check247 7) 0 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c247k7p1 : chartBlock (check247 7) 8 5 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev247k7 : chartBlock (check247 7) 0 13 = true :=
  (chartBlock_join (a := 8) (b := 5) c247k7p0 c247k7p1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c247k8p0 : chartBlock (check247 8) 0 5 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev247k8 : chartBlock (check247 8) 0 5 = true :=
  c247k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c247k9p0 : chartBlock (check247 9) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev247k9 : chartBlock (check247 9) 0 1 = true :=
  c247k9p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded247 : Impossible true (graphGoal 247) 9 (vars 247).toFinset := by
  apply compactRoot (g := grid247) (t := tab247) (dom := compactDomains247) (perms := compactPerms247) pairs247 domains247 autos247
  · intro k hk
    change k ≤ 9 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev247k6
    · exact lev247k7
    · exact lev247k8
    · exact lev247k9
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound247 : Lower true (vars 247) (graphGoal 247) 10 :=
  plain_low (hints := 268502341) (by decide +kernel) excluded247

def grid239 : CompactGrid := (239, 9, samplesP239, samplesQ239)
def tab239 : CompactTable := (compactCount239, compactPath239, compactLive239, compactPoolIDs239, compactBucket239)
def check239 (k : Nat) := compactNode grid239 tab239 compactDomains239 compactPerms239 k
def sliceSpecs239 : List SliceSpec := [(2, 0, 237, 0, 0, 9, 9)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains239 : ∀ d ∈ compactDomains239, Slice true (vars 239) (graphGoal 239) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(237, 9)]) (specs := sliceSpecs239)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound237
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs239 : properPairs (graphGoal 239) (asRow samplesP239) (asRow samplesQ239) :=
  compactPairs (g := grid239) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos239 : ∀ p ∈ compactPerms239, autoOK (graphGoal 239) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c239k9p0 : chartBlock (check239 9) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev239k9 : chartBlock (check239 9) 0 1 = true :=
  c239k9p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded239 : Impossible true (graphGoal 239) 9 (vars 239).toFinset := by
  apply compactRoot (g := grid239) (t := tab239) (dom := compactDomains239) (perms := compactPerms239) pairs239 domains239 autos239
  · intro k hk
    change k ≤ 9 at hk
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
    · exact lev239k9
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound239 : Lower true (vars 239) (graphGoal 239) 10 :=
  plain_low (hints := 268436835) (by decide +kernel) excluded239

def grid223 : CompactGrid := (223, 9, samplesP223, samplesQ223)
def tab223 : CompactTable := (compactCount223, compactPath223, compactLive223, compactPoolIDs223, compactBucket223)
def check223 (k : Nat) := compactNode grid223 tab223 compactDomains223 compactPerms223 k
def sliceSpecs223 : List SliceSpec := [(4, 0, 219, 0, 0, 9, 9)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains223 : ∀ d ∈ compactDomains223, Slice true (vars 223) (graphGoal 223) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(219, 9)]) (specs := sliceSpecs223)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound219
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs223 : properPairs (graphGoal 223) (asRow samplesP223) (asRow samplesQ223) :=
  compactPairs (g := grid223) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos223 : ∀ p ∈ compactPerms223, autoOK (graphGoal 223) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c223k9p0 : chartBlock (check223 9) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev223k9 : chartBlock (check223 9) 0 1 = true :=
  c223k9p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded223 : Impossible true (graphGoal 223) 9 (vars 223).toFinset := by
  apply compactRoot (g := grid223) (t := tab223) (dom := compactDomains223) (perms := compactPerms223) pairs223 domains223 autos223
  · intro k hk
    change k ≤ 9 at hk
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
    · exact lev223k9
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound223 : Lower true (vars 223) (graphGoal 223) 10 :=
  plain_low (hints := 268502595) (by decide +kernel) excluded223

def grid190 : CompactGrid := (190, 7, samplesP190, samplesQ190)
def tab190 : CompactTable := (compactCount190, compactPath190, compactLive190, compactPoolIDs190, compactBucket190)
def check190 (k : Nat) := compactNode grid190 tab190 compactDomains190 compactPerms190 k
def sliceSpecs190 : List SliceSpec := [(8, 0, 182, 0, 0, 7, 7)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains190 : ∀ d ∈ compactDomains190, Slice true (vars 190) (graphGoal 190) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(182, 7)]) (specs := sliceSpecs190)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound182
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs190 : properPairs (graphGoal 190) (asRow samplesP190) (asRow samplesQ190) :=
  compactPairs (g := grid190) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos190 : ∀ p ∈ compactPerms190, autoOK (graphGoal 190) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c190k7p0 : chartBlock (check190 7) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev190k7 : chartBlock (check190 7) 0 1 = true :=
  c190k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded190 : Impossible true (graphGoal 190) 7 (vars 190).toFinset := by
  apply compactRoot (g := grid190) (t := tab190) (dom := compactDomains190) (perms := compactPerms190) pairs190 domains190 autos190
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
    · exact lev190k7
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound190 : Lower true (vars 190) (graphGoal 190) 8 :=
  plain_low (hints := 270628160) (by decide +kernel) excluded190

def grid189 : CompactGrid := (189, 7, samplesP189, samplesQ189)
def tab189 : CompactTable := (compactCount189, compactPath189, compactLive189, compactPoolIDs189, compactBucket189)
def check189 (k : Nat) := compactNode grid189 tab189 compactDomains189 compactPerms189 k
def sliceSpecs189 : List SliceSpec := [(16, 0, 173, 0, 0, 7, 7)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains189 : ∀ d ∈ compactDomains189, Slice true (vars 189) (graphGoal 189) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(173, 7)]) (specs := sliceSpecs189)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound173
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs189 : properPairs (graphGoal 189) (asRow samplesP189) (asRow samplesQ189) :=
  compactPairs (g := grid189) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos189 : ∀ p ∈ compactPerms189, autoOK (graphGoal 189) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c189k7p0 : chartBlock (check189 7) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev189k7 : chartBlock (check189 7) 0 1 = true :=
  c189k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded189 : Impossible true (graphGoal 189) 7 (vars 189).toFinset := by
  apply compactRoot (g := grid189) (t := tab189) (dom := compactDomains189) (perms := compactPerms189) pairs189 domains189 autos189
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
    · exact lev189k7
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound189 : Lower true (vars 189) (graphGoal 189) 8 :=
  plain_low (hints := 537330947) (by decide +kernel) excluded189

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound187 : Lower true (vars 187) (graphGoal 187) 8 :=
  carry_of (old := 187) (rep := 243) (swaps := [113, 99]) (by decide +kernel) bound243

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound175 : Lower true (vars 175) (graphGoal 175) 8 :=
  carry_of (old := 175) (rep := 189) (swaps := [65]) (by decide +kernel) bound189

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound159 : Lower true (vars 159) (graphGoal 159) 8 :=
  carry_of (old := 159) (rep := 190) (swaps := [80, 50]) (by decide +kernel) bound190

def grid191 : CompactGrid := (191, 9, samplesP191, samplesQ191)
def tab191 : CompactTable := (compactCount191, compactPath191, compactLive191, compactPoolIDs191, compactBucket191)
def check191 (k : Nat) := compactNode grid191 tab191 compactDomains191 compactPerms191 k
def sliceSpecs191 : List SliceSpec := [(1, 0, 190, 0, 0, 8, 8), (2, 0, 189, 0, 0, 8, 8), (4, 0, 187, 0, 0, 8, 8), (8, 0, 183, 0, 0, 8, 8), (16, 0, 175, 0, 0, 8, 8), (32, 0, 159, 0, 0, 8, 8)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains191 : ∀ d ∈ compactDomains191, Slice true (vars 191) (graphGoal 191) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(190, 8), (189, 8), (187, 8), (183, 8), (175, 8), (159, 8)]) (specs := sliceSpecs191)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound190
    · exact bound189
    · exact bound187
    · exact bound183
    · exact bound175
    · exact bound159
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs191 : properPairs (graphGoal 191) (asRow samplesP191) (asRow samplesQ191) :=
  compactPairs (g := grid191) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos191 : ∀ p ∈ compactPerms191, autoOK (graphGoal 191) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c191k9p0 : chartBlock (check191 9) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev191k9 : chartBlock (check191 9) 0 1 = true :=
  c191k9p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded191 : Impossible true (graphGoal 191) 9 (vars 191).toFinset := by
  apply compactRoot (g := grid191) (t := tab191) (dom := compactDomains191) (perms := compactPerms191) pairs191 domains191 autos191
  · intro k hk
    change k ≤ 9 at hk
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
    · exact lev191k9
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound191 : Lower true (vars 191) (graphGoal 191) 10 :=
  plain_low (hints := 268502339) (by decide +kernel) excluded191

def grid254 : CompactGrid := (254, 8, samplesP254, samplesQ254)
def tab254 : CompactTable := (compactCount254, compactPath254, compactLive254, compactPoolIDs254, compactBucket254)
def check254 (k : Nat) := compactNode grid254 tab254 compactDomains254 compactPerms254 k
def sliceSpecs254 : List SliceSpec := [(8, 0, 246, 0, 0, 8, 8)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains254 : ∀ d ∈ compactDomains254, Slice true (vars 254) (graphGoal 254) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(246, 8)]) (specs := sliceSpecs254)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound246
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
  plain_low (hints := 287401280) (by decide +kernel) excluded254

def grid123 : CompactGrid := (123, 7, samplesP123, samplesQ123)
def tab123 : CompactTable := (compactCount123, compactPath123, compactLive123, compactPoolIDs123, compactBucket123)
def check123 (k : Nat) := compactNode grid123 tab123 compactDomains123 compactPerms123 k
def sliceSpecs123 : List SliceSpec := [(32, 0, 91, 0, 0, 7, 7)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains123 : ∀ d ∈ compactDomains123, Slice true (vars 123) (graphGoal 123) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(91, 7)]) (specs := sliceSpecs123)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound91
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs123 : properPairs (graphGoal 123) (asRow samplesP123) (asRow samplesQ123) :=
  compactPairs (g := grid123) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos123 : ∀ p ∈ compactPerms123, autoOK (graphGoal 123) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c123k7p0 : chartBlock (check123 7) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev123k7 : chartBlock (check123 7) 0 1 = true :=
  c123k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded123 : Impossible true (graphGoal 123) 7 (vars 123).toFinset := by
  apply compactRoot (g := grid123) (t := tab123) (dom := compactDomains123) (perms := compactPerms123) pairs123 domains123 autos123
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
    · exact lev123k7
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound123 : Lower true (vars 123) (graphGoal 123) 8 :=
  plain_low (hints := 65603) (by decide +kernel) excluded123

def grid127 : CompactGrid := (127, 8, samplesP127, samplesQ127)
def tab127 : CompactTable := (compactCount127, compactPath127, compactLive127, compactPoolIDs127, compactBucket127)
def check127 (k : Nat) := compactNode grid127 tab127 compactDomains127 compactPerms127 k
def sliceSpecs127 : List SliceSpec := [(4, 0, 123, 0, 0, 8, 8)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains127 : ∀ d ∈ compactDomains127, Slice true (vars 127) (graphGoal 127) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(123, 8)]) (specs := sliceSpecs127)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound123
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
theorem c127k8p0 : chartBlock (check127 8) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev127k8 : chartBlock (check127 8) 0 1 = true :=
  c127k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded127 : Impossible true (graphGoal 127) 8 (vars 127).toFinset := by
  apply compactRoot (g := grid127) (t := tab127) (dom := compactDomains127) (perms := compactPerms127) pairs127 domains127 autos127
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
    · exact lev127k8
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound127 : Lower true (vars 127) (graphGoal 127) 9 :=
  plain_low (hints := 66883) (by decide +kernel) excluded127

def grid255 : CompactGrid := (255, 11, samplesP255, samplesQ255)
def tab255 : CompactTable := (compactCount255, compactPath255, compactLive255, compactPoolIDs255, compactBucket255)
def check255 (k : Nat) := compactNode grid255 tab255 compactDomains255 compactPerms255 k
def sliceSpecs255 : List SliceSpec := [(2, 0, 253, 0, 0, 10, 10), (4, 0, 251, 0, 0, 10, 10), (8, 0, 247, 0, 0, 10, 10), (16, 0, 239, 0, 0, 10, 10), (32, 0, 223, 0, 0, 10, 10), (64, 0, 191, 0, 0, 10, 10), (1, 0, 254, 0, 0, 9, 9), (128, 0, 127, 0, 0, 9, 9)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains255 : ∀ d ∈ compactDomains255, Slice true (vars 255) (graphGoal 255) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(253, 10), (251, 10), (247, 10), (239, 10), (223, 10), (191, 10), (254, 9), (127, 9)]) (specs := sliceSpecs255)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound253
    · exact bound251
    · exact bound247
    · exact bound239
    · exact bound223
    · exact bound191
    · exact bound254
    · exact bound127
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
theorem c255k11p0 : chartBlock (check255 11) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev255k11 : chartBlock (check255 11) 0 1 = true :=
  c255k11p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded255 : Impossible true (graphGoal 255) 11 (vars 255).toFinset := by
  apply compactRoot (g := grid255) (t := tab255) (dom := compactDomains255) (perms := compactPerms255) pairs255 domains255 autos255
  · intro k hk
    change k ≤ 11 at hk
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
    · exact lev255k11
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound255 : Lower true (vars 255) (graphGoal 255) 12 :=
  plain_low (hints := 268502339) (by decide +kernel) excluded255
def winningGates : List Gate := [⟨.or,[6,7]⟩, ⟨.or,[2,3]⟩, ⟨.or,[1,9]⟩, ⟨.and,[8,10]⟩, ⟨.or,[5,6]⟩, ⟨.or,[0,2]⟩, ⟨.and,[12,13]⟩, ⟨.or,[1,7]⟩, ⟨.and,[15,4]⟩, ⟨.and,[3,0]⟩, ⟨.or,[11,14]⟩, ⟨.or,[16,17]⟩, ⟨.or,[18,19]⟩]
theorem winningLegal : ∀ g ∈ winningGates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [winningGates,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem winningCorrect : ∀ x : Fin 8 → Bool, Circuit.eval ⟨winningGates,20⟩ (List.ofFn x) = edge8 x := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem asListed : ∀ x : Fin 8 → Bool, edge8 x = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by decide +kernel
end PEqualNP.Outside.L_meta_14760

open PEqualNP.Outside.L_meta_14760 PEqualNP.CircuitLowerBounds
theorem PEqualNP.Outside.L_meta_14760 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
    have low : 11 < k := by
      by_contra! small
      apply excluded255 k small
      have same : graph = graphGoal 255 := by decide +kernel
      simpa only [←same, show vars 255 = eightInputs by rfl] using run
    exact ⟨winningGates,20,winningLegal,by change 13 ≤ gates.length; omega, fun x => (winningCorrect x).trans (asListed x)⟩
  · refine ⟨gates,o,?_,le_rfl,correct⟩
    intro g hg
    obtain ⟨op,arity⟩ := legal g hg
    exact ⟨op.imp_right (fun h => h.resolve_right (fun e => hn ⟨g,hg,e⟩)),arity⟩
