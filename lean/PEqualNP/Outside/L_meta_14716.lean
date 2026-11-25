import PEqualNP.Defs





namespace PEqualNP.Outside.L_meta_14716
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
def graph : Sig := (BitVec.ofNat _ (limbs64 [0xffffffffffffffff,0xfffffefefffffafa,0xfffefffefffefffa,0xfefefefeeeccaa00,0xffffffffffffffff,0xfffffefefffffafa,0xfffefffefffefffa,0xfefefefeeeccaa00]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
 (x 0 && x 3) || (x 1 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 6 && x 7)
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
 (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 6 &&& x 7)
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
 (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 6 &&& x 7)
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
 (x 0 && x 3) || (x 1 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 6 && x 7)
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

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([3, 4, 5, 0, 1, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([3, 4, 5, 0, 1, 0, 0, 0] : List Nat).getD i.val 0))

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

def samplesP196 : Nat → Bits
  | 2 => ~~~(0x204c : Bits)
  | 6 => ~~~(0x40b0 : Bits)
  | 7 => 0xeefc
  | _ => 0

def samplesQ196 : Nat → Bits
  | 2 => 0x2412
  | 6 => ~~~(0xbdfa : Bits)
  | 7 => 0x1828
  | _ => 0

def compactPerms196 : Array (List Nat) := ([[], [118], [98], [98, 118], [114, 118], [114]] : List (List Nat)).toArray

def compactDomains196 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray

def compactWords196 : Nat → Nat
  | 0 => 0x7
  | _ => 0

def compactCount196 (k : Nat) : Nat := match k with
  | 3 => 1
  | _ => 0

def compactPath196 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => 0
  | _ => 0

def compactLive196 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => readCompactBits compactWords196 (0 + 3*i) 3
  | _ => 0

def compactPoolIDs196 (k : Nat) (i : Nat) : List Nat := match k with
  | 3 => let v := readCompactBits compactWords196 (3 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords196 (3 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket196 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP228 : Nat → Bits
  | 2 => ~~~(0x808048009483c18 : Bits)
  | 5 => 0x5cff212fd9f20f24
  | 6 => ~~~(0x110129325032c1e4 : Bits)
  | 7 => 0x79f9fc9e7f48fdd8
  | _ => 0

def samplesQ228 : Nat → Bits
  | 2 => 0x820008114000046
  | 5 => 0x2382761e089b5f20
  | 6 => ~~~(0x6eefc7d77db4f9f6 : Bits)
  | 7 => 0x642414461105990
  | _ => 0

def compactPerms228 : Array (List Nat) := ([[], [118]] : List (List Nat)).toArray

def compactDomains228 : Array (Sig × Nat) := ([(subcube 32 0, 4)] : List (Sig × Nat)).toArray

def compactWords228 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def compactCount228 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath228 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive228 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords228 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs228 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords228 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords228 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket228 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP166 : Nat → Bits
  | 1 => 0xbbfcb27bdd9d0ec6
  | 2 => ~~~(0x2000a241901d00c6 : Bits)
  | 5 => ~~~(0x80c01824080f630 : Bits)
  | 7 => 0xebcfe1bff280f7f0
  | _ => 0

def samplesQ166 : Nat → Bits
  | 1 => 0x44a16929088b5e84
  | 2 => ~~~(0xdeff9fb7bcfce5ee : Bits)
  | 5 => 0x85400948424214a
  | 7 => 0x16350632302c65e0
  | _ => 0

def compactPerms166 : Array (List Nat) := ([[], [113, 82]] : List (List Nat)).toArray

def compactDomains166 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray

def compactWords166 : Nat → Nat
  | 0 => 0xf
  | _ => 0

def compactCount166 (k : Nat) : Nat := match k with
  | 3 => 1
  | _ => 0

def compactPath166 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => 0
  | _ => 0

def compactLive166 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => readCompactBits compactWords166 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs166 (k : Nat) (i : Nat) : List Nat := match k with
  | 3 => let v := readCompactBits compactWords166 (4 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords166 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket166 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP230 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0x6f2f9ff58e,0x7dc01ff7ee7ebcbe,0x542f80087bff9cee,0x327b2638015ddc60]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x48010018b,0x642400018843c238,0x442f0a187b000ca8,0x63343e380fa19c78])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0x5edfff3bc9,0xeab89fdb9ffd4f79,0xec57812a7ffa6f9e,0xc1f4e6f800e3b8e4]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x830013044,0xe8c8e012003c0c06,0x3c57852be01a3c5e,0x8048e6f8f0447be4])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x7cbff1ff77,0xe4647f3ff9f3c206,0x3fff7e119f1ffc79,0xef0c1800ffa47f18]))
  | _ => 0

def samplesQ230 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0x10d8742261,0x20eda21042a5a11,0xd946698112d78824,0x102814b6555d5440]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x481500008,0x4424108241020001,0x4044401040830240,0x884200a410504106]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x2124025412,0x10412508821484ca,0x9912408d286402,0x40904a4922a2a8a0]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x77cf5fcbfb,0x5f7f13bfdf3f717f,0x6feccbfdd89f7e7f,0xf9fae7a4fed47ff6])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x342064280,0x91b0314180c505a,0x988002c181c5019,0x2100460066843e10]))
  | _ => 0

def compactPerms230 : Array (List Nat) := ([[], [118]] : List (List Nat)).toArray

def compactDomains230 : Array (Sig × Nat) := ([(subcube 2 0, 5), (subcube 0 2, 5), (subcube 64 0, 4), (subcube 128 0, 4), (subcube 32 0, 4), (subcube 32 2, 4)] : List (Sig × Nat)).toArray

def compactWords230 : Nat → Nat
  | 0 => (limbs64 [0x1feff6dce,0x1fe09f948847fe3f,0xc372d27177fc4e0f,0xf1be4971463ffffe,0x8c9846847816ac1f])
  | _ => 0

def compactCount230 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 3
  | 4 => 1
  | _ => 0

def compactPath230 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords230 (29 + 12*i) 12
  | 4 => let v := readCompactBits compactWords230 (221 + 12*i) 12
    (readCompactBits compactWords230 (209 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def compactLive230 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords230 (0 + 5*i) 5
  | 5 => readCompactBits compactWords230 (65 + 6*i) 6
  | 4 => readCompactBits compactWords230 (233 + 7*i) 7
  | _ => 0

def compactPoolIDs230 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords230 (23 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords230 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits compactWords230 (91 + 5*i) 5
    let n := v >>> 3
    let bits := readCompactBits compactWords230 (83 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 4 => let v := readCompactBits compactWords230 (240 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords230 (240 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket230 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords230 (106 + 2*(i % 2)) 2
    let off := ((i/2 + d) % 9)
    let v := readCompactBits compactWords230 (110 + 11*off) 11
    if v >>> 3 == (i/104729)%251 then [v &&& 7] else []
  | 4 => let d := readCompactBits compactWords230 (242 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 5)
    let v := readCompactBits compactWords230 (244 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | _ => []

def samplesP182 : Nat → Bits
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0x4600c80b5,0x824d020a080719c0,0xfc0c13ec8602c061,0xac5787de3328a7c6])) : Bits)
  | 2 => (BitVec.ofNat _ (limbs64 [0x5faffcbfed,0x8dcc7ffb3bff183f,0xfc0cd26c7e7ee1e7,0x99f3805e3167e342]))
  | 4 => ~~~((BitVec.ofNat _ (limbs64 [0x310100628,0x2cee012000f0140f,0x3825da7e003466d6,0x8123f07e38427b72])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0x767f9ffebe,0x6a6a7f6eeff015c1,0xfbefda5217ffde57,0xa54ff0602878bc72]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x6f5fffc731,0xb6f57fbfdcc7ffce,0x3c3501acefb766f8,0xee34079e138a7f84]))
  | _ => 0

def samplesQ182 : Nat → Bits
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0x7b9bfb2f5e,0xfdf6d7ef7d5df5af,0xf770fcf7d6d3ebfb,0xbf5fde9bab3cafde])) : Bits)
  | 2 => (BitVec.ofNat _ (limbs64 [0x205081c210,0x60134a6010004a84,0x110f4402cc4c0181,0x811102689545c102]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x318110308,0x466448c20085485,0x1510582054430028,0x30490a08ab348488]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x982300900,0x9184940241593403,0x445000851293ca02,0x40098822a382c50]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x10a1241846,0x808b1010c332052,0x48c0205023b02050,0xa04b186408a3a04]))
  | _ => 0

def compactPerms182 : Array (List Nat) := ([[], [114, 84], [33, 116], [33, 66, 84, 117], [65, 117], [65, 82, 116, 117], [81, 66], [81, 114, 84, 117], [113, 114, 116, 117], [113, 82]] : List (List Nat)).toArray

def compactDomains182 : Array (Sig × Nat) := ([(subcube 2 0, 4), (subcube 4 0, 4), (subcube 16 0, 4), (subcube 32 0, 4), (subcube 128 0, 4)] : List (Sig × Nat)).toArray

def compactWords182 : Nat → Nat
  | 0 => (limbs64 [0xff0ff0b763487,0x59e22ff0b34c0af9,0x46803fe06b7178a0,0x51592ff07f81d62c,0x668285993fc1fe0b,0xc4ff83fc11f34286,0xfffd00900688d11f])
  | _ => 0

def compactCount182 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 2
  | 4 => 1
  | _ => 0

def compactPath182 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords182 (26 + 12*i) 12
  | 4 => let v := readCompactBits compactWords182 (313 + 12*i) 12
    (readCompactBits compactWords182 (301 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def compactLive182 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords182 (0 + 5*i) 5
  | 5 => readCompactBits compactWords182 (50 + 6*i) 6
  | 4 => readCompactBits compactWords182 (325 + 7*i) 7
  | _ => 0

def compactPoolIDs182 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords182 (20 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords182 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits compactWords182 (64 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords182 (62 + 2*(v &&& 1)) (2*n)
    compactIDsFromBits bits 2 n
  | 4 => let v := readCompactBits compactWords182 (332 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords182 (332 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket182 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords182 (68 + 3*(i % 4)) 3
    let off := ((i/4 + d) % 17)
    let v := readCompactBits compactWords182 (80 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 4 => let d := readCompactBits compactWords182 (334 + 3*(i % 2)) 3
    let off := ((i/2 + d) % 8)
    let v := readCompactBits compactWords182 (340 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | _ => []

def samplesP244 : Nat → Bits
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x120000c06180,0xa0a4088401327078,0x28013308c21a0411,0xc362c3e00fa704b8])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0xdd2ffdf172ec,0x6083ffcdf3cf70ff,0x1c240300f7ffb4b4,0x71e5e1e008db5c88]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xfa4fe6fee333,0x9403fcfefdb0ff0f,0xe03884223f3ffb47,0xc27e5c0210eee444]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x41506400e23d,0x46d01008c08df00f,0xd030c733c5043866,0x40e55de2f81a67cc])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0xf7dfffcfed9d,0xeaf7fbbfcffff078,0xfbd37319efde4c7b,0xcfe3c3e0efb727b8]))
  | _ => 0

def samplesQ244 : Nat → Bits
  | 2 => (BitVec.ofNat _ (limbs64 [0x120400444080,0x8005120028002420,0x4100000884810206,0x2801088840105106]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x22d122478507,0xe6f84194316b6a2,0x71899d5026f590a0,0xc12ca8cc5ad95c80]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x5b08f119c0c,0x23ba6870c2038199,0x387e37c13b2e7881,0x8078862339eea440]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0xbeaddafd5bcb,0xbb2f5eeba9ebedf5,0xf749aabd87ad6e6f,0x6bd57db8fd3a77ee])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x82808100240,0x1100408200c10111,0x40002401084448,0x280442021222228]))
  | _ => 0

def compactPerms244 : Array (List Nat) := ([[], [84, 114]] : List (List Nat)).toArray

def compactDomains244 : Array (Sig × Nat) := ([(subcube 16 0, 5)] : List (Sig × Nat)).toArray

def compactWords244 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount244 (k : Nat) : Nat := match k with
  | 5 => 1
  | _ => 0

def compactPath244 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => 0
  | _ => 0

def compactLive244 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => readCompactBits compactWords244 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs244 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let v := readCompactBits compactWords244 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords244 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket244 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP242 : Nat → Bits
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0x2040002c048838,0xe0110401171583ea,0x56708081c0812,0xa745b1e03f15819a])) : Bits)
  | 4 => ~~~((BitVec.ofNat _ (limbs64 [0x8a0404079ca45,0x200039041e187820,0x473de8c33000072b,0x8c3c7c189e347a78])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0x7c6fd9efecae65,0x7f5ff7d561df875,0xc0f888c7fe5f770a,0xa57ecc1881977960]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x6e9fe67ff3d858,0x27fffd8fbf107faa,0x1f0d6007f9fd89f3,0x9e3d30001ff4e618]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x7beffffc5dcbbe,0xe7fb3ff7dfff83ea,0x6735670f3fbe0e3f,0xefc5b1e03f3d9b9a]))
  | _ => 0

def samplesQ242 : Nat → Bits
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0x5fbefef2fff7cf,0x7ebf5fbdfded6ef6,0xf75efbfd5b5fbb5f,0xbfdfd7aebb97adbe])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x8a2684018c0c5,0x26040a9185492424,0x220ca91409539044,0xa24b0282a9828584]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x390a2d08b4188,0x7cb05830a9280ce2,0xa1586b355a4e3242,0x81591628a3972920]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x116449940c4683,0xca620c1cac53204e,0x2f0395cf1351150,0x984d309a49e4e408]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x4180209a03000,0x1189010042209981,0x8902008306880809,0x4808c6106191a12]))
  | _ => 0

def compactPerms242 : Array (List Nat) := ([[], [101, 113]] : List (List Nat)).toArray

def compactDomains242 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray

def compactWords242 : Nat → Nat
  | 0 => 0x1f
  | _ => 0

def compactCount242 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath242 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive242 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords242 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs242 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords242 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords242 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket242 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP246 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0xfbb3fffacff3debb,0x47fd13ca71affefc,0xfff77fc3a7fc37a5,0xfcbff511faa0adad,0x42fdf9f07030093f,0xbff4efe7b3c5fe7c,0xb7e179fbfd01ff8c,0x847ff01a11af01ab,0xfc2944c4010f2f9f,0x8cfbe7cd6a7b1f8f,0xa8708fa4c270038,0xf380e65e7598324]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x200a0000c80b0604,0x45429270e1800080,0x40021c8287003780,0x17c00801f8b824f8,0x62f8ac06f071d940,0x1000e60c0260dcc0,0xa7006d801fc9e02f,0xe0790f8809ff01ab,0xfc01d7c7830fce0f,0x2cc138180a3f169c,0x1f03dc71703ff838,0xf3fef4e1619cbf4])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0xbf5cfff7ff1f8bae,0xfcc0713c8f0fffe3,0xdf9ffbf27f07ffbf,0x8ff0cb83e61e0e1a,0xcf982463b001c93c,0x7fffff9ceef1c3f1,0x7f19dffc383fe017,0xe0878f8783fd83e0,0xe1c040c38003f9dc,0xffc73ebf8f3c2e34,0x43667c0cf201f800,0xf1c3cd651874834]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xf66eff3dffef2d75,0xe72a8a35626ff9ff,0xefebbc3fdff84be5,0xf340feedfd78a249,0xb2e2c68c4b32003f,0xfc6bfffb433bfdc2,0xcfff66bbc2c001eb,0x7b7800fdedae0254,0xfe29241c094c3e7f,0x7c3fd8fa9dbbd04b,0x750097f551e600f8,0xa0393e0eb84708]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x36103300007083a,0x228c71bf62700000,0x8e0123417f004ba5,0xe800f00007788b09,0x9ff854f973b3ef00,0x2c40081001812340,0x5f0112bbe037e1df,0xe006f097f7af0254,0xfc286cdf8d7fc190,0xdc02c0e805fb096f,0x63043c8ed1e7f8f8,0xfffc00f661f87f3c])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0xefebfffff8ff765e,0x3bdef4f3e0dff79f,0xfe7fffcdff03ffda,0x7fcf387e11f951f0,0x3d781c1ff4c1f663,0xffdffe7c1dee3fcf,0xff06bf8707ffe07f,0xe0007f807e537c1f,0x1c169b038630dfa3,0xffc0f97870c701fc,0xbf19fc03b018f800,0xf047e3ca3078f8d0]))
  | _ => 0

def samplesQ246 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0x44c08213a080140,0x3000c8348a416050,0x810103ea8114319,0x450a80445050000,0x28000602014b841b,0x8d4444090009200,0x480082294440334,0xa010826a14480a30,0xd99410124020048a,0x8870a1c560220482,0x280004a001410b6,0x21588661a5508204]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x200a400068420204,0x5028220c0844402,0x140202a82405210,0x2504002080102010,0x240280420610052,0x2258011208012028,0x14100014008815,0x800244820802290,0x9118008002088100,0xc22204c640008900,0x60500080888042a4,0x445000a141c4100a]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x40a3110840703403,0x21e06c170be0804,0x920e058113641044,0x3906042a80e09065,0x10b902846b030e0,0x732a898062820541,0x292185482098cc49,0x4aa324112aa13082,0x209a52c94013910,0x6387162a8b082224,0x504451462816300,0x46a5389450874820]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x991045a0110d00a,0x84d354a1518902c,0x60488c1000c8cc2,0x98815592206254a1,0x51d007080845ba4,0xd4213a28201a4c00,0x4b608119690a20c8,0x58911908a150445,0x2643030db0133a75,0x340d483815992201,0x14001730204b0849,0x10a4791e0a284500]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0xfc9edecdefdaefcd,0xff778f64dd8dcdfa,0xbd5bfaebcedff671,0xff7d06e7ff97e6de,0x6e56ff5eeded18d2,0x7ef9697edbbdfb6b,0xf6d51ef7f66fba5f,0x39ddff5cef8fefb9,0x9339f6b36fba8790,0xfe67cdee56f78def,0xfbd4faeedbe7dea4,0xfdf6c1f761fcffbe])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x1014804103000880,0xc02109040d018180,0x2001404008198401,0x805100846a00020a,0x40004100090c0800,0xc81606401240002,0x90000284c0462200,0x21189300840c0c21,0x400009800680,0x1c40c90010440048,0x8800a80010461800,0x3100c1422038a090]))
  | _ => 0

def compactPerms246 : Array (List Nat) := ([[], [84, 114]] : List (List Nat)).toArray

def compactDomains246 : Array (Sig × Nat) := ([(subcube 16 0, 7), (subcube 32 0, 7), (subcube 64 0, 7), (subcube 2 0, 6), (subcube 0 2, 6), (subcube 4 0, 5), (subcube 128 0, 5)] : List (Sig × Nat)).toArray

def compactWords246 : Nat → Nat
  | 0 => (limbs64 [0x1b912fce44c1825,0xff0ff05631a1920b,0x77ff0ff0e19dc558,0xb1c5096baffbebeb,0xeee4c17311cc4131,0x4c2825425025ff1,0xfe385ab1ff1fe352,0xa9cff05529540521,0x798436104325876,0x99876210435fffff,0xc12a12812d0a323f])
  | _ => 0

def compactCount246 (k : Nat) : Nat := match k with
  | 8 => 1
  | 7 => 3
  | 6 => 5
  | 5 => 1
  | _ => 0

def compactPath246 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => 0
  | 7 => readCompactBits compactWords246 (27 + 12*i) 12
  | 6 => let v := readCompactBits compactWords246 (368 + 14*i) 14
    (readCompactBits compactWords246 (332 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 5 => let v := readCompactBits compactWords246 (664 + 12*i) 12
    (readCompactBits compactWords246 (640 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | _ => 0

def compactLive246 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => readCompactBits compactWords246 (0 + 6*i) 6
  | 7 => readCompactBits compactWords246 (63 + 7*i) 7
  | 6 => readCompactBits compactWords246 (438 + 8*i) 8
  | 5 => readCompactBits compactWords246 (676 + 9*i) 9
  | _ => 0

def compactPoolIDs246 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let v := readCompactBits compactWords246 (21 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords246 (6 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 7 => let v := readCompactBits compactWords246 (204 + 9*i) 9
    let n := v >>> 5
    let bits := readCompactBits compactWords246 (84 + 4*(v &&& 31)) (4*n)
    compactIDsFromBits bits 4 n
  | 6 => let v := readCompactBits compactWords246 (493 + 5*i) 5
    let n := v >>> 3
    let bits := readCompactBits compactWords246 (478 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits compactWords246 (685 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords246 (685 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket246 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let d := readCompactBits compactWords246 (231 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 9)
    let v := readCompactBits compactWords246 (233 + 11*off) 11
    if v >>> 3 == (i/104729)%251 then [v &&& 7] else []
  | 6 => let d := readCompactBits compactWords246 (518 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 10)
    let v := readCompactBits compactWords246 (520 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | 5 => let d := readCompactBits compactWords246 (687 + 1*(i % 1)) 1
    let off := ((i/1 + d) % 1)
    let v := readCompactBits compactWords246 (688 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | _ => []

def samplesP254 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0x37fe65c8e6e45ea5,0x1eaffea1405dcf6c,0x7f67437f0241bf7b,0x16731f89bf5d94a8,0x5fbf81e48009fa5,0x87fdee443c86602,0x81e9335805c39945,0xcff0000b90780ae0,0x100011e000f85eeb,0xf199fea24affd2ad,0xe5d6fe1fba5bf88,0x335b9a874bc1eb81,0x47b1055f2003260d,0x41f960c0e70072c0,0x2e007c58049926b,0xf345b50e8c5c0c44]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xc0d3fe7ff89800ff,0xf9fb4c9809a1abff,0xc4abec0e27ffc1ae,0x9de000ffebf22a01,0xb800fffc105f6000,0x7ec0f5e6200eddde,0xc2000007fe3ca690,0x82bffed86500e,0x7f4001f3017b7c,0xfa4f39a11fa0fbc1,0xf38b82bf708a3fe3,0x46fef6e3032d764,0x7ed00024bec050,0x3f8e423707f80001,0xf00f783a106a44b3,0x84703d33d1a0d013]))
  | 3 => (BitVec.ofNat _ (limbs64 [0xff2c107f1f5d7f30,0xe1f54f63ffae5798,0x7c913e91dbce1bd6,0x157fea743403f282,0x17c003a3ec97ef20,0x10003182bc100a0,0x3c026cb1001d442a,0x7627d5f000018001,0xa0008e000c00ffbf,0xfffdb95fee2ce2f3,0xcfebfd4e1eafc37d,0x7d922c30b24c0419,0xf803b0fe1b70fc0c,0xe01ad37e0078000,0xd008000207bf9ff,0xa29c8aa0322e0108]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xfe0fdf801fe28bc0,0xfe000ffe0ffffc00,0x84becfe1fc07e1ff,0xea9ff58fc03c0003,0xe83f040400e80fff,0x8180fc03d5f19f40,0x3ffd901a07e2003f,0x8037fe00007800f0,0x380003e001eedf0,0xfff7c9e7f0d0fd7e,0x73f470179f52f43e,0x87fc33c1cc4ef81e,0xc40087dfc30077,0xc00e07c8f880007e,0x3007c1c0f46edd,0x47a1c4c323c12064]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x37f185c8f91bad5a,0x1eaff15eb0523093,0x7bd8b37efdb9be84,0xe9931f79bf626b54,0x5c40019b700905a,0xf67f2118423679fd,0x41e93344023c6685,0xcfc8000b90060a06,0x100f11c030e0afd7,0x2faff75ab5ff2d2e,0x8da2eff9e45947b7,0xcaa459794bb11461,0x4736fa58c000d98a,0xb1f698c018787280,0x32c100140037af3c,0x87b421d4c2d1c10]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x8d3fbb70767f0ff,0xe754b367f601abff,0xbb54108e27fe7e51,0x620ce0f6548dd5fe,0x4200ffe3efa00000,0x7ebf0a199c0ea221,0x3c16cca7f9c3596a,0x30082bf47201a509,0xec70ae01cc01f47f,0x47ec65c1f5f0411,0xfc7412be8f74385c,0xf86ff4908433289a,0xb8492fa024bd3fa0,0x3e71bd0807878d01,0xcd0e80202f147702,0x780e3adc21d2038b]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xc92c2a37e0bff70f,0x15ab09dfffe5467,0x836ffdf1d8304429,0xffecff024a800d7d,0xfa3f0040137f70df,0x810000e7bc31001f,0xc216cfe8f800bbd0,0x39d7d4046f807510,0x4f80601e0306938f,0xdff276bde1031fde,0x301f9d4061ffc8c3,0xff91c40e358c03e6,0xbf884f21db4c03f3,0xc000523f18000d3e,0x10780a5f8f99c4,0x9d824160de13e2a0]))
  | _ => 0

def samplesQ254 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0x442204248480e21,0x4c43828110808028,0x250145090800080b,0x104c28190a0484,0x25104b12824440a4,0x8012445031862402,0x50914180128a2825,0x2d02388641086045,0xa40048426411a2a,0x511824200a4a9288,0xa0c4b8049240e88,0x215b880311406181,0x122101112100440c,0x44c9400222022a04,0x2a8c124982491062,0xf144b10a88180804]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x10c00c101a180c80,0xd96a02410005a160,0x40200c0162a00028,0x84040062102a0c02,0x608264200428490,0x21400222a10c2028,0x84000144644a004,0x8012045042040c0,0x4a008acc54a38,0x9849008008205841,0x2308020d108024a1,0x4612e003060d308,0x44c0000c18c048,0xd81021046200010,0xa209a129106840a3,0x4502c0391004012]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x774494b36e4c9c91,0x48e7474b9abca729,0x1606411c98a9b1a,0xb4ac652230a0ca4a,0x12544464892d8209,0x1158624a48588aa4,0x94a0e95504898892,0x5280a28deac250,0x4c0d96ffa441dbbf,0xffddb80dc42ca263,0x40c37c081cab8371,0x5182262212445138,0x9b42b15a597064c8,0x44838973ea133100,0x131822230fbd9ff,0xa29888a0122e0100]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xd00dc59002802192,0x241c5806543110,0x88a4a2b24087c054,0xe6050086a0105010,0xd00e300430a21512,0x24843920ca01c389,0xa48240960454110,0x39405116278b1a,0x3094c028800865d0,0xac67c98600806c30,0x717000178642f006,0x6a412e08a0e180c,0xc0a206c8120860,0x901605d840a08058,0xc020219464b46e99,0x62104c123c12040]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x4204c0892101b05a,0x204740a02321491,0x1848a0f6000ac294,0x23a32305a254a060,0x4881008854813208,0x1a89090406214845,0x624186808204648,0x92a88620b0828712,0xb5b102620118a5c5,0x26a6d352b5950504,0x84a2a470a0104112,0xca004168ca860c20,0x49103a0a40401882,0xb0320949081914c2,0x144208144116af1c,0x82b421444251400]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x810420000202002,0x2010102440001814,0x81090a204506404,0x201001484043030,0x8182119862000106,0xc04101000a20502,0x1c040020200329,0xb1804a1060001122,0x30900000102a2440,0x22405013530010,0x9c1000a20340100c,0xa00c905088130802,0x2a000850a00,0x9210300801008c08,0x5cc6008084042600,0x5006125c20c00089]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x6200007e042d005,0x1400231a0440b,0x342400018080a02,0x8e0f50041c0028c,0x284108200d086021,0x8203040c14500040,0xc00190a0180204c2,0x640140001980000,0xc030fc640009007,0x439036296000018e,0x59140601d0840,0x1810400604000060,0x3f08151803400591,0x4000080738080386,0x110184203039144,0x898041204c128220]))
  | _ => 0

def compactPerms254 : Array (List Nat) := ([[], [84, 114]] : List (List Nat)).toArray

def compactDomains254 : Array (Sig × Nat) := ([(subcube 8 0, 9)] : List (Sig × Nat)).toArray

def compactWords254 : Nat → Nat
  | 0 => 0x27f
  | _ => 0

def compactCount254 (k : Nat) : Nat := match k with
  | 9 => 1
  | _ => 0

def compactPath254 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => 0
  | _ => 0

def compactLive254 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => readCompactBits compactWords254 (0 + 7*i) 7
  | _ => 0

def compactPoolIDs254 (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let v := readCompactBits compactWords254 (8 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords254 (7 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket254 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP201 : Nat → Bits
  | 0 => ~~~(0x20041b0188c9532 : Bits)
  | 3 => ~~~(0xc287c5403533d8 : Bits)
  | 6 => 0xeffe7b3fcacb7b2
  | 7 => 0xbbed1c75bf51d58
  | _ => 0

def samplesQ201 : Nat → Bits
  | 0 => ~~~(0xdf7ff6edfbffdf6 : Bits)
  | 3 => 0xe0a5429205cc24
  | 6 => 0x104080444800092
  | 7 => 0x450a22a0925cd40
  | _ => 0

def compactPerms201 : Array (List Nat) := ([[], [96], [115], [115, 96]] : List (List Nat)).toArray

def compactDomains201 : Array (Sig × Nat) := ([(subcube 8 0, 4)] : List (Sig × Nat)).toArray

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

def samplesP217 : Nat → Bits
  | 0 => ~~~((BitVec.ofNat _ (limbs64 [0x480140,0x670981902200c111,0xa0f03d46f1490123,0xc28e8f661d4cba6a])) : Bits)
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x1300206,0x68607be0095007bd,0xe2041b757005799,0x2023596aef360fb8])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0xdd3eb7e,0x6ed9600ffff2ed95,0x26a37c0051fdfdab,0x2a6f8862017fe808]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xbfbffe7,0x7722f3bf2f7ff7fb,0xf8f41176a2eb77d7,0xd2a2c704fc3c9762]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xf6ff7df,0xe96d99cffbddd33d,0x8f78ed87555fd339,0xe59f596a0fc63ab8]))
  | _ => 0

def samplesQ217 : Nat → Bits
  | 0 => ~~~((BitVec.ofNat _ (limbs64 [0xfb76eff,0xdcf7ff6befbcfded,0xdff7dffdcf7bb9fb,0xdfaff77f7dddbbee])) : Bits)
  | 3 => (BitVec.ofNat _ (limbs64 [0x1320225,0x4800536980288d44,0x892450254053a042,0x8c08210f11c93044]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x22c318d,0x80228fde0e80075e,0xb31925c802fc7820,0x23aaa0b73fe800]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x4044088,0x550c0220103008,0x1211060005281091,0x1280022024148122]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x910220,0x1480202141044800,0x824501088038108,0x4104410f00c01288]))
  | _ => 0

def compactPerms217 : Array (List Nat) := ([[], [96]] : List (List Nat)).toArray

def compactDomains217 : Array (Sig × Nat) := ([(subcube 8 0, 5), (subcube 16 0, 5), (subcube 0 16, 5), (subcube 1 0, 4), (subcube 64 0, 4), (subcube 128 16, 4)] : List (Sig × Nat)).toArray

def compactWords217 : Nat → Nat
  | 0 => (limbs64 [0x2f22ee50a01fa,0x506c7e807844e91f])
  | _ => 0

def compactCount217 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 1
  | 4 => 1
  | _ => 0

def compactPath217 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords217 (29 + 12*i) 12
  | 4 => let v := readCompactBits compactWords217 (83 + 12*i) 12
    (readCompactBits compactWords217 (71 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def compactLive217 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords217 (0 + 5*i) 5
  | 5 => readCompactBits compactWords217 (41 + 6*i) 6
  | 4 => readCompactBits compactWords217 (95 + 7*i) 7
  | _ => 0

def compactPoolIDs217 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords217 (23 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords217 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits compactWords217 (55 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords217 (47 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 4 => let v := readCompactBits compactWords217 (102 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords217 (102 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket217 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords217 (61 + 1*(i % 1)) 1
    let off := ((i/1 + d) % 1)
    let v := readCompactBits compactWords217 (62 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | 4 => let d := readCompactBits compactWords217 (104 + 1*(i % 1)) 1
    let off := ((i/1 + d) % 1)
    let v := readCompactBits compactWords217 (105 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | _ => []

def samplesP205 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x6efe,0xfbdf0b7a2ff3cff6,0xc9ee9ec6a0e7bae6,0xf63938e94c6b0b34]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x380,0x8a19a30bb80003a5,0x92d9cc7fcf102fc,0xac001efd4d404ffc])) : Bits)
  | 3 => (BitVec.ofNat _ (limbs64 [0x7b3f,0xaee9a7d4179fffa5,0x9d59d5c00c577dbc,0xad17e49c4857c09c]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x800,0x600b742000cc00,0xcdc052f820e60900,0xa639e8ab5acfb134])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x5fbf,0xdf70fb2da76cfff9,0x6fa57a3970a7cf59,0xaee8da2313ccf560]))
  | _ => 0

def samplesQ205 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x1109,0x200908491100894,0x3104810440a9222,0x421004128a90824]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x385,0xb112203b3422407,0x2b904c809096b500,0x408c2045eabb9002]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x4e0,0x1984480b6e88820b,0x78c4842522056c90,0x8110823cd256c090]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x77fd,0xffdffecfffdeefdf,0xffffffb7ffdfffbb,0xe7bdfffffffffdb6])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x2050,0x108a04404c044148,0x5044800209414809,0x2200523810446500]))
  | _ => 0

def compactPerms205 : Array (List Nat) := ([[], [50, 112]] : List (List Nat)).toArray

def compactDomains205 : Array (Sig × Nat) := ([(subcube 1 0, 5), (subcube 4 0, 5), (subcube 8 0, 5), (subcube 128 0, 5)] : List (Sig × Nat)).toArray

def compactWords205 : Nat → Nat
  | 0 => 0x41c9f
  | _ => 0

def compactCount205 (k : Nat) : Nat := match k with
  | 6 => 1
  | _ => 0

def compactPath205 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | _ => 0

def compactLive205 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords205 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs205 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords205 (13 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords205 (5 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | _ => []

def compactBucket205 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP213 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x5f2ffaefc5,0x8b5827f73dfe2ba3,0xf43e158a45f3fee7,0xac994c04d96f4168]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x550008f79,0x8859780205a02bf9,0xc02895dbce003fee,0x4044fc4df06c3fc])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x764fa5fd3b,0xc4c047ebffe9f35d,0xca2100018bffbdbe,0x1706f3c00076f204]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x1020006081,0x869ac0013040e005,0xc017782bca830036,0x9be7c381d14e2c])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x7dffdffef9,0xbebbdf9ff7f7ecfd,0xc1dff87bcb8f737e,0x40ffefc387d1cebc]))
  | _ => 0

def samplesQ213 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x20d2449230,0x74075608218e3c46,0x8396149b1c2ee07,0x90188204e1ed4108]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x551089759,0x10116d589082350c,0x90aa219a99a9c402,0xb249a095a0f92402]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x9b84e2690,0x193ebb8a0ac2496a,0xdcd3b328957f3412,0x940cd2d94b76f200]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x6fdf7ddfff,0x7d777f5bbfdfbfdf,0xbbbff7ffbdebef37,0xf6dfffb7f5fd6fae])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x204000006,0x40000104110000,0x40400000120,0x40820800000008a4]))
  | _ => 0

def compactPerms213 : Array (List Nat) := ([[], [32]] : List (List Nat)).toArray

def compactDomains213 : Array (Sig × Nat) := ([(subcube 1 0, 5)] : List (Sig × Nat)).toArray

def compactWords213 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount213 (k : Nat) : Nat := match k with
  | 5 => 1
  | _ => 0

def compactPath213 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => 0
  | _ => 0

def compactLive213 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => readCompactBits compactWords213 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs213 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let v := readCompactBits compactWords213 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords213 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket213 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP157 : Nat → Bits
  | 0 => ~~~((BitVec.ofNat _ (limbs64 [0x980200a0020fb3,0x6004002943039184,0x2b2f1a5441029a00,0xe311e2cb2b1a85e4])) : Bits)
  | 2 => (BitVec.ofNat _ (limbs64 [0xdd4fe7fad22c2f3,0xfc4ffff77738d84,0x1cef1003fb7bd200,0x1ff7f00329f9acc0]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x425044209d0c28b,0xf000e80022910be0,0x58efbed480500780,0x1f3906dbaf8940fc])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0xfa8ffcafcd82f80,0x6ffff8adfa8953e3,0x6b200a57edffafe6,0xe31902c802fa5324]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xefffff7fbd7dfbb,0xffffef7be397bbfc,0xfbefbed7d7d6df99,0xff39e6dbaf9fc5fc]))
  | _ => 0

def samplesQ157 : Nat → Bits
  | 0 => ~~~((BitVec.ofNat _ (limbs64 [0xf677def6ffef34e,0xdbbcdf2efb7f9f73,0xcfdcfba57537fe78,0xf3e9fcff6a5eb5f6])) : Bits)
  | 2 => (BitVec.ofNat _ (limbs64 [0x22b42815855751c,0xe2d18a1740acf9a5,0x155079fbb1190a2,0x46735041d9f92c40]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x42514224cc4c202,0xd9b09620091d1f10,0x4c0c2b0175264070,0xc2c0c81c6a56b502]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x5724b18367441f,0x1e158211b5208239,0x3d65d71b04fbaaa2,0x465a4b4106f85320]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x100080204080040,0x108410808110400,0x4000002040044408,0x3100201c20068094]))
  | _ => 0

def compactPerms157 : Array (List Nat) := ([[], [66]] : List (List Nat)).toArray

def compactDomains157 : Array (Sig × Nat) := ([(subcube 4 0, 4)] : List (Sig × Nat)).toArray

def compactWords157 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount157 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath157 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive157 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords157 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs157 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords157 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords157 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket157 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP221 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xfde5ffdbf7cd8fed,0xdfe2c5c3e94bfff7,0xfff5de57b66e9fbf,0x43dfe23fa7a7cb01,0xe07b909cf8ce0915,0x3e7bf7fefd9fd06f,0xc9d35defc7f1c8f4,0xd07bdc137cd141fa,0xab0609b5041a8af7,0x3fe4acddbaf3703e,0x79bc10c71c17081c,0x8b38475b27901654]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x8cb000a06218261,0xc4bb56eaf27c0076,0x20000417e1821e08,0x42610227f6f735c9,0xf24bf1c1e8eeabff,0x80004502d04d0002,0x85daf794161c0,0xd87e7dba7f0f41fc,0xdc864dbfbf1fcf02,0x910c904130f7fdf8,0x757f40101207ff1f,0xcb3de01755593ffc])) : Bits)
  | 3 => (BitVec.ofNat _ (limbs64 [0xee9eff7eeeebfa9e,0xe4f9ba686407fdfe,0x69ffffbf6383bde9,0xeeeeb7a98a2917c8,0xb647f7d116260080,0xbff7ff67d74c73be,0xff7f939f7b41e331,0xc54e847a070b71d4,0x7cbe0420911248be,0xf73e9bf2ef899cc8,0x75774c066ef26812,0xc2240b94cbf9011c]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xde68feafff37ccf3,0x989f02821283ffff,0xfe2bafe6cd975e4e,0x93275ffe545630f1,0xd8036962e0000240,0x3fdeeffffa6fac57,0x31aefff3bb8d34c8,0xaa742b8cbb2481ed,0x54c000000a0505ff,0xfbdf7ff974e6af31,0x663be03893088701,0x2fe7555e2020]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x4004000060058c9a,0x42aa0161080500,0x40000a0000051c07,0x86f3b889060201,0xe473f97a16c74e44,0x2502240d20e8045,0xc9779240020196b4,0xc74d8a043c0121df,0x37c7ba214e1f8d85,0x67342cf04288a230,0x713750ef9df38f15,0xba6277b42fb8e274])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0xfbdffdff7ff5b77b,0x677e7e3df33bff7f,0xf7de7f99f9fd7e17,0x7cf1fbf7f9d6240f,0x67f8f96b0fc1ee6e,0x33fd7fdbd2ff8fc1,0xce7dfe6c7c7e1786,0x5f8d7ba47c0f2e1f,0x97c1fa0b6e0d85cd,0xc53df467531ce3f0,0x914753f991e59705,0x3843f4b43c29eae0]))
  | _ => 0

def samplesQ221 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x21a202208507010,0x419322406154406,0x1034203850118240,0x2c01060205100c8,0x9c06620061060c8,0x904894c4002c5050,0x1508c0340b0c080,0x30c8244d00212026,0x80403012050538d3,0xa24208d08701036,0x23400c08c008808,0x9a0554a24901044]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x8cb104b0a211021,0x45ab164ad27f2123,0x485612a00a10a88,0x4b702a7236936543,0x32d2a30042acaad2,0x391b9a5061a61931,0x641386819018699a,0xe1dd02c4114024a0,0x8d149014a6595cfd,0x26b1061ccd280413,0x2a118663c5500248,0x5ea21fe8a2a44002]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x1161808990840060,0x5306419398ea8861,0x98808408a062019,0x51394e195206c426,0x20300800c8099b25,0x62276a23c5022304,0xc0200188b00b2b4f,0xca078a20c4045009,0x680181098ad0002c,0xe5129862a7010c81,0x70030c2600c21007,0xc6462a94cb290110]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x2197047032c01324,0x6548ed7d657cf2ab,0x408424527abcace3,0xc833083b31b4642,0x24d8228543f7453e,0xffd045bd43271112,0x4098b4d192188650,0x19123cab9d7316c7,0x25d8dc70c6511afe,0x99cf6fb170a08613,0x22190472964aab60,0x110cefe3555e2000]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0xbffbf7efdfff7b75,0xffff77ffdeffefff,0xddff6f7fdff7fbdd,0xfbfdff7ff7ffffff,0xbffeefb5efbdfbff,0xfb7ffef7f7affbf7,0xedffffdffebffbff,0xffffeffdf7edfdbf,0xff75fdffffff7eff,0xefb7beffeffdbef7,0xfb3fdeffdfffdedf,0xfff77ffeefbdfb76])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x4204080800a0800,0x8800008008800810,0x8042020080020010,0x1008440800201810,0x8004001020001001,0x24200210008080,0x80440040c070005,0x200800040044008,0x4000008010220000,0x4000904202042040,0x8100500800241007,0x8040001408018a20]))
  | _ => 0

def compactPerms221 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains221 : Array (Sig × Nat) := ([(subcube 4 0, 7), (subcube 16 0, 7), (subcube 1 0, 6), (subcube 8 0, 6), (subcube 0 16, 6), (subcube 64 0, 5), (subcube 9 0, 5), (subcube 17 0, 5), (subcube 20 0, 5), (subcube 24 0, 5), (subcube 128 16, 5), (subcube 4 16, 5), (subcube 5 0, 4), (subcube 68 0, 4), (subcube 80 0, 4), (subcube 132 0, 4)] : List (Sig × Nat)).toArray

def compactWords221 : Nat → Nat
  | 0 => (limbs64 [0x34620c4585af45a0,0xb4564ac3556a4545,0x27a4d694525a3442,0x87d0e91c3358630b,0x713d22e3705f08d0,0xc41501b000220788,0x1563508080088560,0x885258141825078,0xe05065288a2a288a,0x9141a2a20906928,0x88ca229045078625,0x4420208872581424,0x2508086014088188,0x801482150c82020,0x4920518854321408,0x818808604670288f,0x31c0e21e18c4d22a,0x4d288988e703512,0x89c18b510c604981,0x8b4d2889e8e70291,0x346009e2322a22a2,0x6698a22d1135fdfd,0xffededfdbdbefdfe,0xdfdfdfdfdfdfdefe,0xddfdbfbfddffbfdd,0xfdffbf7fbfddff7f,0x7fbfdff5fdffbfbf,0xdddfefefafcfe7ef,0xafe7efefad261526,0x36613660b660b66,0x4a624a602242a66,0x22242a6622462226,0x2206226602260124,0x2922296622e60443,0x2c222c2629c329a2,0x29e629a629a323a4,0x2bc32ba22ba628e4,0x28a428c328a228a0,0x28e628a628a320a6,0x18e610e610642824,0x2843282228202826,0x2823202020462026,0x20261e42c32c2240,0x2242a32222a22202,0xa02200960ff80629,0xb4e6e7f859eff858,0x5c1bc040194b37f8,0x55a24d6707a1ff81,0x8c1acd375abb5199,0xb0e5d3b3a530864,0xc50e80cc02830442,0x4141452146208230,0x506ca9408a8c8d01,0x84b1900505187254,0x6012c46030a0a096,0xd2540915049200a0,0x53282500a3034540,0x92061148a004658,0x9a02384ca99050d0,0x19389bfffefefffb,0xffdffffffffbfdc8,0x5485865c45445445,0x4054648444448044,0x4403401a298843f])
  | 1 => (limbs64 [0x89266859a266899a,0xe22c653264c0530f,0x1899318cc4111046,0x773ddacd66f37ecd,0x6f9779bd72ef37ae,0xd66e6f9b9ee6e7b3,0xeb3cdf979b9ed9ee,0xd37e5cef9ddacdce,0xe7bb3d9cee77b3d9,0xdf27b75ba5d7b3f8,0xee762f975f67b3e9,0xf8be5f3e9f4fc5f2,0xf3f4dadd599c5b4e,0x8670c338619c0bc,0xe45670ab383c90af,0xce17e700121409c2,0x4e036707511709c,0xd4445a670fd11659,0xc32ce0ba725d398e,0x90b34459e70d9392,0xc9c164e62a429439,0x8690a34458a22c73,0x8a39c3c4c3e432f3,0x39789cbc464e271e,0x938139cd54e4aa70,0x55398890a4ce0124,0x28911459c88ce60e,0x428521430ca14450,0xe728539428c814e3,0xe7165381d9c4d40,0x46c6237393315113,0x3111173110173090,0x1330521721500631,0x1006196112196012,0x1950121950053161,0x1131601131511131,0x5011312195311115,0x31100530d0053032,0x1530219521511521,0x5005191005116011,0x1150151150111150,0x501501101500501,0x1004311115aea930,0xffc0253ffc0ebd8b,0x177cb799f055bfc0,0x4844dc8a1bd0204f,0x53fc0ff01be17dc9,0x34e071e8257d33fc,0x3cfd5aff03fc0f,0xf039dcd5d14eeff0,0x19d3ff01b9bb014d,0x55ff0051e3749119,0x181a76c95a2670ff,0x1871648aaa3e0d4,0x7449543fc0df76c2,0xb1f37e41a2a47273,0xb294e4c62d509ff0,0x3fc05c60bc06d091,0xa6ff035040007480,0x1880001c11811,0x40158ea454ba6548,0xe864ed9852ca5248,0x48c51521b4047c8f,0x9dab8a6fcd25a13])
  | 2 => (limbs64 [0x141c84a1,0x862fd677642ad57a,0x7fc3fc3fc0672bcf,0xfc3fc04192a96a33,0x1352eb795801a124,0x9249249582738d74,0x9d2a358d6358ce35,0x9d358b9274f2278d,0x6364b50034851485,0x8d017d016d01a507,0x4d062d04c4459504,0x9507048501075445,0xd404ce44c3401ce4,0x405401ce14c48658,0x65cc240486540440,0x14e68658444e6865,0x8044e68654044e54,0x44014e48654014e,0x10c44454e0865401,0x4e00c44454454044,0x1b511fe039e05e2,0x91f4ae70fbc17f80,0xd055fe02f59ff806,0x65f74fb3611dc14a,0x64058e874624153,0x43089d4c3eb8c51b,0xa473dc5d339bd2ff,0xe03fc0638ab76460,0x8ffc072107b69fe0,0x3c10ff804e01fe02,0xa507f80ff007804c,0x9e7f802527be30bc,0xed786664ee4b8416,0xfcb59877fe02dd87,0xf80ff00867f15bff,0x80e13dfe0339e8da,0x8120a803cf135692,0x372b34ea80a1f04c,0xb37fe00515958935,0x223c65c5b6e87e95,0x8fec4ddf8530095c,0x600a090340329804,0x40526262665252,0x5642463232362222,0x2612121212121212,0x1212160202020202,0x5f5e5d5c5b1b1b5,0xa1a1a1a1a1a59191,0x95857565554d1115,0x104f4e0e4d8b4a8,0x8474606c34280952,0xaa546993203c9901])
  | _ => 0

def compactCount221 (k : Nat) : Nat := match k with
  | 8 => 1
  | 7 => 14
  | 6 => 55
  | 5 => 68
  | 4 => 16
  | _ => 0

def compactPath221 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => 0
  | 7 => readCompactBits compactWords221 (32 + 12*i) 12
  | 6 => let v := readCompactBits compactWords221 (1387 + 16*i) 16
    (readCompactBits compactWords221 (1255 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 5 => let v := readCompactBits compactWords221 (6234 + 17*i) 17
    (readCompactBits compactWords221 (5466 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 4 => let v := readCompactBits compactWords221 (10736 + 16*i) 16
    (readCompactBits compactWords221 (10232 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | _ => 0

def compactLive221 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => readCompactBits compactWords221 (0 + 6*i) 6
  | 7 => readCompactBits compactWords221 (200 + 7*i) 7
  | 6 => readCompactBits compactWords221 (2267 + 8*i) 8
  | 5 => readCompactBits compactWords221 (7390 + 9*i) 9
  | 4 => readCompactBits compactWords221 (10992 + 10*i) 10
  | _ => 0

def compactPoolIDs221 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let v := readCompactBits compactWords221 (26 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords221 (6 + 4*(v &&& 7)) (4*n)
    compactIDsFromBits bits 4 n
  | 7 => let v := readCompactBits compactWords221 (858 + 11*i) 11
    let n := v >>> 7
    let bits := readCompactBits compactWords221 (298 + 5*(v &&& 127)) (5*n)
    compactIDsFromBits bits 5 n
  | 6 => let v := readCompactBits compactWords221 (3739 + 11*i) 11
    let n := v >>> 8
    let bits := readCompactBits compactWords221 (2707 + 6*(v &&& 255)) (6*n)
    compactIDsFromBits bits 6 n
  | 5 => let v := readCompactBits compactWords221 (8268 + 8*i) 8
    let n := v >>> 6
    let bits := readCompactBits compactWords221 (8002 + 7*(v &&& 63)) (7*n)
    compactIDsFromBits bits 7 n
  | 4 => let v := readCompactBits compactWords221 (11162 + 3*i) 3
    let n := v >>> 2
    let bits := readCompactBits compactWords221 (11152 + 5*(v &&& 3)) (5*n)
    compactIDsFromBits bits 5 n
  | _ => []

def compactBucket221 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let d := readCompactBits compactWords221 (1012 + 3*(i % 5)) 3
    let off := ((i/5 + d) % 19)
    let v := readCompactBits compactWords221 (1027 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | 6 => let d := readCompactBits compactWords221 (4344 + 6*(i % 19)) 6
    let off := ((i/19 + d) % 72)
    let v := readCompactBits compactWords221 (4458 + 14*off) 14
    if v >>> 6 == (i/104729)%251 then [v &&& 63] else []
  | 5 => let d := readCompactBits compactWords221 (8812 + 5*(i % 23)) 5
    let off := ((i/23 + d) % 87)
    let v := readCompactBits compactWords221 (8927 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 4 => let d := readCompactBits compactWords221 (11210 + 4*(i % 6)) 4
    let off := ((i/6 + d) % 21)
    let v := readCompactBits compactWords221 (11234 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | _ => []

def samplesP253 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xe6bbe3f0b6ffecbd,0x33ea6aff4276e15,0xf3b9acfa0aa1f792,0x9763373f82b4ad60,0x3c3fb77c502640cf,0xa3fa9240411979f7,0xb40dad36a0369905,0xac0e394daafda608,0x786720d6f0803804,0xdac29d1fc7655e1,0x8da579a2c24e6a5f,0x7d40a972e99c4cb0,0xc05fd460ce3c087c,0x1847896601e50c86,0x2f042bb360a0531,0x79e2949588892c94]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x99dd72dfddfeff67,0x6c6bef50bfd88b17,0xc4d7df00cae733dd,0xe8adc18917cf53f9,0xc8376bafab84ed93,0xfc00209f82e63418,0x424f20595dc01f00,0xd3f1c2b0c24286bf,0x8698c4090017c230,0x7201c1ef9edab8a3,0x1ef9bd9d373baab4,0x3b8c329f5621307f,0x860eb945400af82,0x1d1ef606b646f000,0x1d019d44c0819976,0x5a2c08aed3464023]))
  | 3 => (BitVec.ofNat _ (limbs64 [0xf6bebd8eefe75fc7,0xafd7d3a61cf8b14f,0x19e9dfdd1dfe1c3e,0xc7d278f1e9717c90,0xb7c6abd216a70a03,0x9421cb16c301d022,0x6c6007a0aa03605a,0x2f08fd8b1d80f957,0x18001800ca0024c1,0x12623bed7fddf5e,0x67354f7a3d99d2e5,0xa7b57d57abc34704,0x738101ecab375613,0x8006388f76040962,0xcc60022100debf,0x81150f25bc60021c]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xf9f7ddffb77f94fa,0xf33d5956eb27d0b2,0xecb870e7fa5fe872,0x5f9cb7fe7c34d39f,0x7bd84363c821b52c,0x43d491a83d188648,0x33925ac95435e6a4,0x10013946540159e0,0x400000200060000a,0x805017fdefffba67,0xf59bf66dfaebf77a,0xb4fa9ee4d59a8b48,0xbc26366030fbf060,0x7a14621c99a0201,0xe00200000804eff6,0xf298b1532f908040]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xff43feff4f87fb3f,0xfcc003f90027ffe8,0xff4600fff501ffed,0x27ffc83fffcb01ff,0xc01ffc805fd801f0,0x3ff6c007ee6007f,0xc80ff001ffc80005,0xc00fc6b000fe0000,0x6007c0870003c030,0xe0002fff7a7ef99,0xfa5e81d0fd747d9f,0xc5ff4f88fe60703f,0x78179f00c0007f,0xe0f80fd801f8f004,0x300833c0200f6cb,0xeccf660a40d94020]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x3fec6f2f78b9b7f0,0x90aabcf95fdd1eef,0x376e7315371806cf,0x38350f46157bfe06,0x3fe89cffa45b5204,0x5c014de100fe4f84,0xdf08f3e02097dfa,0x5df40640373f2037,0x81601b581f9c05c1,0x70034a66697be2dc,0x93c2329f88f59503,0x5a33e3fd005ebcc0,0x7799e80b7508a789,0xe259309948030178,0x1c2d204195726a48,0x3461db4823203b0b]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x4f7f9f71fb586bd8,0x5fd57c0fe3da65f8,0xa17af2ae5fec921,0xf84afec0ea8eae6f,0xc7e1541de158be78,0x280e367fbc01ab81,0x93b050c601fe82fb,0x22f2003fe9005fc8,0x8798272025681b0e,0x80d8971b3b8d753e,0x686ece6747860de8,0xca4fd42b00258383,0x8f8608138bc75984,0x7fa0c170be390699,0xe0121c8048fd318d,0x871260f0543695c0]))
  | _ => 0

def samplesQ253 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x408901001440a415,0x90614050412,0x1008a0c280,0x4004063080000160,0x3400402c00060158,0x400c143010214,0x442025000000405,0x22040242a0800080,0x18008010080035,0x5161410c100060,0x8108a082002a08,0x19008810401c4030,0x4026c00010340008,0x1800400601a00206,0x200381a0090110,0x58a0809088012084]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x88c00488054a001,0x4520ab0286418106,0x10c201002040d0,0xc224029830580028,0x1913480509034319,0x490082851349a004,0x2c4004002904805,0x4248524020c03204,0x1208008410810516,0x219271458e581021,0x4292c8420132804,0x3984321500092018,0x106262b050118302,0xc02e00290844004,0x8820a9c2a0818934,0x5a24088692020022]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x12362484c32241ca,0x2f86c01188c82020,0x51c98407544a1040,0x2740500a61f1340a,0x4b46a1012db14a24,0xeca2862a0820f008,0x9a21110a6a422030,0x450808154450a802,0x4685486045035c4a,0xe504029ed3ccd40e,0x4634454a149810e5,0x6a52447aa800509,0x328025ec82431610,0x240602c872082848,0x56e0524184dcaf,0x81150d2514600210]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xd92111ea353d0479,0x8581c972c461620a,0xc86aa041c23870e6,0x4a84f35e2054523e,0x1902c707540c38e5,0x1647164544c4718,0x74a682b8189e4f08,0x21665502c00b9385,0x6328f9a9d2250616,0x2d1069edef7fb845,0x819a722dea6bd638,0xa4189ee0478a0358,0x182a74a910d90230,0x8e2b462358824a22,0xce000a050d2ceff6,0x728891532f908000]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xa442fa3548835a28,0x308440b1000a7a68,0x454e24ca500b392e,0x2108d14300811692,0xc048b50212101480,0x90923902882204c3,0x6011e984c448a292,0x88130ca11b17086a,0xa0e14b216b746840,0x840482ba71a7ef90,0xfa4281105d244113,0xc06b41089ea20145,0x98040f02401075,0xa0b90a484a4830d0,0x2349041c0a1276cb,0xa44b660840d84000]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x25004a0320881200,0x8142001004209,0x2202314020002426,0x11894004028210,0x4d202082000,0x1040400004040141,0x482490040188,0x8821012013080121,0xa820050302240000,0x208042020232290,0x1140121100408402,0x401201a0044218c0,0x4090001250020a0,0x8069101008000030,0x4509000006222240,0x2040524821000909]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x25084100a000980,0x20540009201800a0,0x1000c2211060001,0x310200000a810c01,0x40e02000a0a00400,0x24100c0880021082,0x8810300224008022,0x41000940c040048,0x8300100100c8c0,0x902402121080410a,0x28048042018401c0,0x240400a08008003,0x818008040a005800,0x6100014806191088,0x2016440840101009,0x8512202040241440]))
  | _ => 0

def compactPerms253 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains253 : Array (Sig × Nat) := ([(subcube 32 0, 9)] : List (Sig × Nat)).toArray

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

def samplesP251 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xd1cfdfe0177ff396,0x417819fe7fd401f5,0xfe537ac00f23fe52,0x3d0afa7fb600e200,0xfffdff48200927f7,0x6f0429203b84bbdb,0x4093d77fdbd00000,0x67ee99c9698004fd,0x80de1de017e003e0,0xde251e399368e2,0x64b25f39205f7807,0x6df904e5dbb00f30,0xd001ff41700b87ec,0x2a23d4068fa8006,0xf81247ab82c2125,0x1d9926252c2b4629]))
  | 1 => (BitVec.ofNat _ (limbs64 [0xfe87fafffbf7bff9,0x6e0dfe61c6e38be9,0xdedc1c43b96dfad,0x40dd92147ff9571f,0x4abfbbbd4a7e5a5c,0xa62806ca807b5c00,0x636003cb6003a4cd,0x7e17e6168039ff22,0x1e0e202a0010011,0xe101c6e6d37d09c9,0xff1bd6e5fbf6ddab,0x94d319b2640b741f,0x151e138a0be8021e,0x6395e88334c00e58,0x100e5b850000cb53,0xcb527019c7e83042]))
  | 3 => (BitVec.ofNat _ (limbs64 [0xa1f8e35ceef9ffe9,0xa5ffefc8627aae0f,0x70735ddfc9fd11f2,0xbea30ddf8970bdea,0x61fe0c176078101e,0x20fa43c81001ba66,0xae0fc0090ec09b2,0x80e803e93fcf8808,0xff020018019a030e,0x41a0ff7fed3f71e,0x18ac2fc63fa46f2e,0x9e77baff1bc449c0,0x67e020e1ffc2fa83,0xc1003a9c34117004,0x77120000402fdf8,0x9236338630d0010d]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xefff27bf179fcc97,0xbb77960bfdab503a,0x3fd32730fedfe050,0xcdf6f5e0423fddf5,0x810df0a02086cde9,0x90045adfe4050458,0xb46f28812b3ff640,0x1910e5c856700b09,0x7ed0e20028003800,0x3a20df99ef70ab3f,0x847de83edc58f7d7,0x72eec5dbb5af82d6,0xa8025c4080f77d10,0x75e004fd7040009,0xe002db814013365e,0xe615ce63a248052]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xff77feffefe9bf6e,0x908de195b91c75d6,0xcdbebe3b346adfff,0xb2df6d947dc6571f,0xb4b244429571a3a3,0x59d38d35407ee3a4,0x639c03ca9403a4cd,0x1718200039f0d4,0x13c01c282010011,0xc1c10fffedeeddf5,0xfbdba6da3ba9a250,0xebace34c7a4b7808,0x151d8c340b1405e1,0x9869d7334bc00e50,0x180c04761003f6bc,0x248ccb19c8c73000]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x7e3bdd5ff87e4cfd,0xfe8219f7906fffd5,0xf3ac953fc22125ad,0xc328f26bc9ffa8e0,0xff428077df803400,0xfbf0003ffa4437,0x9d13f43464ac5b32,0xf6687636864602f7,0x211c1d541ec40e,0x4002a7937ecb6e3,0x9f4451f7c41f8ff8,0x2d06fe05e474872f,0x6ae1a1be84090053,0xfc23c2bc802171a0,0x700008afcf1a86,0xe08785da07184d84]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x1ffc3da3fd86737e,0x5ff2663e0f95fe2a,0x820ceaeff5dc2a0f,0x7f750fabb68f2aff,0x1e4143889f87c800,0xdf05b437cf800189,0x9c0c08340f505b3f,0x89810817f9867502,0xfe0100254864fce0,0x1a2419efdebf561c,0x63e7b909c7e310fd,0xd3197f3a8010b0e1,0x8afe421f7434f82c,0x3cdc05608b2e81a3,0xe080800043f1cde9,0x71688860d1148ab0]))
  | _ => 0

def samplesQ251 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x500c004013000094,0x4008000810440020,0x10000d000400,0x10208000000e200,0x80c000091008,0x9000292004010013,0x4180208040800000,0x119110001000060a,0x8100020000000400,0x520000000002800,0x412083120400803,0x400004e040300800,0x5000410000028040,0x280000068040006,0x1001448a08200000,0xd01202124214021]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x540290d2a1432a51,0x621004042820108,0x109000100020904,0x104082911108104c,0x4221114041423040,0xa541082a41233031,0x11c2412801894506,0x235524842525420a,0xa54830040050a244,0x8808004492180081,0x521314a172961ca9,0x45310b240082405,0x448128222201204,0x4105080004824542,0x5249098308888943,0xc952301185882002]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x2190c218c491f00a,0x3b5ca4480b29204,0x5461465950841057,0x140124c99d520865,0x22b4090632128486,0xa4890849030288c,0x28245144304d83a5,0x2008a2c468401140,0x3050a1489884c0f6,0xfa4a0df7dad30618,0x18a827041f044624,0x987428191a804140,0x226c04633b445886,0x48042b1515106620,0x392a8200412edf8,0x9234128410d00108]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xa80c2704129c0086,0xa0800683a1100442,0x3e228000f2095020,0x4ca5700002370100,0x240c6c830489c62a,0x101475411608044a,0x6a102c8166402090,0x1c809a2a10000d11,0x835043ac9830800,0x20c066992d602b22,0x46c481e8048e342,0x52a08549a58540d2,0x28c2400d50180,0x840a404f8014100c,0x8802460c65333614,0x60144e63a248040]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x83616c2948289522,0x30908384891836c0,0x56b68a50504dd2b1,0x435300484530523,0xb414042c18a00a85,0x826448400944740,0x619185384149061,0x882208608a92a865,0x12240c49c8ab5922,0x6242cfbb6de6d174,0xa940824a0921a010,0x2b8c630412875042,0x125843411440da1,0x884ad1158140a298,0x29240034504776bc,0x208ccb0848461000]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x823190700640c60,0x200210a001010451,0x8202812400294020,0x822c102040810100,0x54220210c606060,0x4310043020c1120,0x4b043082007010,0x466000a06366030,0x806040062030800,0x55208252090c3,0x830440c0801a01c0,0x2502d004a045022a,0x800a00484080110,0xa02a40a080001180,0x806c0201310d1206,0x4082855a02080484]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x6d000a02c024308,0xa71a05404825a00,0x400122d30014201d,0x30000183b54000f5,0xa30100863100801,0x230a8008c1824a84,0x1424000e11100642,0x82080400c1c19004,0x60060c00400c06f,0xca1a0966d29d440c,0x6081b10044a1101c,0x80090a0202008000,0x80fc000a7300380c,0x58140d1007228070,0x6090a11000c0c9e9,0x30680800c1100a10]))
  | _ => 0

def compactPerms251 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains251 : Array (Sig × Nat) := ([(subcube 8 0, 9)] : List (Sig × Nat)).toArray

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

def samplesP247 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xc69d87ff8effbc1e,0x3fffdc7cafff4f6a,0x57d1edd6ffed2029,0x63f74dbda2392db2,0xa9cc3f69f41f58a0,0xa01a13b7b6451018,0x9c8c4a82ea36f340,0x67c2079f58030476,0x6f1c314c70a0519,0xd4041290053dff62,0xbfec381e73f29bc9,0x8fce9e5116c1a026,0x98289bcda1659374,0xce8602a1f87160a0,0x900045a15c395fe,0x8f4c128086692320]))
  | 1 => (BitVec.ofNat _ (limbs64 [0xfff1fbf8f7d6fe9f,0xe3fc4fd77bf2545f,0x68971b23fae19fdd,0x1e48fd3fc547fbd0,0x1b727e948b6eff74,0x2165adcce500e204,0x373b48f41033e64,0x800cb96c790c4989,0xff4c00b508304a20,0x20008800f06f1b7f,0x5e61ff0bd33df277,0x4c73763b67945de0,0xe78b2438a45600ce,0xe40f90b23601340,0x20e21b20680007d1,0xcaa16c3ae3e01844]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xbfe3dffef9ff4ff4,0x3e0ef22fd7eb8bbd,0xadfa129714f6d21f,0x751ff245fbc872ef,0xd49c8d5e3ff0a400,0xd790ee48019a4067,0x401ab409b3cc09bf,0x88f2021186f0b266,0x80affea20c480c6,0xda650f083fbde3,0xe37f01b42e2364ee,0x8a75f71fecee4059,0x3951c4f351a2fc80,0xd01b8d32138e0000,0xd61de08580005df6,0x10706e4f1806400b]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xf89f7f4f7ff8cff9,0xfbcfbffbaa3cbe8b,0xa72dee2d1f153c36,0xfbf88dc45dbead4c,0xb6d3f0f62b9f5740,0x5ee510b748596f98,0x60938973143902b8,0x673df462a01cc409,0x89013c1408300a20,0xb00006032b7efd1,0x7395c9fdcfce9cb9,0x77b659fe91f99e45,0xa635630c40996388,0x3d650c9dc480805f,0x21b202a003aed,0x1c95998c1d508054]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xff6ffc770729f17f,0xdff3af97d7cda454,0x9096f4dbe51b5fe2,0x9db70f3a3a87d62f,0x5badbeeb4b71a08b,0x219a417b1aa19de3,0x3ec408cbec33d9b,0x180cbe907913b209,0xf0b200a1c00c441e,0x3008eb00c852defc,0x9d9bf6eba0c16d7e,0xbb8a69a48f6a1d98,0x584ad8355a480331,0x1b8f64adc6e1380,0x2ee0049c50802e2a,0x253b8075e4195808]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x79fe239dfc7ff3eb,0xccf571effdde7bb7,0xfe6fa1f8e17aedcd,0xa04db2d26e795f3d,0x6e234125f48601df,0x802ac00212e007f,0xff650b7408f4c444,0x10e3414d86ee5db6,0x3f71c4b37013140,0x44f50405013a779c,0x8cb6ce547d9d7f10,0x70fd86cefb15a23f,0x468418c22fa7ec6b,0x209c704403900c00,0xd11c0002857dab0d,0x614671701ba02683]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x77efca3fb873fe7,0xf53bfff87c35f1e0,0x5b685f6c0a8ee3f2,0xcea272eb95f680d3,0xe57fc39bd4e90a3f,0xde6d5200def6bf80,0xbc0077704508c003,0xff1148a207e12bd0,0x740ce34a10c3b081,0x8b2310fa068de0bf,0x604a37e39c7e8387,0xf509a9e178026382,0x1f627029e181c17,0xf36303f42c11ec3f,0x1e041023e7010,0xf28a8783609685b0]))
  | _ => 0

def samplesQ247 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x81841c8c80001e,0x31045054863544c0,0x4d3a1450a600004,0x56a50015c8700060,0x88c321234160280,0xa1885000690f5000,0x200c0a8f510d0144,0x2004c321021450,0xd0c200020f004a0,0x502478650c7db962,0x3024080a23b28048,0x8544904006c5a040,0x180947c120c08060,0xce010023e80080a0,0x210204e2904255f6,0xe44028082412020]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x355190e89156268a,0xa0a8091449930441,0xc43010090800910,0x5600082040444830,0x802081008589191,0x850206c4c7313280,0x8408a2501e0a520,0x8a0122077150602d,0x63041a48a40100a5,0x188400080c69106a,0x4a40a50b11155245,0x4c41660b62841120,0x481042980528040,0x492320404a22,0x24d8412138490551,0xcaa0642ac2a01004]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xa100467049640b14,0xe402285218dd0,0x47321030224120c,0x56292000e85020e9,0x814105a04120110,0x20a07290a01a2428,0x4104a60880405,0x2044068042143438,0x4a08506420500cb0,0x540530a18e7db961,0x236001902a2100a8,0x8824e41c44048050,0x2901c54151c0c840,0x4403803362040088,0x459088c1a00055f6,0x10604a0e1002000a]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xc08a630666a8c941,0x1303126b220c0088,0xa214261126216046,0x287101408c988740,0x9445500645034602,0x183c291208c4c52a,0x710b10c038050a51,0x3476806802870140,0x423602551565442,0x611232211116ef91,0x118508d44cca8cb0,0x2332117491588441,0x8a10694402890180,0x642d148c4084804c,0x58028e0643123aac,0x141519841d508040]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x4a26280302015020,0x4e51a68010482000,0x20004490601264c0,0x1120508108a9300,0x400442143202464,0xa11010900c08005,0x44a144100e105a08,0x1110503008218282,0x9053050343003002,0xa350000230024694,0x849b526080402512,0x128a09a0082a0c81,0x20018100a000310,0x13c300410222541,0xa24200c4284aa08,0x211b805124184800]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x18780101201a80c1,0xcf0218920c00226,0x6008043021086041,0x8010910002898304,0x6620400041004046,0x1006084e04200306,0x118240000470c030,0x8403c01818808307,0xb0600c0a4100920a,0x2110011050824690,0x8c12c60444087a00,0x60980282b108040f,0x420408000224250a,0xac104401000c04,0x126c02000991aa09,0x4102317009200281]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x604188010013420,0xc0008c0058001000,0x1100180800008020,0x428201000002,0x10081808080b021,0x601040102000081,0xc60843002003008,0xb00300400604080,0x10030008080100,0x884000000000c,0x4008302190040107,0x1001080108004200,0x62000204001005,0x1040020004126303,0x6108000c0000,0xa088840160840510]))
  | _ => 0

def compactPerms247 : Array (List Nat) := ([[], [32]] : List (List Nat)).toArray

def compactDomains247 : Array (Sig × Nat) := ([(subcube 1 0, 9)] : List (Sig × Nat)).toArray

def compactWords247 : Nat → Nat
  | 0 => 0x27f
  | _ => 0

def compactCount247 (k : Nat) : Nat := match k with
  | 9 => 1
  | _ => 0

def compactPath247 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => 0
  | _ => 0

def compactLive247 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => readCompactBits compactWords247 (0 + 7*i) 7
  | _ => 0

def compactPoolIDs247 (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let v := readCompactBits compactWords247 (8 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords247 (7 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket247 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP238 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0x5f3acf,0xfffe5e7cf7ab83bc,0x9f890a500ffdfe9f,0xc7fff8d1fdf8651d,0x37fc7e5d6ffca066,0x8244fc39d1df0200,0x887fbffedfe7a7f,0x472f69fd2f3fba3e,0xf1f592d7e0e6042f,0xf948c34058cfc580,0x2380777f2bfdd,0x7f7bf1ba332e51f2,0x3b82c87d81c0e505,0x8000bbe964e6e180]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x4a020,0x2001052c0816380,0xb8e2885440003018,0x6000c01f2006110,0x374003f000ff1462,0x8257f005f982e270,0x3898000000f07248,0x3e002fc01f403c,0x314197ff003fc407,0xe60c1fe018ffc001,0x5f07f867063c1e18,0x6a0b03c083227fc2,0x7f03f81ee007ff1f,0x84073c7388c6f1f4])) : Bits)
  | 3 => (BitVec.ofNat _ (limbs64 [0x77d48f,0xfafff1f3e2eaecc3,0xd02260270ffff3fe,0x3f2fff996f06fff2,0xff47e3fd0d031c10,0x62a321c657826030,0x2007c7fffff3ffc9,0xf8ff1e57f238ce77,0xff43ca1f1d3f3f00,0x26841ca184763800,0x1801c0607fcfb9ff,0xea9f6fe38c107e06,0x8f4f8b86be07001a,0x400ffc71a097024]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x7eed3f,0xffc7bfc7cb577ffc,0xe9769c688ffa7d7f,0xffffb72ff2fffb1d,0x4bc47db29fff4279,0x81b8f43e29a4ff80,0xc887fffcd3fdf5fd,0x47d289fad0ff75fd,0x3ff66d3700d9c4df,0xc63f2351a74fc580,0x203a39872ffd7e3a,0xffe57646c3f1d1f5,0xcb0d3c7a6038e565,0x8800761e89d76388]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x101400,0x460025c3028040,0x4901662880004000,0x630000d001f0d,0x4b447c100f00e81d,0x81a8f43a07850180,0xcbe00078c1000dc9,0x47c209d000208003,0xf0b6681700c03f08,0x1983e341e74fc59e,0xa03a399f20c02187,0xea7574027f1dd1f5,0x8b0c08611e38e565,0x8bb8f28c063f6f88])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x7db72f,0xc77fffffdd95f343,0x28c1e79c4ffffff9,0xfed67c669f011fef,0xff7b9ff2f2e0fd8f,0x9d5fd201ae018040,0x137f3c7bffffffca,0xbffef7afcdc7c18b,0xf0a835e80200fb00,0x1983ffee7bb9c27f,0xc70400187efc4787,0xea7f9fdd7f0fafc9,0x743070015e001a00,0x3bffcb0863e9c50]))
  | _ => 0

def samplesQ238 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0x20c538,0x1004a5c20844354a,0x6076452ee5602824,0x94644524c0564e46,0x431352a118495331,0x493142948c2821ea,0xa255b353a8a84293,0x124324e44612a010,0x2592123478a89202,0x8cb8a984a82d134b,0x32809132f5a29594,0x5c4ad13a160644a2,0x1284893504825455,0x6122abe964a4c100]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x4a020,0x8300014080807300,0x88c2804448404200,0x34c1086082054010,0x4282021002030260,0x103c20181028040,0x30812604a1020830,0xc215840c200900,0xd02301812200408,0x20ec001060080202,0x40166b1022044,0x109014130c8c0001,0x2c0b6401800044,0x4c68830c5028040a]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x82b72,0x7908604141d352c,0x2d999dd0fe0c8130,0xd56829521661a875,0x10900494a36da229,0x9d6546d8b848370c,0x5f9fc46655c294d0,0x9b662cd666430476,0x4508a949430a5c4b,0x2a454d50c900599e,0x72add22ffc53943,0x609d6ea11404a6c4,0x9b46992636936202,0xc58ffc612097020]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x112c4,0x81a421824088005,0x1601229112929402,0x400a008825280021,0x9c48a844c4242482,0x2604084812010415,0x12a48a812552000,0x4914801810491045,0x5024c18204450971,0x41010462069288a4,0x494848080a594a2a,0xa320224441109250,0xc101140822192928,0x9081541289532280]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x6febff,0xbff9bf5ebefdffff,0xbfff9df7ffcfff7f,0xf5ef7b7bfffdfbff,0xf6be67bfb3fff7fb,0xfff7effdff7bffff,0x7f9fe67ff7fe9ffb,0xfffffdfefeffbd77,0xfdbfbf79f33b7fdf,0xfbef7ffffdce7f9f,0x7fffff7efff739c7,0xfafffef77f9fffff,0xfbefbf7f3fbfe7c6,0x4fffffde563fffea])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x248d1,0x1c882000062c0c9c,0x132c1823b1898069,0xc028101a7118a202,0x84086421311c2001,0xca421f858186cb3,0x4c060019463c9188,0x3f0c6050c2c70054,0xc01c0a6121034310,0xc30060a60586400c,0x319fa004ef40081,0x8a6788c430018fc8,0xb300b0002e080702,0x1937c9006169840]))
  | _ => 0

def compactPerms238 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains238 : Array (Sig × Nat) := ([(subcube 8 0, 7)] : List (Sig × Nat)).toArray

def compactWords238 : Nat → Nat
  | 0 => 0x13f
  | _ => 0

def compactCount238 (k : Nat) : Nat := match k with
  | 7 => 1
  | _ => 0

def compactPath238 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | _ => 0

def compactLive238 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits compactWords238 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs238 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits compactWords238 (7 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords238 (6 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket238 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP237 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xf7bfff7fbfd3f33,0x6fdee1f5afff7e79,0xfffb8fdf99ffc1ff,0xba393f6f6017c32f,0x81dd18c77dffe793,0xfc67dccf2f747bf3,0x338c403ff3fe236,0x20fbfa65cf883807,0x87c9f46f47594e23,0xc1f630d9a478a278,0x42f388dd14c25654]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x20500020a043198,0x6059b58c20120000,0x87a0f601811c11c,0x63c476848560731,0xf0df1ed7c0630000,0x3829c0f40aa07212,0xe80fc027f87f1e6,0x20f6f065dffa3f47,0xc3b084461a1d4c3d,0x835c3741f828fe7e,0x62f3b9b9d8065fdc])) : Bits)
  | 3 => (BitVec.ofNat _ (limbs64 [0xbe6bffe6efbd1b8,0xf97549084ff2cfff,0xfdf66f663d9a7fbb,0xc714c36859493bca,0x31a210903ff7defe,0x679f5ffcaae8f6ae,0x52b5376294c671c7,0x34d6156000402342,0xcfb5ef9cff7cc93c,0x955d0c174f905066,0x60120392badc011c]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xfb53f1bffcebfcd,0xf18896980fffffff,0x1a7bf1e7ee1f861c,0x3ffe3871819e0c30,0xfe0820013efb7ffc,0x7879e0f7dfff8cfc,0x7c40f83c1fb87c38,0x3f03e001c301c088,0xffebbfe7a9e73c3,0x1e003f61f8670280,0x84e083ebd92a6020]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x208010004b8021,0x6196489080000219,0x101180478c1e0203,0x8138b879a189cb4e,0x812c38e90490029c,0x40101c492a740ce0,0x7078c76397386c31,0x37d30a7be381f88f,0x9589e338605ac3c2,0x1d561899a7f7a2e8,0xdef6c6d316fbe274])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0xeedbfff9f47e0ff,0x66f33c868fdfb39f,0xfffd9e79de75fb47,0xc5e8c498aee0c755,0xc0740e68a7ffbbed,0x9bb8bf797ab77f53,0xaccacfc363018de1,0xc3f40a9a30b21c05,0x1fbbc773b8e384dc,0x2b5ed388b3a8ac08,0x1a0477b146358ac0]))
  | _ => 0

def samplesQ237 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x84010802024084,0x1001040800510401,0x40c010002100500,0x102000088280090,0x1020021008108110,0x420008a00200a01,0x24000a208400021,0x8220002000200c0,0x2000502141014220,0x4004208004200210,0x60a044404405044]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x20520080b002108,0x4041948c00c02044,0x110e01a04a144540,0x124044040400220,0x400906501a948101,0x4014020024020048,0x23c204a308401029,0x2823104002080404,0x400150a96520a002,0x880880c00100210,0xa71a444624d08022]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x419444099940a41,0x608b2d7b9844910,0xa04294a0e8a6d065,0x124029140612d402,0x8a5da565f7c5522a,0xa815420180cd0a0,0xb59b4d098192b48a,0x2141511948315920,0x8f15a69cb4780854,0x151101106a82142a,0xe1544392b29c0110]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x4ac874a0110212,0xa366962fe248a00,0x2a00a64b10c89a89,0xd841498832035043,0x296d8aea06a7ec0,0x28c8644190449430,0x4414514c261b44d4,0x465c638c50d46900,0x9fee2b461a8a0145,0x610152128c338a5,0x8609ba9d92a2000]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0xfdf6febfff77fdf,0xdf6db7fffdfdefdd,0xff7fffbeefb7fd7f,0xbff77fdeff7ff6fb,0xfefff777fffddbbf,0x7ffd7efbfe7efff9,0xbffbfffffdfebfeb,0xfdf3ff5fdefffff6,0xff9df7fdfdfbebff,0x7fd7bfbdeffff77a,0xffff77f7b6fffb76])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x112422030b01600,0x830c0331750c0888,0x6020320aa022082c,0x8a101b020306700a,0x26127103652908a4,0x19804c105214b120,0x90091844a588a042,0x45102208c410cb12,0x8e98855088c800cc,0x24520300a989240a,0x482413b102250a00]))
  | _ => 0

def compactPerms237 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains237 : Array (Sig × Nat) := ([(subcube 32 0, 7)] : List (Sig × Nat)).toArray

def compactWords237 : Nat → Nat
  | 0 => 0x13f
  | _ => 0

def compactCount237 (k : Nat) : Nat := match k with
  | 7 => 1
  | _ => 0

def compactPath237 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | _ => 0

def compactLive237 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits compactWords237 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs237 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits compactWords237 (7 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords237 (6 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket237 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP235 : Nat → Bits
  | 0 => ~~~((BitVec.ofNat _ (limbs64 [0x8010000,0x2a05904a50188c,0x430000030184000,0x30079001800be041,0xe03f0e00906fc61f,0x700e09c200680000,0x3c0eb0078183c1e9,0x173008bff403f8,0x7a068000ff00e87f,0x850183f07fc38630,0xf033c383c1619ff0,0xf0f01f985c05ffa1,0xf0073a7073b78732])) : Bits)
  | 1 => (BitVec.ofNat _ (limbs64 [0x7dd4bff9,0x3bfeae978fdde830,0x85d43fdf7ffff7d0,0x90d79f3feb7be65a,0x5f3f838e9bbdc7aa,0x616008020007f6cf,0xfffffb35e9cd2fe8,0xb47f7bbeeb7758c0,0x7ac087281ae3e84f,0x950000004743f68f,0xf7bff7ada869b473,0xb0ba765d12c072a0,0x30003ce529ff4600]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x2058c000,0x384050078b8771d3,0x25dfc007420000c0,0x10d08e0e178400a0,0x1f3f138e9fb77ce5,0x1cd07e0e7ff800c9,0x800101c865800e68,0xa06a47075788bc1f,0xfa1987f81ae3e803,0xfcbffcf3c74a060f,0x3608181008eba07b,0x7009e3f8a9fa7fe2,0x33ffc0b691fc7fd8])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0x7b6b7f1e,0xfffd5defcaf2d1cc,0x664b3ffffffde8ef,0x78d7d13f94fc79a5,0xbfff728f14a2fa55,0x529e0802618729ff,0xfffe74ca77b2dfff,0xd47f74b914f8a73c,0x7f3ec72e1a03804f,0xe98e10004743ef7f,0xfdb7c8d25f713478,0x40b189baedc072a0,0x33d03312d7f33600]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x7e5fffe7,0xfffbf177fb5f198f,0x1dbeffffff5e5ffc,0x372fbec17f879fe5,0xffff0f708f4f3c1f,0x3c0ff9c01e7edfff,0xff0f8fdfffa3d5e9,0xab978f49bf8c03fb,0xfa07b8d1e5fc6830,0x7c31e3f038819e3c,0xf2783f73d98fcb8d,0xf0491fb85c258d01,0xc02fca72738cc9b2]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x6fb93fff,0xfc6e57987fa776d3,0x20303fe7f2bbffff,0xfff8eece978fe0fb,0xe0381c00f07744e5,0x9cd0760c006ffff9,0xbcffb1ef85dfea7f,0x6beaf7465780bc1f,0x801900d0ff00ffb3,0x86018cf38009fff3,0x3e4bdb9fe0e28bf2,0x7f44e3c0a93a0d42,0x73fbc90348158]))
  | _ => 0

def samplesQ235 : Nat → Bits
  | 0 => ~~~((BitVec.ofNat _ (limbs64 [0x77fefeff,0xbff7fbefbdefff7b,0xffdffddfbfbfdeff,0xe7ffcffffff3ffbb,0xfffffdffff9ff9ff,0xcffdffbffff6eff7,0xbffebfe7ffdfdbff,0xbfff3ffefffbfffb,0xfffe3ffeffff7fff,0xf8ffffefff3fffff,0xfbf3fbffd76f9ffe,0xfffaffbffcffff9f,0xf7b7fffbf7b7e7f6])) : Bits)
  | 1 => (BitVec.ofNat _ (limbs64 [0x22b5012,0xd5091129200214ce,0x722bab1224820085,0xfa6234a808cc48c4,0xaa92282445020051,0xa152569754dd48d,0x6aa8822041004922,0x3124292308cc5515,0x2985d2a14c72a52a,0x7a10a491211540a,0xa72eb72d28489122,0x9222241100892a69,0x284aace5296e4400]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x2058c442,0x1850702588853143,0x55df0430d111225,0x350840325110a28,0x8c5b20b6190528a7,0xb47e0258f6aa16,0x30c22a449246403a,0x9bd01b225112948,0x314a1b126a442600,0xa00a40e3db15f990,0xc9c322ca860409b0,0x1bb034856401b10e,0x45003f4944038024]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x4948869,0x882220091092a31,0x8990548911200a40,0x11942542621a50a,0x45090512a0190922,0x42092948a220962,0x95540442a2940288,0x4891410662120a0,0x9230094c23090a95,0x381285248904ab65,0x5091485252200498,0x4110888a24429484,0x91915312d6912200]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x1a02019,0x400088004204610,0xa200018082044010,0xa00040cc02606480,0x4080900100804000,0xc040000d81000421,0x830c01000c011001,0x8002004802681090,0x9400c4001b0033,0x10401000000a002c,0x3030103111030004,0x48022018000c01,0xb010c02233804092]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x1046c220,0x81d0b06380418928,0x5cc7cc470508860c,0x402b823309908322,0x2347607e0301982b,0x13c31b2269663d0,0xc3212c1820cc06e,0x3ed033049904c69,0x8a6a003a0524098c,0x88062061bf35fed3,0xa40c984c20003f0,0x37306581a42a0382,0x44833f9880348140]))
  | _ => 0

def compactPerms235 : Array (List Nat) := ([[], [115]] : List (List Nat)).toArray

def compactDomains235 : Array (Sig × Nat) := ([(subcube 8 0, 7)] : List (Sig × Nat)).toArray

def compactWords235 : Nat → Nat
  | 0 => 0x13f
  | _ => 0

def compactCount235 (k : Nat) : Nat := match k with
  | 7 => 1
  | _ => 0

def compactPath235 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | _ => 0

def compactLive235 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits compactWords235 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs235 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits compactWords235 (7 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords235 (6 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket235 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP231 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x776effef,0xfebbb36ec3d346af,0xbffff3ef2ffce57,0x1ff3ff7e83df8337,0x606ef418221dc407,0x9f71ffff3ff367f,0xc1b8ee9e6ff870d1,0x3e238c9c7d0bfe00,0xf1e70b45bc20605c,0xfecf8e7ae3125168,0xe3d9e744b9ce0c20,0x73c6f9d08259468]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x7d58fff5,0x1ffde4c3ece4d011,0x13feb9dfff7c7468,0xeafa3adf7dbeac0a,0xa5923c73d8a37000,0x1007ffdefdeaedcf,0x9fcef9f47717da6a,0xf508736a4ea52e85,0xf588000000a033f,0xbcfbfbb5fbae2d96,0x6561323a6781311c,0xed273bf0300]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x20150001,0x108812436ad8f661,0x1c00891000195060,0xaf00f28811c0f0e,0x64da3e79b2d5c887,0x59f8001ac00a3056,0x4600f08471307f50,0x3ea3fca87e05ae85,0x4fe80b6dbcba6363,0x30fa8c08011e65a0,0x6d41fb1d29cffd3c,0x73fe0f9833f97f8])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0x7bb7fe7b,0xffd2df733ff8afc2,0xdbf9ffffdfbbfbf0,0xf4fe35af9e5d5fcd,0x261d3b6ceb428f48,0x1867f63fdfd2d5be,0x6e71f6ebff67a574,0xcab47c75cf56ce9a,0xea08841c84e83af,0x73fc77e9074db3e6,0x9900c9bd59b139dc,0xb28092b87789b04]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x1600260,0x10e42081c3c692,0xc000000a12202e50,0x14b2308f0c028385,0xa105fd64e80b554f,0x3e63140400120489,0x858a8122f47d0e5,0xee20075e4d76ce92,0xe1788d3f84ef7e4,0x8ac903e1226c1bd6,0xd1086666f9bf3ddc,0x7fa81b9318f8fb2c])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x6ff5ffff,0xf1cc7ebdfbcbf670,0xe7ffcffb3ffd3fff,0x1fb5cfa9ed22fb84,0xd9c1cfe5b4dd5887,0x660ffdffee1f3ad1,0x7e5fb917b9fe5f85,0x2ee3878a307481f7,0x4e1f70ba30907457,0x8bfb8dcf3c7c4e91,0x5c0e7e47a84ec400,0x748392f198da60b8]))
  | _ => 0

def samplesQ231 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x8918010,0x80c0429118289140,0xb488483403053018,0x14c00291121004c,0x825108858cc0a040,0xf00c1306321a0750,0x80604908490820e4,0x116008ea01809088,0x4018048208a608fc,0x840d825203901118,0xa1118600e8000d20,0xc641f1408241408]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x2a71042,0xf4420a281a1a2faa,0xeee020b82112d7b2,0x51a9a935882910a4,0x12588204a59085ee,0xad7eddd299b20b45,0x440814c440529b3,0xa7a120a3ab323cd0,0xad0a6e226a2010fe,0xa8aaeb35f98a0414,0xc1310012e104a59b,0x20a54ed272b70200]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x20154010,0x508812023890b460,0x144c043089236128,0x10c5080811000204,0x4650205496818884,0x5054868423168348,0x944051940400845,0x3040084902828818,0xc91044030c3042fc,0xc05406392810850,0x93150060e40008b2,0xcc01f0648802006]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x44808a4,0x224200440054015,0x110104200880001,0x2610520224c4a012,0x880440200041011,0x281202944400022,0x2210202002229200,0x400c950414004223,0x1261110811000401,0x5350148804440022,0x800408810925044,0x9108a02985488900]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x7e9fdf9b,0xdfff7bff7ebcbded,0xbfcdfcffbbff7b7f,0xfbcf3df9737fdeff,0xfefbeedffff5bff4,0xf9df9fbe3f3e9fff,0xbf7dfd7f6ffffdef,0x3b77fbff4fdfb9fd,0xc9bfcfef7fff5eff,0x8ecfc7f7b7ff1fff,0xff3deefefdff3fb2,0x7ff79fb758feffae])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x100a0482,0x61101400404088d,0xb01800110400203,0x62003110204c9401,0x2022000840200330,0x98308380c001080,0x1009100220919102,0x205b1040c102061,0x23004400490003,0x2c2058424200281,0x408280400563000,0x310180a1105a40a0]))
  | _ => 0

def compactPerms231 : Array (List Nat) := ([[], [118], [32], [32, 118]] : List (List Nat)).toArray

def compactDomains231 : Array (Sig × Nat) := ([(subcube 1 0, 7)] : List (Sig × Nat)).toArray

def compactWords231 : Nat → Nat
  | 0 => 0x13f
  | _ => 0

def compactCount231 (k : Nat) : Nat := match k with
  | 7 => 1
  | _ => 0

def compactPath231 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | _ => 0

def compactLive231 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits compactWords231 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs231 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits compactWords231 (7 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords231 (6 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket231 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP111 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x7d7b7fb7,0xdffebfdb9bb30d34,0xbf4bbffffffcfecb,0xde183997ffedf7cf,0xfb86369cbff1f320,0x40c47481c7fcf1df,0xffff8fe3fffaff23,0x8e3af890e11c1c10,0x43e0e3f73fbf8efe,0x3dfc6380007df03,0xcc8dfe7dd9e56799,0xd5c14062c78043c1,0x1dff9b4449c7494]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x5f6c3fff,0xe6e6ceee270fca0c,0x42323fefed1f7fff,0x3c67c9e8ecfc3cf1,0xfe7e0ae0487264e3,0x9b320800281b7ffb,0xfbfaf27d17ddbcbc,0xf97fe8e63ee07e68,0xbe53107c4b070124,0x3c00000441cfefbf,0x2ffde7b2f4a2386a,0xb98a07d5b983900e,0x3f4cf06dc300]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x445c0a0,0x2046c4993098d8e,0x72fbc00605184002,0x123201c00cf007c8,0xbb078afc6df370b3,0x52e35cc5ffe00000,0xd280834111f0c22c,0x803c08f6bb801fa8,0x1ff983fdab2f81be,0x23dfde3d4dc80c0c,0xf844c045ae67b0a,0xb1cf01fc819fd3ff,0x9dfc065c66df7dc])) : Bits)
  | 3 => (BitVec.ofNat _ (limbs64 [0x77b5bfef,0xff1d7c67f4fbb0be,0x70c47fff3ffbc7fe,0x2ff63f5f1ff3c7e8,0x877f801e218f0bbf,0x32ab7045d01fefff,0xfec58fdb7877c6dc,0x4df73fef9a9f9bbc,0x43dc8385a828e183,0xe1d018310c07a2ff,0xbf8eddcf3bc4d906,0x233e787e861c03b1,0x8482747ce93805c]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x7ed7fffc,0xfbfdfd9dfbcce5cb,0xb1bf3fded7ffff7c,0xd3bff7f0f2f23b7e,0xfd99cdff767018db,0xe7c58f082cdfff65,0xf7bcfd7e97a1437f,0xf6bcd7f93f00618f,0x3dabec7b84c7f1d8,0x3e02e44671ee7c5c,0xdff339c4ea5bbe74,0xa07787a941e3dc0e,0x159214ab076bbb20]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x10300004,0xc0009c862082203c,0xb107000800000648,0xc043910f2e03060,0xc41e049e32700beb,0xa3842709ecc06141,0x20048c7a16010410,0x4c32f0893e1c781c,0x63c2e0770c87e1c0,0x3fd2e47671ee0213,0x8c89b1c0b9c1bc74,0xa1324663c7e3df8f,0x15da358e449bbb34])) : Bits)
  | _ => 0

def samplesQ111 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x2849028,0x2101400414485089,0x409464010304c00e,0x201600b801020018,0x8480480160010884,0xb25b014218089110,0x314480a7100ac120,0x420b0010a4800454,0x27800268101080,0x2030040b422ac102,0x4081c241c5c16098,0x84c0000380005041,0x4393890401c1404]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x2093c208,0x895d6100d9a034e3,0xb94dd7048052d484,0xf0829e7251c5a508,0x1590a12b74a9a210,0x26ce436f86fa4dda,0x9332245633469408,0x62298a581dab42d0,0x4ac98d2a25362c20,0xaab8352824bfeaab,0xae5673275a01052,0x8d9213111309192d,0xc011bf4cf04d4200]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x445c8b0,0x201548419b008d0a,0x60f3e24820d0f027,0x921c04c810930c50,0xc205817971e1e002,0x626a048538bc9869,0x28606c467642b012,0x43092648f002060c,0x6236180ccc4498e2,0x1b086082dbfe191,0x604ab069b5900411,0x84b2361136004848,0x9e683f9a28900022]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x84a6091,0x860821889040b40,0x8e2b986014501141,0x688d00364140942,0x5a2085a898a0b040,0x8008eb0271760a5,0xc801264022611080,0x88412c2402c0889,0x2c9031b48140a04a,0xcc830044a495225c,0xac0e198a18040004,0x221a5258122d8180,0x1ac007470c838050]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x1280101,0x4422002200110214,0x600089240010200,0x440400126205083,0x828120000060520,0x101041012204,0x4488010880800044,0x141040030204a821,0x840020910089020c,0x4404089000001444,0x9510088400008a20,0x480a040a48492,0x208240210722a900]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x6fcffbff,0x3bf7eb7fdffddfcb,0xeefffe7ff7d7f7ef,0xbfbff5fffd9f0f7e,0xfee5fffbfdeffff6,0xfeffdff73fbff9fd,0xf967effff7eff5fe,0x7fbffedef4fe1fdf,0x7fb7fbfeff54f9fb,0xffbfbfffefbfe3df,0xeccffbebfdf5feff,0xaffef7fbf7fffbc9,0x9ffd3fdf6c9fbf76])) : Bits)
  | _ => 0

def compactPerms111 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains111 : Array (Sig × Nat) := ([(subcube 4 0, 7)] : List (Sig × Nat)).toArray

def compactWords111 : Nat → Nat
  | 0 => 0x13f
  | _ => 0

def compactCount111 (k : Nat) : Nat := match k with
  | 7 => 1
  | _ => 0

def compactPath111 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | _ => 0

def compactLive111 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits compactWords111 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs111 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits compactWords111 (7 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords111 (6 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket111 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP173 : Nat → Bits
  | 0 => ~~~((BitVec.ofNat _ (limbs64 [0x400002040ac2,0x2480d0002381e006,0xb807071100d233b8,0x101c702e0b889da4])) : Bits)
  | 2 => (BitVec.ofNat _ (limbs64 [0xf6fefafcebfb,0xa4bffee5fff1ec76,0xb87707119bff37f8,0x5e3ef02e0ba9fda4]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x11c0c882eb18,0x5dc00041ca9c08f7,0x877ff79102025d0,0x6ac37e6feb2513fc])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0xddbfffc7fac0,0x547ff15fff8c23ff,0x78c0f710f5feeff8,0x31c37222e0ee1664]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xf97fcfbe0f1e,0x69bedffbea9fd887,0x8f370869fef33197,0xeadd0c4d0bd59998]))
  | _ => 0

def samplesQ173 : Nat → Bits
  | 0 => ~~~((BitVec.ofNat _ (limbs64 [0xbffbfefbfdbf,0xdff6ff7dbf7fcffe,0x7f7effeffddbf3ff,0x77defdfcfadedfb6])) : Bits)
  | 2 => (BitVec.ofNat _ (limbs64 [0x90205861004,0x111830200a823801,0xc0c810080a2e1050,0x1200822317296884]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x11d04cd0a818,0xddf48a1097368caa,0x4a46a562cd9bc0ad,0x45420f05adacc02]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x22605018252a,0x8a860344a424c132,0x131229a3f1c06289,0x2146348460c61620]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x68818496089,0x8662460985104598,0x19126326b451418b,0x40cc145428d49110]))
  | _ => 0

def compactPerms173 : Array (List Nat) := ([[], [117]] : List (List Nat)).toArray

def compactDomains173 : Array (Sig × Nat) := ([(subcube 32 0, 4)] : List (Sig × Nat)).toArray

def compactWords173 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount173 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath173 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive173 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords173 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs173 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords173 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords173 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket173 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP175 : Nat → Bits
  | 0 => ~~~((BitVec.ofNat _ (limbs64 [0x401100001110,0x8dba08042099885,0x6080060000006018,0x4001e0201c103ee0,0x7818b0e141c90bfc,0x1f81f04056627c00,0x1e30800f327cc4,0x1f0401050000f180,0xf2cf0001fa103e08,0x7f0df83e43c7468,0xe0fe1f480c02180f,0x795ae211de3efb9c,0x1c151827c038f985,0x78337920a2abf6e4])) : Bits)
  | 1 => (BitVec.ofNat _ (limbs64 [0xee8f3f77fff1,0xf1fdbbaa03e9ac80,0x843fff7f8df9effc,0x72bde6af83f0fde2,0x7f7f38a1b8083c70,0x1fe8605d4002143f,0xdfbeffebc8f3fd3e,0x1fb767a5ce7ebfc7,0xfd1e075020193a4f,0xe1794403e43c0000,0xf4067efdb3db7a,0xffd6edd8c719fba1,0x1ca99d2230c0f904,0xdf75ca25b060]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xfbb67ffbd7fe,0xfe4ebefc5e0690e7,0x78bfffe7f3befbf8,0x77c3fbf05feb1e7d,0xf8b7f0f741c3c38f,0xeb81b7807660683d,0xf7fffffc3f0efedb,0xff0ef927af83fc78,0xf2e5f805db703eb8,0x17849f800ddc7468,0xe00a193f3d3e5d9f,0x7fdf2f1f87e07dc,0x116783fcb380081,0x7833e578a3fa4684]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x90ec0704400,0xf04c0e1611a9c6ef,0x9fc0000300388300,0x45fa031483e21d40,0x82724ffb8cbfe64,0xefb8241aeff2ffc1,0x9080400010409c1a,0xc04e6200d9d0e10,0xfdb519b804507aff,0xd7f746812dde77ff,0xe7ff1fc011198210,0x36420c1c65f3fe9,0x16ab8ea1cffff8d,0x7fbb044d932d8ffc])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0xdf7dffffff1f,0xf9dbe457fdc9cb7f,0xe7bff69b7ffffffb,0xcd7a395fffffffc2,0x7878b75ebfcf3bfc,0x1f907062ae6217ff,0xbbfff997f7fdfefc,0x1f44875931fd4fbf,0xf2df00a82616c3b7,0xdef77b83f83e0399,0xe0fe0779de4ba2e5,0xfb6ff25706e7fddd,0x1c551ac20cf8fd85,0xb883d88b40df9e4]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xfd5bbffc7dff,0xeff4f97f3b9568d,0x187feffffe7ff71f,0xcdffc734bc163ffd,0x8f8fe4e940f9ce64,0xe43f8c1ad190e83f,0xfcdf76ffdf721dc7,0xecfdfefe5d9df390,0xcda119bbdcc07c48,0x7f2c6fd27c07466,0x701188fffddbe1f,0x797a2fa1de1e3a2a,0xe36aa0edd4070208,0x74337ae713ab8618]))
  | _ => 0

def samplesQ175 : Nat → Bits
  | 0 => ~~~((BitVec.ofNat _ (limbs64 [0xbfeefd7ff6ef,0xf774dfffddfee7fe,0xdffbddfbfdbf6bdf,0xb7fddbdfbffbde9f,0xff2f7ff6bffaf7f3,0xebffc7bfefbff3f9,0xebdebebfcf3d7ddf,0xfff2ffdcaffcfdff,0xffcafffbf97ffcb7,0xeff53fffe9dff3de,0xfff3fe2fceffb9ef,0x7d5feebfde3efdbe,0xfdfd7fe5cbfff8fd,0xf3f27bb6f6ebfef6])) : Bits)
  | 1 => (BitVec.ofNat _ (limbs64 [0x1170e0ad0106,0x24034444f4945375,0x73e2aa1211135585,0x8a5209264d48aac9,0x20924148536692a6,0x45131d68a7594baf,0x12b4a66291474b6e,0x46062c8f46480902,0xa62c514c950a150a,0x90a54a2982aaa86d,0x122253feb9315b48,0xd304ad986d089361,0x488d092a918253a6,0x2028d775ca252040]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x449810c2c10,0x1130101b1990e18,0x56c160080071704,0x40042704200e83a2,0x68ec0846063264,0x4065c580811948c,0x44c1e9a0184f02fc,0xc0419834c000050,0x299110223d80640,0x200fa6011c018871,0x307fa30160518,0x4b5325839180649,0x15380a13000485,0xc67c558a1720204]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x90ec8306644,0xb0400a1e94a8c4ce,0x9fdb0120581b09d1,0x119c8a90a9834c0e,0xa2a31b29aca12a0,0xe9aa058b8da2f278,0x6b581c9b05250c4d,0x779028c8868c902f,0x4c26a32e0735023,0x2b302cb0280cf2c0,0xa7b2622fcea630e6,0x641bca2e480a1816,0x7c0d4d44c1106039,0x81527bb264c27002]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x208210108060,0x1224128800222080,0x80140a900882040,0x1108c04100a00404,0x9301002208104401,0x20c8808140842010,0x810a001540002400,0x2150820020a45489,0x5100222048008831,0x4210011440441082,0x29102801464880a5,0x2840400302224884,0x2440024048592810,0x118028801408d8a0]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x2a44401c222,0x7000822c0c46a122,0xc290c060343800c8,0x82c040d384614001,0xb901132638400190,0x63880385822e0171,0xa806120cc3101c00,0xe3306018039c300b,0x314208581821c810,0xc980018ce0c03180,0x6370e005ccc9a803,0x194a04a2c0063804,0xed2801c1c00b1808,0xb0903aa612898410]))
  | _ => 0

def compactPerms175 : Array (List Nat) := ([[], [49, 114, 80]] : List (List Nat)).toArray

def compactDomains175 : Array (Sig × Nat) := ([(subcube 2 0, 5), (subcube 8 0, 5), (subcube 0 2, 5), (subcube 1 8, 4), (subcube 32 2, 4)] : List (Sig × Nat)).toArray

def compactWords175 : Nat → Nat
  | 0 => 0x51084ff
  | _ => 0

def compactCount175 (k : Nat) : Nat := match k with
  | 6 => 1
  | _ => 0

def compactPath175 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | _ => 0

def compactLive175 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords175 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs175 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords175 (21 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords175 (6 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | _ => []

def compactBucket175 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP239 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xf1fc3fbe73ffc183,0xf6f1fc783e0fdbc0,0xfc0ff7f0f801ff0,0x5fc06e0df18ffc87,0xfd183e7f4f80e400,0x78107c07fe014042,0xfc1bf810f87ff780,0xc03fbf42005fe00f,0xe7a00f0ee1b60c0f,0xc0007c0135c3fb0f,0x9f458a7d73080ed6,0x17d0f83c5ce0c39a,0x600d8e03f85c7d0,0x16c0790c1e3e3400,0xc3e0420bc7c341aa,0xe3d4449144194654]))
  | 1 => (BitVec.ofNat _ (limbs64 [0xee77ed79bebfedff,0x7f49ffad15f2e5ac,0x770b2fdcb027f9fa,0x38ef0ffb0cfcea45,0x8ff6ddd149fdce4b,0xdee801fad380404,0x3f58723260e5c26,0x6ac85504c2013f2,0x5806c00000000000,0x11c4001c7feefdf6,0x1f93fdb36faffe7d,0xb9ae799796930e84,0xe3472668c85e0655,0x8c07d4c119cc00e5,0x1005800000006fb7,0xb931710e5dd03000]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xff27ffc9efe1ff43,0xaffe5476eadc26ff,0xf8b0dc14ffff41a0,0x73fff1019d7af7f8,0x1fda6cb22f11a0,0x3087fff800213bbf,0x6200032e5f80023f,0x401150adf384a004,0x11fbf0f114480370,0x2b80e2bff335c4,0x87fe09de82f1597b,0x54bfac27fb17b063,0xd800af961102f828,0x11fe008fe5f1c000,0x2c003cf43820f137,0xc06839f3a2068023]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x9fdff1cfcfb97fff,0xd6dfabc7f12fa33b,0x8e3ff0e98ff95e5f,0xdc3261cc6b4f234f,0x72b7e1f4bdd01b28,0x476873a621dd7da2,0xa01ba4cc807005c0,0xb9602a8382595d88,0x65c07080001800c,0xe1037002fffeecb,0x64b66bdafcfead15,0xef0dd7fa4be8b311,0x5f8101a26f9242f,0x8b8765af0300b00,0x39a430042007edd,0x921b4e5122e0011c]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xef8fd3763d7e13fc,0xf9b7ffd2d5fd19ac,0x78f42fa34027e605,0xa7109ff6f2f315bd,0x8fe91daeb9fd31b4,0x8df1001852c68479,0x3ee78c3d98e5bd9,0x6934553b38013fd,0xa006c800e0380870,0x11e5801e661dd7f9,0xf86bf62cec5ff1ea,0x5e4e8648366c0d67,0x1b47c697085801aa,0x6b07ab31060dc0e5,0x9c05841384801d58,0x44ae862cdac9b020]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x3ef82effd3debebd,0xfb2e57a92ad3de57,0x83cfd36ff458adaf,0x863f94f296b01b7a,0xf2e22213f6522a5f,0xd21e83e081fe821d,0x1de444d503f1a860,0xf94cfa2c1c26ac03,0xea5930460b81f781,0x2e1a034099bc1e30,0xf9b874079d015784,0xa3f12bebe51840fc,0x24b85929d126bb07,0xe339867001c20b1a,0x205a3904115f0264,0x1cc3ba2c05304d8b]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x51fbdeb7fc47fe7e,0xdffab9fcf207c53,0xf57f00927bdeb25f,0xe9cdfa3f6f05ccb2,0x7d4de78b462ac4d7,0xa2010c415e02fbc0,0xdc001b382401a01f,0x3fc200bc6dfb4e70,0x1da130b11e467082,0xe00048a11a7febff,0x624d97e113f6a2ab,0xe87357d5a9077c08,0xf8bf2145e6a158d0,0xf44009a6ea02341a,0x402000e8283cbecb,0x2f0481c2b9260ac0]))
  | _ => 0

def samplesQ239 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x2024100870008182,0x22200058140022c4,0xb40200404000c00,0x6a00040105451000,0x801a240002002000,0x6889000080210260,0x80004017a4000220,0x8022109010020008,0x1c04004900400881,0x34004354803104,0x100086403080056,0x9080105410c302,0x60028a008018300,0x1400000d1a000000,0xd04040181640c122,0x4140408144014044]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x4c66ad299a9568aa,0x6c0172314444a565,0x2d1066d095138888,0xb04628982d647804,0xa482111061647048,0xa59aab112b631142,0x8b3019985a54a05,0x9314b518a4158b42,0xc95aa6c184d2a09,0x8481118bffeabda4,0x169159b1498dc664,0xb1aa791786919a80,0x611224c84a128619,0x813148548981254,0x59157040244a6bb7,0xb931710a55902000]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x690019c06a20a141,0x62840140ccc2144,0x930ecc004560988,0x200c61088544d220,0x80020048a04010c0,0x5e010a4181004622,0xc210440e23000c60,0x3244827006020e,0x1201064810600c01,0x2001431bf7a23500,0x386005602810913,0x1412a4215390b240,0xc000a08418009228,0x876040509b00000,0x8844251c7220e136,0xc068289320020022]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x919320c305391471,0xcb808261468911,0xb01944e119b3509c,0x8066301e2008618a,0x37a4402469c242a5,0x122234621448dc08,0x62c28d40123624ca,0x1a844202c4980014,0x8218c2b0b1007052,0xd6c91508ab7fceca,0x2426630a70660d01,0xce0d46a209e11010,0x489b001262d8201d,0x2892571260908362,0x1a2070548203edd,0x921a0c5022e00110]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x82894214014a1214,0x91948d0000010808,0x9085010140806210,0x110124200120089,0x1121488600890706,0x40108a1014088d,0x444302018129108,0x8c10844032864a0,0xe028501222029114,0x4240042000154259,0xc868a408a4523088,0x244024820240401,0x849420300880082,0x2100a1102404c529,0x488882180851448,0x48686248a489000]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x640040400c60800,0xd004170002104000,0x100a00080022,0x401000012800050,0x40000014100102,0x150019808120004,0x1108000818104,0x129400100ac60,0x4000310004100000,0x880400000000,0xd81814008c005200,0x14009088008002c,0x100001240800,0x8208006000400018,0x419980000830000,0x881922c00100489]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x1018c2328400460c,0x9522880c0209803,0xf003000133814051,0x80c2903260002488,0x7da0c20541870429,0x80208420260c8181,0x2c24a86008007083,0x140820c02a14190,0x20a0003060803030,0xcfc23400085dcaf3,0x204182811030a0a8,0x682110c428230000,0x183f0102c6984051,0x60001910e0025407,0x220260880c1ec9,0x2604014099240a00]))
  | _ => 0

def compactPerms239 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains239 : Array (Sig × Nat) := ([(subcube 1 0, 8), (subcube 2 0, 8), (subcube 4 0, 8), (subcube 8 0, 8), (subcube 128 0, 8), (subcube 0 2, 8), (subcube 64 0, 7), (subcube 32 2, 7)] : List (Sig × Nat)).toArray

def compactWords239 : Nat → Nat
  | 0 => 0x4059bb447f
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
  | 9 => let v := readCompactBits compactWords239 (31 + 8*i) 8
    let n := v >>> 4
    let bits := readCompactBits compactWords239 (7 + 3*(v &&& 15)) (3*n)
    compactIDsFromBits bits 3 n
  | _ => []

def compactBucket239 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP223 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xf9a7d3fedb987f67,0x4dbec27c45bdf39c,0x65b2b9d1fc0cc35b,0x81b9fdb3df40361a,0x7f9f781aa100af43,0x97a640007dee903a,0x4473786f1a05bf4,0x201caece3265820d,0xe00c2031c2781035,0x834d7acfb9d59e5f,0xdcd96617f3612d9,0xbb66e14d65989d81,0x801f5b338ec842b1,0x8d3851d064374180,0xf1080260f0545d55,0xa355884d489458a4]))
  | 1 => (BitVec.ofNat _ (limbs64 [0xffd9fc3fe3ff8003,0xfe40027ffa1ffc60,0x5fff601ffff3c1f,0xfe41fffc03ffc80f,0xe01f7fe401ff5003,0xffd8007f8003ffc0,0x7f801f900007f00,0x27e350007d80000d,0xf0c1c200000000,0x7fffdd37e1fa3,0xf20f07fe7c3fecfe,0x5bf8ffb07a60f0fe,0xe05cc0390003fe,0xfc07e007fc00000,0x2107c83000729ff,0x79e6f30280f40108]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xfffb7fe7755413ee,0x9277fd8085f0beff,0xfa46d9f648dfffad,0xef4ed9eca1ddcc1d,0x95e08008fc075ffc,0x20159f8808c06dc4,0x6098585901e0001b,0xdc0200d24141b7f2,0x1d030a0c010201c0,0x1c1fffffedbabeed,0xfbe66d4b13d8310f,0xed234bb7d276206c,0x10a3a014810cfd01,0xd03fa4df81f80007,0x63811c040fd77f,0x84103756d3030003]))
  | 3 => (BitVec.ofNat _ (limbs64 [0xcefd7f377e656dd0,0xeb838f972be3471f,0xfff92e7f8f23cb96,0x58f1e2f3de5fbee,0x1a1021bb07080e34,0xc26e16f24f439208,0x6b23a1003e0be067,0x3c8b25827e49e0,0xe00810012044c225,0x620abfbdfee569f5,0xde76d18a9afbbfb1,0x16dbb4c7a416c600,0xe704072b6673320c,0x233dae7ba323900,0xcd0c00408807beab,0x128ec4957c080434]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xf627aff99fe2fe9b,0xb1bd326bb45e0b83,0x85cd49aff3f0c0fc,0x7bb7e243e2be35e5,0x9c7f461158f0a083,0x6821a87ff2116c35,0x97a4c866ce542488,0x27dca5314e1a7c0d,0xf0c1c204002c0a,0xae54fb6febf15a,0xedb8ef95e3edd3e7,0x9885de4a5d816af1,0x78d8c30c36b78140,0x7ec421285a088078,0x2907c830022d6d8,0xc5a94aab2f508148]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x175e91dbbebb937d,0x5c6bfdc77be17d6b,0x9a1bd68810d33c60,0x5070201f7c22b7f2,0xefe683e7220f70bc,0x458e100313c022b,0xb80fbeb02fff9f3d,0xdbe1706b988415f2,0xa0414347b95c3c0,0x6c57ad023f0142ba,0x19b7ab4acc3cc1e,0xe5be0afe8b891d12,0xef07acdcc98cbcce,0x20038a2001cc3e07,0x2c6401287b90a120,0xd8133ca023ec7613]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x29feeecced8fecbc,0x27dc7db8de0e80f4,0x7a24277e272c37e3,0xbefe07d0de1b4bf1,0x63e89c44def08148,0x19837f8586bc01d7,0xd850460fd01f80c2,0xd8035f9ca5bbea12,0x17032e089cab3c1a,0x91a9c376d6dee504,0x3671b87fc5046f60,0x665d3539806f030f,0x1f7830e350734c33,0xf1cc051f8405c6f8,0x1083821407e96a86,0x2e680178942baac0]))
  | _ => 0

def samplesQ223 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x1103c20213880008,0x83a2c044444c3008,0x104951a4000089,0xc17904400140b205,0x586040a81088000,0x4c14c1084411002a,0x24d0d090204044d2,0x21886ba02000,0x80bc00a4090120a,0xf0d48c38911820b,0x8408661401210c8,0xa804a0044398a000,0x80bb080406480081,0x8d0400d064008180,0x211002a8904c4554,0x8151804848904084]))
  | 1 => (BitVec.ofNat _ (limbs64 [0xaed1642480b18400,0x9a6042d860938429,0x289c850228445916,0x474b66b0040e8023,0x20084a60884a1533,0x1b5504870807a4a2,0x53950448641289b0,0x94842669aa81e96,0x491c0c8aad584401,0x3115af5dd2521ca1,0xb205032c2c074c58,0x53f0bfb06232d036,0x1a0544111090294,0x2413c10c6905488,0x4960a493109729b7,0x7966f10280a40008]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x75601aa721443068,0x82b0e44141c5188f,0x191ac510e1c1f392,0xe15fcfc90058d48d,0xc20243222183aa,0x146383245e820244,0xe648411202806002,0x4486204851069051,0xcc49498a421518b2,0x679f7defed8896c4,0x6966254811982005,0xa1034826b296e06c,0x20a98114021c1880,0xc41f085a4db00022,0x2045135a840fd77d,0x84102646d2010002]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x882831116c00e540,0x48110c8b28810a35,0x2da8842243475912,0x22025aa3148d45a0,0x2040a815264224cc,0x20aa2c0083c03294,0x8290b2114062805,0x252a4611044c0084,0x55d008a0182c6da1,0x2012b73c76e46944,0x942250829a292b20,0x160a10c3b0224424,0x650083610031301c,0x407158069a921200,0x568c21440c23baab,0x128c449514080420]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x400689d8160020ca,0x2098840180441904,0x1404098d10100a0,0xb0900841a2605484,0x90d3248815316200,0x6000623811180858,0x8800b8a292e10641,0x70a491902442e061,0x6417005400618a2,0x64a50a22da9401a,0x4598e89143e091a7,0x80540481c802280,0x3049810422901100,0xe4140162080a8933,0x21118202960d648,0x84810aa92f508100]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x214004800000215,0x400100010204000,0x8201120000100400,0x440000000,0xa01008010104011,0x100001100088800,0x104244880310220,0x1000902280004422,0x2000024000000000,0x8020000000000030,0x9808102440c012,0xb0021800000900,0x8040008c8008442,0x820000400c11,0x820080121100000,0x4802182021441211]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x880400c8028c00,0x80401a822000060,0x60802006002c0840,0xa0000200c040870,0x6020c03408001044,0x288088280441400,0x1020020140048104,0x840040500000a00,0x13000100808c445,0x821012462100,0x201100680040600,0x4448050100610001,0x30020c300034034,0x10c0100182044208,0x1488840400802882,0x22280110002a2840]))
  | _ => 0

def compactPerms223 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains223 : Array (Sig × Nat) := ([(subcube 2 0, 9)] : List (Sig × Nat)).toArray

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

def samplesP187 : Nat → Bits
  | 0 => ~~~((BitVec.ofNat _ (limbs64 [0x4a000,0x2800008e04023026,0xc19308500001006,0xc01115c021ec00,0xfd408010b0604001,0xff803803e041f9cb,0x1183c400204003f8,0x30018f000eb80df,0x96c2241afc037,0x200ffcc023e9f878,0x70c1ff224c0f05c1,0xf40b02383ec7e007,0xf9e02e065c27e782,0xdb15d585961ad3aa])) : Bits)
  | 1 => (BitVec.ofNat _ (limbs64 [0x7e7b6f,0xffc3ffffaf513fc7,0xe52c39e73fff17ff,0xffeed0343ffbffe0,0xfdf6fadabcc07f01,0xf9f83dd5b869d00b,0x11fff7b57dff07fa,0x76ec7dbf80e87fff,0xfdbde67291a54874,0xfe0ffce003f80e78,0x6001f1037d5acf9b,0xfebad7683e2fe907,0xe009f746d307e082,0x5b10cd575c38e1a2]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x104d70,0x838100cb240fc6,0xf7d73f27c0060158,0xc04303df9c4a0,0x83a256108263f2b,0xf9ce179cfed7afcf,0xfb8001004c808000,0xd4c29a0d80601f35,0x73c7f877f1b82e2,0xfedf7ef0805807ff,0xf3cfffe20010cb84,0x8948a003639ff00,0x3813de3f2f7fefc6,0xdfff005b32b93ffa])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x5fcebf,0xffbf9dcdccf6ef7e,0xcf9b061f3ffeff5f,0xcefff559fd2dcc7f,0xef3a9f71bbe602eb,0xef41d783e6c279c3,0x107bdffffff0fb9f,0xd7fa9efc63f383d5,0x1f0a6da646afc1a7,0x22df46aea02df778,0x10c01e23cf1f1de5,0x8bf7ebbcf0f03e80,0xfdf06e0f5c202702,0xdb05359d96c7322a]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x7de59f,0xf8ffff8e53afdfa7,0x12d7b184bfefffff,0xf3dd2fbffff7ff80,0xf9c9a5254f387c01,0xf1862a285f95a80c,0xc9ffed4effff87e1,0x89d39a4ffcfffdff,0xe2411b8d6b5ab67a,0xfd0ff8d003c00987,0x6001e1c1febdefdf,0xf50daa973f0fc607,0x181608b72f07c0c0,0x4f8f3883339dd80]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x77bd4f,0xefffe3f2ff2e30fe,0xbc517e207ff7f9fe,0x3dffdff7c0f9e4bf,0x1e7f65fff027813e,0x1e8e101ee057afc0,0x2277fffbeecff87c,0xff07fbf19f6f9e3f,0x63c7c037d1b8283,0xf03f51fc5bf000,0x93ce0e20ffe7f3e4,0x7cdf1e7806d1f178,0x3be39e382c780f04,0x8007dee3a29a1258]))
  | _ => 0

def samplesQ187 : Nat → Bits
  | 0 => ~~~((BitVec.ofNat _ (limbs64 [0x7b5ffd,0xf7fbdf79ffffdfdd,0xf7feef7ff7aff7f7,0xfcffeed5ffddf3ff,0xfcbfbfeebf9fffff,0xfe7ff7fdffbfffbf,0xff73fde7be7ffbfb,0xfbfff8ffffebfedf,0xfff76fddbdafbfb7,0xdffffc3fdfe9f7f7,0xfffffedfffeff5dd,0xf7cbfe3ffef7efff,0xf9ffaffe5fdfe77e,0xbaf5ffe5f75bdbee])) : Bits)
  | 1 => (BitVec.ofNat _ (limbs64 [0x18490,0x881d0800408e4210,0xad18410854424c4,0x8020128ad440860a,0x43500221010c0898,0x4400828841040d60,0xc04e80b008aa1102,0x320800090440c88c,0x451020028a14d008,0x484512c44906aa90,0x2a4440829008b13,0x5090556824048912,0x2048a24012128a91,0xb088c534c308102]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x104d78,0x1291c11089344bc4,0x37562727d621a051,0xe48646109a54e0ac,0x89c894c2988ae2b,0x7812c494ac9ebf8e,0x9b7334c3127cdbc8,0x186ca892750a8c05,0xe893289830231aa6,0x51269826d048c355,0x340f7e4dffc63459,0xe24a70374840c2df,0x496483525483001e,0xa841ffa4c542c004]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x203141,0xc060f013011040,0x100478e078091000,0xc1c0174022a2860,0x40d60144c01c300,0x836002018038004,0x27901b4c71408019,0x9c0180203880200,0x1ac89a28454001f1,0x2220853020380100,0xfc0010c142181424,0xb27a290c8e02600,0xd804000e00a03042,0x4417310c10c73220]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x21a60,0x434084512d100148,0xe4284a4b62830232,0x4405604409184145,0x2403290a34028646,0x2a5a5045288a9293,0x24314906a4158888,0x8851a856a1282443,0x2844069425220511,0x16124c1214a05001,0x35523247d6ad408c,0xa5018a055a424209,0x4836089205096148,0x74738033095880]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x842b4,0x11080d080854c701,0x41aa811d81a06150,0xd040e48045040383,0x6882826210981c0a,0xe001e18422ac5839,0x5860e4218e0339a0,0x500ae0302c019c15,0x6107040498058e06,0xd5140008dc03033,0x6e61cbd63e1c0,0x14c80c090011c03b,0xe186701c18c304,0xa220cee1a2180048]))
  | _ => 0

def compactPerms187 : Array (List Nat) := ([[], [65, 117]] : List (List Nat)).toArray

def compactDomains187 : Array (Sig × Nat) := ([(subcube 8 0, 7)] : List (Sig × Nat)).toArray

def compactWords187 : Nat → Nat
  | 0 => 0x13f
  | _ => 0

def compactCount187 (k : Nat) : Nat := match k with
  | 7 => 1
  | _ => 0

def compactPath187 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | _ => 0

def compactLive187 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits compactWords187 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs187 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits compactWords187 (7 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords187 (6 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket187 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP183 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x7dcb3ffa,0xb7fd88fbdd5e70d8,0xb208ff7fdfe7f6e4,0xddbfac3f33b83b4f,0xffa43a9a871e0258,0xcf02a440d9fc7dff,0xfbdfd6fe48fff86d,0xdbea0e66819feaa2,0x10ae96c3607628b6,0x70525c05809fcfd8,0xcfe9fccf805948cf,0x26f72163f62c5040,0x12c2bfdc4309a428]))
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0x20a18000,0x3304822ec3804dd,0xe17a004090240044,0x15f027384038021c,0xe4177b913e079648,0xb20aeefafc004804,0x606244245878040c,0x9c0b0a0369b9cfe3,0xd00ba07ff074783e,0x16737fddf9c40943,0x5489860e01b8cc6,0xceb8b371b9fc5f67,0x96f3e2a8d3517f2e])) : Bits)
  | 2 => (BitVec.ofNat _ (limbs64 [0x77ba3fff,0x7f35d7e7b6b80c22,0xe164ffe7bcfdffdf,0xb7f0372a7bffc6bc,0x1bf0c4f53e019427,0x909a4a8a05fffbfe,0xe5e7afadbd4c3e7e,0xbccff99379280148,0x3f5be17c9020597f,0x862120d8191ffbe7,0xb7ed3aff0be9d32,0xc5383eb421c00027,0x84307fa18ef01902]))
  | 4 => ~~~((BitVec.ofNat _ (limbs64 [0x10584018,0x405837090c21968,0xfaa5000000c13204,0xe1a0940b3300c06a,0x11a442fe9f2c24af,0xc91e8fcbde341010,0x49a208810cd829,0x18e231a691ac2b12,0x17ced74c80b2baf7,0x967b7cff9da0c0d8,0x4226c106331e6933,0x64f129a477efd0f7,0x96fad1c5463e3dea])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0x7ef5fffd,0xcfff7f32fde783dd,0xd9f5ffdaffff7f75,0xf5eff7ffff07c1fa,0xe4174b8df9e475eb,0xaa0ea981cffffe37,0x7f79e323d77bc58b,0x9ffbfb8099a5cf33,0xd0cb9f7c8ff3f601,0x906a64bb0527857b,0xf43edf72ef1a6c36,0xea808b0dbfc3c0f0,0x14ea1289f05f65c2]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x7b7dff1f,0xfffeeb7ceafbdd6d,0x6ebafffdf3ffbbfe,0x6bf0dfd9c478fe7f,0xf5ef73721e2fae8c,0x717dc67a31b7dfdd,0xfeea7c5cfbbcdfbd,0x7c37362f66f83fd7,0xc704600ff09cbafe,0x6111b44f8dcf8df,0x77c7a9743307a3c1,0x5cf9f1f0583c1f07,0x8211e16657365a2c]))
  | _ => 0

def samplesQ183 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x234c404,0xc82467000a618724,0x4c77a28413067105,0x6a406412884003f0,0x144b0e60b8e01783,0x5060d0ab278c413d,0x3d985500db03810,0x9b25080a98b0142a,0x10f56840005589c8,0x783841e61bfcc00,0xcba8a883809855c2,0x20371027d0105088,0x1702ff9c03088408]))
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0x5f5e5fbf,0xbec797fd57effb62,0x7e95f46ff769ff7f,0xfddddad239edfd5a,0xd9e795fffbfee837,0xdffdb70db752cdb7,0x6da7ff77d27d7eff,0xff7b52bdaff5cd99,0xb7efbbbf3dd829fb,0xeffe49ffee562d6b,0x1fda9cfaf5ffeed4,0xcffffb59bbf6ed4e,0xf6e9eaa8fb53ff7e])) : Bits)
  | 2 => (BitVec.ofNat _ (limbs64 [0x845c208,0x885a610848469359,0x149b918101261711,0x2884007d54405155,0x408d0b2089427781,0x4521f551a9c272b0,0xc0f883158d900870,0x290f08008a3aa044,0x8266200504725750,0xa287c40ca5ffab86,0xa58c30a00ac1d42,0xe0123836c0804432,0x26147fa10ae00802]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x1058410e,0x444813010c09860,0x7a85700221009164,0xc0d458421880540a,0x50c1003688440005,0xc82c870897420d87,0x4504893212100816,0x4901021803848598,0x9283098514082898,0xa2ba004d20162522,0x5d01cb880c88644,0x91212488090244a,0x3029aa28a941c210]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x10a1022,0x140000c400086802,0x2200444804480002,0x8411180001890c0a,0x20100002188800,0x90020410108c02,0x2c00400000494480,0x40509421444190,0x100839031082002,0x9000a000069,0x1402147065000010,0x28080002244a140,0x80690000f0136140]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x4820860,0x1101100105002082,0x81000c20c0010802,0x4230100031b0800,0x2220808940000030,0x200080440318040,0x3802300040040209,0x41001c460404200,0x49008610e3000006,0x84000a000001059,0x3007004410032000,0x4484100084d8301,0x8840004254161024]))
  | _ => 0

def compactPerms183 : Array (List Nat) := ([[], [65, 117], [32], [32, 65, 117]] : List (List Nat)).toArray

def compactDomains183 : Array (Sig × Nat) := ([(subcube 1 0, 7)] : List (Sig × Nat)).toArray

def compactWords183 : Nat → Nat
  | 0 => 0x13f
  | _ => 0

def compactCount183 (k : Nat) : Nat := match k with
  | 7 => 1
  | _ => 0

def compactPath183 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | _ => 0

def compactLive183 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits compactWords183 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs183 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits compactWords183 (7 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords183 (6 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket183 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP159 : Nat → Bits
  | 0 => ~~~((BitVec.ofNat _ (limbs64 [0x8c1101,0x5100200813ee,0xe07a73c824008004,0x525001f1c5e52b,0x800a02028e18807,0xf9ec040c0015f4e0,0x26fe4b9f41810002,0x1c185c021002858,0x1c091e30242fd808,0xee01a0fff11dedb8,0x8944554e607f7be4,0x6ca9030954479458,0xa48230b6ef78031,0xe432c543e684716f,0xebad865259d2abaa])) : Bits)
  | 1 => (BitVec.ofNat _ (limbs64 [0xfbcaaff,0x1bbfffc310ffeff6,0xe401edcc03ffbf9d,0xfffefe3fefffffe7,0x879e00ff81ff83f,0xf9e601000f901c03,0xfde200017fef5fdf,0xf7df83c3ef81fc07,0xff07fe0ffefffbf8,0x1e07f803f03fe3f4,0x98c407400e0f19a0,0x7ffbf3cf92fb,0x3e3bdfbb1df39830,0xf0fc3c01f800121,0xe88393fcf7c28422]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xdfad0ff,0xe7dfd77c370f70ba,0xf82e705043ffe7ef,0x7fff77c4f775ecfb,0xb87bff01dfe7dc1,0x78f80a0d7010e03c,0x21c02943ffbaafb,0xffff874c38fe2bf9,0x43fb7f779f7ffc03,0xe0f882fc84cdec98,0x81443461d0706240,0x4008fffddfbfdefd,0xdb4528ebe4f68000,0x14f03d5fe060000e,0x327edfa00f6e300]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x4128e02,0x301045704c760a0,0x15296df67c000688,0x60002200c8504896,0xb750502581c7901,0xfcf2d28a7f90bc33,0x76d3dbbfc00008c8,0x4002020d7ea00901,0x83027a061d8c09b9,0xcf1ce8a0d08dfadb,0xc4c53741de7f7fed,0xfdab4400da8100a6,0x441108ab05fff810,0x17fdcd66110ef36f,0xfbbc41a6b0ea87fa])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0xfd75dff,0xff6d7f37efe71bef,0x93790beb27fffeff,0xf15bfff9d9cd5d1f,0xff759d2f6efd8fb7,0xe585d4ea0f65b6e3,0x26f2490b7fddffff,0xcdf37fbf7f61eb5f,0x9ccf1bbe25ae1f8c,0xcf05a4a3f91d1bab,0x4cf9558e6e0f19a4,0x2ca1efaf5e6765c6,0xedff3b2c0fcf763d,0xe43ec52216847161,0xe8896fc2d98b1caa]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xeefbfff,0xfff3fddfecd8f7ed,0x7dfa77b6ffffdffe,0xeef7fbfbf8d2e3be,0xfffe67f2fbe1fb40,0x9e7af69ef09ffdf0,0x76dddbbebfb7fdee,0x7beefcfdf7be1df8,0xbf38fef07d8dc939,0xef1869fc5380fc5b,0xe707fb5ff070664d,0xfdabd75efcd1bd3e,0x46d8e7c3623de9d3,0xf3f1cc67e10ef24e,0x133cd6373878abd8]))
  | _ => 0

def samplesQ159 : Nat → Bits
  | 0 => ~~~((BitVec.ofNat _ (limbs64 [0xf73eefa,0xfbefb6fff7ff6cd3,0x1fb5cd77deeea7f5,0x7e5deffaf6bfe9d7,0xf3f91fdfcafff5f9,0x7f13fffd7ffaf4df,0xdae1f779edf536e7,0xf9ddfe8fe9fffc59,0x5ff59eb7bbafe7f4,0xeefeddff75effd27,0xe8ff992fbfff079f,0xef5933cf77f7b659,0xeeceebdf6bfd1ff1,0xff32fbe3e6fa7f5f,0xe7a9b65f5dd7abee])) : Bits)
  | 1 => (BitVec.ofNat _ (limbs64 [0x435520,0x6564012c6d41000d,0x12fc10236cb821b6,0xb0001a4350e10420,0x55240c93056c2460,0xa40d362b11226355,0x12515d5435001549,0x77580942c9824908,0xc155875a6a060991,0x4454729464354590,0x44108894349182ee,0x841a15fa938d9250,0x412d7b1b8529850,0x290241c431a29482,0xaa8392bcb7428002]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x2052f81,0x860ac01ccd0ad4c,0x27908f8abc4b0c72,0xe42e50121a8a3b8a,0x2810a4460200976a,0x892c4092a46b0fd3,0xd7d6b16a7b6b2080,0xc8bba15802288123,0x88fcb17efc1cb800,0x33445894fa02f4d,0x194c044283a4abe0,0x1b27eefc4ab34ef1,0x5a042818fcf2a204,0x80641c0e93602004,0x56e7edea00a6e100]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x4128e12,0x4181261745556080,0x1214d745e8604b1,0x3c400170601a49d7,0x40a909804a4a2191,0x3800d0307da2b455,0x92414239ecf51227,0x29046808405bd049,0x19549213aa278054,0x24488d3011c65824,0xa8d5912404fd0281,0xae1033cf2574a409,0xaaca825928500741,0xa1207281a6b00750,0x8529b6594d152804]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x28a242,0x890c0c11018a100,0x2c02e01493408c00,0x423a41423002014,0x209b406438029802,0xa324914a4110c00,0x8504a2808a14ea92,0x808026982208a023,0x80830808590964a,0x3221800980003001,0x22887322c2242c10,0x5a24ea0540022106,0xe16d280c07052224,0x8464142882152124,0x40186d4240891ca0]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x1104008,0x2005020403230012,0x5004100240280,0x121000c800314041,0x1100011140240090,0x600010601300200c,0x820040104800464,0x1044180540064418,0x7000a0002024084,0x4008182430430020,0xc001080030130000,0x8450110234401008,0x48041c3000800c0,0x7310c08060821252,0x2100121518500248]))
  | _ => 0

def compactPerms159 : Array (List Nat) := ([[], [49, 64]] : List (List Nat)).toArray

def compactDomains159 : Array (Sig × Nat) := ([(subcube 2 0, 5), (subcube 4 0, 5), (subcube 8 0, 5), (subcube 0 2, 5), (subcube 1 8, 4), (subcube 16 2, 4)] : List (Sig × Nat)).toArray

def compactWords159 : Nat → Nat
  | 0 => 0x1031ee117046b13f
  | _ => 0

def compactCount159 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 1
  | _ => 0

def compactPath159 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords159 (30 + 12*i) 12
  | _ => 0

def compactLive159 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords159 (0 + 6*i) 6
  | 5 => readCompactBits compactWords159 (42 + 7*i) 7
  | _ => 0

def compactPoolIDs159 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords159 (24 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords159 (6 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits compactWords159 (49 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords159 (49 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket159 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords159 (51 + 1*(i % 1)) 1
    let off := ((i/1 + d) % 1)
    let v := readCompactBits compactWords159 (52 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | _ => []

def samplesP191 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xc751b3e7fa9a2d97,0xa06fe53fddf5cc5c,0xdff1a7cfd280338,0x3abcd5cf84e810c7,0xffdd6f700444076b,0x2d0c85750ddc8338,0xdb8c8e8ed41358,0x6307f008b208be07,0xc010dac0cf99f3df,0x7a4db3c7382ac9b,0xe2282f74d5dcc6ec,0x3c77cb1018540a04,0x67c67c0383dac68e,0x32de00f38f0d82c1,0x791012e86481bc53,0x5dd1292ca8a290a5]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x3b48ff54c57dfa54,0x12fc78f31f2ce380,0xfadc9e0fef554fff,0xd507febdb408f710,0x1473a40023b9101c,0xca72dea24ff80083,0xff64da01000beda0,0xff00f140f10000,0x1f01000e15f3eebd,0x9cfe75ad0fe919f1,0xd34ff9cfa1e27da4,0x6eeaa06cf668c3f9,0x9c4023f000aa0fb0,0xea20c89e43007d02,0x640e90280d619ca,0xf4bb1cc24b0e0342]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x3caf3aa73fe5d26b,0xfd1a453ce22af3e7,0x10fa1e7317fffc30,0x3ffb2b306b77488b,0xe80200afd8102270,0xf2f328dd50277cc4,0x10237170600630,0x73780f060d024078,0x20c020310ef5ffe7,0xe5fb667c7cfdd618,0x5ff00f9f7b14b9d3,0x887b34f3023ff40e,0x98b980000225f00f,0xcd2f3f010cf00000,0x802f041509f8b6e3,0xfa02c0f774106408]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x85b6c41a3afafb16,0xed607eccf3df0d7f,0x9f1fe38c07856cc2,0x9e3cf40609c2b003,0xc0782135f9e127af,0xc8833022008c010,0x1061247eab96d85f,0x8c80300800003006,0x12c08fefcfff,0xfb5f98cbb4f3b71f,0x9ddfdc653ea79e75,0xb79ccf139d810180,0x1edfe3fcc5090c,0x320c371c4c080080,0x7110000820ff6fbc,0xb1254d14a4dc0005]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xc2e94bfbc51a36eb,0x5fef9acf21fa32db,0xede0e5931ad693c5,0x655b15c870950f34,0x7a6914a05bbdc84,0xd20d468ab213232f,0xe8a64b0e85280cc7,0x9c0780f140350180,0x12e05022b5f7f26,0xffc727f3a87ceb66,0x7c2626f196dbe69a,0xfb87330c07ea0c0b,0x6726007f7d203771,0xd11c0ec7002013c,0x2c0e9009261e76f,0x82ec968b80e30852]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xfcb6fca8c567c5a8,0x129387031ed31c20,0xf72361eff0aab3ff,0xeae7eb724b08e8e8,0x138c5a802646e813,0x3580d95d8fe7fc43,0xff98d5f0700bf200,0xf8c000bcc8c278,0x1ec1e00d17ee117a,0x7ef98992cf1649ed,0xac9fd1ba493d7b5b,0x512d5c8ce81733f6,0x1bb9a38c01550840,0xd5c0c861b3f07e03,0x842014f2402f50bd,0x842f3011b3d9708]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x7b5f055d3a850dfd,0xef95bbf0ec05ffbf,0x6205fdf0e87bfc0f,0xc1c00ac19637077c,0x2801dedfda0ed9c0,0x1772020f0001ffc,0x70f30815ff521af,0xff000f0603060d81,0xe03e0d30683ebcd9,0xfb3cfe47d30f76e6,0x23f1f20aee6b012f,0xc7d000e36180fc71,0xe0415c1cfe1af0f3,0xf33702b007807c,0x88f02051f1ecb14,0x671c2278574168b0]))
  | _ => 0

def samplesQ191 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x401894000000003,0xb075a0002020c044,0x1d05040015280308,0x54001001068584c,0x20902004542504,0x20008da852040000,0xcb700001401568,0x1080000f400b0200,0xd10501d8907007,0x4a0430000808c82,0x4228211450c800c0,0x342300101a14020a,0xe08020038000c681,0xe08f2800202c2,0x140170065809443,0x48d0082828821021]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x1562d6140301a041,0x14144016490c05c5,0x58448a88401400a3,0x10289a88824c201,0x2401a229140d0a0d,0x4220238044840061,0x2212d1244219804a,0xaa2521801134b04,0x840420a554e0a695,0x90b4442c02c918d1,0x110d410881403524,0x26ca803954084128,0x94c0291008830910,0x4a220a824601284a,0xa5024904c0d41982,0x749b0c424a080202]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x4a6fc41152d0001,0x303c880ce3446047,0x19ecbc00015a4100,0x37c001004a08890c,0xa5010118a088a7d8,0x112e3010080900,0x80f8a71340091621,0x2011344a413b8220,0x58390dfcf17b87,0xc5e02234342c8610,0x5b000a956104a151,0x8828a013162ec00e,0xa0ab200120056a07,0xc00718a60c400210,0x8424260ca9f0b6c3,0xda0240a764002008]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x1872542273f9ea8c,0x45881c5451d524a9,0x278eaa162175401,0x4a2ce404c3822221,0x489a0d13602050f1,0x592540068509c491,0x53200e2596a02292,0x802a9fd095541069,0xd72e70c4076f8ff8,0xfb5e904b3453230d,0x84c78c412e261e31,0x314ed21848a5030,0x11ecfa46c43281c,0x6340730c54283000,0x3ab040490a7f6bbc,0xb1254514845c0004]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x801808e8d0281228,0x22a88c0030426038,0x83282413090a4100,0x6583446304211e0,0x912a10c082d08000,0x309cd01822304914,0x9005089201600991,0x301184424ecc3020,0x2158d1008b175922,0x4743219008342102,0x282026e0129bc282,0xd901270083c60403,0x230a006d20606205,0x514d024004a0191,0x24430121621e669,0x8260908980e30840]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x481000204082438c,0x182074114101028,0x2202002520803450,0xc029661224010090,0x509408c04a204000,0x48a10052171240c,0x49040080a0844800,0x850801001444148a,0x43024052030e0068,0x2a098882c9004028,0xa49290220011480a,0x40041d84a0811090,0x90084a405500040,0x1140410111309505,0x10010072100b403c,0xb30011358500]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x3a4000000a80e494,0xd0000f000100e80,0x3e0e0049c05,0x4020c03805852010,0x804260218011820,0xf02000380c0a0e8,0x280000003414e000,0xf00033030000018,0xce0602c000088458,0x381c1c41c3025064,0x50500a8c20000c,0xd0086000003870,0x9d801e0a1030,0x2c0070070118c0c,0x8930821000e0914,0x250c225013004090]))
  | _ => 0

def compactPerms191 : Array (List Nat) := ([[], [65, 117]] : List (List Nat)).toArray

def compactDomains191 : Array (Sig × Nat) := ([(subcube 4 0, 8), (subcube 8 0, 8), (subcube 0 8, 8), (subcube 2 0, 7), (subcube 16 0, 7), (subcube 32 0, 7), (subcube 128 0, 7), (subcube 1 8, 7), (subcube 0 2, 6), (subcube 0 16, 6), (subcube 18 0, 5), (subcube 34 0, 5), (subcube 2 16, 5), (subcube 32 2, 5), (subcube 128 16, 5)] : List (Sig × Nat)).toArray

def compactWords191 : Nat → Nat
  | 0 => (limbs64 [0x6b95f1fe3fc0,0x45ff03aee4a175e0,0x5da5da7eef77de71,0x73899c294c90a3ab,0xfc7f8377fe3fc327,0xb8264a6908d8bb0,0xb580d0ccae924881,0xc00733ec60220c7b,0x8643d93059989201,0xe7416c9815e050d0,0x725bfffffffd2992,0x1509509383ac63ff])
  | _ => 0

def compactCount191 (k : Nat) : Nat := match k with
  | 9 => 1
  | 8 => 4
  | 7 => 3
  | _ => 0

def compactPath191 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => 0
  | 8 => readCompactBits compactWords191 (34 + 12*i) 12
  | 7 => let v := readCompactBits compactWords191 (549 + 13*i) 13
    (readCompactBits compactWords191 (525 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def compactLive191 (k : Nat) (i : Nat) : Nat := match k with
  | 9 => readCompactBits compactWords191 (0 + 7*i) 7
  | 8 => readCompactBits compactWords191 (82 + 8*i) 8
  | 7 => readCompactBits compactWords191 (588 + 9*i) 9
  | _ => 0

def compactPoolIDs191 (k : Nat) (i : Nat) : List Nat := match k with
  | 9 => let v := readCompactBits compactWords191 (28 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords191 (7 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 8 => let v := readCompactBits compactWords191 (369 + 11*i) 11
    let n := v >>> 6
    let bits := readCompactBits compactWords191 (114 + 5*(v &&& 63)) (5*n)
    compactIDsFromBits bits 5 n
  | 7 => let v := readCompactBits compactWords191 (657 + 5*i) 5
    let n := v >>> 3
    let bits := readCompactBits compactWords191 (615 + 6*(v &&& 7)) (6*n)
    compactIDsFromBits bits 6 n
  | _ => []

def compactBucket191 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let d := readCompactBits compactWords191 (413 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 10)
    let v := readCompactBits compactWords191 (415 + 11*off) 11
    if v >>> 3 == (i/104729)%251 then [v &&& 7] else []
  | 7 => let d := readCompactBits compactWords191 (672 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 7)
    let v := readCompactBits compactWords191 (674 + 11*off) 11
    if v >>> 3 == (i/104729)%251 then [v &&& 7] else []
  | _ => []

def samplesP255 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xb72b4004e7e39301,0x400d3f003c590015,0x19f01400fc000806,0x6b800687d51c64e1,0xfdf0cf655a10d6d0,0xfe866865025789e6,0x6970a0a023d7274c,0x842ef71e8d6ca053,0xc2499c7c4a660064,0xca500620026f8dd1,0x80cf805b2087ba80,0x61a83c0194934007,0x9c0dc350016009f0,0x1020113b05b81680,0x28d928d7a1da4921,0x4250a4460a923124]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x400439fb79180000,0x57d4003c0a00568,0x2000800000478010,0x1f012b7f5f6df,0x23d8750f0ffe7112,0xe6c887ffe88a2f8c,0x63c9bd3bff503cfe,0x724f0b637b25a186,0xe9d6172a84194bdc,0x3aae02a3c903854,0x5085f44000266a6,0x3e5003f52600c44,0xf2718001ca802002,0xe080ec402a0000c9,0x8471e5bc78b4c276,0x280e45837a018208]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x34240018015036b,0xfbf280ec03062800,0xc60000df01006069,0x801e0827fbb6ffe7,0xae7dc3a3be696341,0x369fbd017cedc0e9,0x950e8bc0952df1f0,0x9498a16df3d43818,0x8cf6f9b3349c300b,0x4f5d8400711f2aa,0x5051000432f84140,0x7400f7f068436378,0x87e3c000000d600,0x74f0284d00201ea,0x49cb71fd8202b006,0xaab3721880640043]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x9c998ec60041fc94,0xbe0007002000c000,0x18d0000c2380100,0x4ae0040f2fef7f9f,0xebffbedad5799caf,0x56bc91972d8f0db,0xea8f4b7f494cc657,0x56f52e883cf3cbbb,0x7318a9cc5b04b270,0x7001038fc002000f,0xb0a6fe19cd62817c,0x24031c193279338,0xe20c022e004001cd,0x10300002010400fb,0xf69edf2c11215630,0xd490aa60b4000834]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x28d4b00318426cfe,0xd2003c0a0006a,0x20000b0000009680,0x1400314decdbd8e7,0xd66fbbfdbd9929d7,0x397266847d777712,0x957f549c22a5df1b,0x6d36d8ee4d1b544f,0xbda92273aa61cc18,0xb6ae05d0058c4d21,0x803007badf054400,0x1dd70a006810bc87,0x63820080009f0000,0x2880ec400a400874,0x7baab6e342e52159,0x2543887d09080288]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x439fc86a40000,0x5707800005e0510,0x1e00900f00476017,0x8001c81b4deb8938,0xdba77976efe78e3a,0xd93517fa97222e71,0x62b6427bdcaa3ba1,0x8989f492765a5e25,0x1620575571814ba3,0x155182a3b6035aa,0x7a0858a000059959,0x821ac03ead8c0c43,0xd81bc01cb002e02,0xc040123c24100037,0xb3645e428448bcc8,0x502d1584b1958040]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x41b2c60037ae102a,0xba82c0501c00d285,0x401f64f012b80168,0x6a00a8fa44bb18,0x5402cebfe1860aac,0xc899f29e8105112d,0x9ee1740496fac807,0x6b401775808767f0,0xebfe68085628407,0xcd0a2395c063c214,0x2f7120463278343f,0x8808c9ce032c9080,0x72402e3400d02d,0x710008140ade614,0x552501035c0a0787,0x952c081b46026c13]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xfe6907384818efd5,0x408280bc03013a82,0x80626b202d801e80,0x3514034c123b077e,0x3d9f34d872f6f56d,0x36418628fb8de16,0x1c10bfc7681300a8,0xbbf3489182a89fec,0x71474880009a3580,0x3800fc55f89c0240,0x4f86a1a1cd980a83,0xfc37060004d863b8,0x158041d0343f0010,0x80f01009043f90f,0x8e168a182f150888,0xbc053a045685580]))
  | _ => 0

def samplesQ255 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xa20000550588040,0x400004023a00010,0xa010102010006910,0x140a0e14d11020e0,0x47043010a0040d0,0x80200500428822,0x160a0a020002144,0x8406410481400043,0x4000943004660068,0x500220051d8090,0x18001920003000,0x61a0020000034047,0x9400008001602020,0x1080134145081180,0x84920d180d20120,0x240244208120104]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x118e25a03048a039,0x24c6124870003020,0xa448588098120201,0x2308a3293a43653,0x2158640a0a544100,0xa6088253488a0c84,0x42482c32d250208e,0x224a03016a25a102,0x69d60528040d1154,0x286008941028c4,0x10a1104240220c4,0x241009852404054,0x12250048a822248a,0x960244408e0844c9,0x451c19c7894c236,0x80a450262010008]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x1240105a0101920,0x10a1066121202070,0xb010140412802c21,0x64638f36f1b47ae5,0xa47cc3831e002040,0x328a09002c44c0a8,0x110c880081099150,0x9008204cc2540818,0x8c04b18a0424305a,0xb4c0800714c0a2,0xc058000870302140,0x328017b002016145,0x306c100001084422,0x4542382c90201e8,0x48cb61f582029004,0xa213621000200042]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x344080088a013400,0x285422af404a6126,0x82600d2e5b96e3,0x42a0802b26af5f1f,0xeb8fb4cad578900d,0x543091852906058,0xe803031f014c0413,0x12b12c003cb20a90,0x301828ce52081210,0x50244984d800410b,0xb182da20c56080e4,0x920130911b841718,0x62a40a0cc40000d1,0x287040921006087b,0xe696df2c11215410,0xc4908220b4000820]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xa400002488709c0,0x122168310527c592,0x439181140300ac26,0x440214856c53c8a4,0xd6268bf5b5892096,0x1800640435153102,0x9435508020a5de01,0x4c14c8ea0500504d,0x94290212ba208a08,0x361600c001a4c502,0xa21006aa4021c008,0x38825a0228119d81,0x2002128200cc5800,0x2084380520649834,0x7baa346302602141,0x2541887d09080200]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x4411525203260406,0x4810c8040c0a4382,0x2a5a35144098082,0x8430090c4b8108,0x5a831874e1a38e22,0x493514a881200241,0x209242490c220a20,0x1009492100a1624,0x20040417280ca80,0x1403080248601100,0x3a008a2001058818,0x8012c80688841488,0x8808c1452810a44,0x4101001c20502216,0xb3241e0204082cc8,0x5024108491848000]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x9276300180008a,0x202890004000888,0xa01811000000000,0x8100504008408000,0x1000083420800a20,0xc010d28280011101,0x680100016904000,0x6800123000016500,0x2a3020021008801,0x8d02001000220000,0x22120400209040a,0xa484200280080,0x1000023004120c,0xc300080002308604,0x1120000248080283,0x112c080902002411]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x600980c800200015,0x4000000cc0180001,0x60030c3f0288,0xa8000080208051a,0x981340840761509,0x64006002280614,0x8000544480200a8,0x1e10001008880a0,0x140480040180400,0x1c01f8000200,0x150698000d800285,0x8405000014840038,0x38044500e030011,0x823040810006003,0x84148a0825050808,0x880118044405080]))
  | _ => 0

def compactPerms255 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains255 : Array (Sig × Nat) := ([(subcube 1 0, 10), (subcube 2 0, 10), (subcube 4 0, 10), (subcube 8 0, 10), (subcube 16 0, 10), (subcube 32 0, 10), (subcube 64 0, 10)] : List (Sig × Nat)).toArray

def compactWords255 : Nat → Nat
  | 0 => (limbs64 [0xe2383dcb9,0x87fba33f1ac688ff])
  | _ => 0

def compactCount255 (k : Nat) : Nat := match k with
  | 11 => 1
  | 10 => 1
  | _ => 0

def compactPath255 (k : Nat) (i : Nat) : Nat := match k with
  | 11 => 0
  | 10 => readCompactBits compactWords255 (35 + 12*i) 12
  | _ => 0

def compactLive255 (k : Nat) (i : Nat) : Nat := match k with
  | 11 => readCompactBits compactWords255 (0 + 8*i) 8
  | 10 => readCompactBits compactWords255 (47 + 9*i) 9
  | _ => 0

def compactPoolIDs255 (k : Nat) (i : Nat) : List Nat := match k with
  | 11 => let v := readCompactBits compactWords255 (29 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords255 (8 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 10 => let v := readCompactBits compactWords255 (84 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords255 (56 + 4*(v &&& 7)) (4*n)
    compactIDsFromBits bits 4 n
  | _ => []

def compactBucket255 (k : Nat) (i : Nat) : List Nat := match k with
  | 10 => let d := readCompactBits compactWords255 (90 + 1*(i % 1)) 1
    let off := ((i/1 + d) % 1)
    let v := readCompactBits compactWords255 (91 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | _ => []

theorem compactHalves {test : Nat → Bool} {start n : Nat}
    (first : chartBlock test start (n / 2) = true)
    (last : chartBlock test (start + n / 2) (n - n / 2) = true) :
    chartBlock test start n = true := by
  have eq : n / 2 + (n - n / 2) = n := by omega
  simpa only [eq] using chartBlock_join first last

def grid196 : CompactGrid := (196, 3, samplesP196, samplesQ196)
def tab196 : CompactTable := (compactCount196, compactPath196, compactLive196, compactPoolIDs196, compactBucket196)
def check196 (k : Nat) := compactNode grid196 tab196 compactDomains196 compactPerms196 k
def sliceSpecs196 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains196 : ∀ d ∈ compactDomains196, Slice true (vars 196) (graphGoal 196) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs196)
  · simp
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs196 : properPairs (graphGoal 196) (asRow samplesP196) (asRow samplesQ196) :=
  compactPairs (g := grid196) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos196 : ∀ p ∈ compactPerms196, autoOK (graphGoal 196) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c196k3p0 : chartBlock (check196 3) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev196k3 : chartBlock (check196 3) 0 1 = true :=
  c196k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded196 : Impossible true (graphGoal 196) 3 (vars 196).toFinset := by
  apply compactRoot (g := grid196) (t := tab196) (dom := compactDomains196) (perms := compactPerms196) pairs196 domains196 autos196
  · intro k hk
    change k ≤ 3 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev196k3
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound196 : Lower true (vars 196) (graphGoal 196) 4 :=
  plain_low (hints := 570426880) (by decide +kernel) excluded196

def grid228 : CompactGrid := (228, 4, samplesP228, samplesQ228)
def tab228 : CompactTable := (compactCount228, compactPath228, compactLive228, compactPoolIDs228, compactBucket228)
def check228 (k : Nat) := compactNode grid228 tab228 compactDomains228 compactPerms228 k
def sliceSpecs228 : List SliceSpec := [(32, 0, 196, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains228 : ∀ d ∈ compactDomains228, Slice true (vars 228) (graphGoal 228) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(196, 4)]) (specs := sliceSpecs228)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound196
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs228 : properPairs (graphGoal 228) (asRow samplesP228) (asRow samplesQ228) :=
  compactPairs (g := grid228) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos228 : ∀ p ∈ compactPerms228, autoOK (graphGoal 228) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c228k4p0 : chartBlock (check228 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev228k4 : chartBlock (check228 4) 0 1 = true :=
  c228k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded228 : Impossible true (graphGoal 228) 4 (vars 228).toFinset := by
  apply compactRoot (g := grid228) (t := tab228) (dom := compactDomains228) (perms := compactPerms228) pairs228 domains228 autos228
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev228k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound228 : Lower true (vars 228) (graphGoal 228) 5 :=
  plain_low (hints := 572523776) (by decide +kernel) excluded228

def grid166 : CompactGrid := (166, 3, samplesP166, samplesQ166)
def tab166 : CompactTable := (compactCount166, compactPath166, compactLive166, compactPoolIDs166, compactBucket166)
def check166 (k : Nat) := compactNode grid166 tab166 compactDomains166 compactPerms166 k
def sliceSpecs166 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains166 : ∀ d ∈ compactDomains166, Slice true (vars 166) (graphGoal 166) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs166)
  · simp
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs166 : properPairs (graphGoal 166) (asRow samplesP166) (asRow samplesQ166) :=
  compactPairs (g := grid166) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos166 : ∀ p ∈ compactPerms166, autoOK (graphGoal 166) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c166k3p0 : chartBlock (check166 3) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev166k3 : chartBlock (check166 3) 0 1 = true :=
  c166k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded166 : Impossible true (graphGoal 166) 3 (vars 166).toFinset := by
  apply compactRoot (g := grid166) (t := tab166) (dom := compactDomains166) (perms := compactPerms166) pairs166 domains166 autos166
  · intro k hk
    change k ≤ 3 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev166k3
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound166 : Lower true (vars 166) (graphGoal 166) 4 :=
  plain_low (hints := 537920848) (by decide +kernel) excluded166

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound102 : Lower true (vars 102) (graphGoal 102) 4 :=
  carry_of (old := 102) (rep := 166) (swaps := [118]) (by decide +kernel) bound166

def grid230 : CompactGrid := (230, 6, samplesP230, samplesQ230)
def tab230 : CompactTable := (compactCount230, compactPath230, compactLive230, compactPoolIDs230, compactBucket230)
def check230 (k : Nat) := compactNode grid230 tab230 compactDomains230 compactPerms230 k
def sliceSpecs230 : List SliceSpec := [(2, 0, 228, 0, 0, 5, 5), (0, 2, 196, 32, 15728640, 5, 4), (64, 0, 166, 0, 0, 4, 4), (128, 0, 102, 0, 0, 4, 4), (32, 0, 196, 0, 0, 4, 4), (32, 2, 196, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains230 : ∀ d ∈ compactDomains230, Slice true (vars 230) (graphGoal 230) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(228, 5), (196, 4), (166, 4), (102, 4)]) (specs := sliceSpecs230)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact bound228
    · exact bound196
    · exact bound166
    · exact bound102
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs230 : properPairs (graphGoal 230) (asRow samplesP230) (asRow samplesQ230) :=
  compactPairs (g := grid230) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos230 : ∀ p ∈ compactPerms230, autoOK (graphGoal 230) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c230k4p0 : chartBlock (check230 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev230k4 : chartBlock (check230 4) 0 1 = true :=
  c230k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c230k5p0 : chartBlock (check230 5) 0 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev230k5 : chartBlock (check230 5) 0 3 = true :=
  c230k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c230k6p0 : chartBlock (check230 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev230k6 : chartBlock (check230 6) 0 1 = true :=
  c230k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded230 : Impossible true (graphGoal 230) 6 (vars 230).toFinset := by
  apply compactRoot (g := grid230) (t := tab230) (dom := compactDomains230) (perms := compactPerms230) pairs230 domains230 autos230
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev230k4
    · exact lev230k5
    · exact lev230k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound230 : Lower true (vars 230) (graphGoal 230) 7 :=
  plain_low (hints := 571475280) (by decide +kernel) excluded230

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound214 : Lower true (vars 214) (graphGoal 214) 7 :=
  carry_of (old := 214) (rep := 230) (swaps := [114, 84]) (by decide +kernel) bound230

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound180 : Lower true (vars 180) (graphGoal 180) 4 :=
  carry_of (old := 180) (rep := 166) (swaps := [65, 117]) (by decide +kernel) bound166

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound178 : Lower true (vars 178) (graphGoal 178) 4 :=
  carry_of (old := 178) (rep := 166) (swaps := [81, 66]) (by decide +kernel) bound166

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound150 : Lower true (vars 150) (graphGoal 150) 4 :=
  carry_of (old := 150) (rep := 166) (swaps := [114, 84]) (by decide +kernel) bound166

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound54 : Lower true (vars 54) (graphGoal 54) 4 :=
  carry_of (old := 54) (rep := 166) (swaps := [33, 116]) (by decide +kernel) bound166

def grid182 : CompactGrid := (182, 6, samplesP182, samplesQ182)
def tab182 : CompactTable := (compactCount182, compactPath182, compactLive182, compactPoolIDs182, compactBucket182)
def check182 (k : Nat) := compactNode grid182 tab182 compactDomains182 compactPerms182 k
def sliceSpecs182 : List SliceSpec := [(2, 0, 180, 0, 0, 4, 4), (4, 0, 178, 0, 0, 4, 4), (16, 0, 166, 0, 0, 4, 4), (32, 0, 150, 0, 0, 4, 4), (128, 0, 54, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains182 : ∀ d ∈ compactDomains182, Slice true (vars 182) (graphGoal 182) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(180, 4), (178, 4), (166, 4), (150, 4), (54, 4)]) (specs := sliceSpecs182)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact bound180
    · exact bound178
    · exact bound166
    · exact bound150
    · exact bound54
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs182 : properPairs (graphGoal 182) (asRow samplesP182) (asRow samplesQ182) :=
  compactPairs (g := grid182) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos182 : ∀ p ∈ compactPerms182, autoOK (graphGoal 182) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c182k4p0 : chartBlock (check182 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev182k4 : chartBlock (check182 4) 0 1 = true :=
  c182k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c182k5p0 : chartBlock (check182 5) 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev182k5 : chartBlock (check182 5) 0 2 = true :=
  c182k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c182k6p0 : chartBlock (check182 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev182k6 : chartBlock (check182 6) 0 1 = true :=
  c182k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded182 : Impossible true (graphGoal 182) 6 (vars 182).toFinset := by
  apply compactRoot (g := grid182) (t := tab182) (dom := compactDomains182) (perms := compactPerms182) pairs182 domains182 autos182
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev182k4
    · exact lev182k5
    · exact lev182k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound182 : Lower true (vars 182) (graphGoal 182) 7 :=
  plain_low (hints := 537986368) (by decide +kernel) excluded182

def grid244 : CompactGrid := (244, 5, samplesP244, samplesQ244)
def tab244 : CompactTable := (compactCount244, compactPath244, compactLive244, compactPoolIDs244, compactBucket244)
def check244 (k : Nat) := compactNode grid244 tab244 compactDomains244 compactPerms244 k
def sliceSpecs244 : List SliceSpec := [(16, 0, 228, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains244 : ∀ d ∈ compactDomains244, Slice true (vars 244) (graphGoal 244) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(228, 5)]) (specs := sliceSpecs244)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound228
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
theorem c244k5p0 : chartBlock (check244 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev244k5 : chartBlock (check244 5) 0 1 = true :=
  c244k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded244 : Impossible true (graphGoal 244) 5 (vars 244).toFinset := by
  apply compactRoot (g := grid244) (t := tab244) (dom := compactDomains244) (perms := compactPerms244) pairs244 domains244 autos244
  · intro k hk
    change k ≤ 5 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev244k5
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound244 : Lower true (vars 244) (graphGoal 244) 6 :=
  plain_low (hints := 572982528) (by decide +kernel) excluded244

def grid242 : CompactGrid := (242, 4, samplesP242, samplesQ242)
def tab242 : CompactTable := (compactCount242, compactPath242, compactLive242, compactPoolIDs242, compactBucket242)
def check242 (k : Nat) := compactNode grid242 tab242 compactDomains242 compactPerms242 k
def sliceSpecs242 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains242 : ∀ d ∈ compactDomains242, Slice true (vars 242) (graphGoal 242) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs242)
  · simp
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs242 : properPairs (graphGoal 242) (asRow samplesP242) (asRow samplesQ242) :=
  compactPairs (g := grid242) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos242 : ∀ p ∈ compactPerms242, autoOK (graphGoal 242) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c242k4p0 : chartBlock (check242 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev242k4 : chartBlock (check242 4) 0 1 = true :=
  c242k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded242 : Impossible true (graphGoal 242) 4 (vars 242).toFinset := by
  apply compactRoot (g := grid242) (t := tab242) (dom := compactDomains242) (perms := compactPerms242) pairs242 domains242 autos242
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev242k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound242 : Lower true (vars 242) (graphGoal 242) 5 :=
  plain_low (hints := 1192296512) (by decide +kernel) excluded242

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound118 : Lower true (vars 118) (graphGoal 118) 5 :=
  carry_of (old := 118) (rep := 242) (swaps := [114, 84]) (by decide +kernel) bound242

def grid246 : CompactGrid := (246, 8, samplesP246, samplesQ246)
def tab246 : CompactTable := (compactCount246, compactPath246, compactLive246, compactPoolIDs246, compactBucket246)
def check246 (k : Nat) := compactNode grid246 tab246 compactDomains246 compactPerms246 k
def sliceSpecs246 : List SliceSpec := [(16, 0, 230, 0, 0, 7, 7), (32, 0, 214, 0, 0, 7, 7), (64, 0, 182, 0, 0, 7, 7), (2, 0, 244, 0, 0, 6, 6), (0, 2, 196, 48, 16711680, 6, 4), (4, 0, 242, 0, 0, 5, 5), (128, 0, 118, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains246 : ∀ d ∈ compactDomains246, Slice true (vars 246) (graphGoal 246) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(230, 7), (214, 7), (182, 7), (244, 6), (196, 4), (242, 5), (118, 5)]) (specs := sliceSpecs246)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound230
    · exact bound214
    · exact bound182
    · exact bound244
    · exact bound196
    · exact bound242
    · exact bound118
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
theorem c246k5p0 : chartBlock (check246 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev246k5 : chartBlock (check246 5) 0 1 = true :=
  c246k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c246k6p0 : chartBlock (check246 6) 0 5 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev246k6 : chartBlock (check246 6) 0 5 = true :=
  c246k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c246k7p0 : chartBlock (check246 7) 0 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev246k7 : chartBlock (check246 7) 0 3 = true :=
  c246k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c246k8p0 : chartBlock (check246 8) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev246k8 : chartBlock (check246 8) 0 1 = true :=
  c246k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded246 : Impossible true (graphGoal 246) 8 (vars 246).toFinset := by
  apply compactRoot (g := grid246) (t := tab246) (dom := compactDomains246) (perms := compactPerms246) pairs246 domains246 autos246
  · intro k hk
    change k ≤ 8 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev246k5
    · exact lev246k6
    · exact lev246k7
    · exact lev246k8
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound246 : Lower true (vars 246) (graphGoal 246) 9 :=
  plain_low (hints := 571540800) (by decide +kernel) excluded246

def grid254 : CompactGrid := (254, 9, samplesP254, samplesQ254)
def tab254 : CompactTable := (compactCount254, compactPath254, compactLive254, compactPoolIDs254, compactBucket254)
def check254 (k : Nat) := compactNode grid254 tab254 compactDomains254 compactPerms254 k
def sliceSpecs254 : List SliceSpec := [(8, 0, 246, 0, 0, 9, 9)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains254 : ∀ d ∈ compactDomains254, Slice true (vars 254) (graphGoal 254) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(246, 9)]) (specs := sliceSpecs254)
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
theorem c254k9p0 : chartBlock (check254 9) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev254k9 : chartBlock (check254 9) 0 1 = true :=
  c254k9p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded254 : Impossible true (graphGoal 254) 9 (vars 254).toFinset := by
  apply compactRoot (g := grid254) (t := tab254) (dom := compactDomains254) (perms := compactPerms254) pairs254 domains254 autos254
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
    · exact lev254k9
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound254 : Lower true (vars 254) (graphGoal 254) 10 :=
  plain_low (hints := 571565376) (by decide +kernel) excluded254

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound209 : Lower true (vars 209) (graphGoal 209) 5 :=
  carry_of (old := 209) (rep := 228) (swaps := [112, 84, 114]) (by decide +kernel) bound228

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound193 : Lower true (vars 193) (graphGoal 193) 4 :=
  carry_of (old := 193) (rep := 196) (swaps := [32]) (by decide +kernel) bound196

def grid201 : CompactGrid := (201, 4, samplesP201, samplesQ201)
def tab201 : CompactTable := (compactCount201, compactPath201, compactLive201, compactPoolIDs201, compactBucket201)
def check201 (k : Nat) := compactNode grid201 tab201 compactDomains201 compactPerms201 k
def sliceSpecs201 : List SliceSpec := [(8, 0, 193, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains201 : ∀ d ∈ compactDomains201, Slice true (vars 201) (graphGoal 201) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(193, 4)]) (specs := sliceSpecs201)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound193
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
  plain_low (hints := 3) (by decide +kernel) excluded201

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound73 : Lower true (vars 73) (graphGoal 73) 4 :=
  carry_of (old := 73) (rep := 196) (swaps := [32, 115]) (by decide +kernel) bound196

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound216 : Lower true (vars 216) (graphGoal 216) 4 :=
  carry_of (old := 216) (rep := 166) (swaps := [49, 116, 101, 114]) (by decide +kernel) bound166

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound153 : Lower true (vars 153) (graphGoal 153) 4 :=
  carry_of (old := 153) (rep := 166) (swaps := [32, 115, 65, 117, 33, 82]) (by decide +kernel) bound166

def grid217 : CompactGrid := (217, 6, samplesP217, samplesQ217)
def tab217 : CompactTable := (compactCount217, compactPath217, compactLive217, compactPoolIDs217, compactBucket217)
def check217 (k : Nat) := compactNode grid217 tab217 compactDomains217 compactPerms217 k
def sliceSpecs217 : List SliceSpec := [(8, 0, 209, 0, 0, 5, 5), (16, 0, 201, 0, 0, 5, 5), (0, 16, 73, 128, 4026531840, 5, 4), (1, 0, 216, 0, 0, 4, 4), (64, 0, 153, 0, 0, 4, 4), (128, 16, 73, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains217 : ∀ d ∈ compactDomains217, Slice true (vars 217) (graphGoal 217) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(209, 5), (201, 5), (73, 4), (216, 4), (153, 4)]) (specs := sliceSpecs217)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact bound209
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
theorem c217k5p0 : chartBlock (check217 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev217k5 : chartBlock (check217 5) 0 1 = true :=
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
  plain_low (hints := 458755) (by decide +kernel) excluded217

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound204 : Lower true (vars 204) (graphGoal 204) 5 :=
  carry_of (old := 204) (rep := 228) (swaps := [98, 83]) (by decide +kernel) bound228

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound197 : Lower true (vars 197) (graphGoal 197) 5 :=
  carry_of (old := 197) (rep := 201) (swaps := [112, 50]) (by decide +kernel) bound201

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound77 : Lower true (vars 77) (graphGoal 77) 5 :=
  carry_of (old := 77) (rep := 228) (swaps := [96, 82, 115, 101]) (by decide +kernel) bound228

def grid205 : CompactGrid := (205, 6, samplesP205, samplesQ205)
def tab205 : CompactTable := (compactCount205, compactPath205, compactLive205, compactPoolIDs205, compactBucket205)
def check205 (k : Nat) := compactNode grid205 tab205 compactDomains205 compactPerms205 k
def sliceSpecs205 : List SliceSpec := [(1, 0, 204, 0, 0, 5, 5), (4, 0, 201, 0, 0, 5, 5), (8, 0, 197, 0, 0, 5, 5), (128, 0, 77, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains205 : ∀ d ∈ compactDomains205, Slice true (vars 205) (graphGoal 205) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(204, 5), (201, 5), (197, 5), (77, 5)]) (specs := sliceSpecs205)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact bound204
    · exact bound201
    · exact bound197
    · exact bound77
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
theorem c205k6p0 : chartBlock (check205 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev205k6 : chartBlock (check205 6) 0 1 = true :=
  c205k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded205 : Impossible true (graphGoal 205) 6 (vars 205).toFinset := by
  apply compactRoot (g := grid205) (t := tab205) (dom := compactDomains205) (perms := compactPerms205) pairs205 domains205 autos205
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev205k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound205 : Lower true (vars 205) (graphGoal 205) 7 :=
  plain_low (hints := 1539) (by decide +kernel) excluded205

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound220 : Lower true (vars 220) (graphGoal 220) 6 :=
  carry_of (old := 220) (rep := 244) (swaps := [98, 83]) (by decide +kernel) bound244

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound212 : Lower true (vars 212) (graphGoal 212) 5 :=
  carry_of (old := 212) (rep := 228) (swaps := [114, 84]) (by decide +kernel) bound228

def grid213 : CompactGrid := (213, 5, samplesP213, samplesQ213)
def tab213 : CompactTable := (compactCount213, compactPath213, compactLive213, compactPoolIDs213, compactBucket213)
def check213 (k : Nat) := compactNode grid213 tab213 compactDomains213 compactPerms213 k
def sliceSpecs213 : List SliceSpec := [(1, 0, 212, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains213 : ∀ d ∈ compactDomains213, Slice true (vars 213) (graphGoal 213) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(212, 5)]) (specs := sliceSpecs213)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound212
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
theorem c213k5p0 : chartBlock (check213 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev213k5 : chartBlock (check213 5) 0 1 = true :=
  c213k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded213 : Impossible true (graphGoal 213) 5 (vars 213).toFinset := by
  apply compactRoot (g := grid213) (t := tab213) (dom := compactDomains213) (perms := compactPerms213) pairs213 domains213 autos213
  · intro k hk
    change k ≤ 5 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev213k5
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound213 : Lower true (vars 213) (graphGoal 213) 6 :=
  plain_low (hints := 460294) (by decide +kernel) excluded213

def grid157 : CompactGrid := (157, 4, samplesP157, samplesQ157)
def tab157 : CompactTable := (compactCount157, compactPath157, compactLive157, compactPoolIDs157, compactBucket157)
def check157 (k : Nat) := compactNode grid157 tab157 compactDomains157 compactPerms157 k
def sliceSpecs157 : List SliceSpec := [(4, 0, 153, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains157 : ∀ d ∈ compactDomains157, Slice true (vars 157) (graphGoal 157) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(153, 4)]) (specs := sliceSpecs157)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound153
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs157 : properPairs (graphGoal 157) (asRow samplesP157) (asRow samplesQ157) :=
  compactPairs (g := grid157) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos157 : ∀ p ∈ compactPerms157, autoOK (graphGoal 157) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c157k4p0 : chartBlock (check157 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev157k4 : chartBlock (check157 4) 0 1 = true :=
  c157k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded157 : Impossible true (graphGoal 157) 4 (vars 157).toFinset := by
  apply compactRoot (g := grid157) (t := tab157) (dom := compactDomains157) (perms := compactPerms157) pairs157 domains157 autos157
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev157k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound157 : Lower true (vars 157) (graphGoal 157) 5 :=
  plain_low (hints := 460547) (by decide +kernel) excluded157

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound141 : Lower true (vars 141) (graphGoal 141) 4 :=
  carry_of (old := 141) (rep := 166) (swaps := [32, 33, 115, 117]) (by decide +kernel) bound166

def grid221 : CompactGrid := (221, 8, samplesP221, samplesQ221)
def tab221 : CompactTable := (compactCount221, compactPath221, compactLive221, compactPoolIDs221, compactBucket221)
def check221 (k : Nat) := compactNode grid221 tab221 compactDomains221 compactPerms221 k
def sliceSpecs221 : List SliceSpec := [(4, 0, 217, 0, 0, 7, 7), (16, 0, 205, 0, 0, 7, 7), (1, 0, 220, 0, 0, 6, 6), (8, 0, 213, 0, 0, 6, 6), (0, 16, 77, 128, 4026531840, 6, 5), (64, 0, 157, 0, 0, 5, 5), (9, 0, 212, 0, 0, 5, 5), (17, 0, 204, 0, 0, 5, 5), (20, 0, 201, 0, 0, 5, 5), (24, 0, 197, 0, 0, 5, 5), (128, 16, 77, 0, 0, 5, 5), (4, 16, 73, 128, 4026531840, 5, 4), (5, 0, 216, 0, 0, 4, 4), (68, 0, 153, 0, 0, 4, 4), (80, 0, 141, 0, 0, 4, 4), (132, 0, 73, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains221 : ∀ d ∈ compactDomains221, Slice true (vars 221) (graphGoal 221) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(217, 7), (205, 7), (220, 6), (213, 6), (77, 5), (157, 5), (212, 5), (204, 5), (201, 5), (197, 5), (73, 4), (216, 4), (153, 4), (141, 4)]) (specs := sliceSpecs221)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound217
    · exact bound205
    · exact bound220
    · exact bound213
    · exact bound77
    · exact bound157
    · exact bound212
    · exact bound204
    · exact bound201
    · exact bound197
    · exact bound73
    · exact bound216
    · exact bound153
    · exact bound141
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs221 : properPairs (graphGoal 221) (asRow samplesP221) (asRow samplesQ221) :=
  compactPairs (g := grid221) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos221 : ∀ p ∈ compactPerms221, autoOK (graphGoal 221) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c221k4p0 : chartBlock (check221 4) 0 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c221k4p1 : chartBlock (check221 4) 8 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev221k4 : chartBlock (check221 4) 0 16 = true :=
  (chartBlock_join (a := 8) (b := 8) c221k4p0 c221k4p1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c221k5p0 : chartBlock (check221 5) 0 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c221k5p1 : chartBlock (check221 5) 8 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c221k5p2 : chartBlock (check221 5) 16 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c221k5p3 : chartBlock (check221 5) 24 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c221k5p4 : chartBlock (check221 5) 32 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c221k5p5 : chartBlock (check221 5) 40 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c221k5p6 : chartBlock (check221 5) 48 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c221k5p7 : chartBlock (check221 5) 56 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c221k5p8 : chartBlock (check221 5) 64 4 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev221k5 : chartBlock (check221 5) 0 68 = true :=
  (chartBlock_join (a := 32) (b := 36) (chartBlock_join (a := 16) (b := 16) (chartBlock_join (a := 8) (b := 8) c221k5p0 c221k5p1) (chartBlock_join (a := 8) (b := 8) c221k5p2 c221k5p3)) (chartBlock_join (a := 16) (b := 20) (chartBlock_join (a := 8) (b := 8) c221k5p4 c221k5p5) (chartBlock_join (a := 8) (b := 12) c221k5p6 (chartBlock_join (a := 8) (b := 4) c221k5p7 c221k5p8))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c221k6p0 : chartBlock (check221 6) 0 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c221k6p1 : chartBlock (check221 6) 8 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c221k6p2 : chartBlock (check221 6) 16 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c221k6p3 : chartBlock (check221 6) 24 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c221k6p4 : chartBlock (check221 6) 32 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c221k6p5 : chartBlock (check221 6) 40 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c221k6p6 : chartBlock (check221 6) 48 7 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev221k6 : chartBlock (check221 6) 0 55 = true :=
  (chartBlock_join (a := 24) (b := 31) (chartBlock_join (a := 8) (b := 16) c221k6p0 (chartBlock_join (a := 8) (b := 8) c221k6p1 c221k6p2)) (chartBlock_join (a := 16) (b := 15) (chartBlock_join (a := 8) (b := 8) c221k6p3 c221k6p4) (chartBlock_join (a := 8) (b := 7) c221k6p5 c221k6p6)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c221k7p0 : chartBlock (check221 7) 0 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c221k7p1 : chartBlock (check221 7) 8 6 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev221k7 : chartBlock (check221 7) 0 14 = true :=
  (chartBlock_join (a := 8) (b := 6) c221k7p0 c221k7p1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c221k8p0 : chartBlock (check221 8) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev221k8 : chartBlock (check221 8) 0 1 = true :=
  c221k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded221 : Impossible true (graphGoal 221) 8 (vars 221).toFinset := by
  apply compactRoot (g := grid221) (t := tab221) (dom := compactDomains221) (perms := compactPerms221) pairs221 domains221 autos221
  · intro k hk
    change k ≤ 8 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev221k4
    · exact lev221k5
    · exact lev221k6
    · exact lev221k7
    · exact lev221k8
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound221 : Lower true (vars 221) (graphGoal 221) 9 :=
  plain_low (hints := 460291) (by decide +kernel) excluded221

def grid253 : CompactGrid := (253, 9, samplesP253, samplesQ253)
def tab253 : CompactTable := (compactCount253, compactPath253, compactLive253, compactPoolIDs253, compactBucket253)
def check253 (k : Nat) := compactNode grid253 tab253 compactDomains253 compactPerms253 k
def sliceSpecs253 : List SliceSpec := [(32, 0, 221, 0, 0, 9, 9)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains253 : ∀ d ∈ compactDomains253, Slice true (vars 253) (graphGoal 253) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(221, 9)]) (specs := sliceSpecs253)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound221
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
  plain_low (hints := 460035) (by decide +kernel) excluded253

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound243 : Lower true (vars 243) (graphGoal 243) 9 :=
  carry_of (old := 243) (rep := 246) (swaps := [32]) (by decide +kernel) bound246

def grid251 : CompactGrid := (251, 9, samplesP251, samplesQ251)
def tab251 : CompactTable := (compactCount251, compactPath251, compactLive251, compactPoolIDs251, compactBucket251)
def check251 (k : Nat) := compactNode grid251 tab251 compactDomains251 compactPerms251 k
def sliceSpecs251 : List SliceSpec := [(8, 0, 243, 0, 0, 9, 9)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains251 : ∀ d ∈ compactDomains251, Slice true (vars 251) (graphGoal 251) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(243, 9)]) (specs := sliceSpecs251)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound243
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
  plain_low (hints := 65603) (by decide +kernel) excluded251

def grid247 : CompactGrid := (247, 9, samplesP247, samplesQ247)
def tab247 : CompactTable := (compactCount247, compactPath247, compactLive247, compactPoolIDs247, compactBucket247)
def check247 (k : Nat) := compactNode grid247 tab247 compactDomains247 compactPerms247 k
def sliceSpecs247 : List SliceSpec := [(1, 0, 246, 0, 0, 9, 9)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains247 : ∀ d ∈ compactDomains247, Slice true (vars 247) (graphGoal 247) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(246, 9)]) (specs := sliceSpecs247)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound246
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
    · rfl
    · rfl
    · rfl
    · exact lev247k9
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound247 : Lower true (vars 247) (graphGoal 247) 10 :=
  plain_low (hints := 66885) (by decide +kernel) excluded247

def grid238 : CompactGrid := (238, 7, samplesP238, samplesQ238)
def tab238 : CompactTable := (compactCount238, compactPath238, compactLive238, compactPoolIDs238, compactBucket238)
def check238 (k : Nat) := compactNode grid238 tab238 compactDomains238 compactPerms238 k
def sliceSpecs238 : List SliceSpec := [(8, 0, 230, 0, 0, 7, 7)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains238 : ∀ d ∈ compactDomains238, Slice true (vars 238) (graphGoal 238) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(230, 7)]) (specs := sliceSpecs238)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound230
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs238 : properPairs (graphGoal 238) (asRow samplesP238) (asRow samplesQ238) :=
  compactPairs (g := grid238) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos238 : ∀ p ∈ compactPerms238, autoOK (graphGoal 238) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c238k7p0 : chartBlock (check238 7) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev238k7 : chartBlock (check238 7) 0 1 = true :=
  c238k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded238 : Impossible true (graphGoal 238) 7 (vars 238).toFinset := by
  apply compactRoot (g := grid238) (t := tab238) (dom := compactDomains238) (perms := compactPerms238) pairs238 domains238 autos238
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
    · exact lev238k7
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound238 : Lower true (vars 238) (graphGoal 238) 8 :=
  plain_low (hints := 571499856) (by decide +kernel) excluded238

def grid237 : CompactGrid := (237, 7, samplesP237, samplesQ237)
def tab237 : CompactTable := (compactCount237, compactPath237, compactLive237, compactPoolIDs237, compactBucket237)
def check237 (k : Nat) := compactNode grid237 tab237 compactDomains237 compactPerms237 k
def sliceSpecs237 : List SliceSpec := [(32, 0, 205, 0, 0, 7, 7)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains237 : ∀ d ∈ compactDomains237, Slice true (vars 237) (graphGoal 237) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(205, 7)]) (specs := sliceSpecs237)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound205
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
theorem c237k7p0 : chartBlock (check237 7) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev237k7 : chartBlock (check237 7) 0 1 = true :=
  c237k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded237 : Impossible true (graphGoal 237) 7 (vars 237).toFinset := by
  apply compactRoot (g := grid237) (t := tab237) (dom := compactDomains237) (perms := compactPerms237) pairs237 domains237 autos237
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
    · exact lev237k7
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound237 : Lower true (vars 237) (graphGoal 237) 8 :=
  plain_low (hints := 1283) (by decide +kernel) excluded237

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound227 : Lower true (vars 227) (graphGoal 227) 7 :=
  carry_of (old := 227) (rep := 230) (swaps := [32]) (by decide +kernel) bound230

def grid235 : CompactGrid := (235, 7, samplesP235, samplesQ235)
def tab235 : CompactTable := (compactCount235, compactPath235, compactLive235, compactPoolIDs235, compactBucket235)
def check235 (k : Nat) := compactNode grid235 tab235 compactDomains235 compactPerms235 k
def sliceSpecs235 : List SliceSpec := [(8, 0, 227, 0, 0, 7, 7)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains235 : ∀ d ∈ compactDomains235, Slice true (vars 235) (graphGoal 235) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(227, 7)]) (specs := sliceSpecs235)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound227
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs235 : properPairs (graphGoal 235) (asRow samplesP235) (asRow samplesQ235) :=
  compactPairs (g := grid235) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos235 : ∀ p ∈ compactPerms235, autoOK (graphGoal 235) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c235k7p0 : chartBlock (check235 7) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev235k7 : chartBlock (check235 7) 0 1 = true :=
  c235k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded235 : Impossible true (graphGoal 235) 7 (vars 235).toFinset := by
  apply compactRoot (g := grid235) (t := tab235) (dom := compactDomains235) (perms := compactPerms235) pairs235 domains235 autos235
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
    · exact lev235k7
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound235 : Lower true (vars 235) (graphGoal 235) 8 :=
  plain_low (hints := 83) (by decide +kernel) excluded235

def grid231 : CompactGrid := (231, 7, samplesP231, samplesQ231)
def tab231 : CompactTable := (compactCount231, compactPath231, compactLive231, compactPoolIDs231, compactBucket231)
def check231 (k : Nat) := compactNode grid231 tab231 compactDomains231 compactPerms231 k
def sliceSpecs231 : List SliceSpec := [(1, 0, 230, 0, 0, 7, 7)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains231 : ∀ d ∈ compactDomains231, Slice true (vars 231) (graphGoal 231) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(230, 7)]) (specs := sliceSpecs231)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound230
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
theorem c231k7p0 : chartBlock (check231 7) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev231k7 : chartBlock (check231 7) 0 1 = true :=
  c231k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded231 : Impossible true (graphGoal 231) 7 (vars 231).toFinset := by
  apply compactRoot (g := grid231) (t := tab231) (dom := compactDomains231) (perms := compactPerms231) pairs231 domains231 autos231
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
    · exact lev231k7
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound231 : Lower true (vars 231) (graphGoal 231) 8 :=
  plain_low (hints := 1365) (by decide +kernel) excluded231

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound107 : Lower true (vars 107) (graphGoal 107) 7 :=
  carry_of (old := 107) (rep := 230) (swaps := [32, 115]) (by decide +kernel) bound230

def grid111 : CompactGrid := (111, 7, samplesP111, samplesQ111)
def tab111 : CompactTable := (compactCount111, compactPath111, compactLive111, compactPoolIDs111, compactBucket111)
def check111 (k : Nat) := compactNode grid111 tab111 compactDomains111 compactPerms111 k
def sliceSpecs111 : List SliceSpec := [(4, 0, 107, 0, 0, 7, 7)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains111 : ∀ d ∈ compactDomains111, Slice true (vars 111) (graphGoal 111) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(107, 7)]) (specs := sliceSpecs111)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound107
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
theorem c111k7p0 : chartBlock (check111 7) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev111k7 : chartBlock (check111 7) 0 1 = true :=
  c111k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded111 : Impossible true (graphGoal 111) 7 (vars 111).toFinset := by
  apply compactRoot (g := grid111) (t := tab111) (dom := compactDomains111) (perms := compactPerms111) pairs111 domains111 autos111
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
    · exact lev111k7
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound111 : Lower true (vars 111) (graphGoal 111) 8 :=
  plain_low (hints := 1363) (by decide +kernel) excluded111

def grid173 : CompactGrid := (173, 4, samplesP173, samplesQ173)
def tab173 : CompactTable := (compactCount173, compactPath173, compactLive173, compactPoolIDs173, compactBucket173)
def check173 (k : Nat) := compactNode grid173 tab173 compactDomains173 compactPerms173 k
def sliceSpecs173 : List SliceSpec := [(32, 0, 141, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains173 : ∀ d ∈ compactDomains173, Slice true (vars 173) (graphGoal 173) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(141, 4)]) (specs := sliceSpecs173)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound141
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
theorem excluded173 : Impossible true (graphGoal 173) 4 (vars 173).toFinset := by
  apply compactRoot (g := grid173) (t := tab173) (dom := compactDomains173) (perms := compactPerms173) pairs173 domains173 autos173
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev173k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound173 : Lower true (vars 173) (graphGoal 173) 5 :=
  plain_low (hints := 1283) (by decide +kernel) excluded173

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound167 : Lower true (vars 167) (graphGoal 167) 5 :=
  carry_of (old := 167) (rep := 173) (swaps := [80, 49, 114]) (by decide +kernel) bound173

def grid175 : CompactGrid := (175, 6, samplesP175, samplesQ175)
def tab175 : CompactTable := (compactCount175, compactPath175, compactLive175, compactPoolIDs175, compactBucket175)
def check175 (k : Nat) := compactNode grid175 tab175 compactDomains175 compactPerms175 k
def sliceSpecs175 : List SliceSpec := [(2, 0, 173, 0, 0, 5, 5), (8, 0, 167, 0, 0, 5, 5), (0, 2, 141, 32, 15728640, 5, 4), (1, 8, 166, 0, 0, 4, 4), (32, 2, 141, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains175 : ∀ d ∈ compactDomains175, Slice true (vars 175) (graphGoal 175) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(173, 5), (167, 5), (141, 4), (166, 4)]) (specs := sliceSpecs175)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact bound173
    · exact bound167
    · exact bound141
    · exact bound166
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs175 : properPairs (graphGoal 175) (asRow samplesP175) (asRow samplesQ175) :=
  compactPairs (g := grid175) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos175 : ∀ p ∈ compactPerms175, autoOK (graphGoal 175) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c175k6p0 : chartBlock (check175 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev175k6 : chartBlock (check175 6) 0 1 = true :=
  c175k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded175 : Impossible true (graphGoal 175) 6 (vars 175).toFinset := by
  apply compactRoot (g := grid175) (t := tab175) (dom := compactDomains175) (perms := compactPerms175) pairs175 domains175 autos175
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev175k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound175 : Lower true (vars 175) (graphGoal 175) 7 :=
  plain_low (hints := 1363) (by decide +kernel) excluded175

def grid239 : CompactGrid := (239, 9, samplesP239, samplesQ239)
def tab239 : CompactTable := (compactCount239, compactPath239, compactLive239, compactPoolIDs239, compactBucket239)
def check239 (k : Nat) := compactNode grid239 tab239 compactDomains239 compactPerms239 k
def sliceSpecs239 : List SliceSpec := [(1, 0, 238, 0, 0, 8, 8), (2, 0, 237, 0, 0, 8, 8), (4, 0, 235, 0, 0, 8, 8), (8, 0, 231, 0, 0, 8, 8), (128, 0, 111, 0, 0, 8, 8), (0, 2, 205, 32, 15728640, 8, 7), (64, 0, 175, 0, 0, 7, 7), (32, 2, 205, 0, 0, 7, 7)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains239 : ∀ d ∈ compactDomains239, Slice true (vars 239) (graphGoal 239) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(238, 8), (237, 8), (235, 8), (231, 8), (111, 8), (205, 7), (175, 7)]) (specs := sliceSpecs239)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound238
    · exact bound237
    · exact bound235
    · exact bound231
    · exact bound111
    · exact bound205
    · exact bound175
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
  plain_low (hints := 1363) (by decide +kernel) excluded239

def grid223 : CompactGrid := (223, 9, samplesP223, samplesQ223)
def tab223 : CompactTable := (compactCount223, compactPath223, compactLive223, compactPoolIDs223, compactBucket223)
def check223 (k : Nat) := compactNode grid223 tab223 compactDomains223 compactPerms223 k
def sliceSpecs223 : List SliceSpec := [(2, 0, 221, 0, 0, 9, 9)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains223 : ∀ d ∈ compactDomains223, Slice true (vars 223) (graphGoal 223) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(221, 9)]) (specs := sliceSpecs223)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound221
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
  plain_low (hints := 67139) (by decide +kernel) excluded223

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound179 : Lower true (vars 179) (graphGoal 179) 7 :=
  carry_of (old := 179) (rep := 182) (swaps := [32]) (by decide +kernel) bound182

def grid187 : CompactGrid := (187, 7, samplesP187, samplesQ187)
def tab187 : CompactTable := (compactCount187, compactPath187, compactLive187, compactPoolIDs187, compactBucket187)
def check187 (k : Nat) := compactNode grid187 tab187 compactDomains187 compactPerms187 k
def sliceSpecs187 : List SliceSpec := [(8, 0, 179, 0, 0, 7, 7)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains187 : ∀ d ∈ compactDomains187, Slice true (vars 187) (graphGoal 187) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(179, 7)]) (specs := sliceSpecs187)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound179
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs187 : properPairs (graphGoal 187) (asRow samplesP187) (asRow samplesQ187) :=
  compactPairs (g := grid187) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos187 : ∀ p ∈ compactPerms187, autoOK (graphGoal 187) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c187k7p0 : chartBlock (check187 7) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev187k7 : chartBlock (check187 7) 0 1 = true :=
  c187k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded187 : Impossible true (graphGoal 187) 7 (vars 187).toFinset := by
  apply compactRoot (g := grid187) (t := tab187) (dom := compactDomains187) (perms := compactPerms187) pairs187 domains187 autos187
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
    · exact lev187k7
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound187 : Lower true (vars 187) (graphGoal 187) 8 :=
  plain_low (hints := 65603) (by decide +kernel) excluded187

def grid183 : CompactGrid := (183, 7, samplesP183, samplesQ183)
def tab183 : CompactTable := (compactCount183, compactPath183, compactLive183, compactPoolIDs183, compactBucket183)
def check183 (k : Nat) := compactNode grid183 tab183 compactDomains183 compactPerms183 k
def sliceSpecs183 : List SliceSpec := [(1, 0, 182, 0, 0, 7, 7)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains183 : ∀ d ∈ compactDomains183, Slice true (vars 183) (graphGoal 183) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(182, 7)]) (specs := sliceSpecs183)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound182
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs183 : properPairs (graphGoal 183) (asRow samplesP183) (asRow samplesQ183) :=
  compactPairs (g := grid183) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos183 : ∀ p ∈ compactPerms183, autoOK (graphGoal 183) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c183k7p0 : chartBlock (check183 7) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev183k7 : chartBlock (check183 7) 0 1 = true :=
  c183k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded183 : Impossible true (graphGoal 183) 7 (vars 183).toFinset := by
  apply compactRoot (g := grid183) (t := tab183) (dom := compactDomains183) (perms := compactPerms183) pairs183 domains183 autos183
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
    · exact lev183k7
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound183 : Lower true (vars 183) (graphGoal 183) 8 :=
  plain_low (hints := 66885) (by decide +kernel) excluded183

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound189 : Lower true (vars 189) (graphGoal 189) 7 :=
  carry_of (old := 189) (rep := 175) (swaps := [65, 117]) (by decide +kernel) bound175

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound155 : Lower true (vars 155) (graphGoal 155) 5 :=
  carry_of (old := 155) (rep := 242) (swaps := [16, 97, 83, 116, 101]) (by decide +kernel) bound242

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound151 : Lower true (vars 151) (graphGoal 151) 5 :=
  carry_of (old := 151) (rep := 157) (swaps := [64, 49]) (by decide +kernel) bound157

def grid159 : CompactGrid := (159, 6, samplesP159, samplesQ159)
def tab159 : CompactTable := (compactCount159, compactPath159, compactLive159, compactPoolIDs159, compactBucket159)
def check159 (k : Nat) := compactNode grid159 tab159 compactDomains159 compactPerms159 k
def sliceSpecs159 : List SliceSpec := [(2, 0, 157, 0, 0, 5, 5), (4, 0, 155, 0, 0, 5, 5), (8, 0, 151, 0, 0, 5, 5), (0, 2, 141, 16, 983040, 5, 4), (1, 8, 150, 0, 0, 4, 4), (16, 2, 141, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains159 : ∀ d ∈ compactDomains159, Slice true (vars 159) (graphGoal 159) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(157, 5), (155, 5), (151, 5), (141, 4), (150, 4)]) (specs := sliceSpecs159)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact bound157
    · exact bound155
    · exact bound151
    · exact bound141
    · exact bound150
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs159 : properPairs (graphGoal 159) (asRow samplesP159) (asRow samplesQ159) :=
  compactPairs (g := grid159) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos159 : ∀ p ∈ compactPerms159, autoOK (graphGoal 159) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c159k5p0 : chartBlock (check159 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev159k5 : chartBlock (check159 5) 0 1 = true :=
  c159k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c159k6p0 : chartBlock (check159 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev159k6 : chartBlock (check159 6) 0 1 = true :=
  c159k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded159 : Impossible true (graphGoal 159) 6 (vars 159).toFinset := by
  apply compactRoot (g := grid159) (t := tab159) (dom := compactDomains159) (perms := compactPerms159) pairs159 domains159 autos159
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev159k5
    · exact lev159k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound159 : Lower true (vars 159) (graphGoal 159) 7 :=
  plain_low (hints := 67395) (by decide +kernel) excluded159

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound63 : Lower true (vars 63) (graphGoal 63) 7 :=
  carry_of (old := 63) (rep := 159) (swaps := [65, 117]) (by decide +kernel) bound159

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound45 : Lower true (vars 45) (graphGoal 45) 4 :=
  carry_of (old := 45) (rep := 166) (swaps := [32, 33, 115]) (by decide +kernel) bound166

def grid191 : CompactGrid := (191, 9, samplesP191, samplesQ191)
def tab191 : CompactTable := (compactCount191, compactPath191, compactLive191, compactPoolIDs191, compactBucket191)
def check191 (k : Nat) := compactNode grid191 tab191 compactDomains191 compactPerms191 k
def sliceSpecs191 : List SliceSpec := [(4, 0, 187, 0, 0, 8, 8), (8, 0, 183, 0, 0, 8, 8), (0, 8, 182, 1, 15, 8, 7), (2, 0, 189, 0, 0, 7, 7), (16, 0, 175, 0, 0, 7, 7), (32, 0, 159, 0, 0, 7, 7), (128, 0, 63, 0, 0, 7, 7), (1, 8, 182, 0, 0, 7, 7), (0, 2, 141, 48, 16711680, 6, 4), (0, 16, 45, 130, 4026532080, 6, 4), (18, 0, 173, 0, 0, 5, 5), (34, 0, 157, 0, 0, 5, 5), (2, 16, 45, 128, 4026531840, 5, 4), (32, 2, 141, 16, 983040, 5, 4), (128, 16, 45, 2, 240, 5, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains191 : ∀ d ∈ compactDomains191, Slice true (vars 191) (graphGoal 191) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(187, 8), (183, 8), (182, 7), (189, 7), (175, 7), (159, 7), (63, 7), (141, 4), (45, 4), (173, 5), (157, 5)]) (specs := sliceSpecs191)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound187
    · exact bound183
    · exact bound182
    · exact bound189
    · exact bound175
    · exact bound159
    · exact bound63
    · exact bound141
    · exact bound45
    · exact bound173
    · exact bound157
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
theorem c191k7p0 : chartBlock (check191 7) 0 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev191k7 : chartBlock (check191 7) 0 3 = true :=
  c191k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c191k8p0 : chartBlock (check191 8) 0 4 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev191k8 : chartBlock (check191 8) 0 4 = true :=
  c191k8p0
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
    · exact lev191k7
    · exact lev191k8
    · exact lev191k9
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound191 : Lower true (vars 191) (graphGoal 191) 10 :=
  plain_low (hints := 66883) (by decide +kernel) excluded191

def grid255 : CompactGrid := (255, 11, samplesP255, samplesQ255)
def tab255 : CompactTable := (compactCount255, compactPath255, compactLive255, compactPoolIDs255, compactBucket255)
def check255 (k : Nat) := compactNode grid255 tab255 compactDomains255 compactPerms255 k
def sliceSpecs255 : List SliceSpec := [(1, 0, 254, 0, 0, 10, 10), (2, 0, 253, 0, 0, 10, 10), (4, 0, 251, 0, 0, 10, 10), (8, 0, 247, 0, 0, 10, 10), (16, 0, 239, 0, 0, 10, 10), (32, 0, 223, 0, 0, 10, 10), (64, 0, 191, 0, 0, 10, 10)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains255 : ∀ d ∈ compactDomains255, Slice true (vars 255) (graphGoal 255) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(254, 10), (253, 10), (251, 10), (247, 10), (239, 10), (223, 10), (191, 10)]) (specs := sliceSpecs255)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound254
    · exact bound253
    · exact bound251
    · exact bound247
    · exact bound239
    · exact bound223
    · exact bound191
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
  plain_low (hints := 66883) (by decide +kernel) excluded255
def winningGates : List Gate := [⟨.or,[4,6]⟩, ⟨.and,[7,8]⟩, ⟨.or,[6,7]⟩, ⟨.or,[5,10]⟩, ⟨.or,[0,2]⟩, ⟨.and,[11,12]⟩, ⟨.or,[4,5]⟩, ⟨.and,[14,1]⟩, ⟨.or,[0,6]⟩, ⟨.and,[16,3]⟩, ⟨.or,[9,13]⟩, ⟨.or,[15,17]⟩, ⟨.or,[18,19]⟩]
theorem winningLegal : ∀ g ∈ winningGates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [winningGates,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem winningCorrect : ∀ x : Fin 8 → Bool, Circuit.eval ⟨winningGates,20⟩ (List.ofFn x) = edge8 x := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem asListed : ∀ x : Fin 8 → Bool, edge8 x = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by decide +kernel
end PEqualNP.Outside.L_meta_14716

open PEqualNP.Outside.L_meta_14716 PEqualNP.CircuitLowerBounds
theorem PEqualNP.Outside.L_meta_14716 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 2, 6, 3, 6, 0, 7, 2, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
