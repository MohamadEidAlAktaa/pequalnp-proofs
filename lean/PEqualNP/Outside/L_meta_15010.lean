import PEqualNP.Defs





namespace PEqualNP.Outside.L_meta_15010
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
def graph : Sig := (BitVec.ofNat _ (limbs64 [0xfffffffefffffffe,0xfffffffefffffffa,0xfffffefeffffeeee,0xfefefefeeeee0000,0xfffffffefffffffe,0xfffffffefffffffa,0xfffffefeffffeeee,0xfefefefeeeee0000]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
 (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7)
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
 (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7)
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
 (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7)
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
 (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7)
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

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([4, 4, 5, 7, 0, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([4, 4, 5, 7, 0, 0, 0, 0] : List Nat).getD i.val 0))

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

def samplesP82 : Nat → Bits
  | 1 => ~~~(0x4054 : Bits)
  | 4 => ~~~(0x1128 : Bits)
  | 6 => 0xdf7c
  | _ => 0

def samplesQ82 : Nat → Bits
  | 1 => ~~~(0xbbf6 : Bits)
  | 4 => 0x1812
  | 6 => 0x2224
  | _ => 0

def compactPerms82 : Array (List Nat) := ([[], [100], [65], [65, 100], [97, 100], [97]] : List (List Nat)).toArray

def compactDomains82 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray

def compactWords82 : Nat → Nat
  | 0 => 0x7
  | _ => 0

def compactCount82 (k : Nat) : Nat := match k with
  | 3 => 1
  | _ => 0

def compactPath82 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => 0
  | _ => 0

def compactLive82 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => readCompactBits compactWords82 (0 + 3*i) 3
  | _ => 0

def compactPoolIDs82 (k : Nat) (i : Nat) : List Nat := match k with
  | 3 => let v := readCompactBits compactWords82 (3 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords82 (3 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket82 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP210 : Nat → Bits
  | 1 => ~~~(0xa0304d120b2516a : Bits)
  | 4 => ~~~(0x20001120490c2690 : Bits)
  | 6 => 0x7af775afeb8e37d8
  | 7 => 0x6cfb905d7df04f22
  | _ => 0

def samplesQ210 : Nat → Bits
  | 1 => ~~~(0x75eedbb73beb75ee : Bits)
  | 4 => 0x2020010210800064
  | 6 => 0x544821423026588
  | 7 => 0x1385a8ad0856ef02
  | _ => 0

def compactPerms210 : Array (List Nat) := ([[], [97]] : List (List Nat)).toArray

def compactDomains210 : Array (Sig × Nat) := ([(subcube 128 0, 4)] : List (Sig × Nat)).toArray

def compactWords210 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def compactCount210 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath210 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive210 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords210 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs210 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords210 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords210 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket210 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP212 : Nat → Bits
  | 2 => 0xbbe9f93afbc31f98
  | 4 => ~~~(0x800390098431518 : Bits)
  | 6 => 0xebde763dfc8c67e2
  | 7 => ~~~(0x20084600608c62a2 : Bits)
  | _ => 0

def samplesQ212 : Nat → Bits
  | 2 => 0x461292a851552b88
  | 4 => 0x8821122049128a4
  | 6 => 0x15198859284c9742
  | 7 => ~~~(0xdfb6fbeb7df76bae : Bits)
  | _ => 0

def compactPerms212 : Array (List Nat) := ([[], [98, 116]] : List (List Nat)).toArray

def compactDomains212 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray

def compactWords212 : Nat → Nat
  | 0 => 0xf
  | _ => 0

def compactCount212 (k : Nat) : Nat := match k with
  | 3 => 1
  | _ => 0

def compactPath212 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => 0
  | _ => 0

def compactLive212 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => readCompactBits compactWords212 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs212 (k : Nat) (i : Nat) : List Nat := match k with
  | 3 => let v := readCompactBits compactWords212 (4 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords212 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket212 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP214 : Nat → Bits
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0x9400c4032,0xa199c0180410e0a0,0x3cf8331ee0444868,0xf189f2f14f4c15ea])) : Bits)
  | 2 => (BitVec.ofNat _ (limbs64 [0x5e6fdcdfbd,0xaa901f7dfdb5a7ab,0x85f871029fddd549,0xf8bf8070435ff0c0]))
  | 4 => ~~~((BitVec.ofNat _ (limbs64 [0x210000355,0xe12002118030701,0xc138d9238488918d,0x32168d70d2756ad0])) : Bits)
  | 6 => (BitVec.ofNat _ (limbs64 [0x7b5fbf6f73,0xd71a5ffb7e7a47c4,0x797fba3505ffeaad,0xf7070f809c7c3f18]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x6f9feff356,0x2df19fbf9fd3f831,0xfeb8d10afeeed9fe,0x33d8f07143e54ce2]))
  | _ => 0

def samplesQ214 : Nat → Bits
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0x76befb9bcf,0xdef6b39f7fb5decd,0xf7f6cdf775d67d7c,0xffcfeaed9f6e37ee])) : Bits)
  | 2 => (BitVec.ofNat _ (limbs64 [0x2198217102,0x144f9510508f4a34,0xd092388453d1c500,0xa00ca1a4751ef040]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x212010141,0x812100406200a00,0x9012002210502050,0x901202405021124]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x4a430900c,0xa4a30a280540c4,0x4780414025864020,0x56028281926c2608]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x1060948480,0xc2006a81011021c2,0xf0944110c2e180c,0xc0161382e10c82]))
  | _ => 0

def compactPerms214 : Array (List Nat) := ([[], [97]] : List (List Nat)).toArray

def compactDomains214 : Array (Sig × Nat) := ([(subcube 4 0, 5), (subcube 0 4, 5), (subcube 2 0, 4), (subcube 64 0, 4), (subcube 128 4, 4)] : List (Sig × Nat)).toArray

def compactWords214 : Nat → Nat
  | 0 => (limbs64 [0x3030b,0xfeff7f82be51a017,0xf8213fe33535806b,0xfe3e9e2e28c7ffff,0xd00e00900a82d41f])
  | _ => 0

def compactCount214 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 3
  | 4 => 1
  | _ => 0

def compactPath214 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords214 (26 + 12*i) 12
  | 4 => let v := readCompactBits compactWords214 (207 + 12*i) 12
    (readCompactBits compactWords214 (195 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def compactLive214 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords214 (0 + 5*i) 5
  | 5 => readCompactBits compactWords214 (62 + 6*i) 6
  | 4 => readCompactBits compactWords214 (219 + 7*i) 7
  | _ => 0

def compactPoolIDs214 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords214 (20 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords214 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits compactWords214 (88 + 5*i) 5
    let n := v >>> 3
    let bits := readCompactBits compactWords214 (80 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 4 => let v := readCompactBits compactWords214 (226 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords214 (226 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket214 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords214 (103 + 2*(i % 2)) 2
    let off := ((i/2 + d) % 8)
    let v := readCompactBits compactWords214 (107 + 11*off) 11
    if v >>> 3 == (i/104729)%251 then [v &&& 7] else []
  | 4 => let d := readCompactBits compactWords214 (228 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 5)
    let v := readCompactBits compactWords214 (230 + 9*off) 9
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

def samplesP242 : Nat → Bits
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0x420000a02205,0xc218108200aa0c3e,0x420063a0c483048b,0x2231b0e493928d8a])) : Bits)
  | 4 => ~~~((BitVec.ofNat _ (limbs64 [0x10400101c828,0x2520000c82051380,0x937145e19100364,0x98c60e1b0c497270])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0xfb0fb3bfa6ed,0x2103f6bfbee91fa2,0xbb0e10163ff75be8,0xaa17ee0204d7e460]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xde6fddefdb0e,0xc43bfbfecfbe23fc,0x41f366683f9fa47f,0x31e7901d89d99b18]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xf4cfeff16831,0xfa03fdcff3c7dc1f,0x4e340180fdfbc787,0xdef820e012ea7c82]))
  | _ => 0

def samplesQ242 : Nat → Bits
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0xbdfeffdbfdfe,0x7feeffd7defffaf7,0xdfbfbeffefb7edeb,0xfbfbfbb7dfdfafae])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x104241004008,0x2022020140821040,0x402140000846008,0x4220410086048584]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x4f0c7421852,0x4eead454141e50c6,0x541f20e36ba749a1,0x2852932386d7a420]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x2194125020e2,0x1b4465420e152023,0x430d0826e71180e3,0x9c1900718d90a08]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xb3814368546,0xd9dacc0844965ad,0x3351823a7c7a84a1,0x9848a66c38ea7802]))
  | _ => 0

def compactPerms242 : Array (List Nat) := ([[], [117, 65]] : List (List Nat)).toArray

def compactDomains242 : Array (Sig × Nat) := ([(subcube 32 0, 5)] : List (Sig × Nat)).toArray

def compactWords242 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount242 (k : Nat) : Nat := match k with
  | 5 => 1
  | _ => 0

def compactPath242 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => 0
  | _ => 0

def compactLive242 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => readCompactBits compactWords242 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs242 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let v := readCompactBits compactWords242 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords242 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket242 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP244 : Nat → Bits
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x8102060310190,0x9808220139830ed0,0x60026a3a20482932,0x414d0bb89d0c2696])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x6fbffefe7bebb8,0x9ffff6f9fbf31ff9,0xe8926a3f777da976,0x71df8bb89d5e6e96]))
  | 5 => ~~~((BitVec.ofNat _ (limbs64 [0x2e00c804d8a3b,0xb801c08043e01781,0xcf1bee7804212078,0x3f828fbf9e630cf6])) : Bits)
  | 6 => (BitVec.ofNat _ (limbs64 [0x5e6fbde7cd8796,0xfebfbbf79a0fe90,0x5f3a4a07afef373a,0x3f2c88380dabad84]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x7adfeff9f5187b,0xb7fdefc7c7cf07c7,0xe749a47efcfb68f9,0xcfc3078793e51672]))
  | _ => 0

def samplesQ244 : Nat → Bits
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x77ebdfd75eff7f,0xeceeffdbef6abded,0x7dfff7dfba7aeffa,0xd7fddaf5dbbcb6de])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x10410120c00443,0x502048111095203,0x224040066140140,0x4110a11254506a90]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x2e087824c2a19,0xaccc5848094830c9,0x41faa2cdb25aca12,0x826418d1519cb208]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x21923298107228,0xf264c21a04b40950,0xf0d9839f89a90e30,0x960c0c68a3ab8504]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x528141202a30c,0x48a46108cc602988,0x3100d28e18622a98,0x828510a183a41442]))
  | _ => 0

def compactPerms244 : Array (List Nat) := ([[], [101, 66]] : List (List Nat)).toArray

def compactDomains244 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray

def compactWords244 : Nat → Nat
  | 0 => 0x1f
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
  | 4 => let v := readCompactBits compactWords244 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords244 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket244 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP246 : Nat → Bits
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0x4280005100c2285,0x3806318546200103,0x90028380f4858,0x1b00576057d113b,0xc06230be17872581,0x8006405a0b458030,0x540f81840347e02b,0x9f6009fa1fd43fa5,0x40ea1e977ae1e070,0x70c384585d13c278,0x7a5f0e86d3e8fa87,0xe3a5f4e59345df16])) : Bits)
  | 2 => (BitVec.ofNat _ (limbs64 [0xdfcdfeff37f4f3fb,0xbabb51b38f0fffbf,0xbffbce7b69ff4c7b,0xca17fffe071f5a6b,0xc0e91f6a1e81203f,0xdffe77d37f71e4e7,0xf53fc4bf741661fb,0x83e27223b7d01fa5,0x60fe129052e029bc,0xd3cfdbf1fd82d161,0xea3f84cd4fc80a01,0xe1a055c3f6cc4d02]))
  | 4 => ~~~((BitVec.ofNat _ (limbs64 [0x4082000800606892,0x31945e8a840000c,0x20600409c1e00040,0xf004ea3c19878e41,0x6d95e611ed9b206,0x41003016420c781,0xe8318803e03c11d3,0x43dc3603e38097c1,0xf39fd398d7fc0e19,0x1ac9921318ee9c5,0xcf2730f10dde0f79,0xe1f25992b8fa6de2])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0xf63eff9dffef3af7,0x6716ad65202ff97f,0xefef7c2fffe8c9e7,0xf1bc1f75fd62909b,0x3e5a36a11241903f,0xfcf7df7be8a5bfb8,0x4cfff9dbe344101b,0x5f5c080affabb065,0x4f951110469c3e77,0x7caffcbb556fea45,0xbb4002f6b1d60a60,0x190396c1b70c1c2]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xfceafdefdbf8ef87,0xdd5c61c84ecfffff,0x73fdb1bc91ffb25c,0x35e7e3fff89da574,0xf6d8941d1803bf,0xa77fefed7fcfdb17,0xfa3fbb248be981e4,0x3fd8dd348041fda,0x90ebcc0ca9003e7b,0x23ffa74dfa12ee98,0x543f78b28e20059e,0x43b8b3990f7030]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xefb2ff7ffc7f6c9c,0x3be9168cf06ff7cf,0xfc7fffc9fe077fd8,0xfff8ec3e11e50f01,0xc701607fe4862427,0xff9ffbfe877ec7f9,0xffc18fc7003ffe03,0xfc0037fc03d4e781,0xf30a02831061ffd9,0xfdf09d7e399d01fe,0x4fc73f015008f001,0xe2247e94a0f38e04]))
  | _ => 0

def samplesQ246 : Nat → Bits
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0xfbd7f7fee6f7fd7f,0xcffbdefabbfebfd7,0xf7efdfd377bdbeed,0xfbdefffbbaebffef,0x7fffcfeffcfbfeeb,0xee76fdffebffedbf,0xff5ffdedb7dfbfbf,0x5bf7bfbdbf7dfedc,0xf5b7f7edffbffb7f,0x77e7ee5f5fb7fb7e,0xff5fffd6fffbd6af,0xbbd7fcfddb5dff5e])) : Bits)
  | 2 => (BitVec.ofNat _ (limbs64 [0x203241005c220404,0x5002c4470664402,0x24040aed2805114,0x5680441080408100,0x2404408081741414,0xc2bc049102002405,0x904008d308489,0xa900948269180229,0xa4c804020110100,0xc349c2a1e8021100,0x2814004048884852,0x88aa8503c68c4402]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x4082100840302802,0x20900c8284a0800,0x900c010102901040,0x6880421280820040,0x51002104d00201,0x6244140008900028,0x1200412011010482,0x4921108081484208,0x85110810000104,0x6042621242000222,0x40880422814004,0x8914844843049208]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x9c1043a0090c028,0x8861529a8a98a094,0x481194100310ac9,0x28403aca20092602,0x49a08346288a6aab,0x2842d90aa0438980,0x2452100930c92212,0x40e5021884454084,0x55a3448188a67a37,0x34062c1a15254808,0x930112908063122c,0x2114386c19508140]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x315219224050070,0x80a29e2291343281,0x41a00c9250088c8c,0x125c1c8800204a0b,0x1a20860a6823bc6a,0x843068e2e14a0092,0xa006b800849c903d,0x808c2d28143044,0x652242a00a8cf87b,0x3a5804d0801e818,0x30b7002842802aa,0x2c278b198096010]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x104d80a121801121,0xc036c131079191c0,0x20828c50086b8603,0x3d20446a0012a6,0x82a8a023a09c1e0,0x1d03a366a0664080,0x690210c460447264,0x44c4a75048331c2,0x300060844d847ec8,0x1cb01d441091484c,0x4701150090463180,0x66407a9420730804]))
  | _ => 0

def compactPerms246 : Array (List Nat) := ([[], [117, 65]] : List (List Nat)).toArray

def compactDomains246 : Array (Sig × Nat) := ([(subcube 32 0, 7), (subcube 64 0, 7), (subcube 128 0, 7), (subcube 4 0, 6), (subcube 0 4, 6), (subcube 2 0, 5), (subcube 16 0, 5)] : List (Sig × Nat)).toArray

def compactWords246 : Nat → Nat
  | 0 => (limbs64 [0x4a,0xc4bf39130200bfc3,0xe87fc034cbde827f,0xc3fc3fc2556e8218,0xb1c504eb6ffbebeb,0xede4c07311cc4131,0x4c38024020025d3,0xfe01e7f8ff140ffc,0x255ff05529540291,0x534876204319756,0x89872106345fffff,0xc0120100150a323f])
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
  | 5 => let v := readCompactBits compactWords246 (678 + 12*i) 12
    (readCompactBits compactWords246 (654 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | _ => 0

def compactLive246 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => readCompactBits compactWords246 (0 + 6*i) 6
  | 7 => readCompactBits compactWords246 (63 + 7*i) 7
  | 6 => readCompactBits compactWords246 (438 + 8*i) 8
  | 5 => readCompactBits compactWords246 (690 + 9*i) 9
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
  | 5 => let v := readCompactBits compactWords246 (699 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords246 (699 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket246 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let d := readCompactBits compactWords246 (231 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 9)
    let v := readCompactBits compactWords246 (233 + 11*off) 11
    if v >>> 3 == (i/104729)%251 then [v &&& 7] else []
  | 6 => let d := readCompactBits compactWords246 (518 + 2*(i % 2)) 2
    let off := ((i/2 + d) % 11)
    let v := readCompactBits compactWords246 (522 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | 5 => let d := readCompactBits compactWords246 (701 + 1*(i % 1)) 1
    let off := ((i/1 + d) % 1)
    let v := readCompactBits compactWords246 (702 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | _ => []

def samplesP254 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0x28ffe22e49a91bf,0x521ea7efaa3683ee,0xee9f9381fc0981ff,0x7e2b97a157fdc58f,0x5f6f06d900a7d2,0x860ff74ee20d3539,0x1006c9b4f8426e0e,0xccb3f000bbe1c003,0x730020b048fc38e9,0x8f9d8fb6512f7a28,0xfd19b3fc47f68af4,0x9d708a38f803f0f,0x534c2443c8032c7,0x67c3c1873c03781a,0x70303c66104c10c6,0xc387b3864e3883a4]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x9d066bff3fe36240,0x7ff9fd1da510448d,0xfff375b618bfff81,0xa93d00bbfdaf4234,0xa5800fff264f1800,0x3b28393e31401d6e,0x6f09020202bdb0f3,0x3a080209fc0601cc,0x8400d240b7003c7e,0xf95ffa6403fc9f39,0x1fee2c27fce443fe,0xc29bffde60268c9c,0x9005f5a200cbed28,0xe71086837f88024,0x43c188036eb87d,0x20f02e8b72c13408]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x7ff894083d7d76ff,0x99e1fa9eda3ffc72,0x701f68ff274f8611,0xd42ffb5e874003a2,0x4370500068affb92,0xc4d00070412dc280,0x50f0174bd9400074,0x211dadf600003e00,0x700030000bffa,0xffeffe5afd95dcaf,0x8e9f6fd8e93efd33,0x56666f1869c94012,0x674a071ff0340f07,0x3002d67f48000080,0xf800000e07fbfdd,0xde11917011580003]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x8ff117cfc27f8931,0xe1fe000effc07f7f,0x80617f47c7f047e9,0xffd0fce47803fc40,0x7e87a0e390f003fd,0xf03f811ed620c7,0xa0ffe880e4103f88,0x3e030ff0019c030,0x78f80d1c000777b7,0xcd6a6e7d3e1a1fd1,0xf0af53030e397e4b,0xab7c70e191114de0,0x78911818373e3039,0xc07c3f8683040f41,0x900c3e130cf36c94,0x332b4a4381864874]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xf28fe9d2e4e56e7e,0xac1ea7e155c90391,0x111eec79fbf679fe,0x81d4975ed7fe3a70,0x805890052600a42d,0x790fc8b1020aca3e,0xef06c9b407a251f1,0x30b3cf00ba0001c3,0x400d0a0b4f81fd5,0x7ef1fdc99ecf65d6,0xe256cfffb7c90577,0xf5a8885d8e7eb2f0,0x852adda40b400d06,0x9fbc2180c07b7024,0x604001840031dfa3,0x80ba403dac5b0708]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x60766bfddb1c9d80,0x7fe75af25aefb88d,0xffec8a4818bffe7e,0x56c268bbaa50bdcb,0x5a200ff8d9b04000,0x3b27c6c1ccb01d51,0x90f0344902bfcf0c,0xc544020947f80030,0x3e02d004800237f,0x76bff59be3f3e0c6,0x1ff1d027fb1bb389,0x3c9bf7201026b363,0x6ac52a59c0cbd2d0,0x98ef6103784001b,0x803c00701c16c77b,0xdc4c2d4c82a5c0c0]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xfd7994351b82ffcf,0x86015d7125ffff72,0xfe097bee7403806,0x2bff6f4528a0001d,0xbdaff018075f5c6f,0xc4d0000ebdf3e280,0xf09367f3d4d8003,0xde4e5df644063e0c,0x881f024f0303cf8f,0xb3f611a7ec60a37f,0x6160bcd810c7fc8c,0xff65970676d9400d,0x9afa20e3cf35c0f8,0xf0010879c88087c0,0xf83c209e389632a,0x2d44d4b07d263813]))
  | _ => 0

def samplesQ254 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0x2022020202029,0x108c414220200004,0x409008294000000,0xa0082084288820a,0x442050040441051,0x2910401854a10,0x1420c1800011429,0x4083004c60801028,0x2410000282401828,0x101010401011228,0x400832b0009280e4,0x57080125800505,0x400820004800405,0x234300001001212a,0x4520940a00481040,0x4181b08248300284]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x2186005608686028,0x41996582903008ad,0x2c303016058a2000,0x2d0a20392312d21c,0x486102914262c148,0x1088025295051818,0x9421800092043213,0x8a0828518ab048,0x6141484480c2b87a,0x814f382001148b01,0x192c2021dc240346,0x42995c8861a00c8e,0x2005118200590c24,0x6020a3231a08220,0x4065088a966eb05c,0x20902e0352811008]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x67aa24da5839323c,0x48a8eb86d37a59e5,0x6422303227168ab3,0x1d6a606927020890,0x4122c4daa115a084,0xc8cb18c412205443,0x42524754da822526,0x42401c5028df94c9,0x29c3c4dcd050befa,0xef6ffe12288554a5,0x8c830bc0a13e6833,0x5062669829c254a6,0x620d050e91700726,0x121646f711914089,0x16401050c2ffbedd,0xda11816011580002]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x4c801582c80a0000,0xc800220c15003321,0x2040522121020780,0x51c8208024011000,0x1101d20204920508,0x50200c22062800e1,0x4428810020040314,0x200322012128183,0xa4642140000a490,0x88624e6030080d40,0x80a540020e084e00,0x832800b0080140e0,0x3011010033102030,0x103015a202200a80,0x1009091504b32884,0x2222024181824820]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xc4312c8046050756,0x2c220a3503429110,0x108604606810caaa,0x9044114494250ce1,0x109030040c810c84,0x8f214420201a00a2,0x221860c521008080,0x3524e2130e700691,0x880a2511151c4785,0x7eb0c4c89eca6050,0x22124d4e02410411,0xb50080548a12d230,0x18a4828d9004142,0x98946480401c5844,0x2298410500114fa3,0x802a403ca44a0500]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xa171685102018356,0x6018918ad68880,0x82a228580031d86e,0x402006781504425,0x8a18006dbb206000,0x2500291c0422508,0x900122024de24080,0x196c450104680e44,0x9101054034394347,0x769cb01bc272a086,0x1750800571003108,0x288033080016b202,0x88e003bc842d1c2,0xce21005848005,0xa01402e07104c73b,0x9c4c0d0c02058040]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x90118800038009c2,0x200001100018402,0x180814000404008,0x110c04880c0042,0x8688212010001811,0x510c10160d02300,0x2100088b0461c008,0x2c01810600204200,0x802011200c084105,0x109001854420001a,0x6040941800c19088,0xc04810210188200,0x80e2206048044048,0x4000200888083142,0x8180c62021004122,0x54450902c242011]))
  | _ => 0

def compactPerms254 : Array (List Nat) := ([[]] : List (List Nat)).toArray

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

def samplesP209 : Nat → Bits
  | 0 => 0xbffbcdbbb7aa96e
  | 4 => ~~~(0x1008c18902aa86a : Bits)
  | 6 => 0xdbdd70bf5a33e70
  | 7 => ~~~(0xc117c921133374 : Bits)
  | _ => 0

def samplesQ209 : Nat → Bits
  | 0 => 0x408012182000046
  | 4 => 0x120080801c00380
  | 6 => 0x24610563403cc30
  | 7 => ~~~(0xf2de97db7dc33f6 : Bits)
  | _ => 0

def compactPerms209 : Array (List Nat) := ([[], [64], [118], [118, 64]] : List (List Nat)).toArray

def compactDomains209 : Array (Sig × Nat) := ([(subcube 64 0, 4)] : List (Sig × Nat)).toArray

def compactWords209 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def compactCount209 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath209 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive209 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords209 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs209 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords209 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords209 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket209 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP213 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xbfbfef7,0xe59dab6ffcf7e98f,0x17d1fd54eaef6de6,0xe4ce78d4d053526e]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xf53ff59,0x4677d00ff7eaf571,0x3cee5a8100dff113,0xdfdd840303ff9500]))
  | 4 => ~~~((BitVec.ofNat _ (limbs64 [0x1080600,0x642998603000a113,0x4c69fd12a052443,0xc7444cd75375456a])) : Bits)
  | 6 => (BitVec.ofNat _ (limbs64 [0xdcfefbe,0xbe68b42ffb3df37e,0xc0dfa47a0277fecb,0xfb20c0f81c7ce870]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x500810,0x8654a720c020416c,0x10d9607ec2424982,0xf888b0f89c5a9a74])) : Bits)
  | _ => 0

def samplesQ213 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x4048088,0x10620484008460b0,0x801820810830c06,0xc00040c1430046]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xac52aa,0xa9000df7a24002b4,0x5d63ac12a4db7000,0x920d1559c5df9100]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x10a0202,0x40089821082a0004,0x4142090102580110,0x2022910104809a80]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x2303031,0x85435a51010b41,0x343024804924f0c8,0x490004bc223c6030]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0xfaeffee,0xf9efddf7fbef66be,0xdfefff9bffdb7dde,0xfbefbf5bdddf9bf6])) : Bits)
  | _ => 0

def compactPerms213 : Array (List Nat) := ([[], [64]] : List (List Nat)).toArray

def compactDomains213 : Array (Sig × Nat) := ([(subcube 4 0, 5), (subcube 64 0, 5), (subcube 0 4, 5), (subcube 1 0, 4), (subcube 16 0, 4), (subcube 128 4, 4)] : List (Sig × Nat)).toArray

def compactWords213 : Nat → Nat
  | 0 => (limbs64 [0x1562be51a013b,0xd0397e80582b191f])
  | _ => 0

def compactCount213 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 1
  | 4 => 1
  | _ => 0

def compactPath213 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords213 (29 + 12*i) 12
  | 4 => let v := readCompactBits compactWords213 (83 + 12*i) 12
    (readCompactBits compactWords213 (71 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def compactLive213 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords213 (0 + 5*i) 5
  | 5 => readCompactBits compactWords213 (41 + 6*i) 6
  | 4 => readCompactBits compactWords213 (95 + 7*i) 7
  | _ => 0

def compactPoolIDs213 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords213 (23 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords213 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits compactWords213 (55 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords213 (47 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 4 => let v := readCompactBits compactWords213 (102 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords213 (102 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket213 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords213 (61 + 1*(i % 1)) 1
    let off := ((i/1 + d) % 1)
    let v := readCompactBits compactWords213 (62 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | 4 => let d := readCompactBits compactWords213 (104 + 1*(i % 1)) 1
    let off := ((i/1 + d) % 1)
    let v := readCompactBits compactWords213 (105 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | _ => []

def samplesP241 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x6fffffbf75,0xf3bf77bef7f72f7e,0x2f9fef8db95dde74,0xe79aee997ad4cb6e]))
  | 4 => ~~~((BitVec.ofNat _ (limbs64 [0x220210051,0x311330222002025a,0x260eee8938049a30,0x819a2a996ad4896a])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0x768fef73d9,0x2c9007effd4fcec7,0x322e460101eff888,0xbbbf7008627f5900]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x7b2fb7dc16,0x3f611ffbeafed079,0xec57986a09f7b77b,0x955d091609f9a470]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x2190061314,0x2ebd5808c044cc65,0x2817df6f88410448,0xb71d451e7b994f74])) : Bits)
  | _ => 0

def samplesQ241 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x1001000082,0x400000a04800000,0x2040000600,0x4100600000000146]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x228208011,0x1001209000491100,0x2009200108680008,0x2c40800a14015680]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x974728524,0x434fbec44116550e,0x7ccb939a136fe891,0x92a901aa36ff5800]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x4d0d8134c,0xc016c300e9302047,0x1e70060ab791b8f3,0x1d011582f8a030]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x5e6df5eafb,0x9747a2deacef9bb6,0xbd4db5b1ec69a66a,0xfff4e74a5f995ff6])) : Bits)
  | _ => 0

def compactPerms241 : Array (List Nat) := ([[], [118]] : List (List Nat)).toArray

def compactDomains241 : Array (Sig × Nat) := ([(subcube 32 0, 5)] : List (Sig × Nat)).toArray

def compactWords241 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount241 (k : Nat) : Nat := match k with
  | 5 => 1
  | _ => 0

def compactPath241 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => 0
  | _ => 0

def compactLive241 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => readCompactBits compactWords241 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs241 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let v := readCompactBits compactWords241 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords241 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket241 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP181 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xf77ff77,0xac7b5d7dfbbdc5f4,0xf077f5e4e39f8d71,0xf36e3710f4965a9c]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x2280043,0xf0185dc0890041f7,0x7705f4f4108132,0xc46b37f0f6186ade])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0xbcff9fb,0x734ed8bfff5b79e7,0x1e7c8054577de9ba,0xaeb930e0866d724a]))
  | 5 => ~~~((BitVec.ofNat _ (limbs64 [0x540130,0x246e8ec150103104,0x1878f9767e0809a1,0x3b3036eec746175e])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0xefbe7ff,0xf4bca6ffddf6f31f,0x9fb79323efad3a7,0x5d7306ee435aa556]))
  | _ => 0

def samplesQ181 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x888048,0x418080a0410c0b00,0x806080112060420,0x300a0101c186008c]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0xdd7bdb6,0x6ff7ea55effe74be,0xb759df7f98b1ffb3,0xfcefaeba3e38eefe])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x4302305,0x41127582410444d,0x50a9230281594892,0xa050540e617240]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x560914,0x20640a5482c0142c,0x3219107008b1f000,0xc4040a321e38e820]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x1050810,0xa02480508221020,0x2210140c00a08301,0x8410a2210188412]))
  | _ => 0

def compactPerms181 : Array (List Nat) := ([[], [82, 112]] : List (List Nat)).toArray

def compactDomains181 : Array (Sig × Nat) := ([(subcube 4 0, 5)] : List (Sig × Nat)).toArray

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

def samplesP229 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xeffffdfb7757,0xdd7ffdbcfda4ffee,0xfea7f0eeb7ea3b8,0xe3ef9b71dabb4a5e]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x408140831006,0x9d402c001024ba64,0xb4a7f0e0112a310,0x3659b71da920a5e])) : Bits)
  | 5 => ~~~((BitVec.ofNat _ (limbs64 [0xb0019005c59,0xc5c1c0004508e0c8,0xccfdc70f002c230c,0xfc889d7d170dc99e])) : Bits)
  | 6 => (BitVec.ofNat _ (limbs64 [0xf93f7b9cdc1e,0xa07fff7b550fb249,0xef584300dfbf3f1c,0xde70816012ddac18]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xdebfdfe718e9,0xc5bfeec7fe78e8f4,0xd8f5840fb5ffe347,0x3d8d9c1d05c6d986]))
  | _ => 0

def samplesQ229 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x101102008088,0x2090084481004,0x2804004008482088,0x281024301284052]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0xbf76bdddeffd,0xf6dcffdddf27ed7b,0xd7bfddf7f533efdd,0x6ff7f99cded63b7e])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0xb020d084950,0xc4d8528818012942,0x55388d13f111c511,0x53228844ad23220]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x6c465610331,0x5facc4190b944ae3,0x14519936d6b68f01,0x4c6005b02ed5ac08]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x216028482514,0x7254604c4b056121,0x4122c992a5238545,0x2424a91444c61904]))
  | _ => 0

def compactPerms229 : Array (List Nat) := ([[], [117]] : List (List Nat)).toArray

def compactDomains229 : Array (Sig × Nat) := ([(subcube 32 0, 4)] : List (Sig × Nat)).toArray

def compactWords229 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount229 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath229 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive229 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords229 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs229 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords229 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords229 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket229 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP245 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x6f7ffdff,0xdfeaeed9f76fb9d7,0x6fffdfcffefbffe7,0xf84ffb86fda1ef5a,0xf82da5559b790bdd,0x3b573fe7dec7dc7b,0xda7d6f25e7fa10b5,0xe2135f07bd89f1c8,0x4befaa8fd286ac96,0xe86b36fd34592e47,0xc1a4bc74ae4d51a9,0xd9a2963183294dc]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x1a80060,0x1402b51830031a9f,0x9c000081024b4668,0x2009e3303021afd7,0x5a402544ad2c4bdf,0xbf7904208010186c,0xd29123019143d605,0xe2734fe9c4a9c3a8,0x4acc8acffed6bde5,0x210a2131445cad5b,0x4860b2d1eb4ddfbf,0xf9fac46813cd6fe])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x7df5fefe,0x7fde9f3d5fb972ba,0xb7fbbcffffdee1fa,0x37adcbff32f9fe95,0x56d15de1678cea8a,0xac2dff7dedfe2fe7,0xebf1b3d5db17df47,0xd36324f85e71cf2c,0x282c4040acd2916d,0xf3ced56be995a179,0x58788ba3798c8e16,0xa15848cd35e522a]))
  | 5 => ~~~((BitVec.ofNat _ (limbs64 [0x8470080,0x418c0e419c2dfd62,0x3c0200045c0001c3,0xc30e0bc400c1f018,0x7f61c5f9c3f1ecef,0xaff812400807cf82,0x8418205841c1f86,0x38378781f81fe0f,0x8b2ffcf8fef2bfe0,0x804c108e311d2c79,0xa1bf4f2430cdef3f,0xee1df0b1786a7afe])) : Bits)
  | 6 => (BitVec.ofNat _ (limbs64 [0x7bcaffe7,0xf7afb5e7bc009e61,0x1bff7fb57fed464f,0xc7dfe7740dffb82a,0x5f60409eed255c03,0x5fd7febfd7fbdc,0xf4cbcfdb955dc682,0x19feae984a0321f,0x9bdcd8483a50009f,0x357de9be7f1e7d1a,0xa9bb625940c0813e,0x9ae75656940e0]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x5faefff9,0xfdd57f5ab8e74d0e,0x9bfee3ffdf7f1ff9,0xeb3a3ff9f247f1d5,0x2b42a76880f2e464,0x87a7fefbfb39dfae,0x1f97b22fbcee3f0c,0x2ee05978438fcea3,0xc603b4b044203f7d,0x8f9e3b97d76c8cf9,0x26475784b3416e01,0xe6045e92a8ac2a16]))
  | _ => 0

def samplesQ245 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x10801200,0x1004100600800208,0x1041400840410000,0x20980001004008a0,0x212008804800002,0x40022000600004a,0x1802006018004c,0x180020002000180,0x1a00040008081000,0x8020060c00180201,0x80002c000a001020,0x1c0011201800048c]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x7e57f5d7,0x6bff5eefeffcf5e2,0x6fa7edddeffeb577,0x5f677eeca9bd76fb,0xb7bffbfff7fbfdad,0xe29d9caef19afdff,0xf7ffbf77fd7f7da3,0x6a5afddd74dd6a7e,0xe5fa7ffbefbddeff,0x3d9aa1f3c6fdfffb,0xeaedffdbefebcbd5,0xa3df6e5e85bcf7fe])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x20a8120,0xc021404020028d01,0x82a008021100d00,0x8040861094829002,0x2000200290030461,0x1240891188802801,0x140810410028420,0x8a25202310029801,0x4019018000240080,0x6346904088010120,0x4060020220940484,0x4054808803565200]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x8474182,0x40c80601892cd562,0x2f20840184a62540,0x596646c081883218,0x15058870413060ad,0x829d8c8ee09840b0,0x6424341081604520,0x4a00ad0974904a40,0xe5587851c610463e,0x3d82a171c2e0940a,0xa00d0984402c2c4,0x20d62e4e85948100]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x4350498,0x6580a08035d6096,0xc5900d108c0a42ec,0x1c26114e42204641,0x100c1b504250a11c,0xe9a65466314ac180,0xd0802c5380203292,0x14101590cda80678,0x2504d0330211cc7f,0x141948b27540fc18,0x28940514000a15b,0x2226e5564290060]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x20512012,0x28a02a0451030e0,0x6684244486002024,0x4500508c01286200,0x90a4485560183980,0x601d10a851085484,0x420324308c247182,0x4010989820184038,0x804022192390443d,0x8982183064494c8,0x22044110c1424311,0x22804e1280a82012]))
  | _ => 0

def compactPerms245 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains245 : Array (Sig × Nat) := ([(subcube 32 0, 7), (subcube 128 0, 7), (subcube 4 0, 6), (subcube 64 0, 6), (subcube 0 4, 6), (subcube 1 0, 5), (subcube 16 0, 5), (subcube 68 0, 5), (subcube 65 0, 4), (subcube 144 0, 4)] : List (Sig × Nat)).toArray

def compactWords245 : Nat → Nat
  | 0 => (limbs64 [0x3fc2aaac90,0xd7fc453ff02436f3,0xd9ff1420003d5eaa,0x7cbedb7cb6dc4468,0x8813944732ce499c,0x739301100911100,0x501100900a005009,0x431100bfc0e69e,0x5c7f81ec60887c09,0xa02fca707ad9452e,0x785dd77274cd7a55,0xd33d48ff83a9e874,0xff07f82fdaee4f68,0x1c99b19f194cb7f8,0x3fc024680d58050a,0x1428cc99364c582f,0x5c396ac18334e688,0x11183440a0146318,0xc63f992537cbf2b4,0xad2dfdff7dff7fdd,0xfdffdfdff7f5ff7d,0x7dff7cfd7dbfefef,0xefefefec26026603,0xe223a611a2232223,0x2623260162212221,0x6021202166216621,0x6621262106202628,0x2620261ac012a010,0xe220a220c010a016,0x22602401400a2220,0x22012008017f87f8,0x7f80e4232ff82987,0xa94b0ff87aa41356,0x9fa4fd39a4cc9872,0xea58ca893f25a863,0x66002048b74ec2c,0x84b56e20d56846a,0x20c85747020d4497,0xa260a4956c20846,0xad566214c4970a96,0xaf4450b749ffffff,0xfffffffff7ee2222,0x2602202601401201,0x1400a00d0e223f])
  | _ => 0

def compactCount245 (k : Nat) : Nat := match k with
  | 8 => 1
  | 7 => 10
  | 6 => 26
  | 5 => 7
  | _ => 0

def compactPath245 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => 0
  | 7 => readCompactBits compactWords245 (27 + 12*i) 12
  | 6 => let v := readCompactBits compactWords245 (963 + 16*i) 16
    (readCompactBits compactWords245 (855 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 5 => let v := readCompactBits compactWords245 (2478 + 15*i) 15
    (readCompactBits compactWords245 (2334 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | _ => 0

def compactLive245 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => readCompactBits compactWords245 (0 + 6*i) 6
  | 7 => readCompactBits compactWords245 (147 + 7*i) 7
  | 6 => readCompactBits compactWords245 (1379 + 8*i) 8
  | 5 => readCompactBits compactWords245 (2583 + 9*i) 9
  | _ => 0

def compactPoolIDs245 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let v := readCompactBits compactWords245 (21 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords245 (6 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 7 => let v := readCompactBits compactWords245 (557 + 11*i) 11
    let n := v >>> 7
    let bits := readCompactBits compactWords245 (217 + 4*(v &&& 127)) (4*n)
    compactIDsFromBits bits 4 n
  | 6 => let v := readCompactBits compactWords245 (1687 + 7*i) 7
    let n := v >>> 5
    let bits := readCompactBits compactWords245 (1587 + 5*(v &&& 31)) (5*n)
    compactIDsFromBits bits 5 n
  | 5 => let v := readCompactBits compactWords245 (2646 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords245 (2646 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket245 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let d := readCompactBits compactWords245 (667 + 2*(i % 4)) 2
    let off := ((i/4 + d) % 15)
    let v := readCompactBits compactWords245 (675 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | 6 => let d := readCompactBits compactWords245 (1869 + 4*(i % 9)) 4
    let off := ((i/9 + d) % 33)
    let v := readCompactBits compactWords245 (1905 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 5 => let d := readCompactBits compactWords245 (2660 + 3*(i % 3)) 3
    let off := ((i/3 + d) % 11)
    let v := readCompactBits compactWords245 (2669 + 11*off) 11
    if v >>> 3 == (i/104729)%251 then [v &&& 7] else []
  | _ => []

def samplesP253 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xfa3c230f497e3d82,0x75625ff5df670b82,0x583b7359aae5b1f8,0x23257b45c7fd57ce,0xb8056058707facd8,0x40154d69ee281fd7,0xc6423d380b1561e0,0xe5ac7ad51d640e0c,0x62fe121360872b94,0xfe38f06cdaeb6990,0x2abc5151b3e87ddd,0xa0acf029772431d0,0xc06b5435509d04bc,0xe1b789087290da93,0x4e04372430a15984,0x6878634126965370]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x7ff6ac9bf953cbfd,0xc9d8f78269fbf41a,0x5c773eb6596b2e91,0x7cfa958a86e4debb,0x4438e37a8f805709,0x3b08f22510c48e16,0x1dadc036515a9e4e,0x1a4520a01ca87043,0x8c00002c8540d040,0xc73fef77746b43ff,0x32d7adaf6c6a70be,0xccbd1fd69a8cc463,0x841aacb180a2f53,0xb42d604ea86f2100,0x8023c0c0031a6ac7,0xfc0f2d4cc918a404]))
  | 3 => (BitVec.ofNat _ (limbs64 [0xb6c74f75f6be10ce,0x8e9bbe18767dfde2,0xafc7c7d1f49ecf1e,0x8f03ae4778dafb7c,0xa826068310083876,0x7d0e01d224e04008,0xe14806c0f4205187,0xe999c50be25081b0,0x41c000080002,0xffddffff7fa79cde,0xadfb0ef357b396e9,0xd57ad6fbc0b11a12,0x729660f4ef91d023,0x404280b78b800008,0x1c00009c00febfd,0xf3b102b171840003]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xc57bd38eb6a1dd73,0x7a8641ee5f188a7f,0x57dc8a4fd714bde7,0xd3a6dcb9bb0273d1,0x57c39d246e746ca7,0x80e44c96513fb027,0x38b43bc708958018,0xe45200d6e2870800,0x5105ac035a312429,0x65d779dbd538f68b,0xfa617e4d34d7aad3,0x7a93472554462a2c,0xbd089730a07cf880,0x9e2077f04660c464,0x381828321c4fc661,0x462299871a7148a8]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xffbffcf0003fe202,0x7ffda1ffa0800bfd,0xa01ffda1fffb41ff,0xfcd81ffe03ffac20,0x1ff8003f807fd300,0xfbb2007fd01ff8,0xffc0000bea01ff,0x1a007f280004100f,0x8078000c80c6d000,0xf9e6bfafbfd47f63,0xd53e9faec8fc3f21,0xff43a82ea83bc47f,0x7417ca00e200bf,0x3d8fe007d072081,0x802047c0208dbd7a,0x1843d23ea32a1404]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xedf1706b4fc5e6fd,0xa26f1e77b79ef565,0xf3a069ae0c715661,0x5fdfe231fd1d89e7,0xe3c67cc03f810007,0x8611be4c891360c1,0xca100af9a44fee10,0x14369a3545db0200,0x1281ba101a000214,0x3eff9ef7a955aa6c,0xc707e35edf15cd3e,0x13edffd00548f58c,0x77a3c901b7062b48,0x499b16b900780c12,0x721800140c2635bf,0x93ccac8a0ccd0380]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x1bc89ff4bfc83f3d,0x9535e80988e7769d,0xafe8947e238efa0e,0xa07d61fe7c23241f,0xf0199b85c18283f8,0xffe201bb820fe128,0x3703f50ff6a03e21,0x3eb854abb38e5f0,0x2d0245e025380deb,0x9beb4798e29e9535,0x5dc8f0b0ab0fc346,0x2f5629d02bd30b81,0x8f9c280e4f61d744,0x3e4409479598136c,0x5c7980bc350961a,0xa5945470d460a85b]))
  | _ => 0

def samplesQ253 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x6804000000281080,0x612a480001020102,0x80c244000003708,0x130140040092,0x40022c0010429,0x20c010008001100,0x110008080a001041,0x1420404044109c40,0x482000c00600,0x86004020182a0000,0x20ac00500068005c,0x8000100017200040,0x4009200000910018,0xe00100005a800880,0x4c00700800900880,0x6838014020801230]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x4810e52858384a24,0x491a18000b364020,0x10a50e5298022e83,0x5400280926c8219,0x51648a8d9206143,0x164c65a008450442,0x141090920a401502,0x5421640589013d00,0x8040d06511910a26,0x861d61757009409d,0x22c429062c4810b4,0xc4b5158092880020,0x1040a259088a6212,0x5027005b0aaa41a0,0x42297041061a6a85,0xec092d4448182004]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x304a6f61722aca4c,0x458a8ab0e7669069,0x95a70c43b02aa6a6,0x1f098ad0b0de1259,0x849262862d99bc78,0x883250f0110c5300,0x49284c48605c21d1,0x20c22d4164177c29,0xc311c2ef29b24206,0xf79dfdff7a2298d2,0x8c7904d352331449,0x552a46ead2105234,0x3210e4f42aaac031,0x50c3243f0aa90818,0x2ca0021992cfebf5,0xf33102a171840002]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x80690540e0018c06,0x400018834200038,0x43020804c00c80e2,0x52280b090505001,0x1900121520280284,0x9042244410a94484,0x2808949400100432,0x4040003088062003,0x6100818504160012,0x410431da4400e003,0x4a013a0924922281,0x813400340040a2c,0x18009450006c4020,0x184061a200424029,0x1100b2144fc240,0x40200871a314800]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x96a810c022c68001,0x16c1a2a6a4809c89,0x112918003398030,0x1088cc5601133460,0xa8e0111100148284,0x9201204c6a022b5,0x6264414525204228,0x2a9c8a3022aa0231,0x551e06900a0a50c1,0x79e29e8a87c43760,0x501216a880842f00,0x3b40882668024696,0x1344502232000e5,0x2d8a62021012605,0x80d083a22025957a,0x1042d23a83220400]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x59060a217c24211,0x80a665820cb405,0x10a1410216734000,0x509c4844000a2f6c,0xa0292c4816805912,0x4411001343508063,0x652000351af6088,0x217810c01c900b0,0x8c3802500b00f18d,0x38fb8e05a1550a2c,0x8502c1045b01c922,0x28ca350a002e590,0x5164002bf020941,0x192161900280512,0xb20c0840e120353f,0x93c4ac08044c0180]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x300009400c02101,0x8004200400010600,0x2040012802910000,0xa080600c0c002420,0x6049054002040000,0x410102038410a010,0x6010014830200,0x808020802600014,0x4882010c2001081,0x862020080900500,0x1100c0208104c002,0x2040281020430481,0x8184080241001440,0x4100a0084102206,0x104489004100140a,0x84501084408049]))
  | _ => 0

def compactPerms253 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains253 : Array (Sig × Nat) := ([(subcube 8 0, 9)] : List (Sig × Nat)).toArray

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

def samplesP211 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x5fbf,0xf3d69f56c7bddf7e,0x9f8fc152c657b9bc,0x9e69bf9083730b2c]))
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0x1140,0x80d89627e8085202,0x1decc05afeda01d8,0xd0223ff293825f6e])) : Bits)
  | 4 => ~~~((BitVec.ofNat _ (limbs64 [0x400,0x1026325040900444,0x8e830a53417488a9,0x74c969d8757a3a4])) : Bits)
  | 6 => (BitVec.ofNat _ (limbs64 [0x777e,0xfdeb76346ffafed0,0xbde37e4b2937cffb,0x4376101f0787f3c0]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x7c7f,0x9efcb2e907df77e7,0x4efc8a1050cefcc9,0xf58ef6e0905ec426]))
  | _ => 0

def samplesQ211 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x2044,0x8408608109811010,0x4180862008a19180,0x120181810931020c]))
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0x6eaf,0x5baff9dc94fff357,0xba5a69b72ffa0fdc,0xf37ffc5ad6867f7e])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x420,0x2410100008a100,0x1100100204,0x2022200000001c10]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x883,0x100814894320202,0xa2104004024a0c18,0x4054001294066140]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x389,0x21430806f644404a,0xa635508225066c40,0x81085236b44ec022]))
  | _ => 0

def compactPerms211 : Array (List Nat) := ([[], [113, 96]] : List (List Nat)).toArray

def compactDomains211 : Array (Sig × Nat) := ([(subcube 1 0, 5), (subcube 2 0, 5), (subcube 64 0, 5), (subcube 128 0, 5)] : List (Sig × Nat)).toArray

def compactWords211 : Nat → Nat
  | 0 => 0x41c9f
  | _ => 0

def compactCount211 (k : Nat) : Nat := match k with
  | 6 => 1
  | _ => 0

def compactPath211 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | _ => 0

def compactLive211 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords211 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs211 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords211 (13 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords211 (5 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | _ => []

def compactBucket211 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP219 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x7ee6ffd6,0xffe34ffb5791fd4a,0xcfefdff7f2f5feb,0xc7b63dde96f72e3a,0xddc0307c4d927b8,0xd2d05ff3ff3d9b7f,0x865d393fe79ffe44,0xc4b46a7431f21d78,0x671616113707c497,0xfd7fc17ed477670,0x7ea8fc46c21fd203,0x1004cf12c0b52cb0]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x5faaffff,0x8dffb38e6b860f64,0x88fff277fffbe83e,0x7fbc71fff79f1c0,0x66181cfba30f3840,0x4236e7ffeffe3c7,0xffefbecc3819ff9f,0xba1f81c84e003e8f,0x9868066648000a67,0xed791f9bffb84380,0x9f4380f7fce001cc,0xee00f973e188244]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x48f0050,0x819d09a103977ff6,0x2b00502320005804,0x8737821c96890c73,0x149c1ddf829faeff,0xf7ff8002000dc24a,0x2600115d2808fe5c,0xfa544a7745c21d7f,0x18ec0677fff7eff8,0x1d808121013e7c4,0xde4190dee21ffbff,0x1ff4f113203afffc])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x777fff7f,0xff9deb6db77ceeb3,0xe7ffffefe6f7fe35,0xbf4fbafd5cefcd35,0x51a79bc35aae9e37,0xe12ff9efd9fe5ebe,0x679a77fb3e65f078,0x7d5a55334dcc216f,0x60f5e666c4f6a50e,0x9aec9a7d1af6ab4c,0xd093738f2388a83a,0xf90b45591c2716c]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x6fddfffb,0xf3debcf1dbe770dd,0x72ff7ffbfbfc3fc5,0xffb5c765ff887e57,0x9a39fcdc21d0e7c2,0x6ccffdeafdfe748,0xf8f2d15fdffe63a6,0xda40ea2fb4afdc77,0x98c85810b9d00a73,0xf1ffe7e25153f5bf,0x275490b80d1213f4,0x7468e8233fcf00]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x2600302,0x2a2485304ec49,0xc600204042202e21,0x78005455c606114,0x4b399ac361c83772,0xc6ef884088120304,0xc0da300a161573a6,0xdc1ae1283cac3c6f,0xe0505676fdd68e72,0x8865960149767338,0x3792f0a70d8a93fe,0xef4ecd49395ef64])) : Bits)
  | _ => 0

def samplesQ219 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x1191049,0x20c3005006e0210,0x7306818303109011,0xc00002a489015192,0x1005e0d819060003,0x2c20d050b0258030,0x86a0289007806202,0x211481a40aa20100,0x5e49860110c167,0xc5604144c2b0030,0x46006c06c802c007,0x884e12c0140830]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x20558108,0x328408518428709b,0x571c10d1841092c1,0x5b109b8849200436,0x8146a0480892813d,0x8ccce5d500ea015,0x3a0008c0a90b48a,0x200203a51064cd03,0x2b5aa2928720d027,0x1590f91aea84190,0x1b0124035801c8c4,0x66804f931c180204]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x48f4051,0xa8d5002102b75be6,0x2bb2088150920abc,0x92d6d02e928d5213,0x94b44a8a0204ee,0xb7ba7d29adb09110,0x52ac048282c0260d,0x57d4b0109e96aa5a,0xaaa4cac22185e827,0xde27d34dc368101a,0x2a0262248c214ab,0x445a9ee4dbc50002]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x8800400,0x8060048048010044,0x820620400040804,0x82400200800248,0x600002400406040,0x210202001100088,0x10506030010001,0x4040201084100008,0x8020000108080010,0x1220100800540a00,0x8002100803000408,0x10900401c07040]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x10220812,0xc00410a20108d20,0x80c100082028602a,0x4c0040160e2000,0x6000010044290800,0xd10301820ec00640,0x2042800100060064,0x9ea01448400022f0,0x80100840000488,0xe080e06211002404,0x2014809004001230,0x1163006822238500]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x7d9fdefd,0xebfd7dffeeff5bf6,0x7bb7fbdff7be9fbd,0xf6f7f6bfbbdddbff,0xf7d7f5fedfffedef,0xbfbafd79bdb7b7fd,0xf7fefcffbfd7ef1f,0x77ddf9b6bfbfbb5e,0xfeffcfdfefbdfdff,0xde77d75dcf7f7fbe,0xffb7febfdfcef5af,0xccdefef6dbd5ff76])) : Bits)
  | _ => 0

def compactPerms219 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains219 : Array (Sig × Nat) := ([(subcube 1 0, 7), (subcube 2 0, 7), (subcube 8 0, 7), (subcube 64 0, 6), (subcube 0 8, 6), (subcube 16 0, 5), (subcube 128 8, 5)] : List (Sig × Nat)).toArray

def compactWords219 : Nat → Nat
  | 0 => (limbs64 [0x1c49accd45d7,0xfc7f8ff038f287f8,0x80009ecee7b3edcd,0xe4e70b4e659c2b38,0x24228ce1cc146484,0x5c644c54644c4c65,0x464443ff04e74abf,0xf06d33faff0290c9,0x498cff0601ff0049,0xa88ff0d1dab20b6f,0xf0cb5ff0ff04196c,0xe9dc5e4cc94230ad,0x26149109008209a0,0x330895210572bccf,0x1108208037aa917f,0x7fbf7f77f77fdff7,0x7f7ffb7bf6f30f26,0x224855989130ec22,0xd4c5290a6114e629,0x4c53982730423263,0x2e32422a42a32a32,0x221ff8ff1b220196,0xcf0d376e8cbaff1f,0xe3fc7f8e2b4aaaa0,0x66a9091dc0451032,0x8697438105297645,0x310289762a648764,0x3102897565201938,0x752a6487ffffffbf,0xfffda42e32a32c22,0xe32232221d19a23f])
  | _ => 0

def compactCount219 (k : Nat) : Nat := match k with
  | 8 => 1
  | 7 => 7
  | 6 => 14
  | 5 => 6
  | _ => 0

def compactPath219 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => 0
  | 7 => readCompactBits compactWords219 (27 + 12*i) 12
  | 6 => let v := readCompactBits compactWords219 (711 + 15*i) 15
    (readCompactBits compactWords219 (627 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 5 => let v := readCompactBits compactWords219 (1696 + 15*i) 15
    (readCompactBits compactWords219 (1576 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | _ => 0

def compactLive219 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => readCompactBits compactWords219 (0 + 6*i) 6
  | 7 => readCompactBits compactWords219 (111 + 7*i) 7
  | 6 => readCompactBits compactWords219 (921 + 8*i) 8
  | 5 => readCompactBits compactWords219 (1786 + 9*i) 9
  | _ => 0

def compactPoolIDs219 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let v := readCompactBits compactWords219 (21 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords219 (6 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 7 => let v := readCompactBits compactWords219 (408 + 10*i) 10
    let n := v >>> 6
    let bits := readCompactBits compactWords219 (160 + 4*(v &&& 63)) (4*n)
    compactIDsFromBits bits 4 n
  | 6 => let v := readCompactBits compactWords219 (1178 + 8*i) 8
    let n := v >>> 5
    let bits := readCompactBits compactWords219 (1033 + 5*(v &&& 31)) (5*n)
    compactIDsFromBits bits 5 n
  | 5 => let v := readCompactBits compactWords219 (1840 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords219 (1840 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket219 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let d := readCompactBits compactWords219 (478 + 2*(i % 3)) 2
    let off := ((i/3 + d) % 13)
    let v := readCompactBits compactWords219 (484 + 11*off) 11
    if v >>> 3 == (i/104729)%251 then [v &&& 7] else []
  | 6 => let d := readCompactBits compactWords219 (1290 + 2*(i % 5)) 2
    let off := ((i/5 + d) % 23)
    let v := readCompactBits compactWords219 (1300 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | 5 => let d := readCompactBits compactWords219 (1852 + 2*(i % 2)) 2
    let off := ((i/2 + d) % 10)
    let v := readCompactBits compactWords219 (1856 + 11*off) 11
    if v >>> 3 == (i/104729)%251 then [v &&& 7] else []
  | _ => []

def samplesP251 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x8ff7cfff4f1dff80,0x2ffecc62c067f47f,0x502b95f794f9000f,0x2ff92ad1efd7f460,0x9fc60edfeffe1080,0x8b7ba54b18835625,0x66d01e0f7f4fd200,0x1a2ed24396e007c,0xd026c060f0af7c12,0xe0c1a604f8d87e32,0x7a60a4fd8b81edc,0x135ff419bd3e0719,0xc23b00aff2a005f1,0xe8369250850fd81a,0x2806020e863abae0,0x44da040cba19a4b0]))
  | 1 => (BitVec.ofNat _ (limbs64 [0xdc5ecf4bf0bf87ff,0x3b7ffb6c63fa2fc7,0x8cff6989fb838d3b,0x96fec40f9c114fdf,0x32ef4447f5c7b1e,0xf9845a06f26881da,0x8c24602077b001cb,0x6bf117d94688df91,0x17318303408001,0x70651f889f775c9,0x2e8fc2f3b6d7f16e,0xb28764bd4ac1b900,0x7c4353027508f402,0x1f7e69861a9c07e0,0x173809d1480028c3,0xe5a1ea270d841a44]))
  | 3 => (BitVec.ofNat _ (limbs64 [0xfeaff5de8feedd6f,0xdebfd387febccce3,0xe5546f8e1cbf9fc9,0xf88773e870edd126,0x9cf9773ff0202a30,0x64900cec626ce80d,0x4a2148d780d0ec16,0x96152020f9767a0a,0x3ff8061c0000000c,0x180000ff5ffd3f,0x7af1ad8da53ff6f7,0xbce9ed5fe77026ae,0x21c745c06ffc1be,0x84482c4662b00000,0x8001f00010c07cfe,0xbb186fc8c3900003]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x7b5fb5a7bef2e6f0,0xf6f12d9abd58db7c,0xaa93ba47f446e0fe,0xd7015dde672e2ae7,0x6f39893867c1c4e7,0x126c55b367112828,0x93ce912881a73de9,0x24ad11b38118388,0xcfc689832c5063e0,0xd9a02823cf2cdb0c,0x9b583ab85d66055b,0x4fab9ab666b5c056,0x45a489238a50dbcd,0x10b94029fe412035,0x40d405f0a1155592,0x1534d1185063416c]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x2fb93ab3ff5f7fff,0xfdbff69163850fb8,0x733cd671ef7c7234,0x6effbb2ffbe94fb8,0xf32efba418a38419,0x5fba0058d9601f7,0x71047fd0764801cb,0x680c16e68008dc66,0x2011c000c3870000,0x60781c07fffebf6,0xcd7ff7fdab17e931,0x51729b629d09bee0,0x3b8352d188082a03,0xe04197f91d6c07c0,0x1820000e0c22773f,0x804694f791a89800]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xf3ea7bfdf9fd797f,0xcbc53bfd1c673311,0xbfe89dfe6b36ffc2,0x293695318f16bb9f,0x6cd12edb9307ef60,0xca015a3000a357d2,0x91bba20f0822ae34,0x95a0e8db46912175,0x422938600c288b53,0x1800501c76ff97ed,0xf529f50277e81fa7,0xed542bc1b8864119,0xbddcac8c3d570440,0x57809baf60026002,0x27c80c01620ccb3d,0xba4503302e562700]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xf5f5fe7c77e3ba9f,0xf54afc7f9f9bf08e,0x5fc7623803c97ff5,0xd148eef610fab459,0xf0d7d1e38c9811cf,0x3406a3d89d5cbe00,0x2c5b85f0881d5234,0xfc5f0a0487e72483,0xbdc8061c101014ac,0x20780e03b7a3aed3,0xf0d65d764ac9ea88,0xeebc57ee504a58e7,0x8060af7041a73a3c,0x2b87641081f2980d,0xc003f22011c1074d,0x4aab38c36460409b]))
  | _ => 0

def samplesQ251 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x8c02440149008100,0x240408604000c891,0x100308080030000d,0x30401060c00000,0xfc6200003060000,0x4085008318200008,0x8903c0000928200,0x2120080080109,0x9218060300800840,0xc6081880407420,0x280024c10b80004,0x120820180a460600,0x1b0020300001b2,0x4036080005004018,0x100e0010140a28c0,0x49800048a00a030]))
  | 1 => (BitVec.ofNat _ (limbs64 [0xd0048c016008034a,0x20688924000048c2,0x21280842100000,0x454400424510001,0x5626400054a0202,0x400420010a100499,0x89228522401888c,0x30a2120912441109,0x1492424108805880,0xd2000880407480,0x5026310d5500e,0xa201441c4a411300,0x449400254001092,0x1a290000081299,0x1308a0d0040828c0,0x64a068060d001204]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x6e8761448d8cd46c,0x963e04232a284d80,0xc4151c9a9894b450,0x80916040b164832a,0xa552230d210c8803,0xa2b1c6d631ac60c1,0x1045144330b24ec6,0xaa9089aada6900a2,0x870aab09a1b20a14,0xb5e2c088ed5efd39,0x12e1ac8d842f9663,0x98c9e9072750228a,0x128d2044929a429a,0x84521c0a2a804302,0x8296c08530937cfa,0xb9186788c3900002]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x2019000680022400,0x1280048100181320,0x40000207880000f2,0x8004c813000046,0x6000020060a00041,0x2710013080044000,0x8245420081204002,0x40010640000280,0x400188003310800c,0x101800409088900,0x190018800d000151,0xa2802220b02006,0x418001018000ca40,0x80800400f8000020,0x88100400a9115402,0x100811850234040]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x3b83292165720b5,0x89356110d0c2508,0x619c50d2ad08a550,0x4a8a0942990062aa,0xb0081ba9a820dd50,0x15288920a1088262,0xe200c3099b401461,0x8c44240408b2ae34,0x4141382c25132437,0x190882e17fbf8b56,0x4d5ad010a902a910,0x41721b608418a842,0x9a8018d488136201,0xa14116cb28242960,0x48205c068920d73f,0x804694f110a80800]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x14001f800f15810,0xc90132001d422400,0x894d1f00002ed00,0x2800192188022ab8,0x9000013b980041b8,0x88005e4c00822820,0x3520012808480020,0x21dece00011a412,0x2020301c00470012,0x180027c376b7020d,0xe4286500620006a0,0xd14028190080051,0xba00885c00572400,0x1340922f00002002,0x20e00a2140e0833d,0x9a45022020540500]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x10609a2832200a83,0x4140e20885812004,0x2c0404000410300,0x19008b0008083480,0x10018060884016a8,0x1808300802128e12,0x4522803006091009,0x1429404100861804,0x20e0108440090102,0x4a00124112a102c2,0xa016013242406888,0x640414c050084060,0x88200e1001212004,0x9004211005218c1,0x6140326240400305,0x4223184324400089]))
  | _ => 0

def compactPerms251 : Array (List Nat) := ([[]] : List (List Nat)).toArray

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

def samplesP247 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x445705a921d85c2e,0xfe64c3ff66fcea79,0xfff33f666fd1fd23,0x7e0eb97fed012b1e,0xd34f5932df256d23,0xed7c2f190a1a1068,0xdbb684494cba2312,0x2fa39f188de01ed,0x6a0082342e9eb190,0xca026bd4981a5406,0x8f5729fd0c4e52ee,0xd26fde8c68ad150,0x52e40a159b438b24,0xed1ad02b1f0e6b0b,0xa108403321a8b5b,0x7428140438a29258]))
  | 1 => (BitVec.ofNat _ (limbs64 [0xf22032401a03824f,0xd7f8fddcfbd3fc7f,0x3f17f3dd7c9493fa,0xc459e4fcc1fee8f3,0x3f2fe2cff500bbd3,0xd2a376fe99c20d9d,0x2a5c60310205ddcc,0xf41853f0400ae54,0xe4b24cbf5400baf,0x102c840040a101e8,0x1d7bf4cc7f47b8dd,0xc1dca6b549ecd62d,0xc03b626a71496c01,0x9a990f10746c00b4,0x4a760384161015d,0x6a1529978c100d21]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xb8848004404000f,0xedfbeffebdff3dd1,0xf3bcbdbbebe36f5c,0xafb1514ad6c8fba9,0xfcb175e1a6fe8465,0xab9fd86482ac7a67,0xb4413b80335044c4,0x29a2f68ad7274088,0xb1b459a441a77e40,0x2451100022448a10,0xedb3d6fe1d86d8a,0xf7bad65f66fdbaa0,0x350c5432e69685fb,0x520b999a2719040,0x14003c40c80157a,0x8789fed8c0c52002]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xb5669196a86121d5,0xf787bf675f672fe7,0x9befe6a59f2fc1ac,0x39eec78f357157df,0x23512e9c98d5d75e,0x1e8b8f16f615e390,0xc7a947568c425c31,0xf3053a0170d9fd13,0x5407620a50994182,0x118c832b150a2025,0x68e6177231bda3e1,0x34e53a66bdb03c4e,0x1a298da918a032c5,0x147581ced8906406,0xf008183ac2246090,0xc8c6b0e0538a40b5]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x8582c005382040f,0xbffffe5b83abd3fe,0xdcebcbfaf36a92d5,0x4571a733b7f94ec,0xc38e9d2f6afabeaf,0xdd5379e164220e62,0x9e3986ef107a220,0xcbe413efb20afaa,0x8e4cd90b8a200a30,0xc20781020f481d0,0x13bfcab3beb7c432,0xfbfb9925b153c98d,0xad1692546ab55004,0x60066ee46b8d90b8,0x74600043c5203a6,0x12e6036f1160ac02]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x4e8082430000dbbf,0x7b9f11adfcffd7ae,0xed5c7dfff79d6e7f,0xf3fc3eb17ab62d03,0xacf4b3737bdb7298,0x24ec82837541900d,0x240461817fedb83b,0xd4184c4424061044,0xf1bb2e743e79c46d,0xc1820426cd010008,0x8fbcca96d2687f57,0xfa414fda5e776652,0x67d3a184846a8fda,0xd2c2664400720400,0x8b9f8000109eae4,0x1559c320ee581380]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xb181403c843c200b,0xf87f7eb3ff1cff9f,0x66ffde5f9c7e3c83,0xdba3ef848e8fd674,0x5cfacedc052f49fc,0x7374f50809fde592,0x501a9ebe80b803cf,0xf04582c00bf95233,0x1f095d18146b440,0x225100c902007e03,0x67edf709cfb39f3d,0xe1f619bbb0f21b3,0x88c07dcb051c703a,0x2bed103385820b41,0xf00007c1808416ad,0xa9324c1b2705404c]))
  | _ => 0

def samplesQ247 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x120081206208016,0xc000c20c24000079,0x11003220c509000,0x261c2904400002b4,0x8005605002002422,0x420c0a01020a0a02,0x400c21c800002012,0xf40820084000121,0x24400a1051400001,0x300180120860201e,0x1c532104000640cc,0x12224480000d250,0x4022382410100,0xc51800093d00000b,0x41100074010855a,0x6400140408009018]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x10c893404801536,0xc150c8d429508c2d,0x202031444c09008,0xa2182028802442b0,0x208204913002011,0x2024c5303084800,0xb218a25880210412,0x4500c02480300885,0x2c64302930412411,0x8101929808000816,0x1c53a44809071045,0x8114a415402c5209,0x4001202253012500,0x8000051934080223,0x2525408840b08159,0x6a0108960c000901]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x8161b726036ae426,0xcd11235815f53550,0x39034a34961b200,0x23182040044822b1,0x800304086882040,0xb000882a18282a3,0xd2950b9314002848,0x8a685286254261a0,0x8851a39610b8689,0x9c0140c084117,0x1c53116c01c8698a,0x96a2824d46f4a200,0x2008403202930190,0x80009809b440a048,0x4114c91704a1255a,0x8609f4d0c0c10002]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x4081620101104200,0x602310212222100,0x10c0848002000104,0x1040400201001142,0x10020008048108,0x800104200100c1,0x880142214401040,0x8030200901432010,0x818000003202a0,0x620040002100000,0x8000103020a80120,0x24c0122021900400,0x1020840808001201,0x4000824010a004,0x420011100a442000,0x80842060518a4020]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x120240c988150a89,0x32ae1403020a4082,0xdc69c008220a0490,0x4022109032128008,0x41220c2460104200,0x845130241c412050,0x8601420034a9204,0x1016285910091418,0x210c14686305064,0x40900941c1008660,0x23ac4893b6308020,0x68491920b1010984,0x8942008420244006,0x2084620402041514,0x124230401a460aa4,0x10e6032911202400]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x32101488f04f2049,0x38890021c0851200,0xec0c7841b1024cf2,0x40a0048128008c00,0x2420092240535280,0x10208090f09428,0x441480142120b28,0x200d1cc22800500a,0xc20841868408c044,0x542800810694c0,0x63ac0a82d2402e12,0x520049821e422100,0xfd201800004c84a,0x1282404400200440,0x84aac0085031aa4,0x1158c300a2500280]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x1e1e0040788019c9,0x30640ca0c808ca86,0x2027085c90060491,0x4821828020818000,0x10e088a040304a04,0x3030a0700c307418,0x2420c000c1398524,0x7003043018380c06,0xc03820c002003006,0x8120820b1818440,0x23acc6014c119611,0x81d4092880b0122,0x94218c0040c4022,0x8a1402400821330,0x382804c8910012a5,0x932080b26040044]))
  | _ => 0

def compactPerms247 : Array (List Nat) := ([[]] : List (List Nat)).toArray

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

def samplesP223 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xa07cf0fd5d2dfa17,0x89bf978bdc72b17c,0x7c3f0271ceb81b87,0xdf3dc08ce361f39f,0xf11b60891dc25935,0x840927f6b011ca06,0x605901f8e01cdd08,0x38bb092e4e73800,0xe040c5821f186b1a,0xbf7f8efd8fb15bf6,0x5dd91738f6ec064,0xf77b7d2b0416c2ec,0x7005976d8779115,0x6363c3484a12fb24,0x438203008a070df1,0x784b900941ac4cb0]))
  | 1 => (BitVec.ofNat _ (limbs64 [0xff7fff000ff20017,0xfe43fff42002fff3,0x801fff8e0fffe407,0xffc07ff301ff081f,0xfee0007fe202fec8,0xff8000ffe3007,0xffa07e00007f200b,0xfc7403ed00003e0f,0x1871a0000009060,0x3fc9ef7f6f7ea3f9,0x3e21fc7ff283fc3f,0x297c1ff405e90707,0xf803a17901c8003e,0x83fc3c007de00003,0x8c083c710407e9c9,0xcc5c2f34a8c20244]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xdff6cc2fda53bfe8,0x10b645f97fbd475d,0x7e6837efb71ef6fb,0x1aca2cf1829edee8,0x541ea80f37d8050,0xd3b00102168f0c50,0x83e78600d28086f5,0x44c70e00f24030,0x218200020600080,0x3bfffffffadb597f,0xffbe6eeb61d11257,0x9e93e8b7fe8db083,0x6022ae804c0c1be1,0x34036a6e81ad0400,0x1c002006ff67f,0xf200d2edba08a000]))
  | 3 => (BitVec.ofNat _ (limbs64 [0xd7c70dd7a39c1c79,0xe37c7a3e9fdffcaf,0x8fd1c9f189e078fc,0x64f3b27f7de2e710,0x23c070600800327,0x27d65e3d48601049,0x1818d81f0fe320c2,0x178314103f0980c0,0x1c000010c0010000,0x7dbffbffffe5be8e,0xf3efaa0c6fbf7f99,0xc569d75bdb303530,0x13cc120eb731e402,0x408c9497b6500008,0x7000047007ffbe,0xb5b30d1254240003]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x78fb02faaecde596,0x7583e84bc382ce8c,0x73defc707f479b77,0xa03e7f0c9d9cf47f,0x8d069c701c3aa5b2,0x780ec7c94f81c5b7,0x844661e71060da0b,0xeb884b72db18390e,0x81a7146d1c966415,0x2ea55dcadccf4704,0xb9d343fc1973a3ba,0xd1869ac8e5d60cd7,0x84f3450621b66e29,0x1f9223b0720cc2d0,0x3a043ec909949705,0xa35608aac619516c]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xff89772d75635fec,0xef7c1bd6ebed19d2,0xb1a2358e70252518,0x87f793aefe2d39e3,0x1abc758de6fd1ec8,0x386028c4a120b3a8,0x9ba2e57ed1c1f34,0xec38a8c14535c701,0x2020caeb01809262,0xb3fef011f524ac39,0xc4107f94bebc6dc6,0x3eb7619ffa4a4a68,0x9bdc3cb96a4a1ada,0xc804d49901af1027,0xf48c00388781387e,0x5a0f2d20bf70f00]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x2fbcbbd2f0bee3eb,0x1ec9a425347d2223,0xcfe5ca1ff0dbcfe8,0x790dcd537e530fe4,0x60c39b720905600f,0xcff1903bf05e6ff8,0x760591a83f8361f4,0x10777c2dbacec0f0,0x5e582114e26f0d8d,0x5c5237a6339af4c3,0x4a6e9583d44c9fe9,0x6acca6643a21f918,0x6c3dc2c19681e5c4,0xbc7909678c532dd8,0x173c186707a4282,0x5aad65453550b09b]))
  | _ => 0

def samplesQ223 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x807cb400021d1a04,0x8989c9a44820100c,0x4c150010067c379c,0x4200002c61d2148b,0x1119000408403852,0x90290e3008418a06,0xea04d650200044c2,0x1008235da12080c1,0xc380309121180678,0x3f708e9c0f3152b0,0x18d8073ac004035,0x56201403052ec000,0x302ca3000319011,0x636442404a101300,0x47000344020f09e1,0x704b800900a00830]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x2019510002570a15,0x812bc9409041a46,0x440410248bcc74a5,0xe900052420b20005,0xa9a9082453426a40,0x4110c2102ac58a63,0xba080232050c4446,0x591191d5281a5241,0x28b23584011900b8,0x3f48ee6e05320158,0x2aa59039f200ec35,0x95816f505281701,0xa902815800989010,0x1ac3a4048800b11,0x843854430207c9c9,0x4c4c0f04a0c00204]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xcc328c61c2118324,0x29385061cf6c9d43,0x50ac70fd98a616ff,0x7e900eb289544e48,0xcdc511039e65b04,0x70e2a77a01232cc7,0x79450e81504200d3,0x30c8a78c46544f15,0xd816323269a24a1c,0xfafff5fffaa8497e,0xdd9fe4eb60d11013,0x9213a887b08cb503,0x7042a60244043890,0x5003d27b5b954440,0x408c8b0344cff67f,0xf20092e9ba082000]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x56d494c581048c60,0x6318d8ecd566ac47,0x16a8d1b49aea2239,0x2e3126d6b9c64e49,0x300c632a44758d3f,0x89090b1f02254c0a,0x298af24a266b914b,0x555149248d20937c,0xc89282f07a3e8220,0xfdbf7bf3ffe59696,0x22c7aa252f2b3b19,0x45614319d9a49521,0x31c826168414e002,0x5124d01f36951029,0x2b20102c6857ffbe,0xb5930c1254240002]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x8000430880c020,0x300000420400c000,0x210a408020030800,0x1a501088088050,0x21224008000,0x882004400024088,0x2208940008018,0x2480402002400814,0x40082088420002,0x4081010090c80400,0x105002840152020a,0x8000880800d00094,0x61040201062020,0x1800018210084048,0x800880808901600,0x8210002246095040]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x1b000008b4200080,0x404020080c10491,0x90a0040210000000,0x444028200046b00,0x4423489009904a9,0x2440200151103010,0x4e1080012a13900,0x40c0040050100,0x409020040202101,0x800610016004a801,0xc4004d0000ac01c0,0x208661006a000048,0x101030002e400248,0x8000841900250424,0x308600b034202016,0x1a070d009160500]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x210002100000200a,0x40000020100020,0x400a0040008000,0x800106010020,0x80220c8102080080,0x410400070901030,0x420002001842804,0x8041000000b0002,0x400804001000,0x22001,0x201100100484c0,0x288c006002010800,0x404008110000504,0x410000080420814,0x9012449010200000,0x824610401508089]))
  | _ => 0

def compactPerms223 : Array (List Nat) := ([[], [50]] : List (List Nat)).toArray

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

def samplesP183 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x7dd6fff5,0xbfd89f7ba7b878e8,0x3bfbfefe7ef85dff,0xb0f9bb83b4fff91d,0x5a1f3c06593c1271,0x837f8fbffbbf5fe4,0x8ffe1eebd439ba04,0xffb5200bd761b03b,0x107ce285f10e0679,0xf633e9f93c069493,0xc9bd98b8fb371608,0x1b44fb11425a858]))
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0x20a30000,0x1984845d8e027dc5,0xfc020482401015e0,0x9ce2038021ce85bd,0xd17e0f2e49c856fb,0xebe0090060c51145,0x8701064c14281da5,0xe73f3c02d83ff83a,0x387c2b97ffafcf01,0x50c148918304b891,0xb3ae59bc5cff17ed,0xe3be71435547fe5e])) : Bits)
  | 2 => (BitVec.ofNat _ (limbs64 [0x77b4fffb,0xf99d7cf6de0602c5,0x9bff3defdff7f7e0,0xdca3bffc6bc17c62,0x757e032a2742d48a,0x81fff7fe5cebddb,0xd5879f5d9fe65de5,0xa00a03f6f8be4810,0x29ff091202a0c87f,0xf9c2fed6bf85e9ac,0xb14e1f6d10c80005,0xe20a1f463fc15202]))
  | 4 => ~~~((BitVec.ofNat _ (limbs64 [0x10500060,0x20182e12108ca8ea,0x8000000c124061c1,0x5029b00c06a03921,0x7e275848af24f09e,0x8f66820400928888,0x119a0c89c4c6aa45,0x30b8a0f3e7a64059,0x5abf2bd672faea98,0x3610a6c21998e6ac,0xd9348cc93bcff21f,0xe2bb5b950cf8dbca])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0x7eebffee,0x7ff7e65fb9c1fda7,0xc3fed7fff7dcf5df,0xdffff07c1fae85a5,0xcde1c8e9eba87286,0x73fffcd7ef3893d,0x777965cff7ee0265,0x1739bc12c7be47f9,0xfe032346127828b0,0x5efd3edfcb78a68d,0xbaa045835fc8f01e,0x2394907c17e8b82]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x7b7bfc7f,0xffeeaf9d5eeead5a,0xe7ffef9ffb7f2be1,0x7f6e478fe7febbb9,0xb2265f5c8cc5ec18,0xe8d6fbf6ffd5f2cf,0xbb9beebc6cd8ad9b,0x60fefce12807f84e,0x5abc08906c83c35f,0x37ddc7a3d1987a70,0x5736e8dc2c0703e1,0xe08232d94cda544c]))
  | _ => 0

def samplesQ183 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x2291006,0x4106600148438411,0xc61420906600aa00,0x904404003f008287,0x2060c02d82410502,0x4c91880e03b21200,0xda06004a48201a61,0x4041201d2820002a,0xc1800c1810310ef9,0x32a8a00c008530,0x880d8029e8001610,0x3c05f3014200818]))
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0x5f5c7efd,0xf6397faafbfda27a,0x4ba37fb69fdffdbb,0x6b419edfd5ad39ca,0xffebfdd2377feb3c,0x16ca59ad6d4ffb7d,0x27afbffef54ae6bf,0x572c9afbdddf9eec,0x11f7dfe4a7ff7105,0x5ac7da99ebaffed5,0x33fffd965dfdb9a9,0xbbbd3143f54ffefe])) : Bits)
  | 2 => (BitVec.ofNat _ (limbs64 [0x84b0824,0x42e601090189b932,0x668c080260c4a888,0x1fac40515541305,0x800104ed80140f15,0xa6b84e6cc1f00858,0xd80018101c200229,0xea82485988028239,0x2f91403c10062ff5,0xe182d8c6280141a0,0xb8001c2da0501086,0x8b829f4437811002]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x10500430,0x22080602100c206a,0x1801100081840a8,0x6100880540a41000,0x160008000520601c,0x24841a144082121,0x200003200008400c,0x120c884090c28a04,0x101141c000880004,0x48815018e0060841,0x240011200500888,0x880d2042a1072420]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x1144090,0xa000188002340248,0x922402480014422,0x60001890c0a00808,0xa311000028028,0x104211812c010000,0x529200081426086,0x110c802051c81884,0x10040000a4005000,0x1a450219c3280004,0xa0400011092828,0x201d2003c04e8280]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x4842180,0x88110020a0104284,0x1861060011010446,0x40031b080024840,0x49800002300800e0,0x110630103804c004,0x80848420072182,0x110052043087180,0xc120003400002,0x164c070110803200,0x1122080040b6060,0x6410008948584044]))
  | _ => 0

def compactPerms183 : Array (List Nat) := ([[], [33, 116]] : List (List Nat)).toArray

def compactDomains183 : Array (Sig × Nat) := ([(subcube 1 0, 7), (subcube 2 0, 6), (subcube 4 0, 6), (subcube 32 0, 6), (subcube 16 0, 5), (subcube 128 0, 5), (subcube 6 0, 5), (subcube 34 0, 5), (subcube 36 0, 5), (subcube 17 0, 4), (subcube 20 0, 4), (subcube 130 0, 4)] : List (Sig × Nat)).toArray

def compactWords183 : Nat → Nat
  | 0 => (limbs64 [0x1fe7f91f,0x407fe602068ba352,0x1490a9c20ca8c89c,0xca8c9763fe1fe0,0x691fe1218d4a86d5,0x77fe056e7c4f07fe,0x753afae6840004e,0xf8f73badda7b3e73,0x8848513884e11382,0xce1b381315191312,0x19419519265e5e57,0xca1dc2bdf024bf2b,0x1dbb01d7ff00587a,0x9419d1766ffc02d8,0xa073ff03fc0b1b4e,0x92c27c30b3137fc0,0xb39bfc0ff0320961,0x217d8603bfc0ff01,0x3c0e497a8322a45e,0x33dd7fc0ff0029d0,0x318a60250520f46d,0x3684751640c820a9,0x16524e927b86962b,0x5664c3070a710879,0x3044381b162c58b,0x166bca8105ebb5aa,0x52a32a4460c1a242,0x50000014828920a,0x48721cc881861840,0x800c920425fdfdfd,0xfdfdfd7dedf7bdfd,0xdf7fbfbdfdffedef,0xbdfd7fbdffedfdfb,0xa623a61ba6126622,0x6608262026202608,0x2604432c262c2611,0xa429c3298329e629,0xa629e609e60b232b,0x262b2621232aa628,0xa128e628a62e3243,0x2c21c11a32a32221,0xa1183297417414a4,0x817a7affc0e65ff0,0x67b7fc17e2ef8e22,0xa90d5c9ff04f07b8,0xe203ff02aa20c5e0,0x3b98630a650399a1,0xee22002190865990,0x822e109d05e22c08,0x1623f2a100c63a88,0x46327d29a0846328,0x338e229903a637ff,0xfffffffffffff865,0x465065c644648434,0x43823423a21d843f])
  | _ => 0

def compactCount183 (k : Nat) : Nat := match k with
  | 8 => 1
  | 7 => 9
  | 6 => 27
  | 5 => 7
  | 4 => 2
  | _ => 0

def compactPath183 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => 0
  | 7 => readCompactBits compactWords183 (32 + 12*i) 12
  | 6 => let v := readCompactBits compactWords183 (979 + 16*i) 16
    (readCompactBits compactWords183 (871 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 5 => let v := readCompactBits compactWords183 (2918 + 14*i) 14
    (readCompactBits compactWords183 (2846 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 4 => let v := readCompactBits compactWords183 (3373 + 13*i) 13
    (readCompactBits compactWords183 (3301 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | _ => 0

def compactLive183 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => readCompactBits compactWords183 (0 + 6*i) 6
  | 7 => readCompactBits compactWords183 (140 + 7*i) 7
  | 6 => readCompactBits compactWords183 (1411 + 8*i) 8
  | 5 => readCompactBits compactWords183 (3016 + 9*i) 9
  | 4 => readCompactBits compactWords183 (3399 + 10*i) 10
  | _ => 0

def compactPoolIDs183 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let v := readCompactBits compactWords183 (26 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords183 (6 + 4*(v &&& 7)) (4*n)
    compactIDsFromBits bits 4 n
  | 7 => let v := readCompactBits compactWords183 (487 + 11*i) 11
    let n := v >>> 7
    let bits := readCompactBits compactWords183 (203 + 4*(v &&& 127)) (4*n)
    compactIDsFromBits bits 4 n
  | 6 => let v := readCompactBits compactWords183 (1765 + 7*i) 7
    let n := v >>> 5
    let bits := readCompactBits compactWords183 (1627 + 6*(v &&& 31)) (6*n)
    compactIDsFromBits bits 6 n
  | 5 => let v := readCompactBits compactWords183 (3079 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords183 (3079 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | 4 => let v := readCompactBits compactWords183 (3419 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords183 (3419 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket183 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let d := readCompactBits compactWords183 (586 + 2*(i % 6)) 2
    let off := ((i/6 + d) % 21)
    let v := readCompactBits compactWords183 (598 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 6 => let d := readCompactBits compactWords183 (1954 + 5*(i % 16)) 5
    let off := ((i/16 + d) % 58)
    let v := readCompactBits compactWords183 (2034 + 14*off) 14
    if v >>> 6 == (i/104729)%251 then [v &&& 63] else []
  | 5 => let d := readCompactBits compactWords183 (3093 + 1*(i % 4)) 1
    let off := ((i/4 + d) % 17)
    let v := readCompactBits compactWords183 (3097 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | 4 => let d := readCompactBits compactWords183 (3423 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 6)
    let v := readCompactBits compactWords183 (3425 + 10*off) 10
    if v >>> 2 == (i/104729)%251 then [v &&& 3] else []
  | _ => []

def samplesP191 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x86d1669f61ee536f,0x8bf869a5f417c55f,0xfdf4e4bc0efd379c,0x40678aeb45b9f16c,0x103dfafb4030a00,0xb68c40e81d7e88ed,0x4037001670aa0e9d,0xa18938660f8060cc,0x117a0362606c063f,0xe1f7b3fd9aef9cc0,0xd725ff1881dc73d1,0xc6ec5c7687202914,0xb091f1b90f8b731,0xb0c8b80ce271b82c,0x8c0006e84a71bb1,0x7d5882a12286a160]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x2097b961ff1621fd,0x6cc7f75406fe58c3,0x3f3d7300f9d231f6,0xaafffd547fd7550c,0x6e3070700012fc89,0x8733712faa910ef,0x88007fe999d02101,0x5e74c001fe070301,0xe200000d0180707b,0x7bfafbaf4d1d83f5,0xc7e9e9cfe73abaa,0x7d247efb5059d41a,0x63f671016c004903,0xf634432b88b007d0,0x13000f101807b13b,0xc5e47544ac300684]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xf9282e267c59be6a,0xcf3f965bfb2d2578,0xd23a7bcf10e8366b,0xff8643bfbae62ef3,0xb1468040c7ec0014,0x10a3af5d60d49912,0x77c88004461dc162,0x38e066f0188432,0x4801c908011883e,0xbdfffcbfede69f3f,0xeb9046ff01e7dd73,0x39d3887a69e6010f,0xf41ae2e400208cfc,0xf76cf0500e4000,0x401f081204fe3cd,0xfa0701e6d0454808]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x3f7edff98f8bcd90,0x7639eb65bd307ebc,0xe3cf85f79f1fc983,0xb985de7cd008201,0x4068210119fc709d,0xef5c588183016610,0x8c0202088661febc,0xb7c30f9900601800,0x46000060000bf,0xffdffff6f2b96d39,0xdbd5f8e7ff18ce3f,0x9ef5d78d9e073ee0,0x80c0807af8df50c2,0x430800d31bc00000,0x403e00004107fefe,0xb099361913700003]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x46ee695e91e5a28f,0xf3c66adbcbd7ba9f,0x1fb1abbeee2ca6f,0xb4782b13b5b90c52,0x9e931ed1aa0375e2,0xb113a0e61e800b01,0xb235fd1968d40e82,0x407537980f074308,0x6a618341580a1529,0xd76f6edae5de6a3e,0xf4cf07e061bca4ed,0xe61abb876718117b,0xc151c982fe7282d,0xcc87370f0601801b,0xa1800f508a94ce67,0xa3b26987018c90d4]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xd997d681fef9ddf2,0x90c79caa06e9a723,0x3ec28c40f72dcdf9,0x557ff6a87a6eaa8c,0x71cc6f8e40118376,0x406cc802e556e4ee,0x77c87ff6192fd061,0x5f8a0001f18080f1,0x91820c8e81f06876,0xfe81474fb21273ca,0x247b7963fe6f5354,0x7bdb613ca899ea85,0x93e86ee5530076c2,0x93b8324753e47e0,0x1e01008f14215d8e,0x807ca1a6efa2e08]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xff6991fe02367e15,0x3d3815be79cadbe4,0xcc05ff7f6117fe14,0xff81b45c825851b3,0x8ebd803e7fec8f6b,0x4f80173d002b7710,0x9ff80e3a702315e,0xa806dffe00783c06,0xc1df0303e07839d,0xe3c9d711f61f4c7,0x3baaa11f1e833c8e,0x812fa7c010e6c6e0,0x7c278106871f831c,0x3f40dcd0adc03807,0xe07ef020635a2450,0x56689c78dd095133]))
  | _ => 0

def samplesQ191 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x809148b8e2481305,0x44000001f63ae024,0x1031608c1e150008,0x4061c95480a0206c,0x304520108c030a14,0xa65010487daa1110,0xc80000122f483001,0x1b1d8010060e700,0x16061002e1820e7d,0x20f433ad88e90000,0xc735a618804452a2,0x80c0543311202804,0x313820110d84431,0xb000282cb240002c,0x10c000f0442f11b1,0x795800a022002060]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x80810a29ab0a85b9,0x28020410d22a000a,0x491d21855a531100,0x2034911422353266,0x6402903202890686,0x225532492b893448,0x400c24443b44a448,0xcc914a1544a00902,0x36d3000064912e7b,0x3872bb0d090480a5,0x4d3c928cd44221a2,0x356456db10129c02,0x2192530104484042,0xd21468288020128c,0x961425102c07b139,0x45643444a8200404]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xea834ea510499df0,0x4516b400460e283c,0xd344108f18f27000,0xb2004a7880a02a8c,0x5207942112502454,0xb7e0014d7a390100,0x90101e96746340,0x49bac120220af802,0x67061502081c6ffe,0x39afbcbb84468d16,0xc39486dc00a49933,0x21d1c8384126140b,0x601a82ad102204ca,0xf02c6992448021,0x60142e0294fe3c9,0xfa0501a690044008]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x1e0ec2cdb240d4b1,0xc673e5429c643c2c,0x71d5b0590363d022,0x3a20c9e5c9803885,0x4e023459cb21825,0x73e5826e2c0e2070,0x9c422a68c2f8b58f,0x9e5280553ee99a,0xb8043f2b78b020bf,0xdfdfcff6d0a94d29,0x51d5fa2a7910ce3a,0x9e714315db231e23,0x2100847a596e544a,0x911101c31a420300,0x41d9040441f7fefe,0xb099321113700002]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xa2a214410806002,0x90d0a24a00c40c00,0x2042107081204264,0x120000230d088401,0x3a845406040a040,0x400089a280100a03,0x492920140824202,0x440120230a003d,0x8800651108600080,0xc70944526412021a,0x1040014001b8044d,0x4202a9004e010171,0x4040c282b221808,0x103134100048011,0x4900420192904e46,0x82824103018c9080]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x8004004204000,0x8040086200410701,0x24000850210800a1,0x10a040119428500,0x8118428460249021,0x800489080048a27,0x12418921000200a4,0x2240008a10000018,0x8828a00102209000,0xc600404032107240,0x200249232a090044,0x480a20042a894020,0x8040240009003200,0x909010041124950,0x280a100792000c06,0x2ca1844da0a00]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x140100200140000,0x80084010000c0,0x60000000c10,0x480200000070102,0x80100082000c0082,0x80060100000840c,0x20d050000000020,0xa600001e00010040,0xc400000000,0x30030c0,0x280a000106032000,0xc00c000400080,0x1820000080018104,0x4008010048058c0,0xa006310200000000,0x4208c484c010111]))
  | _ => 0

def compactPerms191 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains191 : Array (Sig × Nat) := ([(subcube 8 0, 9)] : List (Sig × Nat)).toArray

def compactWords191 : Nat → Nat
  | 0 => 0x27f
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
  | 9 => let v := readCompactBits compactWords191 (8 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords191 (7 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket191 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP238 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0x5f,0x5efffffe5fbfe7bd,0x7c9f65dd9da2d7ff,0xdff6fc7ffff1aff7,0xf2e10eb77ff3f13e,0xafe85d39e121fe6f,0x4f9fa598729fe9f7,0xff9ff7a7faa4bd47,0xddbbbf9d8f78bfd9,0xebe6a299bfbe95e0,0x34c492ce78b78009,0x5123fcfdd9de6b9f,0xa7ef1d04e077aab2,0xa1817dfe2f0ddb81,0x86134964f633ba38]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x7b,0x37effbbfefdbc9fb,0xec72fa1a7e6d8bff,0xf9ff9fafff6ff533,0xff5af7cacbfdd247,0xfc32a2cf42d807b2,0xb0becf67815ffe7f,0xfff0fccb7ff947fe,0x341ff2dff1a7dae6,0x90fd5c66e0731d5c,0x822b6f3900f841f2,0xa2dc1f3e0fa67ce4,0xfb9f9fff0b8e40bd,0x50fe83894df22402,0x790fce872a5cc5c4]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x8,0xb7003000380e0d8,0xd04e62dd7c6ecc00,0x806004078020e301,0xf52006a00be04001,0x77f802fbe2b9b7ee,0x40becffff3c06010,0x1000c0037c200306,0xd013e11876008bc3,0xb1fc6006ff3a1ddc,0x342bf3dc48ffc1fb,0xf3ffe02183080d04,0x8b09160ccbf6c2b9,0xc1f863e80dffff83,0xff1c0506aa7ba7fc])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0x7e,0xf95fffe3bff07e7a,0xbbefe6e3f95307ff,0xafe97ffffdee5fc9,0xfdff8eb89f13cef9,0x5fd0423e3cd9f270,0x8e6e5ae6709ff7ff,0xf37fcb5ff6bb7a47,0xd2545f7a7e9f7fe6,0x1b0542867f406adc,0x343a9d327fb00112,0xd2d3fbefa6d9977f,0xdf17f318dff86b75,0x61469be0107de582,0x800f5c501eb5c74]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x6f,0xab8fff7df3e4b1c7,0xd37d7d1c600e63ff,0xf67fffdf9e97facd,0xffa4f9752bee2d87,0xf3cd02f0832605cd,0x40b12f98021ffff8,0x7defff337d4687b9,0xebffed3ffe47e519,0x64faa106df8c1da3,0x492bf0c4804f8009,0x1200fffff79ff04,0xfc787ee00bf1948a,0x8ef962768d801a01,0x8611bffaac60a608]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x2,0x3080382000000123,0x2831651af9030400,0x18081c071cc1,0xfac088100b138006,0x8840423c01404671,0x8ebf2ffe72818060,0x6100010372800441,0x1c1e1f880775fc,0x4ae78286ffc41de0,0x2a9c2230b7811b,0xd3f3e80c0cd07204,0xf41619100bf928b6,0x20c79bf60d7dff83,0x8e11c8e52460de7c])) : Bits)
  | _ => 0

def samplesQ238 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0x20,0xa1081000a1601042,0x14490006059202a,0x440114242024280,0xa88a230810492480,0x9114029408828104,0x2020106108114045,0xe8a80210a082422,0x88010890001228a1,0x486208400a11aa85,0x1800454060621090,0xa09140908460096,0x26d0d01a002a022,0x8214d80404ab29,0x2102482472123028]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x4,0xc810864000702404,0x3ce04a501123642,0x881003661098c30c,0xcc40828180a3020,0x40852381887894e,0x84140004ab25848,0x53902093041820a7,0xc1310444046b123,0x8c12430020c998e0,0xa003014446318c,0x22031c1a08a04884,0x6891959328070081,0x106611908c822103,0x99bca0528148484]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x8,0xb72070889826088,0xd1c642d4544ecf30,0xc10a416a8192a418,0xc5283a830a400632,0x45a8c61a2aaa9bc6,0x40c44cd5e25b9506,0x685c3055250d306b,0xe9902429b42b00a,0x4592e8a2c903409,0xd4e886400633558e,0x63415e9e44d56058,0x54c6c8d131231184,0x34439893a4a50832,0x4cbeaf145045802]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x1,0x6a4080e40878108,0x4c10091806a44815,0x23a28800a4011052,0x500010c1a424c102,0x6881a540c1081480,0xd306a518850ca022,0x80654b0030835a08,0x70a426089288424c,0x2204842bc5020008,0x4510203498198621,0x45463e4a6181269,0x8102620841b80950,0x4708aa2210314494,0x900035c001e94850]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x10,0x547041624c1b2a18,0x689202639ba09dc1,0x818680b18ca92504,0x3648032c7065358,0x280aed09441838d2,0xc64e650635ee2fb8,0x31001f1074015819,0x35b0a261b641d504,0xb30de180804c0560,0x825e90198b098f6c,0x20d0ebf67329bf00,0xbc10107003f101c0,0x5f58e80681820480,0x8e75b7da8c608600]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x7d,0xcf7ee7dbdbfeffde,0xf7cedef557feff73,0xef7e5bfffb9fef3d,0xcdfd7eaf9ede7f37,0x6fbfdeffbfbfbfde,0x7deddcd5effbfd6e,0x7bdc3af76f9f36ff,0xcf9f9effffdfbf3f,0xaedfff9ebcf9fcfb,0xf4f98fd3ceff7ddf,0x6fcfde9e6efd7adc,0xfcd7dddbfb6fb9b7,0x3cf7dfffbdef3df3,0xcddbeaf56d74defe])) : Bits)
  | _ => 0

def compactPerms238 : Array (List Nat) := ([[], [99, 113, 82]] : List (List Nat)).toArray

def compactDomains238 : Array (Sig × Nat) := ([(subcube 8 0, 5), (subcube 64 0, 5), (subcube 0 8, 5), (subcube 0 64, 5)] : List (Sig × Nat)).toArray

def compactWords238 : Nat → Nat
  | 0 => 0x834bf
  | _ => 0

def compactCount238 (k : Nat) : Nat := match k with
  | 6 => 1
  | _ => 0

def compactPath238 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | _ => 0

def compactLive238 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords238 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs238 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords238 (14 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords238 (6 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | _ => []

def compactBucket238 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP233 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xefffefff7bd5fff,0xbffbe7bfffffbf0e,0xee48ffefe9fcfcf9,0x3c7fdfc7a7c3cffc]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x4150001959018df,0xb01980008e798b04,0xe08ffec00445861,0x3edfc7a78284fc])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0xf46ff17ff8e984c,0xfffffe68e67c613,0xf80ce03ff4ff711,0xc03fe00386f2f8c0]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xf98fbe9fc7078b0,0x3fffde59f47839ec,0x1e6830c39effc8ef,0x33ae158021fe0730]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x20a0200622c582c,0x302246000466340a,0xe48fec08808a499,0x302f0583a7424bf0])) : Bits)
  | _ => 0

def samplesQ233 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x100810010022000,0x108402104008101,0x30000081800c08,0x60444042010a64]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x41511449490125a,0xa982911427409147,0x4522a4a2cdaa2294,0x9904055152696b02]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xb92078a0d543a3,0x7e24a206b20b1c78,0x760b07d7704f9031,0xd197221985f2f080]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x67421e059cc70d,0xc2c1864671e10e1e,0x11c70ecf1e34d070,0xf38e01841dfe0510]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0xdf5f5dddddbb6fb,0xebaff575ef55fddf,0xdd3eadbaddaeaedd,0xbb7d6d73776b6bf6])) : Bits)
  | _ => 0

def compactPerms233 : Array (List Nat) := ([[], [101]] : List (List Nat)).toArray

def compactDomains233 : Array (Sig × Nat) := ([(subcube 32 0, 4)] : List (Sig × Nat)).toArray

def compactWords233 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount233 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath233 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive233 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords233 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs233 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords233 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords233 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket233 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP237 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xf6bfffbdffdf,0x7dafcf9dbea49eee,0xf6ffffbf3fcffdfe,0x7e3fefe7e1ff60ff,0x7bc58fb0fee7e9c0,0xd5d1ecd86fe32c3f,0xc7dfff9fb1ff4e0f,0xef0cfd3f4e1fbf97,0xc764e7828ffbef66,0xc31c1f3d3f060c7,0xf64a0f7f9bde4792,0x9fee3f0ad05e4ce1,0x70b1cfbf19877708,0xf2267929cd835978]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xdfb57fff7f6e,0xf7759b3a7e4aa91d,0x3d3ff6ffeeffbfe1,0xb954af7c5bd9bf76,0xef5f705ba90b6a9f,0x5aa61597901c92bf,0xff3fb67ffbf2fdbb,0x1bf0eeebdbe25d7d,0x3b7b196d7507229c,0xa6ce6e1901958438,0xb570a7fc5be6fd,0x679f39f5a5a5885e,0xd85f3469b4788817,0x819a9f8769ca684]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x4192c000184c,0xa80d90bc160a9c7f,0xbfc0049c00840402,0x3c00ae38424f2032,0x3c0bdd0fb0bea9b,0xdde00ddfafffbe80,0x8004040910e18e00,0x72004c4b42e21591,0x1b6be90af7abe33e,0xed64a51d1d5e4ff,0xf6ff7fc2004280b0,0xa3240a83c5bc8c4a,0xd05fc7eb18ffff1f,0xfa3f40896e992ffc])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0xfb5ebfc6ffff,0x9ecff0efcf393070,0xf8bffffffffcf61f,0x7fc1f9f9fe3f830f,0x83f9ffc0e0f8fe0f,0x71e0f0d8e5c003f,0xffec5dfffe1f8ff0,0xf00f3fdfefe7cff8,0x3838f803f07ff078,0xfc1fe03fc0080e1,0xe033703affe79bfd,0xe6f3c68f1fa78f06,0x80c1f3c61e384811,0x7824f699197aa984]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xfde23ffb9bfd,0xe83bf4f671c2549f,0x3ffdfefdb74ffa,0xd7ebbe9a0fc6fef9,0x17e6b45457030178,0xfd600863e0800c3f,0xfaf7fffd55e5f6cf,0xf6fb59cb71fc33eb,0xc7c7401af2a04d07,0x52f60854d2ec2006,0x640045ffe6db8f3,0xf97cfff045f874e8,0x574e8bd940c23500,0x202dfd766117060]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x102400800300,0x5423c0026820309c,0x708010222c000000,0x5341a9c00990824d,0x3450650e4e3694c,0x57160c01cedc0c03,0x420010143116448b,0x8008398b49040b68,0x27745003f0776c44,0x6e1ec13d2a0a0e7,0xe67374409a4d02d1,0x44da350c15e74ce4,0x50c1bbdd143a7d11,0x7a26b9195512f9e4])) : Bits)
  | _ => 0

def samplesQ237 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x94001420050,0x821020a041124010,0x804488210880a02,0x908100004a202280,0x8082444000108228,0x8a08012210100308,0x4418280520084a84,0x2088a0014062101,0x418410908208082,0x8085842008ac400,0x883042412100582,0x60e0100d0044050,0xa18c080d024601,0x84052828c0824148]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x204aa0020499,0x808c40c501b15242,0x8282621031a48303,0xc4019095062842a2,0x10014c2058809108,0xa0590f2608c2214e,0xe32a22011498898c,0x680622890840744,0x16ae0c190c244200,0xa09084b2240d021,0xd860c651c086491,0x22972944a4000812,0x48c928394540c511,0x8911a96856842204]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x4192c45048cc,0xa885128c130a1c7b,0x2fe7022493862250,0x5898b019c88a6834,0xa19294a2ca0aa019,0xc4f8472f2d9b8aaf,0x359319461d0aa8a5,0xae22621191350b04,0x939377222401848a,0xc291d0816a89c2a4,0x4bae2475df15530b,0x54c9b06c88c22235,0xac11919c5522250,0x2594bd749146d002]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x4a1481d0900,0x252007102244858d,0x578104504007460,0x84a426200d20d41,0x2d401097032428c1,0x502270504120dc30,0xc45472c0260471,0x303405814821c098,0xe000202430992548,0x552206b450142308,0x7240b19ae1e3824c,0x8060c48300ab0720,0x830251c412190862,0x3022569109788880]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x21dd0856405,0x34e40b04862dab20,0xf3c9a30c0d1430e1,0x61468aea4518156,0x141d81ab4a606c43,0x5076e694066d70f5,0x9a21c79854628033,0x64707103e061823e,0xe9651a92810c4360,0xa5f0821c0c640b38,0xe344735bec6cb870,0x79301e3601ba03a0,0x9f4613914040b908,0x8ead7d726113020]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0xefdbfd77deff,0xbbdd7efdf7ffdf7b,0xafef7bffbbbeefd7,0xfdb9f5bfdffe7bfe,0xf7b3fdfedbdef7bb,0xeefddfef7dfbfbef,0xf7bb7f577ddeefef,0xfeeefebbbdf76fe7,0xb7bfff7b6e6fdfdf,0xcfbdfbdfebcffeb5,0xdfafeef5df7df7db,0x76ffbd6dfdd76ef7,0x5eedff7ddf76efd5,0xefb7bd7dd7d6fbee])) : Bits)
  | _ => 0

def compactPerms237 : Array (List Nat) := ([[], [99, 82, 112]] : List (List Nat)).toArray

def compactDomains237 : Array (Sig × Nat) := ([(subcube 4 0, 5), (subcube 8 0, 5), (subcube 32 0, 5), (subcube 0 8, 5), (subcube 1 64, 4), (subcube 128 8, 4)] : List (Sig × Nat)).toArray

def compactWords237 : Nat → Nat
  | 0 => 0x3066a13f
  | _ => 0

def compactCount237 (k : Nat) : Nat := match k with
  | 6 => 1
  | _ => 0

def compactPath237 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | _ => 0

def compactLive237 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords237 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs237 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords237 (24 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords237 (6 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | _ => []

def compactBucket237 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP231 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x775ffff7,0xffaef676ee1eb42e,0xe9fffffcfbe5fdf3,0xa6f1ff3ffe7c87bf,0x83376037bea34223,0xcea4b0c7fcf7effc,0xffc6e7fc0dc3bb5e,0x6ffd0e1cc5e38f1c,0x4f1f317dc0073cf1,0x1a5bf206817a7e6f,0x1ca7eb5692342d1c,0x758f5d15ce70e089,0xe3abaf944232296]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x7d75fffa,0xcfff7c9c3f675f43,0x227ff6e77ffefe7c,0x391eb7a7d3df7b7d,0xac0aa5c90f8e7d8c,0x3bc845186fff7def,0x753ddcf9fe77e5f4,0x7713fbcb6b9120e7,0xb4b3c8a4d258eb08,0xe00009503adfdcfd,0xbb3ab6e72e0bb2cd,0x2e09b0eb3c0b1576,0x841b64a9bd9068]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x202c0100,0x8822024435569f26,0x2b400224400030a5,0x30109704baa80239,0xf0e64ad0f8f5b2a,0x8e84f5df80006484,0x50685646003c144,0x71314f4941e38dfd,0x561790b4d24afd41,0xfa5bfb56bb919075,0x288060129e3ab40d,0x2c0fbc714e7bf5ff,0xebea171813bb2fe])) : Bits)
  | 5 => ~~~((BitVec.ofNat _ (limbs64 [0x4500062,0xb4418ce006507,0xe400340000408440,0x1e0b818d0506345,0xa032d9f130b2714f,0xcbc8726e80450160,0x16c5a4190c742414,0x940bd46d952f07,0xc4ac09252c5f2bf6,0xfde1ba17c3404c89,0x9801bb613231832d,0x57f9f10d3274659f,0xe8d7ca6afc879c9e])) : Bits)
  | 6 => (BitVec.ofNat _ (limbs64 [0x7ebafdef,0xbbfbc37df5f1c194,0xe73fffffd7dbb5e5,0x53fe9adcb8f177fb,0x7c7a5ebd0033717e,0x8518400ef35ff7ff,0xf6ffb76f6d3d5fed,0xd0b445446895fdf1,0x526489272ecf3d46,0xf8403a10027db59b,0xefc1fbbb13fa8525,0x577cae603200259e,0x96ad1af307d098]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x6fecff7f,0xfc730fcbdfde2f27,0x1c3fff3fec7ffe8f,0xfde1fd58ffaaea45,0xfb84d9e071dc9b4b,0xcac032607fedfff7,0x8fc7ad17f2fee417,0xb9ff8bf1156e0f0f,0xc48c16903d7ac3f6,0x5a18007c177cbf5,0xf8dd7d78fc31d22b,0x88f3f11d42744001,0xe84167639cda8c06]))
  | _ => 0

def samplesQ231 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x8a08008,0x2030084910c10910,0x16088120d006048c,0x5000ac0002a1242,0x4c8228411098c8,0x501030820940c48,0x8d00750803012408,0x4904041a10960010,0x7480281110820300,0x242042c007ca4406,0x1824880710042314,0x210c50074000d090,0x18225aa804210282]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x28a1001,0x3910814280d080bc,0x952c0082e0422124,0xd4450c9288320052,0x10a4122c20008a5a,0x4232285aae5440a,0x590134504202048c,0x440225120d320440,0x50c2a2459904a125,0x3025420105cb4845,0xa3296630a008298,0x2308004f08225954,0x40621a6428b18048]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x5fd3bef7,0xe3ddfdbfde3b64d9,0xf5fb1fef3dedbe46,0xa6fef9ab3f776dfe,0xfdfbb9d7f7f57697,0xf3ff5ea64dcce79f,0x34dfcb7f75dfebe6,0xbfbfbe776a72ffee,0xd9b737af7e795dbb,0x5fcf9dfbda35f3f5,0x69b9f05afefef5ed,0x9eb7fe78dffb7733,0xe6bba5738b7bbbfe])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0x4500832,0x89141046006401,0x6012044108811800,0x22510910042988,0xa01208c092a06000,0xd0c850224500a281,0x2048822230848260,0x229924002003128,0x8105000844294c12,0x48829808c834b330,0x1884008c4520440,0x8812262084910222,0x2208a51103482120]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x1452192,0x440030900a0a3643,0x8c3540c01880a51,0xa10610c56858901,0x2100014286644001,0x728c9c70510a13b4,0x20dc800414140b40,0x900940e5c209a20d,0x22c500a42314842,0x418a102a98343198,0xe541619080fa0000,0x9c30ac001004222b,0x18da512d3065010]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x101304a1,0x41845034022040c8,0xe1f10e0004a08a40,0x827630030e112098,0x9401205182214404,0x509e4c864c48e117,0x4a8801104c4242,0x2099322548209764,0x812312060e180430,0x42c21518883582e1,0x60993058a0525021,0x8891241002b32101,0x62812543885a8804]))
  | _ => 0

def compactPerms231 : Array (List Nat) := ([[], [33, 118], [97, 114, 80], [113, 98, 80]] : List (List Nat)).toArray

def compactDomains231 : Array (Sig × Nat) := ([(subcube 1 0, 5), (subcube 32 0, 5)] : List (Sig × Nat)).toArray

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

def samplesP235 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x77bf7f,0xbffff57ecdcdcd7f,0x4dee6bdffff9f9bb,0xfffedff1f7fdcff5,0x87d7c3e60e847e37,0x7241e39c3f5de507,0xffcffffc3f9a7ee3,0x3e3e0fe37ff1f8fe,0xfa0af37170bab1ff,0xb8071c45f078c863,0xffe90307cce3e0f9,0xc3d3f9fb39c5e09f,0x30770ea647f07020,0x78cff847884e9b2c]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x7ded7f,0xfcb7ffaf96c3feef,0xb630e4eff9dfffff,0x7ed103af5fde7d5f,0x79be4bfdf11fc84d,0x63febe63c3821a70,0x1ffcf6e7ffffd7d7,0xd9e2d9fc735e1fb1,0xf7ff0cce8f47403b,0x40d7a79a4b922600,0x163cf9ff177cbf,0xbe3e7994c83a7507,0xc8c9fd59ae0f8fc0,0x8600d1e474f364d0]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x207440,0x7141840c23c37,0x3da2e7f00058c000,0x60103a0178642e5,0x808083e2f69c584f,0x63d7fba03747ff77,0xe000622010181c23,0x6c001e472161860,0xfa5af4717f4ad03f,0x28d70f9a40fa0e63,0xffff3ff9030264a3,0x100c033c8fa6187,0x40c76eba47ffffe0,0xfecf2146c0f70ffc])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0x7b57bf,0xc77fff5779f2379e,0x2a438befffffffde,0xb72fe3ae9c5ff2be,0x8e59b7fafe184f8a,0xe38f45830c638266,0x1f376bffffe3ab2b,0xe6dd27fffd5f9f51,0x8831f0b10ff87e3b,0xa0d047e04bed2803,0x9c0630e7fbeaffde,0xbd23867af63c75e0,0x88e12be560f8880,0x388aaf828bf86ac0]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x7e7abf,0xfbcffef86efe3af0,0x918cf70fffffd7e5,0xcff17cde3fa21fe3,0xf7e1bfe7f0fc3047,0x1c31f8e0b09e1811,0xfdfbfffff47c7c7f,0x3fd9f6dcf2ae62ef,0x1dce4c157f41c1c4,0x1f2f199a047a5660,0x61700c1ff79e9f27,0x43fdd6f109fb8a9b,0xc744e2f981403740,0x86456fba44879530]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x100b00,0x8000e0660cc002c8,0x824cebc001811180,0x408e1c581d12,0x75103e4181c6e07,0x7229e4c3889b9a77,0xe10000c424226243,0x381806d871480291,0x1daf48950ff161fb,0x900715c04b786e63,0xfd763cf8c082981c,0x823310d8393df49b,0x884c92fd864fbfc0,0xbecfc8a20ccafff0])) : Bits)
  | _ => 0

def samplesQ235 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x84081,0x4008120142303080,0x10019020a6181042,0x801a08028005009,0x8029800101980180,0xd801c8080400290,0x60c8304041a0160,0x11808c00c007a00,0x180540640004f000,0x580002204002b180,0x810130188c8100c1,0xc01211153001e003,0x3c0c4040404860,0x186d005004a8304]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x21290,0x14a424061181010,0x949130a830c2060,0x407894429100128,0x8221154040c800a2,0x480098028704087,0x46c84286890c0182,0x188015007002e80,0x288410202524e692,0x126302092202a8c0,0x830190088e0050b1,0xaa1c29149802b005,0x8018055004254b4a,0x84d06430634090]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x207444,0x5123141840929423,0x39a2c6bc32094451,0x21442da111035481,0x229a91936289508c,0x24938aa804477355,0x95a691d30e094310,0xab294042248b2a14,0x310966d6062014d8,0x4b528969c024148a,0xc94d184cecd19a58,0x72ab348c1514a849,0x2a1894c0a046222c,0x1522dcb12e08f002]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x4a848,0x1c81208a8404c843,0xc494641540824880,0xb250043280ac04d0,0x394248a022259250,0x3262a02d51883c08,0xb803286162e02609,0xca44522830438146,0x836028029258004d,0x8118540295b8062c,0xcf04167716a2c0c,0x15018642405c04e8,0x38230ac92128085,0x98092f828b902840]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x18560,0x84b0040e1401c106,0x663208d05820c184,0x30d04001d4278056,0x990081e06039600,0xf206a03f03818568,0x19301c3830601600,0xde00d600f007800f,0x807a0f91000b0004,0xa000fdc00495461c,0x1c6003e7701e8706,0xe0c0e200fc0078,0x7c072a180003080,0xc6392f9a44841420]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x6ff4fd,0x77af9fddf3bfbdf7,0x7db3d6bcf7bffd77,0xafcdbfa9bb677ed9,0xefbfbb93e7ff55fe,0xedf79fbafe7f77dd,0x97ae9bf72e5f73fb,0xbffdcdfaefcf7fdd,0x7d6deefe4eacfdfc,0xdfd6df7dccf6bdfa,0xdbddfadcecdb9edd,0xf2bbb5ddfdb7fcdf,0xae7edfddf6ce6efc,0xb5efdcb72ecafff6])) : Bits)
  | _ => 0

def compactPerms235 : Array (List Nat) := ([[], [101]] : List (List Nat)).toArray

def compactDomains235 : Array (Sig × Nat) := ([(subcube 2 0, 5)] : List (Sig × Nat)).toArray

def compactWords235 : Nat → Nat
  | 0 => 0x13f
  | _ => 0

def compactCount235 (k : Nat) : Nat := match k with
  | 5 => 1
  | _ => 0

def compactPath235 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => 0
  | _ => 0

def compactLive235 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => readCompactBits compactWords235 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs235 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let v := readCompactBits compactWords235 (7 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords235 (6 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket235 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP207 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x6f3ee3f7fffb,0xbaffc90cf677501b,0x5f6114ffffe779bb,0xfffef923fe0feb7f,0x71e3f87dc6fc4720,0xe0ffc1c61a1e07bc,0x2cfc44c27eefffcf,0xfefc7c7ce73fe1f1,0xf8f87e2fce1f5f87,0xda39c7833f21b038,0x3838c01f47f00c0c,0xd3471ff7de7e93a7,0x371afff3032c30ce,0x79799e7188377161,0x2108cf9c72046c6c]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x77d4a7f8edff,0xff1ecfef3b981963,0xa486213ffffffffc,0xce3f7f3c1ff1fc8f,0x81fc1f81f8ffb83f,0x70c0607e3e0783f,0xb0008b007fff71f3,0xbfffff8f07c3fe01,0xff1f9fcff3e3e3f8,0xfc1f803c0fe3fc3,0xc03f03e078031001,0x18675fff9f5cff,0xd9ef3c7c1c33c30f,0x8181e78e0fc00e82,0x1810fe5645dab210]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x7eb313ff7eed,0xed65f2794ee9a08c,0x838a583ffbfddfef,0x3bd79dcca5b69ff2,0xdfae65ee1f72d243,0x5b50c8889443aa81,0xc3011024ff9bdf3e,0xfffff373f8357bbe,0x6aefe7f6b3a4b411,0xd1ee116c091943cc,0xd140bd24b1a42072,0x48087fff26fff5e,0xc89dcb9feec30370,0x2c9e0855d3488000,0xc207f3f81aaf8180]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x2b0f4000c09,0x805cc36c06b139fb,0x97ab5dc003801088,0x206190c0436e916,0x11e06988c8781b23,0xcb7ccaceffc2bbbd,0xe4fddfe680031000,0x8c103c3521016220,0x682b8646c20467b1,0xdbefd90b0f3db3c8,0xd838cde679e73c7f,0xd7dff900020e502f,0x1b48940f27435e,0xa99fae558b5fffe3,0xfb1f02145eaef3fc])) : Bits)
  | 6 => (BitVec.ofNat _ (limbs64 [0x7bebdfff9f7f,0xdcfafff78df7bff0,0xbb79c1bfffbfb6df,0xffefbfff40fe65fd,0x7ff3fb9aeb9f8b88,0xaa7f7bfe6da0f94b,0xfc508bc27f77ffff,0xdd779dfdfbfeeeee,0xed2788d1fedd6cee,0xffdef819464685f1,0xfeb8ccc64adf140d,0x511a6ff96da77079,0x7f7bdbafe92cfdd7,0xab9770baa35a3fa2,0x19185be39eb0fe70]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x200200000060,0x822c80108401000,0xab40018008250000,0x8003d20008004e9,0x41a2100002968208,0x225f41860020680b,0xb8508bc202004102,0x10641148c236e880,0xe8040881b28100ce,0xdfd8f001404205f1,0xf03880044293140d,0x511a6a5144271050,0x59089b2b0828b1c7,0x299150ba83423fa2,0x19185bc21290ae70])) : Bits)
  | _ => 0

def samplesQ207 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x10c11c48100a,0x4480357209892ee4,0xa0954b1444229144,0x3406a4d004b91180,0xd0418608cd11212b,0x16207548e002d449,0xd312d338d50da10d,0x1c846d02e30874a0,0x80d00ef8809a8487,0x408d10a7081b606,0xe800b2023c88d842,0x654277959e560387,0x610cd0431b003266,0x711e91082241c0,0x2409cf1870042844]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x82b5a031720,0x40c910328443c2b4,0x1b59daf815408058,0x18a3c451401a3135,0x46a292ae6c20c381,0x1ca1d192248b9710,0x99b371ca9d675137,0x2788148365132c84,0xa44133ea4089812b,0x4e970241289de10,0x6298964d5c255522,0xc160b75e8e0b0da3,0xd16d2c5d1871520b,0xb1038d0901468e,0x4208ee5641ca3010]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x14cec280393,0x12dc0996218657e2,0x7465a7ca670634e4,0x1b0f2f810718296,0x2003d41af0884c38,0xd62305f78dd8967a,0x70786f1bef98180f,0x4d5e2322213a10ec,0xe623787fa2c23036,0xa03de41938457d09,0xc0043306f2471b23,0x3d861dfbf42fb3ce,0xc8844a878ad38320,0x24151079ab288122,0x2295f3f812a78080]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x2b0f5024419,0x864c932c01b33bbb,0x82ab1dc71912f086,0x90b21a5d9c90a020,0xb4c8e8a841b11d29,0x42495ed3beca2258,0xe5ddc9acf9c0eca5,0x34636548509a3565,0x26653a938b4ab182,0xe88e4f2258491596,0x4b16534812896929,0x6ed22eef7d5289d2,0x74c4b329d2599922,0x442052b8e52a2448,0x14c4fdeb21110c02]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x41420106080,0x9b04000452000009,0x44022401a0812280,0x580924aa400e02,0xc2810120c0c44,0x4100000108440084,0x20040405221006c0,0xc031801400048042,0xb20800112403810,0x5a120a91012600c9,0x143402080500091,0x881082061a07018,0xe1201a060048180,0xf022022a048b021,0x187210a18e30c620]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x5ffdff7edfdf,0xf7ddbffeffffffff,0xf6ffffdf7ff7f7fe,0xbdfffeff9dfdf3fe,0xfddbfffbfdfb7fff,0xdfebffffffdff7ff,0xffffffbfffddfdaf,0x7dff7ffff7bffdef,0xeff7fffffbdbbff7,0xedbfff7bfcddffbf,0xff36fbdeffcffffb,0xfff7ffffff7fbbdf,0xfdccfbefdbfffbef,0x6ff77fffef6eedfa,0xb7ddfffb73b7aef6])) : Bits)
  | _ => 0

def compactPerms207 : Array (List Nat) := ([[], [50]] : List (List Nat)).toArray

def compactDomains207 : Array (Sig × Nat) := ([(subcube 2 0, 5)] : List (Sig × Nat)).toArray

def compactWords207 : Nat → Nat
  | 0 => 0x13f
  | _ => 0

def compactCount207 (k : Nat) : Nat := match k with
  | 5 => 1
  | _ => 0

def compactPath207 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => 0
  | _ => 0

def compactLive207 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => readCompactBits compactWords207 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs207 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let v := readCompactBits compactWords207 (7 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords207 (6 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket207 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP175 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x5f,0xea8ffffb3bf3988b,0x4fdde423bc80e17f,0xfb3fdfffe7e78ffc,0x3f7f1fbd0b0fe1f9,0xc9878bc1b8f20043,0x7806f613a410d1ff,0xff0fef5ffe33b873,0xac7e77df5ffc78e8,0x75c2fc0c1ce11fa1,0xdc068c07e1c78423,0x56894105effff677,0xf109b87be8862188,0x677b969a3871c188,0x1e4b7bf25088918]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x77,0xf1fddfffc70ffb6,0xf203e2d64028343f,0xffeff33cfbfc70fb,0xccf81fc3f3e19fdf,0xc66a7a10403f393e,0x9d16820084301ff,0xbdf3fff3e53c7fa3,0xf3d3d1f6b1baff5f,0xd4f18049631e6645,0xda3990a09e187800,0x60c337ff4cf9c,0xf9fe779bf5190df5,0xa2848f64a2b03e50,0x3ee69a2b3060]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x7d,0xb64ffeedffbf23d7,0x3c6e01187137c8bf,0xf7f9fcf77ef8770f,0xf785fda67c7ef62d,0xfa3cb46211c0c7d4,0x16ea0ccc51a423ef,0xf7fefffc3fc35edd,0xbf8dbf26e9c7e4b7,0xab1e07b2850fe924,0x25c46738005bb8c4,0xa87082c9ff7579ea,0x3e0fdfe4f3e03e0f,0xd80a70e7d40e0020,0x3e097b78c3344684]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x4,0x8ed01c0900302b83,0x1649a3f375b1fdc0,0x100c00460c037ec,0x6211f847b408009,0xc33fba4259feb1df,0x18ca7e1ffdf7f20d,0x400600006101891,0xa180b1c601cc7827,0xf7d6f40c050f6fa5,0xddfe9430885bbce7,0xfeffcffe00146610,0x300e9080e3982f9d,0xea0b96eeb83ffff8,0x3fedc22ea33b0ffc])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0x6f,0xfdffffffc7fcef7d,0x9ffddbf5bfd735bf,0xfdd6effffffbffe4,0x737ffffdffd19e1e,0x379d8bee7f3cfebd,0x89e9973cd863d1fd,0x7ffff9afdaffbfdf,0xc3a3a9e92e7d7faf,0xaafd704683e079bb,0xddfe9f589fe07c43,0x58b78e3bf8ba2e1b,0xc7ffbbe67a1ef3f9,0xdac768789d3e3f70,0x22e49748e4dbf9e4]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x1,0x200000e000308014,0x8044014b8062580,0x1000003002204000,0x715c1da10001961c,0x8c8be030304e34,0x9e1843cd863d000,0x3102890018233e43,0x8203012028306489,0xa8f9004283e07921,0xdc048f0897c07c43,0x58b78e3a6820080a,0xc1093b62780631e9,0xd2c66870943e3f70,0x22e49748c408f9e4])) : Bits)
  | _ => 0

def samplesQ175 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x20,0x1570a00ac40c4b64,0x905219dc02bb1e94,0x2d4120c86520780c,0x4885021a8b708834,0x344b345c290d07a8,0x98ed02e0da372f71,0xc90de1603e30d952,0x100fc90676041c50,0x21dd040e9a117684,0x260274c0819c4364,0x61c1cc0fadf5807d,0x3109a46364862186,0x42761602ac4001c8,0x314f7bb01088108]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x8,0xf0e82b4081860169,0x8f88d69bbd68be2,0xa6448061b5459944,0x12b46929adc44424,0x9c1114f532949289,0x3467a74ee33dd7d9,0x25a736728a116d66,0xe0858292f2a04a15,0x397291248a55b24e,0x9454b1924c8d5508,0xec80669f77b445bc,0x99ac16bbb43304c5,0x62142b26a02094f2,0x880c3ee69a2a2040]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x2,0x49b0431304008c60,0xd1999fc70cc8276c,0x19c0300385c43010,0x4e22003d0fa1001a,0x3f0b45903e31b188,0xe92f6030a47b1ee2,0x860f79b00713e05f,0xd1828f3071800460,0x2ae688429f01e640,0x7e8b009f80078,0xb1c1033ffb50586c,0x3800dce670e10c0e,0x4a4268e2a4400130,0x230b7b78c1240204]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x4,0x8ed20c1951242902,0x96c8ab7265a1fddb,0xd202a41a2515279,0x14034e0e3917888a,0x962e18c65a159352,0xb84a327b9df1a7a2,0x7ac5acab2c89a914,0xdac70b1a02820cd8,0x32492dc8cf452388,0xe2992de380e819ea,0xc16d4611dee9992f,0xd4c16f362ca38482,0x14d62a210644180b,0x2053bdd15484f002]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x10,0x204042018011080,0x2000200040004001,0x4012401008000221,0x81080480100222c0,0x4000000080420000,0x210080100800004,0x1050000d40000200,0x20204008112102,0x8400209060220120,0x4888000922008800,0x2001040000a2202,0x4652010002081020,0x8001001011164a01,0x4460000024d158a0]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x7e,0xdffeff9ff76fffef,0xfffbbfff6ffbffff,0x3ff7fafbfff77eff,0x7ee7de7fffff99bf,0xbf7f7dffffffb7fb,0xfffffffbffffbff3,0xffcffdfb3fbbff7f,0xfbefeffeffb77ffe,0x7bffefcfdfddffdd,0xe7bffff799fe7ffe,0xffedfffffffdd97f,0xfdc9fff77effbdef,0xfef77ff7bf7d39ff,0x33dffffbd5acfbee])) : Bits)
  | _ => 0

def compactPerms175 : Array (List Nat) := ([[], [32], [49, 117], [49, 32, 117]] : List (List Nat)).toArray

def compactDomains175 : Array (Sig × Nat) := ([(subcube 1 0, 5)] : List (Sig × Nat)).toArray

def compactWords175 : Nat → Nat
  | 0 => 0x13f
  | _ => 0

def compactCount175 (k : Nat) : Nat := match k with
  | 5 => 1
  | _ => 0

def compactPath175 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => 0
  | _ => 0

def compactLive175 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => readCompactBits compactWords175 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs175 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let v := readCompactBits compactWords175 (7 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords175 (6 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket175 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP239 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x7fe3fc8f800efc0,0xb8fc837c1fe8b2bf,0xf80fc791fc3fa27e,0x10f900fe464387f0,0x3c01e083f4179030,0xfe803fd9a07003f0,0x1e8160017f80fe83,0xfc0401c0c3baee46,0x2801d006ffeedfc5,0xe71af8ff49843bd1,0x4f0c0938e3f663f1,0xef3b844c3816503c,0x1870f0bc14f0f831,0xd5c30c380f0f03c0,0x8c021e0c53757f11,0x4c78a12045918a58]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x911fefb5023ed3f6,0x578638fffb151be3,0xd58b78e67bd86141,0xffb39e0d3af44e8b,0x40494b180be877c7,0x312d469e5a00d19c,0x44988532844f1268,0x2b3c20000010011,0x41a407d9ee59fdcf,0xdedf253e87df0e3b,0x7ecbfa275f1a9cf0,0x9dc3c290cc01a78e,0xa50675120e08494f,0xa83cf122f600dc2d,0x700c00c0207f2c89,0x96445cc35aac41a0]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x2e780b33dff11350,0xaf5f7fc243bfad53,0x6ff002ea66255fa8,0xcb446932653eb806,0x8b96146c92000e6e,0x488f41230fa20a22,0xb16639ce10a02060,0xd4f80c043c4400a8,0x905a2820fe7f76f5,0x7df828cefe27356e,0x8df096e3b1d9ff29,0x71df79bb01684e40,0x152f8a6503378690,0x3704f54d0f02012,0x11e1100cfab59f,0x680f2a65a2423404]))
  | 3 => (BitVec.ofNat _ (limbs64 [0xffe1f4b4efc9ecbf,0xf4e3c303dc566c3c,0x878ea57f83fa5cf7,0xa006c4c19181400d,0x37ee1f1308156888,0x8170b820d04f2c0d,0x49415e096376c117,0xb00303b00001100,0x6000000fdfb7fff,0xaff2d7d1aa73f7ad,0x60ff6e9cde695bdf,0xce987f0336901933,0xc2d80c8bf0c807a6,0x2882b2c728000000,0x3e00023807f9bfa,0x73911598245d0003]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x691fd04a023e3c09,0x1779c47fe4eadbdc,0x2a7b7f187be79ec1,0xff4c610d3d084974,0x8048b4e40bff8807,0xced2869fa580d263,0xa499facc044fed94,0x2b40400e23e0829,0x71da07e1d9d59b3a,0xf1fdda2173d8cdc5,0xf13bf5e7a3651f0e,0x9227c560f3e9f84e,0xba868a521908b686,0x563f011d0670de32,0x60102f084224f2e4,0xb825811edc4e8d84]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xd6e637df75cf6b6f,0x4932fc99a8add7c0,0xf7f5bca5848bbd9f,0x241a96d2c2f5b2cb,0x403062ec65ea2191,0x22778441a7d2592,0xba2e807098901e89,0x694bc2c001814652,0x24801aa7afeb7b,0x7be78f67b47cc07e,0xb3449fdc4cb7e067,0x76fcb884097fa1b1,0x49713524e7276168,0x5eccb480d18400cd,0x940c00c43113c77e,0xb3aa6a8603b34260]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xf881c86fbdf794bf,0xea8d3fa43753642f,0x1874db5f9d54e33e,0x58a13b20880a3530,0xffb78913f400d778,0x35588160659ffc4d,0x437607b7eb39017e,0xb548393f1c40b184,0x8e01780473b6a4be,0x9e2d77985dabfa92,0x9eb7615b3c8ea49e,0x29643a7fc68606c1,0x668943c9e8d71859,0xa1014aeb298b2100,0xbe3d0338cc84867,0xc5d2d679b920301b]))
  | _ => 0

def samplesQ239 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x180032450006800,0xb69100580b052c2c,0x600106219a914008,0x5800ec2188c2c2,0x811960308024037,0xb42800214a500040,0x115026400c00c06a,0x4300370402405882,0x3980803df6605c44,0xe61aa09600003ec0,0xe4c0020e2186340,0x881b828c3000403c,0x428b01010e8e031,0x8840092c08040320,0x9800302812f53d01,0x4858002044900a08]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x30d291441144920,0x2600112911152925,0x30090020c9884801,0x426c14652096849a,0x104840128a4423b,0x913a921502c46290,0x14540c90520c502a,0x126512901244c802,0xcc0222dee586c84,0xc29e200a81431e11,0x6cac8224d1895b0,0x89c9c2819c000296,0x404d41002684204,0xa818c92044024935,0x51488018107d2c89,0x6441c4150a80120]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x799202075384330,0x1b41334218832c23,0xe44104a402171921,0x844438dd840ba688,0xa07054038a02292e,0x332601061a00024a,0x54105c01828f161,0x2043073030611d82,0xa0418627fa7b70c5,0x6daa004e8a243662,0xdc0864031492729,0xb05b618b05000700,0x150882311124c624,0x1f08da4c8802210,0xc418311228fab59b,0x480d2a2122021004]))
  | 3 => (BitVec.ofNat _ (limbs64 [0xa2a9b1acb358893a,0x3d4311485d0e0605,0xc2942dc48ab34965,0x8070a0568310f0e4,0x79c927218ac42222,0x1c351aa04317508e,0x82496f1064006531,0x41319d12b30953a5,0xa8e8828afd3b3fe9,0xaff2c4932a5297a9,0x44670c949a6859cd,0xc489370916309315,0x3181883514883a6,0x98d0968648a45084,0x99004a30a7f9bda,0x73111190245d0002]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x6822c08a00431402,0x4008c084c00882d0,0x92091820408286,0x1901c20010000821,0x82013c04498040,0x88008c881011421,0x882000ca1930680,0x418c043040a2250,0x20a18c00184833a,0x10415a2070980104,0x6031310100240806,0x2040060402ab800,0x8a9200406801108a,0x1606101102311402,0x20a4460041004264,0xb020811e88448480]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x2860c4c820c91056,0x49608880402ad280,0x81b01994000207b6,0xb4004b025e411805,0xd428608810009980,0x2014142b0020825,0xea88c00600b10214,0x2808c00b2c1b0340,0x801a51c20187833b,0x19600f61142cc00e,0xb10012dc00870000,0x76201940006fb100,0x3d00045ed0300ca,0x54803480108020c2,0x240601c1e502c276,0xb1a2628603034040]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x1800400108011081,0x4004848020408080,0x800c01204002282,0x1301050048440010,0x4060094342910c0,0x80c01820802c10,0x6006800a83060084,0x1c00400144820048,0x4006104000848012,0x1005110045814010,0x9010610b04828012,0x1240850008a2040,0x6081014828110808,0x401004021130c41,0x62c24084004024,0x8482c44899202011]))
  | _ => 0

def compactPerms239 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains239 : Array (Sig × Nat) := ([(subcube 1 0, 7), (subcube 2 0, 7), (subcube 8 0, 7), (subcube 4 0, 6), (subcube 32 0, 6), (subcube 64 0, 6), (subcube 0 8, 6), (subcube 0 64, 6), (subcube 36 0, 5), (subcube 128 8, 5)] : List (Sig × Nat)).toArray

def compactWords239 : Nat → Nat
  | 0 => (limbs64 [0x1028cff1,0x467fc7f86b4d2c22,0x28080dbdddfafcfe,0xbb9c527170cc2431,0xcd10b0cc90c90b2,0xf5b82d2ff1fe2fa7,0xf8ff1dc61dff8ff0,0x4b39b84653f06311,0x9354b163c563dc57,0x41d94d7ffbffefef,0xfba43433223442a4,0x2a21c04abc19087f])
  | _ => 0

def compactCount239 (k : Nat) : Nat := match k with
  | 8 => 1
  | 7 => 6
  | 6 => 5
  | _ => 0

def compactPath239 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => 0
  | 7 => readCompactBits compactWords239 (47 + 12*i) 12
  | 6 => let v := readCompactBits compactWords239 (501 + 14*i) 14
    (readCompactBits compactWords239 (453 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def compactLive239 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => readCompactBits compactWords239 (0 + 7*i) 7
  | 7 => readCompactBits compactWords239 (119 + 8*i) 8
  | 6 => readCompactBits compactWords239 (571 + 9*i) 9
  | _ => 0

def compactPoolIDs239 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let v := readCompactBits compactWords239 (39 + 8*i) 8
    let n := v >>> 4
    let bits := readCompactBits compactWords239 (7 + 4*(v &&& 15)) (4*n)
    compactIDsFromBits bits 4 n
  | 7 => let v := readCompactBits compactWords239 (271 + 8*i) 8
    let n := v >>> 5
    let bits := readCompactBits compactWords239 (167 + 4*(v &&& 31)) (4*n)
    compactIDsFromBits bits 4 n
  | 6 => let v := readCompactBits compactWords239 (628 + 4*i) 4
    let n := v >>> 2
    let bits := readCompactBits compactWords239 (616 + 6*(v &&& 3)) (6*n)
    compactIDsFromBits bits 6 n
  | _ => []

def compactBucket239 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let d := readCompactBits compactWords239 (319 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 12)
    let v := readCompactBits compactWords239 (321 + 11*off) 11
    if v >>> 3 == (i/104729)%251 then [v &&& 7] else []
  | 6 => let d := readCompactBits compactWords239 (648 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 8)
    let v := readCompactBits compactWords239 (650 + 11*off) 11
    if v >>> 3 == (i/104729)%251 then [v &&& 7] else []
  | _ => []

def samplesP119 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x6f6effdf,0xfebd725ed3d5a539,0x4bfbfcffe5fedd94,0xf79fff3d8bf70cd7,0x137604114fa9e0b,0x58d73fcff7fd4cff,0xd1daf75c5fa62199,0xf466292f78c67d41,0xa5d869806791a0df,0xf1ee13edc712b25c,0xebd96f0138cca888,0xa4e9fe2104e9a44]))
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0x4890008,0xc0111a780b1c61e2,0x6c02308041020e14,0x943c062083418fd3,0xc3761c8957e0da9b,0xd8d8004204d41861,0xa052060f11a42d39,0x32dea90ff0766e27,0xa17e09b877dde2c2,0x68a262c88891e29c,0x769f2b87193ead89,0x9bcef16e599bbe56])) : Bits)
  | 2 => (BitVec.ofNat _ (limbs64 [0x5fe0fefc,0xdf73edfc99242086,0xa3fefbbfdf9f9a3f,0x9c7f289bf7d9c3c8,0xea5e0c9871453810,0x6fffb7ff7bd33,0x69f71ee7977c917f,0xb99909ce56e2e26,0xa86780201004421e,0xddbbfbbbfda1c637,0x32ae89cd4f300500,0x11800f3afb330402]))
  | 4 => ~~~((BitVec.ofNat _ (limbs64 [0x1220010,0xc39408610312691,0x9800c0070002d003,0xd3c01913a901e6,0x32b9405a3514bc5c,0x75f005001322853c,0x418227a4460120de,0x8d3948cf8f4e3d42,0xa5a19fa479b75b6b,0x1123912126234a5f,0x2be862f04ef19ffe,0x13af9d728c65cfe2])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0x779fff7b,0xfdd9dee72ffb53d2,0x5bffffdf7fe3fff3,0x93f3c6e7b329bf32,0x32f1db8f3714ca58,0x3447ed7f9fca977d,0xbe32e7afff9d2cf8,0xba5868cf8f71e9e6,0x5121982471075a2f,0x6e63ffc62e8d4adb,0x750122f6d8f19d60,0x13aa095d0dc98d82]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x7dbbfdbf,0xefff1bbb7e386ee1,0xbffff7e7fb7e664f,0x6cfcd7785feff9e7,0xd7a8147acfa0f484,0xc1bdd7f6fff6fbec,0xe7cf2fbf60e36e06,0x5bfcf43921e161b,0xa7be179808f8015b,0x3bb7e479ba73698c,0xefe72b20702029f,0x8005f466ccb56270]))
  | _ => 0

def samplesQ119 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x10918020,0x80c083210c2a08c2,0x352300c406112018,0x4e000261c010938,0x3c084a46a00a110,0xa10c260c54080dc0,0x40223804582621e0,0x5c009f000484483,0xa000240815603bc,0x106c122807300264,0x29086c017000b090,0x1c088fa010440a04]))
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0x7b76f7ff,0x1fbef5aff1e7be5d,0xda7f7d2f7dbd9daf,0x79b7efddfbfefd6f,0x7c5bef7ab67f776d,0xffa3557bedd7d675,0xfbdf776bbbeb9ebe,0xbebffeaf7dbfda5f,0x39fbf4ef6aeffd43,0x7fbaeedcecd5fedd,0x5ed7bfd69f7fcbab,0xfbe7716f7dbbfede])) : Bits)
  | 2 => (BitVec.ofNat _ (limbs64 [0x201f4121,0x748412022c935b79,0x5ea820c2128b56e9,0xa2a95a4c99021811,0x138102c4cc08c3ee,0xbdd69dd86e5a0990,0x9240c46410554ab,0x56aa0aa5a31ae12b,0xcc0ca602c19892bc,0xd1bb2b1bfc210430,0x330c4141641484cc,0xb8912f32f3330002]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x1221011,0x618008410002611,0x8a14082060008081,0x2811a208014c1002,0x2008000a10101444,0x50a3106108811201,0x1048000880408412,0x900a840644828008,0x30b02408010040,0x64804c9448409080,0x4010800481144801,0x21602009219a3008]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x8600454,0x22220084004a404,0x8050410801208000,0x1914a10120cc4044,0x4402201000210001,0x4221402381800024,0x2210402002888210,0x8801a40254800844,0x30b2108802200403,0x2e00c4c400840009,0x401009008424923,0x162104d0c888480]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x2442144,0x100044008145900c,0x4048140108041420,0x11044941a0824400,0x810490000460029,0xe004112a144c000,0x8081030120011208,0xa21220131100844,0x308a000120006803,0xb12a040a0006800,0xc212020202012a,0x808310464c214050]))
  | _ => 0

def compactPerms119 : Array (List Nat) := ([[], [100], [16], [16, 100]] : List (List Nat)).toArray

def compactDomains119 : Array (Sig × Nat) := ([(subcube 1 0, 7)] : List (Sig × Nat)).toArray

def compactWords119 : Nat → Nat
  | 0 => 0x13f
  | _ => 0

def compactCount119 (k : Nat) : Nat := match k with
  | 7 => 1
  | _ => 0

def compactPath119 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | _ => 0

def compactLive119 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits compactWords119 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs119 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits compactWords119 (7 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords119 (6 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket119 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP255 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x19d8ab238b80e600,0x3c031802a75b852,0x11b80981925a006a,0x3ffefe47586d7f82,0x8be1f86d4ac6933f,0xb8c8300269b25f21,0x6d83616011599b1c,0x833b63db15dd0576,0x92ae386413ac02c4,0x31c4201c60149a37,0x6195a042db222bd0,0xb036937084250819,0xc41686d81645040e,0x4019c40c342bc2,0x6b9f0415984dc140,0x2480911c858a4960]))
  | 1 => (BitVec.ofNat _ (limbs64 [0xee4640000057e9e0,0x7400c006d0824000,0x20054062100fd80,0x7f6b8dc0fd6f998f,0xe9ddb60fbc714479,0xb105fbd28487e8f5,0x4f4f5c5ff0816cee,0x6b14ac4cf255084f,0xd9d03a2ac4131d60,0x7b83c06a6a40e1,0x642110ba20010532,0x48fe680f41d01497,0x11e60006e80268f0,0x603c20a300803e7,0x211c831e2c5a20bb,0x1a0c568560403484]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x70069003c69f1001,0x88040e1901080000,0x2c4122004c850200,0x3fdb97e76fddedfa,0xda7f2fbf6163930c,0xb3ff84faf53905de,0x9c733a812fb741f0,0xc52e2d37eba4c5b3,0xcd7f7b32cd8c00c,0xc40e472080324dca,0x8a4c28003436d60d,0x950002dc70a18ba0,0xa1a9790100009000,0x83c20304000c7f5,0x8da5c5fdd2007c42,0xd69668a206148008]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x803105fc31600006,0x3b000000000101,0xc000001800000001,0x3ff77ffbef79ffff,0xffafffb6eb9ccfd1,0x4d6a8ee4ee7d5e5b,0x42789bfed3aa9e37,0x6ec6d5a275f353e4,0xf366c3dc7a00d3b1,0x1a00248f0e813300,0xf92dfe0c3c9080f,0x20c82c2081526366,0x3650000000100001,0xf000000081c003ff,0xfcbbff69e5b18419,0x29608942e1000003]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xe610aadc7400e418,0x7200c160d48186ac,0x1a6856012200454,0x953d193ac69eae4e,0x570bc1eae139b0de,0x464340fd798cf082,0x3df885180d1a6b2b,0x14dd99989c2aac8e,0x6d20c46b92a32106,0x2a4ad81391288434,0x918240add8dc2420,0x873942007a2ef41e,0xc0906200da80328,0x183d60512131238,0xd870625903530a34,0x950780681c2902d4]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x11a9140000570e00,0x8003e06207c0040,0xc405a07cc80fa00,0x78d46dbcb2e2567d,0x35f04fdfd78e2866,0x4eb1fb2d12c7b709,0xc2b4a2dfee6567d1,0x930b5228e7aaf249,0x26093a4529431e9b,0xc4357c206a5520d6,0x9a49105504012acd,0xc1958fbe081488,0xea063906f00390c0,0x80021f02820209a,0x57c2fa8270042f24,0x207b370a6a82b008]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xdc85a28cd2819f8,0x4c000600a02569a,0x120e80002110018a,0x260ff25f3fb252f5,0x2e7e9fd09e1a6da2,0x3b364f07034001fe,0xb30ced213eeeb407,0x38e16a7708163f31,0x1e7fcd9084242048,0xf5b198cf15845e08,0x742667022c34d1a2,0x6a0099b30b5a6840,0x1a9c06000446f12,0x780000b040f0849,0xa6473de265a452c2,0xc91900b593604e00]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x22765d73aa81007,0x813f009905002925,0xe01120f8006f0035,0x8ba0e2bd9197a131,0xf496707114e57e81,0xc49c35199e7aaa24,0xb08756a6c05490c8,0xfcf096c50a49fa98,0xe1990590415cec33,0xb80037095cba109,0x788f1d03cad050,0x5f07644004858361,0x5a50c09903b80005,0xf07c0c00c3c0d504,0x126818a68aaa918d,0x42e06e5118150133]))
  | _ => 0

def samplesQ255 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x6416610880600006,0xf04c00021801148,0x20080b86003003e0,0x7faa9600086d2082,0x81e1b00d4a409211,0x3000000060b35b00,0xd03496000010114,0x8214249301900044,0x8006382844ac0280,0x4000c60228902,0x60010040c3210380,0xb036081000210099,0x641000401602041c,0x3a00880427c2,0x219d00159049c000,0x480110480024060]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x2c124140624c4282,0x490405061893060,0x80192400442e0,0x7f6a85c00d2d0902,0xc1c0940d18410008,0x91002890a493c821,0x5415c559001008e,0x29142404d2c50044,0xc9d21a28440249e0,0x28144282200a3,0x2401000861210104,0x9a280641a10091,0x8400124622a890,0xa4094200580403e6,0x211c81140c4a201b,0x204540540002404]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x78260231480a2188,0xaf300210c1c04350,0x648c28205050c273,0x7fc997c36f54ad82,0xda6f2cbb4820110c,0xb14a845a613949c4,0x1c63380106964120,0xc1060d3183a445d3,0xc16b7020c88c128,0xa438100324502,0x82c508401470830c,0x2480027c0121a9d3,0x2591520110808482,0xc90b810510987f5,0x8da5857d92006442,0xd48648a006040008]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x32a3206c802544db,0xeb1267126c105702,0xed926de2e4105083,0x3ff75bf3e779ffed,0x5fafffb6ea90c291,0x58688aa4aa1d5e53,0x44190b3e13288c33,0x6686c48274f25160,0x7062d1ce6a8851b0,0x5212698724014704,0x2b905a6155c10a07,0x24d21c3413106f46,0x349148428050222c,0xc80100898190b3ff,0xfcbbf769e5918418,0x29408942e1000002]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x8200181100022c10,0xa0000d8604020201,0x8481042180000009,0x110820c2008608,0x16024122a12000c6,0x1006909040002,0x10a8800009126a01,0x40899080400808a,0x24200002b2001004,0xa40580180080414,0x28000a518400c00,0x600040030065502,0x8120008910020,0x110802522111018,0xd820420802100820,0x110380680c290080]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x80c8180414811870,0x43052304148806,0x9202840884831c00,0x8014683c9082527d,0x24104340858e0862,0x46b1530110002408,0x4290828a68402240,0x10095208200ab208,0x201004123411402,0x46912c0003052244,0x1008433100003841,0x841158192184400,0x82020928a8091040,0x530400e422200808,0x52427a8260040b24,0x2079220a28809000]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x4106000d001068,0xb020910344002,0x5002a0000e8a3806,0x8004601f30925075,0x281c0ad0001a6d20,0xa1645060240009c,0xa204200024ac9400,0xe1026008002c31,0x1208449009000002,0xe5b1208011017200,0xa6f1204045021,0x484091200a582840,0x21402100441342,0x2c0041a00e84801,0x6423ce261a412c0,0xc818009013400a00]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x8040033800020,0x1001100102040080,0x1060900001820800,0x8000200c10820010,0x2010004014052400,0x48430001440a020,0xa0040480c04010c8,0x1860004408090a00,0x189001001102003,0x481003001c02008,0x288110000a1010,0x900410004080020,0x8408118602c0900,0x304c444200404000,0x240088208221185,0x220261110100111]))
  | _ => 0

def compactPerms255 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains255 : Array (Sig × Nat) := ([(subcube 1 0, 10), (subcube 2 0, 10), (subcube 4 0, 10), (subcube 8 0, 10), (subcube 32 0, 10), (subcube 64 0, 10), (subcube 16 0, 9), (subcube 0 8, 9), (subcube 128 8, 8)] : List (Sig × Nat)).toArray

def compactWords255 : Nat → Nat
  | 0 => (limbs64 [0x4428080c754f8,0x1f75c6ef75048676,0xc874bf7fcff3fc3e,0x127703b2a1081f6c,0x65d49c77ebdd49c7,0x6dd4fffeff748786,0x74648086543210ff])
  | _ => 0

def compactCount255 (k : Nat) : Nat := match k with
  | 11 => 1
  | 10 => 3
  | 9 => 1
  | _ => 0

def compactPath255 (k : Nat) (i : Nat) : Nat := match k with
  | 11 => 0
  | 10 => readCompactBits compactWords255 (48 + 12*i) 12
  | 9 => let v := readCompactBits compactWords255 (336 + 12*i) 12
    (readCompactBits compactWords255 (324 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def compactLive255 (k : Nat) (i : Nat) : Nat := match k with
  | 11 => readCompactBits compactWords255 (0 + 8*i) 8
  | 10 => readCompactBits compactWords255 (84 + 9*i) 9
  | 9 => readCompactBits compactWords255 (348 + 10*i) 10
  | _ => 0

def compactPoolIDs255 (k : Nat) (i : Nat) : List Nat := match k with
  | 11 => let v := readCompactBits compactWords255 (40 + 8*i) 8
    let n := v >>> 4
    let bits := readCompactBits compactWords255 (8 + 4*(v &&& 15)) (4*n)
    compactIDsFromBits bits 4 n
  | 10 => let v := readCompactBits compactWords255 (235 + 9*i) 9
    let n := v >>> 5
    let bits := readCompactBits compactWords255 (111 + 4*(v &&& 31)) (4*n)
    compactIDsFromBits bits 4 n
  | 9 => let v := readCompactBits compactWords255 (418 + 8*i) 8
    let n := v >>> 4
    let bits := readCompactBits compactWords255 (358 + 6*(v &&& 15)) (6*n)
    compactIDsFromBits bits 6 n
  | _ => []

def compactBucket255 (k : Nat) (i : Nat) : List Nat := match k with
  | 10 => let d := readCompactBits compactWords255 (262 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 6)
    let v := readCompactBits compactWords255 (264 + 10*off) 10
    if v >>> 2 == (i/104729)%251 then [v &&& 3] else []
  | 9 => let d := readCompactBits compactWords255 (426 + 1*(i % 1)) 1
    let off := ((i/1 + d) % 1)
    let v := readCompactBits compactWords255 (427 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | _ => []

theorem compactHalves {test : Nat → Bool} {start n : Nat}
    (first : chartBlock test start (n / 2) = true)
    (last : chartBlock test (start + n / 2) (n - n / 2) = true) :
    chartBlock test start n = true := by
  have eq : n / 2 + (n - n / 2) = n := by omega
  simpa only [eq] using chartBlock_join first last

def grid82 : CompactGrid := (82, 3, samplesP82, samplesQ82)
def tab82 : CompactTable := (compactCount82, compactPath82, compactLive82, compactPoolIDs82, compactBucket82)
def check82 (k : Nat) := compactNode grid82 tab82 compactDomains82 compactPerms82 k
def sliceSpecs82 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains82 : ∀ d ∈ compactDomains82, Slice true (vars 82) (graphGoal 82) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs82)
  · simp
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs82 : properPairs (graphGoal 82) (asRow samplesP82) (asRow samplesQ82) :=
  compactPairs (g := grid82) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos82 : ∀ p ∈ compactPerms82, autoOK (graphGoal 82) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c82k3p0 : chartBlock (check82 3) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev82k3 : chartBlock (check82 3) 0 1 = true :=
  c82k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded82 : Impossible true (graphGoal 82) 3 (vars 82).toFinset := by
  apply compactRoot (g := grid82) (t := tab82) (dom := compactDomains82) (perms := compactPerms82) pairs82 domains82 autos82
  · intro k hk
    change k ≤ 3 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev82k3
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound82 : Lower true (vars 82) (graphGoal 82) 4 :=
  plain_low (hints := 16842816) (by decide +kernel) excluded82

def grid210 : CompactGrid := (210, 4, samplesP210, samplesQ210)
def tab210 : CompactTable := (compactCount210, compactPath210, compactLive210, compactPoolIDs210, compactBucket210)
def check210 (k : Nat) := compactNode grid210 tab210 compactDomains210 compactPerms210 k
def sliceSpecs210 : List SliceSpec := [(128, 0, 82, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains210 : ∀ d ∈ compactDomains210, Slice true (vars 210) (graphGoal 210) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(82, 4)]) (specs := sliceSpecs210)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound82
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs210 : properPairs (graphGoal 210) (asRow samplesP210) (asRow samplesQ210) :=
  compactPairs (g := grid210) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos210 : ∀ p ∈ compactPerms210, autoOK (graphGoal 210) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c210k4p0 : chartBlock (check210 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev210k4 : chartBlock (check210 4) 0 1 = true :=
  c210k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded210 : Impossible true (graphGoal 210) 4 (vars 210).toFinset := by
  apply compactRoot (g := grid210) (t := tab210) (dom := compactDomains210) (perms := compactPerms210) pairs210 domains210 autos210
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev210k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound210 : Lower true (vars 210) (graphGoal 210) 5 :=
  plain_low (hints := 1090584640) (by decide +kernel) excluded210

def grid212 : CompactGrid := (212, 3, samplesP212, samplesQ212)
def tab212 : CompactTable := (compactCount212, compactPath212, compactLive212, compactPoolIDs212, compactBucket212)
def check212 (k : Nat) := compactNode grid212 tab212 compactDomains212 compactPerms212 k
def sliceSpecs212 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains212 : ∀ d ∈ compactDomains212, Slice true (vars 212) (graphGoal 212) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs212)
  · simp
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs212 : properPairs (graphGoal 212) (asRow samplesP212) (asRow samplesQ212) :=
  compactPairs (g := grid212) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos212 : ∀ p ∈ compactPerms212, autoOK (graphGoal 212) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c212k3p0 : chartBlock (check212 3) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev212k3 : chartBlock (check212 3) 0 1 = true :=
  c212k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded212 : Impossible true (graphGoal 212) 3 (vars 212).toFinset := by
  apply compactRoot (g := grid212) (t := tab212) (dom := compactDomains212) (perms := compactPerms212) pairs212 domains212 autos212
  · intro k hk
    change k ≤ 3 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev212k3
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound212 : Lower true (vars 212) (graphGoal 212) 4 :=
  plain_low (hints := 604374784) (by decide +kernel) excluded212

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound150 : Lower true (vars 150) (graphGoal 150) 4 :=
  carry_of (old := 150) (rep := 212) (swaps := [97]) (by decide +kernel) bound212

def grid214 : CompactGrid := (214, 6, samplesP214, samplesQ214)
def tab214 : CompactTable := (compactCount214, compactPath214, compactLive214, compactPoolIDs214, compactBucket214)
def check214 (k : Nat) := compactNode grid214 tab214 compactDomains214 compactPerms214 k
def sliceSpecs214 : List SliceSpec := [(4, 0, 210, 0, 0, 5, 5), (0, 4, 82, 128, 4026531840, 5, 4), (2, 0, 212, 0, 0, 4, 4), (64, 0, 150, 0, 0, 4, 4), (128, 4, 82, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains214 : ∀ d ∈ compactDomains214, Slice true (vars 214) (graphGoal 214) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(210, 5), (82, 4), (212, 4), (150, 4)]) (specs := sliceSpecs214)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact bound210
    · exact bound82
    · exact bound212
    · exact bound150
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs214 : properPairs (graphGoal 214) (asRow samplesP214) (asRow samplesQ214) :=
  compactPairs (g := grid214) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos214 : ∀ p ∈ compactPerms214, autoOK (graphGoal 214) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c214k4p0 : chartBlock (check214 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev214k4 : chartBlock (check214 4) 0 1 = true :=
  c214k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c214k5p0 : chartBlock (check214 5) 0 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev214k5 : chartBlock (check214 5) 0 3 = true :=
  c214k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c214k6p0 : chartBlock (check214 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev214k6 : chartBlock (check214 6) 0 1 = true :=
  c214k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded214 : Impossible true (graphGoal 214) 6 (vars 214).toFinset := by
  apply compactRoot (g := grid214) (t := tab214) (dom := compactDomains214) (perms := compactPerms214) pairs214 domains214 autos214
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev214k4
    · exact lev214k5
    · exact lev214k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound214 : Lower true (vars 214) (graphGoal 214) 7 :=
  plain_low (hints := 553715520) (by decide +kernel) excluded214

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound180 : Lower true (vars 180) (graphGoal 180) 4 :=
  carry_of (old := 180) (rep := 212) (swaps := [66, 101]) (by decide +kernel) bound212

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound178 : Lower true (vars 178) (graphGoal 178) 4 :=
  carry_of (old := 178) (rep := 212) (swaps := [65, 116, 101, 114]) (by decide +kernel) bound212

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound166 : Lower true (vars 166) (graphGoal 166) 4 :=
  carry_of (old := 166) (rep := 212) (swaps := [33, 66, 117, 118]) (by decide +kernel) bound212

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound54 : Lower true (vars 54) (graphGoal 54) 4 :=
  carry_of (old := 54) (rep := 212) (swaps := [65, 100, 117]) (by decide +kernel) bound212

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

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound118 : Lower true (vars 118) (graphGoal 118) 7 :=
  carry_of (old := 118) (rep := 214) (swaps := [65, 117]) (by decide +kernel) bound214

def grid242 : CompactGrid := (242, 5, samplesP242, samplesQ242)
def tab242 : CompactTable := (compactCount242, compactPath242, compactLive242, compactPoolIDs242, compactBucket242)
def check242 (k : Nat) := compactNode grid242 tab242 compactDomains242 compactPerms242 k
def sliceSpecs242 : List SliceSpec := [(32, 0, 210, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains242 : ∀ d ∈ compactDomains242, Slice true (vars 242) (graphGoal 242) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(210, 5)]) (specs := sliceSpecs242)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound210
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
theorem c242k5p0 : chartBlock (check242 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev242k5 : chartBlock (check242 5) 0 1 = true :=
  c242k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded242 : Impossible true (graphGoal 242) 5 (vars 242).toFinset := by
  apply compactRoot (g := grid242) (t := tab242) (dom := compactDomains242) (perms := compactPerms242) pairs242 domains242 autos242
  · intro k hk
    change k ≤ 5 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev242k5
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound242 : Lower true (vars 242) (graphGoal 242) 6 :=
  plain_low (hints := 1091633216) (by decide +kernel) excluded242

def grid244 : CompactGrid := (244, 4, samplesP244, samplesQ244)
def tab244 : CompactTable := (compactCount244, compactPath244, compactLive244, compactPoolIDs244, compactBucket244)
def check244 (k : Nat) := compactNode grid244 tab244 compactDomains244 compactPerms244 k
def sliceSpecs244 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains244 : ∀ d ∈ compactDomains244, Slice true (vars 244) (graphGoal 244) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs244)
  · simp
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
  plain_low (hints := 606471424) (by decide +kernel) excluded244

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound230 : Lower true (vars 230) (graphGoal 230) 5 :=
  carry_of (old := 230) (rep := 244) (swaps := [65, 117]) (by decide +kernel) bound244

def grid246 : CompactGrid := (246, 8, samplesP246, samplesQ246)
def tab246 : CompactTable := (compactCount246, compactPath246, compactLive246, compactPoolIDs246, compactBucket246)
def check246 (k : Nat) := compactNode grid246 tab246 compactDomains246 compactPerms246 k
def sliceSpecs246 : List SliceSpec := [(32, 0, 214, 0, 0, 7, 7), (64, 0, 182, 0, 0, 7, 7), (128, 0, 118, 0, 0, 7, 7), (4, 0, 242, 0, 0, 6, 6), (0, 4, 82, 160, 4042260480, 6, 4), (2, 0, 244, 0, 0, 5, 5), (16, 0, 230, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains246 : ∀ d ∈ compactDomains246, Slice true (vars 246) (graphGoal 246) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(214, 7), (182, 7), (118, 7), (242, 6), (82, 4), (244, 5), (230, 5)]) (specs := sliceSpecs246)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound214
    · exact bound182
    · exact bound118
    · exact bound242
    · exact bound82
    · exact bound244
    · exact bound230
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
  plain_low (hints := 554763584) (by decide +kernel) excluded246

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
  plain_low (hints := 554792256) (by decide +kernel) excluded254

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound145 : Lower true (vars 145) (graphGoal 145) 4 :=
  carry_of (old := 145) (rep := 82) (swaps := [16, 118]) (by decide +kernel) bound82

def grid209 : CompactGrid := (209, 4, samplesP209, samplesQ209)
def tab209 : CompactTable := (compactCount209, compactPath209, compactLive209, compactPoolIDs209, compactBucket209)
def check209 (k : Nat) := compactNode grid209 tab209 compactDomains209 compactPerms209 k
def sliceSpecs209 : List SliceSpec := [(64, 0, 145, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains209 : ∀ d ∈ compactDomains209, Slice true (vars 209) (graphGoal 209) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(145, 4)]) (specs := sliceSpecs209)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound145
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs209 : properPairs (graphGoal 209) (asRow samplesP209) (asRow samplesQ209) :=
  compactPairs (g := grid209) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos209 : ∀ p ∈ compactPerms209, autoOK (graphGoal 209) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c209k4p0 : chartBlock (check209 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev209k4 : chartBlock (check209 4) 0 1 = true :=
  c209k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded209 : Impossible true (graphGoal 209) 4 (vars 209).toFinset := by
  apply compactRoot (g := grid209) (t := tab209) (dom := compactDomains209) (perms := compactPerms209) pairs209 domains209 autos209
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev209k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound209 : Lower true (vars 209) (graphGoal 209) 5 :=
  plain_low (hints := 4) (by decide +kernel) excluded209

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound149 : Lower true (vars 149) (graphGoal 149) 5 :=
  carry_of (old := 149) (rep := 210) (swaps := [16, 114, 100, 118]) (by decide +kernel) bound210

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound81 : Lower true (vars 81) (graphGoal 81) 4 :=
  carry_of (old := 81) (rep := 82) (swaps := [16]) (by decide +kernel) bound82

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound197 : Lower true (vars 197) (graphGoal 197) 4 :=
  carry_of (old := 197) (rep := 212) (swaps := [64]) (by decide +kernel) bound212

def grid213 : CompactGrid := (213, 6, samplesP213, samplesQ213)
def tab213 : CompactTable := (compactCount213, compactPath213, compactLive213, compactPoolIDs213, compactBucket213)
def check213 (k : Nat) := compactNode grid213 tab213 compactDomains213 compactPerms213 k
def sliceSpecs213 : List SliceSpec := [(4, 0, 209, 0, 0, 5, 5), (64, 0, 149, 0, 0, 5, 5), (0, 4, 81, 128, 4026531840, 5, 4), (1, 0, 212, 0, 0, 4, 4), (16, 0, 197, 0, 0, 4, 4), (128, 4, 81, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains213 : ∀ d ∈ compactDomains213, Slice true (vars 213) (graphGoal 213) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(209, 5), (149, 5), (81, 4), (212, 4), (197, 4)]) (specs := sliceSpecs213)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact bound209
    · exact bound149
    · exact bound81
    · exact bound212
    · exact bound197
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
theorem c213k5p0 : chartBlock (check213 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev213k5 : chartBlock (check213 5) 0 1 = true :=
  c213k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c213k6p0 : chartBlock (check213 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev213k6 : chartBlock (check213 6) 0 1 = true :=
  c213k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded213 : Impossible true (graphGoal 213) 6 (vars 213).toFinset := by
  apply compactRoot (g := grid213) (t := tab213) (dom := compactDomains213) (perms := compactPerms213) pairs213 domains213 autos213
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev213k4
    · exact lev213k5
    · exact lev213k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound213 : Lower true (vars 213) (graphGoal 213) 7 :=
  plain_low (hints := 1796) (by decide +kernel) excluded213

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound117 : Lower true (vars 117) (graphGoal 117) 7 :=
  carry_of (old := 117) (rep := 214) (swaps := [64, 65, 117]) (by decide +kernel) bound214

def grid241 : CompactGrid := (241, 5, samplesP241, samplesQ241)
def tab241 : CompactTable := (compactCount241, compactPath241, compactLive241, compactPoolIDs241, compactBucket241)
def check241 (k : Nat) := compactNode grid241 tab241 compactDomains241 compactPerms241 k
def sliceSpecs241 : List SliceSpec := [(32, 0, 209, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains241 : ∀ d ∈ compactDomains241, Slice true (vars 241) (graphGoal 241) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(209, 5)]) (specs := sliceSpecs241)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound209
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
theorem c241k5p0 : chartBlock (check241 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev241k5 : chartBlock (check241 5) 0 1 = true :=
  c241k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded241 : Impossible true (graphGoal 241) 5 (vars 241).toFinset := by
  apply compactRoot (g := grid241) (t := tab241) (dom := compactDomains241) (perms := compactPerms241) pairs241 domains241 autos241
  · intro k hk
    change k ≤ 5 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev241k5
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound241 : Lower true (vars 241) (graphGoal 241) 6 :=
  plain_low (hints := 4) (by decide +kernel) excluded241

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound177 : Lower true (vars 177) (graphGoal 177) 5 :=
  carry_of (old := 177) (rep := 210) (swaps := [64, 65, 117, 118]) (by decide +kernel) bound210

def grid181 : CompactGrid := (181, 5, samplesP181, samplesQ181)
def tab181 : CompactTable := (compactCount181, compactPath181, compactLive181, compactPoolIDs181, compactBucket181)
def check181 (k : Nat) := compactNode grid181 tab181 compactDomains181 compactPerms181 k
def sliceSpecs181 : List SliceSpec := [(4, 0, 177, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains181 : ∀ d ∈ compactDomains181, Slice true (vars 181) (graphGoal 181) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(177, 5)]) (specs := sliceSpecs181)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound177
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
  plain_low (hints := 1284) (by decide +kernel) excluded181

def grid229 : CompactGrid := (229, 4, samplesP229, samplesQ229)
def tab229 : CompactTable := (compactCount229, compactPath229, compactLive229, compactPoolIDs229, compactBucket229)
def check229 (k : Nat) := compactNode grid229 tab229 compactDomains229 compactPerms229 k
def sliceSpecs229 : List SliceSpec := [(32, 0, 197, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains229 : ∀ d ∈ compactDomains229, Slice true (vars 229) (graphGoal 229) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(197, 4)]) (specs := sliceSpecs229)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound197
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs229 : properPairs (graphGoal 229) (asRow samplesP229) (asRow samplesQ229) :=
  compactPairs (g := grid229) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos229 : ∀ p ∈ compactPerms229, autoOK (graphGoal 229) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c229k4p0 : chartBlock (check229 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev229k4 : chartBlock (check229 4) 0 1 = true :=
  c229k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded229 : Impossible true (graphGoal 229) 4 (vars 229).toFinset := by
  apply compactRoot (g := grid229) (t := tab229) (dom := compactDomains229) (perms := compactPerms229) pairs229 domains229 autos229
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev229k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound229 : Lower true (vars 229) (graphGoal 229) 5 :=
  plain_low (hints := 1285) (by decide +kernel) excluded229

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound101 : Lower true (vars 101) (graphGoal 101) 4 :=
  carry_of (old := 101) (rep := 212) (swaps := [64, 117]) (by decide +kernel) bound212

def grid245 : CompactGrid := (245, 8, samplesP245, samplesQ245)
def tab245 : CompactTable := (compactCount245, compactPath245, compactLive245, compactPoolIDs245, compactBucket245)
def check245 (k : Nat) := compactNode grid245 tab245 compactDomains245 compactPerms245 k
def sliceSpecs245 : List SliceSpec := [(32, 0, 213, 0, 0, 7, 7), (128, 0, 117, 0, 0, 7, 7), (4, 0, 241, 0, 0, 6, 6), (64, 0, 181, 0, 0, 6, 6), (0, 4, 81, 160, 4042260480, 6, 4), (1, 0, 244, 0, 0, 5, 5), (16, 0, 229, 0, 0, 5, 5), (68, 0, 177, 0, 0, 5, 5), (65, 0, 180, 0, 0, 4, 4), (144, 0, 101, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains245 : ∀ d ∈ compactDomains245, Slice true (vars 245) (graphGoal 245) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(213, 7), (117, 7), (241, 6), (181, 6), (81, 4), (244, 5), (229, 5), (177, 5), (180, 4), (101, 4)]) (specs := sliceSpecs245)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound213
    · exact bound117
    · exact bound241
    · exact bound181
    · exact bound81
    · exact bound244
    · exact bound229
    · exact bound177
    · exact bound180
    · exact bound101
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
theorem c245k5p0 : chartBlock (check245 5) 0 7 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev245k5 : chartBlock (check245 5) 0 7 = true :=
  c245k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c245k6p0 : chartBlock (check245 6) 0 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c245k6p1 : chartBlock (check245 6) 8 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c245k6p2 : chartBlock (check245 6) 16 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c245k6p3 : chartBlock (check245 6) 24 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev245k6 : chartBlock (check245 6) 0 26 = true :=
  (chartBlock_join (a := 16) (b := 10) (chartBlock_join (a := 8) (b := 8) c245k6p0 c245k6p1) (chartBlock_join (a := 8) (b := 2) c245k6p2 c245k6p3))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c245k7p0 : chartBlock (check245 7) 0 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c245k7p1 : chartBlock (check245 7) 8 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev245k7 : chartBlock (check245 7) 0 10 = true :=
  (chartBlock_join (a := 8) (b := 2) c245k7p0 c245k7p1)
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
  plain_low (hints := 1284) (by decide +kernel) excluded245

def grid253 : CompactGrid := (253, 9, samplesP253, samplesQ253)
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
  plain_low (hints := 29956) (by decide +kernel) excluded253

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound218 : Lower true (vars 218) (graphGoal 218) 7 :=
  carry_of (old := 218) (rep := 214) (swaps := [50]) (by decide +kernel) bound214

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound217 : Lower true (vars 217) (graphGoal 217) 7 :=
  carry_of (old := 217) (rep := 213) (swaps := [50]) (by decide +kernel) bound213

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound147 : Lower true (vars 147) (graphGoal 147) 5 :=
  carry_of (old := 147) (rep := 210) (swaps := [96, 113]) (by decide +kernel) bound210

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound83 : Lower true (vars 83) (graphGoal 83) 5 :=
  carry_of (old := 83) (rep := 209) (swaps := [96, 113]) (by decide +kernel) bound209

def grid211 : CompactGrid := (211, 6, samplesP211, samplesQ211)
def tab211 : CompactTable := (compactCount211, compactPath211, compactLive211, compactPoolIDs211, compactBucket211)
def check211 (k : Nat) := compactNode grid211 tab211 compactDomains211 compactPerms211 k
def sliceSpecs211 : List SliceSpec := [(1, 0, 210, 0, 0, 5, 5), (2, 0, 209, 0, 0, 5, 5), (64, 0, 147, 0, 0, 5, 5), (128, 0, 83, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains211 : ∀ d ∈ compactDomains211, Slice true (vars 211) (graphGoal 211) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(210, 5), (209, 5), (147, 5), (83, 5)]) (specs := sliceSpecs211)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact bound210
    · exact bound209
    · exact bound147
    · exact bound83
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs211 : properPairs (graphGoal 211) (asRow samplesP211) (asRow samplesQ211) :=
  compactPairs (g := grid211) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos211 : ∀ p ∈ compactPerms211, autoOK (graphGoal 211) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c211k6p0 : chartBlock (check211 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev211k6 : chartBlock (check211 6) 0 1 = true :=
  c211k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded211 : Impossible true (graphGoal 211) 6 (vars 211).toFinset := by
  apply compactRoot (g := grid211) (t := tab211) (dom := compactDomains211) (perms := compactPerms211) pairs211 domains211 autos211
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev211k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound211 : Lower true (vars 211) (graphGoal 211) 7 :=
  plain_low (hints := 68) (by decide +kernel) excluded211

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound155 : Lower true (vars 155) (graphGoal 155) 6 :=
  carry_of (old := 155) (rep := 242) (swaps := [96, 113, 83, 101]) (by decide +kernel) bound242

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound203 : Lower true (vars 203) (graphGoal 203) 5 :=
  carry_of (old := 203) (rep := 244) (swaps := [112, 97, 83, 100, 114]) (by decide +kernel) bound244

def grid219 : CompactGrid := (219, 8, samplesP219, samplesQ219)
def tab219 : CompactTable := (compactCount219, compactPath219, compactLive219, compactPoolIDs219, compactBucket219)
def check219 (k : Nat) := compactNode grid219 tab219 compactDomains219 compactPerms219 k
def sliceSpecs219 : List SliceSpec := [(1, 0, 218, 0, 0, 7, 7), (2, 0, 217, 0, 0, 7, 7), (8, 0, 211, 0, 0, 7, 7), (64, 0, 155, 0, 0, 6, 6), (0, 8, 83, 128, 4026531840, 6, 5), (16, 0, 203, 0, 0, 5, 5), (128, 8, 83, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains219 : ∀ d ∈ compactDomains219, Slice true (vars 219) (graphGoal 219) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(218, 7), (217, 7), (211, 7), (155, 6), (83, 5), (203, 5)]) (specs := sliceSpecs219)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound218
    · exact bound217
    · exact bound211
    · exact bound155
    · exact bound83
    · exact bound203
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
theorem c219k5p0 : chartBlock (check219 5) 0 6 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev219k5 : chartBlock (check219 5) 0 6 = true :=
  c219k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c219k6p0 : chartBlock (check219 6) 0 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c219k6p1 : chartBlock (check219 6) 8 6 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev219k6 : chartBlock (check219 6) 0 14 = true :=
  (chartBlock_join (a := 8) (b := 6) c219k6p0 c219k6p1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c219k7p0 : chartBlock (check219 7) 0 7 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev219k7 : chartBlock (check219 7) 0 7 = true :=
  c219k7p0
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
    · exact lev219k5
    · exact lev219k6
    · exact lev219k7
    · exact lev219k8
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound219 : Lower true (vars 219) (graphGoal 219) 9 :=
  plain_low (hints := 28740) (by decide +kernel) excluded219

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
  plain_low (hints := 28740) (by decide +kernel) excluded251

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
  plain_low (hints := 1348) (by decide +kernel) excluded247

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
  plain_low (hints := 30532) (by decide +kernel) excluded223

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound179 : Lower true (vars 179) (graphGoal 179) 6 :=
  carry_of (old := 179) (rep := 181) (swaps := [33, 116]) (by decide +kernel) bound181

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound151 : Lower true (vars 151) (graphGoal 151) 6 :=
  carry_of (old := 151) (rep := 242) (swaps := [96, 113, 82, 101]) (by decide +kernel) bound242

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound167 : Lower true (vars 167) (graphGoal 167) 5 :=
  carry_of (old := 167) (rep := 229) (swaps := [80, 97, 114]) (by decide +kernel) bound229

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound55 : Lower true (vars 55) (graphGoal 55) 5 :=
  carry_of (old := 55) (rep := 229) (swaps := [80, 113, 98, 100, 118]) (by decide +kernel) bound229

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound163 : Lower true (vars 163) (graphGoal 163) 4 :=
  carry_of (old := 163) (rep := 212) (swaps := [64, 33, 117, 118, 66]) (by decide +kernel) bound212

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound53 : Lower true (vars 53) (graphGoal 53) 4 :=
  carry_of (old := 53) (rep := 212) (swaps := [64, 100, 117]) (by decide +kernel) bound212

def grid183 : CompactGrid := (183, 8, samplesP183, samplesQ183)
def tab183 : CompactTable := (compactCount183, compactPath183, compactLive183, compactPoolIDs183, compactBucket183)
def check183 (k : Nat) := compactNode grid183 tab183 compactDomains183 compactPerms183 k
def sliceSpecs183 : List SliceSpec := [(1, 0, 182, 0, 0, 7, 7), (2, 0, 181, 0, 0, 6, 6), (4, 0, 179, 0, 0, 6, 6), (32, 0, 151, 0, 0, 6, 6), (16, 0, 167, 0, 0, 5, 5), (128, 0, 55, 0, 0, 5, 5), (6, 0, 177, 0, 0, 5, 5), (34, 0, 149, 0, 0, 5, 5), (36, 0, 147, 0, 0, 5, 5), (17, 0, 166, 0, 0, 4, 4), (20, 0, 163, 0, 0, 4, 4), (130, 0, 53, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains183 : ∀ d ∈ compactDomains183, Slice true (vars 183) (graphGoal 183) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(182, 7), (181, 6), (179, 6), (151, 6), (167, 5), (55, 5), (177, 5), (149, 5), (147, 5), (166, 4), (163, 4), (53, 4)]) (specs := sliceSpecs183)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound182
    · exact bound181
    · exact bound179
    · exact bound151
    · exact bound167
    · exact bound55
    · exact bound177
    · exact bound149
    · exact bound147
    · exact bound166
    · exact bound163
    · exact bound53
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
theorem c183k4p0 : chartBlock (check183 4) 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev183k4 : chartBlock (check183 4) 0 2 = true :=
  c183k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c183k5p0 : chartBlock (check183 5) 0 7 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev183k5 : chartBlock (check183 5) 0 7 = true :=
  c183k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c183k6p0 : chartBlock (check183 6) 0 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c183k6p1 : chartBlock (check183 6) 8 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c183k6p2 : chartBlock (check183 6) 16 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c183k6p3 : chartBlock (check183 6) 24 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev183k6 : chartBlock (check183 6) 0 27 = true :=
  (chartBlock_join (a := 16) (b := 11) (chartBlock_join (a := 8) (b := 8) c183k6p0 c183k6p1) (chartBlock_join (a := 8) (b := 3) c183k6p2 c183k6p3))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c183k7p0 : chartBlock (check183 7) 0 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c183k7p1 : chartBlock (check183 7) 8 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev183k7 : chartBlock (check183 7) 0 9 = true :=
  (chartBlock_join (a := 8) (b := 1) c183k7p0 c183k7p1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c183k8p0 : chartBlock (check183 8) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev183k8 : chartBlock (check183 8) 0 1 = true :=
  c183k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded183 : Impossible true (graphGoal 183) 8 (vars 183).toFinset := by
  apply compactRoot (g := grid183) (t := tab183) (dom := compactDomains183) (perms := compactPerms183) pairs183 domains183 autos183
  · intro k hk
    change k ≤ 8 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev183k4
    · exact lev183k5
    · exact lev183k6
    · exact lev183k7
    · exact lev183k8
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound183 : Lower true (vars 183) (graphGoal 183) 9 :=
  plain_low (hints := 1348) (by decide +kernel) excluded183

def grid191 : CompactGrid := (191, 9, samplesP191, samplesQ191)
def tab191 : CompactTable := (compactCount191, compactPath191, compactLive191, compactPoolIDs191, compactBucket191)
def check191 (k : Nat) := compactNode grid191 tab191 compactDomains191 compactPerms191 k
def sliceSpecs191 : List SliceSpec := [(8, 0, 183, 0, 0, 9, 9)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains191 : ∀ d ∈ compactDomains191, Slice true (vars 191) (graphGoal 191) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(183, 9)]) (specs := sliceSpecs191)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound183
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
  plain_low (hints := 30020) (by decide +kernel) excluded191

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound174 : Lower true (vars 174) (graphGoal 174) 5 :=
  carry_of (old := 174) (rep := 244) (swaps := [81, 114, 99, 117, 116]) (by decide +kernel) bound244

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound102 : Lower true (vars 102) (graphGoal 102) 4 :=
  carry_of (old := 102) (rep := 212) (swaps := [65, 117]) (by decide +kernel) bound212

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound172 : Lower true (vars 172) (graphGoal 172) 4 :=
  carry_of (old := 172) (rep := 212) (swaps := [66, 67, 101]) (by decide +kernel) bound212

def grid238 : CompactGrid := (238, 6, samplesP238, samplesQ238)
def tab238 : CompactTable := (compactCount238, compactPath238, compactLive238, compactPoolIDs238, compactBucket238)
def check238 (k : Nat) := compactNode grid238 tab238 compactDomains238 compactPerms238 k
def sliceSpecs238 : List SliceSpec := [(8, 0, 230, 0, 0, 5, 5), (64, 0, 174, 0, 0, 5, 5), (0, 8, 102, 128, 4026531840, 5, 4), (0, 64, 172, 2, 240, 5, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains238 : ∀ d ∈ compactDomains238, Slice true (vars 238) (graphGoal 238) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(230, 5), (174, 5), (102, 4), (172, 4)]) (specs := sliceSpecs238)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact bound230
    · exact bound174
    · exact bound102
    · exact bound172
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
theorem c238k6p0 : chartBlock (check238 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev238k6 : chartBlock (check238 6) 0 1 = true :=
  c238k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded238 : Impossible true (graphGoal 238) 6 (vars 238).toFinset := by
  apply compactRoot (g := grid238) (t := tab238) (dom := compactDomains238) (perms := compactPerms238) pairs238 domains238 autos238
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev238k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound238 : Lower true (vars 238) (graphGoal 238) 7 :=
  plain_low (hints := 554726736) (by decide +kernel) excluded238

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound201 : Lower true (vars 201) (graphGoal 201) 4 :=
  carry_of (old := 201) (rep := 212) (swaps := [64, 50, 66]) (by decide +kernel) bound212

def grid233 : CompactGrid := (233, 4, samplesP233, samplesQ233)
def tab233 : CompactTable := (compactCount233, compactPath233, compactLive233, compactPoolIDs233, compactBucket233)
def check233 (k : Nat) := compactNode grid233 tab233 compactDomains233 compactPerms233 k
def sliceSpecs233 : List SliceSpec := [(32, 0, 201, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains233 : ∀ d ∈ compactDomains233, Slice true (vars 233) (graphGoal 233) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(201, 4)]) (specs := sliceSpecs233)
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
theorem c233k4p0 : chartBlock (check233 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev233k4 : chartBlock (check233 4) 0 1 = true :=
  c233k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded233 : Impossible true (graphGoal 233) 4 (vars 233).toFinset := by
  apply compactRoot (g := grid233) (t := tab233) (dom := compactDomains233) (perms := compactPerms233) pairs233 domains233 autos233
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev233k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound233 : Lower true (vars 233) (graphGoal 233) 5 :=
  plain_low (hints := 28677) (by decide +kernel) excluded233

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound205 : Lower true (vars 205) (graphGoal 205) 5 :=
  carry_of (old := 205) (rep := 233) (swaps := [112, 82, 99]) (by decide +kernel) bound233

def grid237 : CompactGrid := (237, 6, samplesP237, samplesQ237)
def tab237 : CompactTable := (compactCount237, compactPath237, compactLive237, compactPoolIDs237, compactBucket237)
def check237 (k : Nat) := compactNode grid237 tab237 compactDomains237 compactPerms237 k
def sliceSpecs237 : List SliceSpec := [(4, 0, 233, 0, 0, 5, 5), (8, 0, 229, 0, 0, 5, 5), (32, 0, 205, 0, 0, 5, 5), (0, 8, 101, 128, 4026531840, 5, 4), (1, 64, 172, 0, 0, 4, 4), (128, 8, 101, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains237 : ∀ d ∈ compactDomains237, Slice true (vars 237) (graphGoal 237) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(233, 5), (229, 5), (205, 5), (101, 4), (172, 4)]) (specs := sliceSpecs237)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact bound233
    · exact bound229
    · exact bound205
    · exact bound101
    · exact bound172
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
theorem c237k6p0 : chartBlock (check237 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev237k6 : chartBlock (check237 6) 0 1 = true :=
  c237k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded237 : Impossible true (graphGoal 237) 6 (vars 237).toFinset := by
  apply compactRoot (g := grid237) (t := tab237) (dom := compactDomains237) (perms := compactPerms237) pairs237 domains237 autos237
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev237k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound237 : Lower true (vars 237) (graphGoal 237) 7 :=
  plain_low (hints := 29957) (by decide +kernel) excluded237

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound199 : Lower true (vars 199) (graphGoal 199) 5 :=
  carry_of (old := 199) (rep := 244) (swaps := [112, 81, 98, 116]) (by decide +kernel) bound244

def grid231 : CompactGrid := (231, 6, samplesP231, samplesQ231)
def tab231 : CompactTable := (compactCount231, compactPath231, compactLive231, compactPoolIDs231, compactBucket231)
def check231 (k : Nat) := compactNode grid231 tab231 compactDomains231 compactPerms231 k
def sliceSpecs231 : List SliceSpec := [(1, 0, 230, 0, 0, 5, 5), (32, 0, 199, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains231 : ∀ d ∈ compactDomains231, Slice true (vars 231) (graphGoal 231) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(230, 5), (199, 5)]) (specs := sliceSpecs231)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact bound230
    · exact bound199
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
  plain_low (hints := 1365) (by decide +kernel) excluded231

def grid235 : CompactGrid := (235, 5, samplesP235, samplesQ235)
def tab235 : CompactTable := (compactCount235, compactPath235, compactLive235, compactPoolIDs235, compactBucket235)
def check235 (k : Nat) := compactNode grid235 tab235 compactDomains235 compactPerms235 k
def sliceSpecs235 : List SliceSpec := [(2, 0, 233, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains235 : ∀ d ∈ compactDomains235, Slice true (vars 235) (graphGoal 235) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(233, 5)]) (specs := sliceSpecs235)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound233
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
theorem c235k5p0 : chartBlock (check235 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev235k5 : chartBlock (check235 5) 0 1 = true :=
  c235k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded235 : Impossible true (graphGoal 235) 5 (vars 235).toFinset := by
  apply compactRoot (g := grid235) (t := tab235) (dom := compactDomains235) (perms := compactPerms235) pairs235 domains235 autos235
  · intro k hk
    change k ≤ 5 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev235k5
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound235 : Lower true (vars 235) (graphGoal 235) 6 :=
  plain_low (hints := 28757) (by decide +kernel) excluded235

def grid207 : CompactGrid := (207, 5, samplesP207, samplesQ207)
def tab207 : CompactTable := (compactCount207, compactPath207, compactLive207, compactPoolIDs207, compactBucket207)
def check207 (k : Nat) := compactNode grid207 tab207 compactDomains207 compactPerms207 k
def sliceSpecs207 : List SliceSpec := [(2, 0, 205, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains207 : ∀ d ∈ compactDomains207, Slice true (vars 207) (graphGoal 207) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(205, 5)]) (specs := sliceSpecs207)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound205
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs207 : properPairs (graphGoal 207) (asRow samplesP207) (asRow samplesQ207) :=
  compactPairs (g := grid207) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos207 : ∀ p ∈ compactPerms207, autoOK (graphGoal 207) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c207k5p0 : chartBlock (check207 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev207k5 : chartBlock (check207 5) 0 1 = true :=
  c207k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded207 : Impossible true (graphGoal 207) 5 (vars 207).toFinset := by
  apply compactRoot (g := grid207) (t := tab207) (dom := compactDomains207) (perms := compactPerms207) pairs207 domains207 autos207
  · intro k hk
    change k ≤ 5 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev207k5
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound207 : Lower true (vars 207) (graphGoal 207) 6 :=
  plain_low (hints := 30566) (by decide +kernel) excluded207

def grid175 : CompactGrid := (175, 5, samplesP175, samplesQ175)
def tab175 : CompactTable := (compactCount175, compactPath175, compactLive175, compactPoolIDs175, compactBucket175)
def check175 (k : Nat) := compactNode grid175 tab175 compactDomains175 compactPerms175 k
def sliceSpecs175 : List SliceSpec := [(1, 0, 174, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains175 : ∀ d ∈ compactDomains175, Slice true (vars 175) (graphGoal 175) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(174, 5)]) (specs := sliceSpecs175)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound174
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
theorem c175k5p0 : chartBlock (check175 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev175k5 : chartBlock (check175 5) 0 1 = true :=
  c175k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded175 : Impossible true (graphGoal 175) 5 (vars 175).toFinset := by
  apply compactRoot (g := grid175) (t := tab175) (dom := compactDomains175) (perms := compactPerms175) pairs175 domains175 autos175
  · intro k hk
    change k ≤ 5 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev175k5
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound175 : Lower true (vars 175) (graphGoal 175) 6 :=
  plain_low (hints := 30037) (by decide +kernel) excluded175

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound103 : Lower true (vars 103) (graphGoal 103) 5 :=
  carry_of (old := 103) (rep := 229) (swaps := [80, 113, 98]) (by decide +kernel) bound229

def grid239 : CompactGrid := (239, 8, samplesP239, samplesQ239)
def tab239 : CompactTable := (compactCount239, compactPath239, compactLive239, compactPoolIDs239, compactBucket239)
def check239 (k : Nat) := compactNode grid239 tab239 compactDomains239 compactPerms239 k
def sliceSpecs239 : List SliceSpec := [(1, 0, 238, 0, 0, 7, 7), (2, 0, 237, 0, 0, 7, 7), (8, 0, 231, 0, 0, 7, 7), (4, 0, 235, 0, 0, 6, 6), (32, 0, 207, 0, 0, 6, 6), (64, 0, 175, 0, 0, 6, 6), (0, 8, 103, 128, 4026531840, 6, 5), (0, 64, 172, 3, 255, 6, 4), (36, 0, 203, 0, 0, 5, 5), (128, 8, 103, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains239 : ∀ d ∈ compactDomains239, Slice true (vars 239) (graphGoal 239) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(238, 7), (237, 7), (231, 7), (235, 6), (207, 6), (175, 6), (103, 5), (172, 4), (203, 5)]) (specs := sliceSpecs239)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound238
    · exact bound237
    · exact bound231
    · exact bound235
    · exact bound207
    · exact bound175
    · exact bound103
    · exact bound172
    · exact bound203
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
theorem c239k6p0 : chartBlock (check239 6) 0 5 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev239k6 : chartBlock (check239 6) 0 5 = true :=
  c239k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c239k7p0 : chartBlock (check239 7) 0 6 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev239k7 : chartBlock (check239 7) 0 6 = true :=
  c239k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c239k8p0 : chartBlock (check239 8) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev239k8 : chartBlock (check239 8) 0 1 = true :=
  c239k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded239 : Impossible true (graphGoal 239) 8 (vars 239).toFinset := by
  apply compactRoot (g := grid239) (t := tab239) (dom := compactDomains239) (perms := compactPerms239) pairs239 domains239 autos239
  · intro k hk
    change k ≤ 8 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev239k6
    · exact lev239k7
    · exact lev239k8
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound239 : Lower true (vars 239) (graphGoal 239) 9 :=
  plain_low (hints := 30037) (by decide +kernel) excluded239

def grid119 : CompactGrid := (119, 7, samplesP119, samplesQ119)
def tab119 : CompactTable := (compactCount119, compactPath119, compactLive119, compactPoolIDs119, compactBucket119)
def check119 (k : Nat) := compactNode grid119 tab119 compactDomains119 compactPerms119 k
def sliceSpecs119 : List SliceSpec := [(1, 0, 118, 0, 0, 7, 7)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains119 : ∀ d ∈ compactDomains119, Slice true (vars 119) (graphGoal 119) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(118, 7)]) (specs := sliceSpecs119)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound118
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
theorem c119k7p0 : chartBlock (check119 7) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev119k7 : chartBlock (check119 7) 0 1 = true :=
  c119k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded119 : Impossible true (graphGoal 119) 7 (vars 119).toFinset := by
  apply compactRoot (g := grid119) (t := tab119) (dom := compactDomains119) (perms := compactPerms119) pairs119 domains119 autos119
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
    · exact lev119k7
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound119 : Lower true (vars 119) (graphGoal 119) 8 :=
  plain_low (hints := 1348) (by decide +kernel) excluded119

def grid255 : CompactGrid := (255, 11, samplesP255, samplesQ255)
def tab255 : CompactTable := (compactCount255, compactPath255, compactLive255, compactPoolIDs255, compactBucket255)
def check255 (k : Nat) := compactNode grid255 tab255 compactDomains255 compactPerms255 k
def sliceSpecs255 : List SliceSpec := [(1, 0, 254, 0, 0, 10, 10), (2, 0, 253, 0, 0, 10, 10), (4, 0, 251, 0, 0, 10, 10), (8, 0, 247, 0, 0, 10, 10), (32, 0, 223, 0, 0, 10, 10), (64, 0, 191, 0, 0, 10, 10), (16, 0, 239, 0, 0, 9, 9), (0, 8, 119, 128, 4026531840, 9, 8), (128, 8, 119, 0, 0, 8, 8)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains255 : ∀ d ∈ compactDomains255, Slice true (vars 255) (graphGoal 255) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(254, 10), (253, 10), (251, 10), (247, 10), (223, 10), (191, 10), (239, 9), (119, 8)]) (specs := sliceSpecs255)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound254
    · exact bound253
    · exact bound251
    · exact bound247
    · exact bound223
    · exact bound191
    · exact bound239
    · exact bound119
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
theorem c255k9p0 : chartBlock (check255 9) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev255k9 : chartBlock (check255 9) 0 1 = true :=
  c255k9p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c255k10p0 : chartBlock (check255 10) 0 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev255k10 : chartBlock (check255 10) 0 3 = true :=
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
    · exact lev255k9
    · exact lev255k10
    · exact lev255k11
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound255 : Lower true (vars 255) (graphGoal 255) 12 :=
  plain_low (hints := 30020) (by decide +kernel) excluded255
def winningGates : List Gate := [⟨.or,[3,4]⟩, ⟨.or,[2,8]⟩, ⟨.or,[0,9]⟩, ⟨.and,[7,10]⟩, ⟨.and,[6,4]⟩, ⟨.and,[5,2]⟩, ⟨.or,[5,6]⟩, ⟨.or,[4,14]⟩, ⟨.or,[0,1]⟩, ⟨.and,[15,16]⟩, ⟨.or,[11,12]⟩, ⟨.or,[13,17]⟩, ⟨.or,[18,19]⟩]
theorem winningLegal : ∀ g ∈ winningGates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [winningGates,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem winningCorrect : ∀ x : Fin 8 → Bool, Circuit.eval ⟨winningGates,20⟩ (List.ofFn x) = edge8 x := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem asListed : ∀ x : Fin 8 → Bool, edge8 x = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by decide +kernel
end PEqualNP.Outside.L_meta_15010

open PEqualNP.Outside.L_meta_15010 PEqualNP.CircuitLowerBounds
theorem PEqualNP.Outside.L_meta_15010 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
