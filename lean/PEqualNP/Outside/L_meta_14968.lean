import PEqualNP.Defs





namespace PEqualNP.Outside.L_meta_14968
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
def graph : Sig := (BitVec.ofNat _ (limbs64 [0xfffffffffffffffe,0xfffffffffffefffa,0xfffffefefffffefe,0xeeeeeeeeeeee0000,0xfffffffffffffffe,0xfffffffffffefffa,0xfffffefefffffefe,0xeeeeeeeeeeee0000]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
 (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 5 && x 7)
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
 (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 5 &&& x 7)
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
 (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 5 &&& x 7)
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
 (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 5 && x 7)
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

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([4, 4, 6, 7, 0, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([4, 4, 6, 7, 0, 0, 0, 0] : List Nat).getD i.val 0))

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

def samplesP114 : Nat → Bits
  | 1 => ~~~(0x10080c0018a09944 : Bits)
  | 4 => ~~~(0x50212e0431722b8 : Bits)
  | 5 => 0x5cfab22ddbd22f30
  | 6 => 0x75ff5cce7fa59bcc
  | _ => 0

def samplesQ114 : Nat → Bits
  | 1 => ~~~(0x6fbff7feddffffd6 : Bits)
  | 4 => 0x58112861048a542
  | 5 => 0x2325345c892baf10
  | 6 => 0xa14212844a30a84
  | _ => 0

def compactPerms114 : Array (List Nat) := ([[], [100]] : List (List Nat)).toArray

def compactDomains114 : Array (Sig × Nat) := ([(subcube 32 0, 4)] : List (Sig × Nat)).toArray

def compactWords114 : Nat → Nat
  | 0 => 0x4f
  | _ => 0

def compactCount114 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath114 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive114 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords114 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs114 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords114 (5 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords114 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket114 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP226 : Nat → Bits
  | 1 => ~~~(0x10280c0024907a18 : Bits)
  | 5 => 0xdfefdd7f67f27b9e
  | 6 => ~~~(0xc049d464072709e : Bits)
  | 7 => 0xbbfcbc3efc907ed8
  | _ => 0

def samplesQ226 : Nat → Bits
  | 1 => ~~~(0xedf6f7db7ddbdf3a : Bits)
  | 5 => 0x2110121221031912
  | 6 => 0xc54545908939f20
  | 7 => 0x448d41a85434a6c8
  | _ => 0

def compactPerms226 : Array (List Nat) := ([[], [118, 81]] : List (List Nat)).toArray

def compactDomains226 : Array (Sig × Nat) := ([] : List (Sig × Nat)).toArray

def compactWords226 : Nat → Nat
  | 0 => 0xf
  | _ => 0

def compactCount226 (k : Nat) : Nat := match k with
  | 3 => 1
  | _ => 0

def compactPath226 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => 0
  | _ => 0

def compactLive226 (k : Nat) (i : Nat) : Nat := match k with
  | 3 => readCompactBits compactWords226 (0 + 4*i) 4
  | _ => 0

def compactPoolIDs226 (k : Nat) (i : Nat) : List Nat := match k with
  | 3 => let v := readCompactBits compactWords226 (4 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords226 (4 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket226 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP242 : Nat → Bits
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0x2100014025,0x43c08088402ac31c,0x9222871828850429,0x938d89295ee699c4])) : Bits)
  | 4 => ~~~((BitVec.ofNat _ (limbs64 [0x8500209cc,0x542d40019083a4c1,0x1891b4afb1100394,0xc6346eb1ba3362f8])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0x7dcfb77fa7,0x77245faff7baa7d3,0x95b2f48abfb75ba5,0x92bf68a13aebc8f0]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x6f5fdbdfdd,0xc6c99fffd9efc8fc,0x3a1f93351bdfa4f9,0xcf3c8718c477b30c]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x7a3fefe96c,0x59f01fd9fef3f70d,0xdae1a4083dfdc71e,0xf7c508211bb67cc0]))
  | _ => 0

def samplesQ242 : Nat → Bits
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0x5efeffbdfe,0xbe7f7bfafbbf7ebb,0xfefbf9ffefd7edaf,0xdfdfddfdf6ff9fd6])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x852421844,0x429582028204423,0x384290a024c66022,0x11021069608c8d02]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x230c68018,0x843128282054420,0x9240710443834901,0x809090b822698890]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x10a414a020,0x3016231041852810,0xc23060488b118088,0xc0c899082731204]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x5c8107a82,0x820ced481010a957,0x693688131c7c8404,0x42412b43c9967440]))
  | _ => 0

def compactPerms242 : Array (List Nat) := ([[], [100]] : List (List Nat)).toArray

def compactDomains242 : Array (Sig × Nat) := ([(subcube 128 0, 5), (subcube 0 128, 5), (subcube 16 0, 4), (subcube 64 0, 4), (subcube 32 0, 4), (subcube 32 128, 4)] : List (Sig × Nat)).toArray

def compactWords242 : Nat → Nat
  | 0 => (limbs64 [0x7fa2dfebaf,0xf82be51a00a024ca,0x3ecc4ff8ff12c3fc,0x7f8ff02e28c7ffff,0xd08f00500680d4bf])
  | _ => 0

def compactCount242 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 3
  | 4 => 1
  | _ => 0

def compactPath242 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords242 (26 + 12*i) 12
  | 4 => let v := readCompactBits compactWords242 (227 + 12*i) 12
    (readCompactBits compactWords242 (215 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def compactLive242 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords242 (0 + 5*i) 5
  | 5 => readCompactBits compactWords242 (62 + 6*i) 6
  | 4 => readCompactBits compactWords242 (239 + 7*i) 7
  | _ => 0

def compactPoolIDs242 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords242 (20 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords242 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits compactWords242 (88 + 5*i) 5
    let n := v >>> 3
    let bits := readCompactBits compactWords242 (80 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 4 => let v := readCompactBits compactWords242 (246 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords242 (246 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket242 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords242 (103 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 10)
    let v := readCompactBits compactWords242 (105 + 11*off) 11
    if v >>> 3 == (i/104729)%251 then [v &&& 7] else []
  | 4 => let d := readCompactBits compactWords242 (248 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 5)
    let v := readCompactBits compactWords242 (250 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | _ => []

def samplesP230 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0x6f3fdfed8e,0x7dc67fdfb9f4f3ee,0xa2be2069cdff73b8,0xc9ef3e31019c761c]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x58018018b,0x64268006211e88c6,0x229c3669c50032a1,0x8cd3be31363256bc])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0x5eefffb3c9,0xeab2ff6e7feb9cd7,0x735e1621f7f6be7b,0x7d38e0037a3d8b8]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x830412044,0xe8c3804800e19021,0xe17e1e278016f17a,0x1238e0cff8439f8])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x7d9ff97f77,0xe461fcffe7df8821,0xedfdde067f1ff1e7,0xbc30800cfe763de0]))
  | _ => 0

def samplesQ230 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0x10c8320261,0x208c48410b22054,0x45111104409d2090,0x40a11924910c3414]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x581380808,0x4424e20904100a16,0x8119a40120c70902,0x21080da0c5892842]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x2114082c12,0x1045302208441b02,0x804cc0c234629009,0x24006d046a1c888]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x77cf3f5bfb,0x5f7ce6ff7cfa6ef7,0xed9bb5ff60dff9ff,0xe7eb7dacf58d3dfe])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x262428280,0x91a0c506023a048,0x562000384b184064,0x8401900718561520]))
  | _ => 0

def compactPerms230 : Array (List Nat) := ([[], [114, 101], [33, 117], [33, 82, 101, 118], [81, 118], [81, 98, 117, 118], [97, 82], [97, 114, 101, 118], [113, 114, 117, 118], [113, 98]] : List (List Nat)).toArray

def compactDomains230 : Array (Sig × Nat) := ([(subcube 2 0, 4), (subcube 4 0, 4), (subcube 32 0, 4), (subcube 64 0, 4), (subcube 128 0, 4)] : List (Sig × Nat)).toArray

def compactWords230 : Nat → Nat
  | 0 => (limbs64 [0x2d0bfc,0x3fc0ee7453fc0098,0x9602be51a00ff827,0x20751ff05a237e5d,0xf38b4ff818c5fe08,0x37f82d8952e1006,0xfffd00900688d11f])
  | _ => 0

def compactCount230 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 2
  | 4 => 1
  | _ => 0

def compactPath230 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords230 (26 + 12*i) 12
  | 4 => let v := readCompactBits compactWords230 (287 + 12*i) 12
    (readCompactBits compactWords230 (275 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def compactLive230 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords230 (0 + 5*i) 5
  | 5 => readCompactBits compactWords230 (50 + 6*i) 6
  | 4 => readCompactBits compactWords230 (299 + 7*i) 7
  | _ => 0

def compactPoolIDs230 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords230 (20 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords230 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits compactWords230 (64 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords230 (62 + 2*(v &&& 1)) (2*n)
    compactIDsFromBits bits 2 n
  | 4 => let v := readCompactBits compactWords230 (306 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords230 (306 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket230 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords230 (68 + 3*(i % 4)) 3
    let off := ((i/4 + d) % 15)
    let v := readCompactBits compactWords230 (80 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 4 => let d := readCompactBits compactWords230 (308 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 8)
    let v := readCompactBits compactWords230 (310 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | _ => []

def samplesP118 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0xdeffbfef3f77,0x71f7fdbfe7f3caef,0xdf0f1d8be7dfbc77,0x267dccf1bc7732ec]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x790300316e3,0x2ff4009c021e20a6,0xdf03fd8fc2083c58,0xc2331cf1ff0c2bfc])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0xf74ff3dfcee1,0x1e33e7ff1ffe2161,0xff70ec04fe3ffcb8,0xde0f340077cd1d1c]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xbd8ffd7330ea,0xe903fafcfecc749e,0xc78e10833ffb5f4f,0xc1f3087008fce8c0]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x104001402860,0x5130002004e04049,0xc70c1c83c4131c27,0x44d0c703c7510cc])) : Bits)
  | _ => 0

def samplesQ118 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0x210460008080,0x8402041080900014,0x440804001029014,0x20280049042210a4]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x79174091245,0x2fe331263014ac17,0x4e6528967197c6a1,0x50c4816d15f39402]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x8b80621230e,0x218c638425248528,0x48863390643c6489,0x4485250059c50d08]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x4272126c4614,0x327dc14c60626b2b,0x3b260b8fee90c83,0xc1941436c8dce840]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0xefbf7fbbf7df,0xbfef77fef5fdbdff,0xfeeffbfef5bffebf,0xf5fdafed7ff79dee])) : Bits)
  | _ => 0

def compactPerms118 : Array (List Nat) := ([[], [82, 97]] : List (List Nat)).toArray

def compactDomains118 : Array (Sig × Nat) := ([(subcube 4 0, 5)] : List (Sig × Nat)).toArray

def compactWords118 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount118 (k : Nat) : Nat := match k with
  | 5 => 1
  | _ => 0

def compactPath118 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => 0
  | _ => 0

def compactLive118 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => readCompactBits compactWords118 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs118 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let v := readCompactBits compactWords118 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords118 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket118 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP244 : Nat → Bits
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x91000c4319358,0x900c420139562d85,0x850739090222225a,0x86cd6525762f23ac])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x6e5ffbf678cb38,0x87ffe6f3f3ce6fc3,0xa4632107ceff26d9,0xe3cbc42131ea3784]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x7d8fecffb137c4,0x17fe7f7dbc77b19c,0xc784180ff777db1e,0x84fd210447ade928]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x204048203028a0,0x70100440862e139a,0x820498ba0444c185,0x81c3231ccee00d78])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x7b7fdfedf7b8fa,0x77fddfcfcf3e1fbf,0x9b1c98bf3feee1e7,0x9fc7231ccef70f78]))
  | _ => 0

def samplesQ244 : Nat → Bits
  | 2 => (BitVec.ofNat _ (limbs64 [0x9140244a29148,0x9195082a105a8508,0x8551314a4c1540d,0x5052088895c09812]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x11a10458c3148b,0x5f060c831122d46e,0xd85429e0eb54689,0x82508b2d11e23580]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x2708f044e1818,0xeccc384201784187,0x2ff0634f256c41b,0xf041e0878ce920]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x5fbdd6dfefdfdf,0xdf9f7debfb7fdd7e,0x3dd777feaef5f7bf,0xd7f39bbdf5e2bdfa])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x4882038004205,0x2204100c4803260,0xc500204309282120,0x501260708330648]))
  | _ => 0

def compactPerms244 : Array (List Nat) := ([[], [84, 118]] : List (List Nat)).toArray

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
  | 1 => (BitVec.ofNat _ (limbs64 [0xfbe7ffedf7f3debd,0x47fda8cecdfffefc,0xffeeff5f5f8edf63,0xf27b7ad4fd827e64,0x1fdecf50711765bf,0xbfbe9f63d9e1ff5f,0x2ff0bcf7e683f593,0xafe065768b703ca,0xfc29c0ea0947b721,0xb995dfdaecf63b1f,0x543827d2ce36c30,0xe4600ac6e36460ec]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x20330001860b060a,0x4566eecb38500080,0x4004391b1804ce00,0x5f402c00f9e05bce,0x9f8b628df1d777c0,0x808842e01307630,0x2b8036803fcb82a3,0xe0d177c322bf83e9,0xfc01feef8d47c460,0x33960801c47e2d38,0x6d81ee32b1f3ee38,0xf67ec31f12a5f5fc])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0xbebcffdfef9f8ba6,0xfce625c1b28fffe3,0xdf3ffbd8f8fdff3e,0x3fdc65c1e47838dc,0x79832187b0c062bc,0x7dfffefe7778f1fc,0x5f8ceff87c1d8b8d,0xe1397dc8607da1e0,0xe1c04e640401bbf8,0xefae3ae7f4785c68,0x63b33e0e73208408,0xe2263f134193d01c]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xf71eff73ffef2d7b,0xe7127e2d090ff9ff,0xefd77cbfbf4f2ea3,0xcde4ff2afae2414b,0x9e2d36a84811117f,0xde7deffda19efeb0,0xb3ffb3b799620662,0xf4c187a71736c235,0xfe29308381067cfe,0xb6dbfcdd5377a497,0x78804df2b0d06a00,0x1058f9da1ea885c0]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x284024040070834,0x228121c5c9800000,0x8c024604f80b3e23,0xa0c0500006e22441,0x7f84a5727031f1c0,0x1430085000c089d0,0x178089b7c037855f,0xe02e8fc45d778016,0xfc2871e3833fd3a0,0x8c8814de43f612df,0x13821e4d70f07e07,0xf1f9dfc2616acfcc])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0xeef3feffde7f765e,0x3be9c3d3784ff79f,0xfcffff27f833fedd,0xffc39c3f13e58783,0xe780e07ff4209063,0xfffbfdfe0ef70ff3,0xff835f8f03ff807f,0xe006fbc09fcb9c1f,0x1c16310182385fe7,0x5ffe053fcb8e03f8,0x9f8cfe01d0101207,0x1199d72d306fcf00]))
  | _ => 0

def samplesQ246 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0x41808020c880140,0x3002062122018050,0x82020b221110812,0x110800022214000a,0x4000300400880252,0x4a2810048004500,0x2400424a2441009,0x2048102201040450,0x9110280040200500,0x885059028440904,0x140002900414121,0x21280280a16400a4]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x203340088e22120a,0x524c6893852c406,0x28848bb4a014c18,0x9401049840c0c880,0x94924298a0d6507b,0x113342151402984a,0x9a48012a00a22d,0x4c0221234c100890,0xd99c9243140cba14,0xc2992d839115201,0x322804c4480461a2,0x41a2bcc0c9580202]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x41431020b0303409,0x229581a0d7e0804,0x901c09040a8a41c0,0xe405aa0941828920,0x80b88230c7341d20,0x794d0a44314210d0,0x4890c2414808a152,0x4512a60ca6d108a1,0x209129a1208faa0,0xc7223a0655104449,0x228224842224160a,0x52423d034092d008]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x8e1046c0210d00c,0x86581d2d418602c,0x409190d4080268c,0x620056d500899a00,0xa1d003518062ec2d,0xc8146c0c100e3240,0x11b0401344880666,0xb1001854a490004,0x6ec716023819b81e,0xb208e84d43324003,0x6a000d9401202ad8,0xc0f85a0e888440]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0xfd7bdebbbffaffcf,0xff7fdebb3f7fcdfe,0xbebffbbfffbbcdfb,0xfd1fafbbffdfdbfe,0xf5fffbfdeffe5f7b,0x7dffcb5f7ddfffda,0xfffacffffb5df37f,0xfdfef72ffff73df9,0xdbbdfedf7ffdffb4,0xcfafbfde7fff5fdf,0xffea7ffd7aef77af,0xf3febfc3e9fedfee])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x110c810270800880,0xc012382403a51180,0x20028440215e1142,0x1eca8022c000054,0x508000b090380,0x26c891e200910000,0xa400018880661990,0x20499e58a184c663,0x400401c005e1,0x41d6052280880090,0x8400520010519401,0x3e09032530274900]))
  | _ => 0

def compactPerms246 : Array (List Nat) := ([[], [82, 97]] : List (List Nat)).toArray

def compactDomains246 : Array (Sig × Nat) := ([(subcube 4 0, 7), (subcube 16 0, 7), (subcube 32 0, 7), (subcube 128 0, 6), (subcube 0 128, 6), (subcube 2 0, 5), (subcube 64 0, 5)] : List (Sig × Nat)).toArray

def compactWords246 : Nat → Nat
  | 0 => (limbs64 [0x6244ef389,0x302013fc3fc3d1f1,0x17e87dcffc0e80f2,0x7fc162c71413aebf,0xfbbbbbbd9301cc27,0x3084c21306011010,0x109a1e3ff1fe3fc,0x5b92aa5529540345,0x2107986432015976,0x89873462105fffff,0xc02202002511a23f])
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
  | 6 => let v := readCompactBits compactWords246 (346 + 14*i) 14
    (readCompactBits compactWords246 (310 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 5 => let v := readCompactBits compactWords246 (642 + 12*i) 12
    (readCompactBits compactWords246 (618 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | _ => 0

def compactLive246 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => readCompactBits compactWords246 (0 + 6*i) 6
  | 7 => readCompactBits compactWords246 (63 + 7*i) 7
  | 6 => readCompactBits compactWords246 (416 + 8*i) 8
  | 5 => readCompactBits compactWords246 (654 + 9*i) 9
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
  | 6 => let v := readCompactBits compactWords246 (471 + 5*i) 5
    let n := v >>> 3
    let bits := readCompactBits compactWords246 (456 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits compactWords246 (663 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords246 (663 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket246 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let d := readCompactBits compactWords246 (231 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 7)
    let v := readCompactBits compactWords246 (233 + 11*off) 11
    if v >>> 3 == (i/104729)%251 then [v &&& 7] else []
  | 6 => let d := readCompactBits compactWords246 (496 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 10)
    let v := readCompactBits compactWords246 (498 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | 5 => let d := readCompactBits compactWords246 (665 + 1*(i % 1)) 1
    let off := ((i/1 + d) % 1)
    let v := readCompactBits compactWords246 (666 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | _ => []

def samplesP254 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0x7fea5cdd48bfa883,0xf51ff562c1e7739f,0xd381ff015817ff8a,0x66e82bff0ea802bf,0x5f00df3006fd1484,0x3dfbd041592a8ee8,0x207c96bd0817dad1,0xbbf00002dae38003,0xe44011c18fe0779d,0x83e2e7ea5421dfe1,0xc743cc7fc1fda17f,0xb11353299e1f007c,0xe0ac711139007879,0x807f3c18e79f0737,0xc3c30c00150639,0xc36379c1a85983b0]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x3b3fe7f131403fff,0x8ff664d01206fff3,0x55ce0e37fffc154f,0xc00bfe5e0102d440,0x1dffc896f90001f4,0xa2e9c61a000eb99f,0x4080204057ea0334,0x206fffd0c001c,0x800e20e7003ffcf,0xff37fd4c00ffe1f5,0x49fd1b037f99545f,0xf38c6bff71c06c98,0xd200f8c4012fc280,0x3ff3104706c03008,0xd1c1c30033ddf1f,0x20701746b2a02805]))
  | 3 => (BitVec.ofNat _ (limbs64 [0xc4c107eebbffcc7c,0xfe87b23fe793c1f,0x68ff11c9f8609a0b,0xff77c3a006210fe1,0x62340508ff79160b,0x42021038e9d14000,0x1f01797728800802,0x1d2df97c00001f00,0x300300004fff7,0xfefff732fb384dc9,0x7df3ab7c9e2fffa3,0x8cad96fe01d39300,0xcf3010bf0d61078,0xcf802ca7e9004800,0x72000000703feefe,0xde006ea81518000a]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x80fdf80fc478f07f,0xf0007ffc1fffc021,0x7f0fe1fe007f1ff4,0x3f9c7c03f801f80f,0x80c87a0f007fe803,0xc0fc23e70e2070e0,0x1ffe80388303f407,0xe030ff80001380e0,0xe3800c400060fe7e,0xf3bf1f7d3fc0b1fe,0x8e15b4f027ce1fec,0x4f5ffcc18e22039f,0xf04860e3ef8638f,0x3c0f8d06100c3,0x23c0c40c3eb9a9,0x3389c120c7274070]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x7f145cd2b73f5703,0xf51f8a9d21988c5e,0xac71fefea797e075,0xa6f7abfcf15602b0,0xa000a0c00682eb78,0x3d042c4156d50e17,0xc07c9682f4142529,0xbbcf0002da006003,0x107c01800f98effa,0x7fdbfe9597dede1e,0x36aa73fff9f2408f,0xbee2ac286e1cfc63,0x10ab76e106000476,0x707cc318181e8034,0x8000200b80fa77e7,0x80ed001f489a1700]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xbb3fbb2ece803ffc,0x7ae99b2fec06ffec,0xaa300e37ffebeab0,0x190bd5a1fefd2900,0x1dff3769000001f4,0x9f1639a4a00eb760,0xbf03490057fdfcca,0x440206fd27f000e0,0xf80fc0f8003d82f,0x3cccfab3e8ff3e0a,0xb1fee4837e66aa50,0x4c706bd680206ce7,0x2d508f3ac12fbd00,0x3f8cefa006e037c0,0xde01fc00c0a90d6,0xdc1e96b74244c0c5]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xc4c2a3317fc7c380,0xaf784dffff903e0,0x97fef1c8078865ff,0xd9f4145801def55e,0xe20300f7f986fe0b,0x4001cf9eb7f1411f,0xe0836fcfa86803fc,0x46ddf901240c7f1c,0x103f0230701ca1f1,0xcd7d08cfef072237,0xfa0c5f8c8011ffb0,0x73ff951671ed9300,0xf35f08f4ced18f87,0xc00013473900c808,0xf21c2033f3e16940,0x2d96a8583de73c0a]))
  | _ => 0

def samplesQ254 : Nat → Bits
  | 1 => (BitVec.ofNat _ (limbs64 [0x1022040010248821,0x4205140200020109,0x84890000000180,0x2041214500a41204,0x920040441050800,0x948801409450400,0x4820c30000089141,0x300452180404890,0x4000802044020505,0x20808800200921,0x42010c4a8014a01a,0x20015320088b000c,0x6080410009000048,0x842a3000020a0320,0x2a85402480050410,0x41407840a8500290]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x3808c144b0762173,0x9b961242002e9710,0x702e237166080542,0x8a13518951814382,0x4b224462c2ca0d2,0x202242980d1c068d,0x514002641224301,0x8a882e1568c53c38,0xc17028041e27ff8f,0xe937cc4001ac40f4,0x98519131789404c,0xb48c69b923c36098,0xc40292c400630262,0x1e71204246001030,0xc88903446bddf1d,0x20601504b2800804]))
  | 3 => (BitVec.ofNat _ (limbs64 [0xd9454b0c193f2435,0x87ae3a3754e2b102,0x306611d2eaa5b35a,0x1815138033114504,0xc8c350215e186633,0x2c668a40805a2043,0xb2c7ab55192aa44,0x481c582c997f0d19,0x5315054d068ff7f7,0xbefdf72223184d4d,0x2d50837c1aaf9903,0x8ca58ad500d3a529,0x4c43804352c61270,0x46b0652ee20c4282,0x30011a81623feefe,0xda0066a814180008]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xdc594580406500,0x110862d00da89420,0x52413240207c0a72,0x8a08520a50006443,0xe600489928a8a258,0x803044e1f0107965,0xa594100801a06c0c,0x83228144a152023,0xd432244103cf85a,0xc31e1f443d08a0d6,0x8414a19027c215e0,0x870eac01a2100383,0x604920436424302,0x500100ba4041580b,0x8028a0c8043ab929,0x2281812047234020]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x894c08c2835b1714,0xb0aaa07444980c06,0x646276124aad2211,0x86344a9a3a1860a0,0x2014a1ca189864b4,0x8430000846104a8b,0x838e088a21000022,0xace21a8c3f302569,0x55745032e9eaf8,0x7fcb7a1093de9646,0xa2333562c04085,0x9e660808665425a1,0x23366652000036,0x7295452808250014,0x9560001900fa73e7,0x802d000f408a1100]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x830020004109000c,0x60012cc0004082,0x810000619836000,0x48020080a0830,0x4d932002000005,0x4204380202228000,0x22051bc140032,0x6445008005200304,0x200c040001800020,0x14c02033c0431208,0x306a400048200a00,0x4050004600000c60,0x101000ac008a810,0x180cf0000a080c4,0x1400f00314000c2,0x9c1e029300048041]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x400003004800080,0x22010040,0x8100000800000004,0x4180040400261851,0x3080a1001010808,0x4308342730219120,0x600081408c0c1418,0x101010000008000,0x80008280000000,0x8d4c012000,0xd208448080102630,0x4110140210201000,0x1018081000100481,0x111028949,0x204654091000000,0x592885009652402]))
  | _ => 0

def compactPerms254 : Array (List Nat) := ([[], [82, 97]] : List (List Nat)).toArray

def compactDomains254 : Array (Sig × Nat) := ([(subcube 8 0, 9)] : List (Sig × Nat)).toArray

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
  | 0 => ~~~((BitVec.ofNat _ (limbs64 [0x2000008,0x470e200082208541,0x6873049c2a42251,0xc3a48ce98a7b3648])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0xfabf75f,0xd64d744fbb7fdceb,0x56cba44568ff6b77,0x71aaa8a3186d750a]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xef3fbee,0xedae488fdff2ff0d,0x9d95791892efb04b,0xdef7854ca2f35ac0]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xf57edfb,0xb3fb12ff7afe570,0xe766be6141f5ffd9,0xab644aa149bba438]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x4300142,0x882d5de011024c28,0xd540af757941094b,0x38622ba779a14dba])) : Bits)
  | _ => 0

def samplesQ241 : Nat → Bits
  | 0 => ~~~((BitVec.ofNat _ (limbs64 [0xdffbfff,0xbdf9ffffebebffff,0xfffffff7bffff3fb,0xf7fcffffffffff5c])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x560990,0x99001b320029a72,0x1047480136e4042,0x6108016b144d5500]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x10d1c10,0x1001a71a88006042,0x19e646460069a009,0x9480096223b15a00]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xa83602,0xa4400e4c01a10080,0x9cf380108c91b190,0x640e9023b2a018]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x4308382,0x2858e542480ab0,0x8411b12120965220,0x210c699144ea044]))
  | _ => 0

def compactPerms241 : Array (List Nat) := ([[], [117], [84, 118], [84, 101, 118], [100], [100, 117], [116, 117, 118], [116, 101]] : List (List Nat)).toArray

def compactDomains241 : Array (Sig × Nat) := ([(subcube 16 0, 5), (subcube 32 0, 5), (subcube 64 0, 5), (subcube 128 0, 5), (subcube 80 0, 4), (subcube 160 0, 4)] : List (Sig × Nat)).toArray

def compactWords241 : Nat → Nat
  | 0 => (limbs64 [0x1fe02c,0xbff8004cfa40575c,0x83fc05e3a7a300b2,0x66956c240c4580bd,0x2bff052a50e562c4,0x83e43ca83fe09e6f,0xf82babfe0ff06543,0x255fe01b0110025e,0x3e5c4c3b311cc34a,0x2c014a24010a0422,0xff006461e277f80f,0xf00be64c4d7f801a,0x3f683bfc030a9ff0,0x68c28264021d964,0x1e57fc07f80b1268,0xa4a687ca03b939fe,0x3855b9b5c43bfe0,0x90b98beb58dfe00,0x916ff80ff0098594,0x8f1194b523fe000e,0x57f800f1890dbfc0,0x18279462650b5a7f,0x5b31c37fe0166239,0x5c078b843fc006b,0xf6d4b56dd9979987,0xcc47342939a2047b,0xb743607fc0087031,0x3d391383088c90,0x20b960c902224064,0x265c264857efdfb,0xfdebfdbf7feb9408,0x5059452511946651,0x88446510944650e0,0xa11200ff83c1a79,0x4d61bfdbfc0f05ff,0x7c1d7dffe0a20a3,0xdd4a56ab3b4ff800,0x1616c5504c192a00,0xc190a0189207fffe,0x845802803858d11f])
  | _ => 0

def compactCount241 (k : Nat) : Nat := match k with
  | 7 => 1
  | 6 => 3
  | 5 => 10
  | 4 => 3
  | _ => 0

def compactPath241 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => 0
  | 6 => readCompactBits compactWords241 (29 + 12*i) 12
  | 5 => let v := readCompactBits compactWords241 (455 + 14*i) 14
    (readCompactBits compactWords241 (419 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 4 => let v := readCompactBits compactWords241 (1992 + 14*i) 14
    (readCompactBits compactWords241 (1920 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | _ => 0

def compactLive241 (k : Nat) (i : Nat) : Nat := match k with
  | 7 => readCompactBits compactWords241 (0 + 5*i) 5
  | 6 => readCompactBits compactWords241 (65 + 6*i) 6
  | 5 => readCompactBits compactWords241 (595 + 7*i) 7
  | 4 => readCompactBits compactWords241 (2034 + 8*i) 8
  | _ => 0

def compactPoolIDs241 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let v := readCompactBits compactWords241 (23 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords241 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 6 => let v := readCompactBits compactWords241 (159 + 9*i) 9
    let n := v >>> 5
    let bits := readCompactBits compactWords241 (83 + 4*(v &&& 31)) (4*n)
    compactIDsFromBits bits 4 n
  | 5 => let v := readCompactBits compactWords241 (713 + 7*i) 7
    let n := v >>> 4
    let bits := readCompactBits compactWords241 (665 + 4*(v &&& 15)) (4*n)
    compactIDsFromBits bits 4 n
  | 4 => let v := readCompactBits compactWords241 (2058 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords241 (2058 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket241 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let d := readCompactBits compactWords241 (186 + 3*(i % 4)) 3
    let off := ((i/4 + d) % 17)
    let v := readCompactBits compactWords241 (198 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 5 => let d := readCompactBits compactWords241 (783 + 4*(i % 18)) 4
    let off := ((i/18 + d) % 71)
    let v := readCompactBits compactWords241 (855 + 15*off) 15
    if v >>> 7 == (i/104729)%251 then [v &&& 127] else []
  | 4 => let d := readCompactBits compactWords241 (2064 + 3*(i % 8)) 3
    let off := ((i/8 + d) % 33)
    let v := readCompactBits compactWords241 (2088 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | _ => []

def samplesP249 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x5ffdffff,0xddfdf6f8fdf73ee3,0xdbabfff9efff7dff,0xd9bfd3beb9db60ff,0x6dffbf197640ff99,0x873e1fb3fdb9be7d,0xfef3ca7fa77f80bd,0xdf3f337f921ffd25,0xaba839dfa60fcb46,0xc293cf609cf3ae0a,0x579fc6f0bfd3330b,0xea839e35433ca945,0xc13b541630ce66dc]))
  | 3 => ~~~((BitVec.ofNat _ (limbs64 [0x2c3c060,0x5021e9484da0288f,0x3ff7f000060824c0,0xa9089328419a583c,0x41e1dc5fa390df64,0x6c3f3bffffbc0020,0x8040d02b36623090,0x1610c2437f5f745d,0x8ade3d17452d6496,0xc0d3ffff9efe0088,0x81a044a410e22e4a,0x740d17f3f3bfafcf,0xef3fc019d50dbffc])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x7babbff2,0xffedaf4ede7ad92a,0x3d524ff77ffbefcf,0xbe39bf5b5ba7dc7e,0x8fb3c4c78636327a,0x64db38261805ffef,0xbdcffb9f569e73da,0xdef2eeb363db0ed8,0x967b2523992c2e30,0xdcc0a0591a2179bd,0xd5f4fd7d6ba2cec2,0x794f70c2ce920708,0x681c3a8d59b59428]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x6ff23fff,0x7e77d98f1d9da04c,0x1eec0ffffe5cfff3,0xefc1e3e3e5fc7f9f,0xf1c3f81e1988cce4,0x381c21c86201d3ff,0xcffff467ffe7fcef,0x2fc3c3c3fc63f01f,0x43d43e0c4030f487,0x2083138600cdffcf,0xaee0e79fdc1c1c0c,0x740c1f7fb3c10883,0x8621bf19a744ab00]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x77577f7f,0xf7bbe9f7e3e1429f,0xa0b51fff97bff7fe,0x23fe3fbc47db9fe8,0xd3fc00f9e1b50f64,0x6f21de048195fdf3,0xfbfdb5ea7f797f32,0x363cff7c6d9c20c5,0xa857c9d15dcf24be,0x4b502c198203f5fb,0xa97f3eaeb0e32df9,0x957105b2bc26a608,0x290467f1cd0b50e0]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x1300012,0x40180869051126a,0x98a8500100104102,0x2b1239201c104ca,0x8193a09954242ef8,0x27181da6f9941041,0x8812046471d402a,0xe222331e09ba885,0xa37129c9980eae26,0x4ad3af599ae3250b,0x454a618af931d89,0xf9431c368e16af09,0xe93d769529c676e8])) : Bits)
  | _ => 0

def samplesQ249 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x20020200,0x420001030008400c,0x410040808200402,0xa40100100008008,0x4000400088050002,0x2800004400002000,0xa02001220010080,0x1900300000002200,0x300104001000,0x8920008100000400,0x618004000d00102,0x2840003040140,0x100100060042028c]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x2c3c828,0x52a56a1844a0288f,0x37d4f65443450164,0x2a52160bc8e8ca2d,0x4948894b22904a4c,0xc156737c571db95a,0x2eaa4c808328590c,0x42ab49942451bb4e,0x304cb0412c49b253,0x8dc69912b645fe27,0x661e325b2d0954a4,0xaa5448189404c550,0xb2913fc62ae24002]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x454601c,0x80323030018122d0,0xc0a590e00614880c,0x110003a044426763,0x221c03180180c380,0x5302c000e3ab538c,0x3041e40c80980300,0xc600c103917c84c2,0x6029c820e2006480,0x40c0c00060ce3838,0xd0e0e1316300cc00,0x600d08884c00588a,0x681a380859b49400]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x100dd020,0x80d82250a6a21713,0x6103f890024d5245,0x911b44d40e8a2844,0x2008dab24d24208,0xc56344338077c273,0x454154c1ca2c9140,0x420343d4a5211488,0x2a00d784952426a,0x4454a162a345fb4c,0x80c0878e8900540c,0xb4541a5c94420898,0xc220ff11a304a800]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x8a88180,0x144c06000c349d20,0x1a4a6b01904300c0,0xa089e05ea2250000,0xdc1980730181019,0x80c0018b1c408c21,0xc1bc018006603022,0x201300bc02800925,0x16d4051c013f8039,0x220c03068231c1c3,0x29071c8490023045,0x81700032b003a604,0xe0c7f184094060]))
  | 7 => ~~~((BitVec.ofNat _ (limbs64 [0x7ecffb6b,0xfbff7f7befbfff9f,0x77d7fedddf7fdfef,0xff7f5edfdffafafd,0xdb6bdfffbfdfdbdf,0xfff7f77fd77ffb7b,0x6feb7ddfeffdfbee,0xffbbfbfeed73ffde,0xbbeebffb7ddbfb7f,0xddfefbf7f7ffff6f,0xe6deb7dfafdbfdef,0xff7fdefeff5ecdf9,0xf7b5ffd7abe6feee])) : Bits)
  | _ => 0

def compactPerms249 : Array (List Nat) := ([[], [100]] : List (List Nat)).toArray

def compactDomains249 : Array (Sig × Nat) := ([(subcube 8 0, 8)] : List (Sig × Nat)).toArray

def compactWords249 : Nat → Nat
  | 0 => 0x13f
  | _ => 0

def compactCount249 (k : Nat) : Nat := match k with
  | 8 => 1
  | _ => 0

def compactPath249 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => 0
  | _ => 0

def compactLive249 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => readCompactBits compactWords249 (0 + 6*i) 6
  | _ => 0

def compactPoolIDs249 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let v := readCompactBits compactWords249 (7 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords249 (6 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket249 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP253 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x7019ea7e7f05f5c,0x4f7f3bcc60f8250e,0xbcb3ba7ab87f0234,0x53fa0e3fbd6f35c2,0x1542a7c43fdcd840,0xd49b4bfa800fd1e,0x238ba2d070b551e5,0xd569e6c8b2028583,0xc0dee0141e21fc12,0xfb95e07b1f553921,0x6d7f25072cfd07d,0xfec09270de7090c7,0x8c0e7aa63293c10f,0xec1a61500f57d518,0xa0947011e49151b8,0xc85c0e42c68e2b70]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xfd6637e539bfb057,0x1ef84d7fff01a59a,0x1fef42dc2fa537cf,0xac8c7439acf6da01,0x23cb8c7bc0060b3f,0xf412c0031c7410,0xdc7402a292dabe40,0x28c88580bddd1808,0xe200000e04e0387,0xf5dfdf7df97530ff,0xd49b7fa71fb19d70,0xbb4cf51f23ae3b09,0x108c2d4194810bf1,0x2683fe01750800c1,0x6638180030f6bec,0xfc06345951489005]))
  | 3 => (BitVec.ofNat _ (limbs64 [0xb987ebdbe319e1a3,0x77e18e8fbfde2bf3,0xe1fb3d27c7c7c8f0,0x3b723bc1d2f9e440,0x181d10090218747e,0x602e94c203b0067,0x1300bd178901298d,0xc513183f43f02074,0x4030010000b,0xeffffffede93c739,0x277dcd0b777eaf96,0xe8f5fadffc0ec472,0x873193062b7274c2,0x8041f02f0700220,0x1800040e0007fddb,0xf3983923a884000a]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x5ef99d5a1bee5ea0,0xc89ecbc390e7f4fd,0x42b0f582bf78fd34,0x6dc5cdde426fcbbc,0xeb047b23c3ca780,0xf4494b3079e48299,0xc80b9d2844b68017,0xd09406d74c024400,0xb000da081d806003,0xbd7af9e7f8bcfee0,0xfece037ccaf367aa,0xf5ba6dccce4110b8,0x6bc064be0d0fbe0c,0x23e200b388cb2006,0x81101a007807b766,0x863147063a7920a0]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xe7fe6003fc005fff,0xb01ff43000ffda0f,0xff4c3ffd407fffcb,0x81fff01fff9001ff,0xe000f8003fe30000,0xfbb6003fd600ffe0,0x3f440007f4801fa,0x2a01f92000028203,0x11f01e000218063,0xfe7f7fbbefea3fde,0x7927fc9f9d03f83f,0xff0fa0d180ef03,0xf00f80b9c01c000f,0xd07d81ec0fa01810,0x4008606180e7deb7,0x386188bcc3124c00]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xfc9856bc5c5fa8bd,0xe76776f3df165e60,0xb24cc7595a9835fb,0xfe218fe6199d7e3c,0xd97621bfc0a10689,0x9bd264254f3010e,0x6c015fcd026fce12,0x327e614a1ffd4080,0x38e01a1c618e0a17,0xfad3ed565cac9de,0xa9a02de8ed7c22cd,0x1f33977f20552bcc,0x67721e5859e08af0,0x9919beae800c65ce,0x7038b101812a21b,0x33c7f19c14a50385]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xfa7fe97c86e7a74a,0xb980b13c6f29dbf5,0x4d17c8a7f582ca0f,0xd61ff3e06702bf03,0xe6ad5a44c143f9f7,0xf202dd818fcf0ae1,0xb4fe607fad007628,0xfa61a35e02c3b7c,0x470125e3825015e9,0xd2e2878eb22fc607,0xdb7892f7a08c5fc3,0x470f68a321bb4434,0x18f1c141e66c7530,0x57e4405d72b48a21,0x78ec04ee076c0c45,0x45aac2e12d70d45a]))
  | _ => 0

def samplesQ253 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x100000282101849,0x4900004040102104,0x1110000032c20000,0xa80a0008049000,0x10000a0000842a09,0x400800200108800,0x9001004060002048,0x3021020210202508,0x801040880200a00,0x418080100c150000,0x414a00060019000,0x5a40001002748001,0x400490000124001,0xac0020000a505008,0xa014050000880088,0xc81c044080800a30]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x806a90a381849267,0x478001574c420000,0xc7bb16412fa1705a,0x534149aec82c815,0x19842e6894314313,0x5465d02701582620,0x822609806a00a301,0x7061908c68988f60,0x1c184d90a924588f,0xd59ed57db90432ad,0x549a782514b11810,0xb254e51a42ae280a,0x10d250b94111865,0xa22f80121511048,0x43601890a4f6bec,0xec04245151081004]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x1227c2caa8899141,0x532b1ccd550698a2,0x83313c4da3a8d1f2,0x99768589de218c0d,0x49cc4130cedc788e,0x3a5478044d029c22,0x5015254302e0c9d8,0xc184ba8b50735d26,0x8d8a1ca59aac882f,0xebedfffede119739,0x330dc1036758a614,0x68b5b94fd6264952,0xa3258726a13530c3,0xa0c2a24e0504604,0xa8032c2c4287fddb,0xf3183923a0840008]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x1e8ac1c019c0c324,0x98869400438462,0x4608500688394054,0x2c059482906249d6,0xa9d18416028492,0x522722042a632531,0x4c26e9b000909a33,0x428001c46092ca00,0xd0204803284580fb,0xb45a61c77020fa08,0xdac043398ab26522,0xa4986dc04c801038,0x618024aa040d9046,0x3248012a1090271,0x41281a006c07b764,0x42043063a592000]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xa6384048690007b4,0x32aa54b115c8902b,0xcc6904cd890d1102,0x8d52b00e5723444c,0x40a0b4490c638506,0x30140235a00817bb,0x2314452919018020,0xc95a21c14c5dc2a4,0xb40ae0a5609081a7,0xbe773eabe3c21ede,0x18035c1f1812082f,0x203b2300c582091a,0xa007a238c524000e,0x406d8b2485202010,0x4f0030a18077de37,0x3041883c43124000]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x6000041c20020000,0x1066300093005000,0x2000011840000501,0xc042000002192400,0x2452001340081040,0x90009d0d4040088,0x2180000a956d4080,0x81e082006050014,0x206006400802400,0xa210a0000ca0142,0x212004c0014c02c9,0x102122520000384,0x8040920009e00210,0x1806ac00002d06,0x281800681300013,0x13c3908804240181]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x4800280004202000,0x8000000020200210,0x4802000000a00,0x200406000000282,0x2413008600000040,0x10201c012250000,0xc808010841c1002,0x200002002000001,0x40020004020000,0x284000,0x806002c0800441c0,0x50000a020010400,0x1810004002000500,0x1080004010840923,0x88820225000000,0xa242800c608442]))
  | _ => 0

def compactPerms253 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains253 : Array (Sig × Nat) := ([(subcube 4 0, 9)] : List (Sig × Nat)).toArray

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

def samplesP251 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xbc797e6d0febefff,0xae3bff00affe998b,0x67e8fea0aeaf794,0xf9001e5fe49d1efa,0xfd304fc60effbff8,0x408049eee952c620,0xd5134d9005c1efd1,0xe712001a2ed528d3,0x5803cd04d80c3c27,0x9f0470c3501f38f9,0x802ea0597ee27076,0xe89a7fd0ccf4f039,0x988ec05ff2500be3,0xd06d21440a1fa0b4,0x80281068227b5dc2,0x2660141a7418d258]))
  | 1 => (BitVec.ofNat _ (limbs64 [0xdedfd9f7ac7eae96,0xf17f27fcf6bff5b1,0x9fa1f8f19fd4c9fb,0x838c773bfb20f982,0x2bef832ef449fa71,0xaa1f7a511681bc9a,0xec9844b2040eee,0x80d2b7f117ecd0c,0x137c9002e460c0d0,0x2000870caf8976ee,0x52ba7c939dbb2fcb,0x73949ad3ea2b0dc8,0xf10d5827484e804,0x3cfcd61835381f02,0x73c04e944000158f,0x2d06e84c1b240d24]))
  | 3 => (BitVec.ofNat _ (limbs64 [0xffefff7ffe9bf7bd,0x4fdd9ddf7d3fa61f,0xfbcd9c7cb517ce1c,0xbf9f93e21dde871d,0xbc534cf9773fc080,0xa8313612033b189b,0x3a071442691af034,0x23e25ca1520103d3,0x69d063ff01830000,0x30030000ffffd,0xf7cb9a6e6d147ff7,0xb7e7a3f4ff9dc136,0xe0871e2c067fc37d,0x8905918c5600009,0x7800101803ffd,0xd860fa9387100003]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xfbf6e7ecfb7fd74f,0xdde5e6e3ddf15e6a,0xe58f6f9544fd07f4,0x46e1fdbc056de6e5,0xc2b3bf398931bf07,0xe7818d156cd9c4,0x4a14a78f8425106a,0xe4eda024ad14d4f0,0x261c4cf8d260cb10,0x18c86980420dcdb4,0x69dd43dac2f5cc2a,0xdc7daf2bb39aee01,0x696920938a28f79a,0x217280a4fc824180,0xda02e8a80342b28,0xa9d38631a0e280b4]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xfd5fa19a5fb55966,0xfebedffffb7fea45,0x9851f70e6f2b31ef,0x7c7268dbfed2ff7d,0x2bdc732efb88458e,0x5518845ee8016365,0xa0fb6224b7fa0e91,0x100d2b40c16b3220,0x93632202381030e9,0xc030060f0c67ffd7,0xacb5ff37ed4caf89,0x8c8b492d15740df6,0x6e0d56189041407,0xc2832fe33ad81e42,0x821001607c41ba7c,0x29a11ee23496c00]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xefb17fd3f3d63bfb,0x7bfaf9ff27c577f4,0x66726237fa2efe6b,0x36ff8444da6318e2,0xd6cfbcd12ef6581f,0xbf6069a0568c0028,0xd5e8a37b5841e10a,0x5af0d49a0e8ad52c,0xa48b9425260c0306,0x22cc8800a196bf2f,0x7f64dfa4139fd07d,0x376a546e0ce23209,0x97772a4c3dab0880,0xaf0136bbc004c014,0x7c406016820c6475,0xd21d0b605c961380]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x77ae9ebff5edfcf9,0xb7c77a3fdacaf9fe,0x79be11cbf1d13803,0xc97feba523bf611f,0x552cf0d7d1c62460,0x57ce9621a8f62757,0x2f0058b94abe1105,0x9d12d7c5f0a02a0f,0xcca43bd901930408,0x45331070106ac35a,0x9f5325edb26b9394,0x4b75f49f734112c6,0x70182bb041d33478,0x570ec84703e52069,0x1f91011d828292,0x55ad6585c8e1204b]))
  | _ => 0

def samplesQ251 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xc6800410c022402,0x2a01010088041181,0xd122200c40800,0x30001a00c1010618,0xfc620001818,0x20114020c608,0x4111015800024,0x4210000021200200,0x100859230180c020,0x420800cc018820e9,0xa001160827000,0x20902040c0293030,0x6c01030000364,0x806c10000a0080a2,0x68008120091580,0x2460000a14005018]))
  | 1 => (BitVec.ofNat _ (limbs64 [0xc4cd841a0088c02,0x3010039480a89490,0x5184008540842,0x100000115100428a,0x2000856264002a28,0x902200108004284,0x14d1111110a4480,0x644318a21204445,0x848514a48984220,0x160000e4008820ea,0x301198832ac0,0x73100290e2290898,0x112500254002124,0x34540000102aa2,0x3042868024081583,0x2500e00c1a000904]))
  | 3 => (BitVec.ofNat _ (limbs64 [0xfe277530ce8b3288,0x4f1994da4c3e088c,0xb285b018854e5a98,0x94b4a10245840b2c,0x90d55552231a8832,0x2402d11671b58c6b,0x186120a44488662c,0x41751d6908995355,0x5405287156c1686c,0x82955dc584affffd,0xd10b9a626c105f73,0x16c623e4389d4114,0xa2a34824924d4535,0x8a4382955008c18,0x292b043309213ffd,0xc860da9307100002]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xd39020ac5035400d,0xc004640055400a04,0x182640800010788,0x1e402002c8160,0x23300002018580,0x404197e2004c2001,0x30008486ea40104a,0x3902080400143920,0x8014040032000cc0,0x2003010300714914,0x1d401ca0074800a,0x8c058d011182c100,0x686000818000d481,0x1000804f0000109,0x8190210ac0322a08,0x8830631a0628020]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xf112008803b01124,0x4ae406821132844,0x20c0a10c270852ad,0x8a4a08a28042920,0x89550081b928083,0x2650044422482842,0x30c40020613350,0x1021844442402010,0x62b1841026050940,0x891589110627df14,0xa4a54d0005440508,0x800b482d04104540,0x22a0046489094403,0x40822b2950484500,0x821160284840ea7c,0x21a10e021490400]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x20010712014003f0,0x1e2982322016000,0x642080010528f000,0x2ec004000421800,0x429c400001364001,0x2b8480017930020,0x8a106a6000250111,0x8021decb0000,0x26a0a20404030011,0x803408005c069600,0x7e20c62403080035,0x68500a0c400001,0x1680202c002b0800,0x248120bb00004054,0xe00501401c0c074,0xd21c094040940280]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x808a063044c851,0x90402a0512c0c022,0x810008050000000,0x4102002402100001,0x500000180400300,0x49a90aa00c020084,0xa3080a438a060083,0x2c02208294060c20,0x8840020c00201002,0x40220020000002,0xa50208c92298084,0x4920941203400202,0x8030000900008,0x1200804000a42245,0x1480930484920002,0x11852504c8a02041]))
  | _ => 0

def compactPerms251 : Array (List Nat) := ([[], [100]] : List (List Nat)).toArray

def compactDomains251 : Array (Sig × Nat) := ([(subcube 2 0, 9)] : List (Sig × Nat)).toArray

def compactWords251 : Nat → Nat
  | 0 => 0x27f
  | _ => 0

def compactCount251 (k : Nat) : Nat := match k with
  | 8 => 1
  | _ => 0

def compactPath251 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => 0
  | _ => 0

def compactLive251 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => readCompactBits compactWords251 (0 + 7*i) 7
  | _ => 0

def compactPoolIDs251 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let v := readCompactBits compactWords251 (8 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords251 (7 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket251 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP247 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x2952c07e6a706817,0xfb1063ffec63bd7d,0xfffe27bbb9f47ea3,0x7c3d79ffd900a58f,0x74ebd498a7caa723,0xf75f05dc8c1a438e,0xfbac8412235b3314,0x4e8668a431c0f6d,0xae11823905a710cc,0xcc0467c9060ec00,0xeedb58df0083bebd,0x80cbff7b0412f0a0,0x5590515c6e0d2c9b,0xb265205a3f0fd2b1,0x200040a6027c89db,0x7200540ae0615258]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x5c450480148702c3,0xbffefdef5f3efa7f,0xde679e63fa4a5f6,0x88e3c4fac1ff6c79,0x8fe3f967fd406dd3,0xe8a8dbb712823cd1,0x1279620c0884cdc0,0x3f4314f9a821b2a0,0x3a5ec486fed00ad2,0xc10388810086103e,0x1bf3e4730de5c437,0xae7669acdd7b7c5d,0xc0eb16a3c614b006,0x68621f20e86c0d02,0xcdc307090c00015d,0x698da0dc28900d24]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x22a80a0101081003,0xfefff7ffd7dbdec9,0xfe73d6dcfd785bdc,0xdf42a996eec47dd4,0xff145ee879bf5265,0xb4e7fe22042ce27d,0x644133e01ca844c8,0x51a1d9473c4e0446,0xc5a019b1086bff21,0x2043000070903c0,0xfff7e9bfe323b61,0x4fecf595ff1f5740,0x3a32a32f984b17e4,0x1281f3334570000c,0x21c3810700047fe,0x83c1e75314448003]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x9594b0708806014b,0x7fe1df71ebff5ff3,0xc77dfb5b47cbf0bc,0x73bd871f2978dbef,0x88ec4b5f2632db5e,0xfa6e5db74158c0e,0x879345d5c3234c33,0xe51669098313e89d,0x501662068a24e0c0,0x813988720850600c,0x8dee27bcc73f62fc,0x71bb0e9ae3fc189e,0x16ac6a986182cb1c,0x51db0399b091a180,0x1080878a840b02b4,0xcc26d06147c900b4]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x6252050024e08ca3,0xefff7e6eb0bd65fe,0xf599bdfdfe5b2549,0x8de3ae5377f9276,0x70f3a687dabd6eaf,0xef50de68e9623320,0x11c6981bf407b228,0x3abc84f254c1bd52,0x3a493946f1080a1c,0x30820701e0068031,0x157f9b6cf5d9f90a,0x5f7de648daa4e31d,0xa8549543a9e44019,0x841cdcc4d78c0e43,0xd2000440bb033a6,0x15b40bae51226c00]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x8b293281d201731d,0xddef89953fc7e3a6,0xfbafcef7fae7db7f,0xe7f07e6176bb2681,0xcb1d2db8def5b898,0x133d2081f3c141d1,0x8c0a68a03ff4a837,0x8808b334a0ac4223,0xc1ae6e79079ce533,0x4c3850821fb11102,0x2b1c9945fb4e15d2,0xbf1013f724cdaca2,0x6f4d084413b93f63,0x4d04cc840072201c,0xf05f8011a0470a40,0x127b0ba1aa181383]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xd4a0490e01188422,0xf41fbe9afffcbf9f,0x3adfff2fc79f8e03,0xb70fd7089e87db3a,0x371eb377014f95fc,0x58db3b440bfd9c22,0x68349f6fc05813cf,0xc2570a045ff25198,0x5e195c870531520,0x3244210c60080ec1,0x46a5e7a23afccfcf,0xf08798673be38363,0x8103ecb01472c0e0,0xafba206f0a825060,0x22078605180f429,0xac5a3c149f86a048]))
  | _ => 0

def samplesQ247 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x84010181810409,0xb00062050440006d,0x22019081942400,0x4c7051084000015a,0x4001583000802222,0x40850480840a2022,0x1820b200002014,0x1d41080220000908,0x90400a080a500001,0x4300290088220102,0xda93408100019031,0x80488911000074a0,0x1012340a040403,0x126000127a0002a2,0x204000a82204055a,0x6200440820005018]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x2080a24901202d39,0xb09864c90512aa27,0x40218620b02410,0xc460405080224158,0x82082444c02011,0x8095318648a009,0x4230a11640108414,0x890180a200502428,0xb060502446109409,0x6820284884200200,0xda93c41200a1c410,0xa8464904940b3411,0x400902224c049402,0xa32680814a2,0x4852090846840159,0x6901205c28000904]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x90d475ec90c5c837,0xfecc136e025b92c8,0xa0730258b1196d04,0x466448820a4c2958,0x92200c2929a43040,0x25c206012202053e,0x62aa09e48d023041,0x147088312d048d00,0x28821a3e6c41c747,0x50092c11d1304864,0xdfff309ba0323861,0x4ca8e091dc1d4504,0x2222032888ce064a,0x9711369408204,0x2c1a12a0742127fe,0x8381c65310408002]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xc8694c806250d282,0x4f019900c2a55490,0x61c12410441008c,0x20848806030818a1,0x102401090a025108,0x2122024a28010610,0x9881160885200849,0x2228414c85a68084,0x493a040000d0254,0x104a109101088045,0x256c222c061e024c,0x11b1048a03340904,0x12842088a082480c,0x108410881108105,0x2a09242880982a4,0x8406902145c90020]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x80401836501e1206,0x4d670822a0284000,0xf589980818430004,0xc282226190804,0x3060820b18001000,0xa3124a0210810304,0x30421c4808a31a00,0x1c6259088240c0,0xa010113b08c6134,0x14180035038000cc,0x56c1844f5482808,0x471026484aa0030c,0x8200004981a20018,0x8018c50005042101,0x52d800218303aa4,0x10b403a251220400]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x40200120c0a0040,0x22001038000100,0x5980cc204a001262,0x100040110000600,0x900008080118880,0x10b05080,0x440400020890320,0x4006320040004053,0x208018190802020,0x4820020002410,0x94059400182,0x200126020c08000,0xd40080000012120,0x4804008400202050,0x1105401100105800,0x1078098082100281]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x30b82002e2021c0,0x10849059842d12,0xa04642746008001,0x1003020000808000,0x418204000080404,0x180820380870d081,0x8c01c20060188528,0xe2021184c0702037,0x438e0c000001000,0x8080400200451000,0x87200a844786,0x3007102621428042,0xc40010100080,0x2482004000821450,0x528049518088c001,0xc4a38048e842040]))
  | _ => 0

def compactPerms247 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains247 : Array (Sig × Nat) := ([(subcube 1 0, 9)] : List (Sig × Nat)).toArray

def compactWords247 : Nat → Nat
  | 0 => 0x27f
  | _ => 0

def compactCount247 (k : Nat) : Nat := match k with
  | 8 => 1
  | _ => 0

def compactPath247 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => 0
  | _ => 0

def compactLive247 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => readCompactBits compactWords247 (0 + 7*i) 7
  | _ => 0

def compactPoolIDs247 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let v := readCompactBits compactWords247 (8 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords247 (7 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket247 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP229 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xeefff7e,0xdda6cb7ff6e7cd97,0xfb87cae93337d371,0xcdb7d4a8e2e268bc]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x4181014,0xc4076f40b000a4d5,0xd9028aff30015222,0xe9bf4a9ee4c2afc])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0xf57fd9f,0xe8d73c3cfffdb6d9,0xedd8827603fd6de6,0xede60096ccddac0]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x640908,0xc8f08f8002251382,0xed88477e341421c4,0x4536e0eb7d825fcc])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0xdfbfbfd,0xc679e7bfbb3ff3e6,0xdd2a751e34dff28e,0x773ba0e31d1e374c]))
  | _ => 0

def samplesQ229 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x1111080,0x2049040424044221,0x112041008249110,0x902442401a200a4]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x41890c4,0x8402266600910761,0x8116204522b48845,0x2020462649a35102]))
  | 5 => (BitVec.ofNat _ (limbs64 [0xa82164,0x122043f04a008540,0xd08d380887d12022,0x44403026e49da00]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0xf9bbad7,0xbf6f7666efb7e7ed,0xa736eeddeeb4b9ff,0x6f77ce6fc9a35fee])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x2060408,0x904180881221812,0x8400280400a4088,0x4211309010142448]))
  | _ => 0

def compactPerms229 : Array (List Nat) := ([[], [98, 112]] : List (List Nat)).toArray

def compactDomains229 : Array (Sig × Nat) := ([(subcube 4 0, 5)] : List (Sig × Nat)).toArray

def compactWords229 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount229 (k : Nat) : Nat := match k with
  | 5 => 1
  | _ => 0

def compactPath229 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => 0
  | _ => 0

def compactLive229 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => readCompactBits compactWords229 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs229 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let v := readCompactBits compactWords229 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords229 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket229 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP199 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xedbf7fd69e83,0xc8fff7b97ee73d8f,0xe612d31f7ee38b7,0x66ecf8890cf8586c]))
  | 1 => (BitVec.ofNat _ (limbs64 [0xf63f99fd24ec,0xe13f9bffeb3b86f6,0x338a0042ff77d739,0x8757035040f3ae10]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x4300111094ea,0xc9c092002b233586,0x268b2d7305203a39,0x744fbd94c321e7c])) : Bits)
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x40008052201,0xca00010942860ec0,0x1160d83962024520,0x22fc700f2370e18c])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0xdf7eff3df37b,0xca3eff4fff867fc0,0xf5f0d839efbb6f68,0x3bfcf00f2376f58c]))
  | _ => 0

def samplesQ199 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x124284191158,0x271286818481c1d1,0x5869107d348a190,0x44cc10c115d84844]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x9c8274a521a,0x1ef90f00a18e9143,0x4ab71b09e5579320,0xc41c317224f1ac10]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x4320831090b8,0x894a4624c1074090,0xf1e1521b20d8504,0x542e00b131c96082]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0xfbeef7ffdffe,0xbffbcfedff9ff3df,0xefffbfeff75ff7fc,0xf6fef7f73df9edde])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x208528400c04,0x10a4004818681c22,0x502020c00cb24048,0x2200a90ac2269508]))
  | _ => 0

def compactPerms199 : Array (List Nat) := ([[], [32]] : List (List Nat)).toArray

def compactDomains199 : Array (Sig × Nat) := ([(subcube 1 0, 4)] : List (Sig × Nat)).toArray

def compactWords199 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount199 (k : Nat) : Nat := match k with
  | 4 => 1
  | _ => 0

def compactPath199 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => 0
  | _ => 0

def compactLive199 (k : Nat) (i : Nat) : Nat := match k with
  | 4 => readCompactBits compactWords199 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs199 (k : Nat) (i : Nat) : List Nat := match k with
  | 4 => let v := readCompactBits compactWords199 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords199 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket199 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP231 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x775effdf,0xfebbb36ec3cac2b4,0x7bffff3ef2fdf3a6,0xe7fcffef91ef0337,0x606ef418221dc538,0x2678fbffeffcd9ff,0x6e3ba79bfe30731,0xbc639e98e617de00,0xf1cc21ab72218177,0xe2f317f4dc4945a3,0x8f679d12e7cb0802,0x509e2ff0085c852c]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x7d72ffed,0x9ffde4c3ecf1d408,0xcbfeb9dfff7e7d39,0x3abe8d3beefe6c0a,0xa5923c73d8a37003,0x481fffe777abb73e,0x7f3be7d1dc5ea2da,0x720c636db94a4ea5,0xf721400005a0efc,0xe797fb5beeb8b659,0x9584c8e99e30778c,0x8000ecce1e540d0]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x20390001,0x188812436addf270,0xec0089100018b438,0x223c07a5104c0f0e,0x64da3e79b2d5c97b,0x6fe000a22028c159,0x1803c211c4c3f270,0x3d637ea8fa0b4ea4,0x2fd037abfe7b8f88,0x8395003014799681,0xb507ec74a7ff7f8e,0x58fee0e1916dd7fc])) : Bits)
  | 5 => (BitVec.ofNat _ (limbs64 [0x7bafff73,0xffd2df733fed2fc2,0xbff9ffffdfbbbefe,0x3d3f8af5f70d9fcd,0x261d3b6ceb428f41,0x639fbcfaff4b56f9,0xb9c7dbaffd9d5ae4,0x4d707c72beadaeba,0xe8222239c180cbb,0x9becff231d36cf9a,0x640326f5663c4700,0x10ecc92d177296c0]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x1420240,0x8010e42081c3c68a,0x1c00000a12220ba4,0x5ac8871c2020385,0xa105fd64e80b5579,0xf388a84000481224,0x2162a048bd1e0ec5,0xec408f5ca6ed8e93,0xe2e2277fc19dd94,0x42a21f0349b06f5b,0x4421999be6fe4703,0xd5eddbcc28f2becc])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x6ff9feff,0xf9cc7ebdfbd7f27b,0x7ffcffb3ffe8ffd,0xc7ed77f55a52fb84,0xd9c1cfe5b4dd5878,0x919fefffb87ceb45,0xf97ee45ee7fafc45,0xadc38f8c42e901d7,0x2e3dc254ec01d15c,0x5fbf0cbf71f13a45,0x7039f91ea1c60003,0xc561d2c3b8ab3a0c]))
  | _ => 0

def samplesQ231 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x8a18020,0x40c0429118251143,0x8508483403048c05,0x5300054451004c,0x825108858cc0a044,0xc910926148681d42,0x181242124210684,0x12c010ec05011088,0x20300c44902823f4,0x20c314440e404462,0x84461803a00a4880,0x42821f5008440504]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x28d1002,0x72420a281a0c2ba7,0x278020b8211124d4,0x4c624c86401510a4,0x12588204a59084a4,0xa7dce3a054c82d14,0x1102053110159483,0x264120a6342458d0,0x89152f04512041fc,0x42919a4ae6281053,0x4c4004b845254c8,0x84a20ec860e50090]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x20394028,0x388812023899b270,0xc4cc04308921b959,0x439640114c04204,0x4650205496818872,0x4af639510e5a0d20,0x2510146501008225,0xb188184a19450c18,0xed219c061a2109f2,0x7062c707aa042142,0x4c54018390080e68,0x47089f1c4c920802]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x450084c,0x82420044012c018,0x4060104200881108,0x10c310092a06012,0x88044020004101a,0x1023081a03000088,0x8840808008882020,0xc10c0c0048408602,0x5640c08020c01003,0x9920612101100088,0x2001022042000334,0x10ce02507129040]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x7ebddebb,0x7fff7bff7ebdbbf7,0xe7cdfcffbbfdbffd,0xde7bee9f5ddfdeff,0xfefbeedffff5bef6,0xeffefbf15efa7ffe,0xfdf7f5fdbfffd6af,0xbfdb79febdff5ddc,0xedbfbfeefbff7bfe,0x72f3df4feffc7fff,0xfcf7bbfbf7fafee9,0xd7fa9fdc6cf7bfde])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x10060502,0x8211014004000c84,0x3a11800110424082,0x688008e220041401,0x2022000840200381,0x24084484b0004200,0x4024400882441952,0x421a20122206061,0x4002800160008,0x61c089850800a04,0x1020a01001551002,0xa8210082b0292208]))
  | _ => 0

def compactPerms231 : Array (List Nat) := ([[], [33, 117]] : List (List Nat)).toArray

def compactDomains231 : Array (Sig × Nat) := ([(subcube 1 0, 7), (subcube 2 0, 6), (subcube 4 0, 6), (subcube 64 0, 6), (subcube 32 0, 5), (subcube 128 0, 5), (subcube 6 0, 5), (subcube 66 0, 5), (subcube 68 0, 5), (subcube 33 0, 4), (subcube 36 0, 4), (subcube 130 0, 4)] : List (Sig × Nat)).toArray

def compactWords231 : Nat → Nat
  | 0 => (limbs64 [0xc57fc,0xff0e7ff0da0345d1,0xa90a4854e1065464,0x4e0065464ff0ff0d,0xf2ff0b6bff0ff0ff,0xff02a9e832d74e6,0xff0518ff0ff0dd4b,0x95e2c65d73154200,0x277c7b9dd6ed3d9,0xf39c424289c42708,0x9c1670d9c098a8c8,0x9890ca0ca8c8c117,0x32e40fff81d454a9,0x9fe052db20729878,0x6d2e91fe07f81507,0xb585f4316a3b8df2,0xe1fe070e7392884f,0xfe00f5ee868e89fe,0x1d635a9b397a74f,0xbbcb63ff81fe02b5,0x98c05f3bfe03ec1f,0xe0553247090e8d49,0x6d7fe067305a486,0xcd51aa1c712b77a1,0x7a0bc0bfe037ab09,0x8000128002002004,0x782d8b162c58b,0x35e54082f5dad529,0x5195223060d12102,0x800000a414490524,0x390e6440c30c2040,0x6490212fefefefe,0xfefebef6fbdefeef,0xbfdfdefefff6f7de,0xfebfdefff6fefdd3,0x11d30dd309331133,0x413101310130413,0x2219613161308d2,0x14e194c194f314d3,0x14f304f305919593,0x1593109195531450,0x9473145317192196,0x10e08d19519110d0,0x8c19498e863bf8d3,0x17fc0e487d4ff83f,0xc01eae17ed9b7973,0x60ff07f83105fe0f,0xf07f820a1fe0ff06,0x886a091ad120a5e0,0x3b98630a650399a1,0xee22002190865990,0x822e109d05e22c08,0x1623f2a100c63a88,0x46327d29a0846328,0x338e229903a637ff,0xfffffffffffff865,0x465065c644648434,0x43823423a21d843f])
  | _ => 0

def compactCount231 (k : Nat) : Nat := match k with
  | 8 => 1
  | 7 => 9
  | 6 => 27
  | 5 => 7
  | 4 => 2
  | _ => 0

def compactPath231 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => 0
  | 7 => readCompactBits compactWords231 (32 + 12*i) 12
  | 6 => let v := readCompactBits compactWords231 (1050 + 16*i) 16
    (readCompactBits compactWords231 (942 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 5 => let v := readCompactBits compactWords231 (3033 + 14*i) 14
    (readCompactBits compactWords231 (2961 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | 4 => let v := readCompactBits compactWords231 (3556 + 13*i) 13
    (readCompactBits compactWords231 (3484 + 36*(v >>> 12)) 36) ||| ((v &&& 4095) <<< 36)
  | _ => 0

def compactLive231 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => readCompactBits compactWords231 (0 + 6*i) 6
  | 7 => readCompactBits compactWords231 (140 + 7*i) 7
  | 6 => readCompactBits compactWords231 (1482 + 8*i) 8
  | 5 => readCompactBits compactWords231 (3131 + 9*i) 9
  | 4 => readCompactBits compactWords231 (3582 + 10*i) 10
  | _ => 0

def compactPoolIDs231 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let v := readCompactBits compactWords231 (26 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords231 (6 + 4*(v &&& 7)) (4*n)
    compactIDsFromBits bits 4 n
  | 7 => let v := readCompactBits compactWords231 (487 + 11*i) 11
    let n := v >>> 7
    let bits := readCompactBits compactWords231 (203 + 4*(v &&& 127)) (4*n)
    compactIDsFromBits bits 4 n
  | 6 => let v := readCompactBits compactWords231 (1836 + 7*i) 7
    let n := v >>> 5
    let bits := readCompactBits compactWords231 (1698 + 6*(v &&& 31)) (6*n)
    compactIDsFromBits bits 6 n
  | 5 => let v := readCompactBits compactWords231 (3194 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords231 (3194 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | 4 => let v := readCompactBits compactWords231 (3602 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords231 (3602 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket231 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let d := readCompactBits compactWords231 (586 + 3*(i % 6)) 3
    let off := ((i/6 + d) % 26)
    let v := readCompactBits compactWords231 (604 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 6 => let d := readCompactBits compactWords231 (2025 + 6*(i % 16)) 6
    let off := ((i/16 + d) % 60)
    let v := readCompactBits compactWords231 (2121 + 14*off) 14
    if v >>> 6 == (i/104729)%251 then [v &&& 63] else []
  | 5 => let d := readCompactBits compactWords231 (3208 + 3*(i % 4)) 3
    let off := ((i/4 + d) % 22)
    let v := readCompactBits compactWords231 (3220 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | 4 => let d := readCompactBits compactWords231 (3606 + 1*(i % 2)) 1
    let off := ((i/2 + d) % 6)
    let v := readCompactBits compactWords231 (3608 + 10*off) 10
    if v >>> 2 == (i/104729)%251 then [v &&& 3] else []
  | _ => []

def samplesP239 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x81f01fd7f80fe03f,0xfc7f91e003fe0e7e,0x3fc1ff4327fe00f,0xc787f0fe8f03e007,0xf21a1c07f0780710,0xfc07c8603f003fa7,0x40e00fc03e82c01f,0xf03f81f800401c0c,0x2dee86198070023f,0xf9bfc7f1bf1fc240,0x77d14e30339c3fb6,0x1f9fcfc10c0e0338,0x7838e1e0f8de1f18,0xe9801811c0fe1704,0x200918111c9777e1,0x8c7801104f2614b0]))
  | 1 => (BitVec.ofNat _ (limbs64 [0xecafe469ddd68244,0x7fdf6a087f1f63c3,0x387ffb0a9bc7570b,0x7869ef6188fedaa0,0x69efa08e8e8054e5,0x3e83f01ccad4738,0xac01a6688c9929a0,0x4bc4b400aa384000,0x260d81fc7b,0xd7f9cf3fe4afa1fe,0x1c357fafe26b78d9,0xe78b71e8d03300c7,0x1d420cf1246089c7,0xd403e7852f61e07b,0xc03006000007d59b,0x164678c1d1590340]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x7b5778ae77795cb9,0xf01667fff01a0d8f,0xffc243deada7bff0,0x179989d722d0409,0x9281ff780417a80f,0x2510065f920f4042,0x3f44188561644e63,0x100830773f818023,0xc20001c0120e01bf,0xdfeef5ef8713bf86,0x6aee8dc35e369ecf,0xf95477be7bc06c16,0x80325f0c48277008,0x3ff821e8d000080,0x346e0e0030faebb,0xe80f1656a480a005]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x7f889fa78fae1fff,0x83e969bf83e5ff71,0xc383dc2b6c781f0e,0xa6fe0fe17dd01886,0xd4403c00a6fd8e0,0xc216311e20f0b845,0x809e503a9142b01c,0x2d304b8fc00603d0,0x100006000003f,0xbffffeff38f472b7,0xef2f61fcbddbe345,0x9effa63f83cd9228,0x6785b01097998097,0x147c158a32800000,0x1c800100e007fb7e,0xf3902f88283c000a]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x12affb91ddd97d84,0x7fa094087ce093bc,0xc47fe4f55bb8a8fb,0x7f91ef9e78fd2558,0x69f040897100531a,0x3efc081f352873f,0x5301a9974c9bd640,0x4bfb4a00aa40200c,0x31f0f8070c01f077,0x36373bcfdb485cf9,0x9bcbf06fde74bb21,0xf86889e9203cfcf8,0x9d7d0d0e24809627,0x2a03f864d061f843,0x8000181e18e26e5c,0x7826812f5c9a5b00]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xa557655e2262e77b,0x8c6fbed78ddbf039,0x7c19a8d7d781dff5,0xbc26122af7d07bf6,0x961fab72cf81215f,0x18f911ac40277898,0x28fa4645722d0383,0x940784af55b8cc01,0xc0406e813a40da8,0xe9d7799e73e9fd39,0x80beb2936dc945be,0x335be5644826fc1,0x6288e2734b656cf0,0x2efc65e00d1403bc,0x4370e641041110e6,0x73a9d6a7036504c5]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xde78827822b5bbc2,0x390df77fe25fcc6,0xbfa43729e45e60f4,0xdbde7557872a8779,0x420543531feaea0,0xfc00eef20dd880c0,0xd73ff13a83743dfc,0xa6c07f50550733f2,0xd21b7910e05a021c,0x6e48be70ccf60f4f,0xf5509f5c81a7c47a,0x64e25816bf719107,0x82c7128f931a6368,0xd1000a7b729a0c00,0x3c8f01aee36c8905,0x85d1e878b2c0e83a]))
  | _ => 0

def samplesQ239 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xa0a0022670cba406,0x648c001c00fc8,0x80580b02ac598001,0x5266a4902016007,0x60844882c4112640,0xc201206ded280042,0xa8a0010021507200,0xc0303520c006d021,0x221581098c240e7c,0xd8b847b1b4158000,0x7d800eb0021c20c6,0x1a0a07c0cc8c0010,0x78025160209c9c18,0xc480001540841444,0x60010150048f57a1,0x8858001049201410]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x8422082b34cc8814,0x2a52288429490580,0x1129110aa94ac009,0x23262120a5a293,0x2884ba049c020a00,0x4a4a2274e4ba9232,0x988ca402854248a,0x231415129852e902,0x220c8088c408877a,0xd5d88719e402a066,0x3c1107aaa22950c9,0x4d8a72e0c1270003,0x2c0209b0202c8804,0x542146150442a45a,0x4aa200920407d593,0x6443840d1500240]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x68671a21a0499c3e,0x734040d6711902a0,0xb3c218c1ac4794c1,0x620085c60c10606,0xed105f2689406004,0xe301905f8ca6001c,0x2c0009340d422e03,0x82bc70801430d383,0x8381e5090061c3ff,0x5fe4e5eca203aa80,0x6ce80d8318069a42,0x795817b84bc16026,0x36110c60845816,0x1f384150c801007,0x32180e0924faebb,0xc80e1414a4802004]))
  | 3 => (BitVec.ofNat _ (limbs64 [0xb90b2e839a810e9a,0xb3e3594eb249a721,0x91c85d47060b0d54,0x2ec22acd29c1cc42,0xb40888b0e0f3d562,0x636212c487351b40,0x8a2ea22d024af88c,0x401958a34a9b119b,0xb8a52b159520d5bf,0xaf7ffaff3894d2b5,0x2f2544dc2d532345,0x8e7d229589c5a66a,0x2a15302485899097,0x4cb584a82484c210,0x2c00cd04c287fb7e,0xf3102788283c0008]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x801218089004188,0x9581140294202024,0x4084c04502a00552,0xa90810601480860,0x150054823008027,0x20c0020200098d,0x602209214800045,0x14c1800107880490,0x80a22a6020025081,0x220738460b481c18,0x24a604550008920,0xa020800820502468,0x11d240601000203,0xa14b0a090204001,0x855008241870284c,0x7022810f048a4100]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x1060c008000081,0x8089900180026010,0x800401452000330,0x1880000015100028,0x126a005802a81111,0x410498000014081,0x4004108bd2898060,0x14408a0801880050,0x40601a0000103000,0x2003180201e84509,0x8006b00045c00430,0x5880600000dc8,0x1a0000b402041,0x280c01e001000b00,0x8058660069300044,0x31a1c2a302050081]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x200801000300040,0x22000041002,0x400202000002000,0xc008100080040098,0x222200010080810,0xc1809000000c020,0x41005040c0050020,0x2100021800000004,0x400000202800000,0x40200142,0x8010900080a04418,0x80480210001000,0x80c0020110020120,0x80202122908,0x8a220221000000,0x481486012408822]))
  | _ => 0

def compactPerms239 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains239 : Array (Sig × Nat) := ([(subcube 8 0, 9)] : List (Sig × Nat)).toArray

def compactWords239 : Nat → Nat
  | 0 => 0x27f
  | _ => 0

def compactCount239 (k : Nat) : Nat := match k with
  | 8 => 1
  | _ => 0

def compactPath239 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => 0
  | _ => 0

def compactLive239 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => readCompactBits compactWords239 (0 + 7*i) 7
  | _ => 0

def compactPoolIDs239 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let v := readCompactBits compactWords239 (8 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords239 (7 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket239 (k : Nat) (i : Nat) : List Nat := match k with
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

def samplesP211 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xbfbffcf,0x5a7d578fbddf7ee7,0xe17e854b357de6f2,0x79a6ff041de38396]))
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0x2240803,0x625897d008520267,0x794c016bf5202763,0x4088ff243f0727b6])) : Bits)
  | 4 => ~~~((BitVec.ofNat _ (limbs64 [0x880240,0x98c94980900444a3,0xa0b0a94d0f4442a4,0x1d325bcc55a9c9d2])) : Bits)
  | 6 => (BitVec.ofNat _ (limbs64 [0xeefeff7,0xadd8d9dffafed0ef,0x7ab5792ccbf67fed,0xdd841e8760dede0]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xf87fa7b,0xf2cba00fdf77e733,0xbdc8a84104eff327,0xd63bda0401bf7012]))
  | _ => 0

def samplesQ211 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x4044810,0x2182001181101010,0x6008188042148600,0x4806060884608106]))
  | 1 => ~~~((BitVec.ofNat _ (limbs64 [0xddaf76e,0xbfe77b2cfff357ee,0x97a7a6dcffa87f73,0xcdfff1b67b0f3fbe])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x8a0600,0x9040490408a10060,0x282804401882810,0x8088801029061608]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x1103004,0x205222832020288,0x8404001014205061,0x1500124400928a0]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x789685,0xc201fee44404ae9,0x8ed6c208a8eb7102,0x4214975699f7010]))
  | _ => 0

def compactPerms211 : Array (List Nat) := ([[], [100]] : List (List Nat)).toArray

def compactDomains211 : Array (Sig × Nat) := ([(subcube 2 0, 5), (subcube 128 0, 5), (subcube 0 128, 5), (subcube 16 0, 4), (subcube 64 0, 4), (subcube 1 128, 4)] : List (Sig × Nat)).toArray

def compactWords211 : Nat → Nat
  | 0 => (limbs64 [0x5545dca14430,0x9a06cfd10e8858bf])
  | _ => 0

def compactCount211 (k : Nat) : Nat := match k with
  | 6 => 1
  | 5 => 1
  | 4 => 1
  | _ => 0

def compactPath211 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => 0
  | 5 => readCompactBits compactWords211 (26 + 12*i) 12
  | 4 => let v := readCompactBits compactWords211 (80 + 12*i) 12
    (readCompactBits compactWords211 (68 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | _ => 0

def compactLive211 (k : Nat) (i : Nat) : Nat := match k with
  | 6 => readCompactBits compactWords211 (0 + 5*i) 5
  | 5 => readCompactBits compactWords211 (38 + 6*i) 6
  | 4 => readCompactBits compactWords211 (92 + 7*i) 7
  | _ => 0

def compactPoolIDs211 (k : Nat) (i : Nat) : List Nat := match k with
  | 6 => let v := readCompactBits compactWords211 (20 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords211 (5 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 5 => let v := readCompactBits compactWords211 (52 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords211 (44 + 2*(v &&& 7)) (2*n)
    compactIDsFromBits bits 2 n
  | 4 => let v := readCompactBits compactWords211 (99 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords211 (99 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket211 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let d := readCompactBits compactWords211 (58 + 1*(i % 1)) 1
    let off := ((i/1 + d) % 1)
    let v := readCompactBits compactWords211 (59 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | 4 => let d := readCompactBits compactWords211 (101 + 1*(i % 1)) 1
    let off := ((i/1 + d) % 1)
    let v := readCompactBits compactWords211 (102 + 9*off) 9
    if v >>> 1 == (i/104729)%251 then [v &&& 1] else []
  | _ => []

def samplesP87 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x6ecfbfd695,0xf6237fdfe5b4e6c,0xf1ab101967fdd3e3,0xf62ec71046793388]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x774fd9fd29,0xd3b447cefbfdb717,0x2673ab6009defd3d,0x9875702ba876a854]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x21d0191091,0xdb3ef8048209866c,0x2733bf7dee080b69,0x9434473bef902ffc])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x7dbfff3df6,0xff1a8fbfc7ffccfe,0xf5f0f54e5bb7afd,0x5dfcf01e9b3d63c]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x400000524,0x712000840504c16,0x4b0b50649050b5,0x4fc701e833921c])) : Bits)
  | _ => 0

def samplesQ87 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x1132441912,0xb091ca81a063438f,0x115068451d5d1606,0x822cc11872792108]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x8b4070a54,0x380b1b43c028cd0a,0x10b47453058cb50d,0xa21c10e2a74a044]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x21d14b5091,0x721ef5a191309ea5,0x43e5e249c5f3e414,0x4322e256d8efd002]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x248084008,0x64240806041020,0x420100a0022248a0,0x4400a4080825610]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x7bff7fffdf,0xfaffffebf77fffff,0xfffffeffdfffffbf,0xcf6feffffffff75e])) : Bits)
  | _ => 0

def compactPerms87 : Array (List Nat) := ([[], [16]] : List (List Nat)).toArray

def compactDomains87 : Array (Sig × Nat) := ([(subcube 1 0, 5)] : List (Sig × Nat)).toArray

def compactWords87 : Nat → Nat
  | 0 => 0x9f
  | _ => 0

def compactCount87 (k : Nat) : Nat := match k with
  | 5 => 1
  | _ => 0

def compactPath87 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => 0
  | _ => 0

def compactLive87 (k : Nat) (i : Nat) : Nat := match k with
  | 5 => readCompactBits compactWords87 (0 + 5*i) 5
  | _ => 0

def compactPoolIDs87 (k : Nat) (i : Nat) : List Nat := match k with
  | 5 => let v := readCompactBits compactWords87 (6 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords87 (5 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket87 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP215 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x5ff8fffd,0x6fdc8f3f6bb1fe31,0x13ffcbeff7eefd1f,0xfc1e95efa3a7f8cd,0x26d989e033ea2831,0x9995fcfbfbf7ebcd,0x7e7e4b0ff277ac93,0x76807c98500dff44,0x9696b0908698d8fe,0x787befb6952be107,0x6d645a6cec7f8408,0x180e4f682c611658]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x6f3aff7f,0xf39fb3d9ccd62896,0x23feffb73bff8fe1,0xf0e3e9f9fdf78730,0x38620e3cc8fc70c2,0x227bf7f7df87c0f,0xbde7f3f79dc7d07c,0x87f883e07e323007,0xe9e83b231800211f,0xbda3f5e8ffd23e39,0x7380f4730f0018d0,0xe3100f72d3328124]))
  | 2 => ~~~((BitVec.ofNat _ (limbs64 [0x2930041,0x3172b0822976fd3,0xc00812212024d01,0xe0cac19081a07589,0xa7438f74e2f978fb,0xbbf808001158290d,0x9006084ab447d871,0x57a0f89f582f3a07,0xf2c83bbb9fdcf9e0,0xa9b52420aeeb55,0x734075704c7f9ed8,0xfb9fc1730876d7fc])) : Bits)
  | 4 => (BitVec.ofNat _ (limbs64 [0x7be7fef3,0xfff37f95b7ada5cd,0x9ff9fffefedf6ed1,0xcbfb7797d3ce7eaa,0x9517e5b2b4d1dca9,0x306f7bdef7ce73be,0xf29f8eee7daf6b63,0x4d66e317e9ad0e87,0x5151322b1554c095,0xe3df9d5579a5b9f5,0x258a9dad8b20280,0xf29584d16a8f50b4]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x8200000,0x40880711c438a085,0x10004a0020830a00,0x1021158523078eb4,0x3819c1a815f8d4b1,0x9420101a40804086,0x7a9443255905af63,0x274c87e0fd0d0c44,0x8936b2775612dcc7,0xf112cd00551135bd,0x42049afffc3f018f,0xfa5477f07f0b387c])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x7e97fdcf,0xdfef6f6af67a43c3,0x4bffff7bffb35b2e,0x37eddf942f39fd95,0xeb09d34d4739d610,0x8406dfbfdfd98df7,0xdb947d79ff5c9f61,0x330d9cef9d4f0878,0xaa2ec05442021c4f,0xd7bcff2f661c47dc,0xd20717b5744d010f,0x84073b71d5e2848]))
  | _ => 0

def samplesQ215 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x20072001,0x906260c0820e0180,0xcd100c0a06604a60,0xc09400400f80430,0x86003703c4140480,0x660c248228d00249,0x5414039801322401,0x193001875100900,0x13680560504803de,0x480361920168002e,0x20204a60ac030440,0x1a221e6824200418]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x10c580d0,0x8440680612290769,0xd43805050e804202,0x4d16c61c135214c2,0x46184103e201042d,0xc4dca56e41601649,0x2894009285057502,0xa714891924011908,0x44c9c588562804de,0xb12135888f420a29,0x42a04003ac070871,0x22520f7093300104]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x29310c5,0x11156200221646d3,0xd4c260086080864,0x805f82b007a8a409,0x7010917c0a0449b,0xa31502f46a850269,0x255209509005027,0x2687a02251144011,0x17a35d02508c90dd,0x794648529a401428,0x832400cbe102432,0x58709e88e7810802]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x4180704,0x108002808505812,0x20c1809020003504,0x804028a12400a104,0x2020004800022352,0x903121092004102,0xa044050800024,0x5048202200e64455,0x8002101028020021,0x2d4884450812090,0x40810040902182,0x4084c081488b5020]))
  | 6 => ~~~((BitVec.ofNat _ (limbs64 [0x77dff7ff,0xdf7ffafebbff5ffb,0xfdfdefffaff97f7f,0xefdffffd7ffff7ff,0xe7ff7fffeeb76fff,0xefdfb7fefbfd57ef,0x7fdf6fffdffff76f,0xf7dffb7f75fffdff,0xf7fffffaffffb7ff,0xfbf7fddedfff3fbf,0xfaf6dbfffeff7df7,0xfaffdff9ffbb7d7e])) : Bits)
  | 7 => (BitVec.ofNat _ (limbs64 [0x1684310,0x248090100181b82c,0x32a040600112b582,0x51202c0bb0021a00,0xc600a008000964,0x18e2d90995080084,0x100482002490990,0xd8680d818ae3164c,0xc800820081112000,0x86b8962d64140100,0x9004109000448b89,0x25846117185e2040]))
  | _ => 0

def compactPerms215 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains215 : Array (Sig × Nat) := ([(subcube 1 0, 7), (subcube 4 0, 7), (subcube 2 0, 6), (subcube 128 0, 6), (subcube 0 128, 6), (subcube 16 0, 5), (subcube 64 0, 5), (subcube 130 0, 5), (subcube 17 0, 4), (subcube 66 0, 4)] : List (Sig × Nat)).toArray

def compactWords215 : Nat → Nat
  | 0 => (limbs64 [0x1fe346ba2ff1fe0,0x2e379ff071bfc7f8,0xff182ed0400033b9,0xdbe797cb8f9ec885,0x890a1381a321464a,0x90ab38731108f305,0x19209208d31108d0,0x9108c305193fc1b8,0x931a7f81b57fe00f,0x57a33fc1fe07a2ff,0x83fc0df984226b46,0x6ffe0ff07f82b4e9,0xefec343841641c89,0x2ab9398041d8ff00,0xa5a987c33ff07f82,0xd23fe09500ac14c0,0x10248099326c98cf,0x1eb968d97a23250a,0x90223060d1024280,0x158d6178de317,0xc640842308bbfbf7,0xf7fbfbf7ffb7bfb7,0x77b7ddf7fdfbfeff,0xb7fbfefeffb7f7fe,0x217a42f4c1c986e2,0x15a42bcc17982f30,0x586084c209821302,0xa3254c348c912162,0x32482489885214e3,0x2146428487310a62,0x632432412411a322,0x1221183268a23cc2,0x37f86f1ae8763df8,0xf047f80a2f997f87,0xf87f8383d0695306,0x5c4af94d2764a50a,0xa008cf9674739694,0x68c36414aa366841,0x5286204ad7564682,0x134aa3668054c68a,0x216d52e68c36054a,0xe86d620a557effff,0xfffffffffffc42a4,0x2e32432232032412,0x212411a11d0e223f])
  | _ => 0

def compactCount215 (k : Nat) : Nat := match k with
  | 8 => 1
  | 7 => 10
  | 6 => 26
  | 5 => 7
  | _ => 0

def compactPath215 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => 0
  | 7 => readCompactBits compactWords215 (27 + 12*i) 12
  | 6 => let v := readCompactBits compactWords215 (959 + 15*i) 15
    (readCompactBits compactWords215 (863 + 12*(v >>> 12)) 12) ||| ((v &&& 4095) <<< 12)
  | 5 => let v := readCompactBits compactWords215 (2534 + 15*i) 15
    (readCompactBits compactWords215 (2390 + 24*(v >>> 12)) 24) ||| ((v &&& 4095) <<< 24)
  | _ => 0

def compactLive215 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => readCompactBits compactWords215 (0 + 6*i) 6
  | 7 => readCompactBits compactWords215 (147 + 7*i) 7
  | 6 => readCompactBits compactWords215 (1349 + 8*i) 8
  | 5 => readCompactBits compactWords215 (2639 + 9*i) 9
  | _ => 0

def compactPoolIDs215 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let v := readCompactBits compactWords215 (21 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords215 (6 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | 7 => let v := readCompactBits compactWords215 (565 + 11*i) 11
    let n := v >>> 7
    let bits := readCompactBits compactWords215 (217 + 4*(v &&& 127)) (4*n)
    compactIDsFromBits bits 4 n
  | 6 => let v := readCompactBits compactWords215 (1652 + 7*i) 7
    let n := v >>> 5
    let bits := readCompactBits compactWords215 (1557 + 5*(v &&& 31)) (5*n)
    compactIDsFromBits bits 5 n
  | 5 => let v := readCompactBits compactWords215 (2702 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords215 (2702 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket215 (k : Nat) (i : Nat) : List Nat := match k with
  | 7 => let d := readCompactBits compactWords215 (675 + 2*(i % 4)) 2
    let off := ((i/4 + d) % 15)
    let v := readCompactBits compactWords215 (683 + 12*off) 12
    if v >>> 4 == (i/104729)%251 then [v &&& 15] else []
  | 6 => let d := readCompactBits compactWords215 (1834 + 4*(i % 9)) 4
    let off := ((i/9 + d) % 40)
    let v := readCompactBits compactWords215 (1870 + 13*off) 13
    if v >>> 5 == (i/104729)%251 then [v &&& 31] else []
  | 5 => let d := readCompactBits compactWords215 (2716 + 1*(i % 3)) 1
    let off := ((i/3 + d) % 14)
    let v := readCompactBits compactWords215 (2719 + 11*off) 11
    if v >>> 3 == (i/104729)%251 then [v &&& 7] else []
  | _ => []

def samplesP223 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x57fd03e787edd2df,0xa1789bf978bb8cac,0xbe78f8138eeb81b8,0x7de7b806e363d9ff,0x26d841235c496265,0x88121fdac0475006,0x301800f71e039bd4,0x28238bb125939838,0xe04061c21f306e,0x1cfdf9dfafb153f6,0x6bdaaeb8fdd8064,0x7bde5e958416c176,0x70072edb1de4415,0x636380d0942ffa04,0xc10180047238deb,0xc25c0055068c5960]))
  | 1 => (BitVec.ofNat _ (limbs64 [0xf87ff3fff800ff20,0x17fe43fff4400bf,0xf980fffc70fffe40,0x7ff80ff901fe01ff,0xd8001ffca00bfd98,0x1fe0001ff88006,0xffe03f08000fe400,0x2ffc7407da00003e,0xf01838600000090,0x60ff3fefcf7ea3f9,0x7941f0fff207f83f,0x945f8ffa05e90383,0xf80382f20720003e,0x83fc0f00fbc00038,0x7021e0e08003e9de,0x62e179a283120490]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xffceffb6617da53b,0xfe810b645f9fff51,0xae7d41bf7d71ef6f,0xb1d945b9829d6e80,0x207d601e2fb608a8,0xe7e004086e3c61d0,0x41e7c3001850116f,0xd20044c61c03d740,0x70021c1800604701,0x81effffffadb517f,0xfe6e5dd361a22556,0xcea5745bfe8db841,0xb0229d0090306fe1,0x3403fa9f03500180,0x808e0703001ff67f,0x90061766d048a005]))
  | 3 => (BitVec.ofNat _ (limbs64 [0xff7efe386eba39c1,0xc79e37c7a3e3f7fe,0x579f8e4f8c9e078f,0xc61e763f7de5b100,0x4f03a2c080800647,0xfacf8f5318083c9,0x8c192813e3fc640b,0x417831020fc2f81,0x801c000008800800,0x2f6ff7fffe5be8e,0x6edfd4146f7eff99,0xe25a7badfb303a98,0x3cc241d6cc79302,0x408c75276ca00440,0x34000083803ffb5,0xad986e896884000a]))
  | 4 => (BitVec.ofNat _ (limbs64 [0xaff38fd817d2ecde,0x5967583e84b870b3,0x4667f7e383f479b7,0x7a07cfc69d99e7f8,0xa1a61e03532a9b62,0x701d9f251e072e36,0xc206b4f4e00c1ba0,0x2fcb884ee56c6038,0xe81a385351ca060,0x10ba95b97ccf4f04,0xf7b30ffc19e747bb,0x6961ad6465d6066b,0xc4f34a0c46d9b829,0x1f9208e8e4162003,0x6801f09486c2570d,0x1ab0c15b387942d0]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x5197fc4bb96f5635,0xfecef7c1bd6d7b46,0xe9a211ac73025251,0x887ef256fe2ade31,0xdf1ac1bc77f47590,0x30c02312a0829ee9,0x4fad72afda382f1,0xd1cc38a98214cfc6,0x2120286a77218794,0xe5cfee023524ac39,0x81207724be78dac6,0x1facd0cffa4a4d34,0x4bdc3972d9286bda,0xc804f52003588bbf,0x10a0077541c09870,0x2d07968817a71e05]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xaea97de5de970bee,0x3eb1ec9a42568f49,0x11df2e50ff0dbcfe,0x87a1b9e97e563e46,0x10e5bc418855801f,0xdf6340efc1797d39,0x3b0548cd07f06c1e,0xd03077785beb30c1,0xd05e541088c2580b,0xa7142f4d39afcc3,0x99deab0bd4993fe9,0xb5b3a3321a21f48c,0x3c3dc5832a0794c4,0xbc79025f18a95440,0x875e080a383d2282,0xd56ba834ed70a12a]))
  | _ => 0

def samplesQ223 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x62403e5a00021d1,0xa048989c9a490804,0x658a8008067c379,0xc440001661d468b1,0x264000810400e0a2,0xa0d238c0110650c6,0x75052b220400084a,0x4100826bb848081,0xa1c3881449413004,0xf8fdc9d38f3152b0,0x60d80e3ac008034,0xaa880a01852ec800,0x302d46000c64011,0x636480909420b004,0x1c001889010789eb,0x825c004402801060]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x8a6900ca88002570,0xa150812bc9412107,0x2348208124bcc74a,0x5ea000d220b4005a,0xba44088a2c89a480,0x4221884097165162,0xdd08010640a18842,0x14991193aaa07252,0xa128b115c0213801,0x39fd2fcdc5320158,0x5a45a071f201d834,0x84560b7a85281380,0xd90282b002624010,0x1ac2e9091007018,0x11e2a0828103e9da,0x6260782283000410]))
  | 2 => (BitVec.ofNat _ (limbs64 [0x66ee4194630c2118,0x324293850619eb26,0xa1406387ec8a616f,0xf7d2019889502480,0x971084070e996604,0x61451de8008c65c6,0xbc8403402808400a,0x4650c8a71819414e,0x35d81b141a49824c,0x1bebfebffaa8417e,0x362fc1d360a22012,0xc8846443d08cba81,0xb0428c048010e190,0x5003e49ab7220084,0xa45c03a057f67f,0x90041546d0082004]))
  | 3 => (BitVec.ofNat _ (limbs64 [0xd332eaa4a6281048,0xc606318d8ecaa9aa,0x230c468da4aea223,0x92c624aab9c42493,0x319894847163277,0x92922c7c0495604a,0x14cb392144cd7213,0x2695514a49348292,0xdcc89940785a3684,0x23f6f77e7fe59a96,0x4a87d4452f567618,0xa258518cf9a49a90,0x91c80c2d00538302,0x5124a4066d208c12,0x4d0086583413ffb5,0xac98668960840008]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x21900c000218880c,0x203000004208030,0x22520401003080,0x34a0888090500,0x12644d0420808,0x1104011000090609,0x2d4592a001105,0x6864804040090108,0x1400400a10884200,0x602102030c80c00,0xa1b00d0c01a4050b,0x4101240400d0004a,0x61080404188120,0x18000062201204c0,0xe004401406601604,0x1080811938594080]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x1000b00000434200,0x800404020001040,0x4880002010000000,0x8800000009000,0x8a412001241151,0x800000560408010,0x260000000542690,0x40800000800,0x4048000000022,0x4a001,0x1200005802c0,0x102090802a000024,0x10200059000848,0x8000110000400a03,0x10036018080000,0xd03028004260a01]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x801140010800002,0xa0040000040400,0x1001005002000800,0x100106020208,0x8866220b0600908,0x8208001e2408231,0x220c41c02308584,0x1828041000003800,0x200002004040110,0x22401,0x81502a08100909c1,0x1523803002010400,0x404010220001404,0x410000100884249,0xa05221240a280000,0x412388300d708102]))
  | _ => 0

def compactPerms223 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains223 : Array (Sig × Nat) := ([(subcube 8 0, 9)] : List (Sig × Nat)).toArray

def compactWords223 : Nat → Nat
  | 0 => 0x27f
  | _ => 0

def compactCount223 (k : Nat) : Nat := match k with
  | 8 => 1
  | _ => 0

def compactPath223 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => 0
  | _ => 0

def compactLive223 (k : Nat) (i : Nat) : Nat := match k with
  | 8 => readCompactBits compactWords223 (0 + 7*i) 7
  | _ => 0

def compactPoolIDs223 (k : Nat) (i : Nat) : List Nat := match k with
  | 8 => let v := readCompactBits compactWords223 (8 + 2*i) 2
    let n := v >>> 1
    let bits := readCompactBits compactWords223 (7 + 1*(v &&& 1)) (1*n)
    compactIDsFromBits bits 1 n
  | _ => []

def compactBucket223 (k : Nat) (i : Nat) : List Nat := match k with
  | _ => []

def samplesP255 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0x15a4586000b2c000,0xb80780098f3f0428,0xf82c06dc000b0df,0x6ff9f8438faff80a,0x3f9f81d4f29245fd,0xa21040034ec9ff45,0x6da680e00cb31b3a,0x834ed87f7053e40a,0xb922b9c39165800b,0x10c65207180b1e86,0xf8c35422de441dea,0x606c926004428806,0x7905fd0ad0880280,0x1014340111f2499c,0x6c77e02e184ce000,0x4a40a63903854960]))
  | 1 => (BitVec.ofNat _ (limbs64 [0xc80000012df4381e,0x1800f410400800,0x100d031203fe019d,0xf74d37cedfc3987f,0x1c39b8fb9c48978d,0x840eff84a41f20d1,0x4f7eb85ff802ecdc,0x6b452b858fcce512,0x7d9341e92e827075,0x8003ac701ab4403c,0x3904425a2000829d,0x3fc6800fb1d0195,0xc47980f40271bc00,0xc1e04a06000001d6,0xc42598f86c5a18de,0x3406680a64403490]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xd3005ede7f4900e0,0x400f0060000001,0xe0100c803c0006ff,0xfeef5fe7fbfedfeb,0xa7f37ff61af240e5,0x9fff07d728e457be,0x9c467600d7eec1e0,0xd56b8aaadfaf238d,0x90cb5fbd48bb0f00,0x3b083868201a4b79,0x40312400306f6302,0x340003ffe30a0c78,0x286a00000c00400d,0xe038038000187fe,0xb2fabc7fd2003c05,0xac5a528482120005]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x207fa13fc0000300,0x7a0000000002006,0x3000000008ff,0xff9efffbfefdffdf,0xfbfdfd6ee519f90a,0x6792372773f5bcbb,0x425136ff2ddd1e6d,0x7eb1b5b843d3dcaf,0xaf359e3ef3400f4e,0xc4704203c3c0a4c0,0x1c29bf0c7938404,0x43902c1f04151269,0x8594000021000072,0x800e0003ff,0xff5d7bd7a5b0c01b,0xd12095416100000a]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x159ba78000b2041c,0x801970341038d010,0xe61800c00188076,0xf1f6663f6356e679,0xf27e47ae0d763bf2,0x5a0587fbce33c006,0x3df1499c02bceb57,0x4b7673b2c701b55,0x76dc8603ad647084,0x10ba2d84e4141906,0x86c0a85dd9b81a12,0x1c73420003a29787,0x8302320600061a00,0x21f04542006c036b,0x19ce06b443538270,0x2b0381d09e2402d0]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x224000012d46c001,0x400600ca0f800fc0,0xe036003e141fa,0xbeb2b7bd2c3b67f4,0xdfa67efd63a51672,0x79e6f878151edf29,0xc289475ff742e7a3,0x9342d4410f9f1ae2,0x426c21ea9018707a,0x6f01d3881aaba03a,0xc638422500009d60,0x83839580fce06192,0x3a8180f90281a100,0x83005e1807279,0x6bb25f81f0051b40,0x40bd2e146889b000]))
  | 6 => (BitVec.ofNat _ (limbs64 [0xa850ebed20d3c42,0x18007401a042d038,0xf0e00c92900616e5,0x805fc854f4292f94,0x654abe09c78dac11,0xbde9b828990002fa,0xb31999a0db5d340d,0x28985a46f0207878,0x81e9fe5444848281,0x2bcd8593c5410781,0x1f0d8d82286b60d5,0xc80099bf18b57200,0x6a46005c7e040d,0xe0038b50101c0825,0x1480e341a5a427a5,0x919d00ab11604e05]))
  | 7 => (BitVec.ofNat _ (limbs64 [0xec7af140920803a1,0x67e08b02408523c7,0x11070016c01682b,0x592189b811d411a7,0xc8c5c311386fea0e,0x407948dcf3ea2944,0xb0aeef2320211092,0xfcbc25d4b02c87f5,0x4e166014421b8db0,0xc434007c2564f041,0x203e318d07946029,0xbc0f64400048ec68,0x56944901a10041f2,0x1e0c00a8ee03b680,0x8309050a0aab45aa,0x6e059669c1a812a]))
  | _ => 0

def samplesQ255 : Nat → Bits
  | 0 => (BitVec.ofNat _ (limbs64 [0xcc21080180000342,0xa058040850822411,0x82c3009006a19d,0x494958008f84080a,0x1d1980d4d0124109,0x8000000304cdaa00,0xd0690e000020128,0x8205089250034002,0x280019c122a5820a,0x100318105240,0x58004020c64081c2,0x606c082000020816,0x5104040a82080680,0x14409100104594,0x4435a02e1048e000,0x840240900014060]))
  | 1 => (BitVec.ofNat _ (limbs64 [0x4828054918209143,0x1208481850260400,0x8080e1002102a59d,0x45491540d780900b,0x1c08a0d190400084,0x84006485244f2041,0x542b852a802009c,0x290508808a49a402,0x2c9348e122804427,0x80000c310a104024,0x6900400862408080,0x2342808521a0814,0x402101528231042a,0x82a0402320100196,0xc42590680c4a101e,0x402680a40002410]))
  | 2 => (BitVec.ofNat _ (limbs64 [0xc10636045650706a,0xe7001e305c086f21,0x24c204098788afff,0xfe675fc7f976dd2b,0xa7f373b48a0200e5,0xd6d203d308e567a0,0x1c467204c52cc140,0xd14182aa1c8f288f,0x10c85db888a91f04,0xa8086860401ac948,0x4271602010e14980,0x530102fce1120c34,0xc96410080409800c,0x8456003a090527fe,0xb2fabc7f52003805,0x2852528402020004]))
  | 3 => (BitVec.ofNat _ (limbs64 [0x650da80ac9631db8,0xa32d0e5b0502e14b,0xd2bcd3081a24eff,0xff9ceffa7eedffd5,0xfbddfd6ee418612a,0xe39235355075bc93,0x441216bf09d54c65,0x6681b09843d1d8ab,0x87098e96ba610746,0xc950caa1c902a1c0,0x88d20ab153838504,0x53a41c2d603122e1,0x85240460602412b0,0x8319804c4143ff,0xff5d7bd7a590c019,0xd120950161000008]))
  | 4 => (BitVec.ofNat _ (limbs64 [0x382300444564428,0x400190c020484806,0x2411046004095862,0xb0a6202f20526060,0xe066072a08203a70,0x40850358ca100406,0x10b1030402acea03,0x422272920900b05,0x524c80008d481040,0x103a01806004090a,0x8240205518810e00,0x18010480010093a0,0x8802100425805900,0x2448054400660269,0x19ca049042110060,0x230181d08e240080]))
  | 5 => (BitVec.ofNat _ (limbs64 [0x380a282434d4c00,0x492132400519094a,0x702110200cb84262,0xb2b2a2bd003b27f4,0x42a65e0823811432,0x59e4991800005528,0x4281460d56046200,0x1042544905841a61,0x4028000a80583150,0x918c2800083a898,0x8618289100001c20,0x18315852d212280,0x288082240080a115,0x6000140c41803a69,0x2b824f81e0040b40,0x403d021428881000]))
  | 6 => (BitVec.ofNat _ (limbs64 [0x204000a000090800,0xa00104030000c8,0x20000440600000,0x10801000090294,0x800058d8400,0x2828882011000018,0xa208000010511400,0x98404400200050,0x8120220440000000,0x385820004002480,0x8d8200082011,0x80900300a56000,0x8020150062001,0x50018a0006809800,0x4300a1a40780,0x908c002011400a01]))
  | 7 => (BitVec.ofNat _ (limbs64 [0x40016000000004,0x2000080001000,0x204008200000000,0x0,0x100648a00,0x94000a3020044,0xa028090020001092,0x8380104a0200510,0x16200040020080,0x400000c00600001,0x4100000140008,0x8400400000400008,0x210411111124802,0x1228824022228000,0x82304a2,0x680086294108102]))
  | _ => 0

def compactPerms255 : Array (List Nat) := ([[]] : List (List Nat)).toArray

def compactDomains255 : Array (Sig × Nat) := ([(subcube 1 0, 9), (subcube 2 0, 9), (subcube 4 0, 9), (subcube 8 0, 9), (subcube 16 0, 9), (subcube 32 0, 9), (subcube 6 0, 9)] : List (Sig × Nat)).toArray

def compactWords255 : Nat → Nat
  | 0 => 0x71a5688ff
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
  | 10 => let v := readCompactBits compactWords255 (29 + 6*i) 6
    let n := v >>> 3
    let bits := readCompactBits compactWords255 (8 + 3*(v &&& 7)) (3*n)
    compactIDsFromBits bits 3 n
  | _ => []

def compactBucket255 (k : Nat) (i : Nat) : List Nat := match k with
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

def grid114 : CompactGrid := (114, 4, samplesP114, samplesQ114)
def tab114 : CompactTable := (compactCount114, compactPath114, compactLive114, compactPoolIDs114, compactBucket114)
def check114 (k : Nat) := compactNode grid114 tab114 compactDomains114 compactPerms114 k
def sliceSpecs114 : List SliceSpec := [(32, 0, 82, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains114 : ∀ d ∈ compactDomains114, Slice true (vars 114) (graphGoal 114) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(82, 4)]) (specs := sliceSpecs114)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound82
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs114 : properPairs (graphGoal 114) (asRow samplesP114) (asRow samplesQ114) :=
  compactPairs (g := grid114) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos114 : ∀ p ∈ compactPerms114, autoOK (graphGoal 114) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c114k4p0 : chartBlock (check114 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev114k4 : chartBlock (check114 4) 0 1 = true :=
  c114k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded114 : Impossible true (graphGoal 114) 4 (vars 114).toFinset := by
  apply compactRoot (g := grid114) (t := tab114) (dom := compactDomains114) (perms := compactPerms114) pairs114 domains114 autos114
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev114k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound114 : Lower true (vars 114) (graphGoal 114) 5 :=
  plain_low (hints := 17891392) (by decide +kernel) excluded114

def grid226 : CompactGrid := (226, 3, samplesP226, samplesQ226)
def tab226 : CompactTable := (compactCount226, compactPath226, compactLive226, compactPoolIDs226, compactBucket226)
def check226 (k : Nat) := compactNode grid226 tab226 compactDomains226 compactPerms226 k
def sliceSpecs226 : List SliceSpec := []
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains226 : ∀ d ∈ compactDomains226, Slice true (vars 226) (graphGoal 226) d.1 d.2 := by
  apply compactDomains_valid (earlier := []) (specs := sliceSpecs226)
  · simp
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs226 : properPairs (graphGoal 226) (asRow samplesP226) (asRow samplesQ226) :=
  compactPairs (g := grid226) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos226 : ∀ p ∈ compactPerms226, autoOK (graphGoal 226) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c226k3p0 : chartBlock (check226 3) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev226k3 : chartBlock (check226 3) 0 1 = true :=
  c226k3p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded226 : Impossible true (graphGoal 226) 3 (vars 226).toFinset := by
  apply compactRoot (g := grid226) (t := tab226) (dom := compactDomains226) (perms := compactPerms226) pairs226 domains226 autos226
  · intro k hk
    change k ≤ 3 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · exact lev226k3
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound226 : Lower true (vars 226) (graphGoal 226) 4 :=
  plain_low (hints := 1360003152) (by decide +kernel) excluded226

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound178 : Lower true (vars 178) (graphGoal 178) 4 :=
  carry_of (old := 178) (rep := 226) (swaps := [100]) (by decide +kernel) bound226

def grid242 : CompactGrid := (242, 6, samplesP242, samplesQ242)
def tab242 : CompactTable := (compactCount242, compactPath242, compactLive242, compactPoolIDs242, compactBucket242)
def check242 (k : Nat) := compactNode grid242 tab242 compactDomains242 compactPerms242 k
def sliceSpecs242 : List SliceSpec := [(128, 0, 114, 0, 0, 5, 5), (0, 128, 82, 32, 15728640, 5, 4), (16, 0, 226, 0, 0, 4, 4), (64, 0, 178, 0, 0, 4, 4), (32, 0, 82, 0, 0, 4, 4), (32, 128, 82, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains242 : ∀ d ∈ compactDomains242, Slice true (vars 242) (graphGoal 242) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(114, 5), (82, 4), (226, 4), (178, 4)]) (specs := sliceSpecs242)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · exact bound114
    · exact bound82
    · exact bound226
    · exact bound178
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
theorem c242k5p0 : chartBlock (check242 5) 0 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev242k5 : chartBlock (check242 5) 0 3 = true :=
  c242k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c242k6p0 : chartBlock (check242 6) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev242k6 : chartBlock (check242 6) 0 1 = true :=
  c242k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded242 : Impossible true (graphGoal 242) 6 (vars 242).toFinset := by
  apply compactRoot (g := grid242) (t := tab242) (dom := compactDomains242) (perms := compactPerms242) pairs242 domains242 autos242
  · intro k hk
    change k ≤ 6 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev242k4
    · exact lev242k5
    · exact lev242k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound242 : Lower true (vars 242) (graphGoal 242) 7 :=
  plain_low (hints := 1360068672) (by decide +kernel) excluded242

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound228 : Lower true (vars 228) (graphGoal 228) 4 :=
  carry_of (old := 228) (rep := 226) (swaps := [33, 117]) (by decide +kernel) bound226

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound198 : Lower true (vars 198) (graphGoal 198) 4 :=
  carry_of (old := 198) (rep := 226) (swaps := [97, 82]) (by decide +kernel) bound226

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound166 : Lower true (vars 166) (graphGoal 166) 4 :=
  carry_of (old := 166) (rep := 226) (swaps := [113, 98]) (by decide +kernel) bound226

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound102 : Lower true (vars 102) (graphGoal 102) 4 :=
  carry_of (old := 102) (rep := 226) (swaps := [114, 101]) (by decide +kernel) bound226

def grid230 : CompactGrid := (230, 6, samplesP230, samplesQ230)
def tab230 : CompactTable := (compactCount230, compactPath230, compactLive230, compactPoolIDs230, compactBucket230)
def check230 (k : Nat) := compactNode grid230 tab230 compactDomains230 compactPerms230 k
def sliceSpecs230 : List SliceSpec := [(2, 0, 228, 0, 0, 4, 4), (4, 0, 226, 0, 0, 4, 4), (32, 0, 198, 0, 0, 4, 4), (64, 0, 166, 0, 0, 4, 4), (128, 0, 102, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains230 : ∀ d ∈ compactDomains230, Slice true (vars 230) (graphGoal 230) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(228, 4), (226, 4), (198, 4), (166, 4), (102, 4)]) (specs := sliceSpecs230)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact bound228
    · exact bound226
    · exact bound198
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
theorem c230k5p0 : chartBlock (check230 5) 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev230k5 : chartBlock (check230 5) 0 2 = true :=
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
  plain_low (hints := 554698320) (by decide +kernel) excluded230

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound214 : Lower true (vars 214) (graphGoal 214) 7 :=
  carry_of (old := 214) (rep := 242) (swaps := [97, 82]) (by decide +kernel) bound242

def grid118 : CompactGrid := (118, 5, samplesP118, samplesQ118)
def tab118 : CompactTable := (compactCount118, compactPath118, compactLive118, compactPoolIDs118, compactBucket118)
def check118 (k : Nat) := compactNode grid118 tab118 compactDomains118 compactPerms118 k
def sliceSpecs118 : List SliceSpec := [(4, 0, 114, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains118 : ∀ d ∈ compactDomains118, Slice true (vars 118) (graphGoal 118) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(114, 5)]) (specs := sliceSpecs118)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound114
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs118 : properPairs (graphGoal 118) (asRow samplesP118) (asRow samplesQ118) :=
  compactPairs (g := grid118) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos118 : ∀ p ∈ compactPerms118, autoOK (graphGoal 118) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c118k5p0 : chartBlock (check118 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev118k5 : chartBlock (check118 5) 0 1 = true :=
  c118k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded118 : Impossible true (graphGoal 118) 5 (vars 118).toFinset := by
  apply compactRoot (g := grid118) (t := tab118) (dom := compactDomains118) (perms := compactPerms118) pairs118 domains118 autos118
  · intro k hk
    change k ≤ 5 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev118k5
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound118 : Lower true (vars 118) (graphGoal 118) 6 :=
  plain_low (hints := 17892928) (by decide +kernel) excluded118

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
  plain_low (hints := 578160128) (by decide +kernel) excluded244

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound182 : Lower true (vars 182) (graphGoal 182) 5 :=
  carry_of (old := 182) (rep := 244) (swaps := [97, 82]) (by decide +kernel) bound244

def grid246 : CompactGrid := (246, 8, samplesP246, samplesQ246)
def tab246 : CompactTable := (compactCount246, compactPath246, compactLive246, compactPoolIDs246, compactBucket246)
def check246 (k : Nat) := compactNode grid246 tab246 compactDomains246 compactPerms246 k
def sliceSpecs246 : List SliceSpec := [(4, 0, 242, 0, 0, 7, 7), (16, 0, 230, 0, 0, 7, 7), (32, 0, 214, 0, 0, 7, 7), (128, 0, 118, 0, 0, 6, 6), (0, 128, 82, 36, 15732480, 6, 4), (2, 0, 244, 0, 0, 5, 5), (64, 0, 182, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains246 : ∀ d ∈ compactDomains246, Slice true (vars 246) (graphGoal 246) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(242, 7), (230, 7), (214, 7), (118, 6), (82, 4), (244, 5), (182, 5)]) (specs := sliceSpecs246)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound242
    · exact bound230
    · exact bound214
    · exact bound118
    · exact bound82
    · exact bound244
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
  plain_low (hints := 554763840) (by decide +kernel) excluded246

def grid254 : CompactGrid := (254, 8, samplesP254, samplesQ254)
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
  plain_low (hints := 554792512) (by decide +kernel) excluded254

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound225 : Lower true (vars 225) (graphGoal 225) 5 :=
  carry_of (old := 225) (rep := 114) (swaps := [16, 101, 116]) (by decide +kernel) bound114

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound209 : Lower true (vars 209) (graphGoal 209) 5 :=
  carry_of (old := 209) (rep := 114) (swaps := [16, 117]) (by decide +kernel) bound114

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound177 : Lower true (vars 177) (graphGoal 177) 5 :=
  carry_of (old := 177) (rep := 114) (swaps := [16, 84, 118]) (by decide +kernel) bound114

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound113 : Lower true (vars 113) (graphGoal 113) 5 :=
  carry_of (old := 113) (rep := 114) (swaps := [16]) (by decide +kernel) bound114

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound161 : Lower true (vars 161) (graphGoal 161) 4 :=
  carry_of (old := 161) (rep := 82) (swaps := [16, 84, 118]) (by decide +kernel) bound82

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound81 : Lower true (vars 81) (graphGoal 81) 4 :=
  carry_of (old := 81) (rep := 82) (swaps := [16]) (by decide +kernel) bound82

def grid241 : CompactGrid := (241, 7, samplesP241, samplesQ241)
def tab241 : CompactTable := (compactCount241, compactPath241, compactLive241, compactPoolIDs241, compactBucket241)
def check241 (k : Nat) := compactNode grid241 tab241 compactDomains241 compactPerms241 k
def sliceSpecs241 : List SliceSpec := [(16, 0, 225, 0, 0, 5, 5), (32, 0, 209, 0, 0, 5, 5), (64, 0, 177, 0, 0, 5, 5), (128, 0, 113, 0, 0, 5, 5), (80, 0, 161, 0, 0, 4, 4), (160, 0, 81, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains241 : ∀ d ∈ compactDomains241, Slice true (vars 241) (graphGoal 241) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(225, 5), (209, 5), (177, 5), (113, 5), (161, 4), (81, 4)]) (specs := sliceSpecs241)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound225
    · exact bound209
    · exact bound177
    · exact bound113
    · exact bound161
    · exact bound81
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
theorem c241k4p0 : chartBlock (check241 4) 0 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev241k4 : chartBlock (check241 4) 0 3 = true :=
  c241k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c241k5p0 : chartBlock (check241 5) 0 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c241k5p1 : chartBlock (check241 5) 8 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev241k5 : chartBlock (check241 5) 0 10 = true :=
  (chartBlock_join (a := 8) (b := 2) c241k5p0 c241k5p1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c241k6p0 : chartBlock (check241 6) 0 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev241k6 : chartBlock (check241 6) 0 3 = true :=
  c241k6p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c241k7p0 : chartBlock (check241 7) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev241k7 : chartBlock (check241 7) 0 1 = true :=
  c241k7p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded241 : Impossible true (graphGoal 241) 7 (vars 241).toFinset := by
  apply compactRoot (g := grid241) (t := tab241) (dom := compactDomains241) (perms := compactPerms241) pairs241 domains241 autos241
  · intro k hk
    change k ≤ 7 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev241k4
    · exact lev241k5
    · exact lev241k6
    · exact lev241k7
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound241 : Lower true (vars 241) (graphGoal 241) 8 :=
  plain_low (hints := 4) (by decide +kernel) excluded241

def grid249 : CompactGrid := (249, 8, samplesP249, samplesQ249)
def tab249 : CompactTable := (compactCount249, compactPath249, compactLive249, compactPoolIDs249, compactBucket249)
def check249 (k : Nat) := compactNode grid249 tab249 compactDomains249 compactPerms249 k
def sliceSpecs249 : List SliceSpec := [(8, 0, 241, 0, 0, 8, 8)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains249 : ∀ d ∈ compactDomains249, Slice true (vars 249) (graphGoal 249) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(241, 8)]) (specs := sliceSpecs249)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound241
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs249 : properPairs (graphGoal 249) (asRow samplesP249) (asRow samplesQ249) :=
  compactPairs (g := grid249) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos249 : ∀ p ∈ compactPerms249, autoOK (graphGoal 249) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c249k8p0 : chartBlock (check249 8) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev249k8 : chartBlock (check249 8) 0 1 = true :=
  c249k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded249 : Impossible true (graphGoal 249) 8 (vars 249).toFinset := by
  apply compactRoot (g := grid249) (t := tab249) (dom := compactDomains249) (perms := compactPerms249) pairs249 domains249 autos249
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
    · exact lev249k8
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound249 : Lower true (vars 249) (graphGoal 249) 9 :=
  plain_low (hints := 28676) (by decide +kernel) excluded249

def grid253 : CompactGrid := (253, 8, samplesP253, samplesQ253)
def tab253 : CompactTable := (compactCount253, compactPath253, compactLive253, compactPoolIDs253, compactBucket253)
def check253 (k : Nat) := compactNode grid253 tab253 compactDomains253 compactPerms253 k
def sliceSpecs253 : List SliceSpec := [(4, 0, 249, 0, 0, 9, 9)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains253 : ∀ d ∈ compactDomains253, Slice true (vars 253) (graphGoal 253) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(249, 9)]) (specs := sliceSpecs253)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound249
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
  plain_low (hints := 30212) (by decide +kernel) excluded253

def grid251 : CompactGrid := (251, 8, samplesP251, samplesQ251)
def tab251 : CompactTable := (compactCount251, compactPath251, compactLive251, compactPoolIDs251, compactBucket251)
def check251 (k : Nat) := compactNode grid251 tab251 compactDomains251 compactPerms251 k
def sliceSpecs251 : List SliceSpec := [(2, 0, 249, 0, 0, 9, 9)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains251 : ∀ d ∈ compactDomains251, Slice true (vars 251) (graphGoal 251) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(249, 9)]) (specs := sliceSpecs251)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound249
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
theorem c251k8p0 : chartBlock (check251 8) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev251k8 : chartBlock (check251 8) 0 1 = true :=
  c251k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded251 : Impossible true (graphGoal 251) 8 (vars 251).toFinset := by
  apply compactRoot (g := grid251) (t := tab251) (dom := compactDomains251) (perms := compactPerms251) pairs251 domains251 autos251
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
    · exact lev251k8
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound251 : Lower true (vars 251) (graphGoal 251) 9 :=
  plain_low (hints := 28740) (by decide +kernel) excluded251

def grid247 : CompactGrid := (247, 8, samplesP247, samplesQ247)
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
theorem c247k8p0 : chartBlock (check247 8) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev247k8 : chartBlock (check247 8) 0 1 = true :=
  c247k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded247 : Impossible true (graphGoal 247) 8 (vars 247).toFinset := by
  apply compactRoot (g := grid247) (t := tab247) (dom := compactDomains247) (perms := compactPerms247) pairs247 domains247 autos247
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
    · exact lev247k8
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound247 : Lower true (vars 247) (graphGoal 247) 9 :=
  plain_low (hints := 1604) (by decide +kernel) excluded247

def grid229 : CompactGrid := (229, 5, samplesP229, samplesQ229)
def tab229 : CompactTable := (compactCount229, compactPath229, compactLive229, compactPoolIDs229, compactBucket229)
def check229 (k : Nat) := compactNode grid229 tab229 compactDomains229 compactPerms229 k
def sliceSpecs229 : List SliceSpec := [(4, 0, 225, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains229 : ∀ d ∈ compactDomains229, Slice true (vars 229) (graphGoal 229) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(225, 5)]) (specs := sliceSpecs229)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound225
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
theorem c229k5p0 : chartBlock (check229 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev229k5 : chartBlock (check229 5) 0 1 = true :=
  c229k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded229 : Impossible true (graphGoal 229) 5 (vars 229).toFinset := by
  apply compactRoot (g := grid229) (t := tab229) (dom := compactDomains229) (perms := compactPerms229) pairs229 domains229 autos229
  · intro k hk
    change k ≤ 5 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev229k5
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound229 : Lower true (vars 229) (graphGoal 229) 6 :=
  plain_low (hints := 1541) (by decide +kernel) excluded229

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound227 : Lower true (vars 227) (graphGoal 227) 6 :=
  carry_of (old := 227) (rep := 229) (swaps := [33, 117]) (by decide +kernel) bound229

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound167 : Lower true (vars 167) (graphGoal 167) 6 :=
  carry_of (old := 167) (rep := 118) (swaps := [64, 81, 118]) (by decide +kernel) bound118

def grid199 : CompactGrid := (199, 4, samplesP199, samplesQ199)
def tab199 : CompactTable := (compactCount199, compactPath199, compactLive199, compactPoolIDs199, compactBucket199)
def check199 (k : Nat) := compactNode grid199 tab199 compactDomains199 compactPerms199 k
def sliceSpecs199 : List SliceSpec := [(1, 0, 198, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains199 : ∀ d ∈ compactDomains199, Slice true (vars 199) (graphGoal 199) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(198, 4)]) (specs := sliceSpecs199)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound198
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs199 : properPairs (graphGoal 199) (asRow samplesP199) (asRow samplesQ199) :=
  compactPairs (g := grid199) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos199 : ∀ p ∈ compactPerms199, autoOK (graphGoal 199) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c199k4p0 : chartBlock (check199 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev199k4 : chartBlock (check199 4) 0 1 = true :=
  c199k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded199 : Impossible true (graphGoal 199) 4 (vars 199).toFinset := by
  apply compactRoot (g := grid199) (t := tab199) (dom := compactDomains199) (perms := compactPerms199) pairs199 domains199 autos199
  · intro k hk
    change k ≤ 4 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev199k4
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound199 : Lower true (vars 199) (graphGoal 199) 5 :=
  plain_low (hints := 1638) (by decide +kernel) excluded199

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound103 : Lower true (vars 103) (graphGoal 103) 5 :=
  carry_of (old := 103) (rep := 199) (swaps := [33, 117]) (by decide +kernel) bound199

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound165 : Lower true (vars 165) (graphGoal 165) 5 :=
  carry_of (old := 165) (rep := 114) (swaps := [96, 82, 84, 113, 97]) (by decide +kernel) bound114

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound163 : Lower true (vars 163) (graphGoal 163) 5 :=
  carry_of (old := 163) (rep := 114) (swaps := [64, 81, 118]) (by decide +kernel) bound114

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound195 : Lower true (vars 195) (graphGoal 195) 4 :=
  carry_of (old := 195) (rep := 226) (swaps := [80, 97]) (by decide +kernel) bound226

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound101 : Lower true (vars 101) (graphGoal 101) 4 :=
  carry_of (old := 101) (rep := 226) (swaps := [16, 114, 101]) (by decide +kernel) bound226

def grid231 : CompactGrid := (231, 8, samplesP231, samplesQ231)
def tab231 : CompactTable := (compactCount231, compactPath231, compactLive231, compactPoolIDs231, compactBucket231)
def check231 (k : Nat) := compactNode grid231 tab231 compactDomains231 compactPerms231 k
def sliceSpecs231 : List SliceSpec := [(1, 0, 230, 0, 0, 7, 7), (2, 0, 229, 0, 0, 6, 6), (4, 0, 227, 0, 0, 6, 6), (64, 0, 167, 0, 0, 6, 6), (32, 0, 199, 0, 0, 5, 5), (128, 0, 103, 0, 0, 5, 5), (6, 0, 225, 0, 0, 5, 5), (66, 0, 165, 0, 0, 5, 5), (68, 0, 163, 0, 0, 5, 5), (33, 0, 198, 0, 0, 4, 4), (36, 0, 195, 0, 0, 4, 4), (130, 0, 101, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains231 : ∀ d ∈ compactDomains231, Slice true (vars 231) (graphGoal 231) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(230, 7), (229, 6), (227, 6), (167, 6), (199, 5), (103, 5), (225, 5), (165, 5), (163, 5), (198, 4), (195, 4), (101, 4)]) (specs := sliceSpecs231)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound230
    · exact bound229
    · exact bound227
    · exact bound167
    · exact bound199
    · exact bound103
    · exact bound225
    · exact bound165
    · exact bound163
    · exact bound198
    · exact bound195
    · exact bound101
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
theorem c231k4p0 : chartBlock (check231 4) 0 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev231k4 : chartBlock (check231 4) 0 2 = true :=
  c231k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c231k5p0 : chartBlock (check231 5) 0 7 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev231k5 : chartBlock (check231 5) 0 7 = true :=
  c231k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c231k6p0 : chartBlock (check231 6) 0 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c231k6p1 : chartBlock (check231 6) 8 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c231k6p2 : chartBlock (check231 6) 16 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c231k6p3 : chartBlock (check231 6) 24 3 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev231k6 : chartBlock (check231 6) 0 27 = true :=
  (chartBlock_join (a := 16) (b := 11) (chartBlock_join (a := 8) (b := 8) c231k6p0 c231k6p1) (chartBlock_join (a := 8) (b := 3) c231k6p2 c231k6p3))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c231k7p0 : chartBlock (check231 7) 0 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c231k7p1 : chartBlock (check231 7) 8 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev231k7 : chartBlock (check231 7) 0 9 = true :=
  (chartBlock_join (a := 8) (b := 1) c231k7p0 c231k7p1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c231k8p0 : chartBlock (check231 8) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev231k8 : chartBlock (check231 8) 0 1 = true :=
  c231k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded231 : Impossible true (graphGoal 231) 8 (vars 231).toFinset := by
  apply compactRoot (g := grid231) (t := tab231) (dom := compactDomains231) (perms := compactPerms231) pairs231 domains231 autos231
  · intro k hk
    change k ≤ 8 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev231k4
    · exact lev231k5
    · exact lev231k6
    · exact lev231k7
    · exact lev231k8
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound231 : Lower true (vars 231) (graphGoal 231) 9 :=
  plain_low (hints := 1621) (by decide +kernel) excluded231

def grid239 : CompactGrid := (239, 8, samplesP239, samplesQ239)
def tab239 : CompactTable := (compactCount239, compactPath239, compactLive239, compactPoolIDs239, compactBucket239)
def check239 (k : Nat) := compactNode grid239 tab239 compactDomains239 compactPerms239 k
def sliceSpecs239 : List SliceSpec := [(8, 0, 231, 0, 0, 9, 9)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains239 : ∀ d ∈ compactDomains239, Slice true (vars 239) (graphGoal 239) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(231, 9)]) (specs := sliceSpecs239)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound231
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
    · rfl
    · rfl
    · exact lev239k8
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound239 : Lower true (vars 239) (graphGoal 239) 9 :=
  plain_low (hints := 30293) (by decide +kernel) excluded239

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
theorem bound147 : Lower true (vars 147) (graphGoal 147) 4 :=
  carry_of (old := 147) (rep := 226) (swaps := [80, 97, 100]) (by decide +kernel) bound226

def grid211 : CompactGrid := (211, 6, samplesP211, samplesQ211)
def tab211 : CompactTable := (compactCount211, compactPath211, compactLive211, compactPoolIDs211, compactBucket211)
def check211 (k : Nat) := compactNode grid211 tab211 compactDomains211 compactPerms211 k
def sliceSpecs211 : List SliceSpec := [(2, 0, 209, 0, 0, 5, 5), (128, 0, 83, 0, 0, 5, 5), (0, 128, 82, 1, 15, 5, 4), (16, 0, 195, 0, 0, 4, 4), (64, 0, 147, 0, 0, 4, 4), (1, 128, 82, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains211 : ∀ d ∈ compactDomains211, Slice true (vars 211) (graphGoal 211) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(209, 5), (83, 5), (82, 4), (195, 4), (147, 4)]) (specs := sliceSpecs211)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl
    · exact bound209
    · exact bound83
    · exact bound82
    · exact bound195
    · exact bound147
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
theorem c211k4p0 : chartBlock (check211 4) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev211k4 : chartBlock (check211 4) 0 1 = true :=
  c211k4p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c211k5p0 : chartBlock (check211 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev211k5 : chartBlock (check211 5) 0 1 = true :=
  c211k5p0
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
    · exact lev211k4
    · exact lev211k5
    · exact lev211k6
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound211 : Lower true (vars 211) (graphGoal 211) 7 :=
  plain_low (hints := 68) (by decide +kernel) excluded211

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound213 : Lower true (vars 213) (graphGoal 213) 6 :=
  carry_of (old := 213) (rep := 229) (swaps := [84, 118]) (by decide +kernel) bound229

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound86 : Lower true (vars 86) (graphGoal 86) 5 :=
  carry_of (old := 86) (rep := 114) (swaps := [97, 82]) (by decide +kernel) bound114

def grid87 : CompactGrid := (87, 5, samplesP87, samplesQ87)
def tab87 : CompactTable := (compactCount87, compactPath87, compactLive87, compactPoolIDs87, compactBucket87)
def check87 (k : Nat) := compactNode grid87 tab87 compactDomains87 compactPerms87 k
def sliceSpecs87 : List SliceSpec := [(1, 0, 86, 0, 0, 5, 5)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains87 : ∀ d ∈ compactDomains87, Slice true (vars 87) (graphGoal 87) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(86, 5)]) (specs := sliceSpecs87)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound86
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
theorem c87k5p0 : chartBlock (check87 5) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev87k5 : chartBlock (check87 5) 0 1 = true :=
  c87k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded87 : Impossible true (graphGoal 87) 5 (vars 87).toFinset := by
  apply compactRoot (g := grid87) (t := tab87) (dom := compactDomains87) (perms := compactPerms87) pairs87 domains87 autos87
  · intro k hk
    change k ≤ 5 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev87k5
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound87 : Lower true (vars 87) (graphGoal 87) 6 :=
  plain_low (hints := 1604) (by decide +kernel) excluded87

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound151 : Lower true (vars 151) (graphGoal 151) 5 :=
  carry_of (old := 151) (rep := 244) (swaps := [32, 65, 82, 100]) (by decide +kernel) bound244

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound85 : Lower true (vars 85) (graphGoal 85) 5 :=
  carry_of (old := 85) (rep := 114) (swaps := [96, 82, 97]) (by decide +kernel) bound114

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound149 : Lower true (vars 149) (graphGoal 149) 4 :=
  carry_of (old := 149) (rep := 226) (swaps := [16, 114, 100, 117]) (by decide +kernel) bound226

def grid215 : CompactGrid := (215, 8, samplesP215, samplesQ215)
def tab215 : CompactTable := (compactCount215, compactPath215, compactLive215, compactPoolIDs215, compactBucket215)
def check215 (k : Nat) := compactNode grid215 tab215 compactDomains215 compactPerms215 k
def sliceSpecs215 : List SliceSpec := [(1, 0, 214, 0, 0, 7, 7), (4, 0, 211, 0, 0, 7, 7), (2, 0, 213, 0, 0, 6, 6), (128, 0, 87, 0, 0, 6, 6), (0, 128, 82, 5, 3855, 6, 4), (16, 0, 199, 0, 0, 5, 5), (64, 0, 151, 0, 0, 5, 5), (130, 0, 85, 0, 0, 5, 5), (17, 0, 198, 0, 0, 4, 4), (66, 0, 149, 0, 0, 4, 4)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains215 : ∀ d ∈ compactDomains215, Slice true (vars 215) (graphGoal 215) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(214, 7), (211, 7), (213, 6), (87, 6), (82, 4), (199, 5), (151, 5), (85, 5), (198, 4), (149, 4)]) (specs := sliceSpecs215)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound214
    · exact bound211
    · exact bound213
    · exact bound87
    · exact bound82
    · exact bound199
    · exact bound151
    · exact bound85
    · exact bound198
    · exact bound149
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem pairs215 : properPairs (graphGoal 215) (asRow samplesP215) (asRow samplesQ215) :=
  compactPairs (g := grid215) (by decide +kernel) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem autos215 : ∀ p ∈ compactPerms215, autoOK (graphGoal 215) (p.map swapRows).reverse = true :=
  compactAutos_valid (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c215k5p0 : chartBlock (check215 5) 0 7 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev215k5 : chartBlock (check215 5) 0 7 = true :=
  c215k5p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c215k6p0 : chartBlock (check215 6) 0 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c215k6p1 : chartBlock (check215 6) 8 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c215k6p2 : chartBlock (check215 6) 16 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c215k6p3 : chartBlock (check215 6) 24 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev215k6 : chartBlock (check215 6) 0 26 = true :=
  (chartBlock_join (a := 16) (b := 10) (chartBlock_join (a := 8) (b := 8) c215k6p0 c215k6p1) (chartBlock_join (a := 8) (b := 2) c215k6p2 c215k6p3))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c215k7p0 : chartBlock (check215 7) 0 8 = true := by
  iterate 1 (all_goals apply compactHalves)
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c215k7p1 : chartBlock (check215 7) 8 2 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev215k7 : chartBlock (check215 7) 0 10 = true :=
  (chartBlock_join (a := 8) (b := 2) c215k7p0 c215k7p1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem c215k8p0 : chartBlock (check215 8) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev215k8 : chartBlock (check215 8) 0 1 = true :=
  c215k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded215 : Impossible true (graphGoal 215) 8 (vars 215).toFinset := by
  apply compactRoot (g := grid215) (t := tab215) (dom := compactDomains215) (perms := compactPerms215) pairs215 domains215 autos215
  · intro k hk
    change k ≤ 8 at hk
    interval_cases k
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · exact lev215k5
    · exact lev215k6
    · exact lev215k7
    · exact lev215k8
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound215 : Lower true (vars 215) (graphGoal 215) 9 :=
  plain_low (hints := 1604) (by decide +kernel) excluded215

def grid223 : CompactGrid := (223, 8, samplesP223, samplesQ223)
def tab223 : CompactTable := (compactCount223, compactPath223, compactLive223, compactPoolIDs223, compactBucket223)
def check223 (k : Nat) := compactNode grid223 tab223 compactDomains223 compactPerms223 k
def sliceSpecs223 : List SliceSpec := [(8, 0, 215, 0, 0, 9, 9)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains223 : ∀ d ∈ compactDomains223, Slice true (vars 223) (graphGoal 223) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(215, 9)]) (specs := sliceSpecs223)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl
    · exact bound215
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
theorem c223k8p0 : chartBlock (check223 8) 0 1 = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lev223k8 : chartBlock (check223 8) 0 1 = true :=
  c223k8p0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem excluded223 : Impossible true (graphGoal 223) 8 (vars 223).toFinset := by
  apply compactRoot (g := grid223) (t := tab223) (dom := compactDomains223) (perms := compactPerms223) pairs223 domains223 autos223
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
    · exact lev223k8
  · decide +kernel
  · rfl
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem bound223 : Lower true (vars 223) (graphGoal 223) 9 :=
  plain_low (hints := 30276) (by decide +kernel) excluded223

def grid255 : CompactGrid := (255, 10, samplesP255, samplesQ255)
def tab255 : CompactTable := (compactCount255, compactPath255, compactLive255, compactPoolIDs255, compactBucket255)
def check255 (k : Nat) := compactNode grid255 tab255 compactDomains255 compactPerms255 k
def sliceSpecs255 : List SliceSpec := [(1, 0, 254, 0, 0, 9, 9), (2, 0, 253, 0, 0, 9, 9), (4, 0, 251, 0, 0, 9, 9), (8, 0, 247, 0, 0, 9, 9), (16, 0, 239, 0, 0, 9, 9), (32, 0, 223, 0, 0, 9, 9), (6, 0, 249, 0, 0, 9, 9)]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem domains255 : ∀ d ∈ compactDomains255, Slice true (vars 255) (graphGoal 255) d.1 d.2 := by
  apply compactDomains_valid (earlier := [(254, 9), (253, 9), (251, 9), (247, 9), (239, 9), (223, 9), (249, 9)]) (specs := sliceSpecs255)
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact bound254
    · exact bound253
    · exact bound251
    · exact bound247
    · exact bound239
    · exact bound223
    · exact bound249
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
  plain_low (hints := 30276) (by decide +kernel) excluded255
def winningGates : List Gate := [⟨.or,[5,4]⟩, ⟨.or,[2,0]⟩, ⟨.or,[1,0]⟩, ⟨.or,[6,8]⟩, ⟨.or,[4,9]⟩, ⟨.or,[3,9]⟩, ⟨.or,[5,13]⟩, ⟨.and,[11,10]⟩, ⟨.and,[6,12]⟩, ⟨.and,[7,14]⟩, ⟨.or,[17,16]⟩, ⟨.or,[18,15]⟩]
theorem winningLegal : ∀ g ∈ winningGates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [winningGates,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem winningCorrect : ∀ x : Fin 8 → Bool, Circuit.eval ⟨winningGates,19⟩ (List.ofFn x) = edge8 x := by decide +kernel
set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
theorem asListed : ∀ x : Fin 8 → Bool, edge8 x = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by decide +kernel
end PEqualNP.Outside.L_meta_14968

open PEqualNP.Outside.L_meta_14968 PEqualNP.CircuitLowerBounds
theorem PEqualNP.Outside.L_meta_14968 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
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
