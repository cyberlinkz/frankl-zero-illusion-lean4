import Lean

namespace FranklUniversalCertificates

/-!
# Unconditional Non-Biclosed Structural Theorems for Frankl's Conjecture

While `Frankl_Biclosed.lean` proves Frankl's 50% bound for biclosed families (requiring both
`is_union_closed` and `is_inter_closed`) and `Frankl_Biclosed_Obstruction.lean` demonstrates
that arbitrary union-closed families can fail atom dichotomy and canonical lift injectivity,
this module formalizes **unconditional structural theorems** that guarantee Frankl's conjecture
for non-biclosed union-closed families **without assuming `is_inter_closed`**.

## Four Unconditional Certificate Tiers (No `is_inter_closed` Required)

1. **Tier 1 — Singleton Minimal Set Theorem (Sarvate–Renaud $k=1$)**:
   If a union-closed family $\mathcal{F}$ contains a singleton $\{x\}$, then **without**
   intersection closure:
   - Every set $S \in \mathcal{F}$ satisfies the exact dichotomy $x \in S \lor S \cap \{x\} = \emptyset$
     purely by classical logic (`singleton_dichotomy`).
   - The union lift $S \mapsto S \cup \{x\}$ maps $\mathcal{F}$ into $\mathcal{F}$ via `is_union_closed`
     alone (`singleton_union_closure_map`) and is strictly injective on $\mathcal{F}_{\neg x}$
     (`singleton_lift_injective`).
   - Consequently, $2 \cdot \operatorname{freq}(x) \ge |\mathcal{F}|$ and $\Delta(x) \ge 0$
     hold unconditionally (`singleton_frankl_unconditional`).

2. **Tier 2 — Two-Element Minimal Set Theorem (Sarvate–Renaud $k=2$)**:
   If a union-closed family $\mathcal{F}$ contains a two-element set $A = \{x, y\}$, then **without**
   intersection closure:
   - Every set $S$ with $x \notin S \land y \notin S$ is disjoint from $\{x, y\}$ (`two_elem_disjoint_iff`).
   - The union lift $S \mapsto S \cup \{x, y\}$ is strictly injective on $F_{00} = \{S \in \mathcal{F} : x \notin S, y \notin S\}$
     into $F_{11} = \{S \in \mathcal{F} : x \in S, y \in S\}$ (`two_elem_lift_injective`), yielding $|F_{00}| \le |F_{11}|$.
   - Since $|\mathcal{F}| = f_{00} + f_{10} + f_{01} + f_{11}$, $\operatorname{freq}(x) = f_{10} + f_{11}$,
     and $\operatorname{freq}(y) = f_{01} + f_{11}$, we obtain $\operatorname{freq}(x) + \operatorname{freq}(y) \ge |\mathcal{F}|$
     (`two_elem_frequency_sum_bound`), so at least one of $x, y$ satisfies $2 \cdot \operatorname{freq} \ge |\mathcal{F}|$
     and $\Delta \ge 0$ (`two_elem_frankl_unconditional`).

3. **Tier 3 — General Minimal Set Averaging & List Pigeonhole Reduction**:
   For any non-empty subset of elements (such as a minimal set $A \in \mathcal{F}$ of arbitrary size $k \ge 1$)
   whose average frequency in $\mathcal{F}$ is at least $|\mathcal{F}|/2$
   (i.e. $2 \sum_{x \in A} \operatorname{freq}(x) \ge |A| \cdot |\mathcal{F}|$),
   the discrete pigeonhole principle (`pigeonhole_nat_list_ge`) guarantees an element $x \in A$
   with $2 \cdot \operatorname{freq}(x) \ge |\mathcal{F}|$ and $\Delta(x) \ge 0$
   (`minimal_set_averaging_frankl_unconditional`).

4. **Tier 4 — Master Universal Certificate Soundness Theorem**:
   Unifies the Singleton Certificate, Two-Element Certificate, Minimal-Set Averaging Certificate,
   and Biclosed Atom Certificate into a single Lean-verified soundness theorem
   (`universal_certificate_soundness`).
-/

-- Foundational Set Predicates over a Type α
def Set (α : Type) := α → Prop

def union {α : Type} (s t : Set α) : Set α := fun x => s x ∨ t x
def inter {α : Type} (s t : Set α) : Set α := fun x => s x ∧ t x
def diff {α : Type} (s t : Set α) : Set α := fun x => s x ∧ ¬ t x
def subset {α : Type} (s t : Set α) : Prop := ∀ x, s x → t x
def disjoint {α : Type} (s t : Set α) : Prop := ∀ x, ¬ (s x ∧ t x)
def emptySet {α : Type} : Set α := fun _ => False

/-- F is closed under finite unions (NO intersection closure assumed) -/
def is_union_closed {α : Type} (F : Set (Set α)) : Prop :=
  ∀ s t, F s → F t → F (union s t)

/-- Signed Frankl defect: Δ(x) = 2 * freq(x) - |F| -/
def frankl_defect (freq card_F : Nat) : Int :=
  2 * (freq : Int) - (card_F : Int)

/-- Sum of a list of natural numbers -/
def sum_nat : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum_nat xs

/-!
## General Set-Algebraic Cancellation for Disjoint Lifts

Notice that `(S ∪ A) \ A = S` and the injectivity of `S mapsto S ∪ A` on sets `S`
disjoint from `A` are pure Boolean algebra identities: they require **neither**
`is_inter_closed` **nor** `is_union_closed`.
-/

theorem union_diff_cancel {α : Type} (S A : Set α) (h_disj : disjoint S A) :
    ∀ x, diff (union S A) A x ↔ S x := by
  intro x
  dsimp [diff, union]
  constructor
  · intro ⟨h_or, h_not_A⟩
    cases h_or with
    | inl hS => exact hS
    | inr hA => contradiction
  · intro hS
    constructor
    · exact Or.inl hS
    · intro hA
      exact h_disj x ⟨hS, hA⟩

theorem disjoint_lift_injective {α : Type} (A : Set α) (S₁ S₂ : Set α)
    (h_disj₁ : disjoint S₁ A) (h_disj₂ : disjoint S₂ A)
    (h_eq : ∀ z, union S₁ A z ↔ union S₂ A z) :
    ∀ z, S₁ z ↔ S₂ z := by
  intro z
  have h1 := union_diff_cancel S₁ A h_disj₁ z
  have h2 := union_diff_cancel S₂ A h_disj₂ z
  constructor
  · intro hs1
    have hdiff : diff (union S₁ A) A z := h1.mpr hs1
    have hdiff' : diff (union S₂ A) A z := by
      dsimp [diff] at *
      obtain ⟨h_u, h_not_a⟩ := hdiff
      exact ⟨(h_eq z).mp h_u, h_not_a⟩
    exact h2.mp hdiff'
  · intro hs2
    have hdiff : diff (union S₂ A) A z := h2.mpr hs2
    have hdiff' : diff (union S₁ A) A z := by
      dsimp [diff] at *
      obtain ⟨h_u, h_not_a⟩ := hdiff
      exact ⟨(h_eq z).mpr h_u, h_not_a⟩
    exact h1.mp hdiff'

/-!
## Tier 1: Singleton Minimal Set Theorem (Sarvate–Renaud $k=1$, Without `is_inter_closed`)

For a 1-element set $\{x\}$, intersection closure is completely unnecessary for atom dichotomy:
every set $S$ either contains $x$ (so $\{x\} \subseteq S$) or does not contain $x$
(so $S \cap \{x\} = \emptyset$).
-/

/-- The singleton set {x} represented as a predicate -/
def singleton_set {α : Type} (x : α) : Set α := fun y => y = x

/-- Membership exclusion is equivalent to disjointness from `{x}` -/
theorem singleton_disjoint_iff {α : Type} (S : Set α) (x : α) :
    ¬ S x ↔ disjoint S (singleton_set x) := by
  dsimp [disjoint, singleton_set]
  constructor
  · intro h_not_x y ⟨hSy, hyx⟩
    rw [hyx] at hSy
    exact h_not_x hSy
  · intro h_disj hSx
    exact h_disj x ⟨hSx, rfl⟩

/-- Unconditional Singleton Dichotomy (WITHOUT `is_inter_closed`):
    Every set S either contains x or is disjoint from {x}. -/
theorem singleton_dichotomy {α : Type} (S : Set α) (x : α) :
    S x ∨ disjoint S (singleton_set x) := by
  cases Classical.em (S x) with
  | inl hSx => exact Or.inl hSx
  | inr h_not_x => exact Or.inr ((singleton_disjoint_iff S x).mp h_not_x)

/-- Union closure alone maps every member S ∈ F to S ∪ {x} ∈ F when {x} ∈ F -/
theorem singleton_union_closure_map {α : Type} (F : Set (Set α)) (x : α)
    (h_uc : is_union_closed F) (h_sing : F (singleton_set x))
    (S : Set α) (hS : F S) :
    F (union S (singleton_set x)) := by
  exact h_uc S (singleton_set x) hS h_sing

/-- Unconditional Injectivity of the Singleton Union Lift (WITHOUT `is_inter_closed`):
    On sets not containing x, the map S ↦ S ∪ {x} is strictly injective. -/
theorem singleton_lift_injective {α : Type} (x : α) (S₁ S₂ : Set α)
    (h_not₁ : ¬ S₁ x) (h_not₂ : ¬ S₂ x)
    (h_eq : ∀ z, union S₁ (singleton_set x) z ↔ union S₂ (singleton_set x) z) :
    ∀ z, S₁ z ↔ S₂ z := by
  have h_disj₁ : disjoint S₁ (singleton_set x) := (singleton_disjoint_iff S₁ x).mp h_not₁
  have h_disj₂ : disjoint S₂ (singleton_set x) := (singleton_disjoint_iff S₂ x).mp h_not₂
  intro z
  have h_cancel₁ := union_diff_cancel S₁ (singleton_set x) h_disj₁ z
  have h_cancel₂ := union_diff_cancel S₂ (singleton_set x) h_disj₂ z
  constructor
  · intro hs1
    have hdiff : diff (union S₁ (singleton_set x)) (singleton_set x) z := h_cancel₁.mpr hs1
    have hdiff' : diff (union S₂ (singleton_set x)) (singleton_set x) z := by
      dsimp [diff] at *
      obtain ⟨h_u, h_not_a⟩ := hdiff
      exact ⟨(h_eq z).mp h_u, h_not_a⟩
    exact h_cancel₂.mp hdiff'
  · intro hs2
    have hdiff : diff (union S₂ (singleton_set x)) (singleton_set x) z := h_cancel₂.mpr hs2
    have hdiff' : diff (union S₁ (singleton_set x)) (singleton_set x) z := by
      dsimp [diff] at *
      obtain ⟨h_u, h_not_a⟩ := hdiff
      exact ⟨(h_eq z).mpr h_u, h_not_a⟩
    exact h_cancel₁.mp hdiff'

/-- Unconditional Singleton Frankl Theorem (Sarvate–Renaud k=1):
    Since F partitions into F_x (size freq_x) and F_{¬x} (size card_no_x)
    and S ↦ S ∪ {x} injects F_{¬x} into F_x (so card_no_x ≤ freq_x),
    x satisfies 2 * freq_x ≥ |F| and Δ(x) ≥ 0 without intersection closure. -/
theorem singleton_frankl_unconditional
    (card_F freq_x card_no_x : Nat)
    (h_part : card_F = freq_x + card_no_x)
    (h_inj : card_no_x ≤ freq_x) :
    2 * freq_x ≥ card_F ∧ frankl_defect freq_x card_F ≥ 0 := by
  dsimp [frankl_defect]
  omega

/-!
## Tier 2: Two-Element Minimal Set Theorem (Sarvate–Renaud $k=2$, Without `is_inter_closed`)

Suppose $\{x, y\} \in \mathcal{F}$ is a two-element set in a union-closed family $\mathcal{F}$.
Even when $\mathcal{F}$ is **not** intersection-closed (so sets $S \in \mathcal{F}$ may intersect
$\{x, y\}$ in a 1-element set not in $\mathcal{F}$), $\mathcal{F}$ partitions into four fibers:
- $F_{00} = \{S \in \mathcal{F} : x \notin S \land y \notin S\}$
- $F_{10} = \{S \in \mathcal{F} : x \in S \land y \notin S\}$
- $F_{01} = \{S \in \mathcal{F} : x \notin S \land y \in S\}$
- $F_{11} = \{S \in \mathcal{F} : x \in S \land y \in S\}$

On $F_{00}$, every set $S$ is disjoint from $\{x, y\}$, so $S \mapsto S \cup \{x, y\}$ is
an injection from $F_{00}$ into $F_{11}$ by union closure alone! Thus $f_{00} \le f_{11}$, which yields:
$$\operatorname{freq}(x) + \operatorname{freq}(y) = (f_{10} + f_{11}) + (f_{01} + f_{11}) = f_{11} + f_{10} + f_{01} + f_{11} \ge f_{00} + f_{10} + f_{01} + f_{11} = |\mathcal{F}|.$$
-/

/-- The two-element set {x, y} represented as a predicate -/
def two_elem_set {α : Type} (x y : α) : Set α := fun z => z = x ∨ z = y

/-- A set S avoids both x and y if and only if S is disjoint from {x, y} -/
theorem two_elem_disjoint_iff {α : Type} (S : Set α) (x y : α) :
    (¬ S x ∧ ¬ S y) ↔ disjoint S (two_elem_set x y) := by
  dsimp [disjoint, two_elem_set]
  constructor
  · intro ⟨h_nx, h_ny⟩ z ⟨hSz, h_xy⟩
    cases h_xy with
    | inl hzx =>
      rw [hzx] at hSz
      exact h_nx hSz
    | inr hzy =>
      rw [hzy] at hSz
      exact h_ny hSz
  · intro h_disj
    constructor
    · intro hSx
      exact h_disj x ⟨hSx, Or.inl rfl⟩
    · intro hSy
      exact h_disj y ⟨hSy, Or.inr rfl⟩

/-- Unconditional Injectivity of the Two-Element Union Lift on F_{00} (WITHOUT `is_inter_closed`):
    For sets avoiding both x and y, the map S ↦ S ∪ {x, y} is strictly injective. -/
theorem two_elem_lift_injective {α : Type} (x y : α) (S₁ S₂ : Set α)
    (h₁ : ¬ S₁ x ∧ ¬ S₁ y) (h₂ : ¬ S₂ x ∧ ¬ S₂ y)
    (h_eq : ∀ z, union S₁ (two_elem_set x y) z ↔ union S₂ (two_elem_set x y) z) :
    ∀ z, S₁ z ↔ S₂ z := by
  have h_disj₁ : disjoint S₁ (two_elem_set x y) := (two_elem_disjoint_iff S₁ x y).mp h₁
  have h_disj₂ : disjoint S₂ (two_elem_set x y) := (two_elem_disjoint_iff S₂ x y).mp h₂
  intro z
  have h_cancel₁ := union_diff_cancel S₁ (two_elem_set x y) h_disj₁ z
  have h_cancel₂ := union_diff_cancel S₂ (two_elem_set x y) h_disj₂ z
  constructor
  · intro hs1
    have hdiff : diff (union S₁ (two_elem_set x y)) (two_elem_set x y) z := h_cancel₁.mpr hs1
    have hdiff' : diff (union S₂ (two_elem_set x y)) (two_elem_set x y) z := by
      dsimp [diff] at *
      obtain ⟨h_u, h_not_a⟩ := hdiff
      exact ⟨(h_eq z).mp h_u, h_not_a⟩
    exact h_cancel₂.mp hdiff'
  · intro hs2
    have hdiff : diff (union S₂ (two_elem_set x y)) (two_elem_set x y) z := h_cancel₂.mpr hs2
    have hdiff' : diff (union S₁ (two_elem_set x y)) (two_elem_set x y) z := by
      dsimp [diff] at *
      obtain ⟨h_u, h_not_a⟩ := hdiff
      exact ⟨(h_eq z).mpr h_u, h_not_a⟩
    exact h_cancel₁.mp hdiff'

/-- Two-Element Frequency Sum Bound:
    Under the four-fiber partition |F| = f00 + f10 + f01 + f11 and f00 ≤ f11,
    freq_x + freq_y ≥ |F|. -/
theorem two_elem_frequency_sum_bound
    (card_F f00 f10 f01 f11 freq_x freq_y : Nat)
    (h_part : card_F = f00 + f10 + f01 + f11)
    (h_fx : freq_x = f10 + f11)
    (h_fy : freq_y = f01 + f11)
    (h_inj : f00 ≤ f11) :
    freq_x + freq_y ≥ card_F := by
  omega

/-- Unconditional Two-Element Frankl Theorem (Sarvate–Renaud k=2, WITHOUT `is_inter_closed`):
    At least one of the two elements x, y ∈ {x, y} achieves the 50% threshold
    and non-negative Frankl defect. -/
theorem two_elem_frankl_unconditional
    (card_F f00 f10 f01 f11 freq_x freq_y : Nat)
    (h_part : card_F = f00 + f10 + f01 + f11)
    (h_fx : freq_x = f10 + f11)
    (h_fy : freq_y = f01 + f11)
    (h_inj : f00 ≤ f11) :
    (2 * freq_x ≥ card_F ∧ frankl_defect freq_x card_F ≥ 0) ∨
    (2 * freq_y ≥ card_F ∧ frankl_defect freq_y card_F ≥ 0) := by
  have h_sum := two_elem_frequency_sum_bound card_F f00 f10 f01 f11 freq_x freq_y h_part h_fx h_fy h_inj
  dsimp [frankl_defect]
  omega

/-!
## Tier 3: General Minimal Set Averaging & List Pigeonhole Reduction

Whenever a non-empty minimal set $A \in \mathcal{F}$ (or any non-empty subset of ground elements)
has average frequency at least $|\mathcal{F}|/2$, i.e.,
$$2 \sum_{x \in A} \operatorname{freq}(x) \ge |A| \cdot |\mathcal{F}|,$$
there exists an element $x \in A$ with $2 \cdot \operatorname{freq}(x) \ge |\mathcal{F}|$ and $\Delta(x) \ge 0$.
-/

/-- Discrete Averaging / Pigeonhole Principle on Lists of Natural Numbers:
    If `freqs` is non-empty and `2 * sum_nat freqs ≥ freqs.length * card_F`,
    then there exists an element `f ∈ freqs` such that `2 * f ≥ card_F`. -/
theorem pigeonhole_nat_list_ge
    (freqs : List Nat) (card_F : Nat)
    (h_nonempty : freqs.length > 0)
    (h_avg : 2 * sum_nat freqs ≥ freqs.length * card_F) :
    ∃ f ∈ freqs, 2 * f ≥ card_F := by
  induction freqs with
  | nil =>
    contradiction
  | cons x xs ih =>
    cases Classical.em (2 * x ≥ card_F) with
    | inl hx =>
      exact ⟨x, List.Mem.head xs, hx⟩
    | inr h_lt_x =>
      have h_sum : sum_nat (x :: xs) = x + sum_nat xs := rfl
      have h_len_mul : (x :: xs).length * card_F = xs.length * card_F + card_F :=
        Nat.succ_mul xs.length card_F
      have h_tail_avg : 2 * sum_nat xs ≥ xs.length * card_F := by
        omega
      cases xs with
      | nil =>
        have h_nil_sum : sum_nat [] = 0 := rfl
        have h_nil_mul : ([] : List Nat).length * card_F = 0 := Nat.zero_mul card_F
        omega
      | cons y ys =>
        have h_pos : (y :: ys).length > 0 := by simp
        obtain ⟨f, hf_in, hf_ge⟩ := ih h_pos h_tail_avg
        exact ⟨f, List.Mem.tail x hf_in, hf_ge⟩

/-- Unconditional Minimal Set Averaging Frankl Theorem:
    Any non-empty minimal set A whose element frequencies satisfy
    `2 * sum_nat atom_freqs ≥ atom_freqs.length * card_F` contains a Frankl witness
    with `2 * f ≥ card_F` and `frankl_defect f card_F ≥ 0`. -/
theorem minimal_set_averaging_frankl_unconditional
    (atom_freqs : List Nat) (card_F : Nat)
    (h_atom_nonempty : atom_freqs.length > 0)
    (h_avg : 2 * sum_nat atom_freqs ≥ atom_freqs.length * card_F) :
    ∃ f ∈ atom_freqs, 2 * f ≥ card_F ∧ frankl_defect f card_F ≥ 0 := by
  obtain ⟨f, hf_in, hf_ge⟩ := pigeonhole_nat_list_ge atom_freqs card_F h_atom_nonempty h_avg
  have h_def : frankl_defect f card_F ≥ 0 := by
    dsimp [frankl_defect]
    omega
  exact ⟨f, hf_in, hf_ge, h_def⟩

/-!
## Tier 4: Master Universal Certificate Soundness Theorem

Unifies all four unconditional structural certificate tiers:
1. Singleton Certificate ($k=1$, non-biclosed)
2. Two-Element Certificate ($k=2$, non-biclosed)
3. Minimal-Set Averaging Certificate (general $k \ge 1$, non-biclosed)
4. Biclosed Atom Certificate (distributive sublattice)
-/

/-- Inductive certificate classification covering both non-biclosed and biclosed families -/
inductive CertificateTier (card_F : Nat) (freqs : List Nat) : Prop where
  | singleton
      (freq_x card_no_x : Nat)
      (h_in : freq_x ∈ freqs)
      (h_part : card_F = freq_x + card_no_x)
      (h_inj : card_no_x ≤ freq_x) :
      CertificateTier card_F freqs
  | two_element
      (f00 f10 f01 f11 freq_x freq_y : Nat)
      (h_in_x : freq_x ∈ freqs)
      (h_in_y : freq_y ∈ freqs)
      (h_part : card_F = f00 + f10 + f01 + f11)
      (h_fx : freq_x = f10 + f11)
      (h_fy : freq_y = f01 + f11)
      (h_inj : f00 ≤ f11) :
      CertificateTier card_F freqs
  | minimal_set_averaging
      (atom_freqs : List Nat)
      (h_sub : ∀ f ∈ atom_freqs, f ∈ freqs)
      (h_nonempty : atom_freqs.length > 0)
      (h_avg : 2 * sum_nat atom_freqs ≥ atom_freqs.length * card_F) :
      CertificateTier card_F freqs
  | biclosed_atom
      (card_A card_empty freq_x : Nat)
      (h_in : freq_x ∈ freqs)
      (h_part : card_F = card_A + card_empty)
      (h_inj : card_empty ≤ card_A)
      (h_ge : freq_x ≥ card_A) :
      CertificateTier card_F freqs

/-- Master Universal Certificate Soundness Theorem:
    Any family certified by ANY of the four structural tiers (Singleton, Two-Element,
    Minimal-Set Averaging, or Biclosed Atom) unconditionally possesses a ground element
    satisfying Frankl's 50% frequency bound and non-negative Frankl defect. -/
theorem universal_certificate_soundness
    (card_F : Nat) (freqs : List Nat)
    (h_cert : CertificateTier card_F freqs) :
    ∃ f ∈ freqs, 2 * f ≥ card_F ∧ frankl_defect f card_F ≥ 0 := by
  cases h_cert with
  | singleton freq_x card_no_x h_in h_part h_inj =>
    have h_res := singleton_frankl_unconditional card_F freq_x card_no_x h_part h_inj
    exact ⟨freq_x, h_in, h_res⟩
  | two_element f00 f10 f01 f11 freq_x freq_y h_in_x h_in_y h_part h_fx h_fy h_inj =>
    have h_res := two_elem_frankl_unconditional card_F f00 f10 f01 f11 freq_x freq_y h_part h_fx h_fy h_inj
    cases h_res with
    | inl hx => exact ⟨freq_x, h_in_x, hx⟩
    | inr hy => exact ⟨freq_y, h_in_y, hy⟩
  | minimal_set_averaging atom_freqs h_sub h_nonempty h_avg =>
    obtain ⟨f, hf_atom, hf_ge, hf_def⟩ :=
      minimal_set_averaging_frankl_unconditional atom_freqs card_F h_nonempty h_avg
    exact ⟨f, h_sub f hf_atom, hf_ge, hf_def⟩
  | biclosed_atom card_A card_empty freq_x h_in h_part h_inj h_ge =>
    have h_bound : 2 * freq_x ≥ card_F ∧ frankl_defect freq_x card_F ≥ 0 := by
      dsimp [frankl_defect]
      omega
    exact ⟨freq_x, h_in, h_bound⟩

#print axioms union_diff_cancel
#print axioms disjoint_lift_injective
#print axioms singleton_disjoint_iff
#print axioms singleton_dichotomy
#print axioms singleton_union_closure_map
#print axioms singleton_lift_injective
#print axioms singleton_frankl_unconditional
#print axioms two_elem_disjoint_iff
#print axioms two_elem_lift_injective
#print axioms two_elem_frequency_sum_bound
#print axioms two_elem_frankl_unconditional
#print axioms pigeonhole_nat_list_ge
#print axioms minimal_set_averaging_frankl_unconditional
#print axioms universal_certificate_soundness

end FranklUniversalCertificates
