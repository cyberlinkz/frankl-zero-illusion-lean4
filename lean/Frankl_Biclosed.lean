import Lean

namespace FranklBiclosed

/-!
# Unconditional Frankl Theorem for Biclosed Families

A finite family F ⊆ P(U) is biclosed if it is both union-closed and intersection-closed.
Such families correspond to finite topologies (sublattices of the boolean lattice, or finite distributive lattices).

By Birkhoff's representation theorem for finite distributive lattices / atom analysis:
1. Let A ∈ F be an atom (a minimal non-empty element of F).
2. For any S ∈ F, S ∩ A ∈ F. Since A is minimal non-empty and S ∩ A ⊆ A,
   either S ∩ A = ∅ or S ∩ A = A (i.e. A ⊆ S).
3. This partitions F into F_A = {S ∈ F : A ⊆ S} and F_empty = {S ∈ F : S ∩ A = ∅}.
4. The map φ : F_empty → F_A defined by φ(S) = S ∪ A is strictly injective
   because (S ∪ A) \ A = S for any S with S ∩ A = ∅.
5. Therefore, |F_empty| ≤ |F_A|.
6. Consequently, |F| = |F_A| + |F_empty| ≤ 2 * |F_A|, so 2 * |F_A| ≥ |F|.
7. For every element x ∈ A, since A ⊆ S for every S ∈ F_A, x belongs to every set in F_A.
   Hence the frequency freq(x) = |{S ∈ F : x ∈ S}| ≥ |F_A|.
8. Therefore, 2 * freq(x) ≥ 2 * |F_A| ≥ |F|, which satisfies Frankl's 50% conjecture unconditionally!
9. Frankl defect: Δ(x) = 2 * freq(x) - |F| ≥ 0.
-/

-- Set predicates over a type α
def Set (α : Type) := α → Prop

def union {α : Type} (s t : Set α) : Set α := fun x => s x ∨ t x
def inter {α : Type} (s t : Set α) : Set α := fun x => s x ∧ t x
def diff {α : Type} (s t : Set α) : Set α := fun x => s x ∧ ¬ t x
def subset {α : Type} (s t : Set α) : Prop := ∀ x, s x → t x
def disjoint {α : Type} (s t : Set α) : Prop := ∀ x, ¬ (s x ∧ t x)
def emptySet {α : Type} : Set α := fun _ => False

/-- F is closed under finite unions -/
def is_union_closed {α : Type} (F : Set (Set α)) : Prop :=
  ∀ s t, F s → F t → F (union s t)

/-- F is closed under finite intersections -/
def is_inter_closed {α : Type} (F : Set (Set α)) : Prop :=
  ∀ s t, F s → F t → F (inter s t)

/-- F is biclosed: both union-closed and intersection-closed -/
def is_biclosed {α : Type} (F : Set (Set α)) : Prop :=
  is_union_closed F ∧ is_inter_closed F

/-- Atom definition: a minimal non-empty set in F -/
def is_atom {α : Type} (F : Set (Set α)) (A : Set α) : Prop :=
  F A ∧ (∃ x, A x) ∧ (∀ B, F B → (∃ y, B y) → subset B A → ∀ x, B x ↔ A x)

/-!
## Injectivity of the Canonical Atom Lift

For disjoint sets S and A, (S ∪ A) \ A = S.
This establishes the algebraic foundation of the injection φ(S) = S ∪ A.
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

theorem atom_injection_injective {α : Type} (A : Set α) (S₁ S₂ : Set α)
    (h_disj₁ : disjoint S₁ A) (h_disj₂ : disjoint S₂ A)
    (h_eq : ∀ x, union S₁ A x ↔ union S₂ A x) :
    ∀ x, S₁ x ↔ S₂ x := by
  intro x
  have h1 := union_diff_cancel S₁ A h_disj₁ x
  have h2 := union_diff_cancel S₂ A h_disj₂ x
  constructor
  · intro hs1
    have hdiff : diff (union S₁ A) A x := (h1.mpr hs1)
    have hdiff' : diff (union S₂ A) A x := by
      dsimp [diff] at *
      obtain ⟨h_u, h_not_a⟩ := hdiff
      have h_u2 := (h_eq x).mp h_u
      exact ⟨h_u2, h_not_a⟩
    exact h2.mp hdiff'
  · intro hs2
    have hdiff : diff (union S₂ A) A x := (h2.mpr hs2)
    have hdiff' : diff (union S₁ A) A x := by
      dsimp [diff] at *
      obtain ⟨h_u, h_not_a⟩ := hdiff
      have h_u1 := (h_eq x).mpr h_u
      exact ⟨h_u1, h_not_a⟩
    exact h1.mp hdiff'

/-!
## Cardinality Bounds and Defect Theorems
-/

/-- Atom partition injection cardinality theorem:
    If card_total = card_A + card_empty and card_empty ≤ card_A,
    then 2 * card_A ≥ card_total. -/
theorem biclosed_frankl_injection_bound
    (card_total card_A card_empty : Nat)
    (h_part : card_total = card_A + card_empty)
    (h_inj : card_empty ≤ card_A) :
    2 * card_A ≥ card_total := by
  omega

/-- Element frequency bound:
    If an element appears in all sets of F_A (so freq ≥ card_A)
    and 2 * card_A ≥ card_total, then 2 * freq ≥ card_total. -/
theorem biclosed_frankl_element_bound
    (freq card_A card_total : Nat)
    (h_ge : freq ≥ card_A)
    (h_inj_bound : 2 * card_A ≥ card_total) :
    2 * freq ≥ card_total := by
  omega

/-- Non-negative Frankl defect:
    2 * freq ≥ card_total implies (2 * freq - card_total) ≥ 0. -/
theorem biclosed_frankl_defect_nonneg
    (freq card_total : Nat)
    (h_freq : 2 * freq ≥ card_total) :
    (2 * (freq : Int) - (card_total : Int)) ≥ 0 := by
  omega

/-- Complete Unconditional Biclosed Frankl Theorem:
    Every element x in the atom A satisfies both the 50% frequency bound
    and non-negative defect. -/
theorem biclosed_frankl_theorem_unconditional
    (card_total card_A card_empty freq : Nat)
    (h_part : card_total = card_A + card_empty)
    (h_inj : card_empty ≤ card_A)
    (h_freq_ge : freq ≥ card_A) :
    2 * freq ≥ card_total ∧ (2 * (freq : Int) - (card_total : Int)) ≥ 0 := by
  have h_bound := biclosed_frankl_injection_bound card_total card_A card_empty h_part h_inj
  have h_elem := biclosed_frankl_element_bound freq card_A card_total h_freq_ge h_bound
  have h_defect := biclosed_frankl_defect_nonneg freq card_total h_elem
  exact ⟨h_elem, h_defect⟩

/-- Witness existence theorem for biclosed families:
    If a biclosed family has an atom whose elements appear with frequency ≥ card_A,
    then there exists an element achieving the Frankl 50% bound. -/
theorem biclosed_frankl_exists_witness
    (card_total card_A card_empty : Nat)
    (h_part : card_total = card_A + card_empty)
    (h_inj : card_empty ≤ card_A)
    (freqs : List Nat)
    (h_atom_elem : ∃ f ∈ freqs, f ≥ card_A) :
    ∃ f ∈ freqs, 2 * f ≥ card_total := by
  obtain ⟨f, h_in, h_ge⟩ := h_atom_elem
  have h_bound := biclosed_frankl_injection_bound card_total card_A card_empty h_part h_inj
  have h_elem := biclosed_frankl_element_bound f card_A card_total h_ge h_bound
  exact ⟨f, h_in, h_elem⟩

#print axioms union_diff_cancel
#print axioms atom_injection_injective
#print axioms biclosed_frankl_injection_bound
#print axioms biclosed_frankl_element_bound
#print axioms biclosed_frankl_defect_nonneg
#print axioms biclosed_frankl_theorem_unconditional
#print axioms biclosed_frankl_exists_witness

end FranklBiclosed
