/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.PID
public import TauCeti.Algebra.MonoidAlgebra.Basis
public import TauCeti.RepresentationTheory.FDRep
public import TauCeti.RepresentationTheory.Subrepresentation

/-!
# The augmentation subrepresentation of a permutation representation

For a monoid action on `X`, the augmentation subrepresentation of `k[X]` consists of the vectors
whose coefficients sum to zero. For a group action on finite `X`, the sum of the standard basis
vectors spans an invariant subrepresentation, called the invariant line. Both constructions are
defined over any semiring. If `X` is nonempty, the invariant line is equivalent to the trivial
representation on `k`: every coordinate of a vector in the line is its scalar coefficient.

For finite `X` over a division ring, the augmentation subrepresentation has dimension `|X| - 1`.
When `|X|` is nonzero in the coefficients, the invariant line complements it. The equivalence
`TauCeti.ofMulActionEquivProdAugmentation` expresses this splitting: its first component is the
average of the coefficients, and its second subtracts that multiple of the sum of the standard
basis. For empty `X`, both subrepresentations are zero and are still complementary.

Over a field, the character of the augmentation subrepresentation is the permutation character
minus the trivial character, provided `X` is finite and nonempty. This identity holds even when
the characteristic divides `|X|`, so the invariant line is not a complement. These constructions
underlie the standard representation of the symmetric group.

## Main definitions and results

* `TauCeti.augmentationSubrepresentation`: the kernel of the coefficient sum.
* `TauCeti.permutationSum` and `TauCeti.invariantLine`: the sum of the standard basis and its span.
* `TauCeti.invariantLineEquivTrivial`: the invariant line as the trivial representation on `k`.
* `TauCeti.MonoidAlgebra.ker_sumCoords_basis_eq_span`: the augmentation kernel is spanned by
  differences of standard basis vectors from a fixed one.
* `TauCeti.isCompl_invariantLine_augmentationSubrepresentation_iff`: the two subrepresentations
  are complementary exactly when `X` is empty or its cardinality is nonzero in a division ring.
* `TauCeti.ofMulActionEquivProdAugmentation`: the explicit splitting as trivial plus augmentation.
* `TauCeti.finrank_augmentationSubrepresentation`: the dimension is `|X| - 1`.
* `TauCeti.character_augmentationSubrepresentation`: the character is the permutation character
  minus `1`.

## Implementation notes

The augmentation is `Module.Basis.sumCoords` for `MonoidAlgebra.basis X k`. This linear map
requires no multiplication on `X`, unlike the ring homomorphism augmenting a monoid algebra.
The two maps agree when `X` is a monoid: both send `single x a` to `a`.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, §2.3.
-/

public section

namespace TauCeti

/-! ### The augmentation subrepresentation -/

section Subrep

variable (k : Type*) [Semiring k] (G X : Type*) [Monoid G] [MulAction G X]

/-- The coefficient sum is invariant under the permutation action. -/
@[simp]
theorem sumCoords_basis_ofMulAction (g : G) (v : MonoidAlgebra k X) :
    (MonoidAlgebra.basis X k).sumCoords (Representation.ofMulAction k G X g v) =
      (MonoidAlgebra.basis X k).sumCoords v := by
  have hcoeff : (Representation.ofMulAction k G X g v).coeff =
      Finsupp.mapDomain (g • ·) v.coeff := by
    simp [Representation.ofMulAction_def]
  simp only [Module.Basis.coe_sumCoords, MonoidAlgebra.basis_repr, hcoeff]
  exact Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

/-- The **augmentation subrepresentation** of `k[X]`: the elements whose coefficients sum to
zero. -/
noncomputable def augmentationSubrepresentation :
    Subrepresentation (Representation.ofMulAction k G X) where
  toSubmodule := LinearMap.ker (MonoidAlgebra.basis X k).sumCoords
  apply_mem_toSubmodule g v hv := by
    simpa only [LinearMap.mem_ker, sumCoords_basis_ofMulAction] using hv

@[simp]
theorem toSubmodule_augmentationSubrepresentation :
    (augmentationSubrepresentation k G X).toSubmodule =
      LinearMap.ker (MonoidAlgebra.basis X k).sumCoords :=
  -- `(rfl)`, not `rfl`: the body of `augmentationSubrepresentation` is not `@[expose]`d, so this
  -- must not be inferred `@[defeq]`.
  (rfl)

variable {k G X}

@[simp]
theorem mem_augmentationSubrepresentation_iff {v : MonoidAlgebra k X} :
    v ∈ augmentationSubrepresentation k G X ↔ (MonoidAlgebra.basis X k).sumCoords v = 0 :=
  Iff.rfl

end Subrep

section SubrepRing

variable {k : Type*} [Ring k] {G X : Type*} [Monoid G] [MulAction G X]

/-- A difference of two standard basis vectors has vanishing augmentation. -/
theorem single_sub_single_mem_augmentationSubrepresentation (x y : X) :
    (MonoidAlgebra.single x 1 - MonoidAlgebra.single y 1 : MonoidAlgebra k X) ∈
      augmentationSubrepresentation k G X := by
  rw [mem_augmentationSubrepresentation_iff, map_sub]
  simp

end SubrepRing

/-! ### The invariant line -/

section PermutationSum

variable (k : Type*) [Semiring k] (X : Type*) [Fintype X]

/-- The sum of the standard basis of `k[X]`, for a finite index type. -/
noncomputable def permutationSum : MonoidAlgebra k X := ∑ x : X, MonoidAlgebra.single x (1 : k)

variable {k X}

@[simp]
theorem coeff_permutationSum (x : X) : (permutationSum k X).coeff x = 1 := by
  classical
  simp [permutationSum, MonoidAlgebra.coeff_single, Finsupp.single_apply, Finset.sum_ite_eq']

/-- The augmentation of the sum of the standard basis is the cardinality of the index type.

Deliberately not `@[simp]`: `simp` already proves this from `TauCeti.coeff_permutationSum` and the
generic basis API, so tagging it would be a `simpNF` violation. -/
theorem sumCoords_basis_permutationSum :
    (MonoidAlgebra.basis X k).sumCoords (permutationSum k X) = Fintype.card X := by
  simp

/-- For nonempty `X` and nontrivial coefficients, the sum of the standard basis is nonzero. -/
theorem permutationSum_ne_zero [Nonempty X] [Nontrivial k] : permutationSum k X ≠ 0 := by
  intro h
  have hone := coeff_permutationSum (k := k) (Classical.arbitrary X)
  rw [h] at hone
  simp at hone

end PermutationSum

section InvariantLine

variable (k : Type*) [Semiring k] (G X : Type*) [Group G] [MulAction G X] [Fintype X]

/-- The sum of the standard basis is fixed by the group action. -/
@[simp]
theorem ofMulAction_permutationSum (g : G) :
    Representation.ofMulAction k G X g (permutationSum k X) = permutationSum k X := by
  rw [permutationSum, map_sum]
  simp only [Representation.ofMulAction_single]
  exact Fintype.sum_equiv (MulAction.toPerm g) _ _ fun _ => rfl

/-- The **invariant line** of `k[X]`: the line spanned by the sum of the standard basis, as a
subrepresentation. -/
noncomputable def invariantLine : Subrepresentation (Representation.ofMulAction k G X) where
  toSubmodule := Submodule.span k {permutationSum k X}
  apply_mem_toSubmodule g v hv := by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul, ofMulAction_permutationSum]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

@[simp]
theorem toSubmodule_invariantLine :
    (invariantLine k G X).toSubmodule = Submodule.span k {permutationSum k X} :=
  -- `(rfl)`, not `rfl`: the body of `invariantLine` is not `@[expose]`d, so this must not be
  -- inferred `@[defeq]`.
  (rfl)

/-- The group acts trivially on the invariant line. -/
@[simp]
theorem toRepresentation_invariantLine :
    (invariantLine k G X).toRepresentation = Representation.trivial k G _ := by
  refine DFunLike.ext _ _ fun g => LinearMap.ext fun w => Subtype.ext ?_
  have hw : (w : MonoidAlgebra k X) ∈ Submodule.span k {permutationSum k X} := by
    rw [← toSubmodule_invariantLine k G X]; exact w.2
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw
  -- both sides act on the underlying element of `k[X]`: `Subrepresentation.toRepresentation` is
  -- the restriction of the ambient action, and the trivial representation is the identity
  simp only [Subrepresentation.toRepresentation_apply, LinearMap.coe_restrict_apply,
    Representation.trivial_apply]
  rw [← hc, map_smul, ofMulAction_permutationSum]

variable {k G X}

/-- The elements of the invariant line are exactly the multiples of the sum of the standard
basis. -/
@[simp]
theorem mem_invariantLine_iff {v : MonoidAlgebra k X} :
    v ∈ invariantLine k G X ↔ ∃ c : k, c • permutationSum k X = v :=
  Submodule.mem_span_singleton

end InvariantLine

/-! ### The invariant line as the trivial representation -/

section InvariantLineTrivial

variable (k : Type*) [Semiring k] (G X : Type*) [Group G] [MulAction G X] [Fintype X]
  [Nonempty X]

/-- For a nonempty index type, the invariant line is the trivial representation on the scalars.
The inverse sends a scalar to that multiple of the sum of the standard basis. -/
noncomputable def invariantLineEquivTrivial :
    (invariantLine k G X).toRepresentation.Equiv (Representation.trivial k G k) :=
  Representation.Equiv.mk
    { toFun := fun v => (v : MonoidAlgebra k X).coeff (Classical.arbitrary X)
      invFun := fun c => ⟨c • permutationSum k X, mem_invariantLine_iff.mpr ⟨c, rfl⟩⟩
      left_inv := fun v => by
        obtain ⟨c, hc⟩ := mem_invariantLine_iff.mp v.2
        apply Subtype.ext
        simp [← hc]
      right_inv := fun c => by simp
      map_add' := fun v w => by simp
      map_smul' := fun c v => by simp }
    fun g => by rw [toRepresentation_invariantLine]; rfl

/-- The scalar `c` names the multiple `c • permutationSum k X` of the sum of the standard basis. -/
@[simp]
theorem coe_invariantLineEquivTrivial_symm_apply (c : k) :
    (((invariantLineEquivTrivial k G X).symm c : (invariantLine k G X).toSubmodule) :
      MonoidAlgebra k X) = c • permutationSum k X :=
  (rfl)

/-- Conversely, the scalar naming a vector of the invariant line is its coordinate along the sum of
the standard basis: that multiple of the sum is the vector again. -/
@[simp]
theorem invariantLineEquivTrivial_apply_smul (v : (invariantLine k G X).toSubmodule) :
    invariantLineEquivTrivial k G X v • permutationSum k X = (v : MonoidAlgebra k X) := by
  rw [← coe_invariantLineEquivTrivial_symm_apply k G X (invariantLineEquivTrivial k G X v),
    (invariantLineEquivTrivial k G X).symm_apply_apply]

/-- Every coordinate of a vector in the invariant line is its corresponding scalar. -/
@[simp]
theorem coeff_eq_invariantLineEquivTrivial (v : (invariantLine k G X).toSubmodule) (x : X) :
    (v : MonoidAlgebra k X).coeff x = invariantLineEquivTrivial k G X v := by
  simpa only [MonoidAlgebra.coeff_smul_apply, coeff_permutationSum, smul_eq_mul, mul_one]
    using (congrArg (fun w : MonoidAlgebra k X => w.coeff x)
      (invariantLineEquivTrivial_apply_smul k G X v)).symm

/-- The invariant line has rank one over a semiring satisfying the strong rank condition. -/
@[simp]
theorem finrank_invariantLine [StrongRankCondition k] :
    Module.finrank k (invariantLine k G X).toSubmodule = 1 := by
  rw [LinearEquiv.finrank_eq (invariantLineEquivTrivial k G X).toLinearEquiv]
  simp

end InvariantLineTrivial

/-! ### The dimension of the augmentation subrepresentation -/

section Dimension

variable {k : Type*} [DivisionRing k] {G X : Type*} [Monoid G] [MulAction G X] [Fintype X]

/-- The augmentation subrepresentation has dimension one less than the cardinality of `X`.  For an
empty `X` both sides are zero, the subtraction being truncated. -/
@[simp]
theorem finrank_augmentationSubrepresentation :
    Module.finrank k (augmentationSubrepresentation k G X).toSubmodule = Fintype.card X - 1 := by
  rcases isEmpty_or_nonempty X with hX | hX
  · have hbot : (augmentationSubrepresentation k G X).toSubmodule = ⊥ :=
      Submodule.eq_bot_iff _ |>.mpr fun v _ =>
        MonoidAlgebra.coeff_eq_zero.mp (Finsupp.ext fun x => isEmptyElim x)
    rw [hbot, finrank_bot, Fintype.card_eq_zero]
  have hcard : Module.finrank k (MonoidAlgebra k X) = Fintype.card X :=
    (Module.finrank_eq_card_basis (MonoidAlgebra.basis X k)).trans (by simp)
  have : Module.Finite k (MonoidAlgebra k X) := Module.Finite.of_basis (MonoidAlgebra.basis X k)
  have hrange : Module.finrank k (LinearMap.range (MonoidAlgebra.basis X k).sumCoords) = 1 := by
    rw [LinearMap.range_eq_top.mpr MonoidAlgebra.sumCoords_basis_surjective]
    simp
  have hsum := LinearMap.finrank_range_add_finrank_ker (MonoidAlgebra.basis X k).sumCoords
  rw [hrange, hcard] at hsum
  rw [toSubmodule_augmentationSubrepresentation]
  omega

end Dimension

/-! ### The splitting -/

section DivisionRingScalars

variable (k : Type*) [DivisionRing k] (G X : Type*) [Group G] [MulAction G X] [Fintype X]

variable {k G X}

/-- **The permutation representation splits.**  When the cardinality of `X` is invertible in `k`,
the invariant line and the augmentation subrepresentation are complementary, so `k[X]` is the
direct sum of a trivial representation and a representation of dimension `|X| - 1`.  For an empty
`X` the two are complementary as well, for the degenerate reason that `k[X]` is then the zero
module. -/
theorem isCompl_invariantLine_augmentationSubrepresentation
    (h : IsEmpty X ∨ (Fintype.card X : k) ≠ 0) :
    IsCompl (invariantLine k G X) (augmentationSubrepresentation k G X) := by
  rcases h with hX | h
  · -- `k[X]` is the zero module, so it has only one subrepresentation
    have : Subsingleton (MonoidAlgebra k X) :=
      ⟨fun v w => MonoidAlgebra.coeff_inj.mp (Finsupp.ext fun x => hX.elim x)⟩
    have : Subsingleton (Subrepresentation (Representation.ofMulAction k G X)) :=
      Subrepresentation.toSubmodule_injective.subsingleton
    exact ⟨disjoint_iff.mpr (Subsingleton.elim _ _), codisjoint_iff.mpr (Subsingleton.elim _ _)⟩
  have hsub : IsCompl (Submodule.span k {permutationSum k X})
      (LinearMap.ker (MonoidAlgebra.basis X k).sumCoords) := by
    constructor
    · rw [Submodule.disjoint_def]
      rintro v hv hv'
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [LinearMap.mem_ker, map_smul, sumCoords_basis_permutationSum, smul_eq_mul] at hv'
      rw [(mul_eq_zero.mp hv').resolve_right h, zero_smul]
    · rw [codisjoint_iff, eq_top_iff]
      intro v _
      refine Submodule.mem_sup.mpr
        ⟨((MonoidAlgebra.basis X k).sumCoords v / Fintype.card X) • permutationSum k X,
        Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _),
        v - ((MonoidAlgebra.basis X k).sumCoords v / Fintype.card X) • permutationSum k X,
        ?_, by abel⟩
      rw [LinearMap.mem_ker, map_sub, map_smul, sumCoords_basis_permutationSum, smul_eq_mul,
        div_mul_cancel₀ _ h, sub_self]
  exact Subrepresentation.isCompl_toSubmodule.mp hsub

/-- The invariant line complements the augmentation subrepresentation exactly when the index
set is empty or its cardinality is nonzero in the coefficient division ring. -/
theorem isCompl_invariantLine_augmentationSubrepresentation_iff :
    IsCompl (invariantLine k G X) (augmentationSubrepresentation k G X) ↔
      IsEmpty X ∨ (Fintype.card X : k) ≠ 0 := by
  refine ⟨fun h => ?_, isCompl_invariantLine_augmentationSubrepresentation⟩
  rcases isEmpty_or_nonempty X with hX | hX
  · exact Or.inl hX
  right
  intro hcard
  have hmem : permutationSum k X ∈ augmentationSubrepresentation k G X := by
    rw [mem_augmentationSubrepresentation_iff, sumCoords_basis_permutationSum, hcard]
  have hzero := (Submodule.disjoint_def.mp
    (Subrepresentation.isCompl_toSubmodule.mpr h).disjoint) (permutationSum k X)
    (Submodule.mem_span_singleton_self _) hmem
  exact permutationSum_ne_zero hzero

/-! ### The splitting as trivial plus augmentation -/

section Splitting

variable (k G X)

/-- When `|X|` is nonzero in a division ring, the permutation representation splits as the
trivial representation on the scalars and the augmentation subrepresentation. The scalar
component multiplies the sum of the standard basis. -/
noncomputable def ofMulActionEquivProdAugmentation (h : (Fintype.card X : k) ≠ 0) :
    (Representation.ofMulAction k G X).Equiv
      ((Representation.trivial k G k).prod
        (augmentationSubrepresentation k G X).toRepresentation) :=
  letI : Nonempty X := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero fun h0 => h (by simp [h0]))
  (Subrepresentation.equivProdOfIsCompl
      (isCompl_invariantLine_augmentationSubrepresentation (Or.inr h))).trans
    (Representation.Equiv.mk
      (LinearEquiv.prodCongr (invariantLineEquivTrivial k G X).toLinearEquiv
        (LinearEquiv.refl k _))
      fun g => by
        refine LinearMap.ext fun v => Prod.ext ?_ rfl
        simp)

/-- The splitting adds a multiple of the sum of the standard basis to a vector of the augmentation
subrepresentation. -/
@[simp]
theorem ofMulActionEquivProdAugmentation_symm_apply (h : (Fintype.card X : k) ≠ 0)
    (v : k × (augmentationSubrepresentation k G X).toSubmodule) :
    (ofMulActionEquivProdAugmentation k G X h).symm v =
      v.1 • permutationSum k X + (v.2 : MonoidAlgebra k X) := by
  have : Nonempty X := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero fun h0 => h (by simp [h0]))
  -- The inverse of the composite applies the two inverses in turn.  `Representation.Equiv` has no
  -- lemma for the inverse of a `Representation.Equiv.trans`, so that one step is definitional --
  -- `(rfl)`, not `rfl`, the body of `ofMulActionEquivProdAugmentation` not being `@[expose]`d.
  -- Each of the two inverses is then computed by its own lemma.
  have hcomp : (ofMulActionEquivProdAugmentation k G X h).symm v =
      (Subrepresentation.equivProdOfIsCompl
          (isCompl_invariantLine_augmentationSubrepresentation (Or.inr h))).symm
        ((invariantLineEquivTrivial k G X).symm v.1, v.2) := (rfl)
  rw [hcomp, Subrepresentation.equivProdOfIsCompl_symm_apply,
    coe_invariantLineEquivTrivial_symm_apply]

/-- The scalar component of the splitting is the average of the coefficients. -/
@[simp]
theorem ofMulActionEquivProdAugmentation_apply_fst (h : (Fintype.card X : k) ≠ 0)
    (v : MonoidAlgebra k X) :
    (ofMulActionEquivProdAugmentation k G X h v).1 =
      (MonoidAlgebra.basis X k).sumCoords v / Fintype.card X := by
  have hrec : (ofMulActionEquivProdAugmentation k G X h v).1 • permutationSum k X +
      ((ofMulActionEquivProdAugmentation k G X h v).2 : MonoidAlgebra k X) = v := by
    rw [← ofMulActionEquivProdAugmentation_symm_apply k G X h,
      (ofMulActionEquivProdAugmentation k G X h).symm_apply_apply]
  have haug := congrArg (MonoidAlgebra.basis X k).sumCoords hrec
  rw [map_add, map_smul, sumCoords_basis_permutationSum, smul_eq_mul,
    mem_augmentationSubrepresentation_iff.mp (ofMulActionEquivProdAugmentation k G X h v).2.2,
    add_zero] at haug
  rw [← haug, mul_div_assoc, div_self h, mul_one]

/-- The augmentation component subtracts the average coefficient from every coordinate. -/
@[simp]
theorem coe_ofMulActionEquivProdAugmentation_apply_snd (h : (Fintype.card X : k) ≠ 0)
    (v : MonoidAlgebra k X) :
    ((ofMulActionEquivProdAugmentation k G X h v).2 : MonoidAlgebra k X) =
      v - ((MonoidAlgebra.basis X k).sumCoords v / Fintype.card X) • permutationSum k X := by
  rw [← ofMulActionEquivProdAugmentation_apply_fst k G X h v, eq_sub_iff_add_eq, add_comm,
    ← ofMulActionEquivProdAugmentation_symm_apply k G X h,
    (ofMulActionEquivProdAugmentation k G X h).symm_apply_apply]

end Splitting

end DivisionRingScalars

section Field

variable {k : Type*} [Field k] {G X : Type*} [Monoid G] [MulAction G X]

/-! ### The character of the augmentation subrepresentation -/

/-- **The character of the augmentation subrepresentation** is the character of `k[X]` less `1`.
The subtracted `1` is the trivial quotient `k[X] / ker(augmentation) ≃ k`, so nothing about `|X|`
in `k` is needed: the identity holds in every characteristic, including the one dividing `|X|`,
where the invariant line is *not* a complement.

For a permutation representation the subtracted `1` is the trivial constituent: the character of
`k[X]` counts fixed points, so the character here is the number of fixed points less one. -/
@[simp]
theorem character_augmentationSubrepresentation [Finite X] [Nonempty X] (g : G) :
    (augmentationSubrepresentation k G X).toRepresentation.character g
      = (Representation.ofMulAction k G X).character g - 1 := by
  classical
  -- Take the rank-one map `σ : v ↦ (augmentation v) • single x₀ 1`, a projection onto a line
  -- transverse to the augmentation subrepresentation.  The augmentation is invariant, so `ρ g - σ`
  -- lands in the augmentation subrepresentation, where it restricts to the action of `g`; its
  -- trace is therefore the character on the left, and it is `trace (ρ g) - trace σ`.
  have hfin : Module.Finite k (MonoidAlgebra k X) :=
    Module.Finite.of_basis (MonoidAlgebra.basis X k)
  set e₀ : MonoidAlgebra k X := MonoidAlgebra.single (Classical.arbitrary X) 1 with he₀
  set σ : MonoidAlgebra k X →ₗ[k] MonoidAlgebra k X :=
    (MonoidAlgebra.basis X k).sumCoords.smulRight e₀ with hσ
  have hσ_apply : ∀ v, σ v = (MonoidAlgebra.basis X k).sumCoords v • e₀ := by
    intro v; rw [hσ]; simp
  have he₀_sum : (MonoidAlgebra.basis X k).sumCoords e₀ = 1 := by
    rw [he₀]; simp
  have htraceσ : LinearMap.trace k _ σ = 1 := by
    rw [hσ, LinearMap.trace_smulRight, he₀_sum]
  -- `σ` leaves the augmentation unchanged, because it rescales the augmentation-`1` vector `e₀`
  have hσ_sum : ∀ v, (MonoidAlgebra.basis X k).sumCoords (σ v)
      = (MonoidAlgebra.basis X k).sumCoords v := by
    intro v
    rw [hσ_apply, map_smul, he₀_sum, smul_eq_mul, mul_one]
  -- `ρ g - σ` lands in the augmentation subrepresentation, and restricts there to `ρ g`
  have hmem : ∀ v, (Representation.ofMulAction k G X g - σ) v ∈
      (augmentationSubrepresentation k G X).toSubmodule := fun v => by
    simp only [toSubmodule_augmentationSubrepresentation, LinearMap.mem_ker, LinearMap.sub_apply,
      map_sub, hσ_sum, sumCoords_basis_ofMulAction, sub_self]
  have hrestrict : (Representation.ofMulAction k G X g - σ).restrict (fun v _ => hmem v)
      = (augmentationSubrepresentation k G X).toRepresentation g := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    have hv : σ (v : MonoidAlgebra k X) = 0 := by
      rw [hσ_apply, mem_augmentationSubrepresentation_iff.mp v.2, zero_smul]
    simp [Subrepresentation.toRepresentation_apply, hv]
  have key : LinearMap.trace k _ ((Representation.ofMulAction k G X g - σ).restrict
      (fun v _ => hmem v))
      = LinearMap.trace k _ (Representation.ofMulAction k G X g - σ) :=
    LinearMap.trace_restrict_eq_of_forall_mem _ _ hmem
  simp only [Representation.character]
  rw [← hrestrict, key, map_sub, htraceσ]

end Field

end TauCeti
