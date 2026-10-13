/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Positive
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-!
# The dominant chamber of a base

Over a linearly ordered coefficient ring the simple coroots of a base cut the weight space into
sign-pattern cones, the Weyl chambers. This file introduces the dominant one, both closed and
open, and proves that it meets every Weyl orbit: every weight can be moved into the closed
dominant chamber by some element of the Weyl group. Equivalently, the Weyl translates of the
closed dominant chamber cover the whole weight space.

The two chambers are defined by the signs of the *simple* coroot functionals. Since the coroot of
a positive root is a nonnegative integer combination of the simple coroots, the same sign
conditions in fact hold for all of the positive roots at once, and the file ends by recording that
description of both chambers.

The proof is the classical maximization argument. The Weyl group of a finite root system is
finite, so the sum of the coroot functionals indexed by the positive roots, evaluated along an
orbit, attains a maximum. A simple reflection `sᵢ` permutes the positive roots other than `αᵢ`
and sends `αᵢ` to `-αᵢ`, so applying `sᵢ` changes that sum by `-2⟨αᵢ^∨, x⟩`; maximality
therefore forces `⟨αᵢ^∨, x⟩ ≥ 0` for every simple root, which is dominance.

The weights lying on none of the walls are the **regular** ones. Regularity is defined here too,
since it is the condition separating the two chambers: a dominant weight is strictly dominant
exactly when it is regular. It is stated with no order on the coefficient ring, and is manifestly
Weyl-invariant.

## Main definitions

* `RootPairing.IsRegularWeight` is regularity of a weight: no coroot functional vanishes on it.
* `RootPairing.dominantChamber` is the closed dominant chamber of a base.
* `RootPairing.openDominantChamber` is its open counterpart.

## Main results

* `RootPairing.isRegularWeight_smul`: regularity is invariant under the Weyl group.
* `RootPairing.mem_openDominantChamber_of_isRegularWeight` and
  `RootPairing.isRegularWeight_of_mem_openDominantChamber`: strict dominance is equivalent to
  regular dominance.
* `RootPairing.exists_mem_dominantChamber_of_finite_weylGroup` and
  `RootPairing.exists_mem_dominantChamber`: every weight is Weyl-conjugate into the closed dominant
  chamber.
* `RootPairing.iUnion_smul_dominantChamber_eq_univ`: the Weyl translates of the closed dominant
  chamber cover the weight space.
* `RootPairing.ofIdx_smul_notMem_dominantChamber` and
  `RootPairing.ofIdx_smul_ne_of_mem_openDominantChamber`: a simple reflection moves every point
  of the open dominant chamber, and moves it out of the closed chamber.
* `RootPairing.mem_dominantChamber_iff_forall_mem_posRoots` and
  `RootPairing.mem_openDominantChamber_iff_forall_mem_posRoots`: both chambers are cut out by
  all of the positive coroot functionals, not just the simple ones.

## Implementation notes

The chamber definitions use a preorder on the coefficient ring. Each closure lemma assumes
only the monotonicity of addition or multiplication it needs. Reflection sign changes and
nonnegative coroot expansions use only ordered addition; strict positivity of the expansions
also uses a partial order. The orbit-maximization argument needs a linear order on a
characteristic-zero integral domain, but no compatibility of the order with multiplication.

The maximization argument is proved as `exists_mem_dominantChamber_of_finite_weylGroup`, which
does not require the roots to span: it assumes `Finite P.weylGroup` directly, together with
`Finite ι`, `P.IsCrystallographic` and `P.IsReduced` for the positive-root permutation step.
The theorem `exists_mem_dominantChamber` is the root-system case,
where that finiteness comes from `RootPairing.finite_weylGroup`.

Regularity quantifies over *all* root indices, not just the positive ones. The two are equivalent,
since the coroot functional of a negated root is the negative of the original, and quantifying
over everything keeps the predicate manifestly Weyl-invariant, which is what the chamber arguments
downstream use.

The statements that measure a coroot against the base assume `P.flip.IsReduced` alongside
`P.IsReduced`; Mathlib's `RootPairing.instFlipIsReduced` supplies it whenever `N` is torsion free,
which is automatic over a field.

## References

The argument is the one in J. E. Humphreys, *Introduction to Lie Algebras and Representation
Theory*, GTM 9, Ch. III, §10.3.
-/

public section

namespace RootPairing

open Pointwise Set TauCeti

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

/-! ### Regular weights -/

/-- A weight is **regular** when no coroot functional vanishes on it, that is, when it lies on none
of the walls `ker αᵢ^∨`. -/
def IsRegularWeight (x : M) : Prop := ∀ i, P.coroot' i x ≠ 0

/-- The defining condition of `RootPairing.IsRegularWeight`, as an `Iff`: this introduces and
eliminates the predicate without unfolding it outside this file.

Not a `simp` lemma: unfolding the predicate would take `RootPairing.isRegularWeight_smul` out of
simp-normal form, and would dissolve `IsRegularWeight` out of the goals its own API is stated
about. Use it explicitly, as `rw [isRegularWeight_iff]` or `simp [isRegularWeight_iff]`. -/
lemma isRegularWeight_iff (x : M) : IsRegularWeight P x ↔ ∀ i, P.coroot' i x ≠ 0 := Iff.rfl

/-- **Regularity is a Weyl-invariant condition on weights.** A Weyl-group element matches the
coroot functional of a root with that of its image, so it can neither create nor destroy a
zero. -/
@[simp]
lemma isRegularWeight_smul (w : P.weylGroup) (x : M) :
    IsRegularWeight P (w • x) ↔ IsRegularWeight P x := by
  simpa only [isRegularWeight_iff, _root_.Equiv.symm_symm, coroot'_weylGroupToPerm_smul] using
    (P.weylGroupToPerm w).symm.forall_congr_left
      (p := fun i ↦ P.coroot' i (w • x) ≠ 0)

/-! ### The dominant chamber -/

variable (b : P.Base)

section Preorder

variable [Preorder R]

/-- The closed dominant chamber of a base: the weights on which every simple coroot is
nonnegative. -/
def dominantChamber : Set M := {x | ∀ i ∈ b.support, 0 ≤ P.coroot' i x}

/-- The open dominant chamber of a base: the weights on which every simple coroot is positive. -/
def openDominantChamber : Set M := {x | ∀ i ∈ b.support, 0 < P.coroot' i x}

/-- Membership in the closed dominant chamber. -/
@[simp]
lemma mem_dominantChamber (x : M) :
    x ∈ dominantChamber P b ↔ ∀ i ∈ b.support, 0 ≤ P.coroot' i x := Iff.rfl

/-- Membership in the open dominant chamber. -/
@[simp]
lemma mem_openDominantChamber (x : M) :
    x ∈ openDominantChamber P b ↔ ∀ i ∈ b.support, 0 < P.coroot' i x := Iff.rfl

/-- The open dominant chamber is contained in the closed one. -/
lemma openDominantChamber_subset_dominantChamber :
    openDominantChamber P b ⊆ dominantChamber P b :=
  fun _ hx i hi ↦ (hx i hi).le

/-- The origin is dominant. -/
lemma zero_mem_dominantChamber : (0 : M) ∈ dominantChamber P b := by
  simp

/-- The closed dominant chamber is closed under addition. -/
lemma add_mem_dominantChamber [IsOrderedAddMonoid R] {x y : M} (hx : x ∈ dominantChamber P b)
    (hy : y ∈ dominantChamber P b) : x + y ∈ dominantChamber P b :=
  fun i hi ↦ by simpa using add_nonneg (hx i hi) (hy i hi)

/-- The closed dominant chamber is closed under nonnegative scaling. -/
lemma smul_mem_dominantChamber [PosMulMono R] {t : R} (ht : 0 ≤ t) {x : M}
    (hx : x ∈ dominantChamber P b) :
    t • x ∈ dominantChamber P b :=
  fun i hi ↦ by simpa using mul_nonneg ht (hx i hi)

/-- The open dominant chamber is closed under addition. -/
lemma add_mem_openDominantChamber [AddLeftStrictMono R] {x y : M} (hx : x ∈ openDominantChamber P b)
    (hy : y ∈ openDominantChamber P b) : x + y ∈ openDominantChamber P b :=
  fun i hi ↦ by simpa using add_pos (hx i hi) (hy i hi)

/-- The open dominant chamber is closed under positive scaling. -/
lemma smul_mem_openDominantChamber [PosMulStrictMono R] {t : R} (ht : 0 < t) {x : M}
    (hx : x ∈ openDominantChamber P b) : t • x ∈ openDominantChamber P b :=
  fun i hi ↦ by simpa using mul_pos ht (hx i hi)

end Preorder

section PartialOrder

variable [PartialOrder R]

/-- A dominant weight is strictly dominant as soon as it is regular: nonnegativity that is never
an equality is positivity. -/
lemma mem_openDominantChamber_of_isRegularWeight {x : M} (hx : x ∈ dominantChamber P b)
    (hreg : IsRegularWeight P x) : x ∈ openDominantChamber P b :=
  (mem_openDominantChamber P b x).mpr fun i hi ↦
    lt_of_le_of_ne ((mem_dominantChamber P b x).mp hx i hi) (Ne.symm (hreg i))

end PartialOrder

section Reflections

variable [Preorder R] [IsOrderedAddMonoid R]

/-- A simple reflection carries a weight out of the closed dominant chamber whenever its
corresponding simple coroot is positive on that weight. -/
theorem ofIdx_smul_notMem_dominantChamber {i : ι} (hi : i ∈ b.support) {x : M}
    (hx : 0 < P.coroot' i x) :
    RootPairing.weylGroup.ofIdx P i • x ∉ dominantChamber P b := by
  intro hmem
  have h := hmem i hi
  simp only [weylGroup.ofIdx_smul, Equiv.reflection_smul, coroot'_reflection_self,
    neg_nonneg] at h
  exact hx.not_ge h

/-- No simple reflection fixes a point of the open dominant chamber: it would otherwise stay in
the closed dominant chamber. -/
theorem ofIdx_smul_ne_of_mem_openDominantChamber {i : ι} (hi : i ∈ b.support) {x : M}
    (hx : x ∈ openDominantChamber P b) :
    RootPairing.weylGroup.ofIdx P i • x ≠ x := by
  intro hfix
  refine ofIdx_smul_notMem_dominantChamber P b hi (hx i hi) ?_
  rw [hfix]
  exact openDominantChamber_subset_dominantChamber P b hx

end Reflections

section Finite

variable [Finite ι] [CharZero R] [IsDomain R]

/-- The sum of the coroot functionals indexed by the positive roots, evaluated at `x`. Up to the
factor two this is the pairing of `x` with the Weyl vector on the coroot side; all that is used
below is how it transforms under a simple reflection. -/
private noncomputable def posCorootSum (x : M) : R :=
  ∑ i ∈ posRootsFinset P b, P.coroot' i x

variable [P.IsCrystallographic] [P.IsReduced]

/-- A simple reflection changes `posCorootSum` by twice the value of its own simple coroot. The
reflection permutes the positive roots other than its own simple root, and negates that one. -/
private lemma posCorootSum_reflection {i : ι} (hi : i ∈ b.support) (x : M) :
    posCorootSum P b (P.reflection i x) = posCorootSum P b x - 2 * P.coroot' i x := by
  classical
  -- Work with the underlying sums rather than leaning on `posCorootSum` unfolding silently.
  unfold posCorootSum
  have his : i ∈ posRootsFinset P b :=
    (mem_posRootsFinset P b i).mpr (support_subset_posRoots P b hi)
  -- Reflecting the argument reindexes the summand along `P.reflectionPerm i`.
  have hreindex : ∑ j ∈ posRootsFinset P b, P.coroot' j (P.reflection i x) =
      ∑ j ∈ posRootsFinset P b, P.coroot' (P.reflectionPerm i j) x :=
    Finset.sum_congr rfl fun _ _ ↦ P.coroot'_reflection x
  -- The reflected simple coroot is the negative of the original.
  have hself : P.coroot' (P.reflectionPerm i i) x = -P.coroot' i x := by
    rw [RootPairing.coroot'_reflectionPerm_self]
    simp
  -- Away from `i` the reflection is a bijection of the punctured positive roots.
  have hpunctured : ∑ j ∈ (posRootsFinset P b).erase i, P.coroot' (P.reflectionPerm i j) x =
      ∑ j ∈ (posRootsFinset P b).erase i, P.coroot' j x :=
    sum_posRootsFinset_erase_comp_reflectionPerm P b hi fun j ↦ P.coroot' j x
  have hexpand : ∑ j ∈ posRootsFinset P b, P.coroot' j x =
      P.coroot' i x + ∑ j ∈ (posRootsFinset P b).erase i, P.coroot' j x :=
    (Finset.add_sum_erase _ _ his).symm
  rw [hreindex, ← Finset.add_sum_erase _ _ his, hpunctured, hself, hexpand]
  ring

section FiniteWeylGroup

variable [LinearOrder R] [IsOrderedAddMonoid R] [Finite P.weylGroup]

/-- **Every weight is Weyl-conjugate into the closed dominant chamber**, for a crystallographic
reduced pairing with finitely many roots whose Weyl group is finite. Maximizing `posCorootSum`
along the orbit produces the dominant representative. -/
theorem exists_mem_dominantChamber_of_finite_weylGroup (x : M) :
    ∃ w : P.weylGroup, w • x ∈ dominantChamber P b := by
  obtain ⟨w, hw⟩ := Finite.exists_max fun w : P.weylGroup ↦ posCorootSum P b (w • x)
  refine ⟨w, fun i hi ↦ ?_⟩
  have hsmul : (RootPairing.weylGroup.ofIdx P i * w) • x = P.reflection i (w • x) := by
    simp [mul_smul]
  have hle := hw (RootPairing.weylGroup.ofIdx P i * w)
  rw [hsmul, posCorootSum_reflection P b hi] at hle
  rw [sub_le_self_iff, two_mul, ← two_nsmul] at hle
  exact (nsmul_nonneg_iff (by decide : 2 ≠ 0)).mp hle

/-- Every Weyl orbit meets the closed dominant chamber. -/
theorem orbit_inter_dominantChamber_nonempty (x : M) :
    (MulAction.orbit P.weylGroup x ∩ dominantChamber P b).Nonempty := by
  obtain ⟨w, hw⟩ := exists_mem_dominantChamber_of_finite_weylGroup P b x
  exact ⟨w • x, ⟨w, rfl⟩, hw⟩

/-- **The Weyl translates of the closed dominant chamber cover the weight space.** -/
theorem iUnion_smul_dominantChamber_eq_univ :
    ⋃ w : P.weylGroup, w • dominantChamber P b = (univ : Set M) := by
  refine Set.eq_univ_of_forall fun x ↦ ?_
  obtain ⟨w, hw⟩ := exists_mem_dominantChamber_of_finite_weylGroup P b x
  refine Set.mem_iUnion.mpr ⟨w⁻¹, ?_⟩
  exact ⟨w • x, hw, inv_smul_smul w x⟩

end FiniteWeylGroup

/-- **Every weight is Weyl-conjugate into the closed dominant chamber.** Together with the
uniqueness of that representative this says the closed dominant chamber is a fundamental domain
for the Weyl group. -/
theorem exists_mem_dominantChamber [LinearOrder R] [IsOrderedAddMonoid R] [P.IsRootSystem]
    (x : M) :
    ∃ w : P.weylGroup, w • x ∈ dominantChamber P b :=
  letI := RootPairing.finite_weylGroup P
  exists_mem_dominantChamber_of_finite_weylGroup P b x

end Finite

section PosRoots

variable [CharZero R] [IsDomain R] [Finite ι]
  [P.IsCrystallographic] [P.IsReduced] [P.flip.IsReduced]

variable {x : M}

section Preorder

variable [Preorder R] [IsOrderedAddMonoid R]

/-- Every positive coroot functional is nonnegative on the closed dominant chamber. -/
theorem coroot'_nonneg_of_mem_posRoots (hx : x ∈ dominantChamber P b) {i : ι}
    (hi : i ∈ posRoots P b) : 0 ≤ P.coroot' i x := by
  obtain ⟨f, -, hsum⟩ := exists_coroot'_eq_sum_nat_of_mem_posRoots P b hi
  rw [hsum, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, Nat.cast_smul_eq_nsmul]
  exact Finset.sum_nonneg fun j hj ↦ nsmul_nonneg (hx j hj) _

/-- Every negative coroot functional is nonpositive on the closed dominant chamber. -/
theorem coroot'_nonpos_of_mem_negRoots (hx : x ∈ dominantChamber P b) {i : ι}
    (hi : i ∈ negRoots P b) : P.coroot' i x ≤ 0 := by
  have h := coroot'_nonneg_of_mem_posRoots P b hx
    ((reflectionPerm_self_mem_posRoots_iff_mem_negRoots P b i).mpr hi)
  rw [RootPairing.coroot'_reflectionPerm_self] at h
  simpa using h

/-- **The closed dominant chamber is cut out by the positive coroot functionals**, not just by the
simple ones. -/
theorem mem_dominantChamber_iff_forall_mem_posRoots :
    x ∈ dominantChamber P b ↔ ∀ i ∈ posRoots P b, 0 ≤ P.coroot' i x := by
  refine ⟨fun hx _ hi ↦ coroot'_nonneg_of_mem_posRoots P b hx hi, fun h ↦ ?_⟩
  exact (mem_dominantChamber P b x).mpr fun i hi ↦ h i (support_subset_posRoots P b hi)

end Preorder

variable [PartialOrder R] [IsOrderedAddMonoid R]

/-- Every positive coroot functional is positive on the open dominant chamber. -/
theorem coroot'_pos_of_mem_posRoots (hx : x ∈ openDominantChamber P b) {i : ι}
    (hi : i ∈ posRoots P b) : 0 < P.coroot' i x := by
  -- Some simple coroot really occurs in the expansion, because a coroot is never zero.
  obtain ⟨f, ⟨j, hj, hfj⟩, hsum⟩ := exists_coroot'_eq_sum_nat_of_mem_posRoots P b hi
  have hx' := (mem_openDominantChamber P b x).mp hx
  rw [hsum, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, Nat.cast_smul_eq_nsmul]
  exact Finset.sum_pos' (fun k hk ↦ nsmul_nonneg (hx' k hk).le _) ⟨j, hj,
    nsmul_pos (hx' j hj) hfj⟩

/-- Every negative coroot functional is negative on the open dominant chamber. -/
theorem coroot'_neg_of_mem_negRoots (hx : x ∈ openDominantChamber P b) {i : ι}
    (hi : i ∈ negRoots P b) : P.coroot' i x < 0 := by
  have h := coroot'_pos_of_mem_posRoots P b hx
    ((reflectionPerm_self_mem_posRoots_iff_mem_negRoots P b i).mpr hi)
  rw [RootPairing.coroot'_reflectionPerm_self] at h
  simpa using h

/-- **A strictly dominant weight is regular.** Every root is positive or negative, and the two
kinds of coroot functional are respectively positive and negative on the open dominant chamber. -/
theorem isRegularWeight_of_mem_openDominantChamber (hx : x ∈ openDominantChamber P b) :
    IsRegularWeight P x := by
  intro i
  rcases mem_posRoots_or_mem_negRoots P b i with hi | hi
  · exact (coroot'_pos_of_mem_posRoots P b hx hi).ne'
  · exact (coroot'_neg_of_mem_negRoots P b hx hi).ne

/-- **The open dominant chamber is cut out by the positive coroot functionals**, not just by the
simple ones. -/
theorem mem_openDominantChamber_iff_forall_mem_posRoots :
    x ∈ openDominantChamber P b ↔ ∀ i ∈ posRoots P b, 0 < P.coroot' i x := by
  refine ⟨fun hx _ hi ↦ coroot'_pos_of_mem_posRoots P b hx hi, fun h ↦ ?_⟩
  exact (mem_openDominantChamber P b x).mpr fun i hi ↦ h i (support_subset_posRoots P b hi)

end PosRoots

end RootPairing
