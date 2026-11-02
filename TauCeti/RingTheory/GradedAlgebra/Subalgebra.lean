/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.AlgHom
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Ideal.Over
public import TauCeti.Algebra.DirectSum.Internal

/-!
# The grading of a homogeneous subalgebra

Let `𝒜 : ι → Submodule R A` be a grading of an `R`-algebra `A` and let `T` be an `R`-subalgebra
of `A` which is homogeneous in Mathlib's sense (`DirectSum.SetLike.IsHomogeneous 𝒜 T`): every
homogeneous component of an element of `T` lies in `T`. Then `T` is itself a graded algebra,
with degree-`i` piece the elements of `T` lying in `𝒜 i`, and the inclusion `T → A` is a
homomorphism of graded algebras which commutes with taking homogeneous components.

Typical homogeneous subalgebras are rings of invariants of a grading-preserving action, and the
algebra descended from a grading-preserving descent datum; the second is the graded algebra
underlying effective descent for projective spectra.

## Main definitions

* `Subalgebra.grading T 𝒜`: the grading of `T` induced by `𝒜`.
* `Subalgebra.gradedAlgebra`: for a homogeneous subalgebra this is a grading of `T`.
* `Subalgebra.gradedVal T 𝒜`: the inclusion `T → A` as a homomorphism of graded algebras.

## Main results

* `Subalgebra.isInternal_grading`: the induced grading of a homogeneous subalgebra is internal.
* `Subalgebra.coe_decompose_grading`: the homogeneous components of an element of `T` are its
  homogeneous components in `A`.
* `Subalgebra.toIdeal_irrelevant_grading`: the irrelevant ideal of `T` is the contraction of the
  irrelevant ideal of `A`.
-/

public section

open DirectSum

namespace Subalgebra

section

variable {ι R A : Type*} [DecidableEq ι] [AddMonoid ι] [CommSemiring R] [Semiring A]
  [Algebra R A]

/-- The grading of a subalgebra `T` induced by a grading `𝒜` of the ambient algebra: its
degree-`i` piece consists of the elements of `T` which lie in `𝒜 i`. -/
def grading (T : Subalgebra R A) (𝒜 : ι → Submodule R A) (i : ι) : Submodule R T :=
  (𝒜 i).comap T.val.toLinearMap

variable (T : Subalgebra R A) (𝒜 : ι → Submodule R A)

omit [DecidableEq ι] [AddMonoid ι] in
@[simp]
theorem mem_grading_iff {i : ι} {x : T} : x ∈ T.grading 𝒜 i ↔ (x : A) ∈ 𝒜 i :=
  Iff.rfl

instance [SetLike.GradedMonoid 𝒜] : SetLike.GradedMonoid (T.grading 𝒜) where
  one_mem := SetLike.GradedOne.one_mem (A := 𝒜)
  mul_mem _ _ _ _ hx hy := SetLike.GradedMul.mul_mem (A := 𝒜) hx hy

variable [GradedAlgebra 𝒜] {T 𝒜}

/-- The grading of a homogeneous subalgebra induced by the ambient grading is internal: every
element of `T` is uniquely a finite sum of elements of `T` lying in the pieces `𝒜 i`. -/
theorem isInternal_grading (hT : SetLike.IsHomogeneous 𝒜 T) :
    DirectSum.IsInternal (T.grading 𝒜) :=
  -- Restrict the decomposition of `A` along the inclusion, whose range contains the homogeneous
  -- components of elements of `T`.
  TauCeti.DirectSum.isInternal_comap 𝒜 (T.grading 𝒜) T.val.toLinearMap Subtype.val_injective
    (fun _ _ ↦ Iff.rfl) fun i x ↦ ⟨⟨_, hT i x.2⟩, rfl⟩

/-- A homogeneous subalgebra is a graded algebra, graded by its intersections with the pieces of
the ambient grading. -/
@[instance_reducible]
noncomputable def gradedAlgebra (hT : SetLike.IsHomogeneous 𝒜 T) : GradedAlgebra (T.grading 𝒜) :=
  (isInternal_grading hT).gradedAlgebra

variable (T 𝒜) [GradedAlgebra (T.grading 𝒜)]

/-- The inclusion of a subalgebra into the ambient algebra, as a homomorphism of graded algebras
for the induced grading. -/
def gradedVal : T.grading 𝒜 →ₐᵍ[R] 𝒜 where
  __ := T.val
  map_mem := mem_grading_iff T 𝒜 |>.mp

@[simp]
theorem coe_gradedVal : ⇑(T.gradedVal 𝒜) = Subtype.val :=
  (rfl)

/-- The homogeneous components of an element of a graded subalgebra are its homogeneous
components in the ambient algebra. -/
@[simp]
theorem coe_decompose_grading (x : T) (i : ι) :
    ((decompose (T.grading 𝒜) x i : T) : A) = decompose 𝒜 (x : A) i :=
  (T.gradedVal 𝒜).map_directSumDecompose

end

section Irrelevant

variable {ι R A : Type*} [DecidableEq ι] [AddCommMonoid ι] [PartialOrder ι]
  [CanonicallyOrderedAdd ι] [CommSemiring R] [CommSemiring A] [Algebra R A]
  (T : Subalgebra R A) (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] [GradedAlgebra (T.grading 𝒜)]

/-- The irrelevant ideal of a subalgebra for the induced grading is the contraction of the
irrelevant ideal of the ambient algebra: an element of `T` has zero degree-zero component in `T`
exactly when it does in `A`. -/
theorem toIdeal_irrelevant_grading :
    (HomogeneousIdeal.irrelevant (T.grading 𝒜)).toIdeal =
      (HomogeneousIdeal.irrelevant 𝒜).toIdeal.under T := by
  ext x
  simp [← coe_decompose_grading]

end Irrelevant

end Subalgebra
