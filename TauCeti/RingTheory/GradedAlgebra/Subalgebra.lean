/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.GradedAlgebra.AlgHom

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
-/

@[expose] public section

open DirectSum

namespace Subalgebra

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
    DirectSum.IsInternal (T.grading 𝒜) := by
  -- Each piece of `T` includes into the corresponding piece of `A`.
  let φ : ∀ i, T.grading 𝒜 i →+ 𝒜 i := fun i ↦
    { toFun x := ⟨x.1, x.2⟩
      map_zero' := rfl
      map_add' _ _ := rfl }
  have hφ : ∀ i (a : T.grading 𝒜 i), ((φ i a : 𝒜 i) : A) = ((a : T) : A) := fun _ _ ↦ rfl
  have hcomm : ∀ x : ⨁ i, T.grading 𝒜 i,
      ((DirectSum.coeAddMonoidHom (T.grading 𝒜) x : T) : A) =
        DirectSum.coeAddMonoidHom 𝒜 (DirectSum.map φ x) := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x => simp [hφ]
    | add x y hx hy => simp [hx, hy]
  refine ⟨fun x y hxy ↦ ?_, fun x ↦ ?_⟩
  · refine ((DirectSum.map_injective φ).mpr fun i a b h ↦ by
      ext; rw [← hφ, ← hφ, h]) ((DirectSum.Decomposition.isInternal 𝒜).injective ?_)
    rw [← hcomm, ← hcomm, hxy]
  -- An element of `T` is the sum of its homogeneous components, each of which lies in `T`.
  classical
  refine ⟨∑ i ∈ (decompose 𝒜 (x : A)).support,
    DirectSum.of (fun i ↦ T.grading 𝒜 i) i
      ⟨⟨decompose 𝒜 (x : A) i, hT i x.2⟩, (decompose 𝒜 (x : A) i).2⟩, Subtype.ext ?_⟩
  simp only [map_sum, DirectSum.coeAddMonoidHom_of, AddSubmonoidClass.coe_finsetSum]
  exact DirectSum.sum_support_decompose 𝒜 (x : A)

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
  map_mem hx := hx

@[simp]
theorem coe_gradedVal : ⇑(T.gradedVal 𝒜) = Subtype.val :=
  rfl

/-- The homogeneous components of an element of a graded subalgebra are its homogeneous
components in the ambient algebra. -/
@[simp]
theorem coe_decompose_grading (x : T) (i : ι) :
    ((decompose (T.grading 𝒜) x i : T) : A) = decompose 𝒜 (x : A) i :=
  (T.gradedVal 𝒜).map_directSumDecompose

end Subalgebra
