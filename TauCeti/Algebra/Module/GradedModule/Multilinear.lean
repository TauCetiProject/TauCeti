/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.Internal
public import TauCeti.LinearAlgebra.Graded.Multilinear
public import Mathlib.LinearAlgebra.Multilinear.DirectSum

/-!
# Degreewise multilinear operations

A homogeneous multilinear map between internally graded modules is equivalently a family of
multilinear maps on their homogeneous pieces, with output degree the sum of the input degrees
plus the degree of the operation. The input modules may differ from slot to slot, as happens
for composable morphisms in a graded linear quiver.

`InternalGrading.homogeneousMultilinearEquiv` gives this equivalence without degree casts in its
interface. Its inverse extends a degreewise family uniquely to the total modules. The extension
uses Mathlib's `MultilinearMap.fromDirectSumEquiv` and `DirectSum.decomposeLinearEquiv`.

The degreewise presentation also allows changes of coordinates using Mathlib's
`LinearEquiv.multilinearMapCongrLeft` and `LinearEquiv.multilinearMapCongrRight` on the relevant
pieces, rather than transports of dependent functions.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 7.1.
-/

public section

open scoped BigOperators DirectSum

namespace TauCeti.InternalGrading

universe uR uι uM uN

variable {R : Type uR} [CommSemiring R] {ι : Type uι}
  {M : ι → Type uM} {N : Type uN}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
  [AddCommMonoid N] [Module R N]

variable (G : ∀ i, InternalGrading R (M i)) (ℬ : ℤ → Submodule R N)

section Finite

variable [Finite ι]

/-- Extend multilinear maps on every tuple of homogeneous pieces to the total modules.
No homogeneity condition on the outputs is required for this construction. -/
noncomputable def multilinearFromPieces
    (f : ∀ d : ι → ℤ, MultilinearMap R (fun i ↦ (G i).piece (d i)) N) :
    MultilinearMap R M N := by
  classical
  exact (MultilinearMap.fromDirectSumEquiv f).compLinearMap
    fun i ↦ (DirectSum.decomposeLinearEquiv (G i).piece).toLinearMap

/-- On homogeneous inputs, extension evaluates the specified component. -/
@[simp]
theorem multilinearFromPieces_apply
    (f : ∀ d : ι → ℤ, MultilinearMap R (fun i ↦ (G i).piece (d i)) N)
    (d : ι → ℤ) (x : ∀ i, (G i).piece (d i)) :
    multilinearFromPieces G f (fun i ↦ (x i : M i)) = f d x := by
  classical
  simp [multilinearFromPieces]

/-- Multilinear maps on total modules are determined by their values on homogeneous tuples.
The modules and gradings may depend on the input slot. -/
theorem multilinearMap_ext {f g : MultilinearMap R M N}
    (h : ∀ (d : ι → ℤ) (x : ∀ i, M i),
      (∀ i, x i ∈ (G i).piece (d i)) → f x = g x) : f = g := by
  classical
  apply (LinearEquiv.multilinearMapCongrLeft
    (fun i ↦ (DirectSum.decomposeLinearEquiv (G i).piece).symm)).injective
  apply MultilinearMap.directSum_ext
  intro d
  ext x
  simpa using h d (fun i ↦ (x i : M i)) (fun i ↦ (x i).property)

/-- Extending the restrictions of a multilinear map recovers the map. -/
@[simp]
theorem multilinearFromPieces_comp_subtype (f : MultilinearMap R M N) :
    multilinearFromPieces G (fun d ↦ f.compLinearMap fun i ↦ ((G i).piece (d i)).subtype)
      = f := by
  apply multilinearMap_ext G
  intro d x hx
  exact multilinearFromPieces_apply G _ d (fun i ↦ ⟨x i, hx i⟩)

end Finite

variable [Fintype ι]

/-- An extension is homogeneous exactly when each component has the required output degree. -/
theorem isHomogeneous_multilinearFromPieces_iff
    (f : ∀ d : ι → ℤ, MultilinearMap R (fun i ↦ (G i).piece (d i)) N) (q : ℤ) :
    TauCeti.MultilinearMap.IsHomogeneous (multilinearFromPieces G f)
        (fun i ↦ (G i).piece) ℬ q ↔
      ∀ d x, f d x ∈ ℬ ((∑ i, d i) + q) := by
  constructor
  · intro hf d x
    simpa using hf.map_mem d (fun i ↦ (x i : M i)) (fun i ↦ (x i).property)
  · intro hf
    rw [TauCeti.MultilinearMap.isHomogeneous_def]
    intro d x hx
    have h := hf d (fun i ↦ ⟨x i, hx i⟩)
    rwa [← multilinearFromPieces_apply G f d (fun i ↦ ⟨x i, hx i⟩)] at h

/-- Degree-`q` homogeneous multilinear maps on the total modules are equivalent to arbitrary
families of multilinear maps on the homogeneous pieces with output degree `∑ i, d i + q`.
The target needs only a family of submodules, and no compatibility condition between distinct
degree tuples is needed. -/
noncomputable def homogeneousMultilinearEquiv (q : ℤ) :
    (TauCeti.MultilinearMap.homogeneousSubmodule (R := R) (S := R)
      (fun i ↦ (G i).piece) ℬ q) ≃ₗ[R]
    (∀ d : ι → ℤ, MultilinearMap R (fun i ↦ (G i).piece (d i))
      (ℬ ((∑ i, d i) + q))) where
  toFun f d :=
    (f.val.compLinearMap fun i ↦ ((G i).piece (d i)).subtype).codRestrict
      (ℬ ((∑ i, d i) + q))
      (fun x ↦ (TauCeti.MultilinearMap.mem_homogeneousSubmodule.mp f.property).map_mem d
        (fun i ↦ (x i : M i)) (fun i ↦ (x i).property))
  invFun f :=
    ⟨multilinearFromPieces G (fun d ↦
      (ℬ ((∑ i, d i) + q)).subtype.compMultilinearMap (f d)),
      TauCeti.MultilinearMap.mem_homogeneousSubmodule.mpr
        ((isHomogeneous_multilinearFromPieces_iff G ℬ _ q).2 (fun d x ↦ (f d x).property))⟩
  left_inv f := by
    apply Subtype.ext
    apply multilinearMap_ext G
    intro d x hx
    exact multilinearFromPieces_apply G _ d (fun i ↦ ⟨x i, hx i⟩)
  right_inv f := by
    funext d
    ext x
    simp [multilinearFromPieces_apply, MultilinearMap.codRestrict]
  map_add' f g := by
    funext d
    ext x
    rfl
  map_smul' c f := by
    funext d
    ext x
    rfl

/-- The forward equivalence evaluates the original map on the underlying homogeneous inputs. -/
@[simp]
theorem coe_homogeneousMultilinearEquiv_apply (q : ℤ)
    (f : TauCeti.MultilinearMap.homogeneousSubmodule (R := R) (S := R)
      (fun i ↦ (G i).piece) ℬ q)
    (d : ι → ℤ) (x : ∀ i, (G i).piece (d i)) :
    (homogeneousMultilinearEquiv G ℬ q f d x : N) = f.val (fun i ↦ (x i : M i)) :=
  (rfl)

/-- The inverse equivalence extends the component family with its prescribed values. -/
@[simp]
theorem homogeneousMultilinearEquiv_symm_apply (q : ℤ)
    (f : ∀ d : ι → ℤ, MultilinearMap R (fun i ↦ (G i).piece (d i))
      (ℬ ((∑ i, d i) + q)))
    (d : ι → ℤ) (x : ∀ i, (G i).piece (d i)) :
    ((homogeneousMultilinearEquiv G ℬ q).symm f).val (fun i ↦ (x i : M i)) =
      (f d x : N) := by
  exact multilinearFromPieces_apply G _ d x

end TauCeti.InternalGrading
