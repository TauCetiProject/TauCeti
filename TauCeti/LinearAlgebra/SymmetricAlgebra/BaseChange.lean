/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Bialgebra.SymmetricAlgebra.BaseChange
public import TauCeti.LinearAlgebra.TensorProduct.Submodule
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Grading
public import Mathlib.RingTheory.GradedAlgebra.TensorProduct

/-!
# Graded base change of symmetric algebras

The canonical equivalence `S ⊗[R] Sym(M) ≃ Sym(S ⊗[R] M)` identifies the scalar extension
of every homogeneous piece with the corresponding homogeneous piece over `S`. Both directions
are bundled as graded algebra maps, so the equivalence can be used on projective spectra.
This supplies the homogeneous-coordinate comparison needed to construct families of projective
linear transformations. No freeness, flatness, or finite generation of the module is required.

The underlying equivalence is `TauCeti.SymmetricAlgebra.scalarTensorBialgEquiv`; the grading
on its source is Mathlib's `GradedAlgebra.baseChange`.

The image computation follows the image-of-powers argument in
`TauCeti.exteriorAlgebraEquivBaseChange_map_exteriorPower`, using
`Submodule.baseChange_map` and `Submodule.baseChange_pow` over commutative semirings.

## Main declarations

* `TauCeti.SymmetricAlgebra.homogeneousSubmoduleBaseChangeEquiv`: the degreewise equivalence.
* `TauCeti.SymmetricAlgebra.scalarTensorGradedAlgHom` and
  `TauCeti.SymmetricAlgebra.scalarTensorGradedAlgHomSymm`: the mutually inverse graded maps.
* `TensorProduct.scalarTensorBialgEquiv_mem_homogeneousSubmodule_iff` and
  `SymmetricAlgebra.scalarTensorBialgEquiv_symm_mem_baseChange_iff`: preservation and reflection
  of homogeneous degree in both directions.
* `TauCeti.SymmetricAlgebra.scalarTensorGradedAlgHom_gradedZeroRingHom_comp_algebraMap` and
  its inverse counterpart: the degree-zero comparisons preserve scalars.

Naturality is provided by `LinearMap.scalarTensorBialgEquiv_comp_map` in
`TauCeti.Algebra.Bialgebra.SymmetricAlgebra.BaseChange`.
-/

public section

open scoped TensorProduct

namespace TauCeti.SymmetricAlgebra

variable {R S M : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M]

/-- The image of the scalar-extended degree-`n` piece is exactly the degree-`n` piece of the
symmetric algebra on the scalar-extended module. -/
-- Compare degrees before `Submodule.baseChange_pow` expands the source piece.
@[simp↓]
theorem map_scalarTensorBialgEquiv_baseChange_homogeneousSubmodule (n : ℕ) :
    ((homogeneousSubmodule R M n).baseChange S).map
        (scalarTensorBialgEquiv (k := R) (K := S)).toAlgEquiv.toLinearMap =
      homogeneousSubmodule S (S ⊗[R] M) n := by
  simp only [homogeneousSubmodule, Submodule.baseChange_pow]
  rw [← AlgEquiv.toLinearEquiv_toLinearMap, ← AlgEquiv.toAlgHom_toLinearMap,
    Submodule.map_pow]
  congr 1
  have hr : (LinearMap.range (SymmetricAlgebra.ι R M)).baseChange S =
      LinearMap.range ((SymmetricAlgebra.ι R M).baseChange S) := by
    rw [← Submodule.map_top, Submodule.baseChange_map, Submodule.baseChange_top,
      Submodule.map_top]
  rw [hr, ← LinearMap.range_comp]
  congr 1
  ext m
  simp

/-- The base-change equivalence preserves every homogeneous degree. -/
theorem scalarTensorBialgEquiv_mem_homogeneousSubmodule {n : ℕ}
    {x : S ⊗[R] SymmetricAlgebra R M}
    (hx : x ∈ (homogeneousSubmodule R M n).baseChange S) :
    scalarTensorBialgEquiv (k := R) (K := S) x ∈ homogeneousSubmodule S (S ⊗[R] M) n := by
  rw [← map_scalarTensorBialgEquiv_baseChange_homogeneousSubmodule n]
  exact Submodule.mem_map_of_mem hx

/-- The inverse base-change equivalence also preserves every homogeneous degree. -/
theorem scalarTensorBialgEquiv_symm_mem_baseChange {n : ℕ}
    {x : SymmetricAlgebra S (S ⊗[R] M)}
    (hx : x ∈ homogeneousSubmodule S (S ⊗[R] M) n) :
    (scalarTensorBialgEquiv (k := R) (K := S)).symm x ∈
      (homogeneousSubmodule R M n).baseChange S := by
  rw [← map_scalarTensorBialgEquiv_baseChange_homogeneousSubmodule n] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  simpa only [AlgEquiv.toLinearMap_apply, BialgEquiv.coe_toAlgEquiv,
    BialgEquiv.symm_apply_apply, SetLike.mem_coe] using hy

end TauCeti.SymmetricAlgebra

namespace TensorProduct

open TauCeti.SymmetricAlgebra

variable {R S M : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M]

/-- Membership in a homogeneous piece is preserved and reflected by scalar extension. -/
@[simp]
theorem scalarTensorBialgEquiv_mem_homogeneousSubmodule_iff {n : ℕ}
    (x : S ⊗[R] SymmetricAlgebra R M) :
    scalarTensorBialgEquiv (k := R) (K := S) x ∈ homogeneousSubmodule S (S ⊗[R] M) n ↔
      x ∈ (homogeneousSubmodule R M n).baseChange S := by
  constructor
  · intro hx
    simpa only [BialgEquiv.symm_apply_apply] using
      scalarTensorBialgEquiv_symm_mem_baseChange hx
  · exact scalarTensorBialgEquiv_mem_homogeneousSubmodule

end TensorProduct

namespace TauCeti.SymmetricAlgebra

variable {R S M : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M]

/-- Scalar extension identifies the degree-`n` homogeneous pieces as `S`-modules. -/
noncomputable def homogeneousSubmoduleBaseChangeEquiv (n : ℕ) :
    (homogeneousSubmodule R M n).baseChange S ≃ₗ[S]
      homogeneousSubmodule S (S ⊗[R] M) n :=
  (scalarTensorBialgEquiv (k := R) (K := S)).toAlgEquiv.toLinearEquiv.ofSubmodules _ _
    (map_scalarTensorBialgEquiv_baseChange_homogeneousSubmodule n)

/-- The degreewise equivalence is the restriction of the scalar-extension equivalence. -/
@[simp]
theorem coe_homogeneousSubmoduleBaseChangeEquiv_apply (n : ℕ)
    (x : (homogeneousSubmodule R M n).baseChange S) :
    (homogeneousSubmoduleBaseChangeEquiv n x : SymmetricAlgebra S (S ⊗[R] M)) =
      scalarTensorBialgEquiv (k := R) (K := S) x := by
  exact LinearEquiv.ofSubmodules_apply _ _ x

/-- The inverse degreewise equivalence is the restriction of the inverse scalar-extension
equivalence. -/
@[simp]
theorem coe_homogeneousSubmoduleBaseChangeEquiv_symm_apply (n : ℕ)
    (x : homogeneousSubmodule S (S ⊗[R] M) n) :
    ((homogeneousSubmoduleBaseChangeEquiv n).symm x : S ⊗[R] SymmetricAlgebra R M) =
      (scalarTensorBialgEquiv (k := R) (K := S)).symm x := by
  exact LinearEquiv.ofSubmodules_symm_apply _ _ x

/-- The canonical scalar-extension equivalence, bundled as a graded algebra map. -/
noncomputable def scalarTensorGradedAlgHom :
    (fun n ↦ (homogeneousSubmodule R M n).baseChange S) →ₐᵍ[S]
      homogeneousSubmodule S (S ⊗[R] M) where
  __ := (scalarTensorBialgEquiv (k := R) (K := S) (M := M)).toAlgEquiv.toAlgHom
  map_mem := scalarTensorBialgEquiv_mem_homogeneousSubmodule

/-- The inverse scalar-extension equivalence, bundled as a graded algebra map. -/
noncomputable def scalarTensorGradedAlgHomSymm :
    homogeneousSubmodule S (S ⊗[R] M) →ₐᵍ[S]
      (fun n ↦ (homogeneousSubmodule R M n).baseChange S) where
  __ := (scalarTensorBialgEquiv (k := R) (K := S) (M := M)).symm.toAlgEquiv.toAlgHom
  map_mem := scalarTensorBialgEquiv_symm_mem_baseChange

/-- The inverse graded map is a right inverse of the forward graded map. -/
theorem scalarTensorGradedAlgHom_rightInverse :
    Function.RightInverse
      (scalarTensorGradedAlgHomSymm (R := R) (S := S) (M := M))
      scalarTensorGradedAlgHom :=
  (scalarTensorBialgEquiv (k := R) (K := S)).apply_symm_apply

/-- The inverse graded map is a left inverse of the forward graded map. -/
theorem scalarTensorGradedAlgHom_leftInverse :
    Function.LeftInverse
      (scalarTensorGradedAlgHomSymm (R := R) (S := S) (M := M))
      scalarTensorGradedAlgHom :=
  (scalarTensorBialgEquiv (k := R) (K := S)).symm_apply_apply

/-- On degree zero, the forward comparison preserves the scalar copy of `S`. -/
@[simp]
theorem scalarTensorGradedAlgHom_gradedZeroRingHom_comp_algebraMap :
    scalarTensorGradedAlgHom.toGradedRingHom.gradedZeroRingHom.comp
        (algebraMap S ((homogeneousSubmodule R M 0).baseChange S)) =
      algebraMap S (homogeneousSubmodule S (S ⊗[R] M) 0) := by
  ext s
  simp [GradedRingHom.gradedZeroRingHom_apply_coe, scalarTensorGradedAlgHom,
    SetLike.GradeZero.coe_algebraMap]

/-- On degree zero, the inverse comparison preserves the scalar copy of `S`. -/
@[simp]
theorem scalarTensorGradedAlgHomSymm_gradedZeroRingHom_comp_algebraMap :
    scalarTensorGradedAlgHomSymm.toGradedRingHom.gradedZeroRingHom.comp
        (algebraMap S (homogeneousSubmodule S (S ⊗[R] M) 0)) =
      algebraMap S ((homogeneousSubmodule R M 0).baseChange S) := by
  ext s
  simp only [RingHom.comp_apply, GradedRingHom.gradedZeroRingHom_apply_coe,
    scalarTensorGradedAlgHomSymm, GradedRingHom.coe_mk, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, AlgEquiv.coe_toAlgHom, BialgEquiv.coe_toAlgEquiv,
    SetLike.GradeZero.coe_algebraMap, GradedAlgebra.coe_algebraMap_apply]
  rw [← scalarTensorBialgEquiv_tmul_one, BialgEquiv.symm_apply_apply]

end TauCeti.SymmetricAlgebra

namespace TensorProduct

open TauCeti.SymmetricAlgebra

variable {R S M : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M]

/-- The forward graded map is the existing scalar-extension equivalence. -/
@[simp]
theorem scalarTensorGradedAlgHom_apply (x : S ⊗[R] SymmetricAlgebra R M) :
    scalarTensorGradedAlgHom x = scalarTensorBialgEquiv (k := R) (K := S) x := (rfl)

end TensorProduct

namespace SymmetricAlgebra

open TauCeti.SymmetricAlgebra

variable {R S M : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M]

/-- The inverse comparison preserves and reflects homogeneous degree as well. -/
-- Compare degrees before `Submodule.baseChange_pow` expands the source piece.
@[simp↓]
theorem scalarTensorBialgEquiv_symm_mem_baseChange_iff {n : ℕ}
    (x : SymmetricAlgebra S (S ⊗[R] M)) :
    (scalarTensorBialgEquiv (k := R) (K := S)).symm x ∈
        (homogeneousSubmodule R M n).baseChange S ↔
      x ∈ homogeneousSubmodule S (S ⊗[R] M) n := by
  rw [← TensorProduct.scalarTensorBialgEquiv_mem_homogeneousSubmodule_iff,
    BialgEquiv.apply_symm_apply]

/-- The inverse graded map is the inverse scalar-extension equivalence. -/
@[simp]
theorem scalarTensorGradedAlgHomSymm_apply (x : SymmetricAlgebra S (S ⊗[R] M)) :
    scalarTensorGradedAlgHomSymm x = (scalarTensorBialgEquiv (k := R) (K := S)).symm x := (rfl)

end SymmetricAlgebra
