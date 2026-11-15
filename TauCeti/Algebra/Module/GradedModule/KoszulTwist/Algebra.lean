/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.GradedModule.Internal
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Koszul twists as algebra automorphisms

On an internally integer-graded algebra, multiplication of degree-`p` elements by
`(-1)^(n * p)` is an involutive algebra automorphism. Restricting a module action along this
map supplies the signed left action on cohomological shifts of DG bimodules. The construction
bundles `TauCeti.InternalGrading.koszulTwist` using its existing multiplication and unit laws.
-/

public section

namespace TauCeti.InternalGrading

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
  (𝒜 : ℤ → Submodule R A) [GradedAlgebra 𝒜]

/-- The algebra automorphism scaling degree `p` by `(-1)^(n * p)`. -/
noncomputable def koszulTwistAlgEquiv (n : ℤ) : A ≃ₐ[R] A :=
  AlgEquiv.ofAlgHom
    (AlgHom.ofLinearMap ((ofDecomposition 𝒜).koszulTwist n)
      (koszulTwist_ofDecomposition_one n) (koszulTwist_ofDecomposition_mul n))
    (AlgHom.ofLinearMap ((ofDecomposition 𝒜).koszulTwist n)
      (koszulTwist_ofDecomposition_one n) (koszulTwist_ofDecomposition_mul n))
    (by ext a; exact (ofDecomposition 𝒜).koszulTwist_koszulTwist n a)
    (by ext a; exact (ofDecomposition 𝒜).koszulTwist_koszulTwist n a)

/-- The algebra automorphism has the existing Koszul twist as its underlying linear map. -/
@[simp]
theorem koszulTwistAlgEquiv_apply (n : ℤ) (a : A) :
    koszulTwistAlgEquiv 𝒜 n a = (ofDecomposition 𝒜).koszulTwist n a := (rfl)

/-- On a homogeneous element the automorphism is multiplication by the Koszul sign. -/
theorem koszulTwistAlgEquiv_apply_of_mem (n : ℤ) {p : ℤ} {a : A} (ha : a ∈ 𝒜 p) :
    koszulTwistAlgEquiv 𝒜 n a = (n * p).negOnePow • a := by
  rw [koszulTwistAlgEquiv_apply, koszulTwist_ofDecomposition_apply_of_mem 𝒜 ha]
  simp only [Units.smul_def, Int.cast_smul_eq_zsmul]

/-- The inverse Koszul automorphism is the same automorphism. -/
@[simp]
theorem koszulTwistAlgEquiv_symm (n : ℤ) :
    (koszulTwistAlgEquiv 𝒜 n).symm = koszulTwistAlgEquiv 𝒜 n := by
  ext a
  rfl

/-- A zero twist is the identity algebra automorphism. -/
@[simp]
theorem koszulTwistAlgEquiv_zero : koszulTwistAlgEquiv 𝒜 0 = AlgEquiv.refl := by
  ext a
  simp [koszulTwistAlgEquiv_apply, koszulTwist_zero]

/-- Koszul algebra automorphisms compose by adding their parameters. -/
@[simp]
theorem koszulTwistAlgEquiv_trans (m n : ℤ) :
    (koszulTwistAlgEquiv 𝒜 m).trans (koszulTwistAlgEquiv 𝒜 n) =
      koszulTwistAlgEquiv 𝒜 (n + m) := by
  ext a
  simpa only [AlgEquiv.trans_apply, koszulTwistAlgEquiv_apply, LinearMap.comp_apply] using
    LinearMap.congr_fun ((ofDecomposition 𝒜).koszulTwist_comp n m) a

end TauCeti.InternalGrading
