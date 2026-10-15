/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.AdditiveGroup.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Map
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Cotangent

/-!
# Differentials of additive one-parameter subgroups

The differential of a morphism from the additive group has image spanned by the image of its
unit tangent vector, and coefficient change preserves that image. When the target's cotangent
space is finite projective, scalar extension gives the differential with the same parameter.
These statements
allow a root-space trivialization to be compared with its root-subgroup parametrization without
repeating matrix calculations after scalar extension.

The tangent normalization is `TauCeti.AdditiveGroup.gaTangentLinearEquiv`. The application to
root subgroups follows `TauCeti.Algebra.AlgebraicGroup.SpecialLinear.Root.Adjoint`. The
coefficient-change calculation follows
`TauCeti.Algebra.AlgebraicGroup.Symplectic.RootSubgroup.Differential`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.a.
* B. Conrad, *Reductive Group Schemes* (2014), §5.1.
-/

public section

namespace TauCeti.AdditiveGroup

open scoped TensorProduct

universe u v w

noncomputable section

section Semiring

variable {R : Type u} [CommSemiring R] {B : Type v} [CommSemiring B] [Algebra R B]

/-- The additive tangent vector with parameter `c` is coefficient change of the unit tangent
vector, multiplied by `c`. -/
theorem gaTangentLinearEquiv_symm_eq_smul_mapValue (c : B) :
    (gaTangentLinearEquiv (R := R) (B := B)).symm c =
      c • Derivation.mapValue (Algebra.ofId R B)
        ((gaTangentLinearEquiv (R := R) (B := R)).symm 1) := by
  apply (gaTangentLinearEquiv (R := R) (B := B)).injective
  rw [LinearEquiv.apply_symm_apply, gaTangentLinearEquiv_apply,
    algEquivSelf_derivation_smul_apply, Derivation.mapValue_apply,
    gaTangentLinearEquiv_symm_apply_ι]
  -- The unit is stored in the coefficient synonym, whose semiring is inherited from `B`.
  simp only [map_one]
  erw [Bialgebra.CounitAlgebra.algEquivSelf_apply, mul_one]

/-- The additive tangent vector with parameter `c` is `c` times the unit tangent vector. -/
theorem gaTangentLinearEquiv_symm_eq_smul_symm_one (c : B) :
    (gaTangentLinearEquiv (R := R) (B := B)).symm c =
      c • (gaTangentLinearEquiv (R := R) (B := B)).symm 1 := by
  rw [gaTangentLinearEquiv_symm_eq_smul_mapValue,
    gaTangentLinearEquiv_symm_eq_smul_mapValue (1 : B), one_smul]

end Semiring

variable {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]
  {H : Type w} [CommRing H] [Bialgebra R H]

/-- The differential of an additive one-parameter subgroup sends a tangent vector to its
parameter times the image of the unit tangent vector. -/
theorem derivationComp_eq_smul (φ : H →ₐc[R] SymmetricAlgebra R R)
    (d : Derivation R (SymmetricAlgebra R R)
      (Bialgebra.CounitAlgebra R (SymmetricAlgebra R R) B)) :
    derivationComp (B := B) φ d =
      gaTangentLinearEquiv d • derivationComp (B := B) φ
        ((gaTangentLinearEquiv (R := R) (B := B)).symm 1) := by
  conv_lhs =>
    rw [← (gaTangentLinearEquiv (R := R) (B := B)).symm_apply_apply d,
      gaTangentLinearEquiv_symm_eq_smul_symm_one]
  simpa only [LieHom.coe_toLinearMap, derivationCompLieHom_apply] using
    (derivationCompLieHom (B := B) φ).map_smul (gaTangentLinearEquiv d)
      ((gaTangentLinearEquiv (R := R) (B := B)).symm 1)

/-- An injective additive one-parameter subgroup differential sends the unit tangent vector
to a nonzero vector over every nontrivial coefficient algebra. -/
theorem derivationComp_gaTangentLinearEquiv_symm_one_ne_zero [Nontrivial B]
    (φ : H →ₐc[R] SymmetricAlgebra R R)
    (hφ : Function.Injective (derivationComp (B := B) φ)) :
    derivationComp (B := B) φ ((gaTangentLinearEquiv (R := R) (B := B)).symm 1) ≠ 0 := by
  intro h
  have hd := hφ (h.trans (map_zero _).symm)
  have hu := congrArg (gaTangentLinearEquiv (R := R) (B := B)) hd
  exact one_ne_zero (by simpa only [LinearEquiv.apply_symm_apply, map_zero] using hu)

/-- Coefficient change preserves the image of the additive unit tangent vector under the
differential of any additive one-parameter subgroup. -/
theorem mapValue_derivationComp_gaTangentLinearEquiv_symm_one
    {C : Type*} [CommRing C] [Algebra R C]
    (ψ : B →ₐ[R] C) (φ : H →ₐc[R] SymmetricAlgebra R R) :
    Derivation.mapValue ψ (derivationComp (B := B) φ
      ((gaTangentLinearEquiv (R := R) (B := B)).symm 1)) =
      derivationComp (B := C) φ ((gaTangentLinearEquiv (R := R) (B := C)).symm 1) := by
  have hga : Derivation.mapValue ψ
      ((gaTangentLinearEquiv (R := R) (B := B)).symm 1) =
        (gaTangentLinearEquiv (R := R) (B := C)).symm 1 := by
    apply (gaTangentLinearEquiv (R := R) (B := C)).injective
    simp only [gaTangentLinearEquiv_apply, Derivation.mapValue_apply,
      gaTangentLinearEquiv_symm_apply_ι, map_one]
  ext a
  simp only [Derivation.mapValue_apply, derivationComp_apply]
  have ha := DFunLike.congr_fun hga (φ a)
  simp only [Derivation.mapValue_apply] at ha
  -- Evaluation erases the counit-algebra indexing introduced by precomposition.
  exact ha

/-- The image of the differential of an additive one-parameter subgroup is the line spanned by
its unit tangent vector, over every commutative coefficient algebra. -/
theorem range_derivationCompLieHom_eq_span (B : Type v) [CommRing B] [Algebra R B]
    (φ : H →ₐc[R] SymmetricAlgebra R R) :
    (derivationCompLieHom (B := B) φ).range.toSubmodule =
      B ∙ derivationComp (B := B) φ
        ((gaTangentLinearEquiv (R := R) (B := B)).symm 1) := by
  ext d
  rw [LieSubalgebra.mem_toSubmodule, LieHom.mem_range, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨e, rfl⟩
    refine ⟨gaTangentLinearEquiv e, ?_⟩
    rw [derivationCompLieHom_apply]
    exact (derivationComp_eq_smul φ e).symm
  · rintro ⟨c, rfl⟩
    exact ⟨(gaTangentLinearEquiv (R := R) (B := B)).symm c,
      by rw [gaTangentLinearEquiv_symm_eq_smul_symm_one, map_smul,
        derivationCompLieHom_apply]⟩

variable [Module.Finite R (Bialgebra.CotangentSpace R H)]
  [Module.Projective R (Bialgebra.CotangentSpace R H)]

/-- Scalar extension of the unit tangent vector of an additive one-parameter subgroup is its
coefficient-valued differential with the prescribed parameter. This identity is for explicit
rewriting; the general pure-tensor simp rule is `Derivation.tangentScalarExtensionEquiv_tmul`. -/
theorem tangentScalarExtensionEquiv_tmul_derivationComp (c : B)
    (φ : H →ₐc[R] SymmetricAlgebra R R) :
    Derivation.tangentScalarExtensionEquiv (R := R) (A := H) (B := B)
        (c ⊗ₜ[R] (Derivation.cotangentLinearEquiv (B := R)).symm
          (derivationComp (B := R) φ ((gaTangentLinearEquiv (R := R) (B := R)).symm 1))) =
      derivationComp (B := B) φ ((gaTangentLinearEquiv (R := R) (B := B)).symm c) := by
  rw [Derivation.tangentScalarExtensionEquiv_tmul, LinearEquiv.apply_symm_apply,
    gaTangentLinearEquiv_symm_eq_smul_mapValue (R := R) (B := B) c]
  ext a
  simp only [derivationComp_apply, Derivation.mapValue_apply, Derivation.smul_apply]
  -- Both counit coefficient modules inherit multiplication from the same value algebra.
  rfl

end

end TauCeti.AdditiveGroup
