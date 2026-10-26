/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.IdealSheaf.EulerCharacteristic
public import TauCeti.AlgebraicGeometry.Curves.Degree
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Finite
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Invertible

/-!
# The Euler-characteristic degree of an effective Cartier divisor

Let `X` be a scheme over a field `k` and `I ⊆ 𝒪_X` an ideal sheaf whose closed subscheme
`D = V(I)` is finite over `k`, of rank `dim_k Γ(D, 𝒪_D)`. The exact sequence
`0 ⟶ I ⟶ 𝒪_X ⟶ ι_* 𝒪_D ⟶ 0` and the vanishing of higher cohomology on the affine Noetherian
scheme `D` give

  `χ(I) = χ(𝒪_X) - dim_k Γ(D, 𝒪_D)`

(`Scheme.IdealSheafData.eulerCharBelow_sheaf`, in
`TauCeti.AlgebraicGeometry.IdealSheaf.EulerCharacteristic`), where `χ` is the degree-`2` truncation
`dim H⁰ - dim H¹` and `H⁰(X, 𝒪_X)`, `H¹(X, 𝒪_X)` are assumed finite-dimensional. When `I` is the
ideal sheaf `𝒪_X(-D)` of an effective Cartier divisor `D`, this says that the line bundle `𝒪_X(-D)`
has Euler-characteristic degree `-dim_k Γ(D, 𝒪_D)`
(`Scheme.IdealSheafData.IsEffectiveCartier.eulerDegree_toInvertibleSheaf`). On a connected
smooth proper curve over `k` the degree is additive, so `𝒪_X(D)` has degree
`dim_k Γ(D, 𝒪_D)` (`Scheme.IdealSheafData.IsEffectiveCartier.eulerDegree_inv_mk_toInvertibleSheaf`).
This is the classical `deg 𝒪_X(D) = deg D` for effective divisors, with the degree of `D` read off
as the rank of its closed subscheme, the notion of degree used for relative effective Cartier
divisors in families.

The rank is Mathlib's `Scheme.Hom.finrank` of the finite morphism `D ⟶ Spec k`, evaluated at the
unique point of `Spec k`; it is `dim_k Γ(D, 𝒪_D)` by
`AlgebraicGeometry.Scheme.Hom.finrank_eq_finrank_of_field`.

## References

* R. Hartshorne, *Algebraic Geometry*: Proposition II.6.18 (`𝒪_X(-D)` is the ideal sheaf of
  `D`), Lemma III.2.10 and Theorem III.3.5 (the cohomology of `𝒪_D`), and the proof of
  Theorem IV.1.3 (Riemann–Roch), where degrees are computed from the same kind of exact
  sequence.
-/

public section

open CategoryTheory Limits AlgebraicGeometry Order
open TauCeti.AlgebraicGeometry Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

noncomputable section

variable (k : Type u) [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] (I : X.IdealSheafData)

section Finite

variable [IsFinite (I.subschemeι ≫ X ↘ Spec (.of k))]

section FiniteCohomology

variable [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial X).obj 0)]
  [FiniteDimensional k (Cohomology (InvertibleSheaf.trivial X).obj 1)]

/-- **The degree of `𝒪_X(-D)`.** On a scheme over a field `k` with finite-dimensional
`H⁰(X, 𝒪_X)` and `H¹(X, 𝒪_X)`, the ideal sheaf `𝒪_X(-D)` of an effective Cartier divisor `D`
finite over `k` has Euler-characteristic degree `-dim_k Γ(D, 𝒪_D)`, the negative of the rank of
`D ⟶ Spec k`. -/
theorem IsEffectiveCartier.eulerDegree_toInvertibleSheaf (hI : I.IsEffectiveCartier)
    (s : Spec (.of k)) :
    hI.toInvertibleSheaf.eulerDegree k = -((I.subschemeι ≫ X ↘ Spec (.of k)).finrank s : ℤ) := by
  rw [InvertibleSheaf.eulerDegree_def, IsEffectiveCartier.toInvertibleSheaf_obj,
    eulerCharBelow_sheaf k I s]
  ring

end FiniteCohomology

end Finite

section Smooth

variable [IsProper (X ↘ Spec (.of k))] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  [ConnectedSpace X]

/-- **The degree of `𝒪_X(D)` on a smooth curve.** On a connected smooth proper curve over a
field `k`, the line bundle `𝒪_X(D)` of an effective Cartier divisor `D` has Euler-characteristic
degree `dim_k Γ(D, 𝒪_D)`, the rank of the finite morphism `D ⟶ Spec k`. The geometric
hypotheses supply the finiteness of `D` over `k`, the finiteness of `H⁰(X, 𝒪_X)` and
`H¹(X, 𝒪_X)`, and the additivity of the degree; no rational point or perfect-field assumption is
needed. -/
theorem IsEffectiveCartier.eulerDegree_inv_mk_toInvertibleSheaf (hI : I.IsEffectiveCartier)
    (s : Spec (.of k)) :
    LineBundleClass.eulerDegree k (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹ =
      (I.subschemeι ≫ X ↘ Spec (.of k)).finrank s := by
  -- Over a field every effective Cartier divisor is relative, hence finite over `k`.
  have : IsFinite (I.subschemeι ≫ X ↘ Spec (.of k)) :=
    ((isRelativeEffectiveCartier_iff_isEffectiveCartier I _).mpr hI).isFinite
  have := SmoothOfRelativeDimension.smooth 1 (X ↘ Spec (.of k))
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk_of_smooth (X ↘ Spec (.of k))
  have : IsIntegral X := isIntegral_of_connected_of_isRegularLocalRing_stalk X
  have : ∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X)) :=
    fun x ↦ inferInstance
  have hdim : topologicalKrullDim X = 1 :=
    topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of k))
  have := finiteDimensional_cohomology_one_trivial_of_isProper k hdim
  have := InvertibleSheaf.finiteDimensional_cohomology_zero k
    (fun x ↦ by exact_mod_cast (TauCeti.coheight_le_topologicalKrullDim x).trans hdim.le)
    (InvertibleSheaf.trivial X)
  have h := LineBundleClass.eulerDegree_mul_of_smooth k (LineBundleClass.mk hI.toInvertibleSheaf)
    (LineBundleClass.mk hI.toInvertibleSheaf)⁻¹
  rw [mul_inv_cancel, LineBundleClass.eulerDegree_one, LineBundleClass.eulerDegree_mk,
    hI.eulerDegree_toInvertibleSheaf k I s] at h
  linarith

end Smooth

end

end AlgebraicGeometry.Scheme.IdealSheafData
