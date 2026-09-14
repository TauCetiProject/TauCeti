/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import TauCeti.RingTheory.KrullDimension.Integral

/-!
# Krull dimension of finitely generated algebras over a field

Let `A` be a nontrivial finitely generated algebra over a field `k`. Noether normalization gives an
injective finite map `k[X₁, …, Xₛ] → A`, so `A` has Krull dimension `s`. Extending scalars along
any Noetherian `k`-algebra `K` keeps the map `K[X₁, …, Xₛ] → K ⊗[k] A` injective (every
`k`-module is flat) and finite, so `K ⊗[k] A` has the dimension of `K[X₁, …, Xₛ]`, namely
`dim K + s`. The tensor-product theorem handles the subsingleton case separately.

In particular the Krull dimension of a finitely generated algebra over a field does not change
under extension of the base field. This is the affine form of the invariance of the dimension of
a scheme locally of finite type over a field under field extension, which is what makes
fibrewise dimension bounds on morphisms stable under base change.

## Main results

* `TauCeti.ringKrullDim_eq_of_injective_of_isIntegral_mvPolynomial`: an injective integral map
  `k[X₁, …, Xₛ] → A` forces `dim A = s`, the number of variables.
* `TauCeti.finiteRingKrullDim_of_finiteType`: a nontrivial finitely generated algebra over a field
  has finite Krull dimension.
* `TauCeti.ringKrullDim_tensorProduct_of_isNoetherianRing_of_finiteType`:
  `dim (K ⊗[k] A) = dim K + dim A` for a Noetherian `k`-algebra `K`.
* `TauCeti.ringKrullDim_tensorProduct_field_of_finiteType`: `dim (K ⊗[k] A) = dim A` for a field
  extension `K / k`.

## References

* [Stacks Project, Tag 00OW](https://stacks.math.columbia.edu/tag/00OW) (Noether normalization)
-/

public section

namespace TauCeti

open scoped TensorProduct

variable {k : Type*} [Field k]

/-- If a `k`-algebra `A` is integral over a polynomial ring `k[Xᵢ | i ∈ ι]` in finitely many
variables embedded in it, then `A` has Krull dimension the number of variables. -/
theorem ringKrullDim_eq_of_injective_of_isIntegral_mvPolynomial {ι A : Type*} [Finite ι]
    [CommRing A] [Algebra k A] (g : MvPolynomial ι k →ₐ[k] A) (hinj : Function.Injective g)
    (hint : g.IsIntegral) : ringKrullDim A = Nat.card ι := by
  algebraize [g.toRingHom]
  have : FaithfulSMul (MvPolynomial ι k) A := (faithfulSMul_iff_algebraMap_injective _ _).2 hinj
  rw [ringKrullDim_eq_of_isIntegral_of_faithfulSMul (R := MvPolynomial ι k),
    MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]

variable (k) in
/-- A nontrivial finitely generated algebra over a field has finite Krull dimension. -/
theorem finiteRingKrullDim_of_finiteType (A : Type*) [CommRing A] [Nontrivial A] [Algebra k A]
    [Algebra.FiniteType k A] : FiniteRingKrullDim A := by
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  rw [finiteRingKrullDim_iff_ne_bot_and_top,
    ringKrullDim_eq_of_injective_of_isIntegral_mvPolynomial g hinj hint]
  exact ⟨WithBot.coe_ne_bot, WithBot.coe_inj.not.2 (ENat.natCast_ne_top _)⟩

/-- The Krull dimension of `K ⊗[k] A`, for a Noetherian `k`-algebra `K` and a finitely generated
`k`-algebra `A`, is the sum of the Krull dimensions of `K` and `A`. -/
@[simp]
theorem ringKrullDim_tensorProduct_of_isNoetherianRing_of_finiteType (K A : Type*) [CommRing K]
    [IsNoetherianRing K] [Algebra k K] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] :
    ringKrullDim (K ⊗[k] A) = ringKrullDim K + ringKrullDim A := by
  cases subsingleton_or_nontrivial A with
  | inl hA => simp [ringKrullDim_eq_bot_of_subsingleton]
  | inr hA =>
    -- Noether normalization `k[X₁, …, Xₛ] → A`, base-changed to `K[X₁, …, Xₛ] → K ⊗[k] A`,
    -- stays finite, and stays injective because `K` is flat over the field `k`.
    obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
    let φ := Algebra.TensorProduct.map (AlgHom.id k K) g
    have hφinj : Function.Injective φ :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := K) g.toLinearMap hinj
    have hφfin : φ.toRingHom.Finite := RingHom.Finite.tensorProductMap (AlgHom.Finite.id k K) hfin
    algebraize [φ.toRingHom]
    have : FaithfulSMul (K ⊗[k] MvPolynomial (Fin s) k) (K ⊗[k] A) :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 hφinj
    rw [ringKrullDim_eq_of_isIntegral_of_faithfulSMul (R := K ⊗[k] MvPolynomial (Fin s) k),
      ringKrullDim_eq_of_ringEquiv (MvPolynomial.algebraTensorAlgEquiv k K).toRingEquiv,
      MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_of_injective_of_isIntegral_mvPolynomial g hinj hfin.to_isIntegral]

/-- The Krull dimension of a finitely generated algebra over a field is unchanged by extending
the base field. -/
theorem ringKrullDim_tensorProduct_field_of_finiteType (K A : Type*) [Field K] [Algebra k K]
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A] :
    ringKrullDim (K ⊗[k] A) = ringKrullDim A := by
  rw [ringKrullDim_tensorProduct_of_isNoetherianRing_of_finiteType, ringKrullDim_eq_zero_of_field,
    zero_add]

end TauCeti
