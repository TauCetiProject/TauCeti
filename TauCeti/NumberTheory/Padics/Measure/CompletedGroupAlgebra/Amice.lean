/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Measure.AmiceTransform
public import TauCeti.NumberTheory.Padics.Measure.CompletedGroupAlgebra.Basic
public import TauCeti.NumberTheory.Padics.PadicIntegers
public import TauCeti.NumberTheory.Padics.UnitsDecomposition.Logarithm
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.PowerSeries
import TauCeti.NumberTheory.Padics.Measure.Moments
import TauCeti.NumberTheory.Padics.Measure.Pushforward
import TauCeti.NumberTheory.Padics.Measure.Topology.Amice

/-!
# The Amice transform in the completed group algebra

An integral measure `μ` on `ℤ_p` has two descriptions as a power series. Its Amice transform
`A_μ = ∑ₙ μ(x ↦ (x choose n)) Tⁿ` is Mathlib's `AbstractMeasure.amiceTransform`, an isomorphism
`D(ℤ_p, ℤ_p) ≃ ℤ_p⟦T⟧` of `ℤ_p`-modules. Its image in the completed group algebra
`ℤ_p[[ℤ_p]]`, read in the power-series coordinate `T ↦ [γ] - 1` at the topological generator
`γ = 1` of `ℤ_p`, is a second one. This file shows that they agree: formally
`∫ [a] dμ(a) = ∫ (1 + T) ^ a dμ(a)`, since `[a] = [γ] ^ a = (1 + T) ^ a`.

The comparison is proved for an arbitrary continuous homomorphism `φ : ℤ_p → Γ` into a commutative
profinite group `Γ`. The element `[φ 1] - 1` of `ℤ_p[[Γ]]` is topologically nilpotent
(`TauCeti.completedGroupAlgebra.isTopologicallyNilpotent_of_apply_ofAdd_one_sub_one`), so power
series over `ℤ_p` can be evaluated at it, and the image of the pushforward of `μ` along `φ` is the
value of `A_μ` there (`AbstractMeasure.toCompletedGroupAlgebra_map_eq_aeval_amiceTransform`):

`∫ [φ a] dμ(a) = A_μ([φ 1] - 1)`.

Both sides are continuous in `A_μ`, for the weak topology on measures, which the Amice transform
identifies with the coefficientwise topology on series, and for the inverse-limit topology on
`ℤ_p[[Γ]]`. They agree on the polynomials, because a polynomial is a combination of the powers
`(1 + T) ^ k`, the transforms of the Dirac measures at `k ∈ ℕ`, whose images are both `[φ 1] ^ k`.
As the polynomials are dense, the two sides agree everywhere.

Read through the power-series coordinate `TauCeti.completedGroupAlgebra.powerSeriesCoordinate`
`T ↦ [γ] - 1` of the completed group algebra of an infinite procyclic pro-`p` group `Γ` with
topological generator `γ`, this says that the coordinate of `A_μ` is the completed-group-algebra
element of the pushforward of `μ` along any `φ` with `φ 1 = γ`
(`AbstractMeasure.powerSeriesCoordinate_amiceTransformEquiv_of_apply`). Two cases are recorded:

* `AbstractMeasure.powerSeriesCoordinate_amiceTransformEquiv`: for `Γ = ℤ_p` and `γ = 1`, the
  power-series coordinate of `A_μ` is the completed-group-algebra element of `μ`; so the Dirac
  measure `δ_a` goes to `[a] = [γ ^ a]`, and `T` to `[γ] - 1`;
* `AbstractMeasure.powerSeriesCoordinate_unitsPrincipal_amiceTransformEquiv`: the same identity
  transported to the principal units `1 + qℤ_p` of `ℤ_pˣ`, `q = p ^ TauCeti.padicUnitsDepth p`,
  along `a ↦ γ ^ a = exp (q a)` for the generator `γ = exp q` (`TauCeti.padicUnitsGenerator`),
  which topologically generates them (`TauCeti.topologicallyGenerates_padicUnitsGenerator`).

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, the diagram (3.4)
  with Proposition 3.16 and Theorem 3.25.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §II.2.
-/

public section

noncomputable section

open Topology PowerSeries
open scoped AbstractMeasure PowerSeries.WithPiTopology

variable {p : ℕ} [Fact p.Prime]

namespace TauCeti.completedGroupAlgebra

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  [TotallyDisconnectedSpace Γ] [IsMulCommutative Γ]

/-- The continuous map `a ↦ φ a` from `ℤ_p` underlying a continuous homomorphism
`φ : Multiplicative ℤ_[p] →ₜ* Γ`. -/
private abbrev padicIntMap (φ : Multiplicative ℤ_[p] →ₜ* Γ) : C(ℤ_[p], Γ) :=
  (φ : C(Multiplicative ℤ_[p], Γ)).comp ⟨Multiplicative.ofAdd, continuous_ofAdd⟩

/-- The image in `ℤ_p[[Γ]]` of the pushforward along `φ` of the measure with Amice transform `F`,
as a `ℤ_p`-linear map of `F`. -/
private def amiceIntegral (φ : Multiplicative ℤ_[p] →ₜ* Γ) :
    ℤ_[p]⟦X⟧ →ₗ[ℤ_[p]] completedGroupAlgebra ℤ_[p] Γ :=
  AbstractMeasure.toCompletedGroupAlgebra.toLinearMap ∘ₗ
    AbstractMeasure.map (padicIntMap φ) ∘ₗ AbstractMeasure.amiceTransformEquiv.symm.toLinearMap

omit [TotallyDisconnectedSpace Γ] in
private theorem amiceIntegral_apply (φ : Multiplicative ℤ_[p] →ₜ* Γ) (F : ℤ_[p]⟦X⟧) :
    amiceIntegral φ F = AbstractMeasure.toCompletedGroupAlgebra
      (AbstractMeasure.map (padicIntMap φ) (AbstractMeasure.amiceTransformEquiv.symm F)) :=
  rfl

private theorem continuous_amiceIntegral (φ : Multiplicative ℤ_[p] →ₜ* Γ) :
    Continuous (amiceIntegral φ) := by
  let : TopologicalSpace D(ℤ_[p], ℤ_[p]) := AbstractMeasure.WeakTopology
  let : TopologicalSpace D(Γ, ℤ_[p]) := AbstractMeasure.WeakTopology
  have hA := AbstractMeasure.isHomeomorph_amiceTransformEquiv_weak (p := p)
  rw [LinearEquiv.isHomeomorph_iff] at hA
  exact AbstractMeasure.isHomeomorph_toCompletedGroupAlgebra_weak.continuous.comp
    (((padicIntMap φ).continuous_abstractMeasure_map_weak (R := ℤ_[p]) (E := ℤ_[p])).comp hA.2)

omit [TotallyDisconnectedSpace Γ] in
/-- On the series `(1 + T) ^ k`, the transform of the Dirac measure at `k`, the comparison gives
`[φ 1] ^ k`. -/
private theorem amiceIntegral_one_add_X_pow (φ : Multiplicative ℤ_[p] →ₜ* Γ) (k : ℕ) :
    amiceIntegral φ ((1 + X) ^ k) = of ℤ_[p] Γ (φ (.ofAdd 1)) ^ k := by
  have hδ : AbstractMeasure.amiceTransformEquiv.symm ((1 + X : ℤ_[p]⟦X⟧) ^ k) =
      AbstractMeasure.dirac ℤ_[p] (k : ℤ_[p]) := by
    rw [LinearEquiv.symm_apply_eq, AbstractMeasure.amiceTransformEquiv_apply,
      AbstractMeasure.amiceTransform_dirac, binomialSeries_nat]
  rw [amiceIntegral_apply, hδ, AbstractMeasure.map_dirac,
    AbstractMeasure.toCompletedGroupAlgebra_dirac, ← map_pow, ← map_pow]
  simp [← ofAdd_nsmul]

omit [TotallyDisconnectedSpace Γ] in
/-- On polynomials the comparison is evaluation at `[φ 1] - 1`. -/
private theorem amiceIntegral_coe (φ : Multiplicative ℤ_[p] →ₜ* Γ) (P : Polynomial ℤ_[p]) :
    amiceIntegral φ P = Polynomial.aeval (of ℤ_[p] Γ (φ (.ofAdd 1)) - 1) P := by
  -- Write `P` as a polynomial in `1 + T`.
  obtain ⟨Q, rfl⟩ : ∃ Q : Polynomial ℤ_[p], Q.comp (Polynomial.X + 1) = P :=
    ⟨P.comp (Polynomial.X - 1), by simp [Polynomial.comp_assoc]⟩
  rw [Polynomial.aeval_comp]
  simp only [map_add, Polynomial.aeval_X, map_one, sub_add_cancel]
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [Polynomial.add_comp, Polynomial.coe_add, map_add, hP, hQ]
  | monomial k c =>
    rw [Polynomial.monomial_comp, ← Polynomial.smul_eq_C_mul]
    push_cast
    rw [map_smul, add_comm X, amiceIntegral_one_add_X_pow, Polynomial.aeval_monomial,
      Algebra.smul_def]

end TauCeti.completedGroupAlgebra

namespace AbstractMeasure

open TauCeti TauCeti.completedGroupAlgebra

section General

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  [TotallyDisconnectedSpace Γ] [IsMulCommutative Γ]

/-- **The completed-group-algebra element of a pushforward is the Amice transform evaluated at
`[φ 1] - 1`.** For a continuous homomorphism `φ : ℤ_p → Γ` into a commutative profinite group and an
integral measure `μ` on `ℤ_p`, the pushforward of `μ` along `φ` has image `A_μ([φ 1] - 1)` in
`ℤ_p[[Γ]]`: formally, `∫ [φ a] dμ(a) = ∫ (1 + ([φ 1] - 1)) ^ a dμ(a)`. -/
theorem toCompletedGroupAlgebra_map_eq_aeval_amiceTransform (φ : Multiplicative ℤ_[p] →ₜ* Γ)
    (μ : D(ℤ_[p], ℤ_[p])) :
    toCompletedGroupAlgebra
        (map ((φ : C(Multiplicative ℤ_[p], Γ)).comp ⟨Multiplicative.ofAdd, continuous_ofAdd⟩) μ) =
      PowerSeries.aeval (isTopologicallyNilpotent_of_apply_ofAdd_one_sub_one φ)
        (amiceTransform μ) := by
  have h := PowerSeries.eval₂_unique (continuous_algebraMap ℤ_[p] _)
    (isTopologicallyNilpotent_of_apply_ofAdd_one_sub_one φ) (continuous_amiceIntegral φ)
    fun P ↦ by rw [amiceIntegral_coe, Polynomial.aeval_def]
  rw [PowerSeries.coe_aeval, ← h, amiceIntegral_apply, ← amiceTransformEquiv_apply,
    LinearEquiv.symm_apply_apply]

variable [Infinite Γ]

/-- **The Amice coordinate along a homomorphism `ℤ_p → Γ`.** Let `γ` topologically generate the
infinite commutative pro-`p` group `Γ`, and let `φ : ℤ_p → Γ` be a continuous homomorphism with
`φ 1 = γ`. Then the power-series coordinate `T ↦ [γ] - 1` of `ℤ_p[[Γ]]` sends the Amice transform
of `μ` to the completed-group-algebra element of the pushforward of `μ` along `φ`. -/
theorem powerSeriesCoordinate_amiceTransformEquiv_of_apply (hΓ : IsProP p Γ) {γ : Γ}
    (hγ : (Subgroup.closure ({γ} : Set Γ)).topologicalClosure = ⊤)
    (φ : Multiplicative ℤ_[p] →ₜ* Γ) (hφ : φ (.ofAdd 1) = γ) (μ : D(ℤ_[p], ℤ_[p])) :
    powerSeriesCoordinate hΓ hγ (amiceTransformEquiv μ) =
      completedGroupAlgebraEquiv
        (map ((φ : C(Multiplicative ℤ_[p], Γ)).comp ⟨Multiplicative.ofAdd, continuous_ofAdd⟩)
          μ) := by
  subst hφ
  rw [coe_powerSeriesCoordinate, completedGroupAlgebraEquiv_apply, amiceTransformEquiv_apply,
    toCompletedGroupAlgebra_map_eq_aeval_amiceTransform]

end General

/-- **The Amice coordinate is the completed-group-algebra coordinate.** For an integral measure `μ`
on `ℤ_p`, the power-series coordinate `T ↦ [γ] - 1` of `ℤ_p[[ℤ_p]]`, at the topological generator
`γ = 1` of `ℤ_p`, sends the Amice transform of `μ` to the completed-group-algebra element of `μ`.
In particular the Dirac measure `δ_a`, with transform `(1 + T) ^ a`, goes to `[a] = [γ ^ a]`. -/
theorem powerSeriesCoordinate_amiceTransformEquiv (μ : D(ℤ_[p], ℤ_[p])) :
    powerSeriesCoordinate (isProP_multiplicative_padicInt p)
        (topologicallyGenerates_ofAdd_one_padicInt p) (amiceTransformEquiv μ) =
      completedGroupAlgebraEquiv (map ⟨Multiplicative.ofAdd, continuous_ofAdd⟩ μ) := by
  convert powerSeriesCoordinate_amiceTransformEquiv_of_apply (isProP_multiplicative_padicInt p)
    (topologicallyGenerates_ofAdd_one_padicInt p) (ContinuousMonoidHom.id _) rfl μ using 4
  ext
  simp

/-- **The Amice coordinate on the principal units.** Transport of
`powerSeriesCoordinate_amiceTransformEquiv` to the principal units `1 + qℤ_p` of `ℤ_pˣ`, where
`q = p ^ padicUnitsDepth p`, along the isomorphism `a ↦ γ ^ a = exp (q a)` from `ℤ_p`: the
power-series coordinate `T ↦ [γ] - 1` at the generator `γ = exp q` sends the Amice transform of
`μ` to the completed-group-algebra element of the pushforward of `μ`. -/
theorem powerSeriesCoordinate_unitsPrincipal_amiceTransformEquiv (μ : D(ℤ_[p], ℤ_[p])) :
    powerSeriesCoordinate (isProP_unitsPrincipal p (padicUnitsDepth_pos p))
        topologicallyGenerates_padicUnitsGenerator (amiceTransformEquiv μ) =
      completedGroupAlgebraEquiv
        (map ⟨fun a ↦ (unitsPrincipalLogEquiv p).symm (.ofAdd a),
          (unitsPrincipalLogEquiv p).symm.continuous.comp continuous_ofAdd⟩ μ) := by
  convert powerSeriesCoordinate_amiceTransformEquiv_of_apply (φ := (unitsPrincipalLogEquiv p).symm)
    (isProP_unitsPrincipal p (padicUnitsDepth_pos p)) topologicallyGenerates_padicUnitsGenerator
    unitsPrincipalLogEquiv_symm_ofAdd_one μ using 4
  ext
  simp

/-- The Dirac measure at `a`, with Amice transform `(1 + T) ^ a`, has coordinate `[a] = [γ ^ a]`. -/
example (a : ℤ_[p]) :
    powerSeriesCoordinate (isProP_multiplicative_padicInt p)
        (topologicallyGenerates_ofAdd_one_padicInt p) (amiceTransformEquiv (dirac ℤ_[p] a)) =
      of ℤ_[p] (Multiplicative ℤ_[p]) (Multiplicative.ofAdd a) := by
  rw [powerSeriesCoordinate_amiceTransformEquiv, map_dirac, completedGroupAlgebraEquiv_apply,
    toCompletedGroupAlgebra_dirac, ContinuousMap.coe_mk]

end AbstractMeasure

end
