/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.Measure.AmiceTransform
public import Mathlib.RingTheory.PowerSeries.Substitution
public import TauCeti.NumberTheory.Padics.Division
public import TauCeti.NumberTheory.Padics.Measure.Moments
public import TauCeti.NumberTheory.Padics.Measure.Multiples
public import TauCeti.NumberTheory.Padics.Measure.Pushforward
import TauCeti.NumberTheory.Padics.MahlerBasis

/-!
# The operators `φ` and `ψ` on measures on `ℤ_p`

For a measure `μ` on `ℤ_p`, the measure `φ μ` is the pushforward of `μ` along multiplication by
`p`, and `ψ μ` restricts `μ` to the clopen subset `pℤ_p` and transports it back along
`p x ↦ x`:

`(φ μ) f = μ (x ↦ f (p x))`, `(ψ μ) f = μ (x ↦ if p ∣ x then f (x / p) else 0)`.

The second test function is continuous because `pℤ_p` is clopen; it is
`χ * (f ∘ PadicInt.divideByP p)`, where `χ` is the characteristic function of `pℤ_p`. There is no
averaging factor `p⁻¹`. These are the operators of the Cartier decomposition of measures: `ψ` is a
left inverse of `φ`, and `φ ψ` is restriction to `pℤ_p`, so `1 - φ ψ` is restriction to `ℤ_pˣ`.
Since `φ` is injective, the second identity alone determines `ψ`. On Amice transforms `φ` is the
substitution `T ↦ (1 + T) ^ p - 1`, the coefficientwise form of
`(1 + T) ^ (p x) = ((1 + T) ^ p) ^ x`.

The algebraic statements are made on `D(ℤ_p, R)` for a normed commutative ring `R` (and, for `φ`
and its Amice transform, for a topological commutative ring, respectively `ℤ_p`-algebra, `R`).
Over a nontrivially normed field, `φ` preserves and `ψ` does not increase the continuous-dual
norm.

## Main definitions

* `AbstractMeasure.phiMeasure`: pushforward along `x ↦ p x`.
* `AbstractMeasure.psiMeasure`: restriction to `pℤ_p` followed by transport along `p x ↦ x`.
* `TauCeti.psiSeries`: the transport of `psiMeasure` through the integral Amice equivalence.

## Main results

* `AbstractMeasure.amiceTransform_map_mulLeft_natCast`: pushforward along `x ↦ m x` is the
  substitution `T ↦ (1 + T) ^ m - 1` on Amice transforms.
* `AbstractMeasure.amiceTransform_phiMeasure`: `A_(φ μ) (T) = A_μ ((1 + T) ^ p - 1)`.
* `TauCeti.psiSeries_phi`: series psi is a left inverse of Frobenius substitution.
* `AbstractMeasure.amiceTransform_unitRestriction`: restriction to the units is the series
  projector `F ↦ F - (psiSeries p F).subst ((1 + X) ^ p - 1)`.
* `AbstractMeasure.psiMeasure_phiMeasure`: `ψ (φ μ) = μ`.
* `AbstractMeasure.phiMeasure_psiMeasure`: `φ (ψ μ)` is the restriction of `μ` to `pℤ_p`.
* `AbstractMeasure.unitRestriction_eq_id_sub_phiMeasure_comp_psiMeasure`: `1 - φ ψ` is restriction
  to `ℤ_pˣ`.
* `AbstractMeasure.existsUnique_psiMeasure`: `ψ` is the unique linear map with `φ ψ` the
  restriction to `pℤ_p`.
* `AbstractMeasure.norm_toCLMEquiv_phiMeasure`, `AbstractMeasure.norm_toCLMEquiv_psiMeasure_le`:
  the norm estimates over a nontrivially normed field.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.3 and §II.2.
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, §3.5.5.
-/

public noncomputable section

open ContinuousMap PowerSeries
open scoped AbstractMeasure

variable {p : ℕ} [Fact p.Prime]

namespace AbstractMeasure

section Phi

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- The operator `φ` on measures on `ℤ_p`: pushforward along multiplication by `p`, so that
`(φ μ) f = μ (x ↦ f (p x))`. -/
def phiMeasure : D(ℤ_[p], R) →ₗ[R] D(ℤ_[p], R) :=
  map (ContinuousMap.mulLeft (p : ℤ_[p]))

/-- `φ` is pushforward along multiplication by `p`. -/
theorem phiMeasure_eq_map :
    (phiMeasure : D(ℤ_[p], R) →ₗ[R] D(ℤ_[p], R)) = map (ContinuousMap.mulLeft (p : ℤ_[p])) :=
  (rfl)

/-- `φ μ` integrates `f` to the integral of `x ↦ f (p x)`. -/
@[simp]
theorem phiMeasure_apply (μ : D(ℤ_[p], R)) (f : C(ℤ_[p], R)) :
    phiMeasure μ f = μ (f.comp (ContinuousMap.mulLeft (p : ℤ_[p]))) :=
  map_apply _ μ f

/-- `φ` sends the Dirac measure at `x` to the Dirac measure at `p x`. -/
@[simp]
theorem phiMeasure_dirac (x : ℤ_[p]) : phiMeasure (dirac R x) = dirac R ((p : ℤ_[p]) * x) :=
  map_dirac _ x

/-- `φ` preserves the total mass `μ 1`. -/
theorem phiMeasure_apply_one (μ : D(ℤ_[p], R)) : phiMeasure μ 1 = μ 1 := by
  rw [phiMeasure_apply, one_comp]

variable [Algebra ℤ_[p] R] [ContinuousSMul ℤ_[p] R]

/-- **The Amice transform of a dilation**: the pushforward along multiplication by `m` composes
the Amice transform with `T ↦ (1 + T) ^ m - 1`. -/
theorem amiceTransform_map_mulLeft_natCast (m : ℕ) (μ : D(ℤ_[p], R)) :
    amiceTransform (map (ContinuousMap.mulLeft (m : ℤ_[p])) μ) =
      (amiceTransform μ).subst ((1 + X : R⟦X⟧) ^ m - 1) := by
  set G : ℤ⟦X⟧ := (1 + X) ^ m - 1
  have hG : constantCoeff ((1 + X : R⟦X⟧) ^ m - 1) = 0 := by simp
  -- Over `R`, the coefficients of the powers of the substituted series are those of `G`.
  have hcoeff (n k : ℕ) : coeff n (((1 + X : R⟦X⟧) ^ m - 1) ^ k) = ((coeff n (G ^ k) : ℤ) : R) := by
    rw [show (1 + X : R⟦X⟧) ^ m - 1 = PowerSeries.map (Int.castRingHom R) G by simp [G], ← map_pow,
      coeff_map, eq_intCast]
  -- The Mahler function `x ↦ (m x choose n)`, with values in `R`, in the Mahler basis.
  have hmahler (n : ℕ) :
      ((mahler n : C(ℤ_[p], ℤ_[p])) • (1 : C(ℤ_[p], R))).comp (ContinuousMap.mulLeft (m : ℤ_[p])) =
        ∑ k ∈ Finset.range (n + 1), ((coeff n (G ^ k) : ℤ) : R) •
          ((mahler k : C(ℤ_[p], ℤ_[p])) • (1 : C(ℤ_[p], R))) := by
    ext x
    simp only [comp_apply, coe_mulLeft, smul_apply', ContinuousMap.one_apply,
      PadicInt.mahler_natCast_mul, G, Finset.sum_smul, ContinuousMap.coe_sum, Finset.sum_apply,
      ContinuousMap.smul_apply, mul_smul, Int.cast_smul_eq_zsmul]
  ext n
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hG),
    finsum_eq_sum_of_support_subset (s := Finset.range (n + 1)) _ fun k hk ↦ ?_]
  · rw [coeff_amiceTransform, map_apply, hmahler, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp [hcoeff, coeff_amiceTransform, mul_comm]
  · -- Only the powers `k ≤ n` of a series without constant term contribute to `T ^ n`.
    rw [Function.mem_support] at hk
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra h
    refine hk ?_
    rw [coeff_of_lt_order _ ((Nat.cast_lt.mpr (by lia : n < k)).trans_le
      (le_order_pow_of_constantCoeff_eq_zero k hG)), smul_zero]

/-- **The Amice transform of `φ μ`** is the Amice transform of `μ` composed with
`T ↦ (1 + T) ^ p - 1`: `A_(φ μ) (T) = A_μ ((1 + T) ^ p - 1)`. -/
theorem amiceTransform_phiMeasure (μ : D(ℤ_[p], R)) :
    amiceTransform (phiMeasure μ) = (amiceTransform μ).subst ((1 + X : R⟦X⟧) ^ p - 1) := by
  rw [phiMeasure_eq_map, amiceTransform_map_mulLeft_natCast]

end Phi

section Psi

variable {R : Type*} [NormedCommRing R]

local instance : ContinuousMul C(ℤ_[p], R) :=
  ContinuousMap.instContinuousMulOfLocallyCompactSpace

/-- The operator `ψ` on measures on `ℤ_p`: restriction to `pℤ_p` followed by transport along
`p x ↦ x`, that is, pushforward along `PadicInt.divideByP p` of the restriction to `pℤ_p`. -/
def psiMeasure : D(ℤ_[p], R) →ₗ[R] D(ℤ_[p], R) :=
  map (PadicInt.divideByP p) ∘ₗ restrictMultiples

/-- `ψ μ` integrates `f` to the integral of `x ↦ if p ∣ x then f (x / p) else 0`. -/
@[simp]
theorem psiMeasure_apply (μ : D(ℤ_[p], R)) (f : C(ℤ_[p], R)) :
    psiMeasure μ f = μ (pMultiplesIndicator p R * f.comp (PadicInt.divideByP p)) := by
  rw [psiMeasure, LinearMap.comp_apply, map_apply, restrictMultiples_apply]

/-- `ψ` is a left inverse of `φ`. -/
@[simp]
theorem psiMeasure_phiMeasure (μ : D(ℤ_[p], R)) : psiMeasure (phiMeasure μ) = μ := by
  ext f
  rw [psiMeasure_apply, phiMeasure_apply]
  congr 1
  ext x
  simp [pMultiplesIndicator_eq_one (dvd_mul_right (p : ℤ_[p]) x)]

/-- `φ ψ` is the restriction to `pℤ_p`. -/
@[simp]
theorem phiMeasure_psiMeasure (μ : D(ℤ_[p], R)) :
    phiMeasure (psiMeasure μ) = restrictMultiples μ := by
  ext f
  rw [phiMeasure_apply, psiMeasure_apply, restrictMultiples_apply]
  congr 1
  ext x
  by_cases hx : (p : ℤ_[p]) ∣ x
  · simp [hx, PadicInt.mul_divideByP p hx]
  · simp [hx]

/-- `ψ ∘ φ` is the identity. -/
theorem psiMeasure_comp_phiMeasure :
    (psiMeasure ∘ₗ phiMeasure : D(ℤ_[p], R) →ₗ[R] D(ℤ_[p], R)) = LinearMap.id :=
  LinearMap.ext psiMeasure_phiMeasure

/-- `φ ∘ ψ` is the restriction to `pℤ_p`. -/
theorem phiMeasure_comp_psiMeasure :
    (phiMeasure ∘ₗ psiMeasure : D(ℤ_[p], R) →ₗ[R] D(ℤ_[p], R)) = restrictMultiples :=
  LinearMap.ext phiMeasure_psiMeasure

/-- `φ` is injective. -/
theorem phiMeasure_injective : Function.Injective (phiMeasure : D(ℤ_[p], R) → D(ℤ_[p], R)) :=
  Function.LeftInverse.injective psiMeasure_phiMeasure

/-- `1 - φ ψ` is the restriction to `ℤ_pˣ`. -/
theorem unitRestriction_eq_id_sub_phiMeasure_comp_psiMeasure :
    unitRestriction (p := p) (R := R) = LinearMap.id - phiMeasure ∘ₗ psiMeasure := by
  rw [phiMeasure_comp_psiMeasure, unitRestriction_eq_sub]

/-- Vanishing of psi is equivalent to vanishing of restriction to multiples of `p`. -/
theorem psiMeasure_eq_zero_iff_restrictMultiples_eq_zero (μ : D(ℤ_[p], R)) :
    psiMeasure μ = 0 ↔ restrictMultiples μ = 0 := by
  constructor
  · intro h
    rw [← phiMeasure_psiMeasure, h, map_zero]
  · intro h
    apply phiMeasure_injective
    rw [phiMeasure_psiMeasure, h, map_zero]

/-- The unit projector fixes exactly the kernel of psi. -/
theorem unitRestriction_eq_self_iff_psiMeasure_eq_zero (μ : D(ℤ_[p], R)) :
    unitRestriction μ = μ ↔ psiMeasure μ = 0 := by
  rw [unitRestriction_eq_self_iff_restrictMultiples_eq_zero,
    psiMeasure_eq_zero_iff_restrictMultiples_eq_zero]

/-- **`ψ` is determined by `φ`**: it is the unique linear map `ψ` for which `φ ψ` is the
restriction to `pℤ_p`. Such a map is automatically a left inverse of `φ`
(`psiMeasure_comp_phiMeasure`). -/
theorem existsUnique_psiMeasure :
    ∃! ψ : D(ℤ_[p], R) →ₗ[R] D(ℤ_[p], R), phiMeasure ∘ₗ ψ = restrictMultiples := by
  refine ⟨psiMeasure, phiMeasure_comp_psiMeasure, fun ψ hψ ↦ LinearMap.ext fun μ ↦ ?_⟩
  refine phiMeasure_injective ?_
  rw [← LinearMap.comp_apply, hψ, phiMeasure_psiMeasure]

/-- `ψ` sends the Dirac measure at `p x` to the Dirac measure at `x`. -/
@[simp]
theorem psiMeasure_dirac_mul (x : ℤ_[p]) : psiMeasure (dirac R ((p : ℤ_[p]) * x)) = dirac R x := by
  rw [← phiMeasure_dirac, psiMeasure_phiMeasure]

/-- `ψ` kills the Dirac measure at a unit of `ℤ_p`. -/
@[simp]
theorem psiMeasure_dirac_of_not_dvd {x : ℤ_[p]} (hx : ¬(p : ℤ_[p]) ∣ x) :
    psiMeasure (dirac R x) = 0 := by
  rw [psiMeasure, LinearMap.comp_apply, restrictMultiples_dirac_of_not_dvd hx, map_zero]

end Psi

section Norm

variable {K : Type*} [NontriviallyNormedField K]

/-- `ψ` does not increase the continuous-dual norm of a measure. -/
theorem norm_toCLMEquiv_psiMeasure_le (μ : D(ℤ_[p], K)) :
    ‖toCLMEquiv (psiMeasure μ)‖ ≤ ‖toCLMEquiv μ‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun f ↦ ?_
  rw [coe_toCLMEquiv, psiMeasure_apply, ← coe_toCLMEquiv μ]
  refine ((toCLMEquiv μ).le_opNorm _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  refine (ContinuousMap.norm_le _ (norm_nonneg _)).mpr fun x ↦ ?_
  rw [ContinuousMap.mul_apply, norm_mul]
  by_cases hx : (p : ℤ_[p]) ∣ x
  · rw [pMultiplesIndicator_eq_one hx, norm_one, one_mul, comp_apply]
    exact ContinuousMap.norm_coe_le_norm f _
  · rw [pMultiplesIndicator_eq_zero hx, norm_zero, zero_mul]
    exact norm_nonneg _

/-- `φ` preserves the continuous-dual norm of a measure. -/
@[simp]
theorem norm_toCLMEquiv_phiMeasure (μ : D(ℤ_[p], K)) :
    ‖toCLMEquiv (phiMeasure μ)‖ = ‖toCLMEquiv μ‖ := by
  refine le_antisymm (norm_toCLMEquiv_map_le μ _) ?_
  simpa using norm_toCLMEquiv_psiMeasure_le (phiMeasure μ)

end Norm

section Examples

variable {R : Type*} [NormedCommRing R]

/-- `ψ` fixes the Dirac measure at `0`. -/
example : psiMeasure (dirac R (0 : ℤ_[p])) = dirac R 0 := by
  simpa using psiMeasure_dirac_mul (R := R) (p := p) 0

/-- At `p = 3`, `φ δ₂ = δ₆`. -/
example : phiMeasure (dirac R (2 : ℤ_[3])) = dirac R 6 := by
  rw [phiMeasure_dirac]
  norm_num

/-- At `p = 3`, `ψ δ₆ = δ₂`. -/
example : psiMeasure (dirac R (6 : ℤ_[3])) = dirac R 2 := by
  have h : ((3 : ℕ) : ℤ_[3]) * 2 = 6 := by norm_num
  rw [← h, psiMeasure_dirac_mul]

/-- At `p = 3`, `ψ δ₁ = 0`, since `1` is a unit. -/
example : psiMeasure (dirac R (1 : ℤ_[3])) = 0 :=
  psiMeasure_dirac_of_not_dvd fun h ↦ PadicInt.p_nonunit (isUnit_of_dvd_one h)

end Examples

end AbstractMeasure

namespace TauCeti

open AbstractMeasure

variable (p)

/-- Psi on integral power series, obtained from restriction to `pℤ_p` followed by pushforward
along `x ↦ x / p` through the integral Amice equivalence. It is a linear map. -/
def psiSeries : ℤ_[p]⟦X⟧ →ₗ[ℤ_[p]] ℤ_[p]⟦X⟧ :=
  amiceTransformEquiv.conj psiMeasure

variable {p}

/-- Series psi is the transport of measure psi through the integral Amice equivalence. -/
theorem psiSeries_eq_transport :
    psiSeries p = amiceTransformEquiv.toLinearMap ∘ₗ psiMeasure ∘ₗ
      amiceTransformEquiv.symm.toLinearMap := (rfl)

/-- The measure-theoretic description of series psi. -/
theorem psiSeries_apply (F : ℤ_[p]⟦X⟧) :
    psiSeries p F = amiceTransform (psiMeasure (amiceTransformEquiv.symm F)) := by
  simp only [psiSeries, LinearEquiv.conj_apply_apply, amiceTransformEquiv_apply]

/-- The Amice transform intertwines measure psi and series psi. -/
@[simp↓]
theorem psiSeries_amiceTransform (μ : D(ℤ_[p], ℤ_[p])) :
    psiSeries p μ.amiceTransform = (psiMeasure μ).amiceTransform := by
  simp only [psiSeries, LinearEquiv.conj_apply_apply, ← amiceTransformEquiv_apply,
    LinearEquiv.symm_apply_apply]

/-- Series psi is a left inverse of Frobenius substitution. -/
@[simp]
theorem psiSeries_phi (F : ℤ_[p]⟦X⟧) :
    psiSeries p (F.subst ((1 + X) ^ p - 1)) = F := by
  obtain ⟨μ, rfl⟩ := amiceTransformEquiv.surjective F
  rw [amiceTransformEquiv_apply, ← amiceTransform_phiMeasure,
    psiSeries_amiceTransform, psiMeasure_phiMeasure]

/-- Frobenius after psi is the Amice transform of restriction to `pℤ_p`. -/
theorem subst_psiSeries_amiceTransform (μ : D(ℤ_[p], ℤ_[p])) :
    (psiSeries p μ.amiceTransform).subst ((1 + X) ^ p - 1) =
      (restrictMultiples μ).amiceTransform := by
  rw [psiSeries_amiceTransform, ← amiceTransform_phiMeasure, phiMeasure_psiMeasure]

/-- Series psi kills the Amice transform of `μ` iff `μ` is supported on `ℤ_pˣ`,
i.e. its restriction to `pℤ_p` vanishes. -/
theorem psiSeries_amiceTransform_eq_zero_iff (μ : D(ℤ_[p], ℤ_[p])) :
    psiSeries p μ.amiceTransform = 0 ↔ restrictMultiples μ = 0 := by
  rw [psiSeries_amiceTransform, map_eq_zero_iff _ injective_amiceTransform,
    psiMeasure_eq_zero_iff_restrictMultiples_eq_zero]

/-- Psi divides the exponent by `p` on binomial series with exponent in `pℤ_p`. -/
@[simp]
theorem psiSeries_binomialSeries_mul (x : ℤ_[p]) :
    psiSeries p (binomialSeries ℤ_[p] ((p : ℤ_[p]) * x)) = binomialSeries ℤ_[p] x := by
  rw [← amiceTransform_dirac, psiSeries_amiceTransform, psiMeasure_dirac_mul,
    amiceTransform_dirac]

/-- Psi kills binomial series whose exponent is a unit. -/
@[simp]
theorem psiSeries_binomialSeries_of_not_dvd {x : ℤ_[p]} (hx : ¬ (p : ℤ_[p]) ∣ x) :
    psiSeries p (binomialSeries ℤ_[p] x) = 0 := by
  rw [← amiceTransform_dirac, psiSeries_amiceTransform, psiMeasure_dirac_of_not_dvd hx,
    map_zero]

/-- Psi fixes the constant series one. -/
@[simp]
theorem psiSeries_one : psiSeries p 1 = 1 := by
  simpa only [mul_zero, binomialSeries_zero] using psiSeries_binomialSeries_mul (p := p) 0

/-- Psi kills `1 + X`, the transform of the Dirac mass at the unit one. -/
@[simp]
theorem psiSeries_one_add_X : psiSeries p (1 + X) = 0 := by
  have hunit : ¬ (p : ℤ_[p]) ∣ 1 := fun h ↦ PadicInt.p_nonunit (isUnit_of_dvd_one h)
  have h := psiSeries_binomialSeries_of_not_dvd hunit
  rw [← Nat.cast_one (R := ℤ_[p]), binomialSeries_nat, pow_one] at h
  exact h

-- Psi divides the exponent by the prime on atoms in pℤ_p; it does not average their mass.
example : psiSeries 3 ((1 + X) ^ 3) = 1 + X := by
  have h := psiSeries_binomialSeries_mul (p := 3) 1
  rw [mul_one, binomialSeries_nat, ← Nat.cast_one (R := ℤ_[3]), binomialSeries_nat,
    pow_one] at h
  exact h

end TauCeti

namespace AbstractMeasure

/-- Restriction to the units is the unit projector on integral Amice transforms. -/
theorem amiceTransform_unitRestriction (μ : D(ℤ_[p], ℤ_[p])) :
    (unitRestriction μ).amiceTransform =
      μ.amiceTransform - (TauCeti.psiSeries p μ.amiceTransform).subst ((1 + X) ^ p - 1) := by
  rw [TauCeti.subst_psiSeries_amiceTransform, unitRestriction_eq_sub, LinearMap.sub_apply,
    LinearMap.id_apply, map_sub]

end AbstractMeasure
