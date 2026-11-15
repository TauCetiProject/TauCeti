/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.SupSeminorm
public import TauCeti.RingTheory.Huber.Uniform

import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import TauCeti.Algebra.Module.LocalizedModule.Lift
import TauCeti.Analysis.Normed.Group.Quotient
import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Basis
import TauCeti.RingTheory.Affinoid.Continuity
import TauCeti.RingTheory.Affinoid.MaximumModulus
import TauCeti.RingTheory.Affinoid.MinimalPolynomial
import TauCeti.RingTheory.Affinoid.NoetherNormalization
import TauCeti.RingTheory.Affinoid.PowerBounded
import TauCeti.RingTheory.Huber.Normed
import TauCeti.RingTheory.Huber.StrictMorphism
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Groebner
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UniqueFactorization
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.WeaklyStable

/-!
# Reduced affinoid algebras are Banach function algebras

Let `A` be a reduced affinoid algebra over a complete nonarchimedean field `K`, with a complete
ultrametric algebra norm `‖·‖`. The supremum seminorm `|·|sup` is then equivalent to `‖·‖`: there
is `C > 0` with

`|f|sup ≤ ‖f‖ ≤ C |f|sup` for every `f : A`.

The lower bound holds for every affinoid algebra
(`TauCeti.IsAffinoidAlgebra.supSeminorm_le_norm`); the upper bound fails as soon as `A` has a
nonzero nilpotent, whose supremum seminorm vanishes. Thus the supremum seminorm of a reduced
affinoid algebra is a norm equivalent to `‖·‖`: `A` is a Banach function algebra. In particular
the power-bounded elements `{f | |f|sup ≤ 1}` form a bounded set, so reduced affinoid algebras
are uniform.

For an affinoid domain `A`, choose a Noether normalisation `T = K⟨X₁, …, X_d⟩ → A`. The
Gauss-normed fraction field `F` of `T` is weakly stable, so on the finite extension
`L = Frac A` of `F` the coordinates in an `F`-basis are bounded by the spectral norm. For
`f : A`, the minimal polynomial of `f` over `F` is that over the integrally closed `T`, so the
spectral norm of `f` is at most its supremum seminorm. Clearing denominators, the coordinates of
`s f`, for a fixed nonzero `s : T`, lie in `T` and define an injective `T`-linear map `A → T^m`
whose Gauss norm is at most a constant times `|f|sup`. Since `A` is a finite `T`-module, this map
is strict, hence a topological embedding, so `‖f‖` is at most a constant times the Gauss norm of
the image of `f` (`LinearMap.antilipschitz_of_injective_of_isNoetherian`). A reduced affinoid
algebra embeds in the product of its quotients by minimal primes, again strictly, and the
supremum seminorm of each quotient is at most that of `A`.

## Main results

* `TauCeti.IsAffinoidAlgebra.exists_norm_le_mul_supSeminorm`: for reduced `A` there is `C > 0`
  with `‖f‖ ≤ C |f|sup` for all `f`.
* `TauCeti.IsAffinoidAlgebra.isUniform`: a reduced affinoid algebra with a complete ultrametric
  algebra norm is uniform.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§3.8.3 and
  6.2.4, Theorem 1.
-/

public section

namespace TauCeti.IsAffinoidAlgebra

open _root_.MvPowerSeries Polynomial

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "Tate " σ:max => IsRestricted.subring (R := K) (fun _ : σ ↦ 1)

section Domain

variable {n : ℕ} {A : Type*} [CommRing A] [IsDomain A] [Algebra K A]
  [Algebra (IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)) A]
  [IsScalarTower K (IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)) A]
  [Module.Finite (IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)) A]
  [FaithfulSMul (IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)) A]

local notation "Frac " n:max => MvPowerSeries.GaussFractionField (Fin n) K (fun _ ↦ 1)

/-- For an affinoid domain `A` finite over a Tate algebra `T` and a field `L` over `A`, the
spectral norm of `f : A` over the Gauss-normed fraction field of `T` is at most its supremum
seminorm, because the minimal polynomial of `f` over the fraction field is that over `T`. -/
private theorem spectralNorm_algebraMap_le_supSeminorm (hA : IsAffinoidAlgebra K A)
    {L : Type*} [Field L] [Algebra A L] [Algebra (Tate (Fin n)) L]
    [IsScalarTower (Tate (Fin n)) A L] [Algebra (Frac n) L]
    [IsScalarTower (Tate (Fin n)) (Frac n) L]
    (f : A) : spectralNorm (Frac n) L (algebraMap A L f) ≤ supSeminorm K f := by
  have : Algebra.IsIntegral (Tate (Fin n)) A := Algebra.IsIntegral.of_finite (Tate (Fin n)) A
  have hf := Algebra.IsIntegral.isIntegral (R := Tate (Fin n)) f
  rw [spectralNorm, minpoly.isIntegrallyClosed_eq_field_fractions _ L hf, spectralValue]
  refine ciSup_le fun i ↦ ?_
  rw [spectralValueTerms, (minpoly.monic hf).natDegree_map]
  split_ifs with hi
  · rw [Polynomial.coeff_map, MvPowerSeries.norm_algebraMap_gaussFractionField,
      ← MvPowerSeries.supSeminorm_eq_norm,
      hA.supSeminorm_eq_iSup_minpoly_coeff_rpow (A := Tate (Fin n)) f]
    exact le_ciSup (f := fun j : Fin (minpoly (Tate (Fin n)) f).natDegree ↦
      supSeminorm K ((minpoly (Tate (Fin n)) f).coeff j) ^
        (1 / ((minpoly (Tate (Fin n)) f).natDegree - j : ℝ)))
      (Set.finite_range _).bddAbove ⟨i, hi⟩
  · exact supSeminorm_nonneg f

/-- An affinoid domain `A` finite over a Tate algebra `T` admits an injective `T`-linear map into
a finite free `T`-module whose Gauss norm is bounded by a multiple of the supremum seminorm: the
coordinates of `s f`, in a basis of `Frac A` over the Gauss-normed fraction field of `T` and for
a common denominator `s`, are bounded by its spectral norm since that field is weakly stable. -/
private theorem exists_linearMap_injective_norm_le_mul_supSeminorm
    (hA : IsAffinoidAlgebra K A) :
    ∃ (m : ℕ) (Φ : A →ₗ[Tate (Fin n)] (Fin m → Tate (Fin n))), Function.Injective Φ ∧
      ∃ C : ℝ, 0 < C ∧ ∀ f : A, ‖Φ f‖ ≤ C * supSeminorm K f := by
  let T := Tate (Fin n)
  -- The fraction field `L` of `A` is a finite extension of the Gauss-normed fraction field.
  let L := FractionRing A
  have hTL : Function.Injective (algebraMap T L) := by
    rw [IsScalarTower.algebraMap_eq T A L]
    exact (IsFractionRing.injective A L).comp (FaithfulSMul.algebraMap_injective T A)
  let : Algebra (Frac n) L := (IsFractionRing.lift hTL).toAlgebra
  have : IsScalarTower T (Frac n) L := IsScalarTower.of_algebraMap_eq (R := T) (S := Frac n)
    (A := L) fun t ↦ (IsFractionRing.lift_algebraMap hTL t).symm
  have : Algebra.IsIntegral T A := Algebra.IsIntegral.of_finite T A
  have : FiniteDimensional (Frac n) L := Module.Finite.of_isLocalization T A (nonZeroDivisors T)
  let m := Module.finrank (Frac n) L
  let b := Module.finBasis (Frac n) L
  have : Nonempty (Fin m) := ⟨⟨0, Module.finrank_pos⟩⟩
  -- Weak stability bounds the coordinates by the spectral norm.
  obtain ⟨C, hC, hb⟩ := b.forall_exists_bound_spectralNorm_iff.mp fun φ ↦
    (MvPowerSeries.isWeaklyStable_gaussFractionField (Fin n) K _).exists_bound_spectralNorm φ
  -- Clearing denominators, the coordinates of `s f` lie in `T` for some nonzero `s : T`.
  let θ : (Fin m → T) →ₗ[T] (Fin m → Frac n) :=
    LinearMap.pi fun j ↦ Algebra.linearMap T (Frac n) ∘ₗ LinearMap.proj j
  have hθ : Function.Injective θ := fun x y h ↦
    funext fun j ↦ IsFractionRing.injective T (Frac n) (congr_fun h j)
  have : IsLocalizedModule (nonZeroDivisors T) (θ.restrictScalars T) := by
    rw [LinearMap.restrictScalars_self]
    infer_instance
  obtain ⟨Φ, s, hΦ⟩ := Module.Finite.exists_lift_of_isLocalizedModule_of_injective
    (nonZeroDivisors T) hθ ((b.equivFun : L →ₗ[Frac n] (Fin m → Frac n)).restrictScalars T ∘ₗ
      (IsScalarTower.toAlgHom T A L).toLinearMap)
  have hΦ (f : A) (j : Fin m) : algebraMap T (Frac n) (Φ f j) =
      algebraMap T (Frac n) s * b.repr (algebraMap A L f) j := by
    simpa [θ, Submonoid.smul_def, Algebra.smul_def] using congr_fun (LinearMap.congr_fun hΦ f) j
  have hs : (s : T) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hs' : algebraMap T (Frac n) s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective T (Frac n))).mpr hs
  refine ⟨m, Φ, fun f₁ f₂ h ↦ ?_, ‖(s : T)‖ * C, mul_pos (norm_pos_iff.mpr hs) hC, fun f ↦ ?_⟩
  · -- Equal coordinates of `s f₁` and `s f₂` force `f₁ = f₂`.
    refine IsFractionRing.injective A L (b.repr.injective (Finsupp.ext fun j ↦ ?_))
    have := congrArg (algebraMap T (Frac n)) (congr_fun h j)
    rwa [hΦ, hΦ, mul_right_inj' hs'] at this
  · refine (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) hC.le)
      (supSeminorm_nonneg f))).mpr fun j ↦ ?_
    rw [← MvPowerSeries.norm_algebraMap_gaussFractionField, hΦ, norm_mul,
      MvPowerSeries.norm_algebraMap_gaussFractionField, mul_assoc]
    gcongr
    exact (b.norm_repr_le_norm j).trans ((hb _).trans
      (mul_le_mul_of_nonneg_left (spectralNorm_algebraMap_le_supSeminorm hA f) hC.le))

end Domain

variable {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A]
  [CompleteSpace A]

/-- The norm of an affinoid domain is bounded by a multiple of its supremum seminorm. -/
private theorem exists_norm_le_mul_supSeminorm_of_isDomain [IsDomain A]
    (hA : IsAffinoidAlgebra K A) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : A, ‖f‖ ≤ C * supSeminorm K f := by
  obtain ⟨d, g, hg, hfin⟩ := hA.exists_finite_injective
  let := g.toRingHom.toAlgebra
  have : IsScalarTower K (Tate (Fin d)) A :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (g.commutes c).symm
  have : Module.Finite (Tate (Fin d)) A := hfin
  have : FaithfulSMul (Tate (Fin d)) A :=
    (faithfulSMul_iff_algebraMap_injective (Tate (Fin d)) A).mpr hg
  have : IsNoetherianRing (Tate (Fin d)) := MvPowerSeries.isNoetherianRing_isRestricted_subring
  have : ContinuousSMul (Tate (Fin d)) A :=
    continuousSMul_of_algebraMap _ A (hA.continuous_algHom g)
  obtain ⟨m, Φ, hΦ, C₁, hC₁, hΦC⟩ :=
    exists_linearMap_injective_norm_le_mul_supSeminorm (n := d) hA
  -- Since `A` is a finite module, the injective map `Φ` is bounded below.
  obtain ⟨C₂, hC₂⟩ := Φ.antilipschitz_of_injective_of_isNoetherian K hΦ
  refine ⟨(C₂ + 1) * C₁, by positivity, fun f ↦ (hC₂.le_mul_norm (map_zero Φ) f).trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul (by simp) (hΦC f) (norm_nonneg _) (by positivity)

/-- **Reduced affinoid algebras are Banach function algebras** [BGR, 6.2.4/1]. For a reduced
affinoid algebra `A` with a complete ultrametric algebra norm, there is `C > 0` with
`‖f‖ ≤ C |f|sup` for every `f : A`. Together with `TauCeti.IsAffinoidAlgebra.supSeminorm_le_norm`
this says that the supremum seminorm is a norm equivalent to `‖·‖`. -/
theorem exists_norm_le_mul_supSeminorm [IsReduced A] (hA : IsAffinoidAlgebra K A) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : A, ‖f‖ ≤ C * supSeminorm K f := by
  classical
  have := hA.isNoetherianRing
  let := (minimalPrimes.finite_of_isNoetherianRing A).fintype
  have (I : Ideal A) : IsClosed (I : Set A) := hA.isClosed_ideal I
  -- The bound holds on each quotient by a minimal prime.
  have hcomp (𝔭 : minimalPrimes A) :
      ∃ C : ℝ, 0 < C ∧ ∀ f : A ⧸ 𝔭.1, ‖f‖ ≤ C * supSeminorm K f := by
    have : 𝔭.1.IsPrime := Ideal.IsMinimalPrime.isPrime 𝔭.2
    exact (hA.quotient 𝔭.1).exists_norm_le_mul_supSeminorm_of_isDomain
  choose C hC hCf using hcomp
  -- `A` embeds in the product of these quotients.
  let Ψ : A →ₗ[A] ((𝔭 : minimalPrimes A) → A ⧸ 𝔭.1) :=
    LinearMap.pi fun 𝔭 ↦ (Ideal.Quotient.mkₐ A 𝔭.1).toLinearMap
  have hΨ : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro f hf
    have hf' : f ∈ sInf (minimalPrimes A) := Submodule.mem_sInf.mpr fun 𝔭 h𝔭 ↦
      Ideal.Quotient.eq_zero_iff_mem.mp (congr_fun (LinearMap.mem_ker.mp hf) ⟨𝔭, h𝔭⟩)
    rw [minimalPrimes, Ideal.sInf_minimalPrimes] at hf'
    obtain ⟨n, hn⟩ := hf'
    exact (Submodule.mem_bot A).mpr (IsReduced.eq_zero f ⟨n, (Submodule.mem_bot A).mp hn⟩)
  have (𝔭 : minimalPrimes A) : ContinuousSMul A (A ⧸ 𝔭.1) :=
    continuousSMul_of_algebraMap A _ continuous_quot_mk
  obtain ⟨C₀, hC₀⟩ := Ψ.antilipschitz_of_injective_of_isNoetherian K hΨ
  -- A single constant dominates the constants of all quotients.
  let D := 1 + ∑ 𝔭, C 𝔭
  have hD : 0 < D := add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun 𝔭 _ ↦ (hC 𝔭).le)
  refine ⟨(C₀ + 1) * D, by positivity, fun f ↦ (hC₀.le_mul_norm (map_zero Ψ) f).trans ?_⟩
  rw [mul_assoc]
  refine mul_le_mul (by simp) ((pi_norm_le_iff_of_nonneg
    (mul_nonneg hD.le (supSeminorm_nonneg f))).mpr fun 𝔭 ↦ (hCf 𝔭 _).trans ?_) (norm_nonneg _)
    (by positivity)
  have hle : C 𝔭 ≤ D := by
    have := Finset.single_le_sum (fun 𝔮 _ ↦ (hC 𝔮).le) (Finset.mem_univ 𝔭)
    linarith
  exact mul_le_mul hle (hA.supSeminorm_map_le (hA.quotient 𝔭.1) (Ideal.Quotient.mkₐ K 𝔭.1) f)
    (supSeminorm_nonneg _) hD.le

/-- **Reduced affinoid algebras are uniform.** In a reduced affinoid algebra with a complete
ultrametric algebra norm, the set of power-bounded elements is bounded. -/
theorem isUniform [IsReduced A] (hA : IsAffinoidAlgebra K A) : Huber.IsUniform A := by
  obtain ⟨C, hC₀, hC⟩ := hA.exists_norm_le_mul_supSeminorm
  refine ⟨(Huber.isBounded_closedBall_zero C).subset fun f hf ↦ ?_⟩
  rw [mem_closedBall_zero_iff]
  exact (hC f).trans (mul_le_of_le_one_right hC₀.le
    (hA.isPowerBounded_iff_supSeminorm_le_one.mp hf))

end TauCeti.IsAffinoidAlgebra
