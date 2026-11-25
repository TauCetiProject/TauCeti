/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.TransferInstance
public import TauCeti.Analysis.Normed.Algebra.FunctionAlgebra
public import TauCeti.RingTheory.Affinoid.QuotientNorm
public import TauCeti.RingTheory.Affinoid.SpectralRadius
public import TauCeti.RingTheory.Affinoid.SupSeminorm
public import TauCeti.RingTheory.Huber.Uniform

import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.Topology.UniformSpace.Equiv
import TauCeti.Algebra.Module.LocalizedModule.Lift
import TauCeti.Analysis.Normed.Group.Quotient
import TauCeti.Analysis.Normed.Module.Finite.Basic
import TauCeti.Analysis.Normed.Unbundled.CoordinateNorm
import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Basis
import TauCeti.RingTheory.Affinoid.MaximumModulus
import TauCeti.RingTheory.Affinoid.MinimalPolynomial
import TauCeti.RingTheory.Affinoid.NoetherNormalization
import TauCeti.RingTheory.Huber.Normed
import TauCeti.RingTheory.Ideal.MinimalPrime.Basic
import TauCeti.RingTheory.Ideal.Quotient.Nilpotent
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Groebner
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UniqueFactorization
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.WeaklyStable

/-!
# Reduced affinoid algebras are Banach function algebras

Let `K` be a complete nontrivially normed ultrametric field of arbitrary characteristic, and let `A`
be an affinoid `K`-algebra. When `A` is reduced, its supremum seminorm `supSeminorm K` is a norm on
`A` (`TauCeti.IsAffinoidAlgebra.isReduced_iff_supSeminorm_eq_zero`). This file proves **Bosch,
Güntzer, Remmert, §6.2.4, Theorem 1**: on every reduced affinoid `K`-algebra `A` carrying any
complete `K`-algebra norm (not assumed ultrametric), the supremum norm is equivalent to the Banach
norm: `supSeminorm K f ≤ ‖f‖` (`TauCeti.supSeminorm_le_norm`) and
`∃ C > 0, ∀ f : A, ‖f‖ ≤ C * supSeminorm K f`
(`TauCeti.IsAffinoidAlgebra.exists_norm_le_mul_supSeminorm`).

In particular:
* Every completely normed reduced affinoid algebra is uniform
  (`TauCeti.IsAffinoidAlgebra.isUniform`).
* Equipping an affinoid algebra `A` (without any prior norm) with `supSeminorm K` produces a
  complete uniform ultrametric seminormed `K`-algebra (`TauCeti.IsAffinoidAlgebra.SupNormModel`),
  which is a Banach `K`-algebra when `A` is reduced; for any complete `K`-algebra norm on reduced
  `A` the identity is a bi-Lipschitz topological `K`-algebra isomorphism
  (`TauCeti.IsAffinoidAlgebra.supNormContinuousAlgEquiv`).
* Combining the equivalence with `AlgHom.supSeminorm_apply_le_gelfandRadius`, every `K`-algebra
  homomorphism `φ : B →ₐ[K] A` from an arbitrary normed `K`-algebra `B` with summable geometric
  series (not assumed complete, commutative, ultrametric, Noetherian, or unital-norm-normalized)
  into a completely normed reduced affinoid `K`-algebra `A` is automatically continuous
  (`TauCeti.IsAffinoidAlgebra.continuous_algHom_of_isReduced`).

## Main definitions and results

* `TauCeti.supSeminorm_eq_reducedSpectralAlgNorm`: base-change formula for `supSeminorm K` via
  `reducedSpectralAlgNorm`.
* `TauCeti.IsAffinoidAlgebra.exists_norm_le_mul_supSeminorm`: [BGR, §6.2.4, Theorem 1].
* `TauCeti.IsAffinoidAlgebra.isUniform`: reduced completely normed affinoid algebras are uniform.
* `TauCeti.IsAffinoidAlgebra.SupNormModel`, `TauCeti.IsAffinoidAlgebra.SupNormModel.map`, and
  `TauCeti.IsAffinoidAlgebra.supNormContinuousAlgEquiv`: the canonical complete supremum-normed
  seminormed / Banach algebra model of an affinoid algebra, its induced `1`-Lipschitz continuous
  algebra homomorphisms, and explicit Lipschitz comparisons
  (`TauCeti.IsAffinoidAlgebra.SupNormModel.lipschitzWith_toSupNorm`,
  `TauCeti.IsAffinoidAlgebra.SupNormModel.lipschitzWith_map`, and
  `TauCeti.IsAffinoidAlgebra.SupNormModel.exists_pos_lipschitzWith_ofSupNorm`).
* `TauCeti.IsAffinoidAlgebra.exists_pos_norm_apply_le_mul_gelfandRadius_of_isReduced` and
  `TauCeti.IsAffinoidAlgebra.continuous_algHom_of_isReduced`: quantitative spectral-radius bound and
  automatic continuity from normed `K`-algebras with summable geometric series into completely
  normed reduced affinoid algebras.

## References

* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert],
  §§3.8.3, 6.2.1, 6.2.2, and 6.2.4 (Theorem 1).
-/

public section

open scoped TensorProduct

namespace TauCeti

section TorsionFreeNormalization

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "Tate " σ:max =>
  _root_.MvPowerSeries.IsRestricted.subring (R := K) (fun _ : σ ↦ 1)

/-- Over a complete nontrivially normed ultrametric field `K`, when `A` is a reduced commutative
`K`-algebra that is finite and torsion-free over a finite-variable Tate algebra
`T = K⟨X₁, …, X_d⟩`, and `F` is any fraction field of `T` extending the Gauss norm isometrically
(for instance `TauCeti.MvPowerSeries.GaussFractionField σ K (fun _ ↦ 1)`), the supremum norm on `A`
agrees with `reducedSpectralAlgNorm` on `F ⊗[T] A`. -/
theorem supSeminorm_eq_reducedSpectralAlgNorm {σ : Type*} [Finite σ]
    {F : Type*} [NormedField F] [IsUltrametricDist F] [Algebra (Tate σ) F]
    [IsFractionRing (Tate σ) F] (hF : ∀ t : Tate σ, ‖algebraMap (Tate σ) F t‖ = ‖t‖)
    {A : Type*} [CommRing A] [IsReduced A] [Algebra K A] [Algebra (Tate σ) A]
    [IsScalarTower K (Tate σ) A] [Module.Finite (Tate σ) A] [Module.IsTorsionFree (Tate σ) A]
    (f : A) :
    supSeminorm K f = reducedSpectralAlgNorm F (F ⊗[Tate σ] A) (1 ⊗ₜ[Tate σ] f) := by
  rw [supSeminorm_eq_spectralValue_minpoly (σ := σ) f,
    reducedSpectralAlgNorm_one_tmul_eq_spectralValue_minpoly hF f]

end TorsionFreeNormalization

namespace IsAffinoidAlgebra

section SupNormModel

/-- Type wrapper for an affinoid algebra `A` (with no prior norm) used to equip `A` with its
canonical supremum seminorm `supSeminorm K`. Under `[NormedField K] [IsUltrametricDist K]`,
`hA.SupNormModel` carries only algebraic instances (`CommRing`, `Algebra K`, `algEquiv`); when `K`
is moreover complete and nontrivially normed it acquires the `supSeminorm K` seminormed-algebra
instances, and when `A` is moreover reduced it becomes a complete uniform ultrametric Banach
`K`-algebra. -/
structure SupNormModel {K A : Type*} [NormedField K] [IsUltrametricDist K]
    [CommRing A] [Algebra K A] (_hA : IsAffinoidAlgebra K A) where
  /-- View an element of `A` in the supremum-normed model `hA.SupNormModel`. -/
  toSupNorm ::
  /-- Underlying element of `A`. -/
  ofSupNorm : A

namespace SupNormModel

section Algebraic

variable {K A : Type*} [NormedField K] [IsUltrametricDist K]
  [CommRing A] [Algebra K A] {hA : IsAffinoidAlgebra K A}

@[ext]
theorem ext {x y : hA.SupNormModel} (h : x.ofSupNorm = y.ofSupNorm) : x = y := by
  cases x
  cases y
  congr

@[simp] theorem toSupNorm_ofSupNorm (x : hA.SupNormModel) : toSupNorm x.ofSupNorm = x := (rfl)
@[simp] theorem ofSupNorm_toSupNorm (a : A) : (toSupNorm a : hA.SupNormModel).ofSupNorm = a := (rfl)

/-- The canonical bijection between `hA.SupNormModel` and `A`. -/
def equiv (hA : IsAffinoidAlgebra K A) : hA.SupNormModel ≃ A where
  toFun := ofSupNorm
  invFun := toSupNorm
  left_inv := toSupNorm_ofSupNorm
  right_inv := ofSupNorm_toSupNorm

@[simp] theorem equiv_apply (x : hA.SupNormModel) : equiv hA x = x.ofSupNorm := (rfl)
@[simp] theorem equiv_symm_apply (a : A) : (equiv hA).symm a = toSupNorm a := (rfl)

instance : CommRing hA.SupNormModel := (equiv hA).commRing

@[simp] theorem toSupNorm_zero : (toSupNorm (0 : A) : hA.SupNormModel) = 0 := (rfl)
@[simp] theorem toSupNorm_one : (toSupNorm (1 : A) : hA.SupNormModel) = 1 := (rfl)
@[simp] theorem toSupNorm_add (a b : A) :
    (toSupNorm (a + b) : hA.SupNormModel) = toSupNorm a + toSupNorm b := (rfl)
@[simp] theorem toSupNorm_neg (a : A) :
    (toSupNorm (-a) : hA.SupNormModel) = -toSupNorm a := (rfl)
@[simp] theorem toSupNorm_sub (a b : A) :
    (toSupNorm (a - b) : hA.SupNormModel) = toSupNorm a - toSupNorm b := (rfl)
@[simp] theorem toSupNorm_mul (a b : A) :
    (toSupNorm (a * b) : hA.SupNormModel) = toSupNorm a * toSupNorm b := (rfl)
@[simp] theorem toSupNorm_pow (a : A) (n : ℕ) :
    (toSupNorm (a ^ n) : hA.SupNormModel) = toSupNorm a ^ n := (rfl)
@[simp, norm_cast] theorem toSupNorm_natCast (n : ℕ) :
    (toSupNorm (n : A) : hA.SupNormModel) = n := (rfl)
@[simp] theorem toSupNorm_ofNat (n : ℕ) [n.AtLeastTwo] :
    (toSupNorm (ofNat(n) : A) : hA.SupNormModel) = ofNat(n) := (rfl)
@[simp, norm_cast] theorem toSupNorm_intCast (n : ℤ) :
    (toSupNorm (n : A) : hA.SupNormModel) = n := (rfl)

@[simp] theorem ofSupNorm_zero : (0 : hA.SupNormModel).ofSupNorm = 0 := (rfl)
@[simp] theorem ofSupNorm_one : (1 : hA.SupNormModel).ofSupNorm = 1 := (rfl)
@[simp] theorem ofSupNorm_add (x y : hA.SupNormModel) :
    (x + y).ofSupNorm = x.ofSupNorm + y.ofSupNorm := (rfl)
@[simp] theorem ofSupNorm_neg (x : hA.SupNormModel) : (-x).ofSupNorm = -x.ofSupNorm := (rfl)
@[simp] theorem ofSupNorm_sub (x y : hA.SupNormModel) :
    (x - y).ofSupNorm = x.ofSupNorm - y.ofSupNorm := (rfl)
@[simp] theorem ofSupNorm_mul (x y : hA.SupNormModel) :
    (x * y).ofSupNorm = x.ofSupNorm * y.ofSupNorm := (rfl)
@[simp] theorem ofSupNorm_pow (x : hA.SupNormModel) (n : ℕ) :
    (x ^ n).ofSupNorm = x.ofSupNorm ^ n := (rfl)
@[simp, norm_cast] theorem ofSupNorm_natCast (n : ℕ) :
    (n : hA.SupNormModel).ofSupNorm = n := (rfl)
@[simp] theorem ofSupNorm_ofNat (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : hA.SupNormModel).ofSupNorm = ofNat(n) := (rfl)
@[simp, norm_cast] theorem ofSupNorm_intCast (n : ℤ) :
    (n : hA.SupNormModel).ofSupNorm = n := (rfl)

instance : Algebra K hA.SupNormModel := Equiv.algebra K (equiv hA)

@[simp] theorem toSupNorm_algebraMap (c : K) :
    (toSupNorm (algebraMap K A c) : hA.SupNormModel) = algebraMap K hA.SupNormModel c := (rfl)
@[simp] theorem toSupNorm_smul (c : K) (a : A) :
    (toSupNorm (c • a) : hA.SupNormModel) = c • toSupNorm a := (rfl)
@[simp] theorem ofSupNorm_algebraMap (c : K) :
    (algebraMap K hA.SupNormModel c).ofSupNorm = algebraMap K A c := (rfl)
@[simp] theorem ofSupNorm_smul (c : K) (x : hA.SupNormModel) :
    (c • x).ofSupNorm = c • x.ofSupNorm := (rfl)

/-- Canonical `K`-algebra isomorphism `A ≃ₐ[K] hA.SupNormModel`. -/
def algEquiv (hA : IsAffinoidAlgebra K A) : A ≃ₐ[K] hA.SupNormModel :=
  (Equiv.algEquiv K (equiv hA)).symm

@[simp] theorem algEquiv_apply (a : A) : algEquiv hA a = toSupNorm a := (rfl)
@[simp]
theorem algEquiv_symm_apply (x : hA.SupNormModel) : (algEquiv hA).symm x = x.ofSupNorm := (rfl)

instance [Subsingleton A] : Subsingleton hA.SupNormModel := (equiv hA).subsingleton
instance [Nontrivial A] : Nontrivial hA.SupNormModel := (equiv hA).nontrivial
instance [IsReduced A] : IsReduced hA.SupNormModel :=
  ⟨fun _ hx ↦ ext (hx.map (algEquiv hA).symm.toRingHom).eq_zero⟩

/-- `hA.SupNormModel` is itself an affinoid `K`-algebra. -/
theorem isAffinoidAlgebra (hA : IsAffinoidAlgebra K A) : IsAffinoidAlgebra K hA.SupNormModel :=
  hA.of_surjective (algEquiv hA).toAlgHom (algEquiv hA).surjective

end Algebraic

end SupNormModel

end SupNormModel

section UltrametricCase

open _root_.MvPowerSeries Polynomial

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "Tate " σ:max =>
  _root_.MvPowerSeries.IsRestricted.subring (R := K) (fun _ : σ ↦ 1)

section Domain

variable {n : ℕ} {A : Type*} [CommRing A] [IsDomain A] [Algebra K A]
  [Algebra (_root_.MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)) A]
  [IsScalarTower K (_root_.MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)) A]
  [Module.Finite (_root_.MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)) A]
  [FaithfulSMul (_root_.MvPowerSeries.IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)) A]

local notation "Frac " n:max => MvPowerSeries.GaussFractionField (Fin n) K (fun _ ↦ 1)

/-- Let `A` be an affinoid domain that is a finite faithful algebra over a Tate algebra `T`, and
let `L` be a field that is an algebra over `A` and over the Gauss-normed fraction field of `T`,
with both actions extending that of `T`. The spectral norm of `f : A` in `L` over the fraction
field of `T` is at most the supremum seminorm of `f`. -/
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

/-- An affinoid domain `A` that is a finite faithful algebra over a Tate algebra `T` admits an
injective `T`-linear map into a finite free `T`-module whose Gauss norm is bounded by a multiple
of the supremum seminorm. -/
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
  obtain ⟨C, hC, hb⟩ := (b.forall_exists_bound_iff spectralNorm_nonneg).mp fun φ ↦
    (MvPowerSeries.isWeaklyStable_gaussFractionField (Fin n) K _).exists_bound_spectralNorm φ
  -- Clearing denominators, the coordinates of `s f` lie in `T` for some nonzero `s : T`.
  let θ : (Fin m → T) →ₗ[T] (Fin m → Frac n) :=
    LinearMap.piMap fun _ ↦ Algebra.linearMap T (Frac n)
  have hθ : Function.Injective θ :=
    Pi.map_injective.mpr fun _ ↦ IsFractionRing.injective T (Frac n)
  have : IsLocalizedModule (nonZeroDivisors T) (θ.restrictScalars T) := by
    rw [LinearMap.restrictScalars_self]
    exact IsLocalizedModule.pi _ fun _ ↦ Algebra.linearMap T (Frac n)
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
  have := Huber.IsTateRing.of_normedAlgebra K (Tate (Fin d))
  obtain ⟨m, Φ, hΦ, C₁, hC₁, hΦC⟩ :=
    exists_linearMap_injective_norm_le_mul_supSeminorm (n := d) hA
  -- Since `A` is a finite module, the injective map `Φ` is bounded below.
  obtain ⟨C₂, hC₂⟩ := Φ.antilipschitz_of_injective_of_isNoetherian K hΦ
  refine ⟨(C₂ + 1) * C₁, by positivity, fun f ↦ (hC₂.le_mul_norm (map_zero Φ) f).trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul (by simp) (hΦC f) (norm_nonneg _) (by positivity)

/-- Ultrametric case of [BGR, §6.2.4, Theorem 1]: used internally to establish completeness of
`SupNormModel` on reduced affinoids via `residueNormedCommRing`. -/
private theorem exists_norm_le_mul_supSeminorm_of_isUltrametricDist [IsReduced A]
    (hA : IsAffinoidAlgebra K A) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : A, ‖f‖ ≤ C * supSeminorm K f := by
  classical
  have := hA.isNoetherianRing
  let := (minimalPrimes.finite_of_isNoetherianRing A).fintype
  have (I : Ideal A) : IsClosed (I : Set A) := hA.isClosed_ideal I
  -- The bound holds on each quotient by a minimal prime.
  have hcomp (𝔭 : minimalPrimes A) :
      ∃ C : ℝ, 0 < C ∧ ∀ f : A ⧸ 𝔭.val, ‖f‖ ≤ C * supSeminorm K f := by
    have : 𝔭.val.IsPrime := Ideal.IsMinimalPrime.isPrime 𝔭.property
    exact (hA.quotient 𝔭.val).exists_norm_le_mul_supSeminorm_of_isDomain
  choose C hC hCf using hcomp
  -- `A` embeds in the product of these quotients.
  let Ψ : A →ₗ[A] ((𝔭 : minimalPrimes A) → A ⧸ 𝔭.val) :=
    LinearMap.pi fun 𝔭 ↦ (Ideal.Quotient.mkₐ A 𝔭.val).toLinearMap
  have hΨf (f : A) (𝔭 : minimalPrimes A) : Ψ f 𝔭 = Ideal.Quotient.mk 𝔭.val f := by simp [Ψ]
  have hΨ : Function.Injective Ψ := Ideal.injective_pi_quotient_mk_minimalPrimes A
  have := Huber.IsTateRing.of_normedAlgebra K A
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
  have hsup := hA.supSeminorm_map_le (hA.quotient 𝔭.val) (Ideal.Quotient.mkₐ K 𝔭.val) f
  rw [Ideal.Quotient.mkₐ_eq_mk] at hsup
  rw [hΨf]
  exact mul_le_mul hle hsup (supSeminorm_nonneg _) hD.le

end UltrametricCase

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

section SupNormBanach

namespace SupNormModel

section

variable {A : Type*} [CommRing A] [Algebra K A] {hA : IsAffinoidAlgebra K A}

noncomputable instance : SeminormedCommRing hA.SupNormModel where
  __ := (inferInstance : CommRing hA.SupNormModel)
  __ := RingSeminorm.toSeminormedRing
    { toFun := fun x : hA.SupNormModel ↦ supSeminorm K x.ofSupNorm
      map_zero' := by rw [ofSupNorm_zero, supSeminorm_zero]
      add_le' := fun x y ↦ by
        rw [ofSupNorm_add]
        exact (hA.supSeminorm_add_le x.ofSupNorm y.ofSupNorm).trans
          (max_le_add_of_nonneg (supSeminorm_nonneg _) (supSeminorm_nonneg _))
      neg' := fun x ↦ by rw [ofSupNorm_neg, supSeminorm_neg]
      mul_le' := fun x y ↦ by
        rw [ofSupNorm_mul]
        exact hA.supSeminorm_mul_le x.ofSupNorm y.ofSupNorm }

/-- The norm on `hA.SupNormModel` is `supSeminorm K` of the underlying element. -/
@[simp] theorem norm_def (x : hA.SupNormModel) : ‖x‖ = supSeminorm K x.ofSupNorm := (rfl)

/-- The distance on `hA.SupNormModel` is `supSeminorm K` of the difference of underlying
elements. -/
@[simp] theorem dist_def (x y : hA.SupNormModel) :
    dist x y = supSeminorm K (x.ofSupNorm - y.ofSupNorm) := by
  rw [dist_eq_norm, norm_def, ofSupNorm_sub]

noncomputable instance : NormedAlgebra K hA.SupNormModel where
  norm_smul_le c x := by
    rw [norm_def, norm_def, ofSupNorm_smul]
    exact (supSeminorm_smul c x.ofSupNorm).le

instance : IsUltrametricDist hA.SupNormModel :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y ↦ by
    rw [norm_def, norm_def, norm_def, ofSupNorm_add]
    exact hA.supSeminorm_add_le x.ofSupNorm y.ofSupNorm

instance [Nontrivial A] : NormOneClass hA.SupNormModel where
  norm_one := by rw [norm_def, ofSupNorm_one, supSeminorm_one]

/-- The supremum norm on `hA.SupNormModel` is power-multiplicative. -/
theorem isPowMul_norm : IsPowMul (norm : hA.SupNormModel → ℝ) := fun x _n hn ↦ by
  rw [norm_def, norm_def, ofSupNorm_pow]
  exact supSeminorm_pow x.ofSupNorm (Nat.one_le_iff_ne_zero.mp hn)

noncomputable instance [IsReduced A] : NormedCommRing hA.SupNormModel :=
  { (inferInstance : SeminormedCommRing hA.SupNormModel) with
    eq_of_dist_eq_zero := fun {x y} hxy ↦ by
      rw [dist_def] at hxy
      exact ext (sub_eq_zero.mp (hA.isReduced_iff_supSeminorm_eq_zero.mp ‹_› _ hxy)) }

end

/-- `toSupNorm : A → hA.SupNormModel` is `1`-Lipschitz for any algebra norm on `A` with summable
geometric series. -/
theorem lipschitzWith_toSupNorm {A : Type*} [NormedCommRing A] [NormedAlgebra K A]
    {hA : IsAffinoidAlgebra K A} [HasSummableGeomSeries A] :
    LipschitzWith 1 (toSupNorm : A → hA.SupNormModel) :=
  LipschitzWith.of_dist_le_mul fun x y ↦ by
    rw [NNReal.coe_one, one_mul, dist_def, ofSupNorm_toSupNorm, dist_eq_norm]
    exact supSeminorm_le_norm (x - y)

section Map

variable {A B : Type*} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  {hA : IsAffinoidAlgebra K A} {hB : IsAffinoidAlgebra K B}

private theorem lipschitzWith_map_aux (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B)
    (φ : A →ₐ[K] B) :
    LipschitzWith 1 (fun x : hA.SupNormModel ↦ (toSupNorm (φ x.ofSupNorm) : hB.SupNormModel)) :=
  LipschitzWith.of_dist_le_mul fun x y ↦ by
    rw [NNReal.coe_one, one_mul, dist_def, dist_def, ofSupNorm_toSupNorm, ofSupNorm_toSupNorm,
      ← map_sub]
    exact hA.supSeminorm_map_le hB φ (x.ofSupNorm - y.ofSupNorm)

/-- The `1`-Lipschitz continuous `K`-algebra homomorphism `hA.SupNormModel →A[K] hB.SupNormModel`
induced by a `K`-algebra homomorphism `φ : A →ₐ[K] B` between affinoid algebras. -/
noncomputable def map (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B)
    (φ : A →ₐ[K] B) : hA.SupNormModel →A[K] hB.SupNormModel :=
  { (algEquiv hB).toAlgHom.comp (φ.comp (algEquiv hA).symm.toAlgHom) with
    cont := (lipschitzWith_map_aux hA hB φ).continuous }

/-- Evaluation of `SupNormModel.map hA hB φ` applies `φ` to the underlying element. -/
@[simp]
theorem map_apply (φ : A →ₐ[K] B) (x : hA.SupNormModel) :
    map hA hB φ x = toSupNorm (φ x.ofSupNorm) :=
  (rfl)

/-- `SupNormModel.map` sends the identity algebra homomorphism to the identity continuous algebra
homomorphism. -/
@[simp]
theorem map_id (hA : IsAffinoidAlgebra K A) :
    map hA hA (AlgHom.id K A) = ContinuousAlgHom.id K hA.SupNormModel :=
  ContinuousAlgHom.ext fun x ↦ by simp [map_apply]

/-- Composition of induced continuous algebra homomorphisms `SupNormModel.map` is the map induced
by the composite algebra homomorphism. -/
@[simp]
theorem map_comp {C : Type*} [CommRing C] [Algebra K C] {hC : IsAffinoidAlgebra K C}
    (ψ : B →ₐ[K] C) (φ : A →ₐ[K] B) :
    (map hB hC ψ).comp (map hA hB φ) = map hA hC (ψ.comp φ) :=
  ContinuousAlgHom.ext fun x ↦ by simp [map_apply]

/-- Every induced map `SupNormModel.map hA hB φ` between supremum-normed models is
`1`-Lipschitz. -/
theorem lipschitzWith_map (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B)
    (φ : A →ₐ[K] B) : LipschitzWith 1 (map hA hB φ) :=
  lipschitzWith_map_aux hA hB φ

end Map

section

variable {A : Type*} [CommRing A] [Algebra K A] {hA : IsAffinoidAlgebra K A}

/-- Completeness of `hA.SupNormModel` in the reduced case, via the residue norm. -/
private theorem completeSpace_of_isReduced [IsReduced A] : CompleteSpace hA.SupNormModel := by
  let : NormedCommRing A := hA.residueNormedCommRing
  let : NormedAlgebra K A := hA.residueNormedAlgebra
  have : IsUltrametricDist A := hA.isUltrametricDist_residueNormedCommRing
  have : CompleteSpace A := hA.completeSpace_residueNormedCommRing
  obtain ⟨C, hC, hbound⟩ := hA.exists_norm_le_mul_supSeminorm_of_isUltrametricDist
  have hlip₂ : LipschitzWith (Real.toNNReal C) (ofSupNorm : hA.SupNormModel → A) :=
    LipschitzWith.of_dist_le_mul fun x y ↦ by
      rw [Real.coe_toNNReal C hC.le, dist_eq_norm, dist_def]
      exact hbound (x.ofSupNorm - y.ofSupNorm)
  let e : A ≃ᵤ hA.SupNormModel :=
    { toEquiv := (algEquiv hA).toEquiv
      uniformContinuous_toFun := (lipschitzWith_toSupNorm (hA := hA)).uniformContinuous
      uniformContinuous_invFun := hlip₂.uniformContinuous }
  exact e.completeSpace_iff.mp inferInstance

/-- **Completeness of the supremum seminorm on an affinoid algebra**
([BGR, §6.2.4, Corollary 2]): for any affinoid algebra `A` over a complete nontrivially normed
ultrametric field `K`, `hA.SupNormModel` is a complete seminormed `K`-algebra. -/
instance : CompleteSpace hA.SupNormModel := by
  let q := map hA (hA.quotient (nilradical A)) (Ideal.Quotient.mkₐ K (nilradical A))
  have hq_iso : Isometry q := Isometry.of_dist_eq fun x y ↦ by
    simp only [q, map_apply, dist_def, Ideal.Quotient.mkₐ_eq_mk, ← map_sub,
      supSeminorm_mk_nilradical]
  have hq_surj : Function.Surjective q := fun y ↦
    let ⟨a, ha⟩ := Ideal.Quotient.mk_surjective y.ofSupNorm
    ⟨toSupNorm a, ext ha⟩
  have : CompleteSpace (hA.quotient (nilradical A)).SupNormModel := completeSpace_of_isReduced
  exact (hq_iso.isUniformInducing.completeSpace_congr hq_surj).mpr inferInstance

instance : Huber.IsUniform hA.SupNormModel := by
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := NormedField.exists_norm_lt_one K
  have hϖ : Huber.IsPseudoUniformizer (algebraMap K hA.SupNormModel ϖ) :=
    (Huber.IsPseudoUniformizer.of_norm_lt_one (isUnit_iff_ne_zero.mpr (norm_pos_iff.mp hϖ0))
      hϖ1).map (continuous_algebraMap K hA.SupNormModel)
  exact Huber.IsUniform.of_isPowMul hϖ isPowMul_norm

end

section NormComparison

variable {A : Type*} [NormedCommRing A] [NormedAlgebra K A] {hA : IsAffinoidAlgebra K A}

/-- `ofSupNorm : hA.SupNormModel → A` is Lipschitz for any complete algebra norm on a reduced
affinoid algebra `A`. -/
theorem exists_pos_lipschitzWith_ofSupNorm [CompleteSpace A] [IsReduced A] :
    ∃ C : NNReal, 0 < C ∧ LipschitzWith C (ofSupNorm : hA.SupNormModel → A) := by
  let e : A ≃L[K] hA.SupNormModel :=
    (algEquiv hA).toLinearEquiv.toContinuousLinearEquivOfContinuous
      (lipschitzWith_toSupNorm (hA := hA)).continuous
  let f : hA.SupNormModel →L[K] A := e.symm
  refine ⟨max ‖f‖₊ 1, zero_lt_one.trans_le (le_max_right _ _), ?_⟩
  exact f.lipschitzWith.weaken (le_max_left _ _)

end NormComparison

end SupNormModel

/-- **Bosch–Güntzer–Remmert, §6.2.4, Theorem 1 (Banach function algebra theorem).**
Let `A` be a reduced affinoid algebra over a complete nontrivially normed ultrametric field `K` (of
arbitrary characteristic), equipped with any complete `K`-algebra norm. Then the Banach norm on `A`
is bounded by a constant multiple of the supremum norm `supSeminorm K`: there exists `C > 0` such
that `‖f‖ ≤ C * supSeminorm K f` for every `f : A`. Combined with `TauCeti.supSeminorm_le_norm`,
the two norms are equivalent. -/
theorem exists_norm_le_mul_supSeminorm {A : Type*} [NormedCommRing A] [NormedAlgebra K A]
    [CompleteSpace A] [IsReduced A] (hA : IsAffinoidAlgebra K A) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : A, ‖f‖ ≤ C * supSeminorm K f := by
  obtain ⟨C, hC, hlip⟩ := SupNormModel.exists_pos_lipschitzWith_ofSupNorm (hA := hA)
  refine ⟨C, hC, fun f ↦ ?_⟩
  simpa only [dist_zero_right, SupNormModel.ofSupNorm_toSupNorm, SupNormModel.ofSupNorm_zero,
    SupNormModel.norm_def, sub_zero] using hlip.dist_le_mul (SupNormModel.toSupNorm f) 0

/-- **Uniformity of reduced affinoid algebras.** Every reduced affinoid `K`-algebra over a complete
nontrivially normed ultrametric field `K` carrying a complete `K`-algebra norm has bounded
power-bounded subring (`TauCeti.Huber.IsUniform`). -/
theorem isUniform {A : Type*} [NormedCommRing A] [NormedAlgebra K A]
    [CompleteSpace A] [IsReduced A] (hA : IsAffinoidAlgebra K A) :
    Huber.IsUniform A := by
  obtain ⟨C, hC, hbound⟩ := hA.exists_norm_le_mul_supSeminorm
  exact Huber.IsUniform.of_norm_le_mul_gelfandRadius K ⟨C, fun f ↦
    (hbound f).trans (mul_le_mul_of_nonneg_left
      ((AlgHom.id K A).supSeminorm_apply_le_gelfandRadius f) hC.le)⟩

/-- For any reduced affinoid `K`-algebra `A` over a complete nontrivially normed ultrametric field
`K` carrying a complete `K`-algebra norm, the identity map to `hA.SupNormModel` is a topological
`K`-algebra isomorphism: `supSeminorm K` defines the canonical Banach topology on `A`. -/
noncomputable def supNormContinuousAlgEquiv {A : Type*} [NormedCommRing A] [NormedAlgebra K A]
    [CompleteSpace A] [IsReduced A] (hA : IsAffinoidAlgebra K A) :
    A ≃A[K] hA.SupNormModel :=
  { SupNormModel.algEquiv hA with
    continuous_toFun := SupNormModel.lipschitzWith_toSupNorm.continuous
    continuous_invFun :=
      ((SupNormModel.algEquiv hA).toLinearEquiv.toContinuousLinearEquivOfContinuous
        SupNormModel.lipschitzWith_toSupNorm.continuous).continuous_invFun }

/-- `supNormContinuousAlgEquiv` has `SupNormModel.toSupNorm` as its underlying function. -/
@[simp]
theorem coe_supNormContinuousAlgEquiv {A : Type*} [NormedCommRing A] [NormedAlgebra K A]
    [CompleteSpace A] [IsReduced A] (hA : IsAffinoidAlgebra K A) :
    ⇑hA.supNormContinuousAlgEquiv = SupNormModel.toSupNorm :=
  (rfl)

/-- The underlying `K`-algebra isomorphism of `supNormContinuousAlgEquiv` is
`SupNormModel.algEquiv`. -/
@[simp]
theorem toAlgEquiv_supNormContinuousAlgEquiv {A : Type*} [NormedCommRing A] [NormedAlgebra K A]
    [CompleteSpace A] [IsReduced A] (hA : IsAffinoidAlgebra K A) :
    hA.supNormContinuousAlgEquiv.toAlgEquiv = SupNormModel.algEquiv hA :=
  (rfl)

/-- The inverse of `supNormContinuousAlgEquiv` extracts `SupNormModel.ofSupNorm`. -/
@[simp]
theorem supNormContinuousAlgEquiv_symm_apply {A : Type*} [NormedCommRing A] [NormedAlgebra K A]
    [CompleteSpace A] [IsReduced A] (hA : IsAffinoidAlgebra K A) (x : hA.SupNormModel) :
    hA.supNormContinuousAlgEquiv.symm x = x.ofSupNorm :=
  (rfl)

end SupNormBanach

section AutomaticContinuityFromBanach

variable {B A : Type*} [NormedRing B] [NormedAlgebra K B] [HasSummableGeomSeries B]
  [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A] [IsReduced A]

/-- Quantitative bound for `K`-algebra homomorphisms from an arbitrary normed `K`-algebra `B` with
summable geometric series into a completely normed reduced affinoid `K`-algebra `A` over a
complete nontrivially normed ultrametric field `K`: there exists `C > 0` (independent of `φ`)
such that `‖φ b‖ ≤ C * gelfandRadius b ≤ C * ‖b‖` for every `φ : B →ₐ[K] A` and `b : B`. -/
theorem exists_pos_norm_apply_le_mul_gelfandRadius_of_isReduced
    (hA : IsAffinoidAlgebra K A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (φ : B →ₐ[K] A) (b : B),
      ‖φ b‖ ≤ C * gelfandRadius b ∧ ‖φ b‖ ≤ C * ‖b‖ := by
  obtain ⟨C, hC, hbound⟩ := hA.exists_norm_le_mul_supSeminorm
  refine ⟨C, hC, fun φ b ↦ ?_⟩
  have h1 : ‖φ b‖ ≤ C * gelfandRadius b :=
    (hbound (φ b)).trans (mul_le_mul_of_nonneg_left (φ.supSeminorm_apply_le_gelfandRadius b)
      hC.le)
  exact ⟨h1, h1.trans (mul_le_mul_of_nonneg_left (gelfandRadius_le_norm b) hC.le)⟩

/-- **Automatic continuity from normed algebras with summable geometric series into reduced
affinoid algebras** ([BGR, §3.8.3 / §6.2.4]). Over a complete nontrivially normed ultrametric field
`K`, every `K`-algebra homomorphism from a normed `K`-algebra `B` with summable geometric series
(not assumed complete, commutative, ultrametric, Noetherian, or unital-norm-normalized) into a
completely normed reduced affinoid `K`-algebra `A` is continuous. -/
theorem continuous_algHom_of_isReduced (hA : IsAffinoidAlgebra K A) (φ : B →ₐ[K] A) :
    Continuous φ := by
  obtain ⟨C, _, hC⟩ := hA.exists_pos_norm_apply_le_mul_gelfandRadius_of_isReduced (B := B)
  exact (φ.toLinearMap.mkContinuous C fun b ↦ (hC φ b).2).continuous

end AutomaticContinuityFromBanach

end IsAffinoidAlgebra

end TauCeti
