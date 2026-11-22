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

import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Topology.UniformSpace.Equiv
import TauCeti.Analysis.Normed.Operator.Embedding
import TauCeti.FieldTheory.Minpoly.TorsionFree
import TauCeti.RingTheory.Affinoid.Integral.Basic
import TauCeti.RingTheory.Affinoid.MaximumModulus
import TauCeti.RingTheory.Affinoid.MinimalPolynomial
import TauCeti.RingTheory.Affinoid.NoetherNormalization
import TauCeti.RingTheory.Huber.Normed
import TauCeti.RingTheory.Huber.StrictMorphism
import TauCeti.RingTheory.Ideal.MinimalPrime.Basic
import TauCeti.RingTheory.Ideal.Quotient.Nilpotent
import TauCeti.RingTheory.Localization.TensorProduct
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.FractionField
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
  homomorphism `φ : B →ₐ[K] A` from an arbitrary Banach `K`-algebra `B` (not assumed commutative,
  ultrametric, Noetherian, or unital-norm-normalized) into a completely normed reduced affinoid
  `K`-algebra `A` is automatically continuous
  (`TauCeti.IsAffinoidAlgebra.continuous_algHom_of_isReduced`).

## Main definitions and results

* `TauCeti.IsAffinoidAlgebra.supSeminorm_eq_spectralValue_minpoly`,
  `TauCeti.supSeminorm_eq_spectralValue_minpoly`, and
  `TauCeti.supSeminorm_eq_reducedSpectralAlgNorm`: minimal-polynomial and base-change formulas for
  `supSeminorm K`.
* `TauCeti.IsAffinoidAlgebra.exists_norm_le_mul_supSeminorm`: [BGR, §6.2.4, Theorem 1].
* `TauCeti.IsAffinoidAlgebra.isUniform`: reduced completely normed affinoid algebras are uniform.
* `TauCeti.IsAffinoidAlgebra.SupNormModel` and
  `TauCeti.IsAffinoidAlgebra.supNormContinuousAlgEquiv`: the canonical complete supremum-normed
  seminormed / Banach algebra model of an affinoid algebra, with explicit Lipschitz comparisons
  (`TauCeti.IsAffinoidAlgebra.SupNormModel.lipschitzWith_toSupNorm` and
  `TauCeti.IsAffinoidAlgebra.SupNormModel.exists_pos_lipschitzWith_ofSupNorm`).
* `TauCeti.IsAffinoidAlgebra.exists_pos_norm_apply_le_mul_gelfandRadius_of_isReduced` and
  `TauCeti.IsAffinoidAlgebra.continuous_algHom_of_isReduced`: quantitative spectral-radius bound and
  automatic continuity from arbitrary Banach `K`-algebras into completely normed reduced affinoid
  algebras.

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

/-- **Bosch–Güntzer–Remmert, §6.2.1, Proposition 4(iii).**
Over a complete nontrivially normed ultrametric field `K`, let `A` be an affinoid `K`-algebra
integral and torsion-free over an integrally closed seminormed domain `B` whose supremum seminorm
agrees with its norm. Then for every `f : A`, `supSeminorm K f = spectralValue (minpoly B f)`. -/
theorem IsAffinoidAlgebra.supSeminorm_eq_spectralValue_minpoly
    {B : Type*} [SeminormedCommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra K B]
    {A : Type*} [CommRing A] [Algebra K A] (hA : IsAffinoidAlgebra K A)
    [Algebra B A] [IsScalarTower K B A] [Module.IsTorsionFree B A] [Algebra.IsIntegral B A]
    (hB : ∀ b : B, supSeminorm K b = ‖b‖) (f : A) :
    supSeminorm K f = spectralValue (minpoly B f) := by
  open Polynomial in
  rw [hA.supSeminorm_eq_iSup_minpoly_coeff_rpow (A := B) f]
  simp_rw [hB]
  set p := minpoly B f
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | hpos
  · have hp1 : p = 1 :=
      (minpoly.monic (Algebra.IsIntegral.isIntegral (R := B) f)).natDegree_eq_zero.mp h0
    have : IsEmpty (Fin p.natDegree) := h0 ▸ Fin.isEmpty'
    rw [Real.iSup_of_isEmpty, hp1, Polynomial.spectralValue_one]
  · have : Nonempty (Fin p.natDegree) := ⟨⟨0, hpos⟩⟩
    refine le_antisymm ?_ ?_
    · refine Real.iSup_le (fun i ↦ ?_) (spectralValue_nonneg p)
      rw [← spectralValueTerms_of_lt_natDegree p i.isLt]
      exact le_ciSup (spectralValueTerms_bddAbove p) (i : ℕ)
    · refine ciSup_le fun n ↦ ?_
      by_cases hn : n < p.natDegree
      · rw [spectralValueTerms_of_lt_natDegree p hn]
        exact le_ciSup (Finite.bddAbove_range
          (fun i : Fin p.natDegree ↦ ‖p.coeff i‖ ^ (1 / (p.natDegree - i : ℝ)))) ⟨n, hn⟩
      · rw [spectralValueTerms_of_natDegree_le p (not_lt.mp hn)]
        exact Real.iSup_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _

/-- **Bosch–Güntzer–Remmert, §6.2.2, Proposition 1 / §6.2.1, Proposition 4(iii).**
Over a complete nontrivially normed ultrametric field `K`, let `A` be a commutative `K`-algebra
(with no choice of norm or reducedness assumption) that is finite and torsion-free over a
finite-variable Tate algebra `T = K⟨X₁, …, X_d⟩`. Then for every `f : A`,
`supSeminorm K f = spectralValue (minpoly T f)`. -/
theorem supSeminorm_eq_spectralValue_minpoly {σ : Type*} [Finite σ]
    {A : Type*} [CommRing A] [Algebra K A] [Algebra (Tate σ) A] [IsScalarTower K (Tate σ) A]
    [Module.Finite (Tate σ) A] [Module.IsTorsionFree (Tate σ) A] (f : A) :
    supSeminorm K f = spectralValue (minpoly (Tate σ) f) := by
  have hA : IsAffinoidAlgebra K A := (isAffinoidAlgebra_tate (K := K) (σ := σ)).of_finite
  have : Algebra.IsIntegral (Tate σ) A := Algebra.IsIntegral.of_finite _ _
  let _ := Fintype.ofFinite σ
  let e : Tate σ ≃ₐ[K] Tate (Fin (Fintype.card σ)) :=
    _root_.MvPowerSeries.IsRestricted.renameAlgEquiv (R := K) (Fintype.equivFin σ) fun _ ↦ 1
  have hsup (t : Tate σ) : supSeminorm K t = ‖t‖ := by
    rw [← AlgEquiv.supSeminorm_eq e t, MvPowerSeries.supSeminorm_eq_norm,
      _root_.MvPowerSeries.IsRestricted.norm_renameAlgEquiv]
  exact hA.supSeminorm_eq_spectralValue_minpoly hsup f

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

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "Tate " σ:max =>
  _root_.MvPowerSeries.IsRestricted.subring (R := K) (fun _ : σ ↦ 1)

section BanachFunctionAlgebra

/-- Domain case of [BGR, §6.2.4, Theorem 1]: an affinoid domain embeds finitely and torsion-freely
over a Tate algebra via Noether normalization, and the fraction field of that Tate algebra is
weakly stable in arbitrary characteristic. -/
private theorem exists_norm_le_mul_supSeminorm_of_isDomain {B : Type*} [NormedCommRing B]
    [IsDomain B] [NormedAlgebra K B] [IsUltrametricDist B] [CompleteSpace B]
    (hB : IsAffinoidAlgebra K B) :
    ∃ C : ℝ, 0 < C ∧ ∀ b : B, ‖b‖ ≤ C * supSeminorm K b := by
  obtain ⟨d, g, hg_inj, hg_fin⟩ := hB.exists_finite_injective
  have : IsNoetherianRing (Tate (Fin d)) :=
    (isAffinoidAlgebra_tate (K := K) (σ := Fin d)).isNoetherianRing
  have hg_cont : Continuous g := hB.continuous_algHom g
  have hg_tf : ∀ ⦃t : Tate (Fin d)⦄ ⦃b : B⦄, t ≠ 0 → g t * b = 0 → b = 0 := by
    intro t b ht hmul
    have hgt : g t ≠ 0 := (map_ne_zero_iff g hg_inj).mpr ht
    exact (mul_eq_zero.mp hmul).resolve_left hgt
  obtain ⟨C, hC, hbound⟩ := g.exists_pos_norm_le_mul_smoothingFun_of_isWeaklyStable hg_cont hg_fin
    hg_tf (MvPowerSeries.norm_algebraMap_gaussFractionField (Fin d) K (fun _ ↦ 1))
    (MvPowerSeries.isWeaklyStable_gaussFractionField (Fin d) K (fun _ ↦ 1))
  refine ⟨C, hC, fun b ↦ ?_⟩
  rw [hB.supSeminorm_eq_smoothingFun]
  exact (hbound b).2

/-- Ultrametric case of [BGR, §6.2.4, Theorem 1]: used internally to establish completeness of
`SupNormModel` on reduced affinoids via `residueNormedCommRing`. -/
private theorem exists_norm_le_mul_supSeminorm_of_isUltrametricDist {A : Type*} [NormedCommRing A]
    [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A] [IsReduced A]
    (hA : IsAffinoidAlgebra K A) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : A, ‖f‖ ≤ C * supSeminorm K f := by
  rcases subsingleton_or_nontrivial A with _ | _
  · refine ⟨1, zero_lt_one, fun f ↦ ?_⟩
    simp [Subsingleton.elim f 0]
  have : IsNoetherianRing A := hA.isNoetherianRing
  have : Finite (minimalPrimes A) := (minimalPrimes.finite_of_isNoetherianRing A).to_subtype
  let _ : Fintype (minimalPrimes A) := Fintype.ofFinite (minimalPrimes A)
  have : Nonempty (minimalPrimes A) := Ideal.nonempty_minimalPrimes bot_ne_top
  -- Each minimal prime `𝔭` is closed, so `A ⧸ 𝔭` is a completely normed affinoid domain.
  have hclosed (𝔭 : minimalPrimes A) : IsClosed (𝔭.val : Set A) := hA.isClosed_ideal 𝔭.val
  have hprime (𝔭 : minimalPrimes A) : 𝔭.val.IsPrime := 𝔭.property.1.1
  have hdom_bound (𝔭 : minimalPrimes A) :
      ∃ C : ℝ, 0 < C ∧ ∀ q : A ⧸ 𝔭.val, ‖q‖ ≤ C * supSeminorm K q := by
    have := hclosed 𝔭
    have := hprime 𝔭
    exact exists_norm_le_mul_supSeminorm_of_isDomain (hA.quotient 𝔭.val)
  choose C𝔭 hC𝔭_pos hC𝔭 using hdom_bound
  -- Glue across the finitely many irreducible components via the strict injective diagonal map.
  let δ : A →ₗ[A] ∀ 𝔭 : minimalPrimes A, A ⧸ 𝔭.val :=
    LinearMap.pi fun 𝔭 ↦ (Ideal.Quotient.mkₐ A 𝔭.val).toLinearMap
  have hδ_inj : Function.Injective δ := by
    intro x y hxy
    refine Ideal.injective_pi_quotient_mk_minimalPrimes A ?_
    ext 𝔭
    have h𝔭 := congrFun hxy 𝔭
    simpa only [RingHom.pi_apply, δ, LinearMap.pi_apply, AlgHom.toLinearMap_apply,
      Ideal.Quotient.mkₐ_eq_mk] using h𝔭
  have : Huber.IsTateRing A := Huber.IsTateRing.of_normedAlgebra K A
  have hδ_strict : Topology.IsStrictMap δ := δ.isStrictMap_of_module_finite
  obtain ⟨D, hD, hδ_bound⟩ :=
    (δ.restrictScalars K).exists_pos_norm_le_mul_norm_of_isStrictMap_of_injective hδ_strict hδ_inj
  let M : ℝ := Finset.univ.sup' Finset.univ_nonempty C𝔭
  have hM_pos : 0 < M :=
    let ⟨𝔭₀⟩ := ‹Nonempty (minimalPrimes A)›
    (hC𝔭_pos 𝔭₀).trans_le (Finset.le_sup' C𝔭 (Finset.mem_univ 𝔭₀))
  refine ⟨D * M, mul_pos hD hM_pos, fun f ↦ ?_⟩
  have hδ_le : ‖δ f‖ ≤ M * supSeminorm K f := by
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hM_pos.le (supSeminorm_nonneg f))).mpr fun 𝔭 ↦ ?_
    have := hclosed 𝔭
    calc
      ‖δ f 𝔭‖ = ‖Ideal.Quotient.mk 𝔭.val f‖ := by
        rw [LinearMap.pi_apply, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]
      _ ≤ C𝔭 𝔭 * supSeminorm K (Ideal.Quotient.mk 𝔭.val f) := hC𝔭 𝔭 _
      _ ≤ M * supSeminorm K f :=
        mul_le_mul (Finset.le_sup' C𝔭 (Finset.mem_univ 𝔭))
          (hA.supSeminorm_map_le (hA.quotient 𝔭.val) (Ideal.Quotient.mkₐ K 𝔭.val) f)
          (supSeminorm_nonneg _) hM_pos.le
  calc
    ‖f‖ ≤ D * ‖δ f‖ := hδ_bound f
    _ ≤ D * (M * supSeminorm K f) := mul_le_mul_of_nonneg_left hδ_le hD.le
    _ = (D * M) * supSeminorm K f := (mul_assoc D M _).symm

end BanachFunctionAlgebra

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

/-- `toSupNorm` sends `a : A` to an element of norm `supSeminorm K a`. -/
theorem norm_toSupNorm (a : A) : ‖(toSupNorm a : hA.SupNormModel)‖ = supSeminorm K a := (rfl)

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

/-- `toSupNorm : A → hA.SupNormModel` is `1`-Lipschitz for any complete algebra norm on `A`. -/
theorem lipschitzWith_toSupNorm {A : Type*} [NormedCommRing A] [NormedAlgebra K A]
    {hA : IsAffinoidAlgebra K A} [CompleteSpace A] :
    LipschitzWith 1 (toSupNorm : A → hA.SupNormModel) :=
  LipschitzWith.of_dist_le_mul fun x y ↦ by
    rw [NNReal.coe_one, one_mul, dist_def, ofSupNorm_toSupNorm, dist_eq_norm]
    exact supSeminorm_le_norm (x - y)

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
  let q : hA.SupNormModel → (hA.quotient (nilradical A)).SupNormModel :=
    fun x ↦ toSupNorm (Ideal.Quotient.mk (nilradical A) x.ofSupNorm)
  have hq_iso : Isometry q := Isometry.of_dist_eq fun x y ↦ by
    simp only [q, dist_def, ← map_sub, supSeminorm_mk_nilradical]
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

/-- `supNormContinuousAlgEquiv` is `1`-Lipschitz. -/
theorem lipschitzWith_supNormContinuousAlgEquiv {A : Type*} [NormedCommRing A]
    [NormedAlgebra K A] [CompleteSpace A] [IsReduced A] (hA : IsAffinoidAlgebra K A) :
    LipschitzWith 1 hA.supNormContinuousAlgEquiv :=
  SupNormModel.lipschitzWith_toSupNorm

/-- The inverse of `supNormContinuousAlgEquiv` is Lipschitz. -/
theorem exists_pos_lipschitzWith_supNormContinuousAlgEquiv_symm {A : Type*} [NormedCommRing A]
    [NormedAlgebra K A] [CompleteSpace A] [IsReduced A] (hA : IsAffinoidAlgebra K A) :
    ∃ C : NNReal, 0 < C ∧ LipschitzWith C hA.supNormContinuousAlgEquiv.symm :=
  SupNormModel.exists_pos_lipschitzWith_ofSupNorm (hA := hA)

end SupNormBanach

section AutomaticContinuityFromBanach

variable {B A : Type*} [NormedRing B] [NormedAlgebra K B] [CompleteSpace B]
  [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A] [IsReduced A]

/-- Quantitative bound for `K`-algebra homomorphisms from an arbitrary Banach `K`-algebra `B` into a
completely normed reduced affinoid `K`-algebra `A` over a complete nontrivially normed ultrametric
field `K`: there exists `C > 0` (independent of `φ`) such that
`‖φ b‖ ≤ C * gelfandRadius b ≤ C * ‖b‖` for every `φ : B →ₐ[K] A` and `b : B`. -/
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

/-- **Automatic continuity from arbitrary Banach algebras into reduced affinoid algebras**
([BGR, §3.8.3 / §6.2.4]). Over a complete nontrivially normed ultrametric field `K`, every
`K`-algebra homomorphism from a Banach `K`-algebra `B` (not assumed commutative, ultrametric,
Noetherian, or unital-norm-normalized) into a completely normed reduced affinoid `K`-algebra `A` is
continuous. -/
theorem continuous_algHom_of_isReduced (hA : IsAffinoidAlgebra K A) (φ : B →ₐ[K] A) :
    Continuous φ := by
  obtain ⟨C, _, hC⟩ := hA.exists_pos_norm_apply_le_mul_gelfandRadius_of_isReduced (B := B)
  exact (φ.toLinearMap.mkContinuous C fun b ↦ (hC φ b).2).continuous

end AutomaticContinuityFromBanach

end IsAffinoidAlgebra

end TauCeti
