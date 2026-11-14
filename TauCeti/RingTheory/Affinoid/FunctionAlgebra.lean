/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.FunctionAlgebra
public import TauCeti.RingTheory.Affinoid.QuotientNorm
public import TauCeti.RingTheory.Affinoid.SpectralRadius

import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Topology.UniformSpace.Equiv
import TauCeti.Analysis.Normed.Operator.Embedding
import TauCeti.RingTheory.Affinoid.NoetherNormalization
import TauCeti.RingTheory.Huber.Normed
import TauCeti.RingTheory.Huber.StrictMorphism
import TauCeti.RingTheory.Ideal.MinimalPrime.Basic
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.FractionField
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UniqueFactorization
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.WeaklyStable

/-!
# Reduced affinoid algebras are Banach function algebras

Let `K` be a complete nontrivially normed ultrametric field of arbitrary characteristic, and let `A`
be an affinoid `K`-algebra. When `A` is reduced, its supremum seminorm `supSeminorm K` is a norm on
`A` (`TauCeti.IsAffinoidAlgebra.isReduced_iff_supSeminorm_eq_zero`). This file proves **Bosch,
Güntzer, Remmert, §6.2.4, Theorem 1**: on every reduced affinoid `K`-algebra `A` carrying any
complete ultrametric `K`-algebra norm, the supremum norm is equivalent to the Banach norm:

`∃ C > 0, ∀ f : A, supSeminorm K f ≤ ‖f‖ ∧ ‖f‖ ≤ C * supSeminorm K f`.

In particular:
* Every completely normed reduced affinoid algebra is uniform
  (`TauCeti.IsAffinoidAlgebra.isUniform`).
* Equipping a reduced affinoid algebra `A` (without any prior norm) with `supSeminorm K` produces a
  complete uniform ultrametric Banach `K`-algebra (`TauCeti.IsAffinoidAlgebra.SupNormModel`), and
  for any complete ultrametric `K`-algebra norm on `A` the identity is a topological `K`-algebra
  isomorphism (`TauCeti.IsAffinoidAlgebra.supNormContinuousAlgEquiv`).
* Every `K`-algebra homomorphism `φ : B →ₐ[K] A` from an arbitrary Banach `K`-algebra `B` (not
  assumed commutative, ultrametric, Noetherian, or unital-norm-normalized) into a completely normed
  affinoid `K`-algebra `A` maps power-bounded elements to power-bounded elements
  (`TauCeti.IsAffinoidAlgebra.isPowerBounded_algHom`), and when `A` is reduced `φ` is automatically
  continuous (`TauCeti.IsAffinoidAlgebra.continuous_algHom_of_isReduced`).

## Proof outline

1. **Finite torsion-free extensions of Tate algebras.** If `A` is finite and torsion-free over a
   Tate algebra `T_d = K⟨X₁, …, X_d⟩`, equipping `A` with its canonical residue norm identifies
   `supSeminorm K` with `gelfandRadius`, hence with `spectralValue (minpoly T_d f)`
   (`TauCeti.IsAffinoidAlgebra.supSeminorm_eq_spectralValue_minpoly`) and, when `A` is reduced,
   with `reducedSpectralAlgNorm` on `Frac(T_d) ⊗[T_d] A`
   (`TauCeti.IsAffinoidAlgebra.supSeminorm_eq_reducedSpectralAlgNorm`).
2. **Affinoid domains.** An affinoid domain `B` has a finite injective Noether normalization
   `g : T_d →ₐ[K] B`. Because `B` is a domain, `B` is torsion-free over `T_d`; because `T_d` is a
   unique factorization domain (`TauCeti.MvPowerSeries.uniqueFactorizationMonoid`) and its
   Gauss-normed fraction field is weakly stable in arbitrary characteristic
   (`TauCeti.MvPowerSeries.isWeaklyStable_gaussFractionField`), [BGR, §3.8.3, Theorem 7]
   (`AlgHom.exists_pos_norm_le_mul_smoothingFun_of_isWeaklyStable`) bounds `‖b‖` by
   `C * supSeminorm K b`.
3. **General reduced affinoid algebras.** A general reduced affinoid algebra `A` need not be
   equidimensional, so it need not be torsion-free over a single Tate algebra. Instead, `A` has
   finitely many minimal primes `𝔭`, each quotient `A ⧸ 𝔭` is an affinoid domain with closed kernel
   `𝔭`, and the diagonal `A`-linear map `δ : A →ₗ[A] ∏ 𝔭, A ⧸ 𝔭` is injective
   (`Ideal.injective_pi_quotient_mk_minimalPrimes`) and strict
   (`LinearMap.isStrictMap_of_module_finite`). Combining `‖f‖ ≤ D * ‖δ f‖` with step 2 on each
   component `A ⧸ 𝔭` yields `‖f‖ ≤ C * supSeminorm K f`.

## Main definitions and results

* `TauCeti.IsAffinoidAlgebra.supSeminorm_eq_spectralValue_minpoly` and
  `TauCeti.IsAffinoidAlgebra.supSeminorm_eq_reducedSpectralAlgNorm`: minimal-polynomial and
  base-change formulas for `supSeminorm K` along a finite torsion-free Tate normalization.
* `TauCeti.IsAffinoidAlgebra.banachFunctionAlgebra`: [BGR, §6.2.4, Theorem 1].
* `TauCeti.IsAffinoidAlgebra.isUniform`: reduced completely normed affinoid algebras are uniform.
* `TauCeti.IsAffinoidAlgebra.SupNormModel` and
  `TauCeti.IsAffinoidAlgebra.supNormContinuousAlgEquiv`: the canonical complete supremum-normed
  Banach algebra model of a reduced affinoid algebra.
* `AlgHom.supSeminorm_apply_le_gelfandRadius`,
  `TauCeti.IsAffinoidAlgebra.isPowerBounded_algHom`, and
  `TauCeti.IsAffinoidAlgebra.continuous_algHom_of_isReduced`: automatic continuity and
  power-boundedness preservation from arbitrary Banach `K`-algebras.

## References

* [S. Bosch, U. Güntzer, R. Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert],
  §§3.8.3, 6.2.1, 6.2.2, and 6.2.4 (Theorem 1).
-/

public section

open scoped TensorProduct

section BanachSource

variable {K B A : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedRing B] [NormedAlgebra K B] [CompleteSpace B]
  [CommRing A] [Algebra K A]

/-- Any `K`-algebra homomorphism from a Banach `K`-algebra `B` into a commutative `K`-algebra `A`
is bounded at every classical point `x : MaximalSpectrum A` by the Gelfand radius on `B`. -/
theorem AlgHom.pointNorm_apply_le_gelfandRadius (φ : B →ₐ[K] A) (x : MaximalSpectrum A) (b : B) :
    TauCeti.pointNorm K x (φ b) ≤ gelfandRadius b := by
  let := Ideal.Quotient.field x.asIdeal
  rw [TauCeti.pointNorm_eq_spectralNorm (L := A ⧸ x.asIdeal)
    (ψ := Ideal.Quotient.mkₐ K x.asIdeal) (Ideal.Quotient.mkₐ_ker K x.asIdeal).ge]
  exact ((Ideal.Quotient.mkₐ K x.asIdeal).comp φ).spectralNorm_apply_le_gelfandRadius b

/-- Any `K`-algebra homomorphism from a Banach `K`-algebra `B` into a commutative `K`-algebra `A`
maps every `b : B` to an element of supremum seminorm at most `gelfandRadius b`. -/
theorem AlgHom.supSeminorm_apply_le_gelfandRadius (φ : B →ₐ[K] A) (b : B) :
    TauCeti.supSeminorm K (φ b) ≤ gelfandRadius b :=
  TauCeti.supSeminorm_le (gelfandRadius_nonneg b) fun x ↦ φ.pointNorm_apply_le_gelfandRadius x b

/-- Any `K`-algebra homomorphism from a Banach `K`-algebra `B` into a commutative `K`-algebra `A`
is contractive from the norm on `B` to `TauCeti.supSeminorm K` on `A`. -/
theorem AlgHom.supSeminorm_apply_le_norm (φ : B →ₐ[K] A) (b : B) :
    TauCeti.supSeminorm K (φ b) ≤ ‖b‖ :=
  (φ.supSeminorm_apply_le_gelfandRadius b).trans (gelfandRadius_le_norm b)

end BanachSource

namespace TauCeti.IsAffinoidAlgebra

section SupNormModel

/-- Type wrapper equipping an affinoid algebra `A` (with no prior norm) with its canonical supremum
seminorm `supSeminorm K`. When `A` is reduced, `hA.SupNormModel` is a complete uniform ultrametric
Banach `K`-algebra. -/
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

instance : CommRing hA.SupNormModel where
  zero := ⟨0⟩
  one := ⟨1⟩
  add x y := ⟨x.1 + y.1⟩
  neg x := ⟨-x.1⟩
  sub x y := ⟨x.1 - y.1⟩
  mul x y := ⟨x.1 * y.1⟩
  nsmul n x := ⟨n • x.1⟩
  zsmul n x := ⟨n • x.1⟩
  npow n x := ⟨x.1 ^ n⟩
  natCast n := ⟨n⟩
  intCast n := ⟨n⟩
  add_assoc _ _ _ := ext (add_assoc _ _ _)
  zero_add _ := ext (zero_add _)
  add_zero _ := ext (add_zero _)
  nsmul_zero _ := ext (zero_nsmul _)
  nsmul_succ _ _ := ext (succ_nsmul _ _)
  sub_eq_add_neg _ _ := ext (sub_eq_add_neg _ _)
  zsmul_zero' _ := ext (zero_zsmul _)
  zsmul_succ' _ _ := ext (SubNegMonoid.zsmul_succ' _ _)
  zsmul_neg' _ _ := ext (SubNegMonoid.zsmul_neg' _ _)
  neg_add_cancel _ := ext (neg_add_cancel _)
  add_comm _ _ := ext (add_comm _ _)
  left_distrib _ _ _ := ext (left_distrib _ _ _)
  right_distrib _ _ _ := ext (right_distrib _ _ _)
  zero_mul _ := ext (zero_mul _)
  mul_zero _ := ext (mul_zero _)
  mul_assoc _ _ _ := ext (mul_assoc _ _ _)
  one_mul _ := ext (one_mul _)
  mul_one _ := ext (mul_one _)
  npow_zero _ := ext (pow_zero _)
  npow_succ _ _ := ext (pow_succ _ _)
  natCast_zero := ext Nat.cast_zero
  natCast_succ _ := ext (Nat.cast_succ _)
  intCast_ofNat _ := ext (Int.cast_natCast _)
  intCast_negSucc _ := ext (Int.cast_negSucc _)
  mul_comm _ _ := ext (mul_comm _ _)

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

instance : Algebra K hA.SupNormModel where
  algebraMap :=
    { toFun := fun c ↦ ⟨algebraMap K A c⟩
      map_one' := ext (map_one _)
      map_mul' := fun _ _ ↦ ext (map_mul _ _ _)
      map_zero' := ext (map_zero _)
      map_add' := fun _ _ ↦ ext (map_add _ _ _) }
  commutes' c x := ext (Algebra.commutes c x.1)
  smul := fun c x ↦ ⟨c • x.1⟩
  smul_def' c x := ext (Algebra.smul_def c x.1)

@[simp] theorem ofSupNorm_algebraMap (c : K) :
    (algebraMap K hA.SupNormModel c).ofSupNorm = algebraMap K A c := (rfl)
@[simp] theorem ofSupNorm_smul (c : K) (x : hA.SupNormModel) :
    (c • x).ofSupNorm = c • x.ofSupNorm := (rfl)

/-- Canonical `K`-algebra isomorphism `A ≃ₐ[K] hA.SupNormModel`. -/
def algEquiv (hA : IsAffinoidAlgebra K A) : A ≃ₐ[K] hA.SupNormModel where
  toFun := toSupNorm
  invFun := ofSupNorm
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem algEquiv_apply (a : A) : algEquiv hA a = toSupNorm a := (rfl)
@[simp]
theorem algEquiv_symm_apply (x : hA.SupNormModel) : (algEquiv hA).symm x = x.ofSupNorm := (rfl)

instance [Subsingleton A] : Subsingleton hA.SupNormModel := (algEquiv hA).symm.toEquiv.subsingleton
instance [Nontrivial A] : Nontrivial hA.SupNormModel := (algEquiv hA).symm.toEquiv.nontrivial
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

section TorsionFreeNormalization

/-- **Bosch–Güntzer–Remmert, §6.2.2, Proposition 1 / §6.2.1, Proposition 4(iii).**
Let `A` be an affinoid `K`-algebra (with no choice of norm or reducedness assumption) that is finite
and torsion-free over a finite-variable Tate algebra `T = K⟨X₁, …, X_d⟩`. Then for every `f : A`,
`supSeminorm K f = spectralValue (minpoly T f)`. -/
theorem supSeminorm_eq_spectralValue_minpoly {σ : Type*} [Finite σ]
    {A : Type*} [CommRing A] [Algebra K A] [Algebra (Tate σ) A] [IsScalarTower K (Tate σ) A]
    [Module.Finite (Tate σ) A] [Module.IsTorsionFree (Tate σ) A]
    (hA : IsAffinoidAlgebra K A) (f : A) :
    supSeminorm K f = spectralValue (minpoly (Tate σ) f) := by
  let _ := Fintype.ofFinite σ
  have : Countable σ := Finite.to_countable
  have : IsNoetherianRing (Tate σ) := (isAffinoidAlgebra_tate (K := K) (σ := σ)).isNoetherianRing
  let : NormedCommRing A := hA.residueNormedCommRing
  let : NormedAlgebra K A := hA.residueNormedAlgebra
  have : IsUltrametricDist A := hA.isUltrametricDist_residueNormedCommRing
  have : CompleteSpace A := hA.completeSpace_residueNormedCommRing
  have hcont : Continuous (algebraMap (Tate σ) A) :=
    hA.continuous_algHom (IsScalarTower.toAlgHom K (Tate σ) A)
  rw [hA.supSeminorm_eq_smoothingFun, smoothingFun_normRingSeminorm_eq_gelfandRadius]
  exact gelfandRadius_eq_spectralValue_minpoly K
    (F := MvPowerSeries.GaussFractionField σ K (fun _ ↦ 1))
    (MvPowerSeries.norm_algebraMap_gaussFractionField σ K (fun _ ↦ 1)) hcont f

/-- When `A` is a reduced affinoid `K`-algebra that is finite and torsion-free over a
finite-variable Tate algebra `T = K⟨X₁, …, X_d⟩`, and `F` is any fraction field of `T` extending the
Gauss norm isometrically (for instance `GaussFractionField σ K 1`), the supremum norm on `A` agrees
with `reducedSpectralAlgNorm` on `F ⊗[T] A`. -/
theorem supSeminorm_eq_reducedSpectralAlgNorm {σ : Type*} [Finite σ]
    {F : Type*} [NormedField F] [IsUltrametricDist F] [Algebra (Tate σ) F]
    [IsFractionRing (Tate σ) F] (hF : ∀ t : Tate σ, ‖algebraMap (Tate σ) F t‖ = ‖t‖)
    {A : Type*} [CommRing A] [IsReduced A] [Algebra K A] [Algebra (Tate σ) A]
    [IsScalarTower K (Tate σ) A] [Module.Finite (Tate σ) A] [Module.IsTorsionFree (Tate σ) A]
    (hA : IsAffinoidAlgebra K A) (f : A) :
    supSeminorm K f = reducedSpectralAlgNorm F (F ⊗[Tate σ] A) (1 ⊗ₜ[Tate σ] f) := by
  let _ := Fintype.ofFinite σ
  have : Countable σ := Finite.to_countable
  have : IsNoetherianRing (Tate σ) := (isAffinoidAlgebra_tate (K := K) (σ := σ)).isNoetherianRing
  let : NormedCommRing A := hA.residueNormedCommRing
  let : NormedAlgebra K A := hA.residueNormedAlgebra
  have : IsUltrametricDist A := hA.isUltrametricDist_residueNormedCommRing
  have : CompleteSpace A := hA.completeSpace_residueNormedCommRing
  have hcont : Continuous (algebraMap (Tate σ) A) :=
    hA.continuous_algHom (IsScalarTower.toAlgHom K (Tate σ) A)
  rw [hA.supSeminorm_eq_smoothingFun]
  exact smoothingFun_eq_reducedSpectralAlgNorm K hF hcont f

end TorsionFreeNormalization

section BanachFunctionAlgebra

/-- Domain case of [BGR, §6.2.4, Theorem 1]: an affinoid domain embeds finitely and torsion-freely
over a Tate algebra via Noether normalization, and the fraction field of that Tate algebra is
weakly stable in arbitrary characteristic. -/
private theorem banachFunctionAlgebra_of_isDomain {B : Type*} [NormedCommRing B] [IsDomain B]
    [NormedAlgebra K B] [IsUltrametricDist B] [CompleteSpace B] (hB : IsAffinoidAlgebra K B) :
    ∃ C : ℝ, 0 < C ∧ ∀ b : B, supSeminorm K b ≤ ‖b‖ ∧ ‖b‖ ≤ C * supSeminorm K b := by
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
  exact hbound b

/-- **Bosch–Güntzer–Remmert, §6.2.4, Theorem 1 (Banach function algebra theorem).**
Let `A` be a reduced affinoid algebra over a complete nontrivially normed ultrametric field `K` (of
arbitrary characteristic), equipped with any complete ultrametric `K`-algebra norm. Then the Banach
norm on `A` is equivalent to the supremum norm `supSeminorm K`: there exists `C > 0` such that
`supSeminorm K f ≤ ‖f‖` and `‖f‖ ≤ C * supSeminorm K f` for every `f : A`. -/
theorem banachFunctionAlgebra {A : Type*} [NormedCommRing A] [NormedAlgebra K A]
    [IsUltrametricDist A] [CompleteSpace A] [IsReduced A] (hA : IsAffinoidAlgebra K A) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : A, supSeminorm K f ≤ ‖f‖ ∧ ‖f‖ ≤ C * supSeminorm K f := by
  rcases subsingleton_or_nontrivial A with _ | _
  · refine ⟨1, zero_lt_one, fun f ↦ ?_⟩
    simp [Subsingleton.elim f 0]
  have : IsNoetherianRing A := hA.isNoetherianRing
  have : Finite (minimalPrimes A) := (minimalPrimes.finite_of_isNoetherianRing A).to_subtype
  let _ : Fintype (minimalPrimes A) := Fintype.ofFinite (minimalPrimes A)
  have : Nonempty (minimalPrimes A) := Ideal.nonempty_minimalPrimes bot_ne_top
  -- Each minimal prime `𝔭` is closed, so `A ⧸ 𝔭` is a completely normed affinoid domain.
  have hclosed (𝔭 : minimalPrimes A) : IsClosed (𝔭.1 : Set A) := hA.isClosed_ideal 𝔭.1
  have hprime (𝔭 : minimalPrimes A) : 𝔭.1.IsPrime := 𝔭.2.1.1
  have hdom_bound (𝔭 : minimalPrimes A) :
      ∃ C : ℝ, 0 < C ∧ ∀ q : A ⧸ 𝔭.1, ‖q‖ ≤ C * supSeminorm K q := by
    have := hclosed 𝔭
    have := hprime 𝔭
    obtain ⟨C, hC, h⟩ := banachFunctionAlgebra_of_isDomain (hA.quotient 𝔭.1)
    exact ⟨C, hC, fun q ↦ (h q).2⟩
  choose C𝔭 hC𝔭_pos hC𝔭 using hdom_bound
  -- Glue across the finitely many irreducible components via the strict injective diagonal map.
  let δ : A →ₗ[A] ∀ 𝔭 : minimalPrimes A, A ⧸ 𝔭.1 :=
    LinearMap.pi fun 𝔭 ↦ (Ideal.Quotient.mkₐ A 𝔭.1).toLinearMap
  have hδ_inj : Function.Injective δ := by
    intro x y hxy
    refine Ideal.injective_pi_quotient_mk_minimalPrimes A ?_
    ext 𝔭
    exact congrFun hxy 𝔭
  have : Huber.IsTateRing A := Huber.IsTateRing.of_normedAlgebra K A
  have hδ_strict : Topology.IsStrictMap δ := δ.isStrictMap_of_module_finite
  obtain ⟨D, hD, hδ_bound⟩ :=
    (δ.restrictScalars K).exists_pos_norm_le_mul_norm_of_isStrictMap hδ_strict hδ_inj
  let M : ℝ := Finset.univ.sup' Finset.univ_nonempty C𝔭
  have hM_pos : 0 < M :=
    let ⟨𝔭₀⟩ := ‹Nonempty (minimalPrimes A)›
    (hC𝔭_pos 𝔭₀).trans_le (Finset.le_sup' C𝔭 (Finset.mem_univ 𝔭₀))
  refine ⟨D * M, mul_pos hD hM_pos, fun f ↦ ⟨hA.supSeminorm_le_norm f, ?_⟩⟩
  have hδ_le : ‖δ f‖ ≤ M * supSeminorm K f := by
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg hM_pos.le (supSeminorm_nonneg f))).mpr fun 𝔭 ↦ ?_
    have := hclosed 𝔭
    calc
      ‖δ f 𝔭‖ = ‖Ideal.Quotient.mk 𝔭.1 f‖ := rfl
      _ ≤ C𝔭 𝔭 * supSeminorm K (Ideal.Quotient.mk 𝔭.1 f) := hC𝔭 𝔭 _
      _ ≤ M * supSeminorm K f :=
        mul_le_mul (Finset.le_sup' C𝔭 (Finset.mem_univ 𝔭))
          (hA.supSeminorm_map_le (hA.quotient 𝔭.1) (Ideal.Quotient.mkₐ K 𝔭.1) f)
          (supSeminorm_nonneg _) hM_pos.le
  calc
    ‖f‖ ≤ D * ‖δ f‖ := hδ_bound f
    _ ≤ D * (M * supSeminorm K f) := mul_le_mul_of_nonneg_left hδ_le hD.le
    _ = (D * M) * supSeminorm K f := (mul_assoc D M _).symm

/-- **Uniformity of reduced affinoid algebras.** Every reduced affinoid `K`-algebra carrying a
complete ultrametric `K`-algebra norm has bounded power-bounded subring (`TauCeti.Huber.IsUniform`).
-/
theorem isUniform {A : Type*} [NormedCommRing A] [NormedAlgebra K A]
    [IsUltrametricDist A] [CompleteSpace A] [IsReduced A] (hA : IsAffinoidAlgebra K A) :
    Huber.IsUniform A := by
  obtain ⟨C, _, hC⟩ := hA.banachFunctionAlgebra
  refine Huber.IsUniform.of_norm_le_mul_smoothingFun K ⟨C, fun f ↦ ?_⟩
  rw [← hA.supSeminorm_eq_smoothingFun]
  exact (hC f).2

end BanachFunctionAlgebra

section SupNormBanach

namespace SupNormModel

variable {A : Type*} [CommRing A] [Algebra K A] {hA : IsAffinoidAlgebra K A}

/-- The `RingSeminorm` on `hA.SupNormModel` given by `supSeminorm K`. -/
noncomputable def ringSeminorm (hA : IsAffinoidAlgebra K A) : RingSeminorm hA.SupNormModel where
  toFun x := supSeminorm K x.ofSupNorm
  map_zero' := supSeminorm_zero
  add_le' x y := (hA.supSeminorm_add_le x.1 y.1).trans
    (max_le_add_of_nonneg (supSeminorm_nonneg x.1) (supSeminorm_nonneg y.1))
  neg' x := supSeminorm_neg x.1
  mul_le' x y := hA.supSeminorm_mul_le x.1 y.1

noncomputable instance : SeminormedCommRing hA.SupNormModel where
  __ := (inferInstance : CommRing hA.SupNormModel)
  __ := (ringSeminorm hA).toSeminormedRing

/-- The norm on `hA.SupNormModel` is `supSeminorm K` of the underlying element. -/
@[simp] theorem norm_def (x : hA.SupNormModel) : ‖x‖ = supSeminorm K x.ofSupNorm := (rfl)

/-- `toSupNorm` sends `a : A` to an element of norm `supSeminorm K a`. -/
theorem norm_toSupNorm (a : A) : ‖(toSupNorm a : hA.SupNormModel)‖ = supSeminorm K a := (rfl)

noncomputable instance : NormedAlgebra K hA.SupNormModel where
  norm_smul_le c x := by
    rw [norm_def, norm_def, ofSupNorm_smul]
    exact (supSeminorm_smul c x.1).le

instance : IsUltrametricDist hA.SupNormModel :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y ↦
    hA.supSeminorm_add_le x.1 y.1

instance [Nontrivial A] : NormOneClass hA.SupNormModel where
  norm_one := supSeminorm_one

/-- The supremum norm on `hA.SupNormModel` is power-multiplicative. -/
theorem isPowMul_norm : IsPowMul (norm : hA.SupNormModel → ℝ) := fun x _n hn ↦
  supSeminorm_pow x.ofSupNorm (Nat.one_le_iff_ne_zero.mp hn)

noncomputable instance [IsReduced A] : NormedCommRing hA.SupNormModel :=
  { (inferInstance : SeminormedCommRing hA.SupNormModel) with
    eq_of_dist_eq_zero := fun {x y} hxy ↦ by
      rw [dist_eq_norm, norm_def, ofSupNorm_sub] at hxy
      exact ext (sub_eq_zero.mp (hA.isReduced_iff_supSeminorm_eq_zero.mp ‹_› _ hxy)) }

/-- **Completeness of the supremum norm on a reduced affinoid algebra**
([BGR, §6.2.4, Corollary 2]). Even when `A` carries no prior norm, equipping `A` locally with its
canonical residue norm and applying `banachFunctionAlgebra` shows that `hA.SupNormModel` is a
complete Banach `K`-algebra. -/
instance [IsReduced A] : CompleteSpace hA.SupNormModel := by
  let : NormedCommRing A := hA.residueNormedCommRing
  let : NormedAlgebra K A := hA.residueNormedAlgebra
  have : IsUltrametricDist A := hA.isUltrametricDist_residueNormedCommRing
  have : CompleteSpace A := hA.completeSpace_residueNormedCommRing
  obtain ⟨C, hC, hbound⟩ := hA.banachFunctionAlgebra
  have hlip₁ : LipschitzWith 1 (toSupNorm : A → hA.SupNormModel) :=
    LipschitzWith.of_dist_le_mul fun x y ↦ by
      simpa only [NNReal.coe_one, one_mul, dist_eq_norm_neg_add, norm_def, ofSupNorm_add,
        ofSupNorm_neg, ofSupNorm_toSupNorm] using (hbound (-x + y)).1
  have hlip₂ : LipschitzWith (Real.toNNReal C) (ofSupNorm : hA.SupNormModel → A) :=
    LipschitzWith.of_dist_le_mul fun x y ↦ by
      simpa only [Real.coe_toNNReal C hC.le, dist_eq_norm_neg_add, norm_def, ofSupNorm_add,
        ofSupNorm_neg] using (hbound (-x.ofSupNorm + y.ofSupNorm)).2
  let e : A ≃ᵤ hA.SupNormModel :=
    { toEquiv := (algEquiv hA).toEquiv
      uniformContinuous_toFun := hlip₁.uniformContinuous
      uniformContinuous_invFun := hlip₂.uniformContinuous }
  exact e.completeSpace_iff.mp inferInstance

instance [IsReduced A] : Huber.IsUniform hA.SupNormModel :=
  (isAffinoidAlgebra hA).isUniform

end SupNormModel

/-- For any reduced affinoid `K`-algebra `A` carrying a complete ultrametric `K`-algebra norm, the
identity map to `hA.SupNormModel` is a topological `K`-algebra isomorphism: `supSeminorm K` defines
the canonical Banach topology on `A`. -/
noncomputable def supNormContinuousAlgEquiv {A : Type*} [NormedCommRing A] [NormedAlgebra K A]
    [IsUltrametricDist A] [CompleteSpace A] [IsReduced A] (hA : IsAffinoidAlgebra K A) :
    A ≃A[K] hA.SupNormModel :=
  (SupNormModel.isAffinoidAlgebra hA).toContinuousAlgEquiv (SupNormModel.algEquiv hA)

/-- `supNormContinuousAlgEquiv` has `SupNormModel.toSupNorm` as its underlying function. -/
@[simp]
theorem coe_supNormContinuousAlgEquiv {A : Type*} [NormedCommRing A] [NormedAlgebra K A]
    [IsUltrametricDist A] [CompleteSpace A] [IsReduced A] (hA : IsAffinoidAlgebra K A) :
    ⇑hA.supNormContinuousAlgEquiv = SupNormModel.toSupNorm := by
  ext a
  simp [supNormContinuousAlgEquiv]

/-- The underlying `K`-algebra isomorphism of `supNormContinuousAlgEquiv` is
`SupNormModel.algEquiv`. -/
@[simp]
theorem toAlgEquiv_supNormContinuousAlgEquiv {A : Type*} [NormedCommRing A] [NormedAlgebra K A]
    [IsUltrametricDist A] [CompleteSpace A] [IsReduced A] (hA : IsAffinoidAlgebra K A) :
    hA.supNormContinuousAlgEquiv.toAlgEquiv = SupNormModel.algEquiv hA := by
  simp [supNormContinuousAlgEquiv]

/-- The inverse of `supNormContinuousAlgEquiv` extracts `SupNormModel.ofSupNorm`. -/
@[simp]
theorem symm_apply_supNormContinuousAlgEquiv {A : Type*} [NormedCommRing A] [NormedAlgebra K A]
    [IsUltrametricDist A] [CompleteSpace A] [IsReduced A] (hA : IsAffinoidAlgebra K A)
    (x : hA.SupNormModel) :
    hA.supNormContinuousAlgEquiv.symm x = x.ofSupNorm := by
  change hA.supNormContinuousAlgEquiv.toAlgEquiv.symm x = x.ofSupNorm
  simp

end SupNormBanach

section AutomaticContinuityFromBanach

variable {B A : Type*} [NormedRing B] [NormedAlgebra K B] [CompleteSpace B]
  [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]

/-- Every `K`-algebra homomorphism from an arbitrary Banach `K`-algebra `B` into a completely normed
affinoid `K`-algebra `A` (not necessarily reduced) maps power-bounded elements to power-bounded
elements. Unlike `TauCeti.IsAffinoidAlgebra.isPowerBounded_map`, `B` need not be commutative,
ultrametric, or Noetherian. -/
theorem isPowerBounded_algHom (hA : IsAffinoidAlgebra K A) (φ : B →ₐ[K] A) {b : B}
    (hb : Huber.IsPowerBounded b) : Huber.IsPowerBounded (φ b) :=
  hA.isPowerBounded_iff_supSeminorm_le_one.mpr <|
    (φ.supSeminorm_apply_le_gelfandRadius b).trans
      (Huber.gelfandRadius_le_one_of_isPowerBounded K hb)

variable [IsReduced A]

/-- Quantitative bound for `K`-algebra homomorphisms from an arbitrary Banach `K`-algebra `B` into a
completely normed reduced affinoid `K`-algebra `A`: there exists `C > 0` such that
`‖φ b‖ ≤ C * gelfandRadius b ≤ C * ‖b‖` for every `b : B`. -/
theorem exists_pos_norm_algHom_le_of_isReduced (hA : IsAffinoidAlgebra K A) (φ : B →ₐ[K] A) :
    ∃ C : ℝ, 0 < C ∧ ∀ b : B, ‖φ b‖ ≤ C * gelfandRadius b ∧ ‖φ b‖ ≤ C * ‖b‖ := by
  obtain ⟨C, hC, hbound⟩ := hA.banachFunctionAlgebra
  refine ⟨C, hC, fun b ↦ ?_⟩
  have h1 : ‖φ b‖ ≤ C * gelfandRadius b :=
    ((hbound (φ b)).2).trans (mul_le_mul_of_nonneg_left (φ.supSeminorm_apply_le_gelfandRadius b)
      hC.le)
  exact ⟨h1, h1.trans (mul_le_mul_of_nonneg_left (gelfandRadius_le_norm b) hC.le)⟩

/-- **Automatic continuity from arbitrary Banach algebras into reduced affinoid algebras**
([BGR, §3.8.3 / §6.2.4]). Every `K`-algebra homomorphism from a Banach `K`-algebra `B` (not assumed
commutative, ultrametric, Noetherian, or unital-norm-normalized) into a completely normed reduced
affinoid `K`-algebra `A` is continuous. -/
theorem continuous_algHom_of_isReduced (hA : IsAffinoidAlgebra K A) (φ : B →ₐ[K] A) :
    Continuous φ := by
  obtain ⟨C, _, hC⟩ := hA.exists_pos_norm_algHom_le_of_isReduced φ
  exact (φ.toLinearMap.mkContinuous C fun b ↦ (hC b).2).continuous

end AutomaticContinuityFromBanach

end TauCeti.IsAffinoidAlgebra
