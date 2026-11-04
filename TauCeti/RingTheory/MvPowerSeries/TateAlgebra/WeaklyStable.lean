/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Field.WeaklyStable
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.FractionField

import Mathlib.Algebra.CharP.Reduced
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import TauCeti.Analysis.Normed.Field.FrobeniusRoot
import TauCeti.Analysis.Normed.Module.Bases.CountableType
import TauCeti.Analysis.Normed.Module.Dual.Bounded
import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Basic
import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Basis
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.FieldTheory.PurelyInseparable.Embedding
import TauCeti.FieldTheory.PurelyInseparable.Exponent
import TauCeti.RingTheory.MvPowerSeries.Basic
import TauCeti.RingTheory.MvPowerSeries.Order
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Expand
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Map
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Basic

/-!
# Characteristic-free weak stability of Gauss-normed Tate fraction fields

Let `K` be a complete nontrivially normed ultrametric field of arbitrary characteristic, `σ` a
finite variable type, and `c : σ → ℝ` a positive polyradius. This file proves that the
Gauss-normed fraction field `GaussFractionField σ K c` of the restricted-series algebra
`K{X / c}` is weakly stable (`TauCeti.MvPowerSeries.isWeaklyStable_gaussFractionField`): on every
finite extension `L / GaussFractionField σ K c`, every linear functional is bounded by
`spectralNorm`.

With no variables (`[IsEmpty σ]`), `GaussFractionField σ K c` is isometrically `K`-isomorphic to
`K`, so its spectral norms and weak stability coincide with those of `K` even without completeness
or nontriviality of the norm on `K`.

## Proof outline

By `TauCeti.IsWeaklyStable.of_isPurelyInseparable`, it suffices to prove boundedness of linear
functionals on every finite purely inseparable extension `M` of `F := GaussFractionField σ K c`.
Let `p := ringExpChar K` and `q := p ^ e`, where `e` is the exponent of `M / F`.

1. Replace `K` by `K' := FrobeniusRoot K p e` (`K` equipped with the norm `‖·‖ ^ q⁻¹` and the
   `e`-fold Frobenius `K`-algebra map) and replace the polyradius `c` by `r i = c i ^ q⁻¹`
   (`r i ^ q = c i`). Combining coefficientwise scalar extension with `restrictedExpand q` gives an
   isometric ring homomorphism `Ψ : K{X / c} →+* K'{X / r}`, extending to an isometric field
   embedding `Ψ_F : F →+* F'` into `F' := GaussFractionField σ K' r`.
2. Every `f ∈ K{X / c}` has an explicit `q`-th root `tateRoot f ∈ K'{X / r}` obtained by applying
   `FrobeniusRoot.root K p e` coefficientwise. Choosing an `F`-basis `b` of `M` whose `q`-th powers
   lie in `K{X / c}`, `TauCeti.IsPurelyInseparable.nonempty_algHom_of_forall_exists_pow_eq` embeds
   `M` `F`-linearly into `F'` with `‖ι y‖ = spectralNorm F M y` and `ι (b j)` equal to the `q`-th
   root of `b j ^ q` in `K'{X / r}`.
3. The `K`-span `E ⊆ K'` of all power-series coefficients of the generators `tateRoot (g j)` is
   countably generated over the complete ultrametric field `K`, so `StrongDual K E` separates
   points of `E` (`Submodule.separatingDual_span_of_countable`).
4. Extracting a `q`-adic expansion component (`restrictedExpandComponent`) and applying a
   continuous functional `f_dual : StrongDual K E` coefficientwise produces `K`-linear maps from
   series with coefficients in `E` back to `K{X / c}` that are `K{X / c}`-linear along `Ψ`, bounded
   in Gauss norm, and jointly separating on nonzero elements. Clearing denominators of coordinates
   in the basis `b` yields separating spectrally bounded `F`-linear functionals on `M`, concluding
   by `Module.Dual.exists_bound_of_forall_exists_ne_zero`.

## Main results

* `TauCeti.MvPowerSeries.spectralNorm_gaussFractionField_of_isEmpty` and
  `TauCeti.MvPowerSeries.isWeaklyStable_gaussFractionField_iff_of_isEmpty`: zero-variable agreement
  with extensions of `K`.
* `TauCeti.MvPowerSeries.isWeaklyStable_gaussFractionField`: characteristic-free weak stability of
  `GaussFractionField σ K c` for `[Finite σ]` over a complete nontrivially normed ultrametric field.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §§3.5.3 and 5.3.1,
  Theorem 1.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries Filter
open scoped Topology IntermediateField

section Empty

variable (σ K : Type*) [NormedField K] [IsUltrametricDist K] [IsEmpty σ]
  (c : σ → ℝ) [∀ i, Fact (0 < c i)]

/-- With no variables, the spectral norm of an extension over `GaussFractionField σ K c` coincides
with its spectral norm over `K`. -/
@[simp]
theorem spectralNorm_gaussFractionField_of_isEmpty (L : Type*) [Field L]
    [Algebra K L] [Algebra (GaussFractionField σ K c) L]
    [IsScalarTower K (GaussFractionField σ K c) L] (y : L) :
    spectralNorm (GaussFractionField σ K c) L y = spectralNorm K L y := by
  refine ((gaussFractionFieldIsEmptyAlgEquiv σ K c).toRingEquiv.spectralNorm_eq_of_norm_eq
    (norm_gaussFractionFieldIsEmptyAlgEquiv σ K c) (RingEquiv.refl L) ?_ y).symm
  ext z
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, AlgEquiv.toRingEquiv_toRingHom,
    RingHom.coe_coe, RingEquiv.refl_apply]
  rw [IsScalarTower.algebraMap_apply K (GaussFractionField σ K c) L,
    ← gaussFractionFieldIsEmptyAlgEquiv_symm_apply, AlgEquiv.symm_apply_apply]

/-- With no variables, `GaussFractionField σ K c` is weakly stable if and only if `K` is weakly
stable. -/
@[simp]
theorem isWeaklyStable_gaussFractionField_iff_of_isEmpty :
    IsWeaklyStable (GaussFractionField σ K c) ↔ IsWeaklyStable K :=
  (gaussFractionFieldIsEmptyAlgEquiv σ K c).toRingEquiv.isWeaklyStable_iff_of_norm_eq
    (norm_gaussFractionFieldIsEmptyAlgEquiv σ K c)

end Empty

section WeaklyStable

section Helpers

variable {σ K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- Applying `FrobeniusRoot.root K p e` coefficientwise maps `K{X / c}` into
`(FrobeniusRoot K p e){X / r}` when `r i = c i ^ (p ^ e)⁻¹`. -/
private noncomputable def tateRoot (p : ℕ) [ExpChar K p] (e : ℕ)
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)] (hr : ∀ i, r i = c i ^ (((p ^ e : ℕ) : ℝ)⁻¹))
    (f : IsRestricted.subring (R := K) c) :
    IsRestricted.subring (R := FrobeniusRoot K p e) r :=
  ⟨MvPowerSeries.map (FrobeniusRoot.root K p e) (f : _root_.MvPowerSeries σ K), by
    let qR : ℝ := ((p ^ e : ℕ) : ℝ)
    have hq_inv : 0 < qR⁻¹ :=
      inv_pos.mpr (Nat.cast_pos.mpr (pow_pos (expChar_pos K p) e))
    have hlim :=
      ((Real.continuousAt_rpow_const 0 qR⁻¹ (Or.inr hq_inv.le)).tendsto.comp f.2)
    rw [Real.zero_rpow hq_inv.ne'] at hlim
    refine hlim.congr fun μ ↦ ?_
    dsimp only [Function.comp_apply, qR]
    rw [Real.mul_rpow (norm_nonneg _) (prod_pow_pos μ).le, coeff_map, FrobeniusRoot.norm_root,
      μ.prod_pow_rpow (fun i _ ↦ (Fact.out : 0 < c i).le)]
    congr 1
    exact Finset.prod_congr rfl fun i _ ↦ by simp only [hr]⟩

@[simp]
private theorem coe_tateRoot (p : ℕ) [ExpChar K p] (e : ℕ)
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)] (hr : ∀ i, r i = c i ^ (((p ^ e : ℕ) : ℝ)⁻¹))
    (f : IsRestricted.subring (R := K) c) :
    (tateRoot p e hr f : _root_.MvPowerSeries σ (FrobeniusRoot K p e)) =
      MvPowerSeries.map (FrobeniusRoot.root K p e) (f : _root_.MvPowerSeries σ K) :=
  (rfl)

private theorem tateRoot_pow {p : ℕ} [ExpChar K p] {e : ℕ}
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)]
    (hr : ∀ i, r i = c i ^ (((p ^ e : ℕ) : ℝ)⁻¹))
    (hr_pow : ∀ i, r i ^ p ^ e = c i)
    (f : IsRestricted.subring (R := K) c) :
    tateRoot p e hr f ^ p ^ e =
      restrictedExpand (p ^ e) (pow_pos (expChar_pos K p) e).ne' hr_pow
        (restrictedMap (algebraMap K (FrobeniusRoot K p e)) (C := 1)
          (fun a ↦ by simp) f) := by
  have hp : p ≠ 0 := (expChar_pos K p).ne'
  have hhom : (iterateFrobenius (FrobeniusRoot K p e) p e).comp (FrobeniusRoot.root K p e) =
      algebraMap K (FrobeniusRoot K p e) := by
    ext a
    exact FrobeniusRoot.root_pow_expChar_pow a
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow, coe_tateRoot, coe_restrictedExpand, coe_restrictedMap,
    ← MvPowerSeries.map_iterateFrobenius_expand p hp _ e, ← MvPowerSeries.map_expand,
    MvPowerSeries.map_map, hhom, MvPowerSeries.map_expand]

/-- Embeds a finite purely inseparable extension `M` of `GaussFractionField σ K c` of exponent at
most `e` in exponential characteristic `p` isometrically (for `spectralNorm`) into
`GaussFractionField σ (FrobeniusRoot K p e) r` with `r i = c i ^ (p ^ e)⁻¹`, sending an `F`-basis
of `M` into restricted series over `FrobeniusRoot K p e`. -/
private theorem exists_isometric_ringHom_of_isPurelyInseparable
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)]
    (M : Type*) [Field M] [Algebra (GaussFractionField σ K c) M]
    [FiniteDimensional (GaussFractionField σ K c) M]
    [IsPurelyInseparable (GaussFractionField σ K c) M]
    (p : ℕ) [ExpChar K p] [ExpChar (GaussFractionField σ K c) p]
    (e : ℕ) (he : IsPurelyInseparable.exponent (GaussFractionField σ K c) M ≤ e)
    (hr_def : ∀ i, r i = c i ^ (((p ^ e : ℕ) : ℝ)⁻¹))
    (hr : ∀ i, r i ^ p ^ e = c i)
    (h_iso : ∀ a : K, ‖algebraMap K (FrobeniusRoot K p e) a‖ ≤ 1 * ‖a‖) :
    ∃ (Ψ : IsRestricted.subring (R := K) c →+*
          IsRestricted.subring (R := FrobeniusRoot K p e) r)
      (m : ℕ) (b : Module.Basis (Fin m) (GaussFractionField σ K c) M)
      (rootG : Fin m → IsRestricted.subring (R := FrobeniusRoot K p e) r)
      (ι : M →+* GaussFractionField σ (FrobeniusRoot K p e) r),
      (∀ f, Ψ f = restrictedExpand (p ^ e) (pow_pos (expChar_pos K p) e).ne' hr
        (restrictedMap (algebraMap K (FrobeniusRoot K p e)) h_iso f)) ∧
      (∀ f, ‖Ψ f‖ = ‖f‖) ∧
      (∀ f, ι (algebraMap (GaussFractionField σ K c) M
        (algebraMap (IsRestricted.subring (R := K) c) (GaussFractionField σ K c) f)) =
        algebraMap (IsRestricted.subring (R := FrobeniusRoot K p e) r)
          (GaussFractionField σ (FrobeniusRoot K p e) r) (Ψ f)) ∧
      (∀ y : M, ‖ι y‖ = spectralNorm (GaussFractionField σ K c) M y) ∧
      (∀ j : Fin m, ι (b j) =
        algebraMap (IsRestricted.subring (R := FrobeniusRoot K p e) r)
          (GaussFractionField σ (FrobeniusRoot K p e) r) (rootG j)) := by
  classical
  let T := IsRestricted.subring (R := K) c
  let F := GaussFractionField σ K c
  let K' := FrobeniusRoot K p e
  let T' := IsRestricted.subring (R := K') r
  let F' := GaussFractionField σ K' r
  have : ExpChar F' p := expChar_of_injective_algebraMap (algebraMap K' F').injective p
  have hq : p ^ e ≠ 0 := (pow_pos (expChar_pos K p) e).ne'
  -- Step 1: Extend the isometric Tate-algebra map `Ψ : T →+* T'` across fractions to `F →+* F'`.
  let Ψ : T →+* T' :=
    (restrictedExpand (p ^ e) hq hr).toRingHom.comp (restrictedMap (algebraMap K K') h_iso)
  have hΨ_norm (f : T) : ‖Ψ f‖ = ‖f‖ := by
    dsimp only [Ψ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [norm_restrictedExpand, norm_restrictedMap _ _ FrobeniusRoot.norm_algebraMap]
  have hΨ_inj : Function.Injective Ψ :=
    ((AddMonoidHomClass.isometry_iff_norm Ψ).mpr hΨ_norm).injective
  let _ : Algebra F F' := (Ψ.gaussFractionFieldMap hΨ_inj).toAlgebra
  have hF_alg : algebraMap F F' = Ψ.gaussFractionFieldMap hΨ_inj :=
    RingHom.algebraMap_toAlgebra _
  -- Step 2: Pick an `F`-basis `b` of `M` with `b j ^ p ^ e ∈ T` and `p ^ e`-th roots in `T'`.
  obtain ⟨m, b, g, hg⟩ :=
    IsPurelyInseparable.exists_basis_iterateFrobenius_eq_algebraMap T F M p he
  let rootG (j : Fin m) : T' := tateRoot p e hr_def (g j)
  have hrootG_pow (j : Fin m) : rootG j ^ p ^ e = Ψ (g j) :=
    tateRoot_pow hr_def hr (g j)
  -- Step 3: Embed `M` `F`-linearly into `F'` by sending `b` to the `p ^ e`-th roots `rootG`.
  have hspan_b : IntermediateField.adjoin F (Set.range b) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    rw [← b.sum_repr y]
    refine sum_mem fun j _ ↦ ?_
    rw [Algebra.smul_def]
    exact mul_mem (IntermediateField.algebraMap_mem _ _)
      (IntermediateField.subset_adjoin F _ ⟨j, rfl⟩)
  have ⟨ι₀⟩ : Nonempty (M →ₐ[F] F') := by
    refine IsPurelyInseparable.nonempty_algHom_of_forall_exists_pow_eq F M p he F' hspan_b ?_
    rintro _ ⟨j, rfl⟩
    refine ⟨algebraMap T' F' (rootG j), ?_⟩
    rw [← map_pow, hrootG_pow, ← Ψ.gaussFractionFieldMap_algebraMap hΨ_inj, ← hF_alg, hg]
  -- Step 4: Verify scalar compatibility, spectral-norm isometry, and images of the basis `b`.
  refine ⟨Ψ, m, b, rootG, ι₀.toRingHom, fun _ ↦ rfl, hΨ_norm, fun f ↦ ?_, fun y ↦ ?_, fun j ↦ ?_⟩
  · rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes, hF_alg]
    exact Ψ.gaussFractionFieldMap_algebraMap hΨ_inj f
  · obtain ⟨k, a, ha⟩ := IsPurelyInseparable.pow_mem F p y
    have hpk : p ^ k ≠ 0 := (pow_pos (expChar_pos K p) k).ne'
    refine (pow_left_inj₀ (norm_nonneg _) (spectralNorm_nonneg _) hpk).mp ?_
    have hι_pow : (ι₀ y) ^ p ^ k = Ψ.gaussFractionFieldMap hΨ_inj a := by
      rw [← map_pow, ← ha, AlgHom.commutes, hF_alg]
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← norm_pow, hι_pow,
      Ψ.norm_gaussFractionFieldMap hΨ_inj hΨ_norm,
      TauCeti.spectralNorm_pow_eq_norm_of_pow_eq_algebraMap hpk ha.symm]
  · refine iterateFrobenius_inj F' p e ?_
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, iterateFrobenius_def]
    rw [← map_pow, ← IsPurelyInseparable.algebraMap_iterateFrobenius F p he (b j),
      AlgHom.commutes, hF_alg, ← map_pow, hrootG_pow, ← hg]
    exact Ψ.gaussFractionFieldMap_algebraMap hΨ_inj (g j)

private theorem algebraMap_sum_mul_eq_mul
    {K' : Type*} [NormedField K'] [IsUltrametricDist K']
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)]
    {M : Type*} [Field M] [Algebra (GaussFractionField σ K c) M]
    {m : ℕ} (b : Module.Basis (Fin m) (GaussFractionField σ K c) M)
    (Ψ : IsRestricted.subring (R := K) c →+* IsRestricted.subring (R := K') r)
    (rootG : Fin m → IsRestricted.subring (R := K') r)
    (ι : M →+* GaussFractionField σ K' r)
    (hι_alg : ∀ f, ι (algebraMap (GaussFractionField σ K c) M
      (algebraMap (IsRestricted.subring (R := K) c) (GaussFractionField σ K c) f)) =
      algebraMap (IsRestricted.subring (R := K') r) (GaussFractionField σ K' r) (Ψ f))
    (hι_b : ∀ j, ι (b j) =
      algebraMap (IsRestricted.subring (R := K') r) (GaussFractionField σ K' r) (rootG j))
    (y : M) (s : nonZeroDivisors (IsRestricted.subring (R := K) c))
    (a : Fin m → IsRestricted.subring (R := K) c)
    (ha : ∀ j, algebraMap (IsRestricted.subring (R := K) c) (GaussFractionField σ K c) (a j) =
      (s : IsRestricted.subring (R := K) c) • b.repr y j) :
    algebraMap (IsRestricted.subring (R := K') r) (GaussFractionField σ K' r)
      (∑ j, Ψ (a j) * rootG j) =
      algebraMap (IsRestricted.subring (R := K') r) (GaussFractionField σ K' r) (Ψ s) * ι y := by
  let T := IsRestricted.subring (R := K) c
  let F := GaussFractionField σ K c
  rw [map_sum, ← b.sum_repr y, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have haj : algebraMap T F (a j) = algebraMap T F s * b.repr y j := by
    simpa only [Algebra.smul_def] using ha j
  rw [map_mul, ← hι_alg (a j), haj, map_mul, map_mul, hι_alg s, ← hι_b j, mul_assoc,
    ← map_mul ι, ← Algebra.smul_def (b.repr y j) (b j)]

private theorem exists_restrictedFamily_coeff_sum_ne_zero
    {K' : Type*} [NormedField K'] [IsUltrametricDist K'] [NormedAlgebra K K']
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)]
    {q : ℕ} (hq : q ≠ 0) (hr : ∀ i, r i ^ q = c i)
    (h_iso : ∀ a : K, ‖algebraMap K K' a‖ ≤ 1 * ‖a‖)
    {Ψ : IsRestricted.subring (R := K) c →+* IsRestricted.subring (R := K') r}
    (hΨ_def : ∀ f, Ψ f = restrictedExpand q hq hr (restrictedMap (algebraMap K K') h_iso f))
    {m : ℕ} {rootG : Fin m → IsRestricted.subring (R := K') r}
    {E : Submodule K K'}
    (hrootG_mem : ∀ (j : Fin m) (α : σ →₀ ℕ),
      coeff α (rootG j : _root_.MvPowerSeries σ K') ∈ E)
    {a₀ : Fin m → IsRestricted.subring (R := K) c}
    (ha₀ : ∑ j, Ψ (a₀ j) * rootG j ≠ 0) :
    ∃ (ν : σ →₀ ℕ) (μ : σ →₀ ℕ) (wE : Fin m → IsRestrictedFamily.addSubgroup E c),
      (∀ i, ν i < q) ∧
      (∀ (a : Fin m → IsRestricted.subring (R := K) c) (α : σ →₀ ℕ),
        ((IsRestrictedFamily.coeff K α (∑ j, a j • wE j) : E) : K') =
          coeff α (restrictedExpandComponent hq hr ν (∑ j, Ψ (a j) * rootG j) :
            _root_.MvPowerSeries σ K')) ∧
      IsRestrictedFamily.coeff K μ (∑ j, a₀ j • wE j) ≠ 0 := by
  classical
  obtain ⟨ν, hν, hν_norm⟩ :=
    exists_norm_restrictedExpandComponent_mul_prod_eq hq hr (∑ j, Ψ (a₀ j) * rootG j)
  have hcomp_ne : restrictedExpandComponent hq hr ν (∑ j, Ψ (a₀ j) * rootG j) ≠ 0 := by
    intro h0
    rw [h0, norm_zero, zero_mul] at hν_norm
    exact ha₀ (norm_eq_zero.mp hν_norm.symm)
  obtain ⟨μ, hμ_ne⟩ : ∃ μ, coeff μ
      (restrictedExpandComponent hq hr ν (∑ j, Ψ (a₀ j) * rootG j) :
        _root_.MvPowerSeries σ K') ≠ 0 := by
    by_contra! hall
    exact hcomp_ne (Subtype.ext (MvPowerSeries.ext fun μ ↦ by
      rw [ZeroMemClass.coe_zero, map_zero]
      exact hall μ))
  have hwG_mem (j : Fin m) (α : σ →₀ ℕ) :
      coeff α (restrictedExpandComponent hq hr ν (rootG j) : _root_.MvPowerSeries σ K') ∈ E := by
    rw [coeff_restrictedExpandComponent]
    exact hrootG_mem j (q • α + ν)
  let wE : Fin m → IsRestrictedFamily.addSubgroup E c := fun j ↦
    ⟨fun α ↦ ⟨coeff α (restrictedExpandComponent hq hr ν (rootG j) :
        _root_.MvPowerSeries σ K'), hwG_mem j α⟩,
      IsRestrictedFamily.mem_addSubgroup.mpr <|
        ((isRestrictedFamily_coeff_iff _).mpr
          (restrictedExpandComponent hq hr ν (rootG j)).2).of_norm_le (C := 1) fun _ ↦
            (one_mul _).symm.le⟩
  have hcoe_wE (j : Fin m) (α : σ →₀ ℕ) :
      ((IsRestrictedFamily.coeff K α (wE j) : E) : K') =
        coeff α (restrictedExpandComponent hq hr ν (rootG j) :
          _root_.MvPowerSeries σ K') := by
    rw [IsRestrictedFamily.coeff_apply]
  have hcoe_sum (a : Fin m → IsRestricted.subring (R := K) c) (α : σ →₀ ℕ) :
      ((IsRestrictedFamily.coeff K α (∑ j, a j • wE j) : E) : K') =
        coeff α (restrictedExpandComponent hq hr ν (∑ j, Ψ (a j) * rootG j) :
          _root_.MvPowerSeries σ K') := by
    rw [restrictedExpandComponent_sum, AddSubmonoidClass.coe_finsetSum, map_sum, map_sum,
      Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [hΨ_def, restrictedExpandComponent_restrictedExpand_mul hq hr hν _ (rootG j),
      IsRestrictedFamily.coeff_apply, IsRestrictedFamily.coe_isRestrictedSubring_smul,
      convSMul_apply, Submodule.coe_sum, Subring.coe_mul, coeff_mul]
    refine Finset.sum_congr rfl fun pq _ ↦ ?_
    rw [SetLike.val_smul, Algebra.smul_def, coeff_restrictedMap,
      ← IsRestrictedFamily.coeff_apply (R := K), hcoe_wE]
  refine ⟨ν, μ, wE, hν, hcoe_sum, Subtype.coe_ne_coe.mp ?_⟩
  rw [ZeroMemClass.coe_zero, hcoe_sum]
  exact hμ_ne

private theorem exists_sum_mul_ne_zero_of_sum_ne_zero
    {K' : Type*} [NormedField K'] [IsUltrametricDist K'] [NormedAlgebra K K']
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)]
    {q : ℕ} (hq : q ≠ 0) (hr : ∀ i, r i ^ q = c i)
    (h_iso : ∀ a : K, ‖algebraMap K K' a‖ ≤ 1 * ‖a‖)
    {Ψ : IsRestricted.subring (R := K) c →+* IsRestricted.subring (R := K') r}
    (hΨ_def : ∀ f, Ψ f = restrictedExpand q hq hr (restrictedMap (algebraMap K K') h_iso f))
    {m : ℕ} {rootG : Fin m → IsRestricted.subring (R := K') r}
    {E : Submodule K K'} [SeparatingDual K E]
    (hrootG_mem : ∀ (j : Fin m) (α : σ →₀ ℕ),
      coeff α (rootG j : _root_.MvPowerSeries σ K') ∈ E)
    {a₀ : Fin m → IsRestricted.subring (R := K) c}
    (ha₀ : ∑ j, Ψ (a₀ j) * rootG j ≠ 0) :
    ∃ (g : Fin m → IsRestricted.subring (R := K) c) (C_π : ℝ),
      (∀ a : Fin m → IsRestricted.subring (R := K) c,
        ‖∑ j, a j * g j‖ ≤ C_π * ‖∑ j, Ψ (a j) * rootG j‖) ∧
      ∑ j, a₀ j * g j ≠ 0 := by
  classical
  let T := IsRestricted.subring (R := K) c
  obtain ⟨ν, μ, wE, _, hcoe_sum, hμ_ne⟩ :=
    exists_restrictedFamily_coeff_sum_ne_zero hq hr h_iso hΨ_def hrootG_mem ha₀
  obtain ⟨f_dual, hf_ne⟩ := SeparatingDual.exists_ne_zero (R := K) hμ_ne
  let π : IsRestrictedFamily.addSubgroup E c →ₗ[K] T :=
    (IsRestrictedFamily.subringLinearEquiv.symm.toLinearMap.restrictScalars K).comp
      (IsRestrictedFamily.mapLinearMap f_dual.toLinearMap f_dual.le_opNorm)
  have hπ_coeff (v : IsRestrictedFamily.addSubgroup E c) (α : σ →₀ ℕ) :
      coeff α (π v : _root_.MvPowerSeries σ K) = f_dual (IsRestrictedFamily.coeff K α v) := by
    simp only [π, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearEquiv.coe_toLinearMap, IsRestrictedFamily.coeff_coe_subringLinearEquiv_symm_apply,
      IsRestrictedFamily.coe_mapLinearMap, Function.comp_apply, IsRestrictedFamily.coeff_apply,
      ContinuousLinearMap.coe_coe]
  have hπ_sum (a : Fin m → T) : ∑ j, a j * π (wE j) = π (∑ j, a j • wE j) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    dsimp only [π, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearEquiv.coe_toLinearMap]
    rw [IsRestrictedFamily.mapLinearMap_isRestrictedSubring_smul,
      IsRestrictedFamily.subringLinearEquiv.symm.map_smul, smul_eq_mul]
  refine ⟨fun j ↦ π (wE j), ‖f_dual‖ / ν.prod (r · ^ ·), fun a ↦ ?_, fun h0 ↦ ?_⟩
  · rw [hπ_sum]
    calc ‖π (∑ j, a j • wE j)‖
        ≤ ‖f_dual‖ * ‖restrictedExpandComponent hq hr ν (∑ j, Ψ (a j) * rootG j)‖ := by
          refine norm_le_mul_of_norm_coeff_le (norm_nonneg f_dual) fun α ↦ ?_
          rw [hπ_coeff, ← hcoe_sum a α, ← AddSubgroupClass.coe_norm]
          exact f_dual.le_opNorm _
      _ ≤ ‖f_dual‖ * (‖∑ j, Ψ (a j) * rootG j‖ / ν.prod (r · ^ ·)) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [le_div_iff₀ (prod_pow_pos ν)]
          exact norm_restrictedExpandComponent_mul_prod_le hq hr ν _
      _ = (‖f_dual‖ / ν.prod (r · ^ ·)) * ‖∑ j, Ψ (a j) * rootG j‖ := by ring
  · rw [hπ_sum] at h0
    have hcoeff0 : coeff μ (π (∑ j, a₀ j • wE j) : _root_.MvPowerSeries σ K) = 0 := by
      rw [h0, ZeroMemClass.coe_zero, map_zero]
    rw [hπ_coeff] at hcoeff0
    exact hf_ne hcoeff0

end Helpers

/-- **Characteristic-free weak stability of Gauss-normed Tate fraction fields.**
For any complete nontrivially normed ultrametric field `K` (of arbitrary characteristic), finite
variable type `σ`, and positive polyradius `c : σ → ℝ`, the Gauss-normed fraction field
`GaussFractionField σ K c` is weakly stable ([bosch-guntzer-remmert], §5.3.1, Theorem 1). -/
theorem isWeaklyStable_gaussFractionField (σ K : Type*) [Finite σ]
    [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (c : σ → ℝ) [∀ i, Fact (0 < c i)] :
    IsWeaklyStable (GaussFractionField σ K c) := by
  classical
  let T := IsRestricted.subring (R := K) c
  let F := GaussFractionField σ K c
  refine IsWeaklyStable.of_isPurelyInseparable fun M _ _ _ _ ψ ↦ ?_
  let p := ringExpChar K
  have : ExpChar F p := expChar_of_injective_algebraMap (algebraMap K F).injective p
  let e := IsPurelyInseparable.exponent F M
  set q := p ^ e
  have hq : q ≠ 0 := (pow_pos (expChar_pos K p) e).ne'
  have hqR_ne : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  -- Step 1 & 2: Construct `K' = FrobeniusRoot K p e`, `r = c ^ q⁻¹`, and embed `M` into `F'`.
  let K' := FrobeniusRoot K p e
  let r : σ → ℝ := fun i ↦ c i ^ ((q : ℝ)⁻¹)
  have hr_fact : ∀ i, Fact (0 < r i) := fun i ↦ ⟨Real.rpow_pos_of_pos (Fact.out : 0 < c i) _⟩
  have hr : ∀ i, r i ^ q = c i := fun i ↦ by
    dsimp only [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Fact.out : 0 < c i).le, inv_mul_cancel₀ hqR_ne,
      Real.rpow_one]
  let T' := IsRestricted.subring (R := K') r
  let F' := GaussFractionField σ K' r
  have h_iso : ∀ a : K, ‖algebraMap K K' a‖ ≤ 1 * ‖a‖ := fun a ↦ by
    rw [one_mul, FrobeniusRoot.norm_algebraMap]
  obtain ⟨Ψ, m, b, rootG, ι, hΨ_def, hΨ_norm, hι_alg, hι_norm, hι_b⟩ :=
    exists_isometric_ringHom_of_isPurelyInseparable M p e le_rfl (fun _ ↦ rfl) hr h_iso
  -- Step 3: Span a countable-type `K`-subspace `E ⊆ K'` from all coefficients of `rootG`.
  have : Countable (σ →₀ ℕ) := DFunLike.coe_injective.countable
  obtain ⟨E, _, hrootG_mem⟩ : ∃ E : Submodule K K', SeparatingDual K E ∧
      ∀ (j : Fin m) (α : σ →₀ ℕ), coeff α (rootG j : _root_.MvPowerSeries σ K') ∈ E :=
    ⟨Submodule.span K (Set.range fun idx : Fin m × (σ →₀ ℕ) ↦
        coeff idx.2 (rootG idx.1 : _root_.MvPowerSeries σ K')),
      Submodule.separatingDual_span_of_countable (Set.countable_range _),
      fun j α ↦ Submodule.subset_span ⟨(j, α), rfl⟩⟩
  -- Step 4: Construct separating spectrally bounded `F`-linear functionals on `M`.
  refine Module.Dual.exists_bound_of_forall_exists_ne_zero ψ (spectralNorm F M) fun x₀ hx₀ ↦ ?_
  obtain ⟨s₀, hs₀⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors T)
    (b.repr x₀)
  choose a₀ ha₀ using hs₀
  have hs₀_F_ne : algebraMap T' F' (Ψ s₀) ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_algebraMap_gaussFractionField, hΨ_norm, norm_ne_zero_iff]
    exact nonZeroDivisors.ne_zero s₀.2
  have hu₀_ne : ∑ j, Ψ (a₀ j) * rootG j ≠ 0 := by
    intro h0
    have hmul : algebraMap T' F' (Ψ s₀) * ι x₀ = 0 := by
      rw [← algebraMap_sum_mul_eq_mul b Ψ rootG ι hι_alg hι_b x₀ s₀ a₀ ha₀, h0, map_zero]
    exact mul_ne_zero hs₀_F_ne ((map_ne_zero_iff ι ι.injective).mpr hx₀) hmul
  obtain ⟨g, C_π, hg_norm, hg_ne⟩ :=
    exists_sum_mul_ne_zero_of_sum_ne_zero hq hr h_iso hΨ_def hrootG_mem hu₀_ne
  let φ : Module.Dual F M := b.constr F fun j ↦ algebraMap T F (g j)
  have hφ_clear (y : M) (s : nonZeroDivisors T) (a : Fin m → T)
      (ha : ∀ j, algebraMap T F (a j) = (s : T) • b.repr y j) :
      algebraMap T F s * φ y = algebraMap T F (∑ j, a j * g j) := by
    conv_lhs => rw [← b.sum_repr y]
    rw [map_sum, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    dsimp only [φ]
    rw [map_smul, b.constr_basis, smul_eq_mul, ← mul_assoc,
      ← Algebra.smul_def (s : T) (b.repr y j), ← ha j, ← map_mul]
  refine ⟨φ, ⟨C_π, fun y ↦ ?_⟩, fun hφ0 ↦ ?_⟩
  · obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors T)
      (b.repr y)
    choose a ha using hs
    have hu_norm : ‖∑ j, Ψ (a j) * rootG j‖ = ‖(s : T)‖ * spectralNorm F M y := by
      rw [← norm_algebraMap_gaussFractionField σ K' r _,
        algebraMap_sum_mul_eq_mul b Ψ rootG ι hι_alg hι_b y s a ha, norm_mul,
        norm_algebraMap_gaussFractionField σ K' r _, hΨ_norm, hι_norm]
    have hs_pos : 0 < ‖(s : T)‖ := by
      rw [← norm_algebraMap_gaussFractionField σ K c (s : T), norm_pos_iff]
      exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
    refine le_of_mul_le_mul_left ?_ hs_pos
    calc ‖(s : T)‖ * ‖φ y‖
        = ‖algebraMap T F s * φ y‖ := by
            rw [norm_mul, norm_algebraMap_gaussFractionField σ K c _]
      _ = ‖∑ j, a j * g j‖ := by
            rw [hφ_clear y s a ha, norm_algebraMap_gaussFractionField σ K c _]
      _ ≤ C_π * ‖∑ j, Ψ (a j) * rootG j‖ := hg_norm a
      _ = ‖(s : T)‖ * (C_π * spectralNorm F M y) := by rw [hu_norm]; ring
  · refine hg_ne (IsFractionRing.injective T F ?_)
    rw [map_zero, ← hφ_clear x₀ s₀ a₀ ha₀, hφ0, mul_zero]

end WeaklyStable

section Examples

/-!
### Non-vacuous instances of weak stability over `GaussFractionField`

In at least one variable, `GaussFractionField σ K c` has genuine nontrivial finite extensions of
both types:
* a degree-`2` separable extension defined by `Y ^ 2 + Xᵢ ^ 2 * Y + Xᵢ` (valid in every
  characteristic, including characteristic `2`), and
* in prime characteristic `p`, a nontrivial purely inseparable extension obtained by adjoining a
  `p`-th root of `Xᵢ`.

In both cases `isWeaklyStable_gaussFractionField` yields equivalence between `spectralNorm` and the
power-basis coordinate norm.
-/

universe u₁ u₂

private theorem sq_add_X_sq_mul_add_X_mul_sq_ne_zero {σ R : Type*}
    [CommSemiring R] [NoZeroDivisors R] [Nontrivial R] (i : σ)
    {A B : _root_.MvPowerSeries σ R} (hB : B ≠ 0) :
    A ^ 2 + (_root_.MvPowerSeries.X i) ^ 2 * A * B +
      (_root_.MvPowerSeries.X i) * B ^ 2 ≠ 0 := by
  rcases eq_or_ne A 0 with rfl | hA
  · rw [sq, zero_mul, mul_zero, zero_mul, zero_add, zero_add]
    exact mul_ne_zero (MvPowerSeries.X_ne_zero i) (pow_ne_zero 2 hB)
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp (MvPowerSeries.order_eq_top_iff.not.mpr hA)
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp (MvPowerSeries.order_eq_top_iff.not.mpr hB)
  have ho1 : (A ^ 2).order = ((2 * a : ℕ) : ℕ∞) := by
    rw [MvPowerSeries.order_pow, ← ha, nsmul_eq_mul]
    norm_cast
  have ho2 : ((_root_.MvPowerSeries.X i) * B ^ 2).order = ((1 + 2 * b : ℕ) : ℕ∞) := by
    rw [MvPowerSeries.order_mul, MvPowerSeries.order_X, MvPowerSeries.order_pow, ← hb,
      nsmul_eq_mul]
    norm_cast
  have ho3 : ((_root_.MvPowerSeries.X i) ^ 2 * A * B).order = ((2 + a + b : ℕ) : ℕ∞) := by
    rw [MvPowerSeries.order_mul, MvPowerSeries.order_mul, MvPowerSeries.order_pow,
      MvPowerSeries.order_X, ← ha, ← hb, nsmul_eq_mul]
    norm_cast
  have hne12 : (A ^ 2).order ≠ ((_root_.MvPowerSeries.X i) * B ^ 2).order := by
    rw [ho1, ho2, ne_eq, Nat.cast_inj]
    omega
  have hmin_cast (x y : ℕ) : (min (x : ℕ∞) (y : ℕ∞)) = ((min x y : ℕ) : ℕ∞) :=
    (Monotone.map_min (fun _ _ ↦ Nat.cast_le.mpr)).symm
  have ho12 : (A ^ 2 + (_root_.MvPowerSeries.X i) * B ^ 2).order =
      ((min (2 * a) (1 + 2 * b) : ℕ) : ℕ∞) := by
    rw [MvPowerSeries.order_add_of_order_ne hne12, ho1, ho2, hmin_cast]
  have hlt : min (2 * a) (1 + 2 * b) < 2 + a + b := by omega
  have hne_sum : (A ^ 2 + (_root_.MvPowerSeries.X i) * B ^ 2).order ≠
      ((_root_.MvPowerSeries.X i) ^ 2 * A * B).order := by
    rw [ho12, ho3, ne_eq, Nat.cast_inj]
    exact hlt.ne
  rw [add_right_comm, ne_eq, ← MvPowerSeries.order_eq_top_iff,
    MvPowerSeries.order_add_of_order_ne hne_sum, ho12, ho3, hmin_cast]
  exact ENat.natCast_ne_top _

/-- In any characteristic (including `2`), `Y ^ 2 + Xᵢ ^ 2 * Y + Xᵢ` defines a degree-`2` separable
extension of `GaussFractionField σ K c` on which `spectralNorm` is equivalent to the power-basis
coordinate norm. -/
example (σ : Type u₁) (K : Type u₂) [Finite σ] [Nonempty σ]
    [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (c : σ → ℝ) [∀ i, Fact (0 < c i)] :
    let F := GaussFractionField σ K c
    ∃ (L : Type (max u₁ u₂)) (_ : Field L) (_ : Algebra F L) (_ : FiniteDimensional F L)
      (_ : Algebra.IsSeparable F L) (n : ℕ) (_ : NeZero n) (b : Module.Basis (Fin n) F L),
      Module.finrank F L = 2 ∧
      ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ y,
        b.norm y ≤ C * spectralNorm F L y ∧ spectralNorm F L y ≤ D * b.norm y := by
  classical
  let T := IsRestricted.subring (R := K) c
  let F := GaussFractionField σ K c
  let i₀ : σ := Classical.arbitrary σ
  let X₀ : T := ⟨MvPowerSeries.X i₀, isRestricted_X c i₀⟩
  let x₀ : F := algebraMap T F X₀
  have hx₀_ne : x₀ ≠ 0 := by
    rw [← norm_pos_iff, norm_algebraMap_gaussFractionField, norm_X]
    exact Fact.out
  let P : Polynomial F := Polynomial.X ^ 2 + Polynomial.C (x₀ ^ 2) * Polynomial.X + Polynomial.C x₀
  have hP_deg : P.natDegree = 2 := by
    dsimp only [P]
    compute_degree!
  have hP_monic : P.Monic := by
    dsimp only [P]
    monicity!
  have hP_noroot (z : F) : ¬ P.IsRoot z := by
    intro hz
    rw [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_add, Polynomial.eval_pow,
      Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_C] at hz
    obtain ⟨A, B, hB_mem, rfl⟩ := IsFractionRing.div_surjective T z
    have hB_F_ne : algebraMap T F B ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hB_mem
    have hclear : algebraMap T F (A ^ 2 + X₀ ^ 2 * A * B + X₀ * B ^ 2) = 0 := by
      have hmul := congrArg (· * (algebraMap T F B) ^ 2) hz
      simp only [zero_mul, map_add, map_mul, map_pow] at hmul ⊢
      dsimp only [x₀] at hmul
      field_simp [hB_F_ne] at hmul
      linear_combination hmul
    have hT0 : A ^ 2 + X₀ ^ 2 * A * B + X₀ * B ^ 2 = 0 :=
      (map_eq_zero_iff _ (IsFractionRing.injective T F)).mp hclear
    exact sq_add_X_sq_mul_add_X_mul_sq_ne_zero i₀
      (Subtype.coe_ne_coe.mpr (nonZeroDivisors.ne_zero hB_mem))
      (by simpa only [Subring.coe_add, Subring.coe_mul, SubmonoidClass.coe_pow,
        ZeroMemClass.coe_zero] using congrArg Subtype.val hT0)
  have hP_irr : Irreducible P :=
    Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hP_deg]; decide) hP_noroot
  have hP_sep : P.Separable := by
    rw [Polynomial.separable_iff_derivative_ne_zero hP_irr]
    intro hderiv
    exact hx₀_ne (by simpa [P] using congrArg (Polynomial.eval 0) hderiv)
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_root (P.map (algebraMap F (AlgebraicClosure F)))
    (by rw [Polynomial.degree_map_eq_of_injective (algebraMap F _).injective,
          Polynomial.degree_eq_natDegree hP_monic.ne_zero, hP_deg]; decide)
  have hβ_aeval : Polynomial.aeval β P = 0 := by
    rwa [Polynomial.aeval_def, ← Polynomial.eval_map]
  have hmin : minpoly F β = P :=
    (minpoly.eq_of_irreducible_of_monic hP_irr hβ_aeval hP_monic).symm
  have hβ_int : IsIntegral F β := ⟨P, hP_monic, hβ_aeval⟩
  have hβ_sep : IsSeparable F β := by rwa [IsSeparable, hmin]
  let L := F⟮β⟯
  have : Algebra.IsSeparable F L :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable F (AlgebraicClosure F)).mpr hβ_sep
  have hfin : Module.finrank F L = 2 := by
    rw [IntermediateField.adjoin.finrank hβ_int, hmin, hP_deg]
  let pb := IntermediateField.adjoin.powerBasis hβ_int
  have hdim : pb.dim = 2 := by rw [IntermediateField.adjoin.powerBasis_dim, hmin, hP_deg]
  have : NeZero pb.dim := ⟨by omega⟩
  obtain ⟨C, D, hC, hD, hCD⟩ :=
    (isWeaklyStable_gaussFractionField σ K c).exists_basis_norm_comparison pb.basis
  exact ⟨L, inferInstance, inferInstance, IntermediateField.adjoin.finiteDimensional hβ_int,
    inferInstance, pb.dim, inferInstance, pb.basis, hfin, C, D, hC, hD, hCD⟩

/-- In prime characteristic `p`, adjoining a `p`-th root of a coordinate variable `Xᵢ` produces a
nontrivial finite purely inseparable extension of `GaussFractionField σ K c` on which `spectralNorm`
is equivalent to the power-basis coordinate norm. -/
example (σ : Type u₁) (K : Type u₂) [Finite σ] [Nonempty σ]
    [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (c : σ → ℝ) [∀ i, Fact (0 < c i)] :
    let F := GaussFractionField σ K c
    ∃ (M : Type (max u₁ u₂)) (_ : Field M) (_ : Algebra F M) (_ : FiniteDimensional F M)
      (_ : IsPurelyInseparable F M) (n : ℕ) (_ : NeZero n) (b : Module.Basis (Fin n) F M),
      1 < Module.finrank F M ∧
      ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ y,
        b.norm y ≤ C * spectralNorm F M y ∧ spectralNorm F M y ≤ D * b.norm y := by
  classical
  have hp : p.Prime := Fact.out
  let T := IsRestricted.subring (R := K) c
  let F := GaussFractionField σ K c
  have : ExpChar K p := .prime hp
  have : ExpChar F p := expChar_of_injective_algebraMap (algebraMap K F).injective p
  let i₀ : σ := Classical.arbitrary σ
  let X₀ : T := ⟨MvPowerSeries.X i₀, isRestricted_X c i₀⟩
  let x₀ : F := algebraMap T F X₀
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap F (AlgebraicClosure F) x₀) hp.pos
  have hα_int : IsIntegral F α :=
    ⟨Polynomial.X ^ p - Polynomial.C x₀, Polynomial.monic_X_pow_sub_C x₀ hp.ne_zero, by
      simp [hα]⟩
  let M := F⟮α⟯
  have : IsPurelyInseparable F M := by
    rw [← le_perfectClosure_iff, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff,
      SetLike.mem_coe, mem_perfectClosure_iff_pow_mem p]
    exact ⟨1, x₀, by rw [pow_one, hα]⟩
  have : FiniteDimensional F M := IntermediateField.adjoin.finiteDimensional hα_int
  have hfin_gt : 1 < Module.finrank F M := by
    by_contra! hle
    have heq1 : Module.finrank F M = 1 := le_antisymm hle Module.finrank_pos
    obtain ⟨z, hz⟩ :=
      IntermediateField.mem_bot.mp (IntermediateField.finrank_adjoin_simple_eq_one_iff.mp heq1)
    have hzp : z ^ p = x₀ := by
      apply (algebraMap F (AlgebraicClosure F)).injective
      rw [map_pow, hz, hα]
    obtain ⟨A, B, hB_mem, rfl⟩ := IsFractionRing.div_surjective T z
    have hB_F_ne : algebraMap T F B ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hB_mem
    have hclear : algebraMap T F (A ^ p) = algebraMap T F (X₀ * B ^ p) := by
      have hmul := congrArg (· * (algebraMap T F B) ^ p) hzp
      rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero p hB_F_ne)] at hmul
      simpa only [x₀, map_mul, map_pow] using hmul
    have hser : (A : _root_.MvPowerSeries σ K) ^ p =
        (_root_.MvPowerSeries.X i₀ : _root_.MvPowerSeries σ K) *
          (B : _root_.MvPowerSeries σ K) ^ p := by
      simpa only [Subring.coe_mul, SubmonoidClass.coe_pow]
        using congrArg Subtype.val (IsFractionRing.injective T F hclear)
    have hB_ne : (B : _root_.MvPowerSeries σ K) ≠ 0 :=
      Subtype.coe_ne_coe.mpr (nonZeroDivisors.ne_zero hB_mem)
    have hA_ne : (A : _root_.MvPowerSeries σ K) ≠ 0 := by
      intro hA0
      rw [hA0, zero_pow hp.ne_zero] at hser
      exact mul_ne_zero (MvPowerSeries.X_ne_zero i₀) (pow_ne_zero p hB_ne) hser.symm
    obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp (MvPowerSeries.order_eq_top_iff.not.mpr hA_ne)
    obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp (MvPowerSeries.order_eq_top_iff.not.mpr hB_ne)
    have hord_eq := congrArg MvPowerSeries.order hser
    rw [MvPowerSeries.order_pow, ← ha, MvPowerSeries.order_mul, MvPowerSeries.order_X,
      MvPowerSeries.order_pow, ← hb, nsmul_eq_mul, nsmul_eq_mul] at hord_eq
    have hnat : p * a = 1 + p * b := by exact_mod_cast hord_eq
    have hmod := congrArg (· % p) hnat
    rw [Nat.mul_mod_right, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hp.one_lt] at hmod
    exact zero_ne_one hmod
  let pb := IntermediateField.adjoin.powerBasis hα_int
  have hdim_pos : 0 < pb.dim := by
    rw [IntermediateField.adjoin.powerBasis_dim, ← IntermediateField.adjoin.finrank hα_int]
    exact zero_lt_one.trans hfin_gt
  have : NeZero pb.dim := ⟨hdim_pos.ne'⟩
  obtain ⟨C, D, hC, hD, hCD⟩ :=
    (isWeaklyStable_gaussFractionField σ K c).exists_basis_norm_comparison pb.basis
  exact ⟨M, inferInstance, inferInstance, inferInstance, inferInstance,
    pb.dim, inferInstance, pb.basis, hfin_gt, C, D, hC, hD, hCD⟩

end Examples

end TauCeti.MvPowerSeries
