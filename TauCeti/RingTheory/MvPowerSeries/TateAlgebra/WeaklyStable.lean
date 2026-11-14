/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Field.WeaklyStable
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.FractionField

import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Data.Finsupp.Encodable
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.RingTheory.Localization.Integer
import TauCeti.Analysis.Normed.Module.Bases.CountableType
import TauCeti.Analysis.Normed.Module.Dual.Bounded
import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Basic
import TauCeti.Analysis.Normed.Unbundled.SpectralNorm.Basis
import TauCeti.FieldTheory.PurelyInseparable.Exponent
import TauCeti.RingTheory.MvPowerSeries.Basic
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.FrobeniusRoot
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Dual

/-!
# Characteristic-free weak stability of Gauss-normed Tate fraction fields

Let `K` be a complete nontrivially normed ultrametric field of arbitrary characteristic, `σ` a
countable variable type, and `c : σ → ℝ` a positive polyradius. This file proves that the
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
2. Every `f ∈ K{X / c}` has an explicit `q`-th root
   `frobeniusRootRestrictedEquiv p e hr f ∈ K'{X / r}` obtained by applying
   `FrobeniusRoot.root K p e` coefficientwise. Choosing an `F`-basis `b` of `M` whose `q`-th powers
   lie in `K{X / c}`, `exists_algHom_gaussFractionField_frobeniusRoot_of_isPurelyInseparable` embeds
   `M` `F`-linearly into `F'` with `‖ι y‖ = spectralNorm F M y` and `ι (b j)` equal to the `q`-th
   root of `b j ^ q` in `K'{X / r}`.
3. The `K`-span `E ⊆ K'` of all power-series coefficients of the generators
   `frobeniusRootRestrictedEquiv p e hr (g j)` is countably generated over the complete ultrametric
   field `K`, so `StrongDual K E` separates points (`Submodule.separatingDual_span_of_countable`).
4. Extracting a `q`-adic expansion component (`restrictedExpandComponentFamily`) and applying a
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
  `GaussFractionField σ K c` for `[Countable σ]` over a complete nontrivially normed ultrametric
  field.

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

/-- Embeds a finite purely inseparable extension `M` of `GaussFractionField σ K c` of exponent at
most `e` in exponential characteristic `p` isometrically (for `spectralNorm`) into
`GaussFractionField σ (FrobeniusRoot K p e) r` with `r i = c i ^ (p ^ e)⁻¹`, sending an `F`-basis
of `M` into restricted series over `FrobeniusRoot K p e`. -/
private theorem exists_isometric_ringHom_of_isPurelyInseparable
    {σ K : Type*} [NormedField K] [IsUltrametricDist K]
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)]
    (M : Type*) [Field M] [Algebra (GaussFractionField σ K c) M]
    [FiniteDimensional (GaussFractionField σ K c) M]
    [IsPurelyInseparable (GaussFractionField σ K c) M]
    (p : ℕ) [ExpChar K p] [ExpChar (GaussFractionField σ K c) p]
    (e : ℕ) (he : IsPurelyInseparable.exponent (GaussFractionField σ K c) M ≤ e)
    (hr_def : ∀ i, r i = c i ^ (((p ^ e : ℕ) : ℝ)⁻¹)) (hr : ∀ i, r i ^ p ^ e = c i)
    (h_iso : ∀ a : K, ‖algebraMap K (FrobeniusRoot K p e) a‖ ≤ 1 * ‖a‖) :
    let K' := FrobeniusRoot K p e
    let T := IsRestricted.subring (R := K) c
    let F := GaussFractionField σ K c
    let T' := IsRestricted.subring (R := K') r
    let F' := GaussFractionField σ K' r
    ∃ (Ψ : T →+* T') (m : ℕ) (b : Module.Basis (Fin m) F M) (rootG : Fin m → T') (ι : M →+* F'),
      (∀ f, Ψ f = restrictedExpand (p ^ e) (pow_pos (expChar_pos K p) e).ne' hr
        (restrictedMap (algebraMap K K') h_iso f)) ∧
      (∀ f, ‖Ψ f‖ = ‖f‖) ∧
      (∀ f, ι (algebraMap F M (algebraMap T F f)) = algebraMap T' F' (Ψ f)) ∧
      (∀ y : M, ‖ι y‖ = spectralNorm F M y) ∧
      (∀ j : Fin m, ι (b j) = algebraMap T' F' (rootG j)) := by
  intro K' T F T' F'
  let Ψ : T →+* T' := frobeniusRootRestrictedHom p e hr
  have hΨ_norm : ∀ f : T, ‖Ψ f‖ = ‖f‖ := norm_frobeniusRootRestrictedHom p e hr
  have hΨ_inj : Function.Injective Ψ := frobeniusRootRestrictedHom_injective p e hr
  let _ : Algebra F F' := (Ψ.gaussFractionFieldMap hΨ_inj).toAlgebra
  have hF_alg : algebraMap F F' = Ψ.gaussFractionFieldMap hΨ_inj := RingHom.algebraMap_toAlgebra _
  obtain ⟨m, b, rootG, ι₀, hι_alg, hι_b⟩ :=
    exists_algHom_gaussFractionField_frobeniusRoot_of_isPurelyInseparable M p e he hr_def hr
  refine ⟨Ψ, m, b, rootG, ι₀.toRingHom, frobeniusRootRestrictedHom_apply p e hr, hΨ_norm,
    hι_alg, fun y ↦ ?_, hι_b⟩
  obtain ⟨k, a, ha⟩ := IsPurelyInseparable.pow_mem F p y
  have hpk : p ^ k ≠ 0 := (pow_pos (expChar_pos K p) k).ne'
  refine (pow_left_inj₀ (norm_nonneg _) (spectralNorm_nonneg _) hpk).mp ?_
  have hι_pow : (ι₀ y) ^ p ^ k = Ψ.gaussFractionFieldMap hΨ_inj a := by
    rw [← map_pow, ← ha, AlgHom.commutes, hF_alg]
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← norm_pow, hι_pow,
    Ψ.norm_gaussFractionFieldMap hΨ_inj hΨ_norm,
    TauCeti.spectralNorm_pow_eq_norm_of_pow_eq_algebraMap hpk ha.symm]

private theorem exists_sum_mul_ne_zero_of_sum_ne_zero
    {σ K K' : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [NormedField K'] [IsUltrametricDist K'] [NormedAlgebra K K']
    {c r : σ → ℝ} [∀ i, Fact (0 < c i)] [∀ i, Fact (0 < r i)] {q : ℕ} (hq : q ≠ 0)
    (hr : ∀ i, r i ^ q = c i) (h_iso : ∀ a : K, ‖algebraMap K K' a‖ ≤ 1 * ‖a‖)
    {Ψ : IsRestricted.subring (R := K) c →+* IsRestricted.subring (R := K') r}
    (hΨ_def : ∀ f, Ψ f = restrictedExpand q hq hr (restrictedMap (algebraMap K K') h_iso f))
    {m : ℕ} {rootG : Fin m → IsRestricted.subring (R := K') r} {E : Submodule K K'}
    [SeparatingDual K E]
    (hrootG_mem : ∀ (j : Fin m) (α : σ →₀ ℕ),
      coeff α (rootG j : _root_.MvPowerSeries σ K') ∈ E)
    {a₀ : Fin m → IsRestricted.subring (R := K) c} (ha₀ : ∑ j, Ψ (a₀ j) * rootG j ≠ 0) :
    ∃ (g : Fin m → IsRestricted.subring (R := K) c) (C_π : ℝ),
      (∀ a : Fin m → IsRestricted.subring (R := K) c,
        ‖∑ j, a j * g j‖ ≤ C_π * ‖∑ j, Ψ (a j) * rootG j‖) ∧
      ∑ j, a₀ j * g j ≠ 0 := by
  let T := IsRestricted.subring (R := K) c
  have hterm_mem (a : Fin m → T) (j : Fin m) (α : σ →₀ ℕ) :
      coeff α ((Ψ (a j) * rootG j : IsRestricted.subring (R := K') r) :
        _root_.MvPowerSeries σ K') ∈ E := by
    rw [hΨ_def]
    exact coeff_restrictedExpand_restrictedMap_mul_mem hq hr h_iso E (a j) (hrootG_mem j) α
  have hsum_mem (s : Finset (Fin m)) (a : Fin m → T) (α : σ →₀ ℕ) :
      coeff α ((∑ j ∈ s, Ψ (a j) * rootG j : IsRestricted.subring (R := K') r) :
        _root_.MvPowerSeries σ K') ∈ E := by
    rw [AddSubmonoidClass.coe_finsetSum, map_sum]
    exact E.sum_mem fun j _ ↦ hterm_mem a j α
  obtain ⟨ν, hν, f_dual, hf_ne⟩ :=
    exists_toSubringDual_restrictedExpandComponentFamily_ne_zero hq hr E ha₀
      (hsum_mem Finset.univ a₀)
  let wE (j : Fin m) := restrictedExpandComponentFamily hq hr ν E (rootG j) (hrootG_mem j)
  have hcomp_sum (s : Finset (Fin m)) (a : Fin m → T) :
      restrictedExpandComponentFamily hq hr ν E (∑ j ∈ s, Ψ (a j) * rootG j) (hsum_mem s a) =
        ∑ j ∈ s, a j • wE j := by
    rw [restrictedExpandComponentFamily_sum hq hr ν E s _ (hterm_mem a)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← restrictedExpandComponentFamily_restrictedExpand_mul hq hr hν h_iso E (a j) (rootG j)
        (hrootG_mem j) (hz_mul := coeff_restrictedExpand_restrictedMap_mul_mem hq hr h_iso E
          (a j) (hrootG_mem j))]
    exact restrictedExpandComponentFamily_congr hq hr ν E
      (congrArg (· * rootG j) (hΨ_def (a j)))
  let π := IsRestrictedFamily.toSubringDual (c := c) f_dual
  have hπ_sum (a : Fin m → T) :
      ∑ j, a j * π (wE j) =
        π (restrictedExpandComponentFamily hq hr ν E (∑ j, Ψ (a j) * rootG j)
          (hsum_mem Finset.univ a)) := by
    rw [hcomp_sum Finset.univ a, map_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [map_smul, smul_eq_mul]
  refine ⟨fun j ↦ π (wE j), ‖f_dual‖ / ν.prod (r · ^ ·), fun a ↦ ?_, fun h0 ↦ ?_⟩
  · rw [hπ_sum a]
    exact norm_toSubringDual_restrictedExpandComponentFamily_le hq hr ν E f_dual _ _
  · exact hf_ne (by rwa [← hπ_sum a₀])

end Helpers

/-- **Characteristic-free weak stability of Gauss-normed Tate fraction fields.**
For any complete nontrivially normed ultrametric field `K` (of arbitrary characteristic), countable
variable type `σ`, and positive polyradius `c : σ → ℝ`, the Gauss-normed fraction field
`GaussFractionField σ K c` is weakly stable ([bosch-guntzer-remmert], §5.3.1, Theorem 1). -/
theorem isWeaklyStable_gaussFractionField (σ K : Type*) [Countable σ]
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
  have hr (i : σ) : r i ^ q = c i := by
    dsimp only [r]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Fact.out : 0 < c i).le, inv_mul_cancel₀ hqR_ne,
      Real.rpow_one]
  let T' := IsRestricted.subring (R := K') r
  let F' := GaussFractionField σ K' r
  have h_iso (a : K) : ‖algebraMap K K' a‖ ≤ 1 * ‖a‖ := by
    rw [one_mul, FrobeniusRoot.norm_algebraMap]
  obtain ⟨Ψ, m, b, rootG, ι, hΨ_def, hΨ_norm, hι_alg, hι_norm, hι_b⟩ :=
    exists_isometric_ringHom_of_isPurelyInseparable M p e le_rfl (fun _ ↦ rfl) hr h_iso
  -- Step 3: Span a countable-type `K`-subspace `E ⊆ K'` from all coefficients of `rootG`.
  obtain ⟨E, _, hrootG_mem⟩ : ∃ E : Submodule K K', SeparatingDual K E ∧
      ∀ (j : Fin m) (α : σ →₀ ℕ), coeff α (rootG j : _root_.MvPowerSeries σ K') ∈ E :=
    ⟨Submodule.span K (Set.range fun idx : Fin m × (σ →₀ ℕ) ↦
        coeff idx.2 (rootG idx.1 : _root_.MvPowerSeries σ K')),
      Submodule.separatingDual_span_of_countable (Set.countable_range _),
      fun j α ↦ Submodule.subset_span ⟨(j, α), rfl⟩⟩
  -- Step 4: Construct separating spectrally bounded `F`-linear functionals on `M`.
  refine Module.Dual.exists_bound_of_forall_exists_ne_zero ψ (spectralNorm F M) fun x₀ hx₀ ↦ ?_
  obtain ⟨s₀, hs₀⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors T) (b.repr x₀)
  choose a₀ ha₀ using hs₀
  have hs₀_F_ne : algebraMap T' F' (Ψ s₀) ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_algebraMap_gaussFractionField, hΨ_norm, norm_ne_zero_iff]
    exact nonZeroDivisors.ne_zero s₀.2
  have hu₀_ne : ∑ j, Ψ (a₀ j) * rootG j ≠ 0 := fun h0 ↦ by
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
        = ‖algebraMap T F s * φ y‖ := by rw [norm_mul, norm_algebraMap_gaussFractionField σ K c _]
      _ = ‖∑ j, a j * g j‖ := by rw [hφ_clear y s a ha, norm_algebraMap_gaussFractionField σ K c _]
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

/-- In any characteristic (including `2`), `Y ^ 2 + Xᵢ ^ 2 * Y + Xᵢ` defines a degree-`2` separable
extension of `GaussFractionField σ K c` on which `spectralNorm` is equivalent to the power-basis
coordinate norm. -/
example (σ : Type u₁) (K : Type u₂) [Countable σ] [Nonempty σ]
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
  let X₀ : T := ⟨X i₀, isRestricted_X c i₀⟩
  let x₀ : F := algebraMap T F X₀
  have hx₀_ne : x₀ ≠ 0 := by
    rw [← norm_pos_iff, norm_algebraMap_gaussFractionField_X]; exact Fact.out
  let P : Polynomial F := Polynomial.X ^ 2 + Polynomial.C (x₀ ^ 2) * Polynomial.X + Polynomial.C x₀
  have hP_deg : P.natDegree = 2 := by dsimp only [P]; compute_degree!
  have hP_monic : P.Monic := by dsimp only [P]; monicity!
  have hP_irr : Irreducible P :=
    Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hP_deg]; decide)
      (not_isRoot_X_sq_add_C_sq_mul_X_add_C σ K c i₀)
  have hP_sep : P.Separable := by
    rw [Polynomial.separable_iff_derivative_ne_zero hP_irr]
    exact fun hderiv ↦ hx₀_ne (by simpa [P] using congrArg (Polynomial.eval 0) hderiv)
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_root (P.map (algebraMap F (AlgebraicClosure F)))
    (by rw [Polynomial.degree_map_eq_of_injective (algebraMap F _).injective,
          Polynomial.degree_eq_natDegree hP_monic.ne_zero, hP_deg]; decide)
  have hβ_aeval : Polynomial.aeval β P = 0 := by rwa [Polynomial.aeval_def, ← Polynomial.eval_map]
  have hmin : minpoly F β = P := (minpoly.eq_of_irreducible_of_monic hP_irr hβ_aeval hP_monic).symm
  have hβ_int : IsIntegral F β := ⟨P, hP_monic, hβ_aeval⟩
  have hβ_sep : IsSeparable F β := by rwa [IsSeparable, hmin]
  let L := F⟮β⟯
  have : Algebra.IsSeparable F L :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable F (AlgebraicClosure F)).mpr hβ_sep
  have hfin : Module.finrank F L = 2 := by
    rw [IntermediateField.adjoin.finrank hβ_int, hmin, hP_deg]
  let pb := IntermediateField.adjoin.powerBasis hβ_int
  have : NeZero pb.dim := ⟨by rw [IntermediateField.adjoin.powerBasis_dim, hmin, hP_deg]; decide⟩
  obtain ⟨C, D, hC, hD, hCD⟩ :=
    (isWeaklyStable_gaussFractionField σ K c).exists_basis_norm_comparison pb.basis
  exact ⟨L, inferInstance, inferInstance, IntermediateField.adjoin.finiteDimensional hβ_int,
    inferInstance, pb.dim, inferInstance, pb.basis, hfin, C, D, hC, hD, hCD⟩

/-- In prime characteristic `p`, adjoining a `p`-th root of a coordinate variable `Xᵢ` produces a
nontrivial finite purely inseparable extension of `GaussFractionField σ K c` on which `spectralNorm`
is equivalent to the power-basis coordinate norm. -/
example (σ : Type u₁) (K : Type u₂) [Countable σ] [Nonempty σ]
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
  let X₀ : T := ⟨X i₀, isRestricted_X c i₀⟩
  let x₀ : F := algebraMap T F X₀
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap F (AlgebraicClosure F) x₀) hp.pos
  have hα_int : IsIntegral F α :=
    ⟨Polynomial.X ^ p - Polynomial.C x₀, Polynomial.monic_X_pow_sub_C x₀ hp.ne_zero, by simp [hα]⟩
  let M := F⟮α⟯
  have : IsPurelyInseparable F M := by
    rw [← le_perfectClosure_iff, IntermediateField.adjoin_le_iff, Set.singleton_subset_iff,
      SetLike.mem_coe, mem_perfectClosure_iff_pow_mem p]
    exact ⟨1, x₀, by rw [pow_one, hα]⟩
  have : FiniteDimensional F M := IntermediateField.adjoin.finiteDimensional hα_int
  have hfin_gt : 1 < Module.finrank F M := by
    by_contra! hle
    obtain ⟨z, hz⟩ := IntermediateField.mem_bot.mp
      (IntermediateField.finrank_adjoin_simple_eq_one_iff.mp (le_antisymm hle Module.finrank_pos))
    exact pow_ne_algebraMap_gaussFractionField_X σ K c i₀ hp.ne_one z
      ((algebraMap F (AlgebraicClosure F)).injective (by rw [map_pow, hz, hα]))
  let pb := IntermediateField.adjoin.powerBasis hα_int
  have : NeZero pb.dim := ⟨by
    rw [IntermediateField.adjoin.powerBasis_dim, ← IntermediateField.adjoin.finrank hα_int]
    exact (zero_lt_one.trans hfin_gt).ne'⟩
  obtain ⟨C, D, hC, hD, hCD⟩ :=
    (isWeaklyStable_gaussFractionField σ K c).exists_basis_norm_comparison pb.basis
  exact ⟨M, inferInstance, inferInstance, inferInstance, inferInstance,
    pb.dim, inferInstance, pb.basis, hfin_gt, C, D, hC, hD, hCD⟩

end Examples

end TauCeti.MvPowerSeries
