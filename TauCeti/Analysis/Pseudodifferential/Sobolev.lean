/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Quantization
public import TauCeti.Analysis.Pseudodifferential.Symbol.Basic
public import TauCeti.Analysis.Pseudodifferential.Symbol.Topology
public import TauCeti.Analysis.Sobolev.BesselPotential.Postcomp
import TauCeti.Analysis.Distribution.SchwartzSpace.Fourier
import TauCeti.Analysis.Distribution.TemperedDistribution.Lp
import TauCeti.Analysis.Fourier.Continuous
import TauCeti.Analysis.Fourier.Parametric
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Peetre
import TauCeti.MeasureTheory.Integral.SchurTest

/-!
# Sobolev mapping of pseudodifferential operators with compact spatial support

Let `a` be a symbol of order `m` on `ℝⁿ` (`TauCeti.Symbol n V W m`) that vanishes for positions
outside a compact set, with values in operators between complex Hilbert spaces `V` and `W`. Its
left quantization `Op(a)`, defined on Schwartz functions by `TauCeti.quantizeSchwartzValue`, extends
to a bounded operator `H^s(ℝⁿ; V) → H^{s - m}(ℝⁿ; W)` between Mathlib's Bessel-potential spaces,
for every real `s` (`TauCeti.Symbol.quantizeSobolev`). The order `m` of the symbol is thus the
number of derivatives `Op(a)` loses.

The same holds for finite-dimensional complex normed `V` and `W`, whose norms need not come from
inner products (`TauCeti.Symbol.exists_quantizeSobolev`): isomorphisms with `ℂ^k` and `ℂ^l`
induce isomorphisms of the Bessel-potential spaces (`BesselPotentialSpace.postcomp`) and
conjugate `a` to a symbol between Hilbert spaces (`TauCeti.Symbol.map`).

## The Fourier argument

For a fixed frequency `ξ`, the position slice `x ↦ a(x, ξ)` is smooth with support in a fixed
compact set, so its Fourier transform `â(η, ξ)` decays rapidly in `η`; the symbol estimates in
the position give, for every `N`,
`(1 + ‖η‖) ^ N ‖â(η, ξ)‖ ≤ C_N ⟨ξ⟩ ^ m`
(`TauCeti.Symbol.HasCompactSpatialSupport.exists_one_add_norm_pow_mul_norm_fourier_le`), where
`⟨ξ⟩ = (1 + ‖ξ‖ ^ 2) ^ (1 / 2)`. Taking the Fourier transform of
`Op(a) u (x) = ∫ exp(2πi ⟪ζ, x⟫) a(x, 2πζ) (𝓕 u ζ) dζ` in `x` gives the convolution-type formula
`𝓕 (Op(a) u) ξ = ∫ â(ξ - ζ, 2πζ) (𝓕 u ζ) dζ`
(`TauCeti.Symbol.HasCompactSpatialSupport.fourier_quantizeSchwartzValue`). Peetre's inequality
`⟨ξ⟩ ^ (s - m) ≤ 2 ^ (|s - m| / 2) ⟨ξ - ζ⟩ ^ |s - m| ⟨ζ⟩ ^ (s - m)` turns this into the bound
`⟨ξ⟩ ^ (s - m) ‖𝓕 (Op(a) u) ξ‖ ≤ C ∫ k(ξ - ζ) ⟨ζ⟩ ^ s ‖𝓕 u ζ‖ dζ` with an integrable kernel
`k(η) = (1 + ‖η‖) ^ (|s - m| - N)`, `N > n + |s - m|`, and Schur's test bounds the right side in
`L²`
(`TauCeti.Symbol.HasCompactSpatialSupport.exists_eLpNorm_smul_fourier_quantizeSchwartzValue_le`).
Since the `H^s` norm is the `L²` norm of `⟨ξ⟩ ^ s 𝓕 u`, this is the estimate
`‖Op(a) u‖_{H^{s-m}} ≤ C ‖u‖_{H^s}` on Schwartz functions, and density of Schwartz functions in
`H^s` gives the bounded extension.

## Continuity in the symbol

The constants above depend on `a` only through finitely many of its seminorms
`p_{K,α,[]}(a)` (`TauCeti.Symbol.seminorm`) on a compact set `K` outside which `a` vanishes, and
only through position derivatives: the decay of `â` comes from Schwartz seminorms of the position
slices, which these seminorms bound, and the rest of the argument is linear in the decay constant.
So for a fixed `K` there are finitely many words `α` and a constant `C` with
`‖Op(a)‖_{H^s → H^{s-m}} ≤ C max_α p_{K,α,[]}(a)` for every symbol `a` vanishing outside `K`
(`TauCeti.Symbol.exists_norm_quantizeSobolev_le_seminorm`). Since `Op(a)` is linear in `a`
(`TauCeti.Symbol.quantizeSobolev_add`, `TauCeti.Symbol.quantizeSobolev_smul`), a family
`t ↦ aₜ` of such symbols that is continuous in the symbol topology quantizes to a family of
operators continuous in the operator norm (`Continuous.symbol_quantizeSobolev`). This is
the continuity used to deform elliptic operators within a fixed Sobolev scale, for instance along
homotopies of symbols.

## Main declarations

* `TauCeti.Symbol.HasCompactSpatialSupport.exists_one_add_norm_pow_mul_norm_fourier_le`,
  `TauCeti.Symbol.HasCompactSpatialSupport.exists_norm_fourier_slice_le`: rapid decay of the
  Fourier transform in the position.
* `TauCeti.Symbol.exists_one_add_norm_pow_mul_norm_fourier_le_seminorm`: rapid decay with a
  constant bounded by symbol seminorms on a fixed compact set.
* Further facts about the Fourier transform `â(η, ξ)` of the position slices: linearity in `a`
  (`TauCeti.Symbol.HasCompactSpatialSupport.fourier_slice_add`,
  `TauCeti.Symbol.HasCompactSpatialSupport.fourier_slice_smul`), integrability in `η` and Fourier
  inversion (`TauCeti.Symbol.HasCompactSpatialSupport.integrable_fourier_slice`,
  `TauCeti.Symbol.HasCompactSpatialSupport.fourierInv_fourier_slice`), joint continuity
  (`TauCeti.Symbol.HasCompactSpatialSupport.continuous_fourier_slice`), differentiability in `ξ`
  with the Fourier transform of `∂_ξ a` as derivative
  (`TauCeti.Symbol.HasCompactSpatialSupport.hasFDerivAt_fourier_slice`,
  `TauCeti.Symbol.HasCompactSpatialSupport.coordinateDeriv_fourier_slice`), and
  `(∂_{x_j} a)^(η, ξ) = 2πi ηⱼ â(η, ξ)`
  (`TauCeti.Symbol.HasCompactSpatialSupport.fourier_spatialDeriv_slice`).
* `TauCeti.Symbol.HasCompactSpatialSupport.fourier_quantizeSchwartzValue`: the Fourier transform
  of `Op(a) u`.
* `TauCeti.Symbol.HasCompactSpatialSupport.exists_eLpNorm_smul_fourier_quantizeSchwartzValue_le`:
  the Sobolev estimate on Schwartz functions, on the Fourier side.
* `TauCeti.Symbol.exists_eLpNorm_smul_fourier_quantizeSchwartzValue_le_seminorm`: the same
  estimate with a constant bounded by symbol seminorms on a fixed compact set.
* `TauCeti.Symbol.quantizeSobolev`: the bounded operator `H^s → H^{s - m}`, with
  `TauCeti.Symbol.toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply` identifying its values
  on Schwartz functions.
* `TauCeti.Symbol.quantizeSobolev_add`, `TauCeti.Symbol.quantizeSobolev_smul`,
  `TauCeti.Symbol.quantizeSobolev_sub`: linearity in the symbol.
* `TauCeti.Symbol.exists_norm_quantizeSobolev_le_seminorm`: the operator norm of `Op(a)` is
  bounded by finitely many symbol seminorms on a fixed compact set.
* `Continuous.symbol_quantizeSobolev`: continuity in the operator norm of the
  quantizations of a continuous family of symbols vanishing outside a common compact set.
* `TauCeti.Symbol.toDistr_postcomp_comp_comp_postcomp_toBesselPotentialSpaceCLM_apply`: Sobolev
  extensions of quantizations are compatible with isomorphisms of the fibres.
* `TauCeti.Symbol.exists_quantizeSobolev`: the mapping property for finite-dimensional normed
  `V` and `W`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (3.31).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.13.
-/

public section

noncomputable section

open MeasureTheory Real FourierTransform TemperedDistribution
open TopologicalSpace (Compacts)
open scoped ENNReal NNReal SchwartzMap BesselPotentialSpace RealInnerProductSpace ContDiff
  LineDeriv

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ}

section Decay

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {a : Symbol n V W m}

/-! ### Rapid decay of the Fourier transform in the position -/

/-- The position slice `y ↦ a(y, ξ)` of a symbol with compact spatial support, as a Schwartz
function. -/
def HasCompactSpatialSupport.sliceSchwartz (ha : a.HasCompactSpatialSupport)
    (ξ : CoordinateSpace n) : 𝓢(CoordinateSpace n, V →L[ℂ] W) :=
  (ha.hasCompactSupport_slice ξ).toSchwartzMap (a.contDiff_coefficient_slice ξ)

@[simp]
theorem HasCompactSpatialSupport.coe_sliceSchwartz (ha : a.HasCompactSpatialSupport)
    (ξ : CoordinateSpace n) : ⇑(ha.sliceSchwartz ξ) = fun y ↦ a.coefficient (y, ξ) :=
  funext (HasCompactSupport.toSchwartzMap_toFun _ _)

/-- The Fourier transform of the Schwartz slice is the Fourier transform of the position slice. -/
theorem HasCompactSpatialSupport.fourier_sliceSchwartz (ha : a.HasCompactSpatialSupport)
    (ξ η : CoordinateSpace n) :
    𝓕 (ha.sliceSchwartz ξ) η = 𝓕 (fun y ↦ a.coefficient (y, ξ)) η := by
  rw [SchwartzMap.fourier_coe, ha.coe_sliceSchwartz]

/-- The Fourier transform of the position slice is additive in the symbol. -/
theorem HasCompactSpatialSupport.fourier_slice_add {b : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) (hb : b.HasCompactSpatialSupport) (ξ η : CoordinateSpace n) :
    𝓕 (fun y ↦ (a + b).coefficient (y, ξ)) η =
      𝓕 (fun y ↦ a.coefficient (y, ξ)) η + 𝓕 (fun y ↦ b.coefficient (y, ξ)) η := by
  have h : (ha.add hb).sliceSchwartz ξ = ha.sliceSchwartz ξ + hb.sliceSchwartz ξ := by
    ext y
    simp
  rw [← (ha.add hb).fourier_sliceSchwartz, h, FourierTransform.fourier_add, add_apply,
    ha.fourier_sliceSchwartz, hb.fourier_sliceSchwartz]

/-- The Fourier transform of the position slice is homogeneous in the symbol. -/
theorem HasCompactSpatialSupport.fourier_slice_smul (ha : a.HasCompactSpatialSupport) (c : ℂ)
    (ξ η : CoordinateSpace n) :
    𝓕 (fun y ↦ (c • a).coefficient (y, ξ)) η = c • 𝓕 (fun y ↦ a.coefficient (y, ξ)) η := by
  have h : (ha.smul c).sliceSchwartz ξ = c • ha.sliceSchwartz ξ := by
    ext y
    simp
  rw [← (ha.smul c).fourier_sliceSchwartz, h, FourierTransform.fourier_smul,
    ← ha.fourier_sliceSchwartz]
  rfl

/-- The Fourier transform `η ↦ â(η, ξ)` of each position slice is integrable. -/
theorem HasCompactSpatialSupport.integrable_fourier_slice (ha : a.HasCompactSpatialSupport)
    (ξ : CoordinateSpace n) : Integrable (𝓕 fun y ↦ a.coefficient (y, ξ)) := by
  rw [← ha.coe_sliceSchwartz, ← SchwartzMap.fourier_coe]
  exact (𝓕 (ha.sliceSchwartz ξ)).integrable

/-- **Fourier inversion for the position slices**: `a(x, ξ) = ∫ exp(2πi ⟪η, x⟫) â(η, ξ) dη`. -/
theorem HasCompactSpatialSupport.fourierInv_fourier_slice [CompleteSpace W]
    (ha : a.HasCompactSpatialSupport) (ξ : CoordinateSpace n) :
    𝓕⁻ (𝓕 fun y ↦ a.coefficient (y, ξ)) = fun y ↦ a.coefficient (y, ξ) := by
  rw [← ha.coe_sliceSchwartz, ← SchwartzMap.fourier_coe, ← SchwartzMap.fourierInv_coe,
    fourierInv_fourier_eq]

/-- The Schwartz seminorms of the position slices of a symbol vanishing at positions outside a
compact set `K ⊆ closedBall 0 R` are bounded by its seminorms on `K` without frequency derivatives:
`‖a(·, ξ)‖_{k,l} ≤ R ^ k (∑_{|α| = l} p_{K,α,[]}(a)) ⟨ξ⟩ ^ m`. -/
private theorem HasCompactSpatialSupport.seminorm_sliceSchwartz_le
    (ha : a.HasCompactSpatialSupport) {K : Compacts (CoordinateSpace n)}
    (haK : ∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) (k l : ℕ) (ξ : CoordinateSpace n) :
    SchwartzMap.seminorm ℂ k l (ha.sliceSchwartz ξ) ≤
      R ^ k * (∑ r : Fin l → Fin n, Symbol.seminorm K (List.ofFn r) [] a) *
        (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  have hD : 0 ≤ R ^ k * ∑ r : Fin l → Fin n, Symbol.seminorm K (List.ofFn r) [] a :=
    mul_nonneg (pow_nonneg hR0 _) (Finset.sum_nonneg fun r _ ↦ apply_nonneg _ _)
  refine SchwartzMap.seminorm_le_bound ℂ k l _ (mul_nonneg hD (by positivity)) fun x ↦ ?_
  rw [ha.coe_sliceSchwartz]
  by_cases hx : x ∈ K
  · calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ l (fun y ↦ a.coefficient (y, ξ)) x‖
        ≤ R ^ k * ∑ r : Fin l → Fin n,
            Symbol.seminorm K (List.ofFn r) [] a * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
          gcongr
          · exact hR x hx
          refine (norm_iteratedFDeriv_le_sum_coordinateDeriv
            ((a.contDiff_coefficient_slice ξ).of_le (mod_cast le_top)) x).trans
              (Finset.sum_le_sum fun r _ ↦ ?_)
          simpa [mixedDeriv_def, coordinateDeriv_nil] using
            le_seminorm K (List.ofFn r) [] a hx ξ
      _ = _ := by rw [← Finset.sum_mul, mul_assoc]
  · -- Outside `K` the slice vanishes near `x`, so all its derivatives vanish at `x`.
    have hsupp : Function.support (fun y ↦ a.coefficient (y, ξ)) ⊆ K := fun y hy ↦
      by_contra fun h ↦ hy (haK y h ξ)
    have hzero : iteratedFDeriv ℝ l (fun y ↦ a.coefficient (y, ξ)) x = 0 :=
      Function.notMem_support.mp fun hmem ↦
        hx (closure_minimal hsupp K.isCompact.isClosed (support_iteratedFDeriv_subset l hmem))
    rw [hzero, norm_zero, mul_zero]
    positivity

/-- Finite suprema of Schwartz seminorms of the position slices of a symbol vanishing outside `K`
are bounded by a finite supremum of its seminorms `p_{K,α,[]}`, once the words `α` cover all
derivative orders that occur. -/
private theorem HasCompactSpatialSupport.finset_sup_seminorm_sliceSchwartz_le
    (ha : a.HasCompactSpatialSupport) {K : Compacts (CoordinateSpace n)}
    (haK : ∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ x ∈ K, ‖x‖ ≤ R) {s : Finset (ℕ × ℕ)} {S : Finset (List (Fin n))}
    (hS : ∀ i ∈ s, ∀ r : Fin i.2 → Fin n, List.ofFn r ∈ S) (ξ : CoordinateSpace n) :
    (s.sup (schwartzSeminormFamily ℂ _ _)) (ha.sliceSchwartz ξ) ≤
      (∑ i ∈ s, R ^ i.1 * (n : ℝ) ^ i.2) * (S.sup fun α ↦ Symbol.seminorm K α []) a *
        (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  set q : ℝ := (S.sup fun α ↦ Symbol.seminorm K α []) a
  have hq0 : 0 ≤ q := apply_nonneg _ _
  refine Seminorm.finset_sup_apply_le (by positivity) fun i hi ↦
    (ha.seminorm_sliceSchwartz_le haK hR0 hR i.1 i.2 ξ).trans ?_
  -- Each of the `n ^ l` seminorms `p_{K,α,[]}(a)` with `|α| = l` is at most `q`.
  have hsum : ∑ r : Fin i.2 → Fin n, Symbol.seminorm K (List.ofFn r) [] a ≤ (n : ℝ) ^ i.2 * q :=
    calc ∑ r : Fin i.2 → Fin n, Symbol.seminorm K (List.ofFn r) [] a
        ≤ ∑ _r : Fin i.2 → Fin n, q := Finset.sum_le_sum fun r _ ↦
          Seminorm.le_finset_sup_apply (p := fun α ↦ Symbol.seminorm K α []) (hS i hi r)
      _ = (n : ℝ) ^ i.2 * q := by simp
  calc R ^ i.1 * (∑ r : Fin i.2 → Fin n, Symbol.seminorm K (List.ofFn r) [] a) *
        (1 + ‖ξ‖ ^ 2) ^ (m / 2)
      ≤ R ^ i.1 * ((n : ℝ) ^ i.2 * q) * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by gcongr
    _ = R ^ i.1 * (n : ℝ) ^ i.2 * q * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by ring
    _ ≤ (∑ i ∈ s, R ^ i.1 * (n : ℝ) ^ i.2) * q * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
        gcongr
        exact Finset.single_le_sum (f := fun i : ℕ × ℕ ↦ R ^ i.1 * (n : ℝ) ^ i.2)
          (fun j _ ↦ by positivity) hi

variable (V W m) in
/-- **Rapid decay of the Fourier transform in the position, uniformly in the symbol.** For a
compact set `K` and every `N`, there are finitely many words `α` and a constant `C` such that every
symbol `a` of order `m` vanishing at positions outside `K` satisfies
`(1 + ‖η‖) ^ N ‖â(η, ξ)‖ ≤ C max_α p_{K,α,[]}(a) ⟨ξ⟩ ^ m`, where `â(η, ξ)` is the Fourier transform
of the position slice `x ↦ a(x, ξ)`. Only the position derivatives of `a` enter. -/
theorem exists_one_add_norm_pow_mul_norm_fourier_le_seminorm (K : Compacts (CoordinateSpace n))
    (N : ℕ) :
    ∃ (S : Finset (List (Fin n))) (C : ℝ), 0 ≤ C ∧ ∀ a : Symbol n V W m,
      (∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0) → ∀ η ξ : CoordinateSpace n,
        (1 + ‖η‖) ^ N * ‖𝓕 (fun x ↦ a.coefficient (x, ξ)) η‖ ≤
          C * (S.sup fun α ↦ Symbol.seminorm K α []) a * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  obtain ⟨R, hR⟩ := K.isCompact.isBounded.subset_closedBall 0
  have hR' (x : CoordinateSpace n) (hx : x ∈ K) : ‖x‖ ≤ max R 0 :=
    (mem_closedBall_zero_iff.mp (hR hx)).trans (le_max_left _ _)
  -- The Fourier transform is continuous on Schwartz space, so the seminorm controlling
  -- `(1 + ‖η‖) ^ N ‖𝓕 g η‖` is bounded by finitely many Schwartz seminorms of `g`.
  have hq : Continuous
      (((Finset.Iic (N, 0)).sup (schwartzSeminormFamily ℂ (CoordinateSpace n) (V →L[ℂ] W))).comp
        (fourierCLM ℂ 𝓢(CoordinateSpace n, V →L[ℂ] W)).toLinearMap) :=
    ((schwartz_withSeminorms ℂ _ _).continuous_finsetSup_seminorm _).comp
      (fourierCLM ℂ _).continuous
  obtain ⟨s, c, -, hc⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ _ _) _ hq
  -- The words whose seminorms bound the Schwartz seminorms in `s` of the position slices.
  let S : Finset (List (Fin n)) :=
    s.biUnion fun i ↦ Finset.univ.image (List.ofFn : (Fin i.2 → Fin n) → List (Fin n))
  have hS (i : ℕ × ℕ) (hi : i ∈ s) (r : Fin i.2 → Fin n) : List.ofFn r ∈ S :=
    Finset.mem_biUnion.2 ⟨i, hi, Finset.mem_image_of_mem _ (Finset.mem_univ r)⟩
  set D : ℝ := ∑ i ∈ s, max R 0 ^ i.1 * (n : ℝ) ^ i.2
  have hD : 0 ≤ D := Finset.sum_nonneg fun i _ ↦ by positivity
  refine ⟨S, 2 ^ N * c * D, by positivity, fun a haK η ξ ↦ ?_⟩
  have ha : a.HasCompactSpatialSupport := hasCompactSpatialSupport_iff.2 ⟨K, K.isCompact, haK⟩
  have hcs := hc (ha.sliceSchwartz ξ)
  simp only [Seminorm.comp_apply, ContinuousLinearMap.coe_coe, fourierCLM_apply,
    smul_apply, NNReal.smul_def, smul_eq_mul] at hcs
  calc (1 + ‖η‖) ^ N * ‖𝓕 (fun x ↦ a.coefficient (x, ξ)) η‖
      = (1 + ‖η‖) ^ N *
          ‖iteratedFDeriv ℝ 0 (𝓕 (ha.sliceSchwartz ξ) : 𝓢(CoordinateSpace n, V →L[ℂ] W)) η‖ := by
        rw [norm_iteratedFDeriv_zero, ha.fourier_sliceSchwartz]
    _ ≤ 2 ^ N * ((Finset.Iic (N, 0)).sup fun i ↦ SchwartzMap.seminorm ℂ i.1 i.2)
          (𝓕 (ha.sliceSchwartz ξ) : 𝓢(CoordinateSpace n, V →L[ℂ] W)) :=
        SchwartzMap.one_add_le_sup_seminorm_apply (m := (N, 0)) le_rfl le_rfl _ _
    _ ≤ 2 ^ N * (c * (D * (S.sup fun α ↦ Symbol.seminorm K α []) a * (1 + ‖ξ‖ ^ 2) ^ (m / 2))) := by
        gcongr
        exact hcs.trans (by
          gcongr
          exact ha.finset_sup_seminorm_sliceSchwartz_le haK (le_max_right _ _) hR' hS ξ)
    _ = 2 ^ N * c * D * (S.sup fun α ↦ Symbol.seminorm K α []) a * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
        ring

/-- **Rapid decay of the Fourier transform in the position.** For a symbol `a` of order `m` with
compact spatial support and every `N`, the Fourier transform `â(η, ξ)` of the position slice
`x ↦ a(x, ξ)` satisfies `(1 + ‖η‖) ^ N ‖â(η, ξ)‖ ≤ C ⟨ξ⟩ ^ m`, uniformly in `η` and `ξ`. -/
theorem HasCompactSpatialSupport.exists_one_add_norm_pow_mul_norm_fourier_le
    (ha : a.HasCompactSpatialSupport) (N : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ η ξ : CoordinateSpace n,
      (1 + ‖η‖) ^ N * ‖𝓕 (fun x ↦ a.coefficient (x, ξ)) η‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.mp ha
  obtain ⟨S, C, hC, h⟩ := exists_one_add_norm_pow_mul_norm_fourier_le_seminorm m V W ⟨K, hK⟩ N
  exact ⟨C * (S.sup fun α ↦ Symbol.seminorm ⟨K, hK⟩ α []) a, mul_nonneg hC (apply_nonneg _ _),
    h a hKa⟩

/-- **Rapid decay.** For every `r`, the Fourier transform of the position slice satisfies
`‖â(η, ξ)‖ ≤ C ⟨ξ⟩ ^ m ⟨η⟩ ^ (-r)`. -/
theorem HasCompactSpatialSupport.exists_norm_fourier_slice_le (ha : a.HasCompactSpatialSupport)
    (r : ℝ) : ∃ C, 0 ≤ C ∧ ∀ η ξ : CoordinateSpace n,
      ‖𝓕 (fun y ↦ a.coefficient (y, ξ)) η‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) * (1 + ‖η‖ ^ 2) ^ (-r / 2) := by
  obtain ⟨C, hC0, hC⟩ := ha.exists_one_add_norm_pow_mul_norm_fourier_le ⌈r⌉₊
  refine ⟨C, hC0, fun η ξ ↦ ?_⟩
  -- `⟨η⟩ ^ r ≤ (1 + ‖η‖) ^ ⌈r⌉₊`
  have hw : (1 + ‖η‖ ^ 2) ^ (r / 2) ≤ (1 + ‖η‖) ^ ⌈r⌉₊ :=
    (Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖η‖])
      (by linarith [Nat.le_ceil r])).trans (one_add_norm_sq_rpow_le_one_add_norm_pow η ⌈r⌉₊)
  have hpos : 0 < (1 + ‖η‖ ^ 2) ^ (r / 2) := by positivity
  rw [show -r / 2 = -(r / 2) by ring, Real.rpow_neg (by positivity), ← div_eq_mul_inv,
    le_div_iff₀ hpos]
  calc ‖𝓕 (fun y ↦ a.coefficient (y, ξ)) η‖ * (1 + ‖η‖ ^ 2) ^ (r / 2)
      ≤ ‖𝓕 (fun y ↦ a.coefficient (y, ξ)) η‖ * (1 + ‖η‖) ^ ⌈r⌉₊ := by gcongr
    _ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (m / 2) := by rw [mul_comm]; exact hC η ξ

/-! ### Regularity of the Fourier transform in the position -/

/-- The Fourier transform `â(η, ξ)` of the position slice of a symbol with compact spatial support
is jointly continuous in `η` and `ξ`. -/
theorem HasCompactSpatialSupport.continuous_fourier_slice (ha : a.HasCompactSpatialSupport) :
    Continuous fun q : CoordinateSpace n × CoordinateSpace n ↦
      𝓕 (fun y ↦ a.coefficient (y, q.2)) q.1 := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.mp ha
  simpa only [Real.fourier_eq, Circle.smul_def] using
    continuous_integral_fourierChar_smul a.contDiff_coefficient.continuous hK hKa

/-- The Fourier transform in the position of the spatial derivative `∂_{x_j} a` is
`2πi ηⱼ â(η, ξ)`. -/
theorem HasCompactSpatialSupport.fourier_spatialDeriv_slice (ha : a.HasCompactSpatialSupport)
    (j : Fin n) (η ξ : CoordinateSpace n) :
    𝓕 (fun y ↦ (Symbol.spatialDeriv j a).coefficient (y, ξ)) η =
      ((2 * π * Complex.I) * ⟪η, EuclideanSpace.single j (1 : ℝ)⟫) •
        𝓕 (fun y ↦ a.coefficient (y, ξ)) η := by
  have hd : ⇑(∂_{EuclideanSpace.single j (1 : ℝ)} (ha.sliceSchwartz ξ) :
      𝓢(CoordinateSpace n, V →L[ℂ] W)) = fun y ↦ (Symbol.spatialDeriv j a).coefficient (y, ξ) := by
    funext y
    rw [SchwartzMap.lineDerivOp_apply, (ha.sliceSchwartz ξ).differentiableAt.lineDeriv_eq_fderiv,
      ha.coe_sliceSchwartz, fderiv_coefficient_single]
  rw [← hd, ← SchwartzMap.fourier_coe, SchwartzMap.fourier_lineDerivOp_apply,
    ha.fourier_sliceSchwartz]

/-- **Differentiation in the frequency.** The Fourier transform `â(η, ξ)` of the position slice
of a symbol with compact spatial support is differentiable in `ξ`, with the Fourier transform of
the frequency derivative as derivative. -/
theorem HasCompactSpatialSupport.hasFDerivAt_fourier_slice (ha : a.HasCompactSpatialSupport)
    (η ξ₀ : CoordinateSpace n) :
    HasFDerivAt (fun ξ ↦ 𝓕 (fun y ↦ a.coefficient (y, ξ)) η)
      (∫ y, (𝐞 (-⟪y, η⟫) : ℂ) • fderiv ℝ (fun ξ ↦ a.coefficient (y, ξ)) ξ₀) ξ₀ := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.mp ha
  simpa only [Real.fourier_eq, Circle.smul_def] using
    hasFDerivAt_integral_fourierChar_smul (a.contDiff_coefficient.of_le (by simp)) hK hKa η ξ₀

/-- The coordinate derivative `∂_{ξ_j} â(η, ξ)` is the Fourier transform of the position slice of
the frequency derivative `∂_{ξ_j} a`. -/
theorem HasCompactSpatialSupport.coordinateDeriv_fourier_slice (ha : a.HasCompactSpatialSupport)
    (j : Fin n) (η ξ : CoordinateSpace n) :
    coordinateDeriv [j] (fun ξ ↦ 𝓕 (fun y ↦ a.coefficient (y, ξ)) η) ξ =
      𝓕 (fun y ↦ (Symbol.frequencyDeriv j a).coefficient (y, ξ)) η := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.mp ha
  rw [coordinateDeriv_cons, coordinateDeriv_nil, (ha.hasFDerivAt_fourier_slice η ξ).fderiv,
    integral_fourierChar_smul_fderiv_apply (a.contDiff_coefficient.of_le (by simp)) hK hKa η ξ,
    Real.fourier_eq]
  simp only [Circle.smul_def, coefficient_frequencyDeriv, coordinateDeriv_cons,
    coordinateDeriv_nil]

end Decay

/-! ### The Fourier transform of the quantization -/

section Quantization

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {a : Symbol n V W m}

/-- The integrand of the double integral giving `𝓕 (Op(a) u) ξ` is integrable in the position
and the frequency: it is dominated by the indicator of the spatial support of `a` times an
integrable function of the frequency. -/
private theorem HasCompactSpatialSupport.integrable_fourierChar_smul_apply
    (ha : a.HasCompactSpatialSupport) (u : 𝓢(CoordinateSpace n, V)) (ξ : CoordinateSpace n) :
    Integrable (fun p : CoordinateSpace n × CoordinateSpace n ↦
      𝐞 (-⟪p.1, ξ - p.2⟫) • a.coefficient (p.1, (2 * π) • p.2) (𝓕 u p.2)) (volume.prod volume) := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.mp ha
  obtain ⟨C, hC0, hC⟩ := a.exists_bound_coefficient K hK
  have hFcont : Continuous fun p : CoordinateSpace n × CoordinateSpace n ↦
      𝐞 (-⟪p.1, ξ - p.2⟫) • a.coefficient (p.1, (2 * π) • p.2) (𝓕 u p.2) :=
    (Real.continuous_fourierChar.comp (by fun_prop)).smul
      ((a.contDiff_coefficient.continuous.comp (by fun_prop)).clm_apply
        ((𝓕 u).continuous.comp continuous_snd))
  have hK1 : Integrable (K.indicator fun _ ↦ (1 : ℝ)) :=
    (integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne)
  have hg : Integrable fun ζ : CoordinateSpace n ↦
      C * ((2 * π) ^ |m| * ((1 + ‖ζ‖ ^ 2) ^ (m / 2) * ‖𝓕 u ζ‖)) :=
    (((𝓕 u).integrable_one_add_norm_sq_rpow_mul_norm (m / 2)).const_mul _).const_mul _
  refine (hK1.mul_prod hg).mono' hFcont.aestronglyMeasurable (.of_forall fun p ↦ ?_)
  by_cases hx : p.1 ∈ K
  · rw [Set.indicator_of_mem hx, one_mul, Circle.norm_smul]
    refine ((a.coefficient _).le_opNorm _).trans ?_
    have hscale := one_add_norm_smul_sq_rpow_le (c := 2 * π) (by linarith [Real.two_le_pi]) m p.2
    calc ‖a.coefficient (p.1, (2 * π) • p.2)‖ * ‖𝓕 u p.2‖
        ≤ C * (1 + ‖(2 * π) • p.2‖ ^ 2) ^ (m / 2) * ‖𝓕 u p.2‖ := by
          gcongr
          exact hC _ hx _
      _ ≤ C * ((2 * π) ^ |m| * (1 + ‖p.2‖ ^ 2) ^ (m / 2)) * ‖𝓕 u p.2‖ := by gcongr
      _ = _ := by ring
  · rw [Set.indicator_of_notMem hx, zero_mul]
    simp [hKa p.1 hx]

/-- **The Fourier transform of the quantization.** For a symbol `a` with compact spatial support,
`𝓕 (Op(a) u) ξ = ∫ â(ξ - ζ, 2πζ) (𝓕 u ζ) dζ`, where `â(η, ξ)` is the Fourier transform of the
position slice `x ↦ a(x, ξ)` at `η`. -/
theorem HasCompactSpatialSupport.fourier_quantizeSchwartzValue (ha : a.HasCompactSpatialSupport)
    (u : 𝓢(CoordinateSpace n, V)) (ξ : CoordinateSpace n) :
    𝓕 (quantizeSchwartzValue a.coefficient u) ξ =
      ∫ ζ, 𝓕 (fun x ↦ a.coefficient (x, (2 * π) • ζ)) (ξ - ζ) (𝓕 u ζ) := by
  obtain ⟨K, hK, hKa⟩ := hasCompactSpatialSupport_iff.mp ha
  set F : CoordinateSpace n × CoordinateSpace n → W := fun p ↦
    𝐞 (-⟪p.1, ξ - p.2⟫) • a.coefficient (p.1, (2 * π) • p.2) (𝓕 u p.2) with hF
  have hFint : Integrable F (volume.prod volume) := ha.integrable_fourierChar_smul_apply u ξ
  calc 𝓕 (quantizeSchwartzValue a.coefficient u) ξ = ∫ x, ∫ ζ, F (x, ζ) := by
        rw [Real.fourier_eq]
        refine integral_congr_ae (.of_forall fun x ↦ ?_)
        simp only [quantizeSchwartzValue_def, hF]
        rw [Circle.smul_def, ← integral_smul]
        refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
        simp only [Circle.smul_def, smul_smul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
        congr 3
        rw [inner_sub_right, real_inner_comm ζ x]
        ring
    _ = ∫ ζ, ∫ x, F (x, ζ) := integral_integral_swap hFint
    _ = _ := by
        refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
        have hint : Integrable fun x ↦ 𝐞 (-⟪x, ξ - ζ⟫) • a.coefficient (x, (2 * π) • ζ) :=
          ((Real.continuous_fourierChar.comp (by fun_prop)).smul
            (a.contDiff_coefficient_slice _).continuous).integrable_of_hasCompactSupport
              (HasCompactSupport.intro hK fun x hx ↦ by simp [hKa x hx, Circle.smul_def])
        dsimp only
        rw [Real.fourier_eq, ContinuousLinearMap.integral_apply hint]
        simp only [hF, Circle.smul_def, smul_apply]

/-- The pointwise kernel bound behind the Sobolev estimate: Peetre's inequality and the decay of
`â` give `⟨ξ⟩ ^ (s - m) ‖â(ξ - ζ, 2πζ) v‖ ≤ B k(ξ - ζ) ⟨ζ⟩ ^ s ‖v‖` with
`k(η) = (1 + ‖η‖) ^ (|s - m| - N)`. -/
private theorem rpow_mul_norm_fourier_apply_le {s C₀ : ℝ} {N : ℕ} (hC₀ : 0 ≤ C₀)
    (hdecay : ∀ η ξ : CoordinateSpace n,
      (1 + ‖η‖) ^ N * ‖𝓕 (fun x ↦ a.coefficient (x, ξ)) η‖ ≤ C₀ * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (ξ ζ : CoordinateSpace n) (v : V) :
    (1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) * ‖𝓕 (fun x ↦ a.coefficient (x, (2 * π) • ζ)) (ξ - ζ) v‖ ≤
      2 ^ (|s - m| / 2) * C₀ * (2 * π) ^ |m| * (1 + ‖ξ - ζ‖) ^ (-((N : ℝ) - |s - m|)) *
        ((1 + ‖ζ‖ ^ 2) ^ (s / 2) * ‖v‖) := by
  set A := 𝓕 (fun x ↦ a.coefficient (x, (2 * π) • ζ)) (ξ - ζ)
  set t := 1 + ‖ξ - ζ‖
  have ht : 0 < t := by positivity
  have hA : ‖A‖ ≤ C₀ * (1 + ‖(2 * π) • ζ‖ ^ 2) ^ (m / 2) * (t ^ N)⁻¹ := by
    rw [le_mul_inv_iff₀ (by positivity), mul_comm]
    exact hdecay _ _
  have hscale := one_add_norm_smul_sq_rpow_le (c := 2 * π) (by linarith [Real.two_le_pi]) m ζ
  have hpeetre := one_add_norm_sq_rpow_le_mul_sub (s - m) ξ ζ
  -- The bracket `⟨η⟩ ^ |s - m|` is at most `(1 + ‖η‖) ^ |s - m|`.
  have hbr : (1 + ‖ξ - ζ‖ ^ 2) ^ (|s - m| / 2) ≤ t ^ |s - m| :=
    one_add_norm_sq_rpow_le_one_add_norm_rpow _ (abs_nonneg _)
  have hk : t ^ |s - m| * (t ^ N)⁻¹ = t ^ (-((N : ℝ) - |s - m|)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg ht.le, ← Real.rpow_add ht]
    ring_nf
  have hw : (1 + ‖ζ‖ ^ 2) ^ ((s - m) / 2) * (1 + ‖ζ‖ ^ 2) ^ (m / 2) = (1 + ‖ζ‖ ^ 2) ^ (s / 2) := by
    rw [← Real.rpow_add (by positivity)]
    ring_nf
  calc (1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) * ‖A v‖
      ≤ (2 ^ (|s - m| / 2) * (1 + ‖ξ - ζ‖ ^ 2) ^ (|s - m| / 2) * (1 + ‖ζ‖ ^ 2) ^ ((s - m) / 2)) *
          ((C₀ * ((2 * π) ^ |m| * (1 + ‖ζ‖ ^ 2) ^ (m / 2)) * (t ^ N)⁻¹) * ‖v‖) := by
        gcongr
        refine (A.le_opNorm v).trans ?_
        gcongr
        exact hA.trans (by gcongr)
    _ ≤ (2 ^ (|s - m| / 2) * t ^ |s - m| * (1 + ‖ζ‖ ^ 2) ^ ((s - m) / 2)) *
          ((C₀ * ((2 * π) ^ |m| * (1 + ‖ζ‖ ^ 2) ^ (m / 2)) * (t ^ N)⁻¹) * ‖v‖) := by gcongr
    _ = 2 ^ (|s - m| / 2) * C₀ * (2 * π) ^ |m| * (t ^ |s - m| * (t ^ N)⁻¹) *
          (((1 + ‖ζ‖ ^ 2) ^ ((s - m) / 2) * (1 + ‖ζ‖ ^ 2) ^ (m / 2)) * ‖v‖) := by ring
    _ = _ := by rw [hk, hw]

/-- The pointwise form of the Sobolev estimate: `⟨ξ⟩ ^ (s - m) ‖𝓕 (Op(a) u) ξ‖` is bounded by the
integral of the kernel `B k(ξ - ζ)` of `rpow_mul_norm_fourier_apply_le` against
`⟨ζ⟩ ^ s ‖𝓕 u ζ‖`. -/
private theorem HasCompactSpatialSupport.enorm_smul_fourier_quantizeSchwartzValue_le
    (ha : a.HasCompactSpatialSupport) {s C₀ : ℝ} {N : ℕ} (hC₀ : 0 ≤ C₀)
    (hdecay : ∀ η ξ : CoordinateSpace n,
      (1 + ‖η‖) ^ N * ‖𝓕 (fun x ↦ a.coefficient (x, ξ)) η‖ ≤ C₀ * (1 + ‖ξ‖ ^ 2) ^ (m / 2))
    (u : 𝓢(CoordinateSpace n, V)) (ξ : CoordinateSpace n) :
    ‖(((1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ) • 𝓕 (quantizeSchwartzValue a.coefficient u) ξ‖ₑ ≤
      ∫⁻ ζ, ENNReal.ofReal (2 ^ (|s - m| / 2) * C₀ * (2 * π) ^ |m| *
          (1 + ‖ξ - ζ‖) ^ (-((N : ℝ) - |s - m|))) *
        ‖(((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 u ζ‖ₑ := by
  rw [ha.fourier_quantizeSchwartzValue, enorm_smul]
  calc ‖(((1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ)‖ₑ *
        ‖∫ ζ, 𝓕 (fun x ↦ a.coefficient (x, (2 * π) • ζ)) (ξ - ζ) (𝓕 u ζ)‖ₑ
      ≤ ‖(((1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ)‖ₑ *
        ∫⁻ ζ, ‖𝓕 (fun x ↦ a.coefficient (x, (2 * π) • ζ)) (ξ - ζ) (𝓕 u ζ)‖ₑ := by
        gcongr
        exact enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ ζ, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) *
          ‖𝓕 (fun x ↦ a.coefficient (x, (2 * π) • ζ)) (ξ - ζ) (𝓕 u ζ)‖) := by
        rw [← lintegral_const_mul' _ _ enorm_ne_top]
        refine lintegral_congr fun ζ ↦ ?_
        rw [ENNReal.ofReal_mul (by positivity), ofReal_norm, ← ofReal_norm, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
    _ ≤ _ := by
        refine lintegral_mono fun ζ ↦ ?_
        rw [enorm_smul, ← ofReal_norm, ← ofReal_norm, Complex.norm_real,
          Real.norm_of_nonneg (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal (rpow_mul_norm_fourier_apply_le hC₀ hdecay ξ ζ (𝓕 u ζ))

variable (V W m) in
/-- The constant in the Sobolev estimate on Schwartz functions is linear in the decay constant of
`â`: there is `A` such that, whenever `(1 + ‖η‖) ^ N ‖â(η, ξ)‖ ≤ C₀ ⟨ξ⟩ ^ m` with
`N = ⌈|s - m|⌉₊ + n + 1`, `‖⟨ξ⟩ ^ (s - m) 𝓕 (Op(a) u)‖_{L²} ≤ A C₀ ‖⟨ξ⟩ ^ s 𝓕 u‖_{L²}`. -/
private theorem exists_eLpNorm_smul_fourier_quantizeSchwartzValue_le_mul (s : ℝ) :
    ∃ A, 0 ≤ A ∧ ∀ a : Symbol n V W m, a.HasCompactSpatialSupport → ∀ C₀, 0 ≤ C₀ →
      (∀ η ξ : CoordinateSpace n, (1 + ‖η‖) ^ (⌈|s - m|⌉₊ + n + 1) *
        ‖𝓕 (fun x ↦ a.coefficient (x, ξ)) η‖ ≤ C₀ * (1 + ‖ξ‖ ^ 2) ^ (m / 2)) →
      ∀ u : 𝓢(CoordinateSpace n, V),
        eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ) •
            𝓕 (quantizeSchwartzValue a.coefficient u) ξ) 2 volume ≤
          ENNReal.ofReal (A * C₀) *
            eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 u ξ) 2 volume := by
  set N : ℕ := ⌈|s - m|⌉₊ + n + 1
  set k : CoordinateSpace n → ℝ := fun η ↦ (1 + ‖η‖) ^ (-((N : ℝ) - |s - m|))
  have hk_int : Integrable k := integrable_one_add_norm (by
    rw [finrank_euclideanSpace, Fintype.card_fin]
    have := Nat.le_ceil |s - m|
    push_cast [N]
    linarith)
  refine ⟨2 ^ (|s - m| / 2) * (2 * π) ^ |m| * ∫ η, k η,
    mul_nonneg (by positivity) (integral_nonneg fun η ↦ by positivity),
    fun a ha C₀ hC₀ hdecay u ↦ ?_⟩
  set B := 2 ^ (|s - m| / 2) * C₀ * (2 * π) ^ |m|
  have hB : 0 ≤ B := by positivity
  rw [show 2 ^ (|s - m| / 2) * (2 * π) ^ |m| * (∫ η, k η) * C₀ = B * ∫ η, k η by ring]
  set A := ENNReal.ofReal (B * ∫ η, k η)
  -- The pointwise bound by the kernel `B k(ξ - ζ)` acting on `⟨ζ⟩ ^ s ‖𝓕 u ζ‖`.
  have hpt := ha.enorm_smul_fourier_quantizeSchwartzValue_le (s := s) hC₀ hdecay u
  -- Schur's test for the kernel `B k(ξ - ζ)`, whose row and column integrals are `A`.
  have hint : ∫⁻ η, ENNReal.ofReal (B * k η) = A := by
    rw [← ofReal_integral_eq_lintegral_ofReal (hk_int.const_mul B)
      (.of_forall fun η ↦ mul_nonneg hB (Real.rpow_nonneg (by positivity) _)), integral_const_mul]
  have hkcont : Continuous k :=
    (continuous_const.add continuous_norm).rpow_const fun x ↦
      Or.inl (add_pos_of_pos_of_nonneg one_pos (norm_nonneg x)).ne'
  have hkmeas : AEMeasurable (Function.uncurry fun x y : CoordinateSpace n ↦
      ENNReal.ofReal (B * k (x - y))) (volume.prod volume) :=
    (ENNReal.continuous_ofReal.comp (continuous_const.mul
      (hkcont.comp (continuous_fst.sub continuous_snd)))).measurable.aemeasurable
  have hw (r : ℝ) : Continuous fun x : CoordinateSpace n ↦ (((1 + ‖x‖ ^ 2) ^ (r / 2) : ℝ) : ℂ) :=
    (by fun_prop : (fun x : CoordinateSpace n ↦
      (((1 + ‖x‖ ^ 2) ^ (r / 2) : ℝ) : ℂ)).HasTemperateGrowth).1.continuous
  have hgmeas : AEStronglyMeasurable
      (fun ζ : CoordinateSpace n ↦ (((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 u ζ) :=
    ((hw s).smul (𝓕 u).continuous).aestronglyMeasurable
  have hschur := TauCeti.eLpNorm_lintegral_mul_le hkmeas hgmeas.enorm
    (p := 2) one_le_two (A := A) (B := A)
    (.of_forall fun x ↦ (lintegral_sub_left_eq_self (fun η ↦ ENNReal.ofReal (B * k η)) x).trans
      hint |>.le)
    (.of_forall fun y ↦ (lintegral_sub_right_eq_self (fun η ↦ ENNReal.ofReal (B * k η)) y).trans
      hint |>.le)
  calc _ ≤ eLpNorm (fun ξ ↦ ∫⁻ ζ, ENNReal.ofReal (B * k (ξ - ζ)) *
          ‖(((1 + ‖ζ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 u ζ‖ₑ) 2 volume :=
        eLpNorm_mono_enorm ((hw (s - m)).smul
          (ha.integrable_quantizeSchwartzValue u).continuous_fourier).aestronglyMeasurable
          fun ξ ↦ by rw [enorm_eq_self]; exact hpt ξ
    _ ≤ _ := hschur
    _ = _ := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num), eLpNorm_enorm _ hgmeas,
          sub_add_cancel, ENNReal.rpow_one]


/-- **The Sobolev estimate on Schwartz functions.** For a symbol `a` of order `m` with compact
spatial support and every real `s`, there is a constant `C` with
`‖⟨ξ⟩ ^ (s - m) 𝓕 (Op(a) u)‖_{L²} ≤ C ‖⟨ξ⟩ ^ s 𝓕 u‖_{L²}` for every Schwartz function `u`, that
is, `‖Op(a) u‖_{H^{s-m}} ≤ C ‖u‖_{H^s}`. -/
theorem HasCompactSpatialSupport.exists_eLpNorm_smul_fourier_quantizeSchwartzValue_le
    (ha : a.HasCompactSpatialSupport) (s : ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ u : 𝓢(CoordinateSpace n, V),
      eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ) •
          𝓕 (quantizeSchwartzValue a.coefficient u) ξ) 2 volume ≤
        ENNReal.ofReal C *
          eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 u ξ) 2 volume := by
  obtain ⟨A, hA, hAa⟩ := exists_eLpNorm_smul_fourier_quantizeSchwartzValue_le_mul m V W s
  obtain ⟨C₀, hC₀, hdecay⟩ := ha.exists_one_add_norm_pow_mul_norm_fourier_le (⌈|s - m|⌉₊ + n + 1)
  exact ⟨A * C₀, mul_nonneg hA hC₀, hAa a ha C₀ hC₀ hdecay⟩

variable (V W m) in
/-- **The Sobolev estimate on Schwartz functions, uniformly in the symbol.** For a compact set `K`
and every real `s`, there are finitely many words `α` and a constant `C` such that every symbol
`a` of order `m` vanishing at positions outside `K` satisfies
`‖Op(a) u‖_{H^{s-m}} ≤ C max_α p_{K,α,[]}(a) ‖u‖_{H^s}` for every Schwartz function `u`. -/
theorem exists_eLpNorm_smul_fourier_quantizeSchwartzValue_le_seminorm
    (K : Compacts (CoordinateSpace n)) (s : ℝ) :
    ∃ (S : Finset (List (Fin n))) (C : ℝ), 0 ≤ C ∧ ∀ a : Symbol n V W m,
      (∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0) → ∀ u : 𝓢(CoordinateSpace n, V),
        eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ) •
            𝓕 (quantizeSchwartzValue a.coefficient u) ξ) 2 volume ≤
          ENNReal.ofReal (C * (S.sup fun α ↦ Symbol.seminorm K α []) a) *
            eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 u ξ) 2 volume := by
  obtain ⟨A, hA, hAa⟩ := exists_eLpNorm_smul_fourier_quantizeSchwartzValue_le_mul m V W s
  obtain ⟨S, C, hC, hdecay⟩ :=
    exists_one_add_norm_pow_mul_norm_fourier_le_seminorm m V W K (⌈|s - m|⌉₊ + n + 1)
  refine ⟨S, A * C, mul_nonneg hA hC, fun a haK u ↦ ?_⟩
  have h := hAa a (hasCompactSpatialSupport_iff.2 ⟨K, K.isCompact, haK⟩) _
    (mul_nonneg hC (apply_nonneg _ _)) (hdecay a haK) u
  rwa [← mul_assoc] at h
end Quantization

/-! ### The bounded operator on Bessel-potential spaces -/

section Sobolev

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] {a : Symbol n V W m}

/-- The quantization of a symbol with compact spatial support, as a linear map from Schwartz
functions to `L²`. -/
private def HasCompactSpatialSupport.quantizeLp (ha : a.HasCompactSpatialSupport) :
    𝓢(CoordinateSpace n, V) →ₗ[ℂ] Lp W 2 (volume : Measure (CoordinateSpace n)) where
  toFun u := (ha.memLp_quantizeSchwartzValue u 2).toLp _
  map_add' u v := by
    obtain ⟨C, -, hC⟩ := isUniform_iff.mp ha.isUniform [] []
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ (.of_forall fun x ↦ ?_)
    exact quantizeSchwartzValue_add_right (a.contDiff_coefficient.continuous.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      (fun ξ ↦ by simpa using hC x ξ) u v
  map_smul' c u := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (.of_forall fun x ↦ quantizeSchwartzValue_smul_right c u)

omit [CompleteSpace V] [CompleteSpace W] in
private theorem HasCompactSpatialSupport.quantizeLp_apply (ha : a.HasCompactSpatialSupport)
    (u : 𝓢(CoordinateSpace n, V)) :
    ha.quantizeLp u = (ha.memLp_quantizeSchwartzValue u 2).toLp _ :=
  (rfl)

omit [CompleteSpace V] in
/-- The weighted Fourier transform of the quantization is the tempered distribution of the
`L²` function `⟨ξ⟩ ^ r 𝓕 (Op(a) u)`, whenever the latter lies in `L²`. -/
private theorem HasCompactSpatialSupport.smulLeftCLM_fourier_quantizeLp
    (ha : a.HasCompactSpatialSupport) (r : ℝ) (u : 𝓢(CoordinateSpace n, V))
    (hG : MemLp (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (r / 2) : ℝ) : ℂ) •
      𝓕 (quantizeSchwartzValue a.coefficient u) ξ) 2) :
    smulLeftCLM W (fun x : CoordinateSpace n ↦ (((1 + ‖x‖ ^ 2) ^ (r / 2) : ℝ) : ℂ))
        (𝓕 (ha.quantizeLp u : 𝓢'(CoordinateSpace n, W))) =
      (hG.toLp _ : 𝓢'(CoordinateSpace n, W)) := by
  ext φ
  rw [smulLeftCLM_apply_apply, ha.quantizeLp_apply,
    Lp.fourier_toTemperedDistribution_apply _ (ha.integrable_quantizeSchwartzValue u)
      (MemLp.coeFn_toLp _),
    Lp.toTemperedDistribution_apply]
  refine integral_congr_ae ((hG.coeFn_toLp).mono fun ξ hξ ↦ ?_)
  dsimp only
  rw [hξ, SchwartzMap.smulLeftCLM_apply_apply (by fun_prop), smul_eq_mul, mul_comm, mul_smul]

omit [CompleteSpace V] [CompleteSpace W] in
private theorem HasCompactSpatialSupport.memLp_smul_fourier_quantizeSchwartzValue
    (ha : a.HasCompactSpatialSupport) (s : ℝ) (u : 𝓢(CoordinateSpace n, V)) :
    MemLp (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ) •
      𝓕 (quantizeSchwartzValue a.coefficient u) ξ) 2 := by
  obtain ⟨C, -, hC⟩ := ha.exists_eLpNorm_smul_fourier_quantizeSchwartzValue_le s
  exact (hC u).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (SchwartzMap.memLp_one_add_norm_sq_rpow_smul_fourier s u 2))

omit [CompleteSpace V] in
private theorem HasCompactSpatialSupport.memSobolev_quantizeLp (ha : a.HasCompactSpatialSupport)
    (s : ℝ) (u : 𝓢(CoordinateSpace n, V)) :
    MemSobolev (s - m) 2 (ha.quantizeLp u : 𝓢'(CoordinateSpace n, W)) :=
  memSobolev_iff_exists_smulLeftCLM_fourier.2 ⟨_, ha.smulLeftCLM_fourier_quantizeLp (s - m) u
    (ha.memLp_smul_fourier_quantizeSchwartzValue s u)⟩

omit [CompleteSpace V] in
/-- The quantization of a symbol of order `m` with compact spatial support, as a linear map from
Schwartz functions to `H^{s - m}`. -/
private def HasCompactSpatialSupport.quantizeBessel (ha : a.HasCompactSpatialSupport) (s : ℝ) :
    𝓢(CoordinateSpace n, V) →ₗ[ℂ] H^{s - m}(CoordinateSpace n, W) where
  toFun u := (ha.memSobolev_quantizeLp s u).toBesselPotentialSpace
  map_add' u v := BesselPotentialSpace.ext (by
    simp only [MemSobolev.toBesselPotentialSpace_toDistr, BesselPotentialSpace.toDistr_add,
      map_add]
    exact (Lp.toTemperedDistributionCLM W volume 2).map_add _ _)
  map_smul' c u := BesselPotentialSpace.ext (by
    simp only [MemSobolev.toBesselPotentialSpace_toDistr, BesselPotentialSpace.toDistr_smul,
      map_smul, RingHom.id_apply]
    exact (Lp.toTemperedDistributionCLM W volume 2).map_smul _ _)

omit [CompleteSpace V] in
private theorem HasCompactSpatialSupport.toDistr_quantizeBessel (ha : a.HasCompactSpatialSupport)
    (s : ℝ) (u : 𝓢(CoordinateSpace n, V)) :
    (ha.quantizeBessel s u).toDistr = (ha.quantizeLp u : 𝓢'(CoordinateSpace n, W)) :=
  MemSobolev.toBesselPotentialSpace_toDistr _

/-- A constant of the Sobolev estimate on the Fourier side bounds the quantization from `H^s` to
`H^{s - m}` on Schwartz functions. -/
private theorem HasCompactSpatialSupport.norm_quantizeBessel_le
    (ha : a.HasCompactSpatialSupport) {s C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ u : 𝓢(CoordinateSpace n, V),
      eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ ((s - m) / 2) : ℝ) : ℂ) •
          𝓕 (quantizeSchwartzValue a.coefficient u) ξ) 2 volume ≤
        ENNReal.ofReal C *
          eLpNorm (fun ξ ↦ (((1 + ‖ξ‖ ^ 2) ^ (s / 2) : ℝ) : ℂ) • 𝓕 u ξ) 2 volume)
    (u : 𝓢(CoordinateSpace n, V)) :
    ‖ha.quantizeBessel s u‖ ≤ C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖ := by
  have hG := ha.memLp_smul_fourier_quantizeSchwartzValue s u
  rw [BesselPotentialSpace.norm_eq_of_smulLeftCLM_fourier_eq
      ((ha.toDistr_quantizeBessel s u).symm ▸ ha.smulLeftCLM_fourier_quantizeLp (s - m) u hG),
    Lp.norm_toLp, SchwartzMap.norm_toBesselPotentialSpaceCLM, ← ENNReal.toReal_ofReal hC0,
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (SchwartzMap.memLp_one_add_norm_sq_rpow_smul_fourier s u 2).eLpNorm_ne_top) (hC u)

/-- On Schwartz functions the quantization is bounded from `H^s` to `H^{s - m}`. -/
private theorem HasCompactSpatialSupport.exists_norm_quantizeBessel_le
    (ha : a.HasCompactSpatialSupport) (s : ℝ) :
    ∃ C, ∀ u : 𝓢(CoordinateSpace n, V),
      ‖ha.quantizeBessel s u‖ ≤ C * ‖SchwartzMap.toBesselPotentialSpaceCLM s 2 u‖ := by
  obtain ⟨C, hC0, hC⟩ := ha.exists_eLpNorm_smul_fourier_quantizeSchwartzValue_le s
  exact ⟨C, ha.norm_quantizeBessel_le hC0 hC⟩

/-- **Sobolev mapping of pseudodifferential operators with compact spatial support.** The left
quantization `Op(a)` of a symbol `a` of order `m` with compact spatial support extends from
Schwartz functions to a bounded operator `H^s(ℝⁿ; V) → H^{s - m}(ℝⁿ; W)` between Bessel-potential
spaces, for every real `s`. On a Schwartz function `u` it is the tempered distribution of the
function `Op(a) u` (`TauCeti.Symbol.toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply`), and
it is the unique continuous linear map with this property
(`BesselPotentialSpace.continuousLinearMap_ext`). -/
def quantizeSobolev (a : Symbol n V W m) (ha : a.HasCompactSpatialSupport) (s : ℝ) :
    H^{s}(CoordinateSpace n, V) →L[ℂ] H^{s - m}(CoordinateSpace n, W) :=
  (ha.quantizeBessel s).extendOfNorm
    (SchwartzMap.toBesselPotentialSpaceCLM (E := CoordinateSpace n) (F := V) s 2).toLinearMap

/-- On Schwartz functions, the bounded extension is the quantization into `H^{s - m}`. -/
private theorem quantizeSobolev_toBesselPotentialSpaceCLM (ha : a.HasCompactSpatialSupport)
    (s : ℝ) (u : 𝓢(CoordinateSpace n, V)) :
    a.quantizeSobolev ha s (SchwartzMap.toBesselPotentialSpaceCLM s 2 u) =
      ha.quantizeBessel s u := by
  obtain ⟨C, hC⟩ := ha.exists_norm_quantizeBessel_le s
  have h := LinearMap.extendOfNorm_eq (f := ha.quantizeBessel s)
    (e := (SchwartzMap.toBesselPotentialSpaceCLM (E := CoordinateSpace n) (F := V) s 2).toLinearMap)
    (SchwartzMap.denseRange_toBesselPotentialSpaceCLM s ENNReal.ofNat_ne_top) ⟨C, hC⟩ u
  rwa [ContinuousLinearMap.coe_coe] at h

/-- On a Schwartz function `u`, the operator `Op(a) : H^s → H^{s - m}` gives the tempered
distribution of the function `Op(a) u = quantizeSchwartzValue a.coefficient u`. -/
@[simp]
theorem toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply
    (ha : a.HasCompactSpatialSupport) (s : ℝ) (u : 𝓢(CoordinateSpace n, V))
    (φ : 𝓢(CoordinateSpace n, ℂ)) :
    (a.quantizeSobolev ha s (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
      ∫ x, φ x • quantizeSchwartzValue a.coefficient u x := by
  rw [quantizeSobolev_toBesselPotentialSpaceCLM, ha.toDistr_quantizeBessel, ha.quantizeLp_apply,
    Lp.toTemperedDistribution_apply]
  exact integral_congr_ae ((ha.memLp_quantizeSchwartzValue u 2).coeFn_toLp.mono fun x hx ↦ by
    simp only [hx])


omit [CompleteSpace V] [CompleteSpace W] in
private theorem HasCompactSpatialSupport.quantizeLp_add {b : Symbol n V W m}
    (ha : a.HasCompactSpatialSupport) (hb : b.HasCompactSpatialSupport)
    (u : 𝓢(CoordinateSpace n, V)) :
    (ha.add hb).quantizeLp u = ha.quantizeLp u + hb.quantizeLp u := by
  obtain ⟨C, -, hC⟩ := isUniform_iff.mp ha.isUniform [] []
  obtain ⟨C', -, hC'⟩ := isUniform_iff.mp hb.isUniform [] []
  rw [ha.quantizeLp_apply, hb.quantizeLp_apply, (ha.add hb).quantizeLp_apply, ← MemLp.toLp_add]
  refine MemLp.toLp_congr _ _ (.of_forall fun x ↦ ?_)
  rw [coefficient_add]
  exact quantizeSchwartzValue_add_left
    (a.contDiff_coefficient.continuous.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (fun ξ ↦ by simpa using hC x ξ)
    (b.contDiff_coefficient.continuous.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (fun ξ ↦ by simpa using hC' x ξ) u

omit [CompleteSpace V] [CompleteSpace W] in
private theorem HasCompactSpatialSupport.quantizeLp_smul (ha : a.HasCompactSpatialSupport) (c : ℂ)
    (u : 𝓢(CoordinateSpace n, V)) :
    (ha.smul c).quantizeLp u = c • ha.quantizeLp u := by
  rw [ha.quantizeLp_apply, (ha.smul c).quantizeLp_apply, ← MemLp.toLp_const_smul]
  refine MemLp.toLp_congr _ _ (.of_forall fun x ↦ ?_)
  rw [coefficient_smul, quantizeSchwartzValue_smul_left]
  rfl

/-- The Sobolev extension of the quantization is additive in the symbol. -/
theorem quantizeSobolev_add {b : Symbol n V W m} (ha : a.HasCompactSpatialSupport)
    (hb : b.HasCompactSpatialSupport) (s : ℝ) :
    (a + b).quantizeSobolev (ha.add hb) s = a.quantizeSobolev ha s + b.quantizeSobolev hb s := by
  refine BesselPotentialSpace.continuousLinearMap_ext ENNReal.ofNat_ne_top fun u ↦ ?_
  rw [add_apply, quantizeSobolev_toBesselPotentialSpaceCLM,
    quantizeSobolev_toBesselPotentialSpaceCLM, quantizeSobolev_toBesselPotentialSpaceCLM]
  refine BesselPotentialSpace.ext ?_
  rw [BesselPotentialSpace.toDistr_add, (ha.add hb).toDistr_quantizeBessel,
    ha.toDistr_quantizeBessel, hb.toDistr_quantizeBessel, ha.quantizeLp_add hb]
  exact (Lp.toTemperedDistributionCLM W volume 2).map_add _ _

/-- The Sobolev extension of the quantization is homogeneous in the symbol. -/
theorem quantizeSobolev_smul (ha : a.HasCompactSpatialSupport) (c : ℂ) (s : ℝ) :
    (c • a).quantizeSobolev (ha.smul c) s = c • a.quantizeSobolev ha s := by
  refine BesselPotentialSpace.continuousLinearMap_ext ENNReal.ofNat_ne_top fun u ↦ ?_
  rw [smul_apply, quantizeSobolev_toBesselPotentialSpaceCLM,
    quantizeSobolev_toBesselPotentialSpaceCLM]
  refine BesselPotentialSpace.ext ?_
  rw [BesselPotentialSpace.toDistr_smul, (ha.smul c).toDistr_quantizeBessel,
    ha.toDistr_quantizeBessel, ha.quantizeLp_smul]
  exact (Lp.toTemperedDistributionCLM W volume 2).map_smul _ _

/-- The Sobolev extension of the quantization of `-a` is `-Op(a)`. -/
theorem quantizeSobolev_neg (ha : a.HasCompactSpatialSupport) (s : ℝ) :
    (-a).quantizeSobolev ha.neg s = -a.quantizeSobolev ha s := by
  simpa using quantizeSobolev_smul ha (-1) s

/-- The Sobolev extension of the quantization is subtractive in the symbol. -/
theorem quantizeSobolev_sub {b : Symbol n V W m} (ha : a.HasCompactSpatialSupport)
    (hb : b.HasCompactSpatialSupport) (s : ℝ) :
    (a - b).quantizeSobolev (ha.sub hb) s = a.quantizeSobolev ha s - b.quantizeSobolev hb s := by
  have h := quantizeSobolev_add ha hb.neg s
  rw [quantizeSobolev_neg] at h
  simpa only [sub_eq_add_neg] using h

/-- The Sobolev extension of the quantization of the zero symbol is zero. -/
@[simp]
theorem quantizeSobolev_zero (ha : (0 : Symbol n V W m).HasCompactSpatialSupport) (s : ℝ) :
    (0 : Symbol n V W m).quantizeSobolev ha s = 0 := by
  simpa only [smul_zero, zero_smul] using quantizeSobolev_smul ha (0 : ℂ) s

variable (V W m) in
/-- **The operator norm of `Op(a) : H^s → H^{s - m}` is controlled by finitely many symbol
seminorms.** For a compact set `K` and every real `s`, there are finitely many words `α` and a
constant `C` such that every symbol `a` of order `m` vanishing at positions outside `K` satisfies
`‖Op(a)‖ ≤ C max_α p_{K,α,[]}(a)`. Only the position derivatives of `a` enter. -/
theorem exists_norm_quantizeSobolev_le_seminorm (K : Compacts (CoordinateSpace n)) (s : ℝ) :
    ∃ (S : Finset (List (Fin n))) (C : ℝ), 0 ≤ C ∧ ∀ (a : Symbol n V W m)
      (ha : a.HasCompactSpatialSupport), (∀ x ∉ K, ∀ ξ, a.coefficient (x, ξ) = 0) →
        ‖a.quantizeSobolev ha s‖ ≤ C * (S.sup fun α ↦ Symbol.seminorm K α []) a := by
  obtain ⟨S, C, hC, h⟩ := exists_eLpNorm_smul_fourier_quantizeSchwartzValue_le_seminorm m V W K s
  refine ⟨S, C, hC, fun a ha haK ↦ ?_⟩
  have hC' : 0 ≤ C * (S.sup fun α ↦ Symbol.seminorm K α []) a := mul_nonneg hC (apply_nonneg _ _)
  refine LinearMap.opNorm_extendOfNorm_le (f := ha.quantizeBessel s)
    (e := (SchwartzMap.toBesselPotentialSpaceCLM (E := CoordinateSpace n) (F := V) s 2).toLinearMap)
    (SchwartzMap.denseRange_toBesselPotentialSpaceCLM s ENNReal.ofNat_ne_top) hC' fun u ↦ ?_
  rw [ContinuousLinearMap.coe_coe]
  exact ha.norm_quantizeBessel_le hC' (h a haK) u

/-- **Continuity of the quantization in the symbol.** Let `t ↦ aₜ` be a family of symbols of order
`m`, continuous for the symbol topology, which all vanish at positions outside a common compact set
`K`. Then `t ↦ Op(aₜ)` is continuous in the operator norm of `H^s → H^{s - m}`, for every real
`s`. -/
theorem _root_.Continuous.symbol_quantizeSobolev {X : Type*} [TopologicalSpace X]
    {a : X → Symbol n V W m}
    (hcont : Continuous a) {K : Compacts (CoordinateSpace n)}
    (haK : ∀ t, ∀ x ∉ K, ∀ ξ, (a t).coefficient (x, ξ) = 0) (s : ℝ) :
    Continuous fun t ↦
      (a t).quantizeSobolev (hasCompactSpatialSupport_iff.2 ⟨K, K.isCompact, haK t⟩) s := by
  obtain ⟨S, C, -, hbound⟩ := exists_norm_quantizeSobolev_le_seminorm m V W K s
  set q : Seminorm ℂ (Symbol n V W m) := S.sup fun α ↦ Symbol.seminorm K α []
  have hq : Continuous q :=
    Seminorm.continuous_finsetSup fun α _ ↦ by
      simpa only [seminormFamily_apply] using
        (withSeminorms (n := n) (V := V) (W := W) (m := m)).continuous_seminorm (K, α, [])
  refine continuous_iff_continuousAt.2 fun t₀ ↦ tendsto_iff_norm_sub_tendsto_zero.2 ?_
  refine squeeze_zero (fun t ↦ norm_nonneg _) (fun t ↦ ?_)
    (?_ : Filter.Tendsto (fun t ↦ C * q (a t - a t₀)) _ _)
  · rw [← quantizeSobolev_sub]
    exact hbound _ _ fun x hx ξ ↦ by simp [haK t x hx ξ, haK t₀ x hx ξ]
  · simpa using ((hq.comp (hcont.sub (continuous_const (y := a t₀)))).tendsto t₀).const_mul C

end Sobolev

section Transport

variable {V W V' W' : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W] [NormedAddCommGroup V']
  [NormedSpace ℂ V'] [CompleteSpace V'] [NormedAddCommGroup W'] [NormedSpace ℂ W']
  [CompleteSpace W']

/-- **Change of fibres for Sobolev extensions of quantizations.** Let `e₁ : V ≃L[ℂ] V'` and
`e₂ : W ≃L[ℂ] W'`, and let `T : H^s(ℝⁿ; V') → H^r(ℝⁿ; W')` agree on Schwartz functions with the
quantization of the conjugated symbol `e₂ a e₁⁻¹`. Then `e₂⁻¹ ∘ T ∘ e₁ : H^s(ℝⁿ; V) → H^r(ℝⁿ; W)`
agrees on Schwartz functions with the quantization of `a`
(`TauCeti.quantizeSchwartzValue_arrowCongr`). -/
theorem toDistr_postcomp_comp_comp_postcomp_toBesselPotentialSpaceCLM_apply
    (a : Symbol n V W m) (e₁ : V ≃L[ℂ] V') (e₂ : W ≃L[ℂ] W') {r s : ℝ}
    {T : H^{s}(CoordinateSpace n, V') →L[ℂ] H^{r}(CoordinateSpace n, W')}
    (hT : ∀ (u : 𝓢(CoordinateSpace n, V')) (φ : 𝓢(CoordinateSpace n, ℂ)),
      (T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
        ∫ x, φ x • quantizeSchwartzValue
          (a.map ((e₁.arrowCongr e₂).toContinuousLinearMap.restrictScalars ℝ)).coefficient u x)
    (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)) :
    ((BesselPotentialSpace.postcomp _ r 2 (e₂.symm : W' →L[ℂ] W) ∘L T ∘L
        BesselPotentialSpace.postcomp _ s 2 (e₁ : V →L[ℂ] V'))
        (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
      ∫ x, φ x • quantizeSchwartzValue a.coefficient u x := by
  have hc : (a.map ((e₁.arrowCongr e₂).toContinuousLinearMap.restrictScalars ℝ)).coefficient =
      fun p ↦ e₁.arrowCongr e₂ (a.coefficient p) :=
    funext fun p ↦ by simp
  have hq (x : CoordinateSpace n) :
      quantizeSchwartzValue
          (a.map ((e₁.arrowCongr e₂).toContinuousLinearMap.restrictScalars ℝ)).coefficient
          (u.postcompCLM (e₁ : V →L[ℂ] V')) x =
        e₂ (quantizeSchwartzValue a.coefficient u x) := by
    rw [hc, quantizeSchwartzValue_arrowCongr]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ← SchwartzMap.toBesselPotentialSpaceCLM_postcompCLM,
    BesselPotentialSpace.toDistr_postcomp_apply, hT]
  simp only [hq, ← map_smul, ContinuousLinearEquiv.integral_comp_comm,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]

end Transport

section FiniteDimensional

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [FiniteDimensional ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [FiniteDimensional ℂ W]

/-- **Sobolev mapping of pseudodifferential operators with compact spatial support.** For a
symbol `a` of order `m` with compact spatial support between finite-dimensional complex normed
spaces and every real `s`, the quantization `Op(a)` extends from Schwartz functions to a bounded
operator `H^s(ℝⁿ; V) → H^{s - m}(ℝⁿ; W)`.

The norms of `V` and `W` need not come from inner products: isomorphisms `e₁ : V ≃L[ℂ] ℂ^k`,
`e₂ : W ≃L[ℂ] ℂ^l` induce isomorphisms of the Bessel-potential spaces
(`BesselPotentialSpace.postcomp`), and the operator is `e₂⁻¹ ∘ Op(e₂ a e₁⁻¹) ∘ e₁` with the
Hilbert-space operator `TauCeti.Symbol.quantizeSobolev`
(`TauCeti.Symbol.toDistr_postcomp_comp_comp_postcomp_toBesselPotentialSpaceCLM_apply`). -/
theorem exists_quantizeSobolev (a : Symbol n V W m) (ha : a.HasCompactSpatialSupport) (s : ℝ) :
    ∃ T : H^{s}(CoordinateSpace n, V) →L[ℂ] H^{s - m}(CoordinateSpace n, W),
      ∀ (u : 𝓢(CoordinateSpace n, V)) (φ : 𝓢(CoordinateSpace n, ℂ)),
        (T (SchwartzMap.toBesselPotentialSpaceCLM s 2 u)).toDistr φ =
          ∫ x, φ x • quantizeSchwartzValue a.coefficient u x := by
  -- Transport to the Hilbert spaces `ℂ^k` and `ℂ^l` along isomorphisms `e₁` and `e₂`.
  let e₁ : V ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  let e₂ : W ≃L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ W)) :=
    ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm
  exact ⟨_, toDistr_postcomp_comp_comp_postcomp_toBesselPotentialSpaceCLM_apply a e₁ e₂
    (toDistr_quantizeSobolev_toBesselPotentialSpaceCLM_apply (ha.map _) s)⟩

end FiniteDimensional

end Symbol

end TauCeti
