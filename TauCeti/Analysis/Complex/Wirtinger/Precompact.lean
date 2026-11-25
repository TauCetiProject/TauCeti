/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.InteriorEstimate
public import Mathlib.Topology.MetricSpace.Holder
import TauCeti.Analysis.Sobolev.Morrey.Basic
import TauCeti.MeasureTheory.Function.LpSeminorm.TriangleInequality
import TauCeti.Topology.MetricSpace.Holder

/-!
# Uniform `W^{1,p}` and Hölder bounds for bounded maps with `\bar∂` bounded in `Lᵖ`, `p > 2`

Let `2 < p < ∞` and let `U ⊆ ℂ` be open. This file proves that a family of smooth maps
`u : ℂ → F` into a complex Hilbert space which is uniformly bounded on `U`, and whose
conjugate Wirtinger derivatives `\bar∂u` are, up to a uniformly bounded error, uniformly
bounded in `Lᵖ(U)`, is bounded in `W^{1,p}` on every compact subset of `U`
(`TauCeti.exists_eLpNorm_fderiv_le_of_norm_conjWirtingerDeriv_sub_le`, which only needs
`1 < p < ∞`) and uniformly Hölder continuous of exponent `1 - 2 / p` there
(`TauCeti.exists_holderOnWith_of_norm_conjWirtingerDeriv_sub_le`). The resulting locally uniformly
convergent subsequences for a proper target are
`TauCeti.exists_strictMono_tendstoLocallyUniformlyOn_of_norm_conjWirtingerDeriv_sub_le` in
`TauCeti.Analysis.Complex.Wirtinger.Compactness`.

The bounded error term allows `\bar∂u` to differ from an `Lᵖ`-small or `Lᵖ`-bounded function by
bounded zeroth-order terms, as for the equation `\bar∂u + ν u = g` with bounded `ν` and bounded
`u`. The exponent `1 - 2 / p` is the exponent of Morrey's embedding `W^{1,p} ⊆ C^{1 - 2 / p}` in
the plane; for `p = 2 + 2 / m` it is `1 / (m + 1)`.

## The argument

Fix a compact set `K ⊆ U`. On a bounded open neighbourhood `V` of `K` inside `U` the bounded
maps `u` and `\bar∂u - g` lie in `Lᵖ(V)` with uniform bounds, so the interior estimate for the
Cauchy–Riemann operator
(`TauCeti.exists_eLpNorm_fderiv_le_eLpNorm_conjWirtingerDeriv_add_eLpNorm`) bounds the
derivative `Du` in `Lᵖ(K)` uniformly over the family. Applied to a closed thickening `L` of `K`
inside `U`, Morrey's inequality on `L`, in the plane form
`TauCeti.exists_edist_le_of_contDiffOn_cthickening_of_two_lt`, bounds `‖u x - u y‖` by a
multiple of `|x - y|^(1 - 2 / p)` for nearby points `x, y ∈ K`, and the sup bound handles
distant points (`HolderOnWith.of_dist_lt_of_dist_le`).

## Main results

* `TauCeti.eLpNorm_conjWirtingerDeriv_restrict_le_of_norm_sub_le`: an `Lᵖ(K)` bound on `\bar∂u`
  from `‖\bar∂u - g‖ ≤ M` on `K` and an `Lᵖ(K)` bound on `g`.
* `TauCeti.exists_eLpNorm_fderiv_le_of_norm_conjWirtingerDeriv_sub_le`: the uniform interior
  `W^{1,p}` bound.
* `TauCeti.exists_holderOnWith_of_norm_conjWirtingerDeriv_sub_le`: the uniform Hölder bound on
  compact subsets.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix B (Morrey's inequality and interior estimates
  for the Cauchy–Riemann operator).
-/

public section

open scoped ENNReal NNReal ContDiff Topology
open MeasureTheory Metric Set Filter

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- **`Lᵖ` bounds on `\bar∂` up to a bounded error.** Let `1 ≤ p`, let `U ⊆ ℂ` be open and let
`K ⊆ U` be measurable. If `u` is smooth on `U`, `‖\bar∂u - g‖ ≤ M` on `K` and
`‖g‖_{Lᵖ(K)} ≤ B`, then `‖\bar∂u‖_{Lᵖ(K)} ≤ |K|^(1/p) M + B`. -/
theorem eLpNorm_conjWirtingerDeriv_restrict_le_of_norm_sub_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {p : ℝ≥0∞} (hp : 1 ≤ p) {U K : Set ℂ} (hU : IsOpen U)
    (hK : MeasurableSet K) (hKU : K ⊆ U) {u g : ℂ → E} (hu : ContDiffOn ℝ ∞ u U) {M : ℝ}
    {B : ℝ≥0} (hM : ∀ z ∈ K, ‖conjWirtingerDeriv u z 1 - g z‖ ≤ M)
    (hB : eLpNorm g p (volume.restrict K) ≤ B) :
    eLpNorm (fun z ↦ conjWirtingerDeriv u z 1) p (volume.restrict K) ≤
      volume K ^ p.toReal⁻¹ * ENNReal.ofReal M + B :=
  eLpNorm_restrict_le_of_norm_sub_le hp hK ((hu.conjWirtingerDeriv_apply_of_isOpen hU (m := 0)
    (by simp) 1).continuousOn.mono hKU |>.aestronglyMeasurable hK) hM hB

/-- **Uniform interior `W^{1,p}` bounds from `\bar∂` bounds.** Let `1 < p < ∞`, let `U ⊆ ℂ` be
open and `K ⊆ U` compact, and let `A, M, B ≥ 0`. There is a constant `N` such that every map `u`
smooth on `U` with `‖u‖ ≤ A` on `U`, and `‖\bar∂u - g‖ ≤ M` on `U` for some `g` with
`‖g‖_{Lᵖ(U)} ≤ B`, satisfies `‖Du‖_{Lᵖ(K)} ≤ N`. -/
theorem exists_eLpNorm_fderiv_le_of_norm_conjWirtingerDeriv_sub_le {p : ℝ≥0∞} (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (A M B : ℝ≥0) :
    ∃ N : ℝ≥0, ∀ u g : ℂ → F, ContDiffOn ℝ ∞ u U → (∀ z ∈ U, ‖u z‖ ≤ A) →
      (∀ z ∈ U, ‖conjWirtingerDeriv u z 1 - g z‖ ≤ M) →
      eLpNorm g p (volume.restrict U) ≤ B → eLpNorm (fderiv ℝ u) p (volume.restrict K) ≤ N := by
  -- Work on a bounded open neighbourhood `V` of `K` in `U`, where bounded maps lie in `Lᵖ`.
  set V := U ∩ thickening 1 K
  have hV : IsOpen V := hU.inter isOpen_thickening
  have hVU : V ⊆ U := inter_subset_left
  obtain ⟨C₁, hC₁⟩ := exists_eLpNorm_fderiv_le_eLpNorm_conjWirtingerDeriv_add_eLpNorm (F := F) hp
    hp_top hV hK (subset_inter hKU (self_subset_thickening one_pos K))
  set S : ℝ≥0∞ := volume V ^ p.toReal⁻¹
  have hS : S ≠ (∞ : ℝ≥0∞) := ENNReal.rpow_ne_top_of_nonneg (by positivity)
    (hK.isBounded.thickening.subset inter_subset_right).measure_lt_top.ne
  have hbound : ∀ {f : ℂ → F} {c : ℝ≥0}, AEStronglyMeasurable f (volume.restrict V) →
      (∀ z ∈ U, ‖f z‖ ≤ c) → eLpNorm f p (volume.restrict V) ≤ S * ENNReal.ofReal c := by
    intro f c hf hfc
    refine (eLpNorm_le_of_ae_bound hf ((ae_restrict_iff' hV.measurableSet).2
      (Eventually.of_forall fun z hz ↦ hfc z (hVU hz)))).trans_eq ?_
    rw [Measure.restrict_apply_univ]
  refine ⟨(C₁ * (S * ENNReal.ofReal M + B + S * ENNReal.ofReal A)).toNNReal,
    fun u g hu hA hM hB ↦ ?_⟩
  rw [ENNReal.coe_toNNReal (by simp [ENNReal.mul_ne_top, hS])]
  have hderiv : eLpNorm (fun z ↦ conjWirtingerDeriv u z 1) p (volume.restrict V) ≤
      S * ENNReal.ofReal M + B :=
    eLpNorm_conjWirtingerDeriv_restrict_le_of_norm_sub_le hp.le hU hV.measurableSet hVU hu
      (fun z hz ↦ hM z (hVU hz))
      ((eLpNorm_mono_measure _ (Measure.restrict_mono hVU le_rfl)).trans hB)
  refine (hC₁ u (hu.mono hVU)).trans ?_
  gcongr
  exact hbound (hu.continuousOn.mono hVU |>.aestronglyMeasurable hV.measurableSet) hA

/-- **Uniform Hölder bounds from `\bar∂` bounds.** Let `2 < p < ∞`, let `U ⊆ ℂ` be open and
`K ⊆ U` compact, and let `A, M, B ≥ 0`. There is a constant `C` such that every map `u` smooth on
`U` with `‖u‖ ≤ A` on `U`, and `‖\bar∂u - g‖ ≤ M` on `U` for some `g` with `‖g‖_{Lᵖ(U)} ≤ B`, is
Hölder continuous on `K` with exponent `1 - 2 / p` and constant `C`. -/
theorem exists_holderOnWith_of_norm_conjWirtingerDeriv_sub_le {p : ℝ≥0} (hp : 2 < p)
    {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) (A M B : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ u g : ℂ → F, ContDiffOn ℝ ∞ u U → (∀ z ∈ U, ‖u z‖ ≤ A) →
      (∀ z ∈ U, ‖conjWirtingerDeriv u z 1 - g z‖ ≤ M) →
      eLpNorm g p (volume.restrict U) ≤ B → HolderOnWith C (1 - 2 / p) u K := by
  -- A uniform bound `N` on `‖Du‖_{Lᵖ}` over a closed thickening `L = cthickening δ K` in `U`.
  obtain ⟨δ, hδ, hLU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨N, hN⟩ := exists_eLpNorm_fderiv_le_of_norm_conjWirtingerDeriv_sub_le (F := F)
    (p := p) (by exact_mod_cast one_lt_two.trans hp) ENNReal.coe_ne_top hU hK.cthickening hLU A M B
  obtain ⟨c, hc⟩ := exists_edist_le_of_contDiffOn_cthickening_of_two_lt (F := F) hp
  set α : ℝ≥0 := 1 - 2 / p
  set δ' : ℝ≥0 := (δ / 2).toNNReal
  have hδ' : (δ' : ℝ) = δ / 2 := Real.coe_toNNReal _ (by positivity)
  refine ⟨c * N + 2 * A * δ' ^ (-(α : ℝ)), fun u g hu hA hM hB ↦
    HolderOnWith.of_dist_lt_of_dist_le (by rw [← NNReal.coe_pos, hδ']; positivity)
      (fun x hx y _ hxy ↦ ?_) fun x hx y hy ↦ ?_⟩
  · -- Morrey's inequality on the `δ`-thickening of `K`.
    rw [hδ'] at hxy
    have h := (hc ((hu.mono hLU).of_le (by simp)) hx (by linarith)).trans
      (mul_le_mul_right (hN u g hu hA hM hB) _)
    -- Convert the extended-distance bound into a bound on distances.
    refine (edist_le_ofReal (by positivity)).1 (h.trans_eq ?_)
    rw [edist_dist, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_rpow_of_nonneg dist_nonneg α.coe_nonneg]
    push_cast
    ring
  · -- Points at distance at least `δ / 2` are handled by the sup bound.
    calc dist (u x) (u y) ≤ ‖u x‖ + ‖u y‖ := dist_le_norm_add_norm _ _
      _ ≤ A + A := add_le_add (hA x (hKU hx)) (hA y (hKU hy))
      _ = ((2 * A : ℝ≥0) : ℝ) := by push_cast; ring

end TauCeti
