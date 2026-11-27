/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.OrthogonalLeftInverse
public import TauCeti.Analysis.PDE.Vortex.Sobolev.Adjoint.Basic
import TauCeti.Analysis.Fredholm.Criteria

/-!
# The complementary inverse of the adjoint vortex operator and the cokernel projection

At a plane vortex `x` with `L∞` class `a`, the gauge-fixed normal model splits into the vortex
operator `L_x : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` (`TauCeti.Vortex.sobolevGaugeFixedOperator`) and its paired
adjoint block `L_x* : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` (`TauCeti.Vortex.sobolevGaugeFixedAdjoint`). The first is
onto with the kernel `ker L_x`, of dimension `2m`; the second is injective with closed range, the
`L²`-orthogonal complement of the values `K` of `ker L_x`. This file supplies the complementary
inverse of the adjoint block and the projection onto its cokernel.

* **The complementary inverse.** `L_x*` has a continuous left inverse
  (`TauCeti.Vortex.hasLeftInverse_sobolevGaugeFixedAdjoint`). Its orthogonal left inverse
  `R = ContinuousLinearMap.orthogonalLeftInverse L_x* : L² → H¹(ℂ)⁴` inverts `L_x*` on its range
  and vanishes on `K`.
* **The cokernel projection.** `1 - L_x* R` is the `L²`-orthogonal projection onto `K`
  (`TauCeti.Vortex.id_sub_sobolevGaugeFixedAdjoint_comp_orthogonalLeftInverse`), the slow
  cokernel projection `Π₋` of the paired block. Together with the inverse,
  `g = L_x* (R g) + Π₋ g` for every `g ∈ L²`.
* **The adjoint of the right inverse.** Let `Q` be the right inverse of `L_x` with values
  `L²`-orthogonal to its kernel, read on `L²` through the values `ι` of the fields. Its Hilbert
  space adjoint, formally `(L_x L_x*)⁻¹ L_x`, is `ι ∘ R`
  (`TauCeti.Vortex.adjoint_comp_orthogonalRightInverse_sobolevGaugeFixedOperator`). So `Q†`
  takes values in `H¹(ℂ)⁴`, and the weighted estimates for `Q†` and its parameter derivatives
  (`TauCeti.Analysis.PDE.Vortex.ParameterDerivative`) are estimates for `R`.

The dependence of `R` and `Π₋` on the vortex, over windows of divisors, is in
`TauCeti.Analysis.PDE.Vortex.Divisor.Smooth`; it comes from the smoothness of the orthogonal left
inverse in the operator (`ContinuousLinearMap.contDiffAt_orthogonalLeftInverse`).

## References

* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open MeasureTheory Filter TopologicalSpace ContinuousLinearMap
open scoped ENNReal RealInnerProductSpace Topology

local notation "μ⊤" => Measure.restrict (volume : Measure ℂ) ((⊤ : Opens ℂ) : Set ℂ)

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤}
  (hx : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0)
  (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
  (hax : a =ᵐ[μ⊤] x)
include hx hsol hlim hax

/-- **The adjoint vortex operator has a continuous left inverse.** At a `C¹` vortex `x` with
`|α| → 1` at infinity and with `L∞` class `a`, the realization `L_x* : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` is
injective with closed range, into a Hilbert space. -/
theorem hasLeftInverse_sobolevGaugeFixedAdjoint : (sobolevGaugeFixedAdjoint a).HasLeftInverse :=
  .of_injective_of_isClosed_range
    (isClosedEmbedding_sobolevGaugeFixedAdjoint hx hsol hlim hax).injective
    (isClosedEmbedding_sobolevGaugeFixedAdjoint hx hsol hlim hax).isClosed_range

/-- **The cokernel projection of the adjoint vortex operator.** At a `C¹` vortex `x` with
`|α| → 1` at infinity and with `L∞` class `a`, let `R` be the orthogonal left inverse of
`L_x* : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)`. Then `1 - L_x* R` is the `L²`-orthogonal projection onto the values
of the kernel of `L_x`, the cokernel of `L_x*`. -/
theorem id_sub_sobolevGaugeFixedAdjoint_comp_orthogonalLeftInverse
    [((sobolevGaugeFixedOperator a).ker.map
      sobolevFieldValues.toLinearMap).HasOrthogonalProjection] :
    ContinuousLinearMap.id ℝ _ -
        sobolevGaugeFixedAdjoint a ∘L (sobolevGaugeFixedAdjoint a).orthogonalLeftInverse =
      ((sobolevGaugeFixedOperator a).ker.map sobolevFieldValues.toLinearMap).starProjection := by
  set K := (sobolevGaugeFixedOperator a).ker.map sobolevFieldValues.toLinearMap
  have hrange := range_sobolevGaugeFixedAdjoint hx hsol hlim hax
  have : (sobolevGaugeFixedAdjoint a).range.HasOrthogonalProjection := hrange ▸ inferInstance
  have hK : (sobolevGaugeFixedAdjoint a).rangeᗮ = K := by rw [hrange, K.orthogonal_orthogonal]
  rw [id_sub_comp_orthogonalLeftInverse_eq_starProjection_orthogonal
    (hasLeftInverse_sobolevGaugeFixedAdjoint hx hsol hlim hax)]
  -- The orthogonal complement of the range `Kᗮ` is `K` (`hK`).
  congr

/-- **The adjoint of the orthogonal right inverse is the complementary inverse of `L_x*`.** At a
`C¹` vortex `x` with `|α| → 1` at infinity and with `L∞` class `a`, whose realization `L_x` has a
finite-dimensional kernel, let `Q` be the right inverse of `L_x` with values `L²`-orthogonal to
its kernel. Read on `L²(ℂ; ℝ⁴)` through the values `ι` of the fields, its Hilbert space adjoint is
`ι ∘ R`, where `R` is the orthogonal left inverse of `L_x*`. In particular `Q†` takes values in
`H¹(ℂ)⁴`. -/
theorem adjoint_comp_orthogonalRightInverse_sobolevGaugeFixedOperator
    [FiniteDimensional ℝ (sobolevGaugeFixedOperator a).ker] :
    adjoint (sobolevFieldValues ∘L
        orthogonalRightInverse sobolevFieldValues (sobolevGaugeFixedOperator a)) =
      sobolevFieldValues ∘L (sobolevGaugeFixedAdjoint a).orthogonalLeftInverse := by
  have hsurj := sobolevGaugeFixedOperator_surjective hx hsol hlim hax
  have hQ := (IsFredholm.of_surjective hsurj).isOrthogonalRightInverse_orthogonalRightInverse
    sobolevFieldValues_injective hsurj
  have hP := id_sub_sobolevGaugeFixedAdjoint_comp_orthogonalLeftInverse hx hsol hlim hax
  set K := (sobolevGaugeFixedOperator a).ker.map sobolevFieldValues.toLinearMap
  set Q := orthogonalRightInverse sobolevFieldValues (sobolevGaugeFixedOperator a)
  set R := (sobolevGaugeFixedAdjoint a).orthogonalLeftInverse
  refine ContinuousLinearMap.ext fun g ↦ ext_inner_right ℝ fun f ↦ ?_
  -- Split `g = L_x* (R g) + Π₋ g`; the values of `Q f` are orthogonal to `Π₋ g`.
  have hsplit : g = sobolevGaugeFixedAdjoint a (R g) + K.starProjection g := by
    rw [← hP, sub_apply, id_apply, comp_apply, add_sub_cancel]
  have horth : ⟪K.starProjection g, sobolevFieldValues (Q f)⟫ = 0 := by
    obtain ⟨y, hy, hyg⟩ := Submodule.mem_map.1 (K.starProjection_apply_mem g)
    rw [← hyg, ContinuousLinearMap.coe_coe, real_inner_comm]
    exact hQ.inner_eq_zero f y hy
  -- `⟪L_x* (R g), ι (Q f)⟫ = ⟪R g, ι (L_x (Q f))⟫ = ⟪ι (R g), f⟫`.
  have hadj : ⟪sobolevGaugeFixedAdjoint a (R g), sobolevFieldValues (Q f)⟫ =
      ⟪sobolevFieldValues (R g), f⟫ := by
    rw [real_inner_comm, ← inner_sobolevGaugeFixedOperator_sobolevFieldValues hx.continuous hax,
      hQ.rightInverse f, real_inner_comm]
  rw [adjoint_inner_left, comp_apply, comp_apply]
  conv_lhs => rw [hsplit]
  rw [inner_add_left, horth, add_zero, hadj]

end TauCeti.Vortex
