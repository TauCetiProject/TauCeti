/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Analysis.Normed.Operator.ClosedRange

/-!
# A map with upper semi-Fredholm derivative is proper near the point

A continuous map between infinite-dimensional Banach spaces need not be proper: a Fredholm linear
map with nonzero kernel has a noncompact fibre over zero. A map whose derivative at a point `a` is
closed-range with finite-dimensional complemented kernel — in particular, a **Fredholm**
operator — is nonetheless proper on a neighbourhood of `a`:

`∃ N ∈ 𝓝 a, ∀ L compact, N ∩ f ⁻¹' L is compact`.

This is Smale's local properness lemma, the geometric half of the input to the Sard--Smale theorem
(Smale, *An infinite dimensional version of Sard's theorem*, Amer. J. Math. 87 (1965), 861–866;
McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*, Appendix A). Its consequence
recorded here is that the preimage `f ⁻¹' L` of a compact set — in particular a level set
`f ⁻¹' {c}`, as occurs for moduli spaces defined by Fredholm equations — is a
**locally compact** space, even when its ambient Banach space is not locally compact.

The proof is quantitative rather than chart-theoretic. The a priori estimate
`ContinuousLinearMap.exists_projection_norm_le` supplies a continuous projection `P`
of `E` onto `ker f'` and a constant `C > 0` with `‖x‖ ≤ C * ‖f' x‖ + ‖P x‖`. On a small enough
closed ball `N` around `a`, strict differentiability turns this into the two-sided bound

`‖x - y‖ ≤ 2 * (C * ‖f x - f y‖) + 2 * ‖P x - P y‖`  for `x, y ∈ N`,

so the map `x ↦ (f x, P x)` is anti-Lipschitz on `N`. Its second component takes values in the
finite-dimensional space `ker f'`, where bounded sets have compact closure, so `x ↦ (f x, P x)`
sends `N ∩ f ⁻¹' L` into a compact box; being anti-Lipschitz, it reflects total boundedness, and
`N ∩ f ⁻¹' L` is totally bounded and closed, hence compact.

## Main declarations

* `TauCeti.one_sub_mul_norm_sub_le`: an a priori estimate survives a nonlinear
  approximation, degraded by its quality — the absorption step behind Peetre's lemma.
* `HasStrictFDerivAt.exists_mem_nhds_forall_isCompact_inter_preimage`: local properness.
* `HasStrictFDerivAt.exists_mem_nhds_isCompact_inter_preimage_singleton`: an arbitrary fibre is
  compact near the point of differentiation.
* `TauCeti.locallyCompactSpace_preimage` and `TauCeti.locallyCompactSpace_preimage_singleton`: the
  preimage of a compact set, and in particular a level set, along which the derivative is Fredholm
  is locally compact.

At a regular point, the zero set of a Fredholm map is a manifold of dimension its index;
`TauCeti.Analysis.Fredholm.LevelSet.Basic` supplies those charts. Local properness complements
this description at singular points and makes the critical values of a Fredholm map locally
closed in the Sard--Smale argument.
-/

public section

namespace TauCeti

open Filter Metric Set Submodule Topology
open scoped NNReal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
variable {f : E → F} {f' : E →L[𝕜] F} {a : E}

omit [ProperSpace 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- **An a priori estimate survives a nonlinear approximation, degraded by its quality.** Suppose
every vector is controlled by its image under `f'` together with an auxiliary additive map `P`,
as `‖z‖ ≤ C * ‖f' z‖ + ‖P z‖`, and `f` approximates `f'` on `N` to within `ε`. Then the same
control holds for `f` on `N`, with the left side scaled by `1 - C * ε`; it has content exactly
when `C * ε < 1`, and taking `ε ≤ (2 * C)⁻¹` gives the factor-two form properness uses.

Nothing about `P` beyond `map_sub` enters, so it need only be additive into a seminormed additive
group — no scalar-linearity, no idempotence, no constraint on its target. Taking it to be the
projection onto `ker f'` from `ContinuousLinearMap.exists_projection_norm_le` recovers the Peetre
estimate, which characterises semi-Fredholm operators — see Wendl, *Fredholm operators*,
Lemma 5.2. -/
theorem one_sub_mul_norm_sub_le {G : Type*} [SeminormedAddGroup G]
    {P : E →+ G} {C : ℝ} {N : Set E} {ε : ℝ≥0}
    (hC : 0 ≤ C) (hest : ∀ z, ‖z‖ ≤ C * ‖f' z‖ + ‖P z‖)
    (happ : ApproximatesLinearOn f f' N ε) {x : E} (hx : x ∈ N) {y : E} (hy : y ∈ N) :
    (1 - C * (ε : ℝ)) * ‖x - y‖ ≤ C * ‖f x - f y‖ + ‖P x - P y‖ := by
  have h1 := hest (x - y)
  have h2 := happ x hx y hy
  have h3 : ‖f' (x - y)‖ ≤ ‖f x - f y‖ + (ε : ℝ) * ‖x - y‖ := by
    exact (norm_le_norm_add_norm_sub (f x - f y) _).trans (add_le_add le_rfl h2)
  have h4 : C * ‖f' (x - y)‖ ≤ C * (‖f x - f y‖ + (ε : ℝ) * ‖x - y‖) :=
    mul_le_mul_of_nonneg_left h3 hC
  rw [map_sub P x y] at h1
  nlinarith

omit [ProperSpace 𝕜] [CompleteSpace E] [CompleteSpace F] in
/-- The two-sided bound gives anti-Lipschitzness of the coordinate `x ↦ (g x, P x)`.
The product norm is the maximum, so each component distance is at most the distance between
the pairs, and the two constants add. -/
private theorem antilipschitzWith_prodMk {G : Type*} [SeminormedAddCommGroup G] {N : Set E}
    {g : E → F} {P : E → G} {C : ℝ} (hC : 0 ≤ C)
    (key : ∀ x ∈ N, ∀ y ∈ N, ‖x - y‖ ≤ 2 * (C * ‖g x - g y‖) + 2 * ‖P x - P y‖) :
    AntilipschitzWith ⟨2 * C + 2, by positivity⟩ fun x : N => (g (x : E), P (x : E)) := by
  refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
  have hd1 : ‖g (x : E) - g (y : E)‖ ≤ dist (g (x : E), P (x : E)) (g (y : E), P (y : E)) := by
    rw [Prod.dist_eq, ← dist_eq_norm]
    exact le_max_left _ _
  have hd2 : ‖P (x : E) - P (y : E)‖ ≤ dist (g (x : E), P (x : E)) (g (y : E), P (y : E)) := by
    rw [Prod.dist_eq, ← dist_eq_norm]
    exact le_max_right _ _
  have hCd := mul_le_mul_of_nonneg_left hd1 hC
  rw [Subtype.dist_eq, dist_eq_norm]
  calc ‖(x : E) - (y : E)‖
      ≤ 2 * (C * ‖g (x : E) - g (y : E)‖) + 2 * ‖P (x : E) - P (y : E)‖ :=
        key (x : E) x.2 (y : E) y.2
    _ ≤ (2 * C + 2) * dist (g (x : E), P (x : E)) (g (y : E), P (y : E)) := by nlinarith

/-- **Local properness of a map with upper semi-Fredholm derivative.** If `f` is strictly
differentiable at `a` and its derivative there has closed range and finite-dimensional
complemented kernel, then `f` is proper on a neighbourhood `N` of `a`: the part of the preimage of
any compact set lying in `N` is compact.

Compare `ContinuousLinearMap.exists_projection_norm_le`, the linear estimate this is read off
from: the kernel direction, in which `f'` loses all control, is finite-dimensional, so the loss of
compactness it causes is harmless. -/
theorem _root_.HasStrictFDerivAt.exists_mem_nhds_forall_isCompact_inter_preimage
    (hf : HasStrictFDerivAt f f' a) (hclosed : IsClosed (f'.range : Set F))
    (hfinite : FiniteDimensional 𝕜 f'.ker) (hcompl : f'.ker.ClosedComplemented) :
    ∃ N ∈ 𝓝 a, ∀ L : Set F, IsCompact L → IsCompact (N ∩ f ⁻¹' L) := by
  obtain ⟨P, C, hC, _hPidemp, hPrange, hest⟩ :=
    f'.exists_projection_norm_le hclosed hcompl
  have hCpos : (0 : ℝ) < 2 * C := by linarith
  set ε : ℝ≥0 := ⟨(2 * C)⁻¹, inv_nonneg.2 hCpos.le⟩
  have hεcoe : (ε : ℝ) = (2 * C)⁻¹ := rfl
  have hεpos : 0 < ε := by
    rw [← NNReal.coe_pos, hεcoe]
    exact inv_pos.2 hCpos
  obtain ⟨s, hs, happ⟩ := hf.approximates_deriv_on_nhds (Or.inr hεpos)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hs
  set N : Set E := Metric.closedBall a (δ / 2)
  have hNs : N ⊆ s :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have happN : ApproximatesLinearOn f f' N ε := happ.mono_set hNs
  have hcontOn : ContinuousOn f N := happN.continuousOn
  -- the two-sided bound on `N`
  have hCε : C * (ε : ℝ) = 1 / 2 := by rw [hεcoe]; field_simp
  have key : ∀ x ∈ N, ∀ y ∈ N,
      ‖x - y‖ ≤ 2 * (C * ‖f x - f y‖) + 2 * ‖P x - P y‖ := by
    intro x hx y hy
    have h := one_sub_mul_norm_sub_le (P := P.toLinearMap.toAddMonoidHom) hC.le hest happN hx hy
    rw [hCε] at h
    simp only [LinearMap.toAddMonoidHom_coe, ContinuousLinearMap.coe_coe] at h
    linarith
  refine ⟨N, Metric.closedBall_mem_nhds a (by linarith), fun L hL => ?_⟩
  -- the compact box the projection lands in
  have hPmem : ∀ x, P x ∈ f'.ker := by
    intro x
    rw [← hPrange]
    exact ⟨x, rfl⟩
  let _ : FiniteDimensional 𝕜 f'.ker := hfinite
  have : ProperSpace f'.ker := FiniteDimensional.proper 𝕜 f'.ker
  let Pker : E →L[𝕜] f'.ker := P.codRestrict f'.ker hPmem
  let Kp := closure (Pker '' N)
  have hKpc : IsCompact Kp :=
    (Pker.lipschitzWith.isBounded_image Metric.isBounded_closedBall).isCompact_closure
  have hPN : ∀ x ∈ N, Pker x ∈ Kp := fun x hx => subset_closure ⟨x, hx, rfl⟩
  -- the anti-Lipschitz coordinate on `N`
  set Θ : N → F × f'.ker := fun x => (f (x : E), Pker (x : E))
  have hanti : AntilipschitzWith ⟨2 * C + 2, by positivity⟩ Θ :=
    antilipschitzWith_prodMk hC.le key
  have hΘcont : UniformContinuous Θ :=
    happN.lipschitzWith.uniformContinuous.prodMk
      (Pker.lipschitzWith.uniformContinuous.comp uniformContinuous_subtype_val)
  have hind : IsUniformInducing Θ := hanti.isUniformInducing hΘcont
  -- total boundedness, then compactness
  have htb : TotallyBounded
      ((Subtype.val : N → E) '' (Subtype.val : N → E) ⁻¹' (f ⁻¹' L)) := by
    refine TotallyBounded.image ?_ uniformContinuous_subtype_val
    refine (totallyBounded_preimage hind (hL.prod hKpc).totallyBounded).subset ?_
    exact fun x hx => ⟨hx, hPN (x : E) x.2⟩
  rw [Subtype.image_preimage_coe] at htb
  exact htb.isCompact_of_isClosed
    (hcontOn.preimage_isClosed_of_isClosed Metric.isClosed_closedBall hL.isClosed)

/-- An arbitrary fibre of `f` is compact near a point where the derivative has closed range and
finite-dimensional complemented kernel. This is the case `L = {c}` of local properness, and it is
the local compactness statement that a moduli space of a Fredholm problem inherits before any
global energy bound is imposed. -/
theorem _root_.HasStrictFDerivAt.exists_mem_nhds_isCompact_inter_preimage_singleton
    (hf : HasStrictFDerivAt f f' a) (hclosed : IsClosed (f'.range : Set F))
    (hfinite : FiniteDimensional 𝕜 f'.ker) (hcompl : f'.ker.ClosedComplemented) (c : F) :
    ∃ N ∈ 𝓝 a, IsCompact (N ∩ f ⁻¹' {c}) := by
  obtain ⟨N, hN, hprop⟩ :=
    hf.exists_mem_nhds_forall_isCompact_inter_preimage hclosed hfinite hcompl
  exact ⟨N, hN, hprop {c} isCompact_singleton⟩

/-- **The preimage of a compact set under a map with upper semi-Fredholm derivative is locally
compact.** If `f` is strictly differentiable at each point of `f ⁻¹' L`, its derivative there has
closed range and finite-dimensional complemented kernel, and `L` is compact, then `f ⁻¹' L`, with
the topology induced from `E`, is a locally compact space.

No compactness is assumed of the ambient Banach space, and none is available: the point is that
the hypotheses confine the failure of local compactness to the finite-dimensional kernel
direction, which is itself locally compact and is controlled by the kernel projection. -/
theorem locallyCompactSpace_preimage {D : E → E →L[𝕜] F} {L : Set F} (hL : IsCompact L)
    (hf : ∀ x ∈ f ⁻¹' L, HasStrictFDerivAt f (D x) x)
    (hclosed : ∀ x ∈ f ⁻¹' L, IsClosed ((D x).range : Set F))
    (hfinite : ∀ x ∈ f ⁻¹' L, FiniteDimensional 𝕜 (D x).ker)
    (hcompl : ∀ x ∈ f ⁻¹' L, (D x).ker.ClosedComplemented) :
    LocallyCompactSpace (f ⁻¹' L) := by
  have : WeaklyLocallyCompactSpace (f ⁻¹' L) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨N, hN, hprop⟩ :=
      (hf x x.2).exists_mem_nhds_forall_isCompact_inter_preimage
        (hclosed x x.2) (hfinite x x.2) (hcompl x x.2)
    refine ⟨(Subtype.val : (f ⁻¹' L) → E) ⁻¹' N, ?_, ?_⟩
    · rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, Subtype.image_preimage_coe,
        Set.inter_comm]
      exact hprop L hL
    · exact continuous_subtype_val.continuousAt.preimage_mem_nhds hN
  infer_instance

/-- **A level set of a map with upper semi-Fredholm derivative is locally compact**: the case
`L = {c}` of `TauCeti.locallyCompactSpace_preimage`, and the shape every moduli space of a Fredholm
problem takes. -/
theorem locallyCompactSpace_preimage_singleton {D : E → E →L[𝕜] F} {c : F}
    (hf : ∀ x ∈ f ⁻¹' {c}, HasStrictFDerivAt f (D x) x)
    (hclosed : ∀ x ∈ f ⁻¹' {c}, IsClosed ((D x).range : Set F))
    (hfinite : ∀ x ∈ f ⁻¹' {c}, FiniteDimensional 𝕜 (D x).ker)
    (hcompl : ∀ x ∈ f ⁻¹' {c}, (D x).ker.ClosedComplemented) :
    LocallyCompactSpace (f ⁻¹' {c}) :=
  locallyCompactSpace_preimage isCompact_singleton hf hclosed hfinite hcompl

end TauCeti
