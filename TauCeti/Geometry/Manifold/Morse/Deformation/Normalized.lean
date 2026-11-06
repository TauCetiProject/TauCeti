/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
public import TauCeti.Geometry.Manifold.Morse.PseudoGradient.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import TauCeti.Topology.Order.Sublevel
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import TauCeti.Geometry.Manifold.Flow.Complete
import TauCeti.Geometry.Manifold.IntegralCurve.Monotone
import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Deformation of sublevels along a normalized descending field

Let `f` be a smooth real function on a boundaryless finite-dimensional manifold `M`, and let `Y` be
a smooth vector field along which `f` strictly decreases on a compact set `K`, that is
`df(Y) < 0` on `K`. Rescaling `Y` by the positive function `1 / (-df(Y))` gives a field along
which `f` decreases at unit speed. Cut off away from `K`, this is a smooth vector field `X` with
compact support, a nonnegative multiple of `Y` at every point, which equals `Y / (-df(Y))` near
`K` (`TauCeti.exists_vectorField_eq_inv_smul_of_mvfderiv_lt_zero`).

When `K` is a compact band `f⁻¹[a, b]`, the flow of `X` lowers `f` at unit speed through the band
(`TauCeti.exists_flow_eq_inv_smul_of_mvfderiv_lt_zero`). Following it from a point `x` of
`{f ≤ b}` for the time `max (f x - a) 0`, exactly the time needed to reach the level `a`, is a
retraction of `{f ≤ b}` onto `{f ≤ a}`, and following it part of the way is a homotopy fixing
`{f ≤ a}` pointwise (`TauCeti.exists_sublevelDeformation_of_mvfderiv_lt_zero`). Near the band
the field `X` is a positive multiple of `Y`, so the points move along the flow lines of `Y`.

Two choices of `Y` give the classical constructions of Milnor's deformation.

* For a smooth Riemannian metric, `Y = -grad f` has `df(Y) = -‖grad f‖²`, so `X` is the normalized
  gradient field `-grad f / ‖grad f‖²` near the band
  (`TauCeti.exists_sublevelDeformation_neg_mgradient`).
* For a pseudo-gradient `Y` adapted to a Morse function, `X` is its rescaling with `df(X) = -1`
  near the band (`TauCeti.IsAdaptedPseudoGradient.exists_sublevelDeformation`).

In both cases the deformation retraction moves each point of `{f ≤ b}` to the level `a` in the time
`f x - a` and fixes `{f ≤ a}`; only the flow lines along which the points move depend on `Y`. The
construction of `TauCeti.exists_sublevelDeformation` uses instead a field built from charts, with
no metric or pseudo-gradient.

## Main results

* `TauCeti.exists_vectorField_eq_inv_smul_of_mvfderiv_lt_zero`: the cut-off normalized field
  `Y / (-df(Y))` near a compact set on which `df(Y) < 0`.
* `TauCeti.exists_flow_eq_inv_smul_of_mvfderiv_lt_zero`: its flow lowers `f` at unit speed through
  a compact band.
* `TauCeti.exists_sublevelDeformation_of_mvfderiv_lt_zero`: the deformation retraction of
  `{f ≤ b}` onto `{f ≤ a}` along this flow, with hitting time `f x - a`.
* `TauCeti.exists_sublevelDeformation_neg_mgradient`: the same along the normalized
  negative gradient `-grad f / ‖grad f‖²` of a smooth Riemannian metric.
* `TauCeti.IsAdaptedPseudoGradient.exists_sublevelDeformation`: the same along a rescaled adapted
  pseudo-gradient.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.1, whose proof uses the field `grad f / ‖grad f‖²`.
* J. Milnor, *Lectures on the h-cobordism theorem*, Princeton University Press, 1965,
  Definition 3.1 and Theorem 3.4, for gradient-like vector fields.
-/

public section

open Bundle Function Set Topology TauCeti.Manifold
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {f : M → ℝ} {Y : (x : M) → TangentSpace I x}

/-- **Normalizing a descending field near a compact set.** Let `f` be smooth and `Y` a smooth
vector field with `df(Y) < 0` on a compact set `K`. Then there is a smooth vector field `X`,
vanishing outside a compact set, which is a nonnegative multiple of `Y` at every point, along which
`f` never increases, and which equals the normalized field `Y / (-df(Y))` on an open neighbourhood
`U` of `K` on which `df(Y) < 0`. In particular `df(X) = -1` on `U`. -/
theorem exists_vectorField_eq_inv_smul_of_mvfderiv_lt_zero (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hY : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M)))
    {K : Set M} (hK : IsCompact K) (hKY : ∀ x ∈ K, mvfderiv I f x (Y x) < 0) :
    ∃ X : (x : M) → TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)) ∧
      (∀ x, ∃ c : ℝ, 0 ≤ c ∧ X x = c • Y x) ∧ (∀ x, mvfderiv I f x (X x) ≤ 0) ∧
      (∃ U, IsOpen U ∧ K ⊆ U ∧
        ∀ x ∈ U, mvfderiv I f x (Y x) < 0 ∧ X x = (-mvfderiv I f x (Y x))⁻¹ • Y x) ∧
      ∃ C, IsCompact C ∧ ∀ x ∉ C, X x = 0 := by
  -- The derivative `g = df(Y)` is smooth, and negative on an open set containing `K`.
  obtain ⟨g, hg⟩ : ∃ g : M → ℝ, ∀ y, g y = mvfderiv I f y (Y y) := ⟨_, fun _ ↦ rfl⟩
  have hgC : ContMDiff I 𝓘(ℝ) ∞ g := by
    rw [funext hg]
    exact (hf.contMDiff_mvfderiv_apply (m := ∞) (by simp)).comp hY
  have hW : IsOpen {y | g y < 0} := isOpen_lt hgC.continuous continuous_const
  obtain ⟨σ, hσC, hσ1, hσC_compact, hσW, hσ01⟩ := hK.exists_contMDiff_one_nhds_tsupport_subset I hW
    fun x hx ↦ by rw [mem_ofPred_eq, hg]; exact hKY x hx
  have hσg : ∀ y, σ y ≠ 0 → g y < 0 := fun y hy ↦ hσW (subset_tsupport _ hy)
  -- Off `{g < 0}` the cutoff vanishes, and on `{g < 0}` the normalized field is smooth.
  have hZ : ContMDiffOn I I.tangent ∞
      (fun y ↦ (⟨y, (-g y)⁻¹ • Y y⟩ : TangentBundle I M)) {y | g y < 0} :=
    (hgC.neg.contMDiffOn.inv₀ fun y (hy : g y < 0) ↦ neg_ne_zero.2 hy.ne).smul_section
      hY.contMDiffOn
  obtain ⟨X, hX⟩ : ∃ X : (x : M) → TangentSpace I x, ∀ y, X y = σ y • ((-g y)⁻¹ • Y y) :=
    ⟨_, fun _ ↦ rfl⟩
  have hdfX : ∀ y, mvfderiv I f y (X y) = -σ y := fun y ↦ by
    rw [hX, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← hg]
    by_cases hy : σ y = 0
    · simp [hy]
    · field_simp [(hσg y hy).ne]
  refine ⟨X, ?_, fun y ↦ ⟨σ y * (-g y)⁻¹, ?_, by rw [hX, smul_smul]⟩,
    fun y ↦ by rw [hdfX]; linarith [(hσ01 y).1],
    ⟨interior {y | σ y = 1}, isOpen_interior, subset_interior_iff_mem_nhdsSet.2 hσ1,
      fun y hy ↦ ?_⟩, tsupport σ, hσC_compact, fun y hy ↦ ?_⟩
  · rw [funext hX]
    exact ContMDiffOn.smul_section_of_tsupport hσC.contMDiffOn hW hσW hZ
  · by_cases hy : σ y = 0
    · simp [hy]
    · exact mul_nonneg (hσ01 y).1 (inv_nonneg.2 (by linarith [hσg y hy]))
  · have hσy : σ y = 1 := interior_subset hy
    refine ⟨?_, by rw [hX, hσy, one_smul, hg]⟩
    rw [← hg]
    exact hσg y (by rw [hσy]; exact one_ne_zero)
  · rw [hX, image_eq_zero_of_notMem_tsupport hy, zero_smul]

variable [I.Boundaryless]

/-- **The flow of a normalized descending field.** Let `f` be smooth, let the band `f⁻¹[a, b]` be
compact, and let `Y` be a smooth vector field with `df(Y) < 0` on the band. Then there is a smooth
vector field `X`, a nonnegative multiple of `Y` at every point and equal to the normalized field
`Y / (-df(Y))` on an open neighbourhood of the band, whose flow `φ` is jointly smooth in time and
space, never increases `f`, and lowers `f` at unit speed through the band: if `f x ≤ b`, `t ≥ 0`
and `f x - t ≥ a`, then `f (φ t x) = f x - t`. -/
theorem exists_flow_eq_inv_smul_of_mvfderiv_lt_zero (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hY : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M))) {a b : ℝ}
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hbandY : ∀ x, a ≤ f x → f x ≤ b → mvfderiv I f x (Y x) < 0) :
    ∃ X : (x : M) → TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)) ∧
      (∀ x, ∃ c : ℝ, 0 ≤ c ∧ X x = c • Y x) ∧
      (∃ U, IsOpen U ∧ f ⁻¹' Icc a b ⊆ U ∧ ∀ x ∈ U, X x = (-mvfderiv I f x (Y x))⁻¹ • Y x) ∧
      ∃ φ : Flow ℝ M, ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ φ p.1 p.2) ∧
        (∀ x, IsMIntegralCurve (fun t ↦ φ t x) X) ∧ (∀ x, Antitone fun t ↦ f (φ t x)) ∧
        ∀ x t, 0 ≤ t → a ≤ f x - t → f x ≤ b → f (φ t x) = f x - t := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨X, hX, hXY, hXle, ⟨U, hU, hKU, hXU⟩, C, hC, hXC⟩ :=
    exists_vectorField_eq_inv_smul_of_mvfderiv_lt_zero hf hY hcompact fun x hx ↦
      hbandY x hx.1 hx.2
  have hX1 : ContMDiff I I.tangent 1 (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)) :=
    hX.of_le (by simp)
  have hcomplete := isCompleteVectorField_of_isCompact_of_eq_zero_off hX1 hC hXC
  have hfd : MDifferentiable I 𝓘(ℝ) f := hf.mdifferentiable (by simp)
  -- On `U` the field `X` is `Y / (-df(Y))`, so `df(X) = -1` there.
  have hdfX : ∀ y ∈ U, mvfderiv I f y (X y) = -1 := fun y hy ↦ by
    rw [(hXU y hy).2, map_smul, smul_eq_mul, inv_mul_eq_div, div_neg, div_self (hXU y hy).1.ne]
  refine ⟨X, hX, hXY, ⟨U, hU, hKU, fun x hx ↦ (hXU x hx).2⟩, globalFlow X hX1 hcomplete,
    contMDiff_globalFlow_uncurry hcomplete le_top hX, isMIntegralCurve_globalFlow hX1 hcomplete,
    fun x ↦ (isMIntegralCurve_globalFlow hX1 hcomplete x).antitone_comp (fun _ ↦ hfd _)
      fun _ ↦ hXle _, fun x t ht hxt hxb ↦ ?_⟩
  exact apply_globalFlow_eq_sub hX1 hcomplete hf.continuous hU hdfX
    (fun y hya hyb ↦ hKU ⟨hya, hyb⟩) ht hxt hxb

/-- **Deformation of sublevels along a normalized descending field** (Milnor, Theorem 3.1). Let
`f` be smooth, `a ≤ b`, let the band `f⁻¹[a, b]` be compact, and let `Y` be a smooth vector field
with `df(Y) < 0` on the band. Let `X` be a smooth vector field equal to the normalized field
`Y / (-df(Y))` on an open neighbourhood of the band, with flow `φ`. Following `φ` from each point
`x` of `{f ≤ b}` for the time `max (f x - a) 0` it takes to reach the level `a` is a retraction `r`
of `{f ≤ b}` onto `{f ≤ a}`, and there is a homotopy from the inclusion of `r` to the identity
fixing `{f ≤ a}` pointwise. -/
theorem exists_sublevelDeformation_of_mvfderiv_lt_zero (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hY : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M))) {a b : ℝ}
    (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hbandY : ∀ x, a ≤ f x → f x ≤ b → mvfderiv I f x (Y x) < 0) :
    ∃ X : (x : M) → TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)) ∧
      (∃ U, IsOpen U ∧ f ⁻¹' Icc a b ⊆ U ∧ ∀ x ∈ U, X x = (-mvfderiv I f x (Y x))⁻¹ • Y x) ∧
      ∃ φ : Flow ℝ M, (∀ x, IsMIntegralCurve (fun t ↦ φ t x) X) ∧
        ∃ r : C({x | f x ≤ b}, {x | f x ≤ a}),
          (∀ x, (r x : M) = φ (max (f x - a) 0) x) ∧
          (∀ x, r (sublevelInclusion f a b hab x) = x) ∧
          Nonempty (ContinuousMap.HomotopyRel ((sublevelInclusion f a b hab).comp r)
            (ContinuousMap.id _) {x | f x ≤ a}) := by
  obtain ⟨X, hX, -, hXU, φ, -, hφX, -, hφ⟩ :=
    exists_flow_eq_inv_smul_of_mvfderiv_lt_zero hf hY hcompact hbandY
  exact ⟨X, hX, hXU, φ, hφX,
    exists_sublevelDeformation_of_apply_eq_sub hf.continuous hab φ φ.cont' φ.map_zero_apply hφ⟩

/-- **Deformation of sublevels along the normalized gradient** (Milnor, Theorem 3.1). Let `f` be
smooth on a manifold with a smooth Riemannian metric, `a ≤ b`, and let the band `f⁻¹[a, b]` be
compact and contain no critical point of `f`. Let `X` be a smooth vector field equal to the
normalized negative gradient `-grad f / ‖grad f‖²` on an open neighbourhood of the band, with flow
`φ`. Following `φ` from each point `x` of `{f ≤ b}` for the time `max (f x - a) 0` it takes to
reach the level `a` is a retraction `r` of `{f ≤ b}` onto `{f ≤ a}`, and there is a homotopy from
the inclusion of `r` to the identity fixing `{f ≤ a}` pointwise. -/
theorem exists_sublevelDeformation_neg_mgradient
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, a ≤ f x → f x ≤ b → mfderiv I 𝓘(ℝ) f x ≠ 0) :
    ∃ X : (x : M) → TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)) ∧
      (∃ U, IsOpen U ∧ f ⁻¹' Icc a b ⊆ U ∧
        ∀ x ∈ U, X x = (‖mgradient I f x‖ ^ 2)⁻¹ • -mgradient I f x) ∧
      ∃ φ : Flow ℝ M, (∀ x, IsMIntegralCurve (fun t ↦ φ t x) X) ∧
        ∃ r : C({x | f x ≤ b}, {x | f x ≤ a}),
          (∀ x, (r x : M) = φ (max (f x - a) 0) x) ∧
          (∀ x, r (sublevelInclusion f a b hab x) = x) ∧
          Nonempty (ContinuousMap.HomotopyRel ((sublevelInclusion f a b hab).comp r)
            (ContinuousMap.id _) {x | f x ≤ a}) := by
  -- Along `-grad f` the derivative of `f` is `-‖grad f‖²`, negative off the critical points.
  have hdf : ∀ x, mvfderiv I f x (-mgradient I f x) = -‖mgradient I f x‖ ^ 2 := fun x ↦ by
    rw [map_neg, mvfderiv_apply_mgradient, real_inner_self_eq_norm_sq]
  have hY : ContMDiff I I.tangent ∞
      (fun x ↦ (⟨x, -mgradient I f x⟩ : TangentBundle I M)) :=
    have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
    contMDiff_neg_mgradient (n := ∞) (by simpa using hf)
  obtain ⟨X, hX, ⟨U, hU, hKU, hXU⟩, rest⟩ := exists_sublevelDeformation_of_mvfderiv_lt_zero hf hY
    hab hcompact fun x hxa hxb ↦ by
      rw [hdf, neg_lt_zero]
      exact pow_pos (norm_pos_iff.2 fun h ↦
        hreg x hxa hxb (mvfderiv_eq_zero_iff.1 (mgradient_eq_zero_iff.1 h))) 2
  exact ⟨X, hX, ⟨U, hU, hKU, fun x hx ↦ by rw [hXU x hx, hdf, neg_neg]⟩, rest⟩


namespace IsAdaptedPseudoGradient

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {Y : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- **Deformation of sublevels along a rescaled pseudo-gradient.** Let `Y` be a pseudo-gradient
adapted to a smooth function `f`, let `a ≤ b`, and let the band `f⁻¹[a, b]` be compact and contain
no critical point of `f`. Let `X` be a smooth vector field equal to the rescaled pseudo-gradient
`Y / (-df(Y))`, with `df(X) = -1`, on an open neighbourhood of the band, with flow `φ`. Following
`φ` from each point `x` of `{f ≤ b}` for the time `max (f x - a) 0` it takes to reach the level `a`
is a retraction `r` of `{f ≤ b}` onto `{f ≤ a}`, and there is a homotopy from the inclusion of `r`
to the identity fixing `{f ≤ a}` pointwise. -/
theorem exists_sublevelDeformation (hY : IsAdaptedPseudoGradient f Y)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, a ≤ f x → f x ≤ b → mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x ≠ 0) :
    ∃ X : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞ (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∃ U, IsOpen U ∧ f ⁻¹' Icc a b ⊆ U ∧
        ∀ x ∈ U, X x = (-mvfderiv 𝓘(ℝ, E) f x (Y x))⁻¹ • Y x) ∧
      ∃ φ : Flow ℝ M, (∀ x, IsMIntegralCurve (fun t ↦ φ t x) X) ∧
        ∃ r : C({x | f x ≤ b}, {x | f x ≤ a}),
          (∀ x, (r x : M) = φ (max (f x - a) 0) x) ∧
          (∀ x, r (sublevelInclusion f a b hab x) = x) ∧
          Nonempty (ContinuousMap.HomotopyRel ((sublevelInclusion f a b hab).comp r)
            (ContinuousMap.id _) {x | f x ≤ a}) :=
  exists_sublevelDeformation_of_mvfderiv_lt_zero hf hY.contMDiff hab hcompact
    fun x hxa hxb ↦ hY.mvfderiv_apply_lt_zero x (hreg x hxa hxb)

end IsAdaptedPseudoGradient

end TauCeti
