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
import TauCeti.Geometry.Manifold.Flow.Complete
import TauCeti.Geometry.Manifold.Flow.Parametric
import TauCeti.Geometry.Manifold.IntegralCurve.Monotone
import TauCeti.Geometry.Manifold.VectorField.Normalized
import TauCeti.Geometry.Manifold.VectorField.Parametric
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Deformation of sublevels along a normalized descending field

Let `f` be a smooth real function on a boundaryless finite-dimensional manifold `M`, and let `Y` be
a smooth vector field along which `f` strictly decreases on a compact set `K`, that is
`df(Y) < 0` on `K`. Cut off away from `K`, its rescaling `Y / (-df(Y))` is a smooth vector field
`X` with compact support, a nonnegative multiple of `Y` at every point, along which `f` decreases at
unit speed near `K` (`TauCeti.exists_vectorField_eq_inv_smul_of_mvfderiv_lt_zero`).

When `K` is a compact band `f⁻¹[a, b]`, the flow of `X` lowers `f` at unit speed through the band
(`TauCeti.exists_flow_apply_eq_sub_of_mvfderiv_lt_zero`). Following it from a point `x` of
`{f ≤ b}` for the time `max (f x - a) 0` is a retraction of `{f ≤ b}` onto `{f ≤ a}`: a point with
`a ≤ f x` reaches the level `a` after the time `f x - a`, and a point with `f x ≤ a` stays fixed.
Following the flow part of the way is a homotopy fixing `{f ≤ a}` pointwise
(`TauCeti.exists_sublevelDeformation_of_mvfderiv_lt_zero`). Near the band the field `X` is a
positive multiple of `Y`, so the points move along the flow lines of `Y`.

Two choices of `Y` give the classical constructions of Milnor's deformation.

* For a smooth Riemannian metric, `Y = -grad f` has `df(Y) = -‖grad f‖²`, so `X` is the normalized
  gradient field `-grad f / ‖grad f‖²` near the band
  (`TauCeti.exists_sublevelDeformation_neg_mgradient`).
* For a pseudo-gradient `Y` adapted to a Morse function, `X` is its rescaling with `df(X) = -1`
  near the band (`TauCeti.IsAdaptedPseudoGradient.exists_sublevelDeformation`).

In both cases the deformation retraction moves each point of `{f ≤ b}` with `a ≤ f x` to the level
`a` in the time `f x - a` and fixes `{f ≤ a}`; only the flow lines along which the points move
depend on `Y`. The construction of `TauCeti.exists_sublevelDeformation` uses instead a field built
from charts, with no metric or pseudo-gradient.

The retractions obtained from two descending fields `Y₀` and `Y₁` are homotopic relative to
`{f ≤ a}`, and the homotopy can be taken through retractions of the same kind
(`TauCeti.exists_homotopyRel_sublevelRetraction_of_mvfderiv_lt_zero`). The normalized fields `X₀`
and `X₁` both have `df(Xᵢ) = -1` near the band, which is an affine condition, so every field
`(1 - s) • X₀ + s • X₁` of the segment between them has it too. These fields form a jointly smooth
family (`ContMDiff.one_sub_smul_add_smul_vectorField`), so their flows depend continuously on `s`
(`TauCeti.contMDiffAt_flowOf_param`), and following them for the time `max (f x - a) 0` deforms
the retraction along `X₀` into the retraction along `X₁`
(`TauCeti.exists_homotopyRel_sublevelRetraction_of_apply_eq_sub`). In particular the retractions
along a rescaled adapted pseudo-gradient and along the normalized gradient are homotopic relative
to `{f ≤ a}`
(`TauCeti.IsAdaptedPseudoGradient.exists_homotopicRel_sublevelRetraction_neg_mgradient`).

## Main results

* `TauCeti.exists_flow_apply_eq_sub_of_mvfderiv_lt_zero`: the flow of the cut-off normalized field
  `Y / (-df(Y))` lowers `f` at unit speed through a compact band.
* `TauCeti.exists_sublevelDeformation_of_mvfderiv_lt_zero`: the deformation retraction of
  `{f ≤ b}` onto `{f ≤ a}` along this flow, with hitting time `max (f x - a) 0`.
* `TauCeti.exists_sublevelDeformation_neg_mgradient`: the same along the normalized
  negative gradient `-grad f / ‖grad f‖²` of a smooth Riemannian metric.
* `TauCeti.IsAdaptedPseudoGradient.exists_sublevelDeformation`: the same along a rescaled adapted
  pseudo-gradient.
* `TauCeti.exists_homotopyRel_sublevelRetraction_of_mvfderiv_lt_zero`: the retractions along two
  normalized descending fields are homotopic relative to `{f ≤ a}` through the retractions along
  the segment of fields between them.
* `TauCeti.IsAdaptedPseudoGradient.exists_homotopicRel_sublevelRetraction_neg_mgradient`: the
  retractions along a rescaled adapted pseudo-gradient and along the normalized gradient are
  homotopic relative to `{f ≤ a}`.

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

variable [I.Boundaryless]

/-- **The flow of a normalized descending field.** Let `f` be smooth, let the band `f⁻¹[a, b]` be
compact, and let `Y` be a smooth vector field with `df(Y) < 0` on the band. Then there is a smooth
vector field `X`, a nonnegative multiple of `Y` at every point and equal to the normalized field
`Y / (-df(Y))` on an open neighbourhood of the band, whose flow `φ` is jointly smooth in time and
space, never increases `f`, and lowers `f` at unit speed through the band: if `f x ≤ b`, `t ≥ 0`
and `f x - t ≥ a`, then `f (φ t x) = f x - t`. -/
theorem exists_flow_apply_eq_sub_of_mvfderiv_lt_zero (hf : ContMDiff I 𝓘(ℝ) ∞ f)
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
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
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
`x` of `{f ≤ b}` for the time `max (f x - a) 0`, which brings `x` to the level `a` if `a ≤ f x` and
leaves it fixed if `f x ≤ a`, is a retraction `r` of `{f ≤ b}` onto `{f ≤ a}`, and there is a
homotopy from the inclusion of `r` to the identity fixing `{f ≤ a}` pointwise. -/
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
    exists_flow_apply_eq_sub_of_mvfderiv_lt_zero hf hY hcompact hbandY
  exact ⟨X, hX, hXU, φ, hφX,
    exists_sublevelDeformation_of_apply_eq_sub hf.continuous hab φ φ.cont' φ.map_zero_apply hφ⟩

/-- **Deformation of sublevels along the normalized gradient** (Milnor, Theorem 3.1). Let `f` be
smooth on a manifold with a smooth Riemannian metric, `a ≤ b`, and let the band `f⁻¹[a, b]` be
compact and contain no critical point of `f`. Let `X` be a smooth vector field equal to the
normalized negative gradient `-grad f / ‖grad f‖²` on an open neighbourhood of the band, with flow
`φ`. Following `φ` from each point `x` of `{f ≤ b}` for the time `max (f x - a) 0`, which brings
`x` to the level `a` if `a ≤ f x` and leaves it fixed if `f x ≤ a`, is a retraction `r` of
`{f ≤ b}` onto `{f ≤ a}`, and there is a homotopy from the inclusion of `r` to the identity fixing
`{f ≤ a}` pointwise. -/
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

/-- **The retractions along two normalized descending fields are homotopic through retractions of
the same kind.** Let `f` be smooth, `a ≤ b`, let the band `f⁻¹[a, b]` be compact, and let `Y₀` and
`Y₁` be smooth vector fields with `df(Yᵢ) < 0` on the band. Then there are smooth vector fields
`X₀` and `X₁`, equal to the normalized fields `Yᵢ / (-df(Yᵢ))` on an open neighbourhood `U` of the
band, such that every field `Xₛ = (1 - s) • X₀ + s • X₁`, `s ∈ ℝ`, is complete and has
`df(Xₛ) = -1` on `U`. For `s ∈ [0, 1]`, following the flow of `Xₛ` from each point `x` of
`{f ≤ b}` for the time `max (f x - a) 0` is a retraction of `{f ≤ b}` onto `{f ≤ a}`, and these
retractions form a homotopy, relative to `{f ≤ a}`, from the retraction `r₀` along `X₀` to the
retraction `r₁` along `X₁`. So the deformation retractions built from `Y₀` and from `Y₁` are
homotopic through deformation retractions of the same kind, each moving the points of the band to
the level `a` at unit speed. -/
theorem exists_homotopyRel_sublevelRetraction_of_mvfderiv_lt_zero (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {Y₀ Y₁ : (x : M) → TangentSpace I x}
    (hY₀ : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, Y₀ x⟩ : TangentBundle I M)))
    (hY₁ : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, Y₁ x⟩ : TangentBundle I M))) {a b : ℝ}
    (hab : a ≤ b) (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hband₀ : ∀ x, a ≤ f x → f x ≤ b → mvfderiv I f x (Y₀ x) < 0)
    (hband₁ : ∀ x, a ≤ f x → f x ≤ b → mvfderiv I f x (Y₁ x) < 0) :
    ∃ X₀ X₁ : (x : M) → TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, X₀ x⟩ : TangentBundle I M)) ∧
      ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, X₁ x⟩ : TangentBundle I M)) ∧
      (∃ U, IsOpen U ∧ f ⁻¹' Icc a b ⊆ U ∧ ∀ x ∈ U,
        X₀ x = (-mvfderiv I f x (Y₀ x))⁻¹ • Y₀ x ∧ X₁ x = (-mvfderiv I f x (Y₁ x))⁻¹ • Y₁ x ∧
          ∀ s : ℝ, mvfderiv I f x ((1 - s) • X₀ x + s • X₁ x) = -1) ∧
      (∀ s : ℝ, IsCompleteVectorField fun x ↦ (1 - s) • X₀ x + s • X₁ x) ∧
      ∃ r₀ r₁ : C({x | f x ≤ b}, {x | f x ≤ a}),
        (∀ x, (r₀ x : M) = flowOf X₀ (max (f x - a) 0) x) ∧
        (∀ x, (r₁ x : M) = flowOf X₁ (max (f x - a) 0) x) ∧
        (∀ x, r₀ (sublevelInclusion f a b hab x) = x) ∧
        (∀ x, r₁ (sublevelInclusion f a b hab x) = x) ∧
        ∃ F : ContinuousMap.HomotopyRel r₀ r₁ {x | f x ≤ a}, ∀ s x,
          (F (s, x) : M) =
            flowOf (fun y ↦ (1 - (s : ℝ)) • X₀ y + (s : ℝ) • X₁ y) (max (f x - a) 0) x := by
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  obtain ⟨X₀, hX₀, -, -, ⟨U₀, hU₀, hKU₀, hXU₀⟩, C₀, hC₀, hXC₀⟩ :=
    exists_vectorField_eq_inv_smul_of_mvfderiv_lt_zero hf hY₀ hcompact fun x hx ↦
      hband₀ x hx.1 hx.2
  obtain ⟨X₁, hX₁, -, -, ⟨U₁, hU₁, hKU₁, hXU₁⟩, C₁, hC₁, hXC₁⟩ :=
    exists_vectorField_eq_inv_smul_of_mvfderiv_lt_zero hf hY₁ hcompact fun x hx ↦
      hband₁ x hx.1 hx.2
  set v : ℝ → (x : M) → TangentSpace I x := fun s x ↦ (1 - s) • X₀ x + s • X₁ x
  have hv : ContMDiff (𝓘(ℝ).prod I) I.tangent 1
      (fun p : ℝ × M ↦ (⟨p.2, v p.1 p.2⟩ : TangentBundle I M)) :=
    (hX₀.one_sub_smul_add_smul_vectorField hX₁).of_le (by simp)
  -- Every field of the segment vanishes off the compact set `C₀ ∪ C₁`, so it is complete.
  have hcomplete : ∀ s, IsCompleteVectorField (v s) := fun s ↦
    isCompleteVectorField_of_isCompact_of_eq_zero_off (hv.apply_param s) (hC₀.union hC₁)
      fun x hx ↦ by
        rw [mem_union, not_or] at hx
        simp [v, hXC₀ x hx.1, hXC₁ x hx.2]
  -- On `U₀ ∩ U₁` both ends lower `f` at unit speed, hence so does every field of the segment.
  have hdf : ∀ s, ∀ y ∈ U₀ ∩ U₁, mvfderiv I f y (v s y) = -1 := fun s y hy ↦ by
    have h₀ : mvfderiv I f y (X₀ y) = -1 := by
      rw [(hXU₀ y hy.1).2, map_smul, smul_eq_mul, inv_mul_eq_div, div_neg,
        div_self (hXU₀ y hy.1).1.ne]
    have h₁ : mvfderiv I f y (X₁ y) = -1 := by
      rw [(hXU₁ y hy.2).2, map_smul, smul_eq_mul, inv_mul_eq_div, div_neg,
        div_self (hXU₁ y hy.2).1.ne]
    simp only [v, map_add, map_smul, smul_eq_mul, h₀, h₁]
    ring
  -- The flows of the segment depend continuously on the parameter, the time and the point, and
  -- each lowers `f` at unit speed through the band.
  have hcont : Continuous fun p : ℝ × ℝ × M ↦ flowOf (v p.1) p.2.1 p.2.2 :=
    continuous_iff_continuousAt.2 fun p ↦ (contMDiffAt_flowOf_param le_rfl hv
      ((hcomplete p.1).mem_flowDomain p.2.1 p.2.2)).continuousAt
  obtain ⟨r₀, r₁, hr₀, hr₁, hincl₀, hincl₁, F, hF⟩ :=
    exists_homotopyRel_sublevelRetraction_of_apply_eq_sub hf.continuous hab
      (fun s ↦ flowOf (v s)) (hcont.comp (continuous_subtypeVal.prodMap continuous_id))
      (fun s ↦ flowOf_zero (v s)) fun s x t ht hxt hxb ↦ by
        rw [flowOf_eq_globalFlow (hv.apply_param s) (hcomplete s)]
        exact apply_globalFlow_eq_sub (hv.apply_param s) (hcomplete s) hf.continuous
          (hU₀.inter hU₁) (hdf s) (fun y hya hyb ↦ ⟨hKU₀ ⟨hya, hyb⟩, hKU₁ ⟨hya, hyb⟩⟩) ht hxt hxb
  have hv₀ : v 0 = X₀ := funext fun x ↦ by simp [v]
  have hv₁ : v 1 = X₁ := funext fun x ↦ by simp [v]
  refine ⟨X₀, X₁, hX₀, hX₁, ⟨U₀ ∩ U₁, hU₀.inter hU₁, fun x hx ↦ ⟨hKU₀ hx, hKU₁ hx⟩,
    fun x hx ↦ ⟨(hXU₀ x hx.1).2, (hXU₁ x hx.2).2, fun s ↦ hdf s x hx⟩⟩, hcomplete, r₀, r₁,
    fun x ↦ ?_, fun x ↦ ?_, hincl₀, hincl₁, F, hF⟩
  · rw [hr₀, Set.Icc.coe_zero, hv₀]
  · rw [hr₁, Set.Icc.coe_one, hv₁]


namespace IsAdaptedPseudoGradient

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {Y : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- **Deformation of sublevels along a rescaled pseudo-gradient.** Let `Y` be a pseudo-gradient
adapted to a smooth function `f`, let `a ≤ b`, and let the band `f⁻¹[a, b]` be compact and contain
no critical point of `f`. Let `X` be a smooth vector field equal to the rescaled pseudo-gradient
`Y / (-df(Y))`, with `df(X) = -1`, on an open neighbourhood of the band, with flow `φ`. Following
`φ` from each point `x` of `{f ≤ b}` for the time `max (f x - a) 0`, which brings `x` to the level
`a` if `a ≤ f x` and leaves it fixed if `f x ≤ a`, is a retraction `r` of `{f ≤ b}` onto
`{f ≤ a}`, and there is a homotopy from the inclusion of `r` to the identity fixing `{f ≤ a}`
pointwise. -/
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

/-- **The pseudo-gradient and normalized-gradient retractions are homotopic.** Let `Y` be a
pseudo-gradient adapted to a smooth function `f` on a manifold with a smooth Riemannian metric, let
`a ≤ b`, and let the band `f⁻¹[a, b]` be compact and contain no critical point of `f`. Let `X` be
the rescaled pseudo-gradient `Y / (-df(Y))` and `X'` the normalized negative gradient
`-grad f / ‖grad f‖²` on an open neighbourhood of the band, both complete smooth vector fields,
so that `df(X) = df(X') = -1` there. Following their flows from each point `x` of `{f ≤ b}` for the
time `max (f x - a) 0` gives retractions `r` and `r'` of `{f ≤ b}` onto `{f ≤ a}`: each moves a
point of the band to the level `a` at unit speed and fixes `{f ≤ a}`. These two retractions are
homotopic relative to `{f ≤ a}`. A homotopy through the retractions along the fields of the
segment from `X` to `X'` is `TauCeti.exists_homotopyRel_sublevelRetraction_of_mvfderiv_lt_zero`
for `Y` and `-grad f`. -/
theorem exists_homotopicRel_sublevelRetraction_neg_mgradient
    [RiemannianBundle (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
    [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M ↦ TangentSpace 𝓘(ℝ, E) x)]
    (hY : IsAdaptedPseudoGradient f Y) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) {a b : ℝ} (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, a ≤ f x → f x ≤ b → mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x ≠ 0) :
    ∃ X X' : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞ (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞ (fun x ↦ (⟨x, X' x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      IsCompleteVectorField X ∧ IsCompleteVectorField X' ∧
      (∃ U, IsOpen U ∧ f ⁻¹' Icc a b ⊆ U ∧ ∀ x ∈ U,
        X x = (-mvfderiv 𝓘(ℝ, E) f x (Y x))⁻¹ • Y x ∧
        X' x = (‖mgradient 𝓘(ℝ, E) f x‖ ^ 2)⁻¹ • -mgradient 𝓘(ℝ, E) f x) ∧
      ∃ r r' : C({x | f x ≤ b}, {x | f x ≤ a}),
        (∀ x, (r x : M) = flowOf X (max (f x - a) 0) x) ∧
        (∀ x, (r' x : M) = flowOf X' (max (f x - a) 0) x) ∧
        (∀ x, r (sublevelInclusion f a b hab x) = x) ∧
        (∀ x, r' (sublevelInclusion f a b hab x) = x) ∧
        r.HomotopicRel r' {x | f x ≤ a} := by
  -- Along `-grad f` the derivative of `f` is `-‖grad f‖²`, negative off the critical points.
  have hdf : ∀ x, mvfderiv 𝓘(ℝ, E) f x (-mgradient 𝓘(ℝ, E) f x) =
      -‖mgradient 𝓘(ℝ, E) f x‖ ^ 2 := fun x ↦ by
    rw [map_neg, mvfderiv_apply_mgradient, real_inner_self_eq_norm_sq]
  have hgrad : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
      (fun x ↦ (⟨x, -mgradient 𝓘(ℝ, E) f x⟩ : TangentBundle 𝓘(ℝ, E) M)) :=
    have : IsManifold 𝓘(ℝ, E) (∞ + 1) M := by simpa using (inferInstance : IsManifold _ ∞ M)
    contMDiff_neg_mgradient (n := ∞) (by simpa using hf)
  obtain ⟨X, X', hX, hX', ⟨U, hU, hKU, hXU⟩, hcomplete, r, r', hr, hr', hrr, hrr', F, -⟩ :=
    exists_homotopyRel_sublevelRetraction_of_mvfderiv_lt_zero hf hY.contMDiff hgrad hab hcompact
      (fun x hxa hxb ↦ hY.mvfderiv_apply_lt_zero x (hreg x hxa hxb)) fun x hxa hxb ↦ by
        rw [hdf, neg_lt_zero]
        exact pow_pos (norm_pos_iff.2 fun h ↦
          hreg x hxa hxb (mvfderiv_eq_zero_iff.1 (mgradient_eq_zero_iff.1 h))) 2
  refine ⟨X, X', hX, hX', by simpa using hcomplete 0, by simpa using hcomplete 1,
    ⟨U, hU, hKU, fun x hx ↦ ⟨(hXU x hx).1, by rw [(hXU x hx).2.1, hdf, neg_neg]⟩⟩, r, r', hr, hr',
    hrr, hrr', ⟨F⟩⟩

end IsAdaptedPseudoGradient

end TauCeti
