/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorField.Chart.Derivative
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
import TauCeti.Geometry.Manifold.ExtChartAt
import TauCeti.Geometry.Manifold.VectorField.Regularity
import TauCeti.Topology.VectorBundle.ZeroSection

/-!
# The index of a zero of a vector field

Let `V` be a vector field on a manifold `M` modelled on `E`, regarded as the section
`x ↦ (x, V x)` of the tangent bundle. Its **vertical derivative** at `p` is the derivative of this
section at `p`, read in the tangent-bundle chart at `(p, V p)`, followed by the projection
`E × E → E` to the fibre. Its determinant is `TauCeti.zeroDet I V p`, and over `ℝ` the
**index** `TauCeti.zeroSign I V p` is `1` when this determinant is positive and `-1` otherwise.
At a nondegenerate zero, where `zeroDet I V p ≠ 0`, the index is the sign of `det (dV_p)`, the
local index of the zero in the Poincaré–Hopf theorem.

On a boundaryless manifold, the tangent-bundle chart at `(p, V p)` reads the fibre of a point `q`
near `p` through the derivative at `q` of the chart at `p`. So the fibre coordinate of the section
is the coordinate field of `V` in the chart at `p`, and the vertical derivative is the chart
derivative `TauCeti.vectorFieldChartDerivative I V p`, the derivative of that coordinate field
(`TauCeti.snd_comp_mfderiv_eq_fderiv_mpullback`,
`TauCeti.zeroDet_eq_det_vectorFieldChartDerivative`).
This holds whether or not `V` is differentiable at `p`: if it is not, both derivatives are zero.
At a zero of a differentiable field another chart conjugates the chart derivative, so the
determinant can be computed in any chart
(`TauCeti.zeroDet_eq_det_fderiv_mpullback_extChartAt_symm`). On a model space, with its trivial
chart, `zeroDet` is the determinant of the Fréchet derivative of the field
(`TauCeti.zeroDet_modelSpace`). For instance, on `ℝ` the fields `x ↦ x` and `x ↦ -x` have
indices `1` and `-1` at their zero.

On a boundaryless manifold modelled on a finite-dimensional space over a complete field, a
nondegenerate zero of a field differentiable there is isolated
(`TauCeti.eventually_ne_zero_of_zeroDet_ne_zero`): in the chart at `p`, the coordinate field has
an injective derivative at its zero. Consequently a compact set of nondegenerate zeros is finite
(`IsCompact.finite_of_zeroDet_ne_zero`), and a differentiable vector field on a compact boundaryless
real manifold whose zeros are all nondegenerate has only finitely many zeros
(`TauCeti.finite_setOf_eq_zero_of_zeroDet_ne_zero`), so its indices have a finite sum.
Neither orientability nor connectedness enters: changing the chart changes the orientation of
the source and of the target of `dV_p` at once.

## Main definitions

* `TauCeti.zeroDet I V p`: the determinant of the vertical derivative of `V` at `p`.
* `TauCeti.zeroSign I V p`: `1` when `zeroDet I V p` is positive, `-1` otherwise.

## Main results

* `TauCeti.snd_comp_mfderiv_eq_fderiv_mpullback`: on a boundaryless manifold, the fibre component
  of the derivative of the section `x ↦ (x, V x)` is the derivative of the coordinate field of `V`
  in the chart at `p`.
* `TauCeti.zeroDet_eq_det_vectorFieldChartDerivative`: so `zeroDet` is the determinant of the
  chart derivative.
* `TauCeti.zeroDet_eq_det_fderiv_mpullback_extChartAt_symm`: at a zero, `zeroDet` can be computed
  in any chart.
* `TauCeti.zeroSign_eq_sign`: at a nondegenerate zero, the index is the sign of `zeroDet`.
* `TauCeti.eventually_ne_zero_of_zeroDet_ne_zero`: nondegenerate zeros are isolated.
* `IsCompact.finite_of_zeroDet_ne_zero`, `TauCeti.finite_setOf_eq_zero_of_zeroDet_ne_zero`:
  finiteness of nondegenerate zeros on compact sets and compact manifolds.

## References

* J. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §6 (the index of a nondegenerate zero of a vector field is the sign of the determinant of its
  derivative; isolation of nondegenerate zeros).
* V. Guillemin, A. Pollack, *Differential Topology*, Prentice-Hall, 1974, Chapter 3, §5 (the
  index of a nondegenerate zero and the Poincaré–Hopf theorem).
-/

public section

open Bundle Filter Function Set VectorField
open scoped Manifold Topology

namespace TauCeti

section General

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]

variable (I) in
/-- The determinant of the **vertical derivative** of a vector field `V` at `p`: the derivative at
`p` of the section `x ↦ (x, V x)` of the tangent bundle, read in the tangent-bundle chart at
`(p, V p)` and projected to the fibre. On a boundaryless manifold it is the determinant of the
chart derivative of `V` (`TauCeti.zeroDet_eq_det_vectorFieldChartDerivative`); at a zero of a
differentiable field it does not depend on the chart. -/
noncomputable def zeroDet (V : (x : M) → TangentSpace I x) (p : M) : 𝕜 :=
  LinearMap.det ((ContinuousLinearMap.snd 𝕜 E E).comp
    (mfderiv I I.tangent (fun x ↦ (V x : TangentBundle I M)) p)).toLinearMap

/-- `zeroDet I V p` is the determinant of the fibre component of the derivative of the section
`x ↦ (x, V x)` at `p`. -/
theorem zeroDet_def (V : (x : M) → TangentSpace I x) (p : M) :
    zeroDet I V p = LinearMap.det ((ContinuousLinearMap.snd 𝕜 E E).comp
      (mfderiv I I.tangent (fun x ↦ (V x : TangentBundle I M)) p)).toLinearMap :=
  (rfl)

section Boundaryless

variable [I.Boundaryless] {V : (x : M) → TangentSpace I x} {p : M}

/-- Near the chart image of `p`, the fibre coordinate of the section `x ↦ (x, V x)`, written in
the chart at `p` and the tangent-bundle chart at `(p, V p)`, is the coordinate field of `V` in the
chart at `p`. -/
private theorem snd_writtenInExtChartAt_eventuallyEq_mpullback (V : (x : M) → TangentSpace I x)
    (p : M) :
    (fun z ↦ (writtenInExtChartAt I I.tangent p (fun x ↦ (V x : TangentBundle I M)) z).2)
      =ᶠ[𝓝 (extChartAt I p p)] mpullback 𝓘(𝕜, E) I (extChartAt I p).symm V := by
  have h := VectorField.trivializationAt_snd_eventuallyEq_mpullbackWithin_extChartAt_symm V p
  rw [I.range_eq_univ, nhdsWithin_univ, mpullbackWithin_univ] at h
  refine EventuallyEq.trans (Eventually.of_forall fun z ↦ ?_) h
  simp only [writtenInExtChartAt, extChartAt_coe, comp_apply, modelWithCorners_prod_coe,
    Prod.map_snd, modelWithCornersSelf_coe, id_eq]
  -- The tangent-bundle chart at `(p, V p)` is the trivialization at `p` followed by the chart at
  -- `p` on the base, so its fibre coordinate is that of the trivialization.
  rfl

/-- **The vertical derivative is the chart derivative.** On a boundaryless manifold, the fibre
component of the derivative at `p` of the section `x ↦ (x, V x)` of the tangent bundle, read in
the tangent-bundle chart at `(p, V p)`, is the derivative at the chart image of `p` of the
coordinate field of `V` in the chart at `p`. Both sides are zero when `V` is not differentiable at
`p`. -/
theorem snd_comp_mfderiv_eq_fderiv_mpullback (V : (x : M) → TangentSpace I x) (p : M) :
    (ContinuousLinearMap.snd 𝕜 E E).comp
        (mfderiv I I.tangent (fun x ↦ (V x : TangentBundle I M)) p) =
      fderiv 𝕜 (mpullback 𝓘(𝕜, E) I (extChartAt I p).symm V) (extChartAt I p p) := by
  by_cases hV : MDifferentiableAt I I.tangent (fun x ↦ (V x : TangentBundle I M)) p
  · have hd := hV.differentiableWithinAt_writtenInExtChartAt
    rw [I.range_eq_univ, differentiableWithinAt_univ] at hd
    rw [hV.mfderiv, I.range_eq_univ, fderivWithin_univ,
      ← (snd_writtenInExtChartAt_eventuallyEq_mpullback V p).fderiv_eq]
    exact hd.hasFDerivAt.snd.fderiv.symm
  · have hU : ¬DifferentiableAt 𝕜 (mpullback 𝓘(𝕜, E) I (extChartAt I p).symm V)
        (extChartAt I p p) := fun hU ↦
      hV (mdifferentiableAt_section_iff_differentiableAt_mpullbackWithin_extChartAt_symm.2
        (by rwa [I.range_eq_univ, mpullbackWithin_univ]))
    rw [mfderiv_zero_of_not_mdifferentiableAt hV, fderiv_zero_of_not_differentiableAt hU]
    -- Both sides are zero: the tangent space of the tangent bundle is `E × E` by definition.
    ext v
    rfl

/-- On a boundaryless manifold, `zeroDet I V p` is the determinant of the chart derivative of `V`
at `p`. -/
theorem zeroDet_eq_det_vectorFieldChartDerivative (V : (x : M) → TangentSpace I x) (p : M) :
    zeroDet I V p = LinearMap.det (vectorFieldChartDerivative I V p) := by
  rw [zeroDet_def, snd_comp_mfderiv_eq_fderiv_mpullback, vectorFieldChartDerivative_def]
  -- The two sides differ only in reading the tangent space at `p` as the model space `E`.
  rfl

/-- **`zeroDet` is intrinsic at a zero.** At a zero `p` of a vector field differentiable at `p`,
on a boundaryless manifold, `zeroDet I V p` is the determinant of the derivative of the coordinate
field of `V` in any extended chart whose source contains `p`. -/
theorem zeroDet_eq_det_fderiv_mpullback_extChartAt_symm {x' : M}
    (hV : MDifferentiableAt I I.tangent (fun x ↦ (V x : TangentBundle I M)) p) (hV₀ : V p = 0)
    (hp : p ∈ (extChartAt I x').source) :
    zeroDet I V p = LinearMap.det
      (fderiv 𝕜 (mpullback 𝓘(𝕜, E) I (extChartAt I x').symm V) (extChartAt I x' p) :
        E →ₗ[𝕜] E) := by
  rw [zeroDet_eq_det_vectorFieldChartDerivative,
    det_fderiv_mpullback_extChartAt_symm_of_eq_zero hV hV₀ hp]

end Boundaryless

/-- On a model space, with its trivial chart, `zeroDet` is the determinant of the Fréchet
derivative of the vector field. -/
@[simp]
theorem zeroDet_modelSpace (V : (x : E) → TangentSpace 𝓘(𝕜, E) x) (x : E) :
    zeroDet 𝓘(𝕜, E) V x = LinearMap.det (fderiv 𝕜 V x : E →ₗ[𝕜] E) := by
  rw [zeroDet_eq_det_vectorFieldChartDerivative, vectorFieldChartDerivative_modelSpace]

/-! ### Nondegenerate zeros are isolated -/

section Isolated

variable [I.Boundaryless] [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
  {V : (x : M) → TangentSpace I x} {p : M}

/-- **Nondegenerate zeros are isolated.** On a boundaryless manifold modelled on a
finite-dimensional space over a complete field, if `V` is differentiable at `p` with
`zeroDet I V p ≠ 0`, then `V` has no zero close to `p` other than possibly `p` itself. -/
theorem eventually_ne_zero_of_zeroDet_ne_zero
    (hV : MDifferentiableAt I I.tangent (fun x ↦ (V x : TangentBundle I M)) p)
    (hdet : zeroDet I V p ≠ 0) : ∀ᶠ q in 𝓝[≠] p, V q ≠ 0 := by
  set φ := extChartAt I p
  set U := mpullback 𝓘(𝕜, E) I φ.symm V
  have hr (q : M) : range I ∈ 𝓝 (φ q) := by rw [I.range_eq_univ]; exact univ_mem
  -- At a point `q` of the chart, the coordinate field is the image of `V q` under `dφ_q`.
  have hUq {q : M} (hq : q ∈ φ.source) : U (φ q) = mfderiv I 𝓘(𝕜, E) φ q (V q) :=
    mpullback_extChartAt_symm_apply_eq_mfderiv V hq (hr q)
  -- The derivative `D` of the coordinate field at `φ p` has nonzero determinant, so it is
  -- injective and bounded below; hence `U z ≠ 0` for `z ≠ φ p` close to `φ p`.
  have hU : DifferentiableAt 𝕜 U (φ p) := by
    have h := hV.differentiableAt_mpullbackWithin_extChartAt_symm
    rwa [I.range_eq_univ, mpullbackWithin_univ] at h
  set D := fderiv 𝕜 U (φ p)
  have hinj : Injective (D : E →ₗ[𝕜] E) := by
    rw [zeroDet_eq_det_vectorFieldChartDerivative, vectorFieldChartDerivative_def] at hdet
    exact LinearMap.ker_eq_bot.mp <| (LinearMap.isUnit_iff_ker_eq_bot _).mp <|
      (LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  obtain ⟨K, -, hK⟩ := (D : E →ₗ[𝕜] E).injective_iff_antilipschitz.1 hinj
  have hne : ∀ᶠ z in 𝓝[≠] φ p, U z ≠ (0 : E) := hU.hasFDerivAt.eventually_ne ⟨K, hK⟩
  -- The chart sends points `q ≠ p` near `p` to points `≠ φ p` near `φ p`.
  have hsource : φ.source ∈ 𝓝[≠] p := mem_nhdsWithin_of_mem_nhds (extChartAt_source_mem_nhds p)
  filter_upwards [(I.tendsto_extChartAt_nhdsNE p).eventually hne, hsource] with q hq hqs hVq
  -- The zero of `TangentSpace I q` and that of `E` agree by definition.
  exact hq (by rw [hUq hqs, hVq, map_zero]; rfl)

/-- **Finiteness of compact sets of nondegenerate zeros.** On a boundaryless manifold modelled on
a finite-dimensional space over a complete field, a compact set of zeros of `V`, at each of which
`V` is differentiable with `zeroDet I V p ≠ 0`, is finite. -/
theorem _root_.IsCompact.finite_of_zeroDet_ne_zero {s : Set M} (hs : IsCompact s)
    (hV : ∀ p ∈ s, MDifferentiableAt I I.tangent (fun x ↦ (V x : TangentBundle I M)) p)
    (hV₀ : ∀ p ∈ s, V p = 0) (hdet : ∀ p ∈ s, zeroDet I V p ≠ 0) : s.Finite :=
  hs.finite <| isDiscrete_iff_nhdsNE.2 fun p hp ↦ inf_principal_eq_bot.2 <|
    (eventually_ne_zero_of_zeroDet_ne_zero (hV p hp) (hdet p hp)).mono
      fun _ hq hqs ↦ hq (hV₀ _ hqs)

end Isolated

end General

/-! ### The index of a zero -/

section Real

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {V : (x : M) → TangentSpace I x} {p : M}

variable (I) in
/-- The **index** of a vector field `V` at `p`: `1` when `zeroDet I V p` is positive and `-1`
otherwise. At a nondegenerate zero it is the sign of the determinant of the derivative of `V`
(`TauCeti.zeroSign_eq_sign`), the local index of the zero in the Poincaré–Hopf theorem. -/
noncomputable def zeroSign (V : (x : M) → TangentSpace I x) (p : M) : ℤ :=
  if 0 < zeroDet I V p then 1 else -1

theorem zeroSign_eq_one_iff : zeroSign I V p = 1 ↔ 0 < zeroDet I V p := by
  unfold zeroSign
  split_ifs with h <;> simp [h]

theorem zeroSign_eq_neg_one_iff : zeroSign I V p = -1 ↔ zeroDet I V p ≤ 0 := by
  unfold zeroSign
  split_ifs with h
  · simp [h.not_ge]
  · simp [not_lt.mp h]

/-- At a nondegenerate zero, the index is the sign of `zeroDet`. -/
theorem zeroSign_eq_sign (h : zeroDet I V p ≠ 0) :
    zeroSign I V p = SignType.sign (zeroDet I V p) := by
  unfold zeroSign
  split_ifs with hpos
  · simp [hpos]
  · simp [sign_neg (lt_of_le_of_ne (not_lt.mp hpos) h)]

/-- **Finiteness of nondegenerate zeros.** A differentiable vector field on a compact boundaryless
real manifold, modelled on a finite-dimensional space, whose zeros `p` all have
`zeroDet I V p ≠ 0` has only finitely many zeros. -/
theorem finite_setOf_eq_zero_of_zeroDet_ne_zero [I.Boundaryless] [FiniteDimensional ℝ E]
    [CompactSpace M] (hV : MDifferentiable I I.tangent (fun x ↦ (V x : TangentBundle I M)))
    (hdet : ∀ p, V p = 0 → zeroDet I V p ≠ 0) : {p | V p = 0}.Finite := by
  -- The zeros are the complement of the preimage of the open set of nonzero tangent vectors.
  have hclosed : IsClosed {p | V p = 0} := by
    have h := (isOpen_zeroSectionCompl E (TangentSpace I : M → Type _)).preimage hV.continuous
    convert h.isClosed_compl using 1
    ext p
    simp
  exact hclosed.isCompact.finite_of_zeroDet_ne_zero (fun p _ ↦ hV p) (fun _ hp ↦ hp)
    fun p hp ↦ hdet p hp

end Real

/-! ### Examples: the fields `x ↦ x` and `x ↦ -x` on `ℝ` have indices `1` and `-1` at `0` -/

example : zeroSign 𝓘(ℝ, ℝ) (fun x ↦ (x : TangentSpace 𝓘(ℝ, ℝ) x)) 0 = 1 := by
  have h : zeroDet 𝓘(ℝ, ℝ) (fun x ↦ (x : TangentSpace 𝓘(ℝ, ℝ) x)) 0 = 1 :=
    (zeroDet_modelSpace _ 0).trans (by simp)
  exact zeroSign_eq_one_iff.mpr (by rw [h]; exact one_pos)

example : zeroSign 𝓘(ℝ, ℝ) (fun x ↦ (-x : TangentSpace 𝓘(ℝ, ℝ) x)) 0 = -1 := by
  have h : zeroDet 𝓘(ℝ, ℝ) (fun x ↦ (-x : TangentSpace 𝓘(ℝ, ℝ) x)) 0 = -1 :=
    (zeroDet_modelSpace _ 0).trans (by simp)
  exact zeroSign_eq_neg_one_iff.mpr (by rw [h]; norm_num)

end TauCeti
