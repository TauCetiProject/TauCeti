/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.NondegenerateMetric.Family
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Geometry.Manifold.VectorBundle.NondegenerateMetric.Musical

/-!
# The first variation of a smooth family of nondegenerate metrics

Let `g` be a smooth family of nondegenerate metrics on `M` parametrized by a manifold `P`, as
bundled by `TauCeti.Manifold.ContMDiffNondegenerateMetricFamily`. At every point `y : M` the
forms `g (p, y)` all live on the single tangent space `T_y M`, so `p ↦ g (p, y)` is a smooth map
from `P` to a fixed space of bilinear forms. Its differential at `p` in the direction of a
parameter tangent vector `u ∈ T_p P` is the first variation `δ_u g` of the family, a field of
symmetric bilinear forms on `M`.

Along a parameter curve `c : ℝ → P`, the parameter derivative `∂ₜ g_{c t}` of the restricted
family is the variation of `g` at `c t` in the direction of the velocity `c'(t)`. This is the
symmetric field `h = ∂ₜ g_t` entering the first variation formula of the Levi-Civita connection.

The inverse metric varies by `∂ₜ g⁻¹ = -g⁻¹ h g⁻¹`. Here `g⁻¹` at `y` is the inverse of the flat
map `T_y M → T_y^* M`, which is the sharp musical isomorphism
(`TauCeti.Manifold.ContMDiffNondegenerateMetric.inverse_apply`). Paired with two covectors this is
the index formula `∂ₜ g^{ij} = -g^{ik} h_{kl} g^{lj}`. It only needs the metrics at the single
point `y` to be differentiable in the parameter, and holds for every signature.

## Main definitions and results

In the namespace `TauCeti.Manifold.ContMDiffNondegenerateMetricFamily`:

* `variation`: the first variation `δ_u g` of a family at a parameter `p` in the direction
  `u ∈ T_p P`.
* `variation_eq_mfderiv`: the variation at `y` is the differential of `p ↦ g (p, y)`.
* `variation_zero`, `variation_add`, `variation_smul`: the variation is linear in the parameter
  direction.
* `variation_apply_comm`: the variation is a field of symmetric bilinear forms.
* `contMDiff_variation`: in any parameter tangent direction, it is a smooth tensor field.
* `hasDerivAt_apply_apply_comp`: along a differentiable parameter curve `c`, the derivative at `t`
  of `s ↦ g (c s, y) (v, w)` is `δ_{c'(t)} g (v, w)`.
* `variation_comp` and `variation_const`: the variation of a restricted family is given by the
  chain rule, and the variation of a constant family vanishes.
* `hasDerivAt_inverse_comp`, `hasDerivAt_inverse_apply_comp` and
  `hasDerivAt_apply_inverse_apply_comp`: along a differentiable parameter curve, the inverse
  metric has derivative `-g⁻¹ h g⁻¹`, with `h = δ_{c'(t)} g`.

In the namespace `TauCeti.Manifold.ContMDiffNondegenerateMetric`, for a one-parameter family `g_s`
of nondegenerate metrics whose pairings at `y` have parameter derivative `h` at `t`:

* `hasDerivAt_inverse`: the inverse metric at `y` has derivative `-g⁻¹ h g⁻¹`.
* `hasDerivAt_inverse_apply`: its value on a covector `φ` has derivative `-g⁻¹ (h (g⁻¹ φ))`.
* `hasDerivAt_apply_inverse_apply`: the dual pairing `φ (g⁻¹ ψ)` has derivative
  `-h (g⁻¹ φ, g⁻¹ ψ)`.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.K: variations of metrics.
* P. Topping, *Lectures on the Ricci Flow*, LMS Lecture Note Series 325, Cambridge University
  Press (2006), Proposition 2.3.1: the variation of the inverse metric.
-/

public section

noncomputable section

open Filter
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]

/-! ### The inverse of a one-parameter family of metrics -/

namespace ContMDiffNondegenerateMetric

variable [FiniteDimensional ℝ E] {g : ℝ → ContMDiffNondegenerateMetric (I := I) (M := M)} {y : M}
  {h : TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ} {t : ℝ}

/-- **The variation of the inverse metric.** If the pairings of a one-parameter family `g_s` of
nondegenerate metrics at `y` have parameter derivative `h` at `t`, then the inverses
`g_s⁻¹ : T_y^* M → T_y M` of the flat maps have derivative `-g_t⁻¹ ∘ h ∘ g_t⁻¹` at `t`. -/
theorem hasDerivAt_inverse (hh : ∀ v w, HasDerivAt (fun s ↦ g s y v w) (h v w) t) :
    HasDerivAt (fun s ↦ ((g s y).inverse : (E →L[ℝ] ℝ) →L[ℝ] E))
      (-((g t y).inverse ∘L (h ∘L (g t y).inverse))) t := by
  -- The metrics at `y`, as a curve of bilinear forms on the model space.
  set G : ℝ → E →L[ℝ] E →L[ℝ] ℝ := fun s ↦ g s y
  have hG : HasDerivAt G h t := hasDerivAt_clm_apply₂.mpr hh
  exact hG.clm_inverse_of_completeSpace ((g t).isInvertible y)

/-- **The variation of the sharp of a covector.** If the pairings of a one-parameter family `g_s`
of nondegenerate metrics at `y` have parameter derivative `h` at `t`, then for every covector `φ`
the vectors `g_s⁻¹ φ` have derivative `-g_t⁻¹ (h (g_t⁻¹ φ, ·))` at `t`. -/
theorem hasDerivAt_inverse_apply (hh : ∀ v w, HasDerivAt (fun s ↦ g s y v w) (h v w) t)
    (φ : TangentSpace I y →L[ℝ] ℝ) :
    HasDerivAt (fun s ↦ ((g s y).inverse φ : E)) (-(g t y).inverse (h ((g t y).inverse φ))) t := by
  -- The covector `φ` and the inverse metrics, read on the model space.
  set G : ℝ → E →L[ℝ] E →L[ℝ] ℝ := fun s ↦ g s y
  let φ' : E →L[ℝ] ℝ := φ
  have hd : HasDerivAt (fun s ↦ (G s).inverse) (-((G t).inverse ∘L (h ∘L (G t).inverse))) t :=
    hasDerivAt_inverse hh
  have := hd.clm_apply (hasDerivAt_const t φ')
  simp only [map_zero, add_zero, neg_apply, ContinuousLinearMap.comp_apply] at this
  exact this

/-- **The variation of the inverse metric on covectors.** If the pairings of a one-parameter family
`g_s` of nondegenerate metrics at `y` have parameter derivative `h` at `t`, then for all covectors
`φ, ψ` the pairings `g_s⁻¹(φ, ψ) = φ (g_s⁻¹ ψ)` have derivative `-h (g_t⁻¹ φ, g_t⁻¹ ψ)` at `t`.
In index notation, `∂ₜ g^{ij} = -g^{ik} h_{kl} g^{lj}`. -/
theorem hasDerivAt_apply_inverse_apply (hh : ∀ v w, HasDerivAt (fun s ↦ g s y v w) (h v w) t)
    (φ ψ : TangentSpace I y →L[ℝ] ℝ) :
    HasDerivAt (fun s ↦ φ ((g s y).inverse ψ)) (-h ((g t y).inverse φ) ((g t y).inverse ψ)) t := by
  let φ' : E →L[ℝ] ℝ := φ
  refine (φ'.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_inverse_apply hh ψ)).congr_deriv ?_
  have hinv := (g t).isInvertible y
  -- `φ (g⁻¹ ξ) = ξ (g⁻¹ φ)` by symmetry of `g_t`.
  have hdual (ξ : TangentSpace I y →L[ℝ] ℝ) : φ ((g t y).inverse ξ) = ξ ((g t y).inverse φ) := by
    conv_lhs => rw [← hinv.self_apply_inverse φ]
    rw [(g t).apply_comm, hinv.self_apply_inverse]
  -- `h` is symmetric, as a derivative of symmetric forms.
  have hsymm (v w : TangentSpace I y) : h v w = h w v :=
    (hh v w).unique ((hh w v).congr_of_eventuallyEq
      (Eventually.of_forall fun s ↦ (g s).apply_comm y v w))
  have e : φ (-(g t y).inverse (h ((g t y).inverse ψ))) =
      -h ((g t y).inverse φ) ((g t y).inverse ψ) := by
    rw [map_neg, hdual, hsymm]
  -- The derivative is computed on the model space, where `φ'` is `φ`.
  exact e

end ContMDiffNondegenerateMetric

namespace ContMDiffNondegenerateMetricFamily

variable (g : ContMDiffNondegenerateMetricFamily I M IP P)

/-- The family at a fixed point `y`, as a function of the parameter. Its values are typed as
bilinear forms on the model space `E`, so that its derivatives are continuous linear maps into
that normed space. -/
private def atPoint (y : M) : P → E →L[ℝ] E →L[ℝ] ℝ := fun p ↦ g (p, y)

/-- At a fixed point, a smooth nondegenerate metric family is smooth in the parameter. The fibre
coordinate of the trivialization at `y` is smooth, and its inverse at `y` is a fixed continuous
linear map. -/
private theorem contMDiff_atPoint (y : M) :
    ContMDiff IP 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ (g.atPoint y) := by
  intro p
  set e := trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
    (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) y
  have hy : y ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt _ _ y
  have h : ContMDiffAt IP 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ (fun p' ↦ (e ⟨y, g (p', y)⟩).2) p :=
    (Bundle.contMDiffAt_totalSpace_iff.mp
      ((g.contMDiff (p, y)).comp p (contMDiffAt_id.prodMk contMDiffAt_const))).2
  let L : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
    Bundle.Trivialization.symmL ℝ (F := E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) e y
  have hL : ContMDiffAt IP 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ (L ∘ fun p' ↦ (e ⟨y, g (p', y)⟩).2) p :=
    ((ContinuousLinearMap.contMDiff (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] ℝ)
      (F := E →L[ℝ] E →L[ℝ] ℝ) L).contMDiffAt).comp p h
  have heq : (L ∘ fun p' ↦ (e ⟨y, g (p', y)⟩).2) = g.atPoint y := by
    funext p'
    have h := Bundle.Trivialization.symmL_continuousLinearMapAt (R := ℝ) (B := M)
      (F := E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) e hy (g (p', y))
    rwa [Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ (B := M)
      (F := E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) e hy] at h
  rwa [heq] at hL

/-- The derivative of `atPoint`, typed with values in the bilinear forms on the model space. -/
private def atPointDeriv (y : M) (p : P) : TangentSpace IP p →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  mfderiv IP 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) (g.atPoint y) p

/-- The first variation `δ_u g` of a smooth nondegenerate metric family at the parameter `p` in
the direction `u ∈ T_p P`. Its value at `y : M` is the differential at `p` of the smooth map
`p' ↦ g (p', y)` into the bilinear forms on `T_y M`, applied to `u`. -/
def variation (p : P) (u : TangentSpace IP p) (y : M) :
    TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ :=
  g.atPointDeriv y p u

/-- The first variation at `y` is the differential at `p` of the smooth map `p' ↦ g_{p'} y`,
with values typed as bilinear forms on the model space, applied to `u`. -/
theorem variation_eq_mfderiv (p : P) (u : TangentSpace IP p) (y : M) :
    g.variation p u y = mfderiv (M' := E →L[ℝ] E →L[ℝ] ℝ) IP 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)
      (fun p' ↦ g.metric p' y) p u := by
  have h : (fun p' ↦ g.metric p' y : P → E →L[ℝ] E →L[ℝ] ℝ) = g.atPoint y :=
    funext fun p' ↦ g.metric_apply p' y
  rw [h]
  rfl

/-- The first variation in the zero direction vanishes. -/
@[simp]
theorem variation_zero (p : P) : g.variation p 0 = 0 := by
  funext y
  exact map_zero (g.atPointDeriv y p)

/-- The first variation is additive in the parameter direction. -/
@[simp]
theorem variation_add (p : P) (u₁ u₂ : TangentSpace IP p) :
    g.variation p (u₁ + u₂) = g.variation p u₁ + g.variation p u₂ := by
  funext y
  exact map_add (g.atPointDeriv y p) u₁ u₂

/-- The first variation is homogeneous in the parameter direction. -/
@[simp]
theorem variation_smul (p : P) (a : ℝ) (u : TangentSpace IP p) :
    g.variation p (a • u) = a • g.variation p u := by
  funext y
  exact map_smul (g.atPointDeriv y p) a u

/-- The differential of the family at a fixed point. -/
private theorem hasMFDerivAt_atPoint (p : P) (y : M) :
    HasMFDerivAt IP 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) (g.atPoint y) p (g.atPointDeriv y p) :=
  ((g.contMDiff_atPoint y p).mdifferentiableAt (by simp)).hasMFDerivAt

/-- Fibre coordinates commute with differentiation in the parameter, since their linear map
is fixed while the parameter varies. -/
private theorem variation_inCoordinates (p : P) (u : TangentSpace IP p) (x y : M)
    (hy : y ∈ (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
      (fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ) x).baseSet) :
    (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
        (fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ) x
      ⟨y, g.variation p u y⟩).2 =
      mfderiv IP 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)
        (fun p' ↦ (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
          (fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ) x
          ⟨y, g (p', y)⟩).2) p u := by
  let e := trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
    (fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ) x
  let L : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
    Bundle.Trivialization.continuousLinearMapAt ℝ
      (F := E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ) e y
  have hfun : L ∘ g.atPoint y = fun p' ↦ (e ⟨y, g (p', y)⟩).2 := by
    funext p'
    exact Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ (B := M)
      (F := E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ) e hy (g (p', y))
  have hL := ((ContinuousLinearMap.hasMFDerivAt (𝕜 := ℝ)
    (E := E →L[ℝ] E →L[ℝ] ℝ) (E' := E →L[ℝ] E →L[ℝ] ℝ)
    (f := L) (x := g.atPoint y p))).comp p (g.hasMFDerivAt_atPoint p y)
  rw [hfun] at hL
  have hd := congrArg (fun A ↦ A u) hL.mfderiv
  rw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ (B := M)
      (F := E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ) e hy]
  exact hd.symm

/-- The first variation in an arbitrary parameter tangent direction is a smooth section of
the tangent bilinear-form bundle. -/
theorem contMDiff_variation [IsManifold IP 1 P] (p : P) (u : TangentSpace IP p) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun y : M ↦ Bundle.TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ)
        y (g.variation p u y)) := by
  intro x
  rw [Bundle.contMDiffAt_section_iff]
  let e := trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
    (fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] ℝ) x
  let f : M → P → E →L[ℝ] E →L[ℝ] ℝ := fun y p' ↦ (e ⟨y, g (p', y)⟩).2
  have hf : ContMDiffAt (I.prod IP) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (Function.uncurry f) (x, p) :=
    (Bundle.contMDiffAt_totalSpace_iff.mp
      ((g.contMDiff (p, x)).comp (x, p) (contMDiffAt_snd.prodMk contMDiffAt_fst))).2
  have hderiv := hf.mfderiv f (fun _ ↦ p) (m := ∞) contMDiffAt_const (by simp)
  -- The source parameter is fixed, and the target is a normed space, so both tangent
  -- coordinate changes in the parameter derivative reduce to identity maps.
  have hcoord :
      inTangentCoordinates IP 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) (fun _ : M ↦ p)
        (fun y ↦ f y p) (fun y ↦ mfderiv IP 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) (f y) p) x =
      fun y ↦ mfderiv IP 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) (f y) p := by
    funext y
    rw [inTangentCoordinates_eq _ _ _ (mem_chart_source HP p) (by simp),
      tangentBundleCore_coordChange_model_space]
    have hs : (tangentBundleCore IP P).coordChange (achart HP p) (achart HP p) p =
        ContinuousLinearMap.id ℝ EP := by
      ext v
      exact (tangentBundleCore IP P).coordChange_self _ _ (mem_achart_source HP p) v
    rw [hs]
    ext v
    rfl
  rw [hcoord] at hderiv
  -- Evaluate on the fixed tangent vector, regarded in the parameter model space.
  let u' : EP := u
  have hfield := hderiv.clm_apply (contMDiffAt_const (c := u'))
  apply hfield.congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt _ _ x)]
    with y hy
  exact g.variation_inCoordinates p u x y hy

/-- The first variation of a smooth nondegenerate metric family is a field of symmetric bilinear
forms. -/
theorem variation_apply_comm (p : P) (u : TangentSpace IP p) (y : M) (v w : TangentSpace I y) :
    g.variation p u y v w = g.variation p u y w v := by
  let Φ : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  have hf := g.hasMFDerivAt_atPoint p y
  have hΦ := ((ContinuousLinearMap.hasMFDerivAt (𝕜 := ℝ) (E := E →L[ℝ] E →L[ℝ] ℝ)
      (E' := E →L[ℝ] E →L[ℝ] ℝ) (f := Φ) (x := g.atPoint y p))).comp p hf
  have hfun : Φ ∘ g.atPoint y = g.atPoint y := by
    funext p'
    ext a b
    exact g.apply_comm (p', y) b a
  rw [hfun] at hΦ
  have h : g.atPointDeriv y p u = Φ (g.atPointDeriv y p u) :=
    congr($(hf.mfderiv.symm.trans hΦ.mfderiv) u)
  exact congr($h v w)

/-- **The variation along a parameter curve.** For a parameter curve `c` differentiable at `t`,
the derivative at `t` of `s ↦ g (c s, y) (v, w)` is the first variation of `g` at `c t` in the
direction of the velocity `c'(t)`, evaluated at `(v, w)`. -/
theorem hasDerivAt_apply_apply_comp {c : ℝ → P} {t : ℝ} (hc : MDifferentiableAt 𝓘(ℝ) IP c t)
    (y : M) (v w : TangentSpace I y) :
    HasDerivAt (fun s ↦ g (c s, y) v w) (g.variation (c t) (mfderiv 𝓘(ℝ) IP c t 1) y v w) t := by
  have h1 : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) (g.atPoint y ∘ c) t
      ((g.atPointDeriv y (c t)).comp (mfderiv 𝓘(ℝ) IP c t)) :=
    (g.hasMFDerivAt_atPoint (c t) y).comp t hc.hasMFDerivAt
  have h2 : HasFDerivAt (g.atPoint y ∘ c)
      ((g.atPointDeriv y (c t)).comp (mfderiv 𝓘(ℝ) IP c t)) t := h1.hasFDerivAt
  have h3 : HasDerivAt (g.atPoint y ∘ c) (g.atPointDeriv y (c t) (mfderiv 𝓘(ℝ) IP c t 1)) t :=
    h2.hasDerivAt
  -- Evaluate at `v` and `w`, read as vectors of the model space.
  let v' : E := v
  let w' : E := w
  have h4 := (h3.clm_apply (hasDerivAt_const t v')).clm_apply (hasDerivAt_const t w')
  simp only [map_zero, add_zero] at h4
  exact h4

section Comp

variable {EP' : Type*} [NormedAddCommGroup EP'] [NormedSpace ℝ EP']
  {HP' : Type*} [TopologicalSpace HP'] {IP' : ModelWithCorners ℝ EP' HP'}
  {P' : Type*} [TopologicalSpace P'] [ChartedSpace HP' P']

/-- **Chain rule.** The first variation of a family restricted along a smooth parameter map `c`
is the variation of the original family in the direction of the image of `u` under `dc`. -/
@[simp]
theorem variation_comp (c : C^∞⟮IP', P'; IP, P⟯) (p' : P') (u : TangentSpace IP' p') :
    (g.comp c).variation p' u = g.variation (c p') (mfderiv IP' IP c p' u) := by
  funext y
  have hfun : (g.comp c).atPoint y = g.atPoint y ∘ c := by
    funext q
    exact congr($(g.comp_apply c (q, y)))
  have h := (g.hasMFDerivAt_atPoint (c p') y).comp p'
    ((c.contMDiff p').mdifferentiableAt (by simp)).hasMFDerivAt
  rw [← hfun] at h
  exact congr($(h.mfderiv) u)

end Comp

/-- The first variation of a constant family vanishes. -/
@[simp]
theorem variation_const (g₀ : ContMDiffNondegenerateMetric (I := I) (M := M)) (p : P)
    (u : TangentSpace IP p) : (const (IP := IP) g₀).variation p u = 0 := by
  funext y
  let a : E →L[ℝ] E →L[ℝ] ℝ := g₀ y
  have hfun : (const (IP := IP) (P := P) g₀).atPoint y = fun _ ↦ a := by
    funext q
    exact congr($(const_apply g₀ (q, y)))
  have h := hasMFDerivAt_const (I := IP) (I' := 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) a p
  rw [← hfun] at h
  exact congr($(h.mfderiv) u)

section Inverse

variable [FiniteDimensional ℝ E] {c : ℝ → P} {t : ℝ}

/-- **The variation of the inverse metric along a parameter curve.** Along a parameter curve `c`
differentiable at `t`, the inverses `g_{c s}⁻¹ : T_y^* M → T_y M` of the flat maps have derivative
`-g⁻¹ ∘ h ∘ g⁻¹` at `t`, where `g = g_{c t}` and `h = δ_{c'(t)} g` is the first variation of the
family in the direction of the velocity of `c`. -/
theorem hasDerivAt_inverse_comp (hc : MDifferentiableAt 𝓘(ℝ) IP c t) (y : M) :
    HasDerivAt (fun s ↦ ((g (c s, y)).inverse : (E →L[ℝ] ℝ) →L[ℝ] E))
      (-((g (c t, y)).inverse ∘L
        (g.variation (c t) (mfderiv 𝓘(ℝ) IP c t 1) y ∘L (g (c t, y)).inverse))) t := by
  simpa only [metric_apply] using ContMDiffNondegenerateMetric.hasDerivAt_inverse
    (g := fun s ↦ g.metric (c s)) (fun v w ↦ by
      simpa only [metric_apply] using g.hasDerivAt_apply_apply_comp hc y v w)

/-- **The variation of the sharp of a covector along a parameter curve.** Along a parameter curve
`c` differentiable at `t`, the vectors `g_{c s}⁻¹ φ` have derivative `-g⁻¹ (h (g⁻¹ φ, ·))` at `t`,
where `g = g_{c t}` and `h = δ_{c'(t)} g`. -/
theorem hasDerivAt_inverse_apply_comp (hc : MDifferentiableAt 𝓘(ℝ) IP c t) (y : M)
    (φ : TangentSpace I y →L[ℝ] ℝ) :
    HasDerivAt (fun s ↦ ((g (c s, y)).inverse φ : E))
      (-(g (c t, y)).inverse
        (g.variation (c t) (mfderiv 𝓘(ℝ) IP c t 1) y ((g (c t, y)).inverse φ))) t := by
  have h := ContMDiffNondegenerateMetric.hasDerivAt_inverse_apply
    (g := fun s ↦ g.metric (c s)) (fun v w ↦ by
      simpa only [metric_apply] using g.hasDerivAt_apply_apply_comp hc y v w) φ
  simp only [metric_apply] at h
  -- Elaborated with the goal's model-space codomain `E`.
  exact h

/-- **The variation of the inverse metric on covectors along a parameter curve.** Along a
parameter curve `c` differentiable at `t`, the pairings `φ (g_{c s}⁻¹ ψ)` have derivative
`-h (g⁻¹ φ, g⁻¹ ψ)` at `t`, where `g = g_{c t}` and `h = δ_{c'(t)} g`. -/
theorem hasDerivAt_apply_inverse_apply_comp (hc : MDifferentiableAt 𝓘(ℝ) IP c t) (y : M)
    (φ ψ : TangentSpace I y →L[ℝ] ℝ) :
    HasDerivAt (fun s ↦ φ ((g (c s, y)).inverse ψ))
      (-g.variation (c t) (mfderiv 𝓘(ℝ) IP c t 1) y ((g (c t, y)).inverse φ)
        ((g (c t, y)).inverse ψ)) t := by
  simpa only [metric_apply] using ContMDiffNondegenerateMetric.hasDerivAt_apply_inverse_apply
    (g := fun s ↦ g.metric (c s)) (fun v w ↦ by
      simpa only [metric_apply] using g.hasDerivAt_apply_apply_comp hc y v w) φ ψ

end Inverse

end ContMDiffNondegenerateMetricFamily

end TauCeti.Manifold
