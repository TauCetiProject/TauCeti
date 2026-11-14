/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Contactomorphism
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Analysis.Calculus.DifferentialForm.Poincare
import TauCeti.Geometry.Contact.Slice
import TauCeti.Geometry.Contact.Symplectization.Linear
import TauCeti.Geometry.Manifold.DifferentialForm.Opens
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.LocalDiffeomorph
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Prod
import TauCeti.Geometry.Manifold.TwoForm.Kernel
import TauCeti.Geometry.Symplectic.Manifold.Darboux

/-!
# The strict contact Darboux theorem

Let `M` be a smooth manifold with finite-dimensional real model space `E`, and let `α` be a
one-form, smooth on an open set `U`, which is a contact form at an interior point `x₀ ∈ U`
(`TauCeti.IsContactFormAt`). Whereas the conformal contact Darboux theorem in
`TauCeti/Geometry/Contact/Darboux/Manifold.lean`
(`TauCeti.IsContactFormAt.exists_darbouxChart_of_isInteriorPoint`) produces coordinates pulling the
standard contact form `α_std = dz - Σᵢ pᵢ dqᵢ` (`TauCeti.innerProductContactForm`) back to a
positive multiple `g α`, **the strict contact Darboux theorem**
(`TauCeti.IsContactFormAt.exists_strictDarbouxChart_of_isInteriorPoint`) eliminates the conformal
factor `g`: there are `n` with `dim E = 2 n + 1` and a smooth partial diffeomorphism `chart` from
`M` to `ℝⁿ × ℝⁿ × ℝ` with `x₀ ∈ chart.source ⊆ U` and `chart x₀ = 0` such that for every
`x ∈ chart.source` and `v : T_x M`,

`α_std (chart x) (d chart_x v) = α x v`.

For a globally smooth one-form `α`, this pointwise pullback identity on `chart.source` is
equivalent to `chart.toDiffeomorphSourceTarget` being a strict contactomorphism
(`Diffeomorph.IsStrictContactomorphism`) between the restrictions of `α` and `α_std` to the open
source and target (`PartialDiffeomorph.isStrictContactomorphism_toDiffeomorphSourceTarget_iff`,
`PartialDiffeomorph.isStrictContactomorphism_toDiffeomorphSourceTarget_modelSpace_iff`). Moreover,
without assuming finite-dimensionality or global contactness, any partial diffeomorphism into
`V × V × ℝ` pulling `dz - ⟪p, dq⟫` back to `α` on its source straightens the Reeb vector field of
`α` to the coordinate field `∂_z = (0, 0, 1)` on that source
(`TauCeti.SmoothForm.mvfderiv_reebVectorField_of_forall_innerProductContactForm_eq`).

The proof follows the geometric Reeb-slice construction rather than the contact Moser deformation
of `TauCeti/Geometry/Contact/Darboux/Basic.lean`:

1. Read `α` in the preferred extended chart at `x₀`, where openness of the pointwise contact
   condition (`TauCeti.IsContactFormAt.eventually`) gives an open neighbourhood `W₀` on which the
   coordinate one-form `α₀` is a smooth contact form.
2. Choose the affine slice through `y₀` along the contact hyperplane `K = ker α₀(y₀)`, which has
   codimension one and is transverse to the Reeb vector field `R_{α₀}(y₀)`. The local Reeb flow map
   out of this slice is a local diffeomorphism at `(0, 0)`
   (`TauCeti.SmoothForm.IsContactForm.isLocalDiffeomorphAt_flowOf_reebVectorField_comp`) and pulls
   `α₀` back to the contactization form `dt + β` (`(-β).contactization`), where `β` is the
   restriction of `α₀` to the slice (`TauCeti.mpullback_flowOf_comp_apply_eq_contactization`).
3. Because `dβ` is closed and nondegenerate at the origin of the slice, and nondegeneracy is open
   (`TauCeti.SmoothForm.isOpen_setOf_nondegenerate_bilinFormAt`), the symplectic Darboux theorem
   (`TauCeti.SmoothTwoForm.IsSymplectic.exists_standardDarbouxChart`) provides slice coordinates
   `ψ` into `ℝⁿ × ℝⁿ` pulling the standard symplectic form `Σᵢ dqᵢ ∧ dpᵢ` back to `dβ`.
4. On an open ball `B` around `0` in `ℝⁿ × ℝⁿ`, the pushed-forward one-form `β₁ = (ψ⁻¹)^* β` and
   the standard primitive `⟪p, dq⟫` have opposite exterior derivatives, so `β₁ + ⟪p, dq⟫` is
   closed. The Poincaré lemma (`StarConvex.exists_contDiffOn_forall_extDeriv_eq`) supplies a smooth
   function `f` on `B` with `f 0 = 0` and `df = β₁ + ⟪p, dq⟫`. Absorbing `f` into the Reeb-time
   coordinate via `((q, p), t) ↦ (q, p, t + f(q, p))` (the open-domain normed-space counterpart of
   `TauCeti.contactizationShift`) pulls `dz - Σᵢ pᵢ dqᵢ` back to `dt + β₁`, completing the chart.

## Main results

* `PartialDiffeomorph.isStrictContactomorphism_toDiffeomorphSourceTarget_iff`,
  `PartialDiffeomorph.isStrictContactomorphism_toDiffeomorphSourceTarget_modelSpace_iff`: a partial
  diffeomorphism restricts to a strict contactomorphism between its source and target if and only
  if it pulls the target one-form back to the source one-form at every point of its source.
* `TauCeti.SmoothForm.mvfderiv_reebVectorField_of_forall_innerProductContactForm_eq`: a partial
  diffeomorphism into `V × V × ℝ` pulling `dz - ⟪p, dq⟫` back to `α` straightens `α.reebVectorField`
  to `(0, 0, 1)` on its source.
* `TauCeti.IsContactFormAt.exists_partialDiffeomorph_innerProductContactForm_eq`,
  `TauCeti.IsContactFormAt.exists_partialDiffeomorph_innerProductContactForm_eq_of_finrank_eq`:
  strict Darboux partial diffeomorphisms on finite-dimensional real normed spaces.
* `TauCeti.IsContactFormAt.exists_strictDarbouxChart_of_isInteriorPoint`,
  `TauCeti.IsContactFormAt.exists_strictDarbouxChart_of_finrank_eq_of_isInteriorPoint`: strict
  Darboux charts for a locally defined one-form which is contact at an interior point.
* `TauCeti.IsContactFormAt.exists_strictDarbouxChart`,
  `TauCeti.IsContactFormAt.exists_strictDarbouxChart_of_finrank_eq`: the same on boundaryless
  manifolds.
* `TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart_of_isInteriorPoint`,
  `TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart_of_finrank_eq_of_isInteriorPoint`,
  `TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart`,
  `TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart_of_finrank_eq`: global counterparts
  for smooth contact forms.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Theorem 2.5.1.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Theorem 3.5.14.
-/

public section

noncomputable section

open Set Filter Bundle Module TopologicalSpace
open scoped ContDiff Manifold Topology InnerProductSpace

/-! ### Strict contactomorphisms on open domains -/

namespace PartialDiffeomorph

variable {E H M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- A smooth partial diffeomorphism `e` restricts to a strict contactomorphism between its open
source and open target, for the restrictions of smooth one-forms `α` and `β`, if and only if at
every point of `e.source` the differential of `e` pulls `β` back to `α`. -/
theorem isStrictContactomorphism_toDiffeomorphSourceTarget_iff
    (e : PartialDiffeomorph I J M N ∞) (α : TauCeti.SmoothForm I M ℝ 1)
    (β : TauCeti.SmoothForm J N ℝ 1) :
    e.toDiffeomorphSourceTarget.IsStrictContactomorphism
        (TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val α)
        (TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val β) ↔
      ∀ x ∈ e.source, ∀ v : TangentSpace I x, β.1 (e x) ![mfderiv I J e x v] = α.1 x ![v] := by
  let U : Opens M := ⟨e.source, e.open_source⟩
  let W : Opens N := ⟨e.target, e.open_target⟩
  have hcomp : (Subtype.val : W → N) ∘ e.toDiffeomorphSourceTarget = e ∘ (Subtype.val : U → M) :=
    funext fun x ↦ e.toDiffeomorphSourceTarget_apply_coe x
  have hpull (x : U) (v : TangentSpace I x) :
      (TauCeti.SmoothForm.mpullback e.toDiffeomorphSourceTarget
        e.toDiffeomorphSourceTarget.contMDiff
        (TauCeti.SmoothForm.mpullback (Subtype.val : W → N) contMDiff_subtype_val β)).1 x ![v] =
        β.1 (e x) ![mfderiv I J e x (TauCeti.Manifold.tangentSpaceOpenEquiv x v)] := by
    have he : MDifferentiableAt I J e x := e.mdifferentiableAt (n := ∞) (by simp) x.2
    rw [TauCeti.SmoothForm.mpullback_mpullback, TauCeti.SmoothForm.mpullback_apply_one, hcomp,
      Function.comp_apply,
      mfderiv_comp x he ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp)),
      ContinuousLinearMap.comp_apply, TauCeti.Manifold.mfderiv_subtype_val,
      ContinuousLinearEquiv.coe_coe]
  have hrhs (x : U) (v : TangentSpace I x) :
      (TauCeti.SmoothForm.mpullback (Subtype.val : U → M) contMDiff_subtype_val α).1 x ![v] =
        α.1 x ![TauCeti.Manifold.tangentSpaceOpenEquiv x v] := by
    rw [TauCeti.SmoothForm.mpullback_apply_one, TauCeti.Manifold.mfderiv_subtype_val,
      ContinuousLinearEquiv.coe_coe]
  rw [Diffeomorph.isStrictContactomorphism_def, Subtype.ext_iff, funext_iff]
  refine ⟨fun h x hx w ↦ ?_, fun h x ↦ ContinuousAlternatingMap.ext fun m ↦ ?_⟩
  · let x' : U := ⟨x, hx⟩
    let v : TangentSpace I x' := (TauCeti.Manifold.tangentSpaceOpenEquiv x').symm w
    have hv := congrArg (fun A ↦ A ![v]) (h x')
    rwa [hpull, hrhs, ContinuousLinearEquiv.apply_symm_apply] at hv
  · have hm : m = ![m 0] := funext fun i ↦ by fin_cases i; rfl
    rw [hm, hpull, hrhs]
    exact h x.1 x.2 _

/-- For a partial diffeomorphism into a normed space, `e.toDiffeomorphSourceTarget` is a strict
contactomorphism between the restrictions of `α` and `β` if and only if `mvfderiv I e` pulls `β`
back to `α` on `e.source`. -/
theorem isStrictContactomorphism_toDiffeomorphSourceTarget_modelSpace_iff
    (e : PartialDiffeomorph I 𝓘(ℝ, F) M F ∞) (α : TauCeti.SmoothForm I M ℝ 1)
    (β : TauCeti.SmoothForm 𝓘(ℝ, F) F ℝ 1) :
    e.toDiffeomorphSourceTarget.IsStrictContactomorphism
        (TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val α)
        (TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val β) ↔
      ∀ x ∈ e.source, ∀ v : TangentSpace I x, β.1 (e x) ![mvfderiv I e x v] = α.1 x ![v] := by
  simp only [e.isStrictContactomorphism_toDiffeomorphSourceTarget_iff α β,
    mvfderiv_apply_eq_mfderiv_apply]

end PartialDiffeomorph

namespace TauCeti

/-! ### Straightening the Reeb vector field in a strict Darboux chart -/

section ReebStraightening

/-- The pointwise contact condition depends only on the germ of the rough one-form at `x`. -/
private theorem isContactFormAt_of_eventuallyEq {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {α β : RoughForm I M ℝ 1} {x : M} (hc : IsContactFormAt α x)
    (h : ∀ᶠ y in 𝓝 x, α y = β y) :
    IsContactFormAt β x := by
  have hx : α x = β x := h.self_of_nhds
  have hker : α.ker x = β.ker x := by
    ext v
    simp only [RoughForm.mem_ker, hx]
  have hd : mextDeriv α x = mextDeriv β x := mextDeriv_congr_of_eventuallyEq h
  exact ⟨hx ▸ hc.ne_zero, fun v hv hvw ↦
    hc.nondegenerate v (hker.symm ▸ hv) fun w hw ↦ hd ▸ hvw w (hker ▸ hw)⟩

/-- **Reeb straightening in a strict Darboux chart.** If a smooth partial diffeomorphism `chart`
from `M` into `V × V × ℝ` pulls the standard contact form `dz - ⟪p, dq⟫` back to `α` on
`chart.source`, then at every `x ∈ chart.source` the differential of `chart` sends
`α.reebVectorField x` to `(0, 0, 1)`. Neither finite-dimensionality nor global contactness of `α`
is needed. -/
theorem SmoothForm.mvfderiv_reebVectorField_of_forall_innerProductContactForm_eq
    {E H M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] {α : SmoothForm I M ℝ 1}
    {chart : PartialDiffeomorph I 𝓘(ℝ, V × V × ℝ) M (V × V × ℝ) ∞}
    (hchart : ∀ x ∈ chart.source, ∀ v : TangentSpace I x,
      (innerProductContactForm V).1 (chart x) ![mvfderiv I chart x v] = α.1 x ![v])
    {x : M} (hx : x ∈ chart.source) :
    mvfderiv I chart x (α.reebVectorField x) = (0, 0, 1) := by
  let α_std := innerProductContactForm V
  have hd : IsLocalDiffeomorphAt I 𝓘(ℝ, V × V × ℝ) ∞ chart x :=
    chart.isLocalDiffeomorphAt I 𝓘(ℝ, V × V × ℝ) ∞ hx
  have hev : ∀ᶠ y in 𝓝 x, TauCeti.mpullback I 𝓘(ℝ, V × V × ℝ) chart α_std.1 y = α.1 y := by
    filter_upwards [chart.open_source.mem_nhds hx] with y hy
    ext m
    have hvec : (fun i ↦ mfderiv I 𝓘(ℝ, V × V × ℝ) chart y (m i)) =
        (![mvfderiv I chart y (m 0)] : Fin 1 → TangentSpace 𝓘(ℝ, V × V × ℝ) (chart y)) :=
      funext fun i ↦ by fin_cases i; exact (mvfderiv_apply_eq_mfderiv_apply chart y (m 0)).symm
    have hm : m = ![m 0] := funext fun i ↦ by fin_cases i; rfl
    dsimp only [α_std]
    rw [TauCeti.mpullback_apply, hvec, hchart y hy (m 0), ← hm]
  have hf2 : ContMDiffAt I 𝓘(ℝ, V × V × ℝ) 2 chart x := hd.contMDiffAt.of_le (by simp)
  have hbij : Function.Bijective (mfderiv I 𝓘(ℝ, V × V × ℝ) chart x) :=
    (hd.isInvertible_mfderiv (by simp)).bijective
  have hc_pull : IsContactFormAt (TauCeti.mpullback I 𝓘(ℝ, V × V × ℝ) chart α_std.1) x :=
    (isContactFormAt_mpullback_iff hf2 (α_std.contMDiff.of_le (by simp) (chart x)) hbij).2
      (SmoothForm.isContactForm_iff_forall_isContactFormAt.1
        (isContactForm_innerProductContactForm V) (chart x))
  have hc_x : IsContactFormAt α.1 x := isContactFormAt_of_eventuallyEq hc_pull hev
  obtain ⟨v₀, hv₀⟩ := hbij.2 ((NormedSpace.fromTangentSpace (chart x)).symm (0, 0, 1))
  have hmvf : mvfderiv I chart x v₀ = (0, 0, 1) := by
    rw [mvfderiv_apply_eq_mfderiv_apply, hv₀, NormedSpace.fromTangentSpace_symm_apply]
  have hreeb : α.reebVectorField x = v₀ := by
    refine hc_x.reebVectorField_eq_of_apply_eq_one ?_ fun w _ ↦ ?_
    · rw [← hchart x hx v₀]
      have h001 : (![mvfderiv I chart x v₀] : Fin 1 → TangentSpace 𝓘(ℝ, V × V × ℝ) (chart x)) =
          ![(NormedSpace.fromTangentSpace (chart x)).symm (0, 0, 1)] :=
        congrArg (fun u ↦ (![u] : Fin 1 → TangentSpace 𝓘(ℝ, V × V × ℝ) (chart x)))
          ((mvfderiv_apply_eq_mfderiv_apply chart x v₀).trans hv₀)
      rw [h001, innerProductContactForm_apply]
      simp [NormedSpace.fromTangentSpace_symm_apply]
    · rw [← mextDeriv_congr_of_eventuallyEq hev,
        ← mpullback_mextDeriv_at hf2 (α_std.contMDiff.of_le (by simp) (chart x)),
        TauCeti.mpullback_apply]
      have hpair : (fun i ↦ mfderiv I 𝓘(ℝ, V × V × ℝ) chart x (![v₀, w] i)) =
          ![mfderiv I 𝓘(ℝ, V × V × ℝ) chart x v₀, mfderiv I 𝓘(ℝ, V × V × ℝ) chart x w] :=
        funext fun i ↦ by fin_cases i <;> rfl
      rw [hpair, mextDeriv_innerProductContactForm_apply, hv₀,
        NormedSpace.fromTangentSpace_symm_apply]
      simp [stdSymplecticForm_apply]
  rw [hreeb, hmvf]

end ReebStraightening

/-! ### Absorbing a Poincaré primitive into the Reeb coordinate -/

section PrimitiveShift

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The flat one-form `y ↦ (u ↦ ⟪y.2, u.1⟫)` on `V × V`, whose exterior derivative is
`-stdSymplecticForm`. -/
private def momentumOneFormFun (y : V × V) : (V × V) [⋀^Fin 1]→L[ℝ] ℝ :=
  ContinuousAlternatingMap.ofSubsingleton ℝ (V × V) ℝ (0 : Fin 1)
    ((innerSL ℝ y.2).comp (ContinuousLinearMap.fst ℝ V V))

private theorem contDiff_momentumOneFormFun : ContDiff ℝ ∞ (momentumOneFormFun (V := V)) :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := V × V) (F := ℝ)
    (0 : Fin 1)).contDiff.comp <|
      ((innerSL ℝ : V →L[ℝ] V →L[ℝ] ℝ).contDiff.comp contDiff_snd).clm_comp contDiff_const

private theorem extDeriv_momentumOneFormFun_apply (y u w : V × V) :
    extDeriv (momentumOneFormFun (V := V)) y ![u, w] = -stdSymplecticForm u w := by
  have hd (z : Fin 1 → V × V) : HasFDerivAt (fun x : V × V ↦ momentumOneFormFun x z)
      ((innerSL ℝ (z 0).1).comp (ContinuousLinearMap.snd ℝ V V)) y := by
    have hfun : (fun x : V × V ↦ momentumOneFormFun x z) =
        ⇑((innerSL ℝ (z 0).1).comp (ContinuousLinearMap.snd ℝ V V)) := by
      funext x
      simp [momentumOneFormFun, real_inner_comm]
    rw [hfun]
    exact ContinuousLinearMap.hasFDerivAt _
  rw [extDeriv_apply (contDiff_momentumOneFormFun.differentiable (by simp) y), Fin.sum_univ_two,
    (hd _).fderiv, (hd _).fderiv]
  simp [Fin.removeNth, stdSymplecticForm_apply, real_inner_comm w.1]
  ring

/-- On a star-convex open subset `B` of `V × V` centred at `y₀`, any smooth one-form `β₁` whose
exterior derivative is `stdSymplecticForm` differs from `-⟪p, dq⟫` by the differential of a smooth
function `f` vanishing at `y₀`. -/
private theorem exists_primitive_add_inner_eq {B : Set (V × V)} {y₀ : V × V}
    {β₁ : V × V → (V × V) [⋀^Fin 1]→L[ℝ] ℝ} (hB : IsOpen B) (hstar : StarConvex ℝ y₀ B)
    (hβ₁ : ContDiffOn ℝ ∞ β₁ B)
    (hdβ₁ : ∀ y ∈ B, ∀ u w : V × V, extDeriv β₁ y ![u, w] = stdSymplecticForm u w) :
    ∃ f : V × V → ℝ, ContDiffOn ℝ ∞ f B ∧ f y₀ = 0 ∧
      ∀ y ∈ B, ∀ u : V × V, fderiv ℝ f y u = β₁ y ![u] + ⟪y.2, u.1⟫_ℝ := by
  set η₀ : V × V → (V × V) [⋀^Fin 1]→L[ℝ] ℝ := β₁ + momentumOneFormFun
  have hη₀ : ContDiffOn ℝ ∞ η₀ B := hβ₁.add contDiff_momentumOneFormFun.contDiffOn
  have hdη₀ : ∀ y ∈ B, extDeriv η₀ y = 0 := by
    intro y hy
    have hdiff₁ : DifferentiableAt ℝ β₁ y :=
      (hβ₁.differentiableOn (by simp) y hy).differentiableAt (hB.mem_nhds hy)
    have hdiff₂ : DifferentiableAt ℝ (momentumOneFormFun (V := V)) y :=
      contDiff_momentumOneFormFun.differentiable (by simp) y
    ext m
    have hm : m = ![m 0, m 1] := funext fun i ↦ by fin_cases i <;> rfl
    rw [hm]
    dsimp only [η₀]
    simp [extDeriv_add hdiff₁ hdiff₂, hdβ₁ y hy, extDeriv_momentumOneFormFun_apply]
  obtain ⟨γ, hγ, hγ₀, hdγ⟩ :=
    hstar.exists_contDiffOn_forall_extDeriv_eq hB (r := ⊤) le_top hη₀ hdη₀
  let ev₀ : ((V × V) [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousAlternatingMap.apply ℝ (V × V) ℝ (![] : Fin 0 → V × V)
  let f : V × V → ℝ := ⇑ev₀ ∘ γ
  have hf : ContDiffOn ℝ ∞ f B := ev₀.contDiff.comp_contDiffOn hγ
  refine ⟨f, hf, by simp [f, ev₀, hγ₀], fun y hy u ↦ ?_⟩
  have hγ_diff : DifferentiableAt ℝ γ y :=
    (hγ.differentiableOn (by simp) y hy).differentiableAt (hB.mem_nhds hy)
  have hdf : HasFDerivAt f (ev₀.comp (fderiv ℝ γ y)) y :=
    ev₀.hasFDerivAt.comp y hγ_diff.hasFDerivAt
  have heq := congrArg (fun A : (V × V) [⋀^Fin 1]→L[ℝ] ℝ ↦ A ![u]) (hdγ y hy)
  rw [extDeriv_apply_fin_one] at heq
  rw [hdf.fderiv, ContinuousLinearMap.comp_apply]
  simpa [ev₀, η₀, momentumOneFormFun] using heq

/-- The smooth partial diffeomorphism `((q, p), t) ↦ (q, p, t + f (q, p))` from `(V × V) × ℝ`
(with product model `𝓘(ℝ, V × V).prod 𝓘(ℝ)`) to `V × V × ℝ` (with self model `𝓘(ℝ, V × V × ℝ)`),
defined over `B ×ˢ univ` for an open set `B` on which `f` is smooth. -/
private def primitiveShiftPartialDiffeomorph {B : Set (V × V)} {f : V × V → ℝ}
    (hB : IsOpen B) (hf : ContDiffOn ℝ ∞ f B) :
    PartialDiffeomorph (𝓘(ℝ, V × V).prod 𝓘(ℝ)) 𝓘(ℝ, V × V × ℝ)
      ((V × V) × ℝ) (V × V × ℝ) ∞ where
  toFun p := (p.1.1, p.1.2, p.2 + f p.1)
  invFun x := ((x.1, x.2.1), x.2.2 - f (x.1, x.2.1))
  source := B ×ˢ univ
  target := (fun x : V × V × ℝ ↦ (x.1, x.2.1)) ⁻¹' B
  map_source' p hp := hp.1
  map_target' x hx := ⟨hx, mem_univ _⟩
  left_inv' p _ := by simp
  right_inv' x _ := by simp
  open_source := hB.prod isOpen_univ
  open_target := hB.preimage (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  contMDiffOn_toFun := by
    let pr₁ : (V × V) →L[ℝ] V := ContinuousLinearMap.fst ℝ V V
    let pr₂ : (V × V) →L[ℝ] V := ContinuousLinearMap.snd ℝ V V
    have hf' : ContMDiffOn 𝓘(ℝ, V × V) 𝓘(ℝ) ∞ f B := contMDiffOn_iff_contDiffOn.2 hf
    have hfst : ContMDiffOn (𝓘(ℝ, V × V).prod 𝓘(ℝ)) 𝓘(ℝ, V × V) ∞
        (Prod.fst : (V × V) × ℝ → V × V) (B ×ˢ (univ : Set ℝ)) := contMDiffOn_fst
    have hsnd : ContMDiffOn (𝓘(ℝ, V × V).prod 𝓘(ℝ)) 𝓘(ℝ) ∞
        (Prod.snd : (V × V) × ℝ → ℝ) (B ×ˢ (univ : Set ℝ)) := contMDiffOn_snd
    have h1 : ContMDiffOn (𝓘(ℝ, V × V).prod 𝓘(ℝ)) 𝓘(ℝ, V) ∞
        (fun p : (V × V) × ℝ ↦ p.1.1) (B ×ˢ univ) := pr₁.contDiff.contMDiff.comp_contMDiffOn hfst
    have h2 : ContMDiffOn (𝓘(ℝ, V × V).prod 𝓘(ℝ)) 𝓘(ℝ, V) ∞
        (fun p : (V × V) × ℝ ↦ p.1.2) (B ×ˢ univ) := pr₂.contDiff.contMDiff.comp_contMDiffOn hfst
    have h3 : ContMDiffOn (𝓘(ℝ, V × V).prod 𝓘(ℝ)) 𝓘(ℝ) ∞
        (fun p : (V × V) × ℝ ↦ p.2 + f p.1) (B ×ˢ univ) :=
      hsnd.add (hf'.comp hfst fun _ hp ↦ hp.1)
    exact h1.prodMk_space (h2.prodMk_space h3)
  contMDiffOn_invFun := by
    let T : Set (V × V × ℝ) := (fun x : V × V × ℝ ↦ (x.1, x.2.1)) ⁻¹' B
    let pr₁₂ : (V × V × ℝ) →L[ℝ] (V × V) :=
      (ContinuousLinearMap.fst ℝ V (V × ℝ)).prod
        ((ContinuousLinearMap.fst ℝ V ℝ).comp (ContinuousLinearMap.snd ℝ V (V × ℝ)))
    let pr₃ : (V × V × ℝ) →L[ℝ] ℝ :=
      (ContinuousLinearMap.snd ℝ V ℝ).comp (ContinuousLinearMap.snd ℝ V (V × ℝ))
    have hf' : ContMDiffOn 𝓘(ℝ, V × V) 𝓘(ℝ) ∞ f B := contMDiffOn_iff_contDiffOn.2 hf
    have h12 : ContMDiffOn 𝓘(ℝ, V × V × ℝ) 𝓘(ℝ, V × V) ∞ pr₁₂ T :=
      pr₁₂.contDiff.contMDiff.contMDiffOn
    have h3 : ContMDiffOn 𝓘(ℝ, V × V × ℝ) 𝓘(ℝ) ∞ (fun x ↦ pr₃ x - f (pr₁₂ x)) T :=
      pr₃.contDiff.contMDiff.contMDiffOn.sub (hf'.comp h12 fun _ hx ↦ hx)
    exact h12.prodMk h3

/-- If `df(q, p) = β₁(q, p) + ⟪p, dq⟫` on `B`, then `primitiveShiftPartialDiffeomorph` pulls the
standard contact form `dz - ⟪p, dq⟫` back to `dt + β₁` on `B ×ˢ univ`. -/
private theorem innerProductContactForm_primitiveShiftPartialDiffeomorph_apply
    {B : Set (V × V)} {f : V × V → ℝ} {β₁ : V × V → (V × V) [⋀^Fin 1]→L[ℝ] ℝ}
    (hB : IsOpen B) (hf : ContDiffOn ℝ ∞ f B)
    (hdf : ∀ y ∈ B, ∀ u : V × V, fderiv ℝ f y u = β₁ y ![u] + ⟪y.2, u.1⟫_ℝ)
    {p : (V × V) × ℝ} (hp : p ∈ B ×ˢ (univ : Set ℝ))
    (u : TangentSpace (𝓘(ℝ, V × V).prod 𝓘(ℝ)) p) :
    (innerProductContactForm V).1 (primitiveShiftPartialDiffeomorph hB hf p)
      ![mvfderiv (𝓘(ℝ, V × V).prod 𝓘(ℝ)) (primitiveShiftPartialDiffeomorph hB hf) p u] =
      NormedSpace.fromTangentSpace (𝕜 := ℝ) p.2 u.2 +
        β₁ p.1 ![NormedSpace.fromTangentSpace (𝕜 := ℝ) p.1 u.1] := by
  let Θ := primitiveShiftPartialDiffeomorph hB hf
  let g₁ : V × V → V × V × ℝ := fun y ↦ (y.1, y.2, f y)
  let g₂ : ℝ → V × V × ℝ := fun t ↦ (0, 0, t)
  have hΘ_eq : ⇑Θ = g₁ ∘ Prod.fst + g₂ ∘ Prod.snd := by
    funext q
    ext <;> simp [Θ, primitiveShiftPartialDiffeomorph, g₁, g₂, add_comm]
  have hf_at : HasFDerivAt f (fderiv ℝ f p.1) p.1 :=
    ((hf.differentiableOn (by simp) p.1 hp.1).differentiableAt (hB.mem_nhds hp.1)).hasFDerivAt
  have hg₁ : HasFDerivAt g₁ ((ContinuousLinearMap.fst ℝ V V).prod
      ((ContinuousLinearMap.snd ℝ V V).prod (fderiv ℝ f p.1))) p.1 :=
    hasFDerivAt_fst.prodMk (hasFDerivAt_snd.prodMk hf_at)
  have hg₂ : HasFDerivAt g₂
      ((0 : ℝ →L[ℝ] V).prod ((0 : ℝ →L[ℝ] V).prod (ContinuousLinearMap.id ℝ ℝ))) p.2 :=
    (hasFDerivAt_const (0 : V) p.2).prodMk
      ((hasFDerivAt_const (0 : V) p.2).prodMk (hasFDerivAt_id p.2))
  let u₁' : TangentSpace 𝓘(ℝ, V × V) p.1 := u.1
  let u₂' : TangentSpace 𝓘(ℝ) p.2 := u.2
  let u₁ : V × V := NormedSpace.fromTangentSpace (𝕜 := ℝ) p.1 u₁'
  let u₂ : ℝ := NormedSpace.fromTangentSpace (𝕜 := ℝ) p.2 u₂'
  have h1 : mvfderiv 𝓘(ℝ, V × V) g₁ p.1 u₁' = (u₁.1, u₁.2, fderiv ℝ f p.1 u₁) := by
    rw [mvfderiv_eq_fderiv, ContinuousLinearMap.comp_apply, hg₁.fderiv]
    rfl
  have h2 : mvfderiv 𝓘(ℝ) g₂ p.2 u₂' = (0, 0, u₂) := by
    rw [mvfderiv_eq_fderiv, ContinuousLinearMap.comp_apply, hg₂.fderiv]
    rfl
  have hmvf : mvfderiv (𝓘(ℝ, V × V).prod 𝓘(ℝ)) Θ p u =
      (u₁.1, u₁.2, fderiv ℝ f p.1 u₁ + u₂) := by
    have hsum : mvfderiv (𝓘(ℝ, V × V).prod 𝓘(ℝ)) Θ p u =
        mvfderiv 𝓘(ℝ, V × V) g₁ p.1 u₁' + mvfderiv 𝓘(ℝ) g₂ p.2 u₂' := by
      rw [hΘ_eq]
      exact mvfderiv_comp_fst_add_comp_snd_apply
        (mdifferentiableAt_iff_differentiableAt.2 hg₁.differentiableAt)
        (mdifferentiableAt_iff_differentiableAt.2 hg₂.differentiableAt) u
    rw [hsum, h1, h2]
    ext <;> simp
  have h0 : (![mvfderiv (𝓘(ℝ, V × V).prod 𝓘(ℝ)) Θ p u] :
      Fin 1 → TangentSpace 𝓘(ℝ, V × V × ℝ) (Θ p)) =
      ![(NormedSpace.fromTangentSpace (Θ p)).symm (u₁.1, u₁.2, fderiv ℝ f p.1 u₁ + u₂)] :=
    congrArg (fun w ↦ (![w] : Fin 1 → TangentSpace 𝓘(ℝ, V × V × ℝ) (Θ p))) hmvf
  rw [h0, innerProductContactForm_apply, NormedSpace.fromTangentSpace_symm_apply]
  dsimp only [Θ, primitiveShiftPartialDiffeomorph]
  rw [hdf p.1 hp.1 u₁]
  dsimp only [u₁, u₂, u₁', u₂']
  ring

end PrimitiveShift

/-! ### Strict Contact Darboux on finite-dimensional normed spaces -/

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Shrink an open set `W` around `y₀` to an open subset `W₀ : Opens E` on which a smooth flat
one-form `η` restricts to a smooth contact form `α₀`. -/
private theorem exists_opens_isContactForm {η : E → E [⋀^Fin 1]→L[ℝ] ℝ} {W : Set E} {y₀ : E}
    (hc : IsContactFormAt (I := 𝓘(ℝ, E)) η y₀) (hW : IsOpen W) (hy₀W : y₀ ∈ W)
    (hη : ContDiffOn ℝ ∞ η W) :
    ∃ (W₀ : Opens E) (p₀ : W₀) (α₀ : SmoothForm 𝓘(ℝ, E) W₀ ℝ 1),
      (p₀ : E) = y₀ ∧ (W₀ : Set E) ⊆ W ∧ α₀.IsContactForm ∧
      ∀ (p : W₀) (v : TangentSpace 𝓘(ℝ, E) p),
        α₀.1 p ![v] =
          η p.1 ![NormedSpace.fromTangentSpace p.1
            (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, E)) p v)] := by
  let ηR : RoughForm 𝓘(ℝ, E) E ℝ 1 := η
  obtain ⟨W₁', hW₁'_sub, hW₁'_open, hy₀W₁'⟩ :=
    eventually_nhds_iff.1 (hc.eventually ((hη.contDiffAt (hW.mem_nhds hy₀W)).of_le (by simp)))
  let W₀ : Opens E := ⟨W₁' ∩ W, hW₁'_open.inter hW⟩
  let p₀ : W₀ := ⟨y₀, hy₀W₁', hy₀W⟩
  have hη_md (x : W₀) : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (ηR y)) (x : E) := by
    refine contMDiffAt_form_of_contDiffWithinAt_inChartAt_self ?_
    simp only [RoughForm.inChartAt_modelSpace, modelWithCornersSelf_coe, range_id,
      extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq]
    exact hη.contDiffAt (hW.mem_nhds x.2.2)
  have hsmooth :
      IsSmoothForm 𝓘(ℝ, E) ∞ (mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : W₀ → E) ηR) :=
    (isSmoothForm_def (I := 𝓘(ℝ, E)) ∞ _).2 fun x ↦
      (hη_md x).mpullback_form (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (n := ∞) (x := x)) (by simp)
  let α₀ : SmoothForm 𝓘(ℝ, E) W₀ ℝ 1 := ⟨_, hsmooth.mem_smoothBundleForms⟩
  have hbij (x : W₀) :
      Function.Bijective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : W₀ → E) x) := by
    rw [Manifold.mfderiv_subtype_val]
    exact (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, E)) x).bijective
  have hα₀ : α₀.IsContactForm :=
    SmoothForm.isContactForm_iff_forall_isContactFormAt.2 fun x ↦
      (isContactFormAt_mpullback_iff
        ((contMDiff_subtype_val (I := 𝓘(ℝ, E)) (n := ∞)).contMDiffAt.of_le (by simp))
        ((hη_md x).of_le (by simp)) (hbij x)).2 (hW₁'_sub x.1 x.2.1)
  refine ⟨W₀, p₀, α₀, rfl, inter_subset_right, hα₀, fun p v ↦ ?_⟩
  change mpullback 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : W₀ → E) ηR p ![v] = _
  rw [mpullback_apply]
  refine congrArg (η p.1) (funext fun i ↦ ?_)
  fin_cases i
  dsimp only [Matrix.cons_val_zero]
  rw [Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe]
  exact (NormedSpace.fromTangentSpace_apply p.1
    (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, E)) p v)).symm

/-- Construct the affine contact-hyperplane slice `ι_K : S_K → W₀` through `p₀` along
`K = ker α₀(p₀)`, which has codimension one and is transverse to the Reeb vector field at `p₀`. -/
private theorem exists_contactHyperplaneSlice_opens {W₀ : Opens E} (p₀ : W₀)
    {α₀ : SmoothForm 𝓘(ℝ, E) W₀ ℝ 1} (hα₀ : α₀.IsContactForm) :
    ∃ (K : Submodule ℝ E) (S_K : Opens K) (s₀ : S_K) (ι_K : S_K → W₀),
      finrank ℝ K + 1 = finrank ℝ E ∧
      ContMDiff 𝓘(ℝ, K) 𝓘(ℝ, E) ∞ ι_K ∧
      ι_K s₀ = p₀ ∧
      Function.Injective (mfderiv 𝓘(ℝ, K) 𝓘(ℝ, E) ι_K s₀) ∧
      α₀.reebVectorField (ι_K s₀) ∉ (mfderiv 𝓘(ℝ, K) 𝓘(ℝ, E) ι_K s₀).range := by
  let e_at (x : W₀) : TangentSpace 𝓘(ℝ, E) x ≃L[ℝ] E :=
    (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, E)) x).trans (NormedSpace.fromTangentSpace x.1)
  let L_at (x : W₀) : E →ₗ[ℝ] ℝ :=
    ((SmoothForm.degreeOneEquiv α₀ x).comp (e_at x).symm.toContinuousLinearMap).toLinearMap
  have hL_apply (x : W₀) (u : TangentSpace 𝓘(ℝ, E) x) : L_at x (e_at x u) = α₀.1 x ![u] := by
    change SmoothForm.degreeOneEquiv α₀ x ((e_at x).symm (e_at x u)) = α₀.1 x ![u]
    rw [ContinuousLinearEquiv.symm_apply_apply, SmoothForm.degreeOneEquiv_apply_apply_vec]
  let K : Submodule ℝ E := LinearMap.ker (L_at p₀)
  have hL_ne : L_at p₀ ≠ 0 := fun h0 ↦
    (SmoothForm.isContactForm_iff_forall_isContactFormAt.1 hα₀ p₀).ne_zero <| by
      ext m
      have hm : m = ![m 0] := funext fun i ↦ by fin_cases i; rfl
      rw [hm, ← hL_apply p₀ (m 0), h0]
      rfl
  have hdimK : finrank ℝ K + 1 = finrank ℝ E := Module.Dual.finrank_ker_add_one_of_ne_zero hL_ne
  let S_K : Opens K := ⟨{w : K | (p₀ : E) + K.subtypeL w ∈ W₀},
    (continuous_const.add K.subtypeL.continuous).isOpen_preimage _ W₀.2⟩
  let s₀ : S_K := ⟨0, by change (p₀ : E) + K.subtypeL 0 ∈ W₀; simp [p₀.2]⟩
  let ι_K : S_K → W₀ := fun w ↦ ⟨(p₀ : E) + K.subtypeL w.1, w.2⟩
  have hι_K : ContMDiff 𝓘(ℝ, K) 𝓘(ℝ, E) ∞ ι_K := (ContMDiff.subtypeVal_comp_iff W₀ _).1 <|
    contMDiff_const.add (K.subtypeL.contDiff.contMDiff.comp contMDiff_subtype_val)
  have hι_s₀ : ι_K s₀ = p₀ := Subtype.ext (by simp [ι_K, s₀])
  let e_s₀ : TangentSpace 𝓘(ℝ, K) s₀ ≃L[ℝ] K :=
    (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, K)) s₀).trans (NormedSpace.fromTangentSpace s₀.1)
  have hdι (v : TangentSpace 𝓘(ℝ, K) s₀) :
      e_at (ι_K s₀) (mfderiv 𝓘(ℝ, K) 𝓘(ℝ, E) ι_K s₀ v) = K.subtypeL (e_s₀ v) := by
    let A : K → E := fun w ↦ (p₀ : E) + K.subtypeL w
    have hA : HasFDerivAt A K.subtypeL s₀.1 := by
      convert (hasFDerivAt_const (p₀ : E) s₀.1).add K.subtypeL.hasFDerivAt using 1
      exact (zero_add _).symm
    refine (congrArg (NormedSpace.fromTangentSpace (ι_K s₀).1)
      (Manifold.tangentSpaceOpenEquiv_mfderiv_apply (I := 𝓘(ℝ, K)) (I' := 𝓘(ℝ, E))
        (f := ι_K) (A := A) rfl v)).trans ?_
    rw [NormedSpace.fromTangentSpace_apply, ← mvfderiv_apply_eq_mfderiv_apply,
      mvfderiv_eq_fderiv, ContinuousLinearMap.comp_apply, hA.fderiv]
    rfl
  have hι_inj : Function.Injective (mfderiv 𝓘(ℝ, K) 𝓘(ℝ, E) ι_K s₀) := fun v w hvw ↦ by
    have h1 := congrArg (e_at (ι_K s₀)) hvw
    rw [hdι, hdι] at h1
    exact e_s₀.injective (Subtype.ext h1)
  have hR : α₀.reebVectorField (ι_K s₀) ∉ (mfderiv 𝓘(ℝ, K) 𝓘(ℝ, E) ι_K s₀).range := by
    rintro ⟨v, hv⟩
    have h1 : α₀.1 (ι_K s₀) ![α₀.reebVectorField (ι_K s₀)] = 1 := hα₀.apply_reebVectorField _
    have h0 : α₀.1 (ι_K s₀) ![mfderiv 𝓘(ℝ, K) 𝓘(ℝ, E) ι_K s₀ v] = 0 := by
      rw [← hL_apply (ι_K s₀), hdι v, hι_s₀]
      exact LinearMap.mem_ker.1 (e_s₀ v).2
    exact zero_ne_one (h0.symm.trans (hv ▸ h1))
  exact ⟨K, S_K, s₀, ι_K, hdimK, hι_K, hι_s₀, hι_inj, hR⟩

/-- Construct the local Reeb-slice partial diffeomorphism `Ψ : W₀ → S_K × ℝ` around `p₀` along the
affine contact hyperplane `p₀ + ker α₀(p₀)`, pulling the contactization `dt + β` back to `α₀` and
making `dβ` nondegenerate at the origin `s₀` of the slice. -/
private theorem exists_reebSliceChart_opens {W₀ : Opens E} (p₀ : W₀)
    {α₀ : SmoothForm 𝓘(ℝ, E) W₀ ℝ 1} (hα₀ : α₀.IsContactForm) :
    ∃ (K : Submodule ℝ E) (S_K : Opens K) (s₀ : S_K) (β : SmoothForm 𝓘(ℝ, K) S_K ℝ 1)
      (Ψ : PartialDiffeomorph 𝓘(ℝ, E) (𝓘(ℝ, K).prod 𝓘(ℝ)) W₀ (S_K × ℝ) ∞),
      finrank ℝ K + 1 = finrank ℝ E ∧
      ((mextDerivₗ 𝓘(ℝ, K) 1 β).bilinFormAt s₀).Nondegenerate ∧
      p₀ ∈ Ψ.source ∧ Ψ p₀ = (s₀, 0) ∧
      ∀ p ∈ Ψ.source, ∀ v : TangentSpace 𝓘(ℝ, E) p,
        (-β).contactization.1 (Ψ p) ![mfderiv 𝓘(ℝ, E) (𝓘(ℝ, K).prod 𝓘(ℝ)) Ψ p v] =
          α₀.1 p ![v] := by
  obtain ⟨K, S_K, s₀, ι_K, hdimK, hι_K, hι_s₀, hι_inj, hR⟩ :=
    exists_contactHyperplaneSlice_opens p₀ hα₀
  let β : SmoothForm 𝓘(ℝ, K) S_K ℝ 1 := SmoothForm.mpullback ι_K hι_K α₀
  have hnd₀ : ((mextDerivₗ 𝓘(ℝ, K) 1 β).bilinFormAt s₀).Nondegenerate :=
    hα₀.nondegenerate_bilinFormAt_mextDerivₗ_mpullback hι_K hdimK hι_inj hR
  have h0_dom : ((0 : ℝ), ι_K s₀) ∈ flowDomain α₀.reebVectorField :=
    mem_flowDomain_zero (hα₀.contMDiff_reebVectorField.of_le (by simp)) _
  let F : S_K × ℝ → W₀ := fun q ↦ flowOf α₀.reebVectorField q.2 (ι_K q.1)
  have hloc : IsLocalDiffeomorphAt (𝓘(ℝ, K).prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ F (s₀, 0) :=
    hα₀.isLocalDiffeomorphAt_flowOf_reebVectorField_comp hι_K hdimK (p := (s₀, 0)) hι_inj hR h0_dom
  let D : Set (S_K × ℝ) := {q | (q.2, ι_K q.1) ∈ flowDomain α₀.reebVectorField}
  have hD : IsOpen D := isOpen_setOf_mem_flowDomain
    (hα₀.contMDiff_reebVectorField.of_le (by simp)) continuous_snd
    (hι_K.continuous.comp continuous_fst)
  let Φ := hloc.localInverse.symm
  let Φ' := Φ.restrOpen D hD
  let Ψ := Φ'.symm
  have hΦ'_src : Φ'.source = Φ.source ∩ D := Φ.restrOpen_source hD
  have hfΦ : ∀ q ∈ Φ.source, F q = Φ q := fun q hq ↦ by
    have h1 : F (hloc.localInverse (Φ q)) = Φ q := hloc.localInverse_right_inv (Φ.map_source hq)
    have h2 : hloc.localInverse (Φ q) = q := Φ.left_inv hq
    rwa [h2] at h1
  have hs₀_src : (s₀, (0 : ℝ)) ∈ Φ'.source := hΦ'_src ▸ ⟨hloc.localInverse_mem_target, h0_dom⟩
  have hΦ'_zero : Φ' (s₀, 0) = p₀ := by
    rw [PartialDiffeomorph.coe_restrOpen, ← hfΦ (s₀, 0) hloc.localInverse_mem_target]
    dsimp only [F]
    rw [flowOf_zero, hι_s₀]
  refine ⟨K, S_K, s₀, β, Ψ, hdimK, hnd₀, hΦ'_zero ▸ Φ'.map_source hs₀_src,
    hΦ'_zero ▸ Φ'.left_inv hs₀_src, fun p hp v ↦ ?_⟩
  have hΨp : Ψ p ∈ Φ'.source := Ψ.map_source hp
  have hev_F : F =ᶠ[𝓝 (Ψ p)] Φ' := eventually_of_mem (Φ'.open_source.mem_nhds hΨp) fun q hq ↦ by
    rw [PartialDiffeomorph.coe_restrOpen]
    exact hfΦ q (hΦ'_src ▸ hq).1
  have hpull_symm : mpullback (𝓘(ℝ, K).prod 𝓘(ℝ)) 𝓘(ℝ, E) Φ' α₀.1 (Ψ p) =
      (-β).contactization.1 (Ψ p) := by
    rw [hev_F.symm.mpullback_eq]
    exact mpullback_flowOf_comp_apply_eq_contactization hα₀.contMDiff_reebVectorField hι_K
      hα₀.apply_reebVectorField hα₀.interior_mextDeriv_reebVectorField (hΦ'_src ▸ hΨp).2
  have hid : Φ' ∘ Ψ =ᶠ[𝓝 p] id :=
    eventually_of_mem (Ψ.open_source.mem_nhds hp) fun p' hp' ↦ Φ'.right_inv hp'
  have hm := congrArg (fun A ↦ A ![v]) <| mpullback_comp_at (I := 𝓘(ℝ, E))
    (I' := 𝓘(ℝ, K).prod 𝓘(ℝ)) (I'' := 𝓘(ℝ, E))
    (Ψ.mdifferentiableAt (n := ∞) (by simp) hp) (Φ'.mdifferentiableAt (n := ∞) (by simp) hΨp) α₀.1
  have hvec : (fun i ↦ mfderiv 𝓘(ℝ, E) (𝓘(ℝ, K).prod 𝓘(ℝ)) Ψ p (![v] i)) =
      ![mfderiv 𝓘(ℝ, E) (𝓘(ℝ, K).prod 𝓘(ℝ)) Ψ p v] :=
    funext fun i ↦ by fin_cases i; rfl
  rw [hid.mpullback_eq, mpullback_id, mpullback_apply, hpull_symm, hvec] at hm
  exact hm.symm

/-- Construct standard Euclidean symplectic Darboux coordinates `ψ : S_K → ℝⁿ × ℝⁿ` around a point
`s₀` of an open subset `S_K : Opens K` where `dβ` is nondegenerate. -/
private theorem exists_symplecticSliceDarboux_opens {K : Type*} [NormedAddCommGroup K]
    [NormedSpace ℝ K] [FiniteDimensional ℝ K] {S_K : Opens K} {s₀ : S_K}
    {β : SmoothForm 𝓘(ℝ, K) S_K ℝ 1}
    (hnd₀ : ((mextDerivₗ 𝓘(ℝ, K) 1 β).bilinFormAt s₀).Nondegenerate) :
    ∃ (n : ℕ) (ψ : PartialDiffeomorph 𝓘(ℝ, K)
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) S_K
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ∞),
      finrank ℝ K = 2 * n ∧ s₀ ∈ ψ.source ∧ ψ s₀ = 0 ∧
      ∀ z ∈ ψ.target,
        ∀ u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) z,
          (mextDerivₗ 𝓘(ℝ, K) 1 β).eval₂ (ψ.symm z)
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, K) ψ.symm z u)
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, K) ψ.symm z w) =
            stdSymplecticForm (NormedSpace.fromTangentSpace z u)
              (NormedSpace.fromTangentSpace z w) := by
  let σ : SmoothTwoForm 𝓘(ℝ, K) S_K := mextDerivₗ 𝓘(ℝ, K) 1 β
  let S₀ : Opens S_K := ⟨{s | (σ.bilinFormAt s).Nondegenerate},
    σ.isOpen_setOf_nondegenerate_bilinFormAt⟩
  let σ₀ : SmoothTwoForm 𝓘(ℝ, K) S₀ := SmoothForm.mpullback Subtype.val contMDiff_subtype_val σ
  have hσ₀ : σ₀.IsSymplectic := by
    refine ⟨(SmoothForm.isClosed_mextDerivₗ β).mpullback _ _,
      SmoothTwoForm.isNondegenerate_iff_separatingLeft.2 fun x v hv ↦ ?_⟩
    apply (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, K)) x).injective
    rw [map_zero]
    refine x.2.1 _ fun w ↦ ?_
    have h := hv ((Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, K)) x).symm w)
    rwa [SmoothForm.eval₂_mpullback, Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, ← SmoothForm.bilinFormAt_apply] at h
  obtain ⟨n, ψ₀, hs₀', h0', hchart₀⟩ := hσ₀.exists_standardDarbouxChart ⟨s₀, hnd₀⟩
  obtain ⟨ψ, hs₀, -, h0, ht_sub, hsymm⟩ := ψ₀.exists_ambient_of_opens hs₀'
  have hdim : finrank ℝ K = 2 * n := by
    have hL : finrank ℝ K = finrank ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
      ((ψ.isLocalDiffeomorphAt _ _ _ hs₀).mfderivToContinuousLinearEquiv
        (by simp)).toLinearEquiv.finrank_eq
    rw [finrank_prod, finrank_euclideanSpace_fin] at hL
    omega
  refine ⟨n, ψ, hdim, hs₀, h0.trans h0', fun z hz u w ↦ ?_⟩
  let J := 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
  have hz₀ : z ∈ ψ₀.target := ht_sub hz
  have hx₀ : ψ₀.symm z ∈ ψ₀.source := ψ₀.map_target hz₀
  have hev_symm : ψ.symm =ᶠ[𝓝 z] (Subtype.val : S₀ → S_K) ∘ ψ₀.symm :=
    eventually_of_mem (ψ.open_target.mem_nhds hz) hsymm
  have hid₀ : ψ₀ ∘ ψ₀.symm =ᶠ[𝓝 z] id :=
    eventually_of_mem (ψ₀.open_target.mem_nhds hz₀) fun z' hz' ↦ ψ₀.right_inv hz'
  have hinv_d (a : TangentSpace J z) :
      mvfderiv 𝓘(ℝ, K) ψ₀ (ψ₀.symm z) (mfderiv J 𝓘(ℝ, K) ψ₀.symm z a) =
        NormedSpace.fromTangentSpace z a := by
    rw [← mvfderiv_comp_apply z (ψ₀.mdifferentiableAt (n := ∞) (by simp) hx₀)
        (ψ₀.symm.mdifferentiableAt (n := ∞) (by simp) hz₀),
      hid₀.mvfderiv_eq, mvfderiv_apply_eq_mfderiv_apply, mfderiv_id,
      ContinuousLinearMap.id_apply]
    exact (NormedSpace.fromTangentSpace_apply z a).symm
  have key := hchart₀ (ψ₀.symm z) hx₀ (mfderiv J 𝓘(ℝ, K) ψ₀.symm z u)
    (mfderiv J 𝓘(ℝ, K) ψ₀.symm z w)
  rw [hinv_d u, hinv_d w, SmoothBundleForm.eval₂_apply, SmoothForm.coe_mpullback,
    ← mpullback_apply_pair,
    ← mpullback_comp_at (ψ₀.symm.mdifferentiableAt (n := ∞) (by simp) hz₀)
      ((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp)),
    ← hev_symm.mpullback_eq, mpullback_apply_pair, ← SmoothBundleForm.eval₂_apply] at key
  exact key

/-- On an open ball `B ⊆ ψ.target` around `0`, construct a smooth function `f` vanishing at `0`
whose differential absorbs the Poincaré difference between `(ψ.symm)* β` and `-⟪p, dq⟫`. -/
private theorem exists_primitive_of_symplecticSliceDarboux {K : Type*} [NormedAddCommGroup K]
    [NormedSpace ℝ K] {S_K : Opens K} {s₀ : S_K} {β : SmoothForm 𝓘(ℝ, K) S_K ℝ 1} {n : ℕ}
    {ψ : PartialDiffeomorph 𝓘(ℝ, K)
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) S_K
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ∞}
    (hs₀ψ : s₀ ∈ ψ.source) (hψs₀ : ψ s₀ = 0)
    (hψ_symp : ∀ z ∈ ψ.target,
      ∀ u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) z,
        (mextDerivₗ 𝓘(ℝ, K) 1 β).eval₂ (ψ.symm z)
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, K) ψ.symm z u)
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, K) ψ.symm z w) =
          stdSymplecticForm (NormedSpace.fromTangentSpace z u)
            (NormedSpace.fromTangentSpace z w)) :
    ∃ (B : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
      (f : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ),
      IsOpen B ∧ 0 ∈ B ∧ B ⊆ ψ.target ∧ ContDiffOn ℝ ∞ f B ∧ f 0 = 0 ∧
      ∀ y ∈ B, ∀ u : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        fderiv ℝ f y u =
          mpullbackWithin 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, K)
            ψ.symm B β.1 y ![(NormedSpace.fromTangentSpace y).symm u] + ⟪y.2, u.1⟫_ℝ := by
  let V := EuclideanSpace ℝ (Fin n)
  obtain ⟨r, hr, hBr⟩ := Metric.isOpen_iff.1 ψ.open_target 0 (hψs₀ ▸ ψ.map_source hs₀ψ)
  let B : Set (V × V) := Metric.ball 0 r
  have hB_open : IsOpen B := Metric.isOpen_ball
  let β₁ : V × V → (V × V) [⋀^Fin 1]→L[ℝ] ℝ := mpullbackWithin 𝓘(ℝ, V × V) 𝓘(ℝ, K) ψ.symm B β.1
  have hψ_on : ContMDiffOn 𝓘(ℝ, V × V) 𝓘(ℝ, K) ∞ ψ.symm B := ψ.symm.contMDiffOn.mono hBr
  have hβ₁ : ContDiffOn ℝ ∞ β₁ B := fun y hy ↦
    RoughForm.contDiffWithinAt_of_contMDiffWithinAt_modelSpace <|
      ContMDiffOn.mpullbackWithin_form (β.contMDiff.contMDiffOn (s := univ)) hψ_on (by simp)
        (mapsTo_univ _ _) hB_open.uniqueMDiffOn y hy
  have hdβ₁ (y : V × V) (hy : y ∈ B) (u w : V × V) :
      extDeriv β₁ y ![u, w] = stdSymplecticForm u w := by
    have h : extDerivWithin β₁ B y =
        mpullbackWithin 𝓘(ℝ, V × V) 𝓘(ℝ, K) ψ.symm B (mextDeriv β.1) y :=
      extDerivWithin_mpullbackWithin (φ := β.1) ((hψ_on y hy).of_le (by simp))
        hB_open.uniqueDiffOn (subset_closure (hB_open.interior_eq.symm ▸ hy))
        hy ((β.contMDiff (ψ.symm y)).mdifferentiableAt (by simp))
    let u' : TangentSpace 𝓘(ℝ, V × V) y := (NormedSpace.fromTangentSpace y).symm u
    let w' : TangentSpace 𝓘(ℝ, V × V) y := (NormedSpace.fromTangentSpace y).symm w
    have hpair : (fun i ↦ mfderivWithin 𝓘(ℝ, V × V) 𝓘(ℝ, K) ψ.symm B y (![u', w'] i)) =
        ![mfderiv 𝓘(ℝ, V × V) 𝓘(ℝ, K) ψ.symm y u', mfderiv 𝓘(ℝ, V × V) 𝓘(ℝ, K) ψ.symm y w'] :=
      funext fun i ↦ by
        fin_cases i <;>
          exact congrFun (congrArg DFunLike.coe (mfderivWithin_of_isOpen hB_open hy)) _
    have h1 : extDeriv β₁ y ![u, w] = extDerivWithin β₁ B y ![u, w] := by
      rw [extDerivWithin_of_isOpen hB_open hy]
    have h2 : extDerivWithin β₁ B y ![u, w] =
        mpullbackWithin 𝓘(ℝ, V × V) 𝓘(ℝ, K) ψ.symm B (mextDeriv β.1) y ![u', w'] :=
      congrArg (fun A : (V × V) [⋀^Fin 2]→L[ℝ] ℝ ↦ A ![u, w]) h
    rw [h1, h2, mpullbackWithin_apply, hpair, ← mextDerivₗ_apply 𝓘(ℝ, K) 1 β,
      ← SmoothBundleForm.eval₂_apply]
    simpa [u', w'] using hψ_symp y (hBr hy) u' w'
  obtain ⟨f, hf, hf₀, hdf⟩ := exists_primitive_add_inner_eq hB_open
    ((convex_ball (0 : V × V) r).starConvex (Metric.mem_ball_self hr)) hβ₁ hdβ₁
  exact ⟨B, f, hB_open, Metric.mem_ball_self hr, hBr, hf, hf₀, hdf⟩

/-- Evaluating `mpullbackWithin ψ.symm B β` at `ψ s` along `dψ_s u` recovers `β_s u` when `B` is
an open subset of `ψ.target` containing `ψ s`. -/
private theorem mpullbackWithin_symm_mfderiv_apply {K F : Type*} [NormedAddCommGroup K]
    [NormedSpace ℝ K] [NormedAddCommGroup F] [NormedSpace ℝ F] {S_K : Opens K}
    {ψ : PartialDiffeomorph 𝓘(ℝ, K) 𝓘(ℝ, F) S_K F ∞} {B : Set F}
    (hB_open : IsOpen B) (hBr : B ⊆ ψ.target) (β : SmoothForm 𝓘(ℝ, K) S_K ℝ 1)
    {s : S_K} (hs : s ∈ ψ.source) (hψs : ψ s ∈ B) (u : TangentSpace 𝓘(ℝ, K) s) :
    (mpullbackWithin 𝓘(ℝ, F) 𝓘(ℝ, K) ψ.symm B β.1 (ψ s) : F [⋀^Fin 1]→L[ℝ] ℝ)
      ![NormedSpace.fromTangentSpace (ψ s) (mfderiv 𝓘(ℝ, K) 𝓘(ℝ, F) ψ s u)] = β.1 s ![u] := by
  have hid_ψ : ψ.symm ∘ ψ =ᶠ[𝓝 s] id :=
    eventually_of_mem (ψ.open_source.mem_nhds hs) fun s' hs' ↦ ψ.left_inv hs'
  have hd_ψ := ψ.mdifferentiableAt (n := ∞) (by simp) hs
  have hd_symm := ψ.symm.mdifferentiableAt (n := ∞) (by simp) (hBr hψs)
  have hpull_ψ :
      mpullback 𝓘(ℝ, K) 𝓘(ℝ, F) ψ (mpullback 𝓘(ℝ, F) 𝓘(ℝ, K) ψ.symm β.1) s = β.1 s := by
    rw [← mpullback_comp_at hd_ψ hd_symm, hid_ψ.mpullback_eq, mpullback_id]
  let dψu : TangentSpace 𝓘(ℝ, F) (ψ s) := mfderiv 𝓘(ℝ, K) 𝓘(ℝ, F) ψ s u
  have h1 : (mpullbackWithin 𝓘(ℝ, F) 𝓘(ℝ, K) ψ.symm B β.1 (ψ s) : F [⋀^Fin 1]→L[ℝ] ℝ)
      ![NormedSpace.fromTangentSpace (ψ s) dψu] =
      mpullback 𝓘(ℝ, F) 𝓘(ℝ, K) ψ.symm β.1 (ψ s) ![dψu] :=
    congrArg (fun A : F [⋀^Fin 1]→L[ℝ] ℝ ↦ A ![dψu])
      (mpullbackWithin_eq_mpullback (hB_open.uniqueMDiffWithinAt hψs) hd_symm β.1)
  have h2 : (fun i ↦ mfderiv 𝓘(ℝ, K) 𝓘(ℝ, F) ψ s (![u] i)) = ![dψu] :=
    funext fun i ↦ by fin_cases i; rfl
  rw [h1, ← h2, ← mpullback_apply, hpull_ψ]

/-- Given slice Darboux coordinates `ψ : S_K → ℝⁿ × ℝⁿ` around `s₀` pulling `dβ` back to the
standard symplectic form, combine `ψ × id` with the Poincaré primitive shift on an open ball around
`0` to obtain a partial diffeomorphism `Ω : S_K × ℝ → ℝⁿ × ℝⁿ × ℝ` pulling `innerProductContactForm`
back to `(-β).contactization`. -/
private theorem exists_contactizationToInnerProductChart {K : Type*} [NormedAddCommGroup K]
    [NormedSpace ℝ K] {S_K : Opens K} {s₀ : S_K} {β : SmoothForm 𝓘(ℝ, K) S_K ℝ 1} {n : ℕ}
    {ψ : PartialDiffeomorph 𝓘(ℝ, K)
      𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) S_K
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ∞}
    (hs₀ψ : s₀ ∈ ψ.source) (hψs₀ : ψ s₀ = 0)
    (hψ_symp : ∀ z ∈ ψ.target,
      ∀ u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) z,
        (mextDerivₗ 𝓘(ℝ, K) 1 β).eval₂ (ψ.symm z)
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, K) ψ.symm z u)
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, K) ψ.symm z w) =
          stdSymplecticForm (NormedSpace.fromTangentSpace z u)
            (NormedSpace.fromTangentSpace z w)) :
    ∃ Ω : PartialDiffeomorph (𝓘(ℝ, K).prod 𝓘(ℝ))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) (S_K × ℝ)
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞,
      (s₀, (0 : ℝ)) ∈ Ω.source ∧ Ω (s₀, 0) = 0 ∧
      ∀ q ∈ Ω.source, ∀ u : TangentSpace (𝓘(ℝ, K).prod 𝓘(ℝ)) q,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (Ω q)
          ![mvfderiv (𝓘(ℝ, K).prod 𝓘(ℝ)) Ω q u] = (-β).contactization.1 q ![u] := by
  let V := EuclideanSpace ℝ (Fin n)
  obtain ⟨B, f, hB_open, h0B, hBr, hf, hf₀, hdf⟩ :=
    exists_primitive_of_symplecticSliceDarboux hs₀ψ hψs₀ hψ_symp
  let β₁ : V × V → (V × V) [⋀^Fin 1]→L[ℝ] ℝ := mpullbackWithin 𝓘(ℝ, V × V) 𝓘(ℝ, K) ψ.symm B β.1
  let id_ℝ : PartialDiffeomorph 𝓘(ℝ) 𝓘(ℝ) ℝ ℝ ∞ :=
    (ContinuousLinearEquiv.refl ℝ ℝ).toPartialDiffeomorph
  have hid_src : id_ℝ.source = univ := by
    change ((ContinuousLinearEquiv.refl ℝ ℝ).toPartialDiffeomorph).toPartialEquiv.source = univ
    simp
  have hid_apply (t : ℝ) : id_ℝ t = t := by
    change ((ContinuousLinearEquiv.refl ℝ ℝ).toPartialDiffeomorph).toPartialEquiv t = t
    simp
  have hprod_src : (ψ.prod id_ℝ).source = ψ.source ×ˢ univ := by
    rw [PartialDiffeomorph.prod_source, hid_src]
  have hprod_coe : ⇑(ψ.prod id_ℝ) = Prod.map ψ id :=
    funext fun r ↦ by rw [PartialDiffeomorph.prod_apply, hid_apply]; rfl
  let Θ := primitiveShiftPartialDiffeomorph hB_open hf
  let Ω := (ψ.prod id_ℝ).trans Θ
  have hΩ_coe : ⇑Ω = ⇑Θ ∘ Prod.map ψ id := by rw [PartialDiffeomorph.coe_trans, hprod_coe]
  have hs₀Ω : (s₀, (0 : ℝ)) ∈ Ω.source := by
    rw [PartialDiffeomorph.trans_source, hprod_src, mem_inter_iff, mem_preimage, hprod_coe]
    exact ⟨⟨hs₀ψ, mem_univ 0⟩, by simp [Θ, primitiveShiftPartialDiffeomorph, hψs₀, h0B]⟩
  have hΩ₀ : Ω (s₀, 0) = 0 := by
    rw [hΩ_coe, Function.comp_apply]
    simp [Θ, primitiveShiftPartialDiffeomorph, hψs₀, hf₀]
  refine ⟨Ω, hs₀Ω, hΩ₀, fun q hq u ↦ ?_⟩
  rw [PartialDiffeomorph.trans_source, hprod_src, mem_inter_iff, mem_preimage, hprod_coe] at hq
  have hd_ψ := ψ.mdifferentiableAt (n := ∞) (by simp) hq.1.1
  have hd_pm : MDifferentiableAt (𝓘(ℝ, K).prod 𝓘(ℝ)) (𝓘(ℝ, V × V).prod 𝓘(ℝ)) (Prod.map ψ id) q :=
    hprod_coe ▸ (ψ.prod id_ℝ).mdifferentiableAt (n := ∞) (by simp) (hprod_src ▸ hq.1)
  have hd_Θ := Θ.mdifferentiableAt (n := ∞) (by simp) hq.2
  let u₁ : TangentSpace 𝓘(ℝ, K) q.1 := u.1
  let u₂ : TangentSpace 𝓘(ℝ) q.2 := u.2
  rw [hΩ_coe, Function.comp_apply, mvfderiv_comp_apply q hd_Θ hd_pm,
    innerProductContactForm_primitiveShiftPartialDiffeomorph_apply hB_open hf hdf hq.2,
    mfderiv_prodMap hd_ψ mdifferentiableAt_id, mfderiv_id]
  have hβ₁ : β₁ (ψ q.1) ![NormedSpace.fromTangentSpace (ψ q.1)
      (mfderiv 𝓘(ℝ, K) 𝓘(ℝ, V × V) ψ q.1 u₁)] = β.1 q.1 ![u₁] :=
    mpullbackWithin_symm_mfderiv_apply hB_open hBr β hq.1.1 hq.2.1 u₁
  change NormedSpace.fromTangentSpace q.2 u₂ +
      β₁ (ψ q.1) ![NormedSpace.fromTangentSpace (ψ q.1)
        (mfderiv 𝓘(ℝ, K) 𝓘(ℝ, V × V) ψ q.1 u₁)] = (-β).contactization.1 q ![u]
  rw [hβ₁, SmoothForm.contactization_apply, NormedSpace.fromTangentSpace_apply,
    NormedSpace.fromTangentSpace_apply]
  simp [u₁, u₂, Manifold.tangentSpaceProdEquiv_apply]

omit [FiniteDimensional ℝ E] in
/-- If `Φ` extends a partial diffeomorphism `Ξ` defined on an open subset `W₀ : Opens E` to the
ambient space `E`, then `Φ ∘ Subtype.val` agrees with `Ξ` on a neighborhood of `⟨y, hy⟩` for every
`y ∈ Φ.source`. -/
private theorem eventuallyEq_ambient_of_opens {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {W₀ : Opens E} {Ξ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) W₀ F ∞}
    {Φ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, F) E F ∞}
    (hΦW₀ : Φ.source ⊆ W₀) (hΦt : Φ.target ⊆ Ξ.target)
    (hΦsymm : ∀ z ∈ Φ.target, Φ.symm z = ↑(Ξ.symm z)) {y : E} (hy : y ∈ Φ.source) :
    ⟨y, hΦW₀ hy⟩ ∈ Ξ.source ∧ (Φ ∘ (Subtype.val : W₀ → E) =ᶠ[𝓝 ⟨y, hΦW₀ hy⟩] Ξ) := by
  let p : W₀ := ⟨y, hΦW₀ hy⟩
  have hsp : Ξ.symm (Φ y) = p :=
    Subtype.ext ((hΦsymm (Φ y) (Φ.map_source hy)).symm.trans (Φ.left_inv hy))
  have hpΞ : p ∈ Ξ.source := hsp ▸ Ξ.map_target (hΦt (Φ.map_source hy))
  have hΞp_eq : Ξ p = Φ y := hsp ▸ Ξ.right_inv (hΦt (Φ.map_source hy))
  refine ⟨hpΞ, ?_⟩
  filter_upwards [Ξ.open_source.mem_nhds hpΞ,
    (Ξ.contMDiffOn.continuousOn.continuousAt (Ξ.open_source.mem_nhds hpΞ)).preimage_mem_nhds
      (Φ.open_target.mem_nhds (hΞp_eq ▸ Φ.map_source hy))] with p' hp' hΞp'
  have hval : (p' : E) = Φ.symm (Ξ p') :=
    (congrArg Subtype.val (Ξ.left_inv hp')).symm.trans (hΦsymm (Ξ p') hΞp').symm
  exact (congrArg Φ hval).trans (Φ.right_inv hΞp')

/-- **The strict contact Darboux theorem on normed spaces.** Let `η` be a smooth one-form on an
open subset `W` of a finite-dimensional real normed space `E`, which is a contact form at `y₀ ∈ W`.
Then there are `n` with `dim E = 2 n + 1` and a smooth partial diffeomorphism `Φ` from `E` to
`ℝⁿ × ℝⁿ × ℝ` with `y₀ ∈ Φ.source ⊆ W` and `Φ y₀ = 0` which pulls the standard contact form
`dz - Σᵢ pᵢ dqᵢ` back to `η` on `Φ.source`. -/
theorem IsContactFormAt.exists_partialDiffeomorph_innerProductContactForm_eq
    {η : E → E [⋀^Fin 1]→L[ℝ] ℝ} {W : Set E} {y₀ : E}
    (hc : IsContactFormAt (I := 𝓘(ℝ, E)) η y₀) (hW : IsOpen W) (hy₀W : y₀ ∈ W)
    (hη : ContDiffOn ℝ ∞ η W) :
    ∃ (n : ℕ) (Φ : PartialDiffeomorph 𝓘(ℝ, E)
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) E
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞),
      finrank ℝ E = 2 * n + 1 ∧ y₀ ∈ Φ.source ∧ Φ.source ⊆ W ∧ Φ y₀ = 0 ∧
      ∀ y ∈ Φ.source, ∀ v : E,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (Φ y) ![fderiv ℝ Φ y v] =
          η y ![v] := by
  obtain ⟨W₀, p₀, α₀, hp₀_eq, hW₀W, hα₀, hα₀_coe⟩ := exists_opens_isContactForm hc hW hy₀W hη
  obtain ⟨K, S_K, s₀, β, Ψ, hdimK, hnd₀, hp₀Ψ, hΨp₀, hΨ_pull⟩ :=
    exists_reebSliceChart_opens p₀ hα₀
  obtain ⟨n, ψ, hdim₂, hs₀ψ, hψs₀, hψ_symp⟩ := exists_symplecticSliceDarboux_opens hnd₀
  obtain ⟨Ω, hs₀Ω, hΩ₀, hΩ_pull⟩ :=
    exists_contactizationToInnerProductChart hs₀ψ hψs₀ hψ_symp
  let Ξ := Ψ.trans Ω
  have hp₀Ξ : p₀ ∈ Ξ.source := by
    rw [PartialDiffeomorph.trans_source]; exact ⟨hp₀Ψ, by simpa [hΨp₀] using hs₀Ω⟩
  have hΞp₀ : Ξ p₀ = 0 := by rw [PartialDiffeomorph.coe_trans, Function.comp_apply, hΨp₀, hΩ₀]
  obtain ⟨Φ, hy₀Φ, hΦW₀, hΦy₀, hΦt, hΦsymm⟩ := Ξ.exists_ambient_of_opens hp₀Ξ
  refine ⟨n, Φ, by omega, hp₀_eq ▸ hy₀Φ, hΦW₀.trans hW₀W, (hp₀_eq ▸ hΦy₀).trans hΞp₀,
    fun y hy v ↦ ?_⟩
  let p : W₀ := ⟨y, hΦW₀ hy⟩
  obtain ⟨hpΞ, hev_Φ⟩ := eventuallyEq_ambient_of_opens hΦW₀ hΦt hΦsymm hy
  rw [PartialDiffeomorph.coe_trans] at hev_Φ
  obtain ⟨hpΨ, hpΩ⟩ : p ∈ Ψ.source ∧ Ψ p ∈ Ω.source := by
    rwa [PartialDiffeomorph.trans_source] at hpΞ
  let v_p : TangentSpace 𝓘(ℝ, E) p :=
    (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, E)) p).symm
      ((NormedSpace.fromTangentSpace y).symm v)
  have hchain : fderiv ℝ Φ y v =
      mvfderiv (𝓘(ℝ, K).prod 𝓘(ℝ)) Ω (Ψ p) (mfderiv 𝓘(ℝ, E) (𝓘(ℝ, K).prod 𝓘(ℝ)) Ψ p v_p) := by
    have hd_sub := (contMDiff_subtype_val (I := 𝓘(ℝ, E)) (n := ∞)).mdifferentiableAt (x := p)
      (by simp)
    have h1 := congrArg (fun L ↦ L v_p) hev_Φ.mvfderiv_eq
    rw [mvfderiv_comp_apply p (Φ.mdifferentiableAt (n := ∞) (by simp) hy) hd_sub,
      mvfderiv_comp_apply p (Ω.mdifferentiableAt (n := ∞) (by simp) hpΩ)
        (Ψ.mdifferentiableAt (n := ∞) (by simp) hpΨ),
      Manifold.mfderiv_subtype_val, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, mvfderiv_eq_fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] at h1
    exact h1
  let P := EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ
  let σ : P → P [⋀^Fin 1]→L[ℝ] ℝ := (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1
  have h_eval : σ (Φ y) ![fderiv ℝ Φ y v] =
      σ (Ω (Ψ p)) ![mvfderiv (𝓘(ℝ, K).prod 𝓘(ℝ)) Ω (Ψ p)
        (mfderiv 𝓘(ℝ, E) (𝓘(ℝ, K).prod 𝓘(ℝ)) Ψ p v_p)] := by
    rw [show Φ y = Ω (Ψ p) from hev_Φ.self_of_nhds, hchain]
  exact (h_eval.trans (hΩ_pull (Ψ p) hpΩ _)).trans ((hΨ_pull p hpΨ _).trans (by
    rw [hα₀_coe]
    dsimp only [p, v_p]
    rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]))

omit [FiniteDimensional ℝ E] in
/-- **The strict contact Darboux theorem on normed spaces, in dimension `2 n + 1`.** -/
theorem IsContactFormAt.exists_partialDiffeomorph_innerProductContactForm_eq_of_finrank_eq
    {η : E → E [⋀^Fin 1]→L[ℝ] ℝ} {W : Set E} {y₀ : E}
    (hc : IsContactFormAt (I := 𝓘(ℝ, E)) η y₀) {n : ℕ} (hn : finrank ℝ E = 2 * n + 1)
    (hW : IsOpen W) (hy₀W : y₀ ∈ W) (hη : ContDiffOn ℝ ∞ η W) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E)
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) E
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞,
      y₀ ∈ Φ.source ∧ Φ.source ⊆ W ∧ Φ y₀ = 0 ∧
      ∀ y ∈ Φ.source, ∀ v : E,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (Φ y) ![fderiv ℝ Φ y v] =
          η y ![v] := by
  have : FiniteDimensional ℝ E := finite_of_finrank_pos (by omega)
  obtain ⟨m, Φ, hm, hy₀, hsub, h0, hΦ⟩ :=
    hc.exists_partialDiffeomorph_innerProductContactForm_eq hW hy₀W hη
  obtain rfl : m = n := by omega
  exact ⟨Φ, hy₀, hsub, h0, hΦ⟩

end NormedSpace

/-! ### Strict Contact Darboux charts on manifolds -/

section Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **The strict contact Darboux theorem** for a locally defined one-form. Let `α` be a one-form on
`M` which is smooth on an open set `U` and is a contact form at an interior point `x₀ ∈ U`. Then
there are `n` with `dim E = 2 n + 1` and a smooth partial diffeomorphism `chart` from `M` to
`ℝⁿ × ℝⁿ × ℝ` with `x₀ ∈ chart.source ⊆ U` and `chart x₀ = 0` which pulls the standard contact
form `dz - Σᵢ pᵢ dqᵢ` back to `α` on `chart.source`. -/
theorem IsContactFormAt.exists_strictDarbouxChart_of_isInteriorPoint {α : RoughForm I M ℝ 1}
    {U : Set M} {x₀ : M} (hc : IsContactFormAt α x₀) (hU : IsOpen U) (hx₀U : x₀ ∈ U)
    (hα : ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) U)
    (hx₀ : I.IsInteriorPoint x₀) :
    ∃ (n : ℕ) (chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞),
      finrank ℝ E = 2 * n + 1 ∧ x₀ ∈ chart.source ∧ chart.source ⊆ U ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, ∀ v : TangentSpace I x,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (chart x)
          ![mvfderiv I chart x v] = α x ![v] := by
  have : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by simp)
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := IsManifold.of_le (n := ∞) (by simp)
  set e := extChartAt I x₀
  set W : Set E := interior e.target ∩ e.symm ⁻¹' U
  have hW : IsOpen W :=
    ((continuousOn_extChartAt_symm x₀).mono interior_subset).isOpen_inter_preimage
      isOpen_interior hU
  have hy₀W : e x₀ ∈ W :=
    ⟨I.isInteriorPoint_iff.1 hx₀, by rw [mem_preimage, extChartAt_to_inv]; exact hx₀U⟩
  have hη : ContDiffOn ℝ ∞ (α.inChartAt x₀) W := α.contDiffOn_inChartAt_of_contMDiffOn hU hα x₀
  obtain ⟨n, Φ, hdim, hy₀Φ, hΦW, hΦ₀, hΦ⟩ :=
    ((isContactFormAt_inChartAt_iff hx₀).2
      hc).exists_partialDiffeomorph_innerProductContactForm_eq hW hy₀W hη
  let e₀ := extChartPartialDiffeomorph I ∞ x₀
  let chart := e₀.trans Φ
  have hcoe : ⇑chart = ⇑Φ ∘ ⇑e := by
    funext y
    simp [chart, e₀, e]
  have hx₀_src : x₀ ∈ chart.source := by
    rw [PartialDiffeomorph.trans_source, mem_inter_iff, mem_preimage,
      mem_extChartPartialDiffeomorph_source, coe_extChartPartialDiffeomorph]
    exact ⟨hx₀, hy₀Φ⟩
  refine ⟨n, chart, hdim, hx₀_src, fun x hx ↦ ?_, by rw [hcoe, Function.comp_apply, hΦ₀],
    fun x hx v ↦ ?_⟩
  · rw [PartialDiffeomorph.trans_source, extChartPartialDiffeomorph_source,
      coe_extChartPartialDiffeomorph] at hx
    have hxU := (hΦW hx.2).2
    rwa [mem_preimage, e.left_inv hx.1.1] at hxU
  · rw [PartialDiffeomorph.trans_source, extChartPartialDiffeomorph_source,
      coe_extChartPartialDiffeomorph] at hx
    have hx_chart : x ∈ (chartAt H x₀).source := by simpa only [extChartAt_source] using hx.1.1
    have hΦd : DifferentiableAt ℝ Φ (e x) :=
      mdifferentiableAt_iff_differentiableAt.1 (Φ.mdifferentiableAt (n := ∞) (by simp) hx.2)
    have hvec : (fun i ↦ mvfderiv I e x (![v] i)) = ![mvfderiv I e x v] :=
      funext fun i ↦ by fin_cases i; rfl
    rw [hcoe, mvfderiv_comp_apply_of_differentiableAt hΦd (mdifferentiableAt_extChartAt hx_chart),
      Function.comp_apply, hΦ (e x) hx.2, RoughForm.apply_eq_inChartAt_mvfderiv α hx.1.1, hvec]

omit [FiniteDimensional ℝ E] in
/-- **The strict contact Darboux theorem at an interior point, in dimension `2 n + 1`.** On a
manifold of dimension `2 n + 1`, the strict contact Darboux chart of a local contact form at an
interior point lands in `ℝⁿ × ℝⁿ × ℝ` for this `n`. -/
theorem IsContactFormAt.exists_strictDarbouxChart_of_finrank_eq_of_isInteriorPoint
    {α : RoughForm I M ℝ 1} {U : Set M} {x₀ : M} (hc : IsContactFormAt α x₀) {n : ℕ}
    (hn : finrank ℝ E = 2 * n + 1) (hU : IsOpen U) (hx₀U : x₀ ∈ U)
    (hα : ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) U)
    (hx₀ : I.IsInteriorPoint x₀) :
    ∃ chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞,
      x₀ ∈ chart.source ∧ chart.source ⊆ U ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, ∀ v : TangentSpace I x,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (chart x)
          ![mvfderiv I chart x v] = α x ![v] := by
  have : FiniteDimensional ℝ E := finite_of_finrank_pos (by omega)
  obtain ⟨m, chart, hm, hx₀', h⟩ := hc.exists_strictDarbouxChart_of_isInteriorPoint hU hx₀U hα hx₀
  obtain rfl : m = n := by omega
  exact ⟨chart, hx₀', h⟩

/-- **The strict contact Darboux theorem at an interior point.** Around any interior point `x₀` of
a manifold with a smooth contact form `α`, there are `n` with `dim E = 2 n + 1` and a smooth
partial diffeomorphism `chart` from `M` to `ℝⁿ × ℝⁿ × ℝ` with `x₀ ∈ chart.source` and
`chart x₀ = 0` which pulls the standard contact form `dz - Σᵢ pᵢ dqᵢ` back to `α` on
`chart.source`. -/
theorem SmoothForm.IsContactForm.exists_strictDarbouxChart_of_isInteriorPoint
    {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm) {x₀ : M} (hx₀ : I.IsInteriorPoint x₀) :
    ∃ (n : ℕ) (chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞),
      finrank ℝ E = 2 * n + 1 ∧ x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, ∀ v : TangentSpace I x,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (chart x)
          ![mvfderiv I chart x v] = α.1 x ![v] := by
  have : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by simp)
  obtain ⟨n, chart, hdim, hx₀', -, h0, hchart⟩ :=
    (SmoothForm.isContactForm_iff_forall_isContactFormAt.1 hα
      x₀).exists_strictDarbouxChart_of_isInteriorPoint isOpen_univ (mem_univ x₀)
      α.contMDiff.contMDiffOn hx₀
  exact ⟨n, chart, hdim, hx₀', h0, hchart⟩

omit [FiniteDimensional ℝ E] in
/-- **The strict contact Darboux theorem at an interior point, in dimension `2 n + 1`.** On a
manifold of dimension `2 n + 1` with a smooth contact form, the strict contact Darboux chart at an
interior point lands in `ℝⁿ × ℝⁿ × ℝ` for this `n`. -/
theorem SmoothForm.IsContactForm.exists_strictDarbouxChart_of_finrank_eq_of_isInteriorPoint
    {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm) {n : ℕ} (hn : finrank ℝ E = 2 * n + 1)
    {x₀ : M} (hx₀ : I.IsInteriorPoint x₀) :
    ∃ chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞,
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, ∀ v : TangentSpace I x,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (chart x)
          ![mvfderiv I chart x v] = α.1 x ![v] := by
  have : FiniteDimensional ℝ E := finite_of_finrank_pos (by omega)
  obtain ⟨m, chart, hm, hx₀', h⟩ := hα.exists_strictDarbouxChart_of_isInteriorPoint hx₀
  obtain rfl : m = n := by omega
  exact ⟨chart, hx₀', h⟩

section Boundaryless

variable [BoundarylessManifold I M]

/-- **The strict contact Darboux theorem** for a locally defined one-form on a boundaryless
manifold. -/
theorem IsContactFormAt.exists_strictDarbouxChart {α : RoughForm I M ℝ 1} {U : Set M} {x₀ : M}
    (hc : IsContactFormAt α x₀) (hU : IsOpen U) (hx₀U : x₀ ∈ U)
    (hα : ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) U) :
    ∃ (n : ℕ) (chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞),
      finrank ℝ E = 2 * n + 1 ∧ x₀ ∈ chart.source ∧ chart.source ⊆ U ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, ∀ v : TangentSpace I x,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (chart x)
          ![mvfderiv I chart x v] = α x ![v] :=
  hc.exists_strictDarbouxChart_of_isInteriorPoint hU hx₀U hα BoundarylessManifold.isInteriorPoint

omit [FiniteDimensional ℝ E] in
/-- **The strict contact Darboux theorem in dimension `2 n + 1`** for a locally defined one-form on
a boundaryless manifold. -/
theorem IsContactFormAt.exists_strictDarbouxChart_of_finrank_eq {α : RoughForm I M ℝ 1} {U : Set M}
    {x₀ : M} (hc : IsContactFormAt α x₀) {n : ℕ} (hn : finrank ℝ E = 2 * n + 1) (hU : IsOpen U)
    (hx₀U : x₀ ∈ U)
    (hα : ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) U) :
    ∃ chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞,
      x₀ ∈ chart.source ∧ chart.source ⊆ U ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, ∀ v : TangentSpace I x,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (chart x)
          ![mvfderiv I chart x v] = α x ![v] :=
  hc.exists_strictDarbouxChart_of_finrank_eq_of_isInteriorPoint hn hU hx₀U hα
    BoundarylessManifold.isInteriorPoint

/-- **The strict contact Darboux theorem.** Around every point `x₀` of a boundaryless manifold with
a smooth contact form `α`, there are `n` with `dim E = 2 n + 1` and a smooth partial diffeomorphism
`chart` from `M` to `ℝⁿ × ℝⁿ × ℝ` with `x₀ ∈ chart.source` and `chart x₀ = 0` which pulls the
standard contact form `dz - Σᵢ pᵢ dqᵢ` back to `α` on `chart.source`. -/
theorem SmoothForm.IsContactForm.exists_strictDarbouxChart {α : SmoothForm I M ℝ 1}
    (hα : α.IsContactForm) (x₀ : M) :
    ∃ (n : ℕ) (chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞),
      finrank ℝ E = 2 * n + 1 ∧ x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, ∀ v : TangentSpace I x,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (chart x)
          ![mvfderiv I chart x v] = α.1 x ![v] :=
  hα.exists_strictDarbouxChart_of_isInteriorPoint BoundarylessManifold.isInteriorPoint

omit [FiniteDimensional ℝ E] in
/-- **The strict contact Darboux theorem in dimension `2 n + 1`.** On a boundaryless manifold of
dimension `2 n + 1` with a smooth contact form, the strict contact Darboux chart lands in
`ℝⁿ × ℝⁿ × ℝ` for this `n`. -/
theorem SmoothForm.IsContactForm.exists_strictDarbouxChart_of_finrank_eq {α : SmoothForm I M ℝ 1}
    (hα : α.IsContactForm) {n : ℕ} (hn : finrank ℝ E = 2 * n + 1) (x₀ : M) :
    ∃ chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞,
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, ∀ v : TangentSpace I x,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (chart x)
          ![mvfderiv I chart x v] = α.1 x ![v] :=
  hα.exists_strictDarbouxChart_of_finrank_eq_of_isInteriorPoint hn
    BoundarylessManifold.isInteriorPoint

end Boundaryless

end Manifold

end TauCeti
