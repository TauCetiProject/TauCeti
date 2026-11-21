/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Standard
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.BumpFunction.Basic
import TauCeti.Geometry.Contact.Contactization
import TauCeti.Geometry.Contact.Darboux.Manifold
import TauCeti.Geometry.Contact.Flat
import TauCeti.Geometry.Contact.Slice
import TauCeti.Geometry.Manifold.Diffeomorph.Prod
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.DifferentialForm.Poincare
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Symplectic.Manifold.Darboux

/-!
# Darboux charts for contact forms

Let `α` be a contact form on a boundaryless manifold `M` of dimension `2 n + 1`. **Darboux's
theorem for contact forms** says that `α` itself, and not only its kernel, is standard near every
point: there is a smooth chart from `M` to `ℝⁿ × ℝⁿ × ℝ` which pulls the standard contact form
`dz - Σᵢ pᵢ dqᵢ` (`TauCeti.innerProductContactForm`) back to `α`
(`TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart`). The contact Darboux theorem of
`TauCeti.Geometry.Contact.Darboux.Manifold` pulls the standard form back to a positive multiple of
`α`, which identifies the contact structures; here the factor is `1`, so the chart is a strict
contactomorphism onto its image.

The proof straightens `α` along its Reeb flow `φ`.

1. In the chart at `x₀`, the contact hyperplane `K = ker α_{x₀}` of the model space gives a smooth
   slice `ι : K → M` through `x₀` transverse to the Reeb field, so `d(ι^* α)` is nondegenerate
   at `0` (`TauCeti.SmoothForm.IsContactForm.nondegenerate_bilinFormAt_mextDerivₗ_mpullback`).
2. Darboux's theorem for a closed two-form nondegenerate at a point
   (`TauCeti.SmoothTwoForm.exists_darbouxChart_of_nondegenerate_of_isInteriorPoint`)
   reparametrizes the slice by `ℝⁿ × ℝⁿ` so that `d(ι^* α)` is `Σᵢ dqᵢ ∧ dpᵢ` near `0`.
3. Then `ι^* α + ⟪p, dq⟫` is closed near `0`, so by the Poincaré lemma
   (`TauCeti.exists_mextDeriv_eq_nhds`) it is `dg` for a smooth function `g` with `g 0 = 0`.
4. The local Reeb flow map `(w, t) ↦ φ_t(ι w)` is a local diffeomorphism pulling `α` back to
   `dt + ι^* α` (`TauCeti.mpullback_flowOf_comp_apply_eq_contactization`), and the change of
   variables `t = z - g w` (`TauCeti.contactizationShift`) turns this into `dz - ⟪p, dq⟫`. The
   chart is constructed as a local inverse of `(q, p, z) ↦ φ_{z - g(q, p)}(ι(q, p))`.

## Main results

* `TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart`: around every point, a smooth
  chart pulling `dz - Σᵢ pᵢ dqᵢ` back to `α`.
* `TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart_of_finrank_eq`: the same chart, in
  prescribed dimension `2 n + 1`.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 2.5 (Darboux's theorem).
-/

public section

noncomputable section

open Set Filter Metric Module Bundle
open Diffeomorph (prodAssocSymmSelf)
open scoped Manifold ContDiff Topology InnerProductSpace

namespace TauCeti

/-! ### The standard primitive -/

section Standard

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The linear map `(q, p) ↦ (q, p, 0)`. -/
private def zeroSectionCLM : (V × V) →L[ℝ] V × V × ℝ :=
  (ContinuousLinearMap.fst ℝ V V).prod ((ContinuousLinearMap.snd ℝ V V).prod 0)

/-- The one-form `⟪p, dq⟫` on `V × V`, the restriction of `-(dz - ⟪p, dq⟫)` to `z = 0`. Its
contactization `dz - ⟪p, dq⟫` is the standard contact form. -/
private def stdPrimitive : SmoothForm 𝓘(ℝ, V × V) (V × V) ℝ 1 :=
  -SmoothForm.mpullback (zeroSectionCLM V) (zeroSectionCLM V).contMDiff
    (innerProductContactForm V)

private theorem stdPrimitive_apply (w : V × V) (u : TangentSpace 𝓘(ℝ, V × V) w) :
    (stdPrimitive V).val w ![u] = ⟪w.2, u.1⟫_ℝ := by
  have key : (innerProductContactForm V).val (zeroSectionCLM V w) ![zeroSectionCLM V u] =
      -⟪w.2, u.1⟫_ℝ := by
    obtain ⟨a, b⟩ := u
    exact (innerProductContactForm_apply V _ _).trans (by simp [zeroSectionCLM])
  simp only [stdPrimitive, Submodule.coe_neg, Pi.neg_apply, ContinuousAlternatingMap.neg_apply,
    SmoothForm.mpullback_apply_one, ContinuousLinearMap.mfderiv_eq]
  rw [neg_eq_iff_eq_neg]
  exact key

/-- `d⟪p, dq⟫ = -Σᵢ dqᵢ ∧ dpᵢ`. -/
private theorem eval₂_mextDerivₗ_stdPrimitive (w : V × V) (u v : TangentSpace 𝓘(ℝ, V × V) w) :
    SmoothBundleForm.eval₂ (mextDerivₗ 𝓘(ℝ, V × V) 1 (stdPrimitive V)) w u v =
      -stdSymplecticForm u v := by
  have key : stdSymplecticForm ((zeroSectionCLM V u).1, (zeroSectionCLM V u).2.1)
      ((zeroSectionCLM V v).1, (zeroSectionCLM V v).2.1) = stdSymplecticForm u v := by
    obtain ⟨a, b⟩ := u
    obtain ⟨c, d⟩ := v
    simp [zeroSectionCLM]
  rw [stdPrimitive, map_neg, SmoothForm.mextDerivₗ_mpullback, SmoothBundleForm.eval₂_neg,
    SmoothForm.eval₂_mpullback, SmoothBundleForm.eval₂_apply, mextDerivₗ_apply,
    mextDeriv_innerProductContactForm_apply, ContinuousLinearMap.mfderiv_eq]
  exact congrArg Neg.neg key

/-- The reassociation `(q, p, z) ↦ ((q, p), z)` pulls the contactization form of `⟪p, dq⟫` back to
the standard contact form `dz - ⟪p, dq⟫`. -/
private theorem mpullback_reassoc_contactization_stdPrimitive :
    mpullback 𝓘(ℝ, V × V × ℝ) (𝓘(ℝ, V × V).prod 𝓘(ℝ)) (prodAssocSymmSelf ℝ V V ℝ ∞)
      (stdPrimitive V).contactization.val = (innerProductContactForm V).val := by
  let ιL : (V × V × ℝ) →L[ℝ] V × V :=
    (ContinuousLinearMap.fst ℝ V (V × ℝ)).prod
      ((ContinuousLinearMap.fst ℝ V ℝ).comp (ContinuousLinearMap.snd ℝ V (V × ℝ)))
  let hL : (V × V × ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ V ℝ).comp (ContinuousLinearMap.snd ℝ V (V × ℝ))
  have hreassoc : ⇑(prodAssocSymmSelf ℝ V V ℝ ∞) = fun y ↦ (ιL y, hL y) :=
    funext fun y ↦ by simp [ιL, hL]
  rw [hreassoc, ← SmoothForm.coe_mpullback _ (ιL.contMDiff.prodMk hL.contMDiff),
    SmoothForm.mpullback_prodMk_contactization _ ιL.contMDiff hL.contMDiff]
  funext y
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  obtain ⟨w, rfl⟩ : ∃ w, v = ![w] := ⟨v 0, funext fun i ↦ by fin_cases i; rfl⟩
  have key : hL w - ⟪(ιL y).2, (ιL w).1⟫_ℝ = w.2.2 - ⟪y.2.1, w.1⟫_ℝ := by
    obtain ⟨a, -, c⟩ := w
    simp [ιL, hL]
  rw [Pi.sub_apply, ContinuousAlternatingMap.sub_apply, mextDeriv_ofFunction_apply,
    SmoothForm.mpullback_apply_one, ContinuousLinearMap.mfderiv_eq, stdPrimitive_apply,
    innerProductContactForm_apply, ContinuousLinearMap.mfderiv_eq]
  exact key

end Standard

/-! ### A slice transverse to the Reeb field -/

section Slice

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] {α : SmoothForm I M ℝ 1}

/-- Through every point `x₀`, a contact form has a smooth slice transverse to its Reeb field: a
smooth map `ι` from the hyperplane `K = ker α_{x₀}` of the model space, with `ι 0 = x₀`, whose
differential at `0` is injective and misses the Reeb vector. In the chart at `x₀` it is the
translate of `K` to `x₀`, cut off away from `0` so that it stays in the chart. -/
private theorem SmoothForm.IsContactForm.exists_reebSlice (hα : α.IsContactForm) (x₀ : M) :
    ∃ (K : Submodule ℝ E) (ι : K → M), ContMDiff 𝓘(ℝ, K) I ∞ ι ∧ ι 0 = x₀ ∧
      finrank ℝ K + 1 = finrank ℝ E ∧ Function.Injective (mfderiv 𝓘(ℝ, K) I ι 0) ∧
      α.reebVectorField (ι 0) ∉ (mfderiv 𝓘(ℝ, K) I ι 0).range := by
  set e := extChartAt I x₀
  set y₀ := e x₀
  -- The covector `α_{x₀}` as a continuous linear form `ℓ` on the model space.
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : E →L[ℝ] ℝ, ∀ v : E, ℓ v = α.val x₀ ![v] :=
    ⟨SmoothForm.degreeOneEquiv α x₀, SmoothForm.degreeOneEquiv_apply_apply_vec α x₀⟩
  obtain ⟨R₀, hR₀⟩ : ∃ R₀ : E, ℓ R₀ = 1 :=
    ⟨α.reebVectorField x₀, (hℓ _).trans (hα.apply_reebVectorField x₀)⟩
  -- `K = ker ℓ` is a hyperplane, since `ℓ` is onto.
  set K : Submodule ℝ E := LinearMap.ker (ℓ : E →ₗ[ℝ] ℝ)
  have hdim : finrank ℝ K + 1 = finrank ℝ E :=
    Module.Dual.finrank_ker_add_one_of_ne_zero fun h ↦
      one_ne_zero (hR₀.symm.trans (LinearMap.congr_fun h R₀))
  -- Vectors of `K` are killed by `α` at `x₀`. The base point is generalized to any `y = x₀` so
  -- that `hK` applies at `ι 0` without rewriting `ι 0` inside the type `TangentSpace I (ι 0)`.
  have hK (y : M) (hy : y = x₀) (v : E) (hv : v ∈ K) : α.val y ![v] = 0 := by
    subst hy
    rw [← hℓ]
    exact LinearMap.mem_ker.1 hv
  -- A ball about `y₀` in the chart target, and a cutoff of the identity of `K` into it.
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (isOpen_extChartAt_target x₀) y₀
    (mem_extChartAt_target x₀)
  obtain ⟨ρ, hρ, hρid, hρr⟩ := exists_contDiff_eventuallyEq_id_forall_mem_ball (E := K) hr
  have hρ0 : ρ 0 = 0 := hρid.eq_of_nhds
  have hmem (k : K) : y₀ + (ρ k : E) ∈ e.target :=
    hball (by simpa [dist_eq_norm] using hρr k)
  set ι : K → M := fun k ↦ e.symm (y₀ + K.subtypeL (ρ k))
  have hι : ContMDiff 𝓘(ℝ, K) I ∞ ι :=
    (contMDiffOn_extChartAt_symm x₀).comp_contMDiff
      (contDiff_const.add (K.subtypeL.contDiff.comp hρ)).contMDiff hmem
  have hι0 : ι 0 = x₀ := by
    simp [ι, hρ0, y₀, e]
  -- Near `0`, `ι` is the chart inverse on the translate of `K`, so `dι₀` is the inclusion.
  have hloc : ι =ᶠ[𝓝 0] fun k ↦ e.symm (y₀ + K.subtypeL k) := by
    filter_upwards [hρid] with k hk
    simp only [ι, hk, id]
  have hd (w : K) : mfderiv 𝓘(ℝ, K) I ι 0 w = (w : E) := by
    have he : HasMFDerivAt 𝓘(ℝ, E) I e.symm (y₀ + K.subtypeL 0) (ContinuousLinearMap.id ℝ E) := by
      rw [map_zero, add_zero]
      exact hasMFDerivAt_extChartAt_symm_self x₀
    have htr := (K.subtypeL.hasFDerivAt (x := 0)).const_add y₀
    exact DFunLike.congr_fun (((he.comp 0 htr.hasMFDerivAt).congr_mfderiv
      (ContinuousLinearMap.id_comp _)).congr_of_eventuallyEq hloc).mfderiv w
  refine ⟨_, ι, hι, hι0, hdim, fun w w' h ↦ Subtype.ext ((hd w).symm.trans (h.trans (hd w'))),
    fun ⟨w, hw⟩ ↦ ?_⟩
  -- The Reeb vector takes the value `1` under `α`, while vectors of `K` are in its kernel.
  have h1 : α.val (ι 0) ![mfderiv 𝓘(ℝ, K) I ι 0 w] = 1 :=
    (congrArg (fun v ↦ α.val (ι 0) ![v]) hw).trans (hα.apply_reebVectorField _)
  rw [congrArg (fun v ↦ α.val (ι 0) ![v]) (hd w), hK _ hι0 _ w.property] at h1
  exact zero_ne_one h1

end Slice

/-! ### Straightening a symplectic slice -/

section Assembly

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M] {α : SmoothForm I M ℝ 1}
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Changing the primitive.** If `dβ` is the standard symplectic form near `0`, then near `0` the
one-form `-β` differs from `⟪p, dq⟫` by the differential of a smooth function `g` with
`g 0 = 0`. -/
private theorem exists_neg_add_mextDerivₗ_ofFunction_eq_stdPrimitive
    {β : SmoothForm 𝓘(ℝ, V × V) (V × V) ℝ 1}
    (hω : ∀ᶠ w in 𝓝 (0 : V × V), ∀ u v : TangentSpace 𝓘(ℝ, V × V) w,
      SmoothBundleForm.eval₂ (mextDerivₗ 𝓘(ℝ, V × V) 1 β) w u v = stdSymplecticForm u v) :
    ∃ (g : V × V → ℝ) (hg : ContMDiff 𝓘(ℝ, V × V) 𝓘(ℝ) ∞ g), g 0 = 0 ∧
      ∀ᶠ w in 𝓝 (0 : V × V), (-β + mextDerivₗ 𝓘(ℝ, V × V) 0 (SmoothForm.ofFunction ⟨g, hg⟩)).val w =
        (stdPrimitive V).val w := by
  -- `⟪p, dq⟫ + β` is closed near `0`, so it has a primitive there.
  have hγ : ∀ᶠ w in 𝓝 (0 : V × V), mextDeriv (stdPrimitive V + β).val w = 0 := by
    filter_upwards [hω] with w hw
    refine ContinuousAlternatingMap.ext fun v ↦ ?_
    obtain ⟨a, b, rfl⟩ : ∃ a b, v = ![a, b] := ⟨v 0, v 1, funext fun i ↦ by fin_cases i <;> rfl⟩
    rw [← mextDerivₗ_apply, ← SmoothBundleForm.eval₂_apply, map_add, SmoothBundleForm.eval₂_add,
      eval₂_mextDerivₗ_stdPrimitive, hw, neg_add_cancel]
    rfl
  obtain ⟨U, hU, g₀, hg₀, hdg₀⟩ :=
    exists_mextDeriv_eq_nhds (r := ⊤) le_top (stdPrimitive V + β).isSmoothForm hγ
  -- Normalize the primitive to vanish at `0`.
  set g : V × V → ℝ := fun w ↦ g₀ w 0 - g₀ 0 0
  have hg : ContMDiff 𝓘(ℝ, V × V) 𝓘(ℝ) ∞ g := by
    rw [RoughForm.eq_ofFunction g₀, isSmoothForm_ofFunction_iff] at hg₀
    exact hg₀.sub contMDiff_const
  refine ⟨g, hg, sub_self _, eventually_of_mem hU fun w hw ↦ ?_⟩
  have hdg : (mextDerivₗ 𝓘(ℝ, V × V) 0 (SmoothForm.ofFunction ⟨g, hg⟩)).val w =
      (stdPrimitive V + β).val w := by
    rw [mextDerivₗ_apply, ← hdg₀ w hw, RoughForm.eq_ofFunction g₀]
    refine (congrArg (mextDeriv · w) (SmoothForm.coe_ofFunction _)).trans ?_
    exact mextDeriv_ofFunction_eq_of_eventuallyEq_add_const
      (Eventually.of_forall fun y ↦ sub_eq_add_neg _ _)
  rw [Submodule.coe_add, Pi.add_apply, hdg, Submodule.coe_add,
    Pi.add_apply, Submodule.coe_neg, Pi.neg_apply]
  abel

omit [FiniteDimensional ℝ V] in
/-- **The Reeb flow after a change of primitive.** Let `ι : V × V → M` be smooth and `g` a smooth
function. The map `Ξ (q, p, z) = φ_{z - g(q, p)}(ι(q, p))`, the local Reeb flow out of `ι` after
the change of variables `t = z - g(q, p)`, pulls `α` back to the standard contact form
`dz - ⟪p, dq⟫` at every point `(q, p, z)` where the flow is defined and `-ι^* α + dg` agrees with
`⟪p, dq⟫` at `(q, p)`. -/
private theorem mpullback_flowOf_comp_contactizationShift_comp_reassoc (hα : α.IsContactForm)
    {ι : V × V → M} (hι : ContMDiff 𝓘(ℝ, V × V) I ∞ ι) {g : V × V → ℝ}
    (hg : ContMDiff 𝓘(ℝ, V × V) 𝓘(ℝ) ∞ g) {y : V × V × ℝ}
    (hy : ((contactizationShift 𝓘(ℝ, V × V) hg (prodAssocSymmSelf ℝ V V ℝ ∞ y)).2,
      ι (contactizationShift 𝓘(ℝ, V × V) hg (prodAssocSymmSelf ℝ V V ℝ ∞ y)).1) ∈
        flowDomain α.reebVectorField)
    (hθ : (-SmoothForm.mpullback ι hι α +
      mextDerivₗ 𝓘(ℝ, V × V) 0 (SmoothForm.ofFunction ⟨g, hg⟩)).val
        (prodAssocSymmSelf ℝ V V ℝ ∞ y).1 =
        (stdPrimitive V).val (prodAssocSymmSelf ℝ V V ℝ ∞ y).1) :
    TauCeti.mpullback _ I ((fun p : (V × V) × ℝ ↦ flowOf α.reebVectorField p.2 (ι p.1)) ∘
        contactizationShift 𝓘(ℝ, V × V) hg ∘ prodAssocSymmSelf ℝ V V ℝ ∞) α.val y =
      (innerProductContactForm V).val y := by
  have hR := hα.contMDiff_reebVectorField
  set Sh := contactizationShift 𝓘(ℝ, V × V) hg
  set Φ : (V × V) × ℝ → M := fun p ↦ flowOf α.reebVectorField p.2 (ι p.1)
  have hΦd : MDifferentiableAt (𝓘(ℝ, V × V).prod 𝓘(ℝ)) I Φ (Sh (prodAssocSymmSelf ℝ V V ℝ ∞ y)) :=
    (contMDiffAt_flowOf_comp le_top hR contMDiffAt_snd
      (hι.contMDiffAt.comp _ contMDiffAt_fst) hy).mdifferentiableAt (by simp)
  -- The flow pulls `α` back to `dt + ι^* α`, and the shift turns this into `dz - (-ι^* α + dg)`.
  have hflow := mpullback_flowOf_comp_apply_eq_contactization hR hι hα.apply_reebVectorField
    hα.interior_mextDeriv_reebVectorField hy
  have hSh := congrArg Subtype.val (mpullback_contactizationShift_contactization hg
    (θ := -SmoothForm.mpullback ι hι α) (θ' := -SmoothForm.mpullback ι hι α +
      mextDerivₗ 𝓘(ℝ, V × V) 0 (SmoothForm.ofFunction ⟨g, hg⟩))
      (by rw [Submodule.coe_add, mextDerivₗ_apply]
          exact congrArg (_ + mextDeriv ·) (SmoothForm.coe_ofFunction _)))
  rw [SmoothForm.coe_mpullback] at hSh
  -- At `(q, p)`, the contactization forms of `-ι^* α + dg` and of `⟪p, dq⟫` agree.
  have hcon : (-SmoothForm.mpullback ι hι α +
      mextDerivₗ 𝓘(ℝ, V × V) 0 (SmoothForm.ofFunction ⟨g, hg⟩)).contactization.val
        (prodAssocSymmSelf ℝ V V ℝ ∞ y) =
        (stdPrimitive V).contactization.val (prodAssocSymmSelf ℝ V V ℝ ∞ y) := by
    refine ContinuousAlternatingMap.ext fun v ↦ ?_
    obtain ⟨w, rfl⟩ : ∃ w, v = ![w] := ⟨v 0, funext fun i ↦ by fin_cases i; rfl⟩
    rw [SmoothForm.contactization_apply, SmoothForm.contactization_apply, hθ]
  have hpt : TauCeti.mpullback _ _ (Φ ∘ Sh) α.val (prodAssocSymmSelf ℝ V V ℝ ∞ y) =
      (stdPrimitive V).contactization.val (prodAssocSymmSelf ℝ V V ℝ ∞ y) := by
    rw [mpullback_comp_at (Sh.contMDiff.mdifferentiableAt (by simp)) hΦd, ← hcon, ← hSh]
    exact ContinuousAlternatingMap.ext fun u ↦ by
      rw [TauCeti.mpullback_apply (⇑Sh), TauCeti.mpullback_apply (⇑Sh), hflow]
  -- Finally reassociate `(q, p, z) ↦ ((q, p), z)`.
  rw [← Function.comp_assoc,
    mpullback_comp_at ((prodAssocSymmSelf ℝ V V ℝ ∞).contMDiff.mdifferentiableAt (by simp))
    (hΦd.comp _ (Sh.contMDiff.mdifferentiableAt (by simp))),
    ← congrFun (mpullback_reassoc_contactization_stdPrimitive V) y]
  exact ContinuousAlternatingMap.ext fun v ↦ by
    rw [TauCeti.mpullback_apply (⇑(prodAssocSymmSelf ℝ V V ℝ ∞)),
      TauCeti.mpullback_apply (⇑(prodAssocSymmSelf ℝ V V ℝ ∞)), hpt]

/-- **Straightening a slice in Darboux coordinates.** Let `ι : V × V → M` be a smooth map such
that `d(ι^* α)` is the standard symplectic form near `0`. Then a smooth partial diffeomorphism from
`M` to `V × V × ℝ`, defined near `ι 0` and sending it to `0`, pulls the standard contact form
`dz - ⟪p, dq⟫` back to `α`. -/
private theorem SmoothForm.IsContactForm.exists_strictDarbouxChart_of_slice
    (hα : α.IsContactForm) (hn : finrank ℝ E = 2 * finrank ℝ V + 1) {ι : V × V → M}
    (hι : ContMDiff 𝓘(ℝ, V × V) I ∞ ι)
    (hω : ∀ᶠ w in 𝓝 (0 : V × V), ∀ u v : TangentSpace 𝓘(ℝ, V × V) w,
      SmoothBundleForm.eval₂ (mextDerivₗ 𝓘(ℝ, V × V) 1 (SmoothForm.mpullback ι hι α)) w u v =
        stdSymplecticForm u v) :
    ∃ chart : PartialDiffeomorph I 𝓘(ℝ, V × V × ℝ) M (V × V × ℝ) ∞, ι 0 ∈ chart.source ∧
      chart (ι 0) = 0 ∧ ∀ x ∈ chart.source,
        TauCeti.mpullback I 𝓘(ℝ, V × V × ℝ) chart (innerProductContactForm V).val x = α.val x := by
  have hR := hα.contMDiff_reebVectorField
  obtain ⟨g, hg, hg0, hgθ⟩ := exists_neg_add_mextDerivₗ_ofFunction_eq_stdPrimitive hω
  set Sh := contactizationShift 𝓘(ℝ, V × V) hg
  set Φ : (V × V) × ℝ → M := fun p ↦ flowOf α.reebVectorField p.2 (ι p.1)
  set D := {p : (V × V) × ℝ | (p.2, ι p.1) ∈ flowDomain α.reebVectorField}
  have hD : IsOpen D := isOpen_setOf_mem_flowDomain (hR.of_le (by simp)) continuous_snd
    (hι.continuous.comp continuous_fst)
  have h0D : ((0 : V × V), (0 : ℝ)) ∈ D := mem_flowDomain_zero (hR.of_le (by simp)) _
  -- The local Reeb flow out of the slice is a local diffeomorphism at the origin.
  have hnd :
      ((mextDerivₗ 𝓘(ℝ, V × V) 1 (SmoothForm.mpullback ι hι α)).bilinFormAt 0).Nondegenerate := by
    have h : (mextDerivₗ 𝓘(ℝ, V × V) 1 (SmoothForm.mpullback ι hι α)).bilinFormAt 0 =
        (stdSymplecticForm (V := V)).toBilinForm := by
      ext u v
      exact (SmoothForm.bilinFormAt_apply _ _ u v).trans (hω.self_of_nhds u v)
    rw [h]
    exact stdSymplecticForm.nondegenerate
  have hΦ : IsLocalDiffeomorphAt (𝓘(ℝ, V × V).prod 𝓘(ℝ)) I ∞ Φ ((0 : V × V), (0 : ℝ)) :=
    isLocalDiffeomorphAt_flowOf_comp_of_nondegenerate hR hι
      (by rw [finrank_prod, hn]; ring) hα.apply_reebVectorField
      hα.interior_mextDeriv_reebVectorField hnd h0D
  -- The inverse chart `Ξ (q, p, z) = φ_{z - g(q, p)}(ι(q, p))`.
  have hSh0 : (Sh ∘ prodAssocSymmSelf ℝ V V ℝ ∞) 0 = ((0 : V × V), (0 : ℝ)) := by
    have hre : prodAssocSymmSelf ℝ V V ℝ ∞ 0 = ((0 : V × V), (0 : ℝ)) := by simp
    rw [Function.comp_apply, hre, contactizationShift_apply, hg0, sub_zero]
  have hΞ : IsLocalDiffeomorphAt 𝓘(ℝ, V × V × ℝ) I ∞ (Φ ∘ Sh ∘ prodAssocSymmSelf ℝ V V ℝ ∞) 0 :=
    IsLocalDiffeomorphAt.comp
      (hf := IsLocalDiffeomorphAt.comp (hf := (prodAssocSymmSelf ℝ V V ℝ ∞).isLocalDiffeomorph 0)
        (hg := Sh.isLocalDiffeomorph _)) (hg := by rw [hSh0]; exact hΦ)
  have hΞ0 : (Φ ∘ Sh ∘ prodAssocSymmSelf ℝ V V ℝ ∞) 0 = ι 0 := by
    rw [Function.comp_apply, hSh0]
    exact flowOf_zero _ _
  -- Near `0`, `Ξ` pulls `α` back to the standard contact form.
  have hev : ∀ᶠ y in 𝓝 (0 : V × V × ℝ), (Sh ∘ prodAssocSymmSelf ℝ V V ℝ ∞) y ∈ D ∧
      (-SmoothForm.mpullback ι hι α +
        mextDerivₗ 𝓘(ℝ, V × V) 0 (SmoothForm.ofFunction ⟨g, hg⟩)).val
          (prodAssocSymmSelf ℝ V V ℝ ∞ y).1 =
          (stdPrimitive V).val (prodAssocSymmSelf ℝ V V ℝ ∞ y).1 :=
    Filter.Eventually.and (p := fun y ↦ (Sh ∘ prodAssocSymmSelf ℝ V V ℝ ∞) y ∈ D)
      ((Sh.continuous.comp (prodAssocSymmSelf ℝ V V ℝ ∞).continuous).continuousAt.preimage_mem_nhds
        (by rw [hSh0]; exact hD.mem_nhds h0D))
      (((continuous_fst.comp (prodAssocSymmSelf ℝ V V ℝ ∞).continuous).tendsto'
        (0 : V × V × ℝ) (0 : V × V) (by simp)).eventually hgθ)
  have hpull : ∀ᶠ y in 𝓝 (0 : V × V × ℝ),
      TauCeti.mpullback _ I (Φ ∘ Sh ∘ prodAssocSymmSelf ℝ V V ℝ ∞) α.val y =
        (innerProductContactForm V).val y := by
    filter_upwards [hev] with y ⟨hyD, hyθ⟩
    exact mpullback_flowOf_comp_contactizationShift_comp_reassoc hα hι hg hyD hyθ
  obtain ⟨chart, hsrc, hchart, hpb⟩ := hΞ.exists_partialDiffeomorph_mpullback_eq (by simp) hpull
  rw [hΞ0] at hsrc hchart
  exact ⟨chart, hsrc, hchart, hpb⟩

end Assembly

/-! ### The Darboux theorem for contact forms -/

section Darboux

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M] {α : SmoothForm I M ℝ 1}

omit [FiniteDimensional ℝ E] [I.Boundaryless] [T2Space M] in
/-- **Reparametrizing a slice by Darboux coordinates.** Let `ψ` be a chart of `K` in which
`d(ι^* α)` is the standard symplectic form of `V × V`, and let `ι'` agree with `ι ∘ ψ⁻¹` near a
point `w` of the target of `ψ`. Then `d(ι'^* α)` is the standard symplectic form at `w`. -/
private theorem eval₂_mextDerivₗ_mpullback_eq_stdSymplecticForm {K : Type*}
    [NormedAddCommGroup K] [NormedSpace ℝ K] {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {ι : K → M} (hι : ContMDiff 𝓘(ℝ, K) I ∞ ι)
    {ψ : PartialDiffeomorph 𝓘(ℝ, K) 𝓘(ℝ, V × V) K (V × V) ∞}
    (hψ : ∀ s ∈ ψ.source, ∀ a b : TangentSpace 𝓘(ℝ, K) s,
      SmoothBundleForm.eval₂ (mextDerivₗ 𝓘(ℝ, K) 1 (SmoothForm.mpullback ι hι α)) s a b =
        stdSymplecticForm (mvfderiv 𝓘(ℝ, K) ψ s a) (mvfderiv 𝓘(ℝ, K) ψ s b))
    {ι' : V × V → M} (hι' : ContMDiff 𝓘(ℝ, V × V) I ∞ ι') {w : V × V} (hwt : w ∈ ψ.target)
    (hloc : ι' =ᶠ[𝓝 w] ι ∘ ψ.symm) (u v : TangentSpace 𝓘(ℝ, V × V) w) :
    SmoothBundleForm.eval₂ (mextDerivₗ 𝓘(ℝ, V × V) 1 (SmoothForm.mpullback ι' hι' α)) w u v =
      stdSymplecticForm u v := by
  have hsrc : ψ.symm w ∈ ψ.source := ψ.map_target hwt
  have hψs : MDifferentiableAt _ 𝓘(ℝ, K) ψ.symm w := ψ.symm.mdifferentiableAt (by simp) hwt
  -- `dψ ∘ dψ⁻¹` is the identity at `w`.
  have hinv (u : TangentSpace 𝓘(ℝ, V × V) w) :
      mvfderiv 𝓘(ℝ, K) ψ (ψ.symm w) (mfderiv _ 𝓘(ℝ, K) ψ.symm w u) = u := by
    rw [mvfderiv_apply_eq_mfderiv_apply]
    exact ψ.mfderiv_apply_mfderiv_symm_apply (by simp) hwt u
  calc SmoothBundleForm.eval₂ (mextDerivₗ _ 1 (SmoothForm.mpullback ι' hι' α)) w u v
      = TauCeti.mpullback _ I ι' (mextDeriv α.val) w ![u, v] := by
        rw [SmoothForm.mextDerivₗ_mpullback, SmoothBundleForm.eval₂_apply,
          SmoothForm.coe_mpullback, mextDerivₗ_apply]
    _ = TauCeti.mpullback _ 𝓘(ℝ, K) ψ.symm (TauCeti.mpullback _ I ι (mextDeriv α.val)) w
          ![u, v] := by
        rw [hloc.mpullback_eq, mpullback_comp_at hψs (hι.mdifferentiableAt (by simp))]
    _ = SmoothBundleForm.eval₂ (mextDerivₗ 𝓘(ℝ, K) 1 (SmoothForm.mpullback ι hι α)) (ψ.symm w)
          (mfderiv _ 𝓘(ℝ, K) ψ.symm w u) (mfderiv _ 𝓘(ℝ, K) ψ.symm w v) := by
        rw [mpullback_apply_pair, SmoothForm.mextDerivₗ_mpullback, SmoothBundleForm.eval₂_apply,
          SmoothForm.coe_mpullback, mextDerivₗ_apply]
    _ = stdSymplecticForm u v := by
        rw [hψ _ hsrc, hinv, hinv]

/-- **The Darboux theorem for contact forms, in dimension `2 n + 1`.** Let `α` be a contact form
on a boundaryless manifold of dimension `2 n + 1`. Around every point `x₀` there is a smooth
partial diffeomorphism `chart` from `M` to `ℝⁿ × ℝⁿ × ℝ` with `x₀ ∈ chart.source` and
`chart x₀ = 0` which pulls the standard contact form `dz - Σᵢ pᵢ dqᵢ` back to `α` itself on
`chart.source`. -/
theorem SmoothForm.IsContactForm.exists_strictDarbouxChart_of_finrank_eq
    (hα : α.IsContactForm) {n : ℕ} (hn : finrank ℝ E = 2 * n + 1) (x₀ : M) :
    ∃ chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞,
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧ ∀ x ∈ chart.source, ∀ v : TangentSpace I x,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).val (chart x)
          ![mvfderiv I chart x v] = α.val x ![v] := by
  -- A slice transverse to the Reeb field, on which `dα` restricts to a symplectic form at `0`.
  obtain ⟨K, ι, hι, hι0, hdimK, hinj, hR⟩ := hα.exists_reebSlice x₀
  have hσ0 : ((mextDerivₗ 𝓘(ℝ, K) 1 (SmoothForm.mpullback ι hι α)).bilinFormAt 0).Nondegenerate :=
    hα.nondegenerate_bilinFormAt_mextDerivₗ_mpullback hι hdimK hinj hR
  have hK : finrank ℝ K = 2 * n := by omega
  -- Darboux coordinates `ψ` for `σ` on the slice, and a cutoff `ρ` into their target.
  obtain ⟨ψ, hψ0, hψψ0, hψ⟩ :=
    SmoothTwoForm.exists_standardDarbouxChart_of_nondegenerate_of_finrank_eq_of_isInteriorPoint
      (SmoothForm.isClosed_mextDerivₗ _) hK hσ0 BoundarylessManifold.isInteriorPoint
  have h0t : (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ∈ ψ.target := by
    rw [← hψψ0]
    exact ψ.map_source hψ0
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 ψ.open_target 0 h0t
  obtain ⟨ρ, hρ, hρid, hρr⟩ :=
    exists_contDiff_eventuallyEq_id_forall_mem_ball
      (E := EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) hr
  set ι' := ι ∘ ψ.symm ∘ ρ
  have hι' : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) I ∞ ι' :=
    (hι.comp_contMDiffOn ψ.contMDiffOn_invFun).comp_contMDiff hρ.contMDiff fun w ↦ hball (hρr w)
  have hι'0 : ι' 0 = x₀ := by
    have hψs : ψ.symm 0 = 0 := by
      rw [← hψψ0]
      exact ψ.left_inv hψ0
    simp only [ι', Function.comp_apply, hρid.eq_of_nhds, id, hψs, hι0]
  -- In the coordinates `ψ`, `d(ι'^* α)` is the standard symplectic form near `0`.
  have hω : ∀ᶠ w in 𝓝 (0 : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
      ∀ u v, SmoothBundleForm.eval₂ (mextDerivₗ _ 1 (SmoothForm.mpullback ι' hι' α)) w u v =
        stdSymplecticForm u v := by
    filter_upwards [hρid.eventuallyEq_nhds, ψ.open_target.mem_nhds h0t] with w hw hwt
    exact eval₂_mextDerivₗ_mpullback_eq_stdSymplecticForm hι hψ hι' hwt
      (hw.fun_comp (ι ∘ ψ.symm))
  -- Straighten the slice `ι'` along the Reeb flow.
  obtain ⟨chart, hsrc, hchart, hpb⟩ :=
    hα.exists_strictDarbouxChart_of_slice (by rw [finrank_euclideanSpace_fin]; exact hn) hι' hω
  rw [hι'0] at hsrc hchart
  refine ⟨chart, hsrc, hchart, fun x hx v ↦ ?_⟩
  rw [mvfderiv_apply_eq_mfderiv_apply, ← hpb x hx, TauCeti.mpullback_apply]
  congr 1
  funext i
  fin_cases i
  rfl

/-- **The Darboux theorem for contact forms.** Let `α` be a contact form on a boundaryless
manifold. Around every point `x₀` there are `n` with `dim M = 2 n + 1` and a smooth partial
diffeomorphism `chart` from `M` to `ℝⁿ × ℝⁿ × ℝ` with `x₀ ∈ chart.source` and `chart x₀ = 0` which
pulls the standard contact form `dz - Σᵢ pᵢ dqᵢ` back to `α` itself on `chart.source`. -/
theorem SmoothForm.IsContactForm.exists_strictDarbouxChart (hα : α.IsContactForm) (x₀ : M) :
    ∃ (n : ℕ) (chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞),
      finrank ℝ E = 2 * n + 1 ∧ x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, ∀ v : TangentSpace I x,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).val (chart x)
          ![mvfderiv I chart x v] = α.val x ![v] := by
  obtain ⟨n, -, -, hn, -⟩ := hα.exists_darbouxChart x₀
  obtain ⟨chart, h⟩ := hα.exists_strictDarbouxChart_of_finrank_eq hn x₀
  exact ⟨n, chart, hn, h⟩

end Darboux

end TauCeti
