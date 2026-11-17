/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Contactization
public import TauCeti.Geometry.Contact.Contactomorphism
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Geometry.Contact.Slice
import TauCeti.Geometry.Contact.Symplectization.Linear
import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.DifferentialForm.LocalPrimitive
import TauCeti.Geometry.Manifold.DifferentialForm.Opens
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Constructions
import TauCeti.Geometry.Symplectic.Manifold.Darboux
import TauCeti.Geometry.Symplectic.Manifold.Opens
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# The strict contact Darboux theorem

Let `M` be a smooth manifold with finite-dimensional real model space `E`. While the contact
Darboux theorem of `TauCeti.Geometry.Contact.Darboux.Manifold` straightens a contact form up to a
positive conformal factor (`chart^* α_std = g α`), **the strict contact Darboux theorem** eliminates
the conformal factor altogether: around every interior point `x₀` at which a locally smooth one-form
`α` is a contact form (`TauCeti.IsContactFormAt`), there are `n` with `dim E = 2 n + 1` and a
centered smooth partial diffeomorphism `chart` from `M` to `ℝⁿ × ℝⁿ × ℝ` pulling the standard
contact form `α_std = dz - Σᵢ pᵢ dqᵢ` (`TauCeti.innerProductContactForm`) back to `α` itself:

`α_std (chart x) (d chart_x v) = α x v`

for every `x ∈ chart.source` and `v : T_x M`
(`TauCeti.IsContactFormAt.exists_strictDarbouxChart_of_isInteriorPoint`).

When `α` is a global smooth contact form (`TauCeti.SmoothForm.IsContactForm`), the chart restricts
to a strict contactomorphism (`Diffeomorph.IsStrictContactomorphism`) between its open source in `M`
and its open target in `ℝⁿ × ℝⁿ × ℝ`
(`PartialDiffeomorph.isStrictContactomorphism_toDiffeomorphSourceTarget_iff`,
`TauCeti.SmoothForm.IsContactForm.exists_isStrictContactomorphism_opens_of_isInteriorPoint`), and
its differential simultaneously straightens the Reeb vector field `R_α` to `∂_z = (0, 0, 1)` on the
chart domain
(`TauCeti.SmoothForm.IsContactForm.mvfderiv_reebVectorField_of_innerProductContactForm`).
In dimension `3`, composing with the coordinate swap `(q, p, z) ↦ (p₀, q₀, z)` yields charts into
`ℝ × ℝ × ℝ` pulling `TauCeti.standardContactForm` (`dz - x dy`) back to `α` and straightening `R_α`
to `TauCeti.standardReebField`
(`TauCeti.IsContactFormAt.exists_strictStandardDarbouxChart_of_isInteriorPoint`,
`TauCeti.SmoothForm.IsContactForm.exists_strictStandardDarbouxChart_of_isInteriorPoint`).

The proof proceeds in three stages, without assuming `M` is Hausdorff:

1. **Contactizations**
   (`TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart_contactization_of_isInteriorPoint`):
   when `θ` is a one-form on `S` whose contactization `dz - θ` on `S × ℝ` is a contact form, `-dθ`
   is symplectic (`TauCeti.SmoothForm.isContactForm_contactization_iff`). A symplectic Darboux chart
   `ψ` on `S` (`TauCeti.IsSymplectic.exists_standardDarbouxChart_of_isInteriorPoint`) pulls the
   standard symplectic form on `ℝⁿ × ℝⁿ` back to `-dθ`. On the open target of `ψ` in `ℝⁿ × ℝⁿ`
   (which is Hausdorff automatically), the difference between `(ψ⁻¹)^* θ` and the standard primitive
   `Σᵢ pᵢ dqᵢ` is closed, so the Poincaré lemma (`TauCeti.exists_contMDiff_isPrimitiveOn`) produces
   a smooth local primitive `g` near `0`. Normalizing `g(0) = z₀`, the shifted coordinate map
   `(s, z) ↦ ((ψ s).1, (ψ s).2, z - g(ψ s))` pulls `dz - Σᵢ pᵢ dqᵢ` back to `dz - θ`.
2. **Normed spaces** (`TauCeti.exists_partialDiffeomorph_strictDarboux_modelSpace`): given `α`
   smooth on an open set `W ⊆ V` and contact at `x₀ ∈ W`, openness of the contact condition
   (`TauCeti.IsContactFormAt.eventually_modelSpace`) and a smooth bump cutoff restrict `α` to a
   contact form `α_Ω` on an open ball `Ω` around `x₀`. The affine hyperplane slice
   `S_Ω = {k ∈ ker α_{x₀} | x₀ + k ∈ Ω}` is transverse to the Reeb vector field `R_{α_Ω}` at `0`,
   so the local Reeb flow `(s, t) ↦ φ_t(x₀ + s)` is a local diffeomorphism at `(0, 0)`
   (`TauCeti.SmoothForm.IsContactForm.isLocalDiffeomorphAt_flowOf_reebVectorField_comp`) pulling
   `α_Ω` back to the contactization form `dt + ι^* α_Ω`
   (`TauCeti.mpullback_flowOf_comp_apply_eq_contactization`). Shrinking `S_Ω` to an open
   neighbourhood where `d(ι^* α_Ω)` stays nondegenerate and composing a local inverse of the Reeb
   flow with the contactization chart gives a strict Darboux chart on `V`.
3. **Manifolds**: reading `α` in `extChartAt I x₀` reduces the manifold theorem at an interior point
   `x₀` directly to the normed-space theorem on `E`.

## Main results

* `PartialDiffeomorph.isStrictContactomorphism_toDiffeomorphSourceTarget_iff`: a smooth partial
  diffeomorphism pulls `β` back to `α` on its source iff its source-target diffeomorphism is a
  strict contactomorphism between the restricted forms.
* `TauCeti.SmoothForm.IsContactForm.mfderiv_reebVectorField_of_partialDiffeomorph`,
  `TauCeti.SmoothForm.IsContactForm.mvfderiv_reebVectorField_of_innerProductContactForm`,
  `TauCeti.SmoothForm.IsContactForm.mvfderiv_reebVectorField_of_standardContactForm`: Reeb vector
  field straightening along strict partial diffeomorphisms.
* `TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart_contactization_of_isInteriorPoint`,
  `TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart_contactization`: strict Darboux charts
  on contactizations `S × ℝ`.
* `TauCeti.exists_partialDiffeomorph_strictDarboux_modelSpace`: strict contact Darboux theorem on
  finite-dimensional real normed spaces.
* `TauCeti.IsContactFormAt.exists_strictDarbouxChart_of_isInteriorPoint`,
  `TauCeti.IsContactFormAt.exists_strictDarbouxChart_of_finrank_eq_of_isInteriorPoint`,
  `TauCeti.IsContactFormAt.exists_strictDarbouxChart`,
  `TauCeti.IsContactFormAt.exists_strictDarbouxChart_of_finrank_eq`: strict contact Darboux charts
  for locally defined one-forms on manifolds.
* `TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart_of_isInteriorPoint`,
  `TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart_of_finrank_eq_of_isInteriorPoint`,
  `TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart`,
  `TauCeti.SmoothForm.IsContactForm.exists_strictDarbouxChart_of_finrank_eq`: strict contact Darboux
  charts for smooth contact forms, together with open-subset strict contactomorphism versions
  `exists_isStrictContactomorphism_opens*`.
* `TauCeti.IsContactFormAt.exists_strictStandardDarbouxChart_of_isInteriorPoint`,
  `TauCeti.IsContactFormAt.exists_strictStandardDarbouxChart`,
  `TauCeti.SmoothForm.IsContactForm.exists_strictStandardDarbouxChart_of_isInteriorPoint`,
  `TauCeti.SmoothForm.IsContactForm.exists_strictStandardDarbouxChart`: three-dimensional strict
  Darboux charts for `TauCeti.standardContactForm` (`dz - x dy`).

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Theorem 2.5.1 and Section 2.5.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Theorem 3.5.14.
-/

public section

noncomputable section

open Set Filter Bundle Module TopologicalSpace
open scoped ContDiff Manifold Topology InnerProductSpace

/-! ### Strict contactomorphisms and Reeb vector fields on partial diffeomorphisms -/

section PartialDiffeomorphStrict

variable {E H M F H' N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
  {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- A smooth partial diffeomorphism `chart` restricts to a strict contactomorphism between its open
source and open target if and only if it pulls `β` back to `α` pointwise on `chart.source`. -/
theorem PartialDiffeomorph.isStrictContactomorphism_toDiffeomorphSourceTarget_iff
    (chart : PartialDiffeomorph I J M N ∞) (α : TauCeti.SmoothForm I M ℝ 1)
    (β : TauCeti.SmoothForm J N ℝ 1) :
    chart.toDiffeomorphSourceTarget.IsStrictContactomorphism
        (TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val α)
        (TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val β) ↔
      ∀ x ∈ chart.source, ∀ v : TangentSpace I x,
        β.1 (chart x) ![mfderiv I J chart x v] = α.1 x ![v] := by
  set U_M : Opens M := ⟨chart.source, chart.open_source⟩
  set U_N : Opens N := ⟨chart.target, chart.open_target⟩
  set e := chart.toDiffeomorphSourceTarget
  have : IsManifold J 1 N := .of_le (n := ∞) (by simp)
  have hcomp : (Subtype.val : U_N → N) ∘ e = chart ∘ (Subtype.val : U_M → M) :=
    funext fun p ↦ chart.toDiffeomorphSourceTarget_apply_coe p
  have hpoint (p : U_M) (u : TangentSpace I p) :
      (TauCeti.SmoothForm.mpullback e e.contMDiff
        (TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val β)).1 p ![u] =
        β.1 (chart p.1)
          ![mfderiv I J chart p.1 (TauCeti.Manifold.tangentSpaceOpenEquiv p u)] := by
    rw [TauCeti.SmoothForm.mpullback_mpullback, TauCeti.SmoothForm.coe_mpullback]
    have hpull := congrArg (fun g : U_M → N ↦ TauCeti.mpullback I J g β.1 p ![u]) hcomp
    rw [hpull, TauCeti.mpullback_apply]
    have hd : MDifferentiableAt I J chart p.1 :=
      ((chart.contMDiffOn p.1 p.2).contMDiffAt
        (chart.open_source.mem_nhds p.2)).mdifferentiableAt (by simp)
    rw [mfderiv_comp p hd (contMDiff_subtype_val.mdifferentiableAt one_ne_zero),
      TauCeti.Manifold.mfderiv_subtype_val]
    congr 1
    ext i
    fin_cases i
    rfl
  have hsub (p : U_M) (u : TangentSpace I p) :
      (TauCeti.SmoothForm.mpullback Subtype.val contMDiff_subtype_val α).1 p ![u] =
        α.1 p.1 ![TauCeti.Manifold.tangentSpaceOpenEquiv p u] := by
    rw [TauCeti.SmoothForm.coe_mpullback, TauCeti.mpullback_apply,
      TauCeti.Manifold.mfderiv_subtype_val]
    congr 1
    ext i
    fin_cases i
    rfl
  rw [Diffeomorph.isStrictContactomorphism_def, Subtype.ext_iff, funext_iff]
  refine ⟨fun h x hx v ↦ ?_, fun h p ↦ ContinuousAlternatingMap.ext fun u ↦ ?_⟩
  · set p : U_M := ⟨x, hx⟩
    have hu := congrArg (· ![(TauCeti.Manifold.tangentSpaceOpenEquiv p).symm v]) (h p)
    rw [hpoint, hsub, ContinuousLinearEquiv.apply_symm_apply] at hu
    exact hu
  · obtain ⟨w, rfl⟩ : ∃ w, u = ![w] := ⟨u 0, funext fun i ↦ by fin_cases i; rfl⟩
    rw [hpoint p w, hsub p w]
    exact h p.1 p.2 (TauCeti.Manifold.tangentSpaceOpenEquiv p w)

namespace TauCeti

/-- If a smooth partial diffeomorphism `chart` pulls a contact form `β` back to a contact form `α`
on `chart.source`, then its differential carries the Reeb vector field of `α` to that of `β` at
every point of `chart.source`. -/
theorem SmoothForm.IsContactForm.mfderiv_reebVectorField_of_partialDiffeomorph
    [FiniteDimensional ℝ E] {α : SmoothForm I M ℝ 1} {β : SmoothForm J N ℝ 1}
    (hα : α.IsContactForm) (hβ : β.IsContactForm) (chart : PartialDiffeomorph I J M N ∞)
    (hchart : ∀ x ∈ chart.source, ∀ v : TangentSpace I x,
      β.1 (chart x) ![mfderiv I J chart x v] = α.1 x ![v])
    {x : M} (hx : x ∈ chart.source) :
    mfderiv I J chart x (α.reebVectorField x) = β.reebVectorField (chart x) := by
  have : IsManifold I 2 M := .of_le (n := ∞) (by simp)
  have : IsManifold J 2 N := .of_le (n := ∞) (by simp)
  have : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  have : FiniteDimensional ℝ (TangentSpace J (chart x)) :=
    ((chart.isLocalDiffeomorphAt I J ∞ hx).mfderivToContinuousLinearEquiv
      (by simp)).toLinearEquiv.finiteDimensional
  have : FiniteDimensional ℝ F :=
    inferInstanceAs (FiniteDimensional ℝ (TangentSpace J (chart x)))
  set U_M : Opens M := ⟨chart.source, chart.open_source⟩
  set U_N : Opens N := ⟨chart.target, chart.open_target⟩
  set p : U_M := ⟨x, hx⟩
  have hbij_M (q : U_M) : Function.Bijective (mfderiv I I (Subtype.val : U_M → M) q) := by
    rw [Manifold.mfderiv_subtype_val]
    exact (Manifold.tangentSpaceOpenEquiv (I := I) q).bijective
  have hbij_N (q : U_N) : Function.Bijective (mfderiv J J (Subtype.val : U_N → N) q) := by
    rw [Manifold.mfderiv_subtype_val]
    exact (Manifold.tangentSpaceOpenEquiv (I := J) q).bijective
  have he := (chart.isStrictContactomorphism_toDiffeomorphSourceTarget_iff α β).2 hchart
  have hreeb := he.mfderiv_reebVectorField
    (hβ.mpullback Subtype.val contMDiff_subtype_val hbij_N) p
  have hcomp : (Subtype.val : U_N → N) ∘ chart.toDiffeomorphSourceTarget =
      chart ∘ (Subtype.val : U_M → M) :=
    funext fun q ↦ chart.toDiffeomorphSourceTarget_apply_coe q
  have hd_chart : MDifferentiableAt I J chart x :=
    ((chart.contMDiffOn x hx).contMDiffAt (chart.open_source.mem_nhds hx)).mdifferentiableAt
      (by simp)
  set rα := (SmoothForm.mpullback Subtype.val contMDiff_subtype_val α).reebVectorField p
  have h1 := hβ.mfderiv_reebVectorField_mpullback Subtype.val contMDiff_subtype_val hbij_N
    (chart.toDiffeomorphSourceTarget p)
  have h2 : (β.reebVectorField (chart.toDiffeomorphSourceTarget p) : F) =
      β.reebVectorField (chart x) :=
    congrArg (fun y : N ↦ (β.reebVectorField y : F)) (chart.toDiffeomorphSourceTarget_apply_coe p)
  have h3 : mfderiv J J (Subtype.val : U_N → N) (chart.toDiffeomorphSourceTarget p)
      (mfderiv I J chart.toDiffeomorphSourceTarget p rα) =
      mfderiv I J ((Subtype.val : U_N → N) ∘ chart.toDiffeomorphSourceTarget) p rα := by
    rw [mfderiv_comp p (contMDiff_subtype_val.mdifferentiableAt one_ne_zero)
      (chart.toDiffeomorphSourceTarget.contMDiff.mdifferentiableAt (by simp)),
      ContinuousLinearMap.comp_apply]
  have h4 : (mfderiv I J ((Subtype.val : U_N → N) ∘ chart.toDiffeomorphSourceTarget) p rα : F) =
      mfderiv I J (chart ∘ (Subtype.val : U_M → M)) p rα :=
    congrArg (fun g : U_M → N ↦ (mfderiv I J g p rα : F)) hcomp
  have h5 : mfderiv I J (chart ∘ (Subtype.val : U_M → M)) p rα =
      mfderiv I J chart x (α.reebVectorField x) := by
    rw [mfderiv_comp p hd_chart (contMDiff_subtype_val.mdifferentiableAt one_ne_zero),
      ContinuousLinearMap.comp_apply,
      hα.mfderiv_reebVectorField_mpullback Subtype.val contMDiff_subtype_val hbij_M p]
  exact h5.symm.trans (h4.symm.trans (h3.symm.trans
    ((congrArg (mfderiv J J (Subtype.val : U_N → N) (chart.toDiffeomorphSourceTarget p))
      hreeb).trans (h1.trans h2))))

/-- Any smooth partial diffeomorphism into `V₀ × V₀ × ℝ` pulling `innerProductContactForm V₀` back
to a contact form `α` straightens the Reeb vector field of `α` to `(0, 0, 1)`. -/
theorem SmoothForm.IsContactForm.mvfderiv_reebVectorField_of_innerProductContactForm
    [FiniteDimensional ℝ E] {V₀ : Type*} [NormedAddCommGroup V₀] [InnerProductSpace ℝ V₀]
    [FiniteDimensional ℝ V₀] {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm)
    (chart : PartialDiffeomorph I 𝓘(ℝ, V₀ × V₀ × ℝ) M (V₀ × V₀ × ℝ) ∞)
    (hchart : ∀ x ∈ chart.source, ∀ v : TangentSpace I x,
      (innerProductContactForm V₀).1 (chart x) ![mvfderiv I chart x v] = α.1 x ![v])
    {x : M} (hx : x ∈ chart.source) :
    mvfderiv I chart x (α.reebVectorField x) = (0, 0, 1) := by
  have h := hα.mfderiv_reebVectorField_of_partialDiffeomorph
    (isContactForm_innerProductContactForm V₀) chart
    (fun y hy v ↦ by rw [← mvfderiv_apply_eq_mfderiv_apply]; exact hchart y hy v) hx
  rw [mvfderiv_apply_eq_mfderiv_apply, h]
  exact reebVectorField_innerProductContactForm V₀ (chart x)

/-- Any smooth partial diffeomorphism into `ℝ × ℝ × ℝ` pulling `standardContactForm` (`dz - x dy`)
back to a contact form `α` carries the Reeb vector field of `α` to `standardReebField` (`∂_z`). -/
theorem SmoothForm.IsContactForm.mvfderiv_reebVectorField_of_standardContactForm
    [FiniteDimensional ℝ E] {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm)
    (chart : PartialDiffeomorph I 𝓘(ℝ, ℝ × ℝ × ℝ) M (ℝ × ℝ × ℝ) ∞)
    (hchart : ∀ x ∈ chart.source, ∀ v : TangentSpace I x,
      standardContactForm.1 (chart x) ![mvfderiv I chart x v] = α.1 x ![v])
    {x : M} (hx : x ∈ chart.source) :
    mvfderiv I chart x (α.reebVectorField x) = standardReebField (chart x) := by
  have h := hα.mfderiv_reebVectorField_of_partialDiffeomorph isContactForm_standardContactForm
    chart (fun y hy v ↦ by rw [← mvfderiv_apply_eq_mfderiv_apply]; exact hchart y hy v) hx
  rw [mvfderiv_apply_eq_mfderiv_apply, h]
  exact reebVectorField_standardContactForm (chart x)

end TauCeti

end PartialDiffeomorphStrict

namespace TauCeti

/-! ### Strict Darboux charts on contactizations -/

section Contactization

variable {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  [IsManifold J ∞ S]

omit [IsManifold J ∞ S] in
/-- Combining a partial diffeomorphism `ψ` from `S` into `V₀ × V₀` with a smooth function `h` on an
open subset `W₀ ⊆ ψ.target` produces the shifted partial diffeomorphism
`(s, z) ↦ ((ψ s).1, (ψ s).2, z - h (ψ s))` from `S × ℝ` into `V₀ × V₀ × ℝ`. -/
private def contactizationShiftedChart {V₀ : Type*} [NormedAddCommGroup V₀] [NormedSpace ℝ V₀]
    (ψ : PartialDiffeomorph J 𝓘(ℝ, V₀ × V₀) S (V₀ × V₀) ∞) {W₀ : Set (V₀ × V₀)}
    (hW₀ : IsOpen W₀) (hW₀_sub : W₀ ⊆ ψ.target) {h : V₀ × V₀ → ℝ}
    (hh : ContDiffOn ℝ ∞ h W₀) :
    PartialDiffeomorph (J.prod 𝓘(ℝ)) 𝓘(ℝ, V₀ × V₀ × ℝ) (S × ℝ) (V₀ × V₀ × ℝ) ∞ where
  toPartialEquiv :=
    { toFun := fun p ↦ ((ψ p.1).1, (ψ p.1).2, p.2 - h (ψ p.1))
      invFun := fun q ↦ (ψ.symm (q.1, q.2.1), q.2.2 + h (q.1, q.2.1))
      source := (ψ.source ∩ ψ ⁻¹' W₀) ×ˢ univ
      target := {q : V₀ × V₀ × ℝ | (q.1, q.2.1) ∈ W₀}
      map_source' := fun _ hp ↦ hp.1.2
      map_target' := fun q hq ↦ by
        have hψq : ψ (ψ.symm (q.1, q.2.1)) = (q.1, q.2.1) := ψ.right_inv (hW₀_sub hq)
        exact ⟨⟨ψ.map_target (hW₀_sub hq), by rw [mem_preimage, hψq]; exact hq⟩, mem_univ _⟩
      left_inv' := fun _ hp ↦ Prod.ext (ψ.left_inv hp.1.1) (sub_add_cancel _ _)
      right_inv' := fun q hq ↦ by
        have hψq : ψ (ψ.symm (q.1, q.2.1)) = (q.1, q.2.1) := ψ.right_inv (hW₀_sub hq)
        dsimp only
        rw [hψq]
        exact Prod.ext rfl (Prod.ext rfl (add_sub_cancel_right _ _)) }
  open_source := (ψ.toOpenPartialHomeomorph.isOpen_inter_preimage hW₀).prod isOpen_univ
  open_target := hW₀.preimage (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  contMDiffOn_toFun := by
    have hψ₁ : ContMDiffOn (J.prod 𝓘(ℝ)) 𝓘(ℝ, V₀ × V₀) ∞ (fun p : S × ℝ ↦ ψ p.1)
        ((ψ.source ∩ ψ ⁻¹' W₀) ×ˢ univ) :=
      (ψ.contMDiffOn.mono inter_subset_left).comp contMDiff_fst.contMDiffOn fun _ hp ↦ hp.1
    obtain ⟨hψ_fst, hψ_snd⟩ := (contMDiffOn_prod_module_iff _).1 hψ₁
    have hhψ : ContMDiffOn (J.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ (fun p : S × ℝ ↦ h (ψ p.1))
        ((ψ.source ∩ ψ ⁻¹' W₀) ×ˢ univ) :=
      (contMDiffOn_iff_contDiffOn.2 hh).comp hψ₁ fun _ hp ↦ hp.1.2
    exact (contMDiffOn_prod_module_iff _).2
      ⟨hψ_fst, (contMDiffOn_prod_module_iff _).2 ⟨hψ_snd, contMDiff_snd.contMDiffOn.sub hhψ⟩⟩
  contMDiffOn_invFun := by
    set T : Set (V₀ × V₀ × ℝ) := {q | (q.1, q.2.1) ∈ W₀}
    have hpr : ContMDiffOn 𝓘(ℝ, V₀ × V₀ × ℝ) 𝓘(ℝ, V₀ × V₀) ∞
        (fun q : V₀ × V₀ × ℝ ↦ (q.1, q.2.1)) T :=
      contMDiffOn_iff_contDiffOn.2 (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)).contDiffOn
    have hψs : ContMDiffOn 𝓘(ℝ, V₀ × V₀ × ℝ) J ∞
        (fun q : V₀ × V₀ × ℝ ↦ ψ.symm (q.1, q.2.1)) T :=
      ψ.symm.contMDiffOn.comp hpr fun _ hq ↦ hW₀_sub hq
    have hhq : ContMDiffOn 𝓘(ℝ, V₀ × V₀ × ℝ) 𝓘(ℝ) ∞
        (fun q : V₀ × V₀ × ℝ ↦ h (q.1, q.2.1)) T :=
      (contMDiffOn_iff_contDiffOn.2 hh).comp hpr fun _ hq ↦ hq
    exact hψs.prodMk
      ((contMDiffOn_iff_contDiffOn.2 (contDiff_snd.comp contDiff_snd).contDiffOn).add hhq)

/-- Differential of `contactizationShiftedChart` at a point of its source. -/
private theorem mvfderiv_contactizationShiftedChart {V₀ : Type*} [NormedAddCommGroup V₀]
    [NormedSpace ℝ V₀] (ψ : PartialDiffeomorph J 𝓘(ℝ, V₀ × V₀) S (V₀ × V₀) ∞)
    {W₀ : Set (V₀ × V₀)} (hW₀ : IsOpen W₀) (hW₀_sub : W₀ ⊆ ψ.target) {h : V₀ × V₀ → ℝ}
    (hh : ContDiffOn ℝ ∞ h W₀) {p : S × ℝ}
    (hp : p ∈ (contactizationShiftedChart ψ hW₀ hW₀_sub hh).source)
    (v : TangentSpace (J.prod 𝓘(ℝ)) p) :
    mvfderiv (J.prod 𝓘(ℝ)) (contactizationShiftedChart ψ hW₀ hW₀_sub hh) p v =
      ((mvfderiv J ψ p.1 (Manifold.tangentSpaceProdEquiv p v).1).1,
        (mvfderiv J ψ p.1 (Manifold.tangentSpaceProdEquiv p v).1).2,
        NormedSpace.fromTangentSpace p.2 (Manifold.tangentSpaceProdEquiv p v).2 -
          fderiv ℝ h (ψ p.1) (mvfderiv J ψ p.1 (Manifold.tangentSpaceProdEquiv p v).1)) := by
  have : IsManifold J 1 S := .of_le (n := ∞) (by simp)
  let chart := contactizationShiftedChart ψ hW₀ hW₀_sub hh
  have hdchart : MDifferentiableAt (J.prod 𝓘(ℝ)) 𝓘(ℝ, V₀ × V₀ × ℝ) chart p :=
    ((chart.contMDiffOn p hp).contMDiffAt (chart.open_source.mem_nhds hp)).mdifferentiableAt
      (by simp)
  let f₁ : S × ℝ → V₀ × V₀ := ψ ∘ Prod.fst
  have hdψ : MDifferentiableAt J 𝓘(ℝ, V₀ × V₀) ψ p.1 :=
    ((ψ.contMDiffOn p.1 hp.1.1).contMDiffAt
      (ψ.open_source.mem_nhds hp.1.1)).mdifferentiableAt (by simp)
  have hdf₁ : MDifferentiableAt (J.prod 𝓘(ℝ)) 𝓘(ℝ, V₀ × V₀) f₁ p :=
    hdψ.comp p mdifferentiableAt_fst
  have hdh : DifferentiableAt ℝ h (f₁ p) :=
    (hh.contDiffAt (hW₀.mem_nhds hp.1.2)).differentiableAt (by simp)
  have hmv₁ : mvfderiv (J.prod 𝓘(ℝ)) f₁ p v =
      mvfderiv J ψ p.1 (Manifold.tangentSpaceProdEquiv p v).1 := by
    rw [mvfderiv_apply_eq_mfderiv_apply, mfderiv_comp p hdψ mdifferentiableAt_fst,
      ContinuousLinearMap.comp_apply, mfderiv_fst, Manifold.tangentSpaceProdEquiv_apply,
      mvfderiv_apply_eq_mfderiv_apply]
    rfl
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact ((ContinuousLinearMap.fst ℝ V₀ (V₀ × ℝ)).mvfderiv_comp_apply hdchart v).symm.trans
      (((ContinuousLinearMap.fst ℝ V₀ V₀).mvfderiv_comp_apply hdf₁ v).trans
        (congrArg Prod.fst hmv₁))
  · let L₂ := (ContinuousLinearMap.fst ℝ V₀ ℝ).comp (ContinuousLinearMap.snd ℝ V₀ (V₀ × ℝ))
    exact (L₂.mvfderiv_comp_apply hdchart v).symm.trans
      (((ContinuousLinearMap.snd ℝ V₀ V₀).mvfderiv_comp_apply hdf₁ v).trans
        (congrArg Prod.snd hmv₁))
  · let L₃ := (ContinuousLinearMap.snd ℝ V₀ ℝ).comp (ContinuousLinearMap.snd ℝ V₀ (V₀ × ℝ))
    refine (L₃.mvfderiv_comp_apply hdchart v).symm.trans ?_
    -- Unfold `L₃ ∘ chart` to the vertical coordinate minus `h ∘ f₁`.
    change mvfderiv (J.prod 𝓘(ℝ)) (fun q : S × ℝ ↦ q.2 - (h ∘ f₁) q) p v = _
    rw [mvfderiv_fun_sub mdifferentiableAt_snd (hdh.mdifferentiableAt.comp p hdf₁), sub_apply,
      mvfderiv_comp_apply_of_differentiableAt hdh hdf₁, hmv₁,
      mvfderiv_apply_eq_mfderiv_apply, mfderiv_snd, Manifold.tangentSpaceProdEquiv_apply,
      NormedSpace.fromTangentSpace_apply]
    rfl

/-- Given a symplectic Darboux chart `ψ` pulling `stdSymplecticForm` back to `-dθ`, check that the
difference `(ψ⁻¹)^* θ - ⟪p, dq⟫` on `V_P = ⟨ψ.target, ψ.open_target⟩` is closed. -/
private theorem isClosed_contactizationDiffForm {V₀ : Type*} [NormedAddCommGroup V₀]
    [InnerProductSpace ℝ V₀] (θ : SmoothForm J S ℝ 1)
    (ψ : PartialDiffeomorph J 𝓘(ℝ, V₀ × V₀) S (V₀ × V₀) ∞)
    (hψ_symp : ∀ s ∈ ψ.source, ∀ u v : TangentSpace J s,
      (-mextDerivₗ J 1 θ).eval₂ s u v =
        stdSymplecticForm (mvfderiv J ψ s u) (mvfderiv J ψ s v)) :
    let V_P : Opens (V₀ × V₀) := ⟨ψ.target, ψ.open_target⟩
    let e_S := ψ.toDiffeomorphSourceTarget
    let f : V_P → S := Subtype.val ∘ e_S.symm
    let L₀ : (V₀ × V₀) →L[ℝ] (V₀ × V₀ × ℝ) :=
      (ContinuousLinearMap.fst ℝ V₀ V₀).prod ((ContinuousLinearMap.snd ℝ V₀ V₀).prod 0)
    let ι₀ : V_P → V₀ × V₀ × ℝ := L₀ ∘ Subtype.val
    mextDeriv (SmoothForm.mpullback f (contMDiff_subtype_val.comp e_S.symm.contMDiff) θ +
      SmoothForm.mpullback ι₀ (L₀.contDiff.contMDiff.comp contMDiff_subtype_val)
        (innerProductContactForm V₀)).1 = 0 := by
  have : IsManifold J 1 S := .of_le (n := ∞) (by simp)
  intro V_P e_S f L₀ ι₀
  have hf : ContMDiff 𝓘(ℝ, V₀ × V₀) J ∞ f := contMDiff_subtype_val.comp e_S.symm.contMDiff
  have hψf : ψ ∘ f = (Subtype.val : V_P → V₀ × V₀) :=
    funext fun y ↦ by simp [f, e_S, ψ.right_inv y.2]
  have hdfψ (y : V_P) (w : TangentSpace 𝓘(ℝ, V₀ × V₀) y) :
      mvfderiv J ψ (f y) (mfderiv 𝓘(ℝ, V₀ × V₀) J f y w) = w := by
    have hdψy : MDifferentiableAt J 𝓘(ℝ, V₀ × V₀) ψ (f y) :=
      ((ψ.contMDiffOn (f y) (e_S.symm y).2).contMDiffAt
        (ψ.open_source.mem_nhds (e_S.symm y).2)).mdifferentiableAt (by simp)
    rw [mvfderiv_apply_eq_mfderiv_apply, ← ContinuousLinearMap.comp_apply,
      ← mfderiv_comp y hdψy (hf.mdifferentiableAt (by simp)), hψf, Manifold.mfderiv_subtype_val]
    exact Manifold.tangentSpaceOpenEquiv_apply y w
  rw [← mextDerivₗ_apply]
  funext y
  refine ContinuousAlternatingMap.ext fun m ↦ ?_
  obtain ⟨w₁, w₂, rfl⟩ : ∃ w₁ w₂, m = ![w₁, w₂] :=
    ⟨m 0, m 1, funext fun i ↦ by fin_cases i <;> rfl⟩
  rw [map_add, SmoothForm.mextDerivₗ_mpullback, SmoothForm.mextDerivₗ_mpullback,
    Submodule.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply, Pi.zero_apply,
    ContinuousAlternatingMap.coe_zero, Pi.zero_apply, ← SmoothBundleForm.eval₂_apply,
    ← SmoothBundleForm.eval₂_apply, SmoothForm.eval₂_mpullback, SmoothForm.eval₂_mpullback]
  have h₁ := hψ_symp (f y) (e_S.symm y).2 (mfderiv 𝓘(ℝ, V₀ × V₀) J f y w₁)
    (mfderiv 𝓘(ℝ, V₀ × V₀) J f y w₂)
  rw [hdfψ y w₁, hdfψ y w₂, SmoothBundleForm.eval₂_neg] at h₁
  let w₁' : V₀ × V₀ := w₁
  let w₂' : V₀ × V₀ := w₂
  have hdι₀₁ : mfderiv 𝓘(ℝ, V₀ × V₀) 𝓘(ℝ, V₀ × V₀ × ℝ) ι₀ y w₁ = L₀ w₁' := by
    rw [← mvfderiv_apply_eq_mfderiv_apply,
      L₀.mvfderiv_comp_apply (contMDiff_subtype_val.mdifferentiableAt one_ne_zero),
      Manifold.mvfderiv_subtype_val_apply]
  have hdι₀₂ : mfderiv 𝓘(ℝ, V₀ × V₀) 𝓘(ℝ, V₀ × V₀ × ℝ) ι₀ y w₂ = L₀ w₂' := by
    rw [← mvfderiv_apply_eq_mfderiv_apply,
      L₀.mvfderiv_comp_apply (contMDiff_subtype_val.mdifferentiableAt one_ne_zero),
      Manifold.mvfderiv_subtype_val_apply]
  have hL₀ (u : V₀ × V₀) : L₀ u = (u.1, u.2, 0) := rfl
  have hterm₂ : (mextDerivₗ 𝓘(ℝ, V₀ × V₀ × ℝ) 1 (innerProductContactForm V₀)).eval₂ (ι₀ y)
      (mfderiv 𝓘(ℝ, V₀ × V₀) 𝓘(ℝ, V₀ × V₀ × ℝ) ι₀ y w₁)
      (mfderiv 𝓘(ℝ, V₀ × V₀) 𝓘(ℝ, V₀ × V₀ × ℝ) ι₀ y w₂) =
      stdSymplecticForm w₁' w₂' := by
    refine (congrArg₂ ((mextDerivₗ 𝓘(ℝ, V₀ × V₀ × ℝ) 1 (innerProductContactForm V₀)).eval₂
      (ι₀ y)) hdι₀₁ hdι₀₂).trans ?_
    refine (SmoothBundleForm.eval₂_apply _ (ι₀ y) (L₀ w₁') (L₀ w₂')).trans ?_
    refine (congrArg (fun g : RoughForm 𝓘(ℝ, V₀ × V₀ × ℝ) (V₀ × V₀ × ℝ) ℝ (1 + 1) ↦
      g (ι₀ y) ![L₀ w₁', L₀ w₂'])
      (mextDerivₗ_apply 𝓘(ℝ, V₀ × V₀ × ℝ) 1 (innerProductContactForm V₀))).trans ?_
    refine (mextDeriv_innerProductContactForm_apply V₀ (ι₀ y) (L₀ w₁') (L₀ w₂')).trans ?_
    simp only [hL₀, Prod.mk.eta]
  rw [hterm₂]
  linarith

/-- Given a symplectic Darboux chart `ψ` pulling `stdSymplecticForm` back to `-dθ`, the Poincaré
lemma on `ψ.target` supplies an open subset `W₀ ⊆ ψ.target` around `0` and a smooth primitive `h`
normalized by `h 0 = z₀`. -/
private theorem exists_primitive_contactization_darboux {V₀ : Type*} [NormedAddCommGroup V₀]
    [InnerProductSpace ℝ V₀] [FiniteDimensional ℝ V₀] (θ : SmoothForm J S ℝ 1)
    (ψ : PartialDiffeomorph J 𝓘(ℝ, V₀ × V₀) S (V₀ × V₀) ∞) {s₀ : S} (hs₀ψ : s₀ ∈ ψ.source)
    (hψ0 : ψ s₀ = 0) (z₀ : ℝ)
    (hψ_symp : ∀ s ∈ ψ.source, ∀ u v : TangentSpace J s,
      (-mextDerivₗ J 1 θ).eval₂ s u v =
        stdSymplecticForm (mvfderiv J ψ s u) (mvfderiv J ψ s v)) :
    ∃ (W₀ : Set (V₀ × V₀)) (h : V₀ × V₀ → ℝ),
      IsOpen W₀ ∧ W₀ ⊆ ψ.target ∧ (0 : V₀ × V₀) ∈ W₀ ∧ ContDiffOn ℝ ∞ h W₀ ∧ h 0 = z₀ ∧
      ∀ s ∈ ψ.source ∩ ψ ⁻¹' W₀, ∀ u : TangentSpace J s,
        fderiv ℝ h (ψ s) (mvfderiv J ψ s u) + ⟪(ψ s).2, (mvfderiv J ψ s u).1⟫_ℝ = θ.1 s ![u] := by
  have : IsManifold J 1 S := .of_le (n := ∞) (by simp)
  set V_P : Opens (V₀ × V₀) := ⟨ψ.target, ψ.open_target⟩
  set e_S := ψ.toDiffeomorphSourceTarget
  set v₀ : V_P := ⟨0, hψ0 ▸ ψ.map_source hs₀ψ⟩
  set f : V_P → S := Subtype.val ∘ e_S.symm
  have hf : ContMDiff 𝓘(ℝ, V₀ × V₀) J ∞ f := contMDiff_subtype_val.comp e_S.symm.contMDiff
  set L₀ : (V₀ × V₀) →L[ℝ] (V₀ × V₀ × ℝ) :=
    (ContinuousLinearMap.fst ℝ V₀ V₀).prod ((ContinuousLinearMap.snd ℝ V₀ V₀).prod 0)
  set ι₀ : V_P → V₀ × V₀ × ℝ := L₀ ∘ Subtype.val
  set η : SmoothForm 𝓘(ℝ, V₀ × V₀) V_P ℝ 1 :=
    SmoothForm.mpullback f hf θ +
      SmoothForm.mpullback ι₀ (L₀.contDiff.contMDiff.comp contMDiff_subtype_val)
        (innerProductContactForm V₀)
  obtain ⟨g₀, hg₀, O_sub, hv₀O, hprim⟩ := exists_contMDiff_isPrimitiveOn (r := ⊤) le_top
    η.isSmoothForm (isClosed_contactizationDiffForm θ ψ hψ_symp) v₀
  set W₀ : Set (V₀ × V₀) := Subtype.val '' O_sub
  have hW₀ : IsOpen W₀ := V_P.isOpen.isOpenMap_subtype_val O_sub hprim.isOpen
  set g₁ : V_P → ℝ := fun y ↦ g₀ y - g₀ v₀ + z₀
  have hg₁ : ContMDiff 𝓘(ℝ, V₀ × V₀) 𝓘(ℝ) ∞ g₁ := (hg₀.sub contMDiff_const).add contMDiff_const
  set h : V₀ × V₀ → ℝ := Subtype.val.extend g₁ 0
  have hh_ext : ∀ y : V_P, h y.1 = g₁ y := fun y ↦ Subtype.val_injective.extend_apply g₁ 0 y
  have hh_smooth : ContDiffOn ℝ ∞ h W₀ := by
    rw [← contMDiffOn_iff_contDiffOn]
    rintro _ ⟨y, -, rfl⟩
    exact ((hg₁.contMDiffAt (x := y)).extend_subtypeVal 0).contMDiffWithinAt
  refine ⟨W₀, h, hW₀, fun _ ⟨y, _, hy⟩ ↦ hy ▸ y.2, ⟨v₀, hv₀O, rfl⟩, hh_smooth, ?_, fun s hs ↦ ?_⟩
  · -- `v₀.1` is definitionally `0 : V₀ × V₀`.
    change h v₀.1 = z₀
    simp [hh_ext v₀, g₁]
  · obtain ⟨y, hyO, hy_eq⟩ := hs.2
    have hfy : s = f y := by simp [f, e_S, hy_eq, ψ.left_inv hs.1]
    subst hfy
    intro u
    let w' : V₀ × V₀ := mvfderiv J ψ (f y) u
    set w : TangentSpace 𝓘(ℝ, V₀ × V₀) y := w'
    have hfw : mfderiv 𝓘(ℝ, V₀ × V₀) J f y w = u := by
      apply injective_mvfderiv_iff.2
        ((ψ.isLocalDiffeomorphAt J _ ∞ hs.1).mfderivToContinuousLinearEquiv (by simp)).injective
      have hdψs : MDifferentiableAt J 𝓘(ℝ, V₀ × V₀) ψ (f y) :=
        ((ψ.contMDiffOn (f y) hs.1).contMDiffAt
          (ψ.open_source.mem_nhds hs.1)).mdifferentiableAt (by simp)
      have hψf : ψ ∘ f = (Subtype.val : V_P → V₀ × V₀) :=
        funext fun z ↦ by simp [f, e_S, ψ.right_inv z.2]
      rw [mvfderiv_apply_eq_mfderiv_apply, ← ContinuousLinearMap.comp_apply,
        ← mfderiv_comp y hdψs (hf.mdifferentiableAt (by simp)), hψf, Manifold.mfderiv_subtype_val]
      exact Manifold.tangentSpaceOpenEquiv_apply y w
    have hdh_eq : fderiv ℝ h (ψ (f y)) (mvfderiv J ψ (f y) u) = η.1 y ![w] := by
      have hdg₁ : fderiv ℝ h y.1 (mvfderiv J ψ (f y) u) =
          mvfderiv 𝓘(ℝ, V₀ × V₀) (h ∘ (Subtype.val : V_P → V₀ × V₀)) y w := by
        rw [mvfderiv_comp_apply_of_differentiableAt
          ((hh_smooth.contDiffAt (hW₀.mem_nhds ⟨y, hyO, rfl⟩)).differentiableAt (by simp))
          (contMDiff_subtype_val.mdifferentiableAt one_ne_zero),
          Manifold.mvfderiv_subtype_val_apply]
      -- Adding the constant `-g₀ v₀ + z₀` does not change `mvfderiv`.
      have hdg₀ : mvfderiv 𝓘(ℝ, V₀ × V₀) g₁ y w = mvfderiv 𝓘(ℝ, V₀ × V₀) g₀ y w := by
        simp only [g₁, sub_eq_add_neg, add_assoc, mvfderiv_add_const]
      rw [← hy_eq, hdg₁, (funext hh_ext : h ∘ (Subtype.val : V_P → V₀ × V₀) = g₁), hdg₀,
        mvfderiv_apply_eq_mfderiv_apply, ← mextDeriv_ofFunction_apply, hprim.mextDeriv_eq y hyO]
    have hdι₀ : mfderiv 𝓘(ℝ, V₀ × V₀) 𝓘(ℝ, V₀ × V₀ × ℝ) ι₀ y w = L₀ w' := by
      rw [← mvfderiv_apply_eq_mfderiv_apply,
        L₀.mvfderiv_comp_apply (contMDiff_subtype_val.mdifferentiableAt one_ne_zero),
        Manifold.mvfderiv_subtype_val_apply]
    have hv₁ : (fun i : Fin 1 ↦ mfderiv 𝓘(ℝ, V₀ × V₀) J f y (![w] i)) = ![u] := by
      ext i; fin_cases i; exact hfw
    have hv₂ : (fun i : Fin 1 ↦ mfderiv 𝓘(ℝ, V₀ × V₀) 𝓘(ℝ, V₀ × V₀ × ℝ) ι₀ y (![w] i)) =
        ![L₀ w'] := by
      ext i; fin_cases i; exact hdι₀
    have hη_eval : η.1 y ![w] = θ.1 (f y) ![u] - ⟪(ψ (f y)).2, (mvfderiv J ψ (f y) u).1⟫_ℝ := by
      rw [Submodule.coe_add, Pi.add_apply, ContinuousAlternatingMap.add_apply,
        SmoothForm.coe_mpullback, SmoothForm.coe_mpullback, mpullback_apply, mpullback_apply,
        hv₁, hv₂]
      have hL₀ (z : V₀ × V₀) : L₀ z = (z.1, z.2, 0) := rfl
      have hι₀y : ι₀ y = (y.1.1, y.1.2, 0) := rfl
      have hι_app : (innerProductContactForm V₀).1 (ι₀ y) ![L₀ w'] =
          -⟪(ψ (f y)).2, (mvfderiv J ψ (f y) u).1⟫_ℝ := by
        rw [innerProductContactForm_apply V₀ (ι₀ y) (L₀ w'), hι₀y, hL₀ w', hy_eq, zero_sub]
      exact (congrArg (θ.1 (f y) ![u] + ·) hι_app).trans (sub_eq_add_neg _ _).symm
    linarith [hdh_eq, hη_eval]

variable [FiniteDimensional ℝ E']

/-- **Strict contact Darboux theorem on contactizations at an interior point.** Let `θ` be a smooth
one-form on `S` whose contactization `dz - θ` on `S × ℝ` is a contact form. Around any `(s₀, z₀)`
with `s₀` an interior point of `S`, there are `n` with `dim E' = 2 n` and a centered smooth partial
diffeomorphism `chart` from `S × ℝ` to `ℝⁿ × ℝⁿ × ℝ` pulling `innerProductContactForm` back to
`θ.contactization`. -/
theorem SmoothForm.IsContactForm.exists_strictDarbouxChart_contactization_of_isInteriorPoint
    {θ : SmoothForm J S ℝ 1} (hθ : θ.contactization.IsContactForm) {s₀ : S}
    (hs₀ : J.IsInteriorPoint s₀) (z₀ : ℝ) :
    ∃ (n : ℕ) (chart : PartialDiffeomorph (J.prod 𝓘(ℝ))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) (S × ℝ)
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞),
      finrank ℝ E' = 2 * n ∧ (s₀, z₀) ∈ chart.source ∧ chart (s₀, z₀) = 0 ∧
      ∀ p ∈ chart.source, ∀ v : TangentSpace (J.prod 𝓘(ℝ)) p,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (chart p)
          ![mvfderiv (J.prod 𝓘(ℝ)) chart p v] = θ.contactization.1 p ![v] := by
  have hsymp : SmoothTwoForm.IsSymplectic (-mextDerivₗ J 1 θ) :=
    ⟨(SmoothForm.isClosed_mextDerivₗ θ).neg, SmoothForm.isContactForm_contactization_iff.1 hθ⟩
  obtain ⟨n, ψ, hs₀ψ, hψ0, hψ_symp⟩ := hsymp.exists_standardDarbouxChart_of_isInteriorPoint hs₀
  have hdim : finrank ℝ E' = 2 * n := by
    have hL : finrank ℝ E' =
        finrank ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
      ((ψ.isLocalDiffeomorphAt J _ ∞ hs₀ψ).mfderivToContinuousLinearEquiv
        (by simp)).toLinearEquiv.finrank_eq
    rw [finrank_prod, finrank_euclideanSpace_fin] at hL
    omega
  obtain ⟨W₀, h, hW₀, hW₀_sub, h0W₀, hh, hh0, hprim⟩ :=
    exists_primitive_contactization_darboux θ ψ hs₀ψ hψ0 z₀ hψ_symp
  let chart := contactizationShiftedChart ψ hW₀ hW₀_sub hh
  have hp₀ : (s₀, z₀) ∈ chart.source :=
    ⟨⟨hs₀ψ, by
      -- `mem_preimage` unfolds to `ψ s₀ ∈ W₀`.
      change ψ s₀ ∈ W₀
      rwa [hψ0]⟩, mem_univ _⟩
  refine ⟨n, chart, hdim, hp₀, ?_, fun p hp v ↦ ?_⟩
  · -- Unfold `chart (s₀, z₀)` to its coordinate triple.
    change ((ψ s₀).1, (ψ s₀).2, z₀ - h (ψ s₀)) = 0
    rw [hψ0, hh0, sub_self]
    rfl
  · refine (innerProductContactForm_apply (EuclideanSpace ℝ (Fin n)) (chart p)
      (mvfderiv (J.prod 𝓘(ℝ)) chart p v)).trans ?_
    rw [mvfderiv_contactizationShiftedChart ψ hW₀ hW₀_sub hh hp v,
      SmoothForm.contactization_apply]
    have hp' := hprim p.1 hp.1 (Manifold.tangentSpaceProdEquiv p v).1
    -- Both sides are real linear combinations of the vertical component, `dh`, `⟪p, dq⟫`, and `θ`.
    change (NormedSpace.fromTangentSpace p.2 (Manifold.tangentSpaceProdEquiv p v).2 -
        fderiv ℝ h (ψ p.1) (mvfderiv J ψ p.1 (Manifold.tangentSpaceProdEquiv p v).1)) -
      ⟪(ψ p.1).2, (mvfderiv J ψ p.1 (Manifold.tangentSpaceProdEquiv p v).1).1⟫_ℝ = _
    linarith

/-- **Strict contact Darboux theorem on contactizations** over a boundaryless base manifold. -/
theorem SmoothForm.IsContactForm.exists_strictDarbouxChart_contactization
    [BoundarylessManifold J S] {θ : SmoothForm J S ℝ 1} (hθ : θ.contactization.IsContactForm)
    (p₀ : S × ℝ) :
    ∃ (n : ℕ) (chart : PartialDiffeomorph (J.prod 𝓘(ℝ))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) (S × ℝ)
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞),
      finrank ℝ E' = 2 * n ∧ p₀ ∈ chart.source ∧ chart p₀ = 0 ∧
      ∀ p ∈ chart.source, ∀ v : TangentSpace (J.prod 𝓘(ℝ)) p,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (chart p)
          ![mvfderiv (J.prod 𝓘(ℝ)) chart p v] = θ.contactization.1 p ![v] :=
  hθ.exists_strictDarbouxChart_contactization_of_isInteriorPoint
    BoundarylessManifold.isInteriorPoint p₀.2

end Contactization

/-! ### Strict Darboux theorem on finite-dimensional normed spaces -/

section ModelSpace

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Cut off a locally smooth one-form `α` that is contact at `x₀ ∈ W` to obtain a global smooth
one-form `α_glob` on `V` whose restriction `α_Ω` to an open ball `Ω ⊆ W` around `x₀` is a smooth
contact form agreeing with `α` on `Ω`. -/
private theorem exists_smoothContactForm_opens_ball {W : Set V} (hW : IsOpen W) {x₀ : V}
    (hx₀ : x₀ ∈ W) {α : V → V [⋀^Fin 1]→L[ℝ] ℝ} (hα : ContDiffOn ℝ ∞ α W)
    (hc : IsContactFormAt (I := 𝓘(ℝ, V)) α x₀) :
    ∃ (Ω : Opens V) (p₀ : Ω) (α_glob : SmoothForm 𝓘(ℝ, V) V ℝ 1)
      (α_Ω : SmoothForm 𝓘(ℝ, V) Ω ℝ 1),
      (p₀ : V) = x₀ ∧ (Ω : Set V) ⊆ W ∧
      α_Ω = SmoothForm.mpullback Subtype.val contMDiff_subtype_val α_glob ∧
      α_Ω.IsContactForm ∧ ∀ y : Ω, α_Ω.1 y = α y.1 := by
  have hev : ∀ᶠ x in 𝓝 x₀, x ∈ W ∧ IsContactFormAt (I := 𝓘(ℝ, V)) α x :=
    Filter.Eventually.and (hW.mem_nhds hx₀)
      (hc.eventually_modelSpace ((hα.contDiffAt (hW.mem_nhds hx₀)).of_le (by simp)))
  obtain ⟨r, hr, hr_sub⟩ := Metric.eventually_nhds_iff_ball.1 hev
  let ρ : ContDiffBump x₀ := ⟨r / 4, r / 2, by positivity, by linarith⟩
  set α' : V → V [⋀^Fin 1]→L[ℝ] ℝ := fun x ↦ ρ x • α x
  have hρ_sub : tsupport ρ ⊆ W := by
    rw [ρ.tsupport_eq]
    -- `ρ.rOut` is definitionally `r / 2 < r`.
    exact (Metric.closedBall_subset_ball (show ρ.rOut < r by dsimp [ρ]; linarith)).trans
      fun x hx ↦ (hr_sub x hx).1
  have hα'_smooth : ContDiff ℝ ∞ α' := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hxW : x ∈ W
    · exact ρ.contDiffAt.smul (hα.contDiffAt (hW.mem_nhds hxW))
    · refine (contDiffAt_const (c := 0)).congr_of_eventuallyEq ?_
      filter_upwards [(isClosed_tsupport ρ).isOpen_compl.mem_nhds fun h ↦ hxW (hρ_sub h)] with y hy
      simp [α', image_eq_zero_of_notMem_tsupport hy]
  let α_glob : SmoothForm 𝓘(ℝ, V) V ℝ 1 :=
    ⟨α', (isSmoothForm_modelSpace_iff.2 hα'_smooth).mem_smoothBundleForms⟩
  let Ω : Opens V := ⟨Metric.ball x₀ (r / 4), Metric.isOpen_ball⟩
  let p₀ : Ω := ⟨x₀, Metric.mem_ball_self (by positivity)⟩
  let α_Ω : SmoothForm 𝓘(ℝ, V) Ω ℝ 1 :=
    SmoothForm.mpullback Subtype.val contMDiff_subtype_val α_glob
  have hα'_eq_on (y : V) (hy : y ∈ Metric.ball x₀ (r / 4)) : ρ y • α y = α y := by
    simp [ρ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)]
  have hα_Ω_contact : α_Ω.IsContactForm := by
    refine SmoothForm.isContactForm_iff_forall_isContactFormAt.2 fun y ↦ ?_
    have hbij : Function.Bijective (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) (Subtype.val : Ω → V) y) := by
      rw [Manifold.mfderiv_subtype_val]
      exact (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, V)) y).bijective
    rw [SmoothForm.coe_mpullback,
      isContactFormAt_mpullback_iff contMDiff_subtype_val.contMDiffAt
        (α_glob.contMDiff.contMDiffAt.of_le (by simp)) hbij]
    have hev_eq : (fun x ↦ ρ x • α x) =ᶠ[𝓝 y.1] α :=
      eventually_of_mem (Metric.isOpen_ball.mem_nhds y.2) hα'_eq_on
    rw [isContactFormAt_modelSpace_iff_isContact, hα'_eq_on y.1 y.2, hev_eq.extDeriv_eq,
      ← isContactFormAt_modelSpace_iff_isContact]
    exact (hr_sub y.1 (Metric.ball_subset_ball (by linarith) y.2)).2
  refine ⟨Ω, p₀, α_glob, α_Ω, rfl,
    fun y hy ↦ (hr_sub y (Metric.ball_subset_ball (by linarith) hy)).1, rfl, hα_Ω_contact,
    fun y ↦ ?_⟩
  rw [SmoothForm.coe_mpullback, mpullback_subtype_val_apply]
  exact hα'_eq_on y.1 y.2

/-- For any smooth two-form `η` on a finite-dimensional normed space `E`, nondegeneracy of
`η.bilinFormAt` at `x₀` persists on an open neighborhood of `x₀`. -/
private theorem exists_open_nondegenerate_bilinFormAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (η : SmoothForm 𝓘(ℝ, E) E ℝ 2) {x₀ : E}
    (h₀ : (η.bilinFormAt x₀).Nondegenerate) :
    ∃ U : Set E, IsOpen U ∧ x₀ ∈ U ∧ ∀ x ∈ U, (η.bilinFormAt x).Nondegenerate := by
  let gB : E → E →L[ℝ] E →L[ℝ] ℝ := fun x ↦ ContinuousAlternatingMap.flatL ℝ E ℝ (η.1 x)
  have hgB_cont : Continuous gB :=
    (ContinuousAlternatingMap.flatL ℝ E ℝ).continuous.comp
      (isSmoothForm_modelSpace_iff.1 η.isSmoothForm).continuous
  have hgB_eq (x : E) : (gB x).toBilinForm = η.bilinFormAt x := by
    ext u w
    exact (ContinuousAlternatingMap.flatL_apply_apply _ u w).trans
      ((η.bilinFormAt_apply x u w).trans (SmoothBundleForm.eval₂_apply η x u w)).symm
  obtain ⟨U, hU, hU_open, hx₀U⟩ := eventually_nhds_iff.1
    (hgB_cont.continuousAt.eventually_toBilinForm_nondegenerate (by rwa [hgB_eq]))
  exact ⟨U, hU_open, hx₀U, fun x hx ↦ hgB_eq x ▸ hU x hx⟩

/-- Restricting a smooth map `ι : S_Ω → M` to a smaller open subset `S' ≤ S_Ω` on which `-d(ι^* α)`
is everywhere nondegenerate yields a contactization contact form on `S' × ℝ`. -/
private theorem isContactForm_contactization_neg_mpullback_inclusion
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {S_Ω S' : Opens E'} (hS' : S' ≤ S_Ω) {ι : S_Ω → M} (hι : ContMDiff 𝓘(ℝ, E') I ∞ ι)
    (α_M : SmoothForm I M ℝ 1) (dθ_K : SmoothForm 𝓘(ℝ, E') E' ℝ 2)
    (hdθ_S : -mextDerivₗ 𝓘(ℝ, E') 1 (SmoothForm.mpullback ι hι (-α_M)) =
      SmoothForm.mpullback Subtype.val contMDiff_subtype_val dθ_K)
    (hnd : ∀ s : S', (dθ_K.bilinFormAt s.1).Nondegenerate) :
    (-SmoothForm.mpullback (ι ∘ Opens.inclusion hS')
      (hι.comp (contMDiff_inclusion hS')) α_M).contactization.IsContactForm := by
  have : IsManifold I 1 M := .of_le (n := ∞) (by simp)
  rw [SmoothForm.isContactForm_contactization_iff]
  have hpull : SmoothForm.mpullback (Opens.inclusion hS') (contMDiff_inclusion hS')
      (SmoothForm.mpullback (Subtype.val : S_Ω → E') contMDiff_subtype_val dθ_K) =
      SmoothForm.mpullback (Subtype.val : S' → E') contMDiff_subtype_val dθ_K :=
    Subtype.ext <| funext fun s' ↦ by
      rw [SmoothForm.coe_mpullback, SmoothForm.coe_mpullback, mpullback_inclusion_apply,
        SmoothForm.coe_mpullback, mpullback_subtype_val_apply, mpullback_subtype_val_apply]
  have hneg₁ : -SmoothForm.mpullback (ι ∘ Opens.inclusion hS')
      (hι.comp (contMDiff_inclusion hS')) α_M =
      SmoothForm.mpullback (Opens.inclusion hS') (contMDiff_inclusion hS')
        (SmoothForm.mpullback ι hι (-α_M)) :=
    (map_neg (SmoothForm.mpullback (ι ∘ Opens.inclusion hS')
      (hι.comp (contMDiff_inclusion hS'))) α_M).symm.trans
      (SmoothForm.mpullback_mpullback (Opens.inclusion hS') ι
        (contMDiff_inclusion hS') hι (-α_M)).symm
  have hdθ_S' : -mextDerivₗ 𝓘(ℝ, E') 1 (-SmoothForm.mpullback (ι ∘ Opens.inclusion hS')
      (hι.comp (contMDiff_inclusion hS')) α_M) =
      SmoothForm.mpullback Subtype.val contMDiff_subtype_val dθ_K :=
    (congrArg (fun γ ↦ -mextDerivₗ 𝓘(ℝ, E') 1 γ) hneg₁).trans
      ((congrArg Neg.neg (SmoothForm.mextDerivₗ_mpullback (Opens.inclusion hS')
        (contMDiff_inclusion hS') 1 (SmoothForm.mpullback ι hι (-α_M)))).trans
        (((SmoothForm.mpullback (F := ℝ) (k := 2) (Opens.inclusion hS')
          (contMDiff_inclusion hS')).map_neg _).symm.trans
          ((congrArg (SmoothForm.mpullback (Opens.inclusion hS') (contMDiff_inclusion hS'))
            hdθ_S).trans hpull)))
  rw [hdθ_S', SmoothTwoForm.isNondegenerate_iff_separatingLeft]
  intro s' v hv
  exact ((SmoothTwoForm.nondegenerate_bilinFormAt_mpullback_subtype_val_iff s').2
    (hnd s')).1 v fun w ↦ (SmoothForm.bilinFormAt_apply _ s' v w).trans (hv w)

/-- Double negation cancels across `mextDerivₗ` and `SmoothForm.mpullback`. -/
private theorem neg_mextDerivₗ_mpullback_neg
    {E H M E' H' N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 2 N]
    (f : N → M) (hf : ContMDiff J I ∞ f) (α : SmoothForm I M ℝ 1) :
    -mextDerivₗ J 1 (SmoothForm.mpullback f hf (-α)) =
      mextDerivₗ J 1 (SmoothForm.mpullback f hf α) := by
  rw [(SmoothForm.mpullback (F := ℝ) (k := 1) f hf).map_neg α,
    (mextDerivₗ J (M := N) (F := ℝ) 1).map_neg, neg_neg]

/-- Construct a transverse affine hyperplane slice `ι' : S' → Ω` through `p₀` in `ker α_{p₀}` on
which `-ι'^* α_Ω` has contact contactization. -/
private theorem exists_nondegenerate_slice_opens {Ω : Opens V} (p₀ : Ω)
    (α_glob : SmoothForm 𝓘(ℝ, V) V ℝ 1) {α_Ω : SmoothForm 𝓘(ℝ, V) Ω ℝ 1}
    (hα_def : α_Ω = SmoothForm.mpullback Subtype.val contMDiff_subtype_val α_glob)
    (hα_Ω : α_Ω.IsContactForm) :
    ∃ (K : Submodule ℝ V) (_ : FiniteDimensional ℝ K) (S' : Opens K) (s₀' : S') (ι' : S' → Ω)
      (hι' : ContMDiff 𝓘(ℝ, K) 𝓘(ℝ, V) ∞ ι'),
      finrank ℝ K + 1 = finrank ℝ V ∧ ι' s₀' = p₀ ∧
      Function.Injective (mfderiv 𝓘(ℝ, K) 𝓘(ℝ, V) ι' s₀') ∧
      α_Ω.reebVectorField (ι' s₀') ∉ (mfderiv 𝓘(ℝ, K) 𝓘(ℝ, V) ι' s₀').range ∧
      (-SmoothForm.mpullback ι' hι' α_Ω).contactization.IsContactForm := by
  let e_V (p : Ω) : TangentSpace 𝓘(ℝ, V) p ≃L[ℝ] V :=
    (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, V)) p).trans (NormedSpace.fromTangentSpace p.1)
  let K : Submodule ℝ V := (α_Ω.kerDistribution p₀).map (e_V p₀).toLinearEquiv.toLinearMap
  have hdimK : finrank ℝ K + 1 = finrank ℝ V := by
    rw [LinearEquiv.finrank_map_eq]
    exact hα_Ω.finrank_kerDistribution_add_one p₀
  let ι_K : K → V := fun k ↦ p₀.1 + K.subtypeL k
  have hι_K : ContDiff ℝ ∞ ι_K := contDiff_const.add K.subtypeL.contDiff
  let S_Ω : Opens K := ⟨ι_K ⁻¹' Ω, Ω.isOpen.preimage hι_K.continuous⟩
  let s₀ : S_Ω := ⟨0, by simp [S_Ω, ι_K]⟩
  let ι : S_Ω → Ω := fun s ↦ ⟨ι_K s.1, s.2⟩
  have hι : ContMDiff 𝓘(ℝ, K) 𝓘(ℝ, V) ∞ ι :=
    (ContMDiff.subtypeVal_comp_iff Ω ι).1 (hι_K.contMDiff.comp contMDiff_subtype_val)
  have hιs₀ : ι s₀ = p₀ := Subtype.ext (by simp [ι, ι_K, s₀])
  let e_K (s : S_Ω) : TangentSpace 𝓘(ℝ, K) s ≃L[ℝ] K :=
    (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, K)) s).trans (NormedSpace.fromTangentSpace s.1)
  have hdι (u : TangentSpace 𝓘(ℝ, K) s₀) :
      e_V (ι s₀) (mfderiv 𝓘(ℝ, K) 𝓘(ℝ, V) ι s₀ u) = K.subtypeL (e_K s₀ u) := by
    have hopen := congrArg (NormedSpace.fromTangentSpace (ι s₀).1)
      (Manifold.tangentSpaceOpenEquiv_mfderiv_apply (I := 𝓘(ℝ, K)) (I' := 𝓘(ℝ, V))
        (f := ι) (A := ι_K) rfl u)
    have hfderiv : fderiv ℝ ι_K s₀.1 = K.subtypeL := by
      have hcomm : ι_K = fun k : K ↦ K.subtypeL k + p₀.1 := funext fun k ↦ add_comm _ _
      rw [hcomm, fderiv_add_const, K.subtypeL.fderiv]
    exact hopen.trans ((mvfderiv_eq_fderiv_apply (𝕜 := ℝ) ι_K s₀.1 _).trans <| by
      rw [hfderiv]
      exact congrArg K.subtypeL (NormedSpace.fromTangentSpace_apply (𝕜 := ℝ) s₀.1 _).symm)
  have hι_inj : Function.Injective (mfderiv 𝓘(ℝ, K) 𝓘(ℝ, V) ι s₀) := fun u₁ u₂ h ↦
    (e_K s₀).injective <| Subtype.ext <|
      (hdι u₁).symm.trans ((congrArg (e_V (ι s₀)) h).trans (hdι u₂))
  have hR : α_Ω.reebVectorField (ι s₀) ∉ (mfderiv 𝓘(ℝ, K) 𝓘(ℝ, V) ι s₀).range := by
    rintro ⟨u, hu⟩
    simp only [ContinuousLinearMap.coe_coe] at hu
    have hmem : (fun p : Ω ↦ e_V p (α_Ω.reebVectorField p)) (ι s₀) ∈ K := by
      dsimp only
      rw [← hu, hdι u]
      exact (e_K s₀ u).2
    rw [hιs₀] at hmem
    obtain ⟨v, hv, hv_eq⟩ := hmem
    exact hα_Ω.reebVectorField_notMem_kerDistribution p₀ ((e_V p₀).injective hv_eq ▸ hv)
  -- Pull `-α_glob` back to the normed space `K`, where openness of nondegeneracy applies directly.
  let θ_K : SmoothForm 𝓘(ℝ, K) K ℝ 1 := SmoothForm.mpullback ι_K hι_K.contMDiff (-α_glob)
  let dθ_K : SmoothForm 𝓘(ℝ, K) K ℝ 2 := -mextDerivₗ 𝓘(ℝ, K) 1 θ_K
  have hdθ_S : -mextDerivₗ 𝓘(ℝ, K) 1 (SmoothForm.mpullback ι hι (-α_Ω)) =
      SmoothForm.mpullback (Subtype.val : S_Ω → K) contMDiff_subtype_val dθ_K := by
    have hneg_α : -α_Ω = SmoothForm.mpullback Subtype.val contMDiff_subtype_val (-α_glob) := by
      rw [hα_def]
      exact ((SmoothForm.mpullback (F := ℝ) (k := 1) Subtype.val
        contMDiff_subtype_val).map_neg α_glob).symm
    have hpull_eq : SmoothForm.mpullback ι hι (-α_Ω) =
        SmoothForm.mpullback (Subtype.val : S_Ω → K) contMDiff_subtype_val θ_K := by
      rw [hneg_α]
      exact SmoothForm.mpullback_mpullback_of_comp_eq hι contMDiff_subtype_val
        contMDiff_subtype_val hι_K.contMDiff rfl (-α_glob)
    exact (congrArg (fun γ ↦ -mextDerivₗ 𝓘(ℝ, K) 1 γ) hpull_eq).trans
      ((congrArg Neg.neg (SmoothForm.mextDerivₗ_mpullback (Subtype.val : S_Ω → K)
        contMDiff_subtype_val 1 θ_K)).trans
        ((SmoothForm.mpullback (F := ℝ) (k := 2) (Subtype.val : S_Ω → K)
          contMDiff_subtype_val).map_neg (mextDerivₗ 𝓘(ℝ, K) 1 θ_K)).symm)
  have hnd₀ : (dθ_K.bilinFormAt (0 : K)).Nondegenerate := by
    have hnd_s₀ : ((-mextDerivₗ 𝓘(ℝ, K) 1 (SmoothForm.mpullback ι hι (-α_Ω))).bilinFormAt
        s₀).Nondegenerate :=
      (neg_mextDerivₗ_mpullback_neg ι hι α_Ω).symm ▸
        hα_Ω.nondegenerate_bilinFormAt_mextDerivₗ_mpullback hι hdimK hι_inj hR
    exact (SmoothTwoForm.nondegenerate_bilinFormAt_mpullback_subtype_val_iff s₀).1
      (hdθ_S ▸ hnd_s₀)
  obtain ⟨U_K, hU_open, h0U, hU_nd⟩ := exists_open_nondegenerate_bilinFormAt dθ_K hnd₀
  let S' : Opens K := ⟨(S_Ω : Set K) ∩ U_K, S_Ω.isOpen.inter hU_open⟩
  have hS' : S' ≤ S_Ω := inter_subset_left
  let s₀' : S' := ⟨0, s₀.2, h0U⟩
  have hdι' (u : TangentSpace 𝓘(ℝ, K) s₀') :
      mfderiv 𝓘(ℝ, K) 𝓘(ℝ, V) (ι ∘ Opens.inclusion hS') s₀' u = mfderiv 𝓘(ℝ, K) 𝓘(ℝ, V) ι s₀ u := by
    rw [mfderiv_comp s₀' (hι.mdifferentiableAt (by simp))
      ((contMDiff_inclusion hS').mdifferentiableAt one_ne_zero), ContinuousLinearMap.comp_apply,
      Manifold.mfderiv_inclusion_apply]
  exact ⟨K, inferInstance, S', s₀', ι ∘ Opens.inclusion hS', hι.comp (contMDiff_inclusion hS'),
    hdimK, hιs₀, fun u₁ u₂ h ↦ hι_inj ((hdι' u₁).symm.trans (h.trans (hdι' u₂))),
    fun ⟨u, hu⟩ ↦ hR ⟨u, (hdι' u).symm.trans hu⟩,
    isContactForm_contactization_neg_mpullback_inclusion hS' hι α_Ω dθ_K hdθ_S
      fun s' ↦ hU_nd s'.1 s'.2.2⟩

/-- Apply the Reeb flow of `α_Ω` to a transverse slice `ι' : S' → Ω` to obtain a local
diffeomorphism `G_Ω : S' × ℝ → Ω` pulling `α_Ω` back to a contactization contact form. -/
private theorem exists_strictContactization_slice_modelSpace {Ω : Opens V} (p₀ : Ω)
    (α_glob : SmoothForm 𝓘(ℝ, V) V ℝ 1) {α_Ω : SmoothForm 𝓘(ℝ, V) Ω ℝ 1}
    (hα_def : α_Ω = SmoothForm.mpullback Subtype.val contMDiff_subtype_val α_glob)
    (hα_Ω : α_Ω.IsContactForm) :
    ∃ (K : Submodule ℝ V) (_ : FiniteDimensional ℝ K) (S' : Opens K) (s₀' : S')
      (θ' : SmoothForm 𝓘(ℝ, K) S' ℝ 1) (G_Ω : S' × ℝ → Ω) (D₀ : Set (S' × ℝ)),
      finrank ℝ K + 1 = finrank ℝ V ∧
      θ'.contactization.IsContactForm ∧
      IsLocalDiffeomorphAt (𝓘(ℝ, K).prod 𝓘(ℝ)) 𝓘(ℝ, V) ∞ G_Ω (s₀', 0) ∧
      G_Ω (s₀', 0) = p₀ ∧
      IsOpen D₀ ∧ (s₀', (0 : ℝ)) ∈ D₀ ∧
      (∀ q ∈ D₀, ContMDiffAt (𝓘(ℝ, K).prod 𝓘(ℝ)) 𝓘(ℝ, V) ∞ G_Ω q) ∧
      ∀ q ∈ D₀, mpullback (𝓘(ℝ, K).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, V) G_Ω α_Ω.1 q = θ'.contactization.1 q := by
  obtain ⟨K, _, S', s₀', ι', hι', hdimK, hιs₀, hι'_inj, hR', hθ'_contact⟩ :=
    exists_nondegenerate_slice_opens p₀ α_glob hα_def hα_Ω
  have hZ : ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, V).tangent ∞ (T% α_Ω.reebVectorField) :=
    hα_Ω.contMDiff_reebVectorField
  have hp_dom : ((0 : ℝ), ι' s₀') ∈ flowDomain α_Ω.reebVectorField :=
    mem_flowDomain_zero (hZ.of_le (by simp)) (ι' s₀')
  let G_Ω : S' × ℝ → Ω := fun q ↦ flowOf α_Ω.reebVectorField q.2 (ι' q.1)
  let D₀ : Set (S' × ℝ) := {q | (q.2, ι' q.1) ∈ flowDomain α_Ω.reebVectorField}
  have hD₀_open : IsOpen D₀ :=
    isOpen_setOf_mem_flowDomain (hZ.of_le (by simp)) continuous_snd
      (hι'.continuous.comp continuous_fst)
  refine ⟨K, inferInstance, S', s₀', -SmoothForm.mpullback ι' hι' α_Ω, G_Ω, D₀, hdimK, hθ'_contact,
    hα_Ω.isLocalDiffeomorphAt_flowOf_reebVectorField_comp hι' hdimK hι'_inj hR' hp_dom,
    by simp [G_Ω, hιs₀], hD₀_open, hp_dom,
    fun q hq ↦ contMDiffAt_flowOf_comp le_top hZ contMDiffAt_snd
      (hι'.contMDiffAt.comp q contMDiffAt_fst) hq,
    fun q hq ↦ mpullback_flowOf_comp_apply_eq_contactization hZ hι' hα_Ω.apply_reebVectorField
      hα_Ω.interior_mextDeriv_reebVectorField hq⟩

omit [FiniteDimensional ℝ V] in
/-- Lift a partial diffeomorphism `Ψ_Ω` out of an open subset `Ω ⊆ V` to an ambient partial
diffeomorphism `Φ` on `V` around `p₀` and record its pointwise value and Fréchet derivative. -/
private theorem exists_ambient_fderiv_of_opens {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ω : Opens V} (Ψ_Ω : PartialDiffeomorph 𝓘(ℝ, V) 𝓘(ℝ, F) Ω F ∞) {p₀ : Ω}
    (hp₀_Ψ : p₀ ∈ Ψ_Ω.source) :
    ∃ (Φ : PartialDiffeomorph 𝓘(ℝ, V) 𝓘(ℝ, F) V F ∞) (hΦ_sub_Ω : Φ.source ⊆ Ω),
      (p₀ : V) ∈ Φ.source ∧ Φ p₀.1 = Ψ_Ω p₀ ∧
      ∀ x (hx : x ∈ Φ.source),
        (⟨x, hΦ_sub_Ω hx⟩ : Ω) ∈ Ψ_Ω.source ∧ Φ x = Ψ_Ω ⟨x, hΦ_sub_Ω hx⟩ ∧
        ∀ v : V, fderiv ℝ Φ x v = mvfderiv 𝓘(ℝ, V) Ψ_Ω ⟨x, hΦ_sub_Ω hx⟩ v := by
  obtain ⟨Φ, hx₀_Φ, hΦ_sub_Ω, hΦ_p₀, hΦ_tgt, hΦ_symm⟩ := Ψ_Ω.exists_ambient_of_opens hp₀_Ψ
  have hsymm_eq (x : V) (hx : x ∈ Φ.source) :
      Ψ_Ω.toPartialEquiv.symm (Φ x) = ⟨x, hΦ_sub_Ω hx⟩ := by
    have hsymm := hΦ_symm (Φ x) (Φ.map_source hx)
    have hleft : Φ.symm (Φ x) = x := Φ.left_inv hx
    rw [hleft, PartialDiffeomorph.symm_toPartialEquiv] at hsymm
    exact Subtype.ext hsymm.symm
  have hmem_src (x : V) (hx : x ∈ Φ.source) : (⟨x, hΦ_sub_Ω hx⟩ : Ω) ∈ Ψ_Ω.source :=
    hsymm_eq x hx ▸ Ψ_Ω.map_target (hΦ_tgt (Φ.map_source hx))
  have heq_on (x : V) (hx : x ∈ Φ.source) : Φ x = Ψ_Ω ⟨x, hΦ_sub_Ω hx⟩ := by
    rw [← hsymm_eq x hx, Ψ_Ω.right_inv (hΦ_tgt (Φ.map_source hx))]
  refine ⟨Φ, hΦ_sub_Ω, hx₀_Φ, hΦ_p₀, fun x hx ↦ ⟨hmem_src x hx, heq_on x hx, fun v ↦ ?_⟩⟩
  set y : Ω := ⟨x, hΦ_sub_Ω hx⟩
  have hev_Ψ : (Φ ∘ (Subtype.val : Ω → V)) =ᶠ[𝓝 y] Ψ_Ω := by
    filter_upwards [(Φ.open_source.preimage continuous_subtype_val).mem_nhds hx] with z hz
    exact heq_on z.1 hz
  have hdΦ : DifferentiableAt ℝ Φ y.1 :=
    (contMDiffAt_iff_contDiffAt.1
      ((Φ.contMDiffOn x hx).contMDiffAt (Φ.open_source.mem_nhds hx))).differentiableAt (by simp)
  let v_y : TangentSpace 𝓘(ℝ, V) y := v
  exact ((mvfderiv_comp_apply_of_differentiableAt hdΦ
    (contMDiff_subtype_val.mdifferentiableAt one_ne_zero) v_y).trans
    (congrArg (fderiv ℝ Φ y.1) (Manifold.mvfderiv_subtype_val_apply y v_y))).symm.trans
    (congrArg (· v_y) (hev_Ψ.mvfderiv_eq (I := 𝓘(ℝ, V))))

/-- **The strict contact Darboux theorem on finite-dimensional normed spaces.** Let `α` be a smooth
one-form on an open set `W ⊆ V` which is a contact form at `x₀ ∈ W`. Then there are `n` with
`dim V = 2 n + 1` and a centered smooth partial diffeomorphism `Φ` from `V` to `ℝⁿ × ℝⁿ × ℝ` with
`x₀ ∈ Φ.source ⊆ W` pulling `innerProductContactForm` back to `α` on `Φ.source`. -/
theorem exists_partialDiffeomorph_strictDarboux_modelSpace {W : Set V} (hW : IsOpen W) {x₀ : V}
    (hx₀ : x₀ ∈ W) {α : V → V [⋀^Fin 1]→L[ℝ] ℝ} (hα : ContDiffOn ℝ ∞ α W)
    (hc : IsContactFormAt (I := 𝓘(ℝ, V)) α x₀) :
    ∃ (n : ℕ) (Φ : PartialDiffeomorph 𝓘(ℝ, V)
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) V
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞),
      finrank ℝ V = 2 * n + 1 ∧ x₀ ∈ Φ.source ∧ Φ.source ⊆ W ∧ Φ x₀ = 0 ∧
      ∀ x ∈ Φ.source, ∀ v : V,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (Φ x) ![fderiv ℝ Φ x v] =
          α x ![v] := by
  obtain ⟨Ω, p₀, α_glob, α_Ω, hp₀, hΩW, hα_def, hα_Ω, hα_eq⟩ :=
    exists_smoothContactForm_opens_ball hW hx₀ hα hc
  obtain ⟨K, _, S', s₀', θ', G_Ω, D₀, hdimK, hθ', hG_ld, hG_p₀, hD₀_open, hp_D₀, hG_smooth,
    hG_pull⟩ := exists_strictContactization_slice_modelSpace p₀ α_glob hα_def hα_Ω
  obtain ⟨n, Ψ₁, hdimS, hq₀_src, hΨ₁_0, hΨ₁_pull⟩ :=
    hθ'.exists_strictDarbouxChart_contactization (s₀', 0)
  have hdimV : finrank ℝ V = 2 * n + 1 := by omega
  let L_inv := hG_ld.localInverse
  have hp₀_src : p₀ ∈ L_inv.source := hG_p₀ ▸ hG_ld.localInverse_mem_source
  have hL_p₀ : L_inv p₀ = (s₀', 0) :=
    hG_p₀ ▸ hG_ld.localInverse_left_inv hG_ld.localInverse_mem_target
  let O_Ω : Set Ω := L_inv.source ∩ L_inv ⁻¹' D₀
  have hO_open : IsOpen O_Ω := L_inv.toOpenPartialHomeomorph.isOpen_inter_preimage hD₀_open
  let Ψ_Ω := (L_inv.restrOpen O_Ω hO_open).trans Ψ₁
  have hp₀_Ψ : p₀ ∈ Ψ_Ω.source := by
    simp only [Ψ_Ω, O_Ω, PartialDiffeomorph.trans_source, PartialDiffeomorph.restrOpen_source,
      PartialDiffeomorph.coe_restrOpen, mem_inter_iff, mem_preimage, hL_p₀]
    exact ⟨⟨hp₀_src, hp₀_src, hp_D₀⟩, hq₀_src⟩
  obtain ⟨Φ, hΦ_sub_Ω, hx₀_Φ, hΦ_p₀, hΦ_eq⟩ := exists_ambient_fderiv_of_opens Ψ_Ω hp₀_Ψ
  have hΦ_x₀ : Φ x₀ = 0 := by
    rw [← hp₀, hΦ_p₀, PartialDiffeomorph.coe_trans, Function.comp_apply,
      PartialDiffeomorph.coe_restrOpen, hL_p₀, hΨ₁_0]
  refine ⟨n, Φ, hdimV, hp₀ ▸ hx₀_Φ, hΦ_sub_Ω.trans hΩW, hΦ_x₀, fun x hx v ↦ ?_⟩
  obtain ⟨hy_Ψ_src, hΦ_val, hdfΦ⟩ := hΦ_eq x hx
  set y : Ω := ⟨x, hΦ_sub_Ω hx⟩
  let v_y : TangentSpace 𝓘(ℝ, V) y := v
  have hy_mem : (y ∈ L_inv.source ∧ y ∈ O_Ω) ∧ L_inv y ∈ Ψ₁.source := by
    simpa only [Ψ_Ω, PartialDiffeomorph.trans_source, PartialDiffeomorph.restrOpen_source,
      PartialDiffeomorph.coe_restrOpen, mem_inter_iff, mem_preimage] using hy_Ψ_src
  obtain ⟨⟨hy_Linv, hy_Linv_O⟩, hLy_Ψ₁⟩ := hy_mem
  set q : S' × ℝ := L_inv y
  have hGq : G_Ω q = y := hG_ld.localInverse_right_inv hy_Linv
  have hdG : MDifferentiableAt (𝓘(ℝ, K).prod 𝓘(ℝ)) 𝓘(ℝ, V) G_Ω q :=
    (hG_smooth q hy_Linv_O.2).mdifferentiableAt (by simp)
  have hdL : MDifferentiableAt 𝓘(ℝ, V) (𝓘(ℝ, K).prod 𝓘(ℝ)) (⇑L_inv) y :=
    ((L_inv.contMDiffOn y hy_Linv).contMDiffAt
      (L_inv.open_source.mem_nhds hy_Linv)).mdifferentiableAt (by simp)
  set w : TangentSpace (𝓘(ℝ, K).prod 𝓘(ℝ)) q :=
    mfderiv 𝓘(ℝ, V) (𝓘(ℝ, K).prod 𝓘(ℝ)) (⇑L_inv) y v_y
  have hGw : mfderiv (𝓘(ℝ, K).prod 𝓘(ℝ)) 𝓘(ℝ, V) G_Ω q w = v := by
    have hev_val : ((Subtype.val : Ω → V) ∘ G_Ω) ∘ (⇑L_inv) =ᶠ[𝓝 y] Subtype.val :=
      eventually_of_mem (L_inv.open_source.mem_nhds hy_Linv)
        fun z hz ↦ congrArg Subtype.val (hG_ld.localInverse_right_inv hz)
    have hid := congrArg (· v_y) (hev_val.mvfderiv_eq (I := 𝓘(ℝ, V)))
    have hdG_val : MDifferentiableAt (𝓘(ℝ, K).prod 𝓘(ℝ)) 𝓘(ℝ, V)
        ((Subtype.val : Ω → V) ∘ G_Ω) (L_inv y) :=
      Manifold.mdifferentiableAt_subtype_val_comp_iff.2 hdG
    rw [Manifold.mvfderiv_subtype_val_apply, mvfderiv_apply_eq_mfderiv_apply,
      mfderiv_comp y hdG_val hdL, ContinuousLinearMap.comp_apply,
      Manifold.mfderiv_subtype_val_comp_apply] at hid
    exact hid
  have hdΨ₁ : MDifferentiableAt (𝓘(ℝ, K).prod 𝓘(ℝ)) _ (⇑Ψ₁) (L_inv y) :=
    ((Ψ₁.contMDiffOn q hLy_Ψ₁).contMDiffAt (Ψ₁.open_source.mem_nhds hLy_Ψ₁)).mdifferentiableAt
      (by simp)
  have hΨ_def : (⇑Ψ_Ω : Ω → _) = (⇑Ψ₁) ∘ (⇑L_inv) := by
    rw [PartialDiffeomorph.coe_trans, PartialDiffeomorph.coe_restrOpen]
  have hdfΨ : mvfderiv 𝓘(ℝ, V) Ψ_Ω y v_y = mvfderiv (𝓘(ℝ, K).prod 𝓘(ℝ)) Ψ₁ q w := by
    refine (congrArg (fun g ↦ mvfderiv 𝓘(ℝ, V) g y v_y) hΨ_def).trans ?_
    rw [mvfderiv_apply_eq_mfderiv_apply, mfderiv_comp y hdΨ₁ hdL,
      ContinuousLinearMap.comp_apply, ← mvfderiv_apply_eq_mfderiv_apply]
  have hpull_q := congrArg (· ![w]) (hG_pull q hy_Linv_O.2)
  have hvecG : (fun i : Fin 1 ↦ mfderiv (𝓘(ℝ, K).prod 𝓘(ℝ)) 𝓘(ℝ, V) G_Ω q (![w] i)) = ![v] := by
    ext i; fin_cases i; exact hGw
  rw [mpullback_apply, hvecG, hGq, hα_eq y] at hpull_q
  have hval_Ψ : Φ x = Ψ₁ q := by rw [hΦ_val, hΨ_def, Function.comp_apply]
  have hmv_Ψ : fderiv ℝ Φ x v = mvfderiv (𝓘(ℝ, K).prod 𝓘(ℝ)) Ψ₁ q w := (hdfΦ v).trans hdfΨ
  refine (innerProductContactForm_apply (EuclideanSpace ℝ (Fin n)) (Φ x)
    (fderiv ℝ Φ x v)).trans ?_
  rw [hval_Ψ, hmv_Ψ]
  exact (innerProductContactForm_apply (EuclideanSpace ℝ (Fin n)) (Ψ₁ q)
    (mvfderiv (𝓘(ℝ, K).prod 𝓘(ℝ)) Ψ₁ q w)).symm.trans
    ((hΨ₁_pull q hLy_Ψ₁ w).trans hpull_q.symm)

end ModelSpace

/-! ### Strict contact Darboux charts on manifolds -/

section Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **The strict contact Darboux theorem** for a locally defined one-form. Let `α` be a one-form on
`M` which is smooth on an open set `U` and is a contact form at an interior point `x₀ ∈ U`. Then
there are `n` with `dim E = 2 n + 1` and a smooth partial diffeomorphism `chart` from `M` to
`ℝⁿ × ℝⁿ × ℝ` with `x₀ ∈ chart.source ⊆ U` and `chart x₀ = 0` pulling the standard contact form
`dz - Σᵢ pᵢ dqᵢ` back to `α` itself on `chart.source`. -/
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
  have : IsManifold I 1 M := .of_le (n := ∞) (by simp)
  have : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := .of_le (n := ∞) (by simp)
  set e := extChartAt I x₀
  set W : Set E := interior e.target ∩ e.symm ⁻¹' U
  have hW : IsOpen W :=
    ((continuousOn_extChartAt_symm x₀).mono interior_subset).isOpen_inter_preimage
      isOpen_interior hU
  have hy₀W : e x₀ ∈ W :=
    ⟨I.isInteriorPoint_iff.1 hx₀, by rw [mem_preimage, extChartAt_to_inv]; exact hx₀U⟩
  have hη : ContDiffOn ℝ ∞ (α.inChartAt x₀) W := α.contDiffOn_inChartAt_of_contMDiffOn hU hα x₀
  obtain ⟨n, Φ, hdim, hy₀_Φ, hΦW, hΦ₀, hΦ_pull⟩ :=
    exists_partialDiffeomorph_strictDarboux_modelSpace hW hy₀W hη
      ((isContactFormAt_inChartAt_iff hx₀).2 hc)
  let e₀ := extChartPartialDiffeomorph I ∞ x₀
  let chart := e₀.trans Φ
  have hx₀_e₀ : x₀ ∈ e₀.source := (mem_extChartPartialDiffeomorph_source I ∞ x₀).2 hx₀
  have hx₀_src : x₀ ∈ chart.source := by
    rw [PartialDiffeomorph.trans_source, mem_inter_iff, mem_preimage,
      coe_extChartPartialDiffeomorph]
    exact ⟨hx₀_e₀, hy₀_Φ⟩
  refine ⟨n, chart, hdim, hx₀_src, fun x hx ↦ ?_, ?_, fun x hx v ↦ ?_⟩
  · rw [PartialDiffeomorph.trans_source, extChartPartialDiffeomorph_source,
      coe_extChartPartialDiffeomorph] at hx
    have hU' := (hΦW hx.2).2
    rwa [mem_preimage, e.left_inv hx.1.1] at hU'
  · rw [PartialDiffeomorph.coe_trans, Function.comp_apply, coe_extChartPartialDiffeomorph, hΦ₀]
  · rw [PartialDiffeomorph.trans_source, extChartPartialDiffeomorph_source,
      coe_extChartPartialDiffeomorph] at hx
    have hx_chart : x ∈ (chartAt H x₀).source := by simpa only [extChartAt_source] using hx.1.1
    have hdΦ : DifferentiableAt ℝ Φ (e x) :=
      (contMDiffAt_iff_contDiffAt.1
        ((Φ.contMDiffOn (e x) hx.2).contMDiffAt (Φ.open_source.mem_nhds hx.2))).differentiableAt
        (by simp)
    have hcomp : ⇑chart = ⇑Φ ∘ ⇑e := by
      rw [PartialDiffeomorph.coe_trans, coe_extChartPartialDiffeomorph]
    have hval : chart x = Φ (e x) := congrFun hcomp x
    have hmv : mvfderiv I chart x v = fderiv ℝ Φ (e x) (mvfderiv I e x v) := by
      rw [hcomp]
      exact mvfderiv_comp_apply_of_differentiableAt hdΦ (mdifferentiableAt_extChartAt hx_chart) v
    have hvec : (fun i : Fin 1 ↦ mvfderiv I e x (![v] i)) = ![mvfderiv I e x v] := by
      ext i; fin_cases i; rfl
    refine (innerProductContactForm_apply (EuclideanSpace ℝ (Fin n)) (chart x)
      (mvfderiv I chart x v)).trans ?_
    rw [hval, hmv]
    exact (innerProductContactForm_apply (EuclideanSpace ℝ (Fin n)) (Φ (e x))
      (fderiv ℝ Φ (e x) (mvfderiv I e x v))).symm.trans
      ((hΦ_pull (e x) hx.2 (mvfderiv I e x v)).trans
        (by rw [RoughForm.apply_eq_inChartAt_mvfderiv α hx.1.1, hvec]))

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- A partial diffeomorphism from a manifold of dimension `2 n + 1` to `ℝᵐ × ℝᵐ × ℝ` with nonempty
source forces `m = n`. -/
private theorem eq_of_finrank_eq_of_mem_source {m n : ℕ}
    (chart : PartialDiffeomorph I
      𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) × ℝ) M
      (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) × ℝ) ∞)
    {x : M} (hx : x ∈ chart.source) (hn : finrank ℝ E = 2 * n + 1) : m = n := by
  have hL : finrank ℝ E =
      finrank ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) × ℝ) :=
    ((chart.isLocalDiffeomorphAt _ _ _ hx).mfderivToContinuousLinearEquiv
      (by simp)).toLinearEquiv.finrank_eq
  rw [finrank_prod, finrank_prod, finrank_euclideanSpace_fin, finrank_self] at hL
  omega

/-- **The strict contact Darboux theorem at an interior point, in dimension `2 n + 1`.** -/
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
  obtain ⟨m, chart, -, hx₀', h⟩ := hc.exists_strictDarbouxChart_of_isInteriorPoint hU hx₀U hα hx₀
  obtain rfl := eq_of_finrank_eq_of_mem_source chart hx₀' hn
  exact ⟨chart, hx₀', h⟩

/-- **The strict contact Darboux theorem at an interior point** for a smooth contact form `α`:
around any interior point `x₀`, there are `n` with `dim E = 2 n + 1` and a centered smooth partial
diffeomorphism `chart` into `ℝⁿ × ℝⁿ × ℝ` pulling `innerProductContactForm` back to `α` and
straightening `α.reebVectorField` to `(0, 0, 1)`. -/
theorem SmoothForm.IsContactForm.exists_strictDarbouxChart_of_isInteriorPoint
    {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm) {x₀ : M} (hx₀ : I.IsInteriorPoint x₀) :
    ∃ (n : ℕ) (chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞),
      finrank ℝ E = 2 * n + 1 ∧ x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      (∀ x ∈ chart.source, ∀ v : TangentSpace I x,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (chart x)
          ![mvfderiv I chart x v] = α.1 x ![v]) ∧
      ∀ x ∈ chart.source, mvfderiv I chart x (α.reebVectorField x) = (0, 0, 1) := by
  have : IsManifold I 2 M := .of_le (n := ∞) (by simp)
  obtain ⟨n, chart, hdim, hx₀', -, h0, hchart⟩ :=
    (isContactForm_iff_forall_isContactFormAt.1 hα x₀).exists_strictDarbouxChart_of_isInteriorPoint
      isOpen_univ (mem_univ x₀) α.contMDiff.contMDiffOn hx₀
  exact ⟨n, chart, hdim, hx₀', h0, hchart,
    fun x hx ↦ hα.mvfderiv_reebVectorField_of_innerProductContactForm chart hchart hx⟩

/-- **The strict contact Darboux theorem at an interior point, in dimension `2 n + 1`.** -/
theorem SmoothForm.IsContactForm.exists_strictDarbouxChart_of_finrank_eq_of_isInteriorPoint
    {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm) {n : ℕ} (hn : finrank ℝ E = 2 * n + 1)
    {x₀ : M} (hx₀ : I.IsInteriorPoint x₀) :
    ∃ chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞,
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      (∀ x ∈ chart.source, ∀ v : TangentSpace I x,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (chart x)
          ![mvfderiv I chart x v] = α.1 x ![v]) ∧
      ∀ x ∈ chart.source, mvfderiv I chart x (α.reebVectorField x) = (0, 0, 1) := by
  obtain ⟨m, chart, -, hx₀', h⟩ := hα.exists_strictDarbouxChart_of_isInteriorPoint hx₀
  obtain rfl := eq_of_finrank_eq_of_mem_source chart hx₀' hn
  exact ⟨chart, hx₀', h⟩

namespace SmoothForm.IsContactForm

/-- **Local strict contactomorphism to standard contact space at an interior point.** Around any
interior point `x₀`, there are an open neighbourhood `U` of `x₀`, an open neighbourhood `W` of `0`
in `ℝⁿ × ℝⁿ × ℝ`, and a centered diffeomorphism `e : U ≃ₘ W` which is a strict contactomorphism
between the restrictions of `α` and `innerProductContactForm`. -/
theorem exists_isStrictContactomorphism_opens_of_isInteriorPoint
    {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm) {x₀ : M} (hx₀ : I.IsInteriorPoint x₀) :
    ∃ (n : ℕ) (U : Opens M) (hx₀U : x₀ ∈ U)
      (W : Opens (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ))
      (e : U ≃ₘ⟮I, 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ)⟯ W),
      finrank ℝ E = 2 * n + 1 ∧
      (e ⟨x₀, hx₀U⟩ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) = 0 ∧
      e.IsStrictContactomorphism
        (SmoothForm.mpullback Subtype.val contMDiff_subtype_val α)
        (SmoothForm.mpullback Subtype.val contMDiff_subtype_val
          (innerProductContactForm (EuclideanSpace ℝ (Fin n)))) := by
  obtain ⟨n, chart, hdim, hx₀', h0, hchart, -⟩ :=
    hα.exists_strictDarbouxChart_of_isInteriorPoint hx₀
  refine ⟨n, ⟨chart.source, chart.open_source⟩, hx₀', ⟨chart.target, chart.open_target⟩,
    chart.toDiffeomorphSourceTarget, hdim, by simpa using h0, ?_⟩
  exact (chart.isStrictContactomorphism_toDiffeomorphSourceTarget_iff α
    (innerProductContactForm (EuclideanSpace ℝ (Fin n)))).2 fun x hx v ↦ by
      rw [← mvfderiv_apply_eq_mfderiv_apply]
      exact hchart x hx v

/-- **Local strict contactomorphism to standard contact space in dimension `2 n + 1` at an interior
point.** -/
theorem exists_isStrictContactomorphism_opens_of_finrank_eq_of_isInteriorPoint
    {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm) {n : ℕ} (hn : finrank ℝ E = 2 * n + 1)
    {x₀ : M} (hx₀ : I.IsInteriorPoint x₀) :
    ∃ (U : Opens M) (hx₀U : x₀ ∈ U)
      (W : Opens (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ))
      (e : U ≃ₘ⟮I, 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ)⟯ W),
      (e ⟨x₀, hx₀U⟩ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) = 0 ∧
      e.IsStrictContactomorphism
        (SmoothForm.mpullback Subtype.val contMDiff_subtype_val α)
        (SmoothForm.mpullback Subtype.val contMDiff_subtype_val
          (innerProductContactForm (EuclideanSpace ℝ (Fin n)))) := by
  obtain ⟨chart, hx₀', h0, hchart, -⟩ :=
    hα.exists_strictDarbouxChart_of_finrank_eq_of_isInteriorPoint hn hx₀
  refine ⟨⟨chart.source, chart.open_source⟩, hx₀', ⟨chart.target, chart.open_target⟩,
    chart.toDiffeomorphSourceTarget, by simpa using h0, ?_⟩
  exact (chart.isStrictContactomorphism_toDiffeomorphSourceTarget_iff α
    (innerProductContactForm (EuclideanSpace ℝ (Fin n)))).2 fun x hx v ↦ by
      rw [← mvfderiv_apply_eq_mfderiv_apply]
      exact hchart x hx v

end SmoothForm.IsContactForm

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

/-- **The strict contact Darboux theorem** on a boundaryless manifold: around every point `x₀` of
`(M, α)`, there are `n` with `dim E = 2 n + 1` and a centered smooth partial diffeomorphism `chart`
into `ℝⁿ × ℝⁿ × ℝ` pulling `innerProductContactForm` back to `α` and straightening
`α.reebVectorField` to `(0, 0, 1)`. -/
theorem SmoothForm.IsContactForm.exists_strictDarbouxChart {α : SmoothForm I M ℝ 1}
    (hα : α.IsContactForm) (x₀ : M) :
    ∃ (n : ℕ) (chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞),
      finrank ℝ E = 2 * n + 1 ∧ x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      (∀ x ∈ chart.source, ∀ v : TangentSpace I x,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (chart x)
          ![mvfderiv I chart x v] = α.1 x ![v]) ∧
      ∀ x ∈ chart.source, mvfderiv I chart x (α.reebVectorField x) = (0, 0, 1) :=
  hα.exists_strictDarbouxChart_of_isInteriorPoint BoundarylessManifold.isInteriorPoint

/-- **The strict contact Darboux theorem in dimension `2 n + 1`** on a boundaryless manifold. -/
theorem SmoothForm.IsContactForm.exists_strictDarbouxChart_of_finrank_eq {α : SmoothForm I M ℝ 1}
    (hα : α.IsContactForm) {n : ℕ} (hn : finrank ℝ E = 2 * n + 1) (x₀ : M) :
    ∃ chart : PartialDiffeomorph I
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) M
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) ∞,
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      (∀ x ∈ chart.source, ∀ v : TangentSpace I x,
        (innerProductContactForm (EuclideanSpace ℝ (Fin n))).1 (chart x)
          ![mvfderiv I chart x v] = α.1 x ![v]) ∧
      ∀ x ∈ chart.source, mvfderiv I chart x (α.reebVectorField x) = (0, 0, 1) :=
  hα.exists_strictDarbouxChart_of_finrank_eq_of_isInteriorPoint hn
    BoundarylessManifold.isInteriorPoint

/-- **Local strict contactomorphism to standard contact space** on a boundaryless manifold. -/
theorem SmoothForm.IsContactForm.exists_isStrictContactomorphism_opens {α : SmoothForm I M ℝ 1}
    (hα : α.IsContactForm) (x₀ : M) :
    ∃ (n : ℕ) (U : Opens M) (hx₀U : x₀ ∈ U)
      (W : Opens (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ))
      (e : U ≃ₘ⟮I, 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ)⟯ W),
      finrank ℝ E = 2 * n + 1 ∧
      (e ⟨x₀, hx₀U⟩ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) = 0 ∧
      e.IsStrictContactomorphism
        (SmoothForm.mpullback Subtype.val contMDiff_subtype_val α)
        (SmoothForm.mpullback Subtype.val contMDiff_subtype_val
          (innerProductContactForm (EuclideanSpace ℝ (Fin n)))) :=
  hα.exists_isStrictContactomorphism_opens_of_isInteriorPoint BoundarylessManifold.isInteriorPoint

/-- **Local strict contactomorphism to standard contact space in dimension `2 n + 1`** on a
boundaryless manifold. -/
theorem SmoothForm.IsContactForm.exists_isStrictContactomorphism_opens_of_finrank_eq
    {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm) {n : ℕ} (hn : finrank ℝ E = 2 * n + 1)
    (x₀ : M) :
    ∃ (U : Opens M) (hx₀U : x₀ ∈ U)
      (W : Opens (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ))
      (e : U ≃ₘ⟮I, 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ)⟯ W),
      (e ⟨x₀, hx₀U⟩ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) × ℝ) = 0 ∧
      e.IsStrictContactomorphism
        (SmoothForm.mpullback Subtype.val contMDiff_subtype_val α)
        (SmoothForm.mpullback Subtype.val contMDiff_subtype_val
          (innerProductContactForm (EuclideanSpace ℝ (Fin n)))) :=
  hα.exists_isStrictContactomorphism_opens_of_finrank_eq_of_isInteriorPoint hn
    BoundarylessManifold.isInteriorPoint

end Boundaryless

/-! ### Three-dimensional specialization (`dz - x dy` on `ℝ³`) -/

/-- Continuous linear equivalence `(q, p, z) ↦ (p 0, q 0, z)` identifying the `n = 1` Euclidean
standard contact model with `ℝ × ℝ × ℝ` carrying `standardContactForm` (`dz - x dy`). -/
private def strictStandardSwapEquiv :
    (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) × ℝ) ≃L[ℝ] (ℝ × ℝ × ℝ) :=
  let e₁ : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ := PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)
  (e₁.prodCongr (e₁.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ))).trans
    ((ContinuousLinearEquiv.prodAssoc ℝ ℝ ℝ ℝ).symm.trans
      (((ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).prodCongr
        (ContinuousLinearEquiv.refl ℝ ℝ)).trans
        (ContinuousLinearEquiv.prodAssoc ℝ ℝ ℝ ℝ)))

private theorem standardContactForm_apply_strictStandardSwapEquiv
    (u w : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1) × ℝ) :
    standardContactForm.1 (strictStandardSwapEquiv u) ![strictStandardSwapEquiv w] =
      (innerProductContactForm (EuclideanSpace ℝ (Fin 1))).1 u ![w] :=
  (standardContactForm_apply (strictStandardSwapEquiv u) (strictStandardSwapEquiv w)).trans
    ((by simp [strictStandardSwapEquiv] :
      (strictStandardSwapEquiv w).2.2 -
        (strictStandardSwapEquiv u).1 * (strictStandardSwapEquiv w).2.1 =
      w.2.2 - ∑ i : Fin 1, u.2.1.ofLp i * w.1.ofLp i).trans
      (innerProductContactForm_euclideanSpace_apply u w).symm)

/-- **Three-dimensional strict contact Darboux theorem** at an interior point for a locally defined
one-form, landing in `ℝ × ℝ × ℝ` with `standardContactForm` (`dz - x dy`). -/
theorem IsContactFormAt.exists_strictStandardDarbouxChart_of_isInteriorPoint
    {α : RoughForm I M ℝ 1} {U : Set M} {x₀ : M} (hc : IsContactFormAt α x₀)
    (hdim : finrank ℝ E = 3) (hU : IsOpen U) (hx₀U : x₀ ∈ U)
    (hα : ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) U)
    (hx₀ : I.IsInteriorPoint x₀) :
    ∃ chart : PartialDiffeomorph I 𝓘(ℝ, ℝ × ℝ × ℝ) M (ℝ × ℝ × ℝ) ∞,
      x₀ ∈ chart.source ∧ chart.source ⊆ U ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, ∀ v : TangentSpace I x,
        standardContactForm.1 (chart x) ![mvfderiv I chart x v] = α x ![v] := by
  have : IsManifold I 1 M := .of_le (n := ∞) (by simp)
  obtain ⟨chart₀, hx₀', hsU, h0, hpull⟩ :=
    hc.exists_strictDarbouxChart_of_finrank_eq_of_isInteriorPoint (n := 1) (by omega) hU hx₀U hα hx₀
  let chart := chart₀.trans (strictStandardSwapEquiv.toPartialDiffeomorph (n := ∞))
  have hsrc : chart.source = chart₀.source := by simp [chart]
  have hcoe (y : M) : chart y = strictStandardSwapEquiv (chart₀ y) := by simp [chart]
  refine ⟨chart, hsrc.symm ▸ hx₀', hsrc ▸ hsU, by rw [hcoe, h0, map_zero], fun x hx v ↦ ?_⟩
  have hx₀_src : x ∈ chart₀.source := hsrc ▸ hx
  have hd : MDifferentiableAt I _ chart₀ x :=
    ((chart₀.contMDiffOn x hx₀_src).contMDiffAt
      (chart₀.open_source.mem_nhds hx₀_src)).mdifferentiableAt (by simp)
  have hmv : mvfderiv I chart x v = strictStandardSwapEquiv (mvfderiv I chart₀ x v) := by
    have hcomp : ⇑chart = strictStandardSwapEquiv.toContinuousLinearMap ∘ ⇑chart₀ := funext hcoe
    rw [hcomp]
    exact strictStandardSwapEquiv.toContinuousLinearMap.mvfderiv_comp_apply hd v
  refine (standardContactForm_apply (chart x) (mvfderiv I chart x v)).trans ?_
  rw [hcoe, hmv]
  exact (standardContactForm_apply (strictStandardSwapEquiv (chart₀ x))
    (strictStandardSwapEquiv (mvfderiv I chart₀ x v))).symm.trans
    ((standardContactForm_apply_strictStandardSwapEquiv (chart₀ x)
      (mvfderiv I chart₀ x v)).trans (hpull x hx₀_src v))

/-- **Three-dimensional strict contact Darboux theorem** at an interior point for a smooth contact
form `α`, pulling `standardContactForm` (`dz - x dy`) back to `α` and straightening
`α.reebVectorField` to `standardReebField` (`∂_z`). -/
theorem SmoothForm.IsContactForm.exists_strictStandardDarbouxChart_of_isInteriorPoint
    {α : SmoothForm I M ℝ 1} (hα : α.IsContactForm) (hdim : finrank ℝ E = 3) {x₀ : M}
    (hx₀ : I.IsInteriorPoint x₀) :
    ∃ chart : PartialDiffeomorph I 𝓘(ℝ, ℝ × ℝ × ℝ) M (ℝ × ℝ × ℝ) ∞,
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      (∀ x ∈ chart.source, ∀ v : TangentSpace I x,
        standardContactForm.1 (chart x) ![mvfderiv I chart x v] = α.1 x ![v]) ∧
      ∀ x ∈ chart.source,
        mvfderiv I chart x (α.reebVectorField x) = standardReebField (chart x) := by
  have : IsManifold I 2 M := .of_le (n := ∞) (by simp)
  obtain ⟨chart, hx₀', -, h0, hchart⟩ :=
    (isContactForm_iff_forall_isContactFormAt.1 hα
      x₀).exists_strictStandardDarbouxChart_of_isInteriorPoint hdim isOpen_univ (mem_univ x₀)
      α.contMDiff.contMDiffOn hx₀
  exact ⟨chart, hx₀', h0, hchart,
    fun x hx ↦ hα.mvfderiv_reebVectorField_of_standardContactForm chart hchart hx⟩

section BoundarylessThreeDim

variable [BoundarylessManifold I M]

/-- **Three-dimensional strict contact Darboux theorem** on a boundaryless manifold for a locally
defined one-form. -/
theorem IsContactFormAt.exists_strictStandardDarbouxChart {α : RoughForm I M ℝ 1} {U : Set M}
    {x₀ : M} (hc : IsContactFormAt α x₀) (hdim : finrank ℝ E = 3) (hU : IsOpen U) (hx₀U : x₀ ∈ U)
    (hα : ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) ∞
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) U) :
    ∃ chart : PartialDiffeomorph I 𝓘(ℝ, ℝ × ℝ × ℝ) M (ℝ × ℝ × ℝ) ∞,
      x₀ ∈ chart.source ∧ chart.source ⊆ U ∧ chart x₀ = 0 ∧
      ∀ x ∈ chart.source, ∀ v : TangentSpace I x,
        standardContactForm.1 (chart x) ![mvfderiv I chart x v] = α x ![v] :=
  hc.exists_strictStandardDarbouxChart_of_isInteriorPoint hdim hU hx₀U hα
    BoundarylessManifold.isInteriorPoint

/-- **Three-dimensional strict contact Darboux theorem** on a boundaryless `3`-manifold: around
every point `x₀`, there is a centered smooth partial diffeomorphism `chart` into `ℝ × ℝ × ℝ`
pulling `standardContactForm` (`dz - x dy`) back to `α` and straightening `α.reebVectorField` to
`standardReebField` (`∂_z`). -/
theorem SmoothForm.IsContactForm.exists_strictStandardDarbouxChart {α : SmoothForm I M ℝ 1}
    (hα : α.IsContactForm) (hdim : finrank ℝ E = 3) (x₀ : M) :
    ∃ chart : PartialDiffeomorph I 𝓘(ℝ, ℝ × ℝ × ℝ) M (ℝ × ℝ × ℝ) ∞,
      x₀ ∈ chart.source ∧ chart x₀ = 0 ∧
      (∀ x ∈ chart.source, ∀ v : TangentSpace I x,
        standardContactForm.1 (chart x) ![mvfderiv I chart x v] = α.1 x ![v]) ∧
      ∀ x ∈ chart.source,
        mvfderiv I chart x (α.reebVectorField x) = standardReebField (chart x) :=
  hα.exists_strictStandardDarbouxChart_of_isInteriorPoint hdim BoundarylessManifold.isInteriorPoint

end BoundarylessThreeDim

end Manifold

end TauCeti
