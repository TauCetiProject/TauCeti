/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SymmetricPower.Manifold
public import Mathlib.Geometry.Manifold.SmoothEmbedding
import TauCeti.Analysis.Polynomial.SymmetricPower.Cons
import TauCeti.Geometry.Manifold.Immersion.Differential
import TauCeti.Topology.Sym.Cons

/-!
# Adjoining a point to a symmetric power of a complex curve

In disjoint coordinate patches shared by the source and target, adjoining a fixed point changes
only the block containing that point. On that block it is fixed-root insertion in coefficient
coordinates. The source block may have degree zero; repeated points cause no loss of regularity.

The resulting analytic embedding parametrizes the basepoint divisor of the symmetric power,
as in Ozsváth–Szabó, *Holomorphic disks and topological invariants for closed three-manifolds*
([arXiv:math/0101206](https://arxiv.org/abs/math/0101206)), §2.2. The local calculation uses
`TauCeti.Sym.analyticAt_coeffEquiv_cons_coeffEquiv_symm`.
-/

public section

open Filter Set Topology Polynomial Manifold
open scoped ContDiff Manifold

namespace TauCeti

variable {α ι : Type*} [TopologicalSpace α] [Fintype ι] {n : ℕ}

private def consDegrees (m : Option ι → ℕ) : Option ι → ℕ
  | none => m none + 1
  | some i => m (some i)

private def consParts {V : Option ι → Set α} {m : Option ι → ℕ}
    (z : V none) (q : ∀ i, Sym (V i) (m i)) : ∀ i, Sym (V i) (consDegrees m i)
  | none => Sym.cons z (q none)
  | some i => q (some i)

omit [TopologicalSpace α] in
private theorem sumSubtype_consParts {V : Option ι → Set α} {m : Option ι → ℕ}
    (hm : ∑ i, m i = n) (hp : ∑ i, consDegrees m i = n + 1)
    (z : V none) (q : ∀ i, Sym (V i) (m i)) :
    Sym.sumSubtype V (consDegrees m) hp (consParts z q) =
      Sym.cons (z : α) (Sym.sumSubtype V m hm q) := by
  apply _root_.Sym.coe_injective
  simp [Sym.coe_sumSubtype, Fintype.sum_option, consParts, consDegrees,
    _root_.Sym.coe_cons, Multiset.cons_add]

private noncomputable def consBlock (m : Option ι → ℕ) (a : ℂ)
    (c : ∀ i, Fin (m i) → ℂ) : ∀ i, Fin (consDegrees m i) → ℂ
  | none => Sym.coeffEquiv ℂ (m none + 1)
      (Sym.cons a ((Sym.coeffEquiv ℂ (m none)).symm (c none)))
  | some i => c (some i)

private theorem analyticAt_consBlock (m : Option ι → ℕ) (a : ℂ)
    (c : ∀ i, Fin (m i) → ℂ) : AnalyticAt ℂ (consBlock m a) c := by
  refine AnalyticAt.pi fun i => ?_
  cases i with
  | none =>
    exact (Sym.analyticAt_coeffEquiv_cons_coeffEquiv_symm a (c none)).comp
      (f := fun x : (∀ i, Fin (m i) → ℂ) => x none)
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun i => Fin (m i) → ℂ) none).analyticAt c)
  | some i =>
    exact (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun i => Fin (m i) → ℂ) (some i)).analyticAt c

private theorem fderiv_consBlock_injective (m : Option ι → ℕ) (a : ℂ)
    (c : ∀ i, Fin (m i) → ℂ) :
    Function.Injective (fderiv ℂ (consBlock m a) c) := by
  classical
  have ha := (analyticAt_consBlock m a c).differentiableAt
  intro u v huv
  funext i
  have hcoord := congrArg (fun w => w i) huv
  have hcomp := fderiv_apply ha i
  have heq : (fderiv ℂ (fun x => consBlock m a x i) c) u =
      (fderiv ℂ (fun x => consBlock m a x i) c) v := by
    simpa only [hcomp, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using hcoord
  cases i with
  | none =>
    let P : (∀ i, Fin (m i) → ℂ) →L[ℂ] (Fin (m none) → ℂ) :=
      ContinuousLinearMap.proj none
    have hderiv := ((Sym.analyticAt_coeffEquiv_cons_coeffEquiv_symm a (c none)).differentiableAt.hasFDerivAt.comp c P.hasFDerivAt).fderiv
    have hd : fderiv ℂ (fun x => consBlock m a x none) c =
        (fderiv ℂ (fun d => Sym.coeffEquiv ℂ (m none + 1)
          (Sym.cons a ((Sym.coeffEquiv ℂ (m none)).symm d))) (c none)).comp P := hderiv
    rw [hd] at heq
    exact Sym.fderiv_coeffEquiv_cons_coeffEquiv_symm_injective a (c none) heq
  | some i =>
    have hd := (ContinuousLinearMap.proj (R := ℂ)
      (φ := fun i => Fin (m i) → ℂ) (some i)).hasFDerivAt.fderiv (x := c)
    have hd' : fderiv ℂ (fun x => consBlock m a x (some i)) c =
        ContinuousLinearMap.proj (R := ℂ) (φ := fun i => Fin (m i) → ℂ) (some i) := hd
    rw [hd'] at heq
    exact heq

private theorem symOpenPartialHomeomorph_cons_apply
    (φ : Option ι → OpenPartialHomeomorph α ℂ) (V : Option ι → Set α)
    (m : Option ι → ℕ) (hm : ∑ i, m i = n) (hp : ∑ i, consDegrees m i = n + 1)
    (hVo : ∀ i, IsOpen (V i)) (hVsub : ∀ i, V i ⊆ (φ i).source)
    (hVdisj : Pairwise (Function.onFun Disjoint V))
    (e : (Σ i, Fin (m i)) ≃ Fin n)
    (e' : (Σ i, Fin (consDegrees m i)) ≃ Fin (n + 1))
    (hq : Nonempty (∀ i, Sym (V i) (m i)))
    (hr : Nonempty (∀ i, Sym (V i) (consDegrees m i)))
    (z : V none) (q : ∀ i, Sym (V i) (m i)) :
    symOpenPartialHomeomorph φ V (consDegrees m) hp hVo hVsub hVdisj e' hr
        (Sym.cons (z : α) (Sym.sumSubtype V m hm q)) =
      piSigmaConstHomeomorph ℂ e' (consBlock m (φ none z)
        ((piSigmaConstHomeomorph ℂ e).symm
          (symOpenPartialHomeomorph φ V m hm hVo hVsub hVdisj e hq
            (Sym.sumSubtype V m hm q)))) := by
  rw [← sumSubtype_consParts hm hp z q, symOpenPartialHomeomorph_apply,
    symOpenPartialHomeomorph_apply, Homeomorph.symm_apply_apply]
  apply congrArg (piSigmaConstHomeomorph ℂ e')
  funext i
  cases i <;> simp [consParts, consBlock, consDegrees, _root_.Sym.map_cons] <;> rfl

private theorem analyticAt_cons_coordinates (m : Option ι → ℕ)
    (e : (Σ i, Fin (m i)) ≃ Fin n)
    (e' : (Σ i, Fin (consDegrees m i)) ≃ Fin (n + 1)) (a : ℂ) (c : Fin n → ℂ) :
    AnalyticAt ℂ (fun x => piSigmaConstHomeomorph ℂ e'
      (consBlock m a ((piSigmaConstHomeomorph ℂ e).symm x))) c ∧
    Function.Injective (fderiv ℂ (fun x => piSigmaConstHomeomorph ℂ e'
      (consBlock m a ((piSigmaConstHomeomorph ℂ e).symm x))) c) := by
  classical
  let E := ((LinearEquiv.piCurry ℂ (fun (_ : Option ι) _ => ℂ)).symm.trans
    (LinearEquiv.piCongrLeft' ℂ (fun _ => ℂ) e)).toContinuousLinearEquiv
  let E' := ((LinearEquiv.piCurry ℂ (fun (_ : Option ι) _ => ℂ)).symm.trans
    (LinearEquiv.piCongrLeft' ℂ (fun _ => ℂ) e')).toContinuousLinearEquiv
  have hE : (E : (∀ i, Fin (m i) → ℂ) → Fin n → ℂ) = piSigmaConstHomeomorph ℂ e := by
    ext x i
    rw [piSigmaConstHomeomorph_apply]
    rfl
  have hE' : (E' : (∀ i, Fin (consDegrees m i) → ℂ) → Fin (n + 1) → ℂ) =
      piSigmaConstHomeomorph ℂ e' := by
    ext x i
    rw [piSigmaConstHomeomorph_apply]
    rfl
  have hEinv : (E.symm : (Fin n → ℂ) → ∀ i, Fin (m i) → ℂ) =
      (piSigmaConstHomeomorph ℂ e).symm := by
    funext x
    apply E.injective
    rw [E.apply_symm_apply, hE, Homeomorph.apply_symm_apply]
  have ha := analyticAt_consBlock m a ((piSigmaConstHomeomorph ℂ e).symm c)
  refine ⟨(analyticAt_piSigmaConstHomeomorph e' _).comp
    (ha.comp (analyticAt_piSigmaConstHomeomorph_symm e c)), ?_⟩
  have ha' : AnalyticAt ℂ (consBlock m a) (E.symm c) := by rwa [hEinv]
  have hd := (E'.hasFDerivAt.comp _
    (ha'.differentiableAt.hasFDerivAt.comp c E.symm.hasFDerivAt)).fderiv
  simp only [hEinv, hE', Function.comp_def] at hd
  rw [hd]
  exact E'.injective.comp ((fderiv_consBlock_injective m a _).comp E.symm.injective)

private theorem isImmersionAt_cons_of_common_charts [T2Space α] [ChartedSpace ℂ α]
    [IsManifold 𝓘(ℂ) 1 α]
    (φ : Option ι → OpenPartialHomeomorph α ℂ) (V : Option ι → Set α)
    (m : Option ι → ℕ) (hm : ∑ i, m i = n) (hp : ∑ i, consDegrees m i = n + 1)
    (hVo : ∀ i, IsOpen (V i)) (hVsub : ∀ i, V i ⊆ (φ i).source)
    (hVdisj : Pairwise (Function.onFun Disjoint V))
    (e : (Σ i, Fin (m i)) ≃ Fin n)
    (e' : (Σ i, Fin (consDegrees m i)) ≃ Fin (n + 1))
    (hq : Nonempty (∀ i, Sym (V i) (m i)))
    (hr : Nonempty (∀ i, Sym (V i) (consDegrees m i)))
    (hφ : ∀ i, φ i ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 α)
    (z : V none) (s : Sym α n)
    (hs : s ∈ (symOpenPartialHomeomorph φ V m hm hVo hVsub hVdisj e hq).source) :
    letI := symChartedSpace (K := ℂ) (α := α) (n := n)
    letI := symChartedSpace (K := ℂ) (α := α) (n := n + 1)
    IsImmersionAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω (Sym.cons (z : α)) s := by
  let := symChartedSpace (K := ℂ) (α := α) (n := n)
  let := symChartedSpace (K := ℂ) (α := α) (n := n + 1)
  let := isManifold_symChartedSpace (α := α) (n := n)
  let := isManifold_symChartedSpace (α := α) (n := n + 1)
  let C := symOpenPartialHomeomorph φ V m hm hVo hVsub hVdisj e hq
  let D := symOpenPartialHomeomorph φ V (consDegrees m) hp hVo hVsub hVdisj e' hr
  let F := fun c => piSigmaConstHomeomorph ℂ e'
    (consBlock m (φ none z) ((piSigmaConstHomeomorph ℂ e).symm c))
  have hC := symOpenPartialHomeomorph_mem_maximalAtlas φ V m hm hVo hVsub hVdisj e hq hφ
  have hD := symOpenPartialHomeomorph_mem_maximalAtlas φ V (consDegrees m) hp hVo hVsub
    hVdisj e' hr hφ
  -- The same concatenation witnesses both chart sources, including a zero-degree source block.
  have hlocal : ∀ t ∈ C.source, Sym.cons (z : α) t ∈ D.source ∧
      D (Sym.cons (z : α) t) = F (C t) := by
    intro t ht
    rw [symOpenPartialHomeomorph_source] at ht
    obtain ⟨q, rfl⟩ := ht
    refine ⟨?_, symOpenPartialHomeomorph_cons_apply φ V m hm hp hVo hVsub hVdisj e e' hq hr z q⟩
    rw [← sumSubtype_consParts hm hp z q, symOpenPartialHomeomorph_source]
    exact Set.mem_range_self _
  have hFa (c : Fin n → ℂ) := analyticAt_cons_coordinates m e e' (φ none z) c
  have hcoords (t : Sym α n) (ht : t ∈ C.source) :
      (fun c => D (Sym.cons (z : α) (C.symm c))) =ᶠ[𝓝 (C t)] F := by
    filter_upwards [C.open_target.mem_nhds (C.map_source ht)] with c hc
    rw [(hlocal _ (C.map_target hc)).2, C.right_inv hc]
  have hsmooth (t : Sym α n) (ht : t ∈ C.source) :
      ContMDiffAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω (Sym.cons (z : α)) t := by
    rw [contMDiffAt_iff_of_mem_maximalAtlas hC hD ht (hlocal t ht).1]
    refine ⟨(Sym.continuous_cons (z : α)).continuousAt, ?_⟩
    simpa only [mfld_simps, Function.comp_def] using
      ((hFa (C t)).1.congr (hcoords t ht).symm).contDiffAt.contDiffWithinAt
  have hFdiff : IsDiffImmersionAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) F (C s) := by
    have hF : ContDiff ℂ ω F := AnalyticOnNhd.contDiff (fun c _ => (hFa c).1)
    exact ((hF.contDiffOn.isImmersionAt_iff_injective_fderiv isOpen_univ
      (Set.mem_univ (C s)) (by simp)).mpr (hFa (C s)).2).isDiffImmersionAt (by simp)
  have hC1 := IsManifold.maximalAtlas_subset_of_le (I := 𝓘(ℂ, Fin n → ℂ)) (by simp : 1 ≤ ω) hC
  have hCdiff : IsDiffImmersionAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) C s := by
    apply IsDiffImmersionAt.of_mfderiv_isInvertible
    -- Identify the partial equivalences before transporting tangent-space types.
    have hCE : C.extend 𝓘(ℂ, Fin n → ℂ) = C.toPartialEquiv := by
      ext x <;> simp [mfld_simps]
    have h := isInvertible_mfderiv_extend hC1 hs
    rw [hCE] at h
    exact h
  have hDC : IsDiffImmersionAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ)
      (D ∘ Sym.cons (z : α)) s := by
    apply (hFdiff.comp hCdiff).congr
    filter_upwards [C.open_source.mem_nhds hs] with t ht
    exact (hlocal t ht).2
  have hdiff := IsDiffImmersionAt.of_comp ((hsmooth s hs).mdifferentiableAt (by simp))
    ((contMDiffAt_of_mem_maximalAtlas hD (hlocal s hs).1).mdifferentiableAt (by simp)) hDC
  have hsm : ContMDiffOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω
      (Sym.cons (z : α)) C.source := fun t ht => (hsmooth t ht).contMDiffWithinAt
  exact hsm.isImmersionAt_of_hasLeftInverse_mfderiv C.open_source hs (by simp) (isDiffImmersionAt_iff.mp hdiff)

/-- Adjoining a fixed point to unordered tuples on a Hausdorff complex curve is an analytic
smooth embedding for the elementary-symmetric charted structures. Its image is the basepoint
divisor, by `TauCeti.Sym.range_cons`. No distinctness or positive-degree assumption is needed. -/
theorem Sym.isSmoothEmbedding_cons [T2Space α] [ChartedSpace ℂ α] [IsManifold 𝓘(ℂ) 1 α]
    (z : α) :
    letI := symChartedSpace (K := ℂ) (α := α) (n := n)
    letI := symChartedSpace (K := ℂ) (α := α) (n := n + 1)
    IsSmoothEmbedding 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin (n + 1) → ℂ) ω
      (Sym.cons z : Sym α n → Sym α (n + 1)) := by
  classical
  let := symChartedSpace (K := ℂ) (α := α) (n := n)
  let := symChartedSpace (K := ℂ) (α := α) (n := n + 1)
  let := isManifold_symChartedSpace (α := α) (n := n)
  let := isManifold_symChartedSpace (α := α) (n := n + 1)
  refine ⟨isImmersion_iff_forall_isImmersionAt.mpr (fun s => ?_),
    (Sym.isClosedEmbedding_cons z).isEmbedding⟩
  -- Choose one neighbourhood family for the support after insertion. Its basepoint patch
  -- remains present even when its source multiplicity is zero.
  let S := symChartSupport (Sym.cons z s)
  let j : S := ⟨z, mem_symChartSupport.mpr (_root_.Sym.mem_cons_self z s)⟩
  let r := Equiv.optionSubtypeNe j
  obtain ⟨V₀, hVo₀, hmem₀, hsub₀, hdisj₀, hparts⟩ :=
    S.exists_mem_range_sumSubtype_of_t2 (fun a => (chartAt ℂ a).source)
      (fun a _ => (chartAt ℂ a).open_source) (fun a _ => mem_chart_source ℂ a)
  obtain ⟨hm₀, q₀, hq₀⟩ := hparts s (fun a ha =>
    mem_symChartSupport.mpr (_root_.Sym.mem_cons_of_mem ha))
  let V := fun i => V₀ (r i)
  let m := fun i => Multiset.count (r i : α) (s : Multiset α)
  have hm : ∑ i, m i = n := (r.sum_comp _).trans hm₀
  have hp : ∑ i, consDegrees m i = n + 1 := by
    have h := hm
    simp only [Fintype.sum_option] at h ⊢
    simp only [consDegrees]
    omega
  let q := fun i => q₀ (r i)
  have hq : Sym.sumSubtype V m hm q = s := by
    apply _root_.Sym.coe_injective
    rw [Sym.coe_sumSubtype, ← hq₀, Sym.coe_sumSubtype]
    simpa only [q, V] using
      r.sum_comp (fun i => (q₀ i : Multiset (V₀ i)).map Subtype.val)
  let e := (Sym.nonempty_sigmaFinEquiv hm).some
  let e' := (Sym.nonempty_sigmaFinEquiv hp).some
  let hq' : Nonempty (∀ i, Sym (V i) (m i)) := ⟨q⟩
  have hz : z ∈ V none := hmem₀ j
  let hr : Nonempty (∀ i, Sym (V i) (consDegrees m i)) := ⟨consParts ⟨z, hz⟩ q⟩
  have hdisj : Pairwise (Function.onFun Disjoint V) := fun i k hik =>
    hdisj₀ (r.injective.ne hik)
  apply isImmersionAt_cons_of_common_charts (fun i => chartAt ℂ (r i : α)) V m hm hp
    (fun i => hVo₀ (r i)) (fun i => hsub₀ (r i)) hdisj e e' hq' hr
    (fun i => IsManifold.chart_mem_maximalAtlas _) ⟨z, hz⟩ s
  rw [symOpenPartialHomeomorph_source]
  exact ⟨q, hq⟩

end TauCeti
