/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import TauCeti.Analysis.Complex.Wirtinger.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import TauCeti.Analysis.Complex.Wirtinger.OpenDomain
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.Geometry.Manifold.PartitionOfUnity.Basic

/-!
# Global mixed-parameter `bar∂` solver on smooth manifolds

Let `P` be a smooth boundaryless Hausdorff σ-compact manifold modelled on a finite-dimensional real
normed space `EP`, let `E` be a proper complex normed space, let `U ⊆ P × E` and `Ω ⊆ ℂ` be open
sets, and let `F` be a complex Banach space. Given a smooth map `f : (P × E) × ℂ → F` on `U ×ˢ Ω`
which is holomorphic in the complex parameter `q ∈ E`, this file constructs a smooth map
`u : (P × E) × ℂ → F` on `U ×ˢ Ω`, holomorphic in `q ∈ E`, satisfying `bar∂_z u = f` on all of
`U ×ˢ Ω`.

This mixed-parameter solver is designed for inductive Dolbeault–Grothendieck elimination of
several complex variables on product domains: it solves `bar∂` in one complex coordinate `z ∈ ℂ`
without shrinking the domain while simultaneously preserving smooth dependence on an auxiliary
parameter manifold `P` and holomorphy in the remaining complex coordinates `E`.

The proof works in each chart `extChartAt I i` of `P` via the flat-space solver
`TauCeti.exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_with_holomorphic_param`, and glues the
chartwise solutions `v i` using a smooth partition of unity `ρ` on `P` subordinate to the chart
sources (`SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source`):

`u ((p, q), z) = ∑ᶠ i, ρ i p • v i ((p, q), z)`.

Because the weights `ρ i p` depend only on `p ∈ P` — neither on the holomorphic parameter `q ∈ E`
nor on the plane variable `z ∈ ℂ` — multiplication by `ρ i p` commutes with both `bar∂_z` and
complex differentiation in `q`, and the locally finite sum stays smooth on `U ×ˢ Ω` without
partitioning `E` or `Ω`.

## Main results

* `TauCeti.exists_contMDiffOn_conjWirtingerDeriv_apply_one_eq_with_holomorphic_param`: global
  smooth solution of `bar∂_z u = f` on `U ×ˢ Ω`, preserving holomorphy in `q ∈ E`.
* `TauCeti.exists_contMDiffOn_conjWirtingerDeriv_apply_one_eq_with_param`: specialization to
  purely smooth manifold parameters `U ⊆ P`.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Theorem 1.4.4.
* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter I, §3.
-/

public noncomputable section

open Complex Filter Manifold Set Topology
open scoped ContDiff

namespace TauCeti

/-- Chartwise solver: on the chart domain `(U ∩ ((chartAt HP i).source ×ˢ univ)) ×ˢ Ω`, pull `f`
back along `(extChartAt I i).symm`, solve in flat space `EP × E`, and push forward along
`extChartAt I i`. -/
private theorem exists_chart_dbar_solution {EP HP P E F : Type*}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP]
    [TopologicalSpace HP] (I : ModelWithCorners ℝ EP HP) [I.Boundaryless]
    [TopologicalSpace P] [ChartedSpace HP P] [IsManifold I ∞ P]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {U : Set (P × E)} {Ω : Set ℂ} {f : (P × E) × ℂ → F} (hU : IsOpen U) (hΩ : IsOpen Ω)
    (hf : ContMDiffOn ((I.prod 𝓘(ℝ, E)).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, F) ∞ f (U ×ˢ Ω))
    (hfq : ∀ x ∈ U, ∀ z ∈ Ω, DifferentiableAt ℂ (fun q ↦ f ((x.1, q), z)) x.2) (i : P) :
    ∃ v : (P × E) × ℂ → F,
      ContMDiffOn ((I.prod 𝓘(ℝ, E)).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, F) ∞ v
        ((U ∩ ((chartAt HP i).source ×ˢ univ)) ×ˢ Ω) ∧
      (∀ x ∈ U, x.1 ∈ (chartAt HP i).source → ∀ z ∈ Ω,
        conjWirtingerDeriv (fun w ↦ v (x, w)) z 1 = f (x, z)) ∧
      ∀ x ∈ U, x.1 ∈ (chartAt HP i).source → ∀ z ∈ Ω,
        DifferentiableAt ℂ (fun q ↦ v ((x.1, q), z)) x.2 := by
  let e := extChartAt I i
  let s : Set (EP × E) := (e.target ×ˢ univ) ∩ (fun x : EP × E ↦ (e.symm x.1, x.2)) ⁻¹' U
  have hs : IsOpen s :=
    ((continuousOn_extChartAt_symm (I := I) i).prodMap continuousOn_id).isOpen_inter_preimage
      ((isOpen_extChartAt_target (I := I) i).prod isOpen_univ) hU
  let fi : EP × E → ℂ → F := fun x z ↦ f ((e.symm x.1, x.2), z)
  have hfi_mdiff :
      ContMDiffOn ((𝓘(ℝ, EP).prod 𝓘(ℝ, E)).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, F) ∞ ↿fi (s ×ˢ Ω) := by
    have hmap : ContMDiffOn ((𝓘(ℝ, EP).prod 𝓘(ℝ, E)).prod 𝓘(ℝ, ℂ))
        ((I.prod 𝓘(ℝ, E)).prod 𝓘(ℝ, ℂ)) ∞
        (fun y : (EP × E) × ℂ ↦ ((e.symm y.1.1, y.1.2), y.2)) (s ×ˢ Ω) :=
      (((contMDiffOn_extChartAt_symm i).comp (contMDiff_fst.comp contMDiff_fst).contMDiffOn
        (fun _ (hy : _ ∈ s ×ˢ Ω) ↦ hy.1.1.1)).prodMk
        (contMDiff_snd.comp contMDiff_fst).contMDiffOn).prodMk contMDiff_snd.contMDiffOn
    exact hf.comp hmap fun _ hy ↦ ⟨hy.1.2, hy.2⟩
  have hfi_cd : ContDiffOn ℝ ∞ ↿fi (s ×ˢ Ω) :=
    contMDiffOn_iff_contDiffOn.1 <| contMDiffOn_prod_modelWithCornersSelf_iff.1 <|
      contMDiffOn_prod_prod_modelWithCornersSelf_iff.1 hfi_mdiff
  obtain ⟨w, hw_cd, hw_dbar, hw_q⟩ :=
    exists_contDiffOn_conjWirtingerDeriv_apply_one_eq_with_holomorphic_param hs hΩ hfi_cd
      fun x hx z hz ↦ hfq _ hx.2 z hz
  let v : (P × E) × ℂ → F := fun y ↦ w (e y.1.1, y.1.2) y.2
  have hmem {x : P × E} (hxU : x ∈ U) (hxS : x.1 ∈ (chartAt HP i).source) :
      (e x.1, x.2) ∈ s := by
    have hxE : x.1 ∈ e.source := by simpa [e, extChartAt_source] using hxS
    refine ⟨⟨e.map_source hxE, mem_univ _⟩, ?_⟩
    simpa only [mem_preimage, e.left_inv hxE] using hxU
  refine ⟨v, ?_, fun x hxU hxS z hz ↦ ?_, fun x hxU hxS z hz ↦ ?_⟩
  · have hmap : ContMDiffOn ((I.prod 𝓘(ℝ, E)).prod 𝓘(ℝ, ℂ))
        ((𝓘(ℝ, EP).prod 𝓘(ℝ, E)).prod 𝓘(ℝ, ℂ)) ∞
        (fun y : (P × E) × ℂ ↦ ((e y.1.1, y.1.2), y.2))
        ((U ∩ ((chartAt HP i).source ×ˢ univ)) ×ˢ Ω) :=
      (((contMDiffOn_extChartAt (I := I) (x := i)).comp
        (contMDiff_fst.comp contMDiff_fst).contMDiffOn
        fun _ hy ↦ by simpa [extChartAt_source] using hy.1.2.1).prodMk
        (contMDiff_snd.comp contMDiff_fst).contMDiffOn).prodMk contMDiff_snd.contMDiffOn
    have hw_md :
        ContMDiffOn ((𝓘(ℝ, EP).prod 𝓘(ℝ, E)).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, F) ∞ ↿w (s ×ˢ Ω) :=
      contMDiffOn_prod_prod_modelWithCornersSelf_iff.2 <|
        contMDiffOn_prod_modelWithCornersSelf_iff.2 <| contMDiffOn_iff_contDiffOn.2 hw_cd
    exact hw_md.comp hmap fun _ hy ↦ ⟨hmem hy.1.1 hy.1.2.1, hy.2⟩
  · have hxE : x.1 ∈ e.source := by simpa [e, extChartAt_source] using hxS
    simpa only [v, fi, e.left_inv hxE] using hw_dbar (e x.1, x.2) (hmem hxU hxS) z hz
  · exact hw_q (e x.1, x.2) (hmem hxU hxS) z hz

/-- **Global mixed-parameter `bar∂` solver on a smooth manifold.** Let `P` be a smooth
boundaryless Hausdorff σ-compact manifold modelled on a finite-dimensional real normed space `EP`,
let `E` be a proper complex normed space, let `U ⊆ P × E` and `Ω ⊆ ℂ` be open sets, and let `F` be
a complex Banach space. If `f : (P × E) × ℂ → F` is smooth on `U ×ˢ Ω` and holomorphic in the
complex parameter `q ∈ E`, then there exists `u : (P × E) × ℂ → F`, smooth on `U ×ˢ Ω` and
holomorphic in `q ∈ E`, such that `conjWirtingerDeriv (fun w ↦ u (x, w)) z 1 = f (x, z)` for every
`x ∈ U` and `z ∈ Ω`. -/
theorem exists_contMDiffOn_conjWirtingerDeriv_apply_one_eq_with_holomorphic_param
    {EP HP P E F : Type*}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP]
    [TopologicalSpace HP] (I : ModelWithCorners ℝ EP HP) [I.Boundaryless]
    [TopologicalSpace P] [ChartedSpace HP P] [IsManifold I ∞ P]
    [T2Space P] [SigmaCompactSpace P]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {U : Set (P × E)} {Ω : Set ℂ} {f : (P × E) × ℂ → F} (hU : IsOpen U) (hΩ : IsOpen Ω)
    (hf : ContMDiffOn ((I.prod 𝓘(ℝ, E)).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, F) ∞ f (U ×ˢ Ω))
    (hfq : ∀ x ∈ U, ∀ z ∈ Ω, DifferentiableAt ℂ (fun q ↦ f ((x.1, q), z)) x.2) :
    ∃ u : (P × E) × ℂ → F,
      ContMDiffOn ((I.prod 𝓘(ℝ, E)).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, F) ∞ u (U ×ˢ Ω) ∧
      (∀ x ∈ U, ∀ z ∈ Ω, conjWirtingerDeriv (fun w ↦ u (x, w)) z 1 = f (x, z)) ∧
      ∀ x ∈ U, ∀ z ∈ Ω, DifferentiableAt ℂ (fun q ↦ u ((x.1, q), z)) x.2 := by
  obtain ⟨ρ, hρ_sub⟩ := SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source I P
  choose v hv_md hv_dbar hv_q using exists_chart_dbar_solution I hU hΩ hf hfq
  let u : (P × E) × ℂ → F := fun y ↦ ∑ᶠ i : P, ρ i y.1.1 • v i y
  have hmdAt {i : P} {x : P × E} (hxU : x ∈ U) (hxS : x.1 ∈ (chartAt HP i).source)
      {z : ℂ} (hz : z ∈ Ω) :
      ContMDiffAt ((I.prod 𝓘(ℝ, E)).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, F) ∞ (v i) (x, z) := by
    have hopen : IsOpen ((U ∩ ((chartAt HP i).source ×ˢ univ)) ×ˢ Ω) :=
      (hU.inter ((chartAt HP i).open_source.prod isOpen_univ)).prod hΩ
    exact (hv_md i).contMDiffAt (hopen.mem_nhds ⟨⟨hxU, hxS, mem_univ _⟩, hz⟩)
  have hfin_eq (p : P) (q : E) (w : ℂ) :
      u ((p, q), w) = ∑ i ∈ ρ.finsupport p, ρ i p • v i ((p, q), w) :=
    (ρ.sum_finsupport_smul_eq_finsum p fun i _ ↦ v i ((p, q), w)).symm
  refine ⟨u, ?_, ?_, ?_⟩
  · rintro ⟨x, z⟩ ⟨hxU, hz⟩
    exact (ρ.contMDiffAt_finsum_comp (contMDiff_fst.comp contMDiff_fst).contMDiffAt
      fun i hi ↦ hmdAt hxU (hρ_sub i hi) hz).contMDiffWithinAt
  · -- Solution of `bar∂_z u = f` on `U ×ˢ Ω`: `ρ i x.1` is independent of `z`.
    intro x hxU z hz
    have hsrc {i : P} (hi : i ∈ ρ.finsupport x.1) : x.1 ∈ (chartAt HP i).source :=
      hρ_sub i (subset_tsupport (ρ i) ((ρ.mem_finsupport x.1).1 hi))
    have hfun : (fun w ↦ u (x, w)) =
        fun w ↦ ∑ i ∈ ρ.finsupport x.1, ((ρ i x.1 : ℂ) • fun w ↦ v i (x, w)) w := by
      ext w
      simpa only [Pi.smul_apply, Complex.coe_smul] using hfin_eq x.1 x.2 w
    have hdiff {i : P} (hi : i ∈ ρ.finsupport x.1) :
        DifferentiableAt ℝ ((ρ i x.1 : ℂ) • fun w ↦ v i (x, w)) z := by
      have hmd : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, F) ∞ (fun w ↦ v i (x, w)) z :=
        (hmdAt hxU (hsrc hi) hz).comp z (contMDiffAt_const.prodMk contMDiffAt_id)
      exact ((contMDiffAt_iff_contDiffAt.1 hmd).differentiableAt (by simp)).const_smul _
    rw [hfun, conjWirtingerDeriv_fun_sum fun i hi ↦ hdiff hi, sum_apply,
      Finset.sum_congr rfl fun i hi ↦ by
        rw [conjWirtingerDeriv_const_smul, smul_apply, hv_dbar i x hxU (hsrc hi) z hz],
      ← Finset.sum_smul, ← Complex.ofReal_sum, ρ.sum_finsupport x.1 (mem_univ x.1),
      Complex.ofReal_one, one_smul]
  · -- Holomorphy in `q ∈ E`: `ρ i x.1` is independent of `q`.
    intro x hxU z hz
    have hfun : (fun q ↦ u ((x.1, q), z)) =
        fun q ↦ ∑ i ∈ ρ.finsupport x.1, ρ i x.1 • v i ((x.1, q), z) :=
      funext fun q ↦ hfin_eq x.1 q z
    rw [hfun]
    refine DifferentiableAt.fun_sum fun i hi ↦ (hv_q i x hxU ?_ z hz).const_smul (ρ i x.1)
    exact hρ_sub i (subset_tsupport (ρ i) ((ρ.mem_finsupport x.1).1 hi))

/-- **Global `bar∂` solver on an open plane domain with smooth manifold parameters.** Let `P` be a
smooth boundaryless Hausdorff σ-compact manifold modelled on a finite-dimensional real normed space
`EP`, let `U ⊆ P` and `Ω ⊆ ℂ` be open sets, and let `F` be a complex Banach space. Every smooth map
`f : P × ℂ → F` on `U ×ˢ Ω` satisfies `conjWirtingerDeriv (fun w ↦ u (p, w)) z 1 = f (p, z)` for
some smooth `u : P × ℂ → F` on `U ×ˢ Ω`. -/
theorem exists_contMDiffOn_conjWirtingerDeriv_apply_one_eq_with_param
    {EP HP P F : Type*}
    [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP]
    [TopologicalSpace HP] (I : ModelWithCorners ℝ EP HP) [I.Boundaryless]
    [TopologicalSpace P] [ChartedSpace HP P] [IsManifold I ∞ P]
    [T2Space P] [SigmaCompactSpace P]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {U : Set P} {Ω : Set ℂ} {f : P × ℂ → F} (hU : IsOpen U) (hΩ : IsOpen Ω)
    (hf : ContMDiffOn (I.prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, F) ∞ f (U ×ˢ Ω)) :
    ∃ u : P × ℂ → F,
      ContMDiffOn (I.prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, F) ∞ u (U ×ˢ Ω) ∧
      ∀ p ∈ U, ∀ z ∈ Ω, conjWirtingerDeriv (fun w ↦ u (p, w)) z 1 = f (p, z) := by
  let f' : (P × (Fin 0 → ℂ)) × ℂ → F := fun y ↦ f (y.1.1, y.2)
  have hf' : ContMDiffOn ((I.prod 𝓘(ℝ, Fin 0 → ℂ)).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, F) ∞ f'
      ((U ×ˢ (univ : Set (Fin 0 → ℂ))) ×ˢ Ω) :=
    hf.comp ((contMDiff_fst.comp contMDiff_fst).prodMk contMDiff_snd).contMDiffOn
      fun _ hy ↦ ⟨hy.1.1, hy.2⟩
  obtain ⟨u', hu'_md, hu'_dbar, -⟩ :=
    exists_contMDiffOn_conjWirtingerDeriv_apply_one_eq_with_holomorphic_param I
      (hU.prod isOpen_univ) hΩ hf' fun _ _ _ _ ↦ by simp [f']
  refine ⟨fun y ↦ u' ((y.1, 0), y.2), ?_, fun p hp z hz ↦ hu'_dbar (p, 0) ⟨hp, mem_univ _⟩ z hz⟩
  exact hu'_md.comp ((contMDiff_fst.prodMk contMDiff_const).prodMk contMDiff_snd).contMDiffOn
    fun _ hy ↦ ⟨⟨hy.1, mem_univ _⟩, hy.2⟩

end TauCeti
