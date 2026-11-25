/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Cohomology.Bergman.Cochains
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Leray
public import TauCeti.Topology.Sheaves.Cech.Cocycle
import TauCeti.Analysis.Complex.RiemannSurface.Cohomology.Bergman.Finiteness

/-!
# Finite dimensionality of `H¹(X, 𝒪)` on a compact Riemann surface

On a compact Hausdorff Riemann surface `X`, the first Čech cohomology `H¹(X, 𝒪)` of the holomorphic
structure sheaf is a finite-dimensional complex vector space (Forster, Theorem 14.9).

The proof combines two inputs.

* The Bergman-space argument of `TauCeti.RiemannSurface.ChartBergman`: for three nested families
  `W'' ≤ W' ≤ W` of chart opens with relatively compact closures, finitely many square-integrable
  cocycles on `W'` span every holomorphic Čech `1`-cocycle on `W''` up to holomorphic coboundaries
  (`ChartBergman.exists_finset_forall_cocycle_eq_add_smul_sub`). Read through the native sections
  of the structure sheaf and the classical description of degree one Čech cohomology of a cover
  (`TauCeti.Topology.CechOne`), this says that the Čech `H¹` of the cover `W''` is finitely
  generated (`ChartBergman.finite_homology_one_cechComplex`).
* The degree-one Leray theorem: a finite cover by coordinate discs computes `H¹(X, 𝒪)`, so
  `H¹(X, 𝒪)` is finite-dimensional exactly when the Čech `H¹` of such a cover is
  (`TauCeti.Geometry.Manifold.Complex.StructureSheaf.Leray`).

Concentric coordinate discs of radii `r / 8 < r / 4 < r / 2 < r` around every point give such
nested families, and compactness extracts a finite cover.

## Main results

* `OpenPartialHomeomorph.isCompact_closure_inter_preimage_eball_and_subset`: a coordinate disc
  whose closed disc lies in the chart's target has compact closure inside every larger concentric
  coordinate disc.
* `TauCeti.RiemannSurface.ChartBergman.toSections₁_mem_cocycles₁`: the native sections of a
  square-integrable cocycle of the structure sheaf form a native Čech cocycle.
* `TauCeti.RiemannSurface.ChartBergman.finite_homology_one_cechComplex`: the Čech `H¹` of the
  structure sheaf on the innermost cover of nested relatively compact chart families is finitely
  generated.
* `TauCeti.RiemannSurface.finiteDimensional_cechCohomology_one_holomorphicStructureSheafModules`:
  `H¹(X, 𝒪)` is finite-dimensional on every compact Hausdorff Riemann surface.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §14 (Theorem 14.9).
-/

public noncomputable section

open CategoryTheory Metric Opposite Set TopologicalSpace
open scoped ContDiff Manifold

namespace TauCeti.RiemannSurface

/-- A coordinate disc of radius `s` whose closed disc lies in the chart's target has compact
closure, contained in the concentric coordinate disc of any larger radius `t`. -/
theorem _root_.OpenPartialHomeomorph.isCompact_closure_inter_preimage_eball_and_subset
    {X : Type*} [TopologicalSpace X] [T2Space X] {e : OpenPartialHomeomorph X ℂ} {c : ℂ}
    {s t : ℝ} (hst : s < t) (hs : closedBall c s ⊆ e.target) :
    IsCompact (closure (e.source ∩ e ⁻¹' eball c (.ofReal s))) ∧
      closure (e.source ∩ e ⁻¹' eball c (.ofReal s)) ⊆ e.source ∩ e ⁻¹' eball c (.ofReal t) := by
  rw [eball_ofReal, eball_ofReal]
  have hK : IsCompact (e.symm '' closedBall c s) :=
    (isCompact_closedBall c s).image_of_continuousOn (e.continuousOn_symm.mono hs)
  have hcl : closure (e.source ∩ e ⁻¹' ball c s) ⊆ e.symm '' closedBall c s :=
    closure_minimal (fun y hy ↦ ⟨e y, ball_subset_closedBall hy.2, e.left_inv hy.1⟩)
      hK.isClosed
  refine ⟨hK.of_isClosed_subset isClosed_closure hcl, hcl.trans ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨e.map_target (hs hz), by
    rw [mem_preimage, e.right_inv (hs hz)]; exact closedBall_subset_ball hst hz⟩

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]

namespace ChartBergman

variable {ι : Type} {e : ι → OpenPartialHomeomorph X ℂ} {W W' W'' : ι → Opens X}

/-- For the structure sheaf (`g = 1`), the native sections of a square-integrable cocycle form a
native Čech cocycle. -/
theorem toSections₁_mem_cocycles₁ (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hW : ∀ i, (W i : Set X) ⊆ (e i).source)
    {ξ : (i j : ι) → bergmanSpace ℂ ((e i).imageOpens (W i ⊓ W j))} (hξ : ξ ∈ cocycles₁ 1 hW) :
    toSections₁ he hW ξ ∈
      Topology.CechOne.cocycles₁ (holomorphicStructureSheafModules 𝓘(ℂ) X).obj W := by
  rw [Topology.CechOne.mem_cocycles₁_iff]
  intro i j k
  ext ⟨x, hx⟩
  simp only [holomorphicStructureSheafModules.add_apply, holomorphicStructureSheafModules.sub_apply,
    holomorphicStructureSheafModules.map_apply, holomorphicStructureSheafModules.zero_apply]
  exact (mem_cocycles₁_iff_toSections₁ he hW).1 hξ i j k x hx

omit [IsManifold 𝓘(ℂ) 1 X] in
/-- A native Čech one-cocycle of the structure sheaf on a family `V`, extended by zero off the
overlaps, is a family of holomorphic functions on the overlaps satisfying the cocycle identity. -/
private theorem exists_mdifferentiableOn_eq_of_mem_cocycles₁ (V : ι → Opens X)
    (z : Topology.CechOne.cocycles₁ (holomorphicStructureSheafModules 𝓘(ℂ) X).obj V) :
    ∃ ζ : ι → ι → X → ℂ, (∀ i j, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (ζ i j) (V i ⊓ V j)) ∧
      (∀ i j k, ∀ x ∈ V i ⊓ V j ⊓ V k, ζ i j x + ζ j k x = ζ i k x) ∧
      ∀ i j (x : ↥(V i ⊓ V j)), ζ i j x = z.val i j x := by
  classical
  let ζ : ι → ι → X → ℂ := fun i j x ↦ if hx : x ∈ V i ⊓ V j then z.val i j ⟨x, hx⟩ else 0
  have hζ_eq (i j : ι) (x : ↥(V i ⊓ V j)) : ζ i j x = z.val i j x := by
    simp only [ζ]
    split_ifs with h
    · rfl
    · exact absurd x.property h
  refine ⟨ζ, fun i j x hx ↦ ?_, fun i j k x hx ↦ ?_, hζ_eq⟩
  · have hc : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun y : ↥(V i ⊓ V j) ↦ ζ i j y) ⟨x, hx⟩ := by
      simp_rw [hζ_eq]
      exact holomorphicStructureSheafModules.contMDiff _ _
    exact ((contMDiffAt_subtype_iff.1 hc).mdifferentiableAt (by simp)).mdifferentiableWithinAt
  · have := congrArg (fun f ↦ f ⟨x, hx⟩)
      ((Topology.CechOne.mem_cocycles₁_iff (holomorphicStructureSheafModules 𝓘(ℂ) X).obj V).1
        z.property i j k)
    simp only [holomorphicStructureSheafModules.add_apply,
      holomorphicStructureSheafModules.sub_apply, holomorphicStructureSheafModules.map_apply,
      holomorphicStructureSheafModules.zero_apply] at this
    rw [hζ_eq i j ⟨x, hx.1⟩, hζ_eq j k ⟨x, hx.1.2, hx.2⟩, hζ_eq i k ⟨x, hx.1.1, hx.2⟩]
    linear_combination this

/-- Two native Čech one-cocycles of the structure sheaf have the same class when they differ, at
every point of every overlap, by the coboundary `η j - η i` of holomorphic functions `η i` on the
members. -/
private theorem toHomology_eq_of_forall_eq_add_sub (V : ι → Opens X)
    (z z' : Topology.CechOne.cocycles₁ (holomorphicStructureSheafModules 𝓘(ℂ) X).obj V)
    (η : ι → X → ℂ) (hη : ∀ i, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (η i) (V i))
    (h : ∀ i j (x : ↥(V i ⊓ V j)), z.val i j x = z'.val i j x + η j x - η i x) :
    Topology.CechOne.toHomology (holomorphicStructureSheafModules 𝓘(ℂ) X).obj V z =
      Topology.CechOne.toHomology (holomorphicStructureSheafModules 𝓘(ℂ) X).obj V z' := by
  have hηs (i : ι) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun x : V i ↦ η i x) := fun x ↦
    contMDiffAt_subtype_iff.2 (((hη i).contMDiffOn (V i).isOpen).contMDiffAt
      ((V i).isOpen.mem_nhds x.property))
  refine (Topology.CechOne.toHomology_eq_iff _ V z z').2
    ⟨fun i ↦ holomorphicStructureSheafModules.ofContMDiff _ (hηs i), ?_⟩
  funext i j
  ext x
  simp only [Topology.CechOne.d₀₁_apply, holomorphicStructureSheafModules.sub_apply,
    holomorphicStructureSheafModules.map_apply, Pi.sub_apply]
  rw [holomorphicStructureSheafModules.ofContMDiff_apply,
    holomorphicStructureSheafModules.ofContMDiff_apply, h]
  change η j x - η i x = _
  ring

/-- **The Čech `H¹` of a cover by nested chart discs is finitely generated** (Forster 14.9). Let
`closure (W'' i) ⊆ W' i`, `closure (W' i) ⊆ W i`, and `closure (W i)` compact inside the coordinate
disc `(e i).source ∩ e i ⁻¹' eball (c i) (R i)`, with the `W'' i` covering `X`. Then the degree one
Čech cohomology of the structure sheaf on the cover `W''` is a finitely generated complex vector
space. -/
theorem finite_homology_one_cechComplex [T2Space X] [Finite ι] {c : ι → ℂ} {R : ι → ENNReal}
    (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hR : ∀ i, eball (c i) (R i) ⊆ (e i).target)
    (hKW : ∀ i, IsCompact (closure (W i : Set X)))
    (hWU : ∀ i, closure (W i : Set X) ⊆ (e i).source ∩ e i ⁻¹' eball (c i) (R i))
    (hW'W : ∀ i, closure (W' i : Set X) ⊆ W i)
    (hIW : ∀ i, closure (W'' i : Set X) ⊆ W' i) (hcov : IsOpenCover W'') :
    Module.Finite ℂ (((cechComplexFunctor (C := Opens (TopCat.of X)) W'').obj
      (holomorphicStructureSheafModules 𝓘(ℂ) X).obj).homology 1) := by
  classical
  have hW (i : ι) : (W i : Set X) ⊆ (e i).source :=
    subset_closure.trans ((hWU i).trans inter_subset_left)
  have h' (i : ι) : W' i ≤ W i := subset_closure.trans (hW'W i)
  have h'' (i : ι) : W'' i ≤ W' i := subset_closure.trans (hIW i)
  have hW' := subset_source_of_le hW h'
  obtain ⟨s, hs⟩ := exists_finset_forall_cocycle_eq_add_smul_sub 1 he hW hR (fun _ ↦ rfl) hKW hWU
    hW'W hIW hcov (fun _ _ ↦ mdifferentiableOn_const) (fun _ _ _ ↦ rfl)
    (fun _ _ _ _ _ ↦ one_mul 1)
  -- Restrict square-integrable cocycles on `W'` to native cocycles on `W''`, then take classes.
  let Φ : cocycles₁ 1 hW' →ₗ[ℂ]
      Topology.CechOne.cocycles₁ (holomorphicStructureSheafModules 𝓘(ℂ) X).obj W'' :=
    LinearMap.codRestrict _ (toSections₁ he (subset_source_of_le hW' h'') ∘ₗ
      (restrictCochains₁ h'').toLinearMap ∘ₗ (cocycles₁ 1 hW').subtype)
      fun ξ ↦ toSections₁_mem_cocycles₁ he _ (restrictCochains₁_mem_cocycles₁ 1 hW' h'' ξ.property)
  let F := Topology.CechOne.toHomology (holomorphicStructureSheafModules 𝓘(ℂ) X).obj W'' ∘ₗ Φ
  refine ⟨⟨s.image F, eq_top_iff.2 fun y _ ↦ ?_⟩⟩
  obtain ⟨z, rfl⟩ :=
    Topology.CechOne.toHomology_surjective (holomorphicStructureSheafModules 𝓘(ℂ) X).obj W'' y
  obtain ⟨ζ, hζ, hζc, hζ_eq⟩ := exists_mdifferentiableOn_eq_of_mem_cocycles₁ W'' z
  obtain ⟨b, hb, η, hη, hζη⟩ := hs ζ hζ fun i j k x hx ↦ by
    simpa only [Pi.one_apply, one_smul] using hζc i j k x hx
  -- `z` and the restriction of `b` differ by the coboundary of `η`.
  have hzb :
      Topology.CechOne.toHomology (holomorphicStructureSheafModules 𝓘(ℂ) X).obj W'' z = F b := by
    refine toHomology_eq_of_forall_eq_add_sub W'' z (Φ b) η hη fun i j x ↦ ?_
    rw [← hζ_eq, hζη i j x x.property, Pi.one_apply, Pi.one_apply, Pi.one_apply, one_smul]
    refine congrArg (· + η j x - η i x) ?_
    change _ = toSections₁ he _ (restrictCochains₁ h'' b.val) i j x
    rw [toSections₁_apply, restrictCochains₁_apply, BergmanSpace.representative_restrict _ _
      ((e i).map_mem_imageOpens (hW i (h' i (h'' i x.property.1))) x.property)]
  rw [hzb, Finset.coe_image, Submodule.span_image]
  exact Submodule.mem_map_of_mem hb

end ChartBergman

/-- **Finiteness of `H¹(X, 𝒪)`** (Forster 14.9). On a compact Hausdorff Riemann surface the first
Čech cohomology of the holomorphic structure sheaf is a finite-dimensional complex vector space. -/
instance finiteDimensional_cechCohomology_one_holomorphicStructureSheafModules [CompactSpace X]
    [T2Space X] :
    FiniteDimensional ℂ ((Topology.cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 1).obj
      (holomorphicStructureSheafModules 𝓘(ℂ) X).obj) := by
  -- Around every point `x`, a coordinate disc of radius `r x` inside the chart's target.
  have hr (x : X) : ∃ r : ℝ, 0 < r ∧ ball (chartAt ℂ x x) r ⊆ (chartAt ℂ x).target :=
    isOpen_iff.1 (chartAt ℂ x).open_target _ (mem_chart_target ℂ x)
  choose r hr0 hrT using hr
  -- The concentric coordinate discs of radius `r x / 2 ^ n`.
  let D (n : ℕ) (x : X) : Opens X :=
    ⟨(chartAt ℂ x).source ∩ chartAt ℂ x ⁻¹' eball (chartAt ℂ x x) (.ofReal (r x / 2 ^ n)),
      (chartAt ℂ x).isOpen_inter_preimage isOpen_eball⟩
  have hD (n : ℕ) (x : X) : closure (D (n + 1) x : Set X) ⊆ D n x ∧
      IsCompact (closure (D (n + 1) x : Set X)) := by
    have hlt : r x / 2 ^ (n + 1) < r x / 2 ^ n := by
      exact div_lt_div_of_pos_left (hr0 x) (by positivity)
        (pow_lt_pow_right₀ one_lt_two n.lt_succ_self)
    have hlt' : r x / 2 ^ (n + 1) < r x :=
      hlt.trans_le (div_le_self (hr0 x).le (one_le_pow₀ one_le_two))
    obtain ⟨h₁, h₂⟩ := OpenPartialHomeomorph.isCompact_closure_inter_preimage_eball_and_subset
      hlt ((closedBall_subset_ball hlt').trans (hrT x))
    exact ⟨h₂, h₁⟩
  have hcov : IsOpenCover (D 3) := .mk <| eq_top_iff.2 fun x _ ↦ Opens.mem_iSup.2 ⟨x,
    mem_chart_source ℂ x, mem_eball_self (ENNReal.ofReal_pos.2 (div_pos (hr0 x) (by positivity)))⟩
  obtain ⟨s, hs⟩ := hcov.exists_finite_of_compactSpace
  have hD₀ (x : X) : eball (chartAt ℂ x x) (.ofReal (r x / 2 ^ 0)) ⊆ (chartAt ℂ x).target := by
    rw [eball_ofReal, pow_zero, div_one]; exact hrT x
  have hfin := ChartBergman.finite_homology_one_cechComplex (ι := s)
    (e := fun x ↦ chartAt ℂ x.val) (W := fun x ↦ D 1 x.val) (W' := fun x ↦ D 2 x.val)
    (W'' := fun x ↦ D 3 x.val)
    (fun x ↦ IsManifold.chart_mem_maximalAtlas x.val)
    (fun x ↦ hD₀ x.val) (fun x ↦ (hD 0 x.val).2)
    (fun x ↦ (hD 0 x.val).1) (fun x ↦ (hD 1 x.val).1) (fun x ↦ (hD 2 x.val).1) hs
  exact (finite_cechCohomology_one_holomorphicStructureSheafModules_iff_finite_homology_cechComplex
    (fun x : s ↦ D 3 x.val) hs.iSup_eq_top fun x ↦
      subsingleton_H'_one_holomorphicStructureSheafModules_chart_eball
        (IsManifold.chart_mem_maximalAtlas x.val) (by
          rw [eball_ofReal]
          exact (ball_subset_ball (div_le_self (hr0 x.val).le (one_le_pow₀ one_le_two))).trans
            (hrT x.val))).2 hfin

end TauCeti.RiemannSurface
