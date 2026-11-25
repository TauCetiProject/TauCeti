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
import TauCeti.Geometry.Manifold.CoordinateBall

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

A finite cover by coordinate balls `(e i).preimageBall (c i) (r i)` whose concentric balls of
radius `8 r i` are still coordinate balls (`TauCeti.exists_finite_preimageBall_cover`) gives such
nested families, with radii `r i < 2 r i < 4 r i < 8 r i`.

## Main results

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
      (cocycles₁ 1 (subset_source_of_le hW' h'')).subtype ∘ₗ
        (restrictCocycles₁ 1 hW' h'').toLinearMap)
      fun ξ ↦ toSections₁_mem_cocycles₁ he _ (restrictCocycles₁ 1 hW' h'' ξ).property
  have hΦ (ξ : cocycles₁ 1 hW') :
      (Φ ξ).val = toSections₁ he (subset_source_of_le hW' h'') (restrictCochains₁ h'' ξ.val) := by
    simp only [Φ, LinearMap.codRestrict_apply, LinearMap.comp_apply, Submodule.subtype_apply,
      ContinuousLinearMap.coe_coe, coe_restrictCocycles₁]
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
    rw [hΦ, toSections₁_restrictCochains₁ he hW' h'' b.val i j,
      holomorphicStructureSheafModules.map_apply,
      toSections₁_apply]
  rw [hzb, Finset.coe_image, Submodule.span_image]
  exact Submodule.mem_map_of_mem hb

end ChartBergman

/-- **Finiteness of `H¹(X, 𝒪)`** (Forster 14.9). On a compact Hausdorff Riemann surface the first
Čech cohomology of the holomorphic structure sheaf is a finite-dimensional complex vector space. -/
instance finiteDimensional_cechCohomology_one_holomorphicStructureSheafModules [CompactSpace X]
    [T2Space X] :
    FiniteDimensional ℂ ((Topology.cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 1).obj
      (holomorphicStructureSheafModules 𝓘(ℂ) X).obj) := by
  -- Coordinate balls `B i = (e i).preimageBall (c i) (r i)` covering `X`, with `8 r i` in range.
  obtain ⟨ι, _, e, c, r, hatlas, hr, hK, -, hcov⟩ :=
    exists_finite_preimageBall_cover (H := ℂ) 8 (V := fun _ : Unit ↦ (⊤ : Opens X))
      (.mk (top_unique (le_iSup (fun _ : Unit ↦ (⊤ : Opens X)) ())))
  have he (i : ι) : e i ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X :=
    IsManifold.subset_maximalAtlas (hatlas i)
  have hsmall (i : ι) (a : ℝ) (ha : a ≤ 8) : closedBall (c i) (a * r i) ⊆ (e i).target :=
    (closedBall_subset_closedBall (mul_le_mul_of_nonneg_right ha (hr i).le)).trans (hK i)
  have hlt (i : ι) {a b : ℝ} (hab : a < b) : a * r i < b * r i :=
    mul_lt_mul_of_pos_right hab (hr i)
  -- The innermost family `B`, written with `one_mul` so that it matches the cover.
  have hB (i : ι) : (e i).preimageBall (c i) (r i) =
      ⟨(e i).source ∩ e i ⁻¹' eball (c i) (.ofReal (r i)),
        (e i).isOpen_inter_preimage isOpen_eball⟩ := by
    ext x
    rw [SetLike.mem_coe, OpenPartialHomeomorph.mem_preimageBall, Opens.coe_mk, eball_ofReal]
    rfl
  have hfin := ChartBergman.finite_homology_one_cechComplex
    (W := fun i ↦ (e i).preimageBall (c i) (4 * r i))
    (W' := fun i ↦ (e i).preimageBall (c i) (2 * r i))
    (W'' := fun i ↦ (e i).preimageBall (c i) (r i)) (R := fun i ↦ .ofReal (8 * r i)) he
    (fun i ↦ by rw [eball_ofReal]; exact ball_subset_closedBall.trans (hK i))
    (fun i ↦ (e i).isCompact_closure_preimageBall (hsmall i 4 (by norm_num)))
    (fun i ↦ by
      rw [eball_ofReal, ← OpenPartialHomeomorph.coe_preimageBall]
      exact (e i).closure_preimageBall_subset (hsmall i 4 (by norm_num)) (hlt i (by norm_num)))
    (fun i ↦ (e i).closure_preimageBall_subset (hsmall i 2 (by norm_num)) (hlt i (by norm_num)))
    (fun i ↦ by
      simpa only [one_mul] using (e i).closure_preimageBall_subset (hsmall i 1 (by norm_num))
        (hlt i (by norm_num : (1 : ℝ) < 2)))
    (.mk hcov)
  refine (finite_cechCohomology_one_holomorphicStructureSheafModules_iff_finite_homology_cechComplex
    (fun i ↦ (e i).preimageBall (c i) (r i)) hcov fun i ↦ ?_).2 hfin
  have hT : eball (c i) (.ofReal (r i)) ⊆ (e i).target := by
    rw [eball_ofReal]
    simpa only [one_mul] using ball_subset_closedBall.trans (hsmall i 1 (by norm_num))
  rw [hB]
  exact subsingleton_H'_one_holomorphicStructureSheafModules_chart_eball (he i) hT

end TauCeti.RiemannSurface
