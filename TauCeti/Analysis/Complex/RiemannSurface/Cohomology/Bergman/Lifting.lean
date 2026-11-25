/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Cohomology.Bergman.Cochains
import TauCeti.Analysis.Complex.RiemannSurface.Cohomology.DolbeaultGluing
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Tactic.LinearCombination

/-!
# Uniform lifting of Bergman cocycles through compatible triples

Holomorphic extension to larger coordinate discs makes the native middle projection surjective.
Compact inner and outer closures turn the extension and its holomorphic correction into actual
Bergman classes. The Banach open mapping theorem gives one bound for lifting every middle
cocycle in its native norm.

## References

* O. Forster, *Lectures on Riemann Surfaces*, GTM 81, §14.
-/

public noncomputable section

open Metric Set TopologicalSpace MeasureTheory
open scoped Manifold ContDiff ENNReal Topology

universe u
namespace TauCeti.RiemannSurface.ChartBergman

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [T2Space X] {ι : Type*} [Finite ι]
  {e : ι → OpenPartialHomeomorph X ℂ} {W W' W'' : ι → Opens X}
  {U : ι → Set X} {c : ι → ℂ} {R : ι → ℝ≥0∞}

/-- A native middle cocycle extends to larger coordinate discs, modulo a holomorphic
zero-cochain on the middle cover. -/
theorem exists_extended_cocycle_of_middle
    (g : ι → ι → X → ℂ)
    (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hW : ∀ i, (W i : Set X) ⊆ (e i).source) (h' : ∀ i, W' i ≤ W i)
    (hR : ∀ i, eball (c i) (R i) ⊆ (e i).target)
    (hU : ∀ i, U i = (e i).source ∩ e i ⁻¹' eball (c i) (R i))
    (hKW : ∀ i, IsCompact (closure (W i : Set X)))
    (hWU : ∀ i, closure (W i : Set X) ⊆ U i) (hcov : IsOpenCover W')
    (hg : ∀ i j, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (g i j) (U i ∩ U j))
    (hg_one : ∀ i, ∀ x ∈ W' i, g i i x = 1)
    (hg_mul : ∀ i j k, ∀ x ∈ U i ∩ U j ∩ U k, g i j x * g j k x = g i k x)
    (ξ : cocycles₁ g (subset_source_of_le hW h')) :
    ∃ (ζ : ι → ι → X → ℂ) (η : ι → X → ℂ),
      (∀ i j, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (ζ i j) (U i ∩ U j)) ∧
      (∀ i j k, ∀ x ∈ U i ∩ U j ∩ U k, ζ i j x + g i j x • ζ j k x = ζ i k x) ∧
      (∀ i, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (η i) (W' i)) ∧
      (∀ i j, ∀ x ∈ W' i ⊓ W' j, ζ i j x =
        BergmanSpace.representative (ξ.val i j) (e i x) + g i j x • η j x - η i x) := by
  have : CompactSpace X := by
    have hsub : (univ : Set X) ⊆ ⋃ i, closure (W i : Set X) := by
      intro x _
      obtain ⟨i, hi⟩ := hcov.exists_mem x
      exact mem_iUnion.mpr ⟨i, subset_closure (h' i hi)⟩
    exact ⟨(isCompact_iUnion hKW).of_isClosed_subset isClosed_univ hsub⟩
  have hVU (i : ι) : (W' i : Set X) ⊆ U i :=
    fun x hx ↦ hWU i (subset_closure (h' i hx))
  let f : ι → ι → X → ℂ := fun i j x ↦ BergmanSpace.representative (ξ.val i j) (e i x)
  have hf (i j : ι) : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (f i j) (W' i ⊓ W' j) :=
    mdifferentiableOn_representative_comp_chart (he i)
      (inf_subset_source (subset_source_of_le hW h') i j) (ξ.val i j)
  have hc (i j k : ι) (x : X) (hx : x ∈ W' i ⊓ W' j ⊓ W' k) :
      f i j x + g i j x • f j k x = f i k x := by
    have hh := (mem_cocycles₁_iff g _).mp ξ.property i j k x hx
    simp only [smul_eq_mul]
    linear_combination hh
  obtain ⟨ζ, η, hζ, hζc, hη, hζη, -⟩ :=
    exists_mdifferentiableOn_cocycle_eq_add_smul_sub_of_chart_eball
      he hR hU (fun i ↦ (W' i).isOpen) hVU hcov.iSup_set_eq_univ
        hg hg_one hg_mul hf hc
  exact ⟨ζ, η, hζ, hζc, hη, hζη⟩

/-- The native middle projection is onto when the inner closure lies in the middle cover and
outer closures lie in larger coordinate discs. -/
theorem middleProjection_surjective
    (g : ι → ι → X → ℂ)
    (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hW : ∀ i, (W i : Set X) ⊆ (e i).source) (h' : ∀ i, W' i ≤ W i)
    (hR : ∀ i, eball (c i) (R i) ⊆ (e i).target)
    (hU : ∀ i, U i = (e i).source ∩ e i ⁻¹' eball (c i) (R i))
    (hKW : ∀ i, IsCompact (closure (W i : Set X)))
    (hWU : ∀ i, closure (W i : Set X) ⊆ U i) (hcov : IsOpenCover W')
    (hIW : ∀ i, closure (W'' i : Set X) ⊆ W' i)
    (hg : ∀ i j, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (g i j) (U i ∩ U j))
    (hg_one : ∀ i, ∀ x ∈ W' i, g i i x = 1)
    (hg_mul : ∀ i j k, ∀ x ∈ U i ∩ U j ∩ U k, g i j x * g j k x = g i k x) :
    Function.Surjective (middleProjection (W'' := W'') g hW h'
      (fun i ↦ subset_closure.trans (hIW i))) := by
  let h'' : ∀ i, W'' i ≤ W' i := fun i ↦ subset_closure.trans (hIW i)
  intro ξ
  obtain ⟨ζ, η, hζ, hζc, hη, hζη⟩ :=
    exists_extended_cocycle_of_middle g he hW h' hR hU hKW hWU hcov hg hg_one hg_mul ξ
  have hKeW (i : ι) : closure (W i : Set X) ⊆ (e i).source := by
    intro x hx
    have hxU := hWU i hx
    rw [hU i] at hxU
    exact hxU.1
  have houter := exists_cocycle_representative_eq (e := e) (W := W) (U := U)
    g he hKW hWU hKeW ζ hζ hζc
  obtain ⟨Z, hZc, hZ⟩ := houter
  have hKI (i : ι) : IsCompact (closure (W'' i : Set X)) :=
    (hKW i).of_isClosed_subset isClosed_closure
      (fun x hx ↦ subset_closure (h' i (hIW i hx)))
  choose H hH using fun i ↦ exists_representative_eq (e := e i) (V := W'' i)
    (S := W' i) (f := η i) (he i) (hKI i) (hIW i)
    (fun x hx ↦ hW i (h' i (hIW i hx))) (hη i)
  have hneg (i : ι) (x : X) (hx : x ∈ W'' i) :
      BergmanSpace.representative ((-H) i) (e i x) = -η i x := by
    rw [Pi.neg_apply, BergmanSpace.representative_neg _
      ((e i).map_mem_imageOpens (hW i (h' i (h'' i hx))) hx), hH i x hx]
  have ht : (Z, ξ.val, -H) ∈ compatibleTriples g hW h' h'' := by
    rw [mem_compatibleTriples_iff]
    refine ⟨hZc, ξ.property, fun i j x hx ↦ ?_⟩
    rw [hZ i j x ⟨h' i (h'' i hx.1), h' j (h'' j hx.2)⟩,
      hneg j x hx.2, hneg i x hx.1]
    have hh := hζη i j x ⟨h'' i hx.1, h'' j hx.2⟩
    simp only [smul_eq_mul] at hh
    linear_combination -hh
  exact ⟨⟨(Z, ξ.val, -H), ht⟩, Subtype.ext (coe_middleProjection g hW h' h'' _)⟩

omit [Finite ι] in
/-- One positive constant bounds a lift of every native middle cocycle in its native norm. -/
theorem exists_uniform_middle_lift [Fintype ι]
    (g : ι → ι → X → ℂ)
    (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hW : ∀ i, (W i : Set X) ⊆ (e i).source) (h' : ∀ i, W' i ≤ W i)
    (hR : ∀ i, eball (c i) (R i) ⊆ (e i).target)
    (hU : ∀ i, U i = (e i).source ∩ e i ⁻¹' eball (c i) (R i))
    (hKW : ∀ i, IsCompact (closure (W i : Set X)))
    (hWU : ∀ i, closure (W i : Set X) ⊆ U i) (hcov : IsOpenCover W')
    (hIW : ∀ i, closure (W'' i : Set X) ⊆ W' i)
    (hg : ∀ i j, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (g i j) (U i ∩ U j))
    (hg_one : ∀ i, ∀ x ∈ W' i, g i i x = 1)
    (hg_mul : ∀ i j k, ∀ x ∈ U i ∩ U j ∩ U k, g i j x * g j k x = g i k x) :
    ∃ C > 0, ∀ ξ : cocycles₁ g (subset_source_of_le hW h'),
      ∃ t : compatibleTriples (e := e) (W := W) (W' := W') (W'' := W'')
        g hW h' (fun i ↦ subset_closure.trans (hIW i)),
        middleProjection (W'' := W'') g hW h' (fun i ↦ subset_closure.trans (hIW i)) t = ξ ∧
          ‖t‖ ≤ C * ‖ξ‖ := by
  let T : compatibleTriples (e := e) (W := W) (W' := W') (W'' := W'')
        g hW h' (fun i ↦ subset_closure.trans (hIW i)) →L[ℂ]
      cocycles₁ g (subset_source_of_le hW h') :=
    middleProjection (e := e) (W := W) (W' := W') (W'' := W'') g hW h'
      (fun i ↦ subset_closure.trans (hIW i))
  have hT : Function.Surjective T :=
    middleProjection_surjective g he hW h' hR hU hKW hWU hcov hIW hg hg_one hg_mul
  -- Native instance search through the imported subtype exceeds the stock heartbeat budget.
  -- Explicit source and target avoid unification through the unexposed middle projection.
  have : CompleteSpace (compatibleTriples (e := e) (W := W) (W' := W') (W'' := W'')
      g hW h' (fun i ↦ subset_closure.trans (hIW i))) :=
    completeSpace_compatibleTriples g hW h' (fun i ↦ subset_closure.trans (hIW i))
  exact ContinuousLinearMap.exists_preimage_norm_le
    (σ := RingHom.id ℂ) (σ' := RingHom.id ℂ)
    (E := compatibleTriples (e := e) (W := W) (W' := W') (W'' := W'')
      g hW h' (fun i ↦ subset_closure.trans (hIW i)))
    (F := cocycles₁ (e := e) (W := W') g (subset_source_of_le hW h')) T hT

omit [Finite ι] in
/-- Positive coordinate balls at radii `r, 2r, 3r, 4r, 5r` give uniformly bounded native lifts.
The radius-`2r` cover normalizes the transition factors; the middle family has radius `3r`. -/
theorem exists_uniform_middle_lift_preimageBall [Fintype ι]
    (e : ι → OpenPartialHomeomorph X ℂ) (c : ι → ℂ) (r : ι → ℝ)
    (g : ι → ι → X → ℂ)
    (he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℂ) 1 X)
    (hr : ∀ i, 0 < r i) (hclosed : ∀ i, closedBall (c i) (5 * r i) ⊆ (e i).target)
    (hcover : IsOpenCover fun i ↦ (e i).preimageBall (c i) (r i))
    (hg : ∀ i j, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (g i j)
      ((e i).preimageBall (c i) (5 * r i) ⊓ (e j).preimageBall (c j) (5 * r j)))
    (hg_one : ∀ i, ∀ x ∈ (e i).preimageBall (c i) (2 * r i), g i i x = 1)
    (hg_mul : ∀ i j k, ∀ x ∈ (e i).preimageBall (c i) (5 * r i) ⊓
      (e j).preimageBall (c j) (5 * r j) ⊓ (e k).preimageBall (c k) (5 * r k),
        g i j x * g j k x = g i k x) :
    let hW := fun i ↦ (e i).preimageBall_subset_source (c := c i) (r := 4 * r i)
    let h' := fun i ↦ (e i).preimageBall_mono
      (mul_le_mul_of_nonneg_right (by norm_num : (3 : ℝ) ≤ 4) (hr i).le)
    let h'' := fun i ↦ (e i).preimageBall_mono
      (le_mul_of_one_le_left (hr i).le (by norm_num : (1 : ℝ) ≤ 3))
    ∃ C > 0, ∀ ξ : cocycles₁ g (subset_source_of_le hW h'),
      ∃ t : compatibleTriples g hW h' h'',
        middleProjection g hW h' h'' t = ξ ∧ ‖t‖ ≤ C * ‖ξ‖ := by
  dsimp only
  have hsmall (i : ι) (a : ℝ) (ha : a ≤ 5) :
      closedBall (c i) (a * r i) ⊆ (e i).target :=
    (closedBall_subset_closedBall (mul_le_mul_of_nonneg_right ha (hr i).le)).trans (hclosed i)
  have hcov (a : ℝ) (ha : 1 ≤ a) :
      IsOpenCover fun i ↦ (e i).preimageBall (c i) (a * r i) := by
    apply IsOpenCover.mk
    apply top_unique
    rw [← hcover.iSup_eq_top]
    exact iSup_mono fun i ↦ (e i).preimageBall_mono (le_mul_of_one_le_left (hr i).le ha)
  have hd (i : ι) (x : X) (hx : x ∈ (e i).preimageBall (c i) (3 * r i)) : g i i x = 1 := by
    obtain ⟨j, hj⟩ := (hcov 2 (by norm_num)).exists_mem x
    have hi5 := (e i).preimageBall_mono
      (mul_le_mul_of_nonneg_right (by norm_num : (3 : ℝ) ≤ 5) (hr i).le) hx
    have hj5 := (e j).preimageBall_mono
      (mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 5) (hr j).le) hj
    calc
      g i i x = g i j x * g j i x := (hg_mul i j i x ⟨⟨hi5, hj5⟩, hi5⟩).symm
      _ = g j i x * g i j x := mul_comm _ _
      _ = g j j x := hg_mul j i j x ⟨⟨hj5, hi5⟩, hj5⟩
      _ = 1 := hg_one j x hj
  apply exists_uniform_middle_lift (c := c) (R := fun i ↦ ENNReal.ofReal (5 * r i))
    (U := fun i ↦ (e i).preimageBall (c i) (5 * r i)) g he
  · intro i
    rw [Metric.eball_ofReal]
    exact ball_subset_closedBall.trans (hclosed i)
  · intro i
    simp only [OpenPartialHomeomorph.coe_preimageBall, Metric.eball_ofReal]
  · exact fun i ↦ (e i).isCompact_closure_preimageBall (hsmall i 4 (by norm_num))
  · exact fun i ↦ (e i).closure_preimageBall_subset (hsmall i 4 (by norm_num))
      (mul_lt_mul_of_pos_right (by norm_num : (4 : ℝ) < 5) (hr i))
  · exact hcov 3 (by norm_num)
  · intro i
    simpa only [one_mul] using (e i).closure_preimageBall_subset (hsmall i 1 (by norm_num))
      (mul_lt_mul_of_pos_right (by norm_num : (1 : ℝ) < 3) (hr i))
  · exact hg
  · exact hd
  · exact hg_mul

end TauCeti.RiemannSurface.ChartBergman
