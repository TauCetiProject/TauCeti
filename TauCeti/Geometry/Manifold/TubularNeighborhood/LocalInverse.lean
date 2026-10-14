/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.TubularNeighborhood.Euclidean
public import TauCeti.Geometry.Manifold.TubularNeighborhood.SmoothMap
public import TauCeti.Geometry.Manifold.VectorBundle.Tangent

/-!
# Local inverses to normal addition

A Euclidean immersion admits a smooth local retraction to its source manifold near every
image point. The displacement from the retracted point is normal to the immersion. With
the projected normal-bundle atlas, the retraction and displacement together give a smooth
local right inverse to normal addition, recovering the zero section on the immersed patch.
Normal addition is consequently a local diffeomorphism at every zero-section point.

These results transport `exists_contDiffOn_normalRetraction` through a manifold chart.
They apply to individual immersed patches, including self-intersecting immersions; they
do not assert a globally defined retraction or nearest-point uniqueness.

Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Theorem 6.24.
-/

public section

noncomputable section

open Set Function Bundle Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {E V H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  {n : WithTop ℕ∞} [IsManifold I (n + 1) M] {f : M → V}

/-- Near any point of a `C^(n+1)` Euclidean immersion there is a `C^n` local retraction
to its source, with normal displacement. Its domain contains the image of an open source
patch, and the retraction recovers every point of that patch. -/
theorem exists_contMDiffOn_normalRetraction
    (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f) (x₀ : M)
    (himm : Injective (mfderiv I 𝓘(ℝ, V) f x₀)) (hn : 1 ≤ n) :
    ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧
      ∃ t : Set V, IsOpen t ∧ f x₀ ∈ t ∧ f '' U ⊆ t ∧
        ∃ r : V → M, ContMDiffOn 𝓘(ℝ, V) I n r t ∧
          (∀ x ∈ U, r (f x) = x) ∧
          ∀ y ∈ t, r y ∈ U ∧ y - f (r y) ∈ normalSubspace I f (r y) := by
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let e := extChartAt I x₀
  let g : E → V := f ∘ e.symm
  have hgd : ContDiffOn ℝ (n + 1) g e.target :=
    contMDiffOn_iff_contDiffOn.mp (hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm x₀))
  have hx₀ : x₀ ∈ e.source := mem_extChartAt_source x₀
  have hdiff : ∀ x ∈ e.source, DifferentiableAt ℝ g (e x) := fun x hx =>
    (hgd.contDiffAt ((isOpen_extChartAt_target x₀).mem_nhds (e.map_source hx))).differentiableAt
      (by simp)
  obtain ⟨S, hS, hcenter, hSt, t, ht, -, hSimage, q, hq, hleft, hnormal⟩ :=
    exists_contDiffOn_normalRetraction hgd (isOpen_extChartAt_target x₀) (e.map_source hx₀)
      (fderiv_comp_extChartAt_symm_injective hx₀ (hdiff x₀ hx₀) himm) hn
  let U := e.source ∩ e ⁻¹' S
  have hU : IsOpen U := (continuousOn_extChartAt x₀).isOpen_inter_preimage
    (isOpen_extChartAt_source x₀) hS
  have hUt : f '' U ⊆ t := by
    rintro _ ⟨x, hx, rfl⟩
    simpa only [g, Function.comp_apply, e.left_inv hx.1] using hSimage ⟨e x, hx.2, rfl⟩
  have hqt : MapsTo q t e.target := fun y hy => hSt (hnormal y hy).1
  have hr : ContMDiffOn 𝓘(ℝ, V) I n (e.symm ∘ q) t :=
    ((contMDiffOn_extChartAt_symm (n := n + 1) x₀).of_le
      (by simp : n ≤ n + 1)).comp
      (contMDiffOn_iff_contDiffOn.mpr hq) hqt
  refine ⟨U, hU, ⟨hx₀, hcenter⟩, t, ht, hUt ⟨x₀, ⟨hx₀, hcenter⟩, rfl⟩,
    hUt, e.symm ∘ q, hr, ?_, ?_⟩
  · intro x hx
    have hqfx : q (f x) = e x := by
      simpa only [g, Function.comp_apply, e.left_inv hx.1] using hleft (e x) hx.2
    simp only [Function.comp_apply, hqfx, e.left_inv hx.1]
  · intro y hy
    have hqy := hnormal y hy
    have htarget := hSt hqy.1
    have hsource := e.map_target htarget
    refine ⟨⟨hsource, ?_⟩, ?_⟩
    · simpa only [mem_preimage, Function.comp_apply, e.right_inv htarget] using hqy.1
    · rw [Function.comp_apply, normalSubspace_eq_of_mem_source hsource (hdiff _ hsource),
        e.right_inv htarget]
      exact hqy.2

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Normal addition has a `C^n` local right inverse near every image point of a
`C^(n+1)` immersion. On a source patch this inverse recovers the zero section. The
normal bundle carries its projected atlas, with model fibre `F` of the codimension. -/
theorem exists_contMDiff_normalBundle_add_rightInverse
    (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E)
    (x₀ : M) (hn : 1 ≤ n) :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI := normalFiberBundle (hf.of_le le_add_self) himm hdim
    ∃ U : Set M, IsOpen U ∧ x₀ ∈ U ∧
      ∃ t : TopologicalSpace.Opens V, f '' U ⊆ t ∧
        ∃ R : t → TotalSpace F (fun x => normalSubspace I f x),
          ContMDiff 𝓘(ℝ, V) (I.prod 𝓘(ℝ, F)) n R ∧
          (∀ y, (R y).proj ∈ U) ∧
          (∀ y, f (R y).proj + ((R y).2 : V) = y) ∧
          ∀ x ∈ U, ∀ y : t, (y : V) = f x →
            R y = zeroSection F (fun x => normalSubspace I f x) x := by
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  let := normalFiberBundle (hf.of_le le_add_self) himm hdim
  obtain ⟨U, hU, hx₀, s, hs, -, hUs, r, hr, hleft, hnormal⟩ :=
    exists_contMDiffOn_normalRetraction hf x₀ (himm x₀) hn
  let t : TopologicalSpace.Opens V := ⟨s, hs⟩
  let R : t → TotalSpace F (fun x => normalSubspace I f x) :=
    fun y => ⟨r y, ⟨y - f (r y), (hnormal y y.property).2⟩⟩
  have hr' : ContMDiff 𝓘(ℝ, V) I n (fun y : t => r y) :=
    hr.comp_contMDiff contMDiff_subtype_val (fun y => y.property)
  have hR : ContMDiff 𝓘(ℝ, V) (I.prod 𝓘(ℝ, F)) n R := by
    apply (contMDiff_normalBundle_iff hf himm hdim).mpr
    refine ⟨hr', ?_⟩
    simpa only [R, sub_eq_add_neg, Function.comp_def, Pi.add_def] using
      (contMDiff_subtype_val (U := t)).add
      (contDiff_neg.contMDiff.comp ((hf.of_le (by simp : n ≤ n + 1)).comp hr'))
  refine ⟨U, hU, hx₀, t, hUs, R, hR, (fun y => (hnormal y y.property).1), ?_, ?_⟩
  · intro y
    exact add_sub_cancel _ _
  · intro x hx y hy
    apply (isEmbedding_totalSpace_normalSubspace (F := F) f).injective
    exact Prod.ext (by simpa only [R, zeroSection, hy] using hleft x hx)
      (by simp [R, hy, hleft x hx, zeroSection])

/-- Normal addition is a `C^n` local diffeomorphism at every zero-section point of the
normal bundle of a `C^(n+1)` Euclidean immersion. No global embedding or compactness
assumption is needed. -/
theorem isLocalDiffeomorphAt_normalBundle_add_zeroSection
    (hf : ContMDiff I 𝓘(ℝ, V) (n + 1) f)
    (himm : ∀ x, Injective (mfderiv I 𝓘(ℝ, V) f x))
    (hdim : Module.finrank ℝ F = Module.finrank ℝ V - Module.finrank ℝ E)
    (x₀ : M) (hn : 1 ≤ n) :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    letI := normalFiberBundle (hf.of_le le_add_self) himm hdim
    letI := normalVectorBundle (hf.of_le le_add_self) himm hdim
    letI := normalContMDiffVectorBundle hf himm hdim
    IsLocalDiffeomorphAt (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, V) n
      (fun p : TotalSpace F (fun x => normalSubspace I f x) => f p.proj + (p.2 : V))
      (zeroSection F (fun x => normalSubspace I f x) x₀) := by
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  have : IsManifold I n M := .of_le (n := n + 1) (by simp)
  let := normalFiberBundle (hf.of_le le_add_self) himm hdim
  let := normalVectorBundle (hf.of_le le_add_self) himm hdim
  let := normalContMDiffVectorBundle hf himm hdim
  let A : TotalSpace F (fun x => normalSubspace I f x) → V :=
    fun p => f p.proj + (p.2 : V)
  let z := zeroSection F (fun x => normalSubspace I f x) x₀
  have hA : ContMDiff (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, V) n A :=
    contMDiff_normalBundle_add hf himm hdim
  obtain ⟨U, -, hx₀, t, hUt, R, hR, -, hright, hzero⟩ :=
    exists_contMDiff_normalBundle_add_rightInverse hf himm hdim x₀ hn
  let y₀ : t := ⟨f x₀, hUt ⟨x₀, hx₀, rfl⟩⟩
  have hRy : R y₀ = z := hzero x₀ hx₀ y₀ rfl
  have hcomp : A ∘ R = (Subtype.val : t → V) := funext hright
  have hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le (by simp) hn)
  -- The local right inverse makes the differential of normal addition surjective.
  have hderiv := mfderiv_comp y₀ (hA.mdifferentiableAt hn0) (hR.mdifferentiableAt hn0)
  rw [hcomp, Manifold.mfderiv_subtype_val, hRy] at hderiv
  have hsurj : Surjective (mfderiv (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, V) A z) := by
    have h : Surjective (Manifold.tangentSpaceOpenEquiv
        (I := 𝓘(ℝ, V)) y₀).toContinuousLinearMap :=
      (Manifold.tangentSpaceOpenEquiv (I := 𝓘(ℝ, V)) y₀).surjective
    rw [hderiv] at h
    exact Function.Surjective.of_comp
      (f := mfderiv (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, V) A z)
      (g := mfderiv 𝓘(ℝ, V) (I.prod 𝓘(ℝ, F)) R y₀) h
  have hEV : Module.finrank ℝ E ≤ Module.finrank ℝ V :=
    LinearMap.finrank_le_finrank_of_injective (himm x₀)
  have hEF : Module.finrank ℝ (E × F) = Module.finrank ℝ V := by
    rw [Module.finrank_prod, hdim]
    omega
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hEF).mpr hsurj
  let e := (LinearEquiv.ofBijective
    (mfderiv (I.prod 𝓘(ℝ, F)) 𝓘(ℝ, V) A z).toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  apply isLocalDiffeomorphAt_of_mfderiv_eq hA.contMDiffOn isOpen_univ (mem_univ z)
    (BoundarylessManifold.isInteriorPoint (I := I.prod 𝓘(ℝ, F))) hn (e := e)
  -- This equivalence is constructed from the differential itself.
  rfl

end TauCeti
