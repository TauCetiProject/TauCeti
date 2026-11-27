/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Bott.Basic
import TauCeti.Analysis.Calculus.Morse.Bott.Perturbation
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Geometry.Manifold.Morse.LocalDiffeomorph
import TauCeti.Geometry.Manifold.Morse.Submersion
import TauCeti.Geometry.Manifold.VectorBundle.Submersion
import TauCeti.Geometry.Manifold.VectorBundle.ZeroSection
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# Perturbing a Morse–Bott function by a function on a critical submanifold

Let `i : S → M` be a nondegenerate (Morse–Bott) critical submanifold of a function `f` on a
boundaryless manifold, and let `Θ` be a partial diffeomorphism from the total space of a vector
bundle over `S` to `M` which sends each zero vector `0_s` to `i s`, such as a tubular neighbourhood,
or the Morse–Bott tubular neighbourhood (`exists_morseBott_partialDiffeomorph_normalBundle`, in the
namespace `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`). Then `p = proj ∘ Θ⁻¹` is a
retraction of a neighbourhood of `i(S)` onto `S`, and a function `φ` on `S` extends to the function
`φ ∘ p`, constant along the fibres of `Θ`. This file proves that, near `i(S)`, the critical points
of `f + φ ∘ p` are exactly the points `i s` with `s` critical for `φ`; that `i s` is nondegenerate
for `f + φ ∘ p` exactly when `s` is nondegenerate for `φ`; and that the Morse index there is
`ind_φ(s) + ind_f(i s)`, the index of `φ` plus the rank of the negative normal bundle. The
neighbourhood depends only on `f`, `i` and `Θ`, not on `φ`. So when `φ` is a Morse function on `S`,
every critical point of `f + φ ∘ p` near `i(S)` is nondegenerate, and there is one of index `j + λ`
for each critical point of `φ` of index `j`, where `λ` is the index of the critical submanifold.
This is the local step in perturbing a Morse–Bott function into a Morse function by Morse functions
on its critical submanifolds; globally `φ ∘ p` is cut off away from `i(S)` and multiplied by a small
constant.

The statement is first proved on the total space of a vector bundle `E → B` for a function `g`
whose zero section is a nondegenerate critical submanifold: at each zero vector `0_b`, `g` is `C²`
and critical, and the kernel of its critical Hessian is the tangent space of the zero section.
In the chart of the total space at `0_a`, which is a chart of `B` times a trivialization of `E`,
the function `x ↦ g x + φ x.proj` reads `(y, w) ↦ G (y, w) + Φ y`, where `G` and `Φ` are the
coordinate expressions of `g` and `φ`. This is the Euclidean situation of
`TauCeti.eventually_forall_fderiv_add_comp_fst_eq_zero_iff`, `TauCeti.morseIndex_add_comp_fst` and
`TauCeti.isNondegenerateCriticalPoint_add_comp_fst_iff`: the zero section of `G` is critical and
its Hessian has kernel the base directions, because the differential of the zero section is the
first summand inclusion (`TauCeti.Bundle.mfderiv_zeroSection`).

For a Morse–Bott critical submanifold, `g = f ∘ Θ`. Its zero section is a nondegenerate critical
submanifold because `Θ` is a local diffeomorphism sending it to `i`: the differential of `Θ`
carries the kernel of the critical Hessian of `f ∘ Θ` at `0_s` into that of `f` at `i s`, which is
the tangent space of `i`, the image under `dΘ` of the tangent space of the zero section. Critical
points, nondegeneracy and Morse indices are then carried across `Θ`
(`IsLocalDiffeomorphAt.mem_criticalPoints_comp_iff`,
`IsLocalDiffeomorphAt.isManifoldNondegenerateCriticalPoint_comp_iff`,
`TauCeti.IsRegularPoint.manifoldMorseIndex_comp`).

## Main results

* `TauCeti.exists_isOpen_forall_mem_criticalPoints_add_comp_proj_iff`: on a vector bundle, near a
  Morse–Bott zero section, the critical points of `x ↦ g x + φ x.proj` are the zero vectors over
  the critical points of `φ`.
* `TauCeti.isManifoldNondegenerateCriticalPoint_add_comp_proj_zeroSection_iff` and
  `TauCeti.manifoldMorseIndex_add_comp_proj_zeroSection`: their nondegeneracy and Morse indices.

In the namespace `TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold`:

* `exists_isOpen_forall_mem_criticalPoints_add_comp_iff`: near a Morse–Bott critical submanifold
  `i`, the critical points of `f + φ ∘ proj ∘ Θ⁻¹` are the points `i s` with `s` critical for `φ`.
* `isManifoldNondegenerateCriticalPoint_add_comp_iff` and `manifoldMorseIndex_add_comp`: their
  nondegeneracy and Morse indices.

## References

* A. Banyaga and D. E. Hurtubise, *Morse–Bott homology*, Transactions of the American
  Mathematical Society 362 (2010), 3997–4043 (perturbing a Morse–Bott function by Morse functions
  on its critical submanifolds).
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §6.2.
-/

public section

open Bundle Filter Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

/-! ### On the total space of a vector bundle -/

section VectorBundle

variable {EB HB B F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [IB.Boundaryless] [TopologicalSpace B] [ChartedSpace HB B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {E : B → Type*}
  [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  [IsManifold IB 2 B] [ContMDiffVectorBundle 2 F E IB]
  {g : TotalSpace F E → ℝ}

omit [IB.Boundaryless] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E] [IsManifold IB 2 B]
  [ContMDiffVectorBundle 2 F E IB] in
/-- In the chart of the total space at `0_a`, the function `x ↦ g x + φ x.proj` reads
`z ↦ G z + Φ z.1` near every point over the base set of the trivialization at `a`, where `G` and
`Φ` are the coordinate expressions of `g` in that chart and of `φ` in the chart of the base. -/
private theorem comp_extChartAt_symm_eventuallyEq (a : B) (φ : B → ℝ) {z₀ : EB × F}
    (hz₀ : z₀.1 ∈ (extChartAt IB a).target)
    (hz₀' : (extChartAt IB a).symm z₀.1 ∈ (trivializationAt F E a).baseSet) :
    (fun x : TotalSpace F E ↦ g x + φ x.proj) ∘
        (extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F E a)).symm =ᶠ[𝓝 z₀]
      fun z ↦ (g ∘ (extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F E a)).symm) z +
        (φ ∘ (extChartAt IB a).symm) z.1 := by
  have hbase : (fun z : EB × F ↦ (extChartAt IB a).symm z.1) ⁻¹'
      (trivializationAt F E a).baseSet ∈ 𝓝 z₀ :=
    ((continuousAt_extChartAt_symm'' hz₀).comp continuousAt_fst).preimage_mem_nhds
      ((trivializationAt F E a).open_baseSet.mem_nhds hz₀')
  filter_upwards [hbase] with z hz
  have h := Bundle.extChartAt_symm_apply_of_mem_baseSet (IB := IB) (zeroSection F E a)
    (y := z.1) hz z.2
  rw [Prod.mk.eta] at h
  simp only [comp_apply, h, zeroSection_proj]

omit [IB.Boundaryless] [∀ b, Module ℝ (E b)] [VectorBundle ℝ F E] [IsManifold IB 2 B]
  [ContMDiffVectorBundle 2 F E IB] in
/-- The case of `comp_extChartAt_symm_eventuallyEq` at the image `(b', 0)` of the zero vector `0_b`
in the chart of the total space at `0_b`. -/
private theorem comp_extChartAt_symm_eventuallyEq_self (b : B) (φ : B → ℝ) :
    (fun x : TotalSpace F E ↦ g x + φ x.proj) ∘
        (extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F E b)).symm =ᶠ[𝓝 (extChartAt IB b b, 0)]
      fun z ↦ (g ∘ (extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F E b)).symm) z +
        (φ ∘ (extChartAt IB b).symm) z.1 :=
  comp_extChartAt_symm_eventuallyEq b φ (mem_extChartAt_target b)
    (by rw [extChartAt_to_inv]; exact mem_baseSet_trivializationAt F E b)

omit [IsManifold IB 2 B] [ContMDiffVectorBundle 2 F E IB] in
/-- The coordinate expression of a function which is `C²` at the zero vector `0_a`, in the chart of
the total space at `0_a`, is `C²` at the image `(a', 0)` of `0_a`. -/
private theorem chart_contDiffAt (a : B)
    (hg : ContMDiffAt (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ) 2 g (zeroSection F E a)) :
    ContDiffAt ℝ 2 (g ∘ (extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F E a)).symm)
      (extChartAt IB a a, 0) :=
  Bundle.extChartAt_zeroSection_self (IB := IB) (F := F) (V := E) a ▸
    hg.contDiffAt_comp_extChartAt_symm

/-- If every zero vector is a critical point of `g`, then the coordinate expression of `g` in the
chart of the total space at `0_a` is critical along the zero section near the image of `0_a`. -/
private theorem chart_eventually_fderiv_eq_zero (a : B)
    (hcrit : ∀ b, zeroSection F E b ∈ criticalPoints (IB.prod 𝓘(ℝ, F)) g) :
    ∀ᶠ y in 𝓝 (extChartAt IB a a),
      fderiv ℝ (g ∘ (extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F E a)).symm) (y, 0) = 0 := by
  have : IsManifold (IB.prod 𝓘(ℝ, F)) 1 (TotalSpace F E) := .of_le (n := 2) (by norm_num)
  have ha : (extChartAt IB a).symm (extChartAt IB a a) ∈
      (trivializationAt F E a).baseSet ∩ (chartAt HB a).source := by
    rw [extChartAt_to_inv]
    exact ⟨mem_baseSet_trivializationAt F E a, mem_chart_source HB a⟩
  filter_upwards [extChartAt_target_mem_nhds (I := IB) a,
    (continuousAt_extChartAt_symm a).preimage_mem_nhds
      (((trivializationAt F E a).open_baseSet.inter (chartAt HB a).open_source).mem_nhds ha)]
    with y hy hyb
  -- The zero vector `0_b` over the point `b` with coordinate `y` is read as `(y, 0)`.
  set b := (extChartAt IB a).symm y
  have hb : zeroSection F E b ∈ (extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F E a)).source :=
    (Bundle.mem_extChartAt_source_iff _ _).2 ⟨hyb.1, by rw [extChartAt_source]; exact hyb.2⟩
  have hτb : extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F E a) (zeroSection F E b) = (y, 0) := by
    rw [Bundle.extChartAt_zeroSection_of_mem_baseSet a hyb.1, (extChartAt IB a).right_inv hy]
  rw [← hτb, ← mvfderiv_eq_zero_iff_fderiv_comp_extChartAt_symm_eq_zero hb]
  exact mem_criticalPoints.1 (hcrit b)

omit [IB.Boundaryless] [IsManifold IB 2 B] [ContMDiffVectorBundle 2 F E IB] in
/-- If the kernel of the critical Hessian of `g` at `0_a` is the tangent space of the zero section,
then the kernel of the Hessian of the coordinate expression of `g` in the chart of the total space
at `0_a`, at the image of `0_a`, consists of base directions. -/
private theorem chart_ker_le (a : B)
    (hker : (criticalHessian (IB.prod 𝓘(ℝ, F)) g (zeroSection F E a)).ker ≤
      (mfderiv IB (IB.prod 𝓘(ℝ, F)) (zeroSection F E) a).toLinearMap.range) :
    (fderiv ℝ (fderiv ℝ (g ∘ (extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F E a)).symm))
      (extChartAt IB a a, 0)).ker ≤ LinearMap.range (LinearMap.inl ℝ EB F) := by
  -- In the preferred charts the differential of the zero section is the first summand inclusion.
  rw [Bundle.mfderiv_zeroSection, criticalHessian_def, Bundle.extChartAt_zeroSection_self,
    ContinuousLinearMap.coe_inl] at hker
  -- `hker` is about `LinearMap.inl ℝ (TangentSpace IB a) F`, and `TangentSpace IB a` unfolds to
  -- the model space `EB`.
  exact hker

variable [FiniteDimensional ℝ F]

/-- Near each zero vector `0_a`, the critical points of `x ↦ g x + φ x.proj` are the zero vectors
over the critical points of `φ`, for every `φ`. -/
private theorem eventually_forall_mem_criticalPoints_add_comp_proj_iff (a : B)
    (hg : ContMDiffAt (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ) 2 g (zeroSection F E a))
    (hcrit : ∀ b, zeroSection F E b ∈ criticalPoints (IB.prod 𝓘(ℝ, F)) g)
    (hker : (criticalHessian (IB.prod 𝓘(ℝ, F)) g (zeroSection F E a)).ker ≤
      (mfderiv IB (IB.prod 𝓘(ℝ, F)) (zeroSection F E) a).toLinearMap.range) :
    ∀ᶠ x in 𝓝 (zeroSection F E a), ∀ φ : B → ℝ, MDifferentiableAt IB 𝓘(ℝ) φ x.proj →
      (x ∈ criticalPoints (IB.prod 𝓘(ℝ, F)) (fun y ↦ g y + φ y.proj) ↔
        x = zeroSection F E x.proj ∧ x.proj ∈ criticalPoints IB φ) := by
  have : IsManifold (IB.prod 𝓘(ℝ, F)) 1 (TotalSpace F E) := .of_le (n := 2) (by norm_num)
  have : IsManifold IB 1 B := .of_le (n := 2) (by norm_num)
  set τ := extChartAt (IB.prod 𝓘(ℝ, F)) (zeroSection F E a)
  -- The Euclidean statement for the coordinate expression of `g` near `τ 0_a = (a', 0)`.
  have hP := eventually_forall_fderiv_add_comp_fst_eq_zero_iff (chart_contDiffAt a hg)
    (chart_eventually_fderiv_eq_zero a hcrit) (chart_ker_le a hker)
  rw [← Bundle.extChartAt_zeroSection_self (IB := IB) (F := F) (V := E) a] at hP
  have hsrc : ∀ᶠ x in 𝓝 (zeroSection F E a),
      x.proj ∈ (trivializationAt F E a).baseSet ∩ (chartAt HB a).source :=
    (FiberBundle.continuous_proj F E).continuousAt.preimage_mem_nhds
      (((trivializationAt F E a).open_baseSet.inter (chartAt HB a).open_source).mem_nhds
        ⟨mem_baseSet_trivializationAt F E a, mem_chart_source HB a⟩)
  filter_upwards [(continuousAt_extChartAt (zeroSection F E a)).eventually hP, hsrc]
    with x hx ⟨hxe, hxc⟩ φ hφ
  have hxc' : x.proj ∈ (extChartAt IB a).source := by rwa [extChartAt_source]
  have hxs : x ∈ τ.source := (Bundle.mem_extChartAt_source_iff _ _).2 ⟨hxe, hxc'⟩
  have hτx : τ x = (extChartAt IB a x.proj, (trivializationAt F E a x).2) :=
    Bundle.extChartAt_apply_of_mem_baseSet _ hxe
  -- The coordinate expression of `φ` is differentiable at the coordinate of `x.proj`.
  have hΦ : DifferentiableAt ℝ (φ ∘ (extChartAt IB a).symm) (τ x).1 := by
    have h := (mdifferentiableAt_iff_source_of_mem_source hxc).1 hφ
    rw [IB.range_eq_univ, mdifferentiableWithinAt_univ, mdifferentiableAt_iff_differentiableAt] at h
    rwa [hτx]
  have heq := comp_extChartAt_symm_eventuallyEq (g := g) a φ (z₀ := τ x)
    (by rw [hτx]; exact (extChartAt IB a).map_source hxc')
    (by rw [hτx, (extChartAt IB a).left_inv hxc']; exact hxe)
  -- `zeroSection F E b` is `⟨b, 0⟩` by definition.
  have hx0 : x.snd = 0 ↔ x = zeroSection F E x.proj := by
    obtain ⟨b, v⟩ := x
    exact TotalSpace.mk_inj.symm
  rw [mem_criticalPoints, mvfderiv_eq_zero_iff_fderiv_comp_extChartAt_symm_eq_zero hxs,
    heq.fderiv_eq, hx _ hΦ, mem_criticalPoints,
    mvfderiv_eq_zero_iff_fderiv_comp_extChartAt_symm_eq_zero hxc', hτx]
  simp only [(trivializationAt F E a).snd_apply_eq_zero_iff ℝ hxe, hx0]

/-- **Critical points of a perturbation by a function on the base, near a Morse–Bott zero
section.** Let `g` be a function on the total space of a `C²` vector bundle `E → B` with
finite-dimensional fibres over a boundaryless manifold, whose zero section is a
nondegenerate critical submanifold: at every zero vector `0_b`, `g` is `C²` and critical, and the
kernel of its critical Hessian is the tangent space of the zero section. Then there is an open
neighbourhood `N` of the zero section, depending only on `g`, such that for every function `φ` on
`B` and every `x ∈ N` at whose base point `φ` is differentiable, `x` is a critical point of
`y ↦ g y + φ y.proj` exactly when `x` is a zero vector over a critical point of `φ`. -/
theorem exists_isOpen_forall_mem_criticalPoints_add_comp_proj_iff
    (hg : ∀ b, ContMDiffAt (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ) 2 g (zeroSection F E b))
    (hcrit : ∀ b, zeroSection F E b ∈ criticalPoints (IB.prod 𝓘(ℝ, F)) g)
    (hker : ∀ b, (criticalHessian (IB.prod 𝓘(ℝ, F)) g (zeroSection F E b)).ker ≤
      (mfderiv IB (IB.prod 𝓘(ℝ, F)) (zeroSection F E) b).toLinearMap.range) :
    ∃ N : Set (TotalSpace F E), IsOpen N ∧ range (zeroSection F E) ⊆ N ∧
      ∀ x ∈ N, ∀ φ : B → ℝ, MDifferentiableAt IB 𝓘(ℝ) φ x.proj →
        (x ∈ criticalPoints (IB.prod 𝓘(ℝ, F)) (fun y ↦ g y + φ y.proj) ↔
          x = zeroSection F E x.proj ∧ x.proj ∈ criticalPoints IB φ) := by
  refine ⟨interior {x | ∀ φ : B → ℝ, MDifferentiableAt IB 𝓘(ℝ) φ x.proj →
      (x ∈ criticalPoints (IB.prod 𝓘(ℝ, F)) (fun y ↦ g y + φ y.proj) ↔
        x = zeroSection F E x.proj ∧ x.proj ∈ criticalPoints IB φ)}, isOpen_interior, ?_,
    fun x hx ↦ interior_subset hx⟩
  rintro _ ⟨a, rfl⟩
  exact mem_interior_iff_mem_nhds.2
    (eventually_forall_mem_criticalPoints_add_comp_proj_iff a (hg a) hcrit (hker a))

/-- **Nondegenerate critical points of a perturbation by a function on the base, at a Morse–Bott
zero section.** If the zero section of `g` is a nondegenerate critical submanifold, as in
`TauCeti.exists_isOpen_forall_mem_criticalPoints_add_comp_proj_iff`, and `φ` is `C²` at `b`, then
the zero vector `0_b` is a nondegenerate critical point of `y ↦ g y + φ y.proj` exactly when `b` is
a nondegenerate critical point of `φ`. -/
theorem isManifoldNondegenerateCriticalPoint_add_comp_proj_zeroSection_iff
    [FiniteDimensional ℝ EB] {b : B}
    (hg : ContMDiffAt (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ) 2 g (zeroSection F E b))
    (hcrit : ∀ b, zeroSection F E b ∈ criticalPoints (IB.prod 𝓘(ℝ, F)) g)
    (hker : (criticalHessian (IB.prod 𝓘(ℝ, F)) g (zeroSection F E b)).ker ≤
      (mfderiv IB (IB.prod 𝓘(ℝ, F)) (zeroSection F E) b).toLinearMap.range)
    {φ : B → ℝ} (hφ : ContMDiffAt IB 𝓘(ℝ) 2 φ b) :
    IsManifoldNondegenerateCriticalPoint (IB.prod 𝓘(ℝ, F)) (fun y ↦ g y + φ y.proj)
        (zeroSection F E b) ↔ IsManifoldNondegenerateCriticalPoint IB φ b := by
  have heq := comp_extChartAt_symm_eventuallyEq_self (IB := IB) (g := g) b φ
  rw [isManifoldNondegenerateCriticalPoint_iff, isManifoldNondegenerateCriticalPoint_iff,
    Bundle.extChartAt_zeroSection_self,
    ← isNondegenerateCriticalPoint_add_comp_fst_iff (chart_contDiffAt b hg)
      (chart_eventually_fderiv_eq_zero b hcrit) (chart_ker_le b hker)
      hφ.contDiffAt_comp_extChartAt_symm]
  exact heq.isNondegenerateCriticalPoint_iff

/-- **The Morse index of a perturbation by a function on the base, at a critical zero section.**
If `g` is `C²` at `0_b`, every zero vector is a critical point of `g`, and `φ` is `C²` at `b`, then
the Morse index of `y ↦ g y + φ y.proj` at the zero vector `0_b` is the Morse index of `φ` at `b`
plus that of `g` at `0_b`. -/
theorem manifoldMorseIndex_add_comp_proj_zeroSection [FiniteDimensional ℝ EB] {b : B}
    (hg : ContMDiffAt (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ) 2 g (zeroSection F E b))
    (hcrit : ∀ b, zeroSection F E b ∈ criticalPoints (IB.prod 𝓘(ℝ, F)) g)
    {φ : B → ℝ} (hφ : ContMDiffAt IB 𝓘(ℝ) 2 φ b) :
    manifoldMorseIndex (IB.prod 𝓘(ℝ, F)) (fun y ↦ g y + φ y.proj) (zeroSection F E b) =
      manifoldMorseIndex IB φ b + manifoldMorseIndex (IB.prod 𝓘(ℝ, F)) g (zeroSection F E b) := by
  have heq := comp_extChartAt_symm_eventuallyEq_self (IB := IB) (g := g) b φ
  rw [manifoldMorseIndex_def, manifoldMorseIndex_def, manifoldMorseIndex_def,
    Bundle.extChartAt_zeroSection_self, morseIndex_congr_of_eventuallyEq heq]
  exact morseIndex_add_comp_fst (chart_contDiffAt b hg) (chart_eventually_fderiv_eq_zero b hcrit)
    hφ.contDiffAt_comp_extChartAt_symm

end VectorBundle

/-! ### Along a Morse–Bott critical submanifold -/

section Submanifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless] [TopologicalSpace S]
  [ChartedSpace H' S] [IsManifold J 2 S]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {V : S → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ s, AddCommGroup (V s)] [∀ s, Module ℝ (V s)]
  [∀ s, TopologicalSpace (V s)] [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle 2 F V J]
  {n m : ℕ∞ω} {i : SmoothEmbedding J I n S M} {f : M → ℝ}
  {Θ : PartialDiffeomorph (J.prod 𝓘(ℝ, F)) I (TotalSpace F V) M m}

omit [I.Boundaryless] [FiniteDimensional ℝ E'] [J.Boundaryless] [IsManifold J 2 S]
  [FiniteDimensional ℝ F] [∀ s, AddCommGroup (V s)] [∀ s, Module ℝ (V s)] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle 2 F V J] in
/-- Near `Θ 0_s = i s`, the function `f + φ ∘ proj ∘ Θ⁻¹` pulls back along `Θ` to
`x ↦ (f ∘ Θ) x + φ x.proj`. -/
private theorem add_comp_eventuallyEq (φ : S → ℝ) {x : TotalSpace F V} (hx : x ∈ Θ.source) :
    (fun y ↦ f y + φ (Θ.symm y).proj) ∘ Θ =ᶠ[𝓝 x] fun y ↦ (f ∘ Θ) y + φ y.proj := by
  filter_upwards [Θ.open_source.mem_nhds hx] with y hy
  simp only [comp_apply]
  rw [show Θ.symm (Θ y) = y from Θ.toPartialEquiv.left_inv hy]


namespace SmoothEmbedding.IsNondegenerateCriticalSubmanifold

variable (h : i.IsNondegenerateCriticalSubmanifold f) (hm : 2 ≤ m)
  (hΘ : ∀ s, zeroSection F V s ∈ Θ.source) (hΘi : ∀ s, Θ (zeroSection F V s) = i s)
include h hm hΘ hΘi

omit [FiniteDimensional ℝ E'] [IsManifold J 2 S] [FiniteDimensional ℝ F]
  [ContMDiffVectorBundle 2 F V J] in
/-- Pulled back along a partial diffeomorphism `Θ` from the total space of a vector bundle which
sends the zero section to `i`, a Morse–Bott critical submanifold `i` of `f` becomes a Morse–Bott
zero section of `f ∘ Θ`: at every zero vector `f ∘ Θ` is `C²` and critical, and the kernel of its
critical Hessian is the tangent space of the zero section. -/
private theorem zeroSection_hypotheses :
    (∀ s, ContMDiffAt (J.prod 𝓘(ℝ, F)) 𝓘(ℝ) 2 (f ∘ Θ) (zeroSection F V s)) ∧
      (∀ s, zeroSection F V s ∈ criticalPoints (J.prod 𝓘(ℝ, F)) (f ∘ Θ)) ∧
      ∀ s, (criticalHessian (J.prod 𝓘(ℝ, F)) (f ∘ Θ) (zeroSection F V s)).ker ≤
        (mfderiv J (J.prod 𝓘(ℝ, F)) (zeroSection F V) s).toLinearMap.range := by
  have hm0 : m ≠ 0 := (two_pos.trans_le hm).ne'
  have hloc (s : S) := PartialDiffeomorph.isLocalDiffeomorphAt _ _ _ Θ (hΘ s)
  have hf (s : S) : ContMDiffAt I 𝓘(ℝ) 2 f (Θ (zeroSection F V s)) := hΘi s ▸ h.contMDiffAt s
  have hcrit (s : S) : Θ (zeroSection F V s) ∈ criticalPoints I f :=
    hΘi s ▸ h.mem_criticalPoints s
  refine ⟨fun s ↦ (hf s).comp _ ((hloc s).contMDiffAt.of_le hm),
    fun s ↦ ((hloc s).mem_criticalPoints_comp_iff (one_le_two.trans hm)).2 (hcrit s),
    fun s v hv ↦ ?_⟩
  have hD := (hloc s).isInvertible_mfderiv hm0
  -- `dΘ v` lies in the kernel of the critical Hessian of `f` at `i s`, which is the tangent space
  -- of the critical submanifold. Every tangent space `TangentSpace I _` unfolds to the model space
  -- `E`, so `dΘ v`, a vector at `Θ 0_s`, may be read at `i s`.
  let d : TangentSpace I (i s) := mfderiv (J.prod 𝓘(ℝ, F)) I Θ (zeroSection F V s) v
  have hv' : d ∈ (criticalHessian I f (i s)).ker := by
    have hd := (hloc s).ker_criticalHessian_eq_map hm (hf s) (hcrit s) ▸
      Submodule.mem_map_of_mem hv
    rwa [hΘi s] at hd
  obtain ⟨u, hu⟩ := LinearMap.mem_range.1 (h.ker_criticalHessian_le s hv')
  refine ⟨u, hD.injective ?_⟩
  -- Since `i = Θ ∘ 0`, the differential of `i` is `dΘ` composed with that of the zero section.
  have hi : (i : S → M) = Θ ∘ zeroSection F V := funext fun s ↦ (hΘi s).symm
  have hchain : mfderiv J I (i : S → M) s =
      (mfderiv (J.prod 𝓘(ℝ, F)) I Θ (zeroSection F V s)).comp
        (mfderiv J (J.prod 𝓘(ℝ, F)) (zeroSection F V) s) := by
    rw [hi]
    exact mfderiv_comp s (Θ.mdifferentiableAt hm0 (hΘ s))
      ((contMDiff_zeroSection ℝ V).mdifferentiableAt (n := 2) two_ne_zero)
  rw [hchain] at hu
  -- `hu` reads `(dΘ ∘L d0) u = d` with `d = dΘ v`; it closes the goal `dΘ (d0 u) = dΘ v` by
  -- unfolding the composition, the `let` and the tangent spaces at `i s` and `Θ 0_s` (both `E`).
  -- A rewrite with `ContinuousLinearMap.comp_apply` is not possible, since `hchain` is itself only
  -- well typed up to this identification of tangent spaces.
  exact hu

omit [FiniteDimensional ℝ E'] in
/-- **Critical points of a perturbation by a function on a Morse–Bott critical submanifold.** Let
`i : S → M` be a nondegenerate critical submanifold of `f`, with `S` boundaryless, and let `Θ` be
a `C^m` partial diffeomorphism, `m ≥ 2`, from the total space of a `C²` vector bundle over `S` with
finite-dimensional fibres to `M`, sending each zero vector `0_s` to `i s`, such as a tubular
neighbourhood. Then there is an open neighbourhood `U` of the image of
`i`, depending only on `f`, `i` and `Θ`, with the following property. For every function `φ` on
`S` and every `x ∈ U` at whose image `(Θ⁻¹ x).proj` the function `φ` is differentiable, `x` is a
critical point of `f + φ ∘ proj ∘ Θ⁻¹` exactly when `x = i s` for a critical point `s` of `φ`. -/
theorem exists_isOpen_forall_mem_criticalPoints_add_comp_iff :
    ∃ U : Set M, IsOpen U ∧ range i ⊆ U ∧ U ⊆ Θ.target ∧
      ∀ x ∈ U, ∀ φ : S → ℝ, MDifferentiableAt J 𝓘(ℝ) φ (Θ.symm x).proj →
        (x ∈ criticalPoints I (fun y ↦ f y + φ (Θ.symm y).proj) ↔
          x ∈ i '' criticalPoints J φ) := by
  obtain ⟨hg, hcrit, hker⟩ := zeroSection_hypotheses h hm hΘ hΘi
  obtain ⟨N, hNo, hZN, hN⟩ :=
    exists_isOpen_forall_mem_criticalPoints_add_comp_proj_iff hg hcrit hker
  have hleft (z : TotalSpace F V) (hz : z ∈ Θ.source) : Θ.symm (Θ z) = z :=
    Θ.toPartialEquiv.left_inv hz
  refine ⟨Θ.target ∩ Θ.symm ⁻¹' N, Θ.toOpenPartialHomeomorph.isOpen_inter_preimage_symm hNo, ?_,
    inter_subset_left, fun x ⟨hx, hxN⟩ φ hφ ↦ ?_⟩
  · rintro _ ⟨s, rfl⟩
    rw [← hΘi s]
    exact ⟨Θ.toPartialEquiv.map_source (hΘ s), by
      rw [mem_preimage, hleft _ (hΘ s)]
      exact hZN (mem_range_self s)⟩
  -- Pull back along `Θ` to the point `y = Θ⁻¹ x` of the total space.
  set y := Θ.symm x
  have hy : y ∈ Θ.source := Θ.toPartialEquiv.map_target hx
  have hxy : Θ y = x := Θ.toPartialEquiv.right_inv hx
  rw [← hxy, ← (PartialDiffeomorph.isLocalDiffeomorphAt _ _ _ Θ hy).mem_criticalPoints_comp_iff
    (one_le_two.trans hm), (add_comp_eventuallyEq φ hy).mem_criticalPoints_iff, hN y hxN φ hφ]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨y.proj, h₂, by rw [← hΘi, ← h₁]⟩
  · rintro ⟨s, hs, hsy⟩
    have hys : y = zeroSection F V s := by
      rw [← hleft y hy, ← hsy, ← hΘi s, hleft _ (hΘ s)]
    rw [hys, zeroSection_proj]
    exact ⟨rfl, hs⟩

/-- **Nondegenerate critical points of a perturbation by a function on a Morse–Bott critical
submanifold.** With `i` and `Θ` as in
`exists_isOpen_forall_mem_criticalPoints_add_comp_iff`,
if `φ` is `C²` at `s`, then `i s` is a nondegenerate critical point of `f + φ ∘ proj ∘ Θ⁻¹` exactly
when `s` is a nondegenerate critical point of `φ`. -/
theorem isManifoldNondegenerateCriticalPoint_add_comp_iff (s : S) {φ : S → ℝ}
    (hφ : ContMDiffAt J 𝓘(ℝ) 2 φ s) :
    IsManifoldNondegenerateCriticalPoint I (fun y ↦ f y + φ (Θ.symm y).proj) (i s) ↔
      IsManifoldNondegenerateCriticalPoint J φ s := by
  obtain ⟨hg, hcrit, hker⟩ := zeroSection_hypotheses h hm hΘ hΘi
  have heq := add_comp_eventuallyEq (f := f) φ (hΘ s)
  rw [← hΘi s, ← (PartialDiffeomorph.isLocalDiffeomorphAt _ _ _ Θ
    (hΘ s)).isManifoldNondegenerateCriticalPoint_comp_iff hm]
  exact heq.isManifoldNondegenerateCriticalPoint_iff.trans
    (isManifoldNondegenerateCriticalPoint_add_comp_proj_zeroSection_iff (hg s) hcrit (hker s) hφ)

/-- **The Morse index of a perturbation by a function on a Morse–Bott critical submanifold.** With
`i` and `Θ` as in
`exists_isOpen_forall_mem_criticalPoints_add_comp_iff`,
if `s` is a critical point of a function `φ` which is `C²` there, then the Morse index of
`f + φ ∘ proj ∘ Θ⁻¹` at `i s` is the Morse index of `φ` at `s` plus that of `f` at `i s`, the rank
of the negative normal bundle of the critical submanifold. -/
theorem manifoldMorseIndex_add_comp (s : S) {φ : S → ℝ} (hφ : ContMDiffAt J 𝓘(ℝ) 2 φ s)
    (hs : s ∈ criticalPoints J φ) :
    manifoldMorseIndex I (fun y ↦ f y + φ (Θ.symm y).proj) (i s) =
      manifoldMorseIndex J φ s + manifoldMorseIndex I f (i s) := by
  obtain ⟨hg, hcrit, hker⟩ := zeroSection_hypotheses h hm hΘ hΘi
  obtain ⟨N, -, hZN, hN⟩ := exists_isOpen_forall_mem_criticalPoints_add_comp_proj_iff hg hcrit hker
  have hloc := PartialDiffeomorph.isLocalDiffeomorphAt _ _ _ Θ (hΘ s)
  have hΘ₂ := hloc.contMDiffAt.of_le hm
  have hreg : IsRegularPoint (J.prod 𝓘(ℝ, F)) I Θ (zeroSection F V s) :=
    isRegularPoint_iff.2 (hloc.isInvertible_mfderiv (two_pos.trans_le hm).ne').surjective
  have heq := add_comp_eventuallyEq (f := f) φ (hΘ s)
  -- The perturbed function is `C²` and critical at `Θ 0_s = i s`.
  have hF : ContMDiffAt I 𝓘(ℝ) 2 (fun y ↦ f y + φ (Θ.symm y).proj) (Θ (zeroSection F V s)) :=
    (hloc.contMDiffAt_comp_iff hm).1 <| ((hg s).add
      (hφ.comp (zeroSection F V s) (contMDiffAt_proj V))).congr_of_eventuallyEq heq
  have hcritF : Θ (zeroSection F V s) ∈ criticalPoints I (fun y ↦ f y + φ (Θ.symm y).proj) := by
    rw [← hloc.mem_criticalPoints_comp_iff (one_le_two.trans hm), heq.mem_criticalPoints_iff,
      hN _ (hZN (mem_range_self s)) φ (hφ.mdifferentiableAt two_ne_zero)]
    exact ⟨rfl, hs⟩
  rw [← hΘi s, ← hreg.manifoldMorseIndex_comp hF hΘ₂ hcritF,
    manifoldMorseIndex_congr_of_eventuallyEq heq, manifoldMorseIndex_add_comp_proj_zeroSection
      (hg s) hcrit hφ, hreg.manifoldMorseIndex_comp (hΘi s ▸ h.contMDiffAt s) hΘ₂
      (hΘi s ▸ h.mem_criticalPoints s)]

end SmoothEmbedding.IsNondegenerateCriticalSubmanifold

end Submanifold

end TauCeti
