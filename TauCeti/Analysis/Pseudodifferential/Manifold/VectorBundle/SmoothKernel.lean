/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.SmoothKernel
public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.Smoothing
public import TauCeti.Topology.VectorBundle.Dual
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension
import TauCeti.Topology.Algebra.Support

/-!
# Operators with smooth kernels between vector bundles

Let `M` be a manifold modelled on `ℝⁿ`, let `E`, `F` be smooth complex vector bundles over `M`
with model fibres `V` and `W`, and let `μ` be a measure on `M` with a smooth density in every
chart. A **kernel** from `E` to `F` assigns to each pair of points `(x, y)` a continuous linear
map `K(x, y) : E_y → F_x`; an operator `P : Γ(E) → Γ(F)` is the integral operator of `K` when

`P s (x) = ∫ K(x, y) (s y) dμ(y)`

for every smooth section `s`. The fibres of `F` carry no norm, so the integral is read weakly: for
every continuous linear functional `φ` on `F_x`,

`φ (P s x) = ∫ φ (K(x, y) (s y)) dμ(y)`.

This determines `P s x`, since continuous linear functionals separate the points of a fibre
(`TauCeti.separatingDual_fiber`). The kernel is **smooth** when it is smooth in trivializations:
for trivializations `t` of `E` and `t'` of `F` in their atlases, the matrix
`(x, y) ↦ t'ₓ ∘ K(x, y) ∘ t_y⁻¹ : V → W` is smooth on the product of their base sets.

This file shows that an integral operator with a smooth compactly supported kernel is an operator
of order `-∞` between the bundles (`TauCeti.sectionSmoothingPseudodifferentialOperators`), as in
Hörmander (III, §18.1). This is the bundle version of
`TauCeti.mem_smoothingPseudodifferentialOperators_of_forall_apply_eq_integral` for operators on
functions. Integral operators with smooth kernels are the remainders of the pseudodifferential
calculus between bundles, and the finite-rank operators of elliptic theory, such as the projections
onto spans of finitely many smooth compactly supported sections, can be written in this form.

* `TauCeti.isSectionProperlySupported_of_forall_apply_eq_integral`: an operator with a compactly
  supported kernel is properly supported. If `K` vanishes off a compact set `C ⊆ M × M`, the
  outputs are supported in the first projection of `C`, and the operator only sees its input on
  the second projection. No smoothness and no density are needed here.
* `TauCeti.sectionEntry_apply_eq_integral`: the matrix entry `f ↦ χ ℓ(t' (P (f ψ t⁻¹ v)))` of an
  integral operator (`TauCeti.sectionEntry`) is the scalar integral operator with kernel
  `χ(x) ψ(y) ℓ(t'ₓ (K(x, y) (t_y⁻¹ v)))`, a smooth compactly supported function on `M × M` when `K`
  is smooth and compactly supported.
* `TauCeti.mem_sectionSmoothingPseudodifferentialOperators_of_forall_apply_eq_integral`:
  **an operator with a smooth compactly supported kernel has order `-∞`.** Its entries are scalar
  integral operators with smooth compactly supported kernels, hence of order `-∞` on `M`, and an
  operator between bundles has order `-∞` exactly when it is properly supported and all its
  entries do (`TauCeti.mem_sectionSmoothingPseudodifferentialOperators_iff_sectionEntry`).

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1 (the operators
  of order `-∞` are those with smooth kernels).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8.
-/

public section

noncomputable section

open Bundle MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M] [T2Space M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  {E : M → Type*} [TopologicalSpace (TotalSpace V E)] [∀ x, AddCommGroup (E x)]
  [∀ x, Module ℝ (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)] [FiberBundle V E]
  [VectorBundle ℝ V E] [VectorBundle ℂ V E]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {F : M → Type*} [TopologicalSpace (TotalSpace W F)] [∀ x, AddCommGroup (F x)]
  [∀ x, Module ℝ (F x)] [∀ x, Module ℂ (F x)] [∀ x, TopologicalSpace (F x)] [FiberBundle W F]
  [VectorBundle ℝ W F] [VectorBundle ℂ W F]
  [MeasurableSpace M] {μ : Measure M} {K : ∀ x y : M, E y →L[ℂ] F x}
  {P : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯}

/-- **Operators with compactly supported kernels between bundles are properly supported.** If
`φ (P s x) = ∫ φ (K(x, y) (s y)) dμ(y)` for every continuous linear functional `φ` on `F_x`, for a
kernel `K` vanishing off a compact set `C ⊆ M × M`, then `P s` is supported in the first projection
of `C`, and `P s` vanishes as soon as `s` vanishes on the second projection. -/
theorem isSectionProperlySupported_of_forall_apply_eq_integral
    (hKc : ∃ C : Set (M × M), IsCompact C ∧ ∀ x y, (x, y) ∉ C → K x y = 0)
    (hP : ∀ s x (φ : F x →L[ℂ] ℂ), φ (P s x) = ∫ y, φ (K x y (s y)) ∂μ) :
    IsSectionProperlySupported P := by
  obtain ⟨C, hC, hK⟩ := hKc
  -- The kernel vanishes at `(x, y)` unless `x ∈ A` and `y ∈ B`, the projections of `C`.
  set A := Prod.fst '' C
  set B := Prod.snd '' C
  have hA : IsCompact A := hC.image continuous_fst
  have hB : IsCompact B := hC.image continuous_snd
  have hK' {x y : M} (h : x ∉ A ∨ y ∉ B) : K x y = 0 :=
    hK x y fun hxy ↦ h.elim (· ⟨_, hxy, rfl⟩) (· ⟨_, hxy, rfl⟩)
  -- A value of `P s` is zero as soon as every term of its integral is.
  have hzero {s : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯} {x : M} (h : ∀ y, K x y (s y) = 0) :
      P s x = 0 := by
    have := separatingDual_fiber (𝕜 := ℂ) (F := W) F x
    refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℂ) fun φ ↦ ?_
    simp [hP, h]
  refine isSectionProperlySupported_iff.2 fun _ _ ↦
    ⟨A ∪ B, hA.union hB, fun s _ ↦ ?_, fun s hs x _ ↦ hzero fun y ↦ ?_⟩
  · refine ((ContMDiffSection.tsupport_subset_iff hA.isClosed).2 fun x hx ↦
      hzero fun y ↦ ?_).trans subset_union_left
    simp [hK' (.inl hx)]
  · by_cases hy : y ∈ B
    · simp [hs.self_of_nhdsSet y (mem_union_right A hy)]
    · simp [hK' (.inr hy)]

variable [ContMDiffVectorBundle ∞ V E 𝓘(ℝ, CoordinateSpace n)]
  [ContMDiffVectorBundle ∞ W F 𝓘(ℝ, CoordinateSpace n)]
  (t : Trivialization V (π V E)) [MemTrivializationAtlas t]
  (ψ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hψ : tsupport ψ ⊆ t.baseSet) (v : V)
  (t' : Trivialization W (π W F)) [MemTrivializationAtlas t']
  (χ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hχ : tsupport χ ⊆ t'.baseSet) (ℓ : W →L[ℂ] ℂ)

omit [T2Space M] [∀ x, Module ℝ (E x)] [VectorBundle ℝ V E] [∀ x, Module ℝ (F x)]
  [VectorBundle ℝ W F] [MeasurableSpace M] [ContMDiffVectorBundle ∞ V E 𝓘(ℝ, CoordinateSpace n)]
  [ContMDiffVectorBundle ∞ W F 𝓘(ℝ, CoordinateSpace n)] in
include hψ hχ in
/-- The kernel `(x, y) ↦ χ(x) ψ(y) ℓ(t'ₓ (K(x, y) (t_y⁻¹ v)))` of a matrix entry of an integral
operator between bundles is smooth on `M × M` when `K` is smooth in the trivializations `t` and
`t'`. -/
private theorem contMDiff_entryKernel
    (hK : ContMDiffOn (𝓘(ℝ, CoordinateSpace n).prod 𝓘(ℝ, CoordinateSpace n)) 𝓘(ℝ, V →L[ℂ] W) ∞
      (fun p : M × M ↦ (t'.continuousLinearMapAt ℂ p.1).comp ((K p.1 p.2).comp (t.symmL ℂ p.2)))
      (t'.baseSet ×ˢ t.baseSet)) :
    ContMDiff (𝓘(ℝ, CoordinateSpace n).prod 𝓘(ℝ, CoordinateSpace n)) 𝓘(ℝ, ℂ) ∞
      fun p : M × M ↦
        (ψ p.2 • χ p.1) • ℓ (t'.continuousLinearMapAt ℂ p.1 (K p.1 p.2 (t.symmL ℂ p.2 v))) := by
  -- Evaluating the matrix at `v` and applying `ℓ` is a real continuous linear map.
  set L : (V →L[ℂ] W) →L[ℝ] ℂ :=
    (ℓ.restrictScalars ℝ).comp ((ContinuousLinearMap.apply ℂ W v).restrictScalars ℝ)
  have hcut : ContMDiff (𝓘(ℝ, CoordinateSpace n).prod 𝓘(ℝ, CoordinateSpace n)) 𝓘(ℝ) ∞
      fun p : M × M ↦ ψ p.2 • χ p.1 :=
    (ψ.contMDiff.comp contMDiff_snd).smul (χ.contMDiff.comp contMDiff_fst)
  have hg : ContMDiffOn (𝓘(ℝ, CoordinateSpace n).prod 𝓘(ℝ, CoordinateSpace n)) 𝓘(ℝ, ℂ) ∞
      (fun p : M × M ↦ ℓ (t'.continuousLinearMapAt ℂ p.1 (K p.1 p.2 (t.symmL ℂ p.2 v))))
      (t'.baseSet ×ˢ t.baseSet) :=
    L.contMDiff.comp_contMDiffOn hK
  exact hg.contMDiff_smul_of_tsupport_subset
    (t'.open_baseSet.prod t.open_baseSet) hcut.contMDiffOn
    ((tsupport_snd_smul_fst_subset ψ χ).trans (prod_mono hχ hψ))

omit [T2Space M] in
/-- **The entries of an integral operator between bundles.** If `P` is the integral operator of a
kernel `K`, in the sense that `φ (P s x) = ∫ φ (K(x, y) (s y)) dμ(y)` for every continuous linear
functional `φ` on `F_x`, then its matrix entry `f ↦ χ ℓ(t' (P (f ψ t⁻¹ v)))` is the scalar integral
operator with kernel `χ(x) ψ(y) ℓ(t'ₓ (K(x, y) (t_y⁻¹ v)))`. -/
theorem sectionEntry_apply_eq_integral
    (hP : ∀ s x (φ : F x →L[ℂ] ℂ), φ (P s x) = ∫ y, φ (K x y (s y)) ∂μ)
    (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M) :
    sectionEntry t ψ hψ v t' χ hχ ℓ P f x =
      ∫ y, (ψ y • χ x) • ℓ (t'.continuousLinearMapAt ℂ x (K x y (t.symmL ℂ y v))) * f y ∂μ := by
  rw [sectionEntry_apply, ← ℓ.comp_apply, hP, ← integral_smul]
  refine integral_congr_ae (.of_forall fun y ↦ ?_)
  -- Off the base set of `t` the cutoff `ψ` vanishes, and on it the frame section is `t⁻¹ (ψ v)`.
  by_cases hy : y ∈ t.baseSet
  · simp only [ContMDiffSection.smul_apply_of_normedAlgebra,
      t.cutoffFrameSection_apply_eq_symmL ψ hψ v hy, map_smul, ContinuousLinearMap.comp_apply,
      smul_eq_mul, Complex.real_smul]
    push_cast
    ring
  · have hψy : ψ y = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hy (hψ h)
    simp [hψy]

omit [∀ x, Module ℝ (E x)] [VectorBundle ℝ V E] [∀ x, Module ℝ (F x)] [VectorBundle ℝ W F]
  [MeasurableSpace M] [ContMDiffVectorBundle ∞ V E 𝓘(ℝ, CoordinateSpace n)]
  [ContMDiffVectorBundle ∞ W F 𝓘(ℝ, CoordinateSpace n)] in
/-- The kernel of a matrix entry of an integral operator between bundles has compact support when
`K` vanishes off a compact set. -/
private theorem hasCompactSupport_entryKernel {C : Set (M × M)} (hC : IsCompact C)
    (hK : ∀ x y, (x, y) ∉ C → K x y = 0) :
    HasCompactSupport fun p : M × M ↦
      (ψ p.2 • χ p.1) • ℓ (t'.continuousLinearMapAt ℂ p.1 (K p.1 p.2 (t.symmL ℂ p.2 v))) :=
  HasCompactSupport.intro hC fun p hp ↦ by simp [hK p.1 p.2 hp]

/-- **Operators with smooth kernels between bundles have order `-∞`.** Let `μ` be a measure on `M`
with a smooth density `ρ` in every chart `e` of the maximal atlas, in the sense that
`∫ f dμ = ∫_{e.target} ρ(y) f(e⁻¹ y) dy` for continuous compactly supported functions `f`
supported in the chart source. Let `K(x, y) : E_y → F_x` be a kernel that vanishes off a compact
subset of `M × M` and is smooth in trivializations: for trivializations `t` of `E` and `t'` of `F`
in their atlases, `(x, y) ↦ t'ₓ ∘ K(x, y) ∘ t_y⁻¹` is smooth on the product of their base sets. If
`P` is the integral operator of `K`, that is, `φ (P s x) = ∫ φ (K(x, y) (s y)) dμ(y)` for every
smooth section `s` and every continuous linear functional `φ` on `F_x`, then `P` has order `-∞`. -/
theorem mem_sectionSmoothingPseudodifferentialOperators_of_forall_apply_eq_integral
    (hμ : ∀ e : OpenPartialHomeomorph M (CoordinateSpace n),
      e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M →
        ∃ ρ : CoordinateSpace n → ℝ, ContDiffOn ℝ ∞ ρ e.target ∧
          ∀ f : M → ℂ, Continuous f → HasCompactSupport f → tsupport f ⊆ e.source →
            ∫ x, f x ∂μ = ∫ y in e.target, (ρ y : ℂ) * f (e.symm y))
    (hK : ∀ (t : Trivialization V (π V E)) [MemTrivializationAtlas t]
      (t' : Trivialization W (π W F)) [MemTrivializationAtlas t'],
        ContMDiffOn (𝓘(ℝ, CoordinateSpace n).prod 𝓘(ℝ, CoordinateSpace n)) 𝓘(ℝ, V →L[ℂ] W) ∞
          (fun p : M × M ↦ (t'.continuousLinearMapAt ℂ p.1).comp
            ((K p.1 p.2).comp (t.symmL ℂ p.2)))
          (t'.baseSet ×ˢ t.baseSet))
    (hKc : ∃ C : Set (M × M), IsCompact C ∧ ∀ x y, (x, y) ∉ C → K x y = 0)
    (hP : ∀ s x (φ : F x →L[ℂ] ℂ), φ (P s x) = ∫ y, φ (K x y (s y)) ∂μ) :
    P ∈ sectionSmoothingPseudodifferentialOperators := by
  obtain ⟨C, hC, hKC⟩ := hKc
  refine mem_sectionSmoothingPseudodifferentialOperators_iff_sectionEntry.2
    ⟨isSectionProperlySupported_of_forall_apply_eq_integral ⟨C, hC, hKC⟩ hP,
      fun t _ ψ hψ v t' _ χ hχ ℓ ↦ ?_⟩
  -- Each entry is a scalar integral operator with a smooth compactly supported kernel.
  exact mem_smoothingPseudodifferentialOperators_of_forall_apply_eq_integral hμ
    (contMDiff_entryKernel t ψ hψ v t' χ hχ ℓ (hK t t'))
    (hasCompactSupport_entryKernel t ψ v t' χ ℓ hC hKC)
    (sectionEntry_apply_eq_integral t ψ hψ v t' χ hχ ℓ hP)

end TauCeti
