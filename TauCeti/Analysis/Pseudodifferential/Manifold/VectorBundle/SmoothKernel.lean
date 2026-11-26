/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.Kernel
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
for trivializations `t` of `E` and `t'` of `F` in their atlases and every `v` in the model fibre of
`E`, the map `(x, y) ↦ t'ₓ (K(x, y) (t_y⁻¹ v))` is smooth on the product of their base sets. For a
finite-dimensional model fibre this is smoothness of the matrix `t'ₓ ∘ K(x, y) ∘ t_y⁻¹`.

This file shows that the integral operators with smooth compactly supported kernels are operators
of order `-∞` between the bundles (`TauCeti.sectionSmoothingPseudodifferentialOperators`), and
that on a compact manifold every operator of order `-∞` between bundles with finite-dimensional
fibres is of this form, as in Hörmander (III, §18.1). These are the bundle versions of
`TauCeti.mem_smoothingPseudodifferentialOperators_of_forall_apply_eq_integral` and
`TauCeti.exists_contMDiff_forall_apply_eq_integral_of_mem_smoothingPseudodifferentialOperators`
for operators on functions. Integral operators with smooth kernels are the remainders of the
pseudodifferential calculus between bundles, and the finite-rank operators of elliptic theory, such
as the projections onto spans of finitely many smooth sections, can be written in this form.

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
* `TauCeti.exists_forall_apply_eq_integral_of_mem_sectionSmoothingPseudodifferentialOperators`:
  **conversely, on a compact manifold of positive dimension, an operator of order `-∞` has a smooth
  kernel**, for a measure with smooth nonvanishing chart densities. Finitely many cut-off frames
  `ψᵢ tᵢ⁻¹ bⱼ` of `E` and `ψ'ₖ t'ₖ⁻¹ b'ₗ` of `F`, with coefficients `ρᵢ bⱼ*(tᵢ ·)` and
  `ρ'ₖ b'ₗ*(t'ₖ ·)`, expand every section
  (`IsCompact.exists_sum_sum_cutoffFrameCoeff_smul_cutoffFrameSection_apply`). The entries of `P`
  in these frames have order `-∞`, so they have smooth kernels `kᵢⱼₖₗ` by the scalar theorem, and
  `K(x, y) = ∑ ρᵢ(y) ψ'ₖ(x) kᵢⱼₖₗ(x, y) bⱼ*(tᵢ ·) t'ₖ⁻¹ b'ₗ`. Each term is smooth in any pair of
  trivializations, because the coordinate changes are smooth on the overlaps of the base sets and
  the cutoffs vanish off them.
* `TauCeti.mem_sectionSmoothingPseudodifferentialOperators_iff_exists_forall_apply_eq_integral`:
  the two directions together, on a compact manifold.

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
    (hK : ContMDiffOn (𝓘(ℝ, CoordinateSpace n).prod 𝓘(ℝ, CoordinateSpace n)) 𝓘(ℝ, W) ∞
      (fun p : M × M ↦ t'.continuousLinearMapAt ℂ p.1 (K p.1 p.2 (t.symmL ℂ p.2 v)))
      (t'.baseSet ×ˢ t.baseSet)) :
    ContMDiff (𝓘(ℝ, CoordinateSpace n).prod 𝓘(ℝ, CoordinateSpace n)) 𝓘(ℝ, ℂ) ∞
      fun p : M × M ↦
        (ψ p.2 • χ p.1) • ℓ (t'.continuousLinearMapAt ℂ p.1 (K p.1 p.2 (t.symmL ℂ p.2 v))) := by
  have hcut : ContMDiff (𝓘(ℝ, CoordinateSpace n).prod 𝓘(ℝ, CoordinateSpace n)) 𝓘(ℝ) ∞
      fun p : M × M ↦ ψ p.2 • χ p.1 :=
    (ψ.contMDiff.comp contMDiff_snd).smul (χ.contMDiff.comp contMDiff_fst)
  exact ((ℓ.restrictScalars ℝ).contMDiff.comp_contMDiffOn hK).contMDiff_smul_of_tsupport_subset
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
in their atlases and every `v`, `(x, y) ↦ t'ₓ (K(x, y) (t_y⁻¹ v))` is smooth on the product of their
base sets. If
`P` is the integral operator of `K`, that is, `φ (P s x) = ∫ φ (K(x, y) (s y)) dμ(y)` for every
smooth section `s` and every continuous linear functional `φ` on `F_x`, then `P` has order `-∞`. -/
theorem mem_sectionSmoothingPseudodifferentialOperators_of_forall_apply_eq_integral
    (hμ : ∀ e : OpenPartialHomeomorph M (CoordinateSpace n),
      e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M →
        ∃ ρ : CoordinateSpace n → ℝ, ContDiffOn ℝ ∞ ρ e.target ∧
          ∀ f : M → ℂ, Continuous f → HasCompactSupport f → tsupport f ⊆ e.source →
            ∫ x, f x ∂μ = ∫ y in e.target, (ρ y : ℂ) * f (e.symm y))
    (hK : ∀ (t : Trivialization V (π V E)) [MemTrivializationAtlas t]
      (t' : Trivialization W (π W F)) [MemTrivializationAtlas t'] (v : V),
        ContMDiffOn (𝓘(ℝ, CoordinateSpace n).prod 𝓘(ℝ, CoordinateSpace n)) 𝓘(ℝ, W) ∞
          (fun p : M × M ↦ t'.continuousLinearMapAt ℂ p.1 (K p.1 p.2 (t.symmL ℂ p.2 v)))
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
    (contMDiff_entryKernel t ψ hψ v t' χ hχ ℓ (hK t t' v))
    (hasCompactSupport_entryKernel t ψ v t' χ ℓ hC hKC)
    (sectionEntry_apply_eq_integral t ψ hψ v t' χ hχ ℓ hP)

/-! ### Operators of order `-∞` on a compact manifold have smooth kernels -/

section Kernel

omit [T2Space M] [MeasurableSpace M] in
include hψ hχ in
/-- A term `(x, y) ↦ ψ(y) χ(x) k(x, y) ℓ(t_y e) t'ₓ⁻¹ w` of the kernel of an operator of order
`-∞`, read in trivializations `T` of `E` and `T'` of `F`, is smooth on the product of their base
sets, for a smooth function `k` on `M × M`. -/
private theorem contMDiffOn_frameKernelTerm (T : Trivialization V (π V E))
    [MemTrivializationAtlas T] (T' : Trivialization W (π W F)) [MemTrivializationAtlas T']
    (v : V) {k : M × M → ℂ}
    (hk : ContMDiff (𝓘(ℝ, CoordinateSpace n).prod 𝓘(ℝ, CoordinateSpace n)) 𝓘(ℝ, ℂ) ∞ k)
    (ℓ' : V →L[ℂ] ℂ) (w : W) :
    ContMDiffOn (𝓘(ℝ, CoordinateSpace n).prod 𝓘(ℝ, CoordinateSpace n)) 𝓘(ℝ, W) ∞
      (fun p : M × M ↦ ((ψ p.2 • χ p.1) • k p * ℓ' (t.continuousLinearMapAt ℂ p.2
        (T.symmL ℂ p.2 v))) • T'.continuousLinearMapAt ℂ p.1 (t'.symmL ℂ p.1 w))
      (T'.baseSet ×ˢ T.baseSet) := by
  have hcut : ContMDiff (𝓘(ℝ, CoordinateSpace n).prod 𝓘(ℝ, CoordinateSpace n)) 𝓘(ℝ) ∞
      fun p : M × M ↦ ψ p.2 • χ p.1 :=
    (ψ.contMDiff.comp contMDiff_snd).smul (χ.contMDiff.comp contMDiff_fst)
  intro p hp
  by_cases hpc : p ∈ tsupport fun p : M × M ↦ ψ p.2 • χ p.1
  · -- On the support of the cutoff, both coordinate changes are smooth near `p`.
    have hpt := (tsupport_snd_smul_fst_subset ψ χ).trans (prod_mono hχ hψ) hpc
    have hO : (t'.baseSet ∩ T'.baseSet) ×ˢ (T.baseSet ∩ t.baseSet) ∈ 𝓝 p :=
      ((t'.open_baseSet.inter T'.open_baseSet).prod (T.open_baseSet.inter t.open_baseSet)).mem_nhds
        ⟨⟨hpt.1, hp.1⟩, hp.2, hpt.2⟩
    have hy : ContMDiffOn (𝓘(ℝ, CoordinateSpace n).prod 𝓘(ℝ, CoordinateSpace n)) 𝓘(ℝ, ℂ) ∞
        (fun p : M × M ↦ ℓ' (t.continuousLinearMapAt ℂ p.2 (T.symmL ℂ p.2 v)))
        ((t'.baseSet ∩ T'.baseSet) ×ˢ (T.baseSet ∩ t.baseSet)) :=
      (ℓ'.restrictScalars ℝ).contMDiff.comp_contMDiffOn
        ((T.contMDiffOn_continuousLinearMapAt_symmL t v).comp contMDiff_snd.contMDiffOn
          fun q hq ↦ hq.2)
    have hx : ContMDiffOn (𝓘(ℝ, CoordinateSpace n).prod 𝓘(ℝ, CoordinateSpace n)) 𝓘(ℝ, W) ∞
        (fun p : M × M ↦ T'.continuousLinearMapAt ℂ p.1 (t'.symmL ℂ p.1 w))
        ((t'.baseSet ∩ T'.baseSet) ×ˢ (T.baseSet ∩ t.baseSet)) :=
      (t'.contMDiffOn_continuousLinearMapAt_symmL T' w).comp contMDiff_fst.contMDiffOn
        fun q hq ↦ hq.1
    -- Multiplication of a vector by a complex scalar is a real continuous bilinear map.
    have hc := ((hcut p).smul (hk p)).mul (hy.contMDiffAt hO)
    exact (((ContinuousLinearMap.lsmul ℝ ℂ : ℂ →L[ℝ] W →L[ℝ] W).contMDiff.contMDiffAt.comp p
      hc).clm_apply (hx.contMDiffAt hO)).contMDiffWithinAt
  · -- Off the support of the cutoff, the term vanishes near `p`.
    refine (contMDiffAt_const (c := (0 : W))).congr_of_eventuallyEq ?_ |>.contMDiffWithinAt
    filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hpc] with q hq
    rw [hq, Pi.zero_apply, zero_smul, zero_mul, zero_smul]

section FrameKernel

variable [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] {ι κ : Type*} [Fintype ι] [Fintype κ]
  (c : ι → M) (ρ : ι → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯)
  (hρ : ∀ i, tsupport (ρ i) ⊆ (trivializationAt V E (c i)).baseSet)
  (c' : κ → M) (ψ' : κ → C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯)
  (hψ' : ∀ k, tsupport (ψ' k) ⊆ (trivializationAt W F (c' k)).baseSet)
  (kk : ι → Fin (Module.finrank ℂ V) → κ → Fin (Module.finrank ℂ W) → M × M → ℂ)

/-- The kernel `(x, y) ↦ ∑ ρᵢ(y) ψ'ₖ(x) kᵢⱼₖₗ(x, y) bⱼ*(tᵢ ·) t'ₖ⁻¹ b'ₗ` assembled from scalar
kernels `kᵢⱼₖₗ` and cut-off frames, for bases `(bⱼ)` of `V` and `(b'ₗ)` of `W` and the preferred
trivializations `tᵢ` of `E` at `cᵢ` and `t'ₖ` of `F` at `c'ₖ`. It is read through the preferred
trivialization of `F` at `x`, so that it is a continuous linear map `E_y → F_x`. -/
private noncomputable def frameKernel (x y : M) : E y →L[ℂ] F x :=
  ((trivializationAt W F x).symmL ℂ x).comp (∑ k, ∑ l, ∑ i, ∑ j,
    ((ρ i y • ψ' k x) • kk i j k l (x, y)) •
      (((Module.finBasis ℂ V).coord j).toContinuousLinearMap.comp
        ((trivializationAt V E (c i)).continuousLinearMapAt ℂ y)).smulRight
        ((trivializationAt W F x).continuousLinearMapAt ℂ x
          ((trivializationAt W F (c' k)).symmL ℂ x (Module.finBasis ℂ W l))))

omit [T2Space M] [∀ x, Module ℝ (E x)] [VectorBundle ℝ V E] [∀ x, Module ℝ (F x)]
  [VectorBundle ℝ W F] [MeasurableSpace M] [ContMDiffVectorBundle ∞ V E 𝓘(ℝ, CoordinateSpace n)]
  [ContMDiffVectorBundle ∞ W F 𝓘(ℝ, CoordinateSpace n)] in
private theorem frameKernel_apply (x y : M) (e : E y) :
    frameKernel c ρ c' ψ' kk x y e = ∑ k, ∑ l, ∑ i, ∑ j,
      ((ρ i y • ψ' k x) • kk i j k l (x, y) * (Module.finBasis ℂ V).coord j
        ((trivializationAt V E (c i)).continuousLinearMapAt ℂ y e)) •
          (trivializationAt W F (c' k)).symmL ℂ x (Module.finBasis ℂ W l) := by
  simp only [frameKernel, ContinuousLinearMap.comp_apply, FunLike.coe_sum, Finset.sum_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply, map_sum, map_smul, smul_smul,
    (trivializationAt W F x).symmL_continuousLinearMapAt
      (FiberBundle.mem_baseSet_trivializationAt' x), LinearMap.coe_toContinuousLinearMap']

omit [T2Space M] [MeasurableSpace M] in
include hρ hψ' in
/-- The kernel assembled from smooth scalar kernels is smooth in trivializations. -/
private theorem contMDiffOn_frameKernel
    (hkk : ∀ i j k l,
      ContMDiff (𝓘(ℝ, CoordinateSpace n).prod 𝓘(ℝ, CoordinateSpace n)) 𝓘(ℝ, ℂ) ∞ (kk i j k l))
    (T : Trivialization V (π V E)) [MemTrivializationAtlas T] (T' : Trivialization W (π W F))
    [MemTrivializationAtlas T'] (v : V) :
    ContMDiffOn (𝓘(ℝ, CoordinateSpace n).prod 𝓘(ℝ, CoordinateSpace n)) 𝓘(ℝ, W) ∞
      (fun p : M × M ↦ T'.continuousLinearMapAt ℂ p.1 (frameKernel c ρ c' ψ' kk p.1 p.2
        (T.symmL ℂ p.2 v)))
      (T'.baseSet ×ˢ T.baseSet) := by
  -- Read in `T` and `T'`, the kernel is a finite sum of smooth terms.
  refine (contMDiffOn_finsetSum (t := .univ) fun k _ ↦ contMDiffOn_finsetSum (t := .univ)
    fun l _ ↦ contMDiffOn_finsetSum (t := .univ) fun i _ ↦ contMDiffOn_finsetSum (t := .univ)
      fun j _ ↦ contMDiffOn_frameKernelTerm (trivializationAt V E (c i)) (ρ i) (hρ i)
        (trivializationAt W F (c' k)) (ψ' k) (hψ' k) T T' v (hkk i j k l)
        ((Module.finBasis ℂ V).coord j).toContinuousLinearMap (Module.finBasis ℂ W l)).congr
    fun p _ ↦ ?_
  simp only [frameKernel_apply, map_sum, map_smul, LinearMap.coe_toContinuousLinearMap']

omit [T2Space M] [∀ x, Module ℝ (F x)] [VectorBundle ℝ W F]
  [ContMDiffVectorBundle ∞ W F 𝓘(ℝ, CoordinateSpace n)] in
include hρ in
/-- The integral of the kernel assembled from smooth scalar kernels against a smooth section `s`,
paired with a functional `φ`, splits into the integrals of the scalar kernels against the cut-off
frame coefficients of `s`. -/
private theorem integral_frameKernel [CompactSpace M] [OpensMeasurableSpace M]
    [IsFiniteMeasureOnCompacts μ]
    (hkk : ∀ i j k l,
      ContMDiff (𝓘(ℝ, CoordinateSpace n).prod 𝓘(ℝ, CoordinateSpace n)) 𝓘(ℝ, ℂ) ∞ (kk i j k l))
    (s : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) (x : M) (φ : F x →L[ℂ] ℂ) :
    ∫ y, φ (frameKernel c ρ c' ψ' kk x y (s y)) ∂μ = ∑ k, ∑ l, ∑ i, ∑ j,
      ∫ y, kk i j k l (x, y) * (trivializationAt V E (c i)).cutoffFrameCoeff (ρ i) (hρ i)
        ((Module.finBasis ℂ V).coord j).toContinuousLinearMap s y *
        ((ψ' k x : ℂ) * φ ((trivializationAt W F (c' k)).symmL ℂ x (Module.finBasis ℂ W l)))
        ∂μ := by
  -- Each term is continuous, hence integrable on the compact manifold.
  have hint (i : ι) (j : Fin (Module.finrank ℂ V)) (k : κ) (l : Fin (Module.finrank ℂ W))
      (z : ℂ) : Integrable (fun y ↦ kk i j k l (x, y) *
        (trivializationAt V E (c i)).cutoffFrameCoeff (ρ i) (hρ i)
          ((Module.finBasis ℂ V).coord j).toContinuousLinearMap s y * z) μ :=
    ((((hkk i j k l).continuous.comp (continuous_const.prodMk continuous_id)).mul
      (ContMDiffMap.contMDiff _).continuous).mul continuous_const).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have h (y : M) : φ (frameKernel c ρ c' ψ' kk x y (s y)) =
      ∑ k, ∑ l, ∑ i, ∑ j, kk i j k l (x, y) *
        (trivializationAt V E (c i)).cutoffFrameCoeff (ρ i) (hρ i)
          ((Module.finBasis ℂ V).coord j).toContinuousLinearMap s y *
      ((ψ' k x : ℂ) * φ ((trivializationAt W F (c' k)).symmL ℂ x (Module.finBasis ℂ W l))) := by
    simp only [frameKernel_apply, map_sum, map_smul, smul_eq_mul, Complex.real_smul,
      Bundle.Trivialization.cutoffFrameCoeff_apply, LinearMap.coe_toContinuousLinearMap']
    refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦
      Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    push_cast
    ring
  simp only [h]
  rw [integral_finsetSum _ fun k _ ↦ integrable_finsetSum _ fun l _ ↦ integrable_finsetSum _
    fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j k l _]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [integral_finsetSum _ fun l _ ↦ integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _
    fun j _ ↦ hint i j k l _]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j k l _]
  exact Finset.sum_congr rfl fun i _ ↦ integral_finsetSum _ fun j _ ↦ hint i j k l _

end FrameKernel

/-- **Operators of order `-∞` between bundles on a compact manifold have smooth kernels.** Let `M`
be compact of positive dimension, let `E` and `F` have finite-dimensional fibres, and let `μ` be a
measure on `M` with a smooth nonvanishing density in every chart. Every operator `P : Γ(E) → Γ(F)`
of order `-∞` is the integral operator of a kernel `K(x, y) : E_y → F_x` which is smooth in
trivializations: `φ (P s x) = ∫ φ (K(x, y) (s y)) dμ(y)` for every smooth section `s` and every
continuous linear functional `φ` on `F_x`, and `(x, y) ↦ t'ₓ (K(x, y) (t_y⁻¹ v))` is smooth on the
product of the base sets of trivializations `t` of `E` and `t'` of `F` in their atlases. -/
theorem exists_forall_apply_eq_integral_of_mem_sectionSmoothingPseudodifferentialOperators
    [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] [CompactSpace M] [NeZero n] [OpensMeasurableSpace M]
    [IsFiniteMeasureOnCompacts μ] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (hμ : ∀ e : OpenPartialHomeomorph M (CoordinateSpace n),
      e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M →
        ∃ ρ : CoordinateSpace n → ℝ, ContDiffOn ℝ ∞ ρ e.target ∧ (∀ y ∈ e.target, ρ y ≠ 0) ∧
          ∀ f : M → ℂ, Continuous f → HasCompactSupport f → tsupport f ⊆ e.source →
            ∫ x, f x ∂μ = ∫ y in e.target, (ρ y : ℂ) * f (e.symm y))
    (hP : P ∈ sectionSmoothingPseudodifferentialOperators) :
    ∃ K : ∀ x y : M, E y →L[ℂ] F x,
      (∀ (t : Trivialization V (π V E)) [MemTrivializationAtlas t]
        (t' : Trivialization W (π W F)) [MemTrivializationAtlas t'] (v : V),
          ContMDiffOn (𝓘(ℝ, CoordinateSpace n).prod 𝓘(ℝ, CoordinateSpace n)) 𝓘(ℝ, W) ∞
            (fun p : M × M ↦ t'.continuousLinearMapAt ℂ p.1 (K p.1 p.2 (t.symmL ℂ p.2 v)))
            (t'.baseSet ×ˢ t.baseSet)) ∧
        ∀ s x (φ : F x →L[ℂ] ℂ), φ (P s x) = ∫ y, φ (K x y (s y)) ∂μ := by
  -- Finitely many cut-off frames expand the sections of `E` and of `F` on all of `M`.
  obtain ⟨ι, _, c, ρ, ψ, hρ, hψ, hE⟩ :=
    (isCompact_univ (X := M)).exists_sum_sum_cutoffFrameCoeff_smul_cutoffFrameSection_apply
      (I := 𝓘(ℝ, CoordinateSpace n)) (F := E) (Module.finBasis ℂ V)
  obtain ⟨κ, _, c', ρ', ψ', hρ', hψ', hF⟩ :=
    (isCompact_univ (X := M)).exists_sum_sum_cutoffFrameCoeff_smul_cutoffFrameSection_apply
      (I := 𝓘(ℝ, CoordinateSpace n)) (F := F) (Module.finBasis ℂ W)
  -- The entries of `P` in these frames have order `-∞`, so they have smooth kernels.
  have hQ := (mem_sectionSmoothingPseudodifferentialOperators_iff_sectionEntry.1 hP).2
  choose kk hkk hkkP using fun i j k l ↦
    exists_contMDiff_forall_apply_eq_integral_of_mem_smoothingPseudodifferentialOperators hμ
      (hQ (trivializationAt V E (c i)) (ψ i) (hψ i) (Module.finBasis ℂ V j)
        (trivializationAt W F (c' k)) (ρ' k) (hρ' k)
        ((Module.finBasis ℂ W).coord l).toContinuousLinearMap)
  refine ⟨frameKernel c ρ c' ψ' kk, contMDiffOn_frameKernel c ρ hρ c' ψ' hψ' kk hkk,
    fun s x φ ↦ ?_⟩
  rw [integral_frameKernel c ρ hρ c' ψ' kk hkk]
  -- Expand `P s` in the frames of `F`, and `s` in those of `E` inside its coefficients.
  have hs : s = ∑ i, ∑ j, (trivializationAt V E (c i)).cutoffFrameCoeff (ρ i) (hρ i)
      ((Module.finBasis ℂ V).coord j).toContinuousLinearMap s •
        (trivializationAt V E (c i)).cutoffFrameSection (ψ i) (hψ i) (Module.finBasis ℂ V j) := by
    ext y
    exact (hE s y (mem_univ y)).symm
  have hPs := hF (P s) x (mem_univ x)
  simp only [ContMDiffSection.coe_sum, Finset.sum_apply,
    ContMDiffSection.smul_apply_of_normedAlgebra] at hPs
  rw [← hPs, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [map_smul, smul_eq_mul, Bundle.Trivialization.apply_cutoffFrameSection, mul_comm]
  conv_lhs => rw [hs]
  simp only [map_sum, ContMDiffMap.coe_sum, Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← sectionEntry_apply_eq_cutoffFrameCoeff, hkkP, mul_comm, ← integral_mul_const]

/-- **On a compact manifold, the operators of order `-∞` between bundles are the integral operators
with smooth kernels.** Let `M` be compact of positive dimension, let `E` and `F` have
finite-dimensional fibres, and let `μ` be a measure on `M` with a smooth nonvanishing density in
every chart. An operator `P : Γ(E) → Γ(F)` has order `-∞` exactly when there is a kernel
`K(x, y) : E_y → F_x`, smooth in trivializations, with `φ (P s x) = ∫ φ (K(x, y) (s y)) dμ(y)` for
every smooth section `s` and every continuous linear functional `φ` on `F_x`. -/
theorem mem_sectionSmoothingPseudodifferentialOperators_iff_exists_forall_apply_eq_integral
    [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] [CompactSpace M] [NeZero n] [OpensMeasurableSpace M]
    [IsFiniteMeasureOnCompacts μ] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (hμ : ∀ e : OpenPartialHomeomorph M (CoordinateSpace n),
      e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M →
        ∃ ρ : CoordinateSpace n → ℝ, ContDiffOn ℝ ∞ ρ e.target ∧ (∀ y ∈ e.target, ρ y ≠ 0) ∧
          ∀ f : M → ℂ, Continuous f → HasCompactSupport f → tsupport f ⊆ e.source →
            ∫ x, f x ∂μ = ∫ y in e.target, (ρ y : ℂ) * f (e.symm y)) :
    P ∈ sectionSmoothingPseudodifferentialOperators ↔ ∃ K : ∀ x y : M, E y →L[ℂ] F x,
      (∀ (t : Trivialization V (π V E)) [MemTrivializationAtlas t]
        (t' : Trivialization W (π W F)) [MemTrivializationAtlas t'] (v : V),
          ContMDiffOn (𝓘(ℝ, CoordinateSpace n).prod 𝓘(ℝ, CoordinateSpace n)) 𝓘(ℝ, W) ∞
            (fun p : M × M ↦ t'.continuousLinearMapAt ℂ p.1 (K p.1 p.2 (t.symmL ℂ p.2 v)))
            (t'.baseSet ×ˢ t.baseSet)) ∧
        ∀ s x (φ : F x →L[ℂ] ℂ), φ (P s x) = ∫ y, φ (K x y (s y)) ∂μ :=
  ⟨exists_forall_apply_eq_integral_of_mem_sectionSmoothingPseudodifferentialOperators hμ,
    fun ⟨_, hK, hP⟩ ↦ mem_sectionSmoothingPseudodifferentialOperators_of_forall_apply_eq_integral
      (fun e he ↦ (hμ e he).imp fun _ h ↦ ⟨h.1, h.2.2⟩) hK
      ⟨univ, isCompact_univ, fun _ _ h ↦ (h (mem_univ _)).elim⟩ hP⟩

end Kernel

end TauCeti
