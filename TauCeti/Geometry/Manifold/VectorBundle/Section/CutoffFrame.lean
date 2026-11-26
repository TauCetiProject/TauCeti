/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.Schwartz
public import TauCeti.Geometry.Manifold.ContMDiffMap.Basic
public import TauCeti.Geometry.Manifold.DifferentialOperator.ChartCompression.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.ComplexModule
public import TauCeti.Geometry.Manifold.VectorBundle.Section.TestFunction
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension

/-!
# Cut-off frames of a vector bundle

A trivialization `t` of a smooth vector bundle `V → M` gives a frame of `V` only over its base set.
Multiplying by a smooth function `ψ` supported in the base set turns it into global data:

* the **cut-off frame section** `x ↦ ψ(x) t⁻¹ₓ v` of `V`, for a vector `v` of the model fibre
  (`Bundle.Trivialization.cutoffFrameSection`), is a smooth section of `V` on all of `M`;
* for a complex bundle over a real manifold, the **cut-off frame coefficient**
  `x ↦ χ(x) ℓ(tₓ (h x))` of a smooth section `h`, for a complex-linear functional `ℓ` on the model
  fibre (`Bundle.Trivialization.cutoffFrameCoeff`), is a smooth complex-valued function on `M`,
  complex-linear in `h`.

These read operators between sections of bundles as matrices of operators on functions, without
restricting to the base set of a trivialization: the entries of an operator `P` are the operators
`f ↦ χ ℓ(t' (P (f ψ t⁻¹ v)))` on functions on `M`.

In a chart `e` whose source lies in the base set of `t`, a Schwartz function `u` on the model space
and a cutoff `ψ` with compact support in the chart target give the **chart cut-off section**
`x ↦ t⁻¹ₓ (ψ(e x) u(e x))` (`Bundle.Trivialization.chartCutoffSection`), on which chart
compressions of operators between bundles are evaluated. In terms of cut-off frames, it is the sum
of the cut-off frame sections `ρ t⁻¹ bᵢ` with the pulled back coefficients `(ψ bᵢ*(u)) ∘ e`
(`Bundle.Trivialization.chartCutoffSection_eq_sum`).
-/

public section

noncomputable section

open Bundle Set
open scoped ContDiff Distributions Manifold SchwartzMap

namespace Bundle.Trivialization

section Section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {EM : Type*} [NormedAddCommGroup EM]
  [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM] {I : ModelWithCorners 𝕜 EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] {n : ℕ∞ω}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [ContMDiffVectorBundle n F V I]
  (t : Trivialization F (π F V)) [MemTrivializationAtlas t]

/-- The **cut-off frame section** `x ↦ ψ(x) t⁻¹ₓ v` of `V`, for a trivialization `t` of `V` in its
atlas, a `C^n` function `ψ` whose support lies in the base set of `t` and a vector `v` of the model
fibre. It is a `C^n` section of `V` on all of `M`, vanishing outside the support of `ψ`. -/
def cutoffFrameSection (ψ : C^n⟮I, M; 𝕜⟯) (hψ : tsupport ψ ⊆ t.baseSet) (v : F) :
    Cₛ^n⟮I; F, V⟯ where
  toFun x := ψ x • t.symm x v
  contMDiff_toFun := by
    refine ContMDiffOn.smul_section_of_tsupport ψ.contMDiff.contMDiffOn t.open_baseSet hψ ?_
    refine (contMDiffOn_section_iff t t.open_baseSet subset_rfl).2 ?_
    exact contMDiffOn_const.congr fun x hx ↦ by rw [t.apply_mk_symm hx]

@[simp]
theorem cutoffFrameSection_apply (ψ : C^n⟮I, M; 𝕜⟯) (hψ : tsupport ψ ⊆ t.baseSet) (v : F)
    (x : M) : t.cutoffFrameSection ψ hψ v x = ψ x • t.symm x v :=
  (rfl)

end Section

section Coeff

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {HM : Type*} [TopologicalSpace HM]
  {I : ModelWithCorners ℝ EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] {n : ℕ∞ω}
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {F : M → Type*} [TopologicalSpace (TotalSpace W F)] [∀ x, AddCommGroup (F x)]
  [∀ x, Module ℝ (F x)] [∀ x, Module ℂ (F x)] [∀ x, TopologicalSpace (F x)] [FiberBundle W F]
  [VectorBundle ℝ W F] [VectorBundle ℂ W F] [ContMDiffVectorBundle n W F I]
  (t : Trivialization W (π W F)) [MemTrivializationAtlas t]

/-- The cut-off frame coefficients `χ(x) ℓ(tₓ (h x))` of a `C^n` section `h` are `C^n`. -/
private theorem contMDiff_cutoffFrameCoeffFun (χ : C^n⟮I, M; ℝ⟯) (hχ : tsupport χ ⊆ t.baseSet)
    (ℓ : W →L[ℂ] ℂ) (h : Cₛ^n⟮I; W, F⟯) :
    ContMDiff I 𝓘(ℝ, ℂ) n fun x ↦ χ x • ℓ (t.continuousLinearMapAt ℂ x (h x)) := by
  refine ContMDiffOn.contMDiff_smul_of_tsupport_subset ?_ t.open_baseSet
    χ.contMDiff.contMDiffOn hχ
  have hs := (contMDiffOn_section_iff t t.open_baseSet subset_rfl).1 h.contMDiff.contMDiffOn
  refine ((ℓ.restrictScalars ℝ).contMDiff.comp_contMDiffOn hs).congr fun x hx ↦ ?_
  simp [continuousLinearMapAt_apply_of_mem ℂ t hx]

/-- The cut-off frame coefficients `χ(x) ℓ(tₓ (h x))` of a `C^n` section `h`, as a `C^n`
function. -/
private def cutoffFrameCoeffFun (χ : C^n⟮I, M; ℝ⟯) (hχ : tsupport χ ⊆ t.baseSet) (ℓ : W →L[ℂ] ℂ)
    (h : Cₛ^n⟮I; W, F⟯) : C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ :=
  ⟨_, contMDiff_cutoffFrameCoeffFun t χ hχ ℓ h⟩

private theorem cutoffFrameCoeffFun_apply (χ : C^n⟮I, M; ℝ⟯) (hχ : tsupport χ ⊆ t.baseSet)
    (ℓ : W →L[ℂ] ℂ) (h : Cₛ^n⟮I; W, F⟯) (x : M) :
    cutoffFrameCoeffFun t χ hχ ℓ h x = χ x • ℓ (t.continuousLinearMapAt ℂ x (h x)) :=
  (rfl)

/-- The **cut-off frame coefficient** `x ↦ χ(x) ℓ(tₓ (h x))` of a section `h` of a complex vector
bundle `F` over a real manifold, for a trivialization `t` of `F` in its atlas, a real `C^n`
function `χ` whose support lies in the base set of `t` and a complex-linear functional `ℓ` on the
model fibre, as a complex-linear map from the `C^n` sections of `F` to the complex-valued `C^n`
functions. -/
def cutoffFrameCoeff (χ : C^n⟮I, M; ℝ⟯) (hχ : tsupport χ ⊆ t.baseSet) (ℓ : W →L[ℂ] ℂ) :
    Cₛ^n⟮I; W, F⟯ →ₗ[ℂ] C^n⟮I, M; 𝓘(ℝ, ℂ), ℂ⟯ where
  toFun := cutoffFrameCoeffFun t χ hχ ℓ
  map_add' g h := by
    ext x
    simp [cutoffFrameCoeffFun_apply, smul_add]
  map_smul' c h := by
    ext x
    simp only [cutoffFrameCoeffFun_apply, ContMDiffMap.complex_smul_apply,
      ContMDiffSection.coe_smul_of_normedAlgebra, Pi.smul_apply, map_smul, Complex.real_smul,
      smul_eq_mul, RingHom.id_apply]
    ring

@[simp]
theorem cutoffFrameCoeff_apply (χ : C^n⟮I, M; ℝ⟯) (hχ : tsupport χ ⊆ t.baseSet) (ℓ : W →L[ℂ] ℂ)
    (h : Cₛ^n⟮I; W, F⟯) (x : M) :
    t.cutoffFrameCoeff χ hχ ℓ h x = χ x • ℓ (t.continuousLinearMapAt ℂ x (h x)) :=
  (rfl)

end Coeff

section ChartCutoff

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM] {M : Type*} [TopologicalSpace M]
  [ChartedSpace EM M] [T2Space M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, Module ℂ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  [VectorBundle ℝ F V] [VectorBundle ℂ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, EM)]
  (t : Trivialization F (π F V)) [MemTrivializationAtlas t] {e : OpenPartialHomeomorph M EM}
  (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, EM) ∞ M) (hE : e.source ⊆ t.baseSet)

/-- The **chart cut-off section** of a Schwartz function `u : EM → F`: for a chart `e` whose
source lies in the base set of the trivialization `t` and a cutoff `ψ` with compact support in the
chart target, the smooth section `x ↦ t⁻¹ₓ (ψ(e x) u(e x))` of `V` on the chart source, extended
by zero. Its frame coefficients in `t`, read in the chart, are `ψ u`. -/
def chartCutoffSection (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (u : 𝓢(EM, F)) :
    Cₛ^∞⟮𝓘(ℝ, EM); F, V⟯ :=
  (t.chartTestSection (n := ⊤) e (contMDiffOn_of_mem_maximalAtlas he) hE
    (ψ.smulSchwartzMap u)).val

omit [∀ x, Module ℂ (V x)] [VectorBundle ℂ F V] in
theorem chartCutoffSection_apply_of_mem (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (u : 𝓢(EM, F))
    {x : M} (hx : x ∈ e.source) :
    t.chartCutoffSection he hE ψ u x = t.symm x (ψ (e x) • u (e x)) := by
  rw [chartCutoffSection, t.chartTestSection_apply_of_mem (n := ⊤) e _ hE _ hx,
    t.symmL_apply (hE hx), TestFunction.smulSchwartzMap_apply]

omit [∀ x, Module ℂ (V x)] [VectorBundle ℂ F V] in
theorem chartCutoffSection_apply_of_notMem (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (u : 𝓢(EM, F)) {x : M} (hx : x ∉ e.source) :
    t.chartCutoffSection he hE ψ u x = 0 :=
  t.chartTestSection_apply_of_notMem (n := ⊤) e _ hE _ hx

/-- **A chart cut-off section in a frame.** Let `ρ` be a real smooth function on `M`, supported in
the base set of `t`, which equals `1` on `e⁻¹(supp ψ)`, and `(bᵢ)` a basis of the model fibre `F`
with coordinate functionals `bᵢ*`. Then the chart cut-off section of `u` is the sum over `i` of the
cut-off frame sections `ρ t⁻¹ bᵢ` multiplied by the complex pullbacks `(ψ bᵢ*(u)) ∘ e`. -/
theorem chartCutoffSection_eq_sum [FiniteDimensional ℂ F]
    (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (u : 𝓢(EM, F))
    (ρ : C^∞⟮𝓘(ℝ, EM), M; ℝ⟯) (hρ : tsupport ρ ⊆ t.baseSet)
    (hρψ : ∀ y ∈ tsupport ψ, ρ (e.symm y) = 1) {ι : Type*} [Fintype ι] (b : Module.Basis ι ℂ F) :
    t.chartCutoffSection he hE ψ u = ∑ i, e.complexCutoffPullback he ψ
      (ContMDiffMap.ofContDiff (u.postcompCLM (b.coord i).toContinuousLinearMap)
        ((u.postcompCLM (b.coord i).toContinuousLinearMap).smooth ⊤)) •
          t.cutoffFrameSection ρ hρ (b i) := by
  ext x
  rw [ContMDiffSection.coe_sum, Finset.sum_apply]
  by_cases hx : x ∈ e.source
  · simp only [t.chartCutoffSection_apply_of_mem he hE _ _ hx,
      ContMDiffSection.smul_apply_of_normedAlgebra,
      e.complexCutoffPullback_apply_of_mem he _ _ hx, t.cutoffFrameSection_apply,
      ContMDiffMap.coe_ofContDiff, SchwartzMap.postcompCLM_apply]
    by_cases hψx : ψ (e x) = 0
    · simp [hψx, ← t.symmL_apply (R := ℂ) (hE hx)]
    have hρx : ρ x = 1 := by
      simpa [e.left_inv hx] using hρψ (e x) (subset_tsupport _ hψx)
    simp only [hρx, one_smul, ← t.symmL_apply (R := ℂ) (hE hx), ← map_smul, ← map_sum]
    congr 1
    conv_lhs => rw [← b.sum_repr (u (e x)), Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [← smul_assoc, Complex.real_smul]
  · simp [t.chartCutoffSection_apply_of_notMem he hE _ _ hx,
      e.complexCutoffPullback_apply_of_notMem he _ _ hx]

end ChartCutoff

end Bundle.Trivialization
