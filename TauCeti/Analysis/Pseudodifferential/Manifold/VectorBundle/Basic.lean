/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.CutoffFrame
public import TauCeti.Geometry.Manifold.VectorBundle.Section.TestFunction
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity

/-!
# Classical pseudodifferential operators between vector bundles

Let `M` be a manifold modelled on `ℝⁿ` and let `E`, `F` be smooth complex vector bundles over `M`
with model fibres `V` and `W`. This file defines the classical pseudodifferential operators of
order `m` from the smooth sections of `E` to those of `F`
(`TauCeti.sectionClassicalPseudodifferentialOperators`), following Hörmander (III, §18.1): an
operator between bundles is pseudodifferential when all its matrix entries in local frames are
scalar pseudodifferential operators.

The matrix entries are read with cut-off frames
(`TauCeti.Geometry.Manifold.VectorBundle.Section.CutoffFrame`). For a trivialization `t` of `E` in
its atlas, a real smooth function `ψ` supported in its base set and a vector `v ∈ V`, the
**cut-off frame section** `x ↦ ψ(x) t⁻¹ₓ v` is a smooth section of `E`
(`Bundle.Trivialization.cutoffFrameSection`). For a trivialization `t'` of `F`, a function `χ`
supported in its base set and a complex-linear functional `ℓ` on `W`, the **cut-off frame
coefficient** of a section `h` of `F` is the smooth function `x ↦ χ(x) ℓ(t'ₓ (h x))`
(`Bundle.Trivialization.cutoffFrameCoeff`). The corresponding **entry** of an operator
`P : Γ(E) → Γ(F)` is the scalar operator

`f ↦ χ · ℓ(t' (P (f · ψ t⁻¹ v)))`

on the complex-valued smooth functions on `M` (`TauCeti.sectionEntry`). Then `P` is a classical
pseudodifferential operator of order `m` when it is properly supported
(`TauCeti.IsSectionProperlySupported`) and all its entries are classical pseudodifferential
operators of order `m` on `M` (`TauCeti.classicalPseudodifferentialOperators`).

The supports of `ψ` and `χ` may lie in different, even disjoint, base sets. So the definition
controls `P` between distant points as well, through the scalar class, which itself sees the part
of an operator between distant points through charts of its maximal atlas whose domain has two
components. A definition testing `P` only in a single frame over each chart would leave this part
of `P` unconstrained.

In a chart `e` over whose source both bundles are trivialized, the entries assemble into the
matrix-valued chart compression of `P`: on Schwartz functions `u : ℝⁿ → V`, the operator

`u ↦ φ · t' (P (t⁻¹ ((ψ u) ∘ e))) ∘ e⁻¹`

is the quantization `Op(a)` of a classical symbol `a` of order `m` with values in `V →L[ℂ] W`
(`TauCeti.exists_quantizeSchwartzValue_eq_apply_chartCutoffSection`), where
`t⁻¹ ((ψ u) ∘ e)` is the chart cut-off section `Bundle.Trivialization.chartCutoffSection`. This
is the local description of a pseudodifferential operator between bundles in Taylor (Lecture I,
§8) and Melrose (§5.3).

## Main definitions

* `TauCeti.sectionEntry`: the matrix entry `f ↦ χ ℓ(t' (P (f ψ t⁻¹ v)))` of an operator.
* `TauCeti.IsSectionProperlySupported`: proper support of an operator between bundles.
* `TauCeti.sectionClassicalPseudodifferentialOperators m`: the classical pseudodifferential
  operators of order `m` from `Γ(E)` to `Γ(F)`, a complex submodule.

## Main results

* `TauCeti.sectionClassicalPseudodifferentialOperators_le`: an operator of order `m - k`, `k ∈ ℕ`,
  has order `m`.
* `TauCeti.mem_sectionClassicalPseudodifferentialOperators_zero_of_map_smul`: an operator which is
  linear over the complex-valued smooth functions, that is, a smooth bundle map, has order `0`; in
  particular the identity has order `0`.
* `TauCeti.smul_mem_sectionClassicalPseudodifferentialOperators` and
  `TauCeti.comp_smul_mem_sectionClassicalPseudodifferentialOperators`: multiplying an operator of
  order `m` by a smooth function on either side gives an operator of order `m`.
* `TauCeti.exists_quantizeSchwartzValue_eq_apply_chartCutoffSection`: in a chart over which both
  bundles are trivial, the compression of an operator of order `m` is the quantization of a
  classical symbol of order `m` with values in `V →L[ℂ] W`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1
  (pseudodifferential operators on manifolds and between sections of vector bundles).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8.
* R. Melrose, *Introduction to Microlocal Analysis*, §5.3.
-/

public section

noncomputable section

open Bundle Filter Set TauCeti
open scoped ContDiff Distributions Manifold SchwartzMap Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  {E : M → Type*} [TopologicalSpace (TotalSpace V E)] [∀ x, AddCommGroup (E x)]
  [∀ x, Module ℝ (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)] [FiberBundle V E]
  [VectorBundle ℝ V E] [VectorBundle ℂ V E]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {F : M → Type*} [TopologicalSpace (TotalSpace W F)] [∀ x, AddCommGroup (F x)]
  [∀ x, Module ℝ (F x)] [∀ x, Module ℂ (F x)] [∀ x, TopologicalSpace (F x)] [FiberBundle W F]
  [VectorBundle ℝ W F] [VectorBundle ℂ W F]

namespace TauCeti

/-! ### Properly supported operators between bundles -/

section ProperSupport

/-- An operator `P` from the smooth sections of `E` to those of `F` is **properly supported** when
for every compact set `K` there is a compact set `K'` such that `P s` is supported in `K'` whenever
`s` is supported in `K`, and `P s` vanishes on `K` whenever `s` vanishes on a neighbourhood of
`K'`. This is `TauCeti.IsProperlySupported` for operators between bundles. -/
def IsSectionProperlySupported
    (P : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯) :
    Prop :=
  ∀ K : Set M, IsCompact K → ∃ K' : Set M, IsCompact K' ∧
    (∀ s : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯, s.tsupport ⊆ K → (P s).tsupport ⊆ K') ∧
      ∀ s : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯, (∀ᶠ y in 𝓝ˢ K', s y = 0) → ∀ x ∈ K, P s x = 0

variable {P Q : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯}

theorem isSectionProperlySupported_iff :
    IsSectionProperlySupported P ↔ ∀ K : Set M, IsCompact K → ∃ K' : Set M, IsCompact K' ∧
      (∀ s : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯, s.tsupport ⊆ K → (P s).tsupport ⊆ K') ∧
        ∀ s : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯,
          (∀ᶠ y in 𝓝ˢ K', s y = 0) → ∀ x ∈ K, P s x = 0 :=
  Iff.rfl

theorem isSectionProperlySupported_zero :
    IsSectionProperlySupported (0 : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ]
      Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯) :=
  fun K hK ↦ ⟨K, hK, fun _ _ ↦ by simp [ContMDiffSection.tsupport_zero], fun _ _ _ _ ↦ by simp⟩

theorem isSectionProperlySupported_id :
    IsSectionProperlySupported (LinearMap.id : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ]
      Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) :=
  fun K hK ↦ ⟨K, hK, fun _ hs ↦ hs, fun _ hs x hx ↦ hs.self_of_nhdsSet x hx⟩

theorem IsSectionProperlySupported.add (hP : IsSectionProperlySupported P)
    (hQ : IsSectionProperlySupported Q) : IsSectionProperlySupported (P + Q) := by
  intro K hK
  obtain ⟨K₁, hK₁, hP₁, hP₂⟩ := hP K hK
  obtain ⟨K₂, hK₂, hQ₁, hQ₂⟩ := hQ K hK
  refine ⟨K₁ ∪ K₂, hK₁.union hK₂, fun s hs ↦ ?_, fun s hs x hx ↦ ?_⟩
  · rw [LinearMap.add_apply]
    exact (ContMDiffSection.tsupport_add_subset _ _).trans
      (union_subset_union (hP₁ s hs) (hQ₁ s hs))
  · rw [LinearMap.add_apply, ContMDiffSection.coe_add, Pi.add_apply,
      hP₂ s (hs.filter_mono (nhdsSet_mono subset_union_left)) x hx,
      hQ₂ s (hs.filter_mono (nhdsSet_mono subset_union_right)) x hx, add_zero]

/-- Multiplying a properly supported operator between bundles on the left by a complex-valued
smooth function `g` gives a properly supported operator. -/
theorem IsSectionProperlySupported.smul_left (hP : IsSectionProperlySupported P)
    (g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) : IsSectionProperlySupported (g • P) := by
  intro K hK
  obtain ⟨K', hK', hP₁, hP₂⟩ := hP K hK
  refine ⟨K', hK', fun s hs ↦ ?_, fun s hs x hx ↦ ?_⟩
  · rw [LinearMap.smul_apply]
    exact (ContMDiffSection.tsupport_smul_function_subset_of_normedAlgebra g (P s)).trans
      (inter_subset_right.trans (hP₁ s hs))
  · simp [hP₂ s hs x hx]

theorem IsSectionProperlySupported.smul (hP : IsSectionProperlySupported P) (c : ℂ) :
    IsSectionProperlySupported (c • P) := by
  have hc : c • P = (ContMDiffMap.const c : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) • P :=
    LinearMap.ext fun s ↦ (ContMDiffSection.const_smul_of_normedAlgebra c (P s)).symm
  rw [hc]
  exact hP.smul_left _

/-- **Composition.** The composition of two properly supported operators between bundles is
properly supported. -/
theorem IsSectionProperlySupported.comp {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U]
    {G : M → Type*} [TopologicalSpace (TotalSpace U G)] [∀ x, AddCommGroup (G x)]
    [∀ x, Module ℝ (G x)] [∀ x, Module ℂ (G x)] [∀ x, TopologicalSpace (G x)] [FiberBundle U G]
    [VectorBundle ℝ U G] [VectorBundle ℂ U G]
    {R : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); U, G⟯}
    (hR : IsSectionProperlySupported R) (hP : IsSectionProperlySupported P) :
    IsSectionProperlySupported (R ∘ₗ P) := by
  have := ChartedSpace.locallyCompactSpace (CoordinateSpace n) M
  intro K hK
  obtain ⟨K₁, hK₁, hP₁, -⟩ := hP K hK
  obtain ⟨K₂, hK₂, hR₁, -⟩ := hR K₁ hK₁
  obtain ⟨K₃, hK₃, -, hR₂⟩ := hR K hK
  obtain ⟨L, hL, hK₃L⟩ := exists_compact_superset hK₃
  obtain ⟨K₄, hK₄, -, hP₂⟩ := hP L hL
  refine ⟨K₂ ∪ K₄, hK₂.union hK₄, fun s hs ↦ (hR₁ _ (hP₁ s hs)).trans subset_union_left,
    fun s hs ↦ hR₂ (P s) ?_⟩
  have hPs := hP₂ s (hs.filter_mono (nhdsSet_mono subset_union_right))
  exact Filter.mem_of_superset (isOpen_interior.mem_nhdsSet.2 hK₃L) fun y hy ↦
    hPs y (interior_subset hy)

/-- A **local** operator between bundles, one such that `P s` vanishes at every point near which
`s` vanishes, is properly supported, with `K' = K`. -/
theorem IsSectionProperlySupported.of_local [T2Space M]
    (hP : ∀ s x, (∀ᶠ y in 𝓝 x, s y = 0) → P s x = 0) : IsSectionProperlySupported P := by
  refine fun K hK ↦ ⟨K, hK, fun s hs ↦ ?_,
    fun s hs x hx ↦ hP s x (hs.filter_mono (nhds_le_nhdsSet hx))⟩
  refine (ContMDiffSection.tsupport_subset_iff hK.isClosed).2 fun x hxK ↦ hP s x ?_
  filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hxK] with y hy
  exact s.eq_zero_of_notMem_tsupport fun h ↦ hy (hs h)

/-- An operator between bundles which is linear over the complex-valued smooth functions, that is,
a smooth bundle map, is properly supported. -/
theorem IsSectionProperlySupported.of_map_smul [T2Space M]
    [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]
    (hP : ∀ (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) s, P (f • s) = f • P s) :
    IsSectionProperlySupported P :=
  of_local fun _ _ hs ↦ apply_eq_zero_of_map_smul hP hs

end ProperSupport

/-! ### Matrix entries -/

section Entry

variable [ContMDiffVectorBundle ∞ V E 𝓘(ℝ, CoordinateSpace n)]
  [ContMDiffVectorBundle ∞ W F 𝓘(ℝ, CoordinateSpace n)]
  (t : Trivialization V (π V E)) [MemTrivializationAtlas t]
  (ψ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hψ : tsupport ψ ⊆ t.baseSet) (v : V)
  (t' : Trivialization W (π W F)) [MemTrivializationAtlas t']
  (χ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hχ : tsupport χ ⊆ t'.baseSet) (ℓ : W →L[ℂ] ℂ)

/-- The **matrix entry** `f ↦ χ · ℓ(t' (P (f · ψ t⁻¹ v)))` of an operator `P : Γ(E) → Γ(F)`, for
cut-off frames of `E` and of `F` (`Bundle.Trivialization.cutoffFrameSection` and
`Bundle.Trivialization.cutoffFrameCoeff`): a complex-linear operator on the complex-valued smooth
functions on `M`, linear in `P`. -/
def sectionEntry :
    (Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯) →ₗ[ℂ]
      C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
        C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ where
  toFun P := t'.cutoffFrameCoeff χ hχ ℓ ∘ₗ P ∘ₗ
    (LinearMap.toSpanSingleton _ _ (t.cutoffFrameSection ψ hψ v)).restrictScalars ℂ
  map_add' P Q := by rw [LinearMap.add_comp, LinearMap.comp_add]
  map_smul' c P := by rw [LinearMap.smul_comp, LinearMap.comp_smul, RingHom.id_apply]

@[simp]
theorem sectionEntry_apply
    (P : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯)
    (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M) :
    sectionEntry t ψ hψ v t' χ hχ ℓ P f x =
      χ x • ℓ (t'.continuousLinearMapAt ℂ x (P (f • t.cutoffFrameSection ψ hψ v) x)) :=
  by simp [sectionEntry]

/-- The entries of a properly supported operator are properly supported. -/
theorem IsSectionProperlySupported.sectionEntry
    {P : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯}
    (hP : IsSectionProperlySupported P) :
    IsProperlySupported (TauCeti.sectionEntry t ψ hψ v t' χ hχ ℓ P) := by
  refine isProperlySupported_iff.2 fun K hK ↦ ?_
  obtain ⟨K', hK', hP₁, hP₂⟩ := hP K hK
  refine ⟨K', hK', fun f hf ↦ ?_, fun f hf x hx ↦ ?_⟩
  · have h₂ := hP₁ _ ((ContMDiffSection.tsupport_smul_function_subset_of_normedAlgebra f
      (t.cutoffFrameSection ψ hψ v)).trans (inter_subset_left.trans hf))
    rw [ContMDiffSection.tsupport_def] at h₂
    refine (closure_mono fun y hy ↦ ?_).trans h₂
    simp only [Function.mem_support, sectionEntry_apply] at hy
    exact fun h ↦ hy (by rw [h, map_zero, map_zero, smul_zero])
  · rw [sectionEntry_apply, hP₂ _ (hf.mono fun y hy ↦ by simp [hy]) x hx]
    simp

end Entry

/-! ### Classical pseudodifferential operators between bundles -/

section Class

variable [T2Space M] [ContMDiffVectorBundle ∞ V E 𝓘(ℝ, CoordinateSpace n)]
  [ContMDiffVectorBundle ∞ W F 𝓘(ℝ, CoordinateSpace n)]

/-- The **classical pseudodifferential operators of order `m`** from the smooth sections of `E` to
those of `F`: the complex-linear operators `P` such that

* `P` is properly supported (`TauCeti.IsSectionProperlySupported`);
* for all trivializations `t` of `E` and `t'` of `F` in their atlases, real smooth functions `ψ`
  and `χ` supported in their base sets, vectors `v` of the model fibre of `E` and complex-linear
  functionals `ℓ` on the model fibre of `F`, the matrix entry
  `f ↦ χ · ℓ(t' (P (f · ψ t⁻¹ v)))` of `P` (`TauCeti.sectionEntry`) is a classical
  pseudodifferential operator of order `m` on `M` (`TauCeti.classicalPseudodifferentialOperators`).
-/
def sectionClassicalPseudodifferentialOperators (m : ℝ) :
    Submodule ℂ
      (Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯) where
  carrier := {P | IsSectionProperlySupported P ∧
    ∀ (t : Trivialization V (π V E)) [MemTrivializationAtlas t]
      (ψ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hψ : tsupport ψ ⊆ t.baseSet) (v : V)
      (t' : Trivialization W (π W F)) [MemTrivializationAtlas t']
      (χ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hχ : tsupport χ ⊆ t'.baseSet) (ℓ : W →L[ℂ] ℂ),
      sectionEntry t ψ hψ v t' χ hχ ℓ P ∈ classicalPseudodifferentialOperators m}
  zero_mem' := ⟨isSectionProperlySupported_zero, fun t _ ψ hψ v t' _ χ hχ ℓ ↦ by
    rw [map_zero]
    exact zero_mem _⟩
  add_mem' {P Q} hP hQ := ⟨hP.1.add hQ.1, fun t _ ψ hψ v t' _ χ hχ ℓ ↦ by
    rw [map_add]
    exact add_mem (hP.2 t ψ hψ v t' χ hχ ℓ) (hQ.2 t ψ hψ v t' χ hχ ℓ)⟩
  smul_mem' c P hP := ⟨hP.1.smul c, fun t _ ψ hψ v t' _ χ hχ ℓ ↦ by
    rw [map_smul]
    exact Submodule.smul_mem _ c (hP.2 t ψ hψ v t' χ hχ ℓ)⟩

variable {m : ℝ}
  {P : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯}

theorem mem_sectionClassicalPseudodifferentialOperators_iff :
    P ∈ sectionClassicalPseudodifferentialOperators m ↔ IsSectionProperlySupported P ∧
      ∀ (t : Trivialization V (π V E)) [MemTrivializationAtlas t]
        (ψ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hψ : tsupport ψ ⊆ t.baseSet) (v : V)
        (t' : Trivialization W (π W F)) [MemTrivializationAtlas t']
        (χ : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; ℝ⟯) (hχ : tsupport χ ⊆ t'.baseSet) (ℓ : W →L[ℂ] ℂ),
        sectionEntry t ψ hψ v t' χ hχ ℓ P ∈ classicalPseudodifferentialOperators m :=
  Iff.rfl

/-- **Inclusion of orders.** A classical pseudodifferential operator between bundles of order
`m' = m - k`, `k ∈ ℕ`, has order `m`. -/
theorem sectionClassicalPseudodifferentialOperators_le {m' : ℝ} (k : ℕ) (hk : m' = m - k) :
    sectionClassicalPseudodifferentialOperators (n := n) (M := M) (V := V) (E := E) (W := W)
      (F := F) m' ≤
      sectionClassicalPseudodifferentialOperators m :=
  fun _ hP ↦ ⟨hP.1, fun t _ ψ hψ v t' _ χ hχ ℓ ↦
    classicalPseudodifferentialOperators_le k hk (hP.2 t ψ hψ v t' χ hχ ℓ)⟩

/-- **Operators linear over smooth functions have order `0`.** An operator `P : Γ(E) → Γ(F)` with
`P (f s) = f P s` for all complex-valued smooth functions `f`, that is, a smooth bundle map from
`E` to `F`, is a classical pseudodifferential operator of order `0`. Each of its entries is the
multiplication by the smooth function `χ ℓ(t' (P (ψ t⁻¹ v)))`. -/
theorem mem_sectionClassicalPseudodifferentialOperators_zero_of_map_smul
    [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]
    (hP : ∀ (f : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) s, P (f • s) = f • P s) :
    P ∈ sectionClassicalPseudodifferentialOperators 0 := by
  refine ⟨.of_map_smul hP, fun t _ ψ hψ v t' _ χ hχ ℓ ↦ ?_⟩
  have hentry : sectionEntry t ψ hψ v t' χ hχ ℓ P =
      LinearMap.mulLeft ℂ (sectionEntry t ψ hψ v t' χ hχ ℓ P 1) := by
    ext f x
    simp [hP, mul_comm, mul_left_comm]
  rw [hentry]
  exact mulLeft_mem_classicalPseudodifferentialOperators _

/-- **The identity has order `0`.** -/
theorem id_mem_sectionClassicalPseudodifferentialOperators
    [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] :
    (LinearMap.id : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ]
      Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯) ∈ sectionClassicalPseudodifferentialOperators 0 :=
  mem_sectionClassicalPseudodifferentialOperators_zero_of_map_smul fun _ _ ↦ rfl

/-- **Multiplication on the left.** If `P` is a classical pseudodifferential operator of order `m`
between bundles, then so is `s ↦ g P s` for every complex-valued smooth function `g`: its entries
are the entries of `P` multiplied by `g`. -/
theorem smul_mem_sectionClassicalPseudodifferentialOperators
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    g • P ∈ sectionClassicalPseudodifferentialOperators m := by
  refine ⟨hP.1.smul_left g, fun t _ ψ hψ v t' _ χ hχ ℓ ↦ ?_⟩
  have hentry : sectionEntry t ψ hψ v t' χ hχ ℓ (g • P) =
      LinearMap.mulLeft ℂ g ∘ₗ sectionEntry t ψ hψ v t' χ hχ ℓ P := by
    ext f x
    simp [mul_left_comm]
  rw [hentry]
  exact mulLeft_comp_mem_classicalPseudodifferentialOperators (hP.2 t ψ hψ v t' χ hχ ℓ) g

/-- **Multiplication on the right.** If `P` is a classical pseudodifferential operator of order `m`
between bundles, then so is `s ↦ P (g s)` for every complex-valued smooth function `g`: its entries
are the entries of `P` composed with the multiplication by `g`. -/
theorem comp_smul_mem_sectionClassicalPseudodifferentialOperators
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (g : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) :
    P ∘ₗ (g • LinearMap.id) ∈ sectionClassicalPseudodifferentialOperators m := by
  refine ⟨hP.1.comp (isSectionProperlySupported_id.smul_left g), fun t _ ψ hψ v t' _ χ hχ ℓ ↦ ?_⟩
  have hentry : sectionEntry t ψ hψ v t' χ hχ ℓ (P ∘ₗ (g • LinearMap.id)) =
      sectionEntry t ψ hψ v t' χ hχ ℓ P ∘ₗ LinearMap.mulLeft ℂ g := by
    ext f x
    simp [mul_smul]
  rw [hentry]
  exact comp_mulLeft_mem_classicalPseudodifferentialOperators (hP.2 t ψ hψ v t' χ hχ ℓ) g

end Class

/-! ### Chart compressions -/

section Chart

variable [T2Space M] [ContMDiffVectorBundle ∞ V E 𝓘(ℝ, CoordinateSpace n)]
  [ContMDiffVectorBundle ∞ W F 𝓘(ℝ, CoordinateSpace n)]
  {e : OpenPartialHomeomorph M (CoordinateSpace n)}
  (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
  (t : Trivialization V (π V E)) [MemTrivializationAtlas t] (hE : e.source ⊆ t.baseSet)

/-- **Chart compressions of pseudodifferential operators between bundles.** Let `P` be a classical
pseudodifferential operator of order `m` from `E` to `F`, `e` a chart of the maximal atlas whose
source lies in the base sets of trivializations `t` of `E` and `t'` of `F`, and `φ`, `ψ` cutoffs
with compact supports in the chart target. Then the compression

`u ↦ φ · t' (P (t⁻¹ ((ψ u) ∘ e))) ∘ e⁻¹`

of `P` agrees on Schwartz functions `u : ℝⁿ → V` with the quantization `Op(a)` of a classical
symbol `a` of order `m` with values in `V →L[ℂ] W`. -/
theorem exists_quantizeSchwartzValue_eq_apply_chartCutoffSection [FiniteDimensional ℂ V]
    [FiniteDimensional ℂ W] {m : ℝ}
    {P : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯}
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (t' : Trivialization W (π W F)) [MemTrivializationAtlas t'] (hF : e.source ⊆ t'.baseSet)
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) :
    ∃ a : ClassicalSymbol n V W m, ∀ (u : 𝓢(CoordinateSpace n, V)) (y : CoordinateSpace n),
      quantizeSchwartzValue a.toSymbol.coefficient u y =
        φ y • t'.continuousLinearMapAt ℂ (e.symm y)
          (P (t.chartCutoffSection he hE ψ u) (e.symm y)) := by
  -- A cutoff `ρ` on `M`, supported in the chart source and equal to `1` over the supports of `φ`
  -- and `ψ`, gives cut-off frames which are frames there.
  obtain ⟨χ, hχ⟩ := TestFunction.exists_eventually_eq_one_nhdsSet_tsupport_union φ ψ
  set ρ := e.cutoffPullback he χ 1
  have hρs : tsupport ρ ⊆ e.source := (e.tsupport_cutoffPullback_subset he χ 1).trans <| by
    rintro _ ⟨y, hy, rfl⟩
    exact e.map_target (χ.tsupport_subset hy)
  have hρ (y : CoordinateSpace n) (hy : y ∈ tsupport φ ∪ tsupport ψ) : ρ (e.symm y) = 1 := by
    have hyt : y ∈ e.target := (union_subset φ.tsupport_subset ψ.tsupport_subset) hy
    rw [e.cutoffPullback_one_apply_of_mem he _ (e.map_target hyt), e.right_inv hyt]
    exact hχ.self_of_nhdsSet y hy
  set bV := Module.finBasis ℂ V
  set bW := Module.finBasis ℂ W
  -- The entries of `P` in these frames have symbols `a i j` in the chart.
  choose a ha using fun i j ↦ (mem_classicalPseudodifferentialOperators_iff.1
    (hP.2 t ρ (hρs.trans hE) (bV i) t' ρ (hρs.trans hF) (bW.coord j).toContinuousLinearMap)).2
      e he φ ψ
  refine ⟨∑ i, ∑ j,
    (a i j).map (Symbol.singleEntryMap (bV.coord i).toContinuousLinearMap (bW j)), fun u y ↦ ?_⟩
  simp only [ClassicalSymbol.toSymbol_sum, Symbol.quantizeSchwartzValue_sum_left,
    ClassicalSymbol.toSymbol_map, Symbol.quantizeSchwartzValue_map_singleEntryMap, ha,
    OpenPartialHomeomorph.complexChartCompression_apply, sectionEntry_apply]
  by_cases hφ : φ y = 0
  · simp [hφ]
  have hρy : ρ (e.symm y) = 1 := hρ y (Or.inl (subset_tsupport _ hφ))
  rw [t.chartCutoffSection_eq_sum he hE ψ u ρ (hρs.trans hE)
    (fun y hy ↦ hρ y (Or.inr hy)) bV, map_sum, ContMDiffSection.coe_sum, Finset.sum_apply,
    map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  conv_rhs => rw [← bW.sum_repr (t'.continuousLinearMapAt ℂ (e.symm y) _), Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp [hρy, ← smul_assoc, Complex.real_smul]

end Chart

end TauCeti
