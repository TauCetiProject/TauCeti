/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.ChartCompression.Basic
public import TauCeti.Geometry.Manifold.DifferentialOperator.PrincipalSymbol.Section
public import TauCeti.Geometry.Manifold.VectorBundle.Section.TestFunction
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Geometry.Manifold.ContMDiffMap.Extension
import TauCeti.Geometry.Manifold.MFDeriv.Localized

/-!
# Differential operators between vector bundles, compressed to a chart

Let `M` be a manifold modelled on a real normed space `E`, let `e` be a chart of its maximal smooth
atlas, and let `V` and `W` be smooth vector bundles over `M` with model fibres `F` and `F'`, with
frames (trivializations) `tV` and `tW` over the chart source. An operator `P : Γ(V) → Γ(W)` on the
smooth sections is read in the chart and the frames as a matrix of operators on the smooth real
functions on `E`: for a vector `v ∈ F` and a functional `ℓ` on `F'`, its **entry** is

`f ↦ φ · ℓ (tW (P (tV⁻¹ ((ψ f) • v) ∘ e)) ∘ e⁻¹)`

(`OpenPartialHomeomorph.sectionChartCompression`), where `φ` and `ψ` are cutoffs with compact
supports in the chart target. Here `tV⁻¹ ((ψ f) • v) ∘ e` is the section of `V` whose frame
coefficients are `(ψ f) • v` in the chart, extended by zero outside the chart source
(`OpenPartialHomeomorph.sectionCutoffPullback`), and `φ · ℓ (tW h ∘ e⁻¹)` reads a section `h` of
`W` in the frame `tW`, cut off by `φ` (`OpenPartialHomeomorph.sectionCutoffPushforward`). With
`v` running over a basis of `F` and `ℓ` over the dual basis of `F'`, these entries are the matrix of
the chart compression of `P` in the two frames. They are how an operator between bundles is
described in local coordinates: in each chart, a differential operator between bundles is a matrix
of scalar differential operators, and so the quantization of a matrix-valued polynomial symbol.

This file shows that the entries of the compression of a differential operator are differential
operators, and computes their principal symbols. It is the bundle version of
`OpenPartialHomeomorph.chartCompression`, which treats operators on the smooth functions.

* `OpenPartialHomeomorph.sectionChartCompression_mem_differentialOperators`: every entry of the
  chart compression of a differential operator `P : Γ(V) → Γ(W)` of order at most `m`, in
  Grothendieck's sense of iterated commutators with multiplication operators
  (`TauCeti.differentialOperators`), with no continuity assumed, is a differential operator of
  order at most `m` on `C^∞(E)`. If a cutoff `χ` equals `1` near the supports of `φ` and `ψ`, then
  multiplication by `g ∈ C^∞(E)` is intertwined by the pullback and the pushforward with
  multiplication by `(χ g) ∘ e`, so the commutator of an entry with `g` is the corresponding entry
  of the commutator of `P` with `(χ g) ∘ e` (`TauCeti.comp_comp_mem_differentialOperators`).
* `OpenPartialHomeomorph.smoothPrincipalSymbol_sectionChartCompressionDifferentialOperators`: at
  a point `x` of the chart target, the principal symbol of the `(ℓ, v)` entry at a covector `η` is
  `φ(x) ψ(x) ℓ (tW (σ(P)(e⁻¹ x)(η ∘ de) (tV⁻¹ v)))`, where `σ(P)` is the geometric principal
  symbol of `P` (`TauCeti.sectionPrincipalSymbol`). So the matrix of principal symbols of the
  entries is the matrix of `σ(P)` at the covector `η ∘ de` in the two frames, multiplied by the
  cutoffs: the principal symbol transforms as a function on the cotangent bundle with values in
  `Hom(V, W)`.

## Main definitions

* `OpenPartialHomeomorph.sectionCutoffPullback`: `f ↦ tV⁻¹ ((ψ f) • v) ∘ e`, extended by zero, as
  a linear map `C^∞(E) → Γ(V)`.
* `OpenPartialHomeomorph.sectionCutoffPushforward`: `h ↦ φ · ℓ (tW h ∘ e⁻¹)`, as a linear map
  `Γ(W) → C^∞(E)`.
* `OpenPartialHomeomorph.sectionChartCompression`: the `(ℓ, v)` entry of the chart compression of
  an operator `Γ(V) → Γ(W)`.
* `OpenPartialHomeomorph.sectionChartCompressionDifferentialOperators`: the same entry of the
  compression of differential operators of order at most `m`.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
* R. O. Wells, *Differential Analysis on Complex Manifolds*, 3rd ed., Springer GTM 65 (2008),
  Chapter IV, §2 (differential operators between vector bundles in local frames).
-/

public section

noncomputable section

open Set Filter Topology TauCeti Bundle
open scoped ContDiff Manifold Distributions

namespace OpenPartialHomeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [T2Space M]
  {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {W : M → Type*} [TopologicalSpace (TotalSpace F' W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [FiberBundle F' W] [VectorBundle ℝ F' W] [ContMDiffVectorBundle ∞ F' W 𝓘(ℝ, E)]
  (tV : Trivialization F (π F V)) [MemTrivializationAtlas tV] (hV : e.source ⊆ tV.baseSet)
  (tW : Trivialization F' (π F' W)) [MemTrivializationAtlas tW] (hW : e.source ⊆ tW.baseSet)

/-! ### Pulling back and pushing forward through a chart and a frame -/

/-- The test function `(ψ f) • v` on the chart target, for a cutoff `ψ` with compact support in the
chart target, a smooth function `f` and a vector `v`. -/
private def cutoffSmulRight (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (v : F) :
    C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] 𝓓(⟨e.target, e.open_target⟩, F) where
  toFun f :=
    { toFun y := (ψ y * f y) • v
      contDiff' := (ψ.contDiff.mul (contMDiff_iff_contDiff.1 f.contMDiff)).smul contDiff_const
      hasCompactSupport' := ψ.hasCompactSupport.mul_right.smul_right
      tsupport_subset' := (tsupport_smul_subset_left _ _).trans
        (tsupport_mul_subset_left.trans ψ.tsupport_subset) }
  map_add' f g := TestFunction.ext fun y ↦ by
    simp [TestFunction.coe_mk, mul_add, add_smul]
  map_smul' c f := TestFunction.ext fun y ↦ by
    simp [TestFunction.coe_mk, mul_left_comm, mul_smul]

include he hV in
/-- **Pulling a function on a chart back to a section.** For a cutoff `ψ` with compact support in
the target of the chart `e`, a frame `tV` of `V` over the chart source and a vector `v` of the model
fibre, the smooth section of `V` whose coefficients in the frame are `(ψ f)(e x) • v` on the chart
source, and which vanishes elsewhere, as a linear map `C^∞(E) → Γ(V)` in `f`. -/
def sectionCutoffPullback (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (v : F) :
    C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] Cₛ^∞⟮𝓘(ℝ, E); F, V⟯ :=
  (ContMDiffSection.compactlySupported 𝓘(ℝ, E) F ∞ V).subtype ∘ₗ
    tV.chartTestSection (n := ⊤) e (contMDiffOn_of_mem_maximalAtlas he) hV ∘ₗ
      cutoffSmulRight ψ v

theorem sectionCutoffPullback_apply_of_mem (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (v : F)
    (f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) {x : M} (hx : x ∈ e.source) :
    e.sectionCutoffPullback he tV hV ψ v f x = tV.symmL ℝ x ((ψ (e x) * f (e x)) • v) :=
  tV.chartTestSection_apply_of_mem (n := ⊤) e _ hV _ hx

theorem sectionCutoffPullback_apply_of_notMem (ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (v : F)
    (f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) {x : M} (hx : x ∉ e.source) :
    e.sectionCutoffPullback he tV hV ψ v f x = 0 :=
  tV.chartTestSection_apply_of_notMem (n := ⊤) e _ hV _ hx

omit [T2Space M] in
include he hW in
/-- The frame coefficients `ℓ (tW (h (e⁻¹ y)))` of a smooth section `h` of `W`, cut off by `φ`, are
smooth on `E`. -/
private theorem contMDiff_cutoffPushforwardFun (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (ℓ : F' →L[ℝ] ℝ) (h : Cₛ^∞⟮𝓘(ℝ, E); F', W⟯) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      fun y ↦ φ y * ℓ (tW.continuousLinearMapAt ℝ (e.symm y) (h (e.symm y))) := by
  refine ContMDiffOn.contMDiff_smul_of_tsupport_subset (fun y hy ↦ ?_) e.open_target
    φ.contDiff.contMDiff.contMDiffOn φ.tsupport_subset
  have hys : e.symm y ∈ tW.baseSet := hW (e.map_target hy)
  have hcy : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e.symm y :=
    (contMDiffOn_symm_of_mem_maximalAtlas he).contMDiffAt (e.open_target.mem_nhds hy)
  have hsy := ((tW.contMDiffAt_section_iff hys).1 (h.contMDiff _)).comp y hcy
  refine ((ℓ.contMDiff.contMDiffAt).comp y hsy).contMDiffWithinAt.congr (fun z hz ↦ ?_) ?_
  · simp [tW.coe_linearMapAt_of_mem (hW (e.map_target hz))]
  · simp [tW.coe_linearMapAt_of_mem hys]

include he hW in
/-- **Pushing a section forward to a chart.** For a cutoff `φ` with compact support in the target
of the chart `e`, a frame `tW` of `W` over the chart source and a functional `ℓ` on the model fibre,
the smooth function `y ↦ φ(y) ℓ (tW (h (e⁻¹ y)))` on `E`, which vanishes outside the chart target,
as a linear map `Γ(W) → C^∞(E)` in `h`. -/
def sectionCutoffPushforward (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (ℓ : F' →L[ℝ] ℝ) :
    Cₛ^∞⟮𝓘(ℝ, E); F', W⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯ where
  toFun h := ⟨_, contMDiff_cutoffPushforwardFun he tW hW φ ℓ h⟩
  map_add' g h := by
    ext y
    -- As in `OpenPartialHomeomorph.cutoffPushforward`, the anonymous constructor elaborates to a
    -- bare subtype, so `ContMDiffMap.coe_add` cannot rewrite it; `change` unfolds the coercions.
    change φ y * ℓ (tW.continuousLinearMapAt ℝ (e.symm y) ((g + h) (e.symm y))) =
      φ y * ℓ (tW.continuousLinearMapAt ℝ (e.symm y) (g (e.symm y))) +
        φ y * ℓ (tW.continuousLinearMapAt ℝ (e.symm y) (h (e.symm y)))
    simp [mul_add]
  map_smul' c h := by
    ext y
    change φ y * ℓ (tW.continuousLinearMapAt ℝ (e.symm y) ((c • h) (e.symm y))) =
      c * (φ y * ℓ (tW.continuousLinearMapAt ℝ (e.symm y) (h (e.symm y))))
    simp [mul_left_comm]

omit [T2Space M] in
@[simp]
theorem sectionCutoffPushforward_apply (φ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (ℓ : F' →L[ℝ] ℝ)
    (h : Cₛ^∞⟮𝓘(ℝ, E); F', W⟯) (y : E) :
    e.sectionCutoffPushforward he tW hW φ ℓ h y =
      φ y * ℓ (tW.continuousLinearMapAt ℝ (e.symm y) (h (e.symm y))) :=
  (rfl)

/-! ### Chart compressions -/

/-- The `(ℓ, v)` **entry of the chart compression** of an operator `P : Γ(V) → Γ(W)` by cutoffs
`φ` and `ψ` with compact supports in the target of the chart `e`, in frames `tV` and `tW` over the
chart source: the operator `f ↦ φ · ℓ (tW (P (tV⁻¹ ((ψ f) • v) ∘ e)) ∘ e⁻¹)` on the smooth
functions on `E`, linear in `P`. With `v` running over a basis of the model fibre of `V` and `ℓ`
over the dual basis of that of `W`, these are the entries of the matrix of `P` in the chart and the
frames, localized on the left by `φ` and on the right by `ψ`. -/
def sectionChartCompression (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (ℓ : F' →L[ℝ] ℝ) (v : F) :
    (Cₛ^∞⟮𝓘(ℝ, E); F, V⟯ →ₗ[ℝ] Cₛ^∞⟮𝓘(ℝ, E); F', W⟯) →ₗ[ℝ]
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯ where
  toFun P := e.sectionCutoffPushforward he tW hW φ ℓ ∘ₗ P ∘ₗ e.sectionCutoffPullback he tV hV ψ v
  map_add' P₁ P₂ := by rw [LinearMap.add_comp, LinearMap.comp_add]
  map_smul' c P := by
    rw [LinearMap.smul_comp, LinearMap.comp_smul, RingHom.id_apply]

theorem sectionChartCompression_def (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (ℓ : F' →L[ℝ] ℝ) (v : F) (P : Cₛ^∞⟮𝓘(ℝ, E); F, V⟯ →ₗ[ℝ] Cₛ^∞⟮𝓘(ℝ, E); F', W⟯) :
    e.sectionChartCompression he tV hV tW hW φ ψ ℓ v P =
      e.sectionCutoffPushforward he tW hW φ ℓ ∘ₗ P ∘ₗ e.sectionCutoffPullback he tV hV ψ v :=
  (rfl)

@[simp]
theorem sectionChartCompression_apply (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ))
    (ℓ : F' →L[ℝ] ℝ) (v : F) (P : Cₛ^∞⟮𝓘(ℝ, E); F, V⟯ →ₗ[ℝ] Cₛ^∞⟮𝓘(ℝ, E); F', W⟯)
    (f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) (y : E) :
    e.sectionChartCompression he tV hV tW hW φ ψ ℓ v P f y =
      φ y * ℓ (tW.continuousLinearMapAt ℝ (e.symm y)
        (P (e.sectionCutoffPullback he tV hV ψ v f) (e.symm y))) :=
  (rfl)

section Intertwining

variable {φ ψ χ : 𝓓(⟨e.target, e.open_target⟩, ℝ)}

/-- Pulling back by `ψ` intertwines multiplication by `g` with multiplication by the pullback of
`g` by a cutoff `χ` equal to `1` on the support of `ψ`. -/
theorem sectionCutoffPullback_smul (hχ : tsupport ψ ⊆ χ ⁻¹' {1}) (v : F)
    (g f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    e.sectionCutoffPullback he tV hV ψ v (g • f) =
      e.cutoffPullback he χ g • e.sectionCutoffPullback he tV hV ψ v f := by
  ext x
  by_cases hx : x ∈ e.source
  · simp only [ContMDiffSection.smul_apply, sectionCutoffPullback_apply_of_mem he tV hV _ _ _ hx,
      cutoffPullback_apply_of_mem he _ _ hx, smul_eq_mul, ContMDiffMap.coe_mul, Pi.mul_apply,
      ← map_smul, smul_smul]
    by_cases hψ : ψ (e x) = 0
    · simp [hψ]
    · rw [show χ (e x) = 1 from hχ (subset_tsupport _ hψ)]
      ring_nf
  · simp [sectionCutoffPullback_apply_of_notMem he tV hV _ _ _ hx]

/-- Pushing forward by `φ` intertwines multiplication by the pullback of `g` by a cutoff `χ` equal
to `1` on the support of `φ` with multiplication by `g`. -/
theorem sectionCutoffPushforward_smul (hχ : tsupport φ ⊆ χ ⁻¹' {1}) (ℓ : F' →L[ℝ] ℝ)
    (g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) (h : Cₛ^∞⟮𝓘(ℝ, E); F', W⟯) :
    e.sectionCutoffPushforward he tW hW φ ℓ (e.cutoffPullback he χ g • h) =
      g • e.sectionCutoffPushforward he tW hW φ ℓ h := by
  ext y
  simp only [sectionCutoffPushforward_apply, ContMDiffSection.smul_apply, map_smul, smul_eq_mul,
    ContMDiffMap.coe_mul, Pi.mul_apply]
  by_cases hφ : φ y = 0
  · simp [hφ]
  · have hy : y ∈ e.target := φ.tsupport_subset (subset_tsupport _ hφ)
    rw [cutoffPullback_apply_of_mem he _ _ (e.map_target hy), e.right_inv hy,
      show χ y = 1 from hχ (subset_tsupport _ hφ)]
    ring

/-- Pulling back by `ψ` and pushing forward by `φ` intertwine multiplication by `g` with
multiplication by the pullback of `g` by a cutoff `χ` equal to `1` on the supports of `φ` and
`ψ`. -/
private theorem smul_intertwining (hχ : tsupport φ ∪ tsupport ψ ⊆ χ ⁻¹' {1}) (ℓ : F' →L[ℝ] ℝ)
    (v : F) (g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) :
    (∀ f, e.sectionCutoffPullback he tV hV ψ v (g • f) =
        e.cutoffPullback he χ g • e.sectionCutoffPullback he tV hV ψ v f) ∧
      ∀ h, e.sectionCutoffPushforward he tW hW φ ℓ (e.cutoffPullback he χ g • h) =
        g • e.sectionCutoffPushforward he tW hW φ ℓ h :=
  ⟨sectionCutoffPullback_smul he tV hV (subset_union_right.trans hχ) v g,
    sectionCutoffPushforward_smul he tW hW (subset_union_left.trans hχ) ℓ g⟩

/-- The iterated commutator of an entry of a chart compression with `g` is the same entry of the
compression of the iterated commutator with the pullback of `g` by a cutoff `χ` equal to `1` on the
supports of `φ` and `ψ`. -/
theorem smulCommutator_pow_sectionChartCompression (hχ : tsupport φ ∪ tsupport ψ ⊆ χ ⁻¹' {1})
    (ℓ : F' →L[ℝ] ℝ) (v : F) (g : C^∞⟮𝓘(ℝ, E), E; ℝ⟯)
    (P : Cₛ^∞⟮𝓘(ℝ, E); F, V⟯ →ₗ[ℝ] Cₛ^∞⟮𝓘(ℝ, E); F', W⟯) (k : ℕ) :
    (smulCommutator ℝ g ^ k) (e.sectionChartCompression he tV hV tW hW φ ψ ℓ v P) =
      e.sectionChartCompression he tV hV tW hW φ ψ ℓ v
        ((smulCommutator ℝ (e.cutoffPullback he χ g) ^ k) P) :=
  smulCommutator_pow_comp_comp (smul_intertwining he tV hV tW hW hχ ℓ v g).1
    (smul_intertwining he tV hV tW hW hχ ℓ v g).2 P k

end Intertwining

/-- **Chart compressions of differential operators between bundles.** Every entry of the chart
compression of a differential operator `Γ(V) → Γ(W)` of order at most `m` is a differential
operator of order at most `m` on `C^∞(E)`. -/
theorem sectionChartCompression_mem_differentialOperators [FiniteDimensional ℝ E]
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (ℓ : F' →L[ℝ] ℝ) (v : F)
    {P : Cₛ^∞⟮𝓘(ℝ, E); F, V⟯ →ₗ[ℝ] Cₛ^∞⟮𝓘(ℝ, E); F', W⟯} {m : ℕ}
    (hP : P ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ Cₛ^∞⟮𝓘(ℝ, E); F, V⟯
      Cₛ^∞⟮𝓘(ℝ, E); F', W⟯ m) :
    e.sectionChartCompression he tV hV tW hW φ ψ ℓ v P ∈ differentialOperators ℝ
      C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m := by
  obtain ⟨χ, hχ⟩ := TestFunction.exists_eventually_eq_one_nhdsSet_tsupport_union φ ψ
  exact comp_comp_mem_differentialOperators
    (fun g ↦ ⟨_, smul_intertwining he tV hV tW hW hχ.self_of_nhdsSet ℓ v g⟩) hP

/-- The `(ℓ, v)` entry of the chart compression of differential operators `Γ(V) → Γ(W)` of order at
most `m`, as a linear map to the differential operators of order at most `m` on `C^∞(E)`. -/
def sectionChartCompressionDifferentialOperators [FiniteDimensional ℝ E]
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (ℓ : F' →L[ℝ] ℝ) (v : F) (m : ℕ) :
    differentialOperators ℝ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ Cₛ^∞⟮𝓘(ℝ, E); F, V⟯ Cₛ^∞⟮𝓘(ℝ, E); F', W⟯ m →ₗ[ℝ]
      differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ m :=
  (e.sectionChartCompression he tV hV tW hW φ ψ ℓ v).restrict fun _ ↦
    e.sectionChartCompression_mem_differentialOperators he tV hV tW hW φ ψ ℓ v

@[simp]
theorem coe_sectionChartCompressionDifferentialOperators [FiniteDimensional ℝ E]
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (ℓ : F' →L[ℝ] ℝ) (v : F) {m : ℕ}
    (P : differentialOperators ℝ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ Cₛ^∞⟮𝓘(ℝ, E); F, V⟯
      Cₛ^∞⟮𝓘(ℝ, E); F', W⟯ m) :
    (e.sectionChartCompressionDifferentialOperators he tV hV tW hW φ ψ ℓ v m P :
        C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯) =
      e.sectionChartCompression he tV hV tW hW φ ψ ℓ v P :=
  (rfl)

theorem sectionChartCompressionDifferentialOperators_apply [FiniteDimensional ℝ E]
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (ℓ : F' →L[ℝ] ℝ) (v : F) {m : ℕ}
    (P : differentialOperators ℝ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ Cₛ^∞⟮𝓘(ℝ, E); F, V⟯
      Cₛ^∞⟮𝓘(ℝ, E); F', W⟯ m)
    (f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯) (y : E) :
    (e.sectionChartCompressionDifferentialOperators he tV hV tW hW φ ψ ℓ v m P).val f y =
      φ y * ℓ (tW.continuousLinearMapAt ℝ (e.symm y)
        (P.val (e.sectionCutoffPullback he tV hV ψ v f) (e.symm y))) :=
  (rfl)

/-! ### The principal symbol of a chart compression -/

section PrincipalSymbol

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [FiniteDimensional ℝ F]

/-- **The principal symbol of a chart compression between bundles.** At a point `x` of the chart
target, the principal symbol of the `(ℓ, v)` entry of the chart compression of `P` at a covector
`η` is `φ(x) ψ(x)` times the coefficient along `ℓ`, in the frame `tW`, of the principal symbol of
`P` at `e⁻¹ x` at the covector `η ∘ de`, applied to the vector of `V` with coefficients `v` in the
frame `tV`. -/
theorem smoothPrincipalSymbol_sectionChartCompressionDifferentialOperators
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (ℓ : F' →L[ℝ] ℝ) (v : F) {m : ℕ}
    (P : differentialOperators ℝ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ Cₛ^∞⟮𝓘(ℝ, E); F, V⟯
      Cₛ^∞⟮𝓘(ℝ, E); F', W⟯ m)
    {x : E} (hx : x ∈ e.target) (η : TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ) :
    smoothPrincipalSymbol 𝓘(ℝ, E) BoundarylessManifold.isInteriorPoint
        (e.sectionChartCompressionDifferentialOperators he tV hV tW hW φ ψ ℓ v m P) η =
      φ x * ψ x * ℓ (tW.continuousLinearMapAt ℝ (e.symm x)
        (sectionPrincipalSymbol 𝓘(ℝ, E) (x := e.symm x) BoundarylessManifold.isInteriorPoint P
          (η.comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e (e.symm x))) (tV.symmL ℝ (e.symm x) v))) := by
  obtain ⟨χ, hχ⟩ := TestFunction.exists_eventually_eq_one_nhdsSet_tsupport_union φ ψ
  obtain ⟨g, -, rfl⟩ := exists_contMDiffMap_mvfderiv_eq (I := 𝓘(ℝ, E)) x (0 : ℝ) η
  -- The `m`-fold commutator of the entry with `g` is the same entry of the compression of the
  -- `m`-fold commutator `Q` of `P` with the pullback of `g`, an operator of order zero.
  set Q := (smulCommutator ℝ (e.cutoffPullback he χ g) ^ m)
    (P : Cₛ^∞⟮𝓘(ℝ, E); F, V⟯ →ₗ[ℝ] Cₛ^∞⟮𝓘(ℝ, E); F', W⟯) with hQ
  rw [smoothPrincipalSymbol_mvfderiv, coe_sectionChartCompressionDifferentialOperators,
    smulCommutator_pow_sectionChartCompression he tV hV tW hW hχ.self_of_nhdsSet, ← hQ,
    sectionChartCompression_apply]
  by_cases hφ : φ x = 0
  · simp [hφ]
  -- The principal symbol of `P` at the differential of the pullback of `g`, applied to the value
  -- of the pulled back section, is `1 / m!` times the value of `Q` on that section.
  have hσ := sectionPrincipalSymbol_mvfderiv (x := e.symm x) BoundarylessManifold.isInteriorPoint
    P (e.cutoffPullback he χ g) (e.sectionCutoffPullback he tV hV ψ v 1)
  rw [mvfderiv_cutoffPullback he g hx
      (hχ.filter_mono (nhds_le_nhdsSet (subset_union_left (subset_tsupport _ hφ)))),
    sectionCutoffPullback_apply_of_mem he tV hV _ _ _ (e.map_target hx)] at hσ
  simp only [e.right_inv hx, ContMDiffMap.coe_one, Pi.one_apply, mul_one, map_smul, ← hQ] at hσ
  have h := congrArg (fun w ↦ φ x * ℓ (tW.continuousLinearMapAt ℝ (e.symm x) w)) hσ
  simp only [map_smul, smul_eq_mul] at h
  linear_combination -h

end PrincipalSymbol

end OpenPartialHomeomorph
