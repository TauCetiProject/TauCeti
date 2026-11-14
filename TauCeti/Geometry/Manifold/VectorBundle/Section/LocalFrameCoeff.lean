/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.LocalFrame
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Module

/-!
# Cut-off and open-restricted local-frame coefficients of smooth sections

Let `V` be a `C^n` vector bundle of finite rank over a manifold `M`, over a complete nontrivially
normed field `𝕜`, let `e` be a trivialization of `V`, and let `b` be a basis of the model fibre.

* Multiplying the `i`-th coefficient of a `C^n` section `s` in `e.localFrame b` by a `C^n` function
  `ρ` supported in `e.baseSet` gives a globally `C^n` function, bundled as a `C^n(M)`-linear map
  `Bundle.Trivialization.cutoffLocalFrameCoeff`. Every ideal `J` of `C^n(M)` is then sent into
  itself: `LinearMap.apply_mem_of_mem_smul_top` carries `J Γ(V)` into `J`.
* Over any open subset `U ⊆ e.baseSet`, the local frame restricts to bundled `C^n` sections
  `Bundle.Trivialization.openLocalFrameSection` of the open-restricted bundle, with dual
  `C^n(U)`-linear coordinate maps `Bundle.Trivialization.openLocalFrameCoeff` expanding every
  smooth section over `U`.

## Main results

* `Bundle.Trivialization.cutoffLocalFrameCoeff`: the cut-off frame coefficient as a
  `C^n(M)`-linear map from `C^n` sections to `C^n` functions.
* `Bundle.Trivialization.apply_eq_sum_cutoffLocalFrameCoeff_smul`: where `ρ = 1`, a smooth section
  is the sum of its cut-off frame coefficients times sections agreeing with the local frame.
* `Bundle.Trivialization.openLocalFrameSection`, `Bundle.Trivialization.openLocalFrameCoeff`:
  bundled local frame sections and dual `C^n(U)`-linear coefficient maps over `U ⊆ e.baseSet`, with
  `Bundle.Trivialization.eq_sum_openLocalFrameCoeff_smul`.
-/

public section

open Bundle Module TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

namespace Bundle.Trivialization

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V] {n : ℕ∞ω} [ContMDiffVectorBundle 1 F V I]
  [ContMDiffVectorBundle n F V I]
  {ι : Type*} (e : Trivialization F (π F V)) [MemTrivializationAtlas e] (b : Basis ι 𝕜 F)
  (ρ : C^n⟮I, M; 𝕜⟯) (hρ : tsupport ρ ⊆ e.baseSet)

/-- The `i`-th coefficient of a `C^n` section in the local frame of `e`, multiplied by a `C^n`
function `ρ` supported in `e.baseSet`, as a `C^n(M)`-linear map to `C^n` functions. -/
def cutoffLocalFrameCoeff (i : ι) : Cₛ^n⟮I; F, V⟯ →ₗ[C^n⟮I, M; 𝕜⟯] C^n⟮I, M; 𝕜⟯ where
  toFun s := ⟨fun y ↦ ρ y * e.localFrameCoeff I b i y (s y),
    e.contMDiff_mul_localFrameCoeff b ρ.contMDiff.contMDiffOn hρ s.contMDiff.contMDiffOn i⟩
  map_add' s t := by
    ext y
    exact congrArg (ρ y * ·) (map_add (e.localFrameCoeff I b i y) (s y) (t y)) |>.trans
      (mul_add _ _ _)
  map_smul' f s := by
    ext y
    have h := congrArg (e.localFrameCoeff I b i y) (ContMDiffSection.smul_apply f s y)
    rw [map_smul, smul_eq_mul] at h
    exact (congrArg (ρ y * ·) h).trans (mul_left_comm _ _ _)

/-- The cut-off frame coefficient of `s` at `y` is `ρ y` times the frame coefficient of `s y`. -/
@[simp]
theorem cutoffLocalFrameCoeff_apply (i : ι) (s : Cₛ^n⟮I; F, V⟯) (y : M) :
    e.cutoffLocalFrameCoeff b ρ hρ i s y = ρ y * e.localFrameCoeff I b i y (s y) :=
  (rfl)

/-- At a point where `ρ = 1` and the sections `fr i` agree with the local frame of `e`, a smooth
section is the sum of its cut-off frame coefficients times the `fr i`. -/
theorem apply_eq_sum_cutoffLocalFrameCoeff_smul [Fintype ι] (fr : ι → Cₛ^n⟮I; F, V⟯)
    (s : Cₛ^n⟮I; F, V⟯) {y : M} (hy : ρ y = 1) (hfr : ∀ i, fr i y = e.localFrame b i y) :
    s y = (∑ i, e.cutoffLocalFrameCoeff b ρ hρ i s • fr i : Cₛ^n⟮I; F, V⟯) y := by
  have hyb : y ∈ e.baseSet := hρ (subset_tsupport _ (by simp [hy]))
  have h := congrFun (map_sum (ContMDiffSection.coeAddHom I F n V)
    (fun i ↦ e.cutoffLocalFrameCoeff b ρ hρ i s • fr i) Finset.univ) y
  simp only [ContMDiffSection.coeAddHom_apply, Finset.sum_apply, ContMDiffSection.smul_apply,
    cutoffLocalFrameCoeff_apply, hfr, hy, one_mul] at h
  rw [h]
  exact e.eq_sum_localFrameCoeff_smul hyb

section OpenSubmanifold

variable {U : Opens M}

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] [ContMDiffVectorBundle 1 F V I] in
variable (I n) in
/-- Over an open subset `U ⊆ e.baseSet`, the `i`-th element of `e.localFrame b` as a bundled `C^n`
section of the open-restricted vector bundle. -/
def openLocalFrameSection (hU : (U : Set M) ⊆ e.baseSet) (i : ι) :
    Cₛ^n⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯ where
  toFun x := e.localFrame b i (x : M)
  contMDiff_toFun :=
    (Bundle.Pullback.contMDiff_iff (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M))
      contMDiff_subtype_val).2
      ⟨contMDiff_id,
        (e.contMDiffOn_localFrame_baseSet n b i).comp_contMDiff contMDiff_subtype_val
          fun x ↦ hU x.2⟩

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] [ContMDiffVectorBundle 1 F V I] in
/-- Evaluating `openLocalFrameSection` at `x : U` gives `e.localFrame b i` at `(x : M)`. -/
-- Normalize the bundled inclusion in the implicit pullback-fibre type for `simp`.
@[simp]
theorem openLocalFrameSection_apply (hU : (U : Set M) ⊆ e.baseSet) (i : ι) (x : U) :
    dsimp% only [ContinuousMap.coe_mk]
      (e.openLocalFrameSection I n b hU i x = e.localFrame b i (x : M)) :=
  (rfl)

variable (I n) in
/-- Over an open subset `U ⊆ e.baseSet`, the `i`-th coefficient in `e.localFrame b` as a
`C^n(U)`-linear map from `C^n` sections over `U` to `C^n` functions on `U`. -/
def openLocalFrameCoeff (hU : (U : Set M) ⊆ e.baseSet) (i : ι) :
    Cₛ^n⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯ →ₗ[C^n⟮I, U; 𝕜⟯]
      C^n⟮I, U; 𝕜⟯ where
  toFun s := ⟨fun x ↦ e.localFrameCoeff I b i (x : M) (s x), by
    let ιU : C(U, M) := ⟨Subtype.val, continuous_subtype_val⟩
    have hlift : CMDiff n (fun x : U ↦ (⟨(x : M), s x⟩ : TotalSpace F V)) :=
      ((Bundle.Pullback.contMDiff_iff ιU contMDiff_subtype_val).1 s.contMDiff).2
    have hcoord : CMDiff n (fun x : U ↦ (e ⟨(x : M), s x⟩).2) := fun x ↦
      ((e.contMDiffAt_iff (e.mem_source.2 (hU x.2))).1 (hlift x)).2
    have hlin : CMDiff n (fun x : U ↦ b.coord i (e ⟨(x : M), s x⟩).2) :=
      (LinearMap.toContinuousLinearMap (b.coord i)).contMDiff.comp hcoord
    refine hlin.congr fun x ↦ ?_
    classical
    let sM : Π z : M, V z := fun z ↦ if hz : z ∈ U then s ⟨z, hz⟩ else 0
    have hsM : sM (x : M) = s x := dite_eq_left x.2
    have heq := e.localFrameCoeff_eq_coeff (I := I) (b := b) (s := sM) (hU x.2) (i := i)
    rw [hsM] at heq
    rw [heq, b.coord_apply]
    exact congrArg (fun v ↦ (b.repr (e ⟨(x : M), v⟩).2) i) hsM⟩
  map_add' s t := by
    ext x
    exact map_add (e.localFrameCoeff I b i (x : M)) (s x) (t x)
  map_smul' f s := by
    ext x
    have h := congrArg (e.localFrameCoeff I b i (x : M)) (ContMDiffSection.smul_apply f s x)
    exact h.trans (map_smul (e.localFrameCoeff I b i (x : M)) (f x) (s x))

/-- Evaluating `openLocalFrameCoeff` at `x : U` applies `e.localFrameCoeff I b i (x : M)`. -/
@[simp]
theorem openLocalFrameCoeff_apply (hU : (U : Set M) ⊆ e.baseSet) (i : ι)
    (s : Cₛ^n⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯) (x : U) :
    dsimp% only [ContinuousMap.coe_mk]
      (e.openLocalFrameCoeff I n b hU i s x = e.localFrameCoeff I b i (x : M) (s x)) :=
  (rfl)

/-- Over `U ⊆ e.baseSet`, `openLocalFrameCoeff` and `openLocalFrameSection` are dual. -/
@[simp]
theorem openLocalFrameCoeff_openLocalFrameSection [DecidableEq ι] (hU : (U : Set M) ⊆ e.baseSet)
    (i j : ι) :
    dsimp% only [ContinuousMap.coe_mk]
      (e.openLocalFrameCoeff I n b hU i (e.openLocalFrameSection I n b hU j) =
        if i = j then 1 else 0) := by
  ext x
  rw [openLocalFrameCoeff_apply, openLocalFrameSection_apply,
    TauCeti.Manifold.localFrameCoeff_localFrame b (hU x.2)]
  split_ifs <;> rfl

/-- Over `U ⊆ e.baseSet`, every `C^n` section is the sum of its `openLocalFrameCoeff` coordinates
against `openLocalFrameSection`. -/
theorem eq_sum_openLocalFrameCoeff_smul [Fintype ι] (hU : (U : Set M) ⊆ e.baseSet)
    (s : Cₛ^n⟮I; F, (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)) *ᵖ V⟯) :
    s = ∑ i, e.openLocalFrameCoeff I n b hU i s • e.openLocalFrameSection I n b hU i := by
  classical
  apply ContMDiffSection.ext
  intro x
  let ιU : C(U, M) := ⟨Subtype.val, continuous_subtype_val⟩
  let sM : Π z : M, V z := fun z ↦ if hz : z ∈ U then s ⟨z, hz⟩ else 0
  have hsM : sM (x : M) = s x := dite_eq_left x.2
  have hsum := congrFun (map_sum (ContMDiffSection.coeAddHom I F n (ιU *ᵖ V))
    (fun i ↦ e.openLocalFrameCoeff I n b hU i s • e.openLocalFrameSection I n b hU i) Finset.univ) x
  simp only [ιU, ContinuousMap.coe_mk, ContMDiffSection.coeAddHom_apply, Finset.sum_apply,
    ContMDiffSection.smul_apply, openLocalFrameCoeff_apply] at hsum
  rw [hsum]
  have hexp := e.eq_sum_localFrameCoeff_smul (I := I) (b := b) (s := sM) (hU x.2)
  rw [hsM] at hexp
  exact hexp.trans (Finset.sum_congr rfl fun i _ ↦ rfl)

end OpenSubmanifold

end Bundle.Trivialization

