/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Completion
public import TauCeti.Analysis.Normed.Module.BanachMazur
public import TauCeti.Analysis.Normed.Operator.FiniteDimensional

/-!
# Finite representability

A normed space `E` is *finitely representable* in a normed space `F` if every
finite-dimensional subspace of `E` embeds linearly into `F` with arbitrarily small distortion:
for every finite-dimensional subspace `S` of `E` and every `ε > 0` there is a continuous linear
map `T : S → F` with `(1 - ε) ‖x‖ ≤ ‖T x‖ ≤ (1 + ε) ‖x‖` for all `x ∈ S`. Thus the
finite-dimensional structure of `E` can be found, up to arbitrarily small perturbation of the
norm, inside `F`. This is the relation in which the local theory of Banach spaces states its
results: the bidual `E**` is finitely representable in `E` (the principle of local
reflexivity), and `ℓ²` is finitely representable in every infinite-dimensional Banach space
(Dvoretzky's theorem).

## Main definitions

* `TauCeti.FinitelyRepresentable 𝕜 E F`: `E` is finitely representable in `F`.

## Main results

* `LinearIsometry.finitelyRepresentable`: a space is finitely representable in every space into
  which it embeds isometrically; in particular `TauCeti.FinitelyRepresentable.refl`.
* `TauCeti.FinitelyRepresentable.trans`: finite representability is transitive.
* `TauCeti.FinitelyRepresentable.submodule`: finite representability is inherited by subspaces.
* `LinearIsometry.finitelyRepresentable_of_denseRange`: a space is finitely representable in
  each of its isometrically embedded dense subspaces; so a space and its completion are each
  finitely representable in the other (`TauCeti.finitelyRepresentable_completion_iff`).
* `TauCeti.finitelyRepresentable_iff_banachMazurDist_lt`: over `ℝ` or `ℂ`, `E` is finitely
  representable in `F` if and only if every finite-dimensional subspace of `E` is at
  Banach–Mazur distance less than `1 + ε` from some subspace of `F`, for every `ε > 0`.

## Implementation notes

The definition uses the two-sided bounds `(1 - ε) ‖x‖ ≤ ‖T x‖ ≤ (1 + ε) ‖x‖`, which make sense
over every normed field. Over `ℝ` or `ℂ` they are equivalent to the classical formulation by the
Banach–Mazur distance `‖T‖ ‖T⁻¹‖`, in which a rescaling of `T` is allowed; over a general normed
field the norms of scalars need not fill out the positive reals, so the two formulations differ.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Definition 11.1.1 and §12.2.
-/

public section

open Metric

namespace TauCeti

variable (𝕜 E F : Type*) [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A normed space `E` is **finitely representable** in a normed space `F` if every
finite-dimensional subspace `S` of `E` embeds into `F` with arbitrarily small distortion: for each
`ε > 0` there is a continuous linear map `T : S → F` with
`(1 - ε) * ‖x‖ ≤ ‖T x‖ ≤ (1 + ε) * ‖x‖` for every `x ∈ S`. -/
def FinitelyRepresentable : Prop :=
  ∀ S : Submodule 𝕜 E, FiniteDimensional 𝕜 S → ∀ ε : ℝ, 0 < ε →
    ∃ T : S →L[𝕜] F, ∀ x : S, (1 - ε) * ‖x‖ ≤ ‖T x‖ ∧ ‖T x‖ ≤ (1 + ε) * ‖x‖

variable {𝕜 E F}

/-- The defining property of `FinitelyRepresentable`. -/
theorem finitelyRepresentable_iff :
    FinitelyRepresentable 𝕜 E F ↔
      ∀ S : Submodule 𝕜 E, FiniteDimensional 𝕜 S → ∀ ε : ℝ, 0 < ε →
        ∃ T : S →L[𝕜] F, ∀ x : S, (1 - ε) * ‖x‖ ≤ ‖T x‖ ∧ ‖T x‖ ≤ (1 + ε) * ‖x‖ :=
  Iff.rfl

/-- If `E` is finitely representable in `F`, then each finite-dimensional subspace of `E` embeds
into `F` with distortion bounds `1 ± ε`, for every `ε > 0`. -/
theorem FinitelyRepresentable.exists_continuousLinearMap (h : FinitelyRepresentable 𝕜 E F)
    (S : Submodule 𝕜 E) [FiniteDimensional 𝕜 S] {ε : ℝ} (hε : 0 < ε) :
    ∃ T : S →L[𝕜] F, ∀ x : S, (1 - ε) * ‖x‖ ≤ ‖T x‖ ∧ ‖T x‖ ≤ (1 + ε) * ‖x‖ :=
  h S ‹_› ε hε

/-- To prove finite representability it suffices to embed each finite-dimensional subspace with
distortion bounds `1 ± ε` for `0 < ε < 1`, since the bounds weaken as `ε` grows. -/
theorem finitelyRepresentable_of_forall_lt_one
    (h : ∀ S : Submodule 𝕜 E, FiniteDimensional 𝕜 S → ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ T : S →L[𝕜] F, ∀ x : S, (1 - ε) * ‖x‖ ≤ ‖T x‖ ∧ ‖T x‖ ≤ (1 + ε) * ‖x‖) :
    FinitelyRepresentable 𝕜 E F := by
  intro S hS ε hε
  obtain ⟨T, hT⟩ := h S hS (min ε (1 / 2)) (lt_min hε (by norm_num))
    ((min_le_right _ _).trans_lt (by norm_num))
  refine ⟨T, fun x ↦ ⟨le_trans ?_ (hT x).1, (hT x).2.trans ?_⟩⟩ <;>
    gcongr <;> exact min_le_left _ _

end TauCeti

namespace LinearIsometry

open TauCeti

variable {𝕜 E F : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A normed space is finitely representable in every normed space into which it embeds
isometrically. -/
theorem finitelyRepresentable (f : E →ₗᵢ[𝕜] F) : FinitelyRepresentable 𝕜 E F := by
  intro S _ ε hε
  refine ⟨f.toContinuousLinearMap.comp S.subtypeL, fun x ↦ ?_⟩
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, Submodule.subtypeL_apply,
    coe_toContinuousLinearMap, norm_map, Submodule.norm_coe]
  constructor <;> nlinarith [norm_nonneg x]

end LinearIsometry

namespace TauCeti

variable {𝕜 E F G : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable (𝕜 E) in
/-- Every normed space is finitely representable in itself. -/
theorem FinitelyRepresentable.refl : FinitelyRepresentable 𝕜 E E :=
  (LinearIsometry.id (R := 𝕜) (E := E)).finitelyRepresentable

/-- Finite representability is **transitive**: compose an embedding of a finite-dimensional
subspace of `E` into `F` with an embedding of its finite-dimensional image into `G`. -/
@[trans]
theorem FinitelyRepresentable.trans (hEF : FinitelyRepresentable 𝕜 E F)
    (hFG : FinitelyRepresentable 𝕜 F G) : FinitelyRepresentable 𝕜 E G := by
  intro S _ ε hε
  -- Both embeddings have distortion bounds `1 ± δ`; then `(1 + δ) ^ 2 ≤ 1 + ε` and
  -- `1 - ε ≤ (1 - δ) ^ 2` because `δ ≤ 1 / 3` and `3 * δ ≤ ε`.
  set δ := min ε 1 / 3 with hδ_def
  have hδ : 0 < δ := by positivity
  have hδε : 3 * δ ≤ ε := by rw [hδ_def]; linarith [min_le_left ε 1]
  have hδ1 : 3 * δ ≤ 1 := by rw [hδ_def]; linarith [min_le_right ε 1]
  obtain ⟨T, hT⟩ := hEF.exists_continuousLinearMap S hδ
  obtain ⟨U, hU⟩ := hFG.exists_continuousLinearMap (LinearMap.range (T : S →ₗ[𝕜] F)) hδ
  refine ⟨U.comp T.rangeRestrict, fun x ↦ ?_⟩
  have hTx : ‖T.rangeRestrict x‖ = ‖T x‖ := by
    rw [← Submodule.norm_coe, ContinuousLinearMap.coe_codRestrict_apply]
  rw [ContinuousLinearMap.comp_apply]
  obtain ⟨hT₁, hT₂⟩ := hT x
  obtain ⟨hU₁, hU₂⟩ := hU (T.rangeRestrict x)
  rw [hTx] at hU₁ hU₂
  have hx := norm_nonneg x
  constructor <;> nlinarith

/-- Finite representability is inherited by subspaces: if `E` is finitely representable in `F`,
then so is every subspace of `E`. -/
theorem FinitelyRepresentable.submodule (h : FinitelyRepresentable 𝕜 E F) (S : Submodule 𝕜 E) :
    FinitelyRepresentable 𝕜 S F :=
  S.subtypeₗᵢ.finitelyRepresentable.trans h

end TauCeti

namespace LinearIsometry

open TauCeti

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A normed space is finitely representable in every normed space that embeds into it
isometrically with dense range: finite-dimensional subspaces can be moved into a dense subspace
with arbitrarily small distortion. -/
theorem finitelyRepresentable_of_denseRange (f : F →ₗᵢ[𝕜] E) (hf : DenseRange f) :
    FinitelyRepresentable 𝕜 E F := by
  intro S _ ε hε
  obtain ⟨U, hU⟩ := Metric.denseRange_iff.1
    (ContinuousLinearMap.denseRange_comp (V := S) (g := f.toContinuousLinearMap) hf) S.subtypeL
    ε hε
  refine ⟨U, fun x ↦ ?_⟩
  -- `f ∘ U` is within `ε` of the inclusion of `S`, and `f` preserves norms.
  have hx : ‖(x : E) - f (U x)‖ ≤ ε * ‖x‖ := by
    rw [dist_eq_norm] at hU
    simpa using (S.subtypeL - f.toContinuousLinearMap.comp U).le_of_opNorm_le hU.le x
  have h₁ := norm_sub_norm_le (x : E) (f (U x))
  have h₂ := norm_sub_norm_le (f (U x)) (x : E)
  rw [norm_sub_rev] at h₂
  simp only [norm_map, Submodule.norm_coe] at h₁ h₂ hx ⊢
  constructor <;> linarith

end LinearIsometry

namespace TauCeti

section Completion

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜 E) in
/-- The completion of a normed space is finitely representable in the space itself. -/
theorem finitelyRepresentable_completion :
    FinitelyRepresentable 𝕜 (UniformSpace.Completion E) E :=
  UniformSpace.Completion.toComplₗᵢ.finitelyRepresentable_of_denseRange <| by
    simpa [UniformSpace.Completion.coe_toComplₗᵢ] using UniformSpace.Completion.denseRange_coe

/-- A normed space is finitely representable in the completion of `F` if and only if it is
finitely representable in `F`. -/
theorem finitelyRepresentable_completion_iff :
    FinitelyRepresentable 𝕜 E (UniformSpace.Completion F) ↔ FinitelyRepresentable 𝕜 E F :=
  ⟨fun h ↦ h.trans (finitelyRepresentable_completion 𝕜 F),
    fun h ↦ h.trans UniformSpace.Completion.toComplₗᵢ.finitelyRepresentable⟩

end Completion

section RCLike

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Over `ℝ` or `ℂ`, `E` is finitely representable in `F` if and only if, for every `ε > 0`,
every finite-dimensional subspace of `E` is isomorphic to a subspace of `F` at Banach–Mazur
distance less than `1 + ε`. -/
theorem finitelyRepresentable_iff_banachMazurDist_lt :
    FinitelyRepresentable 𝕜 E F ↔
      ∀ S : Submodule 𝕜 E, FiniteDimensional 𝕜 S → ∀ ε : ℝ, 0 < ε →
        ∃ G : Submodule 𝕜 F, Nonempty (S ≃L[𝕜] G) ∧ banachMazurDist 𝕜 S G < 1 + ε := by
  constructor
  · intro h S _ ε hε
    -- Embed `S` with distortion bounds `1 ± δ`, where `(1 + δ) / (1 - δ) < 1 + ε`, and
    -- compare `S` with the range of the embedding.
    set δ := ε / (ε + 3) with hδ_def
    have hδ : 0 < δ := by positivity
    have hδε : δ * (ε + 3) = ε := div_mul_cancel₀ _ (by positivity)
    have hδ1 : 0 < 1 - δ := by nlinarith
    obtain ⟨T, hT⟩ := h.exists_continuousLinearMap S hδ
    have hinj : Function.Injective T := by
      refine (injective_iff_map_eq_zero T).2 fun x hx ↦ norm_eq_zero.1 ?_
      have := (hT x).1
      rw [hx, norm_zero] at this
      nlinarith [norm_nonneg x]
    let R := LinearMap.range (T : S →ₗ[𝕜] F)
    let e : S ≃L[𝕜] R := (LinearEquiv.ofInjective (T : S →ₗ[𝕜] F) hinj).toContinuousLinearEquiv
    have he (x : S) : ‖e x‖ = ‖T x‖ := by simp [e, ← Submodule.norm_coe]
    refine ⟨R, ⟨e⟩, (banachMazurDist_le e).trans_lt ?_⟩
    have h₁ : ‖(e : S →L[𝕜] R)‖ ≤ 1 + δ :=
      ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x ↦ by
        simpa [he] using (hT x).2
    have h₂ : ‖(e.symm : R →L[𝕜] S)‖ ≤ (1 - δ)⁻¹ :=
      ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y ↦ by
        obtain ⟨x, rfl⟩ := e.surjective y
        simpa [he, le_inv_mul_iff₀ hδ1] using (hT x).1
    calc ‖(e : S →L[𝕜] R)‖ * ‖(e.symm : R →L[𝕜] S)‖ ≤ (1 + δ) * (1 - δ)⁻¹ := by
          gcongr
      _ < 1 + ε := by
        rw [← div_eq_mul_inv, div_lt_iff₀ hδ1]
        nlinarith
  · intro h S _ ε hε
    obtain ⟨G, hne, hd⟩ := h S ‹_› ε hε
    obtain ⟨e, he⟩ := banachMazurDist_lt_iff.1 hd
    rcases subsingleton_or_nontrivial S with hS | hS
    · exact ⟨0, fun x ↦ by simp [Subsingleton.elim x 0]⟩
    -- Rescale `e` by `c = ‖e⁻¹‖`, so that it no longer shrinks any vector.
    set c := ‖(e.symm : G →L[𝕜] S)‖
    have h₁ : 1 ≤ ‖(e : S →L[𝕜] G)‖ * c :=
      (one_le_banachMazurDist hne).trans (banachMazurDist_le e)
    have hc : 0 ≤ c := norm_nonneg _
    refine ⟨(c : 𝕜) • G.subtypeL.comp (e : S →L[𝕜] G), fun x ↦ ?_⟩
    have hTx : ‖((c : 𝕜) • G.subtypeL.comp (e : S →L[𝕜] G)) x‖ = c * ‖e x‖ := by
      simp [norm_smul, abs_of_nonneg hc]
    have hlow : ‖x‖ ≤ c * ‖e x‖ := by
      simpa using (e.symm : G →L[𝕜] S).le_opNorm (e x)
    have hup : ‖e x‖ ≤ ‖(e : S →L[𝕜] G)‖ * ‖x‖ := (e : S →L[𝕜] G).le_opNorm x
    rw [hTx]
    have hx := norm_nonneg x
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hup hc]

end RCLike

end TauCeti
