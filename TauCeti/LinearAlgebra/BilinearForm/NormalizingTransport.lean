/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import TauCeti.Analysis.InnerProductSpace.Spectral.Normalization

/-!
# Normalizing a nondegenerate bilinear form on a finite-dimensional real vector space

Let `q` be a symmetric nondegenerate bilinear form and `h` a positive definite symmetric bilinear
form on a finite-dimensional real vector space `V`, which carries no topology or inner product of
its own. Relative to `h`, the space splits into the negative and positive relative spectral
subspaces of `q` (`LinearMap.BilinForm.relativeSpectralSubspace` for `Iio 0` and `Ioi 0`),
orthogonal for both forms, with `q` negative definite on the first and positive definite on the
second. This file constructs the canonical endomorphism `N` of `V` which preserves both subspaces
and carries `q` to `-h` on the first and to `h` on the second
(`LinearMap.BilinForm.normalizingTransport`). So for `u = u⁻ + u⁺` along the splitting,

`q (N u) (N u) = h (u⁺, u⁺) - h (u⁻, u⁻)`:

in the variable `w = N⁻¹ v`, the value `q v v` is Sylvester's normal form, written with `h` and
without a choice of basis. It is `|K|^(-1/2)` for the operator `K` with `h (K u) v = q u v`.

`N` is read through any linear identification of `V` with a Euclidean space, where it is the
normalizing transport of the pulled-back pair (`ContinuousLinearMap.normalizingTransport`). It is
determined by the properties above together with `0 ≤ h (N u) u` and self-adjointness for `q`
(`LinearMap.BilinForm.eq_normalizingTransport_of_mem_relativeSpectralSubspace`), so it does not
depend on that identification. This is the form in which the normalization applies to the fibres
of a vector bundle, such as the normal spaces of a Morse–Bott critical submanifold with the normal
Hessian and a fibre metric, which are finite-dimensional vector spaces without a chosen norm.

## Main declarations

In the namespace `LinearMap.BilinForm`:

* `normalizingTransport q h`: the normalizing endomorphism of `q` relative to `h`.
* `normalizingTransport_apply_mem_relativeSpectralSubspace_Iio` and
  `apply_normalizingTransport_normalizingTransport_of_mem_relativeSpectralSubspace_Iio`, with their
  `Ioi` counterparts: `N` preserves the relative spectral subspaces and carries `q` to `-h` on the
  negative one and to `h` on the positive one.
* `apply_normalizingTransport_left_eq_right`, `metric_apply_normalizingTransport_left_eq_right`
  and `metric_apply_normalizingTransport_self_pos`: `N` is self-adjoint for `q`, and self-adjoint
  and positive definite for `h`.
* `bijective_normalizingTransport`: `N` is invertible.
* `eq_normalizingTransport_of_mem_relativeSpectralSubspace` and `eq_normalizingTransport_iff`:
  the characterization.
* `normalizingTransport_compl₁₂`: naturality under linear equivalences.

## References

* R. Bhatia, *Positive Definite Matrices*, Princeton University Press, 2007, Chapter 1.
* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
-/

public section

noncomputable section

open InnerProductSpace Module Set

namespace LinearMap.BilinForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- A linear identification of `V` with the Euclidean space of its dimension, through which the
normalizing transport is computed. -/
private def euclideanEquiv (V : Type*) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] :
    V ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ V)) :=
  .ofFinrankEq _ _ (by simp)

/-- A bilinear form on `V`, pulled back to the Euclidean model along `euclideanEquiv V`. -/
private def euclideanForm (q : LinearMap.BilinForm ℝ V) :
    EuclideanSpace ℝ (Fin (finrank ℝ V)) →L[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ V)) →L[ℝ] ℝ :=
  (q.compl₁₂ ((euclideanEquiv V).symm : EuclideanSpace ℝ (Fin (finrank ℝ V)) →ₗ[ℝ] V)
    (euclideanEquiv V).symm).toContinuousBilinearMap

/-- The **normalizing transport** of a bilinear form `q` relative to a second bilinear form `h` on
a finite-dimensional real vector space. When `q` is symmetric and nondegenerate and `h` is
symmetric and positive definite, it is the endomorphism `|K|^(-1/2)`, for `K` defined by
`h (K u) v = q u v`, which preserves the negative and positive relative spectral subspaces of `q`
with respect to `h` and carries `q` to `-h` on the first and to `h` on the second.

It is read through a linear identification `T` of `V` with a Euclidean space, as the normalizing
transport `ContinuousLinearMap.normalizingTransport` of the pair of forms pulled back along `T⁻¹`.
These properties, together with `0 ≤ h (N u) u` and self-adjointness for `q`, determine it
(`LinearMap.BilinForm.eq_normalizingTransport_of_mem_relativeSpectralSubspace`), so it does not
depend on `T`. -/
def normalizingTransport (q h : LinearMap.BilinForm ℝ V) : Module.End ℝ V :=
  ((euclideanEquiv V).symm : EuclideanSpace ℝ (Fin (finrank ℝ V)) →ₗ[ℝ] V) ∘ₗ
    ((euclideanForm q).normalizingTransport (euclideanForm h) :
      EuclideanSpace ℝ (Fin (finrank ℝ V)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ V))) ∘ₗ
    (euclideanEquiv V : V →ₗ[ℝ] EuclideanSpace ℝ (Fin (finrank ℝ V)))

variable {q h : LinearMap.BilinForm ℝ V}

private theorem normalizingTransport_apply_eq (u : V) :
    q.normalizingTransport h u = (euclideanEquiv V).symm
      ((euclideanForm q).normalizingTransport (euclideanForm h) (euclideanEquiv V u)) :=
  (rfl)

private theorem euclideanForm_apply (w w' : EuclideanSpace ℝ (Fin (finrank ℝ V))) :
    euclideanForm q w w' = q ((euclideanEquiv V).symm w) ((euclideanEquiv V).symm w') := by
  simp [euclideanForm, LinearMap.toContinuousBilinearMap_apply]

/-- The pulled-back form, read as a bilinear form on the Euclidean model, is the pull-back of `q`
along `(euclideanEquiv V)⁻¹`. -/
private theorem toBilinForm_euclideanForm :
    (euclideanForm q).toBilinForm =
      q.compl₁₂ ((euclideanEquiv V).symm : EuclideanSpace ℝ (Fin (finrank ℝ V)) →ₗ[ℝ] V)
        (euclideanEquiv V).symm := by
  ext w w'
  simp [euclideanForm_apply]

private theorem euclideanForm_apply_apply (u v : V) :
    euclideanForm q (euclideanEquiv V u) (euclideanEquiv V v) = q u v := by
  simp [euclideanForm_apply]

private theorem euclideanForm_comm (hq : q.IsSymm) (w w' : EuclideanSpace ℝ (Fin (finrank ℝ V))) :
    euclideanForm q w w' = euclideanForm q w' w := by
  rw [euclideanForm_apply, euclideanForm_apply, hq.eq]

/-- A nondegenerate form pulls back to an injective one. -/
private theorem injective_euclideanForm (hq' : LinearMap.ker q = ⊥) :
    Function.Injective (euclideanForm q) := fun w w' hww' ↦ by
  have hker : (euclideanEquiv V).symm (w - w') ∈ LinearMap.ker q := by
    rw [LinearMap.mem_ker]
    ext x
    obtain ⟨y, rfl⟩ := (euclideanEquiv V).symm.surjective x
    have := congr($hww' y)
    rw [euclideanForm_apply, euclideanForm_apply] at this
    simp [map_sub, this]
  rwa [hq', Submodule.mem_bot, map_eq_zero_iff _ (euclideanEquiv V).symm.injective,
    sub_eq_zero] at hker

/-- A positive definite symmetric form pulls back to one with strictly positive Riesz operator. -/
private theorem isStrictlyPositive_euclideanForm (hh : h.IsSymm)
    (hh' : ∀ v, v ≠ 0 → 0 < h v v) :
    IsStrictlyPositive (continuousLinearMapOfBilin (𝕜 := ℝ) (euclideanForm h)) :=
  isStrictlyPositive_continuousLinearMapOfBilin_iff.mpr ⟨euclideanForm_comm hh,
    fun _ hw ↦ hh' _ ((map_ne_zero_iff _ (euclideanEquiv V).symm.injective).mpr hw)⟩

/-- A vector of `V` lies in a relative spectral subspace of `(q, h)` exactly when its image in the
Euclidean model lies in that of the pulled-back pair. -/
private theorem mem_relativeSpectralSubspace_euclideanForm_iff {Ω : Set ℝ} {u : V} :
    euclideanEquiv V u ∈
        (euclideanForm h).toBilinForm.relativeSpectralSubspace (euclideanForm q).toBilinForm Ω ↔
      u ∈ h.relativeSpectralSubspace q Ω := by
  rw [toBilinForm_euclideanForm, toBilinForm_euclideanForm,
    mem_relativeSpectralSubspace_compl₁₂_iff, LinearEquiv.symm_apply_apply]

/-- The normalizing transport is self-adjoint for `q`. -/
theorem apply_normalizingTransport_left_eq_right (hh : h.IsSymm) (hh' : ∀ v, v ≠ 0 → 0 < h v v)
    (u v : V) : q (q.normalizingTransport h u) v = q u (q.normalizingTransport h v) := by
  have := ContinuousLinearMap.apply_normalizingTransport_left_eq_right (q := euclideanForm q)
    (isStrictlyPositive_euclideanForm hh hh') (euclideanEquiv V u) (euclideanEquiv V v)
  rwa [euclideanForm_apply, euclideanForm_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply] at this

/-- The normalizing transport is self-adjoint for `h`. -/
theorem metric_apply_normalizingTransport_left_eq_right (hh : h.IsSymm)
    (hh' : ∀ v, v ≠ 0 → 0 < h v v) (u v : V) :
    h (q.normalizingTransport h u) v = h u (q.normalizingTransport h v) := by
  have := ContinuousLinearMap.metric_apply_normalizingTransport_left_eq_right (q := euclideanForm q)
    (isStrictlyPositive_euclideanForm hh hh') (euclideanEquiv V u) (euclideanEquiv V v)
  rwa [euclideanForm_apply, euclideanForm_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply] at this

variable (hq : q.IsSymm) (hq' : LinearMap.ker q = ⊥) (hh : h.IsSymm)
  (hh' : ∀ v, v ≠ 0 → 0 < h v v)
include hq hq' hh hh'

/-- The normalizing transport preserves the negative relative spectral subspace. -/
theorem normalizingTransport_apply_mem_relativeSpectralSubspace_Iio {u : V}
    (hu : u ∈ h.relativeSpectralSubspace q (Iio 0)) :
    q.normalizingTransport h u ∈ h.relativeSpectralSubspace q (Iio 0) := by
  rw [← mem_relativeSpectralSubspace_euclideanForm_iff, normalizingTransport_apply_eq,
    LinearEquiv.apply_symm_apply]
  exact ContinuousLinearMap.normalizingTransport_apply_mem_relativeSpectralSubspace_Iio
    (isStrictlyPositive_euclideanForm hh hh') (euclideanForm_comm hq) (injective_euclideanForm hq')
    (mem_relativeSpectralSubspace_euclideanForm_iff.mpr hu)

/-- The normalizing transport preserves the positive relative spectral subspace. -/
theorem normalizingTransport_apply_mem_relativeSpectralSubspace_Ioi {u : V}
    (hu : u ∈ h.relativeSpectralSubspace q (Ioi 0)) :
    q.normalizingTransport h u ∈ h.relativeSpectralSubspace q (Ioi 0) := by
  rw [← mem_relativeSpectralSubspace_euclideanForm_iff, normalizingTransport_apply_eq,
    LinearEquiv.apply_symm_apply]
  exact ContinuousLinearMap.normalizingTransport_apply_mem_relativeSpectralSubspace_Ioi
    (isStrictlyPositive_euclideanForm hh hh') (euclideanForm_comm hq) (injective_euclideanForm hq')
    (mem_relativeSpectralSubspace_euclideanForm_iff.mpr hu)

/-- On the negative relative spectral subspace, the normalizing transport carries `q` to `-h`. -/
theorem apply_normalizingTransport_normalizingTransport_of_mem_relativeSpectralSubspace_Iio
    {u : V} (hu : u ∈ h.relativeSpectralSubspace q (Iio 0)) :
    q (q.normalizingTransport h u) (q.normalizingTransport h u) = -h u u := by
  have hhp := isStrictlyPositive_euclideanForm hh hh'
  have hw := mem_relativeSpectralSubspace_euclideanForm_iff.mpr hu
  have := ContinuousLinearMap.apply_normalizingTransport_normalizingTransport hhp
    (euclideanForm_comm hq) (injective_euclideanForm hq') (euclideanEquiv V u) (euclideanEquiv V u)
  rw [(ContinuousLinearMap.negativeSpectralProjection_apply_eq_self_iff hhp
      (euclideanForm_comm hq)).mpr hw, euclideanForm_apply_apply, euclideanForm_apply] at this
  rw [normalizingTransport_apply_eq, this]
  ring

/-- On the positive relative spectral subspace, the normalizing transport carries `q` to `h`. -/
theorem apply_normalizingTransport_normalizingTransport_of_mem_relativeSpectralSubspace_Ioi
    {u : V} (hu : u ∈ h.relativeSpectralSubspace q (Ioi 0)) :
    q (q.normalizingTransport h u) (q.normalizingTransport h u) = h u u := by
  have hhp := isStrictlyPositive_euclideanForm hh hh'
  have hw := mem_relativeSpectralSubspace_euclideanForm_iff.mpr hu
  have := ContinuousLinearMap.apply_normalizingTransport_normalizingTransport hhp
    (euclideanForm_comm hq) (injective_euclideanForm hq') (euclideanEquiv V u) (euclideanEquiv V u)
  rw [(ContinuousLinearMap.negativeSpectralProjection_apply_eq_zero_iff hhp (euclideanForm_comm hq)
      (injective_euclideanForm hq')).mpr hw, map_zero, euclideanForm_apply_apply,
    euclideanForm_apply] at this
  rw [normalizingTransport_apply_eq, this]
  ring

/-- The normalizing transport is positive definite for `h`. -/
theorem metric_apply_normalizingTransport_self_pos {u : V} (hu : u ≠ 0) :
    0 < h (q.normalizingTransport h u) u := by
  have := ContinuousLinearMap.metric_apply_normalizingTransport_self_pos
    (isStrictlyPositive_euclideanForm hh hh') (euclideanForm_comm hq) (injective_euclideanForm hq')
    ((map_ne_zero_iff _ (euclideanEquiv V).injective).mpr hu)
  rwa [euclideanForm_apply, LinearEquiv.symm_apply_apply] at this

/-- The normalizing transport is invertible. -/
theorem bijective_normalizingTransport : Function.Bijective (q.normalizingTransport h) := by
  have hN := ContinuousLinearMap.isUnit_iff_bijective.mp
    (ContinuousLinearMap.isUnit_normalizingTransport (isStrictlyPositive_euclideanForm hh hh')
      (euclideanForm_comm hq) (injective_euclideanForm hq'))
  exact (euclideanEquiv V).symm.bijective.comp (hN.comp (euclideanEquiv V).bijective)

/-- **Characterization of the normalizing transport.** For a symmetric nondegenerate form `q` and
a positive definite symmetric form `h` on a finite-dimensional real vector space, an endomorphism
`S` with `0 ≤ h (S u) u` for all `u` which is self-adjoint for `q`, maps the negative and the
positive relative spectral subspaces of `q` with respect to `h` into themselves, and carries `q` to
`-h` on the first and to `h` on the second, is the normalizing transport of `q` relative to `h`. -/
theorem eq_normalizingTransport_of_mem_relativeSpectralSubspace {S : Module.End ℝ V}
    (hpos : ∀ u, 0 ≤ h (S u) u) (hqS : ∀ u v, q (S u) v = q u (S v))
    (hneg : ∀ u ∈ h.relativeSpectralSubspace q (Iio 0),
      S u ∈ h.relativeSpectralSubspace q (Iio 0) ∧ q (S u) (S u) = -h u u)
    (hposS : ∀ u ∈ h.relativeSpectralSubspace q (Ioi 0),
      S u ∈ h.relativeSpectralSubspace q (Ioi 0) ∧ q (S u) (S u) = h u u) :
    S = q.normalizingTransport h :=
  (euclideanEquiv V).eq_comp_normalizingTransport_comp (fun _ _ ↦ euclideanForm_apply _ _)
    (fun _ _ ↦ euclideanForm_apply _ _) (euclideanForm_comm hq) (injective_euclideanForm hq')
    (isStrictlyPositive_euclideanForm hh hh') hpos hqS hneg hposS

/-- **Characterization of the normalizing transport.** For a symmetric nondegenerate form `q` and
a positive definite symmetric form `h` on a finite-dimensional real vector space, an endomorphism
`S` is the normalizing transport of `q` relative to `h` exactly when `0 ≤ h (S u) u` for all `u`,
`S` is self-adjoint for `q`, maps the negative and the positive relative spectral subspaces of `q`
with respect to `h` into themselves, and carries `q` to `-h` on the first and to `h` on the
second. -/
theorem eq_normalizingTransport_iff {S : Module.End ℝ V} :
    S = q.normalizingTransport h ↔
      (∀ u, 0 ≤ h (S u) u) ∧ (∀ u v, q (S u) v = q u (S v)) ∧
        (∀ u ∈ h.relativeSpectralSubspace q (Iio 0),
          S u ∈ h.relativeSpectralSubspace q (Iio 0) ∧ q (S u) (S u) = -h u u) ∧
        ∀ u ∈ h.relativeSpectralSubspace q (Ioi 0),
          S u ∈ h.relativeSpectralSubspace q (Ioi 0) ∧ q (S u) (S u) = h u u := by
  refine ⟨?_, fun ⟨hpos, hqS, hneg, hposS⟩ ↦
    eq_normalizingTransport_of_mem_relativeSpectralSubspace hq hq' hh hh' hpos hqS hneg hposS⟩
  rintro rfl
  refine ⟨fun u ↦ ?_, apply_normalizingTransport_left_eq_right hh hh', fun u hu ↦ ⟨?_, ?_⟩,
    fun u hu ↦ ⟨?_, ?_⟩⟩
  · rcases eq_or_ne u 0 with rfl | hu
    · simp
    · exact (metric_apply_normalizingTransport_self_pos hq hq' hh hh' hu).le
  · exact normalizingTransport_apply_mem_relativeSpectralSubspace_Iio hq hq' hh hh' hu
  · exact apply_normalizingTransport_normalizingTransport_of_mem_relativeSpectralSubspace_Iio
      hq hq' hh hh' hu
  · exact normalizingTransport_apply_mem_relativeSpectralSubspace_Ioi hq hq' hh hh' hu
  · exact apply_normalizingTransport_normalizingTransport_of_mem_relativeSpectralSubspace_Ioi
      hq hq' hh hh' hu

/-- **Naturality of the normalizing transport.** Pulling both forms back along a linear
equivalence `e` conjugates the normalizing transport by `e`. Normalizations computed in two
linear identifications of a vector space therefore agree under the transition. -/
theorem normalizingTransport_compl₁₂ {W : Type*} [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ W] (e : W ≃ₗ[ℝ] V) :
    normalizingTransport (q.compl₁₂ (e : W →ₗ[ℝ] V) (e : W →ₗ[ℝ] V))
        (h.compl₁₂ (e : W →ₗ[ℝ] V) (e : W →ₗ[ℝ] V)) =
      (e.symm : V →ₗ[ℝ] W) ∘ₗ q.normalizingTransport h ∘ₗ (e : W →ₗ[ℝ] V) := by
  obtain ⟨hpos, hqS, hneg, hposS⟩ := (eq_normalizingTransport_iff hq hq' hh hh').mp rfl
  refine ((eq_normalizingTransport_iff (q := q.compl₁₂ (e : W →ₗ[ℝ] V) (e : W →ₗ[ℝ] V))
    (h := h.compl₁₂ (e : W →ₗ[ℝ] V) (e : W →ₗ[ℝ] V)) ⟨fun _ _ ↦ hq.eq _ _⟩
    (ker_compl₁₂_eq_bot e hq') ⟨fun _ _ ↦ hh.eq _ _⟩
    fun w hw ↦ hh' _ ((map_ne_zero_iff _ e.injective).mpr hw)).mpr
    ⟨fun w ↦ ?_, fun w w' ↦ ?_, fun w hw ↦ ?_, fun w hw ↦ ?_⟩).symm
  · simpa using hpos (e w)
  · simpa using hqS (e w) (e w')
  · rw [mem_relativeSpectralSubspace_compl₁₂_iff] at hw ⊢
    simpa using hneg (e w) hw
  · rw [mem_relativeSpectralSubspace_compl₁₂_iff] at hw ⊢
    simpa using hposS (e w) hw

end LinearMap.BilinForm
