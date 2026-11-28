/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import TauCeti.NumberTheory.NumberField.CMType.Basic

/-!
# The completion of a field with a CM type at an infinite place

Let `Φ` be a CM type on a field `E`. Every infinite place `w` of `E` lies below exactly two complex
embeddings, `w.embedding` and its conjugate, and `Φ` contains exactly one of them, the embedding
`Φ_w` of `Φ` above `w` (`TauCeti.CMType.embedding`). This file identifies the completion `E_w` with
`ℂ` through `Φ_w`: `TauCeti.CMType.completionEmbedding` is the continuous extension of `Φ_w` to
`E_w`, an isometry, and it is onto because a field with a CM type is totally complex
(`TauCeti.CMType.nonempty_iff_isTotallyComplex`).

Adelic constructions over a CM field read the component at `w` of an adele through this
identification, as the coordinates `ℂ^Φ` of the infinite adeles, and turn complex coordinates back
into local components through its inverse.

## Main definitions

* `TauCeti.CMType.completionEmbedding Φ w`: the extension `E_w →+* ℂ` of `Φ_w`.
* `TauCeti.CMType.completionRingEquiv Φ w`: the same map as a ring isomorphism `E_w ≃+* ℂ`.

## Main results

* `TauCeti.CMType.completionEmbedding_algebraMap`: `completionEmbedding Φ w` extends `Φ_w`.
* `TauCeti.CMType.completionEmbedding_coe`: the same statement for the coercion of `WithAbs`.
* `TauCeti.CMType.surjective_completionEmbedding`: `completionEmbedding Φ w` is onto.
* `TauCeti.CMType.norm_completionEmbedding`: `completionEmbedding Φ w` is norm-preserving.
* `TauCeti.CMType.eq_completionEmbedding`: `completionEmbedding Φ w` is the unique continuous
  extension of `Φ_w`.
-/

public section
noncomputable section

open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped ComplexConjugate

namespace TauCeti.CMType

variable {E : Type*} [Field E] (Φ : CMType E)

open scoped Classical in
/-- The **extension of the embedding of `Φ` above `w` to the completion** `E_w →+* ℂ`: Mathlib's
extension `extensionEmbedding w` of `w.embedding` when `w.embedding ∈ Φ`, and its complex conjugate
otherwise. -/
def completionEmbedding (w : InfinitePlace E) : w.Completion →+* ℂ :=
  if w.embedding ∈ Φ then extensionEmbedding w else (starRingEnd ℂ).comp (extensionEmbedding w)

/-- `completionEmbedding Φ w` extends `Φ_w`, stated for the coercion `WithAbs w.val → E_w`. -/
@[simp]
theorem completionEmbedding_coe (w : InfinitePlace E) (x : WithAbs w.val) :
    Φ.completionEmbedding w x = Φ.embedding w x.ofAbs := by
  by_cases h : w.embedding ∈ Φ
  · simp [completionEmbedding, Φ.embedding_of_mem h, h]
  · simp [completionEmbedding, Φ.embedding_of_notMem h, h]

/-- `completionEmbedding Φ w` extends the embedding `Φ_w` of `Φ` above `w`. -/
@[simp]
theorem completionEmbedding_algebraMap (w : InfinitePlace E) (x : E) :
    Φ.completionEmbedding w (algebraMap E w.Completion x) = Φ.embedding w x := by
  rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
    Algebra.algebraMap_self_apply, completionEmbedding_coe, WithAbs.ofAbs_toAbs]

/-- `completionEmbedding Φ w` is an isometry. -/
theorem isometry_completionEmbedding (w : InfinitePlace E) :
    Isometry (Φ.completionEmbedding w) := by
  by_cases h : w.embedding ∈ Φ
  · simpa [completionEmbedding, h] using isometry_extensionEmbedding w
  · simpa [completionEmbedding, h] using
      Complex.isometry_conj.comp (isometry_extensionEmbedding w)

/-- `completionEmbedding Φ w` preserves the norm. -/
@[simp]
theorem norm_completionEmbedding (w : InfinitePlace E) (z : w.Completion) :
    ‖Φ.completionEmbedding w z‖ = ‖z‖ := by
  simpa using (Φ.isometry_completionEmbedding w).norm_map_of_map_zero (map_zero _) z

/-- `completionEmbedding Φ w` is continuous. -/
@[fun_prop, continuity]
theorem continuous_completionEmbedding (w : InfinitePlace E) :
    Continuous (Φ.completionEmbedding w) :=
  (Φ.isometry_completionEmbedding w).continuous

/-- **`completionEmbedding Φ w` is the unique continuous extension of `Φ_w`**: a continuous ring
homomorphism `E_w →+* ℂ` extending the embedding of `Φ` above `w` is `completionEmbedding Φ w`,
since `E` is dense in `E_w`. -/
theorem eq_completionEmbedding {w : InfinitePlace E} {f : w.Completion →+* ℂ}
    (hf : Continuous f) (h : ∀ x : E, f (algebraMap E w.Completion x) = Φ.embedding w x) :
    f = Φ.completionEmbedding w :=
  DFunLike.coe_injective <| AbsoluteValue.Completion.ext hf (Φ.continuous_completionEmbedding w)
    fun x ↦ by
      rw [completionEmbedding_coe, ← h, AbsoluteValue.Completion.algebraMap_def,
        WithAbs.algebraMap_right_apply, Algebra.algebraMap_self_apply, WithAbs.toAbs_ofAbs]

/-- `completionEmbedding Φ w` is onto `ℂ`, since the place `w` is complex: a field with a CM type
is totally complex. -/
theorem surjective_completionEmbedding (w : InfinitePlace E) :
    Function.Surjective (Φ.completionEmbedding w) := by
  have hsurj := surjective_extensionEmbedding_of_isComplex
    ((nonempty_iff_isTotallyComplex.mp ⟨Φ⟩).isComplex w)
  by_cases h : w.embedding ∈ Φ
  · simpa [completionEmbedding, h] using hsurj
  · simpa [completionEmbedding, h] using (starRingEnd ℂ).surjective.comp hsurj

/-- The **identification of the completion `E_w` with `ℂ`** through the embedding `Φ_w` of `Φ`
above `w`: the ring isomorphism whose forward map is `completionEmbedding Φ w`. -/
def completionRingEquiv (w : InfinitePlace E) : w.Completion ≃+* ℂ :=
  RingEquiv.ofBijective (Φ.completionEmbedding w)
    ⟨(Φ.completionEmbedding w).injective, Φ.surjective_completionEmbedding w⟩

/-- The forward map of `completionRingEquiv Φ w` is `completionEmbedding Φ w`. -/
@[simp]
theorem completionRingEquiv_apply (w : InfinitePlace E) (z : w.Completion) :
    Φ.completionRingEquiv w z = Φ.completionEmbedding w z :=
  (rfl)

end TauCeti.CMType
