/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import TauCeti.NumberTheory.NumberField.CMType.Basic

/-!
# The embedding of a CM type above an infinite place

Let `Φ` be a CM type on a field `E`. Every infinite place `w` of `E` lies below exactly two complex
embeddings, `w.embedding` and its conjugate, and `Φ` contains exactly one of them; this is the
embedding `Φ_w` of `Φ` above `w` (`TauCeti.CMType.embedding`). So `Φ` amounts to the choice of a
complex embedding inducing each infinite place, and `Φ_w` identifies the completion `E_w` with a
subfield of `ℂ`: `TauCeti.CMType.completionEmbedding` is the continuous extension of `Φ_w` to
`E_w`, an isometry.

Adelic constructions over a CM field read the component at `w` of an adele through this
identification, as the coordinates `ℂ^Φ` of the infinite adeles.

## Main definitions

* `TauCeti.CMType.embedding Φ w`: the embedding of `Φ` that induces the infinite place `w`.
* `TauCeti.CMType.completionEmbedding Φ w`: its extension `E_w →+* ℂ`.

## Main results

* `TauCeti.CMType.embedding_eq_iff`: `Φ_w` is the unique embedding of `Φ` inducing `w`.
* `TauCeti.CMType.completionEmbedding_algebraMap`: `completionEmbedding Φ w` extends `Φ_w`.
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
/-- The **embedding of a CM type `Φ` above an infinite place `w`**: of the two complex embeddings
inducing `w`, `w.embedding` and its conjugate, the one that lies in `Φ`. -/
def embedding (w : InfinitePlace E) : E →+* ℂ :=
  if w.embedding ∈ Φ then w.embedding else star w.embedding

/-- The embedding of `Φ` above `w` lies in `Φ`. -/
theorem embedding_mem (w : InfinitePlace E) : Φ.embedding w ∈ Φ := by
  by_cases h : w.embedding ∈ Φ
  · simp [embedding, h]
  · simp [embedding, h]

/-- The embedding of `Φ` above `w` induces `w`. -/
@[simp]
theorem mk_embedding (w : InfinitePlace E) : InfinitePlace.mk (Φ.embedding w) = w := by
  by_cases h : w.embedding ∈ Φ
  · simp [embedding, h]
  · simp only [embedding, h, ite_false]
    rw [← ComplexEmbedding.conjugate, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]

/-- **The embedding of `Φ` above `w` is unique**: it is the only embedding of `Φ` inducing `w`,
since the other embedding inducing `w` is its conjugate. -/
theorem embedding_eq_iff {w : InfinitePlace E} {φ : E →+* ℂ} :
    Φ.embedding w = φ ↔ φ ∈ Φ ∧ InfinitePlace.mk φ = w := by
  refine ⟨fun h ↦ h ▸ ⟨Φ.embedding_mem w, Φ.mk_embedding w⟩, fun ⟨hφ, hw⟩ ↦ ?_⟩
  rcases InfinitePlace.mk_eq_iff.mp ((Φ.mk_embedding w).trans hw.symm) with h | h
  · exact h
  · -- the conjugate of an embedding of `Φ` is not in `Φ`
    rw [ComplexEmbedding.conjugate] at h
    have := (Φ.star_mem_iff (Φ.embedding w)).1 (h ▸ hφ)
    exact absurd (Φ.embedding_mem w) this

/-- An embedding of `Φ` is the embedding of `Φ` above the place it induces. -/
@[simp]
theorem embedding_mk {φ : E →+* ℂ} (hφ : φ ∈ Φ) : Φ.embedding (InfinitePlace.mk φ) = φ :=
  Φ.embedding_eq_iff.2 ⟨hφ, rfl⟩

/-- The absolute value of `Φ_w x` is `|x|_w`. -/
@[simp]
theorem norm_embedding_apply (w : InfinitePlace E) (x : E) : ‖Φ.embedding w x‖ = w x := by
  rw [← InfinitePlace.apply, mk_embedding]

/-! ### The extension to the completion -/

open scoped Classical in
/-- The **extension of the embedding of `Φ` above `w` to the completion** `E_w →+* ℂ`: Mathlib's
extension `extensionEmbedding w` of `w.embedding` when `w.embedding ∈ Φ`, and its complex conjugate
otherwise. -/
def completionEmbedding (w : InfinitePlace E) : w.Completion →+* ℂ :=
  if w.embedding ∈ Φ then extensionEmbedding w else (starRingEnd ℂ).comp (extensionEmbedding w)

/-- `completionEmbedding Φ w` extends the embedding `Φ_w` of `Φ` above `w`. -/
@[simp]
theorem completionEmbedding_algebraMap (w : InfinitePlace E) (x : E) :
    Φ.completionEmbedding w (algebraMap E w.Completion x) = Φ.embedding w x := by
  rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
    Algebra.algebraMap_self_apply]
  by_cases h : w.embedding ∈ Φ
  · simp [completionEmbedding, embedding, h]
  · simp [completionEmbedding, embedding, h]

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
      simpa only [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply,
        Algebra.algebraMap_self_apply, WithAbs.toAbs_ofAbs] using
        (h x.ofAbs).trans (Φ.completionEmbedding_algebraMap w x.ofAbs).symm

end TauCeti.CMType
