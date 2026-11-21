/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-!
# Linear independence on images and on subsets of a finite index type

A family `v` is linearly independent on the image `f '' s` of a set under a map injective on `s`
exactly when `v ∘ f` is linearly independent on `s`. This is the linear counterpart of Mathlib's
`affineIndepOn_image_iff`, combining `LinearIndepOn.comp_of_image` and
`LinearIndepOn.image_of_comp`.

When the index type is finite, linear independence of the subfamily indexed by a set `s` can be
tested on coefficient functions on the whole index type that vanish off `s`, with sums over all
indices. This is the subfamily counterpart of Mathlib's `Fintype.linearIndependent_iff`, and the
form in which Carathéodory-type reductions of finite linear combinations use it.

## Main results

* `TauCeti.linearIndepOn_image_iff`: linear independence on `f '' s` versus of `v ∘ f` on `s`.
* `Fintype.linearIndepOn_iff`: linear independence of a subfamily of a finite family, in terms of
  coefficient functions vanishing off the subfamily.
* `LinearIndepOn.restrict_scalars'`: linear independence on a set restricts along a faithful
  scalar action.
-/

public section

namespace TauCeti

variable {ι ι' R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- A family `v` is linearly independent on `f '' s` exactly when `v ∘ f` is linearly independent
on `s`, for `f` injective on `s`. -/
theorem linearIndepOn_image_iff {s : Set ι} {f : ι → ι'} (v : ι' → M) (hf : Set.InjOn f s) :
    LinearIndepOn R v (f '' s) ↔ LinearIndepOn R (v ∘ f) s :=
  ⟨fun h ↦ h.comp_of_image hf, fun h ↦ h.image_of_comp f v⟩

end TauCeti

/-- **Linear independence of a subfamily of a finite family.** The vectors `v i` with `i ∈ s` are
linearly independent exactly when every coefficient function vanishing off `s` with
`∑ i, a i • v i = 0` is zero. -/
theorem Fintype.linearIndepOn_iff {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [Fintype ι] {v : ι → M} {s : Set ι} :
    LinearIndepOn R v s ↔ ∀ a : ι → R, (∀ i ∉ s, a i = 0) → ∑ i, a i • v i = 0 → ∀ i, a i = 0 := by
  rw [_root_.linearIndepOn_iff]
  constructor
  · intro h a has hsum i
    have hmem : (Finsupp.linearEquivFunOnFinite R R ι).symm a ∈ Finsupp.supported R R s := by
      rw [Finsupp.mem_supported']
      exact has
    have h0 := h _ hmem (by
      rw [Finsupp.linearCombination_eq_fintype_linearCombination_apply,
        Fintype.linearCombination_apply, hsum])
    simpa using DFunLike.congr_fun h0 i
  · intro h l hl hsum
    ext i
    refine h l (fun j hj ↦ (Finsupp.mem_supported' R l).1 hl j hj) ?_ i
    rw [← Fintype.linearCombination_apply, ← hsum,
      ← Finsupp.linearCombination_eq_fintype_linearCombination_apply]
    congr 1
    ext j
    simp

namespace LinearIndepOn

/-- A family linearly independent on `s` over `K` remains linearly independent on `s` over a
subring `R` acting faithfully on `K`. -/
theorem restrict_scalars' (R : Type*) {ι K M : Type*} [Semiring R] [Semiring K]
    [AddCommMonoid M] [SMulWithZero R K] [Module R M] [Module K M]
    [IsScalarTower R K M] [FaithfulSMul R K] [IsScalarTower R K K]
    {v : ι → M} {s : Set ι} (hv : LinearIndepOn K v s) : LinearIndepOn R v s :=
  hv.linearIndependent.restrict_scalars' R

end LinearIndepOn
