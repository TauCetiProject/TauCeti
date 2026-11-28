/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# Invariance of the Gram–Schmidt process under strictly earlier perturbations

If two ordered families `v, w : ι → V` in an inner product space over an `RCLike` field differ at
each index `a` by a linear combination of the strictly earlier vectors `w b` (`b < a`), then
`gramSchmidt 𝕜 v = gramSchmidt 𝕜 w`, and hence `gramSchmidtNormed 𝕜 v = gramSchmidtNormed 𝕜 w`.

## Main results

* `TauCeti.gramSchmidt_eq_of_sub_mem_span`: `gramSchmidt 𝕜 v = gramSchmidt 𝕜 w` when
  `v a - w a ∈ Submodule.span 𝕜 (w '' Set.Iio a)` for every `a`.
* `TauCeti.gramSchmidtNormed_eq_of_sub_mem_span`: the normalized companion
  `gramSchmidtNormed 𝕜 v = gramSchmidtNormed 𝕜 w`.
* `TauCeti.gramSchmidt_eq_of_add_mem_span`: the equivalent form where `v a = w a + u a` with
  `u a ∈ Submodule.span 𝕜 (w '' Set.Iio a)` for every `a`.

## Provenance

Adapted from `grh-lean` (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/New/Spanning/Bessel/Basic.lean`, declaration `New.gramSchmidt_eq_of_sub_mem_span`. Here the
statement is generalized from `ℂ` to any `[RCLike 𝕜]` and paired with its normalized and additive
forms.
-/

public section

open InnerProductSpace
open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 ι V : Type*} [RCLike 𝕜] [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

/-- **Invariance of Gram–Schmidt under strictly earlier perturbations.** If `v a - w a` lies in the
span of `{w b | b < a}` for every `a`, then `gramSchmidt 𝕜 v = gramSchmidt 𝕜 w`. -/
theorem gramSchmidt_eq_of_sub_mem_span {v w : ι → V}
    (h_sub : ∀ a : ι, v a - w a ∈ Submodule.span 𝕜 (w '' Set.Iio a)) :
    gramSchmidt 𝕜 v = gramSchmidt 𝕜 w := by
  funext a
  induction a using WellFoundedLT.induction with | ind a ih
  let B : Submodule 𝕜 V := Submodule.span 𝕜 (gramSchmidt 𝕜 w '' Set.Iio a)
  have h_proj (x : ι → V) (hx : ∀ b < a, gramSchmidt 𝕜 x b = gramSchmidt 𝕜 w b) :
      x a - gramSchmidt 𝕜 x a ∈ B ∧ gramSchmidt 𝕜 x a ∈ Bᗮ := by
    constructor
    · rw [gramSchmidt_def'' 𝕜 x a, add_sub_cancel_left]
      exact B.sum_mem fun b hb ↦ B.smul_mem _
        (Submodule.subset_span ⟨b, Finset.mem_Iio.mp hb, (hx b (Finset.mem_Iio.mp hb)).symm⟩)
    · suffices h_perp : B ⟂ 𝕜 ∙ gramSchmidt 𝕜 x a from
        h_perp.ge (Submodule.mem_span_singleton_self _)
      refine Submodule.isOrtho_span.mpr ?_
      rintro _ ⟨b, hb, rfl⟩ _ rfl
      simpa only [hx b hb] using gramSchmidt_orthogonal 𝕜 x (ne_of_lt hb)
  obtain ⟨hv_span, hv_orth⟩ := h_proj v ih
  obtain ⟨hw_span, hw_orth⟩ := h_proj w fun _ _ ↦ rfl
  have h_diff : v a - w a ∈ B := (span_gramSchmidt_Iio 𝕜 w a).ge (h_sub a)
  have h_span : gramSchmidt 𝕜 v a - gramSchmidt 𝕜 w a ∈ B := by
    simpa [sub_sub_sub_comm] using B.sub_mem h_diff (B.sub_mem hv_span hw_span)
  exact sub_eq_zero.mp (inner_self_eq_zero.mp
    (B.inner_right_of_mem_orthogonal h_span (Bᗮ.sub_mem hv_orth hw_orth)))

/-- **Invariance of normalized Gram–Schmidt under strictly earlier perturbations.** If `v a - w a`
lies in the span of `{w b | b < a}` for every `a`, then
`gramSchmidtNormed 𝕜 v = gramSchmidtNormed 𝕜 w`. -/
theorem gramSchmidtNormed_eq_of_sub_mem_span {v w : ι → V}
    (h_sub : ∀ a : ι, v a - w a ∈ Submodule.span 𝕜 (w '' Set.Iio a)) :
    gramSchmidtNormed 𝕜 v = gramSchmidtNormed 𝕜 w := by
  funext a
  simp only [gramSchmidtNormed, gramSchmidt_eq_of_sub_mem_span h_sub]

/-- Additive form of `TauCeti.gramSchmidt_eq_of_sub_mem_span`: adding a vector from the span of
`{w b | b < a}` to each `w a` does not change `gramSchmidt 𝕜 w`. -/
theorem gramSchmidt_eq_of_add_mem_span {w u : ι → V}
    (hu : ∀ a : ι, u a ∈ Submodule.span 𝕜 (w '' Set.Iio a)) :
    gramSchmidt 𝕜 (fun a ↦ w a + u a) = gramSchmidt 𝕜 w :=
  gramSchmidt_eq_of_sub_mem_span fun a ↦ by simpa only [add_sub_cancel_left] using hu a

end TauCeti
