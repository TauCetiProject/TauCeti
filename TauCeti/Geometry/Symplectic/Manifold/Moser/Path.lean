/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Moser
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# Moser's theorem along an exact path

Let `σ₀` and `σ₁` be smooth two-forms on a compact boundaryless manifold `M` whose difference is
exact, `σ₁ - σ₀ = dβ` for a smooth one-form `β`, and such that every form
`σ_s = σ₀ + s (σ₁ - σ₀)` on the segment between them, `s ∈ [0, 1]`, is symplectic. Moser's
theorem gives a smooth isotopy `ψ_t` of `M`, starting at the identity, which pulls the forms of
the segment back to `σ₀`.

Moser's stability theorem (`TauCeti.SmoothTwoForm.exists_isotopy_mpullback_eq`) takes a family
of two-forms parametrized by the whole real line, symplectic at every time, together with
primitives of its velocity. The segment is symplectic only for `s ∈ [0, 1]` in general, so it is
traversed along the smooth step `c = Real.smoothTransition`, which is `0` for `t ≤ 0`, `1` for
`t ≥ 1` and takes every value of `[0, 1]`. The family `σ_{c(t)}`
(`TauCeti.SmoothForm.lineMapFamily`) is symplectic at every time, and its velocity
`c'(t) (σ₁ - σ₀) = d (c'(t) β)` is exact with the smooth family of primitives `c'(t) β`. So the
isotopy satisfies `ψ_t^* σ_{c(t)} = σ₀` for every `t`
(`TauCeti.SmoothTwoForm.exists_isotopy_mpullback_add_smoothTransition_smul_eq`), and every form
`σ_s` with `s ∈ [0, 1]` is pulled back to `σ₀` by one of its maps
(`TauCeti.SmoothTwoForm.exists_diffeomorph_mpullback_add_smul_eq`).

The primitive `β` is part of the data. Equal de Rham classes of `σ₀` and `σ₁` provide one; the
hypotheses here ask for it explicitly.

## Main results

* `TauCeti.SmoothTwoForm.exists_isotopy_mpullback_add_smoothTransition_smul_eq`: the Moser
  isotopy along the segment, traversed by the smooth step `Real.smoothTransition`.
* `TauCeti.SmoothTwoForm.exists_diffeomorph_mpullback_add_smul_eq`: each form of the segment is
  diffeomorphic to `σ₀`.

## References

* J. Moser, *On the volume elements on a manifold*, Transactions of the American Mathematical
  Society 120 (1965), 286–294.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.2 (Moser isotopy).
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless] [T2Space M] [CompactSpace M]

/-- **Moser's theorem along an exact path.** Let `σ₀` and `σ₁` be smooth two-forms on a compact
boundaryless manifold with `σ₁ - σ₀ = dβ`, such that every `σ₀ + s • (σ₁ - σ₀)` with `s ∈ [0, 1]`
is symplectic. Then there is an isotopy `ψ_t`, jointly smooth in `(t, x)`, with `ψ_0 = id` and
`ψ_t^* (σ₀ + c(t) • (σ₁ - σ₀)) = σ₀` for every `t`, where `c = Real.smoothTransition` runs from
`0` for `t ≤ 0` to `1` for `t ≥ 1`. -/
theorem exists_isotopy_mpullback_add_smoothTransition_smul_eq (σ₀ σ₁ : SmoothTwoForm I M)
    (β : SmoothForm I M ℝ 1) (hβ : (σ₁ - σ₀).val = mextDeriv β.val)
    (hσ : ∀ s ∈ Icc (0 : ℝ) 1, IsSymplectic (σ₀ + s • (σ₁ - σ₀))) :
    ∃ ψ : ℝ → M ≃ₘ⟮I, I⟯ M, ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun p : ℝ × M ↦ ψ p.1 p.2) ∧
      (∀ x, ψ 0 x = x) ∧
      ∀ t, SmoothForm.mpullback (ψ t) (ψ t).contMDiff
          (σ₀ + Real.smoothTransition t • (σ₁ - σ₀)) = σ₀ := by
  have hc : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  have hc' : ContDiff ℝ ∞ (deriv Real.smoothTransition) :=
    (contDiff_infty_iff_deriv.1 hc).2
  obtain ⟨ψ, hψ, hψ0, -, hψσ⟩ := exists_isotopy_mpullback_eq
    (SmoothForm.lineMapFamily σ₀ σ₁ hc) (SmoothForm.lineMapFamily 0 β hc') (fun t ↦ by
      rw [SmoothForm.mpullback_prodMk_lineMapFamily]
      exact hσ _ ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩)
    (fun t ↦ by
      have h := congrArg Subtype.val
        (SmoothForm.mpullback_prodMk_timeDeriv_lineMapFamily σ₀ σ₁ hc t)
      rw [SmoothForm.coe_mpullback, SmoothForm.coe_timeDeriv] at h
      rw [h, SmoothForm.mpullback_prodMk_lineMapFamily]
      simp [hβ])
  refine ⟨ψ, hψ, hψ0, fun t ↦ ?_⟩
  simpa [SmoothForm.mpullback_prodMk_lineMapFamily] using hψσ t

/-- **Moser's theorem along an exact path, pointwise.** Under the hypotheses of
`TauCeti.SmoothTwoForm.exists_isotopy_mpullback_add_smoothTransition_smul_eq`, every form
`σ₀ + s • (σ₁ - σ₀)` with `s ∈ [0, 1]` is pulled back to `σ₀` by a diffeomorphism of `M`, one of
the maps of a smooth isotopy starting at the identity. -/
theorem exists_diffeomorph_mpullback_add_smul_eq (σ₀ σ₁ : SmoothTwoForm I M)
    (β : SmoothForm I M ℝ 1) (hβ : (σ₁ - σ₀).val = mextDeriv β.val)
    (hσ : ∀ s ∈ Icc (0 : ℝ) 1, IsSymplectic (σ₀ + s • (σ₁ - σ₀))) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) :
    ∃ φ : M ≃ₘ⟮I, I⟯ M, SmoothForm.mpullback φ φ.contMDiff (σ₀ + s • (σ₁ - σ₀)) = σ₀ := by
  obtain ⟨ψ, -, -, hψ⟩ := exists_isotopy_mpullback_add_smoothTransition_smul_eq σ₀ σ₁ β hβ hσ
  obtain ⟨t, -, rfl⟩ := Real.smoothTransition.surjOn_Icc hs
  exact ⟨ψ t, hψ t⟩

end SmoothTwoForm

end TauCeti
