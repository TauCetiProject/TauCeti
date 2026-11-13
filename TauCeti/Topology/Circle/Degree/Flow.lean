/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Circle.Degree.Secant

/-!
# Short secants of a loop and maps moving the loop along itself

Let `q` be an injective loop in a Hausdorff space `X`, parametrized by `AddCircle 1`, and let
`S : X × X → ℂ` be continuous, with no zeros off the diagonal near the diagonal. For small
`r > 0` the short forward secants `τ ↦ S (q τ, q (τ + r))` vanish nowhere.

Let `ρ (θ, ·)` be a continuous family of maps of `X`, for instance a flow, preserving the trace
of `q`, equal to the identity at `θ = 0`, with `ρ (-θ, ·)` inverse to `ρ (θ, ·)` on the trace,
and without fixed points on the trace for small `θ > 0`. For small `θ`, the map `ρ (θ, ·)` moves
every point of `q` a little along `q`, always in the same direction, because the displacement
of the parameter is continuous, never zero, and the circle is connected; replacing `θ` by `-θ`
makes this direction the positive one. Homotoping the forward displacement of the parameter
linearly to the constant `r` shows that the directions of the short forward secants have the
degree of the directions of the field `x ↦ S (x, ρ (θ, x))` along `q`
(`ContinuousMap.exists_flow_degree_secant_eq`). No differentiability of `q` or of `ρ` is used.

## Main results

* `ContinuousMap.exists_flow_degree_secant_eq`: there are arbitrarily small times `θ ≠ 0` such that
  for all short steps `r > 0` the short forward secants of `S` along `q` vanish nowhere and
  their directions have the degree of the directions of `x ↦ S (x, ρ (θ, x))` along `q`.
-/

public section

open Set Filter Function
open scoped unitInterval Topology

namespace ContinuousMap

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- **Short secants and maps moving a loop along itself.** Let `q` be an injective loop in `X`
and `ρ (θ, ·)` a continuous family of maps of `X` preserving the trace of `q`, equal to the
identity at `θ = 0`, with `ρ (-θ, ·)` inverse to `ρ (θ, ·)` on the trace, and without fixed points
on the trace for small `θ > 0`. Let `S` be a continuous function on `X × X` whose zeros in a
neighborhood `U` of the diagonal all lie on the diagonal. Then there are arbitrarily small
times `θ ≠ 0` such that, for all short steps `r > 0`, the short forward secants
`τ ↦ S (q τ, q (τ + r))` vanish nowhere and their directions have the degree of the directions of
`x ↦ S (x, ρ (θ, x))` along `q`. -/
theorem exists_flow_degree_secant_eq (q : C(AddCircle (1 : ℝ), X)) (hq : Injective q)
    (ρ : ℝ × X → X) (hρ : Continuous ρ) (hρ0 : ∀ τ, ρ (0, q τ) = q τ)
    (hρinv : ∀ θ τ, ρ (-θ, ρ (θ, q τ)) = q τ) (hρne : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ τ, ρ (θ, q τ) ≠ q τ)
    (hρq : ∀ θ τ, ρ (θ, q τ) ∈ range q)
    (S : C(X × X, ℂ)) {U : Set (X × X)} (hU : IsOpen U) (hdiag : ∀ x, (x, x) ∈ U)
    (hzero : ∀ x y, (x, y) ∈ U → S (x, y) = 0 → x = y)
    {P : ℝ → Prop} (hP : ∀ᶠ θ in 𝓝 (0 : ℝ), P θ) :
    ∃ θ : ℝ, θ ≠ 0 ∧ P θ ∧ ∃ δ : ℝ, 0 < δ ∧
      (∀ r ∈ Ioo 0 δ, ∀ τ : AddCircle (1 : ℝ), S (q τ, q (τ + r)) ≠ 0) ∧
      ∀ r ∈ Ioo 0 δ, ∀ {v w : Circle} (γ : Path v v) (η : Path w w),
        (∀ t : I, (γ t : ℂ) =
          S (q (t : ℝ), q (((t : ℝ) + r : ℝ) : AddCircle (1 : ℝ))) /
            ‖S (q (t : ℝ), q (((t : ℝ) + r : ℝ) : AddCircle (1 : ℝ)))‖) →
        (∀ t : I, (η t : ℂ) = S (q (t : ℝ), ρ (θ, q (t : ℝ))) / ‖S (q (t : ℝ), ρ (θ, q (t : ℝ)))‖) →
        Circle.degree γ = Circle.degree η := by
  obtain ⟨δ₀, hδ₀, hsec₀⟩ := q.exists_pos_forall_secant_mem hU hdiag
  set δ := min δ₀ (1 / 4)
  have hδ : 0 < δ := by positivity
  have hδ4 : δ ≤ 1 / 4 := min_le_right _ _
  have hsec (w : ℝ) (hw : |w| < δ) := hsec₀ w (hw.trans_le (min_le_left _ _))
  let e : AddCircle (1 : ℝ) ≃ₜ range q :=
    (q.continuous.isClosedEmbedding hq).isEmbedding.toHomeomorph
  let ψ : ℝ × AddCircle (1 : ℝ) → AddCircle (1 : ℝ) := fun cτ ↦ e.symm ⟨_, hρq cτ.1 cτ.2⟩
  have hqψ (c : ℝ) (τ : AddCircle (1 : ℝ)) : q (ψ (c, τ)) = ρ (c, q τ) :=
    congrArg Subtype.val (e.apply_symm_apply _)
  obtain ⟨c, hc0, hcP, d, hdc, hd⟩ := AddCircle.exists_forall_eq_add_pos ψ
    (e.symm.continuous.comp ((by fun_prop : Continuous fun cτ : ℝ × AddCircle (1 : ℝ) ↦
      ρ (cτ.1, q cτ.2)).subtype_mk _))
    (fun τ ↦ hq (by rw [hqψ, hρ0]))
    (fun θ τ ↦ hq (by simpa [hqψ] using hρinv (-θ) τ))
    (hρne.mono fun θ hθ τ h ↦ hθ τ (by rw [← hqψ, h])) hδ hP
  have hqd (τ : AddCircle (1 : ℝ)) : q (τ + d τ) = ρ (c, q τ) := by rw [← (hd τ).2, hqψ]
  refine ⟨c, hc0, hcP, δ, hδ, fun r hr τ ↦ q.secant_ne_zero hq hzero
    ⟨hr.1, hr.2.trans_le (by linarith)⟩ (hsec r (abs_lt.2 ⟨by linarith [hr.1], hr.2⟩) τ), ?_⟩
  intro r hr v w γ η hγ hη
  exact q.degree_secant_eq hq hzero (hδ4.trans (by norm_num)) hsec hdc (fun τ ↦ (hd τ).1) hr γ η hγ
    fun t ↦ by rw [hη, hqd]

end ContinuousMap
