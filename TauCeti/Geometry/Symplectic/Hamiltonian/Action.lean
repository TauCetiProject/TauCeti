/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Sphere
public import TauCeti.Geometry.Manifold.TwoForm.Basic

/-!
# The Hamiltonian action functional on contractible loops

Let `σ` be a closed two-form on a manifold `M`, typically a symplectic form, and `K : ℝ → M → ℝ`
a time-dependent Hamiltonian. The action of a loop `γ` with a smooth cap `u`, a cylinder from `γ`
to a constant loop (`TauCeti.IsSmoothCap`), is

`𝒜_K(γ) = ∫ u^* σ - ∫₀¹ K(t, γ(t)) dt`

(`TauCeti.SmoothTwoForm.actionFunctional`). Loops are `1`-periodic maps `γ : ℝ → M`, and the action
is a function of the loop on `[0, 1]` (`TauCeti.SmoothTwoForm.actionFunctional_congr`). When `σ` is
weakly exact, that is, when its integral over every smooth sphere vanishes
(`TauCeti.SmoothForm.IsWeaklyExact`), the area term does not depend on the cap, so the action is a
function on the loops that bound a smooth cap; it can be computed with any cap
(`TauCeti.SmoothTwoForm.actionFunctional_eq`). A constant loop at `x` has
action `-∫₀¹ K(t, x) dt` (`TauCeti.SmoothTwoForm.actionFunctional_const`).

This is the convention `𝒜_K(γ) = ∫ u^* σ - ∫ K dt` of Barraud, Damian, Humilière and Oancea, with
the cylinder oriented from the loop to the reference loop, here a constant loop. The capped
convention `A_K(γ, D) = ∫ K dt + ∫_D σ` of `TauCeti.SymplecticForm.hamiltonianAction` takes the disc
`D` from a point to the loop, that is with the opposite orientation, and has the opposite sign.

## Main definitions

* `TauCeti.SmoothTwoForm.actionFunctional`: the Hamiltonian action functional on contractible
  loops.

## Main results

* `TauCeti.SmoothTwoForm.actionFunctional_eq`: for a closed weakly exact form, the action may be
  computed with any smooth cap.
* `TauCeti.SmoothTwoForm.actionFunctional_congr`: the action is a function of the loop on `[0, 1]`.
* `TauCeti.SmoothTwoForm.actionFunctional_const`: the action of a constant loop.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §3.2.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 1.
* H. Hofer and E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Chapter 6.
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff Interval

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {u : ℝ × ℝ → M} {γ : ℝ → M}

variable (σ) in
/-- The **Hamiltonian action functional** of a two-form `σ` and a time-dependent Hamiltonian `K`
on a loop `γ`: `𝒜_K(γ) = ∫ u^* σ - ∫₀¹ K(t, γ(t)) dt`, where the area term
`TauCeti.SmoothForm.capArea` is the integral over a smooth cap `u` of `γ`, a cylinder from `γ` to a
constant loop. For a closed weakly exact form it does not depend on the cap
(`TauCeti.SmoothTwoForm.actionFunctional_eq`). For a loop which is not `1`-periodic or has no
smooth cap the area term is `0`. -/
def actionFunctional (K : ℝ → M → ℝ) (γ : ℝ → M) : ℝ :=
  σ.capArea γ - ∫ t in (0 : ℝ)..1, K t (γ t)

theorem actionFunctional_def (K : ℝ → M → ℝ) (γ : ℝ → M) :
    σ.actionFunctional K γ = σ.capArea γ - ∫ t in (0 : ℝ)..1, K t (γ t) :=
  (rfl)

/-- **The action may be computed with any cap** of a `1`-periodic loop, for a closed weakly exact
form. -/
theorem actionFunctional_eq (hσ : σ.IsWeaklyExact) (hc : σ.IsClosed) (K : ℝ → M → ℝ)
    (hγ : Function.Periodic γ 1) (hu : IsSmoothCap I u γ) :
    σ.actionFunctional K γ =
      rectangleIntegral σ.1 u (0, 0) (1, 1) - ∫ t in (0 : ℝ)..1, K t (γ t) := by
  rw [actionFunctional_def, hσ.capArea_eq hc hγ hu]

/-- **The action is a function of the loop on `[0, 1]`**: two `1`-periodic loops which agree on
`[0, 1]` have the same action. -/
theorem actionFunctional_congr (K : ℝ → M → ℝ) {γ' : ℝ → M} (hγ : Function.Periodic γ 1)
    (hγ' : Function.Periodic γ' 1) (h : EqOn γ γ' (Icc 0 1)) :
    σ.actionFunctional K γ = σ.actionFunctional K γ' := by
  have hK : ∫ t in (0 : ℝ)..1, K t (γ t) = ∫ t in (0 : ℝ)..1, K t (γ' t) :=
    intervalIntegral.integral_congr fun t ht ↦ by
      rw [h (by rwa [uIcc_of_le zero_le_one] at ht)]
  rw [actionFunctional_def, actionFunctional_def, σ.capArea_congr hγ hγ' h, hK]

/-- The action of a constant loop at `x`, for a closed weakly exact form, is
`-∫₀¹ K(t, x) dt`. -/
@[simp]
theorem actionFunctional_const (hσ : σ.IsWeaklyExact) (hc : σ.IsClosed) (K : ℝ → M → ℝ)
    (x : M) : σ.actionFunctional K (fun _ ↦ x) = -∫ t in (0 : ℝ)..1, K t x := by
  rw [actionFunctional_def, hσ.capArea_const hc, zero_sub]

end SmoothTwoForm

end TauCeti
