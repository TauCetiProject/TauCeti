/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The pullback of a set of covectors

Let `f : E → E'` be a map between real inner product spaces, `U` a subset of `E` and `Γ` a set of
covectors `(y, η) ∈ E' × E'`. The pullback

`f^* Γ = {(x, Df(x)ᵀ η) | x ∈ U, (f x, η) ∈ Γ}` (`TauCeti.covectorPullback f U Γ`)

pulls the covectors over `f x` back to `x` by the transpose of the derivative of `f` at `x`. It
bounds the wave front set of the pullback of a distribution along a smooth map
(Hörmander I, Theorem 8.2.4): `WF(f^* T) ⊆ f^* WF(T)`. It is monotone in `Γ`, and it is a cone
whenever `Γ` is one.

## Main declarations

* `TauCeti.covectorPullback`: the pullback `f^* Γ` of a set of covectors.
* `TauCeti.mem_covectorPullback`, `TauCeti.covectorPullback_mono`,
  `TauCeti.smul_mem_covectorPullback`: its membership, its monotonicity in `Γ` and its invariance
  under positive scalings of covectors.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.2.4.
-/

public section

open scoped InnerProduct

namespace TauCeti

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [CompleteSpace E']

/-- The pullback `f^* Γ = {(x, Df(x)ᵀ η) | x ∈ U, (f x, η) ∈ Γ}` of a set `Γ` of covectors along a
map `f` over a set `U`: covectors over `f x` pull back by the transpose of the derivative of `f`
at `x`. -/
def covectorPullback (f : E → E') (U : Set E) (Γ : Set (E' × E')) : Set (E × E) :=
  {p | p.1 ∈ U ∧ ∃ η, (f p.1, η) ∈ Γ ∧ ((fderiv ℝ f p.1)†) η = p.2}

@[simp]
theorem mem_covectorPullback {f : E → E'} {U : Set E} {Γ : Set (E' × E')} {p : E × E} :
    p ∈ covectorPullback f U Γ ↔ p.1 ∈ U ∧ ∃ η, (f p.1, η) ∈ Γ ∧ ((fderiv ℝ f p.1)†) η = p.2 :=
  Iff.rfl

theorem covectorPullback_mono {f : E → E'} {U : Set E} {Γ Γ' : Set (E' × E')} (h : Γ ⊆ Γ') :
    covectorPullback f U Γ ⊆ covectorPullback f U Γ' :=
  fun _ ⟨hx, η, hη, hp⟩ ↦ ⟨hx, η, h hη, hp⟩

/-- The pullback of a cone is a cone. -/
theorem smul_mem_covectorPullback {f : E → E'} {U : Set E} {Γ : Set (E' × E')}
    (hcone : ∀ p ∈ Γ, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ) {p : E × E}
    (hp : p ∈ covectorPullback f U Γ) {t : ℝ} (ht : 0 < t) :
    (p.1, t • p.2) ∈ covectorPullback f U Γ := by
  obtain ⟨hx, η, hη, hηp⟩ := hp
  exact ⟨hx, t • η, hcone _ hη t ht, by rw [map_smul, hηp]⟩

end TauCeti
