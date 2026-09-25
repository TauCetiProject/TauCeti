/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Invariant
public import Mathlib.Algebra.Module.Submodule.Range

/-!
# Invariant submodules of commuting and idempotent endomorphisms

Two facts about `Module.End.invtSubmodule f`, the submodules stable under an endomorphism `f`.

The range of an endomorphism is stable under every endomorphism commuting with it.

Let `e` and `f` be idempotent endomorphisms, `P` a submodule stable under `f` and `Q` one stable
under `e`. If `e ξ` and `f ξ` lie in `P ⊔ Q`, then `ξ` can be corrected by an element `ι ∈ P ⊔ Q`
so that `e (ξ - ι) ∈ Q` and `f (ξ - ι) ∈ P`. This is the existence half of Lemma 3 of Popa and
Zagier. There `ℛ` is the space spanned by integral matrices of positive determinant, on which
`PSL(2, ℤ)` acts on both sides, and `π_S = (1 + S) / 2` and `π_U = (1 + U + U²) / 3` are
idempotents. The maps are right multiplications, `e ξ = ξ π_S` and `f ξ = ξ π_U`, while
`P = π_S ℛ` and `Q = π_U ℛ` are the images of left multiplication by `π_S` and `π_U`; they are
stable under `f` and `e` because left and right multiplication commute. The hypotheses say that
`ξ` lies in their set `𝒜`, and `ξ - ι = ξ - ξ_S - ξ_U` is the image of `ξ` under their projection
onto `ℬ`.

## Main results

* `TauCeti.End.range_mem_invtSubmodule_of_commute`: the range of `f` is stable under every `g`
  commuting with `f`.
* `TauCeti.End.exists_mem_sup_apply_sub_mem_of_isIdempotentElem`: the correction `ι ∈ P ⊔ Q`
  above exists.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. 762 (2020), 105–122, arXiv:1711.00327, Section 3, Lemma 3.
-/

public section

namespace TauCeti.End

open Module LinearMap

/-- **The range of an endomorphism is stable under every endomorphism commuting with it.** -/
theorem range_mem_invtSubmodule_of_commute {R M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] {f g : End R M} (h : Commute f g) : range f ∈ g.invtSubmodule :=
  Function.Semiconj.mapsTo_range (f := f) (fa := g) fun x ↦ LinearMap.congr_fun h.eq x

/-- **Popa–Zagier's projection, existence half** (Lemma 3): let `e` and `f` be idempotent, `P` a
submodule stable under `f` and `Q` one stable under `e`. If `e ξ` and `f ξ` lie in `P ⊔ Q`, then
there is `ι ∈ P ⊔ Q` with `e (ξ - ι) ∈ Q` and `f (ξ - ι) ∈ P`.

The scalars form a ring rather than a semiring: over a semiring a submodule need not be closed
under negation, and the statement then fails. -/
theorem exists_mem_sup_apply_sub_mem_of_isIdempotentElem {R M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] {e f : End R M} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    {P Q : Submodule R M} (hP : P ∈ f.invtSubmodule) (hQ : Q ∈ e.invtSubmodule) {ξ : M}
    (heξ : e ξ ∈ P ⊔ Q) (hfξ : f ξ ∈ P ⊔ Q) :
    ∃ ι ∈ P ⊔ Q, e (ξ - ι) ∈ Q ∧ f (ξ - ι) ∈ P := by
  obtain ⟨p₁, hp₁, q₁, hq₁, h₁⟩ := Submodule.mem_sup.1 heξ
  obtain ⟨p₂, hp₂, q₂, hq₂, h₂⟩ := Submodule.mem_sup.1 hfξ
  -- the correction is `ι = p₁ + q₂`: as `e ξ = e (e ξ)` and `f ξ = f (f ξ)`, we get
  -- `e (ξ - ι) = e (q₁ - q₂)` and `f (ξ - ι) = f (p₂ - p₁)`
  have he' : e (p₁ + q₁) = e ξ := by rw [h₁, ← End.mul_apply, he.eq]
  have hf' : f (p₂ + q₂) = f ξ := by rw [h₂, ← End.mul_apply, hf.eq]
  refine ⟨p₁ + q₂, Submodule.add_mem_sup hp₁ hq₂, ?_, ?_⟩
  · simpa [← he'] using hQ (sub_mem hq₁ hq₂)
  · simpa [← hf'] using hP (sub_mem hp₂ hp₁)

end TauCeti.End
