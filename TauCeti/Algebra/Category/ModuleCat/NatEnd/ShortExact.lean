/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.NatEnd
public import TauCeti.Algebra.Homology.ShortComplex.FunctorCategory

/-!
# Reduction of a module-valued functor modulo an element

Let `Φ : C ⥤ ModuleCat R` be a functor to modules and `a ∈ R`. Suppose that `a` is a
non-zero-divisor on every value `Φ(A)`, and that `q : Φ ⟶ G` is a map to a functor to abelian
groups which kills `a Φ`, is onto at every object and whose kernel at every object is `a Φ(A)`.
Then `0 → Φ → Φ → G → 0`, with first map the action `CategoryTheory.Functor.smulEnd Φ a` of `a`,
is a short exact sequence of functors to abelian groups (`TauCeti.shortExact_smulEnd`). Exactness
in a category of functors to abelian groups is checked objectwise
(`CategoryTheory.ShortComplex.shortExact_of_forall_function_exact`).

## Main results

* `TauCeti.shortExact_smulEnd`: the reduction of a functor to modules modulo a non-zero-divisor
  is short exact.

## References

* [ShortProof]: `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/PadicComparison/Completion.lean` (declaration
  `New.Variety.modShortExact_of_isSMulRegular_of_isReductionMod`); Apache 2.0, Copyright 2026
  Anthropic, PBC. The statement is adapted from this declaration, for functors to modules over a
  ring.
-/

public section

open CategoryTheory

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] {R : Type*} [Ring R]

/-- **Reduction modulo `a`.** Let `Φ` be a functor to `R`-modules on whose values `a` is a
non-zero-divisor, and `q : Φ ⟶ G` a map to a functor to abelian groups which kills `a Φ`, is onto
at every object and whose kernel at every object is `a Φ(A)`. Then `0 → Φ → Φ → G → 0`, with first
map the action of `a`, is short exact. -/
theorem shortExact_smulEnd {Φ : C ⥤ ModuleCat.{w} R} {G : C ⥤ AddCommGrpCat.{w}} {a : R}
    {q : Φ ⋙ forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w} ⟶ G} (hq : (Φ.smulEnd a).asHom ≫ q = 0)
    (ha : ∀ A, IsSMulRegular (Φ.obj A) a) (hsurj : ∀ A, Function.Surjective (q.app A))
    (hker : ∀ A (x : Φ.obj A), q.app A x = 0 → ∃ y, a • y = x) :
    (ShortComplex.mk _ _ hq).ShortExact := by
  have hf (A : C) : ⇑((Φ.smulEnd a).asHom.app A) = fun x : Φ.obj A ↦ a • x :=
    funext (Φ.smulEnd_asHom_app_apply a A)
  refine ShortComplex.shortExact_of_forall_function_exact (fun A ↦ ?_) (fun A x ↦ ?_) hsurj
  · dsimp only
    rw [hf]
    exact ha A
  · refine ⟨fun hx ↦ ?_, ?_⟩
    · dsimp only
      rw [hf]
      exact hker A x hx
    · rintro ⟨y, rfl⟩
      exact congr($(congr_app hq A) y)

end TauCeti
