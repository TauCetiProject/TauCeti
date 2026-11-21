/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Divisible
public import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.Algebra.Module.Injective

/-!
# Extending homomorphisms into rootable commutative groups

A commutative group `U` satisfying `[RootableBy U ℕ]` has an `ℕ`-divisible (hence `ℤ`-divisible)
additive counterpart `Additive U`, which is therefore injective as a `ℤ`-module by Baer's
criterion (`Module.Baer.of_divisible`). Consequently, any homomorphism `Multiplicative H →* U`
extends along any injective additive homomorphism `f : H →+ L`.

## Main results

* `RootableBy.exists_monoidHom_comp_toMultiplicative_eq`: extending a character
  `Multiplicative H →* U` along an injective `f : H →+ L` when `[RootableBy U ℕ]`.

## References

* W. Bruns and J. Gubeladze, *Polytopes, Rings, and K-Theory*, Chapter 2.
* S. Lang, *Algebra*, Chapter III (divisible abelian groups and injectivity).
-/

public section

namespace RootableBy

/-- Into any commutative group `U` that is `ℕ`-rootable (for instance `Kˣ` for an algebraically
closed field `K` via `TauCeti.IsAlgClosed.unitsRootableByNat`), every character
`Multiplicative H →* U` extends along any injective additive group homomorphism `f : H →+ L`. -/
theorem exists_monoidHom_comp_toMultiplicative_eq {H L U : Type*} [AddCommGroup H]
    [AddCommGroup L] [CommGroup U] [RootableBy U ℕ] {f : H →+ L} (hf : Function.Injective f)
    (ψ : Multiplicative H →* U) :
    ∃ χ : Multiplicative L →* U, χ.comp f.toMultiplicative = ψ := by
  let : DivisibleBy (Additive U) ℕ :=
    divisibleByOfSMulRightSurj (Additive U) ℕ fun {n} hn u ↦ by
      obtain ⟨b, hb⟩ := RootableBy.surjective_pow U ℕ hn (Additive.toMul u)
      exact ⟨Additive.ofMul b, by simpa using congrArg Additive.ofMul hb⟩
  let : DivisibleBy (Additive U) ℤ := AddGroup.divisibleByIntOfDivisibleByNat (Additive U)
  obtain ⟨g, hg⟩ := (Module.Baer.of_divisible (Additive U)).extension_property_addMonoidHom
    f hf ψ.toAdditiveRight
  exact ⟨AddMonoidHom.toMultiplicativeLeft g, MonoidHom.ext fun x ↦ by
    simpa using congrArg Additive.toMul (DFunLike.congr_fun hg x.toAdd)⟩

end RootableBy
