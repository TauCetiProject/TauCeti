/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Basic

/-!
# Products of pseudouniformisers

In a commutative topological monoid with zero and continuous multiplication, a product of two
pseudouniformisers is a pseudouniformiser: a product of units is a unit, and a topologically
nilpotent element is power-bounded, so its product with a topologically nilpotent element is
topologically nilpotent. Hence a product over a nonempty finite family of pseudouniformisers is a
pseudouniformiser. No nonarchimedean hypothesis is needed.

This is how invariant pseudouniformisers are produced for a finite group acting continuously on
a Tate ring: the product of the translates of a pseudouniformiser is again one.

## Main results

* `TauCeti.Huber.IsPseudoUniformizer.mul`: a product of two pseudouniformisers.
* `TauCeti.Huber.IsPseudoUniformizer.prod`: a product over a nonempty finite family.
-/

public section

namespace TauCeti.Huber

variable {R : Type*} [CommMonoidWithZero R] [TopologicalSpace R] [ContinuousMul R]

/-- **A product of two pseudouniformisers is a pseudouniformiser.** -/
theorem IsPseudoUniformizer.mul {a b : R} (ha : IsPseudoUniformizer a)
    (hb : IsPseudoUniformizer b) : IsPseudoUniformizer (a * b) :=
  have ha' := IsPowerBounded.of_isTopologicallyNilpotent ha.isTopologicallyNilpotent
  isPseudoUniformizer_iff.mpr
    ⟨ha.isUnit.mul hb.isUnit, ha'.isTopologicallyNilpotent_mul hb.isTopologicallyNilpotent⟩

/-- **A product over a nonempty finite family of pseudouniformisers is a pseudouniformiser.**
The empty product `1` is not one unless the monoid is trivial. -/
theorem IsPseudoUniformizer.prod {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {f : ι → R}
    (hf : ∀ i ∈ s, IsPseudoUniformizer (f i)) : IsPseudoUniformizer (∏ i ∈ s, f i) :=
  Finset.prod_induction_nonempty f _ (fun _ _ ↦ IsPseudoUniformizer.mul) hs hf

end TauCeti.Huber
