/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Even.BaseChange
public import TauCeti.RepresentationTheory.Spin.Polarization.Split.Even

/-!
# Base change of the even Clifford algebra of the standard split form

Let `R → S` be an algebra and `q = TauCeti.splitEvenForm R n` the standard split quadratic form
`(f, x) ↦ f x` on `(Rⁿ)* × Rⁿ`. The base change `TauCeti.splitEvenSpaceBaseChange` of the split
space carries `q` to its image in `S`, so `TauCeti.evenBaseChange` gives an `R`-algebra map
`ι m₁ ι m₂ ↦ ι m₁_S ι m₂_S` between the even Clifford algebras of `q` and of
`TauCeti.splitEvenForm S n`. No hypothesis on `2` is needed, unlike for Mathlib's
`CliffordAlgebra.ofBaseChange`.

## Main definitions

* `TauCeti.splitEvenEvenBaseChange`: the base change map
  `CliffordAlgebra.even (splitEvenForm R n) →ₐ[R] CliffordAlgebra.even (splitEvenForm S n)`.

## Main results

* `TauCeti.splitEvenEvenBaseChange_ι`: the base change map sends `ι m₁ ι m₂` to
  `ι m₁_S ι m₂_S`.
-/

public section

namespace TauCeti

open _root_.CliffordAlgebra

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (n : ℕ)

/-- The base change map `CliffordAlgebra.even (splitEvenForm R n) → CliffordAlgebra.even
(splitEvenForm S n)` along an algebra `R → S`, sending `ι m₁ ι m₂` to `ι m₁_S ι m₂_S`: the
instance of `evenBaseChange` at `splitEvenSpaceBaseChange`. -/
noncomputable def splitEvenEvenBaseChange :
    even (splitEvenForm R n) →ₐ[R] even (splitEvenForm S n) :=
  evenBaseChange (splitEvenSpaceBaseChange R S n) (splitEvenForm_splitEvenSpaceBaseChange R S n)

/-- The base change map sends `ι m₁ ι m₂` to `ι m₁_S ι m₂_S`. -/
@[simp]
theorem splitEvenEvenBaseChange_ι (m₁ m₂ : SplitEvenSpace R n) :
    splitEvenEvenBaseChange R S n ((even.ι _).bilin m₁ m₂) =
      (even.ι _).bilin (splitEvenSpaceBaseChange R S n m₁)
        (splitEvenSpaceBaseChange R S n m₂) :=
  evenBaseChange_ι _ _ m₁ m₂

end TauCeti
