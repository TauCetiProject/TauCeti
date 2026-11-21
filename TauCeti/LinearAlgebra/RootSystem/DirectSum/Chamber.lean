/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.DirectSum.Internal
public import TauCeti.LinearAlgebra.RootSystem.Chamber

/-!
# Regular weights and dominant chambers on direct sums of root pairings

Regularity of weights and membership in the closed and open dominant chambers decompose
coordinatewise for finite external direct sums (`RootPairing.pi P`) and along
`TauCeti.internalProjection` for finite internal direct sums
(`RootPairing.internalDirectSum hEi hEt P`).

## Main results

* `RootPairing.isRegularWeight_pi_iff`, `RootPairing.mem_dominantChamber_pi_iff`,
  `RootPairing.mem_openDominantChamber_pi_iff`: coordinatewise decompositions for
  `RootPairing.pi P`.
* `RootPairing.isRegularWeight_internalDirectSum_iff`,
  `RootPairing.mem_dominantChamber_internalDirectSum_iff`,
  `RootPairing.mem_openDominantChamber_internalDirectSum_iff`: decompositions along
  `TauCeti.internalProjection` for `RootPairing.internalDirectSum hEi hEt P`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4-6*, Ch. VI §1, no. 2.
-/

public section

open TauCeti

namespace RootPairing

section External

variable {κ R : Type*} [Fintype κ] [DecidableEq κ] [CommRing R] [NeZero (2 : R)]
  {ι M N : κ → Type*}
  [∀ c, AddCommGroup (M c)] [∀ c, Module R (M c)]
  [∀ c, AddCommGroup (N c)] [∀ c, Module R (N c)]
  {P : ∀ c, RootPairing (ι c) R (M c) (N c)}

/-- A weight of a finite direct sum is regular iff every coordinate is regular. -/
theorem isRegularWeight_pi_iff (x : ∀ c, M c) :
    (pi P).IsRegularWeight x ↔ ∀ c, (P c).IsRegularWeight (x c) := by
  simp [isRegularWeight_iff, Sigma.forall]

/-- **The closed dominant chamber of a finite direct sum decomposes coordinatewise.** -/
theorem mem_dominantChamber_pi_iff [Preorder R] (b : ∀ c, (P c).Base) (x : ∀ c, M c) :
    x ∈ (pi P).dominantChamber (Base.pi b) ↔ ∀ c, x c ∈ (P c).dominantChamber (b c) := by
  simp [mem_dominantChamber, Sigma.forall]

/-- **The open dominant chamber of a finite direct sum decomposes coordinatewise.** -/
theorem mem_openDominantChamber_pi_iff [Preorder R] (b : ∀ c, (P c).Base) (x : ∀ c, M c) :
    x ∈ (pi P).openDominantChamber (Base.pi b) ↔ ∀ c, x c ∈ (P c).openDominantChamber (b c) := by
  simp [mem_openDominantChamber, Sigma.forall]

end External

section Internal

variable {κ R M : Type*} [Finite κ] [CommRing R] [NeZero (2 : R)]
  [AddCommGroup M] [Module R M]
  {E : κ → Submodule R M} {hEi : iSupIndep E} {hEt : ⨆ c, E c = ⊤}
  {ι N : κ → Type*} [∀ c, AddCommGroup (N c)] [∀ c, Module R (N c)]
  {P : ∀ c, RootPairing (ι c) R (E c) (N c)}

/-- A weight of an internal direct sum is regular iff every projection is regular. -/
theorem isRegularWeight_internalDirectSum_iff (x : M) :
    (internalDirectSum hEi hEt P).IsRegularWeight x ↔
      ∀ c, (P c).IsRegularWeight (internalProjection hEi hEt c x) := by
  simp [isRegularWeight_iff, Sigma.forall]

/-- **The closed dominant chamber of an internal direct sum decomposes along
`TauCeti.internalProjection`.** -/
theorem mem_dominantChamber_internalDirectSum_iff [Preorder R] (b : ∀ c, (P c).Base) (x : M) :
    x ∈ (internalDirectSum hEi hEt P).dominantChamber (Base.internalDirectSum hEi hEt b) ↔
      ∀ c, internalProjection hEi hEt c x ∈ (P c).dominantChamber (b c) := by
  simp [mem_dominantChamber, Sigma.forall]

/-- **The open dominant chamber of an internal direct sum decomposes along
`TauCeti.internalProjection`.** -/
theorem mem_openDominantChamber_internalDirectSum_iff [Preorder R] (b : ∀ c, (P c).Base) (x : M) :
    x ∈ (internalDirectSum hEi hEt P).openDominantChamber (Base.internalDirectSum hEi hEt b) ↔
      ∀ c, internalProjection hEi hEt c x ∈ (P c).openDominantChamber (b c) := by
  simp [mem_openDominantChamber, Sigma.forall]

end Internal

end RootPairing
