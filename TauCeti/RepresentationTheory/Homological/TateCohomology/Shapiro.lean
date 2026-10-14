/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
public import TauCeti.RepresentationTheory.Homological.TateCohomology.Periodic

/-!
# Shapiro's lemma for Tate cohomology

Let `G` be a finite group, `S` a subgroup of `G` and `A` a representation of `S`. This file
identifies the Tate cohomology of the coinduced representation `Coind_S^G A` with that of `A`:

`H-hat^n(G, Coind_S^G A) ≅ H-hat^n(S, A)`.

Mathlib's Shapiro lemma `groupCohomology.coindIso` gives this for ordinary cohomology, which is
Tate cohomology in positive degrees, so the isomorphism holds in every positive degree for every
finite group (`coindIsoPos`). When `G` is cyclic, so is `S`, and two-periodicity of Tate
cohomology (`Rep.FiniteCyclicGroup.periodicIso`) carries every degree to a positive one, on both
sides at once (`coindIso`).

This is how the Tate cohomology of a module whose summands are permuted transitively by `G` is
computed from the stabilizer of one summand: for instance the units of a semi-local algebra
`K_v ⊗[K] L` of a cyclic extension of number fields, coinduced from the decomposition group of one
place above `v`.

## Main definitions

* `TauCeti.TateCohomology.coindIsoPos`: `H-hat^n(G, Coind_S^G A) ≅ H-hat^n(S, A)` for `G` finite
  and every positive `n : ℕ`.
* `TauCeti.TateCohomology.coindIso`: `H-hat^n(G, Coind_S^G A) ≅ H-hat^n(S, A)` for `G` finite
  cyclic and every `n : ℤ`.

## References

* J. S. Milne, *Class Field Theory*, Chapter II, Proposition 1.11 (Shapiro's lemma) and §3
  (Tate cohomology), and Chapter VII, §2.
-/

public section
noncomputable section

universe u

open CategoryTheory Rep

namespace TauCeti.TateCohomology

variable {R G : Type u} [CommRing R] [Group G] [Fintype G] (S : Subgroup G) [Fintype S]
  (A : Rep R S)

/-- **Shapiro's lemma for Tate cohomology in positive degrees.** For a subgroup `S` of a finite
group `G` and a representation `A` of `S`, the Tate cohomology of the coinduced representation
`Coind_S^G A` is that of `A`, in every positive degree `n`. -/
def coindIsoPos (n : ℕ) [NeZero n] : tateCohomology (coind S.subtype A) n ≅ tateCohomology A n :=
  (_root_.TateCohomology.isoGroupCohomology n).app _ ≪≫ groupCohomology.coindIso A n ≪≫
    ((_root_.TateCohomology.isoGroupCohomology n).app A).symm

variable [IsCyclic G]

/-- Shapiro's isomorphism in a positive degree `m` congruent to `n` modulo two, transported to
degree `n` by two-periodicity on both sides. -/
private def coindIsoOfModEq (n : ℤ) (m : ℕ) [NeZero m] (h : n ≡ m [ZMOD 2]) :
    tateCohomology (coind S.subtype A) n ≅ tateCohomology A n :=
  Rep.FiniteCyclicGroup.periodicIso _ n m h ≪≫ coindIsoPos S A m ≪≫
    Rep.FiniteCyclicGroup.periodicIso A m n h.symm

/-- **Shapiro's lemma for Tate cohomology of a finite cyclic group.** For a subgroup `S` of a
finite cyclic group `G` and a representation `A` of `S`, the Tate cohomology of the coinduced
representation `Coind_S^G A` is that of `A`, in every degree `n : ℤ`. -/
def coindIso (n : ℤ) : tateCohomology (coind S.subtype A) n ≅ tateCohomology A n :=
  haveI : NeZero (n % 2 + 2).toNat := ⟨by omega⟩
  coindIsoOfModEq S A n (n % 2 + 2).toNat <| by
    unfold Int.ModEq
    omega

end TauCeti.TateCohomology
