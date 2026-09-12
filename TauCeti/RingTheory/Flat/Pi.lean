/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

import Mathlib.Algebra.DirectSum.Module
import TauCeti.RingTheory.Ideal.Operations

/-!
# A finite product of flat modules is flat, and when it is faithfully flat

Mathlib knows that an arbitrary direct sum of flat modules is flat (`Module.Flat.directSum`), but
`∀ i, M i` is not definitionally a direct sum, so nothing fires for a product. Over a finite index
the two agree, and this file records the resulting instance together with the criterion that
upgrades it to faithful flatness.

Mathlib defines `Module.FaithfullyFlat` as flatness plus `m • ⊤ ≠ ⊤` for every maximal ideal `m`,
so the criterion is about locating a single component that keeps `m` proper — the factorwise half
of that is `Ideal.smul_top_eq_top_of_pi`, a general ideal-action fact with no flatness or
finiteness in it, which lives in `TauCeti/RingTheory/Ideal/Operations.lean`: a product is
faithfully flat as soon as each factor is flat and **no maximal ideal expands in every factor at
once**. Individually the factors may all fail to be faithfully flat.

## Main results

* `Module.Flat.pi`: a finite product of flat modules is flat.
* `Module.FaithfullyFlat.pi_of_exists_submodule_ne_top`: a finite product of flat modules is
  faithfully flat as soon as every maximal ideal stays proper in *some* factor.
* `Module.FaithfullyFlat.pi_of_faithfullyFlat`: the special case of one distinguished faithfully
  flat factor.
* `Module.FaithfullyFlat.pi`: a finite *nonempty* product of faithfully flat modules.

## Implementation notes

`Module.FaithfullyFlat.pi` asks `[Nonempty ι]`, and that is not slack: for `ι` empty the product
is the trivial module, in which `m • ⊤ = ⊤ = ⊥` for every `m`, so it is faithfully flat over no
nonzero ring at all — while `∀ i, FaithfullyFlat R (M i)` holds vacuously. Dropping the hypothesis
would make the instance false. Flatness has no such caveat: the trivial module is flat.

The finiteness is not an artefact of the comparison used here: by Chase's theorem a ring is
coherent exactly when every product of flat modules is flat, so over a non-coherent ring the
statement fails outright for a large enough index. Nothing is lost over a noetherian base, but the
hypothesis cannot simply be dropped.
-/

public section

variable {R : Type*} {ι : Type*} {M : ι → Type*}

namespace Module

section Flat

variable [CommSemiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- **A finite product of flat modules is flat.** The finiteness is essential; see the module
docstring. -/
instance Flat.pi [Finite ι] [∀ i, Flat R (M i)] : Flat R (∀ i, M i) := by
  have := Fintype.ofFinite ι
  exact Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype R ι M).symm

end Flat

section FaithfullyFlat

variable [CommRing R] [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

/-- **A finite product of flat modules is faithfully flat as soon as no maximal ideal expands
every factor at once.** Each individual factor may fail to be faithfully flat; what is needed is
that the failures are not simultaneous. -/
theorem FaithfullyFlat.pi_of_exists_submodule_ne_top [Finite ι] [∀ i, Flat R (M i)]
    (h : ∀ m : Ideal R, m.IsMaximal → ∃ i, m • (⊤ : Submodule R (M i)) ≠ ⊤) :
    FaithfullyFlat R (∀ i, M i) where
  submodule_ne_top m hm htop := (h m hm).elim fun i hi ↦ hi (m.smul_top_eq_top_of_pi htop i)

/-- **One faithfully flat factor carries a finite product of flat modules.** This is the special
case of `FaithfullyFlat.pi_of_exists_submodule_ne_top` where one fixed index works for every
maximal ideal; when no single factor does, that criterion is the one to use. -/
theorem FaithfullyFlat.pi_of_faithfullyFlat [Finite ι] [∀ i, Flat R (M i)] (j : ι)
    [FaithfullyFlat R (M j)] : FaithfullyFlat R (∀ i, M i) :=
  FaithfullyFlat.pi_of_exists_submodule_ne_top fun _ hm ↦
    ⟨j, FaithfullyFlat.submodule_ne_top hm⟩

/-- A finite **nonempty** product of faithfully flat modules is faithfully flat. The emptiness
hypothesis is essential; see the module docstring. -/
instance FaithfullyFlat.pi [Nonempty ι] [Finite ι] [∀ i, FaithfullyFlat R (M i)] :
    FaithfullyFlat R (∀ i, M i) :=
  FaithfullyFlat.pi_of_faithfullyFlat (Classical.arbitrary ι)

end FaithfullyFlat

end Module

end
