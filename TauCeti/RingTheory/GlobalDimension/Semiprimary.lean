/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HopkinsLevitzki
public import TauCeti.Algebra.Category.ModuleCat.Quotient
public import TauCeti.RingTheory.GlobalDimension

/-!
# The global dimension of a semiprimary ring

A ring `A` is semiprimary when its Jacobson radical `J` is nilpotent and `A ⧸ J` is a semisimple
ring; Artinian rings, and in particular Artin algebras, are semiprimary. Auslander's theorem says
that the global dimension of such a ring is the projective dimension of the single module `A ⧸ J`.
The ring need not be Noetherian, and no finiteness is asked of the modules.

There are two steps. A module annihilated by a two-sided ideal `I` with `A ⧸ I` semisimple has
projective dimension at most that of `A ⧸ I` (`Module.IsTorsionBySet.hasProjectiveDimensionLT`).
Every module `M` over a semiprimary ring has the finite filtration `M ⊇ J • M ⊇ J² • M ⊇ ⋯ ⊇ 0`
whose layers are annihilated by `J` (`IsSemiprimaryRing.induction`), and projective dimension
bounds pass through extensions.

The quotient `A ⧸ J` lives in the universe of `A`; for modules in another universe `v` it is
replaced by `Shrink.{v} (A ⧸ J)`, as in `TauCeti.globalDimension_le_tfae`.

## Main results

* `ModuleCat.hasProjectiveDimensionLT_of_isSemiprimaryRing`: over a semiprimary ring, every module
  has projective dimension at most that of `A ⧸ J`.
* `TauCeti.globalDimension_eq_projectiveDimension_quotient_jacobson`: **Auslander's theorem**, the
  global dimension of a semiprimary ring is the projective dimension of `A ⧸ J`.

## References

* M. Auslander, *On the dimension of modules and algebras III. Global dimension*, Nagoya Math.
  J. 9 (1955), 67–77, Corollary 9 and Corollary 11 (b), p. 73.
-/

public section

universe v u

open CategoryTheory

variable {A : Type u} [Ring A] [Small.{v} A]

/-- Over a semiprimary ring `A`, with Jacobson radical `J`, every module has projective dimension
`< n` as soon as `A ⧸ J` does. The layers of the filtration `M ⊇ J • M ⊇ J² • M ⊇ ⋯ ⊇ 0` are
annihilated by `J`, and projective dimension bounds pass through extensions. -/
theorem ModuleCat.hasProjectiveDimensionLT_of_isSemiprimaryRing [IsSemiprimaryRing A]
    (M : ModuleCat.{v} A) (n : ℕ)
    [HasProjectiveDimensionLT (ModuleCat.of A (Shrink.{v} (A ⧸ Ring.jacobson A))) n] :
    HasProjectiveDimensionLT M n := by
  refine IsSemiprimaryRing.induction ℤ A M
    (P := fun N _ _ _ ↦ HasProjectiveDimensionLT (ModuleCat.of A N) n)
    (fun N _ _ _ _ _ hJ ↦ hJ.hasProjectiveDimensionLT (M := ModuleCat.of A N) n)
    (fun N _ _ _ _ hK hQ ↦ ?_)
  -- Extend along the short exact sequence `0 → J • N → N → N ⧸ J • N → 0`.
  exact (Ring.jacobson A • ⊤ : Submodule A N).shortExact_quotientShortComplex
    |>.hasProjectiveDimensionLT_X₂ n hK hQ

namespace TauCeti

/-- **Auslander's theorem.** The global dimension of a semiprimary ring `A`, for instance an
Artinian ring, is the projective dimension of `A ⧸ J`, where `J` is the Jacobson radical. Both
sides are `⊥` for the zero ring. Auslander, *On the dimension of modules and algebras III*,
Corollary 11 (b). -/
theorem globalDimension_eq_projectiveDimension_quotient_jacobson [IsSemiprimaryRing A] :
    globalDimension.{v} A =
      projectiveDimension (ModuleCat.of A (Shrink.{v} (A ⧸ Ring.jacobson A))) :=
  le_antisymm ((globalDimension_le_iff A _).mpr fun M ↦
      projectiveDimension_le_of_hasProjectiveDimensionLT fun n _ ↦
        M.hasProjectiveDimensionLT_of_isSemiprimaryRing n)
    (ModuleCat.projectiveDimension_le_globalDimension _)

end TauCeti
