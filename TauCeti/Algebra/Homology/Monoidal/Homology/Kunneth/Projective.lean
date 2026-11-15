/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import TauCeti.Algebra.Homology.Monoidal.Homology.Kunneth.Basic

/-!
# The Künneth theorem for a factor with projective homology

Let `K` be a chain complex of projective modules over a commutative ring `R`, indexed by `ℕ`,
whose homology modules are projective, and let `L` be any chain complex of `R`-modules indexed by
`ℕ`.  Then the Künneth map

`⨁_{p + q = n} Hₚ(K) ⊗ H_q(L) ⟶ Hₙ(K ⊗ L)`

is an isomorphism (`HomologicalComplex.isIso_homologyKunneth_of_projective`).  No condition is
imposed on `L` or on `R`.

The cycles of `K` split off its terms and its homology splits off its cycles
(`ChainComplex.isSplitMono_iCycles_of_projective_homology`), so `K` is homotopy equivalent to a
complex with zero differentials whose terms are its homology modules
(`HomologicalComplex.exists_homotopyEquiv_d_eq_zero`).  These are projective, hence flat, so the
Künneth theorem for a flat factor with zero differentials
(`HomologicalComplex.isIso_homologyKunneth_of_d_eq_zero_of_flat`) applies, and the Künneth map is
invariant under homotopy equivalences
(`HomologicalComplex.isIso_homologyKunneth_iff_of_homotopyEquiv`).

A typical `K` is the relative chain complex of a topological pair with free relative homology, such
as a cube modulo its boundary; the theorem then computes the relative homology of the product of
the pair with an arbitrary space.

## References

* C. Weibel, *An Introduction to Homological Algebra*, Section 3.6, the Künneth formula.
-/

public section

noncomputable section

open CategoryTheory

namespace HomologicalComplex

universe u

variable {R : Type u} [CommRing R] (K L : ChainComplex (ModuleCat.{u} R) ℕ)
  [∀ p, Module.Projective R (K.X p)] [∀ p, Module.Projective R (K.homology p)]

/-- **The Künneth theorem when one factor is projective with projective homology.**  If `K` is a
complex of projective modules indexed by `ℕ` whose homology modules are projective, then for every
complex `L` the Künneth map `⨁_{p + q = n} Hₚ(K) ⊗ H_q(L) ⟶ Hₙ(K ⊗ L)` is an isomorphism. -/
theorem isIso_homologyKunneth_of_projective (n : ℕ) : IsIso (homologyKunneth K L n) := by
  have (p : ℕ) : Projective (K.homology p) := ModuleCat.projective_of_categoryTheory_projective _
  have (p : ℕ) : Projective (K.X p) := ModuleCat.projective_of_categoryTheory_projective _
  have := K.isSplitMono_iCycles_of_projective_homology
  -- `K` is homotopy equivalent to a complex with zero differentials, whose terms are the
  -- homology modules of `K` and so are flat
  obtain ⟨K', hK', ⟨e⟩⟩ := K.exists_homotopyEquiv_d_eq_zero
  have (p : ℕ) : Module.Flat R (K'.X p) :=
    have : Module.Projective R (K'.X p) := .of_equiv ((e.toHomologyIso p).trans
      (K'.XIsoHomologyOfDEqZero p (hK' _ _) (hK' _ _)).symm).toLinearEquiv
    inferInstance
  rw [isIso_homologyKunneth_iff_of_homotopyEquiv n e (HomotopyEquiv.refl L)]
  exact isIso_homologyKunneth_of_d_eq_zero_of_flat K' L hK' n

end HomologicalComplex
