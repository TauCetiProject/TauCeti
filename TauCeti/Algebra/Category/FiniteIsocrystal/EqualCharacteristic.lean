/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import TauCeti.Algebra.Category.FiniteIsocrystal.Splitting
public import TauCeti.RingTheory.LaurentSeries.DifferenceEquation.Frobenius

/-!
# Splitting extensions of equal-characteristic isocrystals

Every epimorphism of finite isocrystals over `k((X))` has a Frobenius-equivariant
section when `k` is algebraically closed and Frobenius fixes `X` and raises
each coefficient to `p^f` for `f > 0`. The identity on the target is fixed by
Frobenius conjugation. Surjectivity of the Lang map on linear maps into the
kernel gives a fixed lift of this identity, hence an equivariant section.
-/

public section

open CategoryTheory Function
open scoped LaurentSeries

namespace TauCeti.FiniteIsocrystal

variable {k E : Type*} [Field k] [CommRing E] [Algebra E k⸨X⸩]
  {p : ℕ} [Fact p.Prime] [CharP k p] [IsAlgClosed k] {f : ℕ}
  {σ : k⸨X⸩ ≃ₐ[E] k⸨X⸩} {D D' : FiniteIsocrystal σ}

/-- Every epimorphism of equal-characteristic finite isocrystals over an algebraically
closed residue field splits when Frobenius fixes `X` and raises each coefficient to
`p^f` for `f > 0`. In particular, every short exact sequence of such isocrystals splits. -/
theorem isSplitEpi_of_epi (hσ : σ.toRingEquiv = LaurentSeries.coefficientFrobenius p f)
    (hf : 0 < f) (g : D ⟶ D') [Epi g] : IsSplitEpi g := by
  apply isSplitEpi_of_surjective_sum_mul_iterate _ g
  intro s a ha
  simpa only [hσ] using
    LaurentSeries.surjective_sum_mul_coefficientFrobenius (p := p) hf a ha

/-- A short exact sequence of finite isocrystals over an algebraically closed residue field
splits for positive coefficient Frobenius. -/
noncomputable def splittingOfShortExact
    (hσ : σ.toRingEquiv = LaurentSeries.coefficientFrobenius p f)
    (hf : 0 < f) (S : ShortComplex (FiniteIsocrystal σ)) (hS : S.ShortExact) : S.Splitting := by
  letI := hS.epi_g
  letI := isSplitEpi_of_epi hσ hf S.g
  exact ShortComplex.Splitting.ofExactOfSection S hS.exact (section_ S.g)
    (IsSplitEpi.id _) hS.mono_f

end TauCeti.FiniteIsocrystal
