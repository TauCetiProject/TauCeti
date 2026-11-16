/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.QuadraticForm.Global.Classification
import TauCeti.NumberTheory.QuadraticForm.Global.HasseMinkowski.Representation

/-!
# The Hasse–Minkowski theorem for isometry and global classification

Two finite-dimensional quadratic forms over a number field `K` are globally isometric if and only
if they are locally isometric at every finite and every real place of `K`. Neither nondegeneracy
nor prior finite dimensionality of the second space is required.

Global isometry follows directly from the Hasse–Minkowski theorem for representation
(`QuadraticForm.isRepresentedBy_iff_locallyRepresents`): local equivalence at any finite place
transfers finite dimensionality to the second space and gives equality of dimensions, while local
equivalence supplies local representation, so the resulting injective global isometry is bijective.

Combining the isometry theorem with the local invariant classification
(`QuadraticForm.locallyEquivalent_iff_globalInvariants_eq`) shows that regular quadratic forms over
a number field are classified up to global isometry by their complete system of invariants: rank,
global discriminant, finite-place Hasse invariants, and real-place positive indices.

## Main results

* `QuadraticForm.equivalent_of_locallyEquivalent`: the **Hasse–Minkowski theorem for isometry**
  for arbitrary (possibly degenerate) quadratic forms over a number field, with the first space
  finite-dimensional.
* `QuadraticForm.equivalent_iff_locallyEquivalent`: global equivalence is equivalent to local
  equivalence at all finite and real places.
* `QuadraticForm.equivalent_iff_globalInvariants_eq`: two regular forms over a number field are
  globally isometric if and only if they have the same `GlobalFormInvariants`.
* `QuadraticForm.equivalent_iff_finrank_eq_and_discr_eq_and_finiteHasse_eq_and_realPositiveIndex_eq`
  gives the unpacked global-invariant classification criterion for regular forms over a number
  field.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, Springer (1963), Theorem 66:4.
* J.-P. Serre, *A Course in Arithmetic*, Springer (1973), Chapter IV, Theorem 9.
* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Graduate Studies in Mathematics 67,
  American Mathematical Society (2005), Chapter VI, Principle 3.1 and Theorem 3.7.
-/

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace TauCeti
open TauCeti.NumberField.QuadraticForm
open scoped TensorProduct

universe u v w

namespace QuadraticForm

variable {K : Type u} [Field K] [NumberField K]
variable {V : Type v} [AddCommGroup V] [Module K V]
variable {W : Type w} [AddCommGroup W] [Module K W]

/-- **The Hasse–Minkowski theorem for isometry.** Two quadratic forms over a number field, with the
first on a finite-dimensional space, are globally isometric whenever they are locally isometric at
every finite and every real place. Neither nondegeneracy nor prior finite dimensionality of `W` is
required. -/
theorem equivalent_of_locallyEquivalent [FiniteDimensional K V] {Q : _root_.QuadraticForm K V}
    {R : _root_.QuadraticForm K W} (hloc : Q.LocallyEquivalent R) :
    Q.Equivalent R := by
  have : FiniteDimensional K W := by
    let v₀ : HeightOneSpectrum (𝓞 K) := Classical.arbitrary _
    obtain ⟨e⟩ := ((locallyEquivalent_iff Q R).mp hloc).1 v₀
    have : FiniteDimensional (v₀.adicCompletion K) (v₀.adicCompletion K ⊗[K] W) :=
      Module.Finite.equiv e.toLinearEquiv
    have hlt := Module.rank_lt_aleph0 (v₀.adicCompletion K) (v₀.adicCompletion K ⊗[K] W)
    rw [Module.rank_baseChange] at hlt
    exact Module.rank_lt_aleph0_iff.mp (by simpa [Cardinal.lift_lt_aleph0] using hlt)
  exact ((Q.isRepresentedBy_iff_locallyRepresents R).mpr
    hloc.locallyRepresents).equivalent_of_finrank_eq hloc.finrank_eq

/-- **The Hasse–Minkowski theorem for isometry** as an equivalence: two quadratic forms over a
number field, with the first on a finite-dimensional space, are globally isometric if and only if
they are locally isometric at every finite and every real place. -/
theorem equivalent_iff_locallyEquivalent [FiniteDimensional K V] {Q : _root_.QuadraticForm K V}
    {R : _root_.QuadraticForm K W} :
    Q.Equivalent R ↔ Q.LocallyEquivalent R :=
  ⟨LocallyEquivalent.of_equivalent, equivalent_of_locallyEquivalent⟩

/-- **Global classification by invariants.** Two regular quadratic forms over a number field are
globally isometric if and only if they have the same system of local invariants. -/
theorem equivalent_iff_globalInvariants_eq [FiniteDimensional K V] [FiniteDimensional K W]
    {Q : _root_.QuadraticForm K V} {R : _root_.QuadraticForm K W}
    (hQ : Q.Nondegenerate) (hR : R.Nondegenerate) :
    Q.Equivalent R ↔ Q.globalInvariants hQ = R.globalInvariants hR :=
  equivalent_iff_locallyEquivalent.trans (locallyEquivalent_iff_globalInvariants_eq hQ hR)

/-- **Global classification by unpacked invariants.** Two regular quadratic forms over a number
field are globally isometric if and only if they have the same dimension, global discriminant,
finite-place Hasse invariants, and real-place positive indices. -/
theorem equivalent_iff_finrank_eq_and_discr_eq_and_finiteHasse_eq_and_realPositiveIndex_eq
    [FiniteDimensional K V] [FiniteDimensional K W]
    {Q : _root_.QuadraticForm K V} {R : _root_.QuadraticForm K W}
    (hQ : Q.Nondegenerate) (hR : R.Nondegenerate) :
    letI : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
    Q.Equivalent R ↔
      Module.finrank K V = Module.finrank K W ∧
      RegularFormClass.discr (formClass Q hQ) = RegularFormClass.discr (formClass R hR) ∧
      Q.finiteHasse hQ = R.finiteHasse hR ∧ Q.realPositiveIndex = R.realPositiveIndex := by
  let : Invertible (2 : K) := invertibleOfNonzero two_ne_zero
  rw [equivalent_iff_globalInvariants_eq hQ hR]
  refine ⟨fun h ↦ ⟨?_, ?_, ?_, ?_⟩, fun ⟨hrank, hdiscr, hhasse, hpos⟩ ↦
    GlobalFormInvariants.ext (by simpa using hrank) (by simpa [globalInvariants_discr] using hdiscr)
      (by simpa using hhasse) (by simpa using hpos)⟩
  · simpa using congrArg GlobalFormInvariants.rank h
  · simpa [globalInvariants_discr] using congrArg GlobalFormInvariants.discr h
  · simpa using congrArg GlobalFormInvariants.finiteHasse h
  · simpa using congrArg GlobalFormInvariants.realPositiveIndex h

end QuadraticForm
