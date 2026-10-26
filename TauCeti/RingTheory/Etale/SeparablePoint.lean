/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Étale algebras over affine space have points with separable residue field

Let `B` be a nonzero étale algebra over a polynomial ring `k[X₁, …, Xₙ]` over an infinite field
`k`. Then `B` has a prime ideal whose residue field is separable over `k`. The image of `Spec B`
in affine space is a nonempty open subset, so it contains a `k`-rational point `x`. The residue
field extensions of an étale algebra are separable, so a prime lying over `x` has residue field
separable over `κ(x) = k`.

## Main results

* `TauCeti.Algebra.Etale.exists_isPrime_isSeparable_residueField`: a nonzero étale algebra over
  a polynomial ring over an infinite field `k` has a prime ideal whose residue field is separable
  over `k`.

## References

* [The Stacks Project, Tag 056U](https://stacks.math.columbia.edu/tag/056U): the closed points
  of a smooth scheme over a field with separable residue field are dense.
-/

public section

open MvPolynomial

namespace TauCeti.Algebra

variable {k : Type*} [Field k]

/-- A nonzero étale algebra over a polynomial ring over an infinite field `k` has a prime ideal
whose residue field is separable over `k`. -/
theorem Etale.exists_isPrime_isSeparable_residueField [Infinite k] {σ : Type*} {B : Type*}
    [CommRing B] [Nontrivial B] [Algebra k B] [Algebra (MvPolynomial σ k) B]
    [IsScalarTower k (MvPolynomial σ k) B] [Algebra.Etale (MvPolynomial σ k) B] :
    ∃ (q : Ideal B) (_ : q.IsPrime), Algebra.IsSeparable k q.ResidueField := by
  -- The image of `Spec B` in affine space is a nonempty open subset, so it contains a nonempty
  -- basic open `D(h)`.
  have hopen : IsOpen (Set.range (PrimeSpectrum.comap (algebraMap (MvPolynomial σ k) B))) := by
    simpa using PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation _ isOpen_univ
  obtain ⟨Q⟩ : Nonempty (PrimeSpectrum B) := inferInstance
  obtain ⟨_, ⟨h, rfl⟩, hQ, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (Set.mem_range_self Q) hopen
  have h0 : h ≠ 0 := by
    rintro rfl
    simp at hQ
  -- Over an infinite field, the nonzero polynomial `h` does not vanish at some `k`-point `x`.
  obtain ⟨x, hx⟩ : ∃ x, eval x h ≠ 0 := by
    by_contra! H
    exact h0 (MvPolynomial.funext fun x ↦ by simpa using H x)
  have hsurj : Function.Surjective (eval (R := k) x) := fun a ↦ ⟨C a, eval_C a⟩
  let m := RingHom.ker (eval (R := k) x)
  have : m.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hsurj
  obtain ⟨q, hq⟩ := @hsub ⟨m, inferInstance⟩ hx
  have : q.asIdeal.LiesOver m := ⟨congrArg PrimeSpectrum.asIdeal hq.symm⟩
  refine ⟨q.asIdeal, inferInstance, ?_⟩
  -- The residue field of `x` is `k`.
  have hκ : Function.Bijective (algebraMap k m.ResidueField) := by
    refine ⟨(algebraMap k m.ResidueField).injective, fun y ↦ ?_⟩
    obtain ⟨g, rfl⟩ := m.algebraMap_residueField_surjective y
    refine ⟨eval x g, ?_⟩
    rw [IsScalarTower.algebraMap_apply k (MvPolynomial σ k), algebraMap_eq,
      ← sub_eq_zero, ← map_sub, Ideal.algebraMap_residueField_eq_zero]
    simp [m]
  have : Algebra.IsSeparable k m.ResidueField :=
    AlgEquiv.Algebra.isSeparable (AlgEquiv.ofBijective (Algebra.ofId k _) hκ)
  -- The residue field extension `κ(q) / κ(x)` of the étale algebra is separable.
  let := Localization.AtPrime.algebraOfLiesOver m q.asIdeal
  have : IsScalarTower k m.ResidueField q.asIdeal.ResidueField := by
    refine .of_algebraMap_eq fun a ↦ ?_
    rw [IsScalarTower.algebraMap_apply k (MvPolynomial σ k) m.ResidueField,
      IsScalarTower.algebraMap_apply k (MvPolynomial σ k) q.asIdeal.ResidueField,
      IsScalarTower.algebraMap_apply (MvPolynomial σ k) m.ResidueField q.asIdeal.ResidueField]
  exact Algebra.IsSeparable.trans k m.ResidueField _

end TauCeti.Algebra
