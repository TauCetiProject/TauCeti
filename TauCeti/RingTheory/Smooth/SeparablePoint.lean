/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Smooth algebras over a field have points with separable residue field

Let `A` be a nonzero smooth algebra over a field `k`. Then `A` has a maximal ideal `m` whose
residue field `A ⧸ m` is a finite separable extension of `k`. Geometrically, a nonempty smooth
scheme over `k` has a closed point with finite separable residue field, so it acquires a rational
point over a finite separable extension of `k`. This supplies rational points after a finite
separable extension of a field that need not be perfect, such as the fraction field of a discrete
valuation ring.

When `k` is finite, `k` is perfect and every maximal ideal works: its residue field is finite over
`k` by the Nullstellensatz. When `k` is infinite, `A` is étale over a polynomial ring
`k[X₁, …, Xₙ]` after inverting an element. The image of an étale morphism is open, and a nonempty
open subset of affine space over an infinite field contains a `k`-rational point `x`. The residue
field extensions of an étale algebra are separable, so a prime lying over `x` has residue field
separable over `κ(x) = k`.

## Main results

* `Algebra.Etale.exists_isPrime_isSeparable_residueField`: a nonzero étale algebra over a
  polynomial ring over an infinite field `k` has a prime ideal whose residue field is separable
  over `k`.
* `Algebra.Smooth.exists_isMaximal_isSeparable`: a nonzero smooth algebra over a field `k` has a
  maximal ideal whose residue field is a finite separable extension of `k`.

## References

* [The Stacks Project, Tag 056U](https://stacks.math.columbia.edu/tag/056U): the closed points
  of a smooth scheme over a field with separable residue field are dense.
-/

public section

open MvPolynomial

namespace Algebra

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

/-- A nonzero smooth algebra over a field `k` has a maximal ideal whose residue field is a finite
separable extension of `k`. -/
theorem Smooth.exists_isMaximal_isSeparable (k A : Type*) [Field k] [CommRing A] [Nontrivial A]
    [Algebra k A] [Algebra.Smooth k A] :
    ∃ m : Ideal A, m.IsMaximal ∧ Module.Finite k (A ⧸ m) ∧ Algebra.IsSeparable k (A ⧸ m) := by
  obtain ⟨p, hp⟩ := Ideal.exists_maximal A
  cases finite_or_infinite k
  · -- A finite field is perfect, and the residue field of any maximal ideal is finite over it.
    let := Ideal.Quotient.field p
    have : Module.Finite k (A ⧸ p) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ p)
    exact ⟨p, hp, this, Algebra.IsAlgebraic.isSeparable_of_perfectField⟩
  -- After inverting some `f`, the algebra is étale over a polynomial ring.
  obtain ⟨f, hfp, n, _, _, _⟩ := IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (p := p)
  have : Nontrivial (Localization.Away f) := by
    have : (p.map (algebraMap A (Localization.Away f))).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint (.powers f) _ p hp.isPrime
        ((Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hfp)
    exact ⟨0, 1, fun h ↦ this.ne_top ((Ideal.eq_top_iff_one _).mpr (h ▸ zero_mem _))⟩
  obtain ⟨q, _, _⟩ := Etale.exists_isPrime_isSeparable_residueField (k := k) (σ := Fin n)
    (B := Localization.Away f)
  -- The quotient of `A` by the kernel of `A → κ(q)` embeds into the separable extension `κ(q)`.
  let φ : A →ₐ[k] q.ResidueField := IsScalarTower.toAlgHom k A q.ResidueField
  have hφ : Function.Injective (Ideal.kerLiftAlg φ) := Ideal.kerLiftAlg_injective φ
  have hsep : Algebra.IsSeparable k (A ⧸ RingHom.ker φ) :=
    ⟨fun x ↦ (isSeparable_map_iff _ hφ).mp (Algebra.IsSeparable.isSeparable k _)⟩
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hfield : IsField (A ⧸ RingHom.ker φ) :=
    (Algebra.IsIntegral.isField_iff_isField (algebraMap k _).injective).mp (Field.toIsField k)
  exact ⟨_, Ideal.Quotient.maximal_of_isField _ hfield, Algebra.IsIntegral.finite, hsep⟩

end Algebra
