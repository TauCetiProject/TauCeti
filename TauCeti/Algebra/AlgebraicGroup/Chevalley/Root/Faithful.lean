/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Subgroup
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Basic
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Scheme
import TauCeti.Data.Nat.Factorial.Prime
import TauCeti.LinearAlgebra.Matrix.IdealEntries
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Scalar faithfulness of Chevalley root operators

For every Chevalley datum `D` of every valid Dynkin type, each integral root operator
`kostantRootOperator` on `D.lattice` remains faithful under scalar multiplication after base change
to any commutative ring `A` — including nonreduced rings with nilpotents and rings of
characteristics two and three.

This discharges the operator-faithfulness hypothesis needed for ordered-product uniqueness in
`TauCeti.Algebra.AlgebraicGroup.Chevalley.OrderedProduct` and pointwise root-subgroup injectivity in
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Injective` for arbitrary weight lattices and
commutative value rings, without asserting a closed immersion of root subgroup schemes.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.smul_baseChange_kostantRootOperator_eq_zero_iff`: scalar
  faithfulness of every Chevalley root operator after base change to any commutative ring.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 17–20.
* M. Demazure and A. Grothendieck, *SGA 3*, Exp. XXII, §4.1.
-/

public section

open Multiplicative TensorProduct TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

attribute [local instance high] Algebra.toModule

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

private theorem not_forall_prime_dvd_toMatrix_kostantRootOperator
    (γ : Fin t.numRoots) {p : ℕ} (hp : p.Prime) :
    ¬ ∀ r s : Fin D.dim, (p : ℤ) ∣
      LinearMap.toMatrix D.basis D.basis
        (kostantRootOperator (t.chevalleySystem ht) (t.lieBasis ht).h D.representation D.lattice
          (kostantForm_chevalleySystem_smul_mem D.representation D.lattice
            D.representation_mem_lattice D.isNilpotent_representation_rootGenerator) γ) r s := by
  classical
  intro hdvd
  let : Fact p.Prime := ⟨hp⟩
  let hAll := kostantForm_chevalleySystem_smul_mem D.representation D.lattice
    D.representation_mem_lattice D.isNilpotent_representation_rootGenerator
  let eγ := D.representation (_root_.UniversalEnvelopingAlgebra.ι ℚ (t.chevalleySystem ht γ))
  have hdiv (k : ℕ) (v : D.carrier) (hv : v ∈ D.lattice) :
      Associative.dividedPower k eγ • v ∈ D.lattice :=
    dividedPower_apply_mem_of_kostantForm_apply_mem
      (t.chevalleySystem ht) (t.lieBasis ht).h D.representation hAll γ k hv
  let Dop (k : ℕ) : Module.End ℤ D.lattice := integralDividedPower eγ D.lattice k (hdiv k)
  let Dmat (k : ℕ) : Matrix (Fin D.dim) (Fin D.dim) ℤ := LinearMap.toMatrix D.basis D.basis (Dop k)
  have hpow (k : ℕ) : k.factorial • Dmat k = Dmat 1 ^ k := by
    dsimp only [Dmat, Dop]
    rw [← map_nsmul, ← integralDividedPower_one_pow eγ D.lattice hdiv k, LinearMap.toMatrix_pow]
  have hdvd1 (i j : Fin D.dim) : (p : ℤ) ∣ Dmat 1 i j := by
    simpa only [Dmat, Dop, kostantRootOperator_def] using hdvd i j
  -- Entrywise divisibility of `Dmat 1` by `p` puts `Dmat 1 ^ k = k! • Dmat k` in `(p)^k`.
  have hDop_dvd {k : ℕ} (hk : k ≠ 0) (r s : Fin D.dim) : (p : ℤ) ∣ Dmat k r s := by
    have hmem := Matrix.pow_apply_mem_pow
      (fun i j => Ideal.mem_span_singleton.mpr (hdvd1 i j)) k r s
    rw [← hpow k, Ideal.span_singleton_pow, Ideal.mem_span_singleton, Matrix.smul_apply,
      nsmul_eq_mul] at hmem
    exact hp.intCast_dvd_of_pow_dvd_factorial_mul hk hmem
  -- Consequently `x_γ(1) = 1` over `ZMod p`, contradicting `rootSubgroupPoints_ofAdd_one_ne_one`.
  apply D.rootSubgroupPoints_ofAdd_one_ne_one (ZMod p) γ
  refine Subtype.ext (Units.ext ?_)
  let q := (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := ZMod p)).symm (ofAdd 1)
  have hq : AdditiveGroup.gaPointsMulEquiv q = ofAdd (1 : ZMod p) := MulEquiv.apply_symm_apply _ _
  rw [D.coe_rootSubgroupPoints, ← hq,
    ← TauCeti.DynkinType.kostantRootSubgroupMatrix_eq_matrix_chevalleyRootSubgroup
      D.representation D.lattice D.representation_mem_lattice
      D.isNilpotent_representation_rootGenerator D.basis γ (ZMod p) q,
    kostantRootSubgroupMatrix_eq_sum (t.chevalleySystem ht) (t.lieBasis ht).h
      D.representation D.lattice hAll γ
      (isNilpotent_apply_ι_chevalleySystem D.representation
        D.isNilpotent_representation_rootGenerator γ) D.basis (nilpotencyClass eγ + 1) Dmat
      (Nat.le_succ _) (fun k _ s => by simp [Dmat, Dop, eγ, LinearMap.toMatrix_apply]),
    hq, toAdd_ofAdd, Finset.sum_range_succ']
  have hD0 : Dmat 0 = 1 := by simp [Dmat, Dop, integralDividedPower_zero, LinearMap.toMatrix_one]
  have hsum0 : (∑ k ∈ Finset.range (nilpotencyClass eγ), (1 : ZMod p) ^ (k + 1) •
      (Dmat (k + 1)).map (Int.cast : ℤ → ZMod p)) = 0 :=
    Finset.sum_eq_zero fun k _ => Matrix.ext fun r s => by
      simpa only [one_pow, one_smul, Matrix.map_apply, Matrix.zero_apply,
        ZMod.intCast_zmod_eq_zero_iff_dvd] using hDop_dvd (Nat.succ_ne_zero k) r s
  simp only [Subgroup.coe_one, Units.val_one, pow_zero, one_smul, hD0,
    Matrix.map_one Int.cast Int.cast_zero Int.cast_one, hsum0, zero_add]

/-- Every all-root operator on the lattice of a Chevalley datum remains faithful under scalar
multiplication after base change to an arbitrary commutative ring, including nonreduced rings and
rings of characteristics two and three. -/
theorem smul_baseChange_kostantRootOperator_eq_zero_iff
    (γ : Fin t.numRoots) (A : Type v) [CommRing A] (c : A) :
    c • (kostantRootOperator (t.chevalleySystem ht) (t.lieBasis ht).h D.representation D.lattice
      (kostantForm_chevalleySystem_smul_mem D.representation D.lattice
        D.representation_mem_lattice D.isNilpotent_representation_rootGenerator) γ).baseChange A =
      0 ↔ c = 0 := by
  refine ⟨fun hc => ?_, fun hc => hc ▸ zero_smul _ _⟩
  let X := kostantRootOperator (t.chevalleySystem ht) (t.lieBasis ht).h D.representation D.lattice
    (kostantForm_chevalleySystem_smul_mem D.representation D.lattice
      D.representation_mem_lattice D.isNilpotent_representation_rootGenerator) γ
  let f : Fin D.dim × Fin D.dim → ℤ := fun ij => LinearMap.toMatrix D.basis D.basis X ij.fst ij.snd
  let I : Ideal ℤ := Ideal.span (Set.range f)
  have h1 : (1 : ℤ) ∈ I := by
    let d : ℤ := Submodule.IsPrincipal.generator I
    have hd_unit : IsUnit d := by
      rw [Int.isUnit_iff_natAbs_eq]
      by_contra hne1
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne1
      apply D.not_forall_prime_dvd_toMatrix_kostantRootOperator γ hp
      intro r s
      have hf_mem : f (r, s) ∈ Ideal.span {d} := by
        rw [Ideal.span_singleton_generator I]
        exact Ideal.subset_span ⟨(r, s), rfl⟩
      exact dvd_trans (Int.ofNat_dvd_left.mpr hpd) (Ideal.mem_span_singleton.mp hf_mem)
    rw [← Ideal.span_singleton_generator I, Ideal.mem_span_singleton]
    exact hd_unit.dvd
  obtain ⟨w, hw⟩ := (Ideal.mem_span_range_iff_exists_fun).mp h1
  have hmat := congrArg (LinearMap.toMatrix (D.basis.baseChange A) (D.basis.baseChange A)) hc
  rw [map_smul, Module.Basis.toMatrix_baseChange_baseChange, map_zero] at hmat
  have hcf (ij : Fin D.dim × Fin D.dim) : c * (f ij : A) = 0 := by
    have hij := congrFun (congrFun hmat ij.fst) ij.snd
    simpa only [Matrix.smul_apply, Matrix.map_apply, algebraMap_int_eq, Int.coe_castRingHom,
      smul_eq_mul, Matrix.zero_apply, f] using hij
  have hwA : ∑ ij : Fin D.dim × Fin D.dim, (w ij : A) * (f ij : A) = 1 := by
    simpa only [Int.cast_sum, Int.cast_mul, Int.cast_one, smul_eq_mul] using
      congrArg (Int.cast : ℤ → A) hw
  calc
    c = c * 1 := (mul_one c).symm
    _ = c * ∑ ij : Fin D.dim × Fin D.dim, (w ij : A) * (f ij : A) := by rw [hwA]
    _ = ∑ ij : Fin D.dim × Fin D.dim, (w ij : A) * (c * (f ij : A)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    _ = 0 := Finset.sum_eq_zero fun ij _ => by rw [hcf ij, mul_zero]

end TauCeti.DynkinType.ChevalleyDatum
