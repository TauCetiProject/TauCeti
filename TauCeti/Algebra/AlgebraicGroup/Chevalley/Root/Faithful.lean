/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Subgroup
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Basic
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Scheme
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Scalar faithfulness of Chevalley root operators

For every Chevalley datum `D` of every valid Dynkin type, each integral root operator
`kostantRootOperator` on `D.lattice` remains faithful under scalar multiplication after base change
to any commutative ring `A` — including nonreduced rings with nilpotents and rings of
characteristics two and three.

This discharges the operator-faithfulness hypothesis needed for ordered-product uniqueness in
`TauCeti.Algebra.AlgebraicGroup.Chevalley.OrderedProduct` and pointwise root-subgroup injectivity in
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Injective`, removing full-weight and characteristic
restrictions without asserting a closed immersion of root subgroup schemes.

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

private theorem integralDividedPower_one_pow {V : Type*} [AddCommGroup V] [Module ℚ V]
    (x : Module.End ℚ V) (M : AddSubgroup V)
    (hdiv : ∀ k : ℕ, ∀ v ∈ M, Associative.dividedPower k x • v ∈ M) (k : ℕ) :
    integralDividedPower x M 1 (hdiv 1) ^ k =
      k.factorial • integralDividedPower x M k (hdiv k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ih, mul_smul_comm,
      mul_integralDividedPower x M 1 k (hdiv 1) (hdiv k) (hdiv (1 + k)), smul_smul]
    have hchoose : k.factorial * Nat.choose (1 + k) 1 = (k + 1).factorial := by
      rw [Nat.add_comm 1 k, Nat.choose_one_right, Nat.factorial_succ, mul_comm]
    rw [hchoose]
    congr 2
    omega

private theorem prime_dvd_of_factorial_mul_eq_pow_mul {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0)
    {a b : ℤ} (hab : (k.factorial : ℤ) * a = (p : ℤ) ^ k * b) :
    (p : ℤ) ∣ a := by
  let : Fact p.Prime := ⟨hp⟩
  by_contra hpa
  have hpa_nat : ¬ p ∣ a.natAbs := fun h => hpa (Int.ofNat_dvd_left.mpr h)
  have hab_nat : k.factorial * a.natAbs = p ^ k * b.natAbs := by
    simpa only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] using
      congrArg Int.natAbs hab
  have hcop : (p ^ k).Coprime a.natAbs := (hp.coprime_iff_not_dvd.mpr hpa_nat).pow_left k
  have hdvd_fac : p ^ k ∣ k.factorial := hcop.dvd_of_dvd_mul_right ⟨b.natAbs, hab_nat⟩
  have hle : k ≤ multiplicity p k.factorial :=
    (Nat.pow_dvd_iff_le_multiplicity hp.ne_one (Nat.factorial_ne_zero k)).mp hdvd_fac
  exact absurd hle (not_le_of_gt (multiplicity_factorial_lt_of_ne_zero p hk))

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
  let hnil := isNilpotent_apply_ι_chevalleySystem D.representation
    D.isNilpotent_representation_rootGenerator
  let eγ := D.representation (_root_.UniversalEnvelopingAlgebra.ι ℚ (t.chevalleySystem ht γ))
  have hdiv_mem (k : ℕ) : ∀ v ∈ D.lattice, Associative.dividedPower k eγ • v ∈ D.lattice :=
    fun _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem
      (t.chevalleySystem ht) (t.lieBasis ht).h D.representation hAll γ k hv
  let Dop : ℕ → Module.End ℤ D.lattice := fun k =>
    integralDividedPower eγ D.lattice k (hdiv_mem k)
  let Dmat : ℕ → Matrix (Fin D.dim) (Fin D.dim) ℤ :=
    fun k => LinearMap.toMatrix D.basis D.basis (Dop k)
  have hDop1 : Dop 1 = kostantRootOperator (t.chevalleySystem ht) (t.lieBasis ht).h
      D.representation D.lattice hAll γ := by
    rw [kostantRootOperator_def]
  -- Factor `Dmat 1 = p • M'` so `k! • Dmat k = p^k • (M' ^ k)` forces `p ∣ Dmat k r s` for `k ≥ 1`.
  let M' : Matrix (Fin D.dim) (Fin D.dim) ℤ := Matrix.of fun r s => Dmat 1 r s / (p : ℤ)
  have hM' : Dmat 1 = (p : ℤ) • M' := by
    ext r s
    simpa only [Dmat, M', Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] using
      (Int.mul_ediv_cancel' (hDop1 ▸ hdvd r s)).symm
  have hDop_dvd {k : ℕ} (hk : k ≠ 0) (r s : Fin D.dim) : (p : ℤ) ∣ Dmat k r s := by
    have hmat_eq : k.factorial • Dmat k = ((p : ℤ) ^ k) • (M' ^ k) := by
      dsimp only [Dmat, Dop]
      rw [← map_nsmul, ← integralDividedPower_one_pow eγ D.lattice hdiv_mem k,
        ← LinearMap.toMatrix_pow, show LinearMap.toMatrix D.basis D.basis (Dop 1) = (p : ℤ) • M'
          from hM', smul_pow]
    have hab : (k.factorial : ℤ) * Dmat k r s = (p : ℤ) ^ k * (M' ^ k) r s := by
      simpa only [Matrix.smul_apply, nsmul_eq_mul, smul_eq_mul] using
        congrFun (congrFun hmat_eq r) s
    exact prime_dvd_of_factorial_mul_eq_pow_mul hp hk hab
  -- Consequently `x_γ(1) = 1` over `ZMod p`, contradicting `rootSubgroupPoints_ofAdd_one_ne_one`.
  apply D.rootSubgroupPoints_ofAdd_one_ne_one (ZMod p) γ
  apply Subtype.ext
  apply Units.ext
  rw [D.coe_rootSubgroupPoints]
  let q := (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := ZMod p)).symm (ofAdd 1)
  have hq : AdditiveGroup.gaPointsMulEquiv q = ofAdd (1 : ZMod p) :=
    MulEquiv.apply_symm_apply _ _
  rw [← hq, ← TauCeti.DynkinType.kostantRootSubgroupMatrix_eq_matrix_chevalleyRootSubgroup
    D.representation D.lattice D.representation_mem_lattice
    D.isNilpotent_representation_rootGenerator D.basis γ (ZMod p) q]
  let N := nilpotencyClass eγ
  have haction (k : ℕ) (s : Fin D.dim) :
      Dop k (D.basis s) = ∑ r, Dmat k r s • D.basis r := by
    simp [Dmat, LinearMap.toMatrix_apply]
  rw [kostantRootSubgroupMatrix_eq_sum (t.chevalleySystem ht) (t.lieBasis ht).h
      D.representation D.lattice hAll γ (hnil γ) D.basis (N + 1) Dmat (Nat.le_succ _)
      (fun k _ s => haction k s),
    hq, toAdd_ofAdd, Finset.sum_range_succ']
  have hD0 : Dmat 0 = 1 := by simp [Dmat, Dop, integralDividedPower_zero, LinearMap.toMatrix_one]
  have hsum0 : (∑ k ∈ Finset.range N, (1 : ZMod p) ^ (k + 1) •
      (Dmat (k + 1)).map (Int.cast : ℤ → ZMod p)) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    ext r s
    simp only [one_pow, one_smul, Matrix.map_apply, Matrix.zero_apply,
      ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hDop_dvd (Nat.succ_ne_zero k) r s
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
