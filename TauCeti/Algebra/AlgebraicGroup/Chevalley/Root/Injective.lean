/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Basic
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Scheme
import TauCeti.Algebra.Group.Hom.Rational
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.OrderedProduct
import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.WeightDegree
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Integral faithfulness of Chevalley root operators and root subgroups

For **every** Chevalley datum `D` — without assuming full weight lattice or simple lacing — and
over **every** commutative ring `A` — including nonreduced rings with nilpotents and rings of
bad characteristic — each integral root operator `kostantRootOperator` on `D.lattice` remains
faithful under scalar multiplication after base change to `A`, and every root subgroup homomorphism
`D.rootSubgroupPoints γ A` is injective.

Suppose a rational prime `p` divided every entry of the integer matrix of the first divided power
`X_γ = E_γ^{(1)}` in `D.basis`. Then `X_γ^k` would map `D.lattice` into `p^k • D.lattice` for all
`k ≥ 1`. Since `k! • E_γ^{(k)} = X_γ^k` and `multiplicity p (k!) < k` for every `k ≥ 1`, every
positive divided power `E_γ^{(k)}` would vanish modulo `p`, forcing
`D.rootSubgroupPoints γ (ZMod p) (ofAdd 1) = 1` and contradicting
`ChevalleyDatum.rootSubgroupPoints_ofAdd_one_ne_one`. Hence the matrix entries of `X_γ` generate
the unit ideal of `ℤ`, which gives scalar faithfulness over every commutative ring `A`. Combining
scalar faithfulness with the weight-graded matrix degree argument of
`list_prod_map_kostantRootSubgroupParam_inj` on each positive simple root and transporting along
Weyl reflections via `ChevalleyDatum.rootSubgroupPoints_injective_of_simple` proves injectivity of
every root subgroup over every commutative ring.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.smul_baseChange_kostantRootOperator_eq_zero_iff`: scalar
  faithfulness of every Chevalley root operator after base change to any commutative ring.
* `TauCeti.DynkinType.ChevalleyDatum.rootSubgroupPoints_injective`: `D.rootSubgroupPoints γ A` is
  injective over every commutative ring `A`.
* `TauCeti.DynkinType.ChevalleyDatum.rootSubgroupPoints_inj` and
  `TauCeti.DynkinType.ChevalleyDatum.rootSubgroupPoints_eq_one_iff`: `simp` characterizations of
  equality and triviality of root-subgroup points over any commutative ring.

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
  let hnil := isNilpotent_apply_ι_chevalleySystem D.representation
    D.isNilpotent_representation_rootGenerator
  let eγ := D.representation (_root_.UniversalEnvelopingAlgebra.ι ℚ (t.chevalleySystem ht γ))
  have hdiv_mem (k : ℕ) : ∀ v ∈ D.lattice, Associative.dividedPower k eγ • v ∈ D.lattice :=
    fun _ hv => dividedPower_apply_mem_of_kostantForm_apply_mem
      (t.chevalleySystem ht) (t.lieBasis ht).h D.representation hAll γ k hv
  let Dop : ℕ → Module.End ℤ D.lattice := fun k =>
    integralDividedPower eγ D.lattice k (hdiv_mem k)
  have hDop1 : Dop 1 = kostantRootOperator (t.chevalleySystem ht) (t.lieBasis ht).h
      D.representation D.lattice hAll γ := by
    rw [kostantRootOperator_def]
  have hpow_fac (k : ℕ) : Dop 1 ^ k = k.factorial • Dop k := by
    induction k with
    | zero => simp [Dop]
    | succ k ih =>
      rw [pow_succ', ih, mul_smul_comm]
      dsimp only [Dop]
      rw [mul_integralDividedPower eγ D.lattice 1 k (hdiv_mem 1) (hdiv_mem k) (hdiv_mem (1 + k)),
        smul_smul]
      have hchoose : k.factorial * Nat.choose (1 + k) 1 = (k + 1).factorial := by
        rw [Nat.add_comm 1 k, Nat.choose_one_right, Nat.factorial_succ, mul_comm]
      rw [hchoose]
      congr 2
      omega
  have hstep (m : D.lattice) : ∃ y : D.lattice, Dop 1 m = (p : ℤ) • y := by
    rw [hDop1]
    set X := kostantRootOperator (t.chevalleySystem ht) (t.lieBasis ht).h
      D.representation D.lattice hAll γ
    have hdiv (r : Fin D.dim) : (p : ℤ) ∣ D.basis.repr (X m) r := by
      let coord : D.lattice →ₗ[ℤ] ℤ :=
        (Finsupp.lapply r).comp (D.basis.repr.toLinearMap.comp X)
      have hcoord_eq : D.basis.repr (X m) r = ∑ s, D.basis.repr m s * coord (D.basis s) := by
        simpa only [coord, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
          Finsupp.lapply_apply, map_sum, map_zsmul, smul_eq_mul] using
          congrArg coord (D.basis.sum_repr m).symm
      rw [hcoord_eq]
      refine Finset.dvd_sum fun s _ => dvd_mul_of_dvd_right ?_ _
      simpa only [coord, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        Finsupp.lapply_apply, LinearMap.toMatrix_apply] using hdvd r s
    refine ⟨∑ r, (D.basis.repr (X m) r / (p : ℤ)) • D.basis r, ?_⟩
    rw [Finset.smul_sum]
    conv_lhs => rw [← D.basis.sum_repr (X m)]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [smul_smul, Int.mul_ediv_cancel' (hdiv r)]
  have hpow_dvd (k : ℕ) (m : D.lattice) :
      ∃ y : D.lattice, (Dop 1 ^ k) m = ((p : ℤ) ^ k) • y := by
    induction k with
    | zero => exact ⟨m, by simp⟩
    | succ k ih =>
      obtain ⟨y, hy⟩ := ih
      obtain ⟨z, hz⟩ := hstep y
      refine ⟨z, ?_⟩
      rw [pow_succ', mul_apply_eq_comp, hy, map_zsmul, hz, smul_smul, pow_succ]
  have hDop_dvd {k : ℕ} (hk : k ≠ 0) (r s : Fin D.dim) :
      (p : ℤ) ∣ LinearMap.toMatrix D.basis D.basis (Dop k) r s := by
    obtain ⟨y, hy⟩ := hpow_dvd k (D.basis s)
    have h1 : (k.factorial • Dop k) (D.basis s) = ((p : ℤ) ^ k) • y := by
      rw [← hpow_fac k]
      exact hy
    have hcoord : (k.factorial : ℤ) * D.basis.repr (Dop k (D.basis s)) r =
        (p : ℤ) ^ k * D.basis.repr y r := by
      rw [LinearMap.smul_apply] at h1
      simpa only [map_nsmul, map_zsmul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul,
        nsmul_eq_mul] using congrArg (fun x => D.basis.repr x r) h1
    set a := LinearMap.toMatrix D.basis D.basis (Dop k) r s
    have hab : (k.factorial : ℤ) * a = (p : ℤ) ^ k * D.basis.repr y r := by
      simpa only [a, LinearMap.toMatrix_apply] using hcoord
    by_contra hpa
    have hpa_nat : ¬ p ∣ a.natAbs := fun h => hpa (Int.ofNat_dvd_left.mpr h)
    have hab_nat : k.factorial * a.natAbs = p ^ k * (D.basis.repr y r).natAbs := by
      simpa only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] using
        congrArg Int.natAbs hab
    have hcop : (p ^ k).Coprime a.natAbs := (hp.coprime_iff_not_dvd.mpr hpa_nat).pow_left k
    have hdvd_fac : p ^ k ∣ k.factorial :=
      hcop.dvd_of_dvd_mul_right ⟨(D.basis.repr y r).natAbs, hab_nat⟩
    have hle : k ≤ multiplicity p k.factorial :=
      (Nat.pow_dvd_iff_le_multiplicity hp.ne_one (Nat.factorial_ne_zero k)).mp hdvd_fac
    exact absurd hle (not_le_of_gt (multiplicity_factorial_lt_of_ne_zero p hk))
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
  let Dmat : ℕ → Matrix (Fin D.dim) (Fin D.dim) ℤ :=
    fun k => LinearMap.toMatrix D.basis D.basis (Dop k)
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
  let f : Fin D.dim × Fin D.dim → ℤ := fun ij => LinearMap.toMatrix D.basis D.basis X ij.1 ij.2
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
    have hij := congrFun (congrFun hmat ij.1) ij.2
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

/-- Over every commutative ring, every root subgroup homomorphism of a Chevalley datum is
injective. No reducedness, characteristic, or full-weight hypothesis is required. -/
theorem rootSubgroupPoints_injective (γ : Fin t.numRoots) (A : Type v) [CommRing A] :
    Function.Injective (D.rootSubgroupPoints γ A) := by
  refine D.rootSubgroupPoints_injective_of_simple A (fun i => ?_) γ
  obtain ⟨n, degree, hn, hdegree⟩ := (t.weightDegree ht).exists_pos_nat_mul_eq_intCast
  have hpos : t.simpleIndex ht i ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) :=
    support_subset_posRoots _ _ (t.simpleIndex_mem_support i)
  have hposdegree : 0 < degree ((t.simplyConnectedRootDatum ht).root (t.simpleIndex ht i)) := by
    have h := mul_pos (Nat.cast_pos.mpr hn : (0 : ℚ) < n) (t.weightDegree_root_pos ht hpos)
    rw [hdegree] at h
    exact_mod_cast h
  let hAll := kostantForm_chevalleySystem_smul_mem D.representation D.lattice
    D.representation_mem_lattice D.isNilpotent_representation_rootGenerator
  intro a b hab
  have hnative := (list_prod_map_kostantRootSubgroupParam_inj
    (t.chevalleySystem ht) (t.lieBasis ht).h D.representation D.lattice hAll
    (isNilpotent_apply_ι_chevalleySystem D.representation
      D.isNilpotent_representation_rootGenerator)
    (b := D.basis) (wt := D.weight) (α := (t.simplyConnectedRootDatum ht).root)
    (degree := degree) A D.isCartanWeightVector_basis
    (l := [t.simpleIndex ht i]) (by simp)
    (fun δ _ => t.lie_lieBasis_h_chevalleySystem ht δ)
    (fun δ hδ => by simpa [List.mem_singleton.mp hδ] using hposdegree)
    (fun δ _ c hc => (D.smul_baseChange_kostantRootOperator_eq_zero_iff δ A c).mp hc)
    (u := fun _ => toAdd a) (v := fun _ => toAdd b)).mp
  have hparam : chevalleyRootSubgroup D.representation D.lattice D.representation_mem_lattice
      D.isNilpotent_representation_rootGenerator (t.simpleIndex ht i) (CommAlgCat.of ℤ A) a =
    chevalleyRootSubgroup D.representation D.lattice D.representation_mem_lattice
      D.isNilpotent_representation_rootGenerator (t.simpleIndex ht i) (CommAlgCat.of ℤ A) b := by
    apply Units.map_injective (f := (LinearMap.toMatrixAlgEquiv
      (D.basis.baseChange A)).toMulEquiv.toMonoidHom)
      (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).injective
    simpa only [D.coe_rootSubgroupPoints, MulEquiv.toMonoidHom_eq_coe] using
      congrArg Subtype.val hab
  simp only [List.map_singleton, List.prod_singleton,
    kostantRootSubgroupParam_chevalleySystem D.representation D.lattice
      D.representation_mem_lattice D.isNilpotent_representation_rootGenerator,
    ofAdd_toAdd] at hnative
  exact toAdd.injective (hnative hparam (t.simpleIndex ht i) (List.mem_singleton_self _))

/-- Two parameters in the same root subgroup produce equal datum points if and only if they are
equal, over any commutative ring. -/
@[simp]
theorem rootSubgroupPoints_inj {γ : Fin t.numRoots} {A : Type v} [CommRing A]
    {u v : Multiplicative A} :
    D.rootSubgroupPoints γ A u = D.rootSubgroupPoints γ A v ↔ u = v :=
  (D.rootSubgroupPoints_injective γ A).eq_iff

/-- A root-subgroup point is the identity if and only if its multiplicative parameter is `1`, over
any commutative ring. -/
@[simp]
theorem rootSubgroupPoints_eq_one_iff {γ : Fin t.numRoots} {A : Type v} [CommRing A]
    {u : Multiplicative A} :
    D.rootSubgroupPoints γ A u = 1 ↔ u = 1 :=
  map_eq_one_iff _ (D.rootSubgroupPoints_injective γ A)

end TauCeti.DynkinType.ChevalleyDatum
