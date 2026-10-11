/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.ChangeOfGroup
import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Basic
import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicPow

/-!
# Prime-to-p restriction for the pro-p class module

Power maps of exponent prime to `p` are automorphisms of the pro-`p` class module. Consequently,
restriction from a finite quotient to a subgroup of index prime to `p` is injective in degrees one
and two.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  (3.6.3) and (3.6.4), (i) ⇒ (iii).
-/

public section

namespace TauCeti

open ContCohomology

universe u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- The `m`-th power map on `V^ab(p)` is bijective when `m` is prime to `p`. -/
theorem abelianizationProP_pow_bijective (hp : p.Prime) (V : Subgroup G)
    (hV : IsOpen (V : Set G)) (m : ℕ) (hm : Nat.Coprime m p) :
    Function.Bijective fun a : abelianizationProP p G V ↦ a ^ m := by
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : CompactSpace V :=
    isCompact_iff_compactSpace.mp (V.isClosed_of_isOpen hV).isCompact
  let hP : IsProP p (abelianizationProP p G V) :=
    isProP_maximalProPQuotient (p := p) (G := TopologicalAbelianization V)
  have hunit : IsUnit (m : ℤ_[p]) :=
    PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr hm.symm)
  let a : ℤ_[p]ˣ := hunit.unit
  have ha : (a : ℤ_[p]) = m := hunit.unit_spec
  have heq : (fun x : abelianizationProP p G V ↦ x ^ m) = hP.padicPowHomeomorph a := by
    funext x
    rw [IsProP.padicPowHomeomorph_apply, ha, hP.padicPow_natCast]
  rw [heq]
  exact (hP.padicPowHomeomorph a).bijective

private theorem abelianizationProP_nsmul_bijective (hp : p.Prime) (V : Subgroup G)
    (hV : IsOpen (V : Set G)) (m : ℕ) (hm : Nat.Coprime m p) :
    Function.Bijective fun a : Additive (abelianizationProP p G V) ↦ m • a := by
  have hpow := abelianizationProP_pow_bijective hp V hV m hm
  constructor
  · intro a b hab
    apply Additive.toMul.injective
    apply hpow.injective
    simpa only [toMul_nsmul] using congrArg Additive.toMul hab
  · intro a
    obtain ⟨b, hb⟩ := hpow.surjective a.toMul
    refine ⟨Additive.ofMul b, Additive.toMul.injective ?_⟩
    simpa only [toMul_nsmul, toMul_ofMul] using hb

private noncomputable def abelianizationProPNsmulEquiv (hp : p.Prime) (V : Subgroup G)
    (hV : IsOpen (V : Set G)) (m : ℕ) (hm : Nat.Coprime m p) :
    Additive (abelianizationProP p G V) ≃+ Additive (abelianizationProP p G V) :=
  AddEquiv.ofBijective (nsmulAddMonoidHom m) (abelianizationProP_nsmul_bijective hp V hV m hm)

@[simp]
private theorem abelianizationProPNsmulEquiv_apply (hp : p.Prime) (V : Subgroup G)
    (hV : IsOpen (V : Set G)) (m : ℕ) (hm : Nat.Coprime m p)
    (a : Additive (abelianizationProP p G V)) :
    abelianizationProPNsmulEquiv hp V hV m hm a = m • a :=
  rfl

private theorem continuous_abelianizationProPNsmulEquiv (hp : p.Prime) (V : Subgroup G)
    (hV : IsOpen (V : Set G)) (m : ℕ) (hm : Nat.Coprime m p) :
    Continuous (abelianizationProPNsmulEquiv hp V hV m hm) := by
  -- Unfold the private equivalence to expose its underlying multiplication map to the topology API.
  change Continuous fun a : Additive (abelianizationProP p G V) ↦ m • a
  exact continuous_nsmul m

private theorem continuous_abelianizationProPNsmulEquiv_symm (hp : p.Prime) (V : Subgroup G)
    (hV : IsOpen (V : Set G)) (m : ℕ) (hm : Nat.Coprime m p) :
    Continuous (abelianizationProPNsmulEquiv hp V hV m hm).symm := by
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : CompactSpace V :=
    isCompact_iff_compactSpace.mp (V.isClosed_of_isOpen hV).isCompact
  let hP : IsProP p (abelianizationProP p G V) :=
    isProP_maximalProPQuotient (p := p) (G := TopologicalAbelianization V)
  have hunit : IsUnit (m : ℤ_[p]) :=
    PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr hm.symm)
  let a : ℤ_[p]ˣ := hunit.unit
  have ha : (a : ℤ_[p]) = m := hunit.unit_spec
  have hc : Continuous fun x : Additive (abelianizationProP p G V) ↦
      Additive.ofMul ((hP.padicPowHomeomorph a).symm x.toMul) := by
    exact (hP.padicPowHomeomorph a).symm.continuous
  apply hc.congr
  intro x
  apply (abelianizationProPNsmulEquiv hp V hV m hm).injective
  rw [(abelianizationProPNsmulEquiv hp V hV m hm).apply_symm_apply]
  apply Additive.toMul.injective
  -- Cross to the multiplicative carrier where the inverse `p`-adic power identities apply.
  change ((hP.padicPowHomeomorph a).symm x.toMul) ^ m = x.toMul
  rw [← hP.padicPow_natCast, ← ha, ← IsProP.padicPowHomeomorph_apply]
  exact (hP.padicPowHomeomorph a).apply_symm_apply x.toMul

private theorem abelianizationProPNsmulEquiv_smul {V : Subgroup G} [V.Normal]
    (hp : p.Prime) (hV : IsOpen (V : Set G)) (m : ℕ) (hm : Nat.Coprime m p)
    (q : G ⧸ V) (a : Additive (abelianizationProP p G V)) :
    abelianizationProPNsmulEquiv hp V hV m hm (q • a) =
      q • abelianizationProPNsmulEquiv hp V hV m hm a := by
  simp only [abelianizationProPNsmulEquiv_apply]
  clear hm
  induction m with
  | zero => simp
  | succ m ih => simp only [succ_nsmul, smul_add, ih]

private noncomputable def abelianizationProPNsmulH1Equiv {V : Subgroup G} [V.Normal]
    (hp : p.Prime) (hV : IsOpen (V : Set G)) (m : ℕ) (hm : Nat.Coprime m p) :
    H1 (G ⧸ V) (Additive (abelianizationProP p G V)) ≃+
      H1 (G ⧸ V) (Additive (abelianizationProP p G V)) :=
  explicitCoeff1Equiv (G ⧸ V) (Additive (abelianizationProP p G V))
    (abelianizationProPNsmulEquiv hp V hV m hm)
    (continuous_abelianizationProPNsmulEquiv hp V hV m hm)
    (continuous_abelianizationProPNsmulEquiv_symm hp V hV m hm)
    (abelianizationProPNsmulEquiv_smul hp hV m hm)

@[simp]
private theorem abelianizationProPNsmulH1Equiv_apply {V : Subgroup G} [V.Normal]
    (hp : p.Prime) (hV : IsOpen (V : Set G)) (m : ℕ) (hm : Nat.Coprime m p)
    (x : H1 (G ⧸ V) (Additive (abelianizationProP p G V))) :
    abelianizationProPNsmulH1Equiv hp hV m hm x = m • x := by
  rw [abelianizationProPNsmulH1Equiv, explicitCoeff1Equiv_apply]
  apply explicitCoeff1_eq_nsmul
  intro a
  rfl

private noncomputable def abelianizationProPNsmulH2Equiv {V : Subgroup G} [V.Normal]
    (hp : p.Prime) (hV : IsOpen (V : Set G)) (m : ℕ) (hm : Nat.Coprime m p) :
    H2 (G ⧸ V) (Additive (abelianizationProP p G V)) ≃+
      H2 (G ⧸ V) (Additive (abelianizationProP p G V)) :=
  explicitCoeff2Equiv (G ⧸ V) (Additive (abelianizationProP p G V))
    (abelianizationProPNsmulEquiv hp V hV m hm)
    (continuous_abelianizationProPNsmulEquiv hp V hV m hm)
    (continuous_abelianizationProPNsmulEquiv_symm hp V hV m hm)
    (abelianizationProPNsmulEquiv_smul hp hV m hm)

@[simp]
private theorem abelianizationProPNsmulH2Equiv_apply {V : Subgroup G} [V.Normal]
    (hp : p.Prime) (hV : IsOpen (V : Set G)) (m : ℕ) (hm : Nat.Coprime m p)
    (x : H2 (G ⧸ V) (Additive (abelianizationProP p G V))) :
    abelianizationProPNsmulH2Equiv hp hV m hm x = m • x := by
  rw [abelianizationProPNsmulH2Equiv, explicitCoeff2Equiv_apply]
  apply explicitCoeff2_eq_nsmul
  intro a
  rfl

/-- Restriction to a subgroup of index prime to `p` is injective on the first cohomology of the
pro-`p` class module. -/
theorem abelianizationProPRes1_injective (hp : p.Prime) (V : Subgroup G) [V.Normal]
    (hV : IsOpen (V : Set G)) (S : Subgroup (G ⧸ V)) (hS : ¬p ∣ S.index) :
    Function.Injective
      (explicitRes1 (G ⧸ V) (Additive (abelianizationProP p G V)) S) := by
  let _ : Finite (G ⧸ V) := V.quotient_finite_of_isOpen hV
  let _ : DiscreteTopology (G ⧸ V) := QuotientGroup.discreteTopology hV
  let _ : S.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hcop : S.index.Coprime p := (hp.coprime_iff_not_dvd.mpr hS).symm
  let e := abelianizationProPNsmulH1Equiv hp hV S.index hcop
  intro x y hxy
  apply e.injective
  rw [abelianizationProPNsmulH1Equiv_apply, abelianizationProPNsmulH1Equiv_apply]
  calc
    S.index • x = explicitCor1 (G ⧸ V) (Additive (abelianizationProP p G V)) S
        (isOpen_discrete (S : Set (G ⧸ V)))
        (explicitRes1 (G ⧸ V) (Additive (abelianizationProP p G V)) S x) :=
      (explicitCor1_comp_res1 (G ⧸ V) (Additive (abelianizationProP p G V)) S
        (isOpen_discrete (S : Set (G ⧸ V))) x).symm
    _ = explicitCor1 (G ⧸ V) (Additive (abelianizationProP p G V)) S
        (isOpen_discrete (S : Set (G ⧸ V)))
        (explicitRes1 (G ⧸ V) (Additive (abelianizationProP p G V)) S y) := congrArg _ hxy
    _ = S.index • y := explicitCor1_comp_res1 (G ⧸ V)
      (Additive (abelianizationProP p G V)) S (isOpen_discrete (S : Set (G ⧸ V))) y

/-- Restriction to a subgroup of index prime to `p` is injective on the second cohomology of the
pro-`p` class module. -/
theorem abelianizationProPRes2_injective (hp : p.Prime) (V : Subgroup G) [V.Normal]
    (hV : IsOpen (V : Set G)) (S : Subgroup (G ⧸ V)) (hS : ¬p ∣ S.index) :
    Function.Injective
      (explicitRes2 (G ⧸ V) (Additive (abelianizationProP p G V)) S) := by
  let _ : Finite (G ⧸ V) := V.quotient_finite_of_isOpen hV
  let _ : DiscreteTopology (G ⧸ V) := QuotientGroup.discreteTopology hV
  let _ : S.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hcop : S.index.Coprime p := (hp.coprime_iff_not_dvd.mpr hS).symm
  let e := abelianizationProPNsmulH2Equiv hp hV S.index hcop
  intro x y hxy
  apply e.injective
  rw [abelianizationProPNsmulH2Equiv_apply, abelianizationProPNsmulH2Equiv_apply]
  calc
    S.index • x = explicitCor2 (G ⧸ V) (Additive (abelianizationProP p G V)) S
        (isOpen_discrete (S : Set (G ⧸ V)))
        (explicitRes2 (G ⧸ V) (Additive (abelianizationProP p G V)) S x) :=
      (explicitCor2_comp_res2 (G ⧸ V) (Additive (abelianizationProP p G V)) S
        (isOpen_discrete (S : Set (G ⧸ V))) x).symm
    _ = explicitCor2 (G ⧸ V) (Additive (abelianizationProP p G V)) S
        (isOpen_discrete (S : Set (G ⧸ V)))
        (explicitRes2 (G ⧸ V) (Additive (abelianizationProP p G V)) S y) := congrArg _ hxy
    _ = S.index • y := explicitCor2_comp_res2 (G ⧸ V)
      (Additive (abelianizationProP p G V)) S (isOpen_discrete (S : Set (G ⧸ V))) y

end TauCeti
