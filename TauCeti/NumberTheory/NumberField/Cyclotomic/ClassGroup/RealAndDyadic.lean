/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.ComplexConjugation.ClassGroup
public import TauCeti.NumberTheory.NumberField.Cyclotomic.ClassGroup.TameComponents
import Mathlib.Algebra.DirectSum.Module
import Mathlib.NumberTheory.NumberField.ClassNumber
import TauCeti.NumberTheory.NumberField.Cyclotomic.MaximalRealSubfield

/-!
# Real/plus equivalence, even/odd eigenspace splitting, and the dyadic boundary

This module combines the Galois action and tame character decomposition on cyclotomic class groups
(`TauCeti.NumberTheory.NumberField.Cyclotomic.ClassGroup.Action` and
`TauCeti.NumberTheory.NumberField.Cyclotomic.ClassGroup.TameComponents`) with the general CM-field
complex-conjugation theory (`TauCeti.NumberTheory.NumberField.ComplexConjugation.ClassGroup`).

## Main results

### Complex conjugation and full Galois invariance on cyclotomic class groups

For any rational cyclotomic CM field `K` of level `n`:
* `TauCeti.cyclotomic_complexConj_apply`: `IsCMField.complexConj K` coincides with the cyclotomic
  automorphism `(galEquivZMod n K).symm (-1)`.
* `TauCeti.cmClassComplexConj_eq_cyclotomicClassRepresentation_neg_one`: complex conjugation on
  `R ⊗[ℤ] Additive (ClassGroup (𝓞 K))` coincides with `cyclotomicClassRepresentation n K R (-1)`.
* `TauCeti.cyclotomicClassRepresentation_mem_cmClassPlusSubmodule`,
  `TauCeti.cyclotomicClassRepresentation_mem_cmClassMinusSubmodule`,
  `TauCeti.cyclotomicClassRepresentation_mem_cmNormKernel`, and
  `TauCeti.cyclotomicMinusQuotientRepresentation`: all three minus-type modules (`ker N`,
  `ker (c + 1)`, `A / (1 + c) A`) and the plus submodule `ker (c - 1)` are stable under the full
  cyclotomic Galois group `(ZMod n)ˣ`.

### Odd primes `p ≠ 2`

For `K` of level `p ^ r` (`r ≠ 0`, `p ≠ 2`), combined with the general odd-prime CM results
`TauCeti.cmRealClassEquivPlusPadic` and `TauCeti.cmClassMinusSubmodule_eq_ker_relNorm_padic`:
* `TauCeti.isCMField_of_prime_pow_of_ne_two`: `K` is a CM field.
* `TauCeti.cmClassPlusProjector_eq_sum_even_cyclotomicClassProjector` and
  `TauCeti.cmClassMinusProjector_eq_sum_odd_cyclotomicClassProjector`: the plus and minus
  projectors `½ (1 ± c)` are the sums of the even and odd tame character projectors `e_i`.
* `TauCeti.cmClassPlusSubmodule_eq_iSup_even_eigenspace`,
  `TauCeti.cmClassMinusSubmodule_eq_iSup_odd_eigenspace`,
  `TauCeti.isInternal_cmClassPlusSubmodule_even_eigenspace`, and
  `TauCeti.isInternal_cmClassMinusSubmodule_odd_eigenspace`: internal direct-sum decompositions
  `A⁺ = ⨁_{i even} A^{(i)}` and `A⁻ = ⨁_{i odd} A^{(i)}`.

### Dyadic case `p = 2` and the conductor `2` boundary

* `TauCeti.isCMField_of_two_pow`: for `2 ≤ r`, `ℚ(ζ_{2^r})` is a CM field (so the three dyadic
  minus-type modules `cmNormKernel ℤ_[2] K`, `cmClassMinusSubmodule ℤ_[2] K`, and
  `cmMinusQuotient ℤ_[2] K` and their 2-torsion comparison theory apply).
* `TauCeti.subsingleton_classGroup_of_isCyclotomicExtension_le_two` and
  `TauCeti.subsingleton_tensor_classGroup_of_isCyclotomicExtension_le_two`: at conductor `1` or
  `2` (the non-CM boundary `ℚ(ζ₂) = ℚ`), the class group and its base change are trivial.
-/

public section

open NumberField NumberField.IsCMField
open scoped NumberField TensorProduct

namespace TauCeti

section CyclotomicCM

variable (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
  [IsCyclotomicExtension {n} ℚ K] [IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- **Complex conjugation on a rational cyclotomic CM field** coincides with the cyclotomic
automorphism attached to `-1 ∈ (ZMod n)ˣ`. -/
theorem cyclotomic_complexConj_apply (x : K) :
    complexConj K x = (IsCyclotomicExtension.Rat.galEquivZMod n K).symm (-1) x := by
  let φ : K →+* ℂ := Classical.choice inferInstance
  apply φ.injective
  rw [complexEmbedding_complexConj K φ x,
    TauCeti.IsCyclotomicExtension.Rat.complexEmbedding_galEquivZMod_symm_neg_one_apply n φ x]

/-- Complex conjugation on `ClassGroup (𝓞 K)` coincides with the cyclotomic Galois action of
`-1 ∈ (ZMod n)ˣ`. -/
theorem cmClassComplexConjMulAut_eq_cyclotomicClassMulAction_neg_one :
    cmClassComplexConjMulAut K = cyclotomicClassMulAction n K (-1) := by
  have heq : (complexConj K).toRingEquiv =
      ((IsCyclotomicExtension.Rat.galEquivZMod n K).symm (-1)).toRingEquiv :=
    RingEquiv.ext (cyclotomic_complexConj_apply n K)
  ext c
  rw [cmClassComplexConjMulAut_apply, cyclotomicClassMulAction_apply, heq]

/-- **Complex conjugation on the base-changed class module** of a cyclotomic CM field coincides with
`cyclotomicClassRepresentation n K R (-1)`. -/
theorem cmClassComplexConj_eq_cyclotomicClassRepresentation_neg_one (R : Type*) [CommRing R] :
    cmClassComplexConj R K = cyclotomicClassRepresentation n K R (-1) := by
  ext c
  obtain ⟨c, rfl⟩ := Additive.ofMul.surjective c
  simp [cmClassComplexConjMulAut_eq_cyclotomicClassMulAction_neg_one n K]

/-- Every cyclotomic Galois operator commutes with complex conjugation on the base-changed class
module. -/
theorem cyclotomicClassRepresentation_comm_cmClassComplexConj (R : Type*) [CommRing R]
    (a : (ZMod n)ˣ) :
    (cyclotomicClassRepresentation n K R a).comp (cmClassComplexConj R K) =
      (cmClassComplexConj R K).comp (cyclotomicClassRepresentation n K R a) := by
  rw [cmClassComplexConj_eq_cyclotomicClassRepresentation_neg_one n K R]
  change cyclotomicClassRepresentation n K R a * cyclotomicClassRepresentation n K R (-1) =
    cyclotomicClassRepresentation n K R (-1) * cyclotomicClassRepresentation n K R a
  rw [← map_mul, ← map_mul, mul_comm]

/-- The plus submodule `A⁺ = ker (c - 1)` is invariant under the full cyclotomic Galois group. -/
theorem cyclotomicClassRepresentation_mem_cmClassPlusSubmodule (R : Type*) [CommRing R]
    (a : (ZMod n)ˣ) {x : R ⊗[ℤ] Additive (ClassGroup (𝓞 K))}
    (hx : x ∈ cmClassPlusSubmodule R K) :
    cyclotomicClassRepresentation n K R a x ∈ cmClassPlusSubmodule R K := by
  rw [mem_cmClassPlusSubmodule_iff, ← LinearMap.comp_apply,
    ← cyclotomicClassRepresentation_comm_cmClassComplexConj n K R a, LinearMap.comp_apply,
    mem_cmClassPlusSubmodule_iff.mp hx]

/-- The anti-invariant submodule `ker (c + 1)` is invariant under the full cyclotomic Galois
group. -/
theorem cyclotomicClassRepresentation_mem_cmClassMinusSubmodule (R : Type*) [CommRing R]
    (a : (ZMod n)ˣ) {x : R ⊗[ℤ] Additive (ClassGroup (𝓞 K))}
    (hx : x ∈ cmClassMinusSubmodule R K) :
    cyclotomicClassRepresentation n K R a x ∈ cmClassMinusSubmodule R K := by
  rw [mem_cmClassMinusSubmodule_iff, ← LinearMap.comp_apply,
    ← cyclotomicClassRepresentation_comm_cmClassComplexConj n K R a, LinearMap.comp_apply,
    mem_cmClassMinusSubmodule_iff.mp hx, map_neg]

/-- Every cyclotomic automorphism preserves the maximal real subfield `K⁺`. -/
private noncomputable def cyclotomicMaximalRealRingEquiv (a : (ZMod n)ˣ) : K⁺ ≃+* K⁺ := by
  have hmem (b : (ZMod n)ˣ) (x : K⁺) :
      (IsCyclotomicExtension.Rat.galEquivZMod n K).symm b x.1 ∈ K⁺ := by
    rw [← TauCeti.IsCyclotomicExtension.Rat.galEquivZMod_symm_neg_one_apply_eq_self_iff n]
    have hcomm :
        ((IsCyclotomicExtension.Rat.galEquivZMod n K).symm (-1) *
            (IsCyclotomicExtension.Rat.galEquivZMod n K).symm b) x.1 =
          ((IsCyclotomicExtension.Rat.galEquivZMod n K).symm b *
            (IsCyclotomicExtension.Rat.galEquivZMod n K).symm (-1)) x.1 := by
      rw [← map_mul, ← map_mul, mul_comm]
    change ((IsCyclotomicExtension.Rat.galEquivZMod n K).symm (-1) *
        (IsCyclotomicExtension.Rat.galEquivZMod n K).symm b) x.1 = _
    rw [hcomm]
    change (IsCyclotomicExtension.Rat.galEquivZMod n K).symm b
        ((IsCyclotomicExtension.Rat.galEquivZMod n K).symm (-1) x.1) = _
    rw [(TauCeti.IsCyclotomicExtension.Rat.galEquivZMod_symm_neg_one_apply_eq_self_iff n x.1).mpr
      x.2]
  exact
    { toFun x := ⟨(IsCyclotomicExtension.Rat.galEquivZMod n K).symm a x.1, hmem a x⟩
      invFun x := ⟨(IsCyclotomicExtension.Rat.galEquivZMod n K).symm a⁻¹ x.1, hmem a⁻¹ x⟩
      left_inv x := Subtype.ext <| by
        change ((IsCyclotomicExtension.Rat.galEquivZMod n K).symm a⁻¹ *
            (IsCyclotomicExtension.Rat.galEquivZMod n K).symm a) x.1 = x.1
        rw [← map_mul, inv_mul_cancel, map_one]; rfl
      right_inv x := Subtype.ext <| by
        change ((IsCyclotomicExtension.Rat.galEquivZMod n K).symm a *
            (IsCyclotomicExtension.Rat.galEquivZMod n K).symm a⁻¹) x.1 = x.1
        rw [← map_mul, mul_inv_cancel, map_one]; rfl
      map_mul' x y := Subtype.ext (map_mul _ _ _)
      map_add' x y := Subtype.ext (map_add _ _ _) }

omit [IsCMField K] in
/-- **The norm kernel `ker N_{K/K⁺}` is invariant under the full cyclotomic Galois group.** -/
theorem cyclotomicClassRepresentation_mem_cmNormKernel (R : Type*) [CommRing R] (a : (ZMod n)ˣ)
    {x : R ⊗[ℤ] Additive (ClassGroup (𝓞 K))} (hx : x ∈ cmNormKernel R K) :
    cyclotomicClassRepresentation n K R a x ∈ cmNormKernel R K := by
  rw [mem_cmNormKernel_iff] at hx ⊢
  have hcomp := ClassGroup.mulEquivBaseChange_comp_relNormBaseChange R
    (RingOfIntegers.mapRingEquiv (cyclotomicMaximalRealRingEquiv n K a))
    (RingOfIntegers.mapRingEquiv ((IsCyclotomicExtension.Rat.galEquivZMod n K).symm a).toRingEquiv)
    fun r ↦ RingOfIntegers.ext rfl
  have happ := LinearMap.congr_fun hcomp x
  simp only [LinearMap.comp_apply] at happ
  rw [cyclotomicClassRepresentation_apply, ← happ, hx, map_zero]

/-- **The cyclotomic Galois action induced on the minus quotient `A / (1 + c) A`.** -/
noncomputable def cyclotomicMinusQuotientRepresentation (R : Type*) [CommRing R] :
    Representation R (ZMod n)ˣ (cmMinusQuotient R K) where
  toFun a := Submodule.mapQ _ _ (cyclotomicClassRepresentation n K R a) <| by
    rintro _ ⟨y, rfl⟩
    refine ⟨cyclotomicClassRepresentation n K R a y, ?_⟩
    have hc := LinearMap.congr_fun (cyclotomicClassRepresentation_comm_cmClassComplexConj n K R a) y
    simp only [LinearMap.comp_apply] at hc
    simp only [LinearMap.add_apply, LinearMap.id_apply, map_add, hc]
  map_one' := by
    apply Submodule.linearMap_qext
    ext c
    obtain ⟨c, rfl⟩ := Additive.ofMul.surjective c
    simp
  map_mul' a b := by
    apply Submodule.linearMap_qext
    ext c
    obtain ⟨c, rfl⟩ := Additive.ofMul.surjective c
    simp [map_mul]

@[simp]
theorem cyclotomicMinusQuotientRepresentation_mk (R : Type*) [CommRing R] (a : (ZMod n)ˣ)
    (x : R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :
    cyclotomicMinusQuotientRepresentation n K R a (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (cyclotomicClassRepresentation n K R a x) := by
  rfl

end CyclotomicCM

section OddPrime

variable (p r : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p ^ r} ℚ K]

/-- For an odd prime `p` and `r ≠ 0`, `ℚ(ζ_{p^r})` is a CM field. -/
theorem isCMField_of_prime_pow_of_ne_two (hp2 : p ≠ 2) (hr : r ≠ 0) : IsCMField K := by
  have hlt : 2 < p ^ r := by
    have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
    exact lt_of_lt_of_le (by norm_num : 2 < 3) (hp3.trans (Nat.le_self_pow hr p))
  exact IsCyclotomicExtension.Rat.isCMField (S := {p ^ r}) K ⟨p ^ r, rfl, hlt⟩

variable [IsCMField K]

private theorem isUnit_card_tame (hr : r ≠ 0) :
    IsUnit (Nat.card (rootsOfUnity (p - 1) (ZMod (p ^ r))) : ℤ_[p]) := by
  rw [ZMod.natCard_rootsOfUnity_prime_pow p r hr]
  exact (PadicInt.isUnit_natCast_iff (p := p)).mpr <|
    Nat.not_dvd_of_pos_of_lt (Nat.sub_pos_of_lt hp.out.one_lt) (Nat.sub_lt hp.out.pos one_pos)

private theorem neg_one_ne_one_padicInt_units (hp2 : p ≠ 2) : (-1 : ℤ_[p]ˣ) ≠ 1 := by
  intro h
  have h1 : (-1 : ℤ_[p]) = 1 := congrArg Units.val h
  have h2 : (2 : ℤ_[p]) = 0 := by
    rw [← one_add_one_eq_two]
    nth_rw 1 [← h1]
    exact neg_add_cancel 1
  exact (isUnit_two_padicInt p hp2).ne_zero h2

/-- For an odd prime `p`, `(-1 : ℤ_[p]ˣ) ^ n = 1` iff `n` is even. -/
private theorem neg_one_pow_padicInt_eq_one_iff (hp2 : p ≠ 2) (n : ℕ) :
    (-1 : ℤ_[p]ˣ) ^ n = 1 ↔ Even n := by
  rcases Nat.even_or_odd n with hn | hn
  · simp [hn.neg_one_pow, hn]
  · simp [hn.neg_one_pow, neg_one_ne_one_padicInt_units p hp2, Nat.not_even_iff_odd.mpr hn]

/-- For an odd prime `p`, `(-1 : ℤ_[p]ˣ) ^ n = -1` iff `n` is odd. -/
private theorem neg_one_pow_padicInt_eq_neg_one_iff (hp2 : p ≠ 2) (n : ℕ) :
    (-1 : ℤ_[p]ˣ) ^ n = -1 ↔ Odd n := by
  rcases Nat.even_or_odd n with hn | hn
  · simp [hn.neg_one_pow, (neg_one_ne_one_padicInt_units p hp2).symm, Nat.not_odd_iff_even.mpr hn]
  · simp [hn.neg_one_pow, hn]

/-- **The plus projector `½ (1 + c)` is the sum of the even tame character projectors** for an
odd prime `p`. -/
theorem cmClassPlusProjector_eq_sum_even_cyclotomicClassProjector (hp2 : p ≠ 2) (hr : r ≠ 0)
    [Invertible (2 : ℤ_[p])] [NeZero (p - 1)] :
    cmClassPlusProjector ℤ_[p] K =
      ∑ i : ZMod (p - 1) with Even i.val, cyclotomicClassProjector p r K hr i.val := by
  classical
  have : NeZero (p ^ r) := ⟨pow_ne_zero r hp.out.ne_zero⟩
  have : HasEnoughRootsOfUnity ℤ_[p] (Monoid.exponent (rootsOfUnity (p - 1) (ZMod (p ^ r)))) := by
    rw [ZMod.exponent_rootsOfUnity_prime_pow p r hr]
    exact hasEnoughRootsOfUnity_padicInt p
  let c : rootsOfUnity (p - 1) (ZMod (p ^ r)) :=
    ⟨-1, ZMod.neg_one_mem_rootsOfUnity_prime_pow hp2 r⟩
  have hc : c * c = 1 := Subtype.ext (by simp [c])
  have halg := congrArg (cyclotomicClassTameRepresentation p r K).asAlgebraHom
    (halfOneAdd_of_eq_sum_charIdempotent (O := ℤ_[p]) (isUnit_card_tame p r hr) hc)
  have hlhs : (cyclotomicClassTameRepresentation p r K).asAlgebraHom
        (halfOneAdd ℤ_[p] (MonoidAlgebra.of ℤ_[p] _ c)) =
      cmClassPlusProjector ℤ_[p] K := by
    rw [cmClassPlusProjector_eq, halfOneAdd_def, halfOneAdd_def, map_smul, map_add, map_one,
      MonoidAlgebra.of_apply, Representation.asAlgebraHom_single_one,
      cyclotomicClassTameRepresentation_apply,
      cmClassComplexConj_eq_cyclotomicClassRepresentation_neg_one (p ^ r) K ℤ_[p]]
  rw [hlhs, map_sum, Finset.sum_filter] at halg
  rw [halg, Finset.sum_filter]
  refine (Fintype.sum_equiv (tameCharEquivZMod p r hr) _ _ fun i ↦ ?_).symm
  have hval : (tameTeichmullerChar p r hr ^ (i.val : ℤ)) c = (-1 : ℤ_[p]ˣ) ^ i.val := by
    rw [MonoidHom.zpow_apply, tameTeichmullerChar_neg_one p r hr hp2, zpow_natCast]
  simp only [cyclotomicClassProjector_eq, tameCharEquivZMod_apply, hval,
    neg_one_pow_padicInt_eq_one_iff p hp2 i.val]

/-- **The minus projector `½ (1 - c)` is the sum of the odd tame character projectors** for an
odd prime `p`. -/
theorem cmClassMinusProjector_eq_sum_odd_cyclotomicClassProjector (hp2 : p ≠ 2) (hr : r ≠ 0)
    [Invertible (2 : ℤ_[p])] [NeZero (p - 1)] :
    cmClassMinusProjector ℤ_[p] K =
      ∑ i : ZMod (p - 1) with Odd i.val, cyclotomicClassProjector p r K hr i.val := by
  classical
  have : NeZero (p ^ r) := ⟨pow_ne_zero r hp.out.ne_zero⟩
  have : HasEnoughRootsOfUnity ℤ_[p] (Monoid.exponent (rootsOfUnity (p - 1) (ZMod (p ^ r)))) := by
    rw [ZMod.exponent_rootsOfUnity_prime_pow p r hr]
    exact hasEnoughRootsOfUnity_padicInt p
  let c : rootsOfUnity (p - 1) (ZMod (p ^ r)) :=
    ⟨-1, ZMod.neg_one_mem_rootsOfUnity_prime_pow hp2 r⟩
  have hc : c * c = 1 := Subtype.ext (by simp [c])
  have halg := congrArg (cyclotomicClassTameRepresentation p r K).asAlgebraHom
    (halfOneAdd_neg_of_eq_sum_charIdempotent (O := ℤ_[p]) (isUnit_card_tame p r hr) hc)
  have hlhs : (cyclotomicClassTameRepresentation p r K).asAlgebraHom
        (halfOneAdd ℤ_[p] (-MonoidAlgebra.of ℤ_[p] _ c)) =
      cmClassMinusProjector ℤ_[p] K := by
    rw [cmClassMinusProjector_eq, halfOneAdd_def, halfOneAdd_def, map_smul, map_add, map_one,
      map_neg, MonoidAlgebra.of_apply, Representation.asAlgebraHom_single_one,
      cyclotomicClassTameRepresentation_apply,
      cmClassComplexConj_eq_cyclotomicClassRepresentation_neg_one (p ^ r) K ℤ_[p]]
  rw [hlhs, map_sum, Finset.sum_filter] at halg
  rw [halg, Finset.sum_filter]
  refine (Fintype.sum_equiv (tameCharEquivZMod p r hr) _ _ fun i ↦ ?_).symm
  have hval : (tameTeichmullerChar p r hr ^ (i.val : ℤ)) c = (-1 : ℤ_[p]ˣ) ^ i.val := by
    rw [MonoidHom.zpow_apply, tameTeichmullerChar_neg_one p r hr hp2, zpow_natCast]
  simp only [cyclotomicClassProjector_eq, tameCharEquivZMod_apply, hval,
    neg_one_pow_padicInt_eq_neg_one_iff p hp2 i.val]

/-- **The plus part is the supremum of the even tame eigenspaces**:
`A_r⁺ = ⨆ (i : ZMod (p - 1)) (_ : Even i.val), A_r^{(i)}`. -/
theorem cmClassPlusSubmodule_eq_iSup_even_eigenspace (hp2 : p ≠ 2) (hr : r ≠ 0) :
    cmClassPlusSubmodule ℤ_[p] K =
      ⨆ (i : ZMod (p - 1)) (_ : Even i.val), cyclotomicClassEigenspace p r K hr i.val := by
  classical
  have : NeZero (p ^ r) := ⟨pow_ne_zero r hp.out.ne_zero⟩
  have : NeZero (p - 1) := ⟨Nat.sub_ne_zero_of_lt hp.out.one_lt⟩
  let : Invertible (2 : ℤ_[p]) := (isUnit_two_padicInt p hp2).invertible
  refine le_antisymm ?_ (iSup₂_le fun i hi x hx ↦ ?_)
  · intro x hx
    rw [← cmClassPlusProjector_apply_of_mem ℤ_[p] K hx,
      cmClassPlusProjector_eq_sum_even_cyclotomicClassProjector p r K hp2 hr,
      LinearMap.coe_sum, Finset.sum_apply]
    refine Submodule.sum_mem _ fun i hi ↦ ?_
    have hi' : Even i.val := (Finset.mem_filter.mp hi).2
    exact le_iSup₂ (f := fun (i : ZMod (p - 1)) (_ : Even i.val) ↦
      cyclotomicClassEigenspace p r K hr i.val) i hi'
      (cyclotomicClassProjector_apply_mem p r K hr i.val x)
  · rw [mem_cmClassPlusSubmodule_iff,
      cmClassComplexConj_eq_cyclotomicClassRepresentation_neg_one (p ^ r) K ℤ_[p]]
    exact cyclotomicClassRepresentation_neg_one_of_mem_eigenspace_even p r K hr hp2
      ((Int.even_natCast _).mpr hi) hx

/-- **The minus part is the supremum of the odd tame eigenspaces**:
`A_r⁻ = ⨆ (i : ZMod (p - 1)) (_ : Odd i.val), A_r^{(i)}`. -/
theorem cmClassMinusSubmodule_eq_iSup_odd_eigenspace (hp2 : p ≠ 2) (hr : r ≠ 0) :
    cmClassMinusSubmodule ℤ_[p] K =
      ⨆ (i : ZMod (p - 1)) (_ : Odd i.val), cyclotomicClassEigenspace p r K hr i.val := by
  classical
  have : NeZero (p ^ r) := ⟨pow_ne_zero r hp.out.ne_zero⟩
  have : NeZero (p - 1) := ⟨Nat.sub_ne_zero_of_lt hp.out.one_lt⟩
  let : Invertible (2 : ℤ_[p]) := (isUnit_two_padicInt p hp2).invertible
  refine le_antisymm ?_ (iSup₂_le fun i hi x hx ↦ ?_)
  · intro x hx
    rw [← cmClassMinusProjector_apply_of_mem ℤ_[p] K hx,
      cmClassMinusProjector_eq_sum_odd_cyclotomicClassProjector p r K hp2 hr,
      LinearMap.coe_sum, Finset.sum_apply]
    refine Submodule.sum_mem _ fun i hi ↦ ?_
    have hi' : Odd i.val := (Finset.mem_filter.mp hi).2
    exact le_iSup₂ (f := fun (i : ZMod (p - 1)) (_ : Odd i.val) ↦
      cyclotomicClassEigenspace p r K hr i.val) i hi'
      (cyclotomicClassProjector_apply_mem p r K hr i.val x)
  · rw [mem_cmClassMinusSubmodule_iff,
      cmClassComplexConj_eq_cyclotomicClassRepresentation_neg_one (p ^ r) K ℤ_[p]]
    exact cyclotomicClassRepresentation_neg_one_of_mem_eigenspace_odd p r K hr hp2
      ((Int.odd_natCast _).mpr hi) hx

/-- **Internal direct-sum decomposition of the plus part into even tame eigenspaces**:
`A_r⁺ = ⨁_{i even} A_r^{(i)}`. -/
theorem isInternal_cmClassPlusSubmodule_even_eigenspace (hp2 : p ≠ 2) (hr : r ≠ 0) :
    DirectSum.IsInternal fun i : {i : ZMod (p - 1) // Even i.val} ↦
      (cyclotomicClassEigenspace p r K hr i.1.val).comap
        (cmClassPlusSubmodule ℤ_[p] K).subtype := by
  have hind : iSupIndep fun i : {i : ZMod (p - 1) // Even i.val} ↦
      cyclotomicClassEigenspace p r K hr i.1.val :=
    ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp
      (isInternal_cyclotomicClassEigenspace p r K hr)).1.comp Subtype.val_injective
  have hset :
      ⨆ i ∈ ({i : ZMod (p - 1) | Even i.val}), cyclotomicClassEigenspace p r K hr i.val =
        cmClassPlusSubmodule ℤ_[p] K :=
    (cmClassPlusSubmodule_eq_iSup_even_eigenspace p r K hp2 hr).symm
  rw [← hset]
  exact DirectSum.isInternal_biSup_submodule_of_iSupIndep
    (A := fun i : ZMod (p - 1) ↦ cyclotomicClassEigenspace p r K hr i.val)
    {i : ZMod (p - 1) | Even i.val} hind

/-- **Internal direct-sum decomposition of the minus part into odd tame eigenspaces**:
`A_r⁻ = ⨁_{i odd} A_r^{(i)}`. -/
theorem isInternal_cmClassMinusSubmodule_odd_eigenspace (hp2 : p ≠ 2) (hr : r ≠ 0) :
    DirectSum.IsInternal fun i : {i : ZMod (p - 1) // Odd i.val} ↦
      (cyclotomicClassEigenspace p r K hr i.1.val).comap
        (cmClassMinusSubmodule ℤ_[p] K).subtype := by
  have hind : iSupIndep fun i : {i : ZMod (p - 1) // Odd i.val} ↦
      cyclotomicClassEigenspace p r K hr i.1.val :=
    ((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp
      (isInternal_cyclotomicClassEigenspace p r K hr)).1.comp Subtype.val_injective
  have hset :
      ⨆ i ∈ ({i : ZMod (p - 1) | Odd i.val}), cyclotomicClassEigenspace p r K hr i.val =
        cmClassMinusSubmodule ℤ_[p] K :=
    (cmClassMinusSubmodule_eq_iSup_odd_eigenspace p r K hp2 hr).symm
  rw [← hset]
  exact DirectSum.isInternal_biSup_submodule_of_iSupIndep
    (A := fun i : ZMod (p - 1) ↦ cyclotomicClassEigenspace p r K hr i.val)
    {i : ZMod (p - 1) | Odd i.val} hind

end OddPrime

section DyadicAndConductorTwo

/-- For `2 ≤ r`, `ℚ(ζ_{2^r})` is a CM field. -/
theorem isCMField_of_two_pow (r : ℕ) (hr : 2 ≤ r) (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {2 ^ r} ℚ K] : IsCMField K := by
  have hlt : 2 < 2 ^ r :=
    lt_of_lt_of_le (by norm_num : 2 < 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) hr)
  exact IsCyclotomicExtension.Rat.isCMField (S := {2 ^ r}) K ⟨2 ^ r, rfl, hlt⟩

/-- Any number field of degree `1` over `ℚ` has trivial class group. -/
theorem subsingleton_classGroup_of_finrank_eq_one (K : Type*) [Field K] [NumberField K]
    (hfin : Module.finrank ℚ K = 1) : Subsingleton (ClassGroup (𝓞 K)) := by
  have hbij : Function.Bijective (algebraMap ℚ K) :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hfin
  let eInt : ℤ ≃+* 𝓞 K :=
    Rat.ringOfIntegersEquiv.symm.trans
      (RingOfIntegers.mapRingEquiv (RingEquiv.ofBijective (algebraMap ℚ K) hbij))
  have hpir : IsPrincipalIdealRing (𝓞 K) :=
    IsPrincipalIdealRing.of_surjective eInt.toRingHom eInt.surjective
  have hcard : Fintype.card (ClassGroup (𝓞 K)) = 1 :=
    NumberField.classNumber_eq_one_iff.mpr hpir
  exact Fintype.card_le_one_iff_subsingleton.mp hcard.le

/-- **Triviality of the class group at conductor `1` or `2`**: when `n ≤ 2` (`n ≠ 0`),
`ℚ(ζₙ) = ℚ` has trivial class group. -/
theorem subsingleton_classGroup_of_isCyclotomicExtension_le_two (n : ℕ) [NeZero n] (hn : n ≤ 2)
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K] :
    Subsingleton (ClassGroup (𝓞 K)) := by
  have hφ : Nat.totient n = 1 := by
    have hpos : 0 < n := NeZero.pos n
    interval_cases n <;> decide
  apply subsingleton_classGroup_of_finrank_eq_one K
  rw [IsCyclotomicExtension.finrank K (Polynomial.cyclotomic.irreducible_rat (NeZero.pos n)), hφ]

/-- **Triviality of base-changed class modules at conductor `1` or `2`** (in particular
`ℤ_[2] ⊗[ℤ] Additive (ClassGroup (𝓞 ℚ(ζ₂)))` is subsingleton). -/
theorem subsingleton_tensor_classGroup_of_isCyclotomicExtension_le_two (n : ℕ) [NeZero n]
    (hn : n ≤ 2) (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
    (R : Type*) [CommRing R] :
    Subsingleton (R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) := by
  have : Subsingleton (ClassGroup (𝓞 K)) :=
    subsingleton_classGroup_of_isCyclotomicExtension_le_two n hn K
  refine ⟨fun x y ↦ ?_⟩
  have hzero (z : R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) : z = 0 := by
    induction z using TensorProduct.inductionOn with
    | tmul r c =>
      have hc : c = 0 := Subsingleton.elim c 0
      rw [hc, TensorProduct.tmul_zero]
    | add a b ha hb => rw [ha, hb, add_zero]
  rw [hzero x, hzero y]

end DyadicAndConductorTwo

end TauCeti
