/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Araki
public import TauCeti.RingTheory.FormalGroup.Typical.Universal
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
import TauCeti.Data.Nat.Cast.Prime
import TauCeti.RingTheory.FormalGroup.Hazewinkel.LeadingDifference

/-!
# Araki's generators of the universal `p`-typical law

Let `p` be a prime. Hazewinkel's integral formal group law `F_v`
(`TauCeti.hazewinkelIntegralFormalGroup p v`) is the universal `p`-typical law over rings in
which every prime `q ≠ p` is invertible (`TauCeti.hazewinkelLift`), so its parameters
`v₁, v₂, …` are polynomial generators of the ring `V = ℤ_(p)[v₁, v₂, …]` of the universal
`p`-typical law. Araki's generators are the Araki coefficients `aₙ` of `F_v`
(`FormalGroup.arakiCoeff`), the coefficients of the expansion
`[p]_F(X) = ∑^F_{i ≥ 0} aᵢ X ^ (p ^ i)`, `a₀ = p`. This file shows that they are polynomial
generators of `V` as well.

The key computation is that `aₙ` is triangular in `v` with unit leading coefficient: if `v` and
`w` agree below `n`, then `aₙ(F_v) - aₙ(F_w) = (1 - p ^ (p ^ n - 1)) (vₙ - wₙ)`
(`TauCeti.arakiCoeff_hazewinkelIntegralFormalGroup_sub`). Over a `ℚ`-algebra this follows from
Hazewinkel's and Araki's recursions for the logarithm, `p ℓₙ = ∑_{i < n} ℓᵢ v_(n - i) ^ (p ^ i)`
and `p ℓₙ = ∑_{i ≤ n} ℓᵢ a_(n - i) ^ (p ^ i)`; it then holds over every commutative ring because
it holds for the universal pair of families over a polynomial ring over `ℤ`. For `n = 1` it says
`a₁ = (1 - p ^ (p - 1)) v₁`.

The factor `1 - p ^ (p ^ n - 1)` is prime to `p`, hence a unit when every prime `q ≠ p` is. Then
`v ↦ (aₙ(F_v))ₙ` is a bijection of families
(`TauCeti.bijective_arakiCoeff_hazewinkelIntegralFormalGroup`), so a commutative `p`-typical law is
determined by its Araki coefficients and every family of Araki coefficients occurs
(`TauCeti.arakiCoeffEquiv`). Equivalently, the `R`-algebra endomorphism of `R[v₁, v₂, …]` sending
`vₙ` to `aₙ` is an automorphism (`TauCeti.arakiAlgEquiv`): the Araki generators generate
`R[v₁, v₂, …]` and are algebraically independent.

## Main definitions

* `TauCeti.arakiCoeffEquiv`: commutative `p`-typical laws correspond to families of Araki
  coefficients `(a₁, a₂, …)`.
* `TauCeti.arakiAlgEquiv`: the `R`-algebra automorphism `vₙ ↦ aₙ` of `R[v₁, v₂, …]`.

## Main results

* `TauCeti.arakiCoeff_hazewinkelIntegralFormalGroup_sub`: the triangularity formula.
* `TauCeti.arakiCoeff_hazewinkelIntegralFormalGroup_congr`: `aₖ(F_v)` only depends on
  `v₁, …, vₖ`.
* `TauCeti.bijective_arakiCoeff_hazewinkelIntegralFormalGroup`: Hazewinkel's parameters and
  Araki's coefficients determine each other.
* `FormalGroup.IsPTypical.eq_of_arakiCoeff_eq`: a `p`-typical law is determined by its Araki
  coefficients.
* `TauCeti.adjoin_range_arakiCoeff_eq_top`, `TauCeti.algebraicIndependent_arakiCoeff`: Araki's
  generators are free polynomial generators.

## References

* S. Araki, *Typical Formal Groups in Complex Cobordism and K-Theory*, Lectures in Mathematics,
  Kyoto University 6, Kinokuniya (1973).
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres* (1986), (A2.2.1),
  (A2.2.2) and Theorem A2.2.3.
-/

public section

noncomputable section

open PowerSeries (coeff)

namespace TauCeti

variable {R : Type*} [CommRing R] {p : ℕ} [hp : Fact p.Prime]

/-! ### Triangularity of Araki's generators -/

/-- The triangularity formula over the integers: for the universal pair of families over
`ℤ[xᵢ, yᵢ]` that agree below `n`. -/
private theorem arakiCoeff_hazewinkelIntegralFormalGroup_sub_universal (n : ℕ+) :
    let v : ℕ+ → MvPolynomial (ℕ+ ⊕ ℕ+) ℤ := fun i ↦ .X (.inl i)
    let w : ℕ+ → MvPolynomial (ℕ+ ⊕ ℕ+) ℤ := fun i ↦ if i < n then .X (.inl i) else .X (.inr i)
    (hazewinkelIntegralFormalGroup p v).arakiCoeff hp.out n -
        (hazewinkelIntegralFormalGroup p w).arakiCoeff hp.out n =
      (1 - (p : MvPolynomial (ℕ+ ⊕ ℕ+) ℤ) ^ (p ^ (n : ℕ) - 1)) * (v n - w n) := by
  intro v w
  -- embed `ℤ[xᵢ, yᵢ]` into `ℚ[xᵢ, yᵢ]`, where the laws are given by Hazewinkel's logarithms
  set ι := MvPolynomial.map (σ := ℕ+ ⊕ ℕ+) (Int.castRingHom ℚ)
  have hι : Function.Injective ι := MvPolynomial.map_injective _ Int.cast_injective
  have hvw : ∀ i < n, ι (v i) = ι (w i) := fun i hi ↦ by simp [v, w, hi]
  have hlog (u : ℕ+ → MvPolynomial (ℕ+ ⊕ ℕ+) ℤ) (k : ℕ) :
      coeff (p ^ k) ((hazewinkelIntegralFormalGroup p u).map ι).log =
        hazewinkelLogCoeff p (ι ∘ u) k := by
    rw [map_hazewinkelIntegralFormalGroup, hazewinkelIntegralFormalGroup_eq_hazewinkelFormalGroup,
      log_hazewinkelFormalGroup, coeff_hazewinkelLog_pow _ hp.out.one_lt]
  have hn : p ^ (n : ℕ) ≠ 0 := pow_ne_zero _ hp.out.ne_zero
  have hpinv (x : MvPolynomial (ℕ+ ⊕ ℕ+) ℚ) :
      (p : MvPolynomial (ℕ+ ⊕ ℕ+) ℚ) * ((p : ℚ)⁻¹ • x) = x := by
    rw [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℚ,
      smul_inv_smul₀ (Nat.cast_ne_zero.2 hp.out.ne_zero)]
  apply hι
  rw [map_sub, FormalGroup.map_arakiCoeff, FormalGroup.map_arakiCoeff,
    FormalGroup.arakiCoeff_sub_arakiCoeff _ hp.out
      ((isPTypical_hazewinkelIntegralFormalGroup p v).map ι) _
      ((isPTypical_hazewinkelIntegralFormalGroup p w).map ι) fun k hk ↦ ?_, hlog, hlog,
    hazewinkelLogCoeff_sub_of_forall_lt (v := ι ∘ v) (w := ι ∘ w) n hvw, ← pow_sub_one_mul hn,
    ← one_sub_mul, mul_assoc, hpinv]
  · simp
  · rw [hlog, hlog]
    exact hazewinkelLogCoeff_congr (N := k) (fun i hi ↦ hvw i (by rw [← PNat.coe_lt_coe]; omega))
      le_rfl

/-- **Araki's generators are triangular in Hazewinkel's.** If `v` and `w` agree below `n`, then
`aₙ(F_v) - aₙ(F_w) = (1 - p ^ (p ^ n - 1)) (vₙ - wₙ)`. For `n = 1` this says
`a₁ = (1 - p ^ (p - 1)) v₁`. -/
theorem arakiCoeff_hazewinkelIntegralFormalGroup_sub {v w : ℕ+ → R} {n : ℕ+}
    (h : ∀ i < n, v i = w i) :
    (hazewinkelIntegralFormalGroup p v).arakiCoeff hp.out n -
        (hazewinkelIntegralFormalGroup p w).arakiCoeff hp.out n =
      (1 - (p : R) ^ (p ^ (n : ℕ) - 1)) * (v n - w n) := by
  -- specialize the universal pair of families along `xᵢ ↦ vᵢ`, `yᵢ ↦ wᵢ`
  set g := MvPolynomial.eval₂Hom (Int.castRingHom R) (Sum.elim v w)
  have e := congrArg g (arakiCoeff_hazewinkelIntegralFormalGroup_sub_universal (p := p) n)
  have hv : (g ∘ fun i ↦ MvPolynomial.X (.inl i)) = v := funext fun i ↦ by simp [g]
  have hw : (g ∘ fun i ↦ if i < n then MvPolynomial.X (.inl i) else MvPolynomial.X (.inr i)) =
      w := funext fun i ↦ by by_cases hi : i < n <;> simp [g, hi, h]
  simp only [map_sub, map_mul, map_one, map_pow, map_natCast, FormalGroup.map_arakiCoeff,
    map_hazewinkelIntegralFormalGroup, hv, hw] at e
  simpa [g] using e

/-- The Araki coefficient `aₖ(F_v)` only depends on `v₁, …, vₖ`. -/
theorem arakiCoeff_hazewinkelIntegralFormalGroup_congr {v w : ℕ+ → R} {k : ℕ}
    (h : ∀ i : ℕ+, (i : ℕ) ≤ k → v i = w i) :
    (hazewinkelIntegralFormalGroup p v).arakiCoeff hp.out k =
      (hazewinkelIntegralFormalGroup p w).arakiCoeff hp.out k := by
  rcases k with _ | k
  · simp
  have e := arakiCoeff_hazewinkelIntegralFormalGroup_sub (p := p) (n := k.succPNat)
    fun i hi ↦ h i (by rw [← PNat.coe_lt_coe, Nat.succPNat_coe] at hi; omega)
  rwa [h _ (by simp), sub_self, mul_zero, sub_eq_zero, Nat.succPNat_coe] at e

variable (p) in
/-- The leading coefficient `1 - p ^ (p ^ n - 1)` of `aₙ` in `vₙ` is prime to `p`, so it is a unit
when every prime `q ≠ p` is. -/
private theorem isUnit_one_sub_pow (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) (n : ℕ+) :
    IsUnit (1 - (p : R) ^ (p ^ (n : ℕ) - 1)) := by
  set e := p ^ (n : ℕ) - 1
  have he : e ≠ 0 := by
    have := Nat.one_lt_pow n.ne_zero hp.out.one_lt
    omega
  have h1 : 1 ≤ p ^ e := Nat.one_le_pow _ _ hp.out.pos
  have hp1 : p ^ e - 1 ≠ 0 := by
    have := Nat.one_lt_pow he hp.out.one_lt
    omega
  have hu : IsUnit ((p ^ e - 1 : ℕ) : R) := by
    refine isUnit_natCast_of_forall_prime_dvd hp1 fun q hq hqd ↦ hunit q hq ?_
    rintro rfl
    have : q ∣ q ^ e - (q ^ e - 1) := Nat.dvd_sub (dvd_pow_self q he) hqd
    rw [Nat.sub_sub_self h1] at this
    exact hq.one_lt.ne' (Nat.dvd_one.mp this)
  rw [Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one] at hu
  simpa using hu.neg

/-! ### Araki's generators classify `p`-typical laws -/

variable (p) in
/-- **Hazewinkel's parameters and Araki's coefficients determine each other.** If every prime
`q ≠ p` is invertible in `R`, then `v ↦ (a₁(F_v), a₂(F_v), …)` is a bijection of families. -/
theorem bijective_arakiCoeff_hazewinkelIntegralFormalGroup
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    Function.Bijective fun (v : ℕ+ → R) (n : ℕ+) ↦
      (hazewinkelIntegralFormalGroup p v).arakiCoeff hp.out n := by
  set α := fun (v : ℕ+ → R) (n : ℕ+) ↦ (hazewinkelIntegralFormalGroup p v).arakiCoeff hp.out n
  have hu := isUnit_one_sub_pow (R := R) p hunit
  refine ⟨fun v w hvw ↦ funext fun n ↦ ?_, fun a ↦ ?_⟩
  · -- `vₙ = wₙ` by induction: `0 = aₙ(F_v) - aₙ(F_w) = (1 - p ^ (p ^ n - 1)) (vₙ - wₙ)`
    induction n using PNat.strongInductionOn with
    | _ n ih =>
      have e := arakiCoeff_hazewinkelIntegralFormalGroup_sub (p := p) ih
      rw [show (hazewinkelIntegralFormalGroup p v).arakiCoeff hp.out n =
        (hazewinkelIntegralFormalGroup p w).arakiCoeff hp.out n from congrFun hvw n, sub_self,
        eq_comm, (hu n).mul_right_eq_zero, sub_eq_zero] at e
      exact e
  -- correct `v₁, v₂, …` one at a time: `V N` has the Araki coefficients `a₁, …, a_N`
  let V : ℕ → ℕ+ → R := fun N ↦ N.rec 0 fun N VN ↦ Function.update VN N.succPNat
    (VN N.succPNat + ↑(hu N.succPNat).unit⁻¹ * (a N.succPNat - α VN N.succPNat))
  have hV (N : ℕ) : V (N + 1) = Function.update (V N) N.succPNat
      (V N N.succPNat + ↑(hu N.succPNat).unit⁻¹ * (a N.succPNat - α (V N) N.succPNat)) := rfl
  have hVne (N : ℕ) (i : ℕ+) (hi : (i : ℕ) ≤ N) : V (N + 1) i = V N i := by
    rw [hV, Function.update_of_ne]
    rintro rfl
    simp at hi
  have hstab (N : ℕ) (i : ℕ+) (hi : (i : ℕ) ≤ N) : V N i = V i i := by
    induction N with
    | zero => exact absurd hi (by simp)
    | succ N ihN =>
      rcases (Nat.lt_or_eq_of_le hi) with hi | hi
      · rw [hVne N i (by omega), ihN (by omega)]
      · rw [hi]
  have hα (N : ℕ) : ∀ k : ℕ+, (k : ℕ) ≤ N → α (V N) k = a k := by
    induction N with
    | zero => exact fun k hk ↦ absurd hk (by simp)
    | succ N ihN =>
      intro k hk
      rcases (Nat.lt_or_eq_of_le hk) with hk | hk
      · rw [← ihN k (by omega)]
        exact arakiCoeff_hazewinkelIntegralFormalGroup_congr fun i hi ↦ hVne N i (by omega)
      · obtain rfl : k = N.succPNat := PNat.eq (by simpa using hk)
        have e := arakiCoeff_hazewinkelIntegralFormalGroup_sub (p := p) (v := V (N + 1))
          (w := V N) (n := N.succPNat) fun i hi ↦ hVne N i (by
            rw [← PNat.coe_lt_coe, Nat.succPNat_coe] at hi; omega)
        rw [hV N, Function.update_self, add_sub_cancel_left, ← mul_assoc, IsUnit.mul_val_inv,
          one_mul, ← hV N, sub_left_inj] at e
        exact e
  refine ⟨fun n ↦ V n n, funext fun n ↦ ?_⟩
  rw [← hα n n le_rfl]
  exact arakiCoeff_hazewinkelIntegralFormalGroup_congr fun i hi ↦ (hstab n i hi).symm

variable (p) (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))

/-- The Hazewinkel parameters `v` with prescribed Araki coefficients. -/
private def arakiParamEquiv : (ℕ+ → R) ≃ (ℕ+ → R) :=
  Equiv.ofBijective _ (bijective_arakiCoeff_hazewinkelIntegralFormalGroup p hunit)

private theorem arakiParamEquiv_apply (v : ℕ+ → R) (n : ℕ+) :
    arakiParamEquiv p hunit v n = (hazewinkelIntegralFormalGroup p v).arakiCoeff hp.out n := (rfl)

/-- The Araki coefficients of Hazewinkel's law commute with base change of the parameters. -/
private theorem map_comp_arakiParamEquiv {S : Type*} [CommRing S]
    (hS : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : S)) (f : R →+* S) (v : ℕ+ → R) :
    f ∘ arakiParamEquiv p hunit v = arakiParamEquiv p hS (f ∘ v) :=
  funext fun n ↦ by
    simp only [Function.comp_apply, arakiParamEquiv_apply, FormalGroup.map_arakiCoeff,
      map_hazewinkelIntegralFormalGroup]

/-- The parameters with prescribed Araki coefficients commute with base change. -/
private theorem map_comp_arakiParamEquiv_symm {S : Type*} [CommRing S]
    (hS : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : S)) (f : R →+* S) (a : ℕ+ → R) :
    f ∘ (arakiParamEquiv p hunit).symm a = (arakiParamEquiv p hS).symm (f ∘ a) := by
  rw [Equiv.eq_symm_apply, ← map_comp_arakiParamEquiv p hunit hS, Equiv.apply_symm_apply]

/-- **Araki's generators classify `p`-typical laws.** If every prime `q ≠ p` is invertible in
`R`, a commutative `p`-typical formal group law over `R` is determined by its Araki coefficients
`(a₁, a₂, …)`, and every family occurs. -/
def arakiCoeffEquiv :
    {F : FormalGroup R // ∃ (_ : F.IsComm), F.IsPTypical p} ≃ (ℕ+ → R) :=
  Equiv.ofBijective (fun F n ↦ F.val.arakiCoeff hp.out n) <| by
    refine ⟨fun F G hFG ↦ ?_, fun a ↦ ?_⟩
    · have := F.property.1
      have := G.property.1
      obtain ⟨v, hv⟩ := F.property.2.exists_eq_hazewinkelIntegralFormalGroup hunit
      obtain ⟨w, hw⟩ := G.property.2.exists_eq_hazewinkelIntegralFormalGroup hunit
      have hvw : v = w := (arakiParamEquiv p hunit).injective <| by
        simpa only [arakiParamEquiv_apply, funext_iff, ← hv, ← hw] using hFG
      exact Subtype.ext (by rw [hv, hw, hvw])
    · refine ⟨⟨hazewinkelIntegralFormalGroup p ((arakiParamEquiv p hunit).symm a), inferInstance,
        isPTypical_hazewinkelIntegralFormalGroup p _⟩, ?_⟩
      exact (arakiParamEquiv p hunit).apply_symm_apply a

/-- `arakiCoeffEquiv` sends a law to its family of Araki coefficients. -/
@[simp]
theorem arakiCoeffEquiv_apply (F : {F : FormalGroup R // ∃ (_ : F.IsComm), F.IsPTypical p})
    (n : ℕ+) : arakiCoeffEquiv p hunit F n = F.val.arakiCoeff hp.out n := (rfl)

/-- The law with prescribed Araki coefficients `a` has Araki coefficients `a`. -/
@[simp]
theorem arakiCoeff_arakiCoeffEquiv_symm (a : ℕ+ → R) (n : ℕ+) :
    ((arakiCoeffEquiv p hunit).symm a).val.arakiCoeff hp.out n = a n := by
  rw [← arakiCoeffEquiv_apply p hunit, Equiv.apply_symm_apply]

end TauCeti

namespace FormalGroup

variable {R : Type*} [CommRing R] {p : ℕ} [hp : Fact p.Prime]

/-- **A `p`-typical law is determined by its Araki coefficients.** If every prime `q ≠ p` is
invertible in `R`, two commutative `p`-typical laws over `R` with the same Araki coefficients
`a₁, a₂, …` are equal. -/
theorem IsPTypical.eq_of_arakiCoeff_eq (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))
    {F G : FormalGroup R} [F.IsComm] [G.IsComm] (hF : F.IsPTypical p) (hG : G.IsPTypical p)
    (h : ∀ n : ℕ+, F.arakiCoeff hp.out n = G.arakiCoeff hp.out n) : F = G := by
  have := (TauCeti.arakiCoeffEquiv p hunit).injective
    (a₁ := ⟨F, inferInstance, hF⟩) (a₂ := ⟨G, inferInstance, hG⟩) (funext h)
  exact congrArg Subtype.val this

end FormalGroup

namespace TauCeti

variable {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime]

/-! ### Araki's generators as polynomial generators -/

section Polynomial

variable (hS : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : MvPolynomial ℕ+ R))

/-- Evaluation at the Araki coefficients `e X` of the generators `X` is a left inverse of
evaluation at the parameters `e⁻¹ X` with Araki coefficients `X`. -/
private theorem aeval_arakiParamEquiv_comp_aeval_symm :
    (MvPolynomial.aeval (arakiParamEquiv p hS MvPolynomial.X)).comp
        (MvPolynomial.aeval ((arakiParamEquiv p hS).symm MvPolynomial.X)) =
      AlgHom.id R (MvPolynomial ℕ+ R) := by
  refine MvPolynomial.algHom_ext fun n ↦ ?_
  set e := arakiParamEquiv p hS
  set X : ℕ+ → MvPolynomial ℕ+ R := MvPolynomial.X
  -- `aeval (e X)` carries the parameters with Araki coefficients `X` to those with Araki
  -- coefficients `aeval (e X) ∘ X = e X`, namely `X`
  have h := map_comp_arakiParamEquiv_symm p hS hS (MvPolynomial.aeval (e X)).toRingHom X
  have hX : (MvPolynomial.aeval (e X)).toRingHom ∘ X = e X :=
    funext fun i ↦ MvPolynomial.aeval_X _ i
  rw [hX, Equiv.symm_apply_apply] at h
  simpa [X] using congrFun h n

/-- Evaluation at the parameters `e⁻¹ X` with Araki coefficients `X` is a left inverse of
evaluation at the Araki coefficients `e X` of the generators `X`. -/
private theorem aeval_arakiParamEquiv_symm_comp_aeval :
    (MvPolynomial.aeval ((arakiParamEquiv p hS).symm MvPolynomial.X)).comp
        (MvPolynomial.aeval (arakiParamEquiv p hS MvPolynomial.X)) =
      AlgHom.id R (MvPolynomial ℕ+ R) := by
  refine MvPolynomial.algHom_ext fun n ↦ ?_
  set e := arakiParamEquiv p hS
  set X : ℕ+ → MvPolynomial ℕ+ R := MvPolynomial.X
  -- `aeval (e⁻¹ X)` carries the Araki coefficients `e X` of `X` to those of `e⁻¹ X`, namely `X`
  have h := map_comp_arakiParamEquiv p hS hS (MvPolynomial.aeval (e.symm X)).toRingHom X
  have hX : (MvPolynomial.aeval (e.symm X)).toRingHom ∘ X = e.symm X :=
    funext fun i ↦ MvPolynomial.aeval_X _ i
  rw [hX, Equiv.apply_symm_apply] at h
  simpa [X] using congrFun h n

end Polynomial

/-- **Araki's generators are free polynomial generators.** If every prime `q ≠ p` is invertible
in `R`, the `R`-algebra endomorphism of `R[v₁, v₂, …]` sending `vₙ` to the Araki coefficient `aₙ`
of Hazewinkel's law `F_v` is an automorphism. For `R = ℤ_(p)` this says that Araki's generators are
polynomial generators of the ring `V = ℤ_(p)[v₁, v₂, …]` of the universal `p`-typical law. -/
def arakiAlgEquiv (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    MvPolynomial ℕ+ R ≃ₐ[R] MvPolynomial ℕ+ R :=
  have hS (q : ℕ) (hq : q.Prime) (hqp : q ≠ p) : IsUnit (q : MvPolynomial ℕ+ R) := by
    simpa using (hunit q hq hqp).map (algebraMap R (MvPolynomial ℕ+ R))
  AlgEquiv.ofAlgHom _ _ (aeval_arakiParamEquiv_comp_aeval_symm p hS)
    (aeval_arakiParamEquiv_symm_comp_aeval p hS)

variable (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))

/-- `arakiAlgEquiv` sends `vₙ` to Araki's generator `aₙ`. -/
@[simp]
theorem arakiAlgEquiv_X (n : ℕ+) :
    arakiAlgEquiv p hunit (.X n) =
      (hazewinkelIntegralFormalGroup p (MvPolynomial.X : ℕ+ → MvPolynomial ℕ+ R)).arakiCoeff
        hp.out n :=
  MvPolynomial.aeval_X _ n

/-- `arakiAlgEquiv` is evaluation at Araki's generators. -/
theorem arakiAlgEquiv_toAlgHom :
    (arakiAlgEquiv p hunit : MvPolynomial ℕ+ R →ₐ[R] MvPolynomial ℕ+ R) =
      MvPolynomial.aeval fun n : ℕ+ ↦
        (hazewinkelIntegralFormalGroup p (MvPolynomial.X : ℕ+ → MvPolynomial ℕ+ R)).arakiCoeff
          hp.out n :=
  MvPolynomial.algHom_ext fun n ↦ by simp

include hunit in
/-- **Araki's generators generate.** If every prime `q ≠ p` is invertible in `R`, the Araki
coefficients `a₁, a₂, …` of Hazewinkel's law generate `R[v₁, v₂, …]` as an `R`-algebra. -/
theorem adjoin_range_arakiCoeff_eq_top :
    Algebra.adjoin R (Set.range fun n : ℕ+ ↦
      (hazewinkelIntegralFormalGroup p (MvPolynomial.X : ℕ+ → MvPolynomial ℕ+ R)).arakiCoeff
        hp.out n) = ⊤ := by
  rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.range_eq_top, ← arakiAlgEquiv_toAlgHom p hunit]
  exact (arakiAlgEquiv p hunit).surjective

include hunit in
/-- **Araki's generators are algebraically independent.** If every prime `q ≠ p` is invertible
in `R`, the Araki coefficients `a₁, a₂, …` of Hazewinkel's law are algebraically independent
over `R`. -/
theorem algebraicIndependent_arakiCoeff :
    AlgebraicIndependent R fun n : ℕ+ ↦
      (hazewinkelIntegralFormalGroup p (MvPolynomial.X : ℕ+ → MvPolynomial ℕ+ R)).arakiCoeff
        hp.out n := by
  rw [algebraicIndependent_iff_injective_aeval, ← arakiAlgEquiv_toAlgHom p hunit]
  exact (arakiAlgEquiv p hunit).injective

end TauCeti
