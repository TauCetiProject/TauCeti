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
import TauCeti.RingTheory.FormalGroup.Hazewinkel.Araki

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

The key computation, in `TauCeti.RingTheory.FormalGroup.Hazewinkel.Araki`, is that `aₙ` is
triangular in `v` with unit leading coefficient: if `v` and `w` agree below `n`, then
`aₙ(F_v) - aₙ(F_w) = (1 - p ^ (p ^ n - 1)) (vₙ - wₙ)`
(`TauCeti.arakiCoeff_hazewinkelIntegralFormalGroup_sub`). For `n = 1` it says
`a₁ = (1 - p ^ (p - 1)) v₁`.

The factor `1 - p ^ (p ^ n - 1)` is prime to `p`, hence a unit when every prime `q ≠ p` is
(`TauCeti.isUnit_one_sub_natCast_pow`). Then
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

* `TauCeti.bijective_arakiCoeff_hazewinkelIntegralFormalGroup`: Hazewinkel's parameters and
  Araki's coefficients determine each other.
* `FormalGroup.IsPTypical.eq_of_arakiCoeff_eq`: a `p`-typical law is determined by its Araki
  coefficients.
* `TauCeti.adjoin_range_arakiCoeff_eq_top`, `TauCeti.algebraicIndependent_arakiCoeff`: Araki's
  generators are free polynomial generators.
* `TauCeti.arakiCoeff_hazewinkelIntegralFormalGroup_arakiAlgEquiv_symm_X`: Hazewinkel's generators
  written in Araki's.

## References

* S. Araki, *Typical Formal Groups in Complex Cobordism and K-Theory*, Lectures in Mathematics,
  Kyoto University 6, Kinokuniya (1973).
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres* (1986), (A2.2.1),
  (A2.2.2) and Theorem A2.2.3.
-/

public section

noncomputable section

namespace TauCeti

variable {R : Type*} [CommRing R] {p : ℕ} [hp : Fact p.Prime]

/-! ### Araki's generators classify `p`-typical laws -/

variable (p) in
/-- **Hazewinkel's parameters and Araki's coefficients determine each other.** If every prime
`q ≠ p` is invertible in `R`, then `v ↦ (a₁(F_v), a₂(F_v), …)` is a bijection of families. -/
theorem bijective_arakiCoeff_hazewinkelIntegralFormalGroup
    (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R)) :
    Function.Bijective fun (v : ℕ+ → R) (n : ℕ+) ↦
      (hazewinkelIntegralFormalGroup p v).arakiCoeff hp.out n := by
  set α := fun (v : ℕ+ → R) (n : ℕ+) ↦ (hazewinkelIntegralFormalGroup p v).arakiCoeff hp.out n
  have hu (n : ℕ+) : IsUnit (1 - (p : R) ^ (p ^ (n : ℕ) - 1)) :=
    isUnit_one_sub_natCast_pow hp.out.one_lt
      (by have := Nat.one_lt_pow n.ne_zero hp.out.one_lt; omega) hunit
  refine ⟨fun v w hvw ↦ funext fun n ↦ ?_, fun a ↦ ?_⟩
  · -- `vₙ = wₙ` by induction: `0 = aₙ(F_v) - aₙ(F_w) = (1 - p ^ (p ^ n - 1)) (vₙ - wₙ)`
    induction n using PNat.strongInductionOn with
    | _ n ih =>
      have e := arakiCoeff_hazewinkelIntegralFormalGroup_sub (p := p) ih
      have hvwn := congrFun hvw n
      simp only [α] at hvwn
      rw [hvwn, sub_self, eq_comm, (hu n).mul_right_eq_zero, sub_eq_zero] at e
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
        have hVN : V (N + 1) N.succPNat = V N N.succPNat +
            ↑(hu N.succPNat).unit⁻¹ * (a N.succPNat - α (V N) N.succPNat) := by
          rw [hV N, Function.update_self]
        rw [hVN] at e
        linear_combination e + (a N.succPNat - α (V N) N.succPNat) * (hu N.succPNat).mul_val_inv
  refine ⟨fun n ↦ V n n, funext fun n ↦ ?_⟩
  rw [← hα n n le_rfl]
  exact arakiCoeff_hazewinkelIntegralFormalGroup_congr fun i hi ↦ (hstab n i hi).symm

variable (p) (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))

/-- The bijection sending Hazewinkel parameters `v` to the Araki coefficients `(aₙ(F_v))ₙ`; its
inverse gives the parameters with prescribed Araki coefficients. -/
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
  ((hazewinkelLift p hunit).trans MvPolynomial.homEquiv).trans (arakiParamEquiv p hunit)

/-- `arakiCoeffEquiv` sends a law to its family of Araki coefficients. -/
@[simp]
theorem arakiCoeffEquiv_apply (F : {F : FormalGroup R // ∃ (_ : F.IsComm), F.IsPTypical p})
    (n : ℕ+) : arakiCoeffEquiv p hunit F n = F.val.arakiCoeff hp.out n := by
  -- `MvPolynomial.homEquiv` sends `f` to `f ∘ X` by definition; Mathlib has no apply lemma for it
  have hhom : MvPolynomial.homEquiv (hazewinkelLift p hunit F) =
      hazewinkelLift p hunit F ∘ MvPolynomial.X := rfl
  rw [arakiCoeffEquiv, Equiv.trans_apply, Equiv.trans_apply, arakiParamEquiv_apply, hhom,
    hazewinkelIntegralFormalGroup_hazewinkelLift_comp_X]

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
    (a₁ := ⟨F, inferInstance, hF⟩) (a₂ := ⟨G, inferInstance, hG⟩)
    (funext fun n ↦ by simpa using h n)
  exact congrArg Subtype.val this

end FormalGroup

namespace TauCeti

variable {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime]

/-! ### Araki's generators as polynomial generators -/

section Polynomial

omit hp in
/-- If every prime `q ≠ p` is invertible in `R`, the same holds in `R[v₁, v₂, …]`. -/
private theorem isUnit_natCast_mvPolynomial (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))
    (q : ℕ) (hq : q.Prime) (hqp : q ≠ p) : IsUnit (q : MvPolynomial ℕ+ R) := by
  simpa using (hunit q hq hqp).map (algebraMap R (MvPolynomial ℕ+ R))

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
  AlgEquiv.ofAlgHom _ _
    (aeval_arakiParamEquiv_comp_aeval_symm p (isUnit_natCast_mvPolynomial p hunit))
    (aeval_arakiParamEquiv_symm_comp_aeval p (isUnit_natCast_mvPolynomial p hunit))

variable (hunit : ∀ q : ℕ, q.Prime → q ≠ p → IsUnit (q : R))

/-- `arakiAlgEquiv` is evaluation at Araki's generators. -/
theorem arakiAlgEquiv_toAlgHom :
    (arakiAlgEquiv p hunit : MvPolynomial ℕ+ R →ₐ[R] MvPolynomial ℕ+ R) =
      MvPolynomial.aeval fun n : ℕ+ ↦
        (hazewinkelIntegralFormalGroup p (MvPolynomial.X : ℕ+ → MvPolynomial ℕ+ R)).arakiCoeff
          hp.out n := by
  rw [arakiAlgEquiv, AlgEquiv.toAlgHom_ofAlgHom]
  exact congrArg MvPolynomial.aeval (funext (arakiParamEquiv_apply p _ _))

/-- `arakiAlgEquiv` sends `vₙ` to Araki's generator `aₙ`. -/
@[simp]
theorem arakiAlgEquiv_X (n : ℕ+) :
    arakiAlgEquiv p hunit (.X n) =
      (hazewinkelIntegralFormalGroup p (MvPolynomial.X : ℕ+ → MvPolynomial ℕ+ R)).arakiCoeff
        hp.out n := by
  rw [← AlgEquiv.coe_toAlgHom, arakiAlgEquiv_toAlgHom, MvPolynomial.aeval_X]

/-- The inverse of `arakiAlgEquiv` writes Hazewinkel's generators in Araki's: at the images of the
generators under it, Hazewinkel's law has Araki coefficients `vₙ`. -/
@[simp]
theorem arakiCoeff_hazewinkelIntegralFormalGroup_arakiAlgEquiv_symm_X (n : ℕ+) :
    (hazewinkelIntegralFormalGroup p fun i ↦ (arakiAlgEquiv p hunit).symm (.X i)).arakiCoeff
      hp.out n = .X n := by
  have hS := isUnit_natCast_mvPolynomial p hunit
  have hsymm : (fun i ↦ (arakiAlgEquiv p hunit).symm (.X i)) =
      (arakiParamEquiv p hS).symm MvPolynomial.X := by
    funext i
    rw [arakiAlgEquiv, AlgEquiv.ofAlgHom_symm, ← AlgEquiv.coe_toAlgHom,
      AlgEquiv.toAlgHom_ofAlgHom, MvPolynomial.aeval_X]
  rw [hsymm, ← arakiParamEquiv_apply p hS, Equiv.apply_symm_apply]

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
