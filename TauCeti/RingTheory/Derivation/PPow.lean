/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Data.Nat.Choose.Dvd
public import Mathlib.RingTheory.Derivation.Lie
public import TauCeti.Algebra.CharP.LinearMaps
public import TauCeti.Algebra.Lie.AdjointAction.Frobenius
public import TauCeti.Algebra.Lie.Basic
public import TauCeti.Algebra.Lie.Restricted.Basic
public import TauCeti.RingTheory.Derivation.Basic
public import TauCeti.RingTheory.Derivation.BaseChange
public import TauCeti.RingTheory.Derivation.Lie
public import TauCeti.RingTheory.Derivation.Localization
public import TauCeti.RingTheory.Kaehler.DualDerivation
-- Non-public: `TauCeti.Algebra.CharP.Lemmas`, `TauCeti.Algebra.Polynomial.Derivative`, and
-- `TauCeti.RingTheory.Derivation.MapCoeffs` support Hochschild's formula; `FirstOrder` supports
-- unit conjugation.
import TauCeti.Algebra.CharP.Lemmas
import TauCeti.Algebra.Polynomial.Derivative
import TauCeti.RingTheory.Derivation.FirstOrder
import TauCeti.RingTheory.Derivation.MapCoeffs

/-!
# The `p`-th power of a derivation

Let `A` be a commutative `R`-algebra of exponential characteristic `p`. The `p`-th iterate
`D^[p]` of an `R`-derivation `D` of `A` is again a derivation: by the general Leibniz rule,
`D^[p] (a * b)` is the sum of `(p choose i) • D^[i] a * D^[p - i] b`, and every binomial
coefficient with `0 < i < p` vanishes in `A`. This file packages `D^[p]` as the derivation
`D.pPow p`. It is not a power in `Derivation R A A`, which carries no multiplication, but its
underlying endomorphism is the power `(D : Module.End R A) ^ p`.

In characteristic `0` the iterate is not a derivation: on `ℚ[x]`, `(d/dx)^[2] (x * x) = 2`, while
the Leibniz rule would give `0`. (Exponential characteristic `1` is characteristic `0`, where
`D.pPow 1 = D`.) On `𝔽_p[x]` the operation is not `A`-linear in `D`: it kills
`d/dx` but fixes `x • d/dx` (`pPow_derivative'` and `pPow_X_smul_derivative'`). More generally, in
prime characteristic `p` over any commutative semiring `A` (no additive inverses are needed),
multiplication by `a : A` satisfies **Hochschild's formula** (`Derivation.pPow_smul`):
`(a • D).pPow p = a ^ p • D.pPow p + ((a • D)^[p - 1] a) • D`, which follows from the vanishing
of the middle coefficients `smulIterCoeff D a p k`, `2 ≤ k < p`, of the expansion
`(a • D)^[p] = ∑ smulIterCoeff D a p k * D^[k]` (`smulIterCoeff_eq_zero_of_mem_Ico`). For
`p = 1`, the scaling identity `(a • D).pPow 1 = a ^ 1 • D.pPow 1` follows directly from
`pPow 1 = D` (`Derivation.pPow_smul_of_apply_eq_zero`).

The `p`-th power is the `p`-map making `Derivation R A A` a restricted Lie algebra in the sense of
Jacobson, and it is the correction term in the `p`-curvature `(∇_D)^p - ∇_{D^[p]}` of a connection
(Katz). This file proves its homogeneity for scalars of `R`, Hochschild's formula for scalars of
`A`, the identity `ad (D^[p]) = (ad D)^p` in the Lie algebra of derivations, Jacobson's formula
`(D + E)^[p] = D^[p] + E^[p] + Λ_p(D, E)`, which together make `Derivation R A A` a restricted Lie
algebra whose inclusion into `Module.End R A` is a restricted morphism, its compatibility with
scalar extension and with localization, its vanishing on the derivations dual to a basis of exact
Kähler differentials, and its compatibility with conjugation by a unit `u`: the `p`-th power of
the operator `D - u⁻¹ D(u)` is the operator `D^[p] - u⁻¹ D^[p](u)` built in the same way from
`D^[p]`. In the language of connections, the rank-one connection `d - du/u` on `A`, whose
horizontal section is `u`, has vanishing `p`-curvature.

## Main declarations

* `Derivation.iterate_leibniz`: in exponential characteristic `p`, the `p`-th iterate of a
  derivation satisfies the Leibniz rule.
* `Derivation.pPow`: the `p`-th power of a derivation, as a derivation.
* `Derivation.pPow_const_smul`: `(c • D)^[p] = c ^ p • D^[p]` for `c : R`.
* `Derivation.smulIterCoeff_eq_zero_of_mem_Ico`: the middle coefficients of the expansion of
  `(a • D)^[p]` vanish in prime characteristic `p` over any commutative semiring `A`.
* `Derivation.pPow_smul`: Hochschild's formula for `(a • D)^[p]`, `a : A`.
* `Derivation.pPow_smul_of_apply_eq_zero`: `(a • D).pPow p = a ^ p • D.pPow p` when `D a = 0`.
* `Derivation.ad_pPow`: `ad (D^[p]) = (ad D) ^ p` in the Lie algebra `Derivation R A A`.
* `Derivation.pPow_add`: Jacobson's formula `(D + E)^[p] = D^[p] + E^[p] + Λ_p(D, E)`.
* `Derivation.instRestrictedLieAlgebra`: `Derivation R A A` is a restricted Lie algebra under
  `pPow`.
* `Derivation.toLinearMapRestrictedLieHom`: the inclusion into `Module.End R A`, with its
  restricted structure `f ↦ f ^ p`, is a restricted morphism.
* `Derivation.pPow_baseChange`: `pPow` commutes with scalar extension `S ⊗[R] -`.
* `Derivation.pPow_extendOfIsLocalization`: `pPow` commutes with extension to a localization.
* `Derivation.pPow_dualDerivation_eq_zero`: the `p`-th powers of the derivations dual to a basis
  `ds_i` of `Ω[A⁄R]` vanish.
* `Derivation.sub_mulLeft_inv_mul_pow_expChar`: `(D - u⁻¹ D(u)) ^ p = D^[p] - u⁻¹ D^[p](u)` in
  `Module.End R A`, for a unit `u`.

## Implementation notes

Expanding `(a • D)^[p] = ∑ k ≤ p, smulIterCoeff D a p k • D^[k]`, Hochschild's formula says that
the coefficients for `2 ≤ k < p` vanish. These coefficients are natural along ring homomorphisms
intertwining the derivations (`map_smulIterCoeff`), so it suffices to prove their vanishing after
lifting `D` to `D.mapCoeffsToPolynomial + d/dX` on `A[X]`. There `(C a • D')^[p]` is a derivation,
so its constant term at `X ^ k` (`2 ≤ k < p`) vanishes by the Leibniz rule, while the expansion
gives `smulIterCoeff D a p k * k !`, and `k !` is a unit in `A` for `k < p`.

## References

* G. Hochschild, *Simple algebras with purely inseparable splitting fields of exponent 1*,
  Trans. Amer. Math. Soc. **79** (1955), 477--489.
* N. Jacobson, *Abstract derivation and Lie algebras*, Trans. Amer. Math. Soc. **42** (1937),
  206--224.
* N. M. Katz, *Nilpotent connections and the monodromy theorem: applications of a result of
  Turrittin*, Publ. Math. IHÉS **39** (1970), 175--232, §5.0 and Proposition 5.3.
-/

public section

open TensorProduct

namespace Derivation

section CommSemiring

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- **The Leibniz rule for the `p`-th iterate.** In exponential characteristic `p`, the `p`-th
iterate of a derivation `D` satisfies `D^[p] (a * b) = a * D^[p] b + b * D^[p] a`. -/
theorem iterate_leibniz (p : ℕ) [hp : ExpChar A p] (D : Derivation R A A) (a b : A) :
    D^[p] (a * b) = a * D^[p] b + b * D^[p] a := by
  obtain _ | ⟨hp⟩ := hp
  · simp [leibniz]
  rw [iterate_apply_mul, Finset.sum_eq_add (0, p) (p, 0) (by simp [hp.ne_zero])]
  · simp [mul_comm, add_comm]
  · rintro ⟨i, j⟩ hij ⟨h0, hp'⟩
    rw [Finset.mem_antidiagonal] at hij
    have hi : i ≠ 0 := by rintro rfl; simp_all
    have hi' : i < p := by
      refine lt_of_le_of_ne (by omega) ?_
      rintro rfl
      exact hp' (by simp_all)
    simp [nsmul_eq_mul, (CharP.cast_eq_zero_iff A p _).mpr
      (Nat.Prime.dvd_choose_self hp hi hi')]
  · simp
  · simp

variable (p : ℕ) [ExpChar A p]

/-- **The `p`-th power of a derivation.** In exponential characteristic `p`, the `p`-th iterate
`D^[p]` of a derivation `D` is a derivation (`iterate_leibniz`). Its underlying endomorphism is
`(D : Module.End R A) ^ p` (`toLinearMap_pPow`). -/
def pPow (D : Derivation R A A) : Derivation R A A where
  toLinearMap := (D : Module.End R A) ^ p
  map_one_eq_zero' :=
    Module.End.pow_map_zero_of_le (Nat.one_le_iff_ne_zero.mpr (expChar_ne_zero A p)) (by simp)
  leibniz' a b := by
    simpa [pow_apply_eq_iterate, smul_eq_mul] using iterate_leibniz p D a b

/-- The `p`-th power of `D` evaluates as the `p`-th iterate of `D`. -/
@[simp]
theorem pPow_apply (D : Derivation R A A) (a : A) : D.pPow p a = D^[p] a := by
  simp [pPow, pow_apply_eq_iterate]

/-- The underlying endomorphism of the `p`-th power of `D` is the `p`-th power of that of `D`. -/
@[simp]
theorem toLinearMap_pPow (D : Derivation R A A) :
    (D.pPow p : Module.End R A) = (D : Module.End R A) ^ p :=
  LinearMap.ext fun a ↦ by simp [pow_apply_eq_iterate]

/-- An element killed by `D` is killed by the `p`-th power of `D`. -/
theorem pPow_apply_eq_zero_of_apply_eq_zero (D : Derivation R A A) {a : A} (h : D a = 0) :
    D.pPow p a = 0 :=
  Module.End.pow_map_zero_of_le (Nat.one_le_iff_ne_zero.mpr (expChar_ne_zero A p)) (by simpa)

/-- If `p ≠ 1`, so that `p` is a prime, an element killed by `D ∘ D` is killed by the `p`-th
power of `D`. -/
theorem pPow_apply_eq_zero_of_apply_apply_eq_zero (hp : p ≠ 1) (D : Derivation R A A) {a : A}
    (h : D (D a) = 0) : D.pPow p a = 0 :=
  Module.End.pow_map_zero_of_le (k := 2) (by have := expChar_ne_zero A p; omega)
    (by simpa [sq] using h)

/-- The `p`-th power of the zero derivation is zero. -/
@[simp]
theorem pPow_zero : (0 : Derivation R A A).pPow p = 0 := by
  ext a
  exact pPow_apply_eq_zero_of_apply_eq_zero p 0 (zero_apply a)

/-- **Homogeneity of the `p`-th power for constant scalars.** For `c : R`,
`(c • D)^[p] = c ^ p • D^[p]`. -/
theorem pPow_const_smul (c : R) (D : Derivation R A A) :
    (c • D).pPow p = c ^ p • D.pPow p := by
  ext a
  rw [pPow_apply, iterate_smul_apply, smul_apply, pPow_apply]

/-- **The `p`-th power commutes with scalar extension.** Extending `D^[p]` from `A` to
`S ⊗[R] A` gives the `p`-th power of the extension of `D`. -/
theorem pPow_baseChange (S : Type*) [CommSemiring S] [Algebra R S] [ExpChar (S ⊗[R] A) p]
    (D : Derivation R A A) : (D.baseChange S).pPow p = (D.pPow p).baseChange S := by
  ext a
  have h : Function.Semiconj (fun x : A ↦ (1 : S) ⊗ₜ[R] x) D (D.baseChange S) :=
    fun x ↦ (baseChange_tmul D 1 x).symm
  simp [(h.iterate_right p a).symm]

section Hochschild

open Polynomial
open scoped Nat

private lemma mapCoeffs_add_derivative_iterate_X_pow (D : Derivation R A A) (m k : ℕ) :
    (⇑(D.mapCoeffsToPolynomial + (Polynomial.derivative' (R := A)).restrictScalars R))^[k]
        (Polynomial.X ^ m : A[X]) =
      Polynomial.derivative^[k] (Polynomial.X ^ m : A[X]) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    have hcoeff :
        D.mapCoeffsToPolynomial (Polynomial.derivative^[k] (Polynomial.X ^ m : A[X])) = 0 := by
      ext n
      rw [Polynomial.iterate_derivative_X_pow_eq_C_mul, coeff_mapCoeffsToPolynomial,
        Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_zero]
      split_ifs <;> simp
    simp [hcoeff]

private lemma coeff_zero_iterate_derivative_X_pow (m k : ℕ) :
    (Polynomial.derivative^[k] (Polynomial.X ^ m : A[X])).coeff 0 =
      if k = m then (m ! : A) else 0 := by
  rw [Polynomial.iterate_derivative_X_pow_eq_C_mul, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  rcases lt_trichotomy k m with hlt | rfl | hgt
  · have : 0 ≠ m - k := by omega
    simp [this, hlt.ne]
  · simp [Nat.descFactorial_self]
  · simp [Nat.descFactorial_of_lt hgt, hgt.ne']

/-- In prime characteristic `p`, the middle coefficients `smulIterCoeff D b p k` (`2 ≤ k < p`)
of the expansion `(b • D)^[p] = ∑ k ≤ p, smulIterCoeff D b p k * D^[k]` vanish, over any
commutative semiring `A`. -/
theorem smulIterCoeff_eq_zero_of_mem_Ico (p : ℕ) [Fact p.Prime] [CharP A p]
    (D : Derivation R A A) (b : A) {k : ℕ} (hk : k ∈ Finset.Ico 2 p) :
    smulIterCoeff D b p k = 0 := by
  -- Lift `D` to `D' = D.mapCoeffsToPolynomial + d/dX` on `A[X]`, and compute the constant
  -- coefficient of `((C b • D').pPow p) (X ^ k)` in two ways: by the Leibniz rule it vanishes
  -- (since `2 ≤ k`), while `iterate_smul_apply_eq_sum` and `map_smulIterCoeff` isolate
  -- `smulIterCoeff D b p k * k!`; finally cancel the unit `k!`.
  let D' : Derivation R A[X] A[X] :=
    D.mapCoeffsToPolynomial + (Polynomial.derivative' (R := A)).restrictScalars R
  have hD'C (x : A) : D' (Polynomial.C x) = Polynomial.C (D x) := by
    simp [D']
  let E : Derivation R A[X] A[X] := (Polynomial.C b • D').pPow p
  have hk2 : 2 ≤ k := (Finset.mem_Ico.mp hk).1
  have hkp : k < p := (Finset.mem_Ico.mp hk).2
  have hlhs : (E (Polynomial.X ^ k : A[X])).coeff 0 = 0 := by
    have hk1 : k - 1 = (k - 2) + 1 := by omega
    rw [E.leibniz_pow, hk1, pow_succ']
    simp [mul_assoc, Polynomial.mul_coeff_zero]
  have hrhs : (E (Polynomial.X ^ k : A[X])).coeff 0 = smulIterCoeff D b p k * (k ! : A) := by
    dsimp only [E]
    rw [pPow_apply, iterate_smul_apply_eq_sum D' (Polynomial.C b) (Polynomial.X ^ k) p,
      Polynomial.finsetSum_coeff]
    have hD'X (j : ℕ) : (⇑D')^[j] (Polynomial.X ^ k : A[X]) =
        Polynomial.derivative^[j] (Polynomial.X ^ k : A[X]) :=
      mapCoeffs_add_derivative_iterate_X_pow D k j
    have hcoeff (j : ℕ) :
        smulIterCoeff D' (Polynomial.C b) p j = Polynomial.C (smulIterCoeff D b p j) :=
      (map_smulIterCoeff Polynomial.C D D' (fun x ↦ (hD'C x).symm) b p j).symm
    simp [hD'X, hcoeff, coeff_zero_iterate_derivative_X_pow,
      Finset.mem_range.mpr (Nat.lt_succ_of_lt hkp)]
  exact (TauCeti.isUnit_natCast_factorial_of_lt p hkp).mul_left_inj.mp
    (by rw [hrhs.symm.trans hlhs, zero_mul])

/-- **Hochschild's formula** (Hochschild 1955; Katz, Proposition 5.3, due to Deligne): for an
algebra element `a : A` and a derivation `D : Derivation R A A` in prime characteristic `p` over any
commutative semiring `A`, `(a • D).pPow p = a ^ p • D.pPow p + ((a • D)^[p - 1] a) • D`. -/
theorem pPow_smul (p : ℕ) [Fact p.Prime] [CharP A p] (a : A) (D : Derivation R A A) :
    (a • D).pPow p = a ^ p • D.pPow p + ((a • D)^[p - 1] a) • D := by
  have hp : p.Prime := Fact.out
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.sub_add_cancel hp.one_le).symm⟩
  ext b
  rw [pPow_apply, add_apply, smul_apply, smul_apply, pPow_apply, smul_eq_mul, smul_eq_mul,
    iterate_smul_apply_eq_sum D a b (q + 1), Finset.sum_range_succ, smulIterCoeff_self, add_comm]
  congr 1
  rw [Finset.sum_eq_single_of_mem 1 (Finset.mem_range.mpr hp.one_lt)]
  · rw [Function.iterate_one, smulIterCoeff_succ_one, Nat.add_sub_cancel]
  · intro k hk hk1
    rcases eq_or_ne k 0 with rfl | hk0
    · rw [smulIterCoeff_succ_zero, zero_mul]
    · rw [smulIterCoeff_eq_zero_of_mem_Ico (q + 1) D a
        (Finset.mem_Ico.mpr ⟨by omega, Finset.mem_range.mp hk⟩), zero_mul]

/-- In exponential characteristic `p`, if `D a = 0`, then `(a • D).pPow p = a ^ p • D.pPow p`:
in prime characteristic `p`, Hochschild's correction term vanishes; at `p = 1`, this follows from
`pPow 1 = D`. -/
theorem pPow_smul_of_apply_eq_zero (D : Derivation R A A) (p : ℕ) [hp : ExpChar A p]
    {a : A} (ha : D a = 0) :
    (a • D).pPow p = a ^ p • D.pPow p := by
  obtain _ | ⟨hp'⟩ := hp
  · ext b
    simp
  · have : Fact p.Prime := ⟨hp'⟩
    have hcorr : (⇑(a • D))^[p - 1] a = 0 := by
      have h1 : p - 1 = (p - 2) + 1 := by
        have := hp'.two_le
        omega
      rw [h1, Function.iterate_succ_apply, smul_apply, ha, smul_zero,
        Function.iterate_fixed (map_zero (a • D))]
    rw [pPow_smul p a D, hcorr, zero_smul, add_zero]

end Hochschild

end CommSemiring

section CommRing

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (p : ℕ) [ExpChar A p]

/-- **The `p`-th power and the adjoint action.** In the Lie algebra of derivations,
`ad (D^[p]) = (ad D) ^ p`, that is, `⁅D^[p], E⁆` is the `p`-fold iterated bracket of `D`
with `E`. -/
theorem ad_pPow (D : Derivation R A A) :
    LieAlgebra.ad R (Derivation R A A) (D.pPow p) = LieAlgebra.ad R (Derivation R A A) D ^ p := by
  ext E : 1
  apply toLinearMapLieHom_injective
  simpa [LieHom.map_ad_pow] using
    congr($(TauCeti.LieAlgebra.ad_pow_expChar_pow (R := R) p (toLinearMapLieHom R A D) 1)
      (toLinearMapLieHom R A E))

/-- **Jacobson's formula for derivations.** `(D + E)^[p] = D^[p] + E^[p] + Λ_p(D, E)`, where
`Λ_p` is Jacobson's Lie polynomial evaluated in the Lie algebra of derivations. -/
theorem pPow_add (D E : Derivation R A A) :
    (D + E).pPow p = D.pPow p + E.pPow p + TauCeti.LieAlgebra.jacobson p D E := by
  let := TauCeti.RestrictedLieAlgebra.ofAssociativeAlgebra R (Module.End R A) p
  apply toLinearMapLieHom_injective
  rw [map_add, map_add, LieHom.map_jacobson]
  simpa using TauCeti.RestrictedLieAlgebra.pMap_add (R := R) (p := p) (D : Module.End R A) E

/-- **Derivations form a restricted Lie algebra** (Jacobson; Katz 1970, (5.0)): the `p`-map is the
`p`-th power `D ↦ D^[p]`. -/
instance instRestrictedLieAlgebra : TauCeti.RestrictedLieAlgebra R (Derivation R A A) p where
  pMap D := D.pPow p
  pMap_smul := pPow_const_smul p
  ad_pMap := ad_pPow p
  pMap_add := pPow_add p

/-- The `p`-map of `Derivation R A A` is `pPow`. -/
@[simp]
theorem pMap_eq_pPow (D : Derivation R A A) :
    TauCeti.RestrictedLieAlgebra.pMap R p D = D.pPow p :=
  (rfl)

variable (R A) in
/-- The inclusion of derivations into `Module.End R A` is a morphism of restricted Lie algebras,
for the restricted structure `f ↦ f ^ p` of the associative algebra `Module.End R A`. -/
def toLinearMapRestrictedLieHom :
    letI := TauCeti.RestrictedLieAlgebra.ofAssociativeAlgebra R (Module.End R A) p
    TauCeti.RestrictedLieHom R (Derivation R A A) (Module.End R A) p :=
  letI := TauCeti.RestrictedLieAlgebra.ofAssociativeAlgebra R (Module.End R A) p
  { toLinearMapLieHom R A with map_pMap' D := by simp }

@[simp]
theorem toLinearMapRestrictedLieHom_apply (D : Derivation R A A) :
    letI := TauCeti.RestrictedLieAlgebra.ofAssociativeAlgebra R (Module.End R A) p
    toLinearMapRestrictedLieHom R A p D = (D : Module.End R A) :=
  toLinearMapLieHom_apply D

@[simp]
theorem toLieHom_toLinearMapRestrictedLieHom :
    letI := TauCeti.RestrictedLieAlgebra.ofAssociativeAlgebra R (Module.End R A) p
    (toLinearMapRestrictedLieHom R A p).toLieHom = toLinearMapLieHom R A :=
  (rfl)

theorem toLinearMapRestrictedLieHom_injective :
    letI := TauCeti.RestrictedLieAlgebra.ofAssociativeAlgebra R (Module.End R A) p
    Function.Injective (toLinearMapRestrictedLieHom R A p) :=
  toLinearMapLieHom_injective

/-- **The `p`-th power commutes with localization.** If `T` is a localization of `A`, extending
`D^[p]` from `A` to `T` gives the `p`-th power of the extension of `D`. -/
theorem pPow_extendOfIsLocalization {T : Type*} [CommRing T] [Algebra R T] [Algebra A T]
    [IsScalarTower R A T] [ExpChar T p] (S : Submonoid A) [IsLocalization S T]
    (D : Derivation R A A) :
    (((Algebra.linearMap A T).compDer D).extendOfIsLocalization S).pPow p =
      ((Algebra.linearMap A T).compDer (D.pPow p)).extendOfIsLocalization S := by
  set E : Derivation R T T := ((Algebra.linearMap A T).compDer D).extendOfIsLocalization S
  have h : Function.Semiconj (algebraMap A T) D E := fun a ↦ by
    simp [E, extendOfIsLocalization_algebraMap]
  refine coe_injective (IsLocalization.eq_of_leibniz S (fun x y ↦ leibniz _ x y)
    (fun x y ↦ leibniz _ x y) fun a ↦ ?_)
  simp [extendOfIsLocalization_algebraMap, (h.iterate_right p a).symm, pow_apply_eq_iterate]

end CommRing

/-! ### Conjugation by a unit -/

section Conjugation

variable {R A : Type*} [CommSemiring R] [CommRing A] [Algebra R A] (p : ℕ) [ExpChar A p]

/-- **The `p`-th power of `D - u⁻¹ D(u)`.** For a unit `u`, the `p`-th power of the operator
`D - u⁻¹ D(u)` on `A` is the operator `D^[p] - u⁻¹ D^[p](u)` built in the same way from the
derivation `D^[p]`. Equivalently, the rank-one connection `d - du/u`, whose horizontal section is
`u`, has vanishing `p`-curvature `(∇_D)^p - ∇_{D^[p]}`. -/
theorem sub_mulLeft_inv_mul_pow_expChar (D : Derivation R A A) (u : Aˣ) :
    (D.toLinearMap - LinearMap.mulLeft R (↑u⁻¹ * D u)) ^ p =
      (D.pPow p).toLinearMap - LinearMap.mulLeft R (↑u⁻¹ * D.pPow p u) := by
  rw [sub_mulLeft_inv_mul_pow, ← toLinearMap_pPow, mulLeft_mul_mul_mulLeft_inv]

end Conjugation

/-! ### Derivations dual to a basis of exact differentials -/

section Basis

variable {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- **Coordinate derivations have vanishing `p`-th power.** If `b` is the basis `ds_i` of exact
differentials of `Ω[A⁄R]` and `A` has prime characteristic `p`, the derivation `∂_i` dual to
`ds_i` satisfies `∂_i^[p] = 0`. -/
theorem pPow_dualDerivation_eq_zero {b : Module.Basis ι A Ω[A⁄R]} {s : ι → A}
    (hs : ∀ i, KaehlerDifferential.D R A (s i) = b i) (p : ℕ) [Fact p.Prime] [CharP A p] (i : ι) :
    (b.dualDerivation i).pPow p = 0 :=
  ext_of_kaehlerD_eq_basis hs fun k ↦ pPow_apply_eq_zero_of_apply_apply_eq_zero p
    (Fact.out : p.Prime).ne_one _
    (Module.Basis.dualDerivation_apply_dualDerivation_apply_of_kaehlerD_eq hs i i k)

end Basis

/-! ### The derivative of polynomials -/

section Polynomial

open Polynomial

variable {R : Type*} [CommSemiring R] (p : ℕ)

/-- In characteristic `p`, the `p`-th power of `d/dx` on `R[X]` vanishes. -/
@[simp]
theorem pPow_derivative' [Fact p.Prime] [CharP R p] :
    (derivative' : Derivation R R[X] R[X]).pPow p = 0 := by
  ext : 1
  exact pPow_apply_eq_zero_of_apply_apply_eq_zero p (Fact.out : p.Prime).ne_one _ (by simp)

/-- In exponential characteristic `p`, the derivation `x • d/dx` of `R[X]` is its own `p`-th
power, since it fixes `X`. With `pPow_derivative'`, this shows that in prime characteristic `pPow`
is not linear for the scalars of `R[X]`. -/
@[simp]
theorem pPow_X_smul_derivative' [ExpChar R p] :
    ((X : R[X]) • (derivative' : Derivation R R[X] R[X])).pPow p =
      (X : R[X]) • (derivative' : Derivation R R[X] R[X]) := by
  have hX : ((X : R[X]) • (derivative' : Derivation R R[X] R[X])) X = X := by simp
  ext
  rw [pPow_apply, Function.iterate_fixed hX, hX]

end Polynomial

end Derivation

section Examples

open Polynomial

-- Witness: on `R[X]` in prime characteristic `p`, Hochschild's formula gives
-- `(X • d/dX).pPow p = X • d/dX` (confirming the `+` sign in `Derivation.pPow_smul`).
example (R : Type*) [CommSemiring R] (p : ℕ) [Fact p.Prime] [CharP R p] :
    ((Polynomial.X : R[X]) • Polynomial.derivative' (R := R)).pPow p =
      (Polynomial.X : R[X]) • Polynomial.derivative' (R := R) := by
  have hX : ((Polynomial.X : R[X]) • Polynomial.derivative' (R := R)) Polynomial.X =
      Polynomial.X := by
    simp
  rw [Derivation.pPow_smul, Derivation.pPow_derivative', smul_zero, zero_add,
    Function.iterate_fixed hX]

-- Witness: characteristic `0` counterexample on `ℚ[X]` showing `(d/dX)^[2]` fails the Leibniz
-- rule without `[ExpChar A p]`.
example :
    (Polynomial.derivative' (R := ℚ))^[2] ((Polynomial.X : ℚ[X]) * Polynomial.X) ≠
      (Polynomial.X : ℚ[X]) * (Polynomial.derivative' (R := ℚ))^[2] Polynomial.X +
        (Polynomial.X : ℚ[X]) * (Polynomial.derivative' (R := ℚ))^[2] Polynomial.X := by
  intro h
  have h0 := congrArg (Polynomial.eval 0) h
  simp [Polynomial.coe_derivative', Function.iterate_succ_apply'] at h0

-- Witness: `Derivation.pPow_add` also holds in exponential characteristic `1` (characteristic `0`).
example (D E : Derivation ℚ ℚ[X] ℚ[X]) :
    (D + E).pPow 1 = D.pPow 1 + E.pPow 1 := by
  rw [Derivation.pPow_add, TauCeti.LieAlgebra.jacobson_one, add_zero]

end Examples
