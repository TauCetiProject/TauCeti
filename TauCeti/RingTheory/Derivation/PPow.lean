/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Factorial.NatCast
import Mathlib.RingTheory.Derivation.MapCoeffs
public import Mathlib.RingTheory.Derivation.Lie
public import TauCeti.Algebra.Lie.AdjointAction.Frobenius
public import TauCeti.Algebra.Lie.Basic
public import TauCeti.Algebra.Lie.Restricted.Basic
public import TauCeti.RingTheory.Derivation.Basic
public import TauCeti.RingTheory.Derivation.BaseChange
public import TauCeti.RingTheory.Derivation.Localization
public import TauCeti.RingTheory.Kaehler.DualDerivation
-- `Module.End.instExpChar` and `Derivation.toLinearMapLieHom` carry `ad_pPow` and `pPow_add` into
-- the associative algebra `Module.End R A`; both appear in `toLinearMapRestrictedLieHom`.
public import TauCeti.Algebra.CharP.LinearMaps
public import TauCeti.RingTheory.Derivation.Lie
import TauCeti.RingTheory.Derivation.FirstOrder

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
`d/dx` but fixes `x • d/dx` (`pPow_derivative'` and `pPow_X_smul_derivative'`).

The `p`-th power is the `p`-map making `Derivation R A A` a restricted Lie algebra in the sense of
Jacobson, and it is the correction term in the `p`-curvature `(∇_D)^p - ∇_{D^[p]}` of a connection
(Katz). This file proves its homogeneity for scalars of `R`, the identity `ad (D^[p]) = (ad D)^p`
in the Lie algebra of derivations, Jacobson's formula
`(D + E)^[p] = D^[p] + E^[p] + Λ_p(D, E)`, which together make `Derivation R A A` a restricted Lie
algebra whose inclusion into `Module.End R A` is a restricted morphism, its compatibility with
scalar extension and with localization,
its vanishing on the derivations dual to a basis of exact Kähler differentials, and its
compatibility with conjugation by a unit `u`: the `p`-th power of the operator `D - u⁻¹ D(u)` is
the operator `D^[p] - u⁻¹ D^[p](u)` built in the same way from `D^[p]`. In the language of
connections, the rank-one connection `d - du/u` on `A`, whose horizontal section is `u`, has
vanishing `p`-curvature.

On multiples `a • D` by elements `a : A`, the `p`-th power obeys Hochschild's formula
`(a • D)^[p] = a ^ p • D^[p] + (a • D)^[p - 1] a • D` (`pPow_smul`), which underlies the
`p`-linearity `ψ(a • D) = a ^ p • ψ(D)` of the `p`-curvature. It follows from the vanishing of
the middle coefficients `c p k`, `2 ≤ k < p`, of the expansion `(a • D)^[p] = ∑ c p k * D^[k]`
(`smulIterCoeff_eq_zero_of_mem_Ico`).

## Main declarations

* `Derivation.iterate_leibniz`: in exponential characteristic `p`, the `p`-th iterate of a
  derivation satisfies the Leibniz rule.
* `Derivation.pPow`: the `p`-th power of a derivation, as a derivation.
* `Derivation.pPow_const_smul`: `(c • D)^[p] = c ^ p • D^[p]` for `c : R`.
* `Derivation.ad_pPow`: `ad (D^[p]) = (ad D) ^ p` in the Lie algebra `Derivation R A A`.
* `Derivation.pPow_add`: Jacobson's formula `(D + E)^[p] = D^[p] + E^[p] + Λ_p(D, E)`.
* `Derivation.instRestrictedLieAlgebra`: `Derivation R A A` is a restricted Lie algebra under
  `pPow`.
* `Derivation.toLinearMapRestrictedLieHom`: the inclusion into `Module.End R A`, with its
  restricted structure `f ↦ f ^ p`, is a restricted morphism.
* `Derivation.smulIterCoeff_eq_zero_of_mem_Ico`: the middle coefficients of the expansion of
  `(a • D)^[p]` vanish.
* `Derivation.pPow_smul`: Hochschild's formula for `(a • D)^[p]`, `a : A`.
* `Derivation.pPow_baseChange`: `pPow` commutes with scalar extension `S ⊗[R] -`.
* `Derivation.pPow_extendOfIsLocalization`: `pPow` commutes with extension to a localization.
* `Derivation.pPow_dualDerivation_eq_zero`: the `p`-th powers of the derivations dual to a basis
  `ds_i` of `Ω[A⁄R]` vanish.
* `Derivation.sub_mulLeft_inv_mul_pow_expChar`: `(D - u⁻¹ D(u)) ^ p = D^[p] - u⁻¹ D^[p](u)` in
  `Module.End R A`, for a unit `u`.

## Implementation notes

Expanding `(a • D)^[p] = ∑ k ≤ p, c k • D^[k]` with coefficients `c k` computed from `a` and `D`,
Hochschild's formula says that the coefficients `c k` with `2 ≤ k < p` vanish. These coefficients
are natural along ring homomorphisms that intertwine the derivations (`map_smulIterCoeff`), so it
suffices to show that they vanish after extending `D` to `A[X]` by `X ↦ 1`. There the operator
`∑ 2 ≤ k < p, c k • D^[k]` is a derivation killing `X`, so it kills every `X ^ k`, while its value
at `X ^ k` is `k ! • c k` once the lower coefficients vanish.

## References

* N. Jacobson, *Abstract derivation and Lie algebras*, Trans. Amer. Math. Soc. **42** (1937),
  206--224.
* N. M. Katz, *Nilpotent connections and the monodromy theorem: applications of a result of
  Turrittin*, Publ. Math. IHÉS **39** (1970), 175--232, §5.0 and Proposition 5.3.
* G. Hochschild, *Simple algebras with purely inseparable splitting fields of exponent 1*,
  Trans. Amer. Math. Soc. **79** (1955), 477--489.
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

/-! ### Hochschild's formula -/

section Hochschild

variable {R A : Type*} [CommSemiring R] [CommRing A] [Algebra R A]

/-- The expansion `iterate_smul_apply_eq_sum` for `n ≥ 2`, with its extreme coefficients
`c n 0 = 0` and `c n n = b ^ n` made explicit. -/
private theorem iterate_smul_apply_eq_add_sum (D : Derivation R A A) (b y : A) {n : ℕ}
    (hn : 2 ≤ n) : (b • D)^[n] y = b ^ n * D^[n] y + smulIterCoeff D b n 1 * D y +
      ∑ k ∈ Finset.Ico 2 n, smulIterCoeff D b n k * D^[k] y := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (by omega : 1 ≤ n)
  -- Split off the top term `k = n`, then the bottom terms `k = 0` and `k = 1`.
  rw [iterate_smul_apply_eq_sum, Finset.sum_range_succ, Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot (by omega), Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  simp only [smulIterCoeff_self, smulIterCoeff_succ_zero, zero_mul, zero_add,
    Function.iterate_one]
  ring

variable (p : ℕ) [Fact p.Prime] [CharP A p]

/-- If some `x` satisfies `D x = 1`, the middle coefficients `c p k`, `2 ≤ k < p`, of the
expansion of `(b • D)^[p]` vanish. The operator `T = ∑ 2 ≤ k < p, c p k • D^[k]` is a derivation,
as `(b • D)^[p] - b ^ p • D^[p] - c p 1 • D`. It kills `x`, hence every `x ^ k`, while
`T (x ^ k) = c p k * k !` once the coefficients below `k` vanish. -/
private theorem smulIterCoeff_eq_zero_of_apply_eq_one (D : Derivation ℤ A A) {x : A}
    (hx : D x = 1) (b : A) {k : ℕ} (hk : k ∈ Finset.Ico 2 p) : smulIterCoeff D b p k = 0 := by
  have hp := (Fact.out : p.Prime)
  have hDx (k j : ℕ) := iterate_apply_pow_of_apply_eq_one D hx k j
  let T : Derivation ℤ A A := (b • D).pPow p - b ^ p • D.pPow p - smulIterCoeff D b p 1 • D
  have hT (z : A) : T z = ∑ k ∈ Finset.Ico 2 p, smulIterCoeff D b p k * D^[k] z := by
    simp only [T, sub_apply, smul_apply, pPow_apply, iterate_smul_apply_eq_add_sum D b z hp.two_le,
      smul_eq_mul]
    ring
  have hTx (k : ℕ) : T (x ^ k) = 0 := by
    have h : T x = 0 := by
      rw [hT]
      refine Finset.sum_eq_zero fun j hj ↦ ?_
      rw [← pow_one x, hDx, Nat.descFactorial_eq_zero_iff_lt.mpr
        (by simp only [Finset.mem_Ico] at hj; omega)]
      simp
    simp [leibniz_pow, h]
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  have h := hTx k
  rw [hT, Finset.sum_eq_single k] at h
  · rw [hDx, Nat.descFactorial_self, Nat.sub_self, pow_zero, mul_one] at h
    exact ((IsUnit.natCast_factorial_iff_of_charP p).mpr
      (Finset.mem_Ico.mp hk).2).mul_left_eq_zero.mp h
  · intro j hj hjk
    rcases lt_or_gt_of_ne hjk with hlt | hlt
    · rw [ih j hlt hj, zero_mul]
    · rw [hDx, Nat.descFactorial_eq_zero_iff_lt.mpr hlt]
      simp
  · exact fun h ↦ absurd hk h

open Polynomial in
/-- In characteristic `p`, the middle coefficients `c p k`, `2 ≤ k < p`, of the expansion
`(b • D)^[p] = ∑ k ≤ p, c p k * D^[k]` (`iterate_smul_apply_eq_sum`) vanish. -/
theorem smulIterCoeff_eq_zero_of_mem_Ico (D : Derivation R A A) (b : A) {k : ℕ}
    (hk : k ∈ Finset.Ico 2 p) : smulIterCoeff D b p k = 0 := by
  -- Extend `D` to `A[X]` by `X ↦ 1` and transport the vanishing back along the injective `C`.
  let : Differential A := ⟨D.restrictScalars ℤ⟩
  -- With this instance, `Differential.deriv y` is `D.restrictScalars ℤ y`, that is, `D y`.
  have hderiv (y : A) : Differential.deriv y = D y := D.restrictScalars_apply ℤ y
  apply C_injective
  rw [map_smulIterCoeff C D (Differential.implicitDeriv 1)
    (fun y ↦ by rw [Differential.implicitDeriv_C, hderiv]), map_zero]
  exact smulIterCoeff_eq_zero_of_apply_eq_one p _ (Differential.implicitDeriv_X 1) (C b) hk

/-- **Hochschild's formula** (Hochschild 1955; Katz, Proposition 5.3, due to Deligne). In
characteristic `p`, for `a : A`, `(a • D)^[p] = a ^ p • D^[p] + (a • D)^[p - 1] a • D`: the
`p`-th power is `p`-homogeneous for the scalars of `A` up to a multiple of `D`. -/
theorem pPow_smul (a : A) (D : Derivation R A A) :
    (a • D).pPow p = a ^ p • D.pPow p + ((a • D)^[p - 1] a) • D := by
  have hp := (Fact.out : p.Prime)
  have h₁ : smulIterCoeff D a p 1 = (a • D)^[p - 1] a := by
    obtain ⟨q, hq⟩ := Nat.exists_eq_add_one_of_ne_zero hp.ne_zero
    rw [hq, smulIterCoeff_succ_one, Nat.add_sub_cancel]
  ext y
  rw [pPow_apply, iterate_smul_apply_eq_add_sum D a y hp.two_le,
    Finset.sum_eq_zero fun k hk ↦ by rw [smulIterCoeff_eq_zero_of_mem_Ico p D a hk, zero_mul], h₁]
  simp [pPow_apply]

end Hochschild

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
differentials of `Ω[A⁄R]` and `A` has characteristic `p`, the derivation `∂_i` dual to `ds_i`
satisfies `∂_i^[p] = 0`. -/
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
