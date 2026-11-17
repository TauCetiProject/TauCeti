/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Data.Nat.Choose.Dvd
public import Mathlib.RingTheory.Derivation.Lie
public import TauCeti.Algebra.Lie.AdjointAction.Frobenius
public import TauCeti.Algebra.Lie.Basic
public import TauCeti.RingTheory.Derivation.Basic
public import TauCeti.RingTheory.Derivation.BaseChange
public import TauCeti.RingTheory.Derivation.Localization
public import TauCeti.RingTheory.Kaehler.DualDerivation

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
in the Lie algebra of derivations, its compatibility with scalar extension and with localization,
and its vanishing on the derivations dual to a basis of exact Kähler differentials. The behaviour
of `pPow` on sums (Jacobson's formula) and on multiples `a • D` by elements `a : A` (Hochschild's
formula) is not treated here.

## Main declarations

* `Derivation.iterate_leibniz`: in exponential characteristic `p`, the `p`-th iterate of a
  derivation satisfies the Leibniz rule.
* `Derivation.pPow`: the `p`-th power of a derivation, as a derivation.
* `Derivation.pPow_const_smul`: `(c • D)^[p] = c ^ p • D^[p]` for `c : R`.
* `Derivation.ad_pPow`: `ad (D^[p]) = (ad D) ^ p` in the Lie algebra `Derivation R A A`.
* `Derivation.pPow_baseChange`: `pPow` commutes with scalar extension `S ⊗[R] -`.
* `Derivation.pPow_extendOfIsLocalization`: `pPow` commutes with extension to a localization.
* `Derivation.pPow_dualDerivation_eq_zero`: the `p`-th powers of the derivations dual to a basis
  `ds_i` of `Ω[A⁄R]` vanish.

## References

* N. Jacobson, *Abstract derivation and Lie algebras*, Trans. Amer. Math. Soc. **42** (1937),
  206--224.
* N. M. Katz, *Nilpotent connections and the monodromy theorem: applications of a result of
  Turrittin*, Publ. Math. IHÉS **39** (1970), 175--232, §5.0.
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
  map_one_eq_zero' := by
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_one_of_ne_zero (expChar_ne_zero A p)
    simp [hn, pow_apply_eq_iterate, Function.iterate_succ_apply]
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

/-- The `p`-th power of the zero derivation is zero. -/
@[simp]
theorem pPow_zero : (0 : Derivation R A A).pPow p = 0 := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_one_of_ne_zero (expChar_ne_zero A p)
  ext a
  rw [pPow_apply, hn, Function.iterate_succ_apply, zero_apply, iterate_map_zero]

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

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (p : ℕ) [ExpChar A p]

/-- **The `p`-th power and the adjoint action.** In the Lie algebra of derivations,
`ad (D^[p]) = (ad D) ^ p`, that is, `⁅D^[p], E⁆` is the `p`-fold iterated bracket of `D`
with `E`. -/
theorem ad_pPow (D : Derivation R A A) :
    LieAlgebra.ad R (Derivation R A A) (D.pPow p) = LieAlgebra.ad R (Derivation R A A) D ^ p := by
  let := LieRing.ofAssociativeRing (A := Module.End R A)
  have : ExpChar (Module.End R A) p :=
    expChar_of_injective_ringHom
      (f := (Algebra.lmul R A : A →ₐ[R] Module.End R A).toRingHom) Algebra.lmul_injective p
  -- The inclusion of derivations into `R`-linear endomorphisms, as a morphism of Lie algebras.
  let ι : Derivation R A A →ₗ⁅R⁆ Module.End R A :=
    { toFun := (↑)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      map_lie' := commutator_coe_linear_map }
  -- `ι` is the coercion by construction.
  have hι_apply (D' : Derivation R A A) : ι D' = (D' : Module.End R A) := rfl
  have hι : Function.Injective ι := fun _ _ h ↦ ext fun a ↦ LinearMap.congr_fun h a
  ext E : 1
  apply hι
  rw [LieHom.map_ad_pow, LieAlgebra.ad_apply, LieHom.map_lie]
  have h := TauCeti.LieAlgebra.ad_pow_expChar_pow (R := R) p (ι D) 1
  rw [pow_one] at h
  rw [← h, LieAlgebra.ad_apply]
  simp only [hι_apply, toLinearMap_pPow]

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

/-! ### Derivations dual to a basis of exact differentials -/

section Basis

variable {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- **Coordinate derivations have vanishing `p`-th power.** If `b` is the basis `ds_i` of exact
differentials of `Ω[A⁄R]` and `A` has characteristic `p`, the derivation `∂_i` dual to `ds_i`
satisfies `∂_i^[p] = 0`. -/
theorem pPow_dualDerivation_eq_zero {b : Module.Basis ι A Ω[A⁄R]} {s : ι → A}
    (hs : ∀ i, KaehlerDifferential.D R A (s i) = b i) (p : ℕ) [Fact p.Prime] [CharP A p] (i : ι) :
    (b.dualDerivation i).pPow p = 0 := by
  obtain ⟨n, hn⟩ : ∃ n, p = n + 2 := ⟨p - 2, by have := (Fact.out : p.Prime).two_le; omega⟩
  refine ext_of_kaehlerD_eq_basis hs fun k ↦ ?_
  rw [pPow_apply, hn, Function.iterate_succ_apply, Function.iterate_succ_apply,
    Module.Basis.dualDerivation_apply_dualDerivation_apply_of_kaehlerD_eq hs, zero_apply,
    iterate_map_zero]

end Basis

/-! ### The derivative of polynomials -/

section Polynomial

open Polynomial

variable {R : Type*} [CommSemiring R] (p : ℕ) [Fact p.Prime] [CharP R p]

/-- In characteristic `p`, the `p`-th power of `d/dx` on `R[X]` vanishes. -/
@[simp]
theorem pPow_derivative' : (derivative' : Derivation R R[X] R[X]).pPow p = 0 := by
  obtain ⟨n, hn⟩ : ∃ n, p = n + 2 := ⟨p - 2, by have := (Fact.out : p.Prime).two_le; omega⟩
  ext
  simp [hn, Function.iterate_succ_apply]

/-- In characteristic `p`, the derivation `x • d/dx` of `R[X]` is its own `p`-th power, since it
fixes `X`. In particular `pPow` is not linear for the scalars of `R[X]`. -/
@[simp]
theorem pPow_X_smul_derivative' :
    ((X : R[X]) • (derivative' : Derivation R R[X] R[X])).pPow p =
      (X : R[X]) • (derivative' : Derivation R R[X] R[X]) := by
  have hX : ((X : R[X]) • (derivative' : Derivation R R[X] R[X])) X = X := by simp
  ext
  rw [pPow_apply, Function.iterate_fixed hX, hX]

end Polynomial

end Derivation
