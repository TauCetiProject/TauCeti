/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Subring.Units
public import TauCeti.NumberTheory.ClassFieldTheory.FiniteCohomology.DegreeTwo
public import TauCeti.NumberTheory.LocalField.AbsoluteRamificationIndex

/-!
# The local Euler characteristic

For a finite smooth discrete Galois representation `A` over a nonarchimedean local field, this
file defines the three-term local Euler characteristic

```text
χ_F(A) = |H⁰(F, A)| |H²(F, A)| / |H¹(F, A)|.
```

Over a finite compatible extension `F` of `ℚ_p` (`TauCeti.FinitePadicExtension`) it also defines
the normalized absolute value of the order of `A`,

```text
φ_F(A) = ‖#A‖_F = |#A|_p ^ [F : ℚ_p] = p ^ (-[F : ℚ_p] v_p(#A)),
```

so that Tate's local Euler characteristic formula reads `χ_F = φ_F`. Unwinding the two positive
rationals turns that equality into the usual cardinality formula

```text
#H¹ = #H⁰ · #H² · p ^ ([F : ℚ_p] v_p(#A)),
```

and, for `𝔽_p`-coefficients, into `dim H¹ = dim H⁰ + dim H² + [F : ℚ_p] dim A`.

## Main results

* `TauCeti.ClassFieldTheory.localEulerCharacteristic`: the positive-rational-valued local Euler
  characteristic of a finite smooth discrete Galois representation.
* `TauCeti.ClassFieldTheory.localEulerCharacteristic_congr`: invariance under isomorphism.
* `TauCeti.ClassFieldTheory.localCardNorm`: the normalized absolute value `φ_F(A)` of the order.
* `TauCeti.ClassFieldTheory.localCardNorm_congr`: invariance under isomorphism.
* `TauCeti.ClassFieldTheory.localCardNorm_mul_of_exact`: multiplicativity in short exact sequences.
* `natCard_continuousCohomology_one_eq_mul_of_localEulerCharacteristic_eq_localCardNorm`:
  `χ_F(A) = φ_F(A)` gives `#H¹ = #H⁰ · #H² · p ^ ([F : ℚ_p] v_p(#A))`.
* `finrank_continuousCohomology_one_eq_add_of_localEulerCharacteristic_eq_localCardNorm`:
  its dimension form for `𝔽_p`-coefficients.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, (7.3.1).
* J. S. Milne, *Arithmetic Duality Theorems*, second edition, I, Theorem 2.8.
-/

public noncomputable section

namespace TauCeti.ClassFieldTheory

open ContCohomology

variable {n : ℕ}

section EulerCharacteristic

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- **The three-term local Euler characteristic** of a finite smooth discrete Galois
representation, as a positive rational number:
`χ_F(A) = |H⁰(F, A)| |H²(F, A)| / |H¹(F, A)|`. -/
def localEulerCharacteristic (hn : (n : F) ≠ 0) (A : GalRep n F)
    [Finite A.V] [Fact (IsSmoothDiscrete (ZMod n) A)] :
    Units.posSubgroup ℚ := by
  have h₀ : Finite (continuousCohomology 0 A) :=
    finite_H (F := F) (n := n) hn A Fact.out (i := 0) (by omega)
  have h₁ : Finite (continuousCohomology 1 A) :=
    finite_H (F := F) (n := n) hn A Fact.out (i := 1) (by omega)
  have h₂ : Finite (continuousCohomology 2 A) :=
    finite_H (F := F) (n := n) hn A Fact.out (i := 2) (by omega)
  let q : ℚ :=
    (Nat.card (continuousCohomology 0 A) : ℚ) * Nat.card (continuousCohomology 2 A) /
      Nat.card (continuousCohomology 1 A)
  have hq : 0 < q := div_pos
    (mul_pos
      (by exact_mod_cast @Nat.card_pos (continuousCohomology 0 A) inferInstance h₀)
      (by exact_mod_cast @Nat.card_pos (continuousCohomology 2 A) inferInstance h₂))
    (by exact_mod_cast @Nat.card_pos (continuousCohomology 1 A) inferInstance h₁)
  exact ⟨Units.mk0 q hq.ne', hq⟩

/-- The value of `localEulerCharacteristic` in `ℚ`. -/
@[simp]
theorem localEulerCharacteristic_coe (hn : (n : F) ≠ 0) (A : GalRep n F)
    [Finite A.V] [Fact (IsSmoothDiscrete (ZMod n) A)] :
    ((localEulerCharacteristic hn A).1 : ℚ) =
      (Nat.card (continuousCohomology 0 A) : ℚ) * Nat.card (continuousCohomology 2 A) /
        Nat.card (continuousCohomology 1 A) := by
  rfl

/-- **Isomorphism invariance of the local Euler characteristic.** Isomorphic representations have
the same local Euler characteristic; finiteness and smoothness of `B` follow from those of `A`
along the isomorphism. -/
theorem localEulerCharacteristic_congr (hn : (n : F) ≠ 0) {A B : GalRep n F}
    [Finite A.V] [Fact (IsSmoothDiscrete (ZMod n) A)] (e : A ≅ B) :
    haveI : Finite B.V := .of_surjective e.hom.hom fun y ↦ ⟨e.inv.hom y, by simp⟩
    haveI : Fact (IsSmoothDiscrete (ZMod n) B) :=
      ⟨.of_injective e.inv (fun x y h ↦ by simpa using congr(e.hom.hom $h)) Fact.out⟩
    localEulerCharacteristic hn A = localEulerCharacteristic hn B := by
  have hcard (i : ℕ) : Nat.card (continuousCohomology i A) = Nat.card (continuousCohomology i B) :=
    Nat.card_congr ((ContinuousCohomology.continuousCohomologyFunctor (ZMod n) _ i).mapIso
      e).toContinuousLinearEquiv.toEquiv
  apply Subtype.ext
  apply Units.ext
  simp only [localEulerCharacteristic_coe, hcard]

end EulerCharacteristic

section CardNorm

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (p : ℕ) [Fact p.Prime] [FinitePadicExtension F p]

/-- **The normalized absolute value of the order** of a finite Galois representation over a
finite compatible extension `F` of `ℚ_p`, as a positive rational number:
`φ_F(A) = ‖#A‖_F = |#A|_p ^ [F : ℚ_p] = p ^ (-[F : ℚ_p] v_p(#A))`, the right-hand side of Tate's
local Euler characteristic formula `χ_F(A) = φ_F(A)`. -/
def localCardNorm (A : GalRep n F) [Finite A.V] : Units.posSubgroup ℚ :=
  have hq : 0 < padicNorm p (Nat.card A.V) ^ Module.finrank ℚ_[p] F :=
    pow_pos ((padicNorm.nonneg _).lt_of_ne
      (padicNorm.nonzero (Nat.cast_ne_zero.2 Nat.card_pos.ne')).symm) _
  ⟨Units.mk0 _ hq.ne', hq⟩

/-- The value of `localCardNorm` in `ℚ`. -/
@[simp]
theorem localCardNorm_coe (A : GalRep n F) [Finite A.V] :
    ((localCardNorm p A).1 : ℚ) = padicNorm p (Nat.card A.V) ^ Module.finrank ℚ_[p] F := by
  rfl

/-- **Isomorphism invariance of `localCardNorm`.** Isomorphic representations have the same
order, hence the same normalized absolute value of the order. -/
theorem localCardNorm_congr {A B : GalRep n F} [Finite A.V] (e : A ≅ B) :
    haveI : Finite B.V := .of_surjective e.hom.hom fun y ↦ ⟨e.inv.hom y, by simp⟩
    localCardNorm p A = localCardNorm p B := by
  apply Subtype.ext
  apply Units.ext
  simp only [localCardNorm_coe,
    Nat.card_congr ((CategoryTheory.forget (GalRep n F)).mapIso e).toEquiv]

/-- **Multiplicativity of `localCardNorm`.** If `0 → A → B → C → 0` is an exact sequence of
representations with `B` finite, then `φ_F(B) = φ_F(A) φ_F(C)`: the order of `B` is the product
of the orders of `A` and `C`, and the `p`-adic norm is multiplicative. -/
theorem localCardNorm_mul_of_exact {A B C : GalRep n F} [Finite B.V]
    (f : A ⟶ B) (g : B ⟶ C) (hf : Function.Injective f.hom)
    (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom) :
    haveI : Finite A.V := .of_injective _ hf
    haveI : Finite C.V := .of_surjective _ hg
    localCardNorm p B = localCardNorm p A * localCardNorm p C := by
  have : Finite A.V := .of_injective _ hf
  have : Finite C.V := .of_surjective _ hg
  have hcard : Nat.card B.V = Nat.card A.V * Nat.card C.V := by
    have hker : g.hom.toAddMonoidHom.ker = f.hom.toAddMonoidHom.range := by
      ext b
      exact (hfg b).trans Iff.rfl
    rw [← AddSubgroup.card_ker_mul_card_range g.hom.toAddMonoidHom, hker,
      (AddMonoidHom.range_eq_top (f := g.hom.toAddMonoidHom)).2 hg, AddSubgroup.card_top,
      mul_left_inj' Nat.card_pos.ne']
    exact (Nat.card_congr (Equiv.ofInjective _ hf)).symm
  apply Subtype.ext
  apply Units.ext
  simp only [localCardNorm_coe, Subgroup.coe_mul, Units.val_mul, hcard, Nat.cast_mul,
    padicNorm.mul, mul_pow]

end CardNorm

section Formula

variable (p : ℕ) [Fact p.Prime]
  {F : Type} [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [FinitePadicExtension F p]

/-- **The cardinality form of the local Euler characteristic formula.** Equality of the local
Euler characteristic and the normalized absolute value of the coefficient order implies
`#H¹ = #H⁰ · #H² · p ^ ([F : ℚ_p] v_p(#A))`. -/
theorem natCard_continuousCohomology_one_eq_mul_of_localEulerCharacteristic_eq_localCardNorm
    [NeZero n] (A : GalRep n F) [Finite A.V] [Fact (IsSmoothDiscrete (ZMod n) A)]
    (h : localEulerCharacteristic (Nat.cast_ne_zero.2 (NeZero.ne n)) A = localCardNorm p A) :
    Nat.card (continuousCohomology 1 A) =
      Nat.card (continuousCohomology 0 A) * Nat.card (continuousCohomology 2 A) *
        p ^ (Module.finrank ℚ_[p] F * padicValNat p (Nat.card A.V)) := by
  have h₁ : Finite (continuousCohomology 1 A) :=
    finite_H (Nat.cast_ne_zero.2 (NeZero.ne n)) A Fact.out (by omega)
  have hcard₁ : 0 < Nat.card (continuousCohomology 1 A) := Nat.card_pos
  have hA : 0 < Nat.card A.V := Nat.card_pos
  -- `φ_F(A) = (p ^ (v_p(#A) [F : ℚ_p]))⁻¹`, so `χ_F(A) = φ_F(A)` reads
  -- `#H⁰ · #H² / #H¹ = (p ^ (v_p(#A) [F : ℚ_p]))⁻¹`.
  have hnorm : padicNorm p (Nat.card A.V) = ((p : ℚ) ^ padicValNat p (Nat.card A.V))⁻¹ := by
    rw [padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hA.ne'), padicValRat.of_nat, zpow_neg,
      zpow_natCast]
  have hq :
      (Nat.card (continuousCohomology 0 A) : ℚ) * Nat.card (continuousCohomology 2 A) /
          Nat.card (continuousCohomology 1 A) =
        ((p : ℚ) ^ (Module.finrank ℚ_[p] F * padicValNat p (Nat.card A.V)))⁻¹ := by
    have := congrArg (fun x : Units.posSubgroup ℚ ↦ ((x.1 : ℚ))) h
    simp only [localEulerCharacteristic_coe, localCardNorm_coe] at this
    rw [this, hnorm, inv_pow, ← pow_mul, mul_comm]
  have hq' :
      (Nat.card (continuousCohomology 1 A) : ℚ) =
        Nat.card (continuousCohomology 0 A) * Nat.card (continuousCohomology 2 A) *
          (p : ℚ) ^ (Module.finrank ℚ_[p] F * padicValNat p (Nat.card A.V)) := by
    rw [div_eq_iff (by exact_mod_cast hcard₁.ne'), eq_comm,
      inv_mul_eq_iff_eq_mul₀ (pow_ne_zero _ (mod_cast (Fact.out : p.Prime).ne_zero))] at hq
    rw [hq, mul_comm]
  exact_mod_cast hq'

/-- **The `𝔽_p`-dimension form of the local Euler characteristic formula.** Equality of the local
Euler characteristic and the normalized absolute value of the coefficient order implies
`dim H¹ = dim H⁰ + dim H² + [F : ℚ_p] dim A`. -/
theorem finrank_continuousCohomology_one_eq_add_of_localEulerCharacteristic_eq_localCardNorm
    (A : GalRep p F) [Finite A.V] [Fact (IsSmoothDiscrete (ZMod p) A)]
    (h : localEulerCharacteristic (Nat.cast_ne_zero.2 (NeZero.ne p)) A = localCardNorm p A) :
    Module.finrank (ZMod p) (continuousCohomology 1 A) =
      Module.finrank (ZMod p) (continuousCohomology 0 A) +
        Module.finrank (ZMod p) (continuousCohomology 2 A) +
          Module.finrank ℚ_[p] F * Module.finrank (ZMod p) A.V := by
  have h₀ : Finite (continuousCohomology 0 A) :=
    finite_H (Nat.cast_ne_zero.2 (NeZero.ne p)) A Fact.out (by omega)
  have h₁ : Finite (continuousCohomology 1 A) :=
    finite_H (Nat.cast_ne_zero.2 (NeZero.ne p)) A Fact.out (by omega)
  have h₂ : Finite (continuousCohomology 2 A) :=
    finite_H (Nat.cast_ne_zero.2 (NeZero.ne p)) A Fact.out (by omega)
  have : Module.Finite (ZMod p) A.V := Module.Finite.of_finite
  have : Module.Finite (ZMod p) (continuousCohomology 0 A) := Module.Finite.of_finite
  have : Module.Finite (ZMod p) (continuousCohomology 1 A) := Module.Finite.of_finite
  have : Module.Finite (ZMod p) (continuousCohomology 2 A) := Module.Finite.of_finite
  have hcard :=
    natCard_continuousCohomology_one_eq_mul_of_localEulerCharacteristic_eq_localCardNorm p A h
  rw [Module.natCard_eq_pow_finrank (K := ZMod p),
    Module.natCard_eq_pow_finrank (K := ZMod p) (V := continuousCohomology 0 A),
    Module.natCard_eq_pow_finrank (K := ZMod p) (V := continuousCohomology 2 A),
    Module.natCard_eq_pow_finrank (K := ZMod p) (V := A.V), Nat.card_zmod,
    padicValNat.prime_pow, ← pow_add, ← pow_add] at hcard
  exact Nat.pow_right_injective (Fact.out : p.Prime).two_le hcard

end Formula

end TauCeti.ClassFieldTheory
