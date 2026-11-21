/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.Topology.Algebra.OpenSubgroup
import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic
import TauCeti.FieldTheory.Galois.SquareRoot

/-!
# The Galois character of a square root

Let `L/K` be an algebraic extension and `a ∈ L` an element whose square lies in `K`. Every
`g ∈ Gal(L/K)` sends `a` to `a` or to `-a` (`AlgEquiv.apply_eq_or_eq_neg_of_sq_eq`), and recording
which gives a continuous character for the Krull topology,

`TauCeti.sqrtCharacter : Gal(L/K) →ₜ* ℤˣ`,   `g a = sqrtCharacter g • a`.

For `L` an algebraic closure, `a = √d` with `d ∈ Kˣ` and `2 ≠ 0` in `K`, this is the quadratic
character of `K(√d)/K`: it is trivial exactly when `d` is a square in `K`. It is the character by
which a quadratic twist by `K(√d)` changes a Galois action. The additive `𝔽₂`-valued reading of
the same sign on a separable closure is `TauCeti.rootSign`, and on the Galois group of a quadratic
extension itself the character is `Algebra.IsQuadraticExtension.quadraticCharacter`.

## Main definitions

* `TauCeti.sqrtCharacter`: the sign by which `Gal(L/K)` acts on a square root of an element of
  `K`.

## Main results

* `TauCeti.apply_eq_sqrtCharacter_smul`: `g a = sqrtCharacter g • a`.
* `TauCeti.eq_sqrtCharacter`: away from characteristic two, a nonzero square root determines its
  character.
* `TauCeti.sqrtCharacter_eq_one_iff`: for a normal extension and away from characteristic two, the
  character is trivial exactly when the square root lies in `K`.
-/

public section

namespace TauCeti

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

open Classical in
/-- The sign by which `Gal(L/K)` acts on a square root `a` of an element of `K`: `1` on the
automorphisms fixing `a` and `-1` on the others, so that `g a = sqrtCharacter ha g • a`
(`apply_eq_sqrtCharacter_smul`). It is continuous for the Krull topology because the stabilizer of
the algebraic element `a` is open. -/
noncomputable def sqrtCharacter [Algebra.IsIntegral K L] {a : L} {c : K}
    (ha : a ^ 2 = algebraMap K L c) : Gal(L/K) →ₜ* ℤˣ where
  toFun g := if g a = a then 1 else -1
  map_one' := by simp
  map_mul' g h := by
    have hgh := AlgEquiv.mul_apply g h a
    by_cases hha : h a = a
    · simp only [hgh, hha, ↓reduceIte, mul_one]
    have hh : h a = -a := (h.apply_eq_or_eq_neg_of_sq_eq ha).resolve_left hha
    have hna : -a ≠ a := hh ▸ hha
    by_cases hga : g a = a
    · have hgha : g (h a) ≠ a := by rw [hh, map_neg, hga]; exact hna
      simp only [hgh, hgha, hga, hha, ↓reduceIte, one_mul]
    · have hgha : g (h a) = a := by
        rw [hh, map_neg, (g.apply_eq_or_eq_neg_of_sq_eq ha).resolve_left hga, neg_neg]
      simp only [hgh, hgha, hga, hha, ↓reduceIte, mul_neg, mul_one, neg_neg]
  continuous_toFun := by
    have hS : IsOpen (MulAction.stabilizer Gal(L/K) a : Set Gal(L/K)) :=
      stabilizer_isOpen_of_isIntegral a
    have hS' := ((MulAction.stabilizer Gal(L/K) a).isClosed_of_isOpen hS).isOpen_compl
    refine continuous_discrete_rng.mpr fun b ↦ ?_
    rcases Int.units_eq_one_or b with rfl | rfl
    · convert hS using 1
      ext g
      by_cases h : g a = a <;> simp [h, AlgEquiv.smul_def]
    · convert hS' using 1
      ext g
      by_cases h : g a = a <;> simp [h, AlgEquiv.smul_def]

variable {a : L} {c : K} (ha : a ^ 2 = algebraMap K L c)

section IsIntegral

variable [Algebra.IsIntegral K L]

open Classical in
/-- The value of `sqrtCharacter` at `g`: `1` if `g` fixes the square root and `-1` otherwise. -/
theorem sqrtCharacter_apply (g : Gal(L/K)) :
    sqrtCharacter ha g = if g a = a then 1 else -1 :=
  (rfl)

/-- The character takes the value `1` exactly on the automorphisms fixing the square root. -/
@[simp]
theorem sqrtCharacter_apply_eq_one_iff {g : Gal(L/K)} : sqrtCharacter ha g = 1 ↔ g a = a := by
  by_cases h : g a = a <;> simp [sqrtCharacter_apply, h]

/-- **The defining property of `sqrtCharacter`**: every automorphism multiplies the square root
by its value. -/
theorem apply_eq_sqrtCharacter_smul (g : Gal(L/K)) : g a = (sqrtCharacter ha g : ℤ) • a := by
  by_cases h : g a = a
  · simp [sqrtCharacter_apply, h]
  · simpa [sqrtCharacter_apply, h] using (g.apply_eq_or_eq_neg_of_sq_eq ha).resolve_left h

/-- **A nonzero square root determines its character** away from characteristic two: a
continuous character `η` with `g a = η g • a` for every `g` is `sqrtCharacter`. -/
theorem eq_sqrtCharacter (h2 : (2 : K) ≠ 0) (ha₀ : a ≠ 0) {η : Gal(L/K) →ₜ* ℤˣ}
    (hη : ∀ g : Gal(L/K), g a = (η g : ℤ) • a) : η = sqrtCharacter ha := by
  have h2a : (2 : L) * a ≠ 0 := by
    refine mul_ne_zero ?_ ha₀
    rw [← map_ofNat (algebraMap K L) 2]
    exact (map_ne_zero _).mpr h2
  refine ContinuousMonoidHom.ext fun g ↦ ?_
  have h := (hη g).symm.trans (apply_eq_sqrtCharacter_smul ha g)
  -- both values are signs, and `a = -a` is impossible since `2 a ≠ 0`
  rcases Int.units_eq_one_or (η g) with h₁ | h₁ <;>
    rcases Int.units_eq_one_or (sqrtCharacter ha g) with h₂ | h₂ <;>
    simp only [h₁, h₂, Units.val_one, Units.val_neg, one_smul, neg_smul] at h ⊢
  · exact absurd (by linear_combination h) h2a
  · exact absurd (by linear_combination -h) h2a

end IsIntegral

/-- **The character of a square root is trivial exactly when the root lies in the base field**,
for a normal extension away from characteristic two. The square root is separable over `K`, and
the separable elements fixed by `Gal(L/K)` are those of `K`. -/
theorem sqrtCharacter_eq_one_iff [Normal K L] (h2 : (2 : K) ≠ 0) :
    sqrtCharacter ha = 1 ↔ a ∈ Set.range (algebraMap K L) := by
  refine ⟨fun h ↦ ?_, fun ⟨x, hx⟩ ↦ ?_⟩
  · by_cases hc : c = 0
    · exact ⟨0, by rw [map_zero, eq_comm, ← pow_eq_zero_iff two_ne_zero, ha, hc, map_zero]⟩
    have hfix : ∀ g : Gal(L/K), g a = a := fun g ↦
      (sqrtCharacter_apply_eq_one_iff ha).mp (by rw [h, ContinuousMonoidHom.coe_one, Pi.one_apply])
    have hsep : IsSeparable K a := by
      refine (Polynomial.separable_X_pow_sub_C c (by exact_mod_cast h2) hc).of_dvd
        (minpoly.dvd K a ?_)
      simp [ha]
    have hmem : a ∈ separableClosure K L ⊓ perfectClosure K L :=
      ⟨hsep, mem_perfectClosure_iff_fixed.mpr hfix⟩
    rw [separableClosure_inf_perfectClosure] at hmem
    exact IntermediateField.mem_bot.mp hmem
  · refine ContinuousMonoidHom.ext fun g ↦ ?_
    rw [ContinuousMonoidHom.coe_one, Pi.one_apply, sqrtCharacter_apply_eq_one_iff, ← hx,
      AlgEquiv.commutes]

end TauCeti
