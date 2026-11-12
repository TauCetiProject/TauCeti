/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Mathlib.Analysis.Quaternion` is imported publicly for `Quaternion.ofComplex`, the `ℝ`-algebra
-- embedding `ℂ →ₐ[ℝ] ℍ[ℝ]` that every statement below is about; it re-exports
-- `Mathlib.Algebra.Quaternion`, hence the `ℍ[·]` notation and the division ring structure on
-- `ℍ[ℝ]`, which is why neither is imported again here.
public import Mathlib.Analysis.Quaternion
-- `Mathlib.LinearAlgebra.Complex.Module` is imported publicly for `Complex.lift`, the universal
-- property saying that an `ℝ`-algebra map out of `ℂ` is exactly a square root of `-1`, and for
-- `Complex.conjAe`, the conjugation this file realizes by `j`.
public import Mathlib.LinearAlgebra.Complex.Module
import TauCeti.Algebra.Field.Basic
import TauCeti.LinearAlgebra.Complex.Module

/-!
# The two embeddings of `ℂ` in the quaternions are conjugate

Complex conjugation on the copy of `ℂ` inside the real quaternions is conjugation by `j`:

`ofComplex (conj z) = j * ofComplex z * j⁻¹`.

More generally, any two `ℝ`-algebra maps `ℂ →ₐ[ℝ] ℍ[ℝ]` are conjugate by a unit of `ℍ[ℝ]`. This is
an instance of the noncentral Skolem-Noether theorem, and is not a case of
`TauCeti.skolemNoether`, which conjugates two `K`-algebra maps `B →ₐ[K] A` only when **both** `A`
and `B` are central simple over `K`: `ℂ` is not central over `ℝ`, its centre being all of `ℂ`.
Centrality of the source cannot simply be dropped either, since complex conjugation is an
`ℝ`-algebra automorphism of `ℂ` that is **not** inner in `ℂ`. The automorphisms
`ℍ[ℝ] ≃ₐ[ℝ] ℍ[ℝ]`, whose source is central simple, are covered by
`TauCeti.exists_unit_conj_of_algEquiv` instead.

The proof uses none of the central simple machinery. An `ℝ`-algebra map `ℂ →ₐ[ℝ] A` is the same
thing as a square root of `-1` in `A` (Mathlib's `Complex.lift`), and a conjugacy between two
such maps holds as soon as it holds at `Complex.I` (`Units.conj_complexAlgHom_apply`), so what has
to be proved is that any two square roots of `-1` in `ℍ[ℝ]` are conjugate. In any division ring,
two square roots `x`, `u` of `-1` are conjugate by `1 - u * x` unless `u * x = 1`, that is unless
`u = -x` (`TauCeti.exists_unit_conj_of_mul_ne_one`). For `x = i` that excluded case is settled by
`j`, which anticommutes with `i`. So every square root of `-1` in `ℍ[ℝ]` is conjugate to `i`, hence
any two are conjugate to each other. Complex conjugation is exactly the excluded case, which is
why `j` is the explicit witness.

## Main definitions

* `TauCeti.Quaternion.jUnit`: the quaternion `j`, as a unit of the division ring `ℍ[ℝ]`.

## Main statements

* `TauCeti.Quaternion.conj_jUnit_ofComplex_I`: conjugation by `j` negates `i`.
* `TauCeti.Quaternion.exists_unit_conj_of_mul_self_eq_neg_one`: any two square roots of `-1` in
  `ℍ[ℝ]` are conjugate by a unit.
* `TauCeti.Quaternion.exists_unit_conj_complexAlgHom`: **noncentral Skolem-Noether for
  `ℂ ⊆ ℍ[ℝ]`** -- any two `ℝ`-algebra maps `ℂ →ₐ[ℝ] ℍ[ℝ]` are conjugate by a unit of `ℍ[ℝ]`.
* `TauCeti.Quaternion.ofComplex_conjAe`: **complex conjugation on `ℂ ⊆ ℍ[ℝ]` is conjugation by
  `j`**, with the explicit witness.

## Implementation notes

Squares are written `u * u = -1` rather than `u ^ 2 = -1`, matching the subtype
`{I' // I' * I' = -1}` that Mathlib's `Complex.lift` is stated over, so that the square relation
satisfied by the value of an `ℝ`-algebra map `f` at `Complex.I` is `(Complex.lift.symm f).prop`,
with no `sq`/`pow` translation.

`TauCeti.Quaternion.jUnit` carries its inverse as data rather than being built with `Units.mk0`
from a nonvanishing proof: `↑jUnit⁻¹` is then a quaternion literal definitionally, which turns the
one coordinate computation of the file into a rewrite rather than a division. The body is not
exposed, so the two coercion lemmas below are proved `(rfl)` rather than `rfl`.

The two coordinate identities are stated with the type ascriptions written out, `(⟨0, 0, 1, 0⟩ :
ℍ[ℝ]) * …`, and are consumed by `exact`/`rw` rather than being inlined into the proofs that need
them. `Quaternion R` is a plain `def` for `ℍ[R,-1,-1]`, so an ascribed anonymous constructor
elaborates at the *unfolded* type and `QuaternionAlgebra.mk_mul_mk` applies to it, whereas the same
literal reached through a declaration of type `ℍ[ℝ]` does not match that `simp` lemma at all and
the product stays stuck. Neither `TauCeti.Quaternion.coe_jUnit` nor
`TauCeti.Quaternion.coe_inv_jUnit` is a `simp` lemma for the same reason: rewriting with them puts
a literal where nothing can act on it unless the goal is already in the ascribed form.

## References

See P. Gille, T. Szamuely, *Central Simple Algebras and Galois Cohomology*, CUP (2006), §2.7, and
I. N. Herstein, *Noncommutative Rings*, MAA (1968), Ch. 4.
-/

public section

open scoped Quaternion

open _root_.Quaternion (ofComplex)

namespace TauCeti

namespace Quaternion

/-- **The quaternion `j`, as a unit** of the division ring `ℍ[ℝ]`. Its inverse `-j` is supplied as
data, so that `↑jUnit⁻¹` reduces to a quaternion literal without a division. -/
def jUnit : ℍ[ℝ]ˣ where
  val := ⟨0, 0, 1, 0⟩
  inv := ⟨0, 0, -1, 0⟩
  val_inv := (by ext <;> simp : (⟨0, 0, 1, 0⟩ : ℍ[ℝ]) * (⟨0, 0, -1, 0⟩ : ℍ[ℝ]) = 1)
  inv_val := (by ext <;> simp : (⟨0, 0, -1, 0⟩ : ℍ[ℝ]) * (⟨0, 0, 1, 0⟩ : ℍ[ℝ]) = 1)

theorem coe_jUnit : (jUnit : ℍ[ℝ]) = ⟨0, 0, 1, 0⟩ := (rfl)

theorem coe_inv_jUnit : ((jUnit⁻¹ : ℍ[ℝ]ˣ) : ℍ[ℝ]) = ⟨0, 0, -1, 0⟩ := (rfl)

/-- The coordinates of `i`: the image of `Complex.I` under the standard embedding. -/
theorem ofComplex_I : ofComplex Complex.I = (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) := by
  ext <;> simp [_root_.Quaternion.coe_ofComplex, _root_.Quaternion.coeComplex]

/-- **Conjugation by `j` negates `i`.** This is the one computation with quaternion coordinates
that the file needs: `j` anticommutes with `i`. -/
theorem conj_jUnit_ofComplex_I :
    (jUnit : ℍ[ℝ]) * ofComplex Complex.I * ((jUnit⁻¹ : ℍ[ℝ]ˣ) : ℍ[ℝ]) = -ofComplex Complex.I := by
  have h : (⟨0, 0, 1, 0⟩ : ℍ[ℝ]) * (⟨0, 1, 0, 0⟩ : ℍ[ℝ]) * (⟨0, 0, -1, 0⟩ : ℍ[ℝ])
      = -(⟨0, 1, 0, 0⟩ : ℍ[ℝ]) := by ext <;> simp
  rw [ofComplex_I, coe_jUnit, coe_inv_jUnit]
  exact h

/-- **Every square root of `-1` in `ℍ[ℝ]` is conjugate to `i`.** In the generic case the
conjugating unit is `1 - u * i`; the one element that excludes is `-i`, which `j` conjugates `i`
to. -/
theorem exists_unit_conj_ofComplex_I {u : ℍ[ℝ]} (hu : u * u = -1) :
    ∃ w : ℍ[ℝ]ˣ, u = (w : ℍ[ℝ]) * ofComplex Complex.I * ((w⁻¹ : ℍ[ℝ]ˣ) : ℍ[ℝ]) := by
  have hx : ofComplex Complex.I * ofComplex Complex.I = -1 := (Complex.lift.symm ofComplex).prop
  by_cases h : u * ofComplex Complex.I = 1
  · refine ⟨jUnit, ?_⟩
    rw [conj_jUnit_ofComplex_I]
    calc u = -(u * ofComplex Complex.I * ofComplex Complex.I) := by
          rw [mul_assoc, hx, mul_neg_one, neg_neg]
      _ = -ofComplex Complex.I := by rw [h, one_mul]
  · exact exists_unit_conj_of_mul_ne_one hx hu h

/-- **Any two square roots of `-1` in `ℍ[ℝ]` are conjugate** by a unit of `ℍ[ℝ]`: both are
conjugate to `i`. -/
theorem exists_unit_conj_of_mul_self_eq_neg_one {u v : ℍ[ℝ]} (hu : u * u = -1) (hv : v * v = -1) :
    ∃ w : ℍ[ℝ]ˣ, v = (w : ℍ[ℝ]) * u * ((w⁻¹ : ℍ[ℝ]ˣ) : ℍ[ℝ]) := by
  obtain ⟨a, rfl⟩ := exists_unit_conj_ofComplex_I hu
  obtain ⟨b, rfl⟩ := exists_unit_conj_ofComplex_I hv
  exact ⟨b * a⁻¹, by simp [mul_assoc]⟩

/-- **Noncentral Skolem-Noether for `ℂ ⊆ ℍ[ℝ]`**: any two `ℝ`-algebra maps `ℂ →ₐ[ℝ] ℍ[ℝ]` are
conjugate by a unit of `ℍ[ℝ]`. The source `ℂ` is simple but **not** central over `ℝ`, so
`TauCeti.skolemNoether` does not apply and the conjugating unit is produced directly, from the
conjugacy of the square roots of `-1`. -/
theorem exists_unit_conj_complexAlgHom (f g : ℂ →ₐ[ℝ] ℍ[ℝ]) :
    ∃ w : ℍ[ℝ]ˣ, ∀ z : ℂ, g z = (w : ℍ[ℝ]) * f z * ((w⁻¹ : ℍ[ℝ]ˣ) : ℍ[ℝ]) := by
  obtain ⟨w, hw⟩ := exists_unit_conj_of_mul_self_eq_neg_one (Complex.lift.symm f).prop
    (Complex.lift.symm g).prop
  exact ⟨w, w.conj_complexAlgHom_apply f g hw⟩

/-- **Complex conjugation on `ℂ ⊆ ℍ[ℝ]` is conjugation by `j`**: the explicit witness in place of
the existential of `TauCeti.Quaternion.exists_unit_conj_complexAlgHom`. -/
theorem ofComplex_conjAe (z : ℂ) :
    ofComplex (Complex.conjAe z) = (jUnit : ℍ[ℝ]) * ofComplex z * ((jUnit⁻¹ : ℍ[ℝ]ˣ) : ℍ[ℝ]) := by
  refine jUnit.conj_complexAlgHom_apply ofComplex (ofComplex.comp Complex.conjAe.toAlgHom) ?_ z
  rw [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, Complex.conjAe_coe, Complex.conj_I, map_neg,
    conj_jUnit_ofComplex_I]

end Quaternion

end TauCeti
