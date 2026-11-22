/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Jacobson.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Nakayama

/-!
# The Jacobson radical of a module-finite algebra

Let `A` be an algebra over a commutative ring `R`, finitely generated as an `R`-module; `A` need not
be commutative. The image of the Jacobson radical of `R` lies in the Jacobson radical of `A`: for
`r` in the radical of `R` and any `y : A`, left multiplication by `1 + y r` is an `R`-linear
endomorphism of `A` that is the identity modulo `r A`, so it is surjective by Nakayama's lemma, and
then bijective, a surjective endomorphism of a finite module over a commutative ring being
injective. Hence `1 + y r` is a unit.

When `R` is local with maximal ideal `𝔪` and `O` is a commutative module-finite `R`-algebra, the
quotient `O ⧸ 𝔪 O` is a finite-dimensional algebra over the residue field `R ⧸ 𝔪`, hence Artinian;
its Jacobson radical is therefore nilpotent, giving a positive `k` with `Ring.jacobson O ^ k ≤ 𝔪 O`
(`TauCeti.Ring.exists_jacobson_pow_le_map_maximalIdeal`).

## Main results

* `TauCeti.Ring.algebraMap_mem_jacobson`: the image of an element of the Jacobson radical of `R`
  lies in the Jacobson radical of a module-finite `R`-algebra.
* `TauCeti.Ring.exists_jacobson_pow_le_map_maximalIdeal`: for a commutative module-finite algebra
  `O` over a local ring `R`, some positive power of `Ring.jacobson O` lies in `𝔪_R O`.

## References

* T. Y. Lam, *A First Course in Noncommutative Rings*, 2nd ed., GTM 131, Springer (2001),
  Corollary (5.9).
-/

public section

namespace TauCeti

namespace Ring

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] [Module.Finite R A]

/-- **The radical of the base lies in the radical of a module-finite algebra.** If `A` is an
`R`-algebra that is finitely generated as an `R`-module and `r` lies in the Jacobson radical of `R`,
then `algebraMap R A r` lies in the Jacobson radical of `A`. -/
theorem algebraMap_mem_jacobson {r : R} (hr : r ∈ Ring.jacobson R) :
    algebraMap R A r ∈ Ring.jacobson A := by
  refine mem_jacobson_iff_isUnit_one_add_mul_left.mpr fun y ↦ ?_
  set u := 1 + y * algebraMap R A r
  -- Left multiplication by `u` is surjective by Nakayama's lemma, since `a = u a - r • (y a)`.
  have hsurj : Function.Surjective (Algebra.lmul R A u) := by
    rw [← LinearMap.range_eq_top, eq_top_iff]
    refine Submodule.le_of_le_smul_of_le_jacobson (I := Ideal.span {r}) Module.Finite.fg_top
      ((Ideal.span_singleton_le_iff_mem _).mpr hr) fun a _ ↦ ?_
    have ha : a = Algebra.lmul R A u a - r • (y * a) := by
      simp [u, mul_assoc, Algebra.smul_def, Algebra.left_comm]
    rw [ha]
    exact Submodule.sub_mem_sup (LinearMap.mem_range_self _ a)
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self r) Submodule.mem_top)
  -- A surjective endomorphism of a finite module over a commutative ring is bijective.
  have hbij : Function.Bijective (Algebra.lmul R A u) :=
    ⟨OrzechProperty.injective_of_surjective_endomorphism _ hsurj, hsurj⟩
  exact Algebra.lmul_isUnit_iff.mp ((Module.End.isUnit_iff _).mpr hbij)

/-- For a module-finite commutative algebra `O` over a local ring `R`, some positive power of the
Jacobson radical of `O` lies in the extension of the maximal ideal of `R`. -/
theorem exists_jacobson_pow_le_map_maximalIdeal (R O : Type*) [CommRing R] [IsLocalRing R]
    [CommRing O] [Algebra R O] [Module.Finite R O] :
    ∃ k : ℕ, 0 < k ∧
      _root_.Ring.jacobson O ^ k ≤ (IsLocalRing.maximalIdeal R).map (algebraMap R O) := by
  set I : Ideal O := (IsLocalRing.maximalIdeal R).map (algebraMap R O)
  let q : O →+* O ⧸ I := Ideal.Quotient.mk I
  let := Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
  let := Ideal.Quotient.algebraQuotientOfLEComap (R := R) (P := I) fun r hr ↦
    Ideal.mem_comap.mpr (Ideal.mem_map_of_mem (algebraMap R O) hr)
  have : IsScalarTower R (R ⧸ IsLocalRing.maximalIdeal R) (O ⧸ I) := .of_algebraMap_eq' rfl
  have : Module.Finite R (O ⧸ I) :=
    .of_surjective (Ideal.Quotient.mkₐ R I).toLinearMap Ideal.Quotient.mk_surjective
  have : Module.Finite (R ⧸ IsLocalRing.maximalIdeal R) (O ⧸ I) := .of_restrictScalars_finite R _ _
  have : IsArtinianRing (O ⧸ I) := .of_finite (R ⧸ IsLocalRing.maximalIdeal R) (O ⧸ I)
  obtain ⟨k, hk⟩ := IsArtinianRing.isNilpotent_jacobson (O ⧸ I)
  have : RingHomSurjective q := ⟨Ideal.Quotient.mk_surjective⟩
  have hmap : (_root_.Ring.jacobson O).map q ≤ _root_.Ring.jacobson (O ⧸ I) :=
    Ideal.map_le_iff_le_comap.mpr (_root_.Ring.le_comap_jacobson (f := q))
  have hpow : (_root_.Ring.jacobson O ^ k).map q = ⊥ := by
    rw [Ideal.map_pow, eq_bot_iff]
    exact (pow_le_pow_left' hmap k).trans (by rw [hk, Ideal.zero_eq_bot])
  have hle : _root_.Ring.jacobson O ^ k ≤ I := fun x hx ↦
    Ideal.Quotient.eq_zero_iff_mem.mp (Ideal.mem_bot.mp (hpow ▸ Ideal.mem_map_of_mem q hx))
  exact ⟨max 1 k, lt_of_lt_of_le one_pos (le_max_left _ _),
    (Ideal.pow_le_pow_right (le_max_right 1 k)).trans hle⟩

end Ring

end TauCeti
