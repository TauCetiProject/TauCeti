/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.Topology.Algebra.Ring.Basic

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Algebra.Group.Units
import TauCeti.Algebra.Polynomial.Semiconj

/-!
# The unipotent radical attached to an idempotent element

For an element `e` of a semiring `A` that is a compatible `k`-module, the upper-right blocks
`TauCeti.upperBlocks k e` are the elements `z : A` satisfying `e * z = z` and `z * e = 0`. They
form a `k`-submodule of square-zero elements. When `A` is a ring and `e` is idempotent, the map
`y ↦ 1 + e * y * (1 - e)` defines a group homomorphism
`IsIdempotentElem.radicalHom he : Multiplicative A →* Aˣ` whose range consists of the units
`u : Aˣ` with `(u : A) - 1 ∈ upperBlocks k e` (`IsIdempotentElem.mem_range_radicalHom_iff`). For
`A = Matrix n n k`, this recovers the unipotent radical of the parabolic subgroup of `GL n k`
stabilizing the image of `e`.

If `A` is a `k`-algebra and a polynomial `p(g)` in `g : A` is a projection onto the image of `e`
(`e * aeval g p = aeval g p` and `aeval g p * e = e`), then every two-sided translate
`x = u * g * u'` by elements of this unipotent radical is conjugate to `g` by the explicit
unipotent unit `he.radicalHom (ofAdd (aeval x p - aeval g p))`
(`IsIdempotentElem.semiconjBy_radicalHom_aeval_sub`).

## Main definitions

* `TauCeti.upperBlocks`: the submodule `{z | e * z = z ∧ z * e = 0}` of upper-right blocks.
* `IsIdempotentElem.radicalHom`: the homomorphism `y ↦ 1 + e * y * (1 - e)` into `Aˣ`.

## Main results

* `IsIdempotentElem.mem_range_radicalHom_iff`:
  `u ∈ he.radicalHom.range ↔ (u : A) - 1 ∈ upperBlocks k e`.
* `IsIdempotentElem.continuous_radicalHom`: over a topological ring `A`, `he.radicalHom` is
  continuous.
* `TauCeti.aeval_sub_aeval_mem_upperBlocks`: if `e * (g * e) = g * e` and `x - g ∈ upperBlocks k e`,
  then `aeval x p - aeval g p ∈ upperBlocks k e` for every polynomial `p`.
* `TauCeti.semiconjBy_one_add_aeval_sub` and `IsIdempotentElem.semiconjBy_radicalHom_aeval_sub`:
  every translate of `g` by the unipotent radical is conjugate to `g` within the unipotent radical.

## References

* L. Alpöge, `New.upperBlocks`, `New.radicalHom`, and `New.semiconjBy_radicalHom_aeval_sub` in
  `src/Lib/General/LinearAlgebra/IdempotentRadical.lean`,
  <https://github.com/leanprover-community/riemann-hypothesis/tree/dba5aded4bf7>.
-/

public section

open Polynomial Multiplicative

namespace TauCeti

section UpperBlocks

variable {k A : Type*} [Semiring k] [Semiring A] [Module k A] [SMulCommClass k A A]
  [IsScalarTower k A A] {e : A}

variable (k e) in
/-- The upper-right blocks with respect to `e`: elements `z : A` with `e * z = z` and
`z * e = 0`. -/
def upperBlocks : Submodule k A where
  carrier := {z : A | e * z = z ∧ z * e = 0}
  add_mem' := by
    rintro y z ⟨hey, hye⟩ ⟨hez, hze⟩
    exact ⟨by rw [mul_add, hey, hez], by rw [add_mul, hye, hze, add_zero]⟩
  zero_mem' := ⟨mul_zero e, zero_mul e⟩
  smul_mem' := by
    rintro c z ⟨hez, hze⟩
    exact ⟨by rw [mul_smul_comm, hez], by rw [smul_mul_assoc, hze, smul_zero]⟩

/-- Membership characterization for `TauCeti.upperBlocks`. -/
@[simp]
theorem mem_upperBlocks_iff {z : A} : z ∈ upperBlocks k e ↔ e * z = z ∧ z * e = 0 :=
  Iff.rfl

/-- Every `y ∈ upperBlocks k e` annihilates any `z` with `e * z = z` on the left. -/
theorem mul_eq_zero_of_mem_upperBlocks {y z : A} (hy : y ∈ upperBlocks k e) (hz : e * z = z) :
    y * z = 0 := by
  rw [← hz, ← mul_assoc, (mem_upperBlocks_iff.mp hy).2, zero_mul]

/-- `upperBlocks k e` is stable under left multiplication by any `g` with `e * (g * e) = g * e`. -/
theorem mul_mem_upperBlocks_left {g z : A} (hg : e * (g * e) = g * e) (hz : z ∈ upperBlocks k e) :
    g * z ∈ upperBlocks k e := by
  obtain ⟨hez, hze⟩ := mem_upperBlocks_iff.mp hz
  exact mem_upperBlocks_iff.mpr ⟨by rw [← hez, ← mul_assoc g, ← mul_assoc, hg],
    by rw [mul_assoc, hze, mul_zero]⟩

/-- `upperBlocks k e` is stable under right multiplication by any `g` with `e * (g * e) = g * e`. -/
theorem mul_mem_upperBlocks_right {g z : A} (hg : e * (g * e) = g * e) (hz : z ∈ upperBlocks k e) :
    z * g ∈ upperBlocks k e := by
  obtain ⟨hez, -⟩ := mem_upperBlocks_iff.mp hz
  exact mem_upperBlocks_iff.mpr
    ⟨by rw [← mul_assoc, hez], by rw [mul_assoc, mul_eq_zero_of_mem_upperBlocks hz hg]⟩

end UpperBlocks

end TauCeti

namespace IsIdempotentElem

open TauCeti

section Ring

variable {A : Type*} [Ring A] {e : A}

/-- For an idempotent `e`, `e * y * (1 - e)` lies in `upperBlocks k e`. -/
theorem mul_mul_one_sub_mem_upperBlocks {k : Type*} [Semiring k] [Module k A] [SMulCommClass k A A]
    [IsScalarTower k A A] (he : IsIdempotentElem e) (y : A) :
    e * y * (1 - e) ∈ upperBlocks k e :=
  mem_upperBlocks_iff.mpr ⟨by rw [← mul_assoc, ← mul_assoc, he.eq],
    by rw [mul_assoc, he.one_sub_mul_self, mul_zero]⟩

/-- The homomorphism `y ↦ 1 + e * y * (1 - e)` from `Multiplicative A` to `Aˣ`. -/
noncomputable def radicalHom (he : IsIdempotentElem e) : Multiplicative A →* Aˣ :=
  MonoidHom.toHomUnits
    { toFun y := 1 + e * y.toAdd * (1 - e)
      map_one' := by rw [toAdd_one, mul_zero, zero_mul, add_zero]
      map_mul' y z := by
        have h_zero : e * y.toAdd * (1 - e) * (e * z.toAdd * (1 - e)) = 0 := by
          rw [mul_assoc (e * y.toAdd), ← mul_assoc (1 - e), ← mul_assoc (1 - e),
            he.one_sub_mul_self, zero_mul, zero_mul, mul_zero]
        rw [toAdd_mul]
        linear_combination (norm := noncomm_ring) -h_zero }

/-- Underlying ring element of `IsIdempotentElem.radicalHom`. -/
@[simp]
theorem coe_radicalHom (he : IsIdempotentElem e) (y : Multiplicative A) :
    (he.radicalHom y : A) = 1 + e * y.toAdd * (1 - e) := by
  rfl

-- Not `@[simp]`: `coe_radicalHom` rewrites the LHS, and `k` is not determined by it (`simpNF`).
/-- On an upper-right block `z ∈ upperBlocks k e`, `he.radicalHom (ofAdd z)` is `1 + z`. -/
theorem coe_radicalHom_of_mem {k : Type*} [Semiring k] [Module k A] [SMulCommClass k A A]
    [IsScalarTower k A A] (he : IsIdempotentElem e) {z : A} (hz : z ∈ upperBlocks k e) :
    (he.radicalHom (ofAdd z) : A) = 1 + z := by
  obtain ⟨hez, hze⟩ := mem_upperBlocks_iff.mp hz
  rw [coe_radicalHom, toAdd_ofAdd, hez, mul_sub, mul_one, hze, sub_zero]

-- Not `@[simp]`: `coe_radicalHom` rewrites the LHS (`simpNF`).
/-- Elements of `IsIdempotentElem.radicalHom he` fix `e` under left multiplication. -/
theorem coe_radicalHom_mul_self (he : IsIdempotentElem e) (y : Multiplicative A) :
    (he.radicalHom y : A) * e = e := by
  rw [coe_radicalHom, add_mul, one_mul, mul_assoc (e * y.toAdd), he.one_sub_mul_self, mul_zero,
    add_zero]

/-- A unit `u : Aˣ` lies in the range of `he.radicalHom` iff `(u : A) - 1 ∈ upperBlocks k e`. -/
theorem mem_range_radicalHom_iff {k : Type*} [Semiring k] [Module k A] [SMulCommClass k A A]
    [IsScalarTower k A A] (he : IsIdempotentElem e) {u : Aˣ} :
    u ∈ he.radicalHom.range ↔ (u : A) - 1 ∈ upperBlocks k e := by
  constructor
  · rintro ⟨y, rfl⟩
    simpa only [coe_radicalHom, add_sub_cancel_left] using
      he.mul_mul_one_sub_mem_upperBlocks (k := k) y.toAdd
  · intro hu
    refine ⟨ofAdd ((u : A) - 1), Units.ext ?_⟩
    rw [he.coe_radicalHom_of_mem hu, add_sub_cancel]

/-- Over a topological ring `A`, `IsIdempotentElem.radicalHom he` is continuous. -/
theorem continuous_radicalHom [TopologicalSpace A] [IsTopologicalRing A] (he : IsIdempotentElem e) :
    Continuous he.radicalHom := by
  have hval : Continuous fun y : Multiplicative A ↦ (he.radicalHom y : A) := by
    simp only [coe_radicalHom]
    exact continuous_const.add ((continuous_const.mul continuous_toAdd).mul continuous_const)
  exact Continuous.of_coeHom_comp hval

/-- If `e * (g * e) = g * e`, then translating `g` on both sides by elements of `he.radicalHom`
changes `g` by an element of `upperBlocks k e`. -/
theorem radicalHom_mul_mul_sub_mem_upperBlocks {k : Type*} [Semiring k] [Module k A]
    [SMulCommClass k A A] [IsScalarTower k A A] (he : IsIdempotentElem e) {g : A}
    (hg : e * (g * e) = g * e) (y z : Multiplicative A) :
    (he.radicalHom y : A) * g * he.radicalHom z - g ∈ upperBlocks k e := by
  rw [coe_radicalHom, coe_radicalHom]
  set a : A := e * y.toAdd * (1 - e)
  set b : A := e * z.toAdd * (1 - e)
  have ha : a ∈ upperBlocks k e := he.mul_mul_one_sub_mem_upperBlocks y.toAdd
  have hgb : g * b ∈ upperBlocks k e :=
    mul_mem_upperBlocks_left hg (he.mul_mul_one_sub_mem_upperBlocks z.toAdd)
  have h_zero : a * (g * b) = 0 :=
    mul_eq_zero_of_mem_upperBlocks ha (mem_upperBlocks_iff.mp hgb).1
  have h_diff : (1 + a) * g * (1 + b) - g = a * g + g * b := by
    linear_combination (norm := noncomm_ring) h_zero
  rw [h_diff]
  exact add_mem (mul_mem_upperBlocks_right hg ha) hgb

end Ring

end IsIdempotentElem

namespace TauCeti

section Algebra

/-- If `e * aeval g p = aeval g p` and `aeval g p * e = e`, then `e * (g * e) = g * e`. -/
theorem mul_mul_eq_mul_of_aeval {k A : Type*} [CommSemiring k] [Semiring A] [Algebra k A]
    {e g : A} {p : k[X]} (h_range : e * aeval g p = aeval g p) (h_fix : aeval g p * e = e) :
    e * (g * e) = g * e := by
  have h_comm : g * aeval g p = aeval g p * g := by
    simpa only [aeval_eq_smeval] using (SemiconjBy.smeval_right (rfl : SemiconjBy g g g) p).eq
  have h_eq : g * e = aeval g p * (g * e) := by rw [← mul_assoc, ← h_comm, mul_assoc, h_fix]
  rw [h_eq, ← mul_assoc, h_range]

variable {k A : Type*} [CommSemiring k] [Ring A] [Algebra k A] {e : A}

/-- If `e * (g * e) = g * e` and `x - g ∈ upperBlocks k e`, then `aeval x p - aeval g p` lies in
`upperBlocks k e` for every polynomial `p`. -/
theorem aeval_sub_aeval_mem_upperBlocks {g x : A} (hg : e * (g * e) = g * e)
    (hx : x - g ∈ upperBlocks k e) (p : k[X]) : aeval x p - aeval g p ∈ upperBlocks k e := by
  obtain ⟨hx_range, hx_ker⟩ := mem_upperBlocks_iff.mp hx
  have hx_image : SemiconjBy e (g * e) x := by
    rw [SemiconjBy]
    linear_combination (norm := noncomm_ring) hg - hx_ker
  have hg_quot : SemiconjBy (1 - e) g ((1 - e) * g) := by
    rw [SemiconjBy]
    linear_combination (norm := noncomm_ring) -hg
  have hx_quot : SemiconjBy (1 - e) x ((1 - e) * g) := by
    rw [SemiconjBy]
    linear_combination (norm := noncomm_ring) hg_quot.eq - hx_range
  have h_image : aeval x p * e = aeval g p * e := by
    simpa only [aeval_eq_smeval] using
      (hx_image.smeval_right p).eq.symm.trans (SemiconjBy.smeval_right hg p).eq
  have h_quot : (1 - e) * aeval x p = (1 - e) * aeval g p := by
    simpa only [aeval_eq_smeval] using
      (hx_quot.smeval_right p).eq.trans (hg_quot.smeval_right p).eq.symm
  refine mem_upperBlocks_iff.mpr ⟨?_, by rw [sub_mul, h_image, sub_self]⟩
  linear_combination (norm := noncomm_ring) -h_quot

/-- If `p(g)` is a projection onto the image of `e` and `x - g ∈ upperBlocks k e`, then
`1 + (aeval x p - aeval g p)` intertwines `x` and `g`. -/
theorem semiconjBy_one_add_aeval_sub {g x : A} {p : k[X]}
    (h_range : e * aeval g p = aeval g p) (h_fix : aeval g p * e = e)
    (hx : x - g ∈ upperBlocks k e) : SemiconjBy (1 + (aeval x p - aeval g p)) x g := by
  obtain ⟨heD, -⟩ := mem_upperBlocks_iff.mp
    (aeval_sub_aeval_mem_upperBlocks (mul_mul_eq_mul_of_aeval h_range h_fix) hx p)
  obtain ⟨hez, -⟩ := mem_upperBlocks_iff.mp hx
  have hg_comm : g * aeval g p = aeval g p * g := by
    simpa only [aeval_eq_smeval] using (SemiconjBy.smeval_right (rfl : SemiconjBy g g g) p).eq
  have hx_comm : x * aeval x p = aeval x p * x := by
    simpa only [aeval_eq_smeval] using (SemiconjBy.smeval_right (rfl : SemiconjBy x x x) p).eq
  have hze : (x - g) * aeval g p = 0 := mul_eq_zero_of_mem_upperBlocks hx h_range
  have hzD : (x - g) * (aeval x p - aeval g p) = 0 := mul_eq_zero_of_mem_upperBlocks hx heD
  have hez' : aeval g p * (x - g) = x - g := by rw [← hez, ← mul_assoc, h_fix]
  rw [SemiconjBy]
  linear_combination (norm := noncomm_ring) hg_comm - hx_comm + hze + hzD - hez'

end Algebra

end TauCeti

namespace IsIdempotentElem

open TauCeti

/-- If `e` is idempotent, `p(g)` is a projection onto its image, and `x = u * g * u'` with
`u, u'` in the image of `he.radicalHom`, then `he.radicalHom (ofAdd (aeval x p - aeval g p))`
conjugates `x` to `g`. -/
theorem semiconjBy_radicalHom_aeval_sub {k A : Type*} [CommSemiring k] [Ring A] [Algebra k A]
    {e : A} (he : IsIdempotentElem e) {g x : Aˣ} {p : k[X]}
    (h_range : e * aeval (g : A) p = aeval (g : A) p)
    (h_fix : aeval (g : A) p * e = e)
    (y z : Multiplicative A) (hx : x = he.radicalHom y * g * he.radicalHom z) :
    SemiconjBy (he.radicalHom (ofAdd (aeval (x : A) p - aeval (g : A) p))) x g := by
  have hg : e * ((g : A) * e) = g * e := mul_mul_eq_mul_of_aeval h_range h_fix
  have h_mem : (x : A) - g ∈ upperBlocks k e := by
    rw [hx, Units.val_mul, Units.val_mul]
    exact he.radicalHom_mul_mul_sub_mem_upperBlocks hg y z
  rw [← SemiconjBy.units_val_iff,
    he.coe_radicalHom_of_mem (aeval_sub_aeval_mem_upperBlocks hg h_mem p)]
  exact semiconjBy_one_add_aeval_sub h_range h_fix h_mem

end IsIdempotentElem
