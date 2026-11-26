/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Instances.Matrix

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Algebra.Group.Units
import TauCeti.Algebra.Polynomial.Semiconj

/-!
# The unipotent radical attached to an idempotent matrix

For an idempotent matrix `ε : Matrix n n k`, the upper-right blocks `Matrix.upperBlocks ε` are the
matrices `Z` satisfying `ε * Z = Z` and `Z * ε = 0`. They form a `k`-submodule of square-zero
matrices, and the map `Y ↦ 1 + ε * Y * (1 - ε)` defines a group homomorphism
`Matrix.radicalHom hε : Multiplicative (Matrix n n k) →* GL n k` whose image is the unipotent
radical of the parabolic subgroup stabilizing the image of `ε`.

If a polynomial `p(g)` in a matrix `g : GL n k` is a projection onto the image of `ε`
(`ε * aeval g p = aeval g p` and `aeval g p * ε = ε`), then every two-sided translate
`x = u * g * u'` by elements of this unipotent radical is conjugate to `g` by the explicit
unipotent element `radicalHom hε (ofAdd (aeval x p - aeval g p))`
(`Matrix.semiconjBy_radicalHom_aeval_sub`).

## Main definitions

* `Matrix.upperBlocks`: the submodule `{Z | ε * Z = Z ∧ Z * ε = 0}` of upper-right blocks.
* `Matrix.radicalHom`: the homomorphism `Y ↦ 1 + ε * Y * (1 - ε)` into `GL n k`.

## Main results

* `Matrix.continuous_radicalHom`: over a topological ring, `Matrix.radicalHom hε` is continuous.
* `Matrix.aeval_sub_aeval_mem_upperBlocks`: if `ε * (g * ε) = g * ε` and `x - g ∈ upperBlocks ε`,
  then `aeval x p - aeval g p ∈ upperBlocks ε` for every polynomial `p`.
* `Matrix.semiconjBy_one_add_aeval_sub` and `Matrix.semiconjBy_radicalHom_aeval_sub`: every
  translate of `g` by the unipotent radical is conjugate to `g` within the unipotent radical.

## References

* L. Alpöge, `New.upperBlocks`, `New.radicalHom`, and `New.semiconjBy_radicalHom_aeval_sub` in
  `src/Lib/General/LinearAlgebra/IdempotentRadical.lean`,
  <https://github.com/leanprover-community/riemann-hypothesis/tree/dba5aded4bf7>.
-/

public section

open Polynomial Multiplicative

namespace Matrix

variable {n k : Type*} [Fintype n] [DecidableEq n] [CommRing k] {ε : Matrix n n k}

variable (ε) in
/-- The upper-right blocks with respect to `ε`: matrices `Z` with `ε * Z = Z` and `Z * ε = 0`. -/
def upperBlocks : Submodule k (Matrix n n k) where
  carrier := {Z : Matrix n n k | ε * Z = Z ∧ Z * ε = 0}
  add_mem' := by
    rintro Y Z ⟨hεY, hYε⟩ ⟨hεZ, hZε⟩
    exact ⟨by rw [mul_add, hεY, hεZ], by rw [add_mul, hYε, hZε, add_zero]⟩
  zero_mem' := ⟨mul_zero ε, zero_mul ε⟩
  smul_mem' := by
    rintro c Z ⟨hεZ, hZε⟩
    exact ⟨by rw [mul_smul_comm, hεZ], by rw [smul_mul_assoc, hZε, smul_zero]⟩

/-- Membership characterization for `Matrix.upperBlocks`. -/
theorem mem_upperBlocks_iff {Z : Matrix n n k} :
    Z ∈ upperBlocks ε ↔ ε * Z = Z ∧ Z * ε = 0 :=
  Iff.rfl

/-- For an idempotent `ε`, `ε * Y * (1 - ε)` lies in `upperBlocks ε`. -/
theorem mul_mul_one_sub_mem_upperBlocks (hε : IsIdempotentElem ε) (Y : Matrix n n k) :
    ε * Y * (1 - ε) ∈ upperBlocks ε :=
  mem_upperBlocks_iff.mpr ⟨by rw [← mul_assoc, ← mul_assoc, hε.eq],
    by rw [mul_assoc, hε.one_sub_mul_self, mul_zero]⟩

/-- Every `Y ∈ upperBlocks ε` annihilates any `Z` with `ε * Z = Z` on the left. -/
theorem mul_eq_zero_of_mem_upperBlocks {Y Z : Matrix n n k} (hY : Y ∈ upperBlocks ε)
    (hZ : ε * Z = Z) : Y * Z = 0 := by
  rw [← hZ, ← mul_assoc, (mem_upperBlocks_iff.mp hY).2, zero_mul]

/-- `upperBlocks ε` is stable under left multiplication by any `g` with `ε * (g * ε) = g * ε`. -/
theorem mul_mem_upperBlocks_left {g Z : Matrix n n k} (hg : ε * (g * ε) = g * ε)
    (hZ : Z ∈ upperBlocks ε) : g * Z ∈ upperBlocks ε := by
  obtain ⟨hεZ, hZε⟩ := mem_upperBlocks_iff.mp hZ
  exact mem_upperBlocks_iff.mpr ⟨by rw [← hεZ, ← mul_assoc g, ← mul_assoc, hg],
    by rw [mul_assoc, hZε, mul_zero]⟩

/-- `upperBlocks ε` is stable under right multiplication by any `g` with `ε * (g * ε) = g * ε`. -/
theorem mul_mem_upperBlocks_right {g Z : Matrix n n k} (hg : ε * (g * ε) = g * ε)
    (hZ : Z ∈ upperBlocks ε) : Z * g ∈ upperBlocks ε := by
  obtain ⟨hεZ, -⟩ := mem_upperBlocks_iff.mp hZ
  exact mem_upperBlocks_iff.mpr
    ⟨by rw [← mul_assoc, hεZ], by rw [mul_assoc, mul_eq_zero_of_mem_upperBlocks hZ hg]⟩

/-- The homomorphism `Y ↦ 1 + ε * Y * (1 - ε)` from `Multiplicative (Matrix n n k)` to `GL n k`. -/
noncomputable def radicalHom (hε : IsIdempotentElem ε) :
    Multiplicative (Matrix n n k) →* GL n k :=
  MonoidHom.toHomUnits
    { toFun Y := 1 + ε * Y.toAdd * (1 - ε)
      map_one' := by rw [toAdd_one, mul_zero, zero_mul, add_zero]
      map_mul' Y Z := by
        have h_zero : ε * Y.toAdd * (1 - ε) * (ε * Z.toAdd * (1 - ε)) = 0 :=
          mul_eq_zero_of_mem_upperBlocks (mul_mul_one_sub_mem_upperBlocks hε Y.toAdd)
            (mem_upperBlocks_iff.mp (mul_mul_one_sub_mem_upperBlocks hε Z.toAdd)).1
        rw [toAdd_mul]
        linear_combination (norm := noncomm_ring) -h_zero }

/-- Underlying matrix of `Matrix.radicalHom`. -/
theorem coe_radicalHom (hε : IsIdempotentElem ε) (Y : Multiplicative (Matrix n n k)) :
    (radicalHom hε Y : Matrix n n k) = 1 + ε * Y.toAdd * (1 - ε) := by rfl

/-- On an upper-right block `Z ∈ upperBlocks ε`, `radicalHom hε (ofAdd Z)` is `1 + Z`. -/
theorem coe_radicalHom_of_mem (hε : IsIdempotentElem ε) {Z : Matrix n n k}
    (hZ : Z ∈ upperBlocks ε) : (radicalHom hε (ofAdd Z) : Matrix n n k) = 1 + Z := by
  obtain ⟨hεZ, hZε⟩ := mem_upperBlocks_iff.mp hZ
  rw [coe_radicalHom, toAdd_ofAdd, hεZ, mul_sub, mul_one, hZε, sub_zero]

/-- Elements of `Matrix.radicalHom hε` fix `ε` under left multiplication. -/
theorem coe_radicalHom_mul_idempotent (hε : IsIdempotentElem ε)
    (Y : Multiplicative (Matrix n n k)) :
    (radicalHom hε Y : Matrix n n k) * ε = ε := by
  rw [coe_radicalHom, add_mul, one_mul, mul_assoc (ε * Y.toAdd), hε.one_sub_mul_self, mul_zero,
    add_zero]

/-- Over a topological ring, `Matrix.radicalHom hε` is continuous. -/
theorem continuous_radicalHom [TopologicalSpace k] [IsTopologicalRing k]
    (hε : IsIdempotentElem ε) : Continuous (radicalHom hε) := by
  have hval : Continuous fun Y : Multiplicative (Matrix n n k) ↦
      (radicalHom hε Y : Matrix n n k) := by
    simp only [coe_radicalHom]
    exact continuous_const.add ((continuous_const.mul continuous_toAdd).mul continuous_const)
  exact Continuous.of_coeHom_comp hval

/-- If `ε * (g * ε) = g * ε` and `x - g ∈ upperBlocks ε`, then `aeval x p - aeval g p` lies in
`upperBlocks ε` for every polynomial `p`. -/
theorem aeval_sub_aeval_mem_upperBlocks {g x : Matrix n n k} (hg : ε * (g * ε) = g * ε)
    (hx : x - g ∈ upperBlocks ε) (p : k[X]) : aeval x p - aeval g p ∈ upperBlocks ε := by
  obtain ⟨hx_range, hx_ker⟩ := mem_upperBlocks_iff.mp hx
  have hx_image : SemiconjBy ε (g * ε) x := by
    rw [SemiconjBy]
    linear_combination (norm := noncomm_ring) hg - hx_ker
  have hg_quot : SemiconjBy (1 - ε) g ((1 - ε) * g) := by
    rw [SemiconjBy]
    linear_combination (norm := noncomm_ring) -hg
  have hx_quot : SemiconjBy (1 - ε) x ((1 - ε) * g) := by
    rw [SemiconjBy]
    linear_combination (norm := noncomm_ring) hg_quot.eq - hx_range
  have h_image : aeval x p * ε = aeval g p * ε := by
    simpa only [aeval_eq_smeval] using
      (hx_image.smeval_right p).eq.symm.trans ((SemiconjBy.smeval_right hg p).eq)
  have h_quot : (1 - ε) * aeval x p = (1 - ε) * aeval g p := by
    simpa only [aeval_eq_smeval] using
      (hx_quot.smeval_right p).eq.trans (hg_quot.smeval_right p).eq.symm
  refine mem_upperBlocks_iff.mpr ⟨?_, by rw [sub_mul, h_image, sub_self]⟩
  linear_combination (norm := noncomm_ring) -h_quot

/-- If `ε * aeval g p = aeval g p` and `aeval g p * ε = ε`, then `ε * (g * ε) = g * ε`. -/
theorem mul_mul_eq_mul_of_aeval {g : Matrix n n k} {p : k[X]}
    (h_range : ε * aeval g p = aeval g p) (h_fix : aeval g p * ε = ε) :
    ε * (g * ε) = g * ε := by
  have h_comm : g * aeval g p = aeval g p * g := by
    simpa only [aeval_eq_smeval] using (SemiconjBy.smeval_right (rfl : SemiconjBy g g g) p).eq
  have h_eq : g * ε = aeval g p * (g * ε) := by rw [← mul_assoc, ← h_comm, mul_assoc, h_fix]
  rw [h_eq, ← mul_assoc, h_range]

/-- If `p(g)` is a projection onto the image of `ε` and `x - g ∈ upperBlocks ε`, then
`1 + (aeval x p - aeval g p)` intertwines `x` and `g`. -/
theorem semiconjBy_one_add_aeval_sub {g x : Matrix n n k} {p : k[X]}
    (h_range : ε * aeval g p = aeval g p) (h_fix : aeval g p * ε = ε)
    (hx : x - g ∈ upperBlocks ε) : SemiconjBy (1 + (aeval x p - aeval g p)) x g := by
  obtain ⟨hεD, -⟩ := mem_upperBlocks_iff.mp
    (aeval_sub_aeval_mem_upperBlocks (mul_mul_eq_mul_of_aeval h_range h_fix) hx p)
  obtain ⟨hεZ, -⟩ := mem_upperBlocks_iff.mp hx
  have hg_comm : g * aeval g p = aeval g p * g := by
    simpa only [aeval_eq_smeval] using (SemiconjBy.smeval_right (rfl : SemiconjBy g g g) p).eq
  have hx_comm : x * aeval x p = aeval x p * x := by
    simpa only [aeval_eq_smeval] using (SemiconjBy.smeval_right (rfl : SemiconjBy x x x) p).eq
  have hZe : (x - g) * aeval g p = 0 := mul_eq_zero_of_mem_upperBlocks hx h_range
  have hZD : (x - g) * (aeval x p - aeval g p) = 0 := mul_eq_zero_of_mem_upperBlocks hx hεD
  have heZ : aeval g p * (x - g) = x - g := by rw [← hεZ, ← mul_assoc, h_fix]
  rw [SemiconjBy]
  linear_combination (norm := noncomm_ring) hg_comm - hx_comm + hZe + hZD - heZ

/-- If `ε * (g * ε) = g * ε`, then translating `g` on both sides by elements of `radicalHom hε`
changes `g` by an element of `upperBlocks ε`. -/
theorem radicalHom_mul_mul_sub_mem_upperBlocks (hε : IsIdempotentElem ε) {g : Matrix n n k}
    (hg : ε * (g * ε) = g * ε) (Y Z : Multiplicative (Matrix n n k)) :
    (radicalHom hε Y : Matrix n n k) * g * radicalHom hε Z - g ∈ upperBlocks ε := by
  rw [coe_radicalHom, coe_radicalHom]
  set A : Matrix n n k := ε * Y.toAdd * (1 - ε)
  set B : Matrix n n k := ε * Z.toAdd * (1 - ε)
  have hA : A ∈ upperBlocks ε := mul_mul_one_sub_mem_upperBlocks hε Y.toAdd
  have hgB : g * B ∈ upperBlocks ε :=
    mul_mem_upperBlocks_left hg (mul_mul_one_sub_mem_upperBlocks hε Z.toAdd)
  have h_zero : A * (g * B) = 0 :=
    mul_eq_zero_of_mem_upperBlocks hA (mem_upperBlocks_iff.mp hgB).1
  have h_diff : (1 + A) * g * (1 + B) - g = A * g + g * B := by
    linear_combination (norm := noncomm_ring) h_zero
  rw [h_diff]
  exact add_mem (mul_mem_upperBlocks_right hg hA) hgB

/-- If `ε` is idempotent, `p(g)` is a projection onto its image, and `x = u * g * u'` with
`u, u'` in the image of `radicalHom hε`, then `radicalHom hε (ofAdd (aeval x p - aeval g p))`
conjugates `x` to `g`. -/
theorem semiconjBy_radicalHom_aeval_sub (hε : IsIdempotentElem ε) {g x : GL n k} {p : k[X]}
    (h_range : ε * aeval (g : Matrix n n k) p = aeval (g : Matrix n n k) p)
    (h_fix : aeval (g : Matrix n n k) p * ε = ε)
    (Y Z : Multiplicative (Matrix n n k)) (hx : x = radicalHom hε Y * g * radicalHom hε Z) :
    SemiconjBy (radicalHom hε (ofAdd (aeval (x : Matrix n n k) p - aeval (g : Matrix n n k) p)))
      x g := by
  have hg : ε * ((g : Matrix n n k) * ε) = g * ε := mul_mul_eq_mul_of_aeval h_range h_fix
  have h_mem : (x : Matrix n n k) - g ∈ upperBlocks ε := by
    rw [hx, Units.val_mul, Units.val_mul]
    exact radicalHom_mul_mul_sub_mem_upperBlocks hε hg Y Z
  rw [← SemiconjBy.units_val_iff,
    coe_radicalHom_of_mem hε (aeval_sub_aeval_mem_upperBlocks hg h_mem p)]
  exact semiconjBy_one_add_aeval_sub h_range h_fix h_mem

end Matrix
