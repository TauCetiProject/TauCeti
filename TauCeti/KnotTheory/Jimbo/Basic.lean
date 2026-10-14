/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import TauCeti.GroupTheory.SpecificGroups.Braid.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.Order

/-!
# The Jimbo representation of the braid group

Let `ι` be a linearly ordered type of colours and `q` a unit of a commutative ring `R`. The
*q-tensor space* on `n` strands is the free `R`-module `(Fin n → ι) →₀ R` on the words of length
`n` in `ι`; for `ι = Fin N` it is the `n`-th tensor power of `R ^ N`. The Jimbo R-matrix acts on
two strands `j` and `k` of a word `w`, depending only on how the colours `a = w j` and `b = w k`
compare:

* if `a = b`, the word is multiplied by `q`;
* if `a < b`, the two colours are exchanged;
* if `b < a`, the two colours are exchanged, and `(q - q⁻¹)` times the word is added.

This is `TauCeti.KnotTheory.jimboGenerator q j k`. It satisfies the Hecke quadratic relation
`T * T = (q - q⁻¹) • T + 1`, equivalently `(T - q) * (T + q⁻¹) = 0`, so it is invertible with
inverse `T + (q⁻¹ - q)`; operators on disjoint pairs of strands commute; and operators on two pairs
sharing a strand satisfy the braid relation, which is the Yang-Baxter equation for this R-matrix.
Hence the adjacent operators define a representation `TauCeti.KnotTheory.jimbo ι q` of the braid
group `TauCeti.BraidGroup n` on the q-tensor space, in which every elementary braid satisfies the
Hecke relation. The representation therefore factors through the Iwahori-Hecke algebra of type
`A`; for `ι = Fin N` it is the action of that algebra on the `n`-th tensor power of the vector
representation of `U_q(gl_N)` in quantum Schur-Weyl duality.

For `ι = Fin N`, Turaev's enhancement of the R-matrix gives a weighted trace of this
representation. The weighted trace alone is not a Markov invariant: positive and negative
stabilization multiply it by `α * β` and `α⁻¹ * β`, where `α` and `β` are the constants of the
enhancement (for this R-matrix `α` is `q ^ N`, up to the choice of orientation conventions).
Turaev's invariant of a braid on `n` strands with exponent sum (writhe) `e` is the weighted trace
multiplied by `α ^ (-e) * β ^ (-n)`. It is a Markov invariant of braids, the `sl_N`
specialization of the HOMFLY polynomial at `z = q - q⁻¹` and `a = q ^ N`; these specializations,
over all `N`, determine the HOMFLY polynomial. The weighted trace is constructed in
`TauCeti/KnotTheory/Jimbo/Trace.lean`; its stabilization laws and writhe normalization are
constructed in `TauCeti/KnotTheory/Jimbo/Stabilization.lean` and
`TauCeti/KnotTheory/Jimbo/Normalization.lean`.
For `N = 2` this is the vertex-model route to the Jones polynomial, which
`TauCeti.TemperleyLieb.markovTrace` follows through the Temperley-Lieb algebra.

At `q = 1` the correction term vanishes, and the representation is the permutation action of
braids on the positions of the letters of a word (`TauCeti.KnotTheory.jimbo_one_apply_single`), so
the Jimbo representation is a one-parameter deformation of the permutation representation.

## Main definitions

* `TauCeti.KnotTheory.jimboGenerator`: the Jimbo R-matrix acting on two strands of the q-tensor
  space.
* `TauCeti.KnotTheory.jimboUnit`: the R-matrix on two adjacent strands, as a unit.
* `TauCeti.KnotTheory.jimbo`: the Jimbo representation
  `BraidGroup n →* (Module.End R ((Fin n → ι) →₀ R))ˣ`.

## Main results

* `TauCeti.KnotTheory.jimboGenerator_mul_self`: the Hecke quadratic relation
  `T * T = (q - q⁻¹) • T + 1`.
* `TauCeti.KnotTheory.jimboGenerator_mul_comm`: operators on disjoint pairs of strands commute.
* `TauCeti.KnotTheory.jimboGenerator_braid`: the braid relation (Yang-Baxter equation).
* `TauCeti.KnotTheory.jimbo_sigma`: the representation takes `σ i` to the R-matrix on the strands
  `i` and `i + 1`.
* `TauCeti.KnotTheory.val_jimbo_sigma_eq_val_inv_add`: the skein relation `σ = σ⁻¹ + (q - q⁻¹)`
  in the representation.
* `TauCeti.KnotTheory.jimbo_one_apply_single`: at `q = 1` it is the permutation action on words.

## References

* M. Jimbo, *A q-analogue of U(gl(N+1)), Hecke algebra, and the Yang-Baxter equation*, Lett.
  Math. Phys. 11 (1986), 247-252.
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*, Ann. of
  Math. 126 (1987), 335-388.
* V. G. Turaev, *The Yang-Baxter equation and invariants of links*, Invent. Math. 92 (1988),
  527-553.
-/

public section

open Function Finsupp

namespace TauCeti.KnotTheory

variable {R : Type*} [CommRing R] {ι : Type*} [LinearOrder ι] {n : ℕ}

/-- The Jimbo R-matrix acting on the strands `j` and `k` of the q-tensor space `(Fin n → ι) →₀ R`.
On a basis word `w`, it multiplies `w` by `q` if `w j = w k`; it exchanges the letters at `j` and
`k` if `w j < w k`; and if `w k < w j` it exchanges them and adds `(q - q⁻¹)` times `w`. -/
noncomputable def jimboGenerator (q : Rˣ) (j k : Fin n) : Module.End R ((Fin n → ι) →₀ R) :=
  linearCombination R fun w ↦
    if w j = w k then (q : R) • single w 1
    else if w j < w k then single (w ∘ Equiv.swap j k) 1
    else single (w ∘ Equiv.swap j k) 1 + ((q : R) - ((q⁻¹ : Rˣ) : R)) • single w 1

/-- The value of the Jimbo R-matrix on a basis word. -/
@[simp]
theorem jimboGenerator_single_one (q : Rˣ) (j k : Fin n) (w : Fin n → ι) :
    jimboGenerator q j k (single w 1) =
      if w j = w k then (q : R) • single w 1
      else if w j < w k then single (w ∘ Equiv.swap j k) 1
      else single (w ∘ Equiv.swap j k) 1 + ((q : R) - ((q⁻¹ : Rˣ) : R)) • single w 1 := by
  simp [jimboGenerator]

/-- The value of the Jimbo R-matrix on the strands `j` and `k` on a basis word whose letters at
`j` and `k` are `x` and `y`. -/
theorem jimboGenerator_single_update_update (q : Rˣ) {j k : Fin n} (hjk : j ≠ k)
    (w : Fin n → ι) (x y : ι) :
    jimboGenerator q j k (single (update (update w j x) k y) 1) =
      if x = y then (q : R) • single (update (update w j x) k y) 1
      else if x < y then single (update (update w j y) k x) 1
      else single (update (update w j y) k x) 1 +
        ((q : R) - ((q⁻¹ : Rˣ) : R)) • single (update (update w j x) k y) 1 := by
  have hswap : update (update w j x) k y ∘ Equiv.swap j k = update (update w j y) k x := by
    rw [Equiv.comp_swap_eq_update]
    simp [update_of_ne hjk, update_comm hjk.symm]
  rw [jimboGenerator_single_one, hswap]
  simp only [update_of_ne hjk, Function.update_self]

/-- The Hecke quadratic relation `T * T = (q - q⁻¹) • T + 1` for the Jimbo R-matrix. -/
theorem jimboGenerator_mul_self (q : Rˣ) {j k : Fin n} (hjk : j ≠ k) :
    jimboGenerator (ι := ι) q j k * jimboGenerator q j k =
      ((q : R) - ((q⁻¹ : Rˣ) : R)) • jimboGenerator q j k + 1 := by
  ext w : 2
  have hT := jimboGenerator_single_update_update q hjk w
  have hW : update (update w j (w j)) k (w k) = w := by simp
  simp only [LinearMap.coe_comp, comp_apply, lsingle_apply, Module.End.mul_apply,
    LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
  rw [← hW]
  clear hW
  generalize w j = x, w k = y
  have hq : (q : R) * ((q⁻¹ : Rˣ) : R) = 1 := q.mul_inv
  rcases lt_trichotomy x y with hxy | hxy | hxy <;> subst_vars <;>
    simp only [map_add, map_smul, ne_of_lt, ne_of_gt, lt_asymm, *, ↓reduceIte] <;>
    match_scalars <;> grind

/-- The Jimbo R-matrix is invertible, with right inverse `T + (q⁻¹ - q)`. -/
theorem jimboGenerator_mul_add (q : Rˣ) {j k : Fin n} (hjk : j ≠ k) :
    jimboGenerator (ι := ι) q j k * (jimboGenerator q j k + (((q⁻¹ : Rˣ) : R) - q) • 1) = 1 := by
  rw [mul_add, jimboGenerator_mul_self q hjk, mul_smul_comm, mul_one]
  module

/-- The Jimbo R-matrix is invertible, with left inverse `T + (q⁻¹ - q)`. -/
theorem add_mul_jimboGenerator (q : Rˣ) {j k : Fin n} (hjk : j ≠ k) :
    (jimboGenerator (ι := ι) q j k + (((q⁻¹ : Rˣ) : R) - q) • 1) * jimboGenerator q j k = 1 := by
  rw [add_mul, jimboGenerator_mul_self q hjk, smul_mul_assoc, one_mul]
  module

/-- Jimbo R-matrices on disjoint pairs of strands commute. -/
theorem jimboGenerator_mul_comm (q : Rˣ) {j k l m : Fin n} (h : [j, k, l, m].Nodup) :
    jimboGenerator (ι := ι) q j k * jimboGenerator q l m =
      jimboGenerator q l m * jimboGenerator q j k := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at h
  obtain ⟨⟨hjk, hjl, hjm⟩, ⟨hkl, hkm⟩, hlm⟩ := h
  ext w : 2
  -- The word with the letters `x, y, u, v` at the positions `j, k, l, m`.
  let W (x y u v : ι) : Fin n → ι := update (update (update (update w j x) k y) l u) m v
  have hT₁ (x y u v : ι) : jimboGenerator q j k (single (W x y u v) 1) =
      if x = y then (q : R) • single (W x y u v) 1
      else if x < y then single (W y x u v) 1
      else single (W y x u v) 1 + ((q : R) - ((q⁻¹ : Rˣ) : R)) • single (W x y u v) 1 := by
    -- Write the letters at `j, k` last, so that `jimboGenerator q j k` sees them.
    simp only [W, update_comm hkm, update_comm hkl, update_comm hjm, update_comm hjl,
      jimboGenerator_single_update_update q hjk]
  have hT₂ (x y u v : ι) : jimboGenerator q l m (single (W x y u v) 1) =
      if u = v then (q : R) • single (W x y u v) 1
      else if u < v then single (W x y v u) 1
      else single (W x y v u) 1 + ((q : R) - ((q⁻¹ : Rˣ) : R)) • single (W x y u v) 1 :=
    jimboGenerator_single_update_update q hlm _ u v
  have hW : W (w j) (w k) (w l) (w m) = w := by simp [W]
  simp only [LinearMap.coe_comp, comp_apply, lsingle_apply, Module.End.mul_apply]
  rw [← hW]
  clear hW
  generalize w j = x, w k = y, w l = u, w m = v
  rcases lt_trichotomy x y with hxy | hxy | hxy <;>
    rcases lt_trichotomy u v with huv | huv | huv <;> subst_vars <;>
    simp only [map_add, map_smul, ne_of_lt, ne_of_gt, lt_asymm, *, ↓reduceIte] <;>
    module

/-- The braid relation for Jimbo R-matrices on two pairs of strands sharing the strand `k`. This is
the Yang-Baxter equation for the Jimbo R-matrix. -/
theorem jimboGenerator_braid (q : Rˣ) {j k l : Fin n} (hjk : j ≠ k) (hkl : k ≠ l) (hjl : j ≠ l) :
    jimboGenerator (ι := ι) q j k * jimboGenerator q k l * jimboGenerator q j k =
      jimboGenerator q k l * jimboGenerator q j k * jimboGenerator q k l := by
  ext w : 2
  -- The word with the letters `x, y, z` at the positions `j, k, l`.
  let W (x y z : ι) : Fin n → ι := update (update (update w j x) k y) l z
  have hT₁ (x y z : ι) : jimboGenerator q j k (single (W x y z) 1) =
      if x = y then (q : R) • single (W x y z) 1
      else if x < y then single (W y x z) 1
      else single (W y x z) 1 + ((q : R) - ((q⁻¹ : Rˣ) : R)) • single (W x y z) 1 := by
    -- Write the letters at `j, k` last, so that `jimboGenerator q j k` sees them.
    simp only [W, update_comm hkl, update_comm hjl, jimboGenerator_single_update_update q hjk]
  have hT₂ (x y z : ι) : jimboGenerator q k l (single (W x y z) 1) =
      if y = z then (q : R) • single (W x y z) 1
      else if y < z then single (W x z y) 1
      else single (W x z y) 1 + ((q : R) - ((q⁻¹ : Rˣ) : R)) • single (W x y z) 1 :=
    jimboGenerator_single_update_update q hkl _ y z
  have hW : W (w j) (w k) (w l) = w := by simp [W]
  simp only [LinearMap.coe_comp, comp_apply, lsingle_apply, Module.End.mul_apply]
  rw [← hW]
  clear hW
  generalize w j = x, w k = y, w l = z
  have hq : (q : R) * ((q⁻¹ : Rˣ) : R) = 1 := q.mul_inv
  -- Each of the thirteen ways to order three letters is a separate computation.
  rcases lt_trichotomy x y with hxy | hxy | hxy <;>
    rcases lt_trichotomy y z with hyz | hyz | hyz <;>
    rcases lt_trichotomy x z with hxz | hxz | hxz <;> subst_vars <;> (try (exfalso; order)) <;>
    simp only [map_add, map_smul, ne_of_lt, ne_of_gt, lt_asymm, *, ↓reduceIte] <;>
    match_scalars <;> grind

/-- At `q = 1` the Jimbo R-matrix exchanges the letters at the strands `j` and `k`. -/
@[simp]
theorem jimboGenerator_one_apply_single (j k : Fin n) (w : Fin n → ι) (c : R) :
    jimboGenerator (1 : Rˣ) j k (single w c) = single (w ∘ Equiv.swap j k) c := by
  rw [← smul_single_one, map_smul, jimboGenerator_single_one]
  by_cases h : w j = w k
  · have hw : w ∘ Equiv.swap j k = w := by
      rw [Equiv.comp_swap_eq_update, h, update_eq_self, ← h, update_eq_self]
    simp [h, hw]
  · split_ifs <;> simp

variable (q : Rˣ)

/-- The Jimbo R-matrix on the two strands crossed by the elementary braid `σ i`, as a unit, with
inverse `T + (q⁻¹ - q)`. -/
noncomputable def jimboUnit (i : Fin (n - 1)) : (Module.End R ((Fin n → ι) →₀ R))ˣ where
  val := jimboGenerator q (BraidGroup.strand i) (BraidGroup.strandSucc i)
  inv := jimboGenerator q (BraidGroup.strand i) (BraidGroup.strandSucc i) +
    (((q⁻¹ : Rˣ) : R) - q) • 1
  val_inv := jimboGenerator_mul_add q (BraidGroup.strand_ne_strandSucc i)
  inv_val := add_mul_jimboGenerator q (BraidGroup.strand_ne_strandSucc i)

/-- The value of the unit `TauCeti.KnotTheory.jimboUnit`. -/
@[simp]
theorem jimboUnit_val (i : Fin (n - 1)) :
    ((jimboUnit q i : (Module.End R ((Fin n → ι) →₀ R))ˣ) : Module.End R ((Fin n → ι) →₀ R)) =
      jimboGenerator q (BraidGroup.strand i) (BraidGroup.strandSucc i) := (rfl)

/-- The value of the inverse of the unit `TauCeti.KnotTheory.jimboUnit`. -/
@[simp]
theorem jimboUnit_inv_val (i : Fin (n - 1)) :
    (((jimboUnit q i : (Module.End R ((Fin n → ι) →₀ R))ˣ)⁻¹ :
      (Module.End R ((Fin n → ι) →₀ R))ˣ) : Module.End R ((Fin n → ι) →₀ R)) =
      jimboGenerator q (BraidGroup.strand i) (BraidGroup.strandSucc i) +
        (((q⁻¹ : Rˣ) : R) - q) • 1 := (rfl)

variable (ι) in
/-- The Jimbo representation of the braid group on the q-tensor space `(Fin n → ι) →₀ R`: the
elementary braid `σ i` acts by the Jimbo R-matrix on the strands `i` and `i + 1`. -/
noncomputable def jimbo : BraidGroup n →* (Module.End R ((Fin n → ι) →₀ R))ˣ :=
  BraidGroup.lift (jimboUnit q)
    (fun h ↦ Units.ext <| by
      simpa only [Units.val_mul, jimboUnit_val] using
        jimboGenerator_mul_comm q (BraidGroup.nodup_strand_strandSucc_strand_strandSucc h))
    (fun {i j} h ↦ Units.ext <| by
      simp only [Units.val_mul, jimboUnit_val]
      have hij : i ≠ j := by
        rintro rfl
        omega
      rcases h with h | h
      · rw [BraidGroup.strand_eq_strandSucc_of_succ h]
        exact jimboGenerator_braid q (BraidGroup.strand_ne_strandSucc i)
          (BraidGroup.strandSucc_ne_strandSucc hij) (BraidGroup.strand_ne_strandSucc_of_succ h)
      · rw [BraidGroup.strand_eq_strandSucc_of_succ h]
        exact (jimboGenerator_braid q (BraidGroup.strand_ne_strandSucc j)
          (BraidGroup.strandSucc_ne_strandSucc hij.symm)
          (BraidGroup.strand_ne_strandSucc_of_succ h)).symm)

/-- The Jimbo representation takes the elementary braid `σ i` to the Jimbo R-matrix on the strands
`i` and `i + 1`. -/
@[simp]
theorem jimbo_sigma (i : Fin (n - 1)) : jimbo ι q (BraidGroup.sigma i) = jimboUnit q i :=
  BraidGroup.lift_sigma _ _ _ i

/-- The skein relation `T = T⁻¹ + (q - q⁻¹)` of an elementary braid in the Jimbo representation,
the relation behind the HOMFLY skein relation. -/
theorem val_jimbo_sigma_eq_val_inv_add (i : Fin (n - 1)) :
    (jimbo ι q (BraidGroup.sigma i) : Module.End R ((Fin n → ι) →₀ R)) =
      ((jimbo ι q (BraidGroup.sigma i))⁻¹ : (Module.End R ((Fin n → ι) →₀ R))ˣ) +
        ((q : R) - ((q⁻¹ : Rˣ) : R)) • 1 := by
  rw [jimbo_sigma, jimboUnit_val, jimboUnit_inv_val]
  module

/-- At `q = 1` the Jimbo representation is the permutation action of braids on words: a braid `b`
sends the word `w` to `w ∘ π⁻¹`, where `π` is the permutation of the strands underlying `b`. -/
@[simp]
theorem jimbo_one_apply_single (b : BraidGroup n) (w : Fin n → ι) (c : R) :
    (jimbo ι (1 : Rˣ) b : Module.End R ((Fin n → ι) →₀ R)) (single w c) =
      single (w ∘ ⇑(BraidGroup.permHom n b)⁻¹) c := by
  induction b using BraidGroup.sigma_induction_on generalizing w c with
  | sigma i =>
    rw [jimbo_sigma, jimboUnit_val, jimboGenerator_one_apply_single, BraidGroup.permHom_sigma,
      BraidGroup.transposition_eq_swap, Equiv.swap_inv]
  | one => simp
  | mul b b' hb hb' =>
    rw [map_mul, Units.val_mul, Module.End.mul_apply, hb', hb, map_mul, mul_inv_rev,
      Equiv.Perm.coe_mul, comp_assoc]
  | inv b hb =>
    simp only [map_inv, inv_inv]
    -- `b` sends `w ∘ π` to `w`, so its inverse sends `w` to `w ∘ π`.
    have h := hb (w ∘ BraidGroup.permHom n b) c
    rw [comp_assoc, ← Equiv.Perm.coe_mul, mul_inv_cancel, Equiv.Perm.coe_one, comp_id] at h
    rw [← h, ← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Module.End.one_apply]

end TauCeti.KnotTheory
