/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LSum
public import TauCeti.KnotTheory.Jimbo.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.Order

/-!
# The signed checked R-matrix on word spaces

Let `ι` be a linearly ordered alphabet in which every letter is designated positive or negative
(by a decidable predicate `pos`), and let `s` be an element of a commutative ring `R`; put
`Q = s ^ 2`, so that in the positive-real setting `s = √Q`. The *signed checked R-matrix* acts on
two strands `j` and `k` of a basis word `w` of the word space `(Fin n → ι) →₀ R`, depending only on
the letters `a = w j` and `b = w k`:

* if `a = b`, the word is multiplied by `Q` when `a` is positive and by `-1` when `a` is negative;
* if `a < b`, it is sent to `(Q - 1) • w - s • w'`, where `w'` exchanges the two letters;
* if `b < a`, it is sent to `-(s • w')`.

On a two-letter block `{a ⊗ b, b ⊗ a}` with `a < b` its matrix is `[[Q - 1, -s], [-s, 0]]`. Write
`X = TauCeti.signedCheckedR pos s j k`. It satisfies the quadratic relation `(X - Q) (X + 1) = 0`,
so over a field its eigenvalues lie among `Q` and `-1`; operators on disjoint pairs of strands
commute; and operators on two pairs sharing a strand satisfy the braid relation. These identities
hold for every `s`, so the adjacent operators satisfy the defining relations of the type-A Hecke
algebra in the normalization `gᵢ = s Tᵢ`, `(gᵢ - Q) (gᵢ + 1) = 0`. When `s` is a unit they are
invertible and define a braid group representation `TauCeti.signedCheckedRep`, and the rescaled
operators `s⁻¹ • X` satisfy the quadratic relation `T * T = (s - s⁻¹) • T + 1` in the convention
`(Tᵢ - s) (Tᵢ + s⁻¹) = 0`.

The matrix of the operator in the word basis is symmetric, the algebraic form of its
self-adjointness for real `s` on the Hilbert space with this orthonormal basis. The atomic tensor
models of Markov traces on the Hecke algebras with a positive real parameter are built from these
operators, on ordered alphabets of positive and negative letters that also carry weights.

If every letter is positive, reversing the order of the alphabet turns the operator into a
rescaled Jimbo R-matrix at the parameter `-s`: `X = (-s) • T_{-s}` on `ιᵒᵈ`
(`TauCeti.signedCheckedR_eq_jimboGenerator`). Negative letters have no such description; signed
alphabets of this kind arise from the vector representation of the quantum supergroup
`U_q(gl(m|n))`.

## Main definitions

* `TauCeti.signedCheckedR`: the signed checked R-matrix acting on two strands of the word space.
* `TauCeti.signedCheckedRUnit`: for a unit `s`, the operator on two adjacent strands, as a unit.
* `TauCeti.signedCheckedRep`: the braid group representation on the word space.

## Main results

* `TauCeti.signedCheckedR_mul_self`: the quadratic relation `X * X = (Q - 1) • X + Q • 1`.
* `TauCeti.signedCheckedR_mul_comm`: operators on disjoint pairs of strands commute.
* `TauCeti.signedCheckedR_braid`: the braid relation.
* `TauCeti.signedCheckedR_single_apply_comm`: the matrix in the word basis is symmetric.
* `TauCeti.inv_smul_signedCheckedR_mul_self`: the Hecke quadratic relation for `s⁻¹ • X`.
* `TauCeti.signedCheckedR_eq_jimboGenerator`: the comparison with the Jimbo R-matrix for an
  alphabet of positive letters.

## References

* Yu. A. Neretin, *Some remarks on traces on the infinite-dimensional Iwahori–Hecke algebra*,
  arXiv:2101.02133, §§1.6–1.7 and §3.1, for the signed product model.
* M. Jimbo, *A q-analogue of U(gl(N+1)), Hecke algebra, and the Yang-Baxter equation*, Lett.
  Math. Phys. 11 (1986), 247–252.
-/

public section

open Function Finsupp

namespace TauCeti

variable {R : Type*} [CommRing R] {ι : Type*} [LinearOrder ι] (pos : ι → Prop) [DecidablePred pos]
  {n : ℕ}

/-- The signed checked R-matrix acting on the strands `j` and `k` of the word space
`(Fin n → ι) →₀ R`, with `Q = s ^ 2`. On a basis word `w` it multiplies `w` by `Q` if
`w j = w k` is positive and by `-1` if it is negative; it sends `w` to `(Q - 1) • w - s • w'` if
`w j < w k`, and to `-(s • w')` if `w k < w j`, where `w'` exchanges the letters at `j` and
`k`. -/
noncomputable def signedCheckedR (s : R) (j k : Fin n) : Module.End R ((Fin n → ι) →₀ R) :=
  linearCombination R fun w ↦
    if w j = w k then (if pos (w j) then s ^ 2 else -1) • single w 1
    else if w j < w k then (s ^ 2 - 1) • single w 1 - s • single (w ∘ Equiv.swap j k) 1
    else -(s • single (w ∘ Equiv.swap j k) 1)

/-- The value of the signed checked R-matrix on a basis word. -/
@[simp]
theorem signedCheckedR_single_one (s : R) (j k : Fin n) (w : Fin n → ι) :
    signedCheckedR pos s j k (single w 1) =
      if w j = w k then (if pos (w j) then s ^ 2 else -1) • single w 1
      else if w j < w k then (s ^ 2 - 1) • single w 1 - s • single (w ∘ Equiv.swap j k) 1
      else -(s • single (w ∘ Equiv.swap j k) 1) := by
  simp [signedCheckedR]

/-- The value of the signed checked R-matrix on the strands `j` and `k` on a basis word whose
letters at `j` and `k` are `x` and `y`. -/
theorem signedCheckedR_single_update_update (s : R) {j k : Fin n} (hjk : j ≠ k)
    (w : Fin n → ι) (x y : ι) :
    signedCheckedR pos s j k (single (update (update w j x) k y) 1) =
      if x = y then (if pos x then s ^ 2 else -1) • single (update (update w j x) k y) 1
      else if x < y then
        (s ^ 2 - 1) • single (update (update w j x) k y) 1 -
          s • single (update (update w j y) k x) 1
      else -(s • single (update (update w j y) k x) 1) := by
  have hswap : update (update w j x) k y ∘ Equiv.swap j k = update (update w j y) k x := by
    rw [Equiv.comp_swap_eq_update]
    simp [update_of_ne hjk, update_comm hjk.symm]
  rw [signedCheckedR_single_one, hswap]
  simp only [update_of_ne hjk, Function.update_self]

/-- The quadratic relation `X * X = (Q - 1) • X + Q • 1`, `Q = s ^ 2`, of the signed checked
R-matrix, that is `(X - Q) (X + 1) = 0`; over a field its eigenvalues lie among `Q` and `-1`. -/
theorem signedCheckedR_mul_self (s : R) (j k : Fin n) :
    signedCheckedR pos s j k * signedCheckedR pos s j k =
      (s ^ 2 - 1) • signedCheckedR pos s j k + s ^ 2 • 1 := by
  ext w : 2
  rcases eq_or_ne j k with rfl | hjk
  · -- On a single strand the operator is diagonal, with diagonal entries `Q` or `-1`.
    by_cases hw : pos (w j) <;>
      simp only [LinearMap.coe_comp, comp_apply, lsingle_apply, Module.End.mul_apply,
        LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
        signedCheckedR_single_one, hw, map_smul, ↓reduceIte] <;> module
  have hR := signedCheckedR_single_update_update pos s hjk w
  have hW : update (update w j (w j)) k (w k) = w := by simp
  simp only [LinearMap.coe_comp, comp_apply, lsingle_apply, Module.End.mul_apply,
    LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply]
  rw [← hW]
  clear hW
  generalize w j = x, w k = y
  rcases lt_trichotomy x y with hxy | hxy | hxy <;> subst_vars <;>
    simp only [map_sub, map_neg, map_smul, ne_of_lt, ne_of_gt, lt_asymm, *, ↓reduceIte] <;>
    (try split_ifs) <;> module

/-- Signed checked R-matrices on disjoint pairs of strands commute. -/
theorem signedCheckedR_mul_comm (s : R) {j k l m : Fin n} (h : [j, k, l, m].Nodup) :
    signedCheckedR pos s j k * signedCheckedR pos s l m =
      signedCheckedR pos s l m * signedCheckedR pos s j k := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at h
  obtain ⟨⟨hjk, hjl, hjm⟩, ⟨hkl, hkm⟩, hlm⟩ := h
  ext w : 2
  -- The word with the letters `x, y, u, v` at the positions `j, k, l, m`.
  let W (x y u v : ι) : Fin n → ι := update (update (update (update w j x) k y) l u) m v
  have hR₁ (x y u v : ι) : signedCheckedR pos s j k (single (W x y u v) 1) =
      if x = y then (if pos x then s ^ 2 else -1) • single (W x y u v) 1
      else if x < y then (s ^ 2 - 1) • single (W x y u v) 1 - s • single (W y x u v) 1
      else -(s • single (W y x u v) 1) := by
    -- Write the letters at `j, k` last, so that `signedCheckedR pos s j k` sees them.
    simp only [W, update_comm hkm, update_comm hkl, update_comm hjm, update_comm hjl,
      signedCheckedR_single_update_update pos s hjk]
  have hR₂ (x y u v : ι) : signedCheckedR pos s l m (single (W x y u v) 1) =
      if u = v then (if pos u then s ^ 2 else -1) • single (W x y u v) 1
      else if u < v then (s ^ 2 - 1) • single (W x y u v) 1 - s • single (W x y v u) 1
      else -(s • single (W x y v u) 1) :=
    signedCheckedR_single_update_update pos s hlm _ u v
  have hW : W (w j) (w k) (w l) (w m) = w := by simp [W]
  simp only [LinearMap.coe_comp, comp_apply, lsingle_apply, Module.End.mul_apply]
  rw [← hW]
  clear hW
  generalize w j = x, w k = y, w l = u, w m = v
  rcases lt_trichotomy x y with hxy | hxy | hxy <;>
    rcases lt_trichotomy u v with huv | huv | huv <;> subst_vars <;>
    simp only [map_sub, map_neg, map_smul, ne_of_lt, ne_of_gt, lt_asymm, *, ↓reduceIte] <;>
    (try split_ifs) <;> module

/-- The braid relation for signed checked R-matrices on two pairs of strands sharing the strand
`k`, the Yang-Baxter equation for the signed checked R-matrix. -/
theorem signedCheckedR_braid (s : R) {j k l : Fin n} (hjk : j ≠ k) (hkl : k ≠ l) (hjl : j ≠ l) :
    signedCheckedR pos s j k * signedCheckedR pos s k l * signedCheckedR pos s j k =
      signedCheckedR pos s k l * signedCheckedR pos s j k * signedCheckedR pos s k l := by
  ext w : 2
  -- The word with the letters `x, y, z` at the positions `j, k, l`.
  let W (x y z : ι) : Fin n → ι := update (update (update w j x) k y) l z
  have hR₁ (x y z : ι) : signedCheckedR pos s j k (single (W x y z) 1) =
      if x = y then (if pos x then s ^ 2 else -1) • single (W x y z) 1
      else if x < y then (s ^ 2 - 1) • single (W x y z) 1 - s • single (W y x z) 1
      else -(s • single (W y x z) 1) := by
    -- Write the letters at `j, k` last, so that `signedCheckedR pos s j k` sees them.
    simp only [W, update_comm hkl, update_comm hjl, signedCheckedR_single_update_update pos s hjk]
  have hR₂ (x y z : ι) : signedCheckedR pos s k l (single (W x y z) 1) =
      if y = z then (if pos y then s ^ 2 else -1) • single (W x y z) 1
      else if y < z then (s ^ 2 - 1) • single (W x y z) 1 - s • single (W x z y) 1
      else -(s • single (W x z y) 1) :=
    signedCheckedR_single_update_update pos s hkl _ y z
  have hW : W (w j) (w k) (w l) = w := by simp [W]
  simp only [LinearMap.coe_comp, comp_apply, lsingle_apply, Module.End.mul_apply]
  rw [← hW]
  clear hW
  generalize w j = x, w k = y, w l = z
  -- Each of the thirteen ways to order three letters is a separate computation; the signs of
  -- the letters only enter through the coincident ones.
  rcases lt_trichotomy x y with hxy | hxy | hxy <;>
    rcases lt_trichotomy y z with hyz | hyz | hyz <;>
    rcases lt_trichotomy x z with hxz | hxz | hxz <;> subst_vars <;> (try (exfalso; order)) <;>
    simp only [map_sub, map_neg, map_smul, ne_of_lt, ne_of_gt, lt_asymm, *, ↓reduceIte] <;>
    (try split_ifs) <;> module

/-- The matrix of the signed checked R-matrix in the word basis is symmetric: the coefficient of
`v` in the image of `w` is the coefficient of `w` in the image of `v`. For real `s` this is the
self-adjointness of the operator for the inner product in which the words are orthonormal. -/
theorem signedCheckedR_single_apply_comm (s : R) (j k : Fin n) (v w : Fin n → ι) :
    signedCheckedR pos s j k (single w 1) v = signedCheckedR pos s j k (single v 1) w := by
  by_cases hvw : v = w
  · rw [hvw]
  have hswap {u u' : Fin n → ι} : u = u' ∘ Equiv.swap j k → u' = u ∘ Equiv.swap j k := by
    rintro rfl
    ext i
    simp
  simp only [signedCheckedR_single_one]
  by_cases hv : v = w ∘ Equiv.swap j k
  · -- `v` and `w` differ by exchanging their letters at `j` and `k`, which are distinct.
    have hw : w = v ∘ Equiv.swap j k := hswap hv
    have hvj : v j = w k := by simp [hv]
    have hvk : v k = w j := by simp [hv]
    have hne : w j ≠ w k := by
      intro h
      refine hvw (hv.trans (funext fun i ↦ ?_))
      rw [comp_apply, Equiv.swap_apply_def]
      split_ifs <;> subst_vars <;> simp [h]
    rcases lt_or_gt_of_ne hne with h | h <;>
      simp [hvj, hvk, h, hne, hne.symm, lt_asymm h, ← hv, ← hw, hvw, Ne.symm hvw]
  · -- Otherwise neither word occurs in the image of the other.
    have hw : w ≠ v ∘ Equiv.swap j k := fun h ↦ hv (hswap h)
    have hv' : w ∘ Equiv.swap j k ≠ v := fun h ↦ hv h.symm
    have hw' : v ∘ Equiv.swap j k ≠ w := fun h ↦ hw h.symm
    split_ifs <;> simp [hvw, Ne.symm hvw, hv', hw']

section Unit

variable (s : Rˣ)

/-- The signed checked R-matrix is invertible when `s` is a unit, with right inverse
`s⁻¹ ^ 2 • (X + (1 - Q) • 1)`. -/
theorem signedCheckedR_mul_smul_add (j k : Fin n) :
    signedCheckedR pos (s : R) j k * ((((s⁻¹ : Rˣ) : R) ^ 2) •
      (signedCheckedR pos (s : R) j k + (1 - (s : R) ^ 2) • 1)) = 1 := by
  have hs : ((s⁻¹ : Rˣ) : R) ^ 2 * (s : R) ^ 2 = 1 := by
    rw [← mul_pow, Units.inv_mul, one_pow]
  rw [mul_smul_comm, mul_add, signedCheckedR_mul_self pos _ j k, mul_smul_comm, mul_one]
  match_scalars
  · ring
  · linear_combination hs

/-- The signed checked R-matrix is invertible when `s` is a unit, with left inverse
`s⁻¹ ^ 2 • (X + (1 - Q) • 1)`. -/
theorem smul_add_mul_signedCheckedR (j k : Fin n) :
    ((((s⁻¹ : Rˣ) : R) ^ 2) • (signedCheckedR pos (s : R) j k + (1 - (s : R) ^ 2) • 1)) *
      signedCheckedR pos (s : R) j k = 1 := by
  have hs : ((s⁻¹ : Rˣ) : R) ^ 2 * (s : R) ^ 2 = 1 := by
    rw [← mul_pow, Units.inv_mul, one_pow]
  rw [smul_mul_assoc, add_mul, signedCheckedR_mul_self pos _ j k, smul_mul_assoc, one_mul]
  match_scalars
  · ring
  · linear_combination hs

/-- **The Hecke normalization.** For a unit `s`, the rescaled operator `T = s⁻¹ • X` satisfies the
type-A Hecke quadratic relation `T * T = (s - s⁻¹) • T + 1`, equivalently
`(T - s) * (T + s⁻¹) = 0`. -/
theorem inv_smul_signedCheckedR_mul_self (j k : Fin n) :
    (((s⁻¹ : Rˣ) : R) • signedCheckedR pos (s : R) j k) *
        (((s⁻¹ : Rˣ) : R) • signedCheckedR pos (s : R) j k) =
      ((s : R) - ((s⁻¹ : Rˣ) : R)) • (((s⁻¹ : Rˣ) : R) • signedCheckedR pos (s : R) j k) + 1 := by
  have hs : ((s⁻¹ : Rˣ) : R) * (s : R) = 1 := Units.inv_mul s
  rw [smul_mul_smul_comm, signedCheckedR_mul_self pos _ j k]
  match_scalars
  · linear_combination (((s⁻¹ : Rˣ) : R) * (s : R)) * hs
  · linear_combination (((s⁻¹ : Rˣ) : R) * (s : R) + 1) * hs

/-- The signed checked R-matrix on the two strands crossed by the elementary braid `σ i`, as a
unit, with inverse `s⁻¹ ^ 2 • (X + (1 - Q) • 1)`. -/
noncomputable def signedCheckedRUnit (i : Fin (n - 1)) : (Module.End R ((Fin n → ι) →₀ R))ˣ where
  val := signedCheckedR pos (s : R) (BraidGroup.strand i) (BraidGroup.strandSucc i)
  inv := (((s⁻¹ : Rˣ) : R) ^ 2) •
    (signedCheckedR pos (s : R) (BraidGroup.strand i) (BraidGroup.strandSucc i) +
      (1 - (s : R) ^ 2) • 1)
  val_inv := signedCheckedR_mul_smul_add pos s _ _
  inv_val := smul_add_mul_signedCheckedR pos s _ _

/-- The value of the unit `TauCeti.signedCheckedRUnit`. -/
@[simp]
theorem signedCheckedRUnit_val (i : Fin (n - 1)) :
    ((signedCheckedRUnit pos s i : (Module.End R ((Fin n → ι) →₀ R))ˣ) :
      Module.End R ((Fin n → ι) →₀ R)) =
      signedCheckedR pos (s : R) (BraidGroup.strand i) (BraidGroup.strandSucc i) := (rfl)

/-- The value of the inverse of the unit `TauCeti.signedCheckedRUnit`. -/
@[simp]
theorem signedCheckedRUnit_inv_val (i : Fin (n - 1)) :
    (((signedCheckedRUnit pos s i : (Module.End R ((Fin n → ι) →₀ R))ˣ)⁻¹ :
      (Module.End R ((Fin n → ι) →₀ R))ˣ) : Module.End R ((Fin n → ι) →₀ R)) =
      (((s⁻¹ : Rˣ) : R) ^ 2) •
        (signedCheckedR pos (s : R) (BraidGroup.strand i) (BraidGroup.strandSucc i) +
          (1 - (s : R) ^ 2) • 1) := (rfl)

/-- The signed checked representation of the braid group on the word space `(Fin n → ι) →₀ R`:
the elementary braid `σ i` acts by the signed checked R-matrix on the strands `i` and `i + 1`. -/
noncomputable def signedCheckedRep : BraidGroup n →* (Module.End R ((Fin n → ι) →₀ R))ˣ :=
  BraidGroup.lift (signedCheckedRUnit pos s)
    (fun h ↦ Units.ext <| by
      simpa only [Units.val_mul, signedCheckedRUnit_val] using
        signedCheckedR_mul_comm pos (s : R)
          (BraidGroup.nodup_strand_strandSucc_strand_strandSucc h))
    (fun {i j} h ↦ Units.ext <| by
      simp only [Units.val_mul, signedCheckedRUnit_val]
      have hij : i ≠ j := by
        rintro rfl
        omega
      rcases h with h | h
      · rw [BraidGroup.strand_eq_strandSucc_of_succ h]
        exact signedCheckedR_braid pos (s : R) (BraidGroup.strand_ne_strandSucc i)
          (BraidGroup.strandSucc_ne_strandSucc hij) (BraidGroup.strand_ne_strandSucc_of_succ h)
      · rw [BraidGroup.strand_eq_strandSucc_of_succ h]
        exact (signedCheckedR_braid pos (s : R) (BraidGroup.strand_ne_strandSucc j)
          (BraidGroup.strandSucc_ne_strandSucc hij.symm)
          (BraidGroup.strand_ne_strandSucc_of_succ h)).symm)

/-- The signed checked representation takes the elementary braid `σ i` to the signed checked
R-matrix on the strands `i` and `i + 1`. -/
@[simp]
theorem signedCheckedRep_sigma (i : Fin (n - 1)) :
    signedCheckedRep pos s (BraidGroup.sigma i) = signedCheckedRUnit (n := n) pos s i :=
  BraidGroup.lift_sigma _ _ _ i

/-- **Comparison with the Jimbo R-matrix.** If every letter is positive, the signed checked
R-matrix is the Jimbo R-matrix at the parameter `-s`, rescaled by `-s`, on the alphabet with the
reversed order: it is the conjugate of `(-s) • T_{-s}` on `(Fin n → ιᵒᵈ) →₀ R` by the relabelling
of words along `ι ≃ ιᵒᵈ`. -/
theorem signedCheckedR_eq_jimboGenerator (hpos : ∀ a, pos a) (j k : Fin n) :
    signedCheckedR pos (s : R) j k =
      (Finsupp.domLCongr (Equiv.arrowCongr (Equiv.refl (Fin n)) OrderDual.toDual) :
        ((Fin n → ι) →₀ R) ≃ₗ[R] ((Fin n → ιᵒᵈ) →₀ R)).symm.conj
        ((-(s : R)) • KnotTheory.jimboGenerator (ι := ιᵒᵈ) (-s) j k) := by
  have hw (w : Fin n → ι) :
      Equiv.arrowCongr (Equiv.refl (Fin n)) OrderDual.toDual w = OrderDual.toDual ∘ w := by
    ext i
    simp
  have he (u : Fin n → ι) (c : R) :
      (Finsupp.domLCongr (Equiv.arrowCongr (Equiv.refl (Fin n)) OrderDual.toDual) :
        ((Fin n → ι) →₀ R) ≃ₗ[R] ((Fin n → ιᵒᵈ) →₀ R)).symm
        (single (OrderDual.toDual ∘ u) c) = single u c := by
    rw [LinearEquiv.symm_apply_eq, domLCongr_single, hw]
  have hs : (s : R) * ((s⁻¹ : Rˣ) : R) = 1 := Units.mul_inv s
  rw [LinearEquiv.symm_conj_apply]
  ext w : 2
  simp only [LinearMap.coe_comp, comp_apply, lsingle_apply, LinearEquiv.coe_coe,
    domLCongr_single, hw, LinearMap.smul_apply, KnotTheory.jimboGenerator_single_one,
    OrderDual.toDual_inj, OrderDual.toDual_lt_toDual, comp_assoc, signedCheckedR_single_one, hpos,
    ↓reduceIte, Units.val_neg, inv_neg]
  -- Compare the two operators in each of the three ways the two letters can be ordered.
  split_ifs <;> (try (exfalso; order)) <;> simp only [map_add, map_smul, he] <;>
    match_scalars <;> first | ring1 | linear_combination hs

end Unit

end TauCeti
