/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.WeilDeligne.Special
public import TauCeti.LinearAlgebra.Determinant.TensorProduct
import TauCeti.LinearAlgebra.Determinant.Lmul

/-!
# Determinants of raw Weil–Deligne parameters

For a raw Weil–Deligne parameter `(V, r, N)` (`TauCeti.WeilDeligneParameter`) this file constructs

* the **rank-one parameter** `(E, χ, 0)` of a character `χ : W →* Eˣ` with open kernel
  (`TauCeti.WeilDeligneParameter.ofCharacter`);
* the **determinant character** `w ↦ det r(w)` (`TauCeti.WeilDeligneParameter.detChar`) and the
  **determinant** `det D = (E, det r, 0)` (`TauCeti.WeilDeligneParameter.det`).

The determinant has zero monodromy, since a nilpotent endomorphism of a line is zero. For
finite-dimensional spaces it is an isomorphism invariant, multiplicative on direct sums, sends a
twist by `χ` to `χ ^ dim V · det`, a dual to the inverse character and a tensor product to
`det r ^ dim V' · det r' ^ dim V`. The determinant of `Sp(n)` is `ω ^ (n (n - 1) / 2)`; in
particular `det Sp(2) = ω`.

## Main definitions

* `TauCeti.WeilDeligneParameter.ofCharacter`: the rank-one parameter of a character.
* `TauCeti.WeilDeligneParameter.detChar`, `TauCeti.WeilDeligneParameter.det`: the determinant.

## Main results

* `TauCeti.WeilDeligneParameter.Iso.det_eq`: isomorphic parameters have equal determinants.
* `TauCeti.WeilDeligneParameter.detChar_ofCharacter`: a rank-one parameter is its own
  determinant.
* `TauCeti.WeilDeligneParameter.detChar_prod`, `detChar_twist`, `detChar_dual`, `detChar_tensor`:
  determinants of the operations.
* `TauCeti.WeilDeligneParameter.detChar_special`, `TauCeti.WeilDeligneParameter.det_special_two`:
  `det Sp(n) = ω ^ (n (n - 1) / 2)` and `det Sp(2) = ω`.

## References

* P. Deligne, *Les constantes des équations fonctionnelles des fonctions L*, in *Modular functions
  of one variable II*, Lecture Notes in Math. 349 (1973), §8.4.1, p. 568, and the proof of §8.4.3,
  p. 569.
-/

public section

noncomputable section

open Module

namespace TauCeti

namespace WeilDeligneParameter

variable {E W V V' : Type*} [Field E] [Group W] [TopologicalSpace W] [AddCommGroup V]
  [Module E V] [AddCommGroup V'] [Module E V'] {deg : W →* Multiplicative ℤ} {q : ℕ}

/-! ### Rank-one parameters -/

variable (deg q) in
/-- The **rank-one parameter** `(E, χ, 0)` of a character `χ : W →* Eˣ` with open kernel:
`w` acts on the line `E` by multiplication by `χ(w)`, and the monodromy is zero. -/
def ofCharacter (χ : W →* Eˣ) (hχ : IsOpen (χ.ker : Set W)) :
    WeilDeligneParameter E W E deg q where
  r := (Algebra.lmul E E).toMonoidHom.comp ((Units.coeHom E).comp χ)
  isOpen_ker := by
    convert hχ using 2
    ext w
    simp [LinearMap.ext_ring_iff]
  N := 0
  isNilpotent_N := IsNilpotent.zero
  conj_N w := by simp

variable {χ : W →* Eˣ} {hχ : IsOpen (χ.ker : Set W)}

@[simp]
theorem ofCharacter_r_apply (w : W) (x : E) : (ofCharacter deg q χ hχ).r w x = χ w * x :=
  (rfl)

@[simp]
theorem ofCharacter_N : (ofCharacter deg q χ hχ).N = 0 :=
  (rfl)

/-! ### Determinant characters -/

/-- The **determinant character** `w ↦ det r(w)` of a raw Weil–Deligne parameter. -/
def detChar (D : WeilDeligneParameter E W V deg q) : W →* Eˣ :=
  (Units.map (LinearMap.det : Module.End E V →* E)).comp D.r.asGroupHom

@[simp]
theorem coe_detChar_apply (D : WeilDeligneParameter E W V deg q) (w : W) :
    (D.detChar w : E) = LinearMap.det (D.r w) := by
  simp [detChar, Representation.asGroupHom_apply]

/-- An element acting trivially has determinant one. -/
theorem ker_le_ker_detChar (D : WeilDeligneParameter E W V deg q) : D.r.ker ≤ D.detChar.ker :=
  fun w hw ↦ by
    rw [MonoidHom.mem_ker] at hw ⊢
    ext
    simp [hw]

/-- The determinant character of the rank-one parameter of `χ` is `χ`. -/
@[simp]
theorem detChar_ofCharacter : (ofCharacter deg q χ hχ).detChar = χ := by
  ext w
  rw [coe_detChar_apply]
  exact LinearMap.det_mulLeft (χ w : E)

/-- Isomorphic parameters have the same determinant character. -/
theorem Iso.detChar_eq {D : WeilDeligneParameter E W V deg q}
    {D' : WeilDeligneParameter E W V' deg q} (f : Iso D D') : D.detChar = D'.detChar := by
  ext w
  rw [f.eq_transport]
  simpa [transport_r, LinearEquiv.conjAlgEquiv_apply] using
    (LinearMap.det_conj (D.r w) f.toLinearEquiv).symm

/-- The determinant of a direct sum is the product of the determinants. -/
@[simp]
theorem detChar_prod [FiniteDimensional E V] [FiniteDimensional E V']
    (D : WeilDeligneParameter E W V deg q) (D' : WeilDeligneParameter E W V' deg q) :
    (D.prod D').detChar = D.detChar * D'.detChar := by
  ext w
  simp only [coe_detChar_apply, MonoidHom.mul_apply, Units.val_mul, prod_r]
  -- `Representation.prod` acts by `LinearMap.prodMap` by definition; Mathlib's `simps` lemma
  -- `Representation.prod_apply_apply` only states this pointwise.
  exact LinearMap.det_prodMap (D.r w) (D'.r w)

/-- The determinant of the dual is the inverse of the determinant. -/
@[simp]
theorem detChar_dual [FiniteDimensional E V] (D : WeilDeligneParameter E W V deg q) :
    D.dual.detChar = D.detChar⁻¹ := by
  ext w
  rw [MonoidHom.inv_apply, ← map_inv]
  simp [Representation.dual_apply, ← LinearMap.dualMap_def, LinearMap.det_dualMap, -map_inv]

/-- The determinant of `Sp(n)` is `ω ^ (n (n - 1) / 2)`. -/
@[simp]
theorem detChar_special (hdeg : Continuous deg) (hq : (q : E) ≠ 0) (n : ℕ) :
    (special q n hdeg hq).detChar = omega deg hq ^ (n * (n - 1) / 2) := by
  ext w
  simp only [coe_detChar_apply, special_r, LinearMap.det_lmul_pi, MonoidHom.pow_apply,
    Units.val_pow_eq_pow_val, specialWeight_apply_eq_omega_pow, Finset.prod_pow_eq_pow_sum,
    Fin.sum_univ_eq_sum_range (fun i ↦ i) n, Finset.sum_range_id]

/-! ### Determinants -/

section Determinant

variable [SeparatelyContinuousMul W]

/-- The **determinant** `(E, det r, 0)` of a raw Weil–Deligne parameter. -/
def det (D : WeilDeligneParameter E W V deg q) : WeilDeligneParameter E W E deg q :=
  ofCharacter deg q D.detChar (Subgroup.isOpen_mono D.ker_le_ker_detChar D.isOpen_ker)

@[simp]
theorem det_r_apply (D : WeilDeligneParameter E W V deg q) (w : W) (x : E) :
    D.det.r w x = LinearMap.det (D.r w) * x := by
  simp [det]

/-- The determinant has zero monodromy. -/
@[simp]
theorem det_N (D : WeilDeligneParameter E W V deg q) : D.det.N = 0 :=
  (rfl)

/-- The determinant character of the determinant is the determinant character. -/
@[simp]
theorem detChar_det (D : WeilDeligneParameter E W V deg q) : D.det.detChar = D.detChar :=
  detChar_ofCharacter

/-- Two parameters with the same determinant character have the same determinant. -/
theorem det_eq_det_of_detChar_eq {D : WeilDeligneParameter E W V deg q}
    {D' : WeilDeligneParameter E W V' deg q} (h : D.detChar = D'.detChar) : D.det = D'.det := by
  unfold det
  congr 1

/-- The determinant of a parameter with character `χ` is the rank-one parameter of `χ`. -/
theorem det_eq_ofCharacter {D : WeilDeligneParameter E W V deg q} (h : D.detChar = χ) :
    D.det = ofCharacter deg q χ hχ := by
  subst h
  rfl

/-- Isomorphic parameters have the same determinant. -/
theorem Iso.det_eq {D : WeilDeligneParameter E W V deg q}
    {D' : WeilDeligneParameter E W V' deg q} (f : Iso D D') : D.det = D'.det :=
  det_eq_det_of_detChar_eq f.detChar_eq

/-- The determinant of a twist by `χ` is `χ ^ dim V · det`. -/
@[simp]
theorem detChar_twist (D : WeilDeligneParameter E W V deg q) :
    (D.twist χ hχ).detChar = χ ^ finrank E V * D.detChar := by
  ext w
  simp [twist_r, Representation.charTwist_apply, LinearMap.det_smul]

/-- The determinant of a tensor product is `det r ^ dim V' · det r' ^ dim V`. -/
@[simp]
theorem detChar_tensor [FiniteDimensional E V] [FiniteDimensional E V']
    (D : WeilDeligneParameter E W V deg q) (D' : WeilDeligneParameter E W V' deg q) :
    (D.tensor D').detChar = D.detChar ^ finrank E V' * D'.detChar ^ finrank E V := by
  ext w
  simp [tensor_r, Representation.tprod_apply, LinearMap.det_tensorProductMap]

/-- **`det Sp(2) = ω`** (Deligne 1973, proof of §8.4.3, p. 569). -/
theorem det_special_two (hdeg : Continuous deg) (hq : (q : E) ≠ 0) :
    (special q 2 hdeg hq).det = ofCharacter deg q (omega deg hq) (isOpen_ker_omega hdeg hq) :=
  det_eq_ofCharacter (by rw [detChar_special]; exact pow_one (omega deg hq))

end Determinant

end WeilDeligneParameter

end TauCeti
