/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.WeilDeligne.Special
public import TauCeti.LinearAlgebra.Determinant.TensorProduct

/-!
# Determinants and restriction of raw Weil–Deligne parameters

For a raw Weil–Deligne parameter `(V, r, N)` (`TauCeti.WeilDeligneParameter`) this file constructs

* the **rank-one parameter** `(E, χ, 0)` of a character `χ : W →* Eˣ` with open kernel
  (`TauCeti.WeilDeligneParameter.ofCharacter`);
* the **determinant character** `w ↦ det r(w)` (`TauCeti.WeilDeligneParameter.detChar`) and the
  **determinant** `det D = (E, det r, 0)` (`TauCeti.WeilDeligneParameter.det`);
* the **restriction** along a continuous homomorphism `ι : W' →* W` of groups with degree maps
  satisfying `deg (ι w) = f · deg' w` (`TauCeti.WeilDeligneParameter.restrict`). It is a raw
  parameter for `W'` with `q ^ f` in place of `q`: for the Weil group `W_L ≤ W_F` of a finite
  extension of local fields, `f` is the residue degree and `q ^ f` the residue cardinality of
  `L`.

The determinant has zero monodromy, since a nilpotent endomorphism of a line is zero. For
finite-dimensional spaces it is an isomorphism invariant, multiplicative on direct sums, sends a
twist by `χ` to `χ ^ dim V · det`, a dual to the inverse character and a tensor product to
`det r ^ dim V' · det r' ^ dim V`. The determinant of `Sp(n)` is `ω ^ (n (n - 1) / 2)`; in
particular `det Sp(2) = ω`. Restriction is functorial and commutes with direct sums, duals,
tensor products and determinants, and the restriction of `Sp(n)` is `Sp(n)` for `q ^ f`.

## Main definitions

* `TauCeti.WeilDeligneParameter.ofCharacter`: the rank-one parameter of a character.
* `TauCeti.WeilDeligneParameter.detChar`, `TauCeti.WeilDeligneParameter.det`: the determinant.
* `TauCeti.WeilDeligneParameter.restrict`: restriction along `ι : W' →* W`.

## Main results

* `TauCeti.WeilDeligneParameter.Iso.det_eq`: isomorphic parameters have equal determinants.
* `TauCeti.WeilDeligneParameter.detChar_ofCharacter`: a rank-one parameter is its own
  determinant.
* `TauCeti.WeilDeligneParameter.detChar_prod`, `detChar_twist`, `detChar_dual`, `detChar_tensor`:
  determinants of the operations.
* `TauCeti.WeilDeligneParameter.detChar_special`, `TauCeti.WeilDeligneParameter.det_special_two`:
  `det Sp(n) = ω ^ (n (n - 1) / 2)` and `det Sp(2) = ω`.
* `TauCeti.WeilDeligneParameter.restrict_special`: restriction of `Sp(n)`.

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

variable {E W W' V V' : Type*} [Field E] [Group W] [TopologicalSpace W] [Group W']
  [TopologicalSpace W'] [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']
  {deg : W →* Multiplicative ℤ} {deg' : W' →* Multiplicative ℤ} {q : ℕ}

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
    change Algebra.lmul E E (χ w : E) = 1 ↔ χ w = 1
    rw [← map_one (Algebra.lmul E E), (Algebra.lmul_injective (R := E) (A := E)).eq_iff,
      Units.val_eq_one]
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
  rw [f.eq_transport, coe_detChar_apply, coe_detChar_apply, transport_r]
  exact (LinearMap.det_conj (D.r w) f.toLinearEquiv).symm

/-- The determinant of a direct sum is the product of the determinants. -/
theorem detChar_prod [FiniteDimensional E V] [FiniteDimensional E V']
    (D : WeilDeligneParameter E W V deg q) (D' : WeilDeligneParameter E W V' deg q) :
    (D.prod D').detChar = D.detChar * D'.detChar := by
  ext w
  rw [coe_detChar_apply, MonoidHom.mul_apply, Units.val_mul, coe_detChar_apply,
    coe_detChar_apply, prod_r]
  exact LinearMap.det_prodMap _ _

/-- The determinant of the dual is the inverse of the determinant. -/
theorem detChar_dual [FiniteDimensional E V] (D : WeilDeligneParameter E W V deg q) :
    D.dual.detChar = D.detChar⁻¹ := by
  ext w
  have h : Module.Dual.transpose (R := E) (D.r w⁻¹) = (D.r w⁻¹).dualMap := rfl
  rw [coe_detChar_apply, dual_r, Representation.dual_apply, h, LinearMap.det_dualMap,
    ← coe_detChar_apply, map_inv, MonoidHom.inv_apply]

/-- The determinant of multiplication by `f` on `Eⁿ` is `∏ i, f i`. -/
private theorem det_lmul_pi {n : ℕ} (f : Fin n → E) :
    LinearMap.det (Algebra.lmul E (Fin n → E) f) = ∏ i, f i := by
  have : Algebra.lmul E (Fin n → E) f = Matrix.toLin' (Matrix.diagonal f) := by
    ext v i
    simp [Matrix.mulVec_diagonal]
  rw [this, LinearMap.det_toLin', Matrix.det_diagonal]

/-- The determinant of `Sp(n)` is `ω ^ (n (n - 1) / 2)`. -/
theorem detChar_special (hdeg : Continuous deg) (hq : (q : E) ≠ 0) (n : ℕ) :
    (special q n hdeg hq).detChar = omega deg hq ^ (n * (n - 1) / 2) := by
  ext w
  rw [coe_detChar_apply, special_r, det_lmul_pi, MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
  simp_rw [specialWeight_apply_eq_omega_pow]
  rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun i ↦ i) n, Finset.sum_range_id]

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
theorem detChar_twist (D : WeilDeligneParameter E W V deg q) :
    (D.twist χ hχ).detChar = χ ^ finrank E V * D.detChar := by
  ext w
  simp [twist_r, Representation.charTwist_apply, LinearMap.det_smul]

/-- The determinant of a tensor product is `det r ^ dim V' · det r' ^ dim V`. -/
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

/-! ### Restriction -/

section Restriction

variable (ι : W' →* W) (hι : Continuous ι) (f : ℕ)
  (hf : ∀ w, (deg (ι w)).toAdd = f * (deg' w).toAdd)

/-- The **restriction** of a raw Weil–Deligne parameter along a continuous homomorphism
`ι : W' →* W` with `deg (ι w) = f · deg' w`: the parameter `(V, r ∘ ι, N)` for `W'`, with `q ^ f`
in place of `q`. For the Weil group of a finite extension of local fields, `f` is the residue
degree. -/
def restrict (D : WeilDeligneParameter E W V deg q) : WeilDeligneParameter E W' V deg' (q ^ f) where
  r := D.r.comp ι
  isOpen_ker := by
    rw [← MonoidHom.comap_ker, Subgroup.coe_comap]
    exact D.isOpen_ker.preimage hι
  N := D.N
  isNilpotent_N := D.isNilpotent_N
  conj_N w := by
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, map_inv, D.conj_N, hf, Nat.cast_pow,
      zpow_mul, zpow_natCast]

variable {ι hι f hf}

@[simp]
theorem restrict_r_apply (D : WeilDeligneParameter E W V deg q) (w : W') :
    (D.restrict ι hι f hf).r w = D.r (ι w) :=
  (rfl)

@[simp]
theorem restrict_N (D : WeilDeligneParameter E W V deg q) : (D.restrict ι hι f hf).N = D.N :=
  (rfl)

variable {D₁ D₂ D₃ : WeilDeligneParameter E W V deg q}

/-- The restriction of a morphism of parameters. -/
def Hom.restrict {D : WeilDeligneParameter E W V deg q} {D' : WeilDeligneParameter E W V' deg q}
    (g : Hom D D') : Hom (D.restrict ι hι f hf) (D'.restrict ι hι f hf) where
  toLinearMap := g.toLinearMap
  isIntertwining' w := g.comp_r (ι w)
  comp_N := g.comp_N

@[simp]
theorem Hom.restrict_toLinearMap {D : WeilDeligneParameter E W V deg q}
    {D' : WeilDeligneParameter E W V' deg q} (g : Hom D D') :
    (g.restrict (ι := ι) (hι := hι) (f := f) (hf := hf)).toLinearMap = g.toLinearMap :=
  (rfl)

@[simp]
theorem Hom.restrict_apply {D : WeilDeligneParameter E W V deg q}
    {D' : WeilDeligneParameter E W V' deg q} (g : Hom D D') (v : V) :
    g.restrict (ι := ι) (hι := hι) (f := f) (hf := hf) v = g v :=
  (rfl)

@[simp]
theorem Hom.restrict_id :
    (Hom.id D₁).restrict (ι := ι) (hι := hι) (f := f) (hf := hf) = Hom.id _ := by
  ext1
  simp

theorem Hom.restrict_comp (g : Hom D₂ D₃) (g' : Hom D₁ D₂) :
    (g.comp g').restrict (ι := ι) (hι := hι) (f := f) (hf := hf) =
      g.restrict.comp g'.restrict := by
  ext1
  simp

/-- The restriction of an isomorphism of parameters. -/
def Iso.restrict {D : WeilDeligneParameter E W V deg q} {D' : WeilDeligneParameter E W V' deg q}
    (g : Iso D D') : Iso (D.restrict ι hι f hf) (D'.restrict ι hι f hf) where
  toLinearEquiv := g.toLinearEquiv
  isIntertwining' w := g.comp_r (ι w)
  comp_N := g.comp_N

@[simp]
theorem Iso.restrict_apply {D : WeilDeligneParameter E W V deg q}
    {D' : WeilDeligneParameter E W V' deg q} (g : Iso D D') (v : V) :
    g.restrict (ι := ι) (hι := hι) (f := f) (hf := hf) v = g v :=
  (rfl)

/-- Restriction commutes with direct sums. -/
theorem restrict_prod (D : WeilDeligneParameter E W V deg q)
    (D' : WeilDeligneParameter E W V' deg q) :
    (D.prod D').restrict ι hι f hf = (D.restrict ι hι f hf).prod (D'.restrict ι hι f hf) := by
  ext w x <;> simp

/-- Restriction commutes with duals. -/
theorem restrict_dual (D : WeilDeligneParameter E W V deg q) :
    D.dual.restrict ι hι f hf = (D.restrict ι hι f hf).dual := by
  ext w φ <;> simp [Representation.dual_apply]

/-- Restriction commutes with determinant characters. -/
theorem detChar_restrict (D : WeilDeligneParameter E W V deg q) :
    (D.restrict ι hι f hf).detChar = D.detChar.comp ι := by
  ext w
  simp

/-- Restriction of `Sp(n)` along `ι` is `Sp(n)` for `W'` and `q ^ f`. -/
theorem restrict_special (hdeg : Continuous deg) (hq : (q : E) ≠ 0) (hdeg' : Continuous deg')
    (hq' : ((q ^ f : ℕ) : E) ≠ 0) (n : ℕ) :
    (special q n hdeg hq).restrict ι hι f hf = special (q ^ f) n hdeg' hq' := by
  ext w v i
  · simp [hf, Nat.cast_pow, ← zpow_natCast, ← zpow_mul, mul_assoc]
  · simp

variable [SeparatelyContinuousMul W] [SeparatelyContinuousMul W']

/-- Restriction commutes with tensor products. -/
theorem restrict_tensor (D : WeilDeligneParameter E W V deg q)
    (D' : WeilDeligneParameter E W V' deg q) :
    (D.tensor D').restrict ι hι f hf = (D.restrict ι hι f hf).tensor (D'.restrict ι hι f hf) := by
  ext w x <;> simp

/-- Restriction commutes with determinants. -/
theorem restrict_det (D : WeilDeligneParameter E W V deg q) :
    D.det.restrict ι hι f hf = (D.restrict ι hι f hf).det := by
  ext w <;> simp

end Restriction

end WeilDeligneParameter

end TauCeti
