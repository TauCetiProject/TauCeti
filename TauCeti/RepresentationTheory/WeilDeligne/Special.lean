/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.WeilDeligne.Operations
public import TauCeti.LinearAlgebra.Eigenspace.Semisimple
public import TauCeti.LinearAlgebra.End.JordanChain.Shift

/-!
# The special Weil–Deligne parameters `Sp(n)`

Let `W` be a topological group with a continuous arithmetic degree `deg : W →* Multiplicative ℤ`,
and `q` a natural number which is nonzero in the field `E`. Write `ω(w) = q ^ deg w ∈ Eˣ`. The
**special parameter** `Sp(n)` is the raw Weil–Deligne parameter on `Eⁿ = Fin n → E` with
standard basis `e₀, …, e_(n-1)` given by

* `r(w) eᵢ = ω(w) ^ i • eᵢ`, and
* `N eᵢ = e_(i+1)` for `i + 1 < n`, `N e_(n-1) = 0`, so `N` is the shift `TauCeti.finShift E n`.

The conjugation relation `r(w) N r(w)⁻¹ = ω(w) • N` holds because `N` raises the weight by one
power of `ω`. The Weil action is diagonal, so `Sp(n)` is Frobenius semisimple, and for `n ≥ 2` its
monodromy is nonzero. The dual of `Sp(2)` is its twist by `ω⁻¹`.

## Main definitions

* `TauCeti.WeilDeligneParameter.omega`: the character `ω(w) = q ^ deg w` of `W`.
* `TauCeti.WeilDeligneParameter.specialWeight`: the eigenvalues `(ω(w) ^ i)ᵢ` of `r(w)`.
* `TauCeti.WeilDeligneParameter.special`: the parameter `Sp(n)`.

## Main results

* `TauCeti.WeilDeligneParameter.special_r_single`, `TauCeti.WeilDeligneParameter.special_N_single`,
  `TauCeti.WeilDeligneParameter.special_N_single_of_add_one_eq`: the action of `r(w)` and `N` on
  the standard basis.
* `TauCeti.WeilDeligneParameter.isFrobeniusSemisimple_special`: `Sp(n)` is Frobenius semisimple.
* `TauCeti.WeilDeligneParameter.special_N_ne_zero`: for `n ≥ 2` the monodromy of `Sp(n)` is
  nonzero.
* `TauCeti.WeilDeligneParameter.dualSpecialTwoIso`: `Sp(2)^∨ ≅ Sp(2) ⊗ ω⁻¹`.

## References

* P. Deligne, *Les constantes des équations fonctionnelles des fonctions L*, in *Modular functions
  of one variable II*, Lecture Notes in Math. 349 (1973), §8.4.1, p. 568, and the proof of §8.4.3,
  p. 569.
-/

public section

noncomputable section

namespace TauCeti

namespace WeilDeligneParameter

variable {E W : Type*} [Field E] [Group W] [TopologicalSpace W] {deg : W →* Multiplicative ℤ}
  {q : ℕ}

/-! ### The character `ω` -/

variable (deg) in
/-- The character `ω(w) = q ^ deg w` of `W`, for `q` nonzero in `E`. -/
def omega (hq : (q : E) ≠ 0) : W →* Eˣ :=
  (zpowersHom Eˣ (Units.mk0 (q : E) hq)).comp deg

omit [TopologicalSpace W] in
@[simp]
theorem coe_omega_apply (hq : (q : E) ≠ 0) (w : W) :
    (omega deg hq w : E) = (q : E) ^ (deg w).toAdd := by
  simp [omega, Units.val_zpow_eq_zpow_val]

omit [TopologicalSpace W] in
theorem coe_omega_inv_apply (hq : (q : E) ≠ 0) (w : W) :
    ((omega deg hq)⁻¹ w : E) = (q : E) ^ (-(deg w).toAdd) := by
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, coe_omega_apply, zpow_neg]

/-- For a continuous degree map, the character `ω` has open kernel. -/
theorem isOpen_ker_omega (hdeg : Continuous deg) (hq : (q : E) ≠ 0) :
    IsOpen ((omega deg hq).ker : Set W) :=
  isOpen_ker_comp_deg hdeg _

/-- For a continuous degree map, the character `ω⁻¹` has open kernel. -/
theorem isOpen_ker_omega_inv (hdeg : Continuous deg) (hq : (q : E) ≠ 0) :
    IsOpen ((omega deg hq)⁻¹.ker : Set W) := by
  rw [omega, ← MonoidHom.inv_comp]
  exact isOpen_ker_comp_deg hdeg _

/-! ### The weights -/

variable (deg) in
/-- The weights of `Sp(n)`: the vector `(ω(w) ^ i)ᵢ` of eigenvalues of `r(w)`, where
`ω(w) = q ^ deg w`. -/
def specialWeight (n : ℕ) (hq : (q : E) ≠ 0) : W →* (Fin n → E) :=
  (MonoidHom.pi fun i : Fin n ↦ (Units.coeHom E).comp (powMonoidHom (i : ℕ))).comp (omega deg hq)

omit [TopologicalSpace W] in
/-- The weights of `Sp(n)` are the powers of `ω`: `specialWeight w i = ω(w) ^ i`. -/
theorem specialWeight_apply_eq_omega_pow (n : ℕ) (hq : (q : E) ≠ 0) (w : W) (i : Fin n) :
    specialWeight deg n hq w i = (omega deg hq w : E) ^ (i : ℕ) := by
  simp [specialWeight]

omit [TopologicalSpace W] in
@[simp]
theorem specialWeight_apply (n : ℕ) (hq : (q : E) ≠ 0) (w : W) (i : Fin n) :
    specialWeight deg n hq w i = (q : E) ^ ((deg w).toAdd * i) := by
  rw [specialWeight_apply_eq_omega_pow, coe_omega_apply, zpow_mul, zpow_natCast]

omit [TopologicalSpace W] in
/-- Multiplication by the weights acts coordinatewise; this is the Weil action of `Sp(n)`. -/
private theorem lmul_comp_specialWeight_apply (n : ℕ) (hq : (q : E) ≠ 0) (w : W) (v : Fin n → E)
    (i : Fin n) :
    (Algebra.lmul E (Fin n → E)).toMonoidHom.comp (specialWeight deg n hq) w v i =
      specialWeight deg n hq w i * v i := by
  simp

/-! ### The special parameter -/

variable (q) in
/-- **The special parameter** `Sp(n)` on `Fin n → E`: `r(w) eᵢ = ω(w) ^ i • eᵢ` with
`ω(w) = q ^ deg w`, and `N eᵢ = e_(i+1)`, `N e_(n-1) = 0` (Deligne 1973, §8.4.1, p. 568). -/
def special (n : ℕ) (hdeg : Continuous deg) (hq : (q : E) ≠ 0) :
    WeilDeligneParameter E W (Fin n → E) deg q where
  r := (Algebra.lmul E (Fin n → E)).toMonoidHom.comp (specialWeight deg n hq)
  isOpen_ker := by
    simp only [specialWeight, omega, ← MonoidHom.comp_assoc]
    exact isOpen_ker_comp_deg hdeg _
  N := finShift E n
  isNilpotent_N := isNilpotent_finShift n
  conj_N w := by
    refine LinearMap.ext fun v ↦ funext fun j ↦ ?_
    simp only [mul_apply_eq_comp, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul,
      lmul_comp_specialWeight_apply, finShift_apply, specialWeight_apply, map_inv, toAdd_inv]
    split_ifs with h
    · simp
    · rw [← mul_assoc, ← zpow_add₀ hq]
      congr 2
      push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr h)]
      ring

variable (hdeg : Continuous deg) (hq : (q : E) ≠ 0)

/-- The Weil action of `Sp(n)` is multiplication by the weights. -/
theorem special_r (n : ℕ) (w : W) :
    (special q n hdeg hq).r w = Algebra.lmul E (Fin n → E) (specialWeight deg n hq w) :=
  (rfl)

@[simp]
theorem special_r_apply (n : ℕ) (w : W) (v : Fin n → E) (i : Fin n) :
    (special q n hdeg hq).r w v i = (q : E) ^ ((deg w).toAdd * i) * v i := by
  simp [special]

@[simp]
theorem special_N (n : ℕ) : (special q n hdeg hq).N = finShift E n :=
  (rfl)

/-- In `Sp(n)`, `r(w) eᵢ = ω(w) ^ i • eᵢ`. -/
theorem special_r_single (n : ℕ) (w : W) (i : Fin n) :
    (special q n hdeg hq).r w (Pi.single i 1) = (q : E) ^ ((deg w).toAdd * i) • Pi.single i 1 := by
  funext j
  rw [special_r_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : j = i
  · subst h; rfl
  · simp [Pi.single_eq_of_ne h]

/-- In `Sp(n)`, `N eᵢ = e_(i+1)` for `i + 1 < n`. -/
theorem special_N_single (n : ℕ) (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    (special q n hdeg hq).N (Pi.single i 1) = Pi.single ⟨i + 1, hi⟩ 1 :=
  finShift_single i hi

/-- In `Sp(n)`, `N e_(n-1) = 0`. -/
theorem special_N_single_of_add_one_eq (n : ℕ) (i : Fin n) (hi : (i : ℕ) + 1 = n) :
    (special q n hdeg hq).N (Pi.single i 1) = 0 :=
  finShift_single_of_add_one_eq i hi

/-- `Sp(n)` is Frobenius semisimple: every `r(w)` is diagonal. -/
theorem isFrobeniusSemisimple_special (n : ℕ) : (special q n hdeg hq).IsFrobeniusSemisimple :=
  (isFrobeniusSemisimple_def _).mpr fun w _ ↦ by
    rw [special_r]
    exact isSemisimple_lmul _

/-- For `n ≥ 2` the monodromy of `Sp(n)` is nonzero. -/
theorem special_N_ne_zero {n : ℕ} (hn : 2 ≤ n) : (special q n hdeg hq).N ≠ 0 := by
  intro h
  have := congr_fun (special_N_single hdeg hq n ⟨0, by omega⟩ (by simp; omega))
    ⟨1, by omega⟩
  rw [h] at this
  simp at this

/-! ### The dual of `Sp(2)` -/

/-- The linear isomorphism `Sp(2)^∨ → Sp(2) ⊗ ω⁻¹` on underlying spaces:
`f ↦ (-f e₁, f e₀)`. -/
private def dualSpecialTwoMap : Module.Dual E (Fin 2 → E) →ₗ[E] (Fin 2 → E) :=
  LinearMap.pi ![-Module.Dual.eval E _ (Pi.single 1 1), Module.Dual.eval E _ (Pi.single 0 1)]

private theorem dualSpecialTwoMap_apply (f : Module.Dual E (Fin 2 → E)) :
    dualSpecialTwoMap f = ![-f (Pi.single 1 1), f (Pi.single 0 1)] := by
  funext i
  fin_cases i <;> simp [dualSpecialTwoMap]

/-- `dualSpecialTwoMap` intertwines the dual monodromy `-Nᵗ` with the shift. -/
private theorem dualSpecialTwoMap_neg_dualMap_finShift (f : Module.Dual E (Fin 2 → E)) :
    dualSpecialTwoMap (-(finShift E 2).dualMap f) = finShift E 2 (dualSpecialTwoMap f) := by
  funext i
  fin_cases i
  · simp [dualSpecialTwoMap_apply, finShift_single_of_add_one_eq (1 : Fin 2) rfl]
  · simp [dualSpecialTwoMap_apply, finShift_single (0 : Fin 2) (by simp)]

private theorem surjective_dualSpecialTwoMap :
    Function.Surjective (dualSpecialTwoMap (E := E)) := fun v ↦
  ⟨v 1 • LinearMap.proj 0 - v 0 • LinearMap.proj 1, funext fun i ↦ by
    fin_cases i <;> simp [dualSpecialTwoMap_apply]⟩

private theorem bijective_dualSpecialTwoMap : Function.Bijective (dualSpecialTwoMap (E := E)) :=
  ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (Subspace.dual_finrank_eq)).mpr surjective_dualSpecialTwoMap, surjective_dualSpecialTwoMap⟩

variable [SeparatelyContinuousMul W]

/-- `dualSpecialTwoMap` intertwines `r^∨ = r(w⁻¹)ᵗ` with the twist of `r` by `ω⁻¹`. -/
private theorem dualSpecialTwoMap_dual_r_apply (w : W) (f : Module.Dual E (Fin 2 → E)) :
    dualSpecialTwoMap ((special q 2 hdeg hq).dual.r w f) =
      ((special q 2 hdeg hq).twist _ (isOpen_ker_omega_inv hdeg hq)).r w
        (dualSpecialTwoMap f) := by
  rw [dual_r, twist_r, Representation.charTwist_apply_apply]
  funext i
  fin_cases i <;>
    simp [dualSpecialTwoMap_apply, Module.Dual.transpose_apply, special_r_single, ← mul_assoc,
      inv_mul_cancel₀ (zpow_ne_zero _ hq)]

/-- **The dual of `Sp(2)`** is its twist by `ω⁻¹`: `Sp(2)^∨ ≅ Sp(2) ⊗ ω⁻¹`, through
`e₀^* ↦ e₁` and `e₁^* ↦ -e₀` (Deligne 1973, proof of §8.4.3, p. 569). -/
def dualSpecialTwoIso :
    Iso (special q 2 hdeg hq).dual ((special q 2 hdeg hq).twist _ (isOpen_ker_omega_inv hdeg hq)) :=
  Iso.ofBijective
    { toLinearMap := dualSpecialTwoMap
      isIntertwining' w := LinearMap.ext fun f ↦ by
        rw [LinearMap.comp_apply, LinearMap.comp_apply]
        exact dualSpecialTwoMap_dual_r_apply hdeg hq w f
      comp_N := LinearMap.ext fun f ↦ by
        simpa using dualSpecialTwoMap_neg_dualMap_finShift f }
    bijective_dualSpecialTwoMap

/-- The isomorphism `Sp(2)^∨ ≅ Sp(2) ⊗ ω⁻¹` sends `f` to `(-f e₁, f e₀)`. -/
@[simp]
theorem dualSpecialTwoIso_apply (f : Module.Dual E (Fin 2 → E)) :
    dualSpecialTwoIso hdeg hq f = ![-f (Pi.single 1 1), f (Pi.single 0 1)] := by
  rw [dualSpecialTwoIso, Iso.coe_ofBijective]
  exact dualSpecialTwoMap_apply f

/-- The isomorphism `Sp(2)^∨ ≅ Sp(2) ⊗ ω⁻¹` sends `e₀^*` to `e₁`. -/
theorem dualSpecialTwoIso_proj_zero :
    dualSpecialTwoIso hdeg hq (LinearMap.proj 0) = (Pi.single 1 1 : Fin 2 → E) := by
  funext i
  fin_cases i <;> simp

/-- The isomorphism `Sp(2)^∨ ≅ Sp(2) ⊗ ω⁻¹` sends `e₁^*` to `-e₀`. -/
theorem dualSpecialTwoIso_proj_one :
    dualSpecialTwoIso hdeg hq (LinearMap.proj 1) = -(Pi.single 0 1 : Fin 2 → E) := by
  funext i
  fin_cases i <;> simp

end WeilDeligneParameter

end TauCeti
