/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.WeilDeligne.Operations
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Instances.Int
import Mathlib.FieldTheory.Separable

/-!
# The special Weil–Deligne parameters `Sp(n)`

Let `W` be a topological group with a continuous arithmetic degree `deg : W →* Multiplicative ℤ`,
and `q` a natural number which is nonzero in the field `E`. Write `ω(w) = q ^ deg w ∈ Eˣ`. The
**special parameter** `Sp(n)` is the raw Weil–Deligne parameter on `Eⁿ = Fin n → E` with
standard basis `e₀, …, e_(n-1)` given by

* `r(w) eᵢ = ω(w) ^ i • eᵢ`, and
* `N eᵢ = e_(i+1)` for `i + 1 < n`, `N e_(n-1) = 0`.

The conjugation relation `r(w) N r(w)⁻¹ = ω(w) • N` holds because `N` raises the weight by one
power of `ω`. The Weil action is diagonal, so `Sp(n)` is Frobenius semisimple, and for `n ≥ 2` its
monodromy is nonzero. The dual of `Sp(2)` is its twist by `ω⁻¹`.

## Main definitions

* `TauCeti.WeilDeligneParameter.specialWeight`: the eigenvalues `(ω(w) ^ i)ᵢ` of `r(w)`.
* `TauCeti.WeilDeligneParameter.omega`: the character `ω(w) = q ^ deg w` of `W`.
* `TauCeti.WeilDeligneParameter.shift`: the shift `eᵢ ↦ e_(i+1)` on `Fin n → E`.
* `TauCeti.WeilDeligneParameter.special`: the parameter `Sp(n)`.

## Main results

* `TauCeti.WeilDeligneParameter.special_r_single`, `TauCeti.WeilDeligneParameter.special_N_single`:
  the action of `r(w)` and `N` on the standard basis.
* `TauCeti.WeilDeligneParameter.isSemisimple_lmul`: multiplication by a fixed vector on
  `Fin n → E`, a diagonal operator, is semisimple.
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

open Polynomial

variable {E W : Type*} [Field E] [Group W] [TopologicalSpace W] {deg : W →* Multiplicative ℤ}
  {q : ℕ}

/-! ### The character `ω` -/

variable (E) in
/-- The weights `(u ^ (k * i))ᵢ` of `Sp(n)` at an element of degree `k`, as a homomorphism
`Multiplicative ℤ →* (Fin n → E)`, for a unit `u` (which is `q`). -/
def specialWeightOfDeg (n : ℕ) (u : Eˣ) : Multiplicative ℤ →* (Fin n → E) :=
  MonoidHom.pi fun i ↦ (Units.coeHom E).comp ((powMonoidHom (i : ℕ)).comp (zpowersHom Eˣ u))

variable (deg) in
/-- The weights of `Sp(n)`: the vector `(ω(w) ^ i)ᵢ` of eigenvalues of `r(w)`, where
`ω(w) = q ^ deg w`. -/
def specialWeight (n : ℕ) (hq : (q : E) ≠ 0) : W →* (Fin n → E) :=
  (specialWeightOfDeg E n (Units.mk0 (q : E) hq)).comp deg

omit [TopologicalSpace W] in
@[simp]
theorem specialWeight_apply (n : ℕ) (hq : (q : E) ≠ 0) (w : W) (i : Fin n) :
    specialWeight deg n hq w i = (q : E) ^ ((deg w).toAdd * i) := by
  simp [specialWeight, specialWeightOfDeg, zpow_mul, zpow_natCast, Units.val_zpow_eq_zpow_val]

/-! ### Diagonal operators -/

/-- Multiplication by a fixed vector `c : Fin n → E`, the diagonal operator with entries `c i`, is
semisimple: it is killed by the squarefree polynomial `∏ (X - c i)` over the distinct values. -/
theorem isSemisimple_lmul {n : ℕ} (c : Fin n → E) :
    (Algebra.lmul E (Fin n → E) c).IsSemisimple := by
  classical
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := ∏ x ∈ Finset.univ.image c, (X - C x)) ?_ ?_
  · exact (separable_prod_X_sub_C_iff' (f := id).mpr fun _ _ _ _ h ↦ h).squarefree
  · rw [aeval_algHom_apply, map_prod]
    convert map_zero (Algebra.lmul E (Fin n → E))
    funext j
    rw [Finset.prod_apply, Pi.zero_apply]
    exact Finset.prod_eq_zero (Finset.mem_image_of_mem c (Finset.mem_univ j)) (by simp)

/-! ### The shift -/

variable (E) in
/-- The shift `eᵢ ↦ e_(i+1)` on `Fin n → E`, with `e_(n-1) ↦ 0`: `(shift v) j = v (j - 1)` for
`j ≥ 1`, and `(shift v) 0 = 0`. -/
def shift (n : ℕ) : Module.End E (Fin n → E) :=
  LinearMap.pi fun j ↦ if _ : (j : ℕ) = 0 then 0 else LinearMap.proj ⟨j - 1, by omega⟩

theorem shift_apply {n : ℕ} (v : Fin n → E) (j : Fin n) :
    shift E n v j = if _ : (j : ℕ) = 0 then 0 else v ⟨j - 1, by omega⟩ := by
  by_cases h : (j : ℕ) = 0 <;> simp [shift, h]

/-- The shift sends `eᵢ` to `e_(i+1)`. -/
theorem shift_single {n : ℕ} (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    shift E n (Pi.single i 1) = Pi.single ⟨i + 1, hi⟩ 1 := by
  funext j
  simp only [shift_apply, Pi.single_apply, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

/-- The shift kills the last basis vector `e_(n-1)`. -/
theorem shift_single_of_add_one_eq {n : ℕ} (i : Fin n) (hi : (i : ℕ) + 1 = n) :
    shift E n (Pi.single i 1) = 0 := by
  funext j
  have := j.isLt
  simp only [shift_apply, Pi.single_apply, Fin.ext_iff, Pi.zero_apply]
  split_ifs <;> first | rfl | omega

/-- The `k`-th power of the shift kills the first `k` coordinates. -/
theorem shift_pow_apply_eq_zero {n : ℕ} (k : ℕ) (v : Fin n → E) (j : Fin n) (hj : (j : ℕ) < k) :
    (shift E n ^ k) v j = 0 := by
  induction k generalizing j with
  | zero => omega
  | succ k ih =>
    rw [pow_succ']
    change shift E n ((shift E n ^ k) v) j = 0
    rw [shift_apply]
    split_ifs with h
    · rfl
    · exact ih _ (by simp; omega)

/-- The shift on `Fin n → E` is nilpotent: its `n`-th power vanishes. -/
theorem shift_pow_eq_zero (n : ℕ) : shift E n ^ n = 0 :=
  LinearMap.ext fun v ↦ funext fun j ↦ shift_pow_apply_eq_zero n v j j.isLt

theorem isNilpotent_shift (n : ℕ) : IsNilpotent (shift E n) :=
  ⟨n, shift_pow_eq_zero n⟩

/-! ### The special parameter -/

variable (q) in
/-- **The special parameter** `Sp(n)` on `Fin n → E`: `r(w) eᵢ = ω(w) ^ i • eᵢ` with
`ω(w) = q ^ deg w`, and `N eᵢ = e_(i+1)`, `N e_(n-1) = 0` (Deligne 1973, §8.4.1, p. 568). -/
def special (n : ℕ) (hdeg : Continuous deg) (hq : (q : E) ≠ 0) :
    WeilDeligneParameter E W (Fin n → E) deg q where
  r := (Algebra.lmul E (Fin n → E)).toMonoidHom.comp (specialWeight deg n hq)
  isOpen_ker := by
    rw [specialWeight, ← MonoidHom.comp_assoc, ← MonoidHom.comap_ker, Subgroup.coe_comap]
    exact hdeg.isOpen_preimage _ (isOpen_discrete _)
  N := shift E n
  isNilpotent_N := isNilpotent_shift n
  conj_N w := by
    refine LinearMap.ext fun v ↦ funext fun j ↦ ?_
    change specialWeight deg n hq w j * shift E n (specialWeight deg n hq w⁻¹ * v) j =
      (q : E) ^ (deg w).toAdd * shift E n v j
    rw [shift_apply, shift_apply]
    split_ifs with h
    · simp
    · rw [Pi.mul_apply, specialWeight_apply, specialWeight_apply, ← mul_assoc,
        ← zpow_add₀ (by exact_mod_cast hq), map_inv, toAdd_inv]
      congr 2
      push_cast [Nat.cast_sub (show 1 ≤ (j : ℕ) by omega)]
      ring

variable (hdeg : Continuous deg) (hq : (q : E) ≠ 0)

theorem special_r_apply (n : ℕ) (w : W) (v : Fin n → E) (i : Fin n) :
    (special q n hdeg hq).r w v i = (q : E) ^ ((deg w).toAdd * i) * v i := by
  simp [special]

@[simp]
theorem special_N (n : ℕ) : (special q n hdeg hq).N = shift E n :=
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
  shift_single i hi

/-- `Sp(n)` is Frobenius semisimple: every `r(w)` is diagonal. -/
theorem isFrobeniusSemisimple_special (n : ℕ) : (special q n hdeg hq).IsFrobeniusSemisimple :=
  (isFrobeniusSemisimple_def _).mpr fun w _ ↦ isSemisimple_lmul (specialWeight deg n hq w)

/-- For `n ≥ 2` the monodromy of `Sp(n)` is nonzero. -/
theorem special_N_ne_zero {n : ℕ} (hn : 2 ≤ n) : (special q n hdeg hq).N ≠ 0 := by
  intro h
  have := congr_fun (special_N_single hdeg hq n ⟨0, by omega⟩ (by simp; omega))
    ⟨1, by omega⟩
  rw [h] at this
  simp at this

/-! ### The character `ω` and the dual of `Sp(2)` -/

variable (deg) in
/-- The character `ω(w) = q ^ deg w` of `W`, for `q` nonzero in `E`. -/
def omega (hq : (q : E) ≠ 0) : W →* Eˣ :=
  (zpowersHom Eˣ (Units.mk0 (q : E) hq)).comp deg

omit [TopologicalSpace W] in
@[simp]
theorem coe_omega_apply (w : W) : (omega deg hq w : E) = (q : E) ^ (deg w).toAdd := by
  simp [omega, Units.val_zpow_eq_zpow_val]

omit [TopologicalSpace W] in
theorem coe_omega_inv_apply (w : W) : ((omega deg hq)⁻¹ w : E) = (q : E) ^ (-(deg w).toAdd) := by
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, coe_omega_apply, zpow_neg]

include hdeg in
/-- For a continuous degree map, the character `ω⁻¹` has open kernel. -/
theorem isOpen_ker_omega_inv : IsOpen ((omega deg hq)⁻¹.ker : Set W) := by
  have : (omega deg hq)⁻¹ = (zpowersHom Eˣ (Units.mk0 (q : E) hq))⁻¹.comp deg := rfl
  rw [this, ← MonoidHom.comap_ker, Subgroup.coe_comap]
  exact hdeg.isOpen_preimage _ (isOpen_discrete _)

/-- The linear isomorphism `Sp(2)^∨ → Sp(2) ⊗ ω⁻¹` on underlying spaces:
`f ↦ (-f e₁, f e₀)`. -/
private def dualSpecialTwoMap : Module.Dual E (Fin 2 → E) →ₗ[E] (Fin 2 → E) :=
  LinearMap.pi ![-Module.Dual.eval E _ (Pi.single 1 1), Module.Dual.eval E _ (Pi.single 0 1)]

private theorem dualSpecialTwoMap_apply_zero (f : Module.Dual E (Fin 2 → E)) :
    dualSpecialTwoMap f 0 = -f (Pi.single 1 1) :=
  (rfl)

private theorem dualSpecialTwoMap_apply_one (f : Module.Dual E (Fin 2 → E)) :
    dualSpecialTwoMap f 1 = f (Pi.single 0 1) :=
  (rfl)

variable [SeparatelyContinuousMul W]

/-- **The dual of `Sp(2)`** is its twist by `ω⁻¹`: `Sp(2)^∨ ≅ Sp(2) ⊗ ω⁻¹`, through
`e₀^* ↦ e₁` and `e₁^* ↦ -e₀` (Deligne 1973, proof of §8.4.3, p. 569). -/
def dualSpecialTwoIso :
    Iso (special q 2 hdeg hq).dual ((special q 2 hdeg hq).twist _ (isOpen_ker_omega_inv hdeg hq)) :=
  Iso.ofBijective
    { toLinearMap := dualSpecialTwoMap
      isIntertwining' w := by
        refine LinearMap.ext fun f ↦ funext fun i ↦ ?_
        rw [LinearMap.comp_apply, LinearMap.comp_apply, dual_r, twist_r,
          Representation.charTwist_apply_apply, Pi.smul_apply, smul_eq_mul]
        rw [special_r_apply, coe_omega_inv_apply]
        fin_cases i
        · simp only [Fin.zero_eta, Fin.isValue, dualSpecialTwoMap_apply_zero,
            Representation.dual_apply_apply, special_r_single, map_smul, smul_eq_mul]
          simp [map_inv]
        · simp only [Fin.mk_one, Fin.isValue, dualSpecialTwoMap_apply_one,
            Representation.dual_apply_apply, special_r_single, map_smul, smul_eq_mul]
          rw [← mul_assoc, ← zpow_add₀ (by exact_mod_cast hq)]
          simp
      comp_N := by
        refine LinearMap.ext fun f ↦ funext fun i ↦ ?_
        rw [LinearMap.comp_apply, LinearMap.comp_apply, dual_N, twist_N, special_N]
        fin_cases i
        · simp only [Fin.zero_eta, Fin.isValue, dualSpecialTwoMap_apply_zero, LinearMap.neg_apply,
            LinearMap.dualMap_apply, shift_apply]
          simp [shift_single_of_add_one_eq (1 : Fin 2) rfl]
        · simp only [Fin.mk_one, Fin.isValue, dualSpecialTwoMap_apply_one, LinearMap.neg_apply,
            LinearMap.dualMap_apply, shift_apply, shift_single (0 : Fin 2) (by simp)]
          simp [dualSpecialTwoMap_apply_zero] }
    ⟨fun f g h ↦ by
      refine LinearMap.pi_ext fun i x ↦ ?_
      have h' : dualSpecialTwoMap f = dualSpecialTwoMap g := h
      have h0 := congr_fun h' 0
      have h1 := congr_fun h' 1
      simp only [dualSpecialTwoMap_apply_zero, dualSpecialTwoMap_apply_one, neg_inj] at h0 h1
      rw [← mul_one x, ← smul_eq_mul, Pi.single_smul, map_smul, map_smul]
      fin_cases i
      · exact congrArg _ h1
      · exact congrArg _ h0,
    fun v ↦ ⟨v 1 • LinearMap.proj 0 - v 0 • LinearMap.proj 1, funext fun i ↦ by
      fin_cases i <;> simp [dualSpecialTwoMap_apply_zero, dualSpecialTwoMap_apply_one]⟩⟩

end WeilDeligneParameter

end TauCeti
