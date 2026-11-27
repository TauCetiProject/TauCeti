/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.SymmetricPower.FinTwo
public import TauCeti.RepresentationTheory.WeilDeligne.Special
public import TauCeti.RepresentationTheory.WeilDeligne.SymmetricPower.Basic

/-!
# Symmetric powers of `Sp(2)`

Let `E` be a field of characteristic zero. The `m`-th symmetric power of the special parameter
`Sp(2)` (`TauCeti.WeilDeligneParameter.special`) is isomorphic to `Sp(m + 1)`
(`TauCeti.WeilDeligneParameter.symSpecialTwoIso`), with no twist.

Write `e₀, e₁` for the standard basis of `E²`. In `Sp(2)` the Weil group acts by `r(w) e₀ = e₀`,
`r(w) e₁ = ω(w) e₁` and the monodromy is the shift `N e₀ = e₁`, `N e₁ = 0`. In `Sym^m ∘ Sp(2)` the
monomials `e₀ ^ (m - j) e₁ ^ j` (`TauCeti.symFinTwoMonomial`) have weights `ω(w) ^ j`
(`TauCeti.WeilDeligneParameter.sym_special_r_symFinTwoMonomial`), and the monodromy sends the
`j`-th to `(m - j)` times the `(j + 1)`-st
(`TauCeti.WeilDeligneParameter.sym_special_N_symFinTwoMonomial`, from the Leibniz rule
`TauCeti.differential_finShift_symFinTwoMonomial`). In characteristic zero the
coefficients `m - j` are nonzero, so the monodromy is a single Jordan block of size `m + 1`:
rescaling the `j`-th monomial by the falling factorial `m (m - 1) ⋯ (m - j + 1)`
(`TauCeti.WeilDeligneParameter.symSpecialBasis`) turns it into the shift `eⱼ ↦ e_(j+1)` of
`Sp(m + 1)`, through the invertibility of `1, …, m` in `E`.

## Main definitions

* `TauCeti.WeilDeligneParameter.symSpecialBasis`: the rescaled monomial basis of `Sym^m (E²)`.
* `TauCeti.WeilDeligneParameter.symSpecialTwoIso`: the isomorphism `Sym^m ∘ Sp(2) ≅ Sp(m + 1)`.

## References

* P. Deligne, *Les constantes des équations fonctionnelles des fonctions L*, in *Modular functions
  of one variable II*, Lecture Notes in Math. 349 (1973), §8.4.1, p. 568.
* J. Tate, *Number theoretic background*, in *Automorphic forms, representations and
  L-functions*, Proc. Sympos. Pure Math. 33, Part 2 (1979), §4.1.
-/

public section

noncomputable section

namespace TauCeti

open _root_.Module SymmetricPower TensorProduct

namespace WeilDeligneParameter

variable {E : Type} [Field E] {W : Type*} [Group W] [TopologicalSpace W]
  [SeparatelyContinuousMul W] {deg : W →* Multiplicative ℤ} {q : ℕ}

variable (hdeg : Continuous deg) (hq : (q : E) ≠ 0)

/-- **The weights of the monomials**: in `Sym^m ∘ Sp(2)`, `r(w)` acts on `e₀ ^ (m - j) e₁ ^ j` by
`ω(w) ^ j`. -/
theorem sym_special_r_symFinTwoMonomial (m : ℕ) {j : ℕ} (hj : j ≤ m) (w : W) :
    ((special q 2 hdeg hq).sym m).r w (symFinTwoMonomial E m j) =
      (q : E) ^ ((deg w).toAdd * j) • symFinTwoMonomial E m j := by
  rw [sym_r, Representation.symmetricPower_apply, symFinTwoMonomial_eq_symmetricPower,
    Basis.map_symmetricPower_of_apply _ _ (fun k : Fin 2 ↦ (q : E) ^ ((deg w).toAdd * k))
      fun k ↦ by simpa using special_r_single hdeg hq 2 w k]
  congr 1
  simp [zpow_mul, Nat.sub_sub_self hj]

/-- **The monodromy on the monomials**: in `Sym^m ∘ Sp(2)`, `N` sends `e₀ ^ (m - j) e₁ ^ j` to
`(m - j) e₀ ^ (m - j - 1) e₁ ^ (j + 1)`; in characteristic zero, a single Jordan block of size
`m + 1`. -/
theorem sym_special_N_symFinTwoMonomial {m j : ℕ} (hj : j < m) :
    ((special q 2 hdeg hq).sym m).N (symFinTwoMonomial E m j) =
      ((m - j : ℕ) : E) • symFinTwoMonomial E m (j + 1) := by
  rw [sym_N, special_N, differential_finShift_symFinTwoMonomial hj]

/-! ### The isomorphism `Sym^m ∘ Sp(2) ≅ Sp(m + 1)` -/

variable (E) in
/-- The basis of `Sym^m (E²)` whose `j`-th vector is the monomial `e₀ ^ (m - j) e₁ ^ j` scaled by
the falling factorial `m (m - 1) ⋯ (m - j + 1)`, which is invertible in characteristic zero. -/
def symSpecialBasis [CharZero E] (m : ℕ) : Basis (Fin (m + 1)) E (Sym[E]^m (Fin 2 → E)) :=
  (((Pi.basisFun E (Fin 2)).symmetricPower m).reindex
    ((symFinTwoEquiv m).trans Fin.revPerm)).unitsSMul fun j ↦
      Units.mk0 (m.descFactorial j : E) (Nat.cast_ne_zero.2
        (Nat.descFactorial_pos.2 (Nat.lt_succ_iff.1 j.isLt)).ne')

theorem symSpecialBasis_apply [CharZero E] (m : ℕ) (j : Fin (m + 1)) :
    symSpecialBasis E m j = (m.descFactorial j : E) • symFinTwoMonomial E m j := by
  have hrev : j.rev = ⟨m - j, by omega⟩ := Fin.ext (by simp only [Fin.val_rev]; omega)
  simp [symSpecialBasis, Basis.unitsSMul_apply, hrev,
    symFinTwoMonomial_eq_symmetricPower]

private theorem equivFun_symSpecialBasis [CharZero E] (m : ℕ) (j : Fin (m + 1)) :
    (symSpecialBasis E m).equivFun (symSpecialBasis E m j) = Pi.single j 1 := by
  rw [← Basis.equivFun_symm_single (symSpecialBasis E m) j, LinearEquiv.apply_symm_apply]

private theorem symSpecialBasis_succ [CharZero E] {m j : ℕ} (hj : j < m) :
    symSpecialBasis E m ⟨j + 1, by omega⟩ =
      (m.descFactorial j : E) • ((m - j : ℕ) : E) • symFinTwoMonomial E m (j + 1) := by
  rw [symSpecialBasis_apply, smul_smul, ← Nat.cast_mul, mul_comm, ← Nat.descFactorial_succ]

/-- **The symmetric powers of `Sp(2)` are the special parameters**: in characteristic zero,
`Sym^m ∘ Sp(2) ≅ Sp(m + 1)`, sending the rescaled monomial
`m (m - 1) ⋯ (m - j + 1) e₀ ^ (m - j) e₁ ^ j` to the `j`-th standard basis vector
(Deligne 1973, §8.4.1, p. 568). -/
def symSpecialTwoIso [CharZero E] (m : ℕ) :
    Iso ((special q 2 hdeg hq).sym m) (special q (m + 1) hdeg hq) where
  toRepresentationEquiv := .mk (symSpecialBasis E m).equivFun fun w ↦
    (symSpecialBasis E m).ext fun j ↦ by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [symSpecialBasis_apply, map_smul,
        sym_special_r_symFinTwoMonomial hdeg hq m (Nat.lt_succ_iff.1 j.isLt), smul_comm,
        ← symSpecialBasis_apply, map_smul, equivFun_symSpecialBasis, special_r_single]
  comp_N := (symSpecialBasis E m).ext fun j ↦ by
    simp only [LinearMap.comp_apply, Representation.Equiv.toIntertwiningMap_mk',
      LinearEquiv.coe_coe, Representation.IntertwiningMap.toLinearMap_mk, equivFun_symSpecialBasis,
      special_N]
    rcases Nat.lt_succ_iff_lt_or_eq.1 j.isLt with hj | hj
    · rw [finShift_single j (by omega), symSpecialBasis_apply, map_smul,
        sym_special_N_symFinTwoMonomial hdeg hq hj, ← symSpecialBasis_succ hj,
        equivFun_symSpecialBasis]
    · rw [finShift_single_of_add_one_eq j (by omega), symSpecialBasis_apply, map_smul, sym_N,
        special_N, hj, differential_finShift_symFinTwoMonomial_self, smul_zero, map_zero]

/-- `Sym^m ∘ Sp(2) ≅ Sp(m + 1)` sends the rescaled monomial basis to the standard basis. -/
@[simp]
theorem symSpecialTwoIso_symSpecialBasis [CharZero E] (m : ℕ) (j : Fin (m + 1)) :
    symSpecialTwoIso hdeg hq m (symSpecialBasis E m j) = Pi.single j 1 := by
  rw [symSpecialTwoIso, Iso.coe_mk, Representation.Equiv.mk_apply, equivFun_symSpecialBasis]

/-- The inverse of `Sym^m ∘ Sp(2) ≅ Sp(m + 1)` sends the standard basis to the rescaled monomial
basis. -/
@[simp]
theorem symSpecialTwoIso_symm_single [CharZero E] (m : ℕ) (j : Fin (m + 1)) :
    (symSpecialTwoIso hdeg hq m).symm (Pi.single j 1) = symSpecialBasis E m j := by
  rw [← symSpecialTwoIso_symSpecialBasis hdeg hq, Iso.symm_apply_apply]

end WeilDeligneParameter

end TauCeti
