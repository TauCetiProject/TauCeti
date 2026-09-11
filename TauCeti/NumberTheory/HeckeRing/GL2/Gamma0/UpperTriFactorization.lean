/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Data.ZMod.FinEquiv
public import TauCeti.NumberTheory.HeckeRing.GL2.CosetDecomposition
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-!
# The upper-triangular coset factorisation at `Γ₀`

Write `γ = !![a, b; c, d] ∈ SL(2, ℤ)`. Matching entries in
`!![1, j; 0, p] · γ = γ' · !![1, j'; 0, p]` forces `γ' = !![a + jc, b'; pc, d - cj']` and
`p b' = b + jd - (a + jc) j'`, so the offset `j'` must solve

`(a + jc) j' ≡ b + jd (mod p)`.

That has a unique solution in `[0, p)` exactly when `a + jc` is invertible modulo `p`, and
`upperTriShift p γ j` is it. On `Γ₀(p)` invertibility is automatic and uniform in `j`: `p ∣ c`
collapses `a + jc` to `a`, and `ad - bc = 1` reduces to `ad ≡ 1 (mod p)`, exhibiting `d` as the
inverse of `a`, so the solution takes the closed form `j' = d b + j d² mod p` and the map is a
bijection of `Fin p`.

Everything here is a statement about matrices and congruence subgroups. Nothing in this file
mentions the slash action; the equivariance of the upper-triangular sum, which consumes these
results, lives in `ModularForms/HeckeSlash/UpperTri/Invariance.lean`.

## Main definitions

* `HeckeRing.GL2.upperTriShift`: the offset map, `j ↦ (a + jc)⁻¹ (b + jd) mod p`.

## Main results

* `HeckeRing.GL2.mul_upperTriShift_natCast`: it solves `(a + jc) j' ≡ b + jd (mod p)` whenever
  `a + jc` is invertible.
* `HeckeRing.GL2.upperTriShift_eq_iff`: and it is the only solution in `[0, p)`.
* `HeckeRing.GL2.upperTriShift_natCast_of_mem_Gamma0`: on `Γ₀(p)` it is `j ↦ d b + j d² mod p`.
* `HeckeRing.GL2.upperTriShift_bijective`: on `Γ₀(p)` it is a bijection of `Fin p`.
* `HeckeRing.GL2.exists_mem_Gamma0_upperTriRep_mul_of_isUnit`: the factorisation
  `!![1, j; 0, p] · γ = γ' · !![1, j'; 0, p]` with `γ' ∈ Γ₀(N)`, from `a + jc` invertible modulo
  `p` and `N ∣ p c`.
* `HeckeRing.GL2.exists_mem_Gamma0_upperTriRep_mul`: the same at `γ ∈ Γ₀(p)`, where the first
  hypothesis holds for every offset at once.
* `HeckeRing.GL2.exists_mem_Gamma0_upperTriRep_mul_of_mem_Gamma0`: its specialisation to `p ∣ N`
  and `γ ∈ Γ₀(N)`, whose conclusion is the modulo-`N` congruence of the lower-right entry.
-/

public section

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup

open scoped MatrixGroups

namespace HeckeRing.GL2

variable {N p : ℕ}

/-- **The offset map**, `j ↦ (a + j c)⁻¹ (b + j d) mod p`, where `γ = !![a, b; c, d]`.

`a + j c` and `b + j d` are the top-left and top-right entries of `!![1, j; 0, p] · γ`
before dividing by `p`, so this is the unique solution in `[0, p)` of
`(a + j c) j' ≡ b + j d (mod p)` — whenever `a + j c` is invertible modulo `p`. Outside that case
the value is `ZMod`'s junk inverse and solves nothing, so every lemma that reads the value *as a
solution of that congruence* carries the invertibility hypothesis. Lemmas that merely evaluate the
map, such as `upperTriShift_natCast`, hold for every `γ` and `j`. -/
def upperTriShift (p : ℕ) [NeZero p] (γ : SL(2, ℤ)) (j : Fin p) : Fin p :=
  (ZMod.finEquiv p).symm (((γ 0 0 + (j : ℕ) * γ 1 0 : ℤ) : ZMod p)⁻¹
    * ((γ 0 1 + (j : ℕ) * γ 1 1 : ℤ) : ZMod p))

/-- The value of `upperTriShift` in `ZMod p`. Deliberately not a `simp` lemma: the junk inverse on
the right is not a normal form, and the two facts callers want are `mul_upperTriShift_natCast` and
`upperTriShift_natCast_of_mem_Gamma0`. -/
lemma upperTriShift_natCast (p : ℕ) [NeZero p] (γ : SL(2, ℤ)) (j : Fin p) :
    ((upperTriShift p γ j : ℕ) : ZMod p)
      = ((γ 0 0 + (j : ℕ) * γ 1 0 : ℤ) : ZMod p)⁻¹ * ((γ 0 1 + (j : ℕ) * γ 1 1 : ℤ) : ZMod p) := by
  simp only [upperTriShift, ZMod.finEquiv_symm_apply_val]
  exact ZMod.natCast_rightInverse _

/-- **The defining congruence.** For `a + j c` invertible modulo `p`, `upperTriShift p γ j` solves
`(a + j c) j' ≡ b + j d (mod p)`. That it is the *only* solution in `[0, p)` is
`upperTriShift_eq_iff`. -/
@[simp] lemma mul_upperTriShift_natCast [NeZero p] {γ : SL(2, ℤ)} {j : Fin p}
    (hA : IsUnit (((γ 0 0 : ℤ) : ZMod p) + ((j : ℕ) : ZMod p) * ((γ 1 0 : ℤ) : ZMod p))) :
    (((γ 0 0 : ℤ) : ZMod p) + ((j : ℕ) : ZMod p) * ((γ 1 0 : ℤ) : ZMod p))
        * ((upperTriShift p γ j : ℕ) : ZMod p)
      = ((γ 0 1 : ℤ) : ZMod p) + ((j : ℕ) : ZMod p) * ((γ 1 1 : ℤ) : ZMod p) := by
  have hA' : IsUnit (((γ 0 0 + (j : ℕ) * γ 1 0 : ℤ) : ZMod p)) := by push_cast; exact hA
  have h : ((γ 0 0 + (j : ℕ) * γ 1 0 : ℤ) : ZMod p) * ((upperTriShift p γ j : ℕ) : ZMod p)
      = ((γ 0 1 + (j : ℕ) * γ 1 1 : ℤ) : ZMod p) := by
    rw [upperTriShift_natCast, ← mul_assoc, ZMod.mul_inv_of_unit _ hA', one_mul]
  push_cast at h
  exact h

/-- **The offset map is the *only* solution.** Under invertibility of `a + j c`, an offset `j'`
in `[0, p)` solves `(a + j c) j' ≡ b + j d (mod p)` exactly when it is `upperTriShift p γ j`.
This is the elimination half of the characteristic API: `mul_upperTriShift_natCast` says the map
solves the congruence, and this says nothing else does. -/
@[simp] lemma upperTriShift_eq_iff [NeZero p] {γ : SL(2, ℤ)} {j j' : Fin p}
    (hA : IsUnit (((γ 0 0 : ℤ) : ZMod p) + ((j : ℕ) : ZMod p) * ((γ 1 0 : ℤ) : ZMod p))) :
    upperTriShift p γ j = j' ↔
      (((γ 0 0 : ℤ) : ZMod p) + ((j : ℕ) : ZMod p) * ((γ 1 0 : ℤ) : ZMod p))
          * ((j' : ℕ) : ZMod p)
        = ((γ 0 1 : ℤ) : ZMod p) + ((j : ℕ) : ZMod p) * ((γ 1 1 : ℤ) : ZMod p) := by
  refine ⟨fun h ↦ h ▸ mul_upperTriShift_natCast hA, fun h ↦ ?_⟩
  have hcancel : ((upperTriShift p γ j : ℕ) : ZMod p) = ((j' : ℕ) : ZMod p) :=
    hA.mul_left_cancel ((mul_upperTriShift_natCast hA).trans h.symm)
  exact Fin.val_injective (by
    simpa [ZMod.val_natCast_of_lt (upperTriShift p γ j).isLt, ZMod.val_natCast_of_lt j'.isLt]
      using congrArg ZMod.val hcancel)

/-- **On `Γ₀(p)` the offset map is `j ↦ d b + j d²`.** The closed form used by the equivariance
results in `TauCeti/NumberTheory/ModularForms/HeckeSlash/UpperTri/Invariance.lean`, and the reason
`upperTriShift_bijective` holds: `d` is the inverse of `a`, and `d²` is again a unit. -/
@[simp] lemma upperTriShift_natCast_of_mem_Gamma0 [NeZero p] {γ : SL(2, ℤ)} (hγp : γ ∈ Gamma0 p)
    (j : Fin p) : ((upperTriShift p γ j : ℕ) : ZMod p)
      = ((γ 1 1 * γ 0 1 + (j : ℕ) * (γ 1 1 * γ 1 1) : ℤ) : ZMod p) := by
  have hA : ((γ 0 0 + (j : ℕ) * γ 1 0 : ℤ) : ZMod p) = ((γ 0 0 : ℤ) : ZMod p) := by
    push_cast
    exact intCast_apply_zero_zero_add_natCast_mul_apply_one_zero_of_mem_Gamma0 hγp j
  rw [upperTriShift_natCast, hA,
    ZMod.inv_eq_of_mul_eq_one _ _ ((γ 1 1 : ℤ) : ZMod p)
      (intCast_apply_zero_zero_mul_apply_one_one_of_mem_Gamma0 hγp)]
  push_cast
  ring

/-- **The offset map is a bijection.** For `γ ∈ Γ₀(p)` it is the affine permutation
`x ↦ d² x + d b` of `ZMod p`, read through `ZMod.finEquiv`: `d` is the inverse of `a` modulo `p`,
so `d²` is a unit and multiplication by it is a permutation. -/
lemma upperTriShift_bijective [NeZero p] {γ : SL(2, ℤ)} (hγp : γ ∈ Gamma0 p) :
    Function.Bijective (upperTriShift p γ) := by
  have hud : IsUnit ((γ 1 1 : ℤ) : ZMod p) :=
    IsUnit.of_mul_eq_one _ (by
      simpa [mul_comm] using intCast_apply_zero_zero_mul_apply_one_one_of_mem_Gamma0 hγp)
  have haffine : upperTriShift p γ =
      (ZMod.finEquiv p).toEquiv.trans
        ((Units.mulLeft (hud.mul hud).unit).trans
          ((Equiv.addRight (((γ 1 1 * γ 0 1 : ℤ) : ZMod p))).trans
            (ZMod.finEquiv p).toEquiv.symm)) := by
    funext j
    symm
    have hfe : ∀ x : Fin p, (ZMod.finEquiv p).toEquiv x = ((x : ℕ) : ZMod p) :=
      fun x ↦ ZMod.finEquiv_apply x
    simp only [Equiv.trans_apply, Units.mulLeft_apply, Equiv.coe_addRight]
    rw [Equiv.symm_apply_eq]
    simp only [hfe, IsUnit.unit_spec, upperTriShift_natCast_of_mem_Gamma0 hγp]
    push_cast
    ring
  rw [haffine]
  exact Equiv.bijective _

/-- The matrix identity behind the coset factorisation, with the four entries of the second
factor given by hypothesis. -/
private lemma upperTriRep_mul_mapGL_eq {p : ℕ} (j j' : Fin p) (γ γ' : SL(2, ℤ))
    (h00 : γ' 0 0 = γ 0 0 + (j : ℕ) * γ 1 0)
    (h01 : (p : ℤ) * γ' 0 1
      = γ 0 1 + (j : ℕ) * γ 1 1 - (γ 0 0 + (j : ℕ) * γ 1 0) * (j' : ℕ))
    (h10 : γ' 1 0 = (p : ℤ) * γ 1 0)
    (h11 : γ' 1 1 = γ 1 1 - γ 1 0 * (j' : ℕ)) :
    upperTriRep p j * mapGL ℚ γ = mapGL ℚ γ' * upperTriRep p j' := by
  have c00 := congrArg (Int.cast : ℤ → ℚ) h00
  have c01 := congrArg (Int.cast : ℤ → ℚ) h01
  have c10 := congrArg (Int.cast : ℤ → ℚ) h10
  have c11 := congrArg (Int.cast : ℤ → ℚ) h11
  push_cast at c00 c01 c10 c11
  refine Units.ext (Matrix.ext fun r t ↦ ?_)
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two, coe_upperTriRep, coe_upperTriRep, mapGL_coe_matrix, mapGL_coe_matrix]
  fin_cases r <;> fin_cases t <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one,
      Matrix.cons_val_one, algebraMap_int_eq, Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply, Int.coe_castRingHom, Matrix.map_apply, one_mul, mul_one, mul_zero,
      add_zero, zero_mul, zero_add] <;>
    [linear_combination -c00; linear_combination -c01 - ((j' : ℕ) : ℚ) * c00;
      linear_combination -c10; linear_combination -((j' : ℕ) : ℚ) * c10 - (p : ℚ) * c11]

/-- **The coset factorisation.** The product `!![1, j; 0, p] · γ` factors as
`γ' · !![1, j'; 0, p]` with `γ' ∈ Γ₀(N)` and `j'` the shifted offset, and the new lower-right
entry is `d - c j'`.

The two hypotheses are exactly what the factorisation consumes, and neither mentions how `p` and
`N` are related. `a + j c` invertible modulo `p` — for the single offset `j` at hand, not
uniformly — is what makes the offset `j'` exist; `N ∣ p c` is what puts the lower-left entry
`p c` of `γ'` back in `Γ₀(N)`. Neither `p ∣ N` nor any membership at a level built from `N` is
assumed, so `p ∤ N` is not excluded. The `Γ₀(p)` specialisation `exists_mem_Gamma0_upperTriRep_mul`,
where invertibility holds for every offset at once and the map is a bijection, is the form callers
usually want.

The lower-right entry is given as an equation rather than as a congruence because the modulus
at which it is useful varies with the caller; the equivariance results in
`TauCeti/NumberTheory/ModularForms/HeckeSlash/UpperTri/Invariance.lean` read off the congruence
modulo `N` they need from that equation and `Γ₀(N)`-membership. -/
theorem exists_mem_Gamma0_upperTriRep_mul_of_isUnit [NeZero p] {γ : SL(2, ℤ)} {j : Fin p}
    (hA : IsUnit (((γ 0 0 + (j : ℕ) * γ 1 0 : ℤ) : ZMod p)))
    (hpc : (((p : ℤ) * γ 1 0 : ℤ) : ZMod N) = 0) : ∃ γ' : SL(2, ℤ), γ' ∈ Gamma0 N ∧
      (γ' 1 1 : ℤ) = γ 1 1 - γ 1 0 * ((upperTriShift p γ j : ℕ) : ℤ) ∧
      upperTriRep p j * mapGL ℚ γ = mapGL ℚ γ' * upperTriRep p (upperTriShift p γ j) := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 :=
    Matrix.SpecialLinearGroup.fin_two_mul_sub_mul_eq_one γ
  -- the entry `b'` is an integer: the defining congruence of the offset map is exactly `p ∣ …`
  have hdvd : (p : ℤ) ∣ γ 0 1 + (j : ℕ) * γ 1 1
      - (γ 0 0 + (j : ℕ) * γ 1 0) * ((upperTriShift p γ j : ℕ) : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hA' : IsUnit (((γ 0 0 : ℤ) : ZMod p) + ((j : ℕ) : ZMod p) * ((γ 1 0 : ℤ) : ZMod p)) := by
      push_cast at hA
      exact hA
    have hmul := mul_upperTriShift_natCast hA'
    push_cast at hmul ⊢
    linear_combination -hmul
  obtain ⟨b', hb'⟩ := hdvd
  set j' := upperTriShift p γ j
  have hdet' : (!![γ 0 0 + (j : ℕ) * γ 1 0, b';
      (p : ℤ) * γ 1 0, γ 1 1 - γ 1 0 * ((j' : ℕ) : ℤ)]).det = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination hdet + (γ 1 0 : ℤ) * hb'
  -- the witness, with its four entries read off once, so that nothing below depends on how the
  -- `SL(2, ℤ)` subtype and the matrix literal reduce
  set γ' : SL(2, ℤ) := ⟨_, hdet'⟩ with hγ'
  have e00 : γ' 0 0 = γ 0 0 + (j : ℕ) * γ 1 0 := by simp [hγ']
  have e01 : γ' 0 1 = b' := by simp [hγ']
  have e10 : γ' 1 0 = (p : ℤ) * γ 1 0 := by simp [hγ']
  have e11 : γ' 1 1 = γ 1 1 - γ 1 0 * ((j' : ℕ) : ℤ) := by simp [hγ']
  refine ⟨γ', Gamma0_mem.mpr ?_, e11, upperTriRep_mul_mapGL_eq _ _ _ _ e00 ?_ e10 e11⟩
  · rw [e10]; exact hpc
  · rw [e01]; exact hb'.symm

/-- **The coset factorisation at `γ ∈ Γ₀(p)`.** The specialisation in which every offset is
admissible at once: on `Γ₀(p)` the entry `a + j c` is `a`, a unit for every `j`, so the general
statement applies uniformly and the offset map is the closed form `j ↦ d b + j d²`. -/
theorem exists_mem_Gamma0_upperTriRep_mul [NeZero p] {γ : SL(2, ℤ)} (hγp : γ ∈ Gamma0 p)
    (hpc : (((p : ℤ) * γ 1 0 : ℤ) : ZMod N) = 0) (j : Fin p) : ∃ γ' : SL(2, ℤ), γ' ∈ Gamma0 N ∧
      (γ' 1 1 : ℤ) = γ 1 1 - γ 1 0 * ((upperTriShift p γ j : ℕ) : ℤ) ∧
      upperTriRep p j * mapGL ℚ γ = mapGL ℚ γ' * upperTriRep p (upperTriShift p γ j) :=
  exists_mem_Gamma0_upperTriRep_mul_of_isUnit
    (isUnit_intCast_apply_zero_zero_add_natCast_mul_apply_one_zero_of_mem_Gamma0 hγp j) hpc

/-- **The coset factorisation at `γ ∈ Γ₀(N)`.** The specialisation of
`exists_mem_Gamma0_upperTriRep_mul` that `p ∣ N` and `γ ∈ Γ₀(N)` afford: both hypotheses of the
general statement follow, and the lower-right entry `d - c j'` becomes a congruence modulo `N`,
so `γ'` has the same `Gamma0Map` value as `γ`. That congruence is what lets the equivariance
results in `TauCeti/NumberTheory/ModularForms/HeckeSlash/UpperTri/Invariance.lean` carry a fixed
character, and it is the form every `Γ₀(N)` caller wants. -/
theorem exists_mem_Gamma0_upperTriRep_mul_of_mem_Gamma0 [NeZero p] (hpN : p ∣ N) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 N) (j : Fin p) :
    ∃ γ' : SL(2, ℤ), γ' ∈ Gamma0 N ∧ ((γ' 1 1 : ℤ) : ZMod N) = ((γ 1 1 : ℤ) : ZMod N) ∧
      upperTriRep p j * mapGL ℚ γ = mapGL ℚ γ' * upperTriRep p (upperTriShift p γ j) := by
  obtain ⟨γ', hγ', hdd, hmul⟩ := exists_mem_Gamma0_upperTriRep_mul
    (Gamma0_le_Gamma0_of_dvd hpN hγ) (by rw [Int.cast_mul, Gamma0_mem.mp hγ, mul_zero]) j
  refine ⟨γ', hγ', ?_, hmul⟩
  rw [hdd]
  push_cast
  rw [Gamma0_mem.mp hγ]
  ring

/-- **Conjugating an element of `Γ(N)` through `[1, 0; 0, p]` lands in `Γ₁(N)`**, for `p ∣ N`:
`[1, 0; 0, p] · δ = ε · [1, 0; 0, p]` with `ε ∈ Γ₁(N)`. This is what lets a `Γ₁(N)`-invariant
function absorb a change of the extra representative of the descent family
(`Newforms/Descent/LevelCommute.lean`). -/
theorem exists_mem_Gamma1_upperTriRep_mul_of_mem_Gamma [NeZero p] (hpN : p ∣ N) {δ : SL(2, ℤ)}
    (hδ : δ ∈ Gamma N) :
    ∃ ε ∈ Gamma1 N, upperTriRep p ⟨0, NeZero.pos p⟩ * mapGL ℚ δ =
      mapGL ℚ ε * upperTriRep p ⟨0, NeZero.pos p⟩ := by
  obtain ⟨h00, h01, -, -⟩ := Gamma_mem.mp (Gamma_le_Gamma_of_dvd hpN hδ)
  obtain ⟨ε, hε, hdd, hmul⟩ :=
    exists_mem_Gamma0_upperTriRep_mul_of_mem_Gamma0 hpN (Gamma_le_Gamma0 N hδ) ⟨0, NeZero.pos p⟩
  have hshift : upperTriShift p δ ⟨0, NeZero.pos p⟩ = ⟨0, NeZero.pos p⟩ := by
    rw [upperTriShift_eq_iff (by simp [h00])]
    simp [h01]
  refine ⟨ε, mem_Gamma1_iff.mpr ⟨hε, ?_⟩, ?_⟩
  · rw [hdd, (Gamma_mem.mp hδ).2.2.2]
  · rwa [hshift] at hmul

end HeckeRing.GL2
