/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.GLPadicInt` occurs in the statements below.
public import TauCeti.NumberTheory.Padics.GeneralLinearGroup.Integral
-- `TauCeti.GL2Mirabolic`, `TauCeti.GL2Borel.mk` and `TauCeti.GL2WeylElement` occur in the
-- statements below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Mirabolic

/-!
# The mirabolic monoid `P⁺` of `GL₂(ℚ_p)`

Colmez's construction of the `p`-adic local Langlands correspondence for `GL₂(ℚ_p)` starts from
the observation that an étale `(φ, Γ)`-module is a module over the submonoid

`P⁺ = {!![a, b; 0, 1] : a ∈ ℤ_p ∖ {0}, b ∈ ℤ_p}`

of the mirabolic subgroup `P(ℚ_p)`: the unipotent matrix `!![1, 1; 0, 1]` acts as multiplication
by `1 + T`, the matrix `φ = !![p, 0; 0, 1]` acts as the Frobenius `φ`, and `!![a, 0; 0, 1]` for
`a ∈ ℤ_p×` acts as the element of `Γ` with cyclotomic character `a`. The module `D ⊠ ℚ_p` is then
obtained by inverting `φ`, since `P(ℚ_p)` is generated as a monoid by `P⁺` and `φ⁻¹`.

This file defines `P⁺`, characterizes its elements by the norms of their two upper entries,
identifies its group of invertible elements with `P(ℤ_p) = P ∩ GL₂(ℤ_p)`, and proves the
generation statement. It also records which upper-triangular matrices lie in `K = GL₂(ℤ_p)`.

## Main definitions

* `TauCeti.GL2MirabolicPlus p`: the submonoid `P⁺` of `GL (Fin 2) ℚ_[p]`.
* `TauCeti.GL2MirabolicPlus.frobenius p`: the matrix `φ = !![p, 0; 0, 1]`.
* `TauCeti.GL2MirabolicPadicInt p`: the subgroup `P(ℤ_p) = P ∩ GL₂(ℤ_p)`.

## Main results

* `TauCeti.GL2Borel.mk_mem_glPadicInt_iff`: `!![a, b; 0, d]` lies in `GL₂(ℤ_p)` exactly when `a`
  and `d` are units of `ℤ_p` and `b ∈ ℤ_p`.
* `TauCeti.GL2MirabolicPlus.mk_mem_iff`: `!![a, b; 0, 1] ∈ P⁺` exactly when `a, b ∈ ℤ_p`.
* `TauCeti.GL2MirabolicPlus.mem_and_inv_mem_iff`: the elements of `P⁺` whose inverse lies in `P⁺`
  are exactly the elements of `P(ℤ_p) = P ∩ GL₂(ℤ_p)`.
* `TauCeti.GL2MirabolicPlus.frobenius_notMem_glPadicInt`: the integral matrix `φ` does not lie in
  `GL₂(ℤ_p)`, so entrywise integrality alone does not characterise `GL₂(ℤ_p)`.
* `TauCeti.GL2MirabolicPadicInt.mem_iff`: `P(ℤ_p)` consists of the mirabolic matrices whose
  upper-left entry is a `p`-adic unit and whose upper-right entry is integral.
* `TauCeti.GL2MirabolicPlus.exists_frobenius_pow_mul_mem`: every element of `P(ℚ_p)` is moved
  into `P⁺` by a power of `φ`.
* `TauCeti.GL2MirabolicPlus.closure_insert_frobenius_inv_eq_gl2Mirabolic`: `P(ℚ_p)` is generated
  as a monoid by `P⁺` and `φ⁻¹`.

## References

* P. Colmez, *Représentations de `GL₂(ℚ_p)` et `(φ, Γ)`-modules*, Astérisque 330 (2010),
  Introduction §4 (Remarque 0.4) and §III.1.1.
* V. Paškūnas, *The image of Colmez's Montreal functor*, Publ. Math. IHÉS 118 (2013), §1.
-/

public section

namespace TauCeti

open Matrix

variable (p : ℕ) [Fact p.Prime]

/-- An upper-triangular matrix `!![a, b; 0, d]` over `ℚ_p` lies in `GL₂(ℤ_p)` exactly when its
diagonal entries are units of `ℤ_p` and its upper-right entry lies in `ℤ_p`. -/
@[simp]
theorem GL2Borel.mk_mem_glPadicInt_iff (a d : ℚ_[p]ˣ) (b : ℚ_[p]) :
    GL2Borel.mk a d b ∈ GLPadicInt (Fin 2) p ↔
      ‖(a : ℚ_[p])‖ = 1 ∧ ‖(d : ℚ_[p])‖ = 1 ∧ ‖b‖ ≤ 1 := by
  simp only [GLPadicInt.mem_iff, GL2Borel.coe_mk, Fin.forall_fin_two, Matrix.det_fin_two_of]
  constructor
  · rintro ⟨⟨⟨ha, hb⟩, -, hd⟩, hdet⟩
    simp only [mul_zero, sub_zero, norm_mul] at hdet
    -- Two norms at most `1` with product `1` are both `1`.
    exact ⟨le_antisymm ha (hdet ▸ mul_le_of_le_one_right (norm_nonneg _) hd),
      le_antisymm hd (hdet ▸ mul_le_of_le_one_left (norm_nonneg _) ha), hb⟩
  · rintro ⟨ha, hd, hb⟩
    simp [ha, hd, hb]

/-- The Weyl element `!![0, 1; 1, 0]` lies in `GL₂(ℤ_p)`. -/
theorem gl2WeylElement_mem_glPadicInt : GL2WeylElement ℚ_[p] ∈ GLPadicInt (Fin 2) p := by
  rw [GLPadicInt.mem_iff, coe_gl2WeylElement, Matrix.det_fin_two_of]
  refine ⟨fun i j ↦ ?_, by simp⟩
  fin_cases i <;> fin_cases j <;> simp

/-- Colmez's **mirabolic monoid** `P⁺`: the matrices `!![a, b; 0, 1]` of `GL₂(ℚ_p)` with
`a, b ∈ ℤ_p`. Since such a matrix is invertible, `a` is automatically nonzero. -/
def GL2MirabolicPlus : Submonoid (GL (Fin 2) ℚ_[p]) where
  carrier := {g | g ∈ GL2Mirabolic ℚ_[p] ∧ ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 0‖ ≤ 1 ∧
    ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1‖ ≤ 1}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' {g h} hg hh := by
    obtain ⟨hgP, hg₀, hg₁⟩ := hg
    obtain ⟨hhP, hh₀, hh₁⟩ := hh
    -- The upper row of `g h` is `(g₀₀ h₀₀, g₀₀ h₀₁ + g₀₁)`.
    refine ⟨mul_mem hgP hhP, ?_, ?_⟩ <;>
      simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, (GL2Mirabolic.mem_iff.mp hhP).1,
        (GL2Mirabolic.mem_iff.mp hhP).2, mul_zero, add_zero, mul_one, norm_mul]
    · exact (mul_le_of_le_one_left (norm_nonneg _) hg₀).trans hh₀
    · refine (Padic.nonarchimedean _ _).trans (max_le ?_ hg₁)
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hg₀).trans hh₁

namespace GL2MirabolicPlus

variable {p}

/-- Membership in `P⁺`: a mirabolic matrix whose two upper entries lie in `ℤ_p`. -/
theorem mem_iff {g : GL (Fin 2) ℚ_[p]} :
    g ∈ GL2MirabolicPlus p ↔ g ∈ GL2Mirabolic ℚ_[p] ∧
      ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 0‖ ≤ 1 ∧ ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1‖ ≤ 1 :=
  Iff.rfl

variable (p) in
/-- `P⁺` is a submonoid of the mirabolic subgroup. -/
theorem le_gl2Mirabolic : GL2MirabolicPlus p ≤ (GL2Mirabolic ℚ_[p]).toSubmonoid :=
  fun _ hg ↦ hg.1

/-- The mirabolic matrix `!![a, b; 0, 1]` lies in `P⁺` exactly when `a, b ∈ ℤ_p`. -/
@[simp]
theorem mk_mem_iff (a : ℚ_[p]ˣ) (b : ℚ_[p]) :
    GL2Borel.mk a 1 b ∈ GL2MirabolicPlus p ↔ ‖(a : ℚ_[p])‖ ≤ 1 ∧ ‖b‖ ≤ 1 := by
  simp [mem_iff]

/-- The unipotent matrix `!![1, b; 0, 1]` lies in `P⁺` exactly when `b ∈ ℤ_p`. -/
-- Not a simp lemma: `simp` unfolds `Matrix.GeneralLinearGroup.upperRightHom b` to its matrix.
theorem upperRightHom_mem_iff (b : ℚ_[p]) :
    GeneralLinearGroup.upperRightHom b ∈ GL2MirabolicPlus p ↔ ‖b‖ ≤ 1 := by
  simp only [mem_iff, GL2Mirabolic.upperRightHom_mem, true_and]
  simp [GeneralLinearGroup.upperRightHom]

/-- The determinant `a` of an element `!![a, b; 0, 1]` of `P⁺` lies in `ℤ_p`. -/
theorem norm_det_le_one {g : GL (Fin 2) ℚ_[p]} (hg : g ∈ GL2MirabolicPlus p) :
    ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]).det‖ ≤ 1 := by
  rw [GL2Mirabolic.det_eq hg.1]
  exact (mem_iff.mp hg).2.1

/-- **The invertible elements of `P⁺` form `P(ℤ_p)`.** An element of `P⁺` has its inverse in `P⁺`
exactly when it lies in `P ∩ GL₂(ℤ_p)`. -/
theorem mem_and_inv_mem_iff {g : GL (Fin 2) ℚ_[p]} :
    g ∈ GL2MirabolicPlus p ∧ g⁻¹ ∈ GL2MirabolicPlus p ↔
      g ∈ GL2Mirabolic ℚ_[p] ⊓ GLPadicInt (Fin 2) p := by
  constructor
  · rintro ⟨hg, hg'⟩
    -- The determinants of `g` and `g⁻¹` have norm at most `1` and product `1`, so both are units.
    have hprod : ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]).det‖ *
        ‖((g⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]).det‖ = 1 := by
      rw [← norm_mul, ← Matrix.det_mul, ← Units.val_mul]
      simp
    refine ⟨hg.1, GLPadicInt.mem_iff.mpr ⟨fun i j ↦ ?_, ?_⟩⟩
    · fin_cases i <;> fin_cases j
      exacts [hg.2.1, hg.2.2, by simp [(GL2Mirabolic.mem_iff.mp hg.1).1],
        by simp [(GL2Mirabolic.mem_iff.mp hg.1).2]]
    · exact le_antisymm (norm_det_le_one hg)
        (hprod ▸ mul_le_of_le_one_right (norm_nonneg _) (norm_det_le_one hg'))
  · -- An element of `P ∩ GL₂(ℤ_p)` has integral entries, and so has its inverse.
    have key : ∀ x ∈ GL2Mirabolic ℚ_[p] ⊓ GLPadicInt (Fin 2) p, x ∈ GL2MirabolicPlus p :=
      fun x hx ↦ ⟨(Subgroup.mem_inf.mp hx).1,
        (GLPadicInt.mem_iff.mp (Subgroup.mem_inf.mp hx).2).1 0 0,
        (GLPadicInt.mem_iff.mp (Subgroup.mem_inf.mp hx).2).1 0 1⟩
    exact fun hg ↦ ⟨key g hg, key g⁻¹ (inv_mem hg)⟩

variable (p) in
/-- `P(ℤ_p) = P ∩ GL₂(ℤ_p)` is contained in `P⁺`. -/
theorem inf_glPadicInt_le :
    (GL2Mirabolic ℚ_[p] ⊓ GLPadicInt (Fin 2) p).toSubmonoid ≤ GL2MirabolicPlus p :=
  fun _ hg ↦ (mem_and_inv_mem_iff.mpr hg).1

variable (p) in
/-- The matrix `φ = !![p, 0; 0, 1]`, which acts on an étale `(φ, Γ)`-module as its Frobenius. -/
noncomputable def frobenius : GL (Fin 2) ℚ_[p] :=
  GL2Borel.mk (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) 1 0

/-- The powers of `φ` are the diagonal matrices `!![p ^ k, 0; 0, 1]`. -/
-- Not a simp lemma: `simp` first rewrites the coercion of a power by `Units.val_pow_eq_pow_val`.
theorem coe_frobenius_pow (k : ℕ) :
    ((frobenius p ^ k : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
      !![(p : ℚ_[p]) ^ k, 0; 0, 1] := by
  induction k with
  | zero => simp [Matrix.one_fin_two]
  | succ k ih =>
    rw [pow_succ, Units.val_mul, ih, frobenius, GL2Borel.coe_mk, Matrix.mul_fin_two]
    simp [pow_succ]

/-- The underlying matrix of `φ` is `!![p, 0; 0, 1]`. -/
@[simp]
theorem coe_frobenius :
    ((frobenius p : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
      !![(p : ℚ_[p]), 0; 0, 1] := by
  simpa using coe_frobenius_pow (p := p) 1

/-- The underlying matrix of `φ⁻¹` is `!![p⁻¹, 0; 0, 1]`. -/
-- Not a simp lemma: `simp` first rewrites the coercion of an inverse by `Matrix.coe_units_inv`.
theorem coe_frobenius_inv :
    (((frobenius p)⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
      !![(p : ℚ_[p])⁻¹, 0; 0, 1] := by
  rw [Matrix.coe_units_inv, coe_frobenius, Matrix.inv_def, Matrix.adjugate_fin_two_of,
    Matrix.det_fin_two_of]
  simp

variable (p) in
/-- `φ = !![p, 0; 0, 1]` lies in `P⁺`. -/
theorem frobenius_mem : frobenius p ∈ GL2MirabolicPlus p := by
  rw [frobenius, mk_mem_iff]
  simpa using (Padic.norm_p_lt_one (p := p)).le

variable (p) in
/-- The integral matrix `φ = !![p, 0; 0, 1]` does not lie in `GL₂(ℤ_p)`, its determinant `p` not
being a unit of `ℤ_p`: entrywise integrality alone does not characterise `GL₂(ℤ_p)`. -/
theorem frobenius_notMem_glPadicInt : frobenius p ∉ GLPadicInt (Fin 2) p := fun h ↦ by
  have hdet := (GLPadicInt.mem_iff.mp h).2
  rw [coe_frobenius, Matrix.det_fin_two_of] at hdet
  simp only [mul_one, mul_zero, sub_zero] at hdet
  exact (Padic.norm_p_lt_one (p := p)).ne hdet

variable (p) in
/-- `φ⁻¹ = !![p⁻¹, 0; 0, 1]` does not lie in `P⁺`: otherwise `φ` would lie in `GL₂(ℤ_p)`, but its
determinant `p` is not a unit of `ℤ_p`. -/
theorem frobenius_inv_notMem : (frobenius p)⁻¹ ∉ GL2MirabolicPlus p := fun h ↦
  frobenius_notMem_glPadicInt p (mem_and_inv_mem_iff.mp ⟨frobenius_mem p, h⟩).2

/-- **Every element of `P(ℚ_p)` is moved into `P⁺` by a power of `φ`**: multiplying
`!![a, b; 0, 1]` on the left by `φ ^ k` multiplies `a` and `b` by `p ^ k`, which makes them
integral for `k` large. -/
theorem exists_frobenius_pow_mul_mem {g : GL (Fin 2) ℚ_[p]} (hg : g ∈ GL2Mirabolic ℚ_[p]) :
    ∃ k : ℕ, frobenius p ^ k * g ∈ GL2MirabolicPlus p := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt
    (max ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 0‖ ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1‖) hp
  -- `‖p ^ k * x‖ = p ^ (-k) * ‖x‖`, which is at most `1` once `‖x‖ < p ^ k`.
  have key : ∀ x : ℚ_[p], ‖x‖ < (p : ℝ) ^ k → ‖(p : ℚ_[p]) ^ k * x‖ ≤ 1 := fun x hx ↦ by
    rw [norm_mul, Padic.norm_p_pow, _root_.zpow_neg, zpow_natCast, inv_mul_le_iff₀ (by positivity),
      mul_one]
    exact hx.le
  refine ⟨k, mul_mem (pow_mem (frobenius_mem p).1 k) hg, ?_, ?_⟩ <;>
    simp only [Units.val_mul, coe_frobenius_pow, Matrix.mul_apply, Fin.sum_univ_two] <;>
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, zero_mul, add_zero]
  exacts [key _ ((le_max_left _ _).trans_lt hk), key _ ((le_max_right _ _).trans_lt hk)]

variable (p) in
/-- **`P(ℚ_p)` is generated as a monoid by `P⁺` and `φ⁻¹`.** -/
theorem closure_insert_frobenius_inv_eq_gl2Mirabolic :
    Submonoid.closure (insert (frobenius p)⁻¹ (GL2MirabolicPlus p : Set (GL (Fin 2) ℚ_[p]))) =
      (GL2Mirabolic ℚ_[p]).toSubmonoid := by
  refine le_antisymm ((Submonoid.closure_le).mpr ?_) fun g hg ↦ ?_
  · rintro g (rfl | hg)
    exacts [Subgroup.inv_mem _ (frobenius_mem p).1, hg.1]
  · obtain ⟨k, hk⟩ := exists_frobenius_pow_mul_mem hg
    have hg' : g = (frobenius p)⁻¹ ^ k * (frobenius p ^ k * g) := by
      rw [inv_pow, inv_mul_cancel_left]
    rw [hg']
    exact mul_mem (pow_mem (Submonoid.subset_closure (Set.mem_insert _ _)) k)
      (Submonoid.subset_closure (Set.mem_insert_of_mem _ hk))

end GL2MirabolicPlus

/-- The integral mirabolic subgroup `P(ℤ_p) = P ∩ GL₂(ℤ_p)`: the matrices `!![a, b; 0, 1]` with
`a ∈ ℤ_p^×` and `b ∈ ℤ_p`. -/
noncomputable def GL2MirabolicPadicInt : Subgroup (GL (Fin 2) ℚ_[p]) :=
  GL2Mirabolic ℚ_[p] ⊓ GLPadicInt (Fin 2) p

namespace GL2MirabolicPadicInt

/-- `P(ℤ_p)` is the intersection of the mirabolic subgroup with `GL₂(ℤ_p)`. -/
theorem eq_inf : GL2MirabolicPadicInt p = GL2Mirabolic ℚ_[p] ⊓ GLPadicInt (Fin 2) p :=
  (rfl)

/-- `P(ℤ_p) ⊆ P`. -/
theorem le_gl2Mirabolic : GL2MirabolicPadicInt p ≤ GL2Mirabolic ℚ_[p] :=
  inf_le_left

/-- `P(ℤ_p) ⊆ GL₂(ℤ_p)`. -/
theorem le_glPadicInt : GL2MirabolicPadicInt p ≤ GLPadicInt (Fin 2) p :=
  inf_le_right

variable {p}

/-- **Membership in `P(ℤ_p)`**: a mirabolic matrix `!![a, b; 0, 1]` lies in `GL₂(ℤ_p)` exactly when
`a` is a `p`-adic unit and `b` is integral. -/
theorem mem_iff {g : GL (Fin 2) ℚ_[p]} :
    g ∈ GL2MirabolicPadicInt p ↔ g ∈ GL2Mirabolic ℚ_[p] ∧
      ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 0‖ = 1 ∧
      ‖(g : Matrix (Fin 2) (Fin 2) ℚ_[p]) 0 1‖ ≤ 1 := by
  rw [eq_inf, Subgroup.mem_inf, and_congr_right_iff]
  intro hg
  obtain ⟨hg₀, hg₁⟩ := GL2Mirabolic.mem_iff.mp hg
  rw [GLPadicInt.mem_iff, GL2Mirabolic.det_eq hg]
  refine ⟨fun h ↦ ⟨h.2, h.1 0 1⟩, fun h ↦ ⟨fun i j ↦ ?_, h.1⟩⟩
  fin_cases i <;> fin_cases j <;> simp [h.1.le, h.2, hg₀, hg₁]

/-- **Membership in `P(ℤ_p)`**: the mirabolic matrix `!![a, b; 0, 1]` lies in `P(ℤ_p)` exactly
when `a` is a `p`-adic unit and `b` is integral. -/
@[simp]
theorem mk_mem_iff (a : ℚ_[p]ˣ) (b : ℚ_[p]) :
    GL2Borel.mk a 1 b ∈ GL2MirabolicPadicInt p ↔ ‖(a : ℚ_[p])‖ = 1 ∧ ‖b‖ ≤ 1 := by
  simp [mem_iff]

variable (p) in
/-- `P(ℤ_p) ⊆ P⁺`. -/
theorem le_gl2MirabolicPlus : (GL2MirabolicPadicInt p).toSubmonoid ≤ GL2MirabolicPlus p :=
  GL2MirabolicPlus.inf_glPadicInt_le p

end GL2MirabolicPadicInt

end TauCeti
