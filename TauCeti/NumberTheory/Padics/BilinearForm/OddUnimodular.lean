/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import TauCeti.LinearAlgebra.BilinearForm.Characteristic
import Mathlib.NumberTheory.Padics.RingHoms
import TauCeti.Data.ZMod.Eight
import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
import TauCeti.LinearAlgebra.BilinearForm.Isometry
import TauCeti.LinearAlgebra.BilinearForm.Odd.LocalRing
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal
import TauCeti.LinearAlgebra.PerfectPairing.Basis
import TauCeti.NumberTheory.Padics.DyadicUnits
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# Odd unimodular forms over `ℤ_[2]`

A symmetric bilinear form over `ℤ_[2]` is *odd unimodular* when its Gram determinant is a unit
and it represents a unit. Such a form has an orthogonal basis whose self-pairings are units
(`LinearMap.BilinForm.IsSymm.exists_orthogonal_basis_isUnit_of_exists_isUnit_apply_self`). It has
two invariants besides its rank: the square class of its determinant, and its *oddity*, the
self-pairing of a characteristic vector modulo `8`
(`LinearMap.BilinForm.IsCharacteristic.eight_dvd_apply_self_sub_apply_self`), which is also the
trace modulo `8` of any unit diagonal Gram matrix. This file proves that the rank, the determinant
square class and the oddity classify odd unimodular forms over `ℤ_[2]`. Together with
`LinearMap.BilinForm.IsSymm.equivalent_iff_isSquare_det_mul_det_of_even` for even forms, this
classifies the unimodular forms over `ℤ_[2]`. The forms `⟨1, 1⟩` and `⟨3, 3⟩` show that the oddity
cannot be dropped (`TauCeti.not_equivalent_toBilin'_diagonal_one_one_three_three_padicInt_two`).

## Main results

* `LinearMap.BilinForm.iIsOrtho.exists_basis_iIsOrtho_apply_self_eq`: a form with a unit diagonal
  orthogonal basis has an orthogonal basis realizing any unit diagonal with the same determinant
  square class and oddity.
* `LinearMap.BilinForm.iIsOrtho.equivalent_iff_isSquare_prod_mul_prod_and_eight_dvd`: two forms
  with unit diagonal orthogonal bases of the same size are isometric exactly when their diagonals
  have the same product up to a square and the same sum modulo `8`.
* `LinearMap.BilinForm.IsSymm.equivalent_iff_isSquare_det_mul_det_and_eight_dvd_of_odd`: odd
  unimodular forms of the same rank are isometric exactly when the product of their Gram
  determinants is a square and characteristic vectors have the same self-pairing modulo `8`.

## Implementation notes

A unit of `ℤ_[2]` is a square exactly when it is `1` modulo `8`, so a diagonal entry matters only
through its residue among `1, 3, 5, 7`. If `b` is an orthogonal basis with self-pairings `dᵢ`, then
`b i` represents `dᵢ`, and `b i + 2 b k` represents `dᵢ + 4 dₖ ≡ 5 dᵢ` and is orthogonal to
`-2 dₖ b i + dᵢ b k`. These vectors never change how many diagonal entries are `3` modulo `4`. When
`d₀`, `d₁`, `d₂` are all `1` or all `3` modulo `4`, the vectors `b₀ + b₁ + b₂` and
`b₀ + b₁ + b₂ + 2 b₃` represent units of the other kind; the invariants guarantee that a fourth
basis vector exists whenever this move is needed
(`ZMod.four_le_of_forall_eq_or_eq`). Given a target diagonal `v` with the same
determinant class and oddity, one of these vectors represents some `vⱼ` up to a unit square and is
orthogonal to a vector with unit self-pairing, so it splits off an odd unimodular complement, and
induction on the rank applies.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §93.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 8, §4.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

open Module
open LinearMap (BilinForm)
open PadicInt (eight_dvd_sub_iff_toZModPow_three_eq exists_eq_sq_mul_of_toZModPow_three_eq
  isSquare_mul_iff_toZModPow_three_eq isUnit_of_toZModPow_three_mul_self
  toZModPow_three_mul_self_of_isUnit)

namespace LinearMap.BilinForm

universe u

/-! ### Realizing a prescribed diagonal -/

section Realization

variable {M N : Type*} [AddCommGroup M] [Module ℤ_[2] M] [AddCommGroup N] [Module ℤ_[2] N]

/-- Isometric forms with unit diagonal orthogonal bases have diagonals whose products differ by a
square and whose sums agree modulo `8`. -/
private theorem Equivalent.isSquare_prod_mul_prod_and_eight_dvd {B : BilinForm ℤ_[2] M}
    {C : BilinForm ℤ_[2] N} (h : B.Equivalent C) {n : ℕ} {b : Basis (Fin n) ℤ_[2] M}
    {c : Basis (Fin n) ℤ_[2] N} (hb : B.iIsOrtho b) (hc : C.iIsOrtho c)
    (hbu : ∀ i, IsUnit (B (b i) (b i))) :
    IsSquare ((∏ i, B (b i) (b i)) * ∏ i, C (c i) (c i)) ∧
      (8 : ℤ_[2]) ∣ ∑ i, C (c i) (c i) - ∑ i, B (b i) (b i) := by
  have hbdet : IsUnit (B.toMatrix b).det := hb.isUnit_det_toMatrix hbu
  have : B.IsPerfPair := b.isPerfPair_of_isUnit_det B hbdet
  refine ⟨?_, h.eight_dvd_sum_apply_self_sub_sum_apply_self PadicInt.two_dvd_sq_sub_self hb hc⟩
  simpa [hb.toMatrix_eq_diagonal, hc.toMatrix_eq_diagonal] using h.isSquare_det_mul_det b c

/-- **Multiplying a represented unit by `5`.** Let `z` have unit self-pairing, and let `e` and `f`
be orthogonal vectors with unit self-pairings such that `B z e = B e e` and `B z f = 0`. Then
`z + 2 f` represents `B z z + 4 B f f`, which is `5 B z z` modulo `8`, and it is orthogonal to the
vector `-2 (B f f) e + (B e e) f`, whose self-pairing is a unit. -/
private theorem exists_toZModPow_three_apply_self_eq_five_mul {B : BilinForm ℤ_[2] M}
    (hB : B.IsSymm) {z e f : M} (hz : IsUnit (B z z)) (he : IsUnit (B e e))
    (hf : IsUnit (B f f)) (hze : B z e = B e e) (hzf : B z f = 0) (hef : B e f = 0) :
    ∃ x y, PadicInt.toZModPow 3 (B x x) = 5 * PadicInt.toZModPow 3 (B z z) ∧ IsUnit (B y y) ∧
      B x y = 0 := by
  have hfz : B f z = 0 := by rw [← hB.eq, hzf]
  have hfe : B f e = 0 := by rw [← hB.eq, hef]
  have h5 : ∀ a c : ZMod (2 ^ 3), a * a = 1 → c * c = 1 → a + 4 * c = 5 * a := by decide
  have hsum : PadicInt.toZModPow 3 (B e e + 4 * B f f) = 5 * PadicInt.toZModPow 3 (B e e) := by
    rw [map_add, map_mul, map_ofNat]
    exact h5 _ _ (toZModPow_three_mul_self_of_isUnit he) (toZModPow_three_mul_self_of_isUnit hf)
  refine ⟨z + (2 : ℤ_[2]) • f, (-2 * B f f) • e + B e e • f, ?_, ?_, ?_⟩
  · have hxx : B (z + (2 : ℤ_[2]) • f) (z + (2 : ℤ_[2]) • f) = B z z + 4 * B f f := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hzf,
        hfz]
      ring
    rw [hxx, map_add, map_mul, map_ofNat]
    exact h5 _ _ (toZModPow_three_mul_self_of_isUnit hz) (toZModPow_three_mul_self_of_isUnit hf)
  · have hyy : B ((-2 * B f f) • e + B e e • f) ((-2 * B f f) • e + B e e • f) =
        B e e * B f f * (B e e + 4 * B f f) := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hef,
        hfe]
      ring
    have h5u : ∀ a : ZMod (2 ^ 3), a * a = 1 → 5 * a * (5 * a) = 1 := by decide
    rw [hyy]
    refine (he.mul hf).mul (isUnit_of_toZModPow_three_mul_self ?_)
    rw [hsum]
    exact h5u _ (toZModPow_three_mul_self_of_isUnit he)
  · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hze, hzf,
      hfe]
    ring

/-- **Representing a residue of the other kind.** Let `b` be an orthogonal basis of rank at least
four whose self-pairings are units congruent to `y` or `5 y` modulo `8`. Then for `a` equal to `-y`
or `-5 y`, either `b₀ + b₁ + b₂` or `b₀ + b₁ + b₂ + 2 b₃` represents `a` modulo `8`, and it is
orthogonal to a vector with unit self-pairing. -/
private theorem exists_toZModPow_three_apply_self_eq_of_four_le {B : BilinForm ℤ_[2] M} {m : ℕ}
    {b : Basis (Fin m) ℤ_[2] M} (hb : B.iIsOrtho b) (hbu : ∀ i, IsUnit (B (b i) (b i)))
    (h4 : 4 ≤ m) {y a : ZMod (2 ^ 3)} (hy : y * y = 1)
    (hdy : ∀ i, PadicInt.toZModPow 3 (B (b i) (b i)) = y ∨
      PadicInt.toZModPow 3 (B (b i) (b i)) = 5 * y)
    (ha : a = -y ∨ a = -(5 * y)) :
    ∃ x z, PadicInt.toZModPow 3 (B x x) = a ∧ IsUnit (B z z) ∧ B x z = 0 := by
  -- With `z = b₀ + b₁ + b₂`, the residue of `B z z` lies in `{-y, -5y}`, so either `z` or
  -- `z + 2 b₃` represents `a`.
  let e : Fin 4 → Fin m := Fin.castLE h4
  have hoe (p q : Fin 4) (hpq : p ≠ q) : B (b (e p)) (b (e q)) = 0 :=
    iIsOrtho_def.mp hb _ _ ((Fin.castLE_injective _).ne hpq)
  set z := b (e 0) + b (e 1) + b (e 2) with hz
  have hzz : B z z = B (b (e 0)) (b (e 0)) + B (b (e 1)) (b (e 1)) + B (b (e 2)) (b (e 2)) := by
    simp (disch := decide) only [hz, map_add, LinearMap.add_apply, hoe]
    ring
  have hz0 : B z (b (e 0)) = B (b (e 0)) (b (e 0)) := by
    simp (disch := decide) only [hz, map_add, LinearMap.add_apply, hoe]
    ring
  have hz3 : B z (b (e 3)) = 0 := by
    simp (disch := decide) only [hz, map_add, LinearMap.add_apply, hoe]
    ring
  have hzy : PadicInt.toZModPow 3 (B z z) = -y ∨ PadicInt.toZModPow 3 (B z z) = -(5 * y) := by
    have key₂ : ∀ y a b : ZMod (2 ^ 3), y * y = 1 → (a = y ∨ a = 5 * y) → (b = y ∨ b = 5 * y) →
        (a + b = 2 * y ∨ a + b = 6 * y) := by decide
    have key₃ : ∀ y s c : ZMod (2 ^ 3), y * y = 1 → (s = 2 * y ∨ s = 6 * y) →
        (c = y ∨ c = 5 * y) → (s + c = -y ∨ s + c = -(5 * y)) := by decide
    simpa only [hzz, map_add] using
      key₃ y _ _ hy (key₂ y _ _ hy (hdy (e 0)) (hdy (e 1))) (hdy (e 2))
  have hzu : IsUnit (B z z) := by
    have key : ∀ y a : ZMod (2 ^ 3), y * y = 1 → (a = -y ∨ a = -(5 * y)) → a * a = 1 := by decide
    exact isUnit_of_toZModPow_three_mul_self (key y _ hy hzy)
  have haz : a = PadicInt.toZModPow 3 (B z z) ∨ a = 5 * PadicInt.toZModPow 3 (B z z) := by
    have key : ∀ y p q : ZMod (2 ^ 3), y * y = 1 → (p = -y ∨ p = -(5 * y)) →
        (q = -y ∨ q = -(5 * y)) → p = q ∨ p = 5 * q := by decide
    exact key y _ _ hy ha hzy
  rcases haz with haz | haz
  · exact ⟨z, b (e 3), haz.symm, hbu (e 3), hz3⟩
  · obtain ⟨x, w, hx, hw, hxw⟩ := exists_toZModPow_three_apply_self_eq_five_mul hb.isSymm hzu
      (hbu (e 0)) (hbu (e 3)) hz0 hz3 (hoe 0 3 (by decide))
    exact ⟨x, w, hx.trans haz.symm, hw, hxw⟩

/-- **A vector representing a target entry, with an odd orthogonal complement.** Let `b` be an
orthogonal basis of rank at least two with unit self-pairings `dᵢ`, and let `v` be a unit family
whose product and sum agree with those of `d` modulo `8`. Then some `vⱼ` is represented, modulo `8`,
by a vector `x` orthogonal to a vector with unit self-pairing. -/
private theorem exists_toZModPow_three_apply_self_eq {B : BilinForm ℤ_[2] M} {m : ℕ}
    {b : Basis (Fin (m + 2)) ℤ_[2] M} (hb : B.iIsOrtho b) (hbu : ∀ i, IsUnit (B (b i) (b i)))
    {v : Fin (m + 2) → ℤ_[2]} (hv : ∀ i, IsUnit (v i))
    (hP : PadicInt.toZModPow 3 (∏ i, B (b i) (b i)) = PadicInt.toZModPow 3 (∏ i, v i))
    (hS : PadicInt.toZModPow 3 (∑ i, B (b i) (b i)) = PadicInt.toZModPow 3 (∑ i, v i)) :
    ∃ j x y, PadicInt.toZModPow 3 (B x x) = PadicInt.toZModPow 3 (v j) ∧ IsUnit (B y y) ∧
      B x y = 0 := by
  have ho : ∀ i j, i ≠ j → B (b i) (b j) = 0 := iIsOrtho_def.mp hb
  have hr (i : Fin (m + 2)) := toZModPow_three_mul_self_of_isUnit (hbu i)
  have hq (j : Fin (m + 2)) := toZModPow_three_mul_self_of_isUnit (hv j)
  by_cases hA : ∃ i j, PadicInt.toZModPow 3 (B (b i) (b i)) = PadicInt.toZModPow 3 (v j)
  · -- Some `dᵢ` already has the residue of some `vⱼ`.
    obtain ⟨i, j, h⟩ := hA
    obtain ⟨k, hk⟩ := exists_ne i
    exact ⟨j, b i, b k, h, hbu k, ho i k hk.symm⟩
  by_cases hB5 : ∃ i j, PadicInt.toZModPow 3 (v j) = 5 * PadicInt.toZModPow 3 (B (b i) (b i))
  · -- Some `vⱼ` has the residue of `5 dᵢ`, which `b i + 2 b k` represents.
    obtain ⟨i, j, h⟩ := hB5
    obtain ⟨k, hk⟩ := exists_ne i
    obtain ⟨x, y, hx, hy, hxy⟩ := exists_toZModPow_three_apply_self_eq_five_mul hb.isSymm (hbu i)
      (hbu i) (hbu k) rfl (ho i k hk.symm) (ho i k hk.symm)
    exact ⟨j, x, y, hx.trans h.symm, hy, hxy⟩
  -- Otherwise every `dᵢ` lies in `{y, 5y}` and every `vⱼ` in `{-y, -5y}`, where `y = d₀`.
  push Not at hA hB5
  set y := PadicInt.toZModPow 3 (B (b 0) (b 0)) with hy
  have hdy (i : Fin (m + 2)) : PadicInt.toZModPow 3 (B (b i) (b i)) = y ∨
      PadicInt.toZModPow 3 (B (b i) (b i)) = 5 * y := by
    have key : ∀ a b c : ZMod (2 ^ 3), a * a = 1 → b * b = 1 → c * c = 1 → c ≠ a → c ≠ 5 * a →
        c ≠ b → c ≠ 5 * b → b = a ∨ b = 5 * a := by decide
    exact key _ _ _ (hr 0) (hr i) (hq 0) (hA 0 0).symm (hB5 0 0) (hA i 0).symm (hB5 i 0)
  have hvy (j : Fin (m + 2)) : PadicInt.toZModPow 3 (v j) = -y ∨
      PadicInt.toZModPow 3 (v j) = -(5 * y) := by
    have key : ∀ a c : ZMod (2 ^ 3), a * a = 1 → c * c = 1 → c ≠ a → c ≠ 5 * a →
        c = -a ∨ c = -(5 * a) := by decide
    exact key _ _ (hr 0) (hq j) (hA 0 j).symm (hB5 0 j)
  -- The invariants then force the rank to be at least four.
  have h4 : 4 ≤ m + 2 := ZMod.four_le_of_forall_eq_or_eq (by omega) (hr 0) hdy hvy
    (by simpa only [map_prod] using hP) (by simpa only [map_sum] using hS)
  obtain ⟨x, z, hx, hz, hxz⟩ := exists_toZModPow_three_apply_self_eq_of_four_le hb hbu h4 (hr 0) hdy
    (hvy 0)
  exact ⟨0, x, z, hx, hz, hxz⟩

/-- **Splitting off a unit vector.** Let `b` be a unit diagonal orthogonal basis of `B`, and let `x`
have unit self-pairing and be orthogonal to a vector with unit self-pairing. Then the orthogonal
complement of `x` has a unit diagonal orthogonal basis `t`, and adjoining `B x x` to the diagonal
of `t` gives the product and the sum of the diagonal of `b` modulo `8`. -/
private theorem exists_basis_orthogonal_span_singleton {B : BilinForm ℤ_[2] M} {m : ℕ}
    {b : Basis (Fin (m + 2)) ℤ_[2] M} (hb : B.iIsOrtho b) (hbu : ∀ i, IsUnit (B (b i) (b i)))
    {x y : M} (hx : IsUnit (B x x)) (hy : IsUnit (B y y)) (hxy : B x y = 0) :
    ∃ t : Basis (Fin (m + 1)) ℤ_[2] (B.orthogonal (ℤ_[2] ∙ x)),
      (B.restrict (B.orthogonal (ℤ_[2] ∙ x))).iIsOrtho t ∧ (∀ i, IsUnit (B (t i) (t i))) ∧
      PadicInt.toZModPow 3 (∏ i, B (b i) (b i)) =
        PadicInt.toZModPow 3 (B x x * ∏ i, B (t i) (t i)) ∧
      PadicInt.toZModPow 3 (∑ i, B (b i) (b i)) =
        PadicInt.toZModPow 3 (B x x + ∑ i, B (t i) (t i)) := by
  have hbdet : IsUnit (B.toMatrix b).det := hb.isUnit_det_toMatrix hbu
  obtain ⟨t, ht, htu⟩ :=
    hb.isSymm.exists_orthogonal_basis_isUnit_orthogonal_span_singleton b hbdet hx hy hxy
  -- Adjoin `x` to `t`, and compare the resulting basis with `b`.
  obtain ⟨c, hc, hcu, hcd⟩ := hb.isSymm.isRefl.exists_orthogonal_basis_isUnit_apply_self_eq_cons hx
    ht htu
  have hcP : ∏ i, B (c i) (c i) = B x x * ∏ i, B (t i) (t i) := by
    simp only [hcd, Fin.prod_cons]
  have hcS : ∑ i, B (c i) (c i) = B x x + ∑ i, B (t i) (t i) := by
    simp only [hcd, Fin.sum_cons]
  obtain ⟨hP, hS⟩ := (Equivalent.refl B).isSquare_prod_mul_prod_and_eight_dvd hb hc hbu
  rw [isSquare_mul_iff_toZModPow_three_eq (IsUnit.prod_univ_iff.mpr hbu)
    (IsUnit.prod_univ_iff.mpr hcu), hcP] at hP
  rw [eight_dvd_sub_iff_toZModPow_three_eq, hcS] at hS
  exact ⟨t, ht, htu, hP, hS⟩

/-- The inductive core of `LinearMap.BilinForm.iIsOrtho.exists_basis_iIsOrtho_apply_self_eq`,
with the invariants compared modulo `8`. -/
private theorem exists_basis_iIsOrtho_apply_self_eq_aux (n : ℕ) :
    ∀ {M : Type u} [AddCommGroup M] [Module ℤ_[2] M] {B : BilinForm ℤ_[2] M}
      (b : Basis (Fin n) ℤ_[2] M), B.iIsOrtho b → (∀ i, IsUnit (B (b i) (b i))) →
      ∀ v : Fin n → ℤ_[2], (∀ i, IsUnit (v i)) →
      PadicInt.toZModPow 3 (∏ i, B (b i) (b i)) = PadicInt.toZModPow 3 (∏ i, v i) →
      PadicInt.toZModPow 3 (∑ i, B (b i) (b i)) = PadicInt.toZModPow 3 (∑ i, v i) →
      ∃ c : Basis (Fin n) ℤ_[2] M, B.iIsOrtho c ∧ ∀ i, B (c i) (c i) = v i := by
  induction n with
  | zero =>
    intro M _ _ B b hb _ v _ _ _
    exact ⟨b, hb, fun i ↦ i.elim0⟩
  | succ n ih =>
  intro M _ _ B b hb hbu v hv hP hS
  rcases n with _ | m
  · -- In rank one, rescale the basis vector.
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one] at hP
    obtain ⟨s, hs, hsv⟩ := exists_eq_sq_mul_of_toZModPow_three_eq (hbu 0) (hv 0) hP
    refine ⟨b.unitsSMul fun _ ↦ hs.unit, iIsOrtho_def.mpr fun i j hij ↦ ?_, fun i ↦ ?_⟩
    · exact (hij (Fin.ext (by omega))).elim
    · obtain rfl : i = 0 := Fin.ext (by omega)
      simp only [Basis.unitsSMul_apply, Units.smul_def, IsUnit.unit_spec, map_smul,
        LinearMap.smul_apply, smul_eq_mul, hsv]
      ring
  -- Choose a vector representing some `vⱼ` with an odd complement, rescaled to represent `vⱼ`.
  obtain ⟨j, x, y, hxv, hyu, hxy⟩ := exists_toZModPow_three_apply_self_eq hb hbu hv hP hS
  have hxu : IsUnit (B x x) :=
    isUnit_of_toZModPow_three_mul_self (hxv ▸ toZModPow_three_mul_self_of_isUnit (hv j))
  obtain ⟨s, -, hsv⟩ := exists_eq_sq_mul_of_toZModPow_three_eq hxu (hv j) hxv
  set x' := s • x with hx'
  have hx'x' : B x' x' = v j := by
    simp only [hx', map_smul, LinearMap.smul_apply, smul_eq_mul, hsv]
    ring
  have hx'u : IsUnit (B x' x') := hx'x' ▸ hv j
  obtain ⟨t, ht, htu, htP, htS⟩ :=
    exists_basis_orthogonal_span_singleton hb hbu hx'u hyu (by simp [hx', hxy])
  rw [hx'x'] at htP htS
  -- Remove `vⱼ` from the target; the complement has the remaining invariants.
  let w : Fin (m + 2) → ℤ_[2] := v ∘ Equiv.swap 0 j
  let v' : Fin (m + 1) → ℤ_[2] := Fin.tail w
  have hvP : ∏ i, v i = v j * ∏ i, v' i := by
    rw [← Equiv.prod_comp (Equiv.swap 0 j), Fin.prod_univ_succ]
    simp [w, v', Fin.tail]
  have hvS : ∑ i, v i = v j + ∑ i, v' i := by
    rw [← Equiv.sum_comp (Equiv.swap 0 j), Fin.sum_univ_succ]
    simp [w, v', Fin.tail]
  have hcancel : ∀ a x z : ZMod (2 ^ 3), a * a = 1 → a * x = a * z → x = z := by decide
  have htP' : PadicInt.toZModPow 3 (∏ i, B (t i) (t i)) =
      PadicInt.toZModPow 3 (∏ i, v' i) := by
    refine hcancel _ _ _ (toZModPow_three_mul_self_of_isUnit (hv j)) ?_
    rw [← map_mul, ← map_mul, ← hvP, ← htP, hP]
  have htS' : PadicInt.toZModPow 3 (∑ i, B (t i) (t i)) =
      PadicInt.toZModPow 3 (∑ i, v' i) := by
    refine add_left_cancel (a := PadicInt.toZModPow 3 (v j)) ?_
    rw [← map_add, ← map_add, ← hvS, ← htS, hS]
  -- The inductive hypothesis realizes the rest of the target on the complement; adjoin `x'`.
  obtain ⟨t', ht', ht'v⟩ := ih (B := B.restrict (B.orthogonal (ℤ_[2] ∙ x'))) t ht htu
    v' (fun i ↦ hv _) htP' htS'
  obtain ⟨c, hc, -, hcd⟩ := hb.isSymm.isRefl.exists_orthogonal_basis_isUnit_apply_self_eq_cons hx'u
    ht' fun i ↦ ht'v i ▸ hv _
  have ht'w (i : Fin (m + 1)) : B (t' i) (t' i) = Fin.tail w i := by
    simpa only [restrict_apply, LinearMap.domRestrict_apply] using ht'v i
  have hcv (i : Fin (m + 2)) : B (c i) (c i) = w i := by
    rw [hcd, hx'x', ← Fin.cons_self_tail w]
    simp [ht'w, w]
  refine ⟨c.reindex (Equiv.swap 0 j), iIsOrtho_def.mpr fun i k hik ↦ ?_, fun i ↦ ?_⟩
  · simp only [Basis.reindex_apply, Equiv.symm_swap]
    exact iIsOrtho_def.mp hc _ _ ((Equiv.swap 0 j).injective.ne hik)
  · simp only [Basis.reindex_apply, Equiv.symm_swap, hcv, w, Function.comp_apply,
      Equiv.swap_apply_self]

/-- **Realizing a prescribed diagonal.** Let `B` be a bilinear form over `ℤ_[2]` with an orthogonal
basis `b` of size `n` whose self-pairings are units. If `v` is a family of `n` units whose product
differs from `∏ i, B (b i) (b i)` by a square and whose sum agrees with `∑ i, B (b i) (b i)` modulo
`8`, then `B` has an orthogonal basis with self-pairings exactly `v`. -/
theorem iIsOrtho.exists_basis_iIsOrtho_apply_self_eq {B : BilinForm ℤ_[2] M} {n : ℕ}
    {b : Basis (Fin n) ℤ_[2] M} (hb : B.iIsOrtho b) (hbu : ∀ i, IsUnit (B (b i) (b i)))
    {v : Fin n → ℤ_[2]} (hv : ∀ i, IsUnit (v i))
    (hsq : IsSquare ((∏ i, B (b i) (b i)) * ∏ i, v i))
    (h8 : (8 : ℤ_[2]) ∣ ∑ i, v i - ∑ i, B (b i) (b i)) :
    ∃ c : Basis (Fin n) ℤ_[2] M, B.iIsOrtho c ∧ ∀ i, B (c i) (c i) = v i :=
  exists_basis_iIsOrtho_apply_self_eq_aux n b hb hbu v hv
    ((isSquare_mul_iff_toZModPow_three_eq (IsUnit.prod_univ_iff.mpr hbu)
      (IsUnit.prod_univ_iff.mpr hv)).mp hsq)
    (eight_dvd_sub_iff_toZModPow_three_eq.mp h8)

/-- **Classification of forms with unit diagonal orthogonal bases over `ℤ_[2]`.** Let `B` and `C`
have orthogonal bases `b` and `c` of the same size whose self-pairings are units. Then `B` and `C`
are isometric exactly when the products of their self-pairings differ by a square and their sums
agree modulo `8`. -/
theorem iIsOrtho.equivalent_iff_isSquare_prod_mul_prod_and_eight_dvd {B : BilinForm ℤ_[2] M}
    {C : BilinForm ℤ_[2] N} {n : ℕ} {b : Basis (Fin n) ℤ_[2] M} {c : Basis (Fin n) ℤ_[2] N}
    (hb : B.iIsOrtho b) (hc : C.iIsOrtho c) (hbu : ∀ i, IsUnit (B (b i) (b i)))
    (hcu : ∀ i, IsUnit (C (c i) (c i))) :
    B.Equivalent C ↔ IsSquare ((∏ i, B (b i) (b i)) * ∏ i, C (c i) (c i)) ∧
      (8 : ℤ_[2]) ∣ ∑ i, C (c i) (c i) - ∑ i, B (b i) (b i) := by
  refine ⟨fun h ↦ h.isSquare_prod_mul_prod_and_eight_dvd hb hc hbu, fun ⟨hsq, h8⟩ ↦ ?_⟩
  obtain ⟨b', hb', hb'v⟩ := hb.exists_basis_iIsOrtho_apply_self_eq hbu hcu hsq h8
  refine ⟨b'.isometryEquivOfToMatrixEq c ?_⟩
  rw [hb'.toMatrix_eq_diagonal, hc.toMatrix_eq_diagonal]
  simp only [hb'v]

end Realization

/-! ### Odd unimodular forms -/

section Odd

variable {M N : Type*} [AddCommGroup M] [Module ℤ_[2] M] [AddCommGroup N] [Module ℤ_[2] N]

/-- **Classification of odd unimodular forms over `ℤ_[2]`.** Let `B` and `C` be symmetric forms
over `ℤ_[2]` with unit Gram determinants in bases of the same size, each representing a unit, and
let `w` and `w'` be characteristic vectors for `B` and `C`. Then `B` and `C` are isometric exactly
when the product of their Gram determinants is a square and `B w w ≡ C w' w'` modulo `8`.

The second condition says that the oddities of `B` and `C` agree. -/
theorem IsSymm.equivalent_iff_isSquare_det_mul_det_and_eight_dvd_of_odd {B : BilinForm ℤ_[2] M}
    {C : BilinForm ℤ_[2] N} (hB : B.IsSymm) (hC : C.IsSymm) {n : ℕ} (b : Basis (Fin n) ℤ_[2] M)
    (c : Basis (Fin n) ℤ_[2] N) (hBdet : IsUnit (B.toMatrix b).det)
    (hCdet : IsUnit (C.toMatrix c).det) (hBodd : ∃ x, IsUnit (B x x))
    (hCodd : ∃ y, IsUnit (C y y)) {w : M} {w' : N} (hw : B.IsCharacteristic w)
    (hw' : C.IsCharacteristic w') :
    B.Equivalent C ↔ IsSquare ((B.toMatrix b).det * (C.toMatrix c).det) ∧
      (8 : ℤ_[2]) ∣ C w' w' - B w w := by
  obtain ⟨b', hb', hb'u⟩ := hB.exists_orthogonal_basis_isUnit_of_exists_isUnit_apply_self b hBdet
    hBodd
  obtain ⟨c', hc', hc'u⟩ := hC.exists_orthogonal_basis_isUnit_of_exists_isUnit_apply_self c hCdet
    hCodd
  have : Free ℤ_[2] M := .of_basis b
  have : Free ℤ_[2] N := .of_basis c
  have : B.IsPerfPair := b.isPerfPair_of_isUnit_det B hBdet
  have : C.IsPerfPair := c.isPerfPair_of_isUnit_det C hCdet
  have hb'det : (B.toMatrix b').det = ∏ i, B (b' i) (b' i) := hb'.det_toMatrix
  have hc'det : (C.toMatrix c').det = ∏ i, C (c' i) (c' i) := hc'.det_toMatrix
  have hb'P := IsUnit.prod_univ_iff.mpr hb'u
  have hc'P := IsUnit.prod_univ_iff.mpr hc'u
  -- Compare the determinants in `b` and `b'`, and the characteristic norms with the traces.
  have hBsq := (isSquare_mul_iff_toZModPow_three_eq hBdet hb'P).mp
    (hb'det ▸ (Equivalent.refl B).isSquare_det_mul_det b b')
  have hCsq := (isSquare_mul_iff_toZModPow_three_eq hCdet hc'P).mp
    (hc'det ▸ (Equivalent.refl C).isSquare_det_mul_det c c')
  have hBw := eight_dvd_sub_iff_toZModPow_three_eq.mp <| hw.eight_dvd_apply_self_sub_apply_self hB
    (hb'.isCharacteristic_sum PadicInt.two_dvd_sq_sub_self)
  have hCw := eight_dvd_sub_iff_toZModPow_three_eq.mp <| hw'.eight_dvd_apply_self_sub_apply_self hC
    (hc'.isCharacteristic_sum PadicInt.two_dvd_sq_sub_self)
  rw [hb'.apply_sum_sum] at hBw
  rw [hc'.apply_sum_sum] at hCw
  rw [hb'.equivalent_iff_isSquare_prod_mul_prod_and_eight_dvd hc' hb'u hc'u,
    isSquare_mul_iff_toZModPow_three_eq hBdet hCdet,
    isSquare_mul_iff_toZModPow_three_eq hb'P hc'P, eight_dvd_sub_iff_toZModPow_three_eq,
    eight_dvd_sub_iff_toZModPow_three_eq, ← hBsq, ← hCsq, ← hBw, ← hCw]

end Odd

end LinearMap.BilinForm
