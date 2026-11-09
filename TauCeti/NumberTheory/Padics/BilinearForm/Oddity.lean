/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import TauCeti.LinearAlgebra.BilinearForm.Characteristic
import TauCeti.LinearAlgebra.BilinearForm.LinearIndependent
import TauCeti.LinearAlgebra.BilinearForm.Modular
import TauCeti.LinearAlgebra.Matrix.BilinearForm
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# The oddity of a block with a unary summand over `ℤ_[2]`

Let `B` be a symmetric form on a `ℤ_[2]`-module, and let `P` be the span of a vector `x` with
`B x x = 2 ^ k a`, `a` a unit, and of a family `t` orthogonal to `x` whose Gram matrix is `2 ^ k G`
with `G` of unit determinant. Then `B` is `2 ^ k` times a unimodular form `C` on `P`, and the
*oddity* of `C`, the self-pairing `C w w` of a characteristic vector `w` modulo `8`
(`LinearMap.BilinForm.IsCharacteristic.eight_dvd_apply_self_sub_apply_self`), is `a` plus a
contribution of `t` alone (`LinearMap.BilinForm.IsSymm.two_pow_mul_eight_dvd_of_eq_span`).

So replacing `x` by another vector `x'` orthogonal to `t`, with `B x' x' = 2 ^ k a'`, changes the
oddity by `a' - a` modulo `8` (`LinearMap.BilinForm.IsSymm.eight_dvd_sub_sub_of_eq_span`). This is
how the oddity of a constituent of type I of a dyadic Jordan splitting changes when a rank-one
block of it is exchanged, as in sign walking and oddity fusion.

## Main results

* `LinearMap.BilinForm.IsSymm.two_pow_mul_eight_dvd_of_eq_span`: the oddity of `C` is `a` plus a
  term depending only on `t` and its Gram matrix, modulo `8`.
* `LinearMap.BilinForm.IsSymm.eight_dvd_sub_sub_of_eq_span`: exchanging `x` for `x'` changes the
  oddity by `a' - a` modulo `8`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
* O. T. O'Meara, *Introduction to Quadratic Forms*, §93.
-/

public section

open Module
open LinearMap (BilinForm)
open scoped Matrix

namespace LinearMap.BilinForm

variable {M : Type*} [AddCommGroup M] [Module ℤ_[2] M] {B : BilinForm ℤ_[2] M}

/-- The characteristic vectors of `P = ⟨x, t⟩`, with `B x x = 2 ^ k a`, `x` orthogonal to `t` and
`B` equal to `2 ^ k C` on `P`, have self-pairings `C w w ≡ a + 2 ^ (-k) B w₀ w₀ (mod 8)` for a
vector `w₀` of the span of `t` that depends only on `t` and its Gram matrix. -/
theorem IsSymm.two_pow_mul_eight_dvd_of_eq_span (hB : B.IsSymm) {k m : ℕ} {x : M} {a : ℤ_[2]}
    {t : Fin m → M} {G : Matrix (Fin m) (Fin m) ℤ_[2]} (hx : B x x = 2 ^ k * a)
    (hG : ∀ i j, B (t i) (t j) = 2 ^ k * G i j) (hxt : ∀ j, B x (t j) = 0) (hau : IsUnit a)
    (hGu : IsUnit G.det) {P : Submodule ℤ_[2] M}
    (hP : P = Submodule.span ℤ_[2] (Set.range (Sum.elim ![x] t)))
    {C : BilinForm ℤ_[2] P} (hC : (2 : ℤ_[2]) ^ k • C = B.restrict P) {w : P}
    (hw : C.IsCharacteristic w) :
    2 ^ k * 8 ∣ 2 ^ k * C w w - 2 ^ k * a -
      B (∑ j, ((fun j ↦ G j j) ᵥ* G⁻¹) j • t j) (∑ j, ((fun j ↦ G j j) ᵥ* G⁻¹) j • t j) := by
  classical
  have h2k : (2 : ℤ_[2]) ^ k ∈ nonZeroDivisors ℤ_[2] :=
    mem_nonZeroDivisors_of_ne_zero (pow_ne_zero k two_ne_zero)
  have hcan : ∀ r s : ℤ_[2], 2 ^ k * r = 2 ^ k * s → r = s := fun r s ↦
    (mul_cancel_left_mem_nonZeroDivisors h2k).mp
  -- `w₀ = ∑ c j • t j` pairs with each `t j` as `t j` pairs with itself.
  set c : Fin m → ℤ_[2] := (fun j ↦ G j j) ᵥ* G⁻¹
  have hcG : c ᵥ* G = fun j ↦ G j j := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hGu, Matrix.vecMul_one]
  set w₀ : M := ∑ j, c j • t j
  have hw₀t (l : Fin m) : B w₀ (t l) = 2 ^ k * G l l := by
    have := congrFun hcG l
    simp only [Matrix.vecMul, dotProduct] at this
    simp [w₀, map_sum, hG, ← this, Finset.mul_sum, mul_left_comm]
  have hxw₀ : B x w₀ = 0 := by simp [w₀, map_sum, hxt]
  -- A basis of `P` adapted to `x` and `t`.
  have hu := hB.isRefl.apply_sum_elim_eq_mul_fromBlocks (A := !![a]) (G := G) (v := ![x]) (t := t)
    (fun i j ↦ by fin_cases i; fin_cases j; simpa using hx) hG
    (fun i j ↦ by fin_cases i; simpa using hxt j)
  have hdet : IsUnit (Matrix.fromBlocks !![a] 0 0 G).det := by
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_fin_one_of]
    exact hau.mul hGu
  have hli := linearIndependent_of_isUnit_det h2k hu hdet
  let b : Basis (Fin 1 ⊕ Fin m) ℤ_[2] P := (Basis.span hli).map (LinearEquiv.ofEq _ _ hP.symm)
  have hb (i : Fin 1 ⊕ Fin m) : (b i : M) = Sum.elim ![x] t i := by simp [b, Basis.span_apply]
  have hBC (y z : P) : 2 ^ k * C y z = B y z := by
    simpa using LinearMap.congr_fun₂ hC y z
  have hCs : C.IsSymm := ⟨fun y z ↦ hcan _ _ (by rw [hBC, hBC, hB.eq])⟩
  have : Module.Free ℤ_[2] P := .of_basis b
  have : C.IsPerfPair := (hP ▸ isModular_restrict_span_range h2k hu hdet).isPerfPair_of_smul_eq
    h2k hC
  -- `x + w₀` is a characteristic vector, of self-pairing `2 ^ k a + B w₀ w₀`.
  have hxP : x ∈ P := hP ▸ Submodule.subset_span ⟨Sum.inl 0, rfl⟩
  have hw₀P : w₀ ∈ P := Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _
    (hP ▸ Submodule.subset_span ⟨Sum.inr j, rfl⟩)
  let w₁ : P := ⟨x + w₀, P.add_mem hxP hw₀P⟩
  have hw₁ : C.IsCharacteristic w₁ := by
    refine (hCs.isCharacteristic_iff_forall_basis PadicInt.two_dvd_sq_sub_self b).mpr fun i ↦ ?_
    have : C w₁ (b i) - C (b i) (b i) = 0 := hcan _ _ (by
      rw [mul_sub, hBC, hBC, mul_zero]
      rcases i with i | j
      · fin_cases i
        simp [w₁, hb, hB.eq w₀ x, hxw₀]
      · simp [w₁, hb, hxt, hw₀t, hG])
    rw [this]
    exact dvd_zero 2
  have hw₁w₁ : 2 ^ k * C w₁ w₁ = 2 ^ k * a + B w₀ w₀ := by
    rw [hBC]
    simp [w₁, hx, hxw₀, hB.eq w₀ x]
  obtain ⟨r, hr⟩ := hw₁.eight_dvd_apply_self_sub_apply_self hCs hw
  exact ⟨r, by linear_combination 2 ^ k * hr + hw₁w₁⟩

/-- Replacing `x` by `x'` in `P = ⟨x, t⟩` changes the oddity of the unimodular rescaling by
`a' - a` modulo `8`, where `B x x = 2 ^ k a` and `B x' x' = 2 ^ k a'`. -/
theorem IsSymm.eight_dvd_sub_sub_of_eq_span (hB : B.IsSymm) {k m : ℕ} {x x' : M} {a a' : ℤ_[2]}
    {t : Fin m → M} {G : Matrix (Fin m) (Fin m) ℤ_[2]} (hx : B x x = 2 ^ k * a)
    (hx' : B x' x' = 2 ^ k * a') (hG : ∀ i j, B (t i) (t j) = 2 ^ k * G i j)
    (hxt : ∀ j, B x (t j) = 0) (hx't : ∀ j, B x' (t j) = 0) (hau : IsUnit a) (ha'u : IsUnit a')
    (hGu : IsUnit G.det) {P P' : Submodule ℤ_[2] M}
    (hP : P = Submodule.span ℤ_[2] (Set.range (Sum.elim ![x] t)))
    (hP' : P' = Submodule.span ℤ_[2] (Set.range (Sum.elim ![x'] t)))
    {C : BilinForm ℤ_[2] P} {C' : BilinForm ℤ_[2] P'} (hC : (2 : ℤ_[2]) ^ k • C = B.restrict P)
    (hC' : (2 : ℤ_[2]) ^ k • C' = B.restrict P') {w : P} {w' : P'} (hw : C.IsCharacteristic w)
    (hw' : C'.IsCharacteristic w') : (8 : ℤ_[2]) ∣ C' w' w' - C w w - (a' - a) := by
  obtain ⟨r, hr⟩ := hB.two_pow_mul_eight_dvd_of_eq_span hx hG hxt hau hGu hP hC hw
  obtain ⟨r', hr'⟩ := hB.two_pow_mul_eight_dvd_of_eq_span hx' hG hx't ha'u hGu hP' hC' hw'
  refine ⟨r' - r, (mul_cancel_left_mem_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero k (two_ne_zero (α := ℤ_[2]))))).mp ?_⟩
  linear_combination hr' - hr

end LinearMap.BilinForm
