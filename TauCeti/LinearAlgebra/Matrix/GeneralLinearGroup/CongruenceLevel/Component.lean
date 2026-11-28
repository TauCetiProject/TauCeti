/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.GL2K0`, the congruence level of `GL₂(A)` compared with the principal component.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.CongruenceLevel
-- `TauCeti.diagGL`, the diagonal elements of `GL₂(K)` conjugating one component into another.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
-- Fractional ideals and their inverses give the entry conditions.
public import Mathlib.RingTheory.FractionalIdeal.Inverse
-- `GL₂(K)` acts on `K²` through `Matrix.mulVec`, and so on its `A`-submodules.
public import Mathlib.LinearAlgebra.Matrix.Action
public import Mathlib.Algebra.Module.Submodule.Pointwise
-- Non-public: translation by a group element preserves inclusions of submodules.
import TauCeti.Algebra.Module.Submodule.Pointwise
-- Non-public: closure of fractional ideals under `+` and `-`, and their lack of zero divisors.
import TauCeti.RingTheory.FractionalIdeal.Basic

/-!
# The component groups `Γ₀(𝔫, 𝔞)` of `GL₂` over a fraction field

Let `A` be a domain with fraction field `K`, let `𝔫` be an ideal of `A` and `𝔞` a fractional
ideal. The **component group**

```text
Γ₀(𝔫, 𝔞) = {(a b; c d) ∈ GL₂(K) : a, d ∈ A, b ∈ 𝔞⁻¹, c ∈ 𝔞𝔫, det ∈ Aˣ}
```

(`TauCeti.Gamma0Component 𝔫 𝔞`) is the stabilizer in `GL₂(K)` of the pair of column lattices
`A ⊕ 𝔞 ⊇ A ⊕ 𝔞𝔫` when `𝔞` is invertible. For `𝔞 = A` it is the image of the congruence group
`Γ₀(𝔫) = {γ ∈ GL₂(A) : γ₂₁ ∈ 𝔫}`. For `K` an imaginary quadratic field and `A` its ring of
integers, the groups `Γ₀(𝔫, 𝔞)` for representatives `𝔞` of the ideal classes are the level-`𝔫`
Bianchi groups, one for each component of the level-`𝔫` Bianchi orbifold when the class number
exceeds one. Conjugation by `diag(1, x)` identifies `Γ₀(𝔫, 𝔞)` with `Γ₀(𝔫, x𝔞)`, so up to
conjugacy the group depends only on the class of `𝔞`.

## Main definitions

* `TauCeti.Gamma0Component 𝔫 𝔞`: the component group `Γ₀(𝔫, 𝔞) ≤ GL₂(K)`.
* `TauCeti.Gamma0Component.lattice 𝔞`: the column lattice `A ⊕ 𝔞` of `K²`.

## Main results

* `TauCeti.Gamma0Component.mem_iff`: the entry conditions defining `Γ₀(𝔫, 𝔞)`.
* `TauCeti.Gamma0Component.map_GL2K0`: `Γ₀(𝔫, A)` is the image of `Γ₀(𝔫) = K₀(𝔫) ≤ GL₂(A)`.
* `TauCeti.Gamma0Component.map_conj_diagGL`: conjugation by `diag(1, x)` carries `Γ₀(𝔫, 𝔞)`
  onto `Γ₀(𝔫, x𝔞)`.
* `TauCeti.Gamma0Component.stabilizer_lattice_inf_stabilizer_lattice`: for invertible `𝔞`,
  `Γ₀(𝔫, 𝔞)` is the stabilizer of the pair `(A ⊕ 𝔞, A ⊕ 𝔞𝔫)`.

## References

* J. Bygott, *Modular forms and modular symbols over imaginary quadratic fields*, PhD thesis,
  University of Exeter, 1998.
* M. P. Lingham, *Modular forms and elliptic curves over imaginary quadratic fields*, PhD thesis,
  University of Nottingham, 2005.
-/

public section

open Matrix FractionalIdeal
open scoped Pointwise nonZeroDivisors

namespace TauCeti

variable {A : Type*} [CommRing A] {K : Type*} [Field K] [Algebra A K]

/-- `𝔞𝔫 ⊆ 𝔞` for an integral ideal `𝔫`. -/
private theorem mem_of_mem_mul_coeIdeal {𝔫 : Ideal A} {𝔞 : FractionalIdeal A⁰ K} {y : K}
    (hy : y ∈ 𝔞 * 𝔫) : y ∈ 𝔞 :=
  mul_le_of_le_one_right' coeIdeal_le_one hy

namespace Gamma0Component

/-! ### The column lattices `A ⊕ 𝔞` -/

/-- The **column lattice `A ⊕ 𝔞`** of `K²`: the vectors whose first coordinate lies in `A` and
whose second lies in `𝔞`. -/
def lattice (𝔞 : FractionalIdeal A⁰ K) : Submodule A (Fin 2 → K) :=
  Submodule.pi Set.univ ![((1 : FractionalIdeal A⁰ K) : Submodule A K), (𝔞 : Submodule A K)]

@[simp]
theorem mem_lattice {𝔞 : FractionalIdeal A⁰ K} {v : Fin 2 → K} :
    v ∈ lattice 𝔞 ↔ v 0 ∈ (1 : FractionalIdeal A⁰ K) ∧ v 1 ∈ 𝔞 := by
  simp only [lattice, Submodule.mem_pi, Set.mem_univ, true_implies, Fin.forall_fin_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, mem_coeToSubmodule]

/-- A matrix `(a b; c d)` with `a, d ∈ A`, `b 𝔟 ⊆ A` and `c ∈ 𝔟` carries `A ⊕ 𝔟` into itself. -/
private theorem smul_lattice_le {γ : GL (Fin 2) K} {𝔟 : FractionalIdeal A⁰ K}
    (h00 : γ 0 0 ∈ (1 : FractionalIdeal A⁰ K)) (h11 : γ 1 1 ∈ (1 : FractionalIdeal A⁰ K))
    (h01 : ∀ y ∈ 𝔟, γ 0 1 * y ∈ (1 : FractionalIdeal A⁰ K)) (h10 : γ 1 0 ∈ 𝔟) :
    γ • lattice 𝔟 ≤ lattice 𝔟 := by
  intro w hw
  obtain ⟨v, hv, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hw
  rw [mem_lattice] at hv ⊢
  rw [Units.smul_def, Matrix.smul_eq_mulVec]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact ⟨FractionalIdeal.add_mem (by simpa using mul_mem_mul h00 hv.1) (h01 _ hv.2),
    FractionalIdeal.add_mem (by simpa using mul_mem_mul h10 hv.1)
      (by simpa using mul_mem_mul h11 hv.2)⟩

/-- A matrix carrying `A ⊕ 𝔟` into itself has `a ∈ A`, `c ∈ 𝔟`, `b 𝔟 ⊆ A` and `d 𝔟 ⊆ 𝔟`. -/
private theorem entries_of_smul_lattice_le {γ : GL (Fin 2) K} {𝔟 : FractionalIdeal A⁰ K}
    (h : γ • lattice 𝔟 ≤ lattice 𝔟) :
    γ 0 0 ∈ (1 : FractionalIdeal A⁰ K) ∧ γ 1 0 ∈ 𝔟 ∧
      ∀ y ∈ 𝔟, γ 0 1 * y ∈ (1 : FractionalIdeal A⁰ K) ∧ γ 1 1 * y ∈ 𝔟 := by
  have key (v : Fin 2 → K) (hv : v ∈ lattice 𝔟) :
      ((γ : Matrix (Fin 2) (Fin 2) K) *ᵥ v) 0 ∈ (1 : FractionalIdeal A⁰ K) ∧
        ((γ : Matrix (Fin 2) (Fin 2) K) *ᵥ v) 1 ∈ 𝔟 :=
    mem_lattice.mp (h (Submodule.smul_mem_pointwise_smul v γ _ hv))
  have h₀ := key ![1, 0]
    (mem_lattice.mpr ⟨by simpa using one_mem_one A⁰, by simp [FractionalIdeal.zero_mem]⟩)
  refine ⟨by simpa [Matrix.mulVec, dotProduct] using h₀.1,
    by simpa [Matrix.mulVec, dotProduct] using h₀.2, fun y hy ↦ ?_⟩
  have h₁ := key ![0, y] (mem_lattice.mpr ⟨by simp [FractionalIdeal.zero_mem], by simpa using hy⟩)
  exact ⟨by simpa [Matrix.mulVec, dotProduct] using h₁.1,
    by simpa [Matrix.mulVec, dotProduct] using h₁.2⟩

end Gamma0Component

variable [IsDomain A] [IsFractionRing A K]

/-- The product of an element of `𝔞⁻¹` and an element of `𝔞` is integral. -/
private theorem mul_mem_one_of_mem_inv {𝔞 : FractionalIdeal A⁰ K} {x y : K} (hx : x ∈ 𝔞⁻¹)
    (hy : y ∈ 𝔞) : x * y ∈ (1 : FractionalIdeal A⁰ K) := by
  have h : 𝔞⁻¹ * 𝔞 ≤ 1 := by
    rw [mul_comm, inv_eq]
    exact mul_one_div_le_one
  exact h (mul_mem_mul hx hy)

variable (𝔫 : Ideal A) (𝔞 : FractionalIdeal A⁰ K)

/-- The **component group** `Γ₀(𝔫, 𝔞) ≤ GL₂(K)` of level `𝔫` and component `𝔞`: the invertible
matrices `(a b; c d)` with `a, d ∈ A`, `b ∈ 𝔞⁻¹`, `c ∈ 𝔞𝔫` and determinant a unit of `A`. For
invertible `𝔞` it is the stabilizer of the lattice pair `A ⊕ 𝔞 ⊇ A ⊕ 𝔞𝔫`
(`TauCeti.Gamma0Component.stabilizer_lattice_inf_stabilizer_lattice`). For `𝔞 = 0` the inverse
`𝔞⁻¹` is Mathlib's junk value `0`, and the group consists of the diagonal matrices with entries
in `Aˣ`. -/
def Gamma0Component : Subgroup (GL (Fin 2) K) where
  carrier := {γ | γ 0 0 ∈ (1 : FractionalIdeal A⁰ K) ∧ γ 1 1 ∈ (1 : FractionalIdeal A⁰ K) ∧
    γ 0 1 ∈ 𝔞⁻¹ ∧ γ 1 0 ∈ 𝔞 * 𝔫 ∧ ∃ u : Aˣ, algebraMap A K u = (γ : Matrix (Fin 2) (Fin 2) K).det}
  one_mem' := ⟨by simp, by simp, by simp [FractionalIdeal.zero_mem],
    by simp [FractionalIdeal.zero_mem], 1, by simp⟩
  mul_mem' {γ δ} hγ hδ := by
    obtain ⟨g00, g11, g01, g10, u, hu⟩ := hγ
    obtain ⟨d00, d11, d01, d10, v, hv⟩ := hδ
    have m1 {x y : K} (hx : x ∈ (1 : FractionalIdeal A⁰ K)) {I : FractionalIdeal A⁰ K}
        (hy : y ∈ I) : x * y ∈ I := by
      simpa using mul_mem_mul hx hy
    have m1' {x y : K} {I : FractionalIdeal A⁰ K} (hx : x ∈ I)
        (hy : y ∈ (1 : FractionalIdeal A⁰ K)) : x * y ∈ I := by
      simpa using mul_mem_mul hx hy
    simp only [Set.mem_ofPred_eq, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.det_mul]
    refine ⟨FractionalIdeal.add_mem (m1 g00 d00)
        (mul_mem_one_of_mem_inv g01 (mem_of_mem_mul_coeIdeal d10)),
      FractionalIdeal.add_mem (mul_comm (δ 0 1) (γ 1 0) ▸
        mul_mem_one_of_mem_inv d01 (mem_of_mem_mul_coeIdeal g10)) (m1 g11 d11),
      FractionalIdeal.add_mem (m1 g00 d01) (m1' g01 d11),
      FractionalIdeal.add_mem (m1' g10 d00) (m1 g11 d10), u * v, ?_⟩
    rw [Units.val_mul, map_mul, hu, hv]
  inv_mem' {γ} hγ := by
    obtain ⟨g00, g11, g01, g10, u, hu⟩ := hγ
    -- `γ⁻¹ = (det γ)⁻¹ · adj γ`, and `(det γ)⁻¹` is the image of the unit `u⁻¹`.
    have hdet : ((γ : Matrix (Fin 2) (Fin 2) K).det)⁻¹ = algebraMap A K ↑u⁻¹ := by
      rw [← hu, map_units_inv]
    have m {I : FractionalIdeal A⁰ K} {y : K} (hy : y ∈ I) : algebraMap A K ↑u⁻¹ * y ∈ I := by
      have := mul_mem_mul ((mem_one_iff A⁰).mpr ⟨(↑u⁻¹ : A), rfl⟩) hy
      rwa [one_mul] at this
    refine ⟨?_, ?_, ?_, ?_, u⁻¹, ?_⟩
    rotate_right
    · rw [Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hdet]
    all_goals simp only [Matrix.coe_units_inv, Matrix.inv_def, Matrix.smul_apply,
      Matrix.adjugate_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul,
      Ring.inverse_eq_inv', hdet]
    exacts [m g11, m g00, m (FractionalIdeal.neg_mem g01), m (FractionalIdeal.neg_mem g10)]

namespace Gamma0Component

variable {𝔫 𝔞}

/-- **Membership in `Γ₀(𝔫, 𝔞)`**: `a, d ∈ A`, `b ∈ 𝔞⁻¹`, `c ∈ 𝔞𝔫`, and the determinant is the
image of a unit of `A`. -/
@[simp]
theorem mem_iff {γ : GL (Fin 2) K} :
    γ ∈ Gamma0Component 𝔫 𝔞 ↔ γ 0 0 ∈ (1 : FractionalIdeal A⁰ K) ∧
      γ 1 1 ∈ (1 : FractionalIdeal A⁰ K) ∧ γ 0 1 ∈ 𝔞⁻¹ ∧ γ 1 0 ∈ 𝔞 * 𝔫 ∧
      ∃ u : Aˣ, algebraMap A K u = (γ : Matrix (Fin 2) (Fin 2) K).det :=
  Iff.rfl

variable (𝔫)

/-- **The principal component is `Γ₀(𝔫)`**: `Γ₀(𝔫, A)` is the image of the congruence level
`K₀(𝔫) = {γ ∈ GL₂(A) : γ₂₁ ∈ 𝔫}` under `GL₂(A) → GL₂(K)`. -/
theorem map_GL2K0 :
    (GL2K0 𝔫).map (GeneralLinearGroup.map (algebraMap A K)) = Gamma0Component 𝔫 1 := by
  ext γ
  simp only [Subgroup.mem_map, mem_iff, one_mul, inv_eq, FractionalIdeal.div_one, mem_one_iff,
    mem_coeIdeal]
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, GL2K0.mem_iff.mp hg, rfl⟩,
      GeneralLinearGroup.det g, ?_⟩
    simp [GeneralLinearGroup.map, RingHom.map_det]
  · rintro ⟨h00, h11, h01, ⟨c, hc, h10⟩, u, hu⟩
    -- Lift the four integral entries to a matrix `M` over `A`.
    have h : ∀ i j, ∃ r : A, algebraMap A K r = γ i j := by
      simp only [Fin.forall_fin_two]
      exact ⟨⟨h00, h01⟩, ⟨_, h10⟩, h11⟩
    choose M hM using h
    have hMγ : (Matrix.of M).map (algebraMap A K) = γ := by
      ext i j
      exact hM i j
    have hdet : (Matrix.of M).det = u := by
      apply IsFractionRing.injective A K
      rw [hu, RingHom.map_det]
      exact congrArg Matrix.det hMγ
    obtain ⟨g, hg⟩ := (Matrix.isUnit_iff_isUnit_det _).mpr (hdet ▸ u.isUnit)
    refine ⟨g, ?_, Units.ext (by simpa [GeneralLinearGroup.map, hg] using hMγ)⟩
    rw [GL2K0.mem_iff, hg, Matrix.of_apply,
      IsFractionRing.injective A K ((hM 1 0).trans h10.symm)]
    exact hc

/-- Conjugation by `diag(1, x)` multiplies the upper-right entry by `x⁻¹` and the lower-left entry
by `x`, and so carries `Γ₀(𝔫, 𝔞)` into `Γ₀(𝔫, x𝔞)`. -/
theorem diagGL_mul_mul_inv_mem_iff (x : Kˣ) {γ : GL (Fin 2) K} :
    diagGL ![1, x] * γ * (diagGL ![1, x])⁻¹ ∈
        Gamma0Component 𝔫 (spanSingleton A⁰ (x : K) * 𝔞) ↔
      γ ∈ Gamma0Component 𝔫 𝔞 := by
  have hx : (x : K) ≠ 0 := x.ne_zero
  have h11 : (x : K) * γ 1 1 * ((x⁻¹ : Kˣ) : K) = γ 1 1 := by
    rw [mul_right_comm, Units.mul_inv, one_mul]
  rw [mem_iff, mem_iff]
  simp only [diagGL_mul_mul_inv_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Units.val_one, inv_one, one_mul, mul_one, h11, Units.val_mul, Matrix.det_units_conj]
  refine and_congr Iff.rfl <| and_congr Iff.rfl <| and_congr ?_ (and_congr ?_ Iff.rfl)
  · -- The upper-right entry: `b x⁻¹ ∈ (x𝔞)⁻¹ ↔ b ∈ 𝔞⁻¹`.
    rcases eq_or_ne 𝔞 0 with rfl | h𝔞
    · simp [inv_zero', mem_zero_iff, hx]
    have hx𝔞 : spanSingleton A⁰ (x : K) * 𝔞 ≠ 0 :=
      mul_ne_zero (spanSingleton_ne_zero_iff.mpr hx) h𝔞
    simp only [mem_inv_iff hx𝔞, mem_inv_iff h𝔞, mem_singleton_mul, forall_exists_index,
      and_imp]
    refine ⟨fun h y hy ↦ ?_, fun h z y hy hz ↦ ?_⟩
    · simpa [mul_assoc, hx] using h _ y hy rfl
    · rw [hz, mul_assoc, ← mul_assoc ((x⁻¹ : Kˣ) : K), Units.inv_mul, one_mul]
      exact h y hy
  · -- The lower-left entry: `x c ∈ x𝔞𝔫 ↔ c ∈ 𝔞𝔫`.
    rw [mul_assoc, mem_singleton_mul]
    exact ⟨fun ⟨z, hz, h⟩ ↦ mul_left_cancel₀ hx h ▸ hz, fun h ↦ ⟨_, h, rfl⟩⟩

/-- **Conjugation between components**: conjugation by `diag(1, x)` carries `Γ₀(𝔫, 𝔞)` onto
`Γ₀(𝔫, x𝔞)`. In particular the conjugacy class of `Γ₀(𝔫, 𝔞)` in `GL₂(K)` depends only on the
class of `𝔞` modulo principal fractional ideals. -/
theorem map_conj_diagGL (x : Kˣ) :
    (Gamma0Component 𝔫 𝔞).map (MulAut.conj (diagGL ![1, x])).toMonoidHom =
      Gamma0Component 𝔫 (spanSingleton A⁰ (x : K) * 𝔞) := by
  ext γ
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨δ, hδ, rfl⟩
    exact (diagGL_mul_mul_inv_mem_iff 𝔫 x).mpr hδ
  · intro hγ
    refine ⟨(diagGL ![1, x])⁻¹ * γ * diagGL ![1, x], ?_, by group⟩
    rw [← diagGL_mul_mul_inv_mem_iff 𝔫 x]
    have h : diagGL ![1, x] * ((diagGL ![1, x])⁻¹ * γ * diagGL ![1, x]) * (diagGL ![1, x])⁻¹ =
        γ := by group
    rwa [h]

/-! ### `Γ₀(𝔫, 𝔞)` as the stabilizer of a lattice pair -/

/-- The entries of an element of the stabilizer of `(A ⊕ 𝔞, A ⊕ 𝔞𝔫)` satisfy the conditions
defining `Γ₀(𝔫, 𝔞)`, for invertible `𝔞`. -/
private theorem entries_of_mem_stabilizer (h𝔞 : IsUnit 𝔞) {γ : GL (Fin 2) K}
    (hL : γ • lattice 𝔞 = lattice 𝔞)
    (hM : γ • lattice (𝔞 * 𝔫 : FractionalIdeal A⁰ K) = lattice (𝔞 * 𝔫 : FractionalIdeal A⁰ K)) :
    γ 0 0 ∈ (1 : FractionalIdeal A⁰ K) ∧ γ 1 1 ∈ (1 : FractionalIdeal A⁰ K) ∧
      γ 0 1 ∈ 𝔞⁻¹ ∧ γ 1 0 ∈ 𝔞 * 𝔫 := by
  obtain ⟨h00, -, hL'⟩ := entries_of_smul_lattice_le hL.le
  obtain ⟨-, h10, -⟩ := entries_of_smul_lattice_le hM.le
  refine ⟨h00, ?_, (mem_inv_iff h𝔞.ne_zero).mpr fun y hy ↦ (hL' y hy).1, h10⟩
  -- `d 𝔞 ⊆ 𝔞` forces `d ∈ 𝔞 𝔞⁻¹ = A`, since `𝔞` is invertible.
  have h𝔞' : 𝔞 * 𝔞⁻¹ = 1 := (mul_inv_cancel_iff_isUnit K).mpr h𝔞
  have hd : spanSingleton A⁰ (γ 1 1) * 𝔞 ≤ 𝔞 := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := mem_singleton_mul.mp hz
    exact (hL' y hy).2
  have : spanSingleton A⁰ (γ 1 1) ≤ 1 :=
    calc spanSingleton A⁰ (γ 1 1) = spanSingleton A⁰ (γ 1 1) * 𝔞 * 𝔞⁻¹ := by
          rw [mul_assoc, h𝔞', mul_one]
      _ ≤ 𝔞 * 𝔞⁻¹ := mul_le_mul_left hd _
      _ = 1 := h𝔞'
  exact this (mem_spanSingleton_self A⁰ _)

/-- The determinant of a matrix satisfying the entry conditions of `Γ₀(𝔫, 𝔞)` is integral. -/
private theorem det_mem_one {γ : GL (Fin 2) K} (h00 : γ 0 0 ∈ (1 : FractionalIdeal A⁰ K))
    (h11 : γ 1 1 ∈ (1 : FractionalIdeal A⁰ K)) (h01 : γ 0 1 ∈ 𝔞⁻¹) (h10 : γ 1 0 ∈ 𝔞 * 𝔫) :
    (γ : Matrix (Fin 2) (Fin 2) K).det ∈ (1 : FractionalIdeal A⁰ K) := by
  rw [Matrix.det_fin_two, sub_eq_add_neg]
  refine FractionalIdeal.add_mem (by simpa using mul_mem_mul h00 h11) ?_
  exact FractionalIdeal.neg_mem (mul_mem_one_of_mem_inv h01 (mem_of_mem_mul_coeIdeal h10))

/-- **`Γ₀(𝔫, 𝔞)` is the stabilizer of the lattice pair `A ⊕ 𝔞 ⊇ A ⊕ 𝔞𝔫`** in `GL₂(K)`, for an
invertible fractional ideal `𝔞`. -/
theorem stabilizer_lattice_inf_stabilizer_lattice (h𝔞 : IsUnit 𝔞) :
    MulAction.stabilizer (GL (Fin 2) K) (lattice 𝔞) ⊓
        MulAction.stabilizer (GL (Fin 2) K) (lattice (𝔞 * 𝔫 : FractionalIdeal A⁰ K)) =
      Gamma0Component 𝔫 𝔞 := by
  ext γ
  simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  constructor
  · rintro ⟨hL, hM⟩
    obtain ⟨h00, h11, h01, h10⟩ := entries_of_mem_stabilizer 𝔫 h𝔞 hL hM
    -- The inverse also stabilizes both lattices, so both determinants are integral.
    obtain ⟨i00, i11, i01, i10⟩ := entries_of_mem_stabilizer 𝔫 h𝔞 (γ := γ⁻¹)
      (inv_smul_eq_iff.mpr hL.symm) (inv_smul_eq_iff.mpr hM.symm)
    obtain ⟨r, hr⟩ := (mem_one_iff A⁰).mp (det_mem_one 𝔫 h00 h11 h01 h10)
    obtain ⟨s, hs⟩ := (mem_one_iff A⁰).mp (det_mem_one 𝔫 i00 i11 i01 i10)
    have hrs : r * s = 1 := by
      apply IsFractionRing.injective A K
      rw [map_mul, hr, hs, map_one, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.det_one]
    exact ⟨h00, h11, h01, h10, ⟨r, s, hrs, mul_comm s r ▸ hrs⟩, hr⟩
  · intro hγ
    -- Every element of `Γ₀(𝔫, 𝔞)` carries each lattice into itself; apply this to `γ⁻¹` too.
    have hle : ∀ δ ∈ Gamma0Component 𝔫 𝔞,
        δ • lattice 𝔞 ≤ lattice 𝔞 ∧
          δ • lattice (𝔞 * 𝔫 : FractionalIdeal A⁰ K) ≤ lattice (𝔞 * 𝔫 : FractionalIdeal A⁰ K) := by
      rintro δ ⟨h00, h11, h01, h10, -⟩
      exact ⟨smul_lattice_le h00 h11 (fun y ↦ mul_mem_one_of_mem_inv h01)
          (mem_of_mem_mul_coeIdeal h10),
        smul_lattice_le h00 h11
          (fun y hy ↦ mul_mem_one_of_mem_inv h01 (mem_of_mem_mul_coeIdeal hy)) h10⟩
    have heq {L : Submodule A (Fin 2 → K)} (h : γ • L ≤ L) (h' : γ⁻¹ • L ≤ L) : γ • L = L :=
      le_antisymm h <| (smul_inv_smul γ L).symm.le.trans
        (Submodule.pointwise_smul_le_pointwise_smul_iff.mpr h')
    exact ⟨heq (hle γ hγ).1 (hle γ⁻¹ (inv_mem hγ)).1, heq (hle γ hγ).2 (hle γ⁻¹ (inv_mem hγ)).2⟩

end Gamma0Component

end TauCeti
