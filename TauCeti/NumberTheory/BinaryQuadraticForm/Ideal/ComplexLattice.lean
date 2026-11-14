/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Quadratic
public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.Change
public import TauCeti.NumberTheory.BinaryQuadraticForm.Root
public import TauCeti.NumberTheory.QuadraticOrder.ComplexEmbedding
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

/-!
# Complex submodules and lattices attached to binary quadratic forms

For an integral binary quadratic form `f = (a, b, c)` of nonpositive discriminant `D ≤ 0`, the
distinguished complex embedding `QuadraticAlgebra.complexEmbedding` of `ℚ(√D)` maps the second
ideal generator `(-b + ω) / 2` to `(-b + √(-D) · i) / 2` and sends the order module
`f.orderIdeal D` to the `ℤ`-submodule `f.complexOrderIdeal D = a ℤ + ((-b + √(-D) · i) / 2) ℤ ⊆ ℂ`
(isomorphic as a `ℤ`-module to `f.orderIdeal D` when `D < 0`; `equivComplexOrderIdeal`).
Because `f.orderIdeal D` is a module over `QuadraticOrder.toSubalgebra D`, the embedded quadratic
subalgebra `complexOrder D` acts on `f.complexOrderIdeal D` by multiplication
(`complexOrder_le_leftOrder_complexOrderIdeal`).

When `f ∈ posDef n` (`n > 0`, `D = -n`), the embedded generator equals `a · root f`
(`complexEmbedding_idealGenerator_posDef`), so `f.complexOrderIdeal (-n)` is the lattice of the
rescaled period pair `a • (root f).periodPair` — explicitly homothetic to `ℤ · root f + ℤ`
(`complexOrderIdeal_eq_lattice_smul_periodPair_root`). Under a proper change of variables
`γ ∈ SL(2, ℤ)`, the algebraic scaling factor `f.idealChangeFactor (-n) γ` embeds to
`conj (denom γ (root f))` (`complexEmbedding_idealChangeFactor_posDef`), giving naturality of
`complexOrderIdeal` under the `SL(2, ℤ)`-action (`complexOrderIdeal_smul` and
`complexOrderIdeal_smul_posDef`).

## Main definitions

* `TauCeti.BinaryQuadraticForm.complexOrderIdeal`: the `ℤ`-submodule
  `a ℤ + ((-b + √(-D) · i) / 2) ℤ ⊆ ℂ` attached to a form `f` of discriminant `D ≤ 0`.
* `TauCeti.BinaryQuadraticForm.equivComplexOrderIdeal`: `f.orderIdeal D hf ≃ₗ[ℤ]
  f.complexOrderIdeal D hD0.le hf` for `D < 0`.

## Main results

* `TauCeti.BinaryQuadraticForm.complexOrder_le_leftOrder_complexOrderIdeal`: `complexOrder D` is
  contained in the multiplier order `(f.complexOrderIdeal D).leftOrder`.
* `TauCeti.BinaryQuadraticForm.complexOrderIdeal_smul`: proper `SL(2, ℤ)`-action multiplies
  `f.complexOrderIdeal D` by the embedded `idealChangeFactor`.
* `TauCeti.BinaryQuadraticForm.complexOrderIdeal_eq_lattice_smul_periodPair_root`: for
  `f : posDef n`, `f.1.complexOrderIdeal (-n)` equals `(a • (root f).periodPair).lattice`.
* `TauCeti.BinaryQuadraticForm.complexEmbedding_idealChangeFactor_posDef`: for `f : posDef n` and
  `γ : SL(2, ℤ)`, `f.1.idealChangeFactor (-n) γ` embeds to `conj (denom γ (root f))`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7, Theorem 7.7, and §10–11.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Chapter II, §1.
-/

public noncomputable section

open Complex ComplexConjugate QuadraticAlgebra
open UpperHalfPlane hiding I
open scoped MatrixGroups

namespace TauCeti.BinaryQuadraticForm

section NonposDiscrim

/-- Under `QuadraticAlgebra.complexEmbedding`, `f.idealGenerator D = (-b + ω) / 2` maps to
`(-b + √(-D) · i) / 2`. -/
@[simp] theorem complexEmbedding_idealGenerator (f : BinaryQuadraticForm ℤ) {D : ℤ}
    (ha : (D : ℚ) ≤ 0) :
    complexEmbedding ha (f.idealGenerator D) =
      (-(f.b : ℂ) + (√(-(D : ℝ)) : ℂ) * I) / 2 := by
  rw [complexEmbedding_apply, idealGenerator_re, idealGenerator_im]
  push_cast
  ring

/-- **The complex `ℤ`-submodule attached to a binary quadratic form** of discriminant `D ≤ 0`: the
image of the form module `f.orderIdeal D` in `ℂ` under `QuadraticAlgebra.complexEmbedding` (a
lattice in `ℂ` when `f` is positive definite, `D < 0`). -/
def complexOrderIdeal (f : BinaryQuadraticForm ℤ) (D : ℤ) (hD0 : D ≤ 0)
    (hf : f.discrim = D) : Submodule ℤ ℂ :=
  ((f.orderIdeal D hf).restrictScalars ℤ).map
    ((complexEmbedding (Int.cast_nonpos.mpr hD0)).restrictScalars ℤ).toLinearMap

/-- Definitional expansion of `complexOrderIdeal`. -/
theorem complexOrderIdeal_def (f : BinaryQuadraticForm ℤ) (D : ℤ) (hD0 : D ≤ 0)
    (hf : f.discrim = D) :
    f.complexOrderIdeal D hD0 hf =
      ((f.orderIdeal D hf).restrictScalars ℤ).map
        ((complexEmbedding (Int.cast_nonpos.mpr hD0)).restrictScalars ℤ).toLinearMap :=
  (rfl)

/-- `f.complexOrderIdeal D` is the `ℤ`-span of `f.a` and `(-f.b + √(-D) · i) / 2`. -/
theorem complexOrderIdeal_eq_span (f : BinaryQuadraticForm ℤ) (D : ℤ) (hD0 : D ≤ 0)
    (hf : f.discrim = D) :
    f.complexOrderIdeal D hD0 hf =
      Submodule.span ℤ ({(f.a : ℂ), (-(f.b : ℂ) + (√(-(D : ℝ)) : ℂ) * I) / 2} : Set ℂ) := by
  rw [complexOrderIdeal_def, orderIdeal_restrictScalars, Submodule.map_span]
  have himg : (((complexEmbedding (Int.cast_nonpos.mpr hD0)).restrictScalars ℤ).toLinearMap ''
      ({(f.a : QuadraticAlgebra ℚ (D : ℚ) 0), f.idealGenerator D} :
        Set (QuadraticAlgebra ℚ (D : ℚ) 0))) =
      ({(f.a : ℂ), (-(f.b : ℂ) + (√(-(D : ℝ)) : ℂ) * I) / 2} : Set ℂ) := by
    simp [Set.image_insert_eq]
  rw [himg]

/-- Membership in `f.complexOrderIdeal D` is an integral combination of `f.a` and
`(-f.b + √(-D) · i) / 2`. -/
theorem mem_complexOrderIdeal_iff (f : BinaryQuadraticForm ℤ) (D : ℤ) (hD0 : D ≤ 0)
    (hf : f.discrim = D) {z : ℂ} :
    z ∈ f.complexOrderIdeal D hD0 hf ↔
      ∃ m k : ℤ, (m : ℂ) * f.a + k * ((-(f.b : ℂ) + (√(-(D : ℝ)) : ℂ) * I) / 2) = z := by
  rw [complexOrderIdeal_eq_span, Submodule.mem_span_pair]
  simp only [zsmul_eq_mul]

/-- The leading coefficient `f.a` belongs to `f.complexOrderIdeal D`. -/
@[simp] theorem a_mem_complexOrderIdeal (f : BinaryQuadraticForm ℤ) (D : ℤ) (hD0 : D ≤ 0)
    (hf : f.discrim = D) :
    (f.a : ℂ) ∈ f.complexOrderIdeal D hD0 hf :=
  (mem_complexOrderIdeal_iff f D hD0 hf).mpr ⟨1, 0, by simp⟩

/-- The embedded second generator `(-f.b + √(-D) · i) / 2` belongs to `f.complexOrderIdeal D`. -/
@[simp] theorem neg_b_add_sqrt_neg_mul_I_div_two_mem_complexOrderIdeal
    (f : BinaryQuadraticForm ℤ) (D : ℤ) (hD0 : D ≤ 0) (hf : f.discrim = D) :
    (-(f.b : ℂ) + (√(-(D : ℝ)) : ℂ) * I) / 2 ∈ f.complexOrderIdeal D hD0 hf :=
  (mem_complexOrderIdeal_iff f D hD0 hf).mpr ⟨0, 1, by simp⟩

/-- For `D < 0`, an element of `ℚ(√D)` maps into `f.complexOrderIdeal D` under
`QuadraticAlgebra.complexEmbedding` if and only if it belongs to `f.orderIdeal D`. -/
@[simp] theorem complexEmbedding_mem_complexOrderIdeal_iff (f : BinaryQuadraticForm ℤ)
    {D : ℤ} {ha : (D : ℚ) ≤ 0} {hD_le : D ≤ 0} (hD0 : D < 0) (hf : f.discrim = D)
    {z : QuadraticAlgebra ℚ (D : ℚ) 0} :
    complexEmbedding ha z ∈ f.complexOrderIdeal D hD_le hf ↔ z ∈ f.orderIdeal D hf := by
  rw [complexOrderIdeal_def, Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, hwz⟩
    have hweq : w = z :=
      complexEmbedding_injective (by exact_mod_cast hD0) hwz
    exact hweq ▸ hw
  · intro hz
    exact ⟨z, hz, rfl⟩

/-- For `D < 0`, the distinguished complex embedding restricts to a `ℤ`-linear equivalence
`f.orderIdeal D hf ≃ₗ[ℤ] f.complexOrderIdeal D hD0.le hf`. -/
def equivComplexOrderIdeal (f : BinaryQuadraticForm ℤ) (D : ℤ) (hD0 : D < 0)
    (hf : f.discrim = D) :
    f.orderIdeal D hf ≃ₗ[ℤ] f.complexOrderIdeal D hD0.le hf :=
  LinearEquiv.ofBijective
    ({ toFun := fun z ↦ ⟨complexEmbedding (Int.cast_nonpos.mpr hD0.le) z.1, ⟨z.1, z.2, rfl⟩⟩
       map_add' := fun x y ↦ by ext; exact map_add _ x.1 y.1
       map_smul' := fun r x ↦ by ext; exact map_zsmul _ r x.1 } :
      f.orderIdeal D hf →ₗ[ℤ] f.complexOrderIdeal D hD0.le hf)
    ⟨fun x y h ↦ Subtype.ext (complexEmbedding_injective (by exact_mod_cast hD0)
      (Subtype.ext_iff.mp h)),
     fun ⟨_, w, hw, rfl⟩ ↦ ⟨⟨w, hw⟩, rfl⟩⟩

/-- Evaluation of `equivComplexOrderIdeal` agrees with `QuadraticAlgebra.complexEmbedding`. -/
@[simp] theorem coe_equivComplexOrderIdeal_apply (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hD0 : D < 0) (hf : f.discrim = D) (z : f.orderIdeal D hf) :
    (equivComplexOrderIdeal f D hD0 hf z : ℂ) =
      complexEmbedding (Int.cast_nonpos.mpr hD0.le) (z : QuadraticAlgebra ℚ (D : ℚ) 0) :=
  (rfl)

/-- Applying `QuadraticAlgebra.complexEmbedding` after `(equivComplexOrderIdeal f D hD0 hf).symm`
recovers the complex element. -/
@[simp] theorem complexEmbedding_equivComplexOrderIdeal_symm (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hD0 : D < 0) (hf : f.discrim = D) (z : f.complexOrderIdeal D hD0.le hf) :
    complexEmbedding (Int.cast_nonpos.mpr hD0.le)
        ((equivComplexOrderIdeal f D hD0 hf).symm z : QuadraticAlgebra ℚ (D : ℚ) 0) = z := by
  rw [← coe_equivComplexOrderIdeal_apply f D hD0 hf, LinearEquiv.apply_symm_apply]

/-- Every element of `f.complexOrderIdeal D` lies in `QuadraticOrder.complexOrder D`. -/
theorem complexOrderIdeal_le_complexOrder (f : BinaryQuadraticForm ℤ) (D : ℤ) (hD0 : D ≤ 0)
    (hf : f.discrim = D) :
    f.complexOrderIdeal D hD0 hf ≤
      Subalgebra.toSubmodule
        (QuadraticOrder.complexOrder D hD0 (hf ▸ f.discrim_emod_four_eq_zero_or_one)) := by
  intro z hz
  rw [Subalgebra.mem_toSubmodule, QuadraticOrder.complexOrder_def, Subalgebra.mem_map]
  rcases hz with ⟨w, hw, rfl⟩
  exact ⟨w, orderIdeal_le_order f D hf hw, rfl⟩

/-- The embedded quadratic order `complexOrder D` is contained in the multiplier order of
`f.complexOrderIdeal D`. -/
theorem complexOrder_le_leftOrder_complexOrderIdeal (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hD0 : D ≤ 0) (hf : f.discrim = D) :
    QuadraticOrder.complexOrder D hD0 (hf ▸ f.discrim_emod_four_eq_zero_or_one) ≤
      (f.complexOrderIdeal D hD0 hf).leftOrder := by
  intro x hx
  rw [QuadraticOrder.complexOrder_def, Subalgebra.mem_map] at hx
  rcases hx with ⟨r, hr, rfl⟩
  rw [Submodule.mem_leftOrder_iff]
  rintro _ ⟨w, hw, rfl⟩
  refine ⟨r * w, ?_, ?_⟩
  · rw [SetLike.mem_coe, Submodule.restrictScalars_mem] at hw ⊢
    simpa only [Algebra.smul_def, Subalgebra.algebraMap_apply] using
      (f.orderIdeal D hf).smul_mem ⟨r, hr⟩ hw
  · exact map_mul ((complexEmbedding (Int.cast_nonpos.mpr hD0)).restrictScalars ℤ) r w

/-- **Naturality of `complexOrderIdeal` under proper `SL(2, ℤ)`-action**: when `f.a ≠ 0`,
`(γ • f).complexOrderIdeal D` is obtained from `f.complexOrderIdeal D` by multiplying by the
embedded `idealChangeFactor`. -/
theorem complexOrderIdeal_smul (f : BinaryQuadraticForm ℤ) (D : ℤ) (hD0 : D ≤ 0)
    (hf : f.discrim = D) (hfa : f.a ≠ 0) (γ : SL(2, ℤ)) :
    (γ • f).complexOrderIdeal D hD0 ((discrim_smul γ f).trans hf) =
      (f.complexOrderIdeal D hD0 hf).map
        (LinearMap.mulLeft ℤ (complexEmbedding (Int.cast_nonpos.mpr hD0)
          (f.idealChangeFactor D γ))) := by
  have h₀ := congrArg (complexEmbedding (Int.cast_nonpos.mpr hD0))
    (idealChangeFactor_mul_first f D hf hfa γ)
  have h₁ := congrArg (complexEmbedding (Int.cast_nonpos.mpr hD0))
    (idealChangeFactor_mul_second f D hf hfa γ)
  simp only [map_mul, map_add, map_intCast, complexEmbedding_idealGenerator] at h₀ h₁
  apply le_antisymm
  · intro z hz
    obtain ⟨m, n, rfl⟩ := (mem_complexOrderIdeal_iff _ _ _ _).mp hz
    rw [Submodule.mem_map]
    refine ⟨(m * γ 1 1 + n * γ 0 1 : ℤ) * (f.a : ℂ) +
        (m * γ 1 0 + n * γ 0 0 : ℤ) * ((-(f.b : ℂ) + (√(-(D : ℝ)) : ℂ) * I) / 2),
      (mem_complexOrderIdeal_iff f D hD0 hf).mpr ⟨_, _, rfl⟩, ?_⟩
    simp only [LinearMap.mulLeft_apply]
    push_cast
    linear_combination (m : ℂ) * h₀ + (n : ℂ) * h₁
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨m, n, rfl⟩ := (mem_complexOrderIdeal_iff f D hD0 hf).mp hy
    have hdet : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      exact_mod_cast Matrix.SpecialLinearGroup.intCast_fin_two_mul_sub_mul_eq_one (R := ℚ) γ
    rw [mem_complexOrderIdeal_iff]
    refine ⟨γ 0 0 * m - γ 0 1 * n, -(γ 1 0 * m) + γ 1 1 * n, ?_⟩
    simp only [LinearMap.mulLeft_apply]
    push_cast
    linear_combination -((γ 0 0 : ℂ) * m - γ 0 1 * n) * h₀ -
      (-(γ 1 0 * m) + γ 1 1 * n) * h₁ +
      complexEmbedding (Int.cast_nonpos.mpr hD0) (f.idealChangeFactor D γ) *
        ((m : ℂ) * f.a + (n : ℂ) * ((-(f.b : ℂ) + (√(-(D : ℝ)) : ℂ) * I) / 2)) * hdet

end NonposDiscrim

section PosDef

variable {n : ℕ} [NeZero n]

/-- For a positive definite form `f ∈ posDef n`, the second ideal generator embeds to
`f.a · root f`. -/
theorem complexEmbedding_idealGenerator_posDef (f : posDef n)
    (ha : ((-(n : ℤ) : ℤ) : ℚ) ≤ 0) :
    complexEmbedding ha (f.1.idealGenerator (-n)) = (f.1.a : ℂ) * (root f : ℂ) := by
  have hfa : (f.1.a : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (mem_posDef.mp f.2).2.ne'
  rw [complexEmbedding_idealGenerator, coe_root]
  have hsqrt : √(-((-(n : ℤ) : ℤ) : ℝ)) = √(n : ℝ) := by simp
  rw [hsqrt]
  field_simp

/-- For `f ∈ posDef n`, `f.a · root f` belongs to `f.1.complexOrderIdeal (-n)`. -/
@[simp] theorem a_mul_root_mem_complexOrderIdeal (f : posDef n) :
    (f.1.a : ℂ) * (root f : ℂ) ∈
      f.1.complexOrderIdeal (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
        (mem_posDef.mp f.2).1 := by
  have hgen := complexEmbedding_idealGenerator_posDef f
    (Int.cast_nonpos.mpr (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)))
  rw [complexEmbedding_idealGenerator] at hgen
  rw [← hgen]
  exact neg_b_add_sqrt_neg_mul_I_div_two_mem_complexOrderIdeal _ _ _ _

/-- **Complex lattice of `f ∈ posDef n` as a rescaled period lattice**: `f.1.complexOrderIdeal (-n)`
equals `(a • (root f).periodPair).lattice = ℤ · (a · root f) + ℤ · a`, hence is homothetic to
`ℤ · root f + ℤ`. -/
theorem complexOrderIdeal_eq_lattice_smul_periodPair_root (f : posDef n) :
    f.1.complexOrderIdeal (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
        (mem_posDef.mp f.2).1 =
      (Units.mk0 (f.1.a : ℂ) (Int.cast_ne_zero.mpr (mem_posDef.mp f.2).2.ne') •
        (root f).periodPair).lattice := by
  have hgen := complexEmbedding_idealGenerator_posDef f
    (Int.cast_nonpos.mpr (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)))
  rw [complexEmbedding_idealGenerator] at hgen
  ext z
  rw [mem_complexOrderIdeal_iff, PeriodPair.mem_lattice]
  simp only [PeriodPair.smul_ω₁, PeriodPair.smul_ω₂, Units.val_mk0, periodPair_ω₁, periodPair_ω₂,
    mul_one, hgen]
  exact ⟨fun ⟨m, k, h⟩ ↦ ⟨k, m, by linear_combination h⟩,
    fun ⟨k, m, h⟩ ↦ ⟨m, k, by linear_combination h⟩⟩

/-- For `f ∈ posDef n`, the multiplier order of `f.1.complexOrderIdeal (-n)` equals the multiplier
order of `(root f).periodPair.lattice = ℤ · root f + ℤ`. -/
theorem leftOrder_complexOrderIdeal_posDef (f : posDef n) :
    (f.1.complexOrderIdeal (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
        (mem_posDef.mp f.2).1).leftOrder =
      (root f).periodPair.lattice.leftOrder := by
  rw [complexOrderIdeal_eq_lattice_smul_periodPair_root, PeriodPair.leftOrder_lattice_smul]

/-- For `f ∈ posDef n`, `QuadraticOrder.complexOrder (-n)` is contained in the multiplier order of
`ℤ · root f + ℤ`. -/
theorem complexOrder_le_leftOrder_lattice_periodPair_root (f : posDef n) :
    QuadraticOrder.complexOrder (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
        ((mem_posDef.mp f.2).1 ▸ f.1.discrim_emod_four_eq_zero_or_one) ≤
      (root f).periodPair.lattice.leftOrder := by
  rw [← leftOrder_complexOrderIdeal_posDef]
  exact complexOrder_le_leftOrder_complexOrderIdeal f.1 (-n)
    (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) (mem_posDef.mp f.2).1

/-- **Embedded proper-change factor as conjugate automorphy factor**: for `f ∈ posDef n` and
`γ ∈ SL(2, ℤ)`, `f.1.idealChangeFactor (-n) γ` maps under `QuadraticAlgebra.complexEmbedding` to
`conj (denom γ (root f))`. -/
theorem complexEmbedding_idealChangeFactor_posDef (f : posDef n) (γ : SL(2, ℤ))
    (ha : ((-(n : ℤ) : ℤ) : ℚ) ≤ 0) :
    complexEmbedding ha (f.1.idealChangeFactor (-n) γ) = conj (denom γ (root f)) := by
  have hfa : (f.1.a : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (mem_posDef.mp f.2).2.ne'
  rw [idealChangeFactor_def, (complexEmbedding ha).map_smul_of_tower, Rat.smul_def, Rat.cast_inv,
    Rat.cast_intCast, complexEmbedding_star, map_add, map_zsmul, map_zsmul, map_intCast,
    complexEmbedding_idealGenerator_posDef, map_add, map_zsmul, map_zsmul, map_intCast, map_mul,
    map_intCast, zsmul_eq_mul, zsmul_eq_mul, ModularGroup.denom_apply, map_add, map_mul,
    map_intCast, map_intCast]
  field_simp
  ring

/-- **Proper `SL(2, ℤ)`-equivariance of `complexOrderIdeal` on `posDef n`**: acting by
`γ ∈ SL(2, ℤ)` scales `f.1.complexOrderIdeal (-n)` by `conj (denom γ (root f))`. -/
theorem complexOrderIdeal_smul_posDef (f : posDef n) (γ : SL(2, ℤ)) :
    (γ • f).1.complexOrderIdeal (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
        (mem_posDef.mp (γ • f).2).1 =
      (f.1.complexOrderIdeal (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
        (mem_posDef.mp f.2).1).map
        (LinearMap.mulLeft ℤ (conj (denom γ (root f)))) := by
  have h := complexOrderIdeal_smul f.1 (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
    (mem_posDef.mp f.2).1 (mem_posDef.mp f.2).2.ne' γ
  rwa [complexEmbedding_idealChangeFactor_posDef] at h

end PosDef

end TauCeti.BinaryQuadraticForm
