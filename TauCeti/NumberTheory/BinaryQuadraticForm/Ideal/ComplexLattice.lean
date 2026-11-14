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

/-!
# Complex submodules and lattices attached to binary quadratic forms

For an integral binary quadratic form `f = (a, b, c)` of nonpositive discriminant `D ≤ 0`,
`QuadraticAlgebra.complexEmbedding` maps `(-b + ω) / 2` to `(-b + √(-D) · i) / 2` and sends the
order module `f.orderIdeal D` to the `ℤ`-submodule
`f.complexOrderIdeal D = a ℤ + ((-b + √(-D) · i) / 2) ℤ ⊆ ℂ` (`equivComplexOrderIdeal` for `D < 0`),
on which `complexOrder D` acts by multiplication (`complexOrder_le_leftOrder_complexOrderIdeal`).

When `f ∈ posDef n` (`n > 0`, `D = -n`), the embedded generator equals `a · root f`
(`complexEmbedding_idealGenerator_posDef`), so `f.complexOrderIdeal (-n)` is the lattice of
`a • (root f).periodPair` (`complexOrderIdeal_eq_lattice_smul_periodPair_root`), and
`(ℤ · root f + ℤ).leftOrder` equals `complexOrder f.primPart.discrim`
(`leftOrder_lattice_periodPair_root_eq_complexOrder_discrim_primPart`), giving primitivity and CM
upper-half-plane characterizations (`leftOrder_lattice_periodPair_eq_complexOrder_iff`) as well as
`(f.complexOrderIdeal D).leftOrder = complexOrder D ↔ f.IsPrimitive` for any integral form `f` of
negative discriminant `D < 0` (`leftOrder_complexOrderIdeal_eq_complexOrder_iff_isPrimitive`).
Under `γ ∈ SL(2, ℤ)`, `f.idealChangeFactor (-n) γ` embeds to `conj (denom γ (root f))`
(`complexEmbedding_idealChangeFactor_posDef`), giving `SL(2, ℤ)`-equivariance
(`complexOrderIdeal_smul`, `complexOrderIdeal_smul_posDef`).

## Main definitions

* `TauCeti.BinaryQuadraticForm.complexOrderIdeal`: the `ℤ`-submodule
  `a ℤ + ((-b + √(-D) · i) / 2) ℤ ⊆ ℂ` attached to a form `f` of discriminant `D ≤ 0`.
* `TauCeti.BinaryQuadraticForm.equivComplexOrderIdeal`: `f.orderIdeal D hf ≃ₗ[ℤ]
  f.complexOrderIdeal D hD0.le hf` for `D < 0`.

## Main results

* `TauCeti.BinaryQuadraticForm.complexOrder_le_leftOrder_complexOrderIdeal`: `complexOrder D` is
  contained in `(f.complexOrderIdeal D).leftOrder`.
* `TauCeti.BinaryQuadraticForm.complexOrderIdeal_smul`,
  `TauCeti.BinaryQuadraticForm.complexOrderIdeal_smul_posDef`: `SL(2, ℤ)`-equivariance of
  `complexOrderIdeal`.
* `TauCeti.BinaryQuadraticForm.complexOrderIdeal_eq_lattice_smul_periodPair_root`: for
  `f : posDef n`, `f.1.complexOrderIdeal (-n)` equals `(a • (root f).periodPair).lattice`.
* `TauCeti.BinaryQuadraticForm.leftOrder_lattice_periodPair_root_eq_complexOrder_discrim_primPart`,
  `TauCeti.BinaryQuadraticForm.leftOrder_lattice_periodPair_root_eq_complexOrder_iff_isPrimitive`,
  `TauCeti.BinaryQuadraticForm.leftOrder_lattice_periodPair_eq_complexOrder_iff`,
  `TauCeti.BinaryQuadraticForm.leftOrder_complexOrderIdeal_eq_complexOrder_iff_isPrimitive`:
  exact multiplier orders of form roots, CM upper-half-plane points, and `complexOrderIdeal`.
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
    complexEmbedding ha (f.idealGenerator D) = (-(f.b : ℂ) + (√(-(D : ℝ)) : ℂ) * I) / 2 := by
  rw [complexEmbedding_apply, idealGenerator_re, idealGenerator_im]; push_cast; ring

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
  congr 1; simp [Set.image_insert_eq]

/-- Membership in `f.complexOrderIdeal D` is an integral combination of `f.a` and
`(-f.b + √(-D) · i) / 2`. -/
theorem mem_complexOrderIdeal_iff (f : BinaryQuadraticForm ℤ) (D : ℤ) (hD0 : D ≤ 0)
    (hf : f.discrim = D) {z : ℂ} :
    z ∈ f.complexOrderIdeal D hD0 hf ↔
      ∃ m k : ℤ, (m : ℂ) * f.a + k * ((-(f.b : ℂ) + (√(-(D : ℝ)) : ℂ) * I) / 2) = z := by
  rw [complexOrderIdeal_eq_span, Submodule.mem_span_pair]; simp only [zsmul_eq_mul]

/-- The leading coefficient `f.a` belongs to `f.complexOrderIdeal D`. -/
@[simp] theorem a_mem_complexOrderIdeal (f : BinaryQuadraticForm ℤ) (D : ℤ) (hD0 : D ≤ 0)
    (hf : f.discrim = D) : (f.a : ℂ) ∈ f.complexOrderIdeal D hD0 hf :=
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
  exact ⟨fun ⟨w, hw, hwz⟩ ↦ complexEmbedding_injective (by exact_mod_cast hD0) hwz ▸ hw,
    fun hz ↦ ⟨z, hz, rfl⟩⟩

/-- For `D < 0`, the distinguished complex embedding restricts to a `ℤ`-linear equivalence
`f.orderIdeal D hf ≃ₗ[ℤ] f.complexOrderIdeal D hD0.le hf`. -/
def equivComplexOrderIdeal (f : BinaryQuadraticForm ℤ) (D : ℤ) (hD0 : D < 0)
    (hf : f.discrim = D) : f.orderIdeal D hf ≃ₗ[ℤ] f.complexOrderIdeal D hD0.le hf :=
  LinearEquiv.ofBijective
    ({ toFun := fun z ↦ ⟨complexEmbedding (Int.cast_nonpos.mpr hD0.le) z.1, ⟨z.1, z.2, rfl⟩⟩
       map_add' := fun x y ↦ by ext; exact map_add _ x.1 y.1
       map_smul' := fun r x ↦ by ext; exact map_zsmul _ r x.1 } :
      f.orderIdeal D hf →ₗ[ℤ] f.complexOrderIdeal D hD0.le hf)
    ⟨fun x y h ↦ Subtype.ext (complexEmbedding_injective (by exact_mod_cast hD0)
      (Subtype.ext_iff.mp h)),
     fun ⟨_, w, hw, rfl⟩ ↦ ⟨⟨w, hw⟩, rfl⟩⟩

/-- Evaluation of `equivComplexOrderIdeal` agrees with `QuadraticAlgebra.complexEmbedding`. -/
@[simp] theorem coe_equivComplexOrderIdeal_apply (f : BinaryQuadraticForm ℤ) (D : ℤ) (hD0 : D < 0)
    (hf : f.discrim = D) (z : f.orderIdeal D hf) :
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
    f.complexOrderIdeal D hD0 hf ≤ Subalgebra.toSubmodule
      (QuadraticOrder.complexOrder D hD0 (hf ▸ f.discrim_emod_four_eq_zero_or_one)) := by
  rintro z ⟨w, hw, rfl⟩
  rw [Subalgebra.mem_toSubmodule, QuadraticOrder.complexOrder_def, Subalgebra.mem_map]
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
  refine ⟨r * w, ?_, map_mul ((complexEmbedding (Int.cast_nonpos.mpr hD0)).restrictScalars ℤ) r w⟩
  rw [SetLike.mem_coe, Submodule.restrictScalars_mem] at hw ⊢
  simpa only [Algebra.smul_def, Subalgebra.algebraMap_apply] using
    (f.orderIdeal D hf).smul_mem ⟨r, hr⟩ hw

/-- **Naturality of `complexOrderIdeal` under proper `SL(2, ℤ)`-action**: when `f.a ≠ 0`,
`(γ • f).complexOrderIdeal D` is obtained from `f.complexOrderIdeal D` by multiplying by the
embedded `idealChangeFactor`. -/
theorem complexOrderIdeal_smul (f : BinaryQuadraticForm ℤ) (D : ℤ) (hD0 : D ≤ 0)
    (hf : f.discrim = D) (hfa : f.a ≠ 0) (γ : SL(2, ℤ)) :
    (γ • f).complexOrderIdeal D hD0 ((discrim_smul γ f).trans hf) =
      (f.complexOrderIdeal D hD0 hf).map
        (LinearMap.mulLeft ℤ (complexEmbedding (Int.cast_nonpos.mpr hD0)
          (f.idealChangeFactor D γ))) := by
  have h : ((γ • f).orderIdeal D ((discrim_smul γ f).trans hf)).restrictScalars ℤ =
      ((f.orderIdeal D hf).restrictScalars ℤ).map
        (LinearMap.mulLeft ℤ (f.idealChangeFactor D γ)) := by
    ext z
    simp only [Submodule.restrictScalars_mem, orderIdeal_smul f D hf hfa γ, Submodule.mem_map,
      LinearMap.mulLeft_apply]
  rw [complexOrderIdeal_def, complexOrderIdeal_def, h, ← Submodule.map_comp, ← Submodule.map_comp]
  congr 1; ext x; exact map_mul (complexEmbedding (Int.cast_nonpos.mpr hD0)) _ x

end NonposDiscrim

section PosDef

variable {n : ℕ} [NeZero n]

/-- For a positive definite form `f ∈ posDef n`, the second ideal generator embeds to
`f.a · root f`. -/
theorem complexEmbedding_idealGenerator_posDef (f : posDef n) (ha : ((-(n : ℤ) : ℤ) : ℚ) ≤ 0) :
    complexEmbedding ha (f.1.idealGenerator (-n)) = (f.1.a : ℂ) * (root f : ℂ) := by
  have hfa : (f.1.a : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (mem_posDef.mp f.2).2.ne'
  rw [complexEmbedding_idealGenerator, coe_root, show √(-((-(n : ℤ) : ℤ) : ℝ)) = √(n : ℝ) by simp]
  field_simp

/-- For `f ∈ posDef n`, `f.a · root f` belongs to `f.1.complexOrderIdeal (-n)`. -/
@[simp] theorem a_mul_root_mem_complexOrderIdeal (f : posDef n) :
    (f.1.a : ℂ) * (root f : ℂ) ∈ f.1.complexOrderIdeal (-n)
      (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) (mem_posDef.mp f.2).1 := by
  have hgen := complexEmbedding_idealGenerator_posDef f
    (Int.cast_nonpos.mpr (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)))
  rw [complexEmbedding_idealGenerator] at hgen
  exact hgen ▸ neg_b_add_sqrt_neg_mul_I_div_two_mem_complexOrderIdeal _ _ _ _

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
        (mem_posDef.mp f.2).1).leftOrder = (root f).periodPair.lattice.leftOrder := by
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

/-- **Exact multiplier order for a primitive positive definite form**: if `f ∈ posDef n` is
primitive, the left order of `ℤ · root f + ℤ` is `QuadraticOrder.complexOrder (-n)`. -/
theorem leftOrder_lattice_periodPair_root_eq_complexOrder_of_isPrimitive (f : posDef n)
    (hfprim : f.1.IsPrimitive) :
    (root f).periodPair.lattice.leftOrder =
      QuadraticOrder.complexOrder (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
        ((mem_posDef.mp f.2).1 ▸ f.1.discrim_emod_four_eq_zero_or_one) := by
  refine le_antisymm (fun x hx ↦ ?_) (complexOrder_le_leftOrder_lattice_periodPair_root f)
  obtain ⟨m, k, rfl⟩ :=
    (UpperHalfPlane.mem_leftOrder_lattice_periodPair_iff_of_quadratic_of_linearCombination_eq_one
      ((eq_root_iff f (root f)).mp rfl) hfprim.exists_linearCombination_eq_one).mp hx
  set O := QuadraticOrder.complexOrder (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
    ((mem_posDef.mp f.2).1 ▸ f.1.discrim_emod_four_eq_zero_or_one)
  exact add_mem (O.intCast_mem m) (mul_mem (O.intCast_mem k)
    (complexOrderIdeal_le_complexOrder f.1 (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
      (mem_posDef.mp f.2).1 (a_mul_root_mem_complexOrderIdeal f)))

/-- **Exact multiplier order of any positive definite form**: for `f ∈ posDef n` (not necessarily
primitive), `(root f).periodPair.lattice.leftOrder` is `complexOrder f.1.primPart.discrim`. -/
theorem leftOrder_lattice_periodPair_root_eq_complexOrder_discrim_primPart (f : posDef n) :
    (root f).periodPair.lattice.leftOrder =
      QuadraticOrder.complexOrder f.1.primPart.discrim (discrim_primPart_neg_of_posDef f).le
        f.1.primPart.discrim_emod_four_eq_zero_or_one := by
  obtain ⟨_, hfa⟩ := mem_posDef.mp f.2
  have hf0 : f.1 ≠ 0 := fun h ↦ by simp [h] at hfa
  have hdneg := discrim_primPart_neg_of_posDef f
  set m : ℕ := (-f.1.primPart.discrim).toNat
  have : NeZero m := ⟨by omega⟩
  have hg_disc : f.1.primPart.discrim = -m := by omega
  let g : posDef m := ⟨f.1.primPart, mem_posDef.mpr ⟨hg_disc, (a_primPart_pos_iff f.1).mpr hfa⟩⟩
  rw [← root_eq_root_of_eq_primPart (f := f) (g := g) rfl,
    leftOrder_lattice_periodPair_root_eq_complexOrder_of_isPrimitive g
      (f.1.isPrimitive_primPart hf0)]
  exact QuadraticOrder.complexOrder_eq_iff.mpr hg_disc.symm

/-- **Primitivity criterion via the multiplier order**: for `f ∈ posDef n`, the left order of
`ℤ · root f + ℤ` equals `complexOrder (-n)` if and only if `f` is primitive. -/
theorem leftOrder_lattice_periodPair_root_eq_complexOrder_iff_isPrimitive (f : posDef n) :
    (root f).periodPair.lattice.leftOrder =
        QuadraticOrder.complexOrder (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
          ((mem_posDef.mp f.2).1 ▸ f.1.discrim_emod_four_eq_zero_or_one) ↔
      f.1.IsPrimitive := by
  refine ⟨fun h ↦ ?_, leftOrder_lattice_periodPair_root_eq_complexOrder_of_isPrimitive f⟩
  have hd : f.1.primPart.discrim = -n := QuadraticOrder.complexOrder_eq_iff.mp
    ((leftOrder_lattice_periodPair_root_eq_complexOrder_discrim_primPart f).symm.trans h)
  have hsq := f.1.discrim_eq_content_sq_mul
  rw [(mem_posDef.mp f.2).1, hd] at hsq
  have hne : (-(n : ℤ)) ≠ 0 := neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (NeZero.ne n))
  have hc2z : (f.1.content : ℤ) ^ 2 = 1 := mul_right_cancel₀ hne
    (show (f.1.content : ℤ) ^ 2 * -(n : ℤ) = 1 * -(n : ℤ) by linear_combination -hsq)
  have : f.1.content ^ 2 = 1 := by exact_mod_cast hc2z
  exact f.1.isPrimitive_iff.mpr (by nlinarith)

/-- **Analytic-algebraic characterization of CM upper-half-plane points**: for `n > 0` with
`-n ≡ 0, 1 mod 4`, the multiplier order of `ℤ τ + ℤ` is `complexOrder (-n)` if and only if
`τ = root f` for a primitive positive definite form `f` of discriminant `-n`. -/
theorem leftOrder_lattice_periodPair_eq_complexOrder_iff
    (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1) {τ : ℍ} :
    τ.periodPair.lattice.leftOrder =
        QuadraticOrder.complexOrder (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n)) hn ↔
      ∃ f : ↥(posDef n ⊓ primitiveForms (-n)),
        root ⟨f, inf_le_left (b := primitiveForms (-n)) f.2⟩ = τ := by
  constructor
  · intro hleft
    -- Since `complexOrder (-n) ≠ ⊥`, `τ` satisfies an integral quadratic `a τ² + b τ + c = 0`.
    have hne : τ.periodPair.lattice.leftOrder ≠ ⊥ := hleft ▸ QuadraticOrder.complexOrder_ne_bot
      (Int.neg_neg_of_pos (Nat.cast_pos.mpr (NeZero.pos n))) hn
    obtain ⟨a, b, c, ha, hrel⟩ := UpperHalfPlane.leftOrder_lattice_periodPair_ne_bot_iff.mp hne
    let f₀ : BinaryQuadraticForm ℤ := ⟨a, b, c⟩
    have hd₀ : f₀.discrim < 0 := discrim_neg_of_quadratic_upperHalfPlane ha.ne' hrel
    set m : ℕ := (-f₀.discrim).toNat
    have : NeZero m := ⟨by omega⟩
    let fp : posDef m := ⟨f₀, mem_posDef.mpr ⟨by omega, ha⟩⟩
    have hroot₀ : τ = root fp := (eq_root_iff fp τ).mpr hrel
    -- Dividing `f₀` by its content gives a primitive form of discriminant `-n` with the same root.
    have hprim_ord := leftOrder_lattice_periodPair_root_eq_complexOrder_discrim_primPart fp
    rw [← hroot₀, hleft] at hprim_ord
    have hd_prim : f₀.primPart.discrim = -n :=
      (QuadraticOrder.complexOrder_eq_iff.mp hprim_ord).symm
    have hf₀_ne : f₀ ≠ 0 := fun h ↦ ha.ne' (by simpa [f₀] using congrArg BinaryQuadraticForm.a h)
    exact ⟨⟨f₀.primPart, (mem_posDef_inf_primitiveForms n).mpr
      ⟨hd_prim, (a_primPart_pos_iff f₀).mpr ha, f₀.isPrimitive_primPart hf₀_ne⟩⟩,
      (root_eq_root_of_eq_primPart (f := fp) rfl).trans hroot₀.symm⟩
  · rintro ⟨f, rfl⟩
    exact leftOrder_lattice_periodPair_root_eq_complexOrder_of_isPrimitive
      ⟨f, inf_le_left (b := primitiveForms (-n)) f.2⟩
      ((mem_posDef_inf_primitiveForms n).mp f.2).2.2

/-- **Embedded proper-change factor as conjugate automorphy factor**: for `f ∈ posDef n` and
`γ ∈ SL(2, ℤ)`, `f.1.idealChangeFactor (-n) γ` maps under `QuadraticAlgebra.complexEmbedding` to
`conj (denom γ (root f))`. -/
theorem complexEmbedding_idealChangeFactor_posDef (f : posDef n) (γ : SL(2, ℤ))
    (ha : ((-(n : ℤ) : ℤ) : ℚ) ≤ 0) :
    complexEmbedding ha (f.1.idealChangeFactor (-n) γ) = conj (denom γ (root f)) := by
  have hfa : (f.1.a : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (mem_posDef.mp f.2).2.ne'
  simp only [idealChangeFactor_def, Rat.smul_def, Rat.cast_inv, Rat.cast_intCast,
    complexEmbedding_star, map_inv₀, map_add, map_intCast,
    complexEmbedding_idealGenerator_posDef, map_mul, zsmul_eq_mul, ModularGroup.denom_apply]
  field_simp; ring

/-- **Proper `SL(2, ℤ)`-equivariance of `complexOrderIdeal` on `posDef n`**: acting by
`γ ∈ SL(2, ℤ)` scales `f.1.complexOrderIdeal (-n)` by `conj (denom γ (root f))`. -/
theorem complexOrderIdeal_smul_posDef (f : posDef n) (γ : SL(2, ℤ)) :
    (γ • f).1.complexOrderIdeal (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
        (mem_posDef.mp (γ • f).2).1 =
      (f.1.complexOrderIdeal (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
        (mem_posDef.mp f.2).1).map (LinearMap.mulLeft ℤ (conj (denom γ (root f)))) := by
  have h := complexOrderIdeal_smul f.1 (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
    (mem_posDef.mp f.2).1 (mem_posDef.mp f.2).2.ne' γ
  rwa [complexEmbedding_idealChangeFactor_posDef] at h

end PosDef

section NegDiscrim

/-- Negating and reflecting an integral form preserves `complexOrderIdeal` on the nose. -/
private theorem complexOrderIdeal_reflected_neg (f : BinaryQuadraticForm ℤ) (D : ℤ) (hD0 : D ≤ 0)
    (hf : f.discrim = D) (hfg : (-f).reflected.discrim = D) :
    (-f).reflected.complexOrderIdeal D hD0 hfg = f.complexOrderIdeal D hD0 hf := by
  ext z
  simp only [mem_complexOrderIdeal_iff, reflected_a, neg_a, reflected_b, neg_b, neg_neg,
    Int.cast_neg]
  exact ⟨fun ⟨m, k, h⟩ ↦ ⟨-m, k, by push_cast; linear_combination h⟩,
    fun ⟨m, k, h⟩ ↦ ⟨-m, k, by push_cast; linear_combination h⟩⟩

/-- For any integral form `f` of negative discriminant `D < 0` (regardless of the sign of `f.a`),
the left order of `f.complexOrderIdeal D` equals `complexOrder D` iff `f` is primitive. -/
theorem leftOrder_complexOrderIdeal_eq_complexOrder_iff_isPrimitive (f : BinaryQuadraticForm ℤ)
    (D : ℤ) (hD0 : D < 0) (hf : f.discrim = D) :
    (f.complexOrderIdeal D hD0.le hf).leftOrder =
        QuadraticOrder.complexOrder D hD0.le (hf ▸ f.discrim_emod_four_eq_zero_or_one) ↔
      f.IsPrimitive := by
  obtain ⟨n, hn0, rfl⟩ : ∃ n : ℕ, 0 < n ∧ D = -(n : ℤ) := ⟨(-D).toNat, by omega, by omega⟩
  have : NeZero n := ⟨hn0.ne'⟩
  rcases lt_trichotomy f.a 0 with hneg | ha0 | hpos
  · have hfg : (-f).reflected.discrim = -n := by
      rw [discrim_reflected, ← neg_one_smul ℤ f, discrim_smul']; simpa using hf
    let fp : posDef n := ⟨(-f).reflected, mem_posDef.mpr ⟨hfg, by simpa using neg_pos.mpr hneg⟩⟩
    rw [← complexOrderIdeal_reflected_neg f (-n) hD0.le hf hfg,
      show (-f).reflected.complexOrderIdeal (-n) hD0.le hfg =
        fp.1.complexOrderIdeal (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
          (mem_posDef.mp fp.2).1 from rfl,
      leftOrder_complexOrderIdeal_posDef fp,
      leftOrder_lattice_periodPair_root_eq_complexOrder_iff_isPrimitive fp]
    simp [fp, isPrimitive_iff]
  · exfalso; rw [discrim_def, discrim, ha0] at hf; nlinarith [sq_nonneg f.b]
  · let fp : posDef n := ⟨f, mem_posDef.mpr ⟨hf, hpos⟩⟩
    rw [show f.complexOrderIdeal (-n) hD0.le hf =
        fp.1.complexOrderIdeal (-n) (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))
          (mem_posDef.mp fp.2).1 from rfl,
      leftOrder_complexOrderIdeal_posDef fp,
      leftOrder_lattice_periodPair_root_eq_complexOrder_iff_isPrimitive fp]

/-- If an integral form `f` of negative discriminant `D < 0` is primitive, the left order of
`f.complexOrderIdeal D` is `QuadraticOrder.complexOrder D`. -/
theorem leftOrder_complexOrderIdeal_of_isPrimitive (f : BinaryQuadraticForm ℤ) (D : ℤ)
    (hD0 : D < 0) (hf : f.discrim = D) (hfprim : f.IsPrimitive) :
    (f.complexOrderIdeal D hD0.le hf).leftOrder =
      QuadraticOrder.complexOrder D hD0.le (hf ▸ f.discrim_emod_four_eq_zero_or_one) :=
  (leftOrder_complexOrderIdeal_eq_complexOrder_iff_isPrimitive f D hD0 hf).mpr hfprim

end NegDiscrim

end TauCeti.BinaryQuadraticForm
