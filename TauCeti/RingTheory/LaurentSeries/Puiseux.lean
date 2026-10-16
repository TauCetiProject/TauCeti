/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import TauCeti.RingTheory.LaurentSeries.Ramified

/-!
# The Puiseux series field

For a field `K`, the field of Puiseux series over `K` is the subfield of the rational-exponent
Hahn series field `HahnSeries ℚ K` consisting of the series whose exponents have a common
denominator: for some `n > 0`, every exponent in the support is of the form `k / n` with `k ∈ ℤ`.
Equivalently, it is the union of the ramified levels `K⸨t ^ (1 / n)⸩`, the images of the
embeddings `LaurentSeries.ramifiedEmbedding K n : K⸨X⸩ → HahnSeries ℚ K`, which form a directed
system under divisibility of `n`.

This file constructs the Puiseux field as an intermediate field of `HahnSeries ℚ K` over `K`,
proves that it is the union of the levels, and that any finite family of Puiseux series, in
particular the coefficients of a polynomial, lies in a single common level. The Laurent series
field `K⸨X⸩` acts on it through the level-one embedding `X ↦ t`, and every level embedding is
compatible with this action after the expansion `X ↦ X ^ n`. In characteristic zero with `K`
algebraically closed the Puiseux field is an algebraic closure of `K⸨X⸩` (the Newton–Puiseux
theorem); the common-level lift of polynomial coefficients is what reduces root finding over the
Puiseux field to a single level.

## Main definitions

* `TauCeti.puiseuxField K`: the Puiseux series field, as an `IntermediateField K (HahnSeries ℚ K)`.
* `TauCeti.puiseuxField.levelEmbedding K n`: the level-`n` embedding `K⸨X⸩ →ₐ[K] puiseuxField K`,
  `X ↦ t ^ (1 / n)`.
* The `K⸨X⸩`-algebra structure on `puiseuxField K` given by `levelEmbedding K 1`, with
  `IsScalarTower K K⸨X⸩ (puiseuxField K)`.

## Main results

* `TauCeti.mem_puiseuxField_iff`: a Hahn series is a Puiseux series exactly when it lies in some
  level.
* `TauCeti.mem_puiseuxField_iff_exists_den_dvd`: a Hahn series is a Puiseux series exactly when
  the denominators of its exponents are bounded in divisibility by a single `n`.
* `TauCeti.puiseuxField_eq_iSup_fieldRange`: the Puiseux field is the supremum of the levels.
* `TauCeti.puiseuxField.exists_forall_mem_range_levelEmbedding`: a finite family of Puiseux series
  lies in a common level.
* `TauCeti.puiseuxField.exists_map_levelEmbedding_eq`: every polynomial over the Puiseux field is
  the image of a polynomial over `K⸨X⸩` under a single level embedding.
* `TauCeti.puiseuxField.levelEmbedding_expand_self`: the level-`n` embedding restricted along
  `X ↦ X ^ n` is the `K⸨X⸩`-algebra map.
-/

public section

open HahnSeries LaurentSeries Polynomial
open scoped LaurentSeries

namespace TauCeti

variable (K : Type*) [Field K]

/-- The **Puiseux series field** over `K`: the Hahn series with rational exponents whose exponents
have a common denominator, that is, the union of the ramified levels `K⸨t ^ (1 / n)⸩`. -/
noncomputable def puiseuxField : IntermediateField K (HahnSeries ℚ K) where
  carrier := {x | ∃ n : ℕ+, ∃ f, ramifiedEmbedding K n f = x}
  mul_mem' := by
    rintro _ _ ⟨n, f, rfl⟩ ⟨m, g, rfl⟩
    refine ⟨n * m, expand K m f * expand K n g, ?_⟩
    rw [map_mul, ramifiedEmbedding_expand, mul_comm n m, ramifiedEmbedding_expand]
  add_mem' := by
    rintro _ _ ⟨n, f, rfl⟩ ⟨m, g, rfl⟩
    refine ⟨n * m, expand K m f + expand K n g, ?_⟩
    rw [map_add, ramifiedEmbedding_expand, mul_comm n m, ramifiedEmbedding_expand]
  algebraMap_mem' r := ⟨1, algebraMap K K⸨X⸩ r, AlgHom.commutes _ r⟩
  inv_mem' := by
    rintro _ ⟨n, f, rfl⟩
    exact ⟨n, f⁻¹, map_inv₀ _ f⟩

variable {K}

/-- A Hahn series is a Puiseux series exactly when it lies in the level-`n` image
`K⸨t ^ (1 / n)⸩` for some `n`. -/
theorem mem_puiseuxField_iff {x : HahnSeries ℚ K} :
    x ∈ puiseuxField K ↔ ∃ n : ℕ+, x ∈ (ramifiedEmbedding K n).range := by
  simp only [AlgHom.mem_range]
  exact Iff.rfl

/-- A Hahn series is a Puiseux series exactly when the denominators of all of its exponents divide
a single positive integer `n`. -/
theorem mem_puiseuxField_iff_exists_den_dvd {x : HahnSeries ℚ K} :
    x ∈ puiseuxField K ↔ ∃ n : ℕ+, ∀ q ∈ x.support, q.den ∣ n := by
  simp only [mem_puiseuxField_iff, mem_range_ramifiedEmbedding_iff]

/-- The level-`n` image of a Laurent series is a Puiseux series. -/
@[simp]
theorem ramifiedEmbedding_mem_puiseuxField (n : ℕ+) (f : K⸨X⸩) :
    ramifiedEmbedding K n f ∈ puiseuxField K :=
  ⟨n, f, rfl⟩

/-- The monomial `a t ^ q` is a Puiseux series for every rational exponent `q`. -/
@[simp]
theorem single_mem_puiseuxField (q : ℚ) (a : K) : single q a ∈ puiseuxField K := by
  refine mem_puiseuxField_iff_exists_den_dvd.mpr ⟨⟨q.den, q.den_pos⟩, fun r hr ↦ ?_⟩
  rw [Set.eq_of_mem_singleton (support_single_subset hr)]
  rfl

/-- Each level `K⸨t ^ (1 / n)⸩` is contained in the Puiseux field. -/
theorem fieldRange_ramifiedEmbedding_le_puiseuxField (n : ℕ+) :
    (ramifiedEmbedding K n).fieldRange ≤ puiseuxField K := by
  rintro _ ⟨f, rfl⟩
  exact ramifiedEmbedding_mem_puiseuxField n f

/-- The levels `K⸨t ^ (1 / n)⸩` form a directed family of subfields under divisibility. -/
theorem directed_fieldRange_ramifiedEmbedding :
    Directed (· ≤ ·) fun n : ℕ+ ↦ (ramifiedEmbedding K n).fieldRange := fun n m ↦
  ⟨n * m, fun _ hx ↦ range_ramifiedEmbedding_le_of_dvd (dvd_mul_right n m) hx,
    fun _ hx ↦ range_ramifiedEmbedding_le_of_dvd (dvd_mul_left m n) hx⟩

/-- The Puiseux field is the supremum of the levels `K⸨t ^ (1 / n)⸩`. -/
theorem puiseuxField_eq_iSup_fieldRange :
    puiseuxField K = ⨆ n : ℕ+, (ramifiedEmbedding K n).fieldRange := by
  refine SetLike.coe_injective ?_
  rw [IntermediateField.coe_iSup_of_directed directed_fieldRange_ramifiedEmbedding]
  ext x
  simp [mem_puiseuxField_iff]

namespace puiseuxField

variable (K) in
/-- The level-`n` embedding `K⸨X⸩ → puiseuxField K`, substituting `X ↦ t ^ (1 / n)`. -/
noncomputable def levelEmbedding (n : ℕ+) : K⸨X⸩ →ₐ[K] puiseuxField K :=
  (ramifiedEmbedding K n).codRestrict (puiseuxField K).toSubalgebra
    (ramifiedEmbedding_mem_puiseuxField n)

/-- As a Hahn series, the level-`n` embedding of `f` is `ramifiedEmbedding K n f`. -/
@[simp]
theorem coe_levelEmbedding (n : ℕ+) (f : K⸨X⸩) :
    (levelEmbedding K n f : HahnSeries ℚ K) = ramifiedEmbedding K n f :=
  (rfl)

/-- The transition map `X ↦ X ^ d` from level `n` to level `n * d` commutes with the level
embeddings into the Puiseux field. -/
@[simp]
theorem levelEmbedding_expand (n d : ℕ+) (f : K⸨X⸩) :
    levelEmbedding K (n * d) (expand K d f) = levelEmbedding K n f :=
  Subtype.ext (ramifiedEmbedding_expand n d f)

/-- `levelEmbedding_expand` as an equality of algebra maps. -/
theorem levelEmbedding_comp_expand (n d : ℕ+) :
    (levelEmbedding K (n * d)).comp (expand K d) = levelEmbedding K n :=
  AlgHom.ext (levelEmbedding_expand n d)

/-- A Puiseux series lies in the image of the level-`n` embedding exactly when, as a Hahn series,
it lies in the level-`n` image `K⸨t ^ (1 / n)⸩`. -/
theorem mem_range_levelEmbedding_iff {n : ℕ+} {x : puiseuxField K} :
    x ∈ (levelEmbedding K n).range ↔ (x : HahnSeries ℚ K) ∈ (ramifiedEmbedding K n).range :=
  ⟨fun ⟨f, hf⟩ ↦ ⟨f, congrArg Subtype.val hf⟩, fun ⟨f, hf⟩ ↦ ⟨f, Subtype.ext hf⟩⟩

/-- Every Puiseux series lies in some level. -/
theorem exists_mem_range_levelEmbedding (x : puiseuxField K) :
    ∃ n : ℕ+, x ∈ (levelEmbedding K n).range := by
  simpa only [mem_range_levelEmbedding_iff] using mem_puiseuxField_iff.mp x.2

/-- For `n ∣ m`, the image of level `n` in the Puiseux field is contained in that of level `m`. -/
theorem range_levelEmbedding_le_of_dvd {n m : ℕ+} (h : n ∣ m) :
    (levelEmbedding K n).range ≤ (levelEmbedding K m).range := fun _ hx ↦
  mem_range_levelEmbedding_iff.mpr
    (range_ramifiedEmbedding_le_of_dvd h (mem_range_levelEmbedding_iff.mp hx))

/-- **Common level**: a finite family of Puiseux series lies in a single level. -/
theorem exists_forall_mem_range_levelEmbedding {ι : Type*} [Finite ι] (x : ι → puiseuxField K) :
    ∃ n : ℕ+, ∀ i, x i ∈ (levelEmbedding K n).range := by
  choose N hN using fun i ↦ exists_mem_range_levelEmbedding (x i)
  have := Fintype.ofFinite ι
  exact ⟨∏ i, N i, fun i ↦
    range_levelEmbedding_le_of_dvd (Finset.dvd_prod_of_mem N (Finset.mem_univ i)) (hN i)⟩

/-- **Common-level lift of polynomial coefficients**: every polynomial over the Puiseux field is
the image of a polynomial over `K⸨X⸩` under a single level embedding. -/
theorem exists_map_levelEmbedding_eq (p : (puiseuxField K)[X]) :
    ∃ n : ℕ+, ∃ q : K⸨X⸩[X], q.map (levelEmbedding K n : K⸨X⸩ →+* puiseuxField K) = p := by
  obtain ⟨n, hn⟩ := exists_forall_mem_range_levelEmbedding fun i : p.support ↦ p.coeff i
  refine ⟨n, (mem_lifts p).mp ((lifts_iff_coeff_lifts p).mpr fun i ↦ ?_)⟩
  by_cases hi : i ∈ p.support
  · exact hn ⟨i, hi⟩
  · rw [notMem_support_iff.mp hi]
    exact ⟨0, map_zero _⟩

/-- The Puiseux field is a `K⸨X⸩`-algebra through the level-one embedding `X ↦ t`. -/
noncomputable instance : Algebra K⸨X⸩ (puiseuxField K) :=
  (levelEmbedding K 1).toAlgebra

/-- The `K⸨X⸩`-algebra map to the Puiseux field is the level-one embedding. -/
theorem algebraMap_laurentSeries_apply (f : K⸨X⸩) :
    algebraMap K⸨X⸩ (puiseuxField K) f = levelEmbedding K 1 f :=
  (rfl)

/-- As a Hahn series, the image of `f` under the `K⸨X⸩`-algebra map is the level-one image
`ramifiedEmbedding K 1 f`. -/
@[simp]
theorem coe_algebraMap_laurentSeries (f : K⸨X⸩) :
    (algebraMap K⸨X⸩ (puiseuxField K) f : HahnSeries ℚ K) = ramifiedEmbedding K 1 f :=
  (rfl)

/-- The `K`-algebra structure on the Puiseux field factors through the `K⸨X⸩`-algebra
structure. -/
instance : IsScalarTower K K⸨X⸩ (puiseuxField K) where
  smul_assoc r f x := by
    -- `IsScalarTower.of_algHom` is stated for the scalar action `Algebra.toSMul` on `K⸨X⸩`,
    -- which agrees only propositionally with its coefficientwise action, so first switch to it.
    rw [← C_mul_eq_smul, ← LaurentSeries.algebraMap_apply, ← Algebra.smul_def]
    exact (IsScalarTower.of_algHom (levelEmbedding K 1)).smul_assoc r f x

/-- The level-`n` embedding restricted along the expansion `X ↦ X ^ n` is the `K⸨X⸩`-algebra
map: as a subfield of the Puiseux field, level `n` contains `K⸨X⸩` with `X` acting as
`t = (t ^ (1 / n)) ^ n`. -/
@[simp]
theorem levelEmbedding_expand_self (n : ℕ+) (f : K⸨X⸩) :
    levelEmbedding K n (expand K n f) = algebraMap K⸨X⸩ (puiseuxField K) f := by
  rw [algebraMap_laurentSeries_apply, ← levelEmbedding_expand 1 n, one_mul]

end puiseuxField

end TauCeti
