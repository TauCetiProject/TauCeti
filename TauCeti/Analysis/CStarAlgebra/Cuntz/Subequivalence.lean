/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import TauCeti.Analysis.CStarAlgebra.ApproximateUnit
import TauCeti.Analysis.Real.Sqrt

/-!
# Cuntz subequivalence

For positive elements `a, b` of a C⋆-algebra `A`, `a` is **Cuntz subequivalent** to `b`,
`TauCeti.CuntzLE a b`, if there are `xₙ ∈ A` with `xₙ⋆ b xₙ → a` in norm (Rørdam, §4.1). The
relation lives on the positive-element subtype `{a : A // 0 ≤ a}`; we define it as membership of
`a` in the closure of `{x⋆ b x : x ∈ A}` and prove the sequential form
(`TauCeti.cuntzLE_iff_exists_tendsto`). Below, `a ≼ b` is informal shorthand for `CuntzLE a b`;
no Lean notation is defined, since the relation is not the order on positive elements. Mutual
subequivalence is `AntisymmRel CuntzLE`.

* It is a preorder (`TauCeti.CuntzLE.refl`, `TauCeti.CuntzLE.trans`): reflexivity uses the
  compressions `e a e → a` along an increasing approximate unit, and transitivity holds because
  `x⋆ (y⋆ c y) x = (yx)⋆ c (yx)`, so `{x⋆ b x}` lies in the closure of `{y⋆ c y}` once `b` does.
* Star homomorphisms preserve it (`TauCeti.CuntzLE.map`).
* Only `0` is subequivalent to `0` (`TauCeti.cuntzLE_zero_right_iff`).
* The cutdowns `(a - ε)₊ = cfcₙ (fun t ↦ max (t - ε) 0) a` satisfy
  `(a - ε)₊ ≼ a` (`TauCeti.cuntzLE_cfcₙ_max_sub_zero`): `(a - ε)₊ = x⋆ a x` for
  `x = cfcₙ (fun t ↦ √(max (t - ε) 0 / t)) a`.

In `ℂ`, `a ≼ b` holds exactly when `b ≠ 0` or `a = 0` (`TauCeti.cuntzLE_complex_iff`), so all
nonzero positive scalars are mutually subequivalent (`TauCeti.antisymmRel_cuntzLE_complex`); for
instance `1` and `2` are mutually subequivalent (`TauCeti.antisymmRel_cuntzLE_one_two`).

## References

* Rørdam, Part I of Rørdam–Størmer, *Classification of Nuclear C*-Algebras. Entropy in Operator
  Algebras*, Encyclopaedia of Mathematical Sciences 126, Springer, 2002, §4.1.
-/

public section

open Filter Topology
open scoped CStarAlgebra ComplexOrder

namespace TauCeti

variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]

/-- **Cuntz subequivalence** `CuntzLE a b` of positive elements: `a` is a norm limit of elements
`x⋆ b x` (Rørdam, §4.1). -/
def CuntzLE (a b : {a : A // 0 ≤ a}) : Prop :=
  (a : A) ∈ closure (Set.range fun x : A ↦ star x * b * x)

theorem cuntzLE_def {a b : {a : A // 0 ≤ a}} :
    CuntzLE a b ↔ (a : A) ∈ closure (Set.range fun x : A ↦ star x * b * x) :=
  Iff.rfl

/-- The sequential form of Cuntz subequivalence: `CuntzLE a b` iff `xₙ⋆ b xₙ → a` for some
sequence. -/
theorem cuntzLE_iff_exists_tendsto {a b : {a : A // 0 ≤ a}} :
    CuntzLE a b ↔ ∃ x : ℕ → A, Tendsto (fun n ↦ star (x n) * b * x n) atTop (𝓝 (a : A)) := by
  rw [cuntzLE_def, mem_closure_iff_seq_limit]
  constructor
  · rintro ⟨y, hy, hya⟩
    choose x hx using hy
    exact ⟨x, by simpa [hx] using hya⟩
  · rintro ⟨x, hx⟩
    exact ⟨_, fun n ↦ ⟨x n, rfl⟩, hx⟩

/-- Only `0` is Cuntz subequivalent to `0`. -/
@[simp]
theorem cuntzLE_zero_right_iff {a : {a : A // 0 ≤ a}} : CuntzLE a 0 ↔ a = 0 := by
  simp [cuntzLE_def, Subtype.ext_iff]

variable [StarOrderedRing A] [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- For positive `b` and any `x`, the compression `x⋆ b x` is Cuntz subequivalent to `b`. -/
theorem cuntzLE_star_mul_mul (x : A) (b : {a : A // 0 ≤ a}) :
    CuntzLE ⟨star x * b * x, star_left_conjugate_nonneg b.property x⟩ b :=
  subset_closure ⟨x, rfl⟩

/-- Every positive element is Cuntz subequivalent to itself. -/
@[refl]
theorem CuntzLE.refl (a : {a : A // 0 ≤ a}) : CuntzLE a a := by
  have hl := CStarAlgebra.increasingApproximateUnit (A := A)
  have : Tendsto (fun e ↦ star e * (a : A) * e) (CStarAlgebra.approximateUnit A) (𝓝 (a : A)) :=
    (hl.tendsto_mul_self (a : A)).congr' <| hl.eventually_star_eq.mono fun e he ↦ by
      simp only [he]
  exact mem_closure_of_tendsto this (.of_forall fun e ↦ ⟨e, rfl⟩)

/-- If `b` is Cuntz subequivalent to `c`, so is every compression `x⋆ b x`. -/
theorem CuntzLE.star_mul_mul {b c : {a : A // 0 ≤ a}} (h : CuntzLE b c) (x : A) :
    CuntzLE ⟨star x * b * x, star_left_conjugate_nonneg b.property x⟩ c := by
  have hcont : Continuous fun z : A ↦ star x * z * x := by fun_prop
  have h1 : star x * (b : A) * x ∈ closure ((fun z : A ↦ star x * z * x) ''
      Set.range fun y : A ↦ star y * c * y) :=
    map_mem_closure (f := fun z : A ↦ star x * z * x) hcont h (Set.mapsTo_image _ _)
  refine closure_mono ?_ h1
  rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
  exact ⟨y * x, by simp [star_mul, mul_assoc]⟩

/-- Cuntz subequivalence is transitive. -/
theorem CuntzLE.trans {a b c : {a : A // 0 ≤ a}} (hab : CuntzLE a b) (hbc : CuntzLE b c) :
    CuntzLE a c := by
  rw [cuntzLE_def] at hab ⊢
  refine closure_minimal ?_ isClosed_closure hab
  rintro _ ⟨x, rfl⟩
  exact hbc.star_mul_mul x

instance : IsPreorder {a : A // 0 ≤ a} CuntzLE where
  refl := CuntzLE.refl
  trans _ _ _ := CuntzLE.trans

/-- Star homomorphisms preserve Cuntz subequivalence. -/
theorem CuntzLE.map {F : Type*} [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B]
    [StarHomClass F A B] {a b : {a : A // 0 ≤ a}} (h : CuntzLE a b) (φ : F) :
    CuntzLE ⟨φ a, map_nonneg φ a.property⟩ ⟨φ b, map_nonneg φ b.property⟩ := by
  have h1 : φ a ∈ closure (φ '' Set.range fun x : A ↦ star x * b * x) :=
    map_mem_closure (map_continuous φ) h (Set.mapsTo_image _ _)
  refine closure_mono ?_ h1
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  exact ⟨φ x, by simp [map_star]⟩

/-- `0` is Cuntz subequivalent to every positive element. -/
@[simp]
theorem cuntzLE_zero_left (b : {a : A // 0 ≤ a}) : CuntzLE 0 b := by
  convert cuntzLE_star_mul_mul 0 b
  simp

/-- The function `t ↦ √(max (t - ε) 0 / t)` used to realize the cutdown `(a - ε)₊` as `x⋆ a x`;
it vanishes on `t < ε`. -/
private noncomputable def cutdownRoot (ε : ℝ) (t : ℝ) : ℝ :=
  √(max (t - ε) 0 / t)

private theorem continuous_cutdownRoot {ε : ℝ} (hε : 0 < ε) : Continuous (cutdownRoot ε) := by
  refine continuous_iff_continuousAt.mpr fun t ↦ ?_
  rcases lt_or_ge t ε with ht | ht
  · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [Iio_mem_nhds ht] with s hs
    simp [cutdownRoot, max_eq_right (sub_nonpos.mpr (le_of_lt hs))]
  · have ht0 : t ≠ 0 := (hε.trans_le ht).ne'
    unfold cutdownRoot
    fun_prop (disch := assumption)

private theorem cutdownRoot_mul_mul_cutdownRoot {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    cutdownRoot ε t * t * cutdownRoot ε t = max (t - ε) 0 := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [cutdownRoot, hε]
  rcases le_or_gt t ε with htε | htε
  · simp [cutdownRoot, max_eq_right (sub_nonpos.mpr htε)]
  · have hpos : 0 ≤ (t - ε) / t := div_nonneg (by linarith) (by linarith)
    simp only [cutdownRoot, max_eq_left (sub_nonneg.mpr htε.le)]
    exact Real.sqrt_div_mul_mul_sqrt_div hpos ht

/-- **Cutdown**: for positive `a` and `ε > 0`, the cutdown
`(a - ε)₊ = cfcₙ (fun t ↦ max (t - ε) 0) a` is Cuntz subequivalent to `a`. -/
theorem cuntzLE_cfcₙ_max_sub_zero (a : {a : A // 0 ≤ a}) {ε : ℝ} (hε : 0 < ε) :
    CuntzLE ⟨cfcₙ (fun t : ℝ ↦ max (t - ε) 0) (a : A), cfcₙ_nonneg fun _ _ ↦ le_max_right _ _⟩
      a := by
  have hc := continuous_cutdownRoot hε
  have h0 : cutdownRoot ε 0 = 0 := by simp [cutdownRoot]
  have hx : IsSelfAdjoint (cfcₙ (cutdownRoot ε) (a : A)) := cfcₙ_predicate _ _
  have hprod : cfcₙ (fun t ↦ cutdownRoot ε t * t * cutdownRoot ε t) (a : A) =
      cfcₙ (cutdownRoot ε) (a : A) * a * cfcₙ (cutdownRoot ε) (a : A) := by
    rw [cfcₙ_mul (fun t ↦ cutdownRoot ε t * t) (cutdownRoot ε) (a : A) (hf := by fun_prop)
      (hf0 := by simp [h0]), cfcₙ_mul (cutdownRoot ε) (fun t ↦ t) (a : A), cfcₙ_id' ℝ (a : A)]
  convert cuntzLE_star_mul_mul (cfcₙ (cutdownRoot ε) (a : A)) a using 2
  rw [hx.star_eq, ← hprod]
  exact cfcₙ_congr fun t _ ↦ (cutdownRoot_mul_mul_cutdownRoot hε.le t).symm

/-- In `ℂ`, a positive scalar `a` is Cuntz subequivalent to a positive scalar `b` exactly when
`b ≠ 0` or `a = 0`. -/
theorem cuntzLE_complex_iff {a b : {z : ℂ // 0 ≤ z}} : CuntzLE a b ↔ (b : ℂ) ≠ 0 ∨ a = 0 := by
  rcases eq_or_ne (b : ℂ) 0 with hb | hb
  · obtain rfl : b = 0 := Subtype.ext hb
    simp
  refine iff_of_true ?_ (.inl hb)
  obtain ⟨r, hr, hra⟩ := RCLike.nonneg_iff_exists_ofReal.mp a.property
  obtain ⟨s, hs, hsb⟩ := RCLike.nonneg_iff_exists_ofReal.mp b.property
  have hs0 : s ≠ 0 := fun h ↦ hb (by simp [← hsb, h])
  convert cuntzLE_star_mul_mul (((√(r / s) : ℝ) : ℂ)) b using 2
  rw [← hra, ← hsb]
  simpa using congrArg Complex.ofReal (Real.sqrt_div_mul_mul_sqrt_div (div_nonneg hr hs) hs0).symm

/-- In `ℂ`, any two nonzero positive scalars are mutually Cuntz subequivalent. -/
theorem antisymmRel_cuntzLE_complex {a b : {z : ℂ // 0 ≤ z}} (ha : (a : ℂ) ≠ 0)
    (hb : (b : ℂ) ≠ 0) : AntisymmRel CuntzLE a b :=
  ⟨cuntzLE_complex_iff.mpr (.inl hb), cuntzLE_complex_iff.mpr (.inl ha)⟩

/-- In `ℂ`, the positive scalars `1` and `2` are mutually Cuntz subequivalent, so mutual
subequivalence is coarser than equality. -/
theorem antisymmRel_cuntzLE_one_two :
    AntisymmRel CuntzLE (⟨1, zero_le_one⟩ : {z : ℂ // 0 ≤ z}) ⟨2, zero_le_two⟩ :=
  antisymmRel_cuntzLE_complex one_ne_zero two_ne_zero

end TauCeti
