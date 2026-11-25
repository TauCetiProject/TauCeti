/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.Analysis.CStarAlgebra.ApproximateUnit

/-!
# Cuntz subequivalence

CStarClassification CL4.1. For positive elements `a, b` of a C⋆-algebra `A`, `a` is **Cuntz
subequivalent** to `b`, `TauCeti.CuntzLE a b`, if there are `xₙ ∈ A` with `xₙ⋆ b xₙ → a` in norm
(Rørdam, §4.1). The relation lives on the positive-element subtype `{a : A // 0 ≤ a}`; we define it
as membership of `a` in the closure of `{x⋆ b x : x ∈ A}` and prove the sequential form
(`TauCeti.cuntzLE_iff_exists_tendsto`). The relation is written out rather than given an order
notation: it is not the order on positive elements. Mutual subequivalence is
`AntisymmRel CuntzLE`.

* It is a preorder (`TauCeti.CuntzLE.refl`, `TauCeti.CuntzLE.trans`): reflexivity uses the
  compressions `e a e → a` along an increasing approximate unit, and transitivity holds because
  `x⋆ (y⋆ c y) x = (yx)⋆ c (yx)`, so `{x⋆ b x}` lies in the closure of `{y⋆ c y}` once `b` does.
* Star homomorphisms preserve it (`TauCeti.CuntzLE.map`).
* Only `0` is subequivalent to `0` (`TauCeti.cuntzLE_zero_right_iff`).
* The cutdowns `(a - ε)₊ = cfcₙ (fun t ↦ max (t - ε) 0) a` satisfy
  `(a - ε)₊ ≼ a` (`TauCeti.cuntzLE_cfcₙ_sub_posPart`): `(a - ε)₊ = x⋆ a x` for
  `x = cfcₙ (fun t ↦ √(max (t - ε) 0 / t)) a`.

The Check that in `ℂ` the positive scalars `1` and `2` are mutually subequivalent, `1 ≼ 2` and
`2 ≼ 1`, is `TauCeti.antisymmRel_cuntzLE_one_two`.

## References

* Rørdam, Part I of Rørdam–Størmer, *Classification of Nuclear C*-Algebras. Entropy in Operator
  Algebras*, Encyclopaedia of Mathematical Sciences 126, Springer, 2002, §4.1.
-/

public section

open Filter Topology
open scoped CStarAlgebra ComplexOrder

namespace TauCeti

variable {A B : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]

/-- **Cuntz subequivalence** `a ≼ b` of positive elements: `a` is a norm limit of elements
`x⋆ b x` (Rørdam, §4.1). -/
def CuntzLE (a b : {a : A // 0 ≤ a}) : Prop :=
  (a : A) ∈ closure (Set.range fun x : A ↦ star x * b * x)

theorem cuntzLE_def {a b : {a : A // 0 ≤ a}} :
    CuntzLE a b ↔ (a : A) ∈ closure (Set.range fun x : A ↦ star x * b * x) :=
  Iff.rfl

/-- The sequential form of Cuntz subequivalence: `a ≼ b` iff `xₙ⋆ b xₙ → a` for some sequence. -/
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
  have : (Set.range fun x : A ↦ star x * ((0 : {a : A // 0 ≤ a}) : A) * x) = {0} := by
    ext
    simp
  rw [cuntzLE_def, this, closure_singleton, Set.mem_singleton_iff, ← Subtype.val_inj,
    Nonneg.coe_zero]

variable [StarOrderedRing A] [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

theorem cuntzLE_star_mul_mul (x : A) (b : {a : A // 0 ≤ a}) :
    CuntzLE ⟨star x * b * x, star_left_conjugate_nonneg b.property x⟩ b :=
  subset_closure ⟨x, rfl⟩

/-- Cuntz subequivalence is reflexive: `e a e → a` along an increasing approximate unit. -/
@[refl]
theorem CuntzLE.refl (a : {a : A // 0 ≤ a}) : CuntzLE a a := by
  have hl := CStarAlgebra.increasingApproximateUnit (A := A)
  have : Tendsto (fun e ↦ star e * (a : A) * e) (CStarAlgebra.approximateUnit A) (𝓝 (a : A)) :=
    (hl.tendsto_mul_self (a : A)).congr' <| hl.eventually_star_eq.mono fun e he ↦ by
      change e * (a : A) * e = star e * (a : A) * e
      rw [he]
  have hne := hl.neBot
  exact mem_closure_of_tendsto this (.of_forall fun e ↦ ⟨e, rfl⟩)

/-- The set `{x⋆ b x}` lies in the closure of `{y⋆ c y}` once `b` does. -/
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
theorem CuntzLE.map {a b : {a : A // 0 ≤ a}} (h : CuntzLE a b) (φ : A →⋆ₙₐ[ℂ] B) :
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
noncomputable def cutdownRoot (ε : ℝ) (t : ℝ) : ℝ :=
  √(max (t - ε) 0 / t)

theorem continuous_cutdownRoot {ε : ℝ} (hε : 0 < ε) : Continuous (cutdownRoot ε) := by
  refine continuous_iff_continuousAt.mpr fun t ↦ ?_
  rcases lt_or_ge t ε with ht | ht
  · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [Iio_mem_nhds ht] with s hs
    simp [cutdownRoot, max_eq_right (sub_nonpos.mpr (le_of_lt hs))]
  · have ht0 : t ≠ 0 := (hε.trans_le ht).ne'
    unfold cutdownRoot
    fun_prop (disch := assumption)

theorem cutdownRoot_sq_mul {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ) :
    cutdownRoot ε t * t * cutdownRoot ε t = max (t - ε) 0 := by
  rcases eq_or_ne t 0 with rfl | ht
  · simp [cutdownRoot, hε]
  rcases le_or_gt t ε with htε | htε
  · simp [cutdownRoot, max_eq_right (sub_nonpos.mpr htε)]
  · have hpos : 0 ≤ max (t - ε) 0 / t := by
      rw [max_eq_left (sub_nonneg.mpr htε.le)]
      exact div_nonneg (sub_nonneg.mpr htε.le) (by linarith)
    rw [cutdownRoot, mul_comm _ t, mul_assoc, Real.mul_self_sqrt hpos, mul_div_cancel₀ _ ht]

/-- **Cutdown**: for positive `a` and `ε > 0`, `(a - ε)₊ ≼ a`, where
`(a - ε)₊ = cfcₙ (fun t ↦ max (t - ε) 0) a`. -/
theorem cuntzLE_cfcₙ_sub_posPart (a : {a : A // 0 ≤ a}) {ε : ℝ} (hε : 0 < ε) :
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
  exact cfcₙ_congr fun t _ ↦ (cutdownRoot_sq_mul hε.le t).symm

/-- In `ℂ`, the positive scalars `1` and `2` are mutually Cuntz subequivalent:
`1 = (1/√2) 2 (1/√2)` and `2 = √2 1 √2`. So mutual subequivalence is coarser than equality. -/
theorem antisymmRel_cuntzLE_one_two :
    AntisymmRel CuntzLE (⟨1, zero_le_one⟩ : {z : ℂ // 0 ≤ z}) ⟨2, zero_le_two⟩ := by
  have h2 : ((√2 : ℝ) : ℂ) * √2 = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt zero_le_two, Complex.ofReal_ofNat]
  have hne : ((√2 : ℝ) : ℂ) ≠ 0 := by simp
  refine ⟨?_, ?_⟩
  · convert cuntzLE_star_mul_mul (((√2 : ℝ) : ℂ)⁻¹) ⟨2, zero_le_two⟩ using 2
    simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal]
    field_simp
    rw [sq, h2]
  · convert cuntzLE_star_mul_mul (((√2 : ℝ) : ℂ)) ⟨1, zero_le_one⟩ using 2
    simp only [Complex.star_def, Complex.conj_ofReal, mul_one]
    exact h2.symm

end TauCeti
