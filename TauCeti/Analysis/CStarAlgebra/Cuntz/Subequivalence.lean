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

CStarClassification CL4.1. For elements `a, b` of a C⋆-algebra `A`, `a` is **Cuntz subequivalent**
to `b`, `TauCeti.CuntzLE a b`, if there are `xₙ ∈ A` with `xₙ⋆ b xₙ → a` in norm (Rørdam, §4.1).
We define it as membership of `a` in the closure of `{x⋆ b x : x ∈ A}` and prove the sequential
form (`TauCeti.cuntzLE_iff_exists_tendsto`). The relation is written out rather than given an
order notation: it is not the spectral order on positive elements. Mutual subequivalence is
`AntisymmRel CuntzLE`.

* It is a preorder (`TauCeti.CuntzLE.refl`, `TauCeti.CuntzLE.trans`): reflexivity uses the
  compressions `e a e → a` along an increasing approximate unit, and transitivity holds because
  `x⋆ (y⋆ c y) x = (yx)⋆ c (yx)`, so `{x⋆ b x}` lies in the closure of `{y⋆ c y}` once `b` does.
* Star homomorphisms preserve it (`TauCeti.CuntzLE.map`).
* Only `0` is subequivalent to `0` (`TauCeti.cuntzLE_zero_right_iff`).
* The cutdowns `(a - ε)₊ = cfcₙ (fun t ↦ max (t - ε) 0) a` satisfy
  `(a - ε)₊ ≼ a` (`TauCeti.cuntzLE_cfcₙ_sub_posPart`): `(a - ε)₊ = x⋆ a x` for
  `x = cfcₙ (fun t ↦ √(max (t - ε) 0 / t)) a`.

The Check that in `ℂ` all nonzero positive scalars are mutually subequivalent, `1 ≼ 2` and `2 ≼ 1`,
is `TauCeti.antisymmRel_cuntzLE_one_two`.

## References

* Rørdam, Part I of Rørdam–Størmer, *Classification of Nuclear C*-Algebras. Entropy in Operator
  Algebras*, Encyclopaedia of Mathematical Sciences 126, Springer, 2002, §4.1.
-/

public section

open Filter Topology
open scoped CStarAlgebra ComplexOrder

namespace TauCeti

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- **Cuntz subequivalence** `a ≼ b`: `a` is a norm limit of elements `x⋆ b x` (Rørdam, §4.1). -/
def CuntzLE (a b : A) : Prop :=
  a ∈ closure (Set.range fun x : A ↦ star x * b * x)

theorem cuntzLE_def {a b : A} :
    CuntzLE a b ↔ a ∈ closure (Set.range fun x : A ↦ star x * b * x) :=
  Iff.rfl

/-- The sequential form of Cuntz subequivalence: `a ≼ b` iff `xₙ⋆ b xₙ → a` for some sequence. -/
theorem cuntzLE_iff_exists_tendsto {a b : A} :
    CuntzLE a b ↔ ∃ x : ℕ → A, Tendsto (fun n ↦ star (x n) * b * x n) atTop (𝓝 a) := by
  rw [cuntzLE_def, mem_closure_iff_seq_limit]
  constructor
  · rintro ⟨y, hy, hya⟩
    choose x hx using hy
    exact ⟨x, by simpa [hx] using hya⟩
  · rintro ⟨x, hx⟩
    exact ⟨_, fun n ↦ ⟨x n, rfl⟩, hx⟩

theorem cuntzLE_star_mul_mul (x b : A) : CuntzLE (star x * b * x) b :=
  subset_closure ⟨x, rfl⟩

/-- Cuntz subequivalence is reflexive: `e a e → a` along an increasing approximate unit of the
spectral order. -/
@[refl]
theorem CuntzLE.refl (a : A) : CuntzLE a a := by
  let := CStarAlgebra.spectralOrder A
  have := CStarAlgebra.spectralOrderedRing A
  have hl := CStarAlgebra.increasingApproximateUnit (A := A)
  have : Tendsto (fun e ↦ star e * a * e) (CStarAlgebra.approximateUnit A) (𝓝 a) :=
    (hl.tendsto_mul_self a).congr' <| hl.eventually_star_eq.mono fun e he ↦ by
      change e * a * e = star e * a * e
      rw [he]
  have hne := hl.neBot
  exact mem_closure_of_tendsto this (.of_forall fun e ↦ ⟨e, rfl⟩)

/-- The set `{x⋆ b x}` lies in the closure of `{y⋆ c y}` once `b` does. -/
theorem CuntzLE.star_mul_mul {b c : A} (h : CuntzLE b c) (x : A) :
    CuntzLE (star x * b * x) c := by
  have hcont : Continuous fun z : A ↦ star x * z * x := by fun_prop
  have h1 : star x * b * x ∈ closure ((fun z : A ↦ star x * z * x) ''
      Set.range fun y : A ↦ star y * c * y) :=
    map_mem_closure (f := fun z : A ↦ star x * z * x) hcont h (Set.mapsTo_image _ _)
  refine closure_mono ?_ h1
  rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
  exact ⟨y * x, by simp [star_mul, mul_assoc]⟩

/-- Cuntz subequivalence is transitive. -/
theorem CuntzLE.trans {a b c : A} (hab : CuntzLE a b) (hbc : CuntzLE b c) : CuntzLE a c := by
  rw [cuntzLE_def] at hab ⊢
  refine closure_minimal ?_ isClosed_closure hab
  rintro _ ⟨x, rfl⟩
  exact hbc.star_mul_mul x

instance : IsPreorder A CuntzLE where
  refl := CuntzLE.refl
  trans _ _ _ := CuntzLE.trans

/-- Star homomorphisms preserve Cuntz subequivalence. -/
theorem CuntzLE.map {a b : A} (h : CuntzLE a b) (φ : A →⋆ₙₐ[ℂ] B) : CuntzLE (φ a) (φ b) := by
  have h1 : φ a ∈ closure (φ '' Set.range fun x : A ↦ star x * b * x) :=
    map_mem_closure (map_continuous φ) h (Set.mapsTo_image _ _)
  refine closure_mono ?_ h1
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  exact ⟨φ x, by simp [map_star]⟩

/-- Only `0` is Cuntz subequivalent to `0`. -/
@[simp]
theorem cuntzLE_zero_right_iff {a : A} : CuntzLE a 0 ↔ a = 0 := by
  have : (Set.range fun x : A ↦ star x * 0 * x) = {0} := by
    ext
    simp
  rw [cuntzLE_def, this, closure_singleton, Set.mem_singleton_iff]

/-- `0` is Cuntz subequivalent to every element. -/
@[simp]
theorem cuntzLE_zero_left (b : A) : CuntzLE 0 b := by
  simpa using cuntzLE_star_mul_mul 0 b

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

/-- **Cutdown**: for `ε > 0`, `(a - ε)₊ ≼ a`, where
`(a - ε)₊ = cfcₙ (fun t ↦ max (t - ε) 0) a`. -/
theorem cuntzLE_cfcₙ_sub_posPart (a : A) {ε : ℝ} (hε : 0 < ε) :
    CuntzLE (cfcₙ (fun t : ℝ ↦ max (t - ε) 0) a) a := by
  by_cases ha : IsSelfAdjoint a
  swap
  · rw [cfcₙ_apply_of_not_predicate a ha]
    exact cuntzLE_zero_left a
  have hc := continuous_cutdownRoot hε
  have h0 : cutdownRoot ε 0 = 0 := by simp [cutdownRoot]
  have hx : IsSelfAdjoint (cfcₙ (cutdownRoot ε) a) := cfcₙ_predicate _ a
  have hprod : cfcₙ (fun t ↦ cutdownRoot ε t * t * cutdownRoot ε t) a =
      cfcₙ (cutdownRoot ε) a * a * cfcₙ (cutdownRoot ε) a := by
    rw [cfcₙ_mul (fun t ↦ cutdownRoot ε t * t) (cutdownRoot ε) a (hf := by fun_prop)
      (hf0 := by simp [h0]), cfcₙ_mul (cutdownRoot ε) (fun t ↦ t) a, cfcₙ_id' ℝ a]
  convert cuntzLE_star_mul_mul (cfcₙ (cutdownRoot ε) a) a using 1
  rw [hx.star_eq, ← hprod]
  exact cfcₙ_congr fun t _ ↦ (cutdownRoot_sq_mul hε.le t).symm

/-- In `ℂ`, `1` and `2` are mutually Cuntz subequivalent: `1 = (1/√2) 2 (1/√2)` and `2 = √2 1 √2`.
Mutual subequivalence identifies the nonzero positive scalars and is coarser than equality. -/
theorem antisymmRel_cuntzLE_one_two : AntisymmRel CuntzLE (1 : ℂ) 2 := by
  have h2 : ((√2 : ℝ) : ℂ) * √2 = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt zero_le_two, Complex.ofReal_ofNat]
  have hne : ((√2 : ℝ) : ℂ) ≠ 0 := by simp
  refine ⟨?_, ?_⟩
  · convert cuntzLE_star_mul_mul (((√2 : ℝ) : ℂ)⁻¹) (2 : ℂ) using 1
    simp only [star_inv₀, Complex.star_def, Complex.conj_ofReal]
    field_simp
    rw [sq, h2]
  · convert cuntzLE_star_mul_mul (((√2 : ℝ) : ℂ)) (1 : ℂ) using 1
    simp only [Complex.star_def, Complex.conj_ofReal, mul_one]
    exact h2.symm

end TauCeti
