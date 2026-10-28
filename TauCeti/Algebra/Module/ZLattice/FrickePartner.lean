/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Level

/-!
# The Fricke partner of an even lattice

Let `L` be an even full lattice in a finite-dimensional real inner product space `E`, of rank `n`
and level `N = level L`. Its *Fricke partner* is the scaled dual lattice `√N • L^∨`. The Fricke
involution `τ ↦ -1 / (N τ)` exchanges the theta series of `L` and of `√N • L^∨`, which is why the
partner appears in the transformation law of `Θ_L` under the Fricke matrix `!![0, -1; N, 0]`.

This file proves that the Fricke partner is again an even lattice, that its determinant is
`Nⁿ / det L`, and computes its level. Since `(√N • L^∨)^∨ = (√N)⁻¹ • L`, an integer `K` is a
multiple of the level of the partner exactly when `N` divides `K ‖x‖² / 2` for every `x ∈ L`. So
the level is governed by the *content* `c_L` of `L`, the greatest common divisor of the half-norms
`‖x‖² / 2` of the vectors of `L` (`ZLattice.content`):
```text
level (√N • L^∨) = N / gcd (N, c_L).
```
In particular the level of the partner divides `N`, and it equals `N` exactly when no prime
dividing `N` divides every half-norm of `L`. Equality fails in general: the lattice `2 ℤ ⊆ ℝ` has
level `8` and content `2`, and its Fricke partner `√8 • ½ ℤ = √2 ℤ` has level `4`
(`ZLattice.level_sqrt_level_smul_dual_span_two`). Similarly `√2 • E₈` has level `2` and content
`2`, while its Fricke partner is `E₈`, of level `1`.

Like the level, the content is defined directly on the real model, for every lattice, so it needs
no integrality hypothesis to state. It is the half-norm counterpart of the norm ideal
`TauCeti.IntegralLattice.normIdeal` of a rational lattice, the ideal spanned by the full norms.

## Main definitions

* `ZLattice.content L`: the nonnegative generator of the ideal of `ℤ` spanned by the half-norms
  `‖x‖² / 2` of the vectors `x ∈ L` of even squared norm. For an even lattice this is the greatest
  common divisor of all its half-norms.

## Main statements

* `ZLattice.dvd_content_iff`: `d` divides the content exactly when it divides every half-norm.
* `ZLattice.isEven_sqrt_level_smul_dual`: the Fricke partner `√N • L^∨` is even, for every `L`.
* `ZLattice.IsIntegral.det_sqrt_level_smul_dual`: for a full integral lattice of rank `n`,
  `det (√N • L^∨) = Nⁿ / det L`.
* `ZLattice.IsEven.level_sqrt_level_smul_dual`: for an even full lattice,
  `level (√N • L^∨) = N / gcd (N, c_L)`.
* `ZLattice.IsEven.level_sqrt_level_smul_dual_dvd`: the level of the Fricke partner divides `N`.
* `ZLattice.IsEven.level_sqrt_level_smul_dual_eq_level_iff`: it equals `N` exactly when `N` is
  coprime to the content.

## References

* W. Ebeling, *Lattices and Codes*, 3rd ed., Springer, 2013, Chapter 3.
* H. Iwaniec, *Topics in Classical Automorphic Forms*, AMS, 1997, Chapter 10.
-/

public section

open Module Submodule
open scoped Pointwise RealInnerProductSpace

namespace ZLattice

/-! ### The content of a lattice -/

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E]

/-- The ideal of `ℤ` spanned by the half-norms `‖x‖² / 2` of the vectors `x ∈ L` of even squared
norm. Its nonnegative generator is the content. -/
private def halfNormIdeal (L : Submodule ℤ E) : Ideal ℤ :=
  Ideal.span {m : ℤ | ∃ x ∈ L, ‖x‖ ^ 2 = 2 * m}

/-- The **content** of a lattice `L`: the nonnegative generator of the ideal of `ℤ` spanned by the
half-norms `‖x‖² / 2` of the vectors `x ∈ L` whose squared norm is an even integer. For an even
lattice every vector qualifies, and the content is the greatest common divisor of all half-norms
of `L` (`dvd_content_iff`). -/
noncomputable def content (L : Submodule ℤ E) : ℕ :=
  (Submodule.IsPrincipal.generator (halfNormIdeal L)).natAbs

variable {L : Submodule ℤ E}

/-- The content is an integer combination of half-norms: it lies in the ideal they span. -/
private theorem natCast_content_mem_halfNormIdeal : (content L : ℤ) ∈ halfNormIdeal L := by
  rw [content, Int.natCast_natAbs]
  rcases abs_choice (Submodule.IsPrincipal.generator (halfNormIdeal L)) with h | h <;> rw [h]
  · exact Submodule.IsPrincipal.generator_mem _
  · exact neg_mem (Submodule.IsPrincipal.generator_mem _)

/-- `d` divides the content of `L` exactly when `d` divides every half-norm `‖x‖² / 2` of a vector
`x ∈ L` of even squared norm. -/
theorem dvd_content_iff {d : ℤ} :
    d ∣ content L ↔ ∀ x ∈ L, ∀ m : ℤ, ‖x‖ ^ 2 = 2 * m → d ∣ m := by
  rw [content, Int.natCast_natAbs, dvd_abs, ← Ideal.span_singleton_le_span_singleton,
    Ideal.span, Submodule.IsPrincipal.span_singleton_generator, halfNormIdeal, Ideal.span_le]
  refine ⟨fun h x hx m hm ↦ ?_, fun h m ⟨x, hx, hm⟩ ↦ ?_⟩
  · exact Ideal.mem_span_singleton.mp (h ⟨x, hx, hm⟩)
  · exact Ideal.mem_span_singleton.mpr (h x hx m hm)

/-- The content of `L` divides every half-norm `‖x‖² / 2` of a vector `x ∈ L` of even squared
norm. -/
theorem content_dvd {x : E} (hx : x ∈ L) {m : ℤ} (hm : ‖x‖ ^ 2 = 2 * m) : (content L : ℤ) ∣ m :=
  dvd_content_iff.mp dvd_rfl x hx m hm

/-- If `n` divides `k` times every half-norm of `L`, then it divides `k` times the content. -/
private theorem dvd_mul_content {n k : ℤ} (h : ∀ x ∈ L, ∀ m : ℤ, ‖x‖ ^ 2 = 2 * m → n ∣ k * m) :
    n ∣ k * content L := by
  refine Submodule.span_induction (p := fun z _ ↦ n ∣ k * z) ?_ ?_ ?_ ?_
    (natCast_content_mem_halfNormIdeal (L := L))
  · rintro m ⟨x, hx, hm⟩
    exact h x hx m hm
  · simp
  · intro a b _ _ ha hb
    simpa [mul_add] using dvd_add ha hb
  · intro a b _ hb
    simpa [mul_left_comm k a] using dvd_mul_of_dvd_right hb a

end Seminormed

section Normed

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E]
  [NormedSpace ℝ F] {L : Submodule ℤ E}

/-- The content is invariant under linear isometry equivalences. -/
@[simp]
theorem content_comap (e : F ≃ₗᵢ[ℝ] E) :
    content (ZLattice.comap ℝ L e.toLinearEquiv.toLinearMap) = content L := by
  refine Int.natCast_dvd_natCast.mp ?_ |>.antisymm (Int.natCast_dvd_natCast.mp ?_)
  · refine dvd_content_iff.mpr fun x hx m hm ↦ content_dvd (x := e.symm x) ?_ ?_
    · simpa using hx
    · simpa using hm
  · refine dvd_content_iff.mpr fun x hx m hm ↦ content_dvd (x := e x) ?_ ?_
    · simpa using hx
    · simpa using hm

end Normed

/-! ### The Fricke partner -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {L : Submodule ℤ E}

variable (L) in
/-- The Fricke partner `√N • L^∨` of a lattice `L` of level `N` is even: for `x ∈ L^∨` the squared
norm `‖√N • x‖² = N ‖x‖²` is an even integer by the definition of the level. -/
theorem isEven_sqrt_level_smul_dual : IsEven (√(level L : ℝ) • dual L) :=
  (isEven_smul_iff _ _).mpr fun x hx ↦ by
    simpa [Real.sq_sqrt (Nat.cast_nonneg _)] using exists_level_mul_norm_sq_eq hx

/-- The Fricke partner `√N • L^∨` of a lattice `L` of level `N` is integral. -/
theorem isIntegral_sqrt_level_smul_dual : IsIntegral (√(level L : ℝ) • dual L) :=
  (isEven_sqrt_level_smul_dual L).isIntegral

section FiniteDimensional

variable [FiniteDimensional ℝ E] [DiscreteTopology L] [IsZLattice ℝ L]

/-- The Fricke partner of a full integral lattice `L` of level `N` and rank `n` has determinant
`det (√N • L^∨) = Nⁿ / det L`. -/
theorem IsIntegral.det_sqrt_level_smul_dual [MeasurableSpace E] [BorelSpace E]
    (h : IsIntegral L) :
    det (√(level L : ℝ) • dual L) = level L ^ finrank ℝ E / det L := by
  rw [det_sqrt_smul _ h.level_pos.ne', det_dual, div_eq_mul_inv]

/-- An integer `K` is a multiple of the level of the Fricke partner `√N • L^∨` of a full integral
lattice `L` of level `N` exactly when `N` divides `K ‖x‖² / 2` for every `x ∈ L`: the dual of the
partner is `(√N)⁻¹ • L`. -/
private theorem IsIntegral.level_sqrt_level_smul_dual_dvd_iff (h : IsIntegral L) {K : ℕ} :
    level (√(level L : ℝ) • dual L) ∣ K ↔
      ∀ x ∈ L, ∃ m : ℤ, (K : ℝ) * ‖x‖ ^ 2 = 2 * level L * m := by
  have hN : (0 : ℝ) < level L := Nat.cast_pos.mpr h.level_pos
  have hs : 0 < √(level L : ℝ) := Real.sqrt_pos.mpr hN
  rw [level_dvd_iff, dual_smul _ hs.ne', dual_dual]
  simp only [mem_smul_pointwise_iff_exists, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, norm_smul, norm_inv, Real.norm_of_nonneg hs.le, mul_pow, inv_pow,
    Real.sq_sqrt hN.le]
  refine forall₂_congr fun x _ ↦ exists_congr fun m ↦ ?_
  constructor <;> intro hm
  · field_simp at hm
    linear_combination hm
  · field_simp
    linear_combination hm

/-- **The level of the Fricke partner.** For an even full lattice `L` of level `N` and content
`c_L` (the greatest common divisor of its half-norms `‖x‖² / 2`), the Fricke partner `√N • L^∨`
has level `N / gcd (N, c_L)`. -/
theorem IsEven.level_sqrt_level_smul_dual (h : IsEven L) :
    level (√(level L : ℝ) • dual L) = level L / Nat.gcd (level L) (content L) := by
  have hN := h.isIntegral.level_pos
  -- Both sides have the same multiples `K`: each is characterized by `N ∣ K c_L`.
  have key (K : ℕ) : level (√(level L : ℝ) • dual L) ∣ K ↔ level L ∣ K * content L := by
    rw [h.isIntegral.level_sqrt_level_smul_dual_dvd_iff, ← Int.natCast_dvd_natCast,
      Nat.cast_mul]
    refine ⟨fun hK ↦ dvd_mul_content fun x hx m hm ↦ ?_, fun hK x hx ↦ ?_⟩
    · obtain ⟨a, ha⟩ := hK x hx
      refine ⟨a, Int.cast_injective (α := ℝ) ?_⟩
      push_cast
      rw [hm] at ha
      linear_combination ha / 2
    · obtain ⟨m, hm⟩ := isEven_iff.mp h x hx
      obtain ⟨a, ha⟩ := hK.trans (mul_dvd_mul_left (K : ℤ) (content_dvd hx hm))
      have ha' : (K : ℝ) * m = level L * a := by exact_mod_cast ha
      refine ⟨a, ?_⟩
      rw [hm]
      linear_combination 2 * ha'
  refine Nat.dvd_antisymm ((key _).mpr ?_) ?_
  · calc level L = level L / Nat.gcd (level L) (content L) * Nat.gcd (level L) (content L) :=
          (Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)).symm
      _ ∣ level L / Nat.gcd (level L) (content L) * content L :=
          Nat.mul_dvd_mul_left _ (Nat.gcd_dvd_right _ _)
  · -- Cancel `c_L` from `level (√N • L^∨) * c_L ≡ 0 * c_L [MOD N]`.
    refine Nat.modEq_zero_iff_dvd.mp <| Nat.ModEq.cancel_right_div_gcd (c := content L) hN ?_
    rw [zero_mul]
    exact Nat.modEq_zero_iff_dvd.mpr ((key _).mp dvd_rfl)

/-- The level of the Fricke partner `√N • L^∨` of an even full lattice of level `N` divides `N`. -/
theorem IsEven.level_sqrt_level_smul_dual_dvd (h : IsEven L) :
    level (√(level L : ℝ) • dual L) ∣ level L := by
  rw [h.level_sqrt_level_smul_dual]
  exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)

/-- The Fricke partner `√N • L^∨` of an even full lattice of level `N` has level exactly `N` if and
only if `N` is coprime to the content of `L`, that is, no prime dividing `N` divides every
half-norm `‖x‖² / 2` of `L`. -/
theorem IsEven.level_sqrt_level_smul_dual_eq_level_iff (h : IsEven L) :
    level (√(level L : ℝ) • dual L) = level L ↔ (level L).Coprime (content L) := by
  rw [h.level_sqrt_level_smul_dual, Nat.div_eq_self, or_iff_right h.isIntegral.level_pos.ne',
    Nat.Coprime]

end FiniteDimensional

/-! ### An example -/

/-- The lattice `2 ℤ ⊆ ℝ` has content `2`: its half-norms are the integers `2 k²`. -/
theorem content_span_two : content (span ℤ {2} : Submodule ℤ ℝ) = 2 := by
  refine Nat.dvd_antisymm (Int.natCast_dvd_natCast.mp ?_) (Int.natCast_dvd_natCast.mp ?_)
  · exact content_dvd (x := 2) (mem_span_singleton_self _) (by norm_num)
  · refine dvd_content_iff.mpr fun x hx m hm ↦ ?_
    obtain ⟨k, rfl⟩ := mem_span_singleton.mp hx
    have hk : ‖k • (2 : ℝ)‖ ^ 2 = 4 * k ^ 2 := by
      rw [zsmul_eq_mul, norm_mul, Real.norm_eq_abs, Real.norm_two, mul_pow, sq_abs]
      ring
    refine ⟨k ^ 2, Int.cast_injective (α := ℝ) ?_⟩
    push_cast
    linarith

/-- The Fricke partner of `2 ℤ ⊆ ℝ`, which has level `8`, is `√8 • ½ ℤ = √2 ℤ`, of level `4`: the
level of the Fricke partner of an even lattice can be a proper divisor of the level. This agrees
with `IsEven.level_sqrt_level_smul_dual`, since the content of `2 ℤ` is `2` (`content_span_two`)
and `8 / gcd (8, 2) = 4`. -/
theorem level_sqrt_level_smul_dual_span_two :
    level (√(level (span ℤ {2} : Submodule ℤ ℝ) : ℝ) • dual (span ℤ {2} : Submodule ℤ ℝ)) = 4 := by
  set b := OrthonormalBasis.singleton Unit ℝ
  have h4 : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq zero_le_two]
  have h8 : √(8 : ℝ) = 2 * √2 := by
    rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul' _ zero_le_two,
      Real.sqrt_sq zero_le_two]
  -- Write `2 ℤ` as `2 • ℤ b` for the orthonormal basis `b = (1)` of `ℝ`.
  have hL : (span ℤ {2} : Submodule ℤ ℝ) = (2 : ℝ) • span ℤ (Set.range b) := by
    simp [b, smul_span]
  have hlevel : level (span ℤ {2} : Submodule ℤ ℝ) = 8 := by
    simpa [hL, h4] using level_sqrt_smul_span_orthonormalBasis b (m := 4) (by norm_num)
  rw [hlevel, hL, dual_smul _ two_ne_zero, dual_span_orthonormalBasis, smul_smul]
  push_cast
  rw [h8, show 2 * √2 * (2 : ℝ)⁻¹ = √2 by ring]
  simpa [b, smul_span] using level_span_sqrt_two

end ZLattice
