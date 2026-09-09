/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.ValuationIntegrality
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Point.AdicCompletion

/-!
# The range of the formal parametrisation

`Point/AdicCompletion.lean` maps the formal-group parameters of the maximal ideal of `𝒪_v`
injectively into the points of the curve over the completion `K_v`. This file computes the image
of that map: a point is parametrised exactly when it is the point at infinity, or its
`x`-coordinate has a pole. Together with the injectivity already proved, this is the content of
Silverman AEC VII.2.2 — the identification of the formal group `Ê(𝔪)` with the kernel of
reduction `E₁(K_v)`.

⚠ Neither the kernel of reduction nor `E₁` is named here, and the statements below say nothing
about reduction. Mathlib's `Reduction.lean` reduces the *curve*, not its points, so there is no
point-level reduction map to take a kernel of; what the range is described by instead is the
valuation of the `x`-coordinate, which is the condition such a map would compare against. Once
that map exists, "reduces to the point at infinity" and "`P = 0` or `1 < v x`" are the same
condition on a point, and the identification is `range_formalPointHomAdicCompletion` rewritten
along it.

## The two inclusions

Both directions run through the same closed form of the coordinates. A parameter `t ≠ 0` has
`x = 1 / (t ^ 2 u(t))` with `u(t)` integral, so `v x` exceeds `1`: that is the easy inclusion.

The converse is the substantial one, and it is where the `w`-equation is inverted. If `1 < v x`
then `v x < v y` — the pole of `y` strictly dominates, by
`Affine.valuation_x_lt_valuation_y` — so `-x / y` and `-1 / y` both lie in the maximal ideal, and
`wEquation_of_equation` says the second solves the `w`-equation at the first. The `w`-equation
has only one solution there (`eq_formalWEval_of_wEquation`), which forces `-1 / y = w(-x / y)`,
and the point is then read off as the parametrised point of `-x / y`.

## Main results

* `WeierstrassCurve.wEquation_of_equation`: the `w`-equation is the Weierstrass equation read in
  the coordinates `z = -x / y`, `w = -1 / y`.
* `WeierstrassCurve.formalPoint_eq_some`: a point whose two ratios `-x / y` and `-1 / y` come
  from the ideal is the parametrised point of the first — the general form of surjectivity, with
  no valuation in sight.
* `WeierstrassCurve.one_lt_valued_xCoord_formalPoint` and
  `WeierstrassCurve.exists_formalPoint_eq_of_one_lt_valued_xCoord`: the two inclusions over an
  adic completion.
* `WeierstrassCurve.range_formalPointHomAdicCompletion` and
  `WeierstrassCurve.mem_range_formalPointHomAdicCompletion_iff`: the range itself. Since the
  range is a subgroup, so is the set of points on the right.
* `WeierstrassCurve.valued_le_one_of_notMem_range`: outside the range both coordinates are
  integral.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1 and VII.2.2.

## Provenance

Not a port. The parametrisation and its injectivity come from the Stoll development pinned in
`Point/Basic.lean`'s provenance; the range computation below is written against this
repository's own `w`-equation API — `eq_formalWEval_of_wEquation`, whose evaluated uniqueness
argument goes through the geometric-series unit lemma rather than through coefficients — and
its valuation input is `Affine/ValuationIntegrality.lean`.
-/

public section

namespace WeierstrassCurve

section Equation

variable {O : Type*} [CommRing O] {K : Type*} [Field K] [Algebra O K] (W : WeierstrassCurve O)

/-- **The `w`-equation is the Weierstrass equation read in the coordinates `z = -x / y`,
`w = -1 / y`.** Clearing the denominators of `y ^ 2 + a₁ x y + a₃ y = x ^ 3 + a₂ x ^ 2 + a₄ x + a₆`
at `x = z / w`, `y = -1 / w` is what produces that equation in the first place; this is the
converse reading, from a point of the curve to a solution of the equation.

The hypothesis is `Equation`, not `Nonsingular`: nothing here needs the point to be smooth. -/
theorem wEquation_of_equation {x y : K} (hxy : (W.baseChange K).toAffine.Equation x y)
    (hy : y ≠ 0) : -y⁻¹ = wEquationRHS W (-(x / y)) (-y⁻¹) := by
  rw [WeierstrassCurve.Affine.equation_iff] at hxy
  simp only [baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at hxy
  rw [wEquationRHS_def]
  field_simp
  linear_combination -hxy

end Equation

section Parametrised

variable {O : Type*} [CommRing O] [UniformSpace O] [IsUniformAddGroup O] [CompleteSpace O]
  [T2Space O] [IsTopologicalRing O] [IsLinearTopology O O]
  {K : Type*} [Field K] [Algebra O K]

variable (W : WeierstrassCurve O) [(W.baseChange K).IsElliptic] [FaithfulSMul O K]

open scoped Classical in
/-- **A point of the curve is the parametrised point of `-x / y`** as soon as `-x / y` and `-1 / y`
both come from the ideal `I`. This is surjectivity of the parametrisation in its valuation-free
form: which points satisfy the hypothesis is a separate question, answered over an adic completion
by `exists_formalPoint_eq_of_one_lt_valued_xCoord`.

The two ratios are asked for as products, `t * y = -x` and `s * y = -1`, so that no division is
needed to state the hypothesis and `y ≠ 0` follows from the second rather than being assumed. The
parameter `s` does not appear in the conclusion: it is there only to witness that `-1 / y` is a
value of the ideal, and the proof identifies it as `w(t)`, which is what pins the point down. -/
theorem formalPoint_eq_some {I : Ideal O} (hI : IsAdic I) {t s : O} (ht : t ∈ I) (hs : s ∈ I)
    {x y : K} (hns : (W.baseChange K).toAffine.Nonsingular x y)
    (hxt : algebraMap O K t * y = -x) (hys : algebraMap O K s * y = -1) :
    W.formalPoint (K := K) hI ht = .some x y hns := by
  have hy : y ≠ 0 := by
    rintro rfl
    simp at hys
  have hT : algebraMap O K t = -(x / y) := by field_simp; linear_combination hxt
  have hS : algebraMap O K s = -y⁻¹ := by field_simp; linear_combination hys
  have hkey : s = W.formalWEval t := by
    refine W.eq_formalWEval_of_wEquation hI ht hs (FaithfulSMul.algebraMap_injective O K ?_)
    rw [W.algebraMap_wEquationRHS (B := K) t s, hT, hS]
    exact W.wEquation_of_equation hns.left hy
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [W.formalWEval_zero] at hkey
    rw [hkey] at hys
    simp at hys
  refine Affine.Point.eq_of_coords (fun h ↦ ht0 ((W.formalPoint_eq_zero_iff hI ht).mp h))
    (by simp) ?_ ?_
  · rw [W.xCoord_formalPoint hI ht ht0, ← hkey, hS, hT, Affine.Point.xCoord_some]
    field_simp
  · rw [W.yCoord_formalPoint hI ht ht0, ← hkey, hS, Affine.Point.yCoord_some]
    field_simp

end Parametrised

section AdicCompletion

open IsDedekindDomain

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  {F : Type*} [Field F] [Algebra A F] [IsFractionRing A F]
  (u : HeightOneSpectrum A)

local notation "O_u" => u.adicCompletionIntegers F
local notation "F_u" => u.adicCompletion F
local notation "m_u" => IsLocalRing.maximalIdeal O_u

local instance : IsLinearTopology O_u O_u :=
  u.isAdic_maximalIdeal_adicCompletionIntegers (K := F) ▸ Ideal.isLinearTopology m_u

local instance : Fact (IsAdic m_u) :=
  ⟨u.isAdic_maximalIdeal_adicCompletionIntegers (K := F)⟩

variable (C : WeierstrassCurve (u.adicCompletionIntegers F))
  [(C.baseChange (u.adicCompletion F)).IsElliptic]

open scoped Classical in
/-- **A nonzero parameter has a pole in the `x`-coordinate of its point.** The closed form
`x * (t ^ 2 u(t)) = 1` of `xCoord_formalPoint_mul_eq_one` makes `x` inverse to an element of the
maximal ideal, `t` lying there and `u(t)` being integral. -/
theorem one_lt_valued_xCoord_formalPoint {t : O_u} (ht : t ∈ m_u) (ht0 : t ≠ 0) :
    1 < Valued.v ((C.formalPoint (K := F_u)
      (u.isAdic_maximalIdeal_adicCompletionIntegers (K := F)) ht).xCoord) := by
  have hkey := congrArg (Valued.v (R := F_u)) (C.xCoord_formalPoint_mul_eq_one (K := F_u)
    (u.isAdic_maximalIdeal_adicCompletionIntegers (K := F)) ht ht0)
  rw [map_mul, map_one] at hkey
  have hcoe : ∀ z : O_u, algebraMap O_u F_u z = (z : F_u) :=
    fun z ↦ Algebra.algebraMap_ofSubsemiring_apply _ z
  have hsmall : Valued.v (algebraMap O_u F_u (t ^ 2 * C.formalUEval t)) < 1 := by
    rw [hcoe]
    push_cast
    rw [map_mul, map_pow]
    calc Valued.v (t : F_u) ^ 2 * Valued.v ((C.formalUEval t : O_u) : F_u)
        ≤ Valued.v (t : F_u) ^ 2 * 1 := mul_le_mul' le_rfl (C.formalUEval t).property
      _ = Valued.v (t : F_u) * Valued.v (t : F_u) := by rw [mul_one, sq]
      _ ≤ 1 * Valued.v (t : F_u) := mul_le_mul' t.property le_rfl
      _ = Valued.v (t : F_u) := one_mul _
      _ < 1 := (Valuation.mem_maximalIdeal_iff _ Valued.v).mp ht
  by_contra hle
  push Not at hle
  refine absurd hkey (ne_of_lt ?_)
  calc Valued.v ((C.formalPoint (K := F_u)
          (u.isAdic_maximalIdeal_adicCompletionIntegers (K := F)) ht).xCoord) *
        Valued.v (algebraMap O_u F_u (t ^ 2 * C.formalUEval t))
      ≤ 1 * Valued.v (algebraMap O_u F_u (t ^ 2 * C.formalUEval t)) :=
        mul_le_mul' hle le_rfl
    _ = Valued.v (algebraMap O_u F_u (t ^ 2 * C.formalUEval t)) := one_mul _
    _ < 1 := hsmall

open scoped Classical in
/-- **A point with a pole in its `x`-coordinate is parametrised**, by the parameter `-x / y`.
This is the converse of `one_lt_valued_xCoord_formalPoint`, and the substantial half of
Silverman AEC VII.2.2.

The pole of `x` is what puts both `-x / y` and `-1 / y` in the maximal ideal: `v x < v y` at such
a point, so `v (x / y) < 1`, and `1 < v y` gives `v (1 / y) < 1`. -/
theorem exists_formalPoint_eq_of_one_lt_valued_xCoord {P : (C.baseChange F_u).toAffine.Point}
    (hP : 1 < Valued.v (Affine.Point.xCoord P)) :
    ∃ t : O_u, ∃ ht : t ∈ m_u, C.formalPoint (K := F_u)
      (u.isAdic_maximalIdeal_adicCompletionIntegers (K := F)) ht = P := by
  have hP0 : P ≠ 0 := by
    rintro rfl
    simp at hP
  obtain ⟨x, y, hns, rfl⟩ := Affine.Point.exists_eq_some_of_ne_zero hP0
  rw [Affine.Point.xCoord_some] at hP
  -- `u.adicCompletionIntegers F` is by definition the valuation subring of `Valued.v`, which is
  -- what lets `C` serve as an integral model of `C⁄K_v` for the valuation estimates, and lets
  -- `Valuation.mem_maximalIdeal_iff` read membership in `m_u` below.
  have : WeierstrassCurve.IsIntegral (Valued.v : Valuation F_u (WithZero
    (Multiplicative ℤ))).valuationSubring (C.baseChange F_u) := ⟨C, rfl⟩
  have hlt : Valued.v x < Valued.v y := Affine.valuation_x_lt_valuation_y Valued.v hns.left hP
  have hy1 : (1 : WithZero (Multiplicative ℤ)) < Valued.v y := hP.trans hlt
  have hyv0 : (0 : WithZero (Multiplicative ℤ)) < Valued.v y := zero_lt_one.trans hy1
  have htv : Valued.v (-(x / y)) < 1 := by
    rw [Valuation.map_neg, map_div₀]
    exact (div_lt_one₀ hyv0).mpr hlt
  have hsv : Valued.v (-y⁻¹) < 1 := by
    rw [Valuation.map_neg, map_inv₀]
    exact (inv_lt_one₀ hyv0).mpr hy1
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hy1
  obtain ⟨t, htm, hct⟩ : ∃ t : O_u, t ∈ m_u ∧ algebraMap O_u F_u t = -(x / y) :=
    ⟨⟨-(x / y), (HeightOneSpectrum.mem_adicCompletionIntegers A F u).mpr htv.le⟩,
      (Valuation.mem_maximalIdeal_iff _ Valued.v).mpr htv,
      Algebra.algebraMap_ofSubsemiring_apply _ _⟩
  obtain ⟨s, hsm, hcs⟩ : ∃ s : O_u, s ∈ m_u ∧ algebraMap O_u F_u s = -y⁻¹ :=
    ⟨⟨-y⁻¹, (HeightOneSpectrum.mem_adicCompletionIntegers A F u).mpr hsv.le⟩,
      (Valuation.mem_maximalIdeal_iff _ Valued.v).mpr hsv,
      Algebra.algebraMap_ofSubsemiring_apply _ _⟩
  refine ⟨t, htm, C.formalPoint_eq_some (K := F_u) _ htm hsm hns ?_ ?_⟩
  · rw [hct]
    field_simp
  · rw [hcs]
    field_simp

open scoped Classical in
/-- **The range of the formal parametrisation of an adic completion**: the point at infinity
together with the points whose `x`-coordinate has a pole. Since the left-hand side is the range of
an additive homomorphism, this exhibits that set of points as a subgroup — the kernel of reduction,
once a reduction map on points exists to call it that. -/
theorem range_formalPointHomAdicCompletion :
    Set.range (C.formalPointHomAdicCompletion u) =
      {P | P = 0 ∨ 1 < Valued.v (Affine.Point.xCoord P)} := by
  ext P
  constructor
  · rintro ⟨Q, rfl⟩
    rw [formalPointHomAdicCompletion_apply]
    rcases eq_or_ne Q.val 0 with h | h
    · exact Or.inl (C.formalPoint_of_param_eq_zero _ Q.property h)
    · exact Or.inr (C.one_lt_valued_xCoord_formalPoint u Q.property h)
  · rintro (rfl | hP)
    · exact ⟨0, map_zero _⟩
    · obtain ⟨t, ht, hteq⟩ := C.exists_formalPoint_eq_of_one_lt_valued_xCoord u hP
      exact ⟨⟨t, ht⟩, by rw [formalPointHomAdicCompletion_apply]; exact hteq⟩

open scoped Classical in
/-- **Membership in the range of the formal parametrisation**, the range being read as the
subgroup `AddMonoidHom.range`. This is `range_formalPointHomAdicCompletion` elementwise. -/
theorem mem_range_formalPointHomAdicCompletion_iff
    {P : (C.baseChange F_u).toAffine.Point} :
    P ∈ (C.formalPointHomAdicCompletion u).range ↔
      P = 0 ∨ 1 < Valued.v (Affine.Point.xCoord P) :=
  Set.ext_iff.mp (C.range_formalPointHomAdicCompletion u) P

open scoped Classical in
/-- **A point outside the range has integral coordinates.** The parametrised points are exactly
those with a pole, so a point of the complement has `v x ≤ 1`, and then the Weierstrass equation
forces `v y ≤ 1` as well. This is the other half of the dichotomy of
`Affine/ValuationIntegrality.lean`, read against the range. -/
theorem valued_le_one_of_notMem_range {P : (C.baseChange F_u).toAffine.Point}
    (hP : P ∉ (C.formalPointHomAdicCompletion u).range) :
    Valued.v (Affine.Point.xCoord P) ≤ 1 ∧ Valued.v (Affine.Point.yCoord P) ≤ 1 := by
  rw [mem_range_formalPointHomAdicCompletion_iff] at hP
  push Not at hP
  obtain ⟨hP0, hx⟩ := hP
  -- as above, `u.adicCompletionIntegers F` is the valuation subring of `Valued.v`
  have : WeierstrassCurve.IsIntegral (Valued.v : Valuation F_u (WithZero
    (Multiplicative ℤ))).valuationSubring (C.baseChange F_u) := ⟨C, rfl⟩
  exact Affine.valuation_x_le_one_and_valuation_y_le_one_of_valuation_x_lt_exp_two Valued.v
    (Affine.Point.nonsingular_coords hP0).left (hx.trans_lt (by simp))

end AdicCompletion

end WeierstrassCurve
