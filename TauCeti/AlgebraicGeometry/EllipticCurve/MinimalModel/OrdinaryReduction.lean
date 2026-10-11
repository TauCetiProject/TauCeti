/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.PointCount
public import TauCeti.AlgebraicGeometry.EllipticCurve.Supersingular
-- Proof-only: the integral model of an equation over `R`, for the examples.
import TauCeti.AlgebraicGeometry.EllipticCurve.IntegralModel
-- Proof-only: the trace criterion for supersingularity over a finite field.
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Frobenius.Supersingular

/-!
# Good ordinary and good supersingular reduction

Let `R` be a discrete valuation ring with fraction field `K` and residue field `k` of
characteristic `p > 0`. A minimal Weierstrass equation over `K` with good reduction reduces to an
elliptic curve over `k`, which is either ordinary or supersingular in the sense of
`WeierstrassCurve.IsOrdinary`. The equation then has **good ordinary**, respectively **good
supersingular**, reduction. These are the hypotheses under which the `p`-adic theory of elliptic
curves is usually stated.

Like Mathlib's `HasGoodReduction`, which they extend, the two predicates are properties of a
minimal equation, and they are applied to the chosen minimal equation `W.minimal R` to speak about
a curve. They depend only on the curve: two minimal models of an elliptic curve have reductions
related by a change of variables over `k`
(`WeierstrassCurve.exists_smul_reduction_eq_of_isMinimal_smul`), and ordinarity is invariant under
changes of variables.

Good reduction persists along every map `R → S` of discrete valuation rings compatible with an
extension `L / K` of fraction fields, with no ramification hypothesis. When the map is local, the
reduction over `S` is the base change of the reduction over `R` along the extension of residue
fields, and ordinarity is invariant under field extension, so good ordinary and good supersingular
reduction are preserved by such base change and, for an equation with good reduction over `R`,
reflected by it.

Over a finite residue field, the reduction is supersingular exactly when `p` divides the trace of
Frobenius of the reduction, `a_q = q + 1 - #E(k)` for `E` the reduction and `q` the order of `k`.

In residue characteristic `2` and `3` the reduction is supersingular exactly when its
`j`-invariant vanishes. This reads off the integral model: with good reduction, it is ordinary at
`2` exactly when `a₁` is a unit, and ordinary at `3` exactly when `b₂` is a unit. The examples at
the end use these criteria for `y² + xy = x³ + 1`, which has good ordinary reduction at residue
characteristic `2`, and for `y² = x³ - x`, which has good supersingular reduction at residue
characteristic `3`.

## Main definitions

* `WeierstrassCurve.HasGoodOrdinaryReduction`: good reduction with ordinary reduction.
* `WeierstrassCurve.HasGoodSupersingularReduction`: good reduction with supersingular reduction.

## Main results

* `WeierstrassCurve.hasGoodReduction_iff_hasGoodOrdinaryReduction_or_hasGoodSupersingularReduction`
  and `WeierstrassCurve.HasGoodOrdinaryReduction.not_hasGoodSupersingularReduction`: good
  reduction is exactly one of the two.
* `WeierstrassCurve.hasGoodOrdinaryReduction_minimal_smul_iff` and
  `WeierstrassCurve.hasGoodSupersingularReduction_minimal_smul_iff`: both are properties of the
  curve.
* `WeierstrassCurve.hasGoodOrdinaryReduction_baseChange_iff` and
  `WeierstrassCurve.hasGoodSupersingularReduction_baseChange_iff`: given good reduction, both are
  preserved and reflected by base change along a local map of discrete valuation rings.
* `WeierstrassCurve.hasGoodSupersingularReduction_iff_dvd_frobeniusTrace` and
  `WeierstrassCurve.hasGoodOrdinaryReduction_iff_not_dvd_frobeniusTrace`: over a finite residue
  field, the trace criterion for the reduction.
* `WeierstrassCurve.hasGoodOrdinaryReduction_iff_isUnit_a₁_of_char_two` and
  `WeierstrassCurve.hasGoodOrdinaryReduction_iff_isUnit_b₂_of_char_three`: the criteria in
  residue characteristic `2` and `3`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], V.3, VII.1.3 and VII.5.4.
-/

public section

namespace WeierstrassCurve

open IsDiscreteValuationRing IsLocalRing

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- **Good ordinary reduction** at `p`: a minimal equation with good reduction whose reduction is
ordinary at `p`, that is, has a nonzero `p`-torsion point over the algebraic closure of the residue
field. It is meant for `p` the characteristic of the residue field. -/
class HasGoodOrdinaryReduction (p : ℕ) (W : WeierstrassCurve K) : Prop
    extends W.HasGoodReduction R where
  isOrdinary_reduction : (W.reduction R).IsOrdinary p

/-- **Good supersingular reduction** at `p`: a minimal equation with good reduction whose
reduction is supersingular at `p`, that is, has no nonzero `p`-torsion point over the algebraic
closure of the residue field. It is meant for `p` the characteristic of the residue field. -/
class HasGoodSupersingularReduction (p : ℕ) (W : WeierstrassCurve K) : Prop
    extends W.HasGoodReduction R where
  isSupersingular_reduction : (W.reduction R).IsSupersingular p

variable {R} {p : ℕ} {W : WeierstrassCurve K}

/-- An equation with good reduction has good ordinary reduction exactly when its reduction is
ordinary. -/
theorem hasGoodOrdinaryReduction_iff_isOrdinary_reduction [W.HasGoodReduction R] :
    W.HasGoodOrdinaryReduction R p ↔ (W.reduction R).IsOrdinary p :=
  ⟨fun h ↦ h.isOrdinary_reduction, fun h ↦ ⟨h⟩⟩

/-- An equation with good reduction has good supersingular reduction exactly when its reduction
is supersingular. -/
theorem hasGoodSupersingularReduction_iff_isSupersingular_reduction [W.HasGoodReduction R] :
    W.HasGoodSupersingularReduction R p ↔ (W.reduction R).IsSupersingular p :=
  ⟨fun h ↦ h.isSupersingular_reduction, fun h ↦ ⟨h⟩⟩

/-! ### The dichotomy -/

/-- **Good reduction is ordinary or supersingular.** -/
theorem HasGoodReduction.hasGoodOrdinaryReduction_or_hasGoodSupersingularReduction
    (h : W.HasGoodReduction R) (p : ℕ) :
    W.HasGoodOrdinaryReduction R p ∨ W.HasGoodSupersingularReduction R p := by
  rw [hasGoodOrdinaryReduction_iff_isOrdinary_reduction,
    hasGoodSupersingularReduction_iff_isSupersingular_reduction, ← not_isSupersingular]
  exact em' _

/-- **Good reduction is exactly good ordinary or good supersingular reduction.** -/
theorem hasGoodReduction_iff_hasGoodOrdinaryReduction_or_hasGoodSupersingularReduction :
    W.HasGoodReduction R ↔ W.HasGoodOrdinaryReduction R p ∨ W.HasGoodSupersingularReduction R p :=
  ⟨fun h ↦ h.hasGoodOrdinaryReduction_or_hasGoodSupersingularReduction p,
    fun h ↦ h.elim (·.toHasGoodReduction) (·.toHasGoodReduction)⟩

/-- **Good ordinary reduction is not good supersingular reduction.** -/
theorem HasGoodOrdinaryReduction.not_hasGoodSupersingularReduction
    (h : W.HasGoodOrdinaryReduction R p) : ¬W.HasGoodSupersingularReduction R p :=
  fun h' ↦ not_isSupersingular.mpr h.isOrdinary_reduction h'.isSupersingular_reduction

/-- **Good supersingular reduction is not good ordinary reduction.** -/
theorem HasGoodSupersingularReduction.not_hasGoodOrdinaryReduction
    (h : W.HasGoodSupersingularReduction R p) : ¬W.HasGoodOrdinaryReduction R p :=
  fun h' ↦ h'.not_hasGoodSupersingularReduction h

/-- For an equation with good reduction, good ordinary reduction is the failure of good
supersingular reduction. -/
theorem HasGoodReduction.hasGoodOrdinaryReduction_iff_not_hasGoodSupersingularReduction
    (h : W.HasGoodReduction R) :
    W.HasGoodOrdinaryReduction R p ↔ ¬W.HasGoodSupersingularReduction R p :=
  ⟨HasGoodOrdinaryReduction.not_hasGoodSupersingularReduction,
    (h.hasGoodOrdinaryReduction_or_hasGoodSupersingularReduction p).resolve_right⟩

/-- For an equation with good reduction, good supersingular reduction is the failure of good
ordinary reduction. -/
theorem HasGoodReduction.hasGoodSupersingularReduction_iff_not_hasGoodOrdinaryReduction
    (h : W.HasGoodReduction R) :
    W.HasGoodSupersingularReduction R p ↔ ¬W.HasGoodOrdinaryReduction R p :=
  ⟨HasGoodSupersingularReduction.not_hasGoodOrdinaryReduction,
    (h.hasGoodOrdinaryReduction_or_hasGoodSupersingularReduction p).resolve_left⟩

/-! ### Independence of the minimal model -/

/-- **Good ordinary reduction transfers between minimal models**: if two minimal equations are
related by a change of variables and one has good ordinary reduction, so does the other. -/
theorem HasGoodOrdinaryReduction.of_isMinimal_smul {W₁ W₂ : WeierstrassCurve K} [IsMinimal R W₂]
    (D : VariableChange K) (hD : D • W₁ = W₂) (h : W₁.HasGoodOrdinaryReduction R p) :
    W₂.HasGoodOrdinaryReduction R p := by
  have : IsMinimal R W₁ := h.toIsMinimal
  have := h.isElliptic
  obtain ⟨C, hC⟩ := exists_smul_reduction_eq_of_isMinimal_smul R D hD
  have : W₂.HasGoodReduction R :=
    ⟨by rw [valuation_Δ_eq_of_isMinimal_smul R D hD]; exact h.goodReduction⟩
  rw [hasGoodOrdinaryReduction_iff_isOrdinary_reduction, ← hC, isOrdinary_variableChange_iff]
  exact h.isOrdinary_reduction

/-- **Good supersingular reduction transfers between minimal models**: if two minimal equations
are related by a change of variables and one has good supersingular reduction, so does the
other. -/
theorem HasGoodSupersingularReduction.of_isMinimal_smul {W₁ W₂ : WeierstrassCurve K}
    [IsMinimal R W₂] (D : VariableChange K) (hD : D • W₁ = W₂)
    (h : W₁.HasGoodSupersingularReduction R p) : W₂.HasGoodSupersingularReduction R p := by
  have : IsMinimal R W₁ := h.toIsMinimal
  have := h.isElliptic
  obtain ⟨C, hC⟩ := exists_smul_reduction_eq_of_isMinimal_smul R D hD
  have : W₂.HasGoodReduction R :=
    ⟨by rw [valuation_Δ_eq_of_isMinimal_smul R D hD]; exact h.goodReduction⟩
  rw [hasGoodSupersingularReduction_iff_isSupersingular_reduction, ← hC,
    isSupersingular_variableChange_iff]
  exact h.isSupersingular_reduction

/-- **Good ordinary reduction is a property of the curve**: the chosen minimal equations of two
equations related by a change of variables have good ordinary reduction together. -/
@[simp]
theorem hasGoodOrdinaryReduction_minimal_smul_iff (D : VariableChange K) (W : WeierstrassCurve K) :
    ((D • W).minimal R).HasGoodOrdinaryReduction R p ↔
      (W.minimal R).HasGoodOrdinaryReduction R p := by
  obtain ⟨C, hC⟩ := exists_smul_minimal_eq_minimal R D W
  exact ⟨.of_isMinimal_smul C⁻¹ (by rw [← hC, inv_smul_smul]), .of_isMinimal_smul C hC⟩

/-- **Good supersingular reduction is a property of the curve**: the chosen minimal equations of
two equations related by a change of variables have good supersingular reduction together. -/
@[simp]
theorem hasGoodSupersingularReduction_minimal_smul_iff (D : VariableChange K)
    (W : WeierstrassCurve K) :
    ((D • W).minimal R).HasGoodSupersingularReduction R p ↔
      (W.minimal R).HasGoodSupersingularReduction R p := by
  obtain ⟨C, hC⟩ := exists_smul_minimal_eq_minimal R D W
  exact ⟨.of_isMinimal_smul C⁻¹ (by rw [← hC, inv_smul_smul]), .of_isMinimal_smul C hC⟩

/-- An equation with good ordinary reduction has a chosen minimal equation with good ordinary
reduction. -/
theorem HasGoodOrdinaryReduction.hasGoodOrdinaryReduction_minimal
    (h : W.HasGoodOrdinaryReduction R p) : (W.minimal R).HasGoodOrdinaryReduction R p :=
  .of_isMinimal_smul _ rfl h

/-- An equation with good supersingular reduction has a chosen minimal equation with good
supersingular reduction. -/
theorem HasGoodSupersingularReduction.hasGoodSupersingularReduction_minimal
    (h : W.HasGoodSupersingularReduction R p) :
    (W.minimal R).HasGoodSupersingularReduction R p :=
  .of_isMinimal_smul _ rfl h

/-! ### Base change -/

section BaseChange

variable (S : Type*) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  {L : Type*} [Field L] [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R S]
  [IsLocalHom (algebraMap R S)]

/-- **Good ordinary reduction is preserved and reflected by base change** along a local map
`R → S` of discrete valuation rings compatible with `K → L`, for an equation with good reduction
over `R`. No ramification hypothesis is needed: the reduction over `S` is the base change of the
reduction over `R`, and ordinarity is invariant under field extension. -/
theorem hasGoodOrdinaryReduction_baseChange_iff
    (hRS : (algebraMap S L).comp (algebraMap R S) = (algebraMap K L).comp (algebraMap R K))
    (hp : p ≠ 0) (h : W.HasGoodReduction R) :
    (W.baseChange L).HasGoodOrdinaryReduction S p ↔ W.HasGoodOrdinaryReduction R p := by
  have := (h.baseChange R S hRS).toIsMinimal
  have := h.baseChange R S hRS
  have := (hasGoodReduction_iff_isElliptic_reduction (R := R)).mp h
  rw [hasGoodOrdinaryReduction_iff_isOrdinary_reduction,
    hasGoodOrdinaryReduction_iff_isOrdinary_reduction, reduction_baseChange R S hRS,
    isOrdinary_baseChange_iff hp]

/-- **Good supersingular reduction is preserved and reflected by base change** along a local map
`R → S` of discrete valuation rings compatible with `K → L`, for an equation with good reduction
over `R`. -/
theorem hasGoodSupersingularReduction_baseChange_iff
    (hRS : (algebraMap S L).comp (algebraMap R S) = (algebraMap K L).comp (algebraMap R K))
    (hp : p ≠ 0) (h : W.HasGoodReduction R) :
    (W.baseChange L).HasGoodSupersingularReduction S p ↔
      W.HasGoodSupersingularReduction R p := by
  have := (h.baseChange R S hRS).toIsMinimal
  have := h.baseChange R S hRS
  have := (hasGoodReduction_iff_isElliptic_reduction (R := R)).mp h
  rw [hasGoodSupersingularReduction_iff_isSupersingular_reduction,
    hasGoodSupersingularReduction_iff_isSupersingular_reduction, reduction_baseChange R S hRS,
    isSupersingular_baseChange_iff hp]

/-- **Good ordinary reduction is preserved by base change** along a local map of discrete
valuation rings. -/
theorem HasGoodOrdinaryReduction.baseChange
    (hRS : (algebraMap S L).comp (algebraMap R S) = (algebraMap K L).comp (algebraMap R K))
    (hp : p ≠ 0) (h : W.HasGoodOrdinaryReduction R p) :
    (W.baseChange L).HasGoodOrdinaryReduction S p :=
  (hasGoodOrdinaryReduction_baseChange_iff S hRS hp h.toHasGoodReduction).mpr h

/-- **Good supersingular reduction is preserved by base change** along a local map of discrete
valuation rings. -/
theorem HasGoodSupersingularReduction.baseChange
    (hRS : (algebraMap S L).comp (algebraMap R S) = (algebraMap K L).comp (algebraMap R K))
    (hp : p ≠ 0) (h : W.HasGoodSupersingularReduction R p) :
    (W.baseChange L).HasGoodSupersingularReduction S p :=
  (hasGoodSupersingularReduction_baseChange_iff S hRS hp h.toHasGoodReduction).mpr h

end BaseChange

/-! ### Finite residue field -/

/-- **Good ordinary reduction by the trace of Frobenius**: over a finite residue field of
characteristic `p`, an equation with good reduction has good ordinary reduction exactly when `p`
does not divide the trace of Frobenius of its reduction. -/
theorem hasGoodOrdinaryReduction_iff_not_dvd_frobeniusTrace [Finite (ResidueField R)]
    [ExpChar (ResidueField R) p] [W.HasGoodReduction R] :
    W.HasGoodOrdinaryReduction R p ↔ ¬(p : ℤ) ∣ (W.reduction R).frobeniusTrace := by
  have := (hasGoodReduction_iff_isElliptic_reduction (R := R)).mp ‹_›
  rw [hasGoodOrdinaryReduction_iff_isOrdinary_reduction, isOrdinary_iff_not_dvd_frobeniusTrace]

/-- **Good supersingular reduction by the trace of Frobenius**: over a finite residue field of
characteristic `p`, an equation with good reduction has good supersingular reduction exactly when
`p` divides the trace of Frobenius of its reduction. -/
theorem hasGoodSupersingularReduction_iff_dvd_frobeniusTrace [Finite (ResidueField R)]
    [ExpChar (ResidueField R) p] [W.HasGoodReduction R] :
    W.HasGoodSupersingularReduction R p ↔ (p : ℤ) ∣ (W.reduction R).frobeniusTrace := by
  have := (hasGoodReduction_iff_isElliptic_reduction (R := R)).mp ‹_›
  rw [hasGoodSupersingularReduction_iff_isSupersingular_reduction,
    isSupersingular_iff_dvd_frobeniusTrace]

/-! ### Residue characteristic two and three -/

/-- **In residue characteristic `2`, good reduction is ordinary exactly when `a₁` is a unit**: the
reduction is supersingular exactly when its `j`-invariant, equivalently its `a₁`, vanishes. -/
theorem hasGoodOrdinaryReduction_iff_isUnit_a₁_of_char_two [CharP (ResidueField R) 2]
    [W.HasGoodReduction R] : W.HasGoodOrdinaryReduction R 2 ↔ IsUnit (W.integralModel R).a₁ := by
  have := (hasGoodReduction_iff_isElliptic_reduction (R := R)).mp ‹_›
  rw [hasGoodOrdinaryReduction_iff_isOrdinary_reduction, isOrdinary_iff_j_ne_zero_of_char_two,
    ne_eq, j_eq_zero_iff_of_char_two, reduction, map_a₁, ← ne_eq, residue_ne_zero_iff_isUnit]

/-- **In residue characteristic `2`, good reduction is supersingular exactly when `a₁` is not a
unit.** -/
theorem hasGoodSupersingularReduction_iff_not_isUnit_a₁_of_char_two [CharP (ResidueField R) 2]
    [W.HasGoodReduction R] :
    W.HasGoodSupersingularReduction R 2 ↔ ¬IsUnit (W.integralModel R).a₁ := by
  rw [← hasGoodOrdinaryReduction_iff_isUnit_a₁_of_char_two,
    HasGoodReduction.hasGoodOrdinaryReduction_iff_not_hasGoodSupersingularReduction ‹_›, not_not]

/-- **In residue characteristic `3`, good reduction is ordinary exactly when `b₂` is a unit**: the
reduction is supersingular exactly when its `j`-invariant, equivalently its `b₂`, vanishes. -/
theorem hasGoodOrdinaryReduction_iff_isUnit_b₂_of_char_three [CharP (ResidueField R) 3]
    [W.HasGoodReduction R] :
    W.HasGoodOrdinaryReduction R 3 ↔ IsUnit (W.integralModel R).b₂ := by
  have := (hasGoodReduction_iff_isElliptic_reduction (R := R)).mp ‹_›
  rw [hasGoodOrdinaryReduction_iff_isOrdinary_reduction, isOrdinary_iff_j_ne_zero_of_char_three,
    ne_eq, j_eq_zero_iff_of_char_three, reduction, map_b₂, ← ne_eq, residue_ne_zero_iff_isUnit]

/-- **In residue characteristic `3`, good reduction is supersingular exactly when `b₂` is not a
unit.** -/
theorem hasGoodSupersingularReduction_iff_not_isUnit_b₂_of_char_three
    [CharP (ResidueField R) 3] [W.HasGoodReduction R] :
    W.HasGoodSupersingularReduction R 3 ↔ ¬IsUnit (W.integralModel R).b₂ := by
  rw [← hasGoodOrdinaryReduction_iff_isUnit_b₂_of_char_three,
    HasGoodReduction.hasGoodOrdinaryReduction_iff_not_hasGoodSupersingularReduction ‹_›, not_not]

/-! ### Examples -/

/-- `y² + xy = x³ + 1` has good ordinary reduction over every discrete valuation ring of residue
characteristic `2`: its discriminant `-433` and its `a₁ = 1` are units there. -/
example [CharP (ResidueField R) 2] :
    ((⟨1, 0, 0, 0, 1⟩ : WeierstrassCurve R).baseChange K).HasGoodOrdinaryReduction R 2 := by
  have : IsIntegral R ((⟨1, 0, 0, 0, 1⟩ : WeierstrassCurve R).baseChange K) := ⟨_, rfl⟩
  have hI := integralModel_eq_of_baseChange_eq (R := R) (W₀ := ⟨1, 0, 0, 0, 1⟩) (K := K) rfl
  have : ((⟨1, 0, 0, 0, 1⟩ : WeierstrassCurve R).baseChange K).HasGoodReduction R := by
    rw [hasGoodReduction_iff_isUnit_integralModel_Δ, hI, ← residue_ne_zero_iff_isUnit]
    have hΔ : (⟨1, 0, 0, 0, 1⟩ : WeierstrassCurve R).Δ = -433 := by
      simp only [Δ, b₂, b₄, b₆, b₈]
      ring
    have h433 : (433 : ResidueField R) = 1 := by
      linear_combination (216 : ResidueField R) * CharP.ofNat_eq_zero (ResidueField R) 2
    rw [hΔ, map_neg, map_ofNat, h433]
    exact neg_ne_zero.mpr one_ne_zero
  rw [hasGoodOrdinaryReduction_iff_isUnit_a₁_of_char_two, hI]
  exact isUnit_one

/-- `y² = x³ - x` has good supersingular reduction over every discrete valuation ring of residue
characteristic `3`: its discriminant `64` is a unit there and its `b₂ = 0` is not. -/
example [CharP (ResidueField R) 3] :
    ((⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve R).baseChange K).HasGoodSupersingularReduction R 3 := by
  have : IsIntegral R ((⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve R).baseChange K) := ⟨_, rfl⟩
  have hI := integralModel_eq_of_baseChange_eq (R := R) (W₀ := ⟨0, 0, 0, -1, 0⟩) (K := K) rfl
  have : ((⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve R).baseChange K).HasGoodReduction R := by
    rw [hasGoodReduction_iff_isUnit_integralModel_Δ, hI, ← residue_ne_zero_iff_isUnit]
    have hΔ : (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve R).Δ = 64 := by
      simp only [Δ, b₂, b₄, b₆, b₈]
      ring
    have h64 : (64 : ResidueField R) = 1 := by
      linear_combination (21 : ResidueField R) * CharP.ofNat_eq_zero (ResidueField R) 3
    rw [hΔ, map_ofNat, h64]
    exact one_ne_zero
  rw [hasGoodSupersingularReduction_iff_not_isUnit_b₂_of_char_three, hI]
  simp [b₂]

end WeierstrassCurve

end
