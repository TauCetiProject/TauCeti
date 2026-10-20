/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Henselian
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.NonsingularReduction
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Terminal
-- Proof-only: the sum of two points with singular reduction at a nonsplit node.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Two
-- Proof-only: the points with singular reduction when the reduction is singular at the origin.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.SingularReduction
-- Proof-only: index two from the sums of points outside a subgroup.
import TauCeti.GroupTheory.Index.Two
-- Proof-only: membership in the principal maximal ideal.
import TauCeti.RingTheory.LocalRing.MaximalIdeal.Generator

/-!
# Points with singular reduction at a nonsplit node of even order

Let `v` be a valuation on a field `F`, with valuation ring `O`, maximal ideal `𝔪` and residue field
`k`, and let `W` be an elliptic curve over `F` with an integral model `W_O` over `O` whose reduction
is a node at the origin with no rational tangent direction: `a₃, a₄, a₆ ∈ 𝔪` and the tangent
quadratic `T² + a₁ T − a₂` has no root in `k`. The points with nonsingular reduction form the
subgroup `E₀(F)` of `W(F)` (`WeierstrassCurve.Affine.nonsingularReduction`), whose index divides
`2` (`WeierstrassCurve.Affine.index_nonsingularReduction_dvd_two_of_tangentQuadratic_no_roots`).
For a discrete valuation, on a minimal equation, this is nonsplit multiplicative reduction of type
`Iₙ` with `n = ord(Δ)`, and Tate's algorithm reports the local index `c_v = gcd(2, n)`
(Silverman, *Advanced Topics*, IV.9, Table 4.1). When `n` is odd every point has nonsingular
reduction (`WeierstrassCurve.Affine.nonsingularReduction_eq_top_of_not_splits`). This file proves
the even case: when `Δ` is a unit times a square, `O` is Henselian and `k` is finite, some point
has singular reduction, so `[E(F) : E₀(F)] = 2`.

The equation-level construction in `Affine/Henselian.lean` proceeds in three steps over `O`
(`WeierstrassCurve.exists_equation_mem_maximalIdeal_of_tangentQuadratic_no_roots`).

* **Centring.** The singular point of the reduction lifts to a critical point `(r, t) ∈ 𝔪²` of the
  Weierstrass polynomial, and translating it to the origin makes `a₃ = a₄ = 0`
  (`WeierstrassCurve.exists_translate_a₃_eq_zero_and_a₄_eq_zero`). On the centred equation
  `y² + a₁ x y = x³ + a₂ x² + a₆` one has `Δ = −a₆ (b₂³ + 432 a₆)`, so `a₆` and `Δ` differ by a
  unit.
* **The residue conic.** Write `Δ` as a unit times `z²`, so that `a₆ = z² A` with `A` a unit.
  Along `(x, y) = (z X, z Y)` the centred equation divided by `z²` is
  `Y² + a₁ X Y − a₂ X² − z X³ = A`, whose reduction is the conic `Y² + a₁ X Y − a₂ X² = A`. Its
  quadratic part is the norm form of the quadratic extension `k[T]/(T² − a₁ T − a₂)` of `k`, and
  over a finite field the norm is surjective (`FiniteField.norm_surjective`), so the conic has a
  point.
* **Lifting.** The residue conic is smooth, since the discriminant `b₂` of its quadratic part is a
  unit, so one of the partial derivatives is a unit at the point, and Hensel's lemma in that
  variable lifts it to a solution `(X, Y)` over `O`. The solution `(z X, z Y)` of the centred
  equation has both coordinates in `𝔪`, and so does the corresponding point of `W`, which therefore
  has singular reduction.

The finiteness of `k` is used only to find a point on the residue conic, which over a general
residue field need not exist.

## Main results

* `WeierstrassCurve.exists_equation_mem_maximalIdeal_of_tangentQuadratic_no_roots`: over a
  Henselian local ring with finite residue field, an equation whose reduction is a nonsplit node
  at the origin, with `Δ` a unit times a square, has a solution in `𝔪 × 𝔪`. This is a converse of
  `WeierstrassCurve.exists_associated_sq_Δ_of_isSingular`.
* `WeierstrassCurve.Affine.exists_notMem_nonsingularReduction_of_tangentQuadratic_no_roots`: at a
  nonsplit node with `Δ` a unit times a square, over a Henselian valuation ring with finite residue
  field, some point has singular reduction.
* `WeierstrassCurve.Affine.index_nonsingularReduction_eq_two_of_tangentQuadratic_no_roots`: in the
  same situation, `[E(F) : E₀(F)] = 2`.
* `Affine.index_nonsingularReduction_eq_two_of_isTateTerminal_I_of_tangentQuadratic_no_roots`:
  when Tate's algorithm stops with the symbol `I₂ₘ` and the tangent quadratic has no root, that
  is at nonsplit multiplicative reduction of even type, `[E(F) : E₀(F)] = 2`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.6.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, IV.9.
* J. Tate, *Algorithm for determining the type of a singular fibre in an elliptic pencil*, in
  *Modular Functions of One Variable IV*, LNM 476 (1975), 33–52.
-/

public section

open IsLocalRing
open TauCeti.IsLocalRing (mem_maximalIdeal_iff_dvd)

namespace WeierstrassCurve


namespace Affine

variable {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀)
  {W : Affine F} [IsIntegral v.valuationSubring W] [DecidableEq F]

/-- **At a nonsplit node with `Δ` a unit times a square, some point has singular reduction**, when
the valuation ring is Henselian, for instance complete, and its residue field is finite. Here the
reduction of the integral model is singular at the origin, `a₃, a₄, a₆ ∈ 𝔪`, and its tangent
quadratic `T² + a₁ T − a₂` has no root in the residue field. For a discrete valuation, on a minimal
equation, this is nonsplit multiplicative reduction of type `Iₙ` with `n` even. -/
theorem exists_notMem_nonsingularReduction_of_tangentQuadratic_no_roots
    [HenselianLocalRing v.valuationSubring] [Finite (ResidueField v.valuationSubring)]
    [W.IsElliptic]
    (h₃ : (integralModel v.valuationSubring W).a₃ ∈ maximalIdeal v.valuationSubring)
    (h₄ : (integralModel v.valuationSubring W).a₄ ∈ maximalIdeal v.valuationSubring)
    (h₆ : (integralModel v.valuationSubring W).a₆ ∈ maximalIdeal v.valuationSubring)
    (hroot : ∀ t : ResidueField v.valuationSubring,
      t ^ 2 + residue _ (integralModel v.valuationSubring W).a₁ * t -
        residue _ (integralModel v.valuationSubring W).a₂ ≠ 0)
    {z : v.valuationSubring} (hΔ : Associated (z ^ 2) (integralModel v.valuationSubring W).Δ) :
    ∃ P : W.Point, P ∉ W.nonsingularReduction v := by
  obtain ⟨x, y, hx, hy, hE⟩ :=
    exists_equation_mem_maximalIdeal_of_tangentQuadratic_no_roots _ h₃ h₄ h₆ hroot hΔ
  have hF : W.Nonsingular x y :=
    W.equation_iff_nonsingular.1 ((equation_integralModel_iff v).1 hE)
  exact ⟨Point.some _ _ hF, (some_notMem_nonsingularReduction_iff v h₃ h₄ h₆ hF).2
    ⟨(Valuation.mem_maximalIdeal_iff (v := v)).1 hx,
      (Valuation.mem_maximalIdeal_iff (v := v)).1 hy⟩⟩

/-- **At a nonsplit node with `Δ` a unit times a square, `[E(F) : E₀(F)] = 2`**, when the valuation
ring is Henselian, for instance complete, and its residue field is finite. Here the reduction of
the integral model is singular at the origin, `a₃, a₄, a₆ ∈ 𝔪`, and its tangent quadratic
`T² + a₁ T − a₂` has no root in the residue field. For a discrete valuation, on a minimal equation,
this is nonsplit multiplicative reduction of type `Iₙ` with `n` even, where Tate's algorithm reports
the local index `2`. -/
theorem index_nonsingularReduction_eq_two_of_tangentQuadratic_no_roots
    [HenselianLocalRing v.valuationSubring] [Finite (ResidueField v.valuationSubring)]
    [W.IsElliptic]
    (h₃ : (integralModel v.valuationSubring W).a₃ ∈ maximalIdeal v.valuationSubring)
    (h₄ : (integralModel v.valuationSubring W).a₄ ∈ maximalIdeal v.valuationSubring)
    (h₆ : (integralModel v.valuationSubring W).a₆ ∈ maximalIdeal v.valuationSubring)
    (hroot : ∀ t : ResidueField v.valuationSubring,
      t ^ 2 + residue _ (integralModel v.valuationSubring W).a₁ * t -
        residue _ (integralModel v.valuationSubring W).a₂ ≠ 0)
    {z : v.valuationSubring} (hΔ : Associated (z ^ 2) (integralModel v.valuationSubring W).Δ) :
    (W.nonsingularReduction v).index = 2 := by
  obtain ⟨P, hP⟩ :=
    exists_notMem_nonsingularReduction_of_tangentQuadratic_no_roots v h₃ h₄ h₆ hroot hΔ
  exact AddSubgroup.index_eq_two_of_add_mem
    (fun _ _ ↦ add_mem_nonsingularReduction_of_tangentQuadratic_no_roots v h₃ h₄ h₆ hroot) hP

/-- **At nonsplit multiplicative reduction of even type `I₂ₘ`, `[E(F) : E₀(F)] = 2`**, when the
valuation ring is Henselian, for instance complete, and its residue field is finite. This is the
local index `c_v = 2` that Tate's algorithm reports there. Here `ϖ` generates the maximal ideal of
the valuation ring, Tate's algorithm, run on the integral model with uniformiser `ϖ`, stops with
the symbol `I₂ₘ` (`ϖ ∣ a₃`, `ϖ ∣ a₄`, `ϖ ∣ a₆`, `ϖ ∤ b₂` and `ϖ²ᵐ ∥ Δ`), and the tangent quadratic
`T² + a₁ T − a₂` has no root in the residue field. -/
theorem index_nonsingularReduction_eq_two_of_isTateTerminal_I_of_tangentQuadratic_no_roots
    [HenselianLocalRing v.valuationSubring] [Finite (ResidueField v.valuationSubring)]
    {ϖ : v.valuationSubring} (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ}) {m : ℕ}
    (hm : m ≠ 0) (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.I (2 * m)))
    (hroot : ∀ t : ResidueField v.valuationSubring,
      t ^ 2 + residue _ (integralModel v.valuationSubring W).a₁ * t -
        residue _ (integralModel v.valuationSubring W).a₂ ≠ 0) :
    (W.nonsingularReduction v).index = 2 := by
  set Wo := integralModel v.valuationSubring W
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
  -- `isTateTerminal_I_add_one` requires the index in successor form.
  rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring] at h
  obtain ⟨h₃, h₄, h₆, -, ⟨c, hc⟩, hn⟩ := isTateTerminal_I_add_one.1 h
  -- `Δ = ϖ^(2k + 2) c` with `c` a unit, since `ϖ^(2k + 3) ∤ Δ`
  have hcu : IsUnit c := by
    by_contra hcu
    obtain ⟨d, rfl⟩ := (mem_maximalIdeal_iff_dvd hϖ).1 ((mem_maximalIdeal _).2 hcu)
    exact hn ⟨d, by rw [hc]; ring⟩
  have : W.IsElliptic := ⟨isUnit_iff_ne_zero.2 fun h0 ↦ hn <| by
    rw [← integralModel_Δ_eq v.valuationSubring W,
      map_eq_zero_iff _ (IsFractionRing.injective v.valuationSubring F)] at h0
    rw [h0]
    exact dvd_zero _⟩
  exact index_nonsingularReduction_eq_two_of_tangentQuadratic_no_roots v
    ((mem_maximalIdeal_iff_dvd hϖ).2 h₃) ((mem_maximalIdeal_iff_dvd hϖ).2 h₄)
    ((mem_maximalIdeal_iff_dvd hϖ).2 h₆) hroot (z := ϖ ^ (k + 1))
    ⟨hcu.unit, by rw [hcu.unit_spec, hc]; ring⟩

end Affine

end WeierstrassCurve
