/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Two
public import TauCeti.AlgebraicGeometry.EllipticCurve.MinimalModel.Valuation
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.LocalIndex
-- Proof-only: centring a node, lifting its tangent directions, and `a₆` associated to `Δ` there.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Henselian
-- Proof-only: the point-group index at the symbols `Iₙ*` with `n ≥ 1`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Four
-- Proof-only: the point-group index at the symbol `IV*`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Index.Three
-- Proof-only: the point-group index at the symbol `I₀*`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Residue.Cubic
-- Proof-only: the point-group index at the symbol `IV`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Residue.Quadratic
-- Proof-only: every point has nonsingular reduction at the symbol `II*`.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.StarredReduction
-- Proof-only: the point-group index at a split node centred at the origin.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.SplitReduction
-- Proof-only: Tate's algorithm detects split multiplicative reduction.
import TauCeti.AlgebraicGeometry.EllipticCurve.TateAlgorithm.Reduction.Type
-- Proof-only: a translation does not change the discriminant.
import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Basic
-- Proof-only: membership in the principal maximal ideal.
import TauCeti.RingTheory.LocalRing.MaximalIdeal.Generator

/-!
# The point-group index reported by Tate's algorithm

Let `v` be a valuation on a field `F`, let `O` be its valuation ring with maximal ideal generated
by `ϖ`, and let `W` be an integral Weierstrass equation over `F`. The points with nonsingular
reduction form the subgroup `E₀(F)` of `W(F)`. When Tate's algorithm stops on the integral model,
its local index is supposed to equal `[W(F) : E₀(F)]`.

This file proves that equality for the seven additive symbols outside the family `Iₙ*` with
`n ≥ 1`. At `II` and `II*`, every point has nonsingular reduction. At `III` and `III*`, the index is
`2`. At `IV` and `IV*`, both indices are `3` precisely when the relevant residue quadratic has a
root and are `1` otherwise. The comparison in these two cases uses
`WeierstrassCurve.hasTateYRoot_iff_exists_residue_root` to identify the root test in the definition
of `WeierstrassCurve.tateLocalIndex` with the one used in the point-index theorems. At `I₀*`, both
indices are one more than the number of roots of the residue cubic, and
`WeierstrassCurve.natCard_tateCubicRoots_eq` identifies the roots in `O ⧸ (ϖ)` counted by the
local index with the roots in the residue field counted by the point-index theorem.

It also proves the equality at the symbols `Iₙ*` with `n ≥ 1`, where both indices are `4` when
the quadratic at which Step 7 of the algorithm stops has a root in the residue field and `2`
otherwise; the root tests are compared through
`WeierstrassCurve.hasTateYRoot_iff_exists_residue_root` and
`WeierstrassCurve.hasTateXRoot_iff_exists_residue_root`.

At the multiplicative symbols `Iₙ`, `n ≥ 1`, with split tangent quadratic `T² + a₁ T − a₂`, the
index is `n`, the local index the algorithm reports there. The stopping equation only has its node
at the origin modulo `ϖ`; a translation by elements of the maximal ideal moves the node itself to
the origin, so that `a₃ = a₄ = 0`, and Hensel's lemma lifts the tangent directions. On that centred
equation `Δ = -a₆ (b₂³ + 432 a₆)` with the second factor a unit, so `v(a₆) = v(Δ) = v(ϖ)ⁿ`, and the
index is computed by
`WeierstrassCurve.Affine.index_nonsingularReduction_eq_of_tangentQuadratic_root`.
The translation does not change the index, because it is defined over the valuation ring
(`WeierstrassCurve.Affine.index_nonsingularReduction_baseChange_smul`).

For a Henselian discrete valuation ring with perfect residue field this gives the order of
`E(F) / E₀(F)` at split multiplicative reduction intrinsically: on a minimal equation it is the
valuation `v(Δ_min)` of the minimal discriminant (Silverman, *The Arithmetic of Elliptic Curves*,
VII.6.1), since Tate's algorithm stops at `I_{v(Δ_min)}` after a change of variables over the
valuation ring.

## Main results

* `index_nonsingularReduction_eq_tateLocalIndex_of_ne_I_of_ne_IStar_add_one`, in the namespace
  `WeierstrassCurve.Affine`: at every additive symbol outside `Iₙ*` with `n ≥ 1`, the point-group
  index is the local index reported by Tate's algorithm.
* `index_nonsingularReduction_eq_tateLocalIndex_of_isTateTerminal_IStar_add_one`, in the namespace
  `WeierstrassCurve.Affine`: at `Iₙ*` with `n ≥ 1`, the point-group index is the local index
  reported by Tate's algorithm.
* `WeierstrassCurve.Affine.index_nonsingularReduction_eq_of_isTateTerminal_I_of_hasTateTangentRoot`:
  at `Iₙ` with `n ≥ 1` and split tangent quadratic, the point-group index is `n`.
* `WeierstrassCurve.Affine.index_nonsingularReduction_eq_localMinimalDiscriminantValuation`: at
  split multiplicative reduction, the index of `E₀` for a minimal equation is the valuation of the
  minimal discriminant.

## References

* J. H. Silverman, *The Arithmetic of Elliptic Curves*, GTM 106, 2nd ed., VII.6.1.
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, IV.9.
* J. Tate, *Algorithm for determining the type of a singular fibre in an elliptic pencil*, in
  *Modular Functions of One Variable IV*, LNM 476 (1975), 33–52.
-/

public section

open IsLocalRing
open TauCeti.IsLocalRing (isUnit_iff_not_dvd mem_maximalIdeal_iff_dvd)

namespace WeierstrassCurve

/-- **Centring a split stopping equation at `Iₙ`.** Over a Henselian local ring whose maximal ideal
is generated by `ϖ`, if Tate's algorithm stops on `W` at `Iₙ` with `n ≥ 1` and the tangent
quadratic has a root modulo `ϖ`, then a translation over the ring makes `a₃ = a₄ = 0`, keeps `b₂` a
unit, gives the tangent quadratic a root, and makes `a₆` the product of `ϖⁿ` and a unit. -/
private theorem exists_variableChange_of_isTateTerminal_I_of_hasTateTangentRoot {R : Type*}
    [CommRing R] [HenselianLocalRing R] {W : WeierstrassCurve R} {ϖ : R}
    (hϖ : maximalIdeal R = Ideal.span {ϖ}) {n : ℕ} (h : W.IsTateTerminal ϖ (.I (n + 1)))
    (hroot : W.HasTateTangentRoot ϖ) :
    ∃ C : VariableChange R, (C • W).a₃ = 0 ∧ (C • W).a₄ = 0 ∧ IsUnit (C • W).b₂ ∧
      (∃ α : R, α ^ 2 + (C • W).a₁ * α - (C • W).a₂ = 0) ∧
      ∃ w : Rˣ, (C • W).a₆ = ϖ ^ (n + 1) * w := by
  obtain ⟨h₃, h₄, h₆, hb₂, ⟨c, hc⟩, hn⟩ := isTateTerminal_I_add_one.1 h
  have hres {z : R} (hz : ϖ ∣ z) : residue R z = 0 :=
    (residue_eq_zero_iff _).2 ((mem_maximalIdeal_iff_dvd hϖ).2 hz)
  -- move the node of the reduction to the origin
  have hb₂' : IsUnit W.b₂ := (isUnit_iff_not_dvd hϖ).2 hb₂
  obtain ⟨r, t, hr, ht, e₃, e₄⟩ := W.exists_translate_a₃_eq_zero_and_a₄_eq_zero
    ((mem_maximalIdeal_iff_dvd hϖ).2 h₃) ((mem_maximalIdeal_iff_dvd hϖ).2 h₄) hb₂'
  set V := VariableChange.mk 1 r 0 t • W
  have hr0 : residue R r = 0 := (residue_eq_zero_iff _).2 hr
  have ht0 : residue R t = 0 := (residue_eq_zero_iff _).2 ht
  have hVb₂ : IsUnit V.b₂ := by
    rw [← residue_ne_zero_iff_isUnit]
    simpa [V, variableChange_b₂, hr0] using (residue_ne_zero_iff_isUnit _).2 hb₂'
  have hV₆ : residue R V.a₆ = 0 := by
    simp [V, variableChange_a₆, hr0, ht0, hres h₃, hres h₄, hres h₆]
  -- the tangent quadratic keeps its root modulo `ϖ`, which lifts
  obtain ⟨t₀, ht₀⟩ := hasTateTangentRoot_def.1 hroot
  obtain ⟨α, hα, -⟩ := V.exists_tangentQuadratic_eq_zero hVb₂ (t₀ := t₀) <| by
    have h0 := hres ht₀
    rw [← residue_eq_zero_iff]
    simp only [map_sub, map_add, map_mul, map_pow] at h0
    simp [V, variableChange_a₁, variableChange_a₂, hr0]
    linear_combination h0
  -- `a₆` is associated to `Δ = ϖ^(n+1) c`, with `c` a unit
  have hc' : IsUnit c := (isUnit_iff_not_dvd hϖ).2 fun ⟨d, hd⟩ ↦ hn ⟨d, by rw [hc, hd]; ring⟩
  obtain ⟨u, hu⟩ := associated_a₆_Δ_of_a₃_eq_zero_of_a₄_eq_zero e₃ e₄
    ((residue_eq_zero_iff _).1 hV₆) hVb₂
  have hΔ : V.a₆ * u = ϖ ^ (n + 1) * c := hu.trans ((variableChange_translate_Δ ..).trans hc)
  refine ⟨_, e₃, e₄, hVb₂, ⟨α, hα⟩, (hc'.mul u⁻¹.isUnit).unit, ?_⟩
  rw [IsUnit.unit_spec]
  linear_combination (↑u⁻¹ : R) * hΔ - V.a₆ * u.mul_inv

namespace Affine

variable {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀)
  {W : Affine F} [IsIntegral v.valuationSubring W] [DecidableEq F]

/-- **At every additive symbol outside `Iₙ*` with `n ≥ 1`, Tate's local index is the point-group
index.** Suppose that `ϖ` generates the maximal ideal of the Henselian valuation ring, its residue
field is perfect, and Tate's algorithm stops on the integral model at a symbol other than `Iₙ` or
`Iₙ*` with `n ≥ 1`. Then the reported local index equals `[W(F) : E₀(F)]`.

The perfectness assumption is used at the symbol `III`, to lift the double tangent direction; the
other six symbols are already covered without it by their individual point-index theorems. -/
theorem index_nonsingularReduction_eq_tateLocalIndex_of_ne_I_of_ne_IStar_add_one
    [HenselianLocalRing v.valuationSubring] [PerfectField (ResidueField v.valuationSubring)]
    {ϖ : v.valuationSubring} (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ})
    {s : TauCeti.ReductionSymbol} (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ s)
    (hsI : ∀ n, s ≠ .I n) (hsIStar : ∀ n, s ≠ .IStar (n + 1)) :
    (W.nonsingularReduction v).index =
      (integralModel v.valuationSubring W).tateLocalIndex ϖ s := by
  classical
  let Wo := integralModel v.valuationSubring W
  rcases s with (_ | n) | _ | _ | _ | (_ | n) | _ | _ | _
  · exact absurd rfl (hsI 0)
  · exact absurd rfl (hsI (n + 1))
  · obtain ⟨-, h₃, h₄, h₆, h₆'⟩ := isTateTerminal_II.1 h
    have hm₂ (z : v.valuationSubring) : z ∈ maximalIdeal v.valuationSubring ^ 2 ↔ ϖ ^ 2 ∣ z := by
      rw [hϖ, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rw [nonsingularReduction_eq_top_of_a₆_notMem v ((mem_maximalIdeal_iff_dvd hϖ).2 h₃)
      ((mem_maximalIdeal_iff_dvd hϖ).2 h₄) ((mem_maximalIdeal_iff_dvd hϖ).2 h₆)
      (fun ha₆ ↦ h₆' ((hm₂ _).1 ha₆)), AddSubgroup.index_top]
    exact tateLocalIndex_II.symm
  · rw [index_nonsingularReduction_eq_two_of_isTateTerminal_III v hϖ h]
    exact tateLocalIndex_III.symm
  · obtain ⟨-, ⟨A₃, h₃⟩, -, ⟨A₆, h₆⟩, -, -⟩ := isTateTerminal_IV.1 h
    have hϖ0 : ϖ ≠ 0 := h.ne_zero (by simp)
    have hroot := hasTateYRoot_iff_exists_residue_root (W := Wo) (m := 1) hϖ hϖ0
      (by simpa [Wo] using h₃) (by simpa [Wo] using h₆)
    by_cases hr : Wo.HasTateYRoot ϖ 1
    · obtain ⟨t, ht⟩ := hroot.mp hr
      rw [index_nonsingularReduction_eq_three_of_isTateTerminal_IV v hϖ h h₃ h₆ ht]
      exact (tateLocalIndex_IV_of_hasTateYRoot hr).symm
    · have hnroot (t : ResidueField v.valuationSubring) :
          t ^ 2 + residue _ A₃ * t - residue _ A₆ ≠ 0 := by
        intro ht
        exact hr (hroot.mpr ⟨t, ht⟩)
      rw [nonsingularReduction_eq_top_of_isTateTerminal_IV v hϖ h h₃ h₆ hnroot,
        AddSubgroup.index_top]
      exact (tateLocalIndex_IV_of_not_hasTateYRoot hr).symm
  · obtain ⟨-, ⟨A₂, h₂⟩, -, ⟨A₄, h₄⟩, ⟨A₆, h₆⟩, -⟩ := isTateTerminal_IStar_zero.1 h
    rw [index_nonsingularReduction_eq_of_isTateTerminal_IStar_zero v hϖ h h₂ h₄ h₆,
      tateLocalIndex_IStar_zero, natCard_tateCubicRoots_eq hϖ (h.ne_zero (by simp)) h₂ h₄ h₆]
  · exact absurd rfl (hsIStar n)
  · obtain ⟨-, -, ⟨A₃, h₃⟩, -, ⟨A₆, h₆⟩, -⟩ := isTateTerminal_IVStar.1 h
    have hϖ0 : ϖ ≠ 0 := h.ne_zero (by simp)
    have hroot := hasTateYRoot_iff_exists_residue_root (W := Wo) (m := 2) hϖ hϖ0
      (by simpa [Wo] using h₃) (by norm_num [Wo]; exact h₆)
    by_cases hr : Wo.HasTateYRoot ϖ 2
    · rw [index_nonsingularReduction_eq_three_of_isTateTerminal_IVStar v hϖ h h₃ h₆
        (hroot.mp hr)]
      exact (tateLocalIndex_IVStar_of_hasTateYRoot hr).symm
    · have hnroot (t : ResidueField v.valuationSubring) :
          t ^ 2 + residue _ A₃ * t - residue _ A₆ ≠ 0 := by
        intro ht
        exact hr (hroot.mpr ⟨t, ht⟩)
      rw [nonsingularReduction_eq_top_of_isTateTerminal_IVStar v hϖ h h₃ h₆ hnroot,
        AddSubgroup.index_top]
      exact (tateLocalIndex_IVStar_of_not_hasTateYRoot hr).symm
  · rw [index_nonsingularReduction_eq_two_of_isTateTerminal_IIIStar v hϖ h]
    exact tateLocalIndex_IIIStar.symm
  · rw [nonsingularReduction_eq_top_of_isTateTerminal_IIStar v hϖ h,
      AddSubgroup.index_top]
    exact tateLocalIndex_IIStar.symm

/-- **At the reduction symbol `Iₙ*` with `n ≥ 1`, Tate's local index is the point-group index.**
Suppose that `ϖ` generates the maximal ideal of the Henselian valuation ring, and that Tate's
algorithm, run on the integral model with uniformiser `ϖ`, stops with the symbol `Iₙ*` for some
`n ≥ 1`. Then `[W(F) : E₀(F)]` is the local index that the algorithm reports: `4` if the quadratic
at which the subprocedure of Step 7 stops has a root in the residue field, and `2` otherwise. -/
theorem index_nonsingularReduction_eq_tateLocalIndex_of_isTateTerminal_IStar_add_one
    [HenselianLocalRing v.valuationSubring] {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ}) {n : ℕ}
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.IStar (n + 1))) :
    (W.nonsingularReduction v).index =
      (integralModel v.valuationSubring W).tateLocalIndex ϖ (.IStar (n + 1)) := by
  classical
  have hϖ0 : ϖ ≠ 0 := h.ne_zero (by simp)
  rcases isTateTerminal_IStar_add_one.1 h with ⟨k, rfl, hk, -⟩ | ⟨k, rfl, hk, -⟩
  · obtain ⟨-, -, -, ⟨A₃, h₃⟩, -, ⟨A₆, h₆⟩⟩ := isTateOddStage_iff.1 hk
    have hroot := hasTateYRoot_iff_exists_residue_root (m := k + 2) (b₆ := A₆) hϖ hϖ0 h₃
      (by rw [h₆]; ring)
    rw [tateLocalIndex_IStar_odd]
    split_ifs with hr
    · obtain ⟨t, ht⟩ := hroot.1 hr
      exact index_nonsingularReduction_eq_four_of_isTateTerminal_IStar_two_mul_add_one v hϖ h h₃
        h₆ ht
    · exact index_nonsingularReduction_eq_two_of_isTateTerminal_IStar_two_mul_add_one v hϖ h h₃
        h₆ fun t ht ↦ hr (hroot.2 ⟨t, ht⟩)
  · obtain ⟨-, ⟨A₂, h₂⟩, -, -, ⟨A₄, h₄⟩, ⟨A₆, h₆⟩⟩ := isTateEvenStage_iff.1 hk
    have hroot := hasTateXRoot_iff_exists_residue_root (m := k + 2) (b₆ := A₆) hϖ hϖ0 h₂ h₄
      (by rw [h₆]; ring)
    rw [tateLocalIndex_IStar_even]
    split_ifs with hr
    · obtain ⟨t, ht⟩ := hroot.1 hr
      exact index_nonsingularReduction_eq_four_of_isTateTerminal_IStar_two_mul_add_two v hϖ h h₂
        h₄ h₆ ht
    · exact index_nonsingularReduction_eq_two_of_isTateTerminal_IStar_two_mul_add_two v hϖ h h₂
        h₄ h₆ fun t ht ↦ hr (hroot.2 ⟨t, ht⟩)

/-- **At split multiplicative reduction `Iₙ`, the point-group index is `n`.** Suppose that `ϖ`
generates the maximal ideal of the Henselian valuation ring, that Tate's algorithm, run on the
integral model with uniformiser `ϖ`, stops with the symbol `Iₙ` for some `n ≥ 1`, and that the
tangent quadratic `T² + a₁ T − a₂` has a root modulo `ϖ`. Then `[W(F) : E₀(F)] = n`, which is the
local index the algorithm reports there
(`WeierstrassCurve.tateLocalIndex_I_add_one_of_hasTateTangentRoot`). -/
theorem index_nonsingularReduction_eq_of_isTateTerminal_I_of_hasTateTangentRoot
    [HenselianLocalRing v.valuationSubring] {ϖ : v.valuationSubring}
    (hϖ : maximalIdeal v.valuationSubring = Ideal.span {ϖ}) {n : ℕ}
    (h : (integralModel v.valuationSubring W).IsTateTerminal ϖ (.I (n + 1)))
    (hroot : (integralModel v.valuationSubring W).HasTateTangentRoot ϖ) :
    (W.nonsingularReduction v).index = n + 1 := by
  obtain ⟨C, e₃, e₄, hb₂, ⟨α, hα⟩, w, e₆⟩ :=
    exists_variableChange_of_isTateTerminal_I_of_hasTateTangentRoot hϖ h hroot
  -- the index is that of the centred model `C • W` over `F`, whose integral model is `C • W_O`
  rw [← index_nonsingularReduction_baseChange_smul v C]
  have hW : integralModel v.valuationSubring (C.baseChange F • W) =
      C • integralModel v.valuationSubring W :=
    integralModel_baseChange_smul _ W C
  have : W.IsElliptic := ⟨by
    rw [← integralModel_Δ_eq v.valuationSubring, isUnit_iff_ne_zero, map_ne_zero_iff _
      (FaithfulSMul.algebraMap_injective _ F)]
    obtain ⟨-, -, -, -, -, hΔ⟩ := isTateTerminal_I_add_one.1 h
    exact fun h0 ↦ hΔ (h0 ▸ dvd_zero _)⟩
  refine index_nonsingularReduction_eq_of_tangentQuadratic_root (W := (C.baseChange F • W).toAffine)
    (α := α) ?_ ?_ ?_ ?_ hϖ n.succ_pos ?_
  · rw [← coe_integralModel_a₃ v, hW, e₃, ZeroMemClass.coe_zero]
  · rw [← coe_integralModel_a₄ v, hW, e₄, ZeroMemClass.coe_zero]
  · rw [← integralModel_b₂_eq v.valuationSubring, hW, ValuationSubring.algebraMap_apply]
    exact (Valuation.valuationSubring.integers v).one_of_isUnit hb₂
  · rw [← coe_integralModel_a₁ v, ← coe_integralModel_a₂ v, hW]
    simpa using congrArg Subtype.val hα
  · have hw : v ((w : v.valuationSubring) : F) = 1 :=
      (Valuation.valuationSubring.integers v).one_of_isUnit w.isUnit
    rw [← coe_integralModel_a₆ v, hW, e₆, MulMemClass.coe_mul, map_mul, hw, mul_one,
      SubmonoidClass.coe_pow, map_pow]

/-- **At split multiplicative reduction, `[E(F) : E₀(F)] = v(Δ_min)`** (Silverman, *The Arithmetic
of Elliptic Curves*, VII.6.1). Let the valuation ring of `v` be a Henselian discrete valuation ring
with perfect residue field, and let `E` be an elliptic curve over `F` given by a minimal equation
with split multiplicative reduction. Then the subgroup `E₀(F)` of points with nonsingular reduction
has index the valuation of the minimal discriminant. Perfectness of the residue field is used only
to run Tate's algorithm (`WeierstrassCurve.exists_isTateTerminal`) on the minimal equation. -/
theorem index_nonsingularReduction_eq_localMinimalDiscriminantValuation
    [IsDiscreteValuationRing v.valuationSubring] [HenselianLocalRing v.valuationSubring]
    [PerfectField (ResidueField v.valuationSubring)] (E : WeierstrassCurve F) [E.IsElliptic]
    [E.HasSplitMultiplicativeReduction v.valuationSubring] :
    (E.toAffine.nonsingularReduction v).index =
      E.localMinimalDiscriminantValuation v.valuationSubring := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible v.valuationSubring
  set Eo := integralModel v.valuationSubring E
  have hE : Eo.baseChange F = E := baseChange_integralModel_eq _ E
  have : IsMinimal v.valuationSubring (Eo.baseChange F) := by rw [hE]; infer_instance
  have hΔ : Eo.Δ ≠ 0 := fun h0 ↦ E.isUnit_Δ.ne_zero <| by
    rw [← integralModel_Δ_eq v.valuationSubring E, h0, map_zero]
  -- run Tate's algorithm on the minimal equation
  obtain ⟨C, s, hC⟩ := exists_isTateTerminal (K := F) hϖ Eo hΔ
  have hCE : (C • Eo).baseChange F = C.baseChange F • E := by
    rw [← integralModel_baseChange_smul, baseChange_integralModel_eq]
  -- it stops at a symbol `Iₙ`, with split tangent quadratic
  obtain ⟨n, rfl⟩ := (hC.hasMultiplicativeReduction_iff hϖ).1 <| by
    rw [hCE, hasMultiplicativeReduction_baseChange_smul_iff]
    infer_instance
  have hroot : (C • Eo).HasTateTangentRoot ϖ := (hasTateTangentRoot_iff_splits hϖ).2 <|
    (hC.hasSplitMultiplicativeReduction_iff hϖ).1 <| by
      rw [hCE, hasSplitMultiplicativeReduction_baseChange_smul_iff]
      infer_instance
  have hint : integralModel v.valuationSubring (C.baseChange F • E) = C • Eo :=
    integralModel_baseChange_smul _ E C
  have : ((C • Eo).baseChange F).IsElliptic := by rw [hCE]; infer_instance
  rw [← index_nonsingularReduction_baseChange_smul v C,
    index_nonsingularReduction_eq_of_isTateTerminal_I_of_hasTateTangentRoot v hϖ.maximalIdeal_eq
      (hint ▸ hC) (hint ▸ hroot), ← hC.localMinimalDiscriminantValuation_eq (K := F) hϖ]
  simp only [hCE, localMinimalDiscriminantValuation_smul]

end Affine

end WeierstrassCurve

end
