/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Assoc
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Addition.Points
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.FormalPoint
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.PairSubst
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Point
import TauCeti.AlgebraicGeometry.EllipticCurve.Universal

/-!
# The addition morphism at the formal point

Let `W` be a Weierstrass curve over a commutative ring `R`, let `E = projModel W` be its projective
model, and let `z₁` and `z₂` be the two variables of `R⟦z₁, z₂⟧ = MvPowerSeries (Unit ⊕ Unit) R`.
In the parameter `z = -X / Y` at the zero section, the formal point of `E`
(`WeierstrassCurve.projModelFormalPoint`) reparametrised by `X ↦ zᵢ` has homogeneous coordinates
`[zᵢ : -1 : w(zᵢ)]`, where `w` is the `w`-expansion `formalW W`. This file proves that the
Bosma–Lenstra addition morphism `E ×_{Spec R} E ⟶ E` sends this pair of points to the formal point
reparametrised by `X ↦ F(z₁, z₂)`, where `F = formalAdd W` is the addition series of the chord
construction (`WeierstrassCurve.lift_projModelFormalPoint_additionMorphism`). In other words, the
group law of `E`, written in the formal parameter along the zero section, is the formal group law
`F` (packaged as Mathlib's `FormalGroup` in `WeierstrassCurve.formalGroup`). It is the input for
reading statements about closed subschemes of `E` supported on the zero section, such as the
divisors `n[0]` being subgroup schemes, as statements about `F`.

The computation is algebraic. The `Y`-coordinate of the addition law `dblAddXYZ`, attached to the
line `Y = 0`, is a unit at the two points (`WeierstrassCurve.isUnit_dblAddY_formalW`): both points
restrict to `[0 : -1 : 0]` at `z₁ = z₂ = 0`, where the law takes the value `[0 : 1 : 0]`. So the
addition morphism is computed by that law, and its value is a unit multiple of
`(F(z₁, z₂), -1, w(F(z₁, z₂)))` (`WeierstrassCurve.dblAddXYZ_formalW_eq_smul`). That identity is
first proved over a domain with nonzero discriminant, in particular for the universal curve over
`ℤ[A₁, ⋯, A₆]`. There, over a fraction field of the power series ring, `dblAddXYZ` represents the
sum of the two points in the group law of the curve
(`WeierstrassCurve.Projective.dblAddXYZ_equiv_add`), and that sum is the point with parameter `F`
(`WeierstrassCurve.thetaPoint_add_of_subst_separates`). Base change along
`WeierstrassCurve.specialize` then gives it for every `W`. No hypothesis is placed on `R`; in
particular `R` need not be reduced.

## Main definitions

* `WeierstrassCurve.formalParamVec`: the projective coordinate triple `[q : -1 : w(q)]` in an
  `MvPowerSeries σ O`-algebra `KK` attached to a parameter series `q`.
* `WeierstrassCurve.formalParamPoint`: the affine point on `W⁄KK` represented by
  `W.formalParamVec q` over a field `KK`.

## Main results

* `WeierstrassCurve.nonsingular_fracCurve_formalParamVec` and
  `WeierstrassCurve.nonsingular_formalParamVec`: for any substitutable series `q`, `[q : -1 : w(q)]`
  is nonsingular in every nontrivial commutative algebra `KK` over `MvPowerSeries σ O`, with no
  discriminant hypothesis on `W`.
* `WeierstrassCurve.toAffine_fracCurve_formalParamVec_eq_thetaPoint`: over a fraction field `KK` of
  `MvPowerSeries σ O`, for a nonzero parameter `q` with zero constant coefficient, the affine point
  represented by `W.formalParamVec q` on `fracCurve W σ KK` is `W.thetaPoint`.
* `WeierstrassCurve.isUnit_dblAddY_formalW` and
  `WeierstrassCurve.isUnit_dblAddY_formalW_subst_pair`: the `Y`-coordinate of `dblAddXYZ` at
  `[z₁ : -1 : w(z₁)]`, `[z₂ : -1 : w(z₂)]` — and more generally at any pair `(q₁, q₂)` of
  substitutable series over an `R`-algebra — is a unit.
* `WeierstrassCurve.dblAddXYZ_formalW_eq_smul` and
  `WeierstrassCurve.dblAddXYZ_formalW_subst_pair_eq_smul`: the value of `dblAddXYZ` at these points
  is a unit multiple of `(F, -1, w(F))`.
* `WeierstrassCurve.formalParamPoint_subst_pair_formalAdd`: specialising `dblAddXYZ_formalW_eq_smul`
  along any pair of substitutable series `(q₁, q₂)` identifies `formalAdd W` with point addition on
  `W⁄KK`, unconditionally for every Weierstrass curve `W`.
* `WeierstrassCurve.exists_formalParamPoint_eq_some_of_algebraMap_ne_zero`,
  `WeierstrassCurve.formalParamPoint_eq_some_of_algebraMap_ne_zero`,
  `WeierstrassCurve.formalParamPoint_eq_zero_iff`,
  `WeierstrassCurve.algebraMap_eq_of_formalParamPoint_eq`, and
  `WeierstrassCurve.formalParamPoint_inj`: affine-coordinate, zero-fibre, and injectivity results
  for `formalParamPoint`.
* `WeierstrassCurve.lift_projModelFormalPoint_additionMorphism`: the addition morphism sends the
  pair of formal points reparametrised by `X ↦ z₁` and `X ↦ z₂` to the formal point
  reparametrised by `X ↦ F(z₁, z₂)`.

## References

* W. Bosma and H. W. Lenstra, Jr., *Complete systems of two addition laws for elliptic curves*,
  J. Number Theory 53 (1995), 229–240.
* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.
* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, §5.3, where the formal group law of an elliptic curve in a
  parameter along the zero section is used to study subgroup schemes supported on the zero section.
-/

public section

open CategoryTheory Limits AlgebraicGeometry MvPowerSeries

namespace WeierstrassCurve

section Algebra

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The `Y`-coordinate of the Bosma–Lenstra addition law `dblAddXYZ` at the points
`[z₁ : -1 : w(z₁)]` and `[z₂ : -1 : w(z₂)]` with parameters the two variables of `R⟦z₁, z₂⟧` is a
unit: at `z₁ = z₂ = 0` it is the value `1` of the law at the point at infinity, taken twice. -/
theorem isUnit_dblAddY_formalW :
    IsUnit ((W.toProjective.map (algebraMap R (MvPowerSeries (Unit ⊕ Unit) R))).dblAddY
      ![X (Sum.inl ()), -1, PowerSeries.subst (X (Sum.inl ())) W.formalW]
      ![X (Sum.inr ()), -1, PowerSeries.subst (X (Sum.inr ())) W.formalW]) := by
  have hc (q : MvPowerSeries (Unit ⊕ Unit) R) (hq : constantCoeff q = 0) :
      constantCoeff ∘ ![q, -1, PowerSeries.subst q W.formalW] = ![0, -1, 0] := by
    funext k
    fin_cases k
    · simpa using hq
    · simp
    · simpa using PowerSeries.constantCoeff_subst_eq_zero hq _ W.constantCoeff_formalW
  rw [isUnit_iff_constantCoeff, ← Projective.map_dblAddY, hc _ (constantCoeff_X _),
    hc _ (constantCoeff_X _)]
  simp [Projective.dblAddY]

section FormalParamVec

variable {O : Type*} [CommRing O] (W : WeierstrassCurve O) {σ : Type*}
  {KK : Type*} [CommRing KK] [Algebra (MvPowerSeries σ O) KK]

/-- The projective coordinate triple `[q : -1 : w(q)]` in `KK` attached to a parameter series `q`,
where `w = W.formalW` is the `w`-expansion of `W`. -/
noncomputable def formalParamVec (q : MvPowerSeries σ O) : Fin 3 → KK :=
  algebraMap (MvPowerSeries σ O) KK ∘ ![q, -1, PowerSeries.subst q W.formalW]

/-- Characterization of `formalParamVec` as `algebraMap (MvPowerSeries σ O) KK ∘ ![q, -1, w(q)]`. -/
theorem formalParamVec_def (q : MvPowerSeries σ O) :
    W.formalParamVec (KK := KK) q =
      algebraMap (MvPowerSeries σ O) KK ∘ ![q, -1, PowerSeries.subst q W.formalW] :=
  (rfl)

@[simp]
theorem formalParamVec_apply_zero (q : MvPowerSeries σ O) :
    W.formalParamVec (KK := KK) q 0 = algebraMap (MvPowerSeries σ O) KK q := by
  simp [formalParamVec]

@[simp]
theorem formalParamVec_apply_one (q : MvPowerSeries σ O) :
    W.formalParamVec (KK := KK) q 1 = -1 := by
  simp [formalParamVec]

@[simp]
theorem formalParamVec_apply_two (q : MvPowerSeries σ O) :
    W.formalParamVec (KK := KK) q 2 =
      algebraMap (MvPowerSeries σ O) KK (PowerSeries.subst q W.formalW) := by
  simp [formalParamVec]

/-- The zero parameter gives the projective triple `[0 : -1 : 0]`. -/
@[simp]
theorem formalParamVec_zero :
    W.formalParamVec (KK := KK) (0 : MvPowerSeries σ O) = ![0, -1, 0] := by
  funext k
  fin_cases k <;>
    simp [formalParamVec, PowerSeries.subst_zero_of_constantCoeff_zero W.constantCoeff_formalW]

/-- For any substitutable parameter series `q`, the projective point `[q : -1 : w(q)]` on
`fracCurve W σ KK` is nonsingular in every nontrivial commutative algebra `KK` over
`MvPowerSeries σ O` (with no discriminant hypothesis on `W`). -/
theorem nonsingular_fracCurve_formalParamVec [Nontrivial KK] {q : MvPowerSeries σ O}
    (hq : PowerSeries.HasSubst q) :
    (fracCurve W σ KK).toProjective.Nonsingular (W.formalParamVec (KK := KK) q) := by
  refine (Projective.nonsingular_iff _).mpr ⟨?_, Or.inr (Or.inr ?_)⟩
  · rw [formalParamVec_def, fracCurve_def, ← map_map]
    exact ((W.toProjective.equation_neg_one_iff_wEquation q _).mpr
      (W.subst_formalW_wEquation hq)).map _
  · set w : MvPowerSeries σ O := PowerSeries.subst q W.formalW
    set ρ := algebraMap (MvPowerSeries σ O) KK
    set z : MvPowerSeries σ O :=
      1 - (C W.a₁ * q + 2 * C W.a₃ * w +
        (C W.a₂ * q ^ 2 + 2 * C W.a₄ * q * w + 3 * C W.a₆ * w ^ 2))
    have hq_nil : constantCoeff q ∈ nilradical O := hq
    have hw_nil : constantCoeff w ∈ nilradical O := by
      rw [mem_nilradical]
      dsimp only [w]
      rw [PowerSeries.subst_def]
      exact MvPowerSeries.IsNilpotent_subst hq.const (by
        rw [← PowerSeries.constantCoeff_eq, W.constantCoeff_formalW]
        exact IsNilpotent.zero)
    have ht_nil : IsNilpotent (W.a₁ * constantCoeff q + 2 * W.a₃ * constantCoeff w +
        (W.a₂ * constantCoeff q ^ 2 + 2 * W.a₄ * constantCoeff q * constantCoeff w +
          3 * W.a₆ * constantCoeff w ^ 2)) := by
      rw [← mem_nilradical]
      refine add_mem (add_mem (Ideal.mul_mem_left _ _ hq_nil) (Ideal.mul_mem_left _ _ hw_nil))
        (add_mem (add_mem ?_ ?_) ?_)
      · rw [pow_two, ← mul_assoc]; exact Ideal.mul_mem_left _ _ hq_nil
      · exact Ideal.mul_mem_left _ _ hw_nil
      · rw [pow_two, ← mul_assoc]; exact Ideal.mul_mem_left _ _ hw_nil
    have hz : IsUnit z := by
      rw [isUnit_iff_constantCoeff]
      simpa [z, map_sub, map_add, map_mul, map_pow, map_ofNat] using ht_nil.isUnit_one_sub
    refine ne_of_eq_of_ne ?_ (hz.map ρ).ne_zero
    simp only [z, w, ρ, fracCurve_def, toProjective, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆,
      RingHom.comp_apply, formalParamVec_apply_zero, formalParamVec_apply_one,
      formalParamVec_apply_two, ← c_eq_algebraMap, map_sub, map_add, map_mul, map_pow, map_one,
      map_ofNat]
    ring

/-- For any substitutable parameter series `q`, the projective point `[q : -1 : w(q)]` on `W⁄KK` is
nonsingular in every nontrivial commutative `O`-algebra `KK` compatible with
`O → MvPowerSeries σ O → KK` (with no discriminant hypothesis on `W`). -/
theorem nonsingular_formalParamVec [Nontrivial KK] [Algebra O KK]
    [IsScalarTower O (MvPowerSeries σ O) KK] {q : MvPowerSeries σ O}
    (hq : PowerSeries.HasSubst q) :
    (W⁄KK).toProjective.Nonsingular (W.formalParamVec (KK := KK) q) := by
  rw [← W.fracCurve_eq_baseChange σ KK]
  exact W.nonsingular_fracCurve_formalParamVec hq

end FormalParamVec

section FractionField

variable {O : Type*} [CommRing O] (W : WeierstrassCurve O) {σ : Type*}
  {KK : Type*} [Field KK] [Algebra (MvPowerSeries σ O) KK]
  [IsFractionRing (MvPowerSeries σ O) KK]

/-- For a nonzero parameter `q` with zero constant coefficient, the affine point represented by
`W.formalParamVec q` on `fracCurve W σ KK` is `W.thetaPoint`. -/
theorem toAffine_fracCurve_formalParamVec_eq_thetaPoint (hΔ : (fracCurve W σ KK).Δ ≠ 0)
    {q : MvPowerSeries σ O} (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    Projective.Point.toAffine (fracCurve W σ KK).toProjective
      (W.formalParamVec (KK := KK) q) = W.thetaPoint hΔ hq hq0 := by
  have hz : W.formalParamVec (KK := KK) q 2 ≠ 0 := by
    rw [formalParamVec_apply_two]
    exact W.algebraMap_subst_formalW_ne_zero hq hq0
  have hN := W.nonsingular_fracCurve_formalParamVec (KK := KK)
    (PowerSeries.HasSubst.of_constantCoeff_zero hq)
  rw [Projective.Point.toAffine_of_Z_ne_zero hN hz, W.thetaPoint_eq_some hΔ hq hq0
    (by simpa [formalParamVec_apply_zero, formalParamVec_apply_one, formalParamVec_apply_two] using
      (Projective.nonsingular_of_Z_ne_zero hz).mp hN)]
  simp

end FractionField

-- Over a domain, with nonzero discriminant, the identity is read off the group law of the curve
-- over a fraction field `KK` of `O⟦z₁, z₂⟧`, where `dblAddXYZ` represents the sum of the two
-- points, which is the point with parameter `F`.
private theorem dblAddXYZ_formalW_eq_smul_of_Δ_ne_zero {O : Type*} [CommRing O] [IsDomain O]
    (W : WeierstrassCurve O) (hΔ : W.Δ ≠ 0) :
    (W.toProjective.map (algebraMap O (MvPowerSeries (Unit ⊕ Unit) O))).dblAddXYZ
        ![X (Sum.inl ()), -1, PowerSeries.subst (X (Sum.inl ())) W.formalW]
        ![X (Sum.inr ()), -1, PowerSeries.subst (X (Sum.inr ())) W.formalW] =
      -(W.toProjective.map (algebraMap O (MvPowerSeries (Unit ⊕ Unit) O))).dblAddY
        ![X (Sum.inl ()), -1, PowerSeries.subst (X (Sum.inl ())) W.formalW]
        ![X (Sum.inr ()), -1, PowerSeries.subst (X (Sum.inr ())) W.formalW] •
        ![formalAdd W, -1, PowerSeries.subst (formalAdd W) W.formalW] := by
  classical
  let KK := FractionRing (MvPowerSeries (Unit ⊕ Unit) O)
  set ρ := algebraMap (MvPowerSeries (Unit ⊕ Unit) O) KK
  set z₁ : MvPowerSeries (Unit ⊕ Unit) O := X (Sum.inl ())
  set z₂ : MvPowerSeries (Unit ⊕ Unit) O := X (Sum.inr ())
  set D := (W.toProjective.map (algebraMap O (MvPowerSeries (Unit ⊕ Unit) O))).dblAddXYZ
    ![z₁, -1, PowerSeries.subst z₁ W.formalW] ![z₂, -1, PowerSeries.subst z₂ W.formalW] with hDdef
  set F := subst (pairSubstitution z₁ z₂) (formalAdd W)
  have hF : F = formalAdd W := by
    have h : pairSubstitution z₁ z₂ = X := funext fun i ↦ by rcases i with ⟨⟩ | ⟨⟩ <;> rfl
    simp only [F, h, subst_self, id_eq]
  have hΔ' := W.fracCurve_Δ_ne_zero (σ := Unit ⊕ Unit) (KK := KK) hΔ
  set W' := fracCurve W (Unit ⊕ Unit) KK with hW'
  have hz₁ : constantCoeff z₁ = 0 := constantCoeff_X _
  have hz₂ : constantCoeff z₂ = 0 := constantCoeff_X _
  have hz₁0 : z₁ ≠ 0 := nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
  have hz₂0 : z₂ ≠ 0 := nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
  -- the specialization `z₁ ↦ X`, `z₂ ↦ 0` separates the two parameters
  have hχ := hasSubst_coordSpecialize (O := O) (Sum.inl () : Unit ⊕ Unit)
  have hχ₁ : subst (coordSpecialize (Sum.inl ())) z₁ = PowerSeries.X :=
    subst_coordSpecialize_X_self _
  have hχ₂ : subst (coordSpecialize (Sum.inl ())) z₂ = 0 :=
    subst_coordSpecialize_X_of_ne (by simp)
  have hFc : constantCoeff F = 0 := constantCoeff_subst_pair_formalAdd W hz₁ hz₂
  have hF0 : F ≠ 0 := W.subst_pair_formalAdd_ne_zero hχ hz₁ hz₂ hχ₁ hχ₂
  -- read in `KK`, the law `dblAddXYZ` is nonzero, since its `Y`-coordinate is a unit, so it
  -- represents the sum of the two points, which is the parametrized point `θ(F)`
  have hN₁ := W.nonsingular_fracCurve_formalParamVec (KK := KK) (.of_constantCoeff_zero hz₁)
  have hN₂ := W.nonsingular_fracCurve_formalParamVec (KK := KK) (.of_constantCoeff_zero hz₂)
  have hD : W'.toProjective.dblAddXYZ (W.formalParamVec (KK := KK) z₁)
      (W.formalParamVec (KK := KK) z₂) = ρ ∘ D := by
    rw [hW', fracCurve_def, ← map_map, formalParamVec_def, formalParamVec_def]
    exact Projective.map_dblAddXYZ ..
  have hDu : IsUnit (D 1) := by simpa [D] using W.isUnit_dblAddY_formalW
  have hD0 : ρ ∘ D ≠ 0 := fun h ↦ (hDu.map ρ).ne_zero (congrFun h 1)
  have hsum : Projective.Point.toAffine W'.toProjective (ρ ∘ D) =
      Projective.Point.toAffine W'.toProjective (W.formalParamVec (KK := KK) F) := by
    rw [← hD,
      Projective.Point.toAffine_of_equiv (Projective.dblAddXYZ_equiv_add hN₁ hN₂ (hD ▸ hD0)),
      Projective.Point.toAffine_add hN₁ hN₂,
      W.toAffine_fracCurve_formalParamVec_eq_thetaPoint hΔ' hz₁ hz₁0,
      W.toAffine_fracCurve_formalParamVec_eq_thetaPoint hΔ' hz₂ hz₂0,
      W.toAffine_fracCurve_formalParamVec_eq_thetaPoint hΔ' hFc hF0]
    exact W.thetaPoint_add_of_subst_separates hΔ' hχ hz₁ hz₂ hz₁0 hz₂0 hχ₁ hχ₂ hFc hF0
  have hDN : W'.toProjective.Nonsingular (ρ ∘ D) :=
    (Projective.equation_iff_nonsingular_of_Δ_ne_zero_of_ne_zero hΔ' hD0).mp
      (hD ▸ hN₁.left.dblAddXYZ hN₂.left)
  -- equal affine points are projectively equivalent: `ρ ∘ D = u • formalParamVec F`
  obtain ⟨u, hu⟩ := (Projective.Point.toAffine_eq_toAffine_iff hDN
    (W.nonsingular_fracCurve_formalParamVec (KK := KK) (.of_constantCoeff_zero hFc))).mp hsum
  have h₁ : ρ (D 1) = -u := by
    simpa [Units.smul_def, formalParamVec_apply_one] using (congrFun hu 1).symm
  rw [← hF, ← Projective.dblAddXYZ_Y, ← hDdef]
  clear_value D
  funext k
  refine IsFractionRing.injective _ KK ?_
  have hk : ρ (D k) = u * ρ (![F, -1, PowerSeries.subst F W.formalW] k) := by
    simpa [Units.smul_def, formalParamVec_def] using (congrFun hu k).symm
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_neg]
  linear_combination hk + ρ (![F, -1, PowerSeries.subst F W.formalW] k) * h₁

/-- **The Bosma–Lenstra addition law at the formal points.** Let `z₁` and `z₂` be the two variables
of `R⟦z₁, z₂⟧`. At the points `[z₁ : -1 : w(z₁)]` and `[z₂ : -1 : w(z₂)]`, where `w` is the
`w`-expansion of `W`, the addition law `dblAddXYZ` attached to the line `Y = 0` is `-Y` times
`(F, -1, w(F))`, where `Y` is its `Y`-coordinate, a unit (`isUnit_dblAddY_formalW`), and
`F = formalAdd W` is the addition series of the chord construction. No hypothesis is placed on `W`
or on `R`. -/
theorem dblAddXYZ_formalW_eq_smul :
    (W.toProjective.map (algebraMap R (MvPowerSeries (Unit ⊕ Unit) R))).dblAddXYZ
        ![X (Sum.inl ()), -1, PowerSeries.subst (X (Sum.inl ())) W.formalW]
        ![X (Sum.inr ()), -1, PowerSeries.subst (X (Sum.inr ())) W.formalW] =
      -(W.toProjective.map (algebraMap R (MvPowerSeries (Unit ⊕ Unit) R))).dblAddY
        ![X (Sum.inl ()), -1, PowerSeries.subst (X (Sum.inl ())) W.formalW]
        ![X (Sum.inr ()), -1, PowerSeries.subst (X (Sum.inr ())) W.formalW] •
        ![formalAdd W, -1, PowerSeries.subst (formalAdd W) W.formalW] := by
  -- specialize the identity for the universal curve, whose base `ℤ[A₁, ⋯, A₆]` is a domain
  have key := dblAddXYZ_formalW_eq_smul_of_Δ_ne_zero Universal.curve Universal.curve_Δ_ne_zero
  set φ := MvPowerSeries.map (σ := Unit ⊕ Unit) W.specialize
  have hcurve : (Universal.curve.toProjective.map (algebraMap (MvPolynomial Coeff ℤ)
      (MvPowerSeries (Unit ⊕ Unit) (MvPolynomial Coeff ℤ)))).map φ =
        W.toProjective.map (algebraMap R (MvPowerSeries (Unit ⊕ Unit) R)) := by
    have h : φ.comp (algebraMap (MvPolynomial Coeff ℤ) _) =
        (algebraMap R (MvPowerSeries (Unit ⊕ Unit) R)).comp W.specialize :=
      RingHom.ext fun a ↦ by simp [φ, ← c_eq_algebraMap]
    refine (Universal.curve.map_map _ _).trans ?_
    rw [h, ← map_map]
    exact congrArg (fun V : WeierstrassCurve R ↦ V.map _) W.map_specialize
  have hpt (q : MvPowerSeries (Unit ⊕ Unit) (MvPolynomial Coeff ℤ)) (hq : constantCoeff q = 0) :
      φ ∘ ![q, -1, PowerSeries.subst q Universal.curve.formalW] =
        ![φ q, -1, PowerSeries.subst (φ q) W.formalW] := by
    funext k
    fin_cases k
    · rfl
    · simp
    · simp [φ, PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hq),
        ← map_formalW]
  have h₁ := hpt (X (Sum.inl ())) (constantCoeff_X _)
  have h₂ := hpt (X (Sum.inr ())) (constantCoeff_X _)
  have hF := hpt _ (constantCoeff_formalAdd Universal.curve)
  simp only [φ, map_X, ← map_formalAdd, map_specialize] at h₁ h₂ hF
  rw [← h₁, ← h₂, ← hF, ← hcurve, Projective.map_dblAddXYZ, Projective.map_dblAddY, key]
  funext k
  fin_cases k <;> simp [φ]

private theorem hasSubst_pair_of_hasSubst {S : Type*} [CommRing S] {σ : Type*}
    {q₁ q₂ : MvPowerSeries σ S} (hq₁ : PowerSeries.HasSubst q₁) (hq₂ : PowerSeries.HasSubst q₂) :
    HasSubst (pairSubstitution q₁ q₂) :=
  hasSubst_of_constantCoeff_nilpotent fun s ↦ by rcases s with ⟨⟩ | ⟨⟩ <;> simpa

private theorem map_substAlgHom_pair_curve {S : Type*} [CommRing S] [Algebra R S] {σ : Type*}
    {q₁ q₂ : MvPowerSeries σ S} (ha : HasSubst (pairSubstitution q₁ q₂)) :
    (W.toProjective.map (algebraMap R (MvPowerSeries (Unit ⊕ Unit) R))).map
        (substAlgHom (R := R) ha).toRingHom =
      W.toProjective.map (algebraMap R (MvPowerSeries σ S)) := by
  refine (W.map_map _ _).trans ?_
  rw [AlgHom.toRingHom_eq_coe, (substAlgHom (R := R) ha).comp_algebraMap]

private theorem substAlgHom_pair_comp_formalW {S : Type*} [CommRing S] [Algebra R S] {σ : Type*}
    {q₁ q₂ : MvPowerSeries σ S} (ha : HasSubst (pairSubstitution q₁ q₂))
    {r : MvPowerSeries (Unit ⊕ Unit) R} (hr : PowerSeries.HasSubst r) :
    (substAlgHom (R := R) ha).toRingHom ∘ ![r, -1, PowerSeries.subst r W.formalW] =
      ![subst (pairSubstitution q₁ q₂) r, -1,
        PowerSeries.subst (subst (pairSubstitution q₁ q₂) r) W.formalW] := by
  funext k
  fin_cases k
  · simp [coe_substAlgHom]
  · exact (map_neg (substAlgHom (R := R) ha).toRingHom 1).trans (congrArg (-·) (map_one _))
  · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Fin.reduceFinMk, Function.comp_apply, Fin.isValue, Matrix.cons_val, PowerSeries.subst_def]
    rw [coe_substAlgHom, subst_comp_subst_apply hr.const ha]

/-- The `Y`-coordinate of the Bosma–Lenstra addition law `dblAddXYZ` at any pair of substitutable
series `(q₁, q₂)` over an `R`-algebra `S` is a unit. -/
theorem isUnit_dblAddY_formalW_subst_pair {S : Type*} [CommRing S] [Algebra R S] {σ : Type*}
    {q₁ q₂ : MvPowerSeries σ S} (hq₁ : PowerSeries.HasSubst q₁) (hq₂ : PowerSeries.HasSubst q₂) :
    IsUnit ((W.toProjective.map (algebraMap R (MvPowerSeries σ S))).dblAddY
      ![q₁, -1, PowerSeries.subst q₁ W.formalW]
      ![q₂, -1, PowerSeries.subst q₂ W.formalW]) := by
  have ha := hasSubst_pair_of_hasSubst hq₁ hq₂
  have h₁ := W.substAlgHom_pair_comp_formalW ha (PowerSeries.HasSubst.X (Sum.inl ()))
  have h₂ := W.substAlgHom_pair_comp_formalW ha (PowerSeries.HasSubst.X (Sum.inr ()))
  simp only [subst_X ha, Sum.elim_inl] at h₁
  simp only [subst_X ha, Sum.elim_inr] at h₂
  rw [← h₁, ← h₂, ← W.map_substAlgHom_pair_curve ha, Projective.map_dblAddY]
  exact W.isUnit_dblAddY_formalW.map (substAlgHom (R := R) ha).toRingHom

/-- **The Bosma–Lenstra addition law specialised along any pair of substitutable series.**
For any `R`-algebra `S` and any pair `(q₁, q₂)` of substitutable series in `MvPowerSeries σ S`,
the value of `dblAddXYZ` at `[q₁ : -1 : w(q₁)]` and `[q₂ : -1 : w(q₂)]` is `-Y` times
`(F(q₁, q₂), -1, w(F(q₁, q₂)))`, where `Y` is its `Y`-coordinate, a unit
(`isUnit_dblAddY_formalW_subst_pair`), and `F = formalAdd W`. -/
theorem dblAddXYZ_formalW_subst_pair_eq_smul {S : Type*} [CommRing S] [Algebra R S] {σ : Type*}
    {q₁ q₂ : MvPowerSeries σ S} (hq₁ : PowerSeries.HasSubst q₁) (hq₂ : PowerSeries.HasSubst q₂) :
    (W.toProjective.map (algebraMap R (MvPowerSeries σ S))).dblAddXYZ
        ![q₁, -1, PowerSeries.subst q₁ W.formalW]
        ![q₂, -1, PowerSeries.subst q₂ W.formalW] =
      -(W.toProjective.map (algebraMap R (MvPowerSeries σ S))).dblAddY
        ![q₁, -1, PowerSeries.subst q₁ W.formalW]
        ![q₂, -1, PowerSeries.subst q₂ W.formalW] •
        ![subst (pairSubstitution q₁ q₂) (formalAdd W), -1,
          PowerSeries.subst (subst (pairSubstitution q₁ q₂) (formalAdd W)) W.formalW] := by
  have ha := hasSubst_pair_of_hasSubst hq₁ hq₂
  have h₁ := W.substAlgHom_pair_comp_formalW ha (PowerSeries.HasSubst.X (Sum.inl ()))
  have h₂ := W.substAlgHom_pair_comp_formalW ha (PowerSeries.HasSubst.X (Sum.inr ()))
  have hF := W.substAlgHom_pair_comp_formalW ha
    (PowerSeries.HasSubst.of_constantCoeff_zero W.constantCoeff_formalAdd)
  simp only [subst_X ha, Sum.elim_inl] at h₁
  simp only [subst_X ha, Sum.elim_inr] at h₂
  rw [← h₁, ← h₂, ← hF, ← W.map_substAlgHom_pair_curve ha, Projective.map_dblAddXYZ,
    Projective.map_dblAddY, W.dblAddXYZ_formalW_eq_smul]
  funext k
  simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, neg_mul, map_neg, map_mul]

end Algebra

section FormalParamPoint

variable {O : Type*} [CommRing O] (W : WeierstrassCurve O) {σ : Type*}
  {KK : Type*} [Field KK] [Algebra (MvPowerSeries σ O) KK]

private theorem algebraMap_subst_formalW_eq_zero_iff {q : MvPowerSeries σ O}
    (hq : PowerSeries.HasSubst q) :
    algebraMap (MvPowerSeries σ O) KK (PowerSeries.subst q W.formalW) = 0 ↔
      algebraMap (MvPowerSeries σ O) KK q = 0 := by
  have hU₀ : IsUnit W.formalU :=
    PowerSeries.isUnit_iff_constantCoeff.mpr (by simp [W.constantCoeff_formalU])
  have hU : IsUnit (PowerSeries.subst q W.formalU) := by
    simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, PowerSeries.coe_substAlgHom] using
      hU₀.map (PowerSeries.substAlgHom hq).toRingHom
  have hW : PowerSeries.subst q W.formalW = q ^ 3 * PowerSeries.subst q W.formalU := by
    rw [W.formalW_eq_X_pow_mul_formalU, PowerSeries.subst_mul hq, PowerSeries.subst_pow hq,
      PowerSeries.subst_X hq]
  rw [hW, map_mul, map_pow, mul_eq_zero]
  simp [(hU.map (algebraMap (MvPowerSeries σ O) KK)).ne_zero]

variable [Algebra O KK]

/-- The affine point on `W⁄KK` represented by `W.formalParamVec q`, i.e., `[q : -1 : w(q)]`. -/
noncomputable def formalParamPoint (q : MvPowerSeries σ O) : (W⁄KK).toAffine.Point :=
  Projective.Point.toAffine (W⁄KK).toProjective (W.formalParamVec (KK := KK) q)

/-- Unfolding characterization of `formalParamPoint`. -/
theorem formalParamPoint_def (q : MvPowerSeries σ O) :
    W.formalParamPoint (KK := KK) q =
      Projective.Point.toAffine (W⁄KK).toProjective (W.formalParamVec (KK := KK) q) :=
  (rfl)

/-- The zero parameter represents the point at infinity `0`. -/
@[simp]
theorem formalParamPoint_zero :
    W.formalParamPoint (KK := KK) (0 : MvPowerSeries σ O) = 0 := by
  refine Projective.Point.toAffine_of_Z_eq_zero ?_
  simp

variable [IsScalarTower O (MvPowerSeries σ O) KK]

/-- Specialising `dblAddXYZ_formalW_eq_smul` along any pair of substitutable series `(q₁, q₂)`
identifies formal addition `formalAdd W` with point addition on `W⁄KK`, unconditionally for every
Weierstrass curve `W` (with no discriminant hypothesis or case split). -/
theorem formalParamPoint_subst_pair_formalAdd [DecidableEq KK] {q₁ q₂ : MvPowerSeries σ O}
    (hq₁ : PowerSeries.HasSubst q₁) (hq₂ : PowerSeries.HasSubst q₂) :
    W.formalParamPoint (KK := KK) (subst (pairSubstitution q₁ q₂) (formalAdd W)) =
      W.formalParamPoint (KK := KK) q₁ + W.formalParamPoint (KK := KK) q₂ := by
  have hu := W.isUnit_dblAddY_formalW_subst_pair hq₁ hq₂
  have hdbl := W.dblAddXYZ_formalW_subst_pair_eq_smul hq₁ hq₂
  set P₁ : Fin 3 → MvPowerSeries σ O := ![q₁, -1, PowerSeries.subst q₁ W.formalW]
  set P₂ : Fin 3 → MvPowerSeries σ O := ![q₂, -1, PowerSeries.subst q₂ W.formalW]
  set F₁₂ : MvPowerSeries σ O := subst (pairSubstitution q₁ q₂) (formalAdd W)
  set ρ := algebraMap (MvPowerSeries σ O) KK
  have hcurve : (W.toProjective.map (algebraMap O (MvPowerSeries σ O))).map ρ =
      (W⁄KK).toProjective := by
    rw [Projective.map, Projective.map, WeierstrassCurve.map_map,
      ← IsScalarTower.algebraMap_eq, ← WeierstrassCurve.baseChange, toProjective]
  have hdblK : (W⁄KK).toProjective.dblAddXYZ (W.formalParamVec (KK := KK) q₁)
      (W.formalParamVec (KK := KK) q₂) =
        (-ρ ((W.toProjective.map (algebraMap O (MvPowerSeries σ O))).dblAddY P₁ P₂)) •
          W.formalParamVec (KK := KK) F₁₂ := by
    rw [← hcurve, formalParamVec_def, formalParamVec_def,
      Projective.map_dblAddXYZ (W' := W.toProjective.map (algebraMap O (MvPowerSeries σ O)))
        ρ P₁ P₂, hdbl]
    funext k
    fin_cases k <;> simp [formalParamVec_def, ρ]
  have huK : IsUnit (-ρ ((W.toProjective.map (algebraMap O (MvPowerSeries σ O))).dblAddY P₁ P₂)) :=
    (hu.map ρ).neg
  have hN₁ := W.nonsingular_formalParamVec (KK := KK) hq₁
  have hN₂ := W.nonsingular_formalParamVec (KK := KK) hq₂
  have h0 : (W⁄KK).toProjective.dblAddXYZ (W.formalParamVec (KK := KK) q₁)
      (W.formalParamVec (KK := KK) q₂) ≠ 0 := by
    rw [hdblK]
    intro h
    exact huK.ne_zero (by simpa [formalParamVec_apply_one] using congrFun h 1)
  have heq1 := Projective.dblAddXYZ_equiv_add hN₁ hN₂ h0
  have heq2 := Projective.smul_equiv (W.formalParamVec (KK := KK) F₁₂) huK
  rw [← hdblK] at heq2
  rw [formalParamPoint_def, ← Projective.Point.toAffine_of_equiv heq2,
    Projective.Point.toAffine_of_equiv heq1, Projective.Point.toAffine_add hN₁ hN₂,
    ← formalParamPoint_def, ← formalParamPoint_def]

/-- For a substitutable parameter `q` whose image in `KK` is nonzero, `W.formalParamPoint q` is a
nonsingular affine point with coordinates `(q / w(q), -1 / w(q))`. -/
theorem exists_formalParamPoint_eq_some_of_algebraMap_ne_zero {q : MvPowerSeries σ O}
    (hq : PowerSeries.HasSubst q) (hq0 : algebraMap (MvPowerSeries σ O) KK q ≠ 0) :
    ∃ h : (W⁄KK).toAffine.Nonsingular
        (algebraMap (MvPowerSeries σ O) KK q /
          algebraMap (MvPowerSeries σ O) KK (PowerSeries.subst q W.formalW))
        (-1 / algebraMap (MvPowerSeries σ O) KK (PowerSeries.subst q W.formalW)),
      W.formalParamPoint (KK := KK) q = .some _ _ h := by
  have hz : W.formalParamVec (KK := KK) q 2 ≠ 0 := by
    rw [formalParamVec_apply_two]
    exact (W.algebraMap_subst_formalW_eq_zero_iff (KK := KK) hq).not.mpr hq0
  have hN := W.nonsingular_formalParamVec (KK := KK) hq
  refine ⟨by simpa [formalParamVec_apply_zero, formalParamVec_apply_one,
      formalParamVec_apply_two] using (Projective.nonsingular_of_Z_ne_zero hz).mp hN, ?_⟩
  rw [formalParamPoint_def, Projective.Point.toAffine_of_Z_ne_zero hN hz]
  simp [formalParamVec_apply_zero, formalParamVec_apply_one, formalParamVec_apply_two]

/-- For a substitutable parameter `q` whose image in `KK` is nonzero, `W.formalParamPoint q` equals
`.some (q / w(q)) (-1 / w(q)) h` for any supplied nonsingularity proof `h`. -/
theorem formalParamPoint_eq_some_of_algebraMap_ne_zero {q : MvPowerSeries σ O}
    (hq : PowerSeries.HasSubst q) (hq0 : algebraMap (MvPowerSeries σ O) KK q ≠ 0)
    (h : (W⁄KK).toAffine.Nonsingular
      (algebraMap (MvPowerSeries σ O) KK q /
        algebraMap (MvPowerSeries σ O) KK (PowerSeries.subst q W.formalW))
      (-1 / algebraMap (MvPowerSeries σ O) KK (PowerSeries.subst q W.formalW))) :
    W.formalParamPoint (KK := KK) q = .some _ _ h := by
  obtain ⟨_, hp⟩ := W.exists_formalParamPoint_eq_some_of_algebraMap_ne_zero (KK := KK) hq hq0
  exact hp

/-- A substitutable parameter represents the point at infinity `0` if and only if its image in `KK`
vanishes. -/
theorem formalParamPoint_eq_zero_iff {q : MvPowerSeries σ O} (hq : PowerSeries.HasSubst q) :
    W.formalParamPoint (KK := KK) q = 0 ↔ algebraMap (MvPowerSeries σ O) KK q = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_contra hq0
    obtain ⟨_, hp⟩ := W.exists_formalParamPoint_eq_some_of_algebraMap_ne_zero (KK := KK) hq hq0
    rw [hp] at h
    cases h
  · refine Projective.Point.toAffine_of_Z_eq_zero ?_
    rw [formalParamVec_apply_two]
    exact (W.algebraMap_subst_formalW_eq_zero_iff (KK := KK) hq).mpr h

/-- Two substitutable parameters yielding the same affine point on `W⁄KK` have the same image in
`KK`. -/
theorem algebraMap_eq_of_formalParamPoint_eq {q₁ q₂ : MvPowerSeries σ O}
    (hq₁ : PowerSeries.HasSubst q₁) (hq₂ : PowerSeries.HasSubst q₂)
    (h : W.formalParamPoint (KK := KK) q₁ = W.formalParamPoint (KK := KK) q₂) :
    algebraMap (MvPowerSeries σ O) KK q₁ = algebraMap (MvPowerSeries σ O) KK q₂ := by
  set ρ := algebraMap (MvPowerSeries σ O) KK
  by_cases h1 : ρ q₁ = 0
  · have hp1 : W.formalParamPoint (KK := KK) q₁ = 0 :=
      (W.formalParamPoint_eq_zero_iff (KK := KK) hq₁).mpr h1
    rw [hp1] at h
    exact h1.trans ((W.formalParamPoint_eq_zero_iff (KK := KK) hq₂).mp h.symm).symm
  · by_cases h2 : ρ q₂ = 0
    · have hp2 : W.formalParamPoint (KK := KK) q₂ = 0 :=
        (W.formalParamPoint_eq_zero_iff (KK := KK) hq₂).mpr h2
      rw [hp2] at h
      exact False.elim (h1 ((W.formalParamPoint_eq_zero_iff (KK := KK) hq₁).mp h))
    · obtain ⟨_, hp1⟩ := W.exists_formalParamPoint_eq_some_of_algebraMap_ne_zero (KK := KK) hq₁ h1
      obtain ⟨_, hp2⟩ := W.exists_formalParamPoint_eq_some_of_algebraMap_ne_zero (KK := KK) hq₂ h2
      rw [hp1, hp2] at h
      obtain ⟨hx, hy⟩ := Affine.Point.some.inj h
      have hw : ρ (PowerSeries.subst q₁ W.formalW) = ρ (PowerSeries.subst q₂ W.formalW) :=
        inv_injective (neg_injective (by simpa [neg_div, one_div] using hy))
      have hw2 : ρ (PowerSeries.subst q₂ W.formalW) ≠ 0 :=
        (W.algebraMap_subst_formalW_eq_zero_iff (KK := KK) hq₂).not.mpr h2
      exact (div_left_inj₀ hw2).mp (hw ▸ hx)

/-- When `MvPowerSeries σ O →+* KK` is injective (for instance, for any fraction field `KK`), two
substitutable parameters give the same affine point on `W⁄KK` if and only if they are equal. -/
theorem formalParamPoint_inj [FaithfulSMul (MvPowerSeries σ O) KK] {q₁ q₂ : MvPowerSeries σ O}
    (hq₁ : PowerSeries.HasSubst q₁) (hq₂ : PowerSeries.HasSubst q₂) :
    W.formalParamPoint (KK := KK) q₁ = W.formalParamPoint (KK := KK) q₂ ↔ q₁ = q₂ :=
  ⟨fun h ↦ FaithfulSMul.algebraMap_injective _ _
    (W.algebraMap_eq_of_formalParamPoint_eq hq₁ hq₂ h), fun h ↦ by subst h; rfl⟩

end FormalParamPoint

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- **The addition morphism at the formal point.** Let `z₁` and `z₂` be the two variables of
`R⟦z₁, z₂⟧`. The Bosma–Lenstra addition morphism `E ×_{Spec R} E ⟶ E` of the projective model
`E = projModel W` sends the pair of formal points reparametrised by `X ↦ z₁` and by `X ↦ z₂` to
the formal point reparametrised by `X ↦ F(z₁, z₂)`, where `F = formalAdd W` is the addition series
of the chord construction. That is, the group law of `E`, written in the parameter `z = -X / Y`
at the zero section, is the formal group law `F`. -/
theorem lift_projModelFormalPoint_additionMorphism [W.IsElliptic] :
    pullback.lift
        (Spec.map (CommRingCat.ofHom (PowerSeries.substAlgHom
          (PowerSeries.HasSubst.X (S := R) (Sum.inl () : Unit ⊕ Unit))).toRingHom) ≫
            W.projModelFormalPoint)
        (Spec.map (CommRingCat.ofHom (PowerSeries.substAlgHom
          (PowerSeries.HasSubst.X (S := R) (Sum.inr () : Unit ⊕ Unit))).toRingHom) ≫
            W.projModelFormalPoint)
        (by simp only [Category.assoc, projModelFormalPoint_projModelOver, ← Spec.map_comp,
          ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]) ≫
          W.additionMorphism =
      Spec.map (CommRingCat.ofHom (PowerSeries.substAlgHom
        (PowerSeries.HasSubst.of_constantCoeff_zero W.constantCoeff_formalAdd)).toRingHom) ≫
          W.projModelFormalPoint := by
  simp only [SpecMap_substAlgHom_projModelFormalPoint]
  -- the `Y`-coordinate of `dblAddXYZ` is a unit, so the addition morphism is computed by that law,
  -- whose value is a unit multiple of `(F, -1, w(F))`
  have hY := W.isUnit_dblAddY_formalW
  rw [W.lift_projModelPoint_additionMorphism_of_isUnit_dblAddXYZ (m := 1) _ _
    (by simpa using hY), projModelPoint_eq_projModelPoint_iff]
  exact ⟨rfl, -hY.unit, by rw [dblAddXYZ_formalW_eq_smul, Units.smul_def, Units.val_neg,
    IsUnit.unit_spec]⟩

end WeierstrassCurve
