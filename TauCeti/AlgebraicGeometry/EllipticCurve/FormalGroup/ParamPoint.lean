/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.WExpansion
import Mathlib.RingTheory.MvPowerSeries.Inverse

/-!
# Formal-parameter points of a Weierstrass curve

Let `W` be a Weierstrass curve over a commutative ring `O`, and let `w = W.formalW` be its
`w`-expansion (`FormalGroup/WExpansion.lean`). For any commutative `MvPowerSeries σ O`-algebra `KK`
and any parameter series `q : MvPowerSeries σ O`, the projective triple
`W.formalParamVec q = [q : -1 : w(q)]` (read along `algebraMap (MvPowerSeries σ O) KK`) defines a
point on the Weierstrass curve base changed along `O → MvPowerSeries σ O → KK`.

When `q` is substitutable (`PowerSeries.HasSubst q`, i.e., its constant coefficient is nilpotent),
`W.formalParamVec q` is unconditionally nonsingular in every nontrivial algebra `KK`, with no
discriminant hypothesis on `W`: the `Z`-partial derivative of the projective Weierstrass equation at
`[q : -1 : w(q)]` has constant coefficient of the form `1 - (nilpotent)`, hence is a unit in
`MvPowerSeries σ O` (`WeierstrassCurve.nonsingular_map_formalParamVec`). Over a field `KK`
extending `O` compatibly with `O → MvPowerSeries σ O → KK`, projecting to affine coordinates via
`Projective.Point.toAffine` gives the affine point `W.formalParamPoint q : (W⁄KK).toAffine.Point`.

Unlike `WeierstrassCurve.formalPoint` in `FormalGroup/Point/Basic.lean` (which evaluates `w` at an
element of an adic ideal in a complete topological ring) and `WeierstrassCurve.projModelFormalPoint`
in `Scheme/FormalPoint.lean` (which lives on the projective scheme model `projModel W`), this module
works purely algebraically with power-series parameters and requires neither topology, schemes, nor
formal-group addition theory. The compatibility of `formalParamPoint` with `formalAdd` via the
Bosma–Lenstra addition law is proved in `Scheme/Addition/FormalPoint.lean`.

## Main definitions

* `WeierstrassCurve.formalParamVec`: the projective coordinate triple `[q : -1 : w(q)]` in an
  `MvPowerSeries σ O`-algebra `KK` attached to a parameter series `q`.
* `WeierstrassCurve.formalParamPoint`: the affine point on `W⁄KK` represented by
  `W.formalParamVec q` over a field `KK`.

## Main results

* `WeierstrassCurve.formalParamVec_apply_zero`, `formalParamVec_apply_one`,
  `formalParamVec_apply_two`, `formalParamVec_zero`: coordinate and zero-parameter simplifications.
* `WeierstrassCurve.formalParamVec_apply_two_eq_zero_iff`: over a reduced algebra `KK`, the
  `Z`-coordinate `w(q)` of `W.formalParamVec q` vanishes if and only if the image of `q` vanishes.
* `WeierstrassCurve.nonsingular_map_formalParamVec` and
  `WeierstrassCurve.nonsingular_formalParamVec`: for any substitutable series `q`, `[q : -1 : w(q)]`
  is nonsingular in every nontrivial commutative algebra `KK` over `MvPowerSeries σ O`, with no
  discriminant hypothesis on `W`.
* `WeierstrassCurve.exists_formalParamPoint_eq_some_of_algebraMap_ne_zero` and
  `WeierstrassCurve.formalParamPoint_eq_some_of_algebraMap_ne_zero`: affine coordinates
  `(q / w(q), -1 / w(q))` when the image of `q` in `KK` is nonzero.
* `WeierstrassCurve.formalParamPoint_eq_zero_iff`: `W.formalParamPoint q = 0` if and only if the
  image of `q` in `KK` vanishes.
* `WeierstrassCurve.algebraMap_eq_of_formalParamPoint_eq` and
  `WeierstrassCurve.formalParamPoint_inj`: injectivity of `formalParamPoint` on substitutable
  parameters (unconditionally on images in `KK`, and on parameters themselves under
  `[FaithfulSMul (MvPowerSeries σ O) KK]`).

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.
-/

public section

open MvPowerSeries

namespace WeierstrassCurve

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

/-- The `X`-coordinate (index `0`) of `W.formalParamVec q` is the image of `q` in `KK`. -/
@[simp]
theorem formalParamVec_apply_zero (q : MvPowerSeries σ O) :
    W.formalParamVec (KK := KK) q 0 = algebraMap (MvPowerSeries σ O) KK q := by
  simp [formalParamVec]

/-- The `Y`-coordinate (index `1`) of `W.formalParamVec q` is `-1`. -/
@[simp]
theorem formalParamVec_apply_one (q : MvPowerSeries σ O) :
    W.formalParamVec (KK := KK) q 1 = -1 := by
  simp [formalParamVec]

/-- The `Z`-coordinate (index `2`) of `W.formalParamVec q` is the image of `w(q)` in `KK`. -/
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

/-- Over a reduced algebra `KK`, the `Z`-coordinate `w(q)` of `W.formalParamVec q` vanishes if and
only if the image of `q` vanishes, for any substitutable parameter series `q`. -/
theorem formalParamVec_apply_two_eq_zero_iff [IsReduced KK] {q : MvPowerSeries σ O}
    (hq : PowerSeries.HasSubst q) :
    W.formalParamVec (KK := KK) q 2 = 0 ↔ algebraMap (MvPowerSeries σ O) KK q = 0 := by
  rw [formalParamVec_apply_two]
  have hU₀ : IsUnit W.formalU :=
    isUnit_iff_constantCoeff.mpr (by
      rw [← PowerSeries.constantCoeff_eq, W.constantCoeff_formalU]
      exact isUnit_one)
  have hU : IsUnit (PowerSeries.subst q W.formalU) := by
    simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, PowerSeries.coe_substAlgHom] using
      hU₀.map (PowerSeries.substAlgHom hq).toRingHom
  have hW : PowerSeries.subst q W.formalW = q ^ 3 * PowerSeries.subst q W.formalU := by
    rw [W.formalW_eq_X_pow_mul_formalU, PowerSeries.subst_mul hq, PowerSeries.subst_pow hq,
      PowerSeries.subst_X hq]
  rw [hW, map_mul, map_pow, (hU.map (algebraMap (MvPowerSeries σ O) KK)).mul_left_eq_zero]
  exact ⟨fun h ↦ isNilpotent_iff_eq_zero.mp ⟨3, h⟩, fun h ↦ by simp [h]⟩

/-- For any substitutable parameter series `q`, the projective point `[q : -1 : w(q)]` on the base
change of `W` along `O → MvPowerSeries σ O → KK` is nonsingular in every nontrivial commutative
algebra `KK` over `MvPowerSeries σ O` (with no discriminant hypothesis on `W`). -/
theorem nonsingular_map_formalParamVec [Nontrivial KK] {q : MvPowerSeries σ O}
    (hq : PowerSeries.HasSubst q) :
    (W.map ((algebraMap (MvPowerSeries σ O) KK).comp
      (algebraMap O (MvPowerSeries σ O)))).toProjective.Nonsingular
        (W.formalParamVec (KK := KK) q) := by
  refine (Projective.nonsingular_iff _).mpr ⟨?_, Or.inr (Or.inr ?_)⟩
  · rw [formalParamVec_def, ← map_map]
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
    simp only [z, w, ρ, toProjective, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆,
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
  rw [baseChange, IsScalarTower.algebraMap_eq O (MvPowerSeries σ O) KK]
  exact W.nonsingular_map_formalParamVec hq

end FormalParamVec

section FormalParamPoint

variable {O : Type*} [CommRing O] (W : WeierstrassCurve O) {σ : Type*}
  {KK : Type*} [Field KK] [Algebra (MvPowerSeries σ O) KK] [Algebra O KK]

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

/-- For a substitutable parameter `q` whose image in `KK` is nonzero, `W.formalParamPoint q` is a
nonsingular affine point with coordinates `(q / w(q), -1 / w(q))`. -/
theorem exists_formalParamPoint_eq_some_of_algebraMap_ne_zero {q : MvPowerSeries σ O}
    (hq : PowerSeries.HasSubst q) (hq0 : algebraMap (MvPowerSeries σ O) KK q ≠ 0) :
    ∃ h : (W⁄KK).toAffine.Nonsingular
        (algebraMap (MvPowerSeries σ O) KK q /
          algebraMap (MvPowerSeries σ O) KK (PowerSeries.subst q W.formalW))
        (-1 / algebraMap (MvPowerSeries σ O) KK (PowerSeries.subst q W.formalW)),
      W.formalParamPoint (KK := KK) q = .some _ _ h := by
  have hz : W.formalParamVec (KK := KK) q 2 ≠ 0 :=
    (W.formalParamVec_apply_two_eq_zero_iff (KK := KK) hq).not.mpr hq0
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
  · exact Projective.Point.toAffine_of_Z_eq_zero
      ((W.formalParamVec_apply_two_eq_zero_iff (KK := KK) hq).mpr h)

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
      have hw2 : ρ (PowerSeries.subst q₂ W.formalW) ≠ 0 := by
        simpa only [formalParamVec_apply_two, ρ] using
          (W.formalParamVec_apply_two_eq_zero_iff (KK := KK) hq₂).not.mpr h2
      exact (div_left_inj₀ hw2).mp (hw ▸ hx)

/-- When `MvPowerSeries σ O →+* KK` is injective (for instance, for any fraction field `KK`), two
substitutable parameters give the same affine point on `W⁄KK` if and only if they are equal. -/
theorem formalParamPoint_inj [FaithfulSMul (MvPowerSeries σ O) KK] {q₁ q₂ : MvPowerSeries σ O}
    (hq₁ : PowerSeries.HasSubst q₁) (hq₂ : PowerSeries.HasSubst q₂) :
    W.formalParamPoint (KK := KK) q₁ = W.formalParamPoint (KK := KK) q₂ ↔ q₁ = q₂ :=
  ⟨fun h ↦ FaithfulSMul.algebraMap_injective _ _
    (W.algebraMap_eq_of_formalParamPoint_eq hq₁ hq₂ h), fun h ↦ by subst h; rfl⟩

end FormalParamPoint

end WeierstrassCurve
