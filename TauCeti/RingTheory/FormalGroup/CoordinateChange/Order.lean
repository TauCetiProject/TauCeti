/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.CoordinateChange.Basic
import TauCeti.RingTheory.FormalGroup.Height.Basic
import TauCeti.RingTheory.FormalGroup.Hom.Defect
import TauCeti.RingTheory.PowerSeries.Coordinate.Order

/-!
# Additive normalization of formal groups to finite order

`FormalGroup.order_homDefect_eq_order_smul_sub` identifies the order of the homomorphism defect
of a coordinate with the order of the difference of the transported law and the target law.
It uses `TauCeti.FormalCoordinate.order_subst` to remove substitution by the coordinate.

`FormalGroup.le_order_nsmulSeries_iff_exists_strict_smul_sub_𝔾ₐ` characterizes when a commutative
formal group law admits a strict coordinate making it additive below a prescribed degree.
It constructs the coordinate using `FormalGroup.exists_le_order_homDefect_of_le_order_nsmulSeries`.
In characteristic `p`, a law of finite height `h` therefore admits a normalization below
`p ^ h` by `FormalGroup.height_eq_natCast_iff`, as used in Lubin–Tate's deformation theorem.

## References

* J. Lubin and J. Tate, *Formal moduli for one-parameter formal Lie groups* (1966), Theorem 3.1.
-/

public section

open MvPowerSeries TauCeti

namespace FormalGroup

/-- The order of the homomorphism defect of `φ` from `F` to `G` is the order of
`(φ • F) - G`. -/
theorem order_homDefect_eq_order_smul_sub {R : Type*} [CommRing R] (F G : FormalGroup R)
    (φ : FormalCoordinate R) :
    (F.homDefect G φ.toPowerSeries).order =
      ((φ • F).toPowerSeries - G.toPowerSeries).order := by
  let a (i : Fin 2) := PowerSeries.subst (X i : MvPowerSeries (Fin 2) R) φ.toPowerSeries
  have ha : HasSubst a :=
    hasSubst_of_constantCoeff_zero fun i ↦ PowerSeries.constantCoeff_subst_eq_zero
      (constantCoeff_X i) φ.toPowerSeries φ.constantCoeff_toPowerSeries
  have hpair : ![a 0, a 1] = a := funext (Fin.forall_fin_two.mpr ⟨rfl, rfl⟩)
  rw [F.homDefect_eq_sub_subst_pair,
    subst_toPowerSeries_eq_subst_smul_toPowerSeries, hpair, ← subst_sub ha]
  exact φ.order_subst _

/-- A commutative formal group law has a strict coordinate in which it agrees with the additive
law below degree `N` if and only if its `p`-series vanishes below degree `N`, for a prime `p`
that vanishes in the coefficient ring. This is the normalization used in Lubin–Tate,
*Formal moduli for one-parameter formal Lie groups*, Theorem 3.1. -/
theorem le_order_nsmulSeries_iff_exists_strict_smul_sub_𝔾ₐ
    {R : Type*} [CommRing R] {F : FormalGroup R} [F.IsComm]
    {p N : ℕ} (hp : p.Prime) (hpR : (p : R) = 0) :
    (N : ℕ∞) ≤ (F.nsmulSeries p).order ↔
      ∃ φ : (FormalCoordinate.linearCoeff (R := R)).ker,
        (N : ℕ∞) ≤ (((φ : FormalCoordinate R) • F).toPowerSeries - 𝔾ₐ.toPowerSeries).order := by
  constructor
  · intro hF
    have hA : (N : ℕ∞) ≤ ((𝔾ₐ (R := R)).nsmulSeries p).order := by
      rw [nsmulSeries_𝔾ₐ_eq_zero hpR, PowerSeries.order_zero]
      exact le_top
    obtain ⟨g, hg, hg₁, hord⟩ :=
      F.exists_le_order_homDefect_of_le_order_nsmulSeries (G := 𝔾ₐ) hp hF hA
    let φ : FormalCoordinate R := ⟨g, hg, hg₁.symm ▸ isUnit_one⟩
    have hφ : φ ∈ (FormalCoordinate.linearCoeff (R := R)).ker :=
      MonoidHom.mem_ker.mpr (Units.ext (by rw [φ.val_linearCoeff]; exact hg₁))
    have horder : (N : ℕ∞) ≤ (F.homDefect 𝔾ₐ φ.toPowerSeries).order := hord
    exact ⟨⟨φ, hφ⟩, (F.order_homDefect_eq_order_smul_sub 𝔾ₐ φ) ▸ horder⟩
  · rintro ⟨φ, hφ⟩
    have h := le_order_nsmulSeries_sub hφ p
    rwa [nsmulSeries_𝔾ₐ_eq_zero hpR, sub_zero, order_nsmulSeries_smul] at h

end FormalGroup
