/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Torsion.Integral
-- Proof-only: the points of `W` are those of its base change along the identity.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.BaseChange
-- Proof-only: the `y`-coordinate of a point with rational `x` is rational.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.IsAlgClosed
-- Proof-only: the absorption of integral elements by an algebraically closed field
-- (`IsIntegral.mem_range_algebraMap_of_minpoly_splits`).
import Mathlib.RingTheory.Adjoin.Field

/-!
# Torsion points over an algebraically closed field are already rational

Over an algebraically closed `F`, a torsion point of `W` with coordinates in an extension `Ω` has
its coordinates in `F`: the extension buys no new torsion. No condition on the index is needed,
because an algebraically closed field also extracts the inseparable roots that a torsion point of
an index divisible by the characteristic has; the companion statements over a merely separably
closed field ask for an invertible index in exchange.

## Main results

* `WeierstrassCurve.mem_range_x_of_zsmul_eq_zero_of_isAlgClosed`: over an algebraically closed
  `F`, the `x`-coordinate of an `n`-torsion point of `W` over an extension lies in the image
  of `F`.
* `WeierstrassCurve.mem_range_baseChange_of_zsmul_eq_zero_of_isAlgClosed`: such an `n`-torsion
  point is therefore the base change of one over `F`.
* `WeierstrassCurve.torsionBy_baseChange_eq_bot_iff_of_isAlgClosed`: for `n ≠ 0`, the
  `n`-torsion of `W` over `Ω` is trivial exactly when that of `W` itself is.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.4(b).
-/

public section

open Polynomial

namespace WeierstrassCurve

variable {F : Type*} [Field F] [IsAlgClosed F] (W : WeierstrassCurve F) [W.IsElliptic]
  {Ω : Type*} [Field Ω] [Algebra F Ω]

/-- **The `x`-coordinate of a torsion point is rational** when the base field is algebraically
closed: integrality then puts it in the image of `F`. -/
theorem mem_range_x_of_zsmul_eq_zero_of_isAlgClosed {n : ℤ} (hn : n ≠ 0) {x y : Ω}
    (hns : (W.baseChange Ω).toAffine.Nonsingular x y)
    (htors : n • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) = 0) :
    x ∈ Set.range (algebraMap F Ω) :=
  (isIntegral_x_of_zsmul_eq_zero W hn hns htors).mem_range_algebraMap_of_minpoly_splits
    (by simpa using IsAlgClosed.splits (minpoly F x))

/-- **A torsion point over an extension of an algebraically closed field is already rational.**
No field extension of an algebraically closed `F` buys new torsion: the coordinates of a torsion
point are integral over `F`, hence already in it. So the `n`-torsion of `W` over `Ω` is the base
change of the `n`-torsion over `F`, for every extension `Ω` and not only an algebraic one. -/
theorem mem_range_baseChange_of_zsmul_eq_zero_of_isAlgClosed [DecidableEq F] [DecidableEq Ω] {n : ℤ}
    (hn : n ≠ 0)
    {P : (W.baseChange Ω).toAffine.Point} (h : n • P = 0) :
    P ∈ Set.range (Affine.Point.baseChange (W' := W) F Ω) := by
  rcases P with _ | ⟨x, y, hns⟩
  · exact ⟨0, Affine.Point.map_zero _⟩
  · have hJac : n • Jacobian.Point.fromAffine (Affine.Point.some _ _ hns) = 0 := by
      have h' := congrArg (Jacobian.Point.toAffineAddEquiv (W.baseChange Ω)).symm h
      rw [map_zsmul, map_zero] at h'
      simpa using h'
    obtain ⟨x₀, hx₀⟩ := W.mem_range_x_of_zsmul_eq_zero_of_isAlgClosed hn hns hJac
    obtain ⟨y₀, hy₀⟩ := W.mem_range_y_of_equation_of_mem_range_x hns.left hx₀
    subst hx₀
    subst hy₀
    refine ⟨Affine.Point.some x₀ y₀ ((W.toAffine.baseChange_nonsingular
      (f := Algebra.ofId F Ω) (FaithfulSMul.algebraMap_injective F Ω) x₀ y₀).mp hns), ?_⟩
    rw [Affine.Point.map_some]
    simp only [Algebra.ofId_apply]

/-- **An extension of an algebraically closed field adds no `n`-torsion**, for `n ≠ 0`: the
`n`-torsion subgroup of `W` over `Ω` is trivial exactly when that of `W` is. Base change is
injective on points, and every `n`-torsion point over `Ω` comes from one over `F`. -/
theorem torsionBy_baseChange_eq_bot_iff_of_isAlgClosed [DecidableEq F] [DecidableEq Ω] {n : ℤ}
    (hn : n ≠ 0) :
    AddSubgroup.torsionBy (W.baseChange Ω).toAffine.Point n = ⊥ ↔
      AddSubgroup.torsionBy W.toAffine.Point n = ⊥ := by
  let e := Affine.Point.equivBaseChangeSelf W.toAffine
  let φ := Affine.Point.baseChange (W' := W) F Ω
  have hφ : Function.Injective φ := Affine.Point.map_injective _
  simp only [AddSubgroup.eq_bot_iff_forall, Submodule.mem_toAddSubgroup,
    Submodule.mem_torsionBy_iff]
  refine ⟨fun h P hP ↦ e.injective (hφ ?_), fun h Q hQ ↦ ?_⟩
  · rw [map_zero, map_zero]
    exact h (φ (e P)) (by rw [← map_zsmul, ← map_zsmul, hP, map_zero, map_zero])
  · obtain ⟨P, rfl⟩ := W.mem_range_baseChange_of_zsmul_eq_zero_of_isAlgClosed hn hQ
    have hnP : n • P = 0 := hφ (by rwa [map_zsmul, map_zero])
    have hP : e.symm P = 0 := h (e.symm P) (by rw [← map_zsmul, hnP, map_zero])
    rw [← e.apply_symm_apply P, hP, map_zero, map_zero]

end WeierstrassCurve

end
