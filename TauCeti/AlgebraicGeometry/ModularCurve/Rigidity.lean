/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Geom.TateNormalForm
public import TauCeti.AlgebraicGeometry.ModularCurve.NaiveLevel

/-!
# Rigidity of the naive moduli problems `[Γ₁(N)]` and `[Γ(N)]` for `N ≥ 4`

A moduli problem over `Ell/B` is rigid when no automorphism of an elliptic curve `E/S` other than
the identity fixes a level structure on `E/S` (`ModuliProblem.IsRigid`). This file proves that for
`N ≥ 4` the naive moduli problem `[Γ₁(N)]` is rigid (`ModuliProblem.isRigid_gammaOneNaive`): an
automorphism of `E` over `S` fixing an `S`-point `P` of exact order `N` in every fibre is the
identity. Since a naive `[Γ(N)]`-structure `(P, Q)` determines the naive `[Γ₁(N)]`-structure `P`,
the naive moduli problem `[Γ(N)]` is rigid for `N ≥ 4` as well
(`ModuliProblem.isRigid_gammaNaive`).

There is no hypothesis on the base `B`: it may be nonreduced, and `N` need not be invertible on it.
The proof goes through the universal Tate normal form. If `P` has exact order `N ≥ 4` in every
fibre, none of `P`, `2P` and `3P` meets the zero section, so `(E, P)` is the pullback of the
universal Tate normal form along a unique cartesian pointed morphism, and an automorphism fixing
`P` is the identity (`EllipticCurveGeom.eq_id_of_isPullback_of_comp_eq`).

The bound is sharp: for `N = 1` and `N = 2` the automorphism `[-1]` fixes every point of order
dividing `N`, and for `N = 3` the curve `Y² + Y = X³` over a field containing a primitive cube root
of unity `ζ` has the automorphism `(X, Y) ↦ (ζX, Y)` fixing the point `(0, 0)` of order `3`.

## Main results

* `TauCeti.AlgebraicGeometry.ModuliProblem.isRigid_gammaOneNaive`: for `N ≥ 4`, the naive moduli
  problem `[Γ₁(N)]` is rigid.
* `TauCeti.AlgebraicGeometry.ModuliProblem.isRigid_gammaNaive`: for `N ≥ 4`, the naive moduli
  problem `[Γ(N)]` is rigid.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, 2.7 (rigidity of naive level structures) and Chapter 4.
* D. Loeffler, *Modular Curves*, lecture notes, §3.3 (Tate normal form and `Y₁(N)`).
-/

public section

open CategoryTheory Limits MonoidalCategory Opposite AlgebraicGeometry MonObj

universe u

namespace TauCeti.AlgebraicGeometry.ModuliProblem

variable {B : Scheme.{u}} {N : ℕ}

/-- **The naive moduli problem `[Γ₁(N)]` is rigid for `N ≥ 4`.** An automorphism of an elliptic
curve `E/S` fixing an `S`-point of exact order `N` in every fibre is the identity. There is no
hypothesis on the base, and `N` need not be invertible on it. -/
theorem isRigid_gammaOneNaive (hN : 4 ≤ N) : (gammaOneNaive B N).IsRigid := by
  have : NeZero N := ⟨by omega⟩
  rw [isRigid_iff]
  intro X σ hσ α hα
  have hφ := (naiveLevelEquiv X α).2
  set P := (naiveLevelEquiv X α).1 (.ofAdd 1)
  -- the multiples `P`, `2P` and `3P` miss the zero section, since `P` has exact order `N ≥ 4`
  have hk (k : ℤ) (hk : 0 < k) (hk' : k < 4) (s : X.base) :
      (P.left ≫ (X.curve.mulBy k).left) s ≠ X.curve.zero s := by
    lift k to ℕ using hk.le
    rw [← Over.comp_left, EllipticCurveGeom.comp_mulBy, zpow_natCast]
    exact (EllipticCurveGeom.isFiberwiseInjective_zmod_iff.mp hφ) k (by omega) (by omega) s
  -- `σ` fixes `P`, because it fixes the naive `[Γ₁(N)]`-structure
  have hσP : P.left ≫ σ.total = P.left := by
    have h := congrArg (fun α ↦ (naiveLevelEquiv X α).1 (.ofAdd 1)) hα
    simp only [naiveLevelEquiv_map, MonoidHom.comp_apply] at h
    simpa [hσ] using (EllipticCurveGeom.eq_pointsPullback_iff σ.isPullback σ.zero_total).mp h.symm
  refine EllObj.hom_ext ?_
  rw [EllObj.id_total]
  refine EllipticCurveGeom.eq_id_of_isPullback_of_comp_eq (P := P.left) (by simp)
    (by simpa using hk 1) (hk 2 (by norm_num) (by norm_num))
    (hk 3 (by norm_num) (by norm_num)) (hσ ▸ σ.isPullback) ?_ hσP
  simp [hσ]

/-- **The naive moduli problem `[Γ(N)]` is rigid for `N ≥ 4`**, because a naive `[Γ(N)]`-structure
`(P, Q)` determines the naive `[Γ₁(N)]`-structure `P` (`gammaNaiveToGammaOneNaive`). -/
theorem isRigid_gammaNaive (hN : 4 ≤ N) : (gammaNaive B N).IsRigid :=
  (isRigid_gammaOneNaive hN).of_hom (gammaNaiveToGammaOneNaive B N)

end TauCeti.AlgebraicGeometry.ModuliProblem
