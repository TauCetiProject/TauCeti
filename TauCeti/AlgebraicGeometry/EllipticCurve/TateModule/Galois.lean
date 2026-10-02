/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateModule.Basic
public import TauCeti.FieldTheory.KrullTopology
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Torsion.Integral
import TauCeti.AlgebraicGeometry.EllipticCurve.Integrality

/-!
# The `ℓ`-adic Galois representation of an elliptic curve

Let `W` be a Weierstrass curve over a field `F`, let `K` be an extension of `F`, and let `ℓ` be a
prime. An `F`-automorphism `σ` of `K` acts on the points of `W` over `K` coordinatewise, by
group automorphisms, so it permutes each torsion level `E[ℓ ^ n]` compatibly with the transition
maps. It therefore acts `ℤ_ℓ`-linearly on the Tate module `T_ℓ E = lim E[ℓ ^ n]`, and this file
packages that action as a representation of `Gal(K/F)` on `T_ℓ E` (Silverman III.7).

For an elliptic curve the representation is **continuous** for the Krull topology on `Gal(K/F)`
and the inverse-limit topology on `T_ℓ E`, with no hypothesis on `K / F`. The coordinates of a
torsion point are integral over `F` — the abscissa is a root of a division polynomial and the
ordinate then solves the Weierstrass equation — so an automorphism near `σ` moves each torsion
point as `σ` does. When `K` is a separable closure of `F` and `ℓ` is invertible in `F`, the Tate
module is free of rank two (`WeierstrassCurve.finrank_tateModule`), so this is the classical
two-dimensional `ℓ`-adic representation; its matrices in `GL₂(ℤ_ℓ)` depend on a choice of basis,
so it is stated basis-free, on `T_ℓ E` itself.

## Main definitions

* `WeierstrassCurve.tateModuleGaloisRepresentation`: the representation of `K ≃ₐ[F] K` on `T_ℓ E`.

## Main results

* `WeierstrassCurve.coe_proj_tateModuleGaloisRepresentation`: on the level `E[ℓ ^ n]` the
  representation is the coordinatewise action on points.
* `WeierstrassCurve.isLocallyConstant_map_of_zsmul_eq_zero`: the orbit map of a torsion point of
  an elliptic curve is locally constant for the Krull topology.
* `WeierstrassCurve.continuous_tateModuleGaloisRepresentation_apply`: for an elliptic curve, the
  action `(σ, x) ↦ σ x` on `T_ℓ E` is jointly continuous.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.7.
-/

public section

noncomputable section

open TauCeti
open scoped WeierstrassCurve

namespace WeierstrassCurve

variable {F K : Type*} [Field F] [Field K] [DecidableEq K] [Algebra F K]
  (W : WeierstrassCurve F)

/-! ### The representation -/

section Representation

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- **The `ℓ`-adic Galois representation** of `W`: an `F`-automorphism `σ` of `K` acts on the
Tate module `T_ℓ E` of `W` over `K` by applying `σ` to the coordinates of every point of every
level `E[ℓ ^ n]`. -/
def tateModuleGaloisRepresentation :
    Representation ℤ_[ℓ] (K ≃ₐ[F] K) (TateModule ℓ (W⁄K).toAffine.Point) where
  toFun σ := TateModule.mapLinearMap (Affine.Point.map (W' := W) σ.toAlgHom)
  map_one' := LinearMap.ext fun x ↦ TateModule.ext fun n ↦ Subtype.ext <| by
    simp only [Module.End.one_apply, TateModule.mapLinearMap_apply, TateModule.proj_map,
      TateModule.levelMap_apply]
    exact Affine.Point.map_id _
  map_mul' σ τ := LinearMap.ext fun x ↦ TateModule.ext fun n ↦ Subtype.ext <| by
    simp only [Module.End.mul_apply, TateModule.mapLinearMap_apply, TateModule.proj_map,
      TateModule.levelMap_apply]
    exact (Affine.Point.map_map τ.toAlgHom σ.toAlgHom _).symm

variable {W ℓ}

/-- The representation applies the induced map of Tate modules of the coordinatewise action on
points. -/
@[simp]
theorem tateModuleGaloisRepresentation_apply (σ : K ≃ₐ[F] K)
    (x : TateModule ℓ (W⁄K).toAffine.Point) :
    W.tateModuleGaloisRepresentation ℓ σ x = TateModule.map (Affine.Point.map σ.toAlgHom) x :=
  TateModule.mapLinearMap_apply _ x

/-- **The representation on the level `E[ℓ ^ n]`**: the `n`-th component of `σ x` is `σ` applied
to the coordinates of the `n`-th component of `x`. -/
theorem coe_proj_tateModuleGaloisRepresentation (σ : K ≃ₐ[F] K)
    (x : TateModule ℓ (W⁄K).toAffine.Point) (n : ℕ) :
    (TateModule.proj n (W.tateModuleGaloisRepresentation ℓ σ x) : (W⁄K).toAffine.Point) =
      Affine.Point.map σ.toAlgHom (TateModule.proj n x : (W⁄K).toAffine.Point) := by
  rw [tateModuleGaloisRepresentation_apply, TateModule.proj_map, TateModule.levelMap_apply]

end Representation

/-! ### Continuity -/

variable [W.IsElliptic]

open WeierstrassCurve.Affine in
/-- **Torsion points move locally constantly under the Galois group.** For a point `P` of an
elliptic curve over `K` killed by a nonzero integer, `σ ↦ σ P` is locally constant for the Krull
topology on `K ≃ₐ[F] K`: the coordinates of `P` are integral over `F`, so they are fixed by an
open subgroup. No hypothesis on `K / F` is needed. -/
theorem isLocallyConstant_map_of_zsmul_eq_zero {n : ℤ} (hn : n ≠ 0) {P : (W⁄K).toAffine.Point}
    (hP : n • P = 0) : IsLocallyConstant fun σ : K ≃ₐ[F] K ↦ Point.map σ.toAlgHom P := by
  rcases P with _ | ⟨x, y, hns⟩
  · exact IsLocallyConstant.const 0
  have hJac : n • Jacobian.Point.fromAffine (Point.some _ _ hns) = 0 :=
    zsmul_fromAffine_eq_zero_iff_zsmul_eq_zero.mpr hP
  have hx := W.isIntegral_x_of_zsmul_eq_zero hn hns hJac
  have hy := W.isIntegral_y_of_equation_of_isIntegral_x hns.left hx
  refine (IsLocallyConstant.iff_eventually_eq _).2 fun σ₀ ↦ ?_
  filter_upwards
    [(IsLocallyConstant.iff_eventually_eq _).1 (hx.isLocallyConstant_apply) σ₀,
      (IsLocallyConstant.iff_eventually_eq _).1 (hy.isLocallyConstant_apply) σ₀]
    with σ hσx hσy
  simp only [Point.map_some, Point.some.injEq]
  exact ⟨hσx, hσy⟩

/-- **The `ℓ`-adic Galois representation of an elliptic curve is continuous**: the action
`(σ, x) ↦ σ x` of `K ≃ₐ[F] K` with its Krull topology on `T_ℓ E` with its inverse-limit topology
is jointly continuous. -/
theorem continuous_tateModuleGaloisRepresentation_apply (ℓ : ℕ) [Fact ℓ.Prime] :
    Continuous fun q : (K ≃ₐ[F] K) × TateModule ℓ (W⁄K).toAffine.Point ↦
      W.tateModuleGaloisRepresentation ℓ q.1 q.2 :=
  (TateModule.continuous_map_apply fun n x ↦
    W.isLocallyConstant_map_of_zsmul_eq_zero (n := ((ℓ ^ n : ℕ) : ℤ))
      (Int.natCast_ne_zero.mpr (pow_ne_zero n (Fact.out : ℓ.Prime).ne_zero))
      ((Submodule.mem_torsionBy_iff _ _).mp x.2)).congr
    fun q ↦ (tateModuleGaloisRepresentation_apply q.1 q.2).symm

end WeierstrassCurve

end
