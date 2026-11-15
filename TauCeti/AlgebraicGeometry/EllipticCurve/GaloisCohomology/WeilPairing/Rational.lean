/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.WeilPairing
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.BaseChange

/-!
# The Weil pairing on rational torsion points

For an elliptic curve `W` over an arbitrary field `K` and `m` invertible in `K`, the Weil pairing
of two `K`-rational `m`-torsion points belongs to `μ_m(K)`. Both points are Galois invariant, so
Galois equivariance makes their geometric Weil pairing invariant as well. The fixed-field theorem
for the separable closure descends the value to `K`, including when `K` is imperfect.

`TauCeti.Isogeny.rationalWeilPairing` packages this descent as an additive bilinear map with
values in `Additive (rootsOfUnity m K)`. Its comparison with the geometric coefficient pairing
characterizes it uniquely. It is alternating, commutes with arbitrary field extensions,
and makes an isogeny adjoint to its dual.
Over a separably closed base it agrees with the geometric pairing and is nondegenerate.
Over a general base the rational torsion subgroup can be isotropic.

The geometric pairing is the divisor construction in `Isogeny/MulByInt/WeilPairing/Basic.lean`;
no new choices of divisors or functions enter the descent.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.1–2.
-/

public section

noncomputable section

namespace TauCeti.Isogeny

open TauCeti.ContCohomology
open scoped WeierstrassCurve _root_.AddSubgroup

variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic]
  (m : ℕ) (hm : IsUnit (m : K))

/-- The Weil pairing of rational torsion points, with its value descended to the base field. -/
def rationalWeilPairing :
    W.toAffine.Point[(m : ℤ)] →+
      W.toAffine.Point[(m : ℤ)] →+ Additive (rootsOfUnity m K) :=
  let b := ((W.torsionCoeffWeilPairing m hm).compl₂ (W.baseTorsionCoeff m)).comp
    (W.baseTorsionCoeff m)
  let e := baseRootsOfUnityEquivInvariants K m
  { toFun P := e.symm.toAddMonoidHom.comp ((b P).codRestrict _ fun Q ↦ by
      rw [FixedPoints.mem_addSubgroup]
      intro σ
      exact (W.torsionCoeffWeilPairing_smul m hm σ
        (W.baseTorsionCoeff m P) (W.baseTorsionCoeff m Q)).symm.trans (by simp [b]))
    map_zero' := by
      apply AddMonoidHom.ext
      intro Q
      apply e.injective
      apply Subtype.ext
      simp
    map_add' P Q := by
      apply AddMonoidHom.ext
      intro T
      apply e.injective
      apply Subtype.ext
      simp }

/-- Mapping the rational Weil pairing to the separable closure recovers the geometric pairing.
This identity also makes the descent independent of every choice. -/
@[simp]
theorem restrictRootsOfUnity_rationalWeilPairing
    (P Q : W.toAffine.Point[(m : ℤ)]) :
    Additive.ofMul (restrictRootsOfUnity (algebraMap K (SeparableClosure K)) m
        (rationalWeilPairing W m hm P Q).toMul) =
      W.torsionCoeffWeilPairing m hm (W.baseTorsionCoeff m P) (W.baseTorsionCoeff m Q) := by
  rw [← coe_baseRootsOfUnityEquivInvariants]
  simp [rationalWeilPairing]

/-- Equality with a rational Weil pairing value can be checked in the separable closure. -/
theorem rationalWeilPairing_eq_iff (P Q : W.toAffine.Point[(m : ℤ)])
    (a : Additive (rootsOfUnity m K)) :
    rationalWeilPairing W m hm P Q = a ↔
      W.torsionCoeffWeilPairing m hm (W.baseTorsionCoeff m P) (W.baseTorsionCoeff m Q) =
        Additive.ofMul (restrictRootsOfUnity (algebraMap K (SeparableClosure K)) m a.toMul) := by
  rw [← restrictRootsOfUnity_rationalWeilPairing]
  exact ⟨fun h ↦ by rw [h], fun h ↦ Additive.toMul.injective <|
    restrictRootsOfUnity_injective _ _ (algebraMap K (SeparableClosure K)).injective
      (congrArg Additive.toMul h)⟩

/-- The comparison with the geometric pairing uniquely determines the rational Weil pairing. -/
theorem rationalWeilPairing_unique
    (b : W.toAffine.Point[(m : ℤ)] →+
      W.toAffine.Point[(m : ℤ)] →+ Additive (rootsOfUnity m K))
    (hb : ∀ P Q,
      Additive.ofMul (restrictRootsOfUnity (algebraMap K (SeparableClosure K)) m (b P Q).toMul) =
        W.torsionCoeffWeilPairing m hm (W.baseTorsionCoeff m P) (W.baseTorsionCoeff m Q)) :
    b = rationalWeilPairing W m hm := by
  apply AddMonoidHom.ext
  intro P
  apply AddMonoidHom.ext
  intro Q
  exact ((rationalWeilPairing_eq_iff W m hm P Q (b P Q)).2 (hb P Q).symm).symm

/-- Over a separably closed base, descent recovers the original divisor-defined Weil pairing. -/
@[simp]
theorem rationalWeilPairing_eq_weilPairing [IsSepClosed K]
    (P Q : W.toAffine.Point[(m : ℤ)]) :
    letI := hm.neZero_natCast
    rationalWeilPairing W m hm P Q = weilPairing W m hm.ne_zero P Q := by
  classical
  have := hm.neZero_natCast
  apply (rationalWeilPairing_eq_iff W m hm P Q _).2
  rw [W.torsionCoeffWeilPairing_apply m hm hm.natCast_ne_zero_of_algebra,
    W.torsionByCongr_symm_baseTorsionCoeff, W.torsionByCongr_symm_baseTorsionCoeff]
  -- The base-change curve and `W.map (algebraMap K Kˢ)` agree at default transparency.
  exact W.weilPairing_torsionMapAlong (algebraMap K (SeparableClosure K)) m hm.ne_zero P Q

/-- The rational Weil pairing is nondegenerate over a separably closed field. -/
theorem rationalWeilPairing_nondegenerate [IsSepClosed K] {P : W.toAffine.Point[(m : ℤ)]}
    (hP : ∀ Q, rationalWeilPairing W m hm P Q = 0) : P = 0 := by
  have := hm.neZero_natCast
  exact weilPairing_nondegenerate W m hm.ne_zero fun Q ↦
    (rationalWeilPairing_eq_weilPairing W m hm P Q).symm.trans (hP Q)

/-- The rational Weil pairing is alternating. -/
@[simp]
theorem rationalWeilPairing_self (P : W.toAffine.Point[(m : ℤ)]) :
    rationalWeilPairing W m hm P P = 0 := by
  apply (rationalWeilPairing_eq_iff W m hm P P 0).2
  simp only [W.torsionCoeffWeilPairing_self, toMul_zero, map_one, ofMul_one]

/-- Interchanging the arguments of the rational Weil pairing inverts its value. -/
theorem rationalWeilPairing_swap (P Q : W.toAffine.Point[(m : ℤ)]) :
    rationalWeilPairing W m hm P Q = -rationalWeilPairing W m hm Q P := by
  have h := rationalWeilPairing_self W m hm (P + Q)
  simp only [map_add, AddMonoidHom.add_apply, rationalWeilPairing_self, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

section BaseChange

variable {L : Type*} [Field L] [Algebra K L] [DecidableEq L]

/-- The rational Weil pairing commutes with arbitrary field extensions. Here `P'` and `Q'`
are the images of `P` and `Q` under the usual base-change map on points. -/
theorem rationalWeilPairing_pointMap
    {P Q : W.toAffine.Point[(m : ℤ)]}
    {P' Q' : (W⁄L).toAffine.Point[(m : ℤ)]}
    (hP : (P' : (W⁄L).toAffine.Point) = W.toAffine.pointMap L P)
    (hQ : (Q' : (W⁄L).toAffine.Point) = W.toAffine.pointMap L Q) :
    rationalWeilPairing (W⁄L) m (by simpa using hm.map (algebraMap K L)) P' Q' =
      Additive.ofMul (restrictRootsOfUnity (algebraMap K L) m
        (rationalWeilPairing W m hm P Q).toMul) := by
  let τ : SeparableClosure K →ₐ[K] SeparableClosure L := IsSepClosed.lift
  have hP' : W.torsionCoeffBaseChange τ m (W.baseTorsionCoeff m P) =
      (W⁄L).baseTorsionCoeff m P' := Subtype.ext (by simp [hP])
  have hQ' : W.torsionCoeffBaseChange τ m (W.baseTorsionCoeff m Q) =
      (W⁄L).baseTorsionCoeff m Q' := Subtype.ext (by simp [hQ])
  apply (rationalWeilPairing_eq_iff (W⁄L) m _ P' Q' _).2
  rw [← hP', ← hQ', W.torsionCoeffWeilPairing_torsionCoeffBaseChange hm τ,
    ← restrictRootsOfUnity_rationalWeilPairing]
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  simp only [toMul_kummerCoeffBaseChange, toMul_ofMul,
    restrictRootsOfUnity_coe_apply, Units.coe_map, MonoidHom.coe_ofClass]
  exact τ.commutes _

end BaseChange

section Dual

variable {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]

/-- An isogeny and its dual are adjoint for the rational Weil pairings over any field.
The images of the rational torsion points `S` and `T` are specified by `S'` and `T'`. -/
theorem rationalWeilPairing_eq_rationalWeilPairing_dual (φ : Isogeny W₁.toAffine W₂.toAffine)
    {S : W₁.toAffine.Point[(m : ℤ)]}
    {T : W₂.toAffine.Point[(m : ℤ)]}
    {S' : W₂.toAffine.Point[(m : ℤ)]}
    {T' : W₁.toAffine.Point[(m : ℤ)]}
    (hS : (Hom.ofIsogeny φ).pointMap S = S')
    (hT : (Hom.ofIsogeny φ.dual).pointMap T = T') :
    rationalWeilPairing W₂ m hm S' T = rationalWeilPairing W₁ m hm S T' := by
  classical
  have := hm.neZero_natCast
  apply (rationalWeilPairing_eq_iff W₂ m hm S' T _).2
  simp only [restrictRootsOfUnity_rationalWeilPairing,
    WeierstrassCurve.torsionCoeffWeilPairing_apply _ _ _ hm.natCast_ne_zero_of_algebra,
    WeierstrassCurve.torsionByCongr_symm_baseTorsionCoeff]
  -- The geometric pairing uses `W⁄Kˢ`, definitionally `W.map (algebraMap K Kˢ)`;
  -- the mapped isogeny and its point maps use the latter presentation.
  refine (φ.map (algebraMap K (SeparableClosure K))).weilPairing_eq_weilPairing_dual m
    hm.natCast_ne_zero_of_algebra ?_ ?_
  · simp only [← Hom.ofIsogeny_map, WeierstrassCurve.coe_torsionMapAlong_apply,
      Hom.pointMap_map, hS]
  · simp only [← dual_map, ← Hom.ofIsogeny_map, WeierstrassCurve.coe_torsionMapAlong_apply,
      Hom.pointMap_map, hT]

end Dual

end TauCeti.Isogeny
