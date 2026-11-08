/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Descent
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Separability
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PointHom.Fiber

/-!
# Orders of geometric isogeny kernels

Rational kernel points are the Galois invariants of the geometric kernel coefficient module.
The geometric kernel of a separable isogeny has order equal to the degree. These identifications
express local cohomology order formulas in terms of rational kernel points and isogeny degrees.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.4.10.
-/

public noncomputable section

namespace TauCeti.Isogeny

open WeierstrassCurve ContCohomology Hom

variable {K : Type} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)

/-- Rational kernel points are exactly the Galois invariants of the geometric kernel. -/
def Hom.kerPointMapEquivInvariants [DecidableEq K] (f : Hom W₁.toAffine W₂.toAffine) :
    f.pointMapHom.ker ≃+ H0 (AbsoluteGaloisGroup K) f.KerCoeff := by
  classical
  let ι : f.pointMapHom.ker →+ H0 (AbsoluteGaloisGroup K) f.KerCoeff :=
    { toFun P := ⟨⟨W₁.basePointCoeff P, by
        rw [AddMonoidHom.mem_ker, AddMonoidHom.coe_ofClass,
          pointCoeffMap_basePointCoeff, (Hom.mem_ker_pointMapHom_iff _ _).1 P.2, map_zero]⟩,
        (FixedPoints.mem_addSubgroup _ _ _).2 fun σ ↦ Subtype.ext (W₁.smul_basePointCoeff σ P)⟩
      map_zero' := by ext; simp
      map_add' _ _ := by ext; simp }
  apply AddEquiv.ofBijective ι
  refine ⟨fun P Q h ↦ Subtype.ext (W₁.basePointCoeff_injective
    (congrArg (fun x : H0 (AbsoluteGaloisGroup K) f.KerCoeff ↦ x.val.val) h)), ?_⟩
  intro P
  obtain ⟨Q, hQ⟩ := W₁.mem_H0_pointCoeff_iff.1 <| (FixedPoints.mem_addSubgroup _ _ _).2
    fun σ ↦ congrArg Subtype.val ((FixedPoints.mem_addSubgroup _ _ _).1 P.2 σ)
  have hker : Q ∈ f.pointMapHom.ker := by
    apply (Hom.mem_ker_pointMapHom_iff _ _).2
    apply W₂.basePointCoeff_injective
    rw [map_zero, ← pointCoeffMap_basePointCoeff, hQ]
    exact P.val.2
  exact ⟨⟨Q, hker⟩, Subtype.ext (Subtype.ext hQ)⟩

/-- The kernel-invariant equivalence is the usual inclusion of rational points into `E(Kˢ)`. -/
@[simp]
theorem Hom.coe_kerPointMapEquivInvariants [DecidableEq K] (f : Hom W₁.toAffine W₂.toAffine)
    (P : f.pointMapHom.ker) :
    ((f.kerPointMapEquivInvariants P).val : W₁.PointCoeff) = W₁.basePointCoeff P := (rfl)

/-- The geometric kernel coefficient module of a separable isogeny has order equal to its degree. -/
theorem natCard_kerCoeff_eq_degree
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField] :
    Nat.card (ofIsogeny φ).KerCoeff = φ.degree := by
  classical
  let ψ := φ.baseChange (SeparableClosure K)
  have hmem (P : W₁.PointCoeff) :
      P ∈ ((ofIsogeny φ).pointCoeffMap : W₁.PointCoeff →+ W₂.PointCoeff).ker ↔
        W₁.pointCoeffEquiv.symm P ∈ ψ.toPointHom.ker := by
    rw [AddMonoidHom.mem_ker, AddMonoidHom.coe_ofClass, AddMonoidHom.mem_ker,
      ← Hom.mapSeparableClosure_ofIsogeny_pointMap,
      ← Hom.pointCoeffEquiv_symm_pointCoeffMap]
    exact W₂.pointCoeffEquiv.symm.map_eq_zero_iff.symm
  rw [Nat.card_congr (Equiv.subtypeEquiv W₁.pointCoeffEquiv.symm.toEquiv hmem),
    ψ.card_ker_toPointHom_eq_degree]
  exact degree_map φ _

end TauCeti.Isogeny
