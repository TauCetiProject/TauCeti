/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Torsion
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Separability
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Degree
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.PointHom.Fiber

/-!
# Orders of geometric and rational isogeny kernels

The Galois invariants of the geometric kernel of a morphism are precisely its rational kernel.
The equivalence here uses descent of points over the separable closure, so it works over an
arbitrary field, including imperfect fields, and also for the zero morphism. It identifies the
order of degree-zero kernel cohomology with the rational kernel order used in local duality.
For a separable isogeny, the geometric kernel has order its degree.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.1.
-/

public noncomputable section

namespace TauCeti.Isogeny.Hom

open WeierstrassCurve TauCeti.ContCohomology

variable {K : Type*} [Field K] [DecidableEq K]
  {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (f : Hom W₁.toAffine W₂.toAffine)

/-- The rational kernel identifies with the Galois invariants of the geometric kernel. -/
def baseKerCoeffEquivInvariants :
    f.pointMapHom.ker ≃+ H0 (AbsoluteGaloisGroup K) f.KerCoeff := by
  let ι : f.pointMapHom.ker →+ f.KerCoeff :=
    (W₁.basePointCoeff.comp f.pointMapHom.ker.subtype).codRestrict _ fun P ↦ by
      simp only [AddMonoidHom.comp_apply, AddSubgroup.subtype_apply, AddMonoidHom.mem_ker,
        AddMonoidHom.coe_ofClass, pointCoeffMap_basePointCoeff]
      rw [← pointMapHom_apply, AddMonoidHom.mem_ker.mp P.2, map_zero]
  let j : f.pointMapHom.ker →+ H0 (AbsoluteGaloisGroup K) f.KerCoeff :=
    ι.codRestrict _ fun P ↦ (FixedPoints.mem_addSubgroup _ _ _).2 fun σ ↦
      Subtype.ext (W₁.smul_basePointCoeff σ P)
  refine AddEquiv.ofBijective j ⟨?_, ?_⟩
  · intro P Q h
    have h' := congrArg
      (fun x : H0 (AbsoluteGaloisGroup K) f.KerCoeff ↦ ((x : f.KerCoeff) : W₁.PointCoeff)) h
    exact Subtype.ext (W₁.basePointCoeff_injective h')
  · intro P
    have hP : (P.val : W₁.PointCoeff) ∈ H0 (AbsoluteGaloisGroup K) W₁.PointCoeff :=
      (FixedPoints.mem_addSubgroup _ _ _).2 fun σ ↦
        congrArg Subtype.val ((FixedPoints.mem_addSubgroup _ _ _).1 P.2 σ)
    obtain ⟨Q, hQ⟩ := W₁.mem_H0_pointCoeff_iff.mp hP
    have hker : Q ∈ f.pointMapHom.ker := by
      apply W₂.basePointCoeff_injective
      rw [map_zero, pointMapHom_apply, ← pointCoeffMap_basePointCoeff, hQ]
      exact P.val.2
    exact ⟨⟨Q, hker⟩, Subtype.ext (Subtype.ext hQ)⟩

/-- The invariant geometric kernel point corresponding to a rational kernel point is its
image under the inclusion into the separable closure. -/
@[simp]
theorem coe_baseKerCoeffEquivInvariants (P : f.pointMapHom.ker) :
    ((f.baseKerCoeffEquivInvariants P : f.KerCoeff) : W₁.PointCoeff) =
      W₁.basePointCoeff P := (rfl)

/-- Degree-zero kernel cohomology counts the rational kernel, not the whole geometric kernel. -/
theorem natCard_H0_kerCoeff :
    Nat.card (H0 (AbsoluteGaloisGroup K) f.KerCoeff) = Nat.card f.pointMapHom.ker :=
  Nat.card_congr f.baseKerCoeffEquivInvariants.symm.toEquiv

end TauCeti.Isogeny.Hom

namespace TauCeti.Isogeny

open WeierstrassCurve TauCeti.ContCohomology

variable {K : Type*} [Field K]
  {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]

/-- A separable isogeny has as many geometric kernel points as its degree. The coefficient
module uses the separable closure; no perfectness or rationality of the kernel is needed. -/
theorem natCard_kerCoeff (φ : Isogeny W₁.toAffine W₂.toAffine)
    [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField] :
    Nat.card (Hom.ofIsogeny φ).KerCoeff = φ.degree := by
  classical
  let ψ := φ.map (algebraMap K (SeparableClosure K))
  have := isSeparable_map φ (algebraMap K (SeparableClosure K))
  have h := Nat.card_congr (W₁.pointCoeffEquiv.symm.toEquiv.subtypeEquiv
    (p := fun P ↦ P ∈ ((Hom.ofIsogeny φ).pointCoeffMap :
      W₁.PointCoeff →+ W₂.PointCoeff).ker)
    (q := fun P ↦ P ∈ ψ.toPointHom.ker) fun P ↦ by
      rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, AddMonoidHom.coe_ofClass,
        ← W₂.pointCoeffEquiv.symm.map_eq_zero_iff,
        Hom.pointCoeffEquiv_symm_pointCoeffMap]
      rw [Hom.mapSeparableClosure, Hom.ofIsogeny_map]
      exact (congrArg (fun Q ↦ Q = 0)
        (Hom.pointMap_ofIsogeny_eq_toPointHom ψ (W₁.pointCoeffEquiv.symm P))).to_iff)
  exact h.trans (ψ.card_ker_toPointHom_eq_degree.trans (degree_map φ _))

end TauCeti.Isogeny
