/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Isogeny.Descent
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.Cokernel
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TopologicallyFinitelyGenerated
public import TauCeti.NumberTheory.LocalField.Generation.AbsoluteGaloisGroup

/-!
# Finiteness of local isogeny cokernels

For a nonzero morphism `f : E₁ → E₂` over a finite extension `K` of `ℚ_p`, the quotient
`E₂(K) / f E₁(K)` is finite, including when `p` divides the degree. This makes its order an
honest finite local Kummer index, as needed in isogeny descent and the local factors of Cassels'
isogeny formula.

The argument uses the Kummer injection into `H¹(G_K, E₁[f])`. The geometric kernel is finite,
and the absolute Galois group of a finite extension of `ℚ_p` is topologically finitely generated,
so this degree-one cohomology group is finite. No reduction hypothesis is required. The
cohomological argument is also stated for a separable isogeny over any field whose absolute
Galois group is topologically finitely generated.

## Main results

* `TauCeti.Isogeny.Hom.finite_kerCoeff`: a nonzero morphism has finite geometric kernel.
* `TauCeti.Isogeny.finiteIndex_range_pointMapHom_of_isTopologicallyFinitelyGenerated`: the
  cokernel of a separable isogeny is finite when the absolute Galois group is topologically
  finitely generated.
* `TauCeti.Isogeny.Hom.finiteIndex_range_pointMapHom_of_module_finite_padic`: the local
  cokernel of any nonzero morphism over a finite extension of `ℚ_p` is finite.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.4.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (7.4.1),
  for topological finite generation of local absolute Galois groups.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. Reine Angew. Math. 217 (1965), 180–199.
-/

public section

noncomputable section

open WeierstrassCurve TauCeti.ContCohomology

namespace TauCeti.Isogeny

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]

/-- The geometric kernel of a nonzero morphism is finite, read in the discrete Galois
coefficient module. -/
theorem Hom.finite_kerCoeff (f : Hom W₁.toAffine W₂.toAffine) (hf : f ≠ 0) :
    Finite f.KerCoeff := by
  classical
  have := f.mapSeparableClosure.finite_ker_pointMapHom
    (fun h ↦ hf ((Hom.map_eq_zero_iff f (algebraMap K (SeparableClosure K))).1 h))
  let ι : f.KerCoeff → f.mapSeparableClosure.pointMapHom.ker := fun P ↦
    ⟨W₁.pointCoeffEquiv.symm P, by
      have hP := P.2
      rw [AddMonoidHom.mem_ker, AddMonoidHom.coe_ofClass] at hP
      rw [AddMonoidHom.mem_ker, Hom.pointMapHom_apply,
        ← Hom.pointCoeffEquiv_symm_pointCoeffMap, hP, map_zero]⟩
  exact Finite.of_injective ι fun P Q h ↦
    Subtype.ext (W₁.pointCoeffEquiv.symm.injective (congrArg Subtype.val h))

/-- The first cohomology of the geometric kernel of a nonzero morphism is finite when the
absolute Galois group is topologically finitely generated. -/
theorem Hom.finite_H1_kerCoeff_of_isTopologicallyFinitelyGenerated
    (f : Hom W₁.toAffine W₂.toAffine) (hf : f ≠ 0)
    (hK : IsTopologicallyFinitelyGenerated (AbsoluteGaloisGroup K)) :
    Finite (H1 (AbsoluteGaloisGroup K) f.KerCoeff) := by
  have := f.finite_kerCoeff hf
  exact hK.finite_H1

variable (φ : Isogeny W₁.toAffine W₂.toAffine)
  [Algebra.IsSeparable φ.fieldPullback.fieldRange W₁.toAffine.FunctionField] [DecidableEq K]

/-- The Kummer injection makes the cokernel of a separable isogeny finite over a field with
topologically finitely generated absolute Galois group. -/
theorem finiteIndex_range_pointMapHom_of_isTopologicallyFinitelyGenerated
    (hK : IsTopologicallyFinitelyGenerated (AbsoluteGaloisGroup K)) :
    (Hom.ofIsogeny φ).pointMapHom.range.FiniteIndex := by
  have := (Hom.ofIsogeny φ).finite_H1_kerCoeff_of_isTopologicallyFinitelyGenerated
    (Hom.ofIsogeny_ne_zero φ) hK
  have := Finite.of_injective φ.kummerClassMap φ.kummerClassMap_injective
  exact AddSubgroup.finiteIndex_of_finite_quotient

/-- A nonzero morphism in characteristic zero has finite cokernel when the absolute Galois
group is topologically finitely generated. -/
theorem Hom.finiteIndex_range_pointMapHom_of_isTopologicallyFinitelyGenerated [CharZero K]
    (f : Hom W₁.toAffine W₂.toAffine) (hf : f ≠ 0)
    (hK : IsTopologicallyFinitelyGenerated (AbsoluteGaloisGroup K)) :
    f.pointMapHom.range.FiniteIndex := by
  have h := (Hom.toIsogeny hf).finiteIndex_range_pointMapHom_of_isTopologicallyFinitelyGenerated hK
  simpa only [Hom.ofIsogeny_toIsogeny] using h

end TauCeti.Isogeny

namespace TauCeti.Isogeny.Hom

variable (p : ℕ) [Fact p.Prime] {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Algebra ℚ_[p] K] [Module.Finite ℚ_[p] K]
  [ValuativeExtension ℚ_[p] K]
  {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (f : Hom W₁.toAffine W₂.toAffine)

include p

variable [DecidableEq K]

/-- The local Kummer cokernel `E₂(K) / f E₁(K)` is finite for every nonzero morphism over a
finite compatible extension of `ℚ_p`, even when `p` divides its degree. -/
theorem finiteIndex_range_pointMapHom_of_module_finite_padic (hf : f ≠ 0) :
    f.pointMapHom.range.FiniteIndex := by
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  exact f.finiteIndex_range_pointMapHom_of_isTopologicallyFinitelyGenerated hf
    (isTopologicallyFinitelyGenerated_absoluteGaloisGroup p K)

end TauCeti.Isogeny.Hom
