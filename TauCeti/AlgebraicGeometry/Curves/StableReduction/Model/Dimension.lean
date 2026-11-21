/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.Fibers
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension

import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import TauCeti.AlgebraicGeometry.Modules.Differentials.Quasicoherent
import TauCeti.AlgebraicGeometry.Modules.GlobalSections
import TauCeti.RingTheory.KrullDimension.DiscreteValuationRing

/-!
# Relative dimension of models over a discrete valuation ring

Let `R` be a discrete valuation ring with fraction field `K`, and let `M` be a model over `R` of a
scheme `C` over `K`. If `C` has relative dimension at most `d` over `K`, then `M` has relative
dimension at most `d` over `R`: its special fibre has Krull dimension at most `d`, its total space
has Krull dimension at most `d + 1`, and every point of its total space has codimension at most
`d + 1`. No excellence or catenarity hypothesis on `R` is needed.

On an affine open `U` of the total space of `M`, the ring `A = Γ(M.total, U)` is of finite type
over `R` and embeds into `B = Γ(C, M.genericι ⁻¹ᵁ U)`, so `A` is `R`-torsion-free while `B` is the
pushout of `A` along `R → K`. Since `C` has Krull dimension at most `d`, so does its affine open
`Spec B`, and `TauCeti.IsDiscreteValuationRing.ringKrullDim_fiber_le` bounds every fibre ring
`κ(p) ⊗[R] A` by `d`.

When `d = 1` and `M` is proper, this makes `M.toBase` a `FamilyOfCurves`, giving the converse to
`TauCeti.Model.familyOfCurves_toK`. Combined with `SmoothOfRelativeDimension`, any proper model of
a smooth curve over `K` is a family of curves over `Spec R`.

## Main results

* `TauCeti.Model.relativeDimensionLE_toBase`: if `RelativeDimensionLE d toK`, then
  `RelativeDimensionLE d M.toBase`.
* `TauCeti.Model.topologicalKrullDim_total_le` and `TauCeti.Model.coheight_le`: if
  `RelativeDimensionLE d toK`, then `topologicalKrullDim M.total ≤ d + 1` and every point of
  `M.total` has codimension at most `d + 1`.
* `TauCeti.Model.familyOfCurves_toBase` and `TauCeti.Model.familyOfCurves_toBase_iff`: a model is
  a family of curves over `Spec R` if and only if it is proper and `toK` has relative dimension at
  most `1`.

## References

* [Stacks Project, Lemma 55.3.2 (0B2J)](https://stacks.math.columbia.edu/tag/0B2J).
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry TauCeti.AlgebraicGeometry

namespace TauCeti

universe u

namespace Model

variable {R K : Type u} [CommRing R] [IsDomain R] [_root_.IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  {C : Scheme.{u}} {toK : C ⟶ Spec (.of K)}

/-- Over an affine open `U` of `M.total`, the chart `Spec Γ(M.total, U) ⟶ Spec R` has relative
dimension at most `d` when `toK` has relative dimension at most `d`. -/
private lemma relativeDimensionLE_fromSpec_toBase (M : Model R K C toK) {d : ℕ}
    [RelativeDimensionLE d toK] {U : M.total.Opens} (hU : IsAffineOpen U) :
    RelativeDimensionLE d (hU.fromSpec ≫ M.toBase) := by
  let : M.total.Over (Spec (.of R)) := ⟨M.toBase⟩
  let : C.Over (Spec (.of K)) := ⟨toK⟩
  have : LocallyOfFiniteType (M.total ↘ Spec (.of R)) :=
    inferInstanceAs (LocallyOfFiniteType M.toBase)
  let : Algebra R Γ(M.total, U) :=
    ((M.total.baseRingToStructurePresheaf R).app (op U)).hom.toAlgebra
  let : hU.fromSpec.IsOver (Spec (.of R)) := isOver_fromSpec R M.total ⟨U, hU⟩
  have hV : IsAffineOpen (M.genericι ⁻¹ᵁ U) := hU.preimage M.genericι
  let : Algebra K Γ(C, M.genericι ⁻¹ᵁ U) :=
    ((C.baseRingToStructurePresheaf K).app (op (M.genericι ⁻¹ᵁ U))).hom.toAlgebra
  let : Algebra Γ(M.total, U) Γ(C, M.genericι ⁻¹ᵁ U) := (M.genericι.app U).hom.toAlgebra
  let : Algebra R Γ(C, M.genericι ⁻¹ᵁ U) :=
    ((M.genericι.app U).hom.comp (algebraMap R Γ(M.total, U))).toAlgebra
  have : IsScalarTower R Γ(M.total, U) Γ(C, M.genericι ⁻¹ᵁ U) := .of_algebraMap_eq' rfl
  have : IsScalarTower R K Γ(C, M.genericι ⁻¹ᵁ U) :=
    Scheme.Modules.isScalarTower_baseRingToStructurePresheaf_app M.genericι U
      M.isPullback_genericι.toCommSq
  have : Algebra.IsPushout R Γ(M.total, U) K Γ(C, M.genericι ⁻¹ᵁ U) :=
    (Scheme.algebraIsPushout_baseRingToStructurePresheaf_of_isAffineOpen
      M.isPullback_genericι hU).symm
  have : Algebra.FiniteType R Γ(M.total, U) :=
    finiteType_sections_of_locallyOfFiniteType R M.total ⟨U, hU⟩
  have : FaithfulSMul R K :=
    (faithfulSMul_iff_algebraMap_injective R K).mpr (IsFractionRing.injective R K)
  have : Module.IsTorsionFree R Γ(C, M.genericι ⁻¹ᵁ U) := .trans K
  have : Module.IsTorsionFree R Γ(M.total, U) := (M.genericι.app_injective U).moduleIsTorsionFree
    (IsScalarTower.toAlgHom R Γ(M.total, U) Γ(C, M.genericι ⁻¹ᵁ U)) (map_smul _)
  have hdimB : ringKrullDim Γ(C, M.genericι ⁻¹ᵁ U) ≤ d := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact hV.fromSpec.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans
      ((relativeDimensionLE_iff_of_field toK).mp inferInstance)
  have hcomp : hU.fromSpec ≫ M.toBase =
      Spec.map (CommRingCat.ofHom (algebraMap R Γ(M.total, U))) :=
    HomIsOver.comp_over (f := hU.fromSpec) (S := Spec (.of R))
  rw [hcomp]
  refine (relativeDimensionLE_SpecMap_iff R Γ(M.total, U)).mpr fun p _ ↦
    (TauCeti.IsDiscreteValuationRing.ringKrullDim_fiber_le
      (K := K) (B := Γ(C, M.genericι ⁻¹ᵁ U)) p).trans hdimB

/-- **Relative dimension of a model.** If the generic fibre `C` has relative dimension at most `d`
over `K`, then the model `M` has relative dimension at most `d` over `R`. -/
@[stacks 0B2J]
instance relativeDimensionLE_toBase (M : Model R K C toK) {d : ℕ} [RelativeDimensionLE d toK] :
    RelativeDimensionLE d M.toBase := by
  refine IsZariskiLocalAtSource.of_iSup_eq_top (fun U : M.total.affineOpens ↦ U.val)
    (iSup_affineOpens_eq_top M.total) fun U ↦ ?_
  have hU : IsAffineOpen U.val := U.property
  have := relativeDimensionLE_fromSpec_toBase (d := d) M hU
  rw [← hU.isoSpec_hom_fromSpec, Category.assoc]
  exact RelativeDimensionLE.isPreimmersion_comp hU.isoSpec.hom _

/-- If `C` has relative dimension at most `d` over `K`, then the total space of any model `M` of
`C` over `R` has Krull dimension at most `d + 1`. -/
theorem topologicalKrullDim_total_le (M : Model R K C toK) {d : ℕ} [RelativeDimensionLE d toK] :
    topologicalKrullDim M.total ≤ (d + 1 : ℕ) := by
  have := LocallyOfFiniteType.isLocallyNoetherian M.toBase
  refine (topologicalKrullDim_le_add_of_relativeDimensionLE (d := d) M.toBase).trans_eq ?_
  have hSpec : topologicalKrullDim (Spec (.of R)) = ringKrullDim R :=
    PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim R
  rw [hSpec, _root_.IsDiscreteValuationRing.ringKrullDim_eq_one R, Nat.cast_add, Nat.cast_one,
    add_comm]

/-- Every point of the total space of a model of `C` has codimension at most `d + 1` when `C` has
relative dimension at most `d` over `K`. -/
theorem coheight_le (M : Model R K C toK) {d : ℕ} [RelativeDimensionLE d toK] (x : M.total) :
    Order.coheight x ≤ d + 1 := by
  exact_mod_cast (coheight_le_topologicalKrullDim x).trans (M.topologicalKrullDim_total_le (d := d))

/-- A proper model of a scheme of relative dimension at most `1` over `K` is a family of curves
over `Spec R`. This is the converse of `TauCeti.Model.familyOfCurves_toK`. -/
theorem familyOfCurves_toBase (M : Model R K C toK) [hM : M.IsProper]
    [RelativeDimensionLE 1 toK] : FamilyOfCurves M.toBase :=
  have : AlgebraicGeometry.IsProper M.toBase := hM
  ⟨⟩

/-- A model `M` is a family of curves over `Spec R` if and only if `M` is proper and its generic
fibre `C` has relative dimension at most `1` over `K`. -/
theorem familyOfCurves_toBase_iff (M : Model R K C toK) :
    FamilyOfCurves M.toBase ↔ M.IsProper ∧ RelativeDimensionLE 1 toK :=
  ⟨fun h ↦ ⟨h.toIsProper, (M.familyOfCurves_toK).toRelativeDimensionLE⟩,
    fun ⟨_, _⟩ ↦ have := ‹M.IsProper›; have := ‹RelativeDimensionLE 1 toK›; M.familyOfCurves_toBase⟩

end Model

end TauCeti
