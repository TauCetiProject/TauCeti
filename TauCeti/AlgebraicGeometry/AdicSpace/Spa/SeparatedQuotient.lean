/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Analytic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Comap
public import Mathlib.Topology.Algebra.UniformRing

/-!
# The analytic locus and the separated quotient

For a topological ring `A`, every continuous valuation kills the closure of zero. Consequently,
pullback along

```text
A → A / closure (0)
```

identifies the adic spectrum of the quotient (with the image plus ring) with the adic spectrum of
`A`. This identification preserves analytic points: a support ideal in the quotient is open if and
only if its inverse image in `A` is open.

This is the passage-to-the-separated-quotient part of Wedhorn Proposition 7.49(2). It reduces the
remaining criterion for nonemptiness of the analytic locus to the Hausdorff case. We also prove the
easy direction of that criterion: if the separated quotient is discrete, then the analytic locus is
empty.

## Main results

* `TauCeti.ValuationSpectrum.closure_zero_le_supp_of_isContinuous`: every continuous valuation
  kills the closure of zero.
* `TauCeti.ValuationSpectrum.spaSeparatedQuotientHomeomorph`: the adic spectrum is unchanged by
  quotienting by the closure of zero.
* `TauCeti.ValuationSpectrum.spaComapSeparatedQuotient_preimage_spaAnalytic`: this
  homeomorphism identifies the two analytic loci.
* `TauCeti.ValuationSpectrum.spaAnalytic_eq_empty_iff_separatedQuotient`: emptiness of the
  analytic locus is invariant under passage to the separated quotient.
* `TauCeti.ValuationSpectrum.spaAnalytic_eq_empty_of_discrete_separationQuotient`: the easy
  implication in the analytic nonemptiness criterion.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 7.49(2).

## Provenance

Developed here; nothing is ported. No external formalization is followed.
-/

public section

namespace TauCeti.ValuationSpectrum

open Topology

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- Pullback along a quotient map preserves and reflects whether the support of a valuation is
open. This is the pointwise reason that quotienting by the closure of zero preserves analytic
points. -/
theorem isOpen_supp_comap_quotientMk_iff (J : Ideal A) (v : Spv (A ⧸ J)) :
    IsOpen ((comap (Ideal.Quotient.mk J) v).supp : Set A) ↔
      IsOpen (v.supp : Set (A ⧸ J)) := by
  have hsupp : Ideal.Quotient.mk J ⁻¹' (v.supp : Set (A ⧸ J)) =
      ((comap (Ideal.Quotient.mk J) v).supp : Set A) := by
    ext a
    simp only [Set.mem_preimage, SetLike.mem_coe, mem_supp_iff, comap_vle, map_zero]
  rw [← hsupp]
  exact isOpen_coinduced.symm

/-- The analytic locus is empty if and only if its preimage in the subtype `spa Aplus` is empty.
This converts between the ambient-set convention used by `spaAnalytic` and the actual topological
space on which maps of adic spectra are defined. -/
private theorem val_preimage_spaAnalytic_eq_empty_iff (Aplus : Subring A) :
    Subtype.val ⁻¹' spaAnalytic Aplus = (∅ : Set (spa Aplus)) ↔ spaAnalytic Aplus = ∅ := by
  constructor
  · intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hvSpa := (mem_spaAnalytic_iff Aplus v).mp hv |>.1
    have : (⟨v, hvSpa⟩ : spa Aplus) ∈ Subtype.val ⁻¹' spaAnalytic Aplus := hv
    rw [h] at this
    exact this
  · intro h
    rw [h, Set.preimage_empty]

section SeparatelyContinuousAdd

variable [SeparatelyContinuousAdd A]

/-- The support of every continuous valuation contains the closure of zero.

If `x` is in the closure of zero but has nonzero value, the open valuation ball about `x` of radius
`v(x)` must contain zero. This says `v(-x) < v(x)`, contradicting invariance under negation. -/
theorem closure_zero_subset_supp_of_isContinuous {v : Spv A} (hv : v.IsContinuous) :
    closure ({0} : Set A) ⊆ v.supp := by
  intro x hx
  rw [v.supp_eq_valuation_supp]
  change v.valuation x = 0
  by_contra hx0
  have hball := ((isContinuous_def v).mp hv).sub_lt_mem_nhds x hx0
  obtain ⟨y, hyball, hy⟩ := mem_closure_iff_nhds.mp hx _ hball
  rw [Set.mem_singleton_iff] at hy
  subst y
  change v.valuation (0 - x) < v.valuation x at hyball
  rw [zero_sub, v.valuation.map_neg] at hyball
  exact (lt_irrefl _ hyball)

end SeparatelyContinuousAdd

section TopologicalRing

variable [IsTopologicalRing A]

/-- The support of every continuous valuation contains the closure of the zero ideal.
Equivalently, every continuous valuation factors through the separated quotient. -/
theorem closure_zero_le_supp_of_isContinuous {v : Spv A} (hv : v.IsContinuous) :
    Ideal.closure (⊥ : Ideal A) ≤ v.supp := by
  intro x hx
  apply closure_zero_subset_supp_of_isContinuous hv
  rwa [← SetLike.mem_coe, Ideal.coe_closure, Submodule.bot_coe] at hx

/-- The ring quotient by the closure of zero. It is homeomorphic to Mathlib's
`SeparationQuotient A`. -/
abbrev separatedQuotientRing : Type _ :=
  A ⧸ Ideal.closure (⊥ : Ideal A)

/-- The image of a plus ring in the quotient by the closure of zero. -/
abbrev separatedQuotientPlus (Aplus : Subring A) :
    Subring (separatedQuotientRing (A := A)) :=
  Aplus.map (Ideal.Quotient.mk (Ideal.closure (⊥ : Ideal A)))

/-- Pullback on adic spectra along the quotient by the closure of zero. -/
def spaComapSeparatedQuotient (Aplus : Subring A) :
    spa (separatedQuotientPlus Aplus) → spa Aplus := fun v ↦
  ⟨comap (Ideal.Quotient.mk (Ideal.closure (⊥ : Ideal A))) v.1,
    comap_mem_spa continuous_quotient_mk'
      (fun a ha ↦
        (Subring.mem_map (f := Ideal.Quotient.mk (Ideal.closure (⊥ : Ideal A)))).mpr
          ⟨a, ha, rfl⟩)
      v.property⟩

/-- The valuation underlying pullback from the separated quotient is the ordinary pullback along
the quotient homomorphism. -/
@[simp]
theorem spaComapSeparatedQuotient_val (Aplus : Subring A)
    (v : spa (separatedQuotientPlus Aplus)) :
    (spaComapSeparatedQuotient Aplus v).1 =
      comap (Ideal.Quotient.mk (Ideal.closure (⊥ : Ideal A))) v.1 := by
  rfl

/-- Pullback from the separated quotient is a topological embedding. -/
theorem isEmbedding_spaComapSeparatedQuotient (Aplus : Subring A) :
    Topology.IsEmbedding (spaComapSeparatedQuotient Aplus) := by
  have hcomp : Subtype.val ∘ spaComapSeparatedQuotient Aplus =
      comap (Ideal.Quotient.mk (Ideal.closure (⊥ : Ideal A))) ∘ Subtype.val := by
    funext v
    exact spaComapSeparatedQuotient_val Aplus v
  refine Topology.IsEmbedding.of_comp_iff Topology.IsEmbedding.subtypeVal |>.mp ?_
  rw [hcomp]
  exact (isEmbedding_comap_quotientMk (Ideal.closure (⊥ : Ideal A))).comp
    Topology.IsEmbedding.subtypeVal

/-- Pullback from the quotient by the closure of zero is surjective on adic spectra. -/
private theorem spaComapSeparatedQuotient_surjective (Aplus : Subring A) :
    Function.Surjective (spaComapSeparatedQuotient Aplus) := by
  intro v
  let J : Ideal A := Ideal.closure ⊥
  have hJ : J ≤ v.1.supp :=
    closure_zero_le_supp_of_isContinuous ((mem_spa_iff Aplus v).mp v.property).1
  have hwSpa : quotientLift J hJ ∈ spa (separatedQuotientPlus Aplus) := by
    rw [mem_spa_iff]
    refine ⟨IsContinuous.quotientLift J hJ ((mem_spa_iff Aplus v).mp v.property).1, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_one (Ideal.Quotient.mk J), ← comap_vle, comap_quotientLift]
    exact (mem_spa_iff Aplus v).mp v.property |>.2 a ha
  refine ⟨⟨quotientLift J hJ, hwSpa⟩, ?_⟩
  apply Subtype.ext
  rw [spaComapSeparatedQuotient_val, comap_quotientLift]

/-- **Wedhorn Proposition 7.49(2), separated-quotient invariance.** Pullback along the quotient by
the closure of zero is a homeomorphism on adic spectra. The plus ring on the quotient is the image
of `Aplus`. -/
noncomputable def spaSeparatedQuotientHomeomorph (Aplus : Subring A) :
    spa (separatedQuotientPlus Aplus) ≃ₜ spa Aplus :=
  (isEmbedding_spaComapSeparatedQuotient Aplus).toHomeomorphOfSurjective
    (spaComapSeparatedQuotient_surjective Aplus)

/-- The separated-quotient homeomorphism is pullback along the quotient map. -/
@[simp]
theorem spaSeparatedQuotientHomeomorph_apply (Aplus : Subring A)
    (v : spa (separatedQuotientPlus Aplus)) :
    spaSeparatedQuotientHomeomorph Aplus v = spaComapSeparatedQuotient Aplus v :=
  by
    exact Topology.IsEmbedding.toHomeomorphOfSurjective_apply
      (isEmbedding_spaComapSeparatedQuotient Aplus)
      (spaComapSeparatedQuotient_surjective Aplus) v

/-- Under pullback from the quotient by the closure of zero, the preimage of the analytic locus is
the analytic locus of the quotient. -/
theorem spaComapSeparatedQuotient_preimage_spaAnalytic (Aplus : Subring A) :
    spaComapSeparatedQuotient Aplus ⁻¹' (Subtype.val ⁻¹' spaAnalytic Aplus) =
      Subtype.val ⁻¹' spaAnalytic (separatedQuotientPlus Aplus) := by
  ext v
  simp only [Set.mem_preimage, mem_spaAnalytic_iff]
  rw [and_iff_right (spaComapSeparatedQuotient Aplus v).property, and_iff_right v.property]
  rw [spaComapSeparatedQuotient_val]
  rw [isAnalyticPoint_def, isAnalyticPoint_def, isOpen_supp_comap_quotientMk_iff]

/-- **Wedhorn Proposition 7.49(2)(iii), locus form.** The homeomorphism induced by passage to the
separated quotient identifies the analytic loci. -/
theorem spaSeparatedQuotientHomeomorph_preimage_spaAnalytic (Aplus : Subring A) :
    spaSeparatedQuotientHomeomorph Aplus ⁻¹' (Subtype.val ⁻¹' spaAnalytic Aplus) =
      Subtype.val ⁻¹' spaAnalytic (separatedQuotientPlus Aplus) := by
  ext v
  rw [Set.mem_preimage, spaSeparatedQuotientHomeomorph_apply]
  exact Set.ext_iff.mp (spaComapSeparatedQuotient_preimage_spaAnalytic Aplus) v

/-- Emptiness of the analytic locus is invariant under passage to the separated quotient. -/
theorem spaAnalytic_eq_empty_iff_separatedQuotient (Aplus : Subring A) :
    spaAnalytic Aplus = ∅ ↔ spaAnalytic (separatedQuotientPlus Aplus) = ∅ := by
  rw [← val_preimage_spaAnalytic_eq_empty_iff Aplus,
    ← val_preimage_spaAnalytic_eq_empty_iff (separatedQuotientPlus Aplus)]
  let e := spaSeparatedQuotientHomeomorph Aplus
  have he : e ⁻¹' (Subtype.val ⁻¹' spaAnalytic Aplus) = ∅ ↔
      (Subtype.val ⁻¹' spaAnalytic Aplus : Set (spa Aplus)) = ∅ := by
    rw [Set.preimage_eq_empty_iff, e.surjective.range_eq]
    simp
  calc
    (Subtype.val ⁻¹' spaAnalytic Aplus : Set (spa Aplus)) = ∅ ↔
        e ⁻¹' (Subtype.val ⁻¹' spaAnalytic Aplus) = ∅ := he.symm
    _ ↔ (Subtype.val ⁻¹' spaAnalytic (separatedQuotientPlus Aplus) :
        Set (spa (separatedQuotientPlus Aplus))) = ∅ := by
      rw [spaSeparatedQuotientHomeomorph_preimage_spaAnalytic]

/-- The easy implication of Wedhorn Proposition 7.49(2): if the separated quotient of a topological
ring is discrete, then its analytic locus is empty. No condition on the plus ring is needed for
this implication. -/
theorem spaAnalytic_eq_empty_of_discrete_separationQuotient (Aplus : Subring A)
    (hdisc : DiscreteTopology (SeparationQuotient A)) : spaAnalytic Aplus = ∅ := by
  let _ := hdisc
  let _ : DiscreteTopology (separatedQuotientRing (A := A)) :=
    (UniformSpace.sepQuotHomeomorphRingQuot A).discreteTopology
  rw [spaAnalytic_eq_empty_iff_separatedQuotient]
  ext v
  simp only [Set.notMem_empty, iff_false, mem_spaAnalytic_iff]
  exact fun hv ↦ (isAnalyticPoint_def v).mp hv.2 (isOpen_discrete _)

end TopologicalRing

end TauCeti.ValuationSpectrum

end
