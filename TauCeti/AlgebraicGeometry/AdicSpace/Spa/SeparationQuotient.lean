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

This is the passage-to-the-separation-quotient part of Wedhorn Proposition 7.49(2). It also proves
that if the separation quotient is discrete, then the analytic locus is empty.

## Main results

* `TauCeti.ValuationSpectrum.spaSeparationQuotientHomeomorph`: the adic spectrum is unchanged by
  quotienting by the closure of zero.
* `TauCeti.ValuationSpectrum.spaComap_preimage_spaAnalytic_separationQuotient`: this
  homeomorphism identifies the two analytic loci.
* `TauCeti.ValuationSpectrum.spaAnalytic_eq_empty_iff_separationQuotient`: emptiness of the
  analytic locus is invariant under passage to the separation quotient.
* `TauCeti.ValuationSpectrum.spaAnalytic_eq_empty_of_discrete_separationQuotient`: the easy
  implication in the analytic nonemptiness criterion.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Proposition 7.49(2).

-/

public section

namespace TauCeti.ValuationSpectrum

open Topology

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- Under pullback from an ideal quotient, the preimage of the analytic locus is the analytic locus
of the quotient. -/
theorem spaComap_preimage_spaAnalytic_quotientMk (J : Ideal A) (Aplus : Subring A) :
    spaComap (Ideal.Quotient.mk J) continuous_quotient_mk' Aplus
        (Aplus.map (Ideal.Quotient.mk J))
        (fun a ha ↦ (Subring.mem_map (f := Ideal.Quotient.mk J)).mpr ⟨a, ha, rfl⟩) ⁻¹'
      (Subtype.val ⁻¹' spaAnalytic Aplus) =
      Subtype.val ⁻¹' spaAnalytic (Aplus.map (Ideal.Quotient.mk J)) := by
  ext v
  simp only [Set.mem_preimage, mem_spaAnalytic_iff]
  rw [and_iff_right (spaComap (Ideal.Quotient.mk J) continuous_quotient_mk' Aplus
    (Aplus.map (Ideal.Quotient.mk J)) _ v).property,
    and_iff_right v.property]
  have hval :
      (spaComap (Ideal.Quotient.mk J) continuous_quotient_mk' Aplus
        (Aplus.map (Ideal.Quotient.mk J))
        (fun a ha ↦ (Subring.mem_map (f := Ideal.Quotient.mk J)).mpr ⟨a, ha, rfl⟩) v).1 =
      comap (Ideal.Quotient.mk J) v.1 :=
    spaComap_val (Ideal.Quotient.mk J) continuous_quotient_mk' Aplus
      (Aplus.map (Ideal.Quotient.mk J)) _ v
  rw [hval]
  rw [isAnalyticPoint_def, isAnalyticPoint_def, isOpen_supp_comap_quotientMk_iff]

section TopologicalRing

variable [IsTopologicalRing A]

/-- The ring quotient by the closure of zero. It is homeomorphic to Mathlib's
`SeparationQuotient A`. -/
abbrev separationQuotientRing : Type _ :=
  A ⧸ Ideal.closure (⊥ : Ideal A)

/-- The image of a plus ring in the quotient by the closure of zero. -/
abbrev separationQuotientPlus (Aplus : Subring A) :
    Subring (separationQuotientRing (A := A)) :=
  Aplus.map (Ideal.Quotient.mk (Ideal.closure (⊥ : Ideal A)))

/-- **Wedhorn Proposition 7.49(2), separated-quotient invariance.** Pullback along the quotient by
the closure of zero is a homeomorphism on adic spectra. The plus ring on the quotient is the image
of `Aplus`. -/
noncomputable def spaSeparationQuotientHomeomorph (Aplus : Subring A) :
    spa (separationQuotientPlus Aplus) ≃ₜ spa Aplus := by
  apply Topology.IsEmbedding.toHomeomorphOfSurjective
    (isEmbedding_spaComap_quotientMk (Ideal.closure (⊥ : Ideal A)) Aplus)
  rw [← Set.range_eq_univ,
    range_spaComap_quotientMk (Ideal.closure (⊥ : Ideal A)) Aplus]
  ext v
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact closure_zero_le_supp_of_isContinuous ((mem_spa_iff Aplus v).mp v.property).1

/-- The separated-quotient homeomorphism is pullback along the quotient map. -/
@[simp]
theorem spaSeparationQuotientHomeomorph_apply (Aplus : Subring A)
    (v : spa (separationQuotientPlus Aplus)) :
    spaSeparationQuotientHomeomorph Aplus v =
      spaComap (Ideal.Quotient.mk (Ideal.closure (⊥ : Ideal A)))
        (continuous_quotient_mk' : Continuous
          (Ideal.Quotient.mk (Ideal.closure (⊥ : Ideal A))))
        Aplus (separationQuotientPlus Aplus)
        (fun a ha ↦ (Subring.mem_map
          (f := Ideal.Quotient.mk (Ideal.closure (⊥ : Ideal A)))).mpr ⟨a, ha, rfl⟩) v := by
  exact Topology.IsEmbedding.toHomeomorphOfSurjective_apply _ _ v

/-- Under pullback from the quotient by the closure of zero, the preimage of the analytic locus is
the analytic locus of the quotient. -/
theorem spaComap_preimage_spaAnalytic_separationQuotient (Aplus : Subring A) :
    spaComap (Ideal.Quotient.mk (Ideal.closure (⊥ : Ideal A)))
        (continuous_quotient_mk' : Continuous
          (Ideal.Quotient.mk (Ideal.closure (⊥ : Ideal A))))
        Aplus (separationQuotientPlus Aplus)
        (fun a ha ↦ (Subring.mem_map
          (f := Ideal.Quotient.mk (Ideal.closure (⊥ : Ideal A)))).mpr ⟨a, ha, rfl⟩) ⁻¹'
      (Subtype.val ⁻¹' spaAnalytic Aplus) =
      Subtype.val ⁻¹' spaAnalytic (separationQuotientPlus Aplus) :=
  spaComap_preimage_spaAnalytic_quotientMk (Ideal.closure (⊥ : Ideal A)) Aplus

/-- **Wedhorn Proposition 7.49(2)(iii), locus form.** The homeomorphism induced by passage to the
separated quotient identifies the analytic loci. -/
theorem spaSeparationQuotientHomeomorph_preimage_spaAnalytic (Aplus : Subring A) :
    spaSeparationQuotientHomeomorph Aplus ⁻¹' (Subtype.val ⁻¹' spaAnalytic Aplus) =
      Subtype.val ⁻¹' spaAnalytic (separationQuotientPlus Aplus) := by
  ext v
  rw [Set.mem_preimage, spaSeparationQuotientHomeomorph_apply]
  exact Set.ext_iff.mp (spaComap_preimage_spaAnalytic_separationQuotient Aplus) v

/-- Emptiness of the analytic locus is invariant under passage to the separated quotient. -/
theorem spaAnalytic_eq_empty_iff_separationQuotient (Aplus : Subring A) :
    spaAnalytic Aplus = ∅ ↔ spaAnalytic (separationQuotientPlus Aplus) = ∅ := by
  rw [← val_preimage_spaAnalytic_eq_empty_iff Aplus,
    ← val_preimage_spaAnalytic_eq_empty_iff (separationQuotientPlus Aplus)]
  let e := spaSeparationQuotientHomeomorph Aplus
  have he : e ⁻¹' (Subtype.val ⁻¹' spaAnalytic Aplus) = ∅ ↔
      (Subtype.val ⁻¹' spaAnalytic Aplus : Set (spa Aplus)) = ∅ := by
    rw [Set.preimage_eq_empty_iff, e.surjective.range_eq]
    simp
  calc
    (Subtype.val ⁻¹' spaAnalytic Aplus : Set (spa Aplus)) = ∅ ↔
        e ⁻¹' (Subtype.val ⁻¹' spaAnalytic Aplus) = ∅ := he.symm
    _ ↔ (Subtype.val ⁻¹' spaAnalytic (separationQuotientPlus Aplus) :
        Set (spa (separationQuotientPlus Aplus))) = ∅ := by
      rw [spaSeparationQuotientHomeomorph_preimage_spaAnalytic]

/-- The easy implication of Wedhorn Proposition 7.49(2): if the separated quotient of a topological
ring is discrete, then its analytic locus is empty. No condition on the plus ring is needed for
this implication. -/
theorem spaAnalytic_eq_empty_of_discrete_separationQuotient (Aplus : Subring A)
    (hdisc : DiscreteTopology (SeparationQuotient A)) : spaAnalytic Aplus = ∅ := by
  let _ := hdisc
  let _ : DiscreteTopology (separationQuotientRing (A := A)) :=
    (UniformSpace.sepQuotHomeomorphRingQuot A).discreteTopology
  rw [spaAnalytic_eq_empty_iff_separationQuotient]
  ext v
  simp only [Set.notMem_empty, iff_false, mem_spaAnalytic_iff]
  exact fun hv ↦ (isAnalyticPoint_def v).mp hv.2 (isOpen_discrete _)

end TopologicalRing

end TauCeti.ValuationSpectrum

end
