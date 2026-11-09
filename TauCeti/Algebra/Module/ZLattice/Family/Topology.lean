/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ZLattice.Family.HomeomorphProd
import TauCeti.Algebra.Module.ZLattice.Quotient

/-!
# Point-set topology of a family of tori

Let `P : Y → (Λ →ₗ[ℤ] E)` be a period family: each period `y ↦ P y l` is continuous and each
`P y` is injective with discrete, full range in a finite-dimensional real normed space `E`. Its
total space is the standard orbit space `(Y × E)/Λ` of the period translation action
(`TauCeti.periodAddAction`), with projection `p : (Y × E)/Λ → Y`
(`TauCeti.torusFamilyProjection`). This file proves the point-set properties of the total space
that a manifold structure on it does not provide by itself.

* The projection `p` is a proper map (`TauCeti.isProperMap_torusFamilyProjection`). In
  particular the preimage of every compact set of parameters is compact
  (`IsProperMap.isCompact_preimage`); taking a singleton, every fibre is compact, which is the
  compactness of the torus `E / LinearMap.range (P y)` read inside the family.
* The total space is Hausdorff when `Y` is (`TauCeti.t2Space_torusFamily`), and compact when
  `Y` is (`TauCeti.compactSpace_torusFamily`).
* The total space is second countable when `Y` is
  (`TauCeti.secondCountableTopology_torusFamily`, in
  `TauCeti.Algebra.Module.ZLattice.Family.Basic`). This needs only continuity of the periods:
  the orbit map of a group acting by homeomorphisms is open.

With the complex-manifold structure of `TauCeti.Algebra.Module.ZLattice.Family.Manifold`, for a
Hausdorff, second-countable complex manifold `Y` and holomorphic periods, these make `(Y × E)/Λ`
a Hausdorff, second-countable complex manifold whose holomorphic submersion `p` is proper with
compact torus fibres.

Properness, Hausdorffness and compactness are read off the global trivialization
`TauCeti.torusFamilyHomeomorphProd`, a homeomorphism over `Y` onto the product of `Y` with the
compact Hausdorff torus `ℝ^ι/ℤ^ι` attached to a lattice basis of `Λ`. The basis is a proof choice:
no statement depends on it, and the trivialization is only topological, so nothing here asserts
holomorphic triviality.

## Main results

* `TauCeti.isProperMap_torusFamilyProjection`: the projection of the family is proper, so its
  fibres are compact.
* `TauCeti.t2Space_torusFamily`: the total space is Hausdorff over a Hausdorff base.
* `TauCeti.compactSpace_torusFamily`: the total space is compact over a compact base.
* `TauCeti.locallyCompactSpace_torusFamily`: the total space is locally compact over a locally
  compact base.

## References

* Christina Birkenhake and Herbert Lange, *Complex Abelian Varieties*, second edition,
  Grundlehren der mathematischen Wissenschaften 302, Springer, 2004, Chapter 8 (families of
  complex tori given by period matrices).
-/

public section

open Module Set Function Submodule

namespace TauCeti

section Trivialization

variable {Y : Type*} [TopologicalSpace Y] {Λ : Type*} [AddCommGroup Λ] [Module.Free ℤ Λ]
  [Module.Finite ℤ Λ] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (P : Y → Λ →ₗ[ℤ] E) [∀ y, DiscreteTopology (LinearMap.range (P y))]
  [∀ y, IsZLattice ℝ (LinearMap.range (P y))]

/-- The projection of the family is the first projection of `Y × T` read through a homeomorphism
over `Y`, where `T` is the standard torus `ℝ^ι/ℤ^ι` of a lattice basis of `Λ`, in its orbit-space
model, which is compact and Hausdorff. This is `TauCeti.torusFamilyHomeomorphProd` for the chosen
basis, followed on the torus factor by `Submodule.orbitRelQuotientContinuousAddEquiv`. -/
private theorem exists_homeomorph_prod_fst_eq_torusFamilyProjection
    (hcont : ∀ l, Continuous fun y ↦ P y l) (hinj : ∀ y, Injective (P y)) :
    letI := periodAddAction P
    ∃ e : AddAction.orbitRel.Quotient Λ (Y × E) ≃ₜ
        Y × AddAction.orbitRel.Quotient
          (span ℤ (range (Pi.basisFun ℝ (Free.ChooseBasisIndex ℤ Λ))))
          (Free.ChooseBasisIndex ℤ Λ → ℝ),
      ∀ z, (e z).1 = torusFamilyProjection P z := by
  let _ := periodAddAction P
  refine ⟨(torusFamilyHomeomorphProd P (Free.chooseBasis ℤ Λ) hinj hcont).trans
    ((Homeomorph.refl Y).prodCongr
      (span ℤ _).orbitRelQuotientContinuousAddEquiv.toHomeomorph.symm), fun z ↦ ?_⟩
  exact fst_torusFamilyHomeomorphProd P (Free.chooseBasis ℤ Λ) hinj hcont z

/-- **The projection of a family of tori is proper.** For a continuous family of full lattices,
the projection `(Y × E)/Λ → Y` is a proper map: it is continuous, and the preimage of every
compact set of parameters is compact (`IsProperMap.isCompact_preimage`). In particular each fibre
is compact; it is the torus `E / LinearMap.range (P y)` (`TauCeti.torusFamilyFiberHomeomorph`). No
hypothesis on `Y` is needed. -/
theorem isProperMap_torusFamilyProjection (hcont : ∀ l, Continuous fun y ↦ P y l)
    (hinj : ∀ y, Injective (P y)) : IsProperMap (torusFamilyProjection P) := by
  let _ := periodAddAction P
  obtain ⟨e, he⟩ := exists_homeomorph_prod_fst_eq_torusFamilyProjection P hcont hinj
  have hp : torusFamilyProjection P = Prod.fst ∘ e := funext fun z ↦ (he z).symm
  rw [hp]
  exact isProperMap_fst_of_compactSpace.comp e.isProperMap

/-- **A family of tori over a Hausdorff base is Hausdorff.** For a continuous family of full
lattices over a Hausdorff space `Y`, the total space `(Y × E)/Λ` is Hausdorff. -/
theorem t2Space_torusFamily [T2Space Y] (hcont : ∀ l, Continuous fun y ↦ P y l)
    (hinj : ∀ y, Injective (P y)) :
    letI := periodAddAction P
    T2Space (AddAction.orbitRel.Quotient Λ (Y × E)) := by
  let _ := periodAddAction P
  obtain ⟨e, -⟩ := exists_homeomorph_prod_fst_eq_torusFamilyProjection P hcont hinj
  exact e.symm.t2Space

/-- **A family of tori over a compact base is compact.** For a continuous family of full lattices
over a compact space `Y`, the total space `(Y × E)/Λ` is compact. -/
theorem compactSpace_torusFamily [CompactSpace Y] (hcont : ∀ l, Continuous fun y ↦ P y l)
    (hinj : ∀ y, Injective (P y)) :
    letI := periodAddAction P
    CompactSpace (AddAction.orbitRel.Quotient Λ (Y × E)) := by
  let _ := periodAddAction P
  obtain ⟨e, -⟩ := exists_homeomorph_prod_fst_eq_torusFamilyProjection P hcont hinj
  exact e.symm.compactSpace

end Trivialization

section LocallyCompact

variable {Y : Type*} [TopologicalSpace Y] {Λ : Type*} [AddCommGroup Λ] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (P : Y → Λ →ₗ[ℤ] E)

/-- **A family of tori over a locally compact base is locally compact.** For a continuous family of
periods over a locally compact space `Y`, the total space `(Y × E)/Λ` is locally compact, as the
image of the locally compact space `Y × E` under the orbit map of the period translation action, an
open quotient map. No fullness, discreteness or injectivity of the periods is needed. -/
theorem locallyCompactSpace_torusFamily [LocallyCompactSpace Y]
    (hcont : ∀ l, Continuous fun y ↦ P y l) :
    letI := periodAddAction P
    LocallyCompactSpace (AddAction.orbitRel.Quotient Λ (Y × E)) := by
  let _ := periodAddAction P
  have := continuousConstVAdd_periodAddAction P hcont
  exact AddAction.isOpenQuotientMap_quotientMk.locallyCompactSpace

end LocallyCompact

end TauCeti
