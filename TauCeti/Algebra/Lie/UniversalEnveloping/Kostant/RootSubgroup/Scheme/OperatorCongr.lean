/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Basic

/-!
# Changing the Lie-algebra presentation of a represented toral closure

The Kostant exponential on a fixed integral lattice depends only on the rational operator
acting on it. Consequently, two actions of possibly different Lie algebras with the same
numbered root operators and weight torus define the same integral closed subgroup of `GLₙ`.
This permits replacing a Serre presentation by a pinned Lie algebra without changing the
represented group scheme, including its nonreduced fibres.

The coordinate-map argument extends the selected-root computation in
`kostantRootSubgroup_congr`: compare the polynomial coactions on the lattice, then use the
common-kernel universal property for the toral defining ideals. No faithfulness, field-valued
point generation, or specialization equality is assumed.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 2 and 3.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

variable {L L' : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing L'] [LieAlgebra ℚ L']
  {I I' κ' : Type*} {κ : Type} {V : Type} [AddCommGroup V] [Module ℚ V]
  (e : I → L) (h : κ → L)
  (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
  (M : AddSubgroup V)
  (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
  {n : ℕ} (b : Module.Basis (Fin n) ℤ M)
  (e' : I' → L') (h' : κ' → L')
  (ρ' : _root_.UniversalEnvelopingAlgebra ℚ L' →ₐ[ℚ] Module.End ℚ V)
  (hM' : ∀ u ∈ kostantForm e' h', ∀ m ∈ M, ρ' u m ∈ M)

/-- The represented root coordinate map depends only on its rational operator and integral
lattice, not on the Lie algebra or generator presentation producing that operator. -/
theorem kostantRootSubgroupCoordinateMap_eq_of_operator_eq
    (i : I) (i' : I')
    (hnil : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hnil' : IsNilpotent (ρ' (_root_.UniversalEnvelopingAlgebra.ι ℚ (e' i'))))
    (hop : ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) =
      ρ' (_root_.UniversalEnvelopingAlgebra.ι ℚ (e' i'))) :
    kostantRootSubgroupCoordinateMap e h ρ M hM i hnil b =
      kostantRootSubgroupCoordinateMap e' h' ρ' M hM' i' hnil' b := by
  apply CommHopfAlgCat.hom_ext
  apply BialgHom.coe_toAlgHom_injective
  apply GeneralLinear.coordinateHopfAlgebra_algHom_ext ℤ n
  intro r s
  simp only [BialgHom.coe_toAlgHom]
  rw [kostantRootSubgroupCoordinateMap_X, kostantRootSubgroupCoordinateMap_X]
  simp only [Comodule.coefficientMatrix_apply, Comodule.matrixCoefficient_def,
    kostantRootSubgroupComodule_coact, hop]

/-- Equality of rational root operators gives the same exponential matrix over every
commutative value ring, not just over the rational field. -/
theorem kostantRootSubgroupMatrix_eq_of_operator_eq
    (i : I) (i' : I')
    (hnil : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hnil' : IsNilpotent (ρ' (_root_.UniversalEnvelopingAlgebra.ι ℚ (e' i'))))
    (hop : ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) =
      ρ' (_root_.UniversalEnvelopingAlgebra.ι ℚ (e' i')))
    {A : Type*} [CommRing A]
    (q : WithConv (AdditiveGroup.coordinateHopfAlgebra ℤ →ₐ[ℤ] A)) :
    kostantRootSubgroupMatrix e h ρ M hM i hnil b q =
      kostantRootSubgroupMatrix e' h' ρ' M hM' i' hnil' b q := by
  rw [← pointsMulEquiv_kostantRootSubgroupCoordinateMap,
    kostantRootSubgroupCoordinateMap_eq_of_operator_eq e h ρ M hM b e' h' ρ' hM'
      i i' hnil hnil' hop,
    pointsMulEquiv_kostantRootSubgroupCoordinateMap]

/-- Two presentations with the same numbered root operators on the same lattice and the same
weight torus define the same integral toral closure, even if their Lie algebras differ. -/
theorem kostantToralDefiningIdeal_eq_of_operator_eq
    [Finite κ] (e' : I → L') (h' : κ → L')
    (hM' : ∀ u ∈ kostantForm e' h', ∀ m ∈ M, ρ' u m ∈ M)
    (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hnil' : ∀ i, IsNilpotent (ρ' (_root_.UniversalEnvelopingAlgebra.ι ℚ (e' i))))
    (wt : Fin n → κ → ℤ)
    (hop : ∀ i, ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) =
      ρ' (_root_.UniversalEnvelopingAlgebra.ι ℚ (e' i))) :
    kostantToralDefiningIdeal e h ρ M hM hnil b wt =
      kostantToralDefiningIdeal e' h' ρ' M hM' hnil' b wt := by
  have hroot (i : I) := kostantRootSubgroupCoordinateMap_eq_of_operator_eq
    e h ρ M hM b e' h' ρ' hM' i i (hnil i) (hnil' i) (hop i)
  apply le_antisymm
  · rw [le_kostantToralDefiningIdeal_iff]
    simpa only [← hroot] using
      (le_kostantToralDefiningIdeal_iff e h ρ M hM hnil b wt _).mp le_rfl
  · rw [le_kostantToralDefiningIdeal_iff]
    simpa only [hroot] using
      (le_kostantToralDefiningIdeal_iff e' h' ρ' M hM' hnil' b wt _).mp le_rfl

end TauCeti.UniversalEnvelopingAlgebra
