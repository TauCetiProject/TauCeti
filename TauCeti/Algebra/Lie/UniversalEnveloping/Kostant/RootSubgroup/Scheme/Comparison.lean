/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.Basic

/-!
# Independence of Kostant root maps from the Lie-algebra presentation

Two admissible actions on the same rational module and integral lattice give the same root
map whenever the selected root vectors act by the same endomorphism. The Lie algebras,
generator families and admissibility proofs may differ. This permits comparison of a Serre
presentation with an independently pinned Lie-algebra action without changing lattice
coordinates or checking only field-valued points.

This extends `kostantRootSubgroup_congr`, which keeps the Lie algebra and its representation
fixed, using the same divided-power coefficient formula of `kostantRootSubgroupComodule`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 2–3.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

variable {L L' : Type*} {V : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing L'] [LieAlgebra ℚ L']
  [AddCommGroup V] [Module ℚ V]
  {I I' J J' : Type*}
  (e : I → L) (h : J → L) (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
  (e' : I' → L') (h' : J' → L')
  (ρ' : _root_.UniversalEnvelopingAlgebra ℚ L' →ₐ[ℚ] Module.End ℚ V)
  (M : AddSubgroup V)
  (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
  (hM' : ∀ u ∈ kostantForm e' h', ∀ m ∈ M, ρ' u m ∈ M)
  (i : I) (i' : I')
  (hnil : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
  (hnil' : IsNilpotent (ρ' (_root_.UniversalEnvelopingAlgebra.ι ℚ (e' i'))))
  {n : ℕ} (b : Module.Basis (Fin n) ℤ M)

/-- Equal root-vector actions on the same lattice have equal coordinate Hopf-algebra maps,
even if their Lie-algebra presentations differ. -/
theorem kostantRootSubgroupCoordinateMap_eq_of_action_eq
    (haction : ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) =
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
    kostantRootSubgroupComodule_coact, haction]

/-- Equal root-vector actions give equal integral root-subgroup morphisms in the fixed
lattice basis, not merely equal maps on field-valued points. -/
theorem kostantRootSubgroup_eq_of_action_eq
    (haction : ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) =
      ρ' (_root_.UniversalEnvelopingAlgebra.ι ℚ (e' i'))) :
    kostantRootSubgroup e h ρ M hM i hnil b =
      kostantRootSubgroup e' h' ρ' M hM' i' hnil' b := by
  rw [kostantRootSubgroup_def, kostantRootSubgroup_def,
    kostantRootSubgroupCoordinateMap_eq_of_action_eq e h ρ e' h' ρ' M hM hM' i i'
      hnil hnil' b haction]

/-- Equal selected actions also give equal root-subgroup matrices over every commutative
coefficient ring. -/
theorem kostantRootSubgroupMatrix_eq_of_action_eq
    (haction : ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) =
      ρ' (_root_.UniversalEnvelopingAlgebra.ι ℚ (e' i')))
    {A : Type*} [CommRing A]
    (q : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    kostantRootSubgroupMatrix e h ρ M hM i hnil b q =
      kostantRootSubgroupMatrix e' h' ρ' M hM' i' hnil' b q := by
  rw [← pointsMulEquiv_kostantRootSubgroupCoordinateMap,
    ← pointsMulEquiv_kostantRootSubgroupCoordinateMap,
    kostantRootSubgroupCoordinateMap_eq_of_action_eq e h ρ e' h' ρ' M hM hM' i i'
      hnil hnil' b haction]

end TauCeti.UniversalEnvelopingAlgebra
