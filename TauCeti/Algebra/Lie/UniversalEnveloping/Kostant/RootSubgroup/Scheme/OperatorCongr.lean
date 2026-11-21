/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Basic
import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Weight.LinearMap

/-!
# Changing the Lie-algebra presentation of a represented toral closure

The Kostant exponential on a fixed integral lattice depends only on the rational operator
acting on it. Consequently, two actions of possibly different Lie algebras whose root operators
match up to a bijection of root indices and whose weight-torus coordinate maps have the same
kernel (for instance, when one weight family is pushed forward from the other along an injective
map of character lattices) define the same integral closed subgroup of `GLₙ`. This permits
replacing a Serre presentation or reindexing simple nodes on a pinned Lie algebra without changing
the represented group scheme, including its nonreduced fibres.

The coordinate-map comparison `kostantRootSubgroupCoordinateMap_eq_of_operator_eq` compares
the polynomial coactions on the lattice. The common-kernel universal property then identifies
the toral defining ideals. No faithfulness, field-valued
point generation, or specialization equality is assumed.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 2 and 3.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

variable {L L' : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing L'] [LieAlgebra ℚ L']
  {I I' : Type*} {κ κ' : Type} {V : Type} [AddCommGroup V] [Module ℚ V]
  (e : I → L) (h : κ → L)
  (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
  (M : AddSubgroup V)
  (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)
  {n : ℕ} (b : Module.Basis (Fin n) ℤ M)
  (e' : I' → L') (h' : κ' → L')
  (ρ' : _root_.UniversalEnvelopingAlgebra ℚ L' →ₐ[ℚ] Module.End ℚ V)
  (hM' : ∀ u ∈ kostantForm e' h', ∀ m ∈ M, ρ' u m ∈ M)

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

/-- Two presentations on the same lattice whose root operators match along a bijection `σ : I ≃ I'`
and whose weight-torus coordinate maps have the same kernel define the same integral toral closure,
even if their Lie algebras, root index sets, or character lattices differ. -/
theorem kostantToralDefiningIdeal_eq_of_operator_equiv
    [Finite κ] [Finite κ'] (σ : I ≃ I')
    (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hnil' : ∀ i', IsNilpotent (ρ' (_root_.UniversalEnvelopingAlgebra.ι ℚ (e' i'))))
    (wt : Fin n → κ → ℤ) (wt' : Fin n → κ' → ℤ)
    (hop : ∀ i, ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) =
      ρ' (_root_.UniversalEnvelopingAlgebra.ι ℚ (e' (σ i))))
    (htorus :
      RingHom.ker
          (GeneralLinear.weightTorusCoordinateMap (R := ℤ) wt).hom.toAlgHom.toRingHom =
        RingHom.ker
          (GeneralLinear.weightTorusCoordinateMap (R := ℤ) wt').hom.toAlgHom.toRingHom) :
    kostantToralDefiningIdeal e h ρ M hM hnil b wt =
      kostantToralDefiningIdeal e' h' ρ' M hM' hnil' b wt' := by
  have hroot (i : I) := kostantRootSubgroupCoordinateMap_eq_of_operator_eq
    e h ρ M hM b e' h' ρ' hM' i (σ i) (hnil i) (hnil' (σ i)) (hop i)
  apply le_antisymm <;> rw [le_kostantToralDefiningIdeal_iff]
  · refine ⟨fun i' => ?_,
      htorus ▸ kostantToralDefiningIdeal_toIdeal_le_torus_ker e h ρ M hM hnil b wt⟩
    obtain ⟨i, rfl⟩ := σ.surjective i'
    simpa only [hroot i] using
      kostantToralDefiningIdeal_toIdeal_le_root_ker e h ρ M hM hnil b wt i
  · refine ⟨fun i => ?_,
      htorus.symm ▸ kostantToralDefiningIdeal_toIdeal_le_torus_ker e' h' ρ' M hM' hnil' b wt'⟩
    simpa only [← hroot i] using
      kostantToralDefiningIdeal_toIdeal_le_root_ker e' h' ρ' M hM' hnil' b wt' (σ i)

/-- Companion to `kostantToralDefiningIdeal_eq_of_operator_equiv` when the weight family `wt` is
pushed forward from `wt'` along an injective linear map of character lattices. -/
theorem kostantToralDefiningIdeal_eq_of_operator_equiv_linearMap
    [Finite κ] [Finite κ'] (σ : I ≃ I')
    (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
    (hnil' : ∀ i', IsNilpotent (ρ' (_root_.UniversalEnvelopingAlgebra.ι ℚ (e' i'))))
    (wt : Fin n → κ → ℤ) (wt' : Fin n → κ' → ℤ)
    (hop : ∀ i, ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)) =
      ρ' (_root_.UniversalEnvelopingAlgebra.ι ℚ (e' (σ i))))
    {f : (κ' → ℤ) →ₗ[ℤ] (κ → ℤ)} (hf : Function.Injective f)
    (hwt : wt = fun j => f (wt' j)) :
    kostantToralDefiningIdeal e h ρ M hM hnil b wt =
      kostantToralDefiningIdeal e' h' ρ' M hM' hnil' b wt' := by
  refine kostantToralDefiningIdeal_eq_of_operator_equiv e h ρ M hM b e' h' ρ' hM' σ hnil hnil'
    wt wt' hop ?_
  rw [hwt]
  exact GeneralLinear.ker_weightTorusCoordinateMap_linearMap hf wt'

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
      kostantToralDefiningIdeal e' h' ρ' M hM' hnil' b wt :=
  kostantToralDefiningIdeal_eq_of_operator_equiv e h ρ M hM b e' h' ρ' hM' (Equiv.refl I)
    hnil hnil' wt wt hop rfl

end TauCeti.UniversalEnvelopingAlgebra
