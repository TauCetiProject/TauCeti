/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Excisive
public import TauCeti.Topology.CWComplex.Classical.RadialNeighborhood
public import TauCeti.Topology.Homotopy.DeformationRetract
public import TauCeti.Topology.Homotopy.SerreFibration.WeakHomotopyEquivalence
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Basic

/-!
# Excisive couples of preimages under a Serre fibration

Let `p : E → B` be a Serre fibration and let `A₁ ⊆ U₁` and `A₂ ⊆ U₂` be subsets of `B`, with `U₁`
and `U₂` open and covering `B`, such that the inclusions `A₁ ⊆ U₁`, `A₂ ⊆ U₂` and
`A₁ ∩ A₂ ⊆ U₁ ∩ U₂` are weak homotopy equivalences. This is the situation of two subcomplexes of
a CW complex covering it, with neighbourhoods deformation retracting onto them and onto their
intersection. Then the preimages `p⁻¹(A₁)` and `p⁻¹(A₂)` form an excisive couple in `E`: the
chains `C(p⁻¹(A₁)) + C(p⁻¹(A₂))` of the singular simplices lying in one of the two preimages
include into the singular chains of `E` by a quasi-isomorphism, with coefficients in any module
(`TauCeti.TopCat.quasiIso_chainComplexMap_smallSingularSubcomplex_ι_preimage`), and by a chain
homotopy equivalence with coefficients in a projective module
(`TauCeti.TopCat.homotopyEquivalences_chainComplexMap_smallSingularSubcomplex_ι_preimage`).

The preimages are in general not open, so the small-chain theorem does not apply to them
directly. Restricting `p` over the subsets of the base keeps the fibres, so the inclusions
`p⁻¹(A₁) ⊆ p⁻¹(U₁)`, `p⁻¹(A₂) ⊆ p⁻¹(U₂)` and `p⁻¹(A₁ ∩ A₂) ⊆ p⁻¹(U₁ ∩ U₂)` are weak homotopy
equivalences (`TauCeti.TopCat.isWeakHomotopyEquivalence_inclusion_preimage`), hence
quasi-isomorphisms on singular chains, and the open preimages `p⁻¹(U₁)` and `p⁻¹(U₂)` cover `E`.
This is the hypothesis of `TauCeti.quasiIso_chainComplexMap_smallSingularSubcomplex_ι_of_nhds`.

For subcomplexes `A₁` and `A₂` of a relative CW complex `C ⊆ B`, the neighbourhoods are their open
radial neighbourhoods in `C` (`Topology.RelCWComplex.Subcomplex.radialNeighborhood`). These
deformation retract onto `A₁` and `A₂`, and the intersection of the two neighbourhoods is the
radial neighbourhood of `A₁ ⊓ A₂`, which deformation retracts onto `A₁ ∩ A₂`. When `A₁` and `A₂`
cover `C`, their radial neighbourhoods cover `C`. Applied to the restriction of `p` over `C`, this
makes `p⁻¹(A₁)` and `p⁻¹(A₂)` an excisive couple in `p⁻¹(C)`
(`TauCeti.TopCat.quasiIso_chainComplexMap_smallSingularSubcomplex_ι_preimage_subcomplex`). For
arbitrary subcomplexes, applied to the CW complex `A₁ ⊔ A₂`, it gives the quasi-isomorphism
`C(p⁻¹(A₁)) + C(p⁻¹(A₂)) → C(p⁻¹(A₁ ∪ A₂))`
(`TauCeti.TopCat.quasiIso_chainComplexMap_smallSingularSubcomplex_ι_preimage_sup`). No condition
is placed on the cells of `C`: there may be infinitely many, in every dimension.

Products of cochains are defined on small chains: a cochain vanishing on `p⁻¹(A₁)` cupped with a
cochain vanishing on `p⁻¹(A₂)` vanishes on `C(p⁻¹(A₁)) + C(p⁻¹(A₂))`. The chain homotopy
equivalence above lets such relative products be computed on the preimages of the subcomplexes of
a skeletal filtration, which is how the products of a Serre spectral sequence are constructed.

## Main results

* `TauCeti.TopCat.quasiIso_chainComplexMap_smallSingularSubcomplex_ι_preimage`: preimages of
  subsets with weakly equivalent open neighbourhoods form an excisive couple.
* `TauCeti.TopCat.homotopyEquivalences_chainComplexMap_smallSingularSubcomplex_ι_preimage`: with
  projective coefficients the small-chain inclusion is a chain homotopy equivalence.
* `TauCeti.TopCat.quasiIso_chainComplexMap_smallSingularSubcomplex_ι_preimage_subcomplex`: the
  preimages of two subcomplexes covering a CW complex form an excisive couple in the part of the
  total space over it. The `homotopyEquivalences_` form of the name is the chain homotopy
  equivalence with projective coefficients.
* `TauCeti.TopCat.quasiIso_chainComplexMap_smallSingularSubcomplex_ι_preimage_sup`: the preimages
  of any two subcomplexes form an excisive couple in the part of the total space over their union,
  with its `homotopyEquivalences_` form as well.

## References

* E. H. Spanier, *Algebraic Topology*, McGraw-Hill, 1966, Chapter 4, Section 6, excisive couples.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Chapter 5, the multiplicative structure of the Serre spectral sequence.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.2, and the
  Appendix, Proposition A.5, for neighbourhoods of subcomplexes.
-/

public section

open CategoryTheory

universe v u

namespace TauCeti.TopCat

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B}

/-- **Preimages under a Serre fibration of subsets with weakly equivalent neighbourhoods form an
excisive couple.** Let `p : E ⟶ B` be a Serre fibration, and let `A₁ ⊆ U₁` and `A₂ ⊆ U₂` be
subsets of `B` with `U₁` and `U₂` open and covering `B`, such that the inclusions `A₁ ⊆ U₁`,
`A₂ ⊆ U₂` and `A₁ ∩ A₂ ⊆ U₁ ∩ U₂` are weak homotopy equivalences. Then the chains of the singular
simplices of `E` lying in `p⁻¹(A₁)` or in `p⁻¹(A₂)` include into the singular chains of `E` by a
quasi-isomorphism, with coefficients in any module `R`. -/
theorem quasiIso_chainComplexMap_smallSingularSubcomplex_ι_preimage (hp : serreFibrations p)
    {A₁ A₂ U₁ U₂ : Set B} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hU : U₁ ∪ U₂ = Set.univ)
    (h₁ : A₁ ⊆ U₁) (h₂ : A₂ ⊆ U₂)
    (hw₁ : (ContinuousMap.inclusion h₁).IsWeakHomotopyEquivalence)
    (hw₂ : (ContinuousMap.inclusion h₂).IsWeakHomotopyEquivalence)
    (hw : (ContinuousMap.inclusion (Set.inter_subset_inter h₁ h₂)).IsWeakHomotopyEquivalence)
    {k : Type v} [Ring k] (R : ModuleCat.{u} k) :
    QuasiIso (SSet.chainComplexMap (E.smallSingularSubcomplex ![p ⁻¹' A₁, p ⁻¹' A₂]).ι R) :=
  quasiIso_chainComplexMap_smallSingularSubcomplex_ι_of_nhds R (hU₁.preimage p.hom.continuous)
    (hU₂.preimage p.hom.continuous) (by rw [← Set.preimage_union, hU, Set.preimage_univ])
    (Set.preimage_mono h₁) (Set.preimage_mono h₂)
    ((isWeakHomotopyEquivalence_inclusion_preimage hp h₁ hw₁).quasiIso_chainComplexMap R)
    ((isWeakHomotopyEquivalence_inclusion_preimage hp h₂ hw₂).quasiIso_chainComplexMap R)
    ((isWeakHomotopyEquivalence_inclusion_preimage hp _ hw).quasiIso_chainComplexMap R)

/-- **The excisive couple of preimages with projective coefficients.** Under the hypotheses of
`TauCeti.TopCat.quasiIso_chainComplexMap_smallSingularSubcomplex_ι_preimage`, with coefficients in
a projective module `R`, for instance the ring itself, the chains of the singular simplices of `E`
lying in `p⁻¹(A₁)` or in `p⁻¹(A₂)` include into the singular chains of `E` by a chain homotopy
equivalence. -/
theorem homotopyEquivalences_chainComplexMap_smallSingularSubcomplex_ι_preimage
    (hp : serreFibrations p) {A₁ A₂ U₁ U₂ : Set B} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂)
    (hU : U₁ ∪ U₂ = Set.univ) (h₁ : A₁ ⊆ U₁) (h₂ : A₂ ⊆ U₂)
    (hw₁ : (ContinuousMap.inclusion h₁).IsWeakHomotopyEquivalence)
    (hw₂ : (ContinuousMap.inclusion h₂).IsWeakHomotopyEquivalence)
    (hw : (ContinuousMap.inclusion (Set.inter_subset_inter h₁ h₂)).IsWeakHomotopyEquivalence)
    {k : Type v} [Ring k] (R : ModuleCat.{u} k) [Projective R] :
    HomologicalComplex.homotopyEquivalences _ _
      (SSet.chainComplexMap (E.smallSingularSubcomplex ![p ⁻¹' A₁, p ⁻¹' A₂]).ι R) :=
  have := quasiIso_chainComplexMap_smallSingularSubcomplex_ι_preimage hp hU₁ hU₂ hU h₁ h₂ hw₁ hw₂
    hw R
  (ChainComplex.quasiIso_iff_of_projective _).1 this

/-! ### Preimages of subcomplexes -/

section Subcomplex

open Topology Topology.RelCWComplex

variable [T2Space B] {C D : Set B} [RelCWComplex C D]

/-- Read inside the complex `C`, the inclusion of a set `S` with the same points as a subcomplex
`A` in a set `T` with the same points as its radial neighbourhood is a weak homotopy equivalence:
`A` is a deformation retract of its radial neighbourhood. -/
private theorem isWeakHomotopyEquivalence_inclusion_preimage_val_radialNeighborhood
    (A : Subcomplex C) {S T : Set B} (hS : (A : Set B) = S) (hT : A.radialNeighborhood = T)
    (hST : S ⊆ T) :
    (ContinuousMap.inclusion (Set.preimage_mono hST :
      (Subtype.val ⁻¹' S : Set C) ⊆ Subtype.val ⁻¹' T)).IsWeakHomotopyEquivalence := by
  subst hS hT
  let e := ContinuousMap.HomotopyEquiv.ofDeformationRetraction
    (ContinuousMap.inclusion A.subset_radialNeighborhood) A.radialNeighborhoodRetraction
    (Subcomplex.radialNeighborhoodRetraction_inclusion A)
    (ContinuousMap.HomotopicRel.homotopic ⟨A.radialNeighborhoodDeformation.symm⟩)
  have he : e.toFun = ContinuousMap.inclusion A.subset_radialNeighborhood :=
    ContinuousMap.HomotopyEquiv.ofDeformationRetraction_toFun ..
  rw [ContinuousMap.isWeakHomotopyEquivalence_inclusion_preimage_val_iff
    (A.radialNeighborhood_subset_complex)]
  exact he ▸ e.isWeakHomotopyEquivalence

/-- **Preimages of two subcomplexes covering a CW complex form an excisive couple.** Let
`p : E ⟶ B` be a Serre fibration, `C ⊆ B` a relative CW complex, and `A₁`, `A₂` subcomplexes
covering it, `A₁ ⊔ A₂ = ⊤`. In the part `p⁻¹(C)` of `E` over `C`, the chains of the singular
simplices lying in `p⁻¹(A₁)` or in `p⁻¹(A₂)` include into the singular chains of `p⁻¹(C)` by a
quasi-isomorphism, with coefficients in any module `R`. -/
theorem quasiIso_chainComplexMap_smallSingularSubcomplex_ι_preimage_subcomplex
    (hp : serreFibrations p) {A₁ A₂ : Subcomplex C} (hA : A₁ ⊔ A₂ = ⊤) {k : Type v} [Ring k]
    (R : ModuleCat.{u} k) :
    QuasiIso (SSet.chainComplexMap ((_root_.TopCat.of (p ⁻¹' C)).smallSingularSubcomplex
      ![Subtype.val ⁻¹' (p ⁻¹' A₁), Subtype.val ⁻¹' (p ⁻¹' A₂)]).ι R) := by
  have h₁ := Set.preimage_mono (f := (Subtype.val : C → B)) A₁.subset_radialNeighborhood
  have h₂ := Set.preimage_mono (f := (Subtype.val : C → B)) A₂.subset_radialNeighborhood
  -- Apply the excision criterion to the restriction `p⁻¹(C) → C` of `p`, with the radial
  -- neighbourhoods read in `C`. The preimage of `Subtype.val ⁻¹' Aᵢ` under this restriction is
  -- `Subtype.val ⁻¹' (p ⁻¹' Aᵢ)` by definition of `ContinuousMap.restrictPreimage`.
  exact quasiIso_chainComplexMap_smallSingularSubcomplex_ι_preimage
    (mem_serreFibrations_restrictPreimage hp C) A₁.isOpen_preimage_val_radialNeighborhood
    A₂.isOpen_preimage_val_radialNeighborhood
    (by rw [← Set.preimage_union, ← Subcomplex.radialNeighborhood_sup, hA,
      Subcomplex.radialNeighborhood_top, Subtype.coe_preimage_self]) h₁ h₂
    (isWeakHomotopyEquivalence_inclusion_preimage_val_radialNeighborhood A₁ rfl rfl
      A₁.subset_radialNeighborhood)
    (isWeakHomotopyEquivalence_inclusion_preimage_val_radialNeighborhood A₂ rfl rfl
      A₂.subset_radialNeighborhood)
    (isWeakHomotopyEquivalence_inclusion_preimage_val_radialNeighborhood (A₁ ⊓ A₂)
      (Subcomplex.coe_inf _ _) (Subcomplex.radialNeighborhood_inf _ _)
      (Set.inter_subset_inter A₁.subset_radialNeighborhood A₂.subset_radialNeighborhood)) R

/-- **The excisive couple of preimages of two subcomplexes covering a CW complex, with projective
coefficients.** Under the hypotheses of
`TauCeti.TopCat.quasiIso_chainComplexMap_smallSingularSubcomplex_ι_preimage_subcomplex`, with
coefficients in a projective module `R`, the chains of the singular simplices of `p⁻¹(C)` lying in
`p⁻¹(A₁)` or in `p⁻¹(A₂)` include into the singular chains of `p⁻¹(C)` by a chain homotopy
equivalence. -/
theorem homotopyEquivalences_chainComplexMap_smallSingularSubcomplex_ι_preimage_subcomplex
    (hp : serreFibrations p) {A₁ A₂ : Subcomplex C} (hA : A₁ ⊔ A₂ = ⊤) {k : Type v} [Ring k]
    (R : ModuleCat.{u} k) [Projective R] :
    HomologicalComplex.homotopyEquivalences _ _
      (SSet.chainComplexMap ((_root_.TopCat.of (p ⁻¹' C)).smallSingularSubcomplex
        ![Subtype.val ⁻¹' (p ⁻¹' A₁), Subtype.val ⁻¹' (p ⁻¹' A₂)]).ι R) :=
  have := quasiIso_chainComplexMap_smallSingularSubcomplex_ι_preimage_subcomplex hp hA R
  (ChainComplex.quasiIso_iff_of_projective _).1 this

/-- **Preimages of two subcomplexes form an excisive couple.** Let `p : E ⟶ B` be a Serre
fibration and `A₁`, `A₂` subcomplexes of a relative CW complex `C ⊆ B`. In the part
`p⁻¹(A₁ ∪ A₂)` of `E` over their union, the chains of the singular simplices lying in `p⁻¹(A₁)`
or in `p⁻¹(A₂)` include into the singular chains of `p⁻¹(A₁ ∪ A₂)` by a quasi-isomorphism,
`C(p⁻¹(A₁)) + C(p⁻¹(A₂)) → C(p⁻¹(A₁ ∪ A₂))`, with coefficients in any module `R`. This is the
case `C = A₁ ⊔ A₂` of
`TauCeti.TopCat.quasiIso_chainComplexMap_smallSingularSubcomplex_ι_preimage_subcomplex`. -/
theorem quasiIso_chainComplexMap_smallSingularSubcomplex_ι_preimage_sup
    (hp : serreFibrations p) (A₁ A₂ : Subcomplex C) {k : Type v} [Ring k] (R : ModuleCat.{u} k) :
    QuasiIso (SSet.chainComplexMap
      ((_root_.TopCat.of (p ⁻¹' (A₁ ⊔ A₂ : Subcomplex C))).smallSingularSubcomplex
        ![Subtype.val ⁻¹' (p ⁻¹' A₁), Subtype.val ⁻¹' (p ⁻¹' A₂)]).ι R) := by
  -- `A₁` and `A₂` are subcomplexes of the CW complex `A₁ ⊔ A₂`, which they cover.
  have h := quasiIso_chainComplexMap_smallSingularSubcomplex_ι_preimage_subcomplex
    (A₁ := Subcomplex.ofLE (le_sup_left : A₁ ≤ A₁ ⊔ A₂))
    (A₂ := Subcomplex.ofLE (le_sup_right : A₂ ≤ A₁ ⊔ A₂)) hp
    (SetLike.coe_injective (by simp [Subcomplex.coe_sup])) R
  rwa [Subcomplex.coe_ofLE, Subcomplex.coe_ofLE] at h

/-- **The excisive couple of preimages of two subcomplexes, with projective coefficients.** Under
the hypotheses of `TauCeti.TopCat.quasiIso_chainComplexMap_smallSingularSubcomplex_ι_preimage_sup`,
with coefficients in a projective module `R`, the chains of the singular simplices of
`p⁻¹(A₁ ∪ A₂)` lying in `p⁻¹(A₁)` or in `p⁻¹(A₂)` include into the singular chains of
`p⁻¹(A₁ ∪ A₂)` by a chain homotopy equivalence. -/
theorem homotopyEquivalences_chainComplexMap_smallSingularSubcomplex_ι_preimage_sup
    (hp : serreFibrations p) (A₁ A₂ : Subcomplex C) {k : Type v} [Ring k] (R : ModuleCat.{u} k)
    [Projective R] :
    HomologicalComplex.homotopyEquivalences _ _ (SSet.chainComplexMap
      ((_root_.TopCat.of (p ⁻¹' (A₁ ⊔ A₂ : Subcomplex C))).smallSingularSubcomplex
        ![Subtype.val ⁻¹' (p ⁻¹' A₁), Subtype.val ⁻¹' (p ⁻¹' A₂)]).ι R) :=
  have := quasiIso_chainComplexMap_smallSingularSubcomplex_ι_preimage_sup hp A₁ A₂ R
  (ChainComplex.quasiIso_iff_of_projective _).1 this

end Subcomplex

end TauCeti.TopCat
