/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Excisive
public import TauCeti.Topology.Homotopy.SerreFibration.WeakHomotopyEquivalence

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

Products of cochains are defined on small chains: a cochain vanishing on `p⁻¹(A₁)` cupped with a
cochain vanishing on `p⁻¹(A₂)` vanishes on `C(p⁻¹(A₁)) + C(p⁻¹(A₂))`. The chain homotopy
equivalence above lets such relative products be computed on the preimages of the subcomplexes of
a skeletal filtration, which is how the products of a Serre spectral sequence are constructed.

## Main results

* `TauCeti.TopCat.quasiIso_chainComplexMap_smallSingularSubcomplex_ι_preimage`: preimages of
  subsets with weakly equivalent open neighbourhoods form an excisive couple.
* `TauCeti.TopCat.homotopyEquivalences_chainComplexMap_smallSingularSubcomplex_ι_preimage`: with
  projective coefficients the small-chain inclusion is a chain homotopy equivalence.

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

end TauCeti.TopCat
