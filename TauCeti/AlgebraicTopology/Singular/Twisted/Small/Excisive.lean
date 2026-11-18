/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.HomologicalComplex.Biprod
public import TauCeti.AlgebraicTopology.Singular.Homotopy.WeakHomotopyEquivalence
public import TauCeti.AlgebraicTopology.Singular.Twisted.Small.MayerVietoris
public import TauCeti.AlgebraicTopology.Singular.Twisted.Small.QuasiIso
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Excisive couples with local coefficients

Let `L` be a local coefficient system on a space `X`. Two subsets `A` and `B` of `X` form an
*excisive couple* for `L` when the twisted chains `C(A; L) + C(B; L)` of the simplices lying in
`A` or in `B`, the complex `smallTwistedChainComplex L (Bool.rec A B)`, include into the twisted
singular chains of `X` by a quasi-isomorphism. The small-chain theorem
(`TauCeti.LocalCoefficientSystem.quasiIso_smallTwistedChainComplexι`) says this when `A` and `B`
are open and cover `X`.

Subsets which are not open often have open neighbourhoods `U ⊇ A` and `V ⊇ B` covering `X` such
that `A ⊆ U`, `B ⊆ V` and `A ∩ B ⊆ U ∩ V` induce isomorphisms on twisted homology. Then `A` and
`B` are excisive for `L` as well
(`TauCeti.LocalCoefficientSystem.quasiIso_smallTwistedChainComplexι_of_nhds`): the Mayer–Vietoris
short exact sequences of supported twisted chains of the two couples form a map of short exact
sequences which is a quasi-isomorphism on the first two terms, hence on the third, and the
chains subordinate to `U` and `V` compute the homology of `X`.

The hypotheses are stated on the inclusions of supported chains `C(A; L) ⟶ C(U; L)`, which are
the twisted chains of the subspaces `A` and `U` with `L` restricted to them
(`TauCeti.LocalCoefficientSystem.subspaceTwistedChainComplexIso`). They hold whenever the
inclusions of subspaces are weak homotopy equivalences, since these induce isomorphisms on
homology with local coefficients. Subcomplexes of a CW complex are deformation retracts of such
neighbourhoods. When the fibres of `L` are projective, the inclusion of the chains of an excisive
couple is a chain homotopy equivalence, as needed to compute relative cochains and their products
on the chains of an excisive couple.

All results are in the namespace `TauCeti.LocalCoefficientSystem`.

## Main results

* `quasiIso_smallTwistedChainComplexι_of_nhds`: subsets whose supported twisted chains are
  quasi-isomorphic to those of open neighbourhoods covering `X`, also on the intersections, form
  an excisive couple.
* `quasiIso_smallTwistedChainComplexInclusion_of_isWeakHomotopyEquivalence`: a weak homotopy
  equivalence `A ⊆ U` gives a quasi-isomorphism of supported twisted chains.
* `quasiIso_smallTwistedChainComplexι_of_isWeakHomotopyEquivalence`: the excisive couple from weak
  homotopy equivalences.
* `homotopyEquivalences_smallTwistedChainComplexι_of_isWeakHomotopyEquivalence`: with projective
  fibres, its chains include by a chain homotopy equivalence.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.2, the
  Mayer–Vietoris sequence for deformation retracts of open neighbourhoods, and Section 3.H.
* E. H. Spanier, *Algebraic Topology*, McGraw-Hill, 1966, Chapter 4, Section 6, excisive couples.
-/

public section

noncomputable section

open CategoryTheory Limits

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] {X : TopCat.{v}}

section Nhds

variable (L : LocalCoefficientSystem.{u, v, max v w} R X) {A B U V : Set X}
  (hAU : A ⊆ U) (hBV : B ⊆ V)

/-- The inclusions of supported twisted chains as a morphism from the Mayer–Vietoris short
complex of `A` and `B` to that of `U` and `V`. -/
private def smallTwistedMayerVietorisInclusion :
    ShortComplex.mk _ _ (smallTwistedMayerVietorisToBiprod_fromBiprod L A B) ⟶
      ShortComplex.mk _ _ (smallTwistedMayerVietorisToBiprod_fromBiprod L U V) where
  τ₁ := smallTwistedChainComplexInclusion <| smallTwistedChains_mono L (fun _ : Unit ↦ A ∩ B)
    (fun _ : Unit ↦ U ∩ V) id fun _ ↦ Set.inter_subset_inter hAU hBV
  τ₂ := biprod.map
    (smallTwistedChainComplexInclusion <|
      smallTwistedChains_mono L (fun _ : Unit ↦ A) (fun _ : Unit ↦ U) id fun _ ↦ hAU)
    (smallTwistedChainComplexInclusion <|
      smallTwistedChains_mono L (fun _ : Unit ↦ B) (fun _ : Unit ↦ V) id fun _ ↦ hBV)
  τ₃ := smallTwistedChainComplexInclusion <| smallTwistedChains_mono L (Bool.rec A B)
    (Bool.rec U V) id fun b ↦ by cases b <;> assumption
  comm₁₂ := by
    apply biprod.hom_ext
    · apply (cancel_mono (smallTwistedChainComplexι L (fun _ : Unit ↦ U))).1
      simp
    · apply (cancel_mono (smallTwistedChainComplexι L (fun _ : Unit ↦ V))).1
      simp
  comm₂₃ := by
    apply (cancel_mono (smallTwistedChainComplexι L (Bool.rec U V))).1
    apply biprod.hom_ext' <;> simp

/-- **Subsets with homologically equivalent open neighbourhoods form an excisive couple for local
coefficients.** Let `A ⊆ U` and `B ⊆ V` be subsets of `X` with `U` and `V` open and covering `X`,
such that the inclusions of twisted chains supported in `A` into those supported in `U`, in `B`
into `V`, and in `A ∩ B` into `U ∩ V` are quasi-isomorphisms. Then the twisted chains of the
singular simplices lying in `A` or in `B` include into the twisted singular chains of `X` by a
quasi-isomorphism. -/
theorem quasiIso_smallTwistedChainComplexι_of_nhds (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ)
    (hA : QuasiIso (smallTwistedChainComplexInclusion <|
      smallTwistedChains_mono L (fun _ : Unit ↦ A) (fun _ : Unit ↦ U) id fun _ ↦ hAU))
    (hB : QuasiIso (smallTwistedChainComplexInclusion <|
      smallTwistedChains_mono L (fun _ : Unit ↦ B) (fun _ : Unit ↦ V) id fun _ ↦ hBV))
    (hAB : QuasiIso (smallTwistedChainComplexInclusion <|
      smallTwistedChains_mono L (fun _ : Unit ↦ A ∩ B) (fun _ : Unit ↦ U ∩ V) id
        fun _ ↦ Set.inter_subset_inter hAU hBV)) :
    QuasiIso (smallTwistedChainComplexι L (Bool.rec A B)) := by
  -- The map of Mayer–Vietoris short exact sequences is a quasi-isomorphism on the first two
  -- terms, hence on the third.
  let ψ := smallTwistedMayerVietorisInclusion L hAU hBV
  have h₂ : QuasiIso ψ.τ₂ := HomologicalComplex.quasiIso_biprod_map _ _
  have hS (U V : Set X) :
      (ShortComplex.mk _ _ (smallTwistedMayerVietorisToBiprod_fromBiprod L U V)).ShortExact := by
    rw [← smallTwistedMayerVietorisShortComplex_def]
    exact shortExact_smallTwistedMayerVietorisShortComplex L U V
  have h₃ : QuasiIso ψ.τ₃ :=
    HomologicalComplex.HomologySequence.quasiIso_τ₃ ψ (hS A B) (hS U V) hAB h₂
  -- Compose with the small-chain theorem for the open cover by `U` and `V`.
  have hUV' := quasiIso_smallTwistedChainComplexι_bool L hU hV hUV
  rw [← smallTwistedChainComplexInclusion_ι (smallTwistedChains_mono L (Bool.rec A B)
    (Bool.rec U V) id fun b ↦ by cases b <;> assumption)]
  exact quasiIso_comp (hφ := h₃) (hφ' := hUV') _ _

end Nhds

section WeakHomotopyEquivalence

variable (L : LocalCoefficientSystem.{u, v, v} R X)

/-- **A weak homotopy equivalence `A ⊆ B` induces a quasi-isomorphism of supported twisted
chains.** If the inclusion of subspaces `A ⊆ B` is a weak homotopy equivalence, then the
inclusion of the twisted chains of `X` supported in `A` into those supported in `B` is a
quasi-isomorphism. -/
theorem quasiIso_smallTwistedChainComplexInclusion_of_isWeakHomotopyEquivalence {A B : Set X}
    (h : A ⊆ B) (hw : (ContinuousMap.inclusion h).IsWeakHomotopyEquivalence) :
    QuasiIso (smallTwistedChainComplexInclusion <|
      smallTwistedChains_mono L (fun _ : Unit ↦ A) (fun _ : Unit ↦ B) id fun _ ↦ h) := by
  -- Through the identifications of supported chains with the twisted chains of the subspaces,
  -- the inclusion of supported chains is the map induced by the inclusion `A ⊆ B`.
  let i := TopCat.ofHom (ContinuousMap.inclusion h)
  let j := TopCat.ofHom (ContinuousMap.subtypeVal B)
  -- The composite `i ≫ j` is the inclusion of `A` into `X` by definition, so restricting `L` to
  -- `A` is restricting it to `B` and then to `A`.
  let e : (pullback (X := TopCat.of ↥A) (ContinuousMap.subtypeVal A)).obj L ≅
      (pullback i.hom).obj ((pullback (X := TopCat.of ↥B) (ContinuousMap.subtypeVal B)).obj L) :=
    (pullbackCompIso i.hom j.hom).app L
  have hsq : (subspaceTwistedChainComplexIso L A).hom ≫ smallTwistedChainComplexInclusion
      (smallTwistedChains_mono L (fun _ : Unit ↦ A) (fun _ : Unit ↦ B) id fun _ ↦ h) =
        twistedChainComplexCoefficientMap e.hom ≫
          twistedChainComplexMap i
            ((pullback (X := TopCat.of ↥B) (ContinuousMap.subtypeVal B)).obj L) ≫
            (subspaceTwistedChainComplexIso L B).hom := by
    apply (cancel_mono (smallTwistedChainComplexι L (fun _ : Unit ↦ B))).1
    simp only [Category.assoc, smallTwistedChainComplexInclusion_ι,
      subspaceTwistedChainComplexIso_hom_ι]
    exact twistedChainComplexMap_comp i j L
  have := hw.quasiIso_twistedChainComplexMap
    ((pullback (X := TopCat.of ↥B) (ContinuousMap.subtypeVal B)).obj L)
  rw [(Iso.eq_inv_comp (subspaceTwistedChainComplexIso L A)).2 hsq]
  infer_instance

variable {A B U V : Set X}

/-- **Subsets which are weakly equivalent to open neighbourhoods covering `X` form an excisive
couple for local coefficients.** Let `A ⊆ U` and `B ⊆ V` be subsets of `X` with `U` and `V` open
and covering `X`, such that the inclusions `A ⊆ U`, `B ⊆ V` and `A ∩ B ⊆ U ∩ V` are weak homotopy
equivalences. Then the twisted chains of the singular simplices lying in `A` or in `B` include into
the twisted singular chains of `X` by a quasi-isomorphism. -/
theorem quasiIso_smallTwistedChainComplexι_of_isWeakHomotopyEquivalence (hU : IsOpen U)
    (hV : IsOpen V) (hUV : U ∪ V = Set.univ) (hAU : A ⊆ U) (hBV : B ⊆ V)
    (hwA : (ContinuousMap.inclusion hAU).IsWeakHomotopyEquivalence)
    (hwB : (ContinuousMap.inclusion hBV).IsWeakHomotopyEquivalence)
    (hw : (ContinuousMap.inclusion (Set.inter_subset_inter hAU hBV)).IsWeakHomotopyEquivalence) :
    QuasiIso (smallTwistedChainComplexι L (Bool.rec A B)) :=
  quasiIso_smallTwistedChainComplexι_of_nhds L hAU hBV hU hV hUV
    (quasiIso_smallTwistedChainComplexInclusion_of_isWeakHomotopyEquivalence L hAU hwA)
    (quasiIso_smallTwistedChainComplexInclusion_of_isWeakHomotopyEquivalence L hBV hwB)
    (quasiIso_smallTwistedChainComplexInclusion_of_isWeakHomotopyEquivalence L _ hw)

/-- **The excisive couple with projective fibres.** Under the hypotheses of
`TauCeti.LocalCoefficientSystem.quasiIso_smallTwistedChainComplexι_of_isWeakHomotopyEquivalence`,
if every fibre of `L` is projective, then the twisted chains of the singular simplices lying in `A`
or in `B` include into the twisted singular chains of `X` by a chain homotopy equivalence. -/
theorem homotopyEquivalences_smallTwistedChainComplexι_of_isWeakHomotopyEquivalence
    [∀ x, Projective (L.obj x)] (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
    (hAU : A ⊆ U) (hBV : B ⊆ V)
    (hwA : (ContinuousMap.inclusion hAU).IsWeakHomotopyEquivalence)
    (hwB : (ContinuousMap.inclusion hBV).IsWeakHomotopyEquivalence)
    (hw : (ContinuousMap.inclusion (Set.inter_subset_inter hAU hBV)).IsWeakHomotopyEquivalence) :
    HomologicalComplex.homotopyEquivalences _ _ (smallTwistedChainComplexι L (Bool.rec A B)) :=
  have (n : ℕ) : Projective ((smallTwistedChainComplex L (Bool.rec A B)).X n) :=
    projective_smallTwistedChainComplex_X L _ n
  (ChainComplex.quasiIso_iff_of_projective _).1 <|
    quasiIso_smallTwistedChainComplexι_of_isWeakHomotopyEquivalence L hU hV hUV hAU hBV hwA hwB hw

end WeakHomotopyEquivalence

end TauCeti.LocalCoefficientSystem
