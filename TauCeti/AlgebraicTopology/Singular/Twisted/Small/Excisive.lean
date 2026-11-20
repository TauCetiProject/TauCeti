/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Small.MayerVietoris
public import TauCeti.AlgebraicTopology.Singular.Twisted.Small.QuasiIso
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import TauCeti.Algebra.Homology.HomologicalComplex.Biprod

/-!
# Excisive couples with local coefficients

Let `L` be a local coefficient system on a space `X`. Two subsets `A` and `B` of `X` form an
*excisive couple* for `L` when the twisted chains supported on the singular simplices lying in
`A` or in `B`, the complex `smallTwistedChainComplex L (Bool.rec A B)`, include into the twisted
singular chains of `X` by a quasi-isomorphism. The small-chain theorem says this when `A` and `B`
are open and cover `X` (`TauCeti.LocalCoefficientSystem.quasiIso_smallTwistedChainComplexι`).

Subsets which are not open often have open neighbourhoods `U ⊇ A` and `V ⊇ B` covering `X` such
that `A ⊆ U`, `B ⊆ V` and `A ∩ B ⊆ U ∩ V` induce isomorphisms on homology with local
coefficients, with `L` restricted to each subspace: subcomplexes of a CW complex, and their
preimages under a Serre fibration, are of this kind. Then `A` and `B` form an excisive couple
for `L` (`TauCeti.LocalCoefficientSystem.quasiIso_smallTwistedChainComplexι_of_nhds`). This is
the local-coefficient form of `TauCeti.quasiIso_chainComplexMap_smallSingularSubcomplex_ι_of_nhds`,
and the proof is the same: the short exact sequences of small twisted chains of the two couples
(`TauCeti.LocalCoefficientSystem.shortExact_smallTwistedMayerVietorisShortComplex`) form a map of
short exact sequences which is a quasi-isomorphism on the first two terms, hence on the third, and
the chains of the open couple include into all chains by the small-chain theorem.

The hypotheses are stated on the twisted chains of the subspaces. They are transported to chains
of `X` supported in the subspaces by the identification
`TauCeti.LocalCoefficientSystem.subspaceTwistedChainComplexIso`, under which the map induced by an
inclusion of subspaces is the inclusion of supports
(`LocalCoefficientSystem.subspaceTwistedChainComplexIso_hom_smallTwistedChainComplexInclusion`).

## Main results

* `TauCeti.LocalCoefficientSystem.quasiIso_smallTwistedChainComplexι_of_nhds`: subsets with open
  neighbourhoods covering `X` whose inclusions, and that of their intersections, are
  quasi-isomorphisms on twisted chains form an excisive couple for `L`.
* `TauCeti.LocalCoefficientSystem.quasiIso_smallTwistedChainComplexInclusion_iff`: the inclusion of
  chains supported in `S` into those supported in `T ⊇ S` is a quasi-isomorphism exactly when the
  inclusion `S ⊆ T` induces one on twisted chains.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.2, the
  Mayer–Vietoris sequence for deformation retracts of open neighbourhoods, and Section 3.H, local
  coefficients.
* E. H. Spanier, *Algebraic Topology*, McGraw-Hill, 1966, Chapter 4, Section 6, excisive couples.
-/

public section

open CategoryTheory Limits

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] {X : TopCat.{v}} (L : LocalCoefficientSystem.{u, v, max v w} R X)

/-- **The inclusion of supports is the map of the inclusion of subspaces.** For `S ⊆ T`, under
the identifications of the twisted chains of `S` and `T`, with `L` restricted, with the twisted
chains of `X` supported in `S` and in `T`, the map induced by the inclusion `S ⊆ T` is the
inclusion of the chains supported in `S` into those supported in `T`. -/
@[reassoc]
lemma subspaceTwistedChainComplexIso_hom_smallTwistedChainComplexInclusion {S T : Set X}
    (h : S ⊆ T) :
    (subspaceTwistedChainComplexIso L S).hom ≫ smallTwistedChainComplexInclusion
        (smallTwistedChains_mono L (fun _ : Unit ↦ S) (fun _ : Unit ↦ T) id fun _ ↦ h) =
      subsetTwistedChainComplexMap L h ≫ (subspaceTwistedChainComplexIso L T).hom := by
  apply (cancel_mono (smallTwistedChainComplexι L (fun _ : Unit ↦ T))).1
  simp

/-- The inclusion of the twisted chains of `X` supported in `S` into those supported in `T` is a
quasi-isomorphism exactly when the inclusion `S ⊆ T` induces a quasi-isomorphism on twisted chains,
with `L` restricted to `S` and `T`. -/
lemma quasiIso_smallTwistedChainComplexInclusion_iff {S T : Set X} (h : S ⊆ T) :
    QuasiIso (smallTwistedChainComplexInclusion
        (smallTwistedChains_mono L (fun _ : Unit ↦ S) (fun _ : Unit ↦ T) id fun _ ↦ h)) ↔
      QuasiIso (subsetTwistedChainComplexMap L h) := by
  rw [← quasiIso_iff_comp_left (subspaceTwistedChainComplexIso L S).hom,
    subspaceTwistedChainComplexIso_hom_smallTwistedChainComplexInclusion L h,
    quasiIso_iff_comp_right]

variable {L} {A B U V : Set X} (hAU : A ⊆ U) (hBV : B ⊆ V)

/-- The inclusions of the twisted chains supported in `A ∩ B`, in `A` and `B`, and in `A` or `B`
into those supported in `U ∩ V`, in `U` and `V`, and in `U` or `V`, as a map of the short exact
sequences of small twisted chains. -/
private noncomputable def smallTwistedMayerVietorisInclusion :
    ShortComplex.mk _ _ (smallTwistedMayerVietorisToBiprod_fromBiprod L A B) ⟶
      ShortComplex.mk _ _ (smallTwistedMayerVietorisToBiprod_fromBiprod L U V) where
  τ₁ := smallTwistedChainComplexInclusion (smallTwistedChains_mono L _ (fun _ : Unit ↦ U ∩ V) id
    fun _ ↦ Set.inter_subset_inter hAU hBV)
  τ₂ := biprod.map
    (smallTwistedChainComplexInclusion
      (smallTwistedChains_mono L _ (fun _ : Unit ↦ U) id fun _ ↦ hAU))
    (smallTwistedChainComplexInclusion
      (smallTwistedChains_mono L _ (fun _ : Unit ↦ V) id fun _ ↦ hBV))
  τ₃ := smallTwistedChainComplexInclusion (smallTwistedChains_mono L _ (Bool.rec U V) id
    (by rintro (_ | _) <;> assumption))
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
coefficients.** Let `A ⊆ U` and `B ⊆ V` be subsets of `X` with `U` and `V` open and covering
`X`, such that the inclusions `A ⊆ U`, `B ⊆ V` and `A ∩ B ⊆ U ∩ V` are quasi-isomorphisms on
twisted singular chains, with `L` restricted to each subspace. Then the twisted chains supported
on the singular simplices lying in `A` or in `B` include into the twisted singular chains of `X`
by a quasi-isomorphism. -/
theorem quasiIso_smallTwistedChainComplexι_of_nhds (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = Set.univ)
    [QuasiIso (subsetTwistedChainComplexMap L hAU)] [QuasiIso (subsetTwistedChainComplexMap L hBV)]
    [QuasiIso (subsetTwistedChainComplexMap L (Set.inter_subset_inter hAU hBV))] :
    QuasiIso (smallTwistedChainComplexι L (Bool.rec A B)) := by
  let ψ := smallTwistedMayerVietorisInclusion (L := L) hAU hBV
  -- The map of short exact sequences is a quasi-isomorphism on the first two terms, hence on the
  -- third.
  have h₁ : QuasiIso ψ.τ₁ := (quasiIso_smallTwistedChainComplexInclusion_iff L _).2 inferInstance
  have h₂ : QuasiIso ψ.τ₂ :=
    have := (quasiIso_smallTwistedChainComplexInclusion_iff L hAU).2 inferInstance
    have := (quasiIso_smallTwistedChainComplexInclusion_iff L hBV).2 inferInstance
    HomologicalComplex.quasiIso_biprod_map _ _
  have hS (A B : Set X) :
      (ShortComplex.mk _ _ (smallTwistedMayerVietorisToBiprod_fromBiprod L A B)).ShortExact := by
    rw [← smallTwistedMayerVietorisShortComplex_def]
    exact shortExact_smallTwistedMayerVietorisShortComplex L A B
  have h₃ : QuasiIso ψ.τ₃ :=
    HomologicalComplex.HomologySequence.quasiIso_τ₃ ψ (hS A B) (hS U V) h₁ h₂
  -- Compose with the small-chain theorem for the open cover by `U` and `V`.
  have hUV' := quasiIso_smallTwistedChainComplexι_bool L hU hV hUV
  rw [← smallTwistedChainComplexInclusion_ι (smallTwistedChains_mono L _ (Bool.rec U V) id
    (by rintro (_ | _) <;> assumption))]
  exact quasiIso_comp (hφ := h₃) (hφ' := hUV') _ _

end TauCeti.LocalCoefficientSystem
