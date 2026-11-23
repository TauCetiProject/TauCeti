/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Restriction.Basic
public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Discrete
import TauCeti.AlgebraicTopology.Singular.Twisted.TotallyDisconnected

/-!
# Degree-zero discrete check for Borel–Moore open restriction

On a discrete space `X` in degree zero, `borelMooreHomologyZeroIsoPi` identifies `H₀^BM(X; L)` with
the product `∏ x, L.obj x` of the fibres of the local coefficient system `L`. This file proves that
under `borelMooreHomologyZeroIsoPi`, open restriction `borelMooreHomologyRestrict j hj L 0` along
an open embedding `j : V ⟶ X` corresponds to precomposing families of point coefficients with `j`
(`TauCeti.LocalCoefficientSystem.borelMooreHomologyRestrict_zero_comp_isoPi`).

## References

* A. Borel and J. C. Moore, *Homology theory for locally compact spaces*, Michigan Math. J. 7
  (1960), 137–159.
* G. E. Bredon, *Sheaf Theory*, 2nd ed., Graduate Texts in Mathematics 170, Chapter V.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite SimplexCategory Topology ChainComplex
open scoped Simplicial

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R]

private lemma borelMooreHomologyZero_eq_of_isoPi {X : TopCat.{v}} [DiscreteTopology X]
    (L : LocalCoefficientSystem.{u, v, max v w} R X) (x : borelMooreHomology L 0) :
    x = (locallyFiniteChainComplex L).isoHomologyι₀.inv.hom
      (((locallyFiniteChainComplex L).pOpcycles 0).hom
        ((eqToHom (locallyFiniteChainComplex_X L 0).symm).hom
          ((locallyFiniteChainsZeroEquivPi L).symm
            ((borelMooreHomologyZeroIsoPi L).hom.hom x)))) := by
  have hinv := congrArg (fun f ↦ f.hom ((borelMooreHomologyZeroIsoPi L).hom.hom x))
    (borelMooreHomologyZeroIsoPi_inv L)
  have h1 : (borelMooreHomologyZeroIsoPi L).inv.hom
      ((borelMooreHomologyZeroIsoPi L).hom.hom x) = x := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, Iso.hom_inv_id, ModuleCat.hom_id,
      LinearMap.id_apply]
  rw [h1] at hinv
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, LinearEquiv.toModuleIso_inv,
    ModuleCat.hom_ofHom, LinearEquiv.coe_coe] using hinv

private lemma evalZeroRelativeCoeff_comp (P : TopPair.{v})
    (L : LocalCoefficientSystem.{u, v, max v w} R P.fst)
    {C' : ChainComplex (ModuleCat.{max v w} R) ℕ} (φ : C' ⟶ P.twistedChainComplex L)
    (hd0 : (P.twistedChainComplex L).d 1 0 = 0)
    (σ : (TopCat.toSSet.obj P.fst) _⦋0⦌)
    (hσ : ¬Set.range (TopCat.simplexMap σ) ⊆ Set.range P.map) (z : C'.X 0) :
    (((P.twistedChainComplex L).isoHomologyι₀.hom ≫
        ((P.twistedChainComplex L).pOpcyclesIso 1 0 (by simp) hd0).inv ≫
        P.twistedChainComplexCoeff L σ hσ).hom
      ((HomologicalComplex.homologyMap φ 0).hom
        (C'.isoHomologyι₀.inv.hom ((C'.pOpcycles 0).hom z)))) =
      (P.twistedChainComplexCoeff L σ hσ).hom ((φ.f 0).hom z) := by
  have h1 :=
    pOpcycles_comp_isoHomologyι₀_inv_comp_homologyMap_comp_isoHomologyι₀_hom_comp_pOpcyclesIso_inv
      φ hd0
  have h2 := congrArg (fun g ↦ g.hom z)
    (congrArg (· ≫ P.twistedChainComplexCoeff L σ hσ) h1)
  simpa only [Category.assoc, ModuleCat.hom_comp, LinearMap.comp_apply] using h2

private lemma ofSubsetMap_zero_comp_coeff {V X : TopCat.{v}}
    (j : V ⟶ X) (hj : Function.Injective j.hom) (L : LocalCoefficientSystem.{u, v, max v w} R X)
    {S : Set V} {v : V}
    (hρ : ¬Set.range (TopCat.simplexMap (TopCat.toSSetObj₀Equiv.symm (j.hom v))) ⊆
      Set.range (TopPair.ofSubset (j.hom '' S)ᶜ).map)
    (hρV : ¬Set.range (TopCat.simplexMap (TopCat.toSSetObj₀Equiv.symm v)) ⊆
      Set.range (TopPair.ofSubset Sᶜ).map) :
    (TopPair.twistedChainComplexMapOfFstEq (TopPair.ofSubsetMap j
        (Set.SurjOn.mapsTo_compl (Set.surjOn_image j.hom S) hj))
        (TopPair.ofSubsetMap_fst _ _) L).f 0 ≫
        (TopPair.ofSubset (j.hom '' S)ᶜ).twistedChainComplexCoeff L
          (TopCat.toSSetObj₀Equiv.symm (j.hom v)) hρ =
      (TopPair.ofSubset Sᶜ).twistedChainComplexCoeff ((pullback j.hom).obj L)
        (TopCat.toSSetObj₀Equiv.symm v) hρV := by
  let p := TopPair.ofSubsetMap j (Set.SurjOn.mapsTo_compl (Set.surjOn_image j.hom S) hj)
  have hρ' : ¬Set.range (TopCat.simplexMap ((TopCat.toSSet.map j).app (op ⦋0⦌)
      (TopCat.toSSetObj₀Equiv.symm v))) ⊆ Set.range (TopPair.ofSubset (j.hom '' S)ᶜ).map := by
    rwa [TauCeti.TopCat.toSSet_map_app_toSSetObj₀Equiv_symm]
  have hcoeff : (TopPair.ofSubset (j.hom '' S)ᶜ).twistedChainComplexCoeff L
        (TopCat.toSSetObj₀Equiv.symm (j.hom v)) hρ ≍
      (TopPair.ofSubset (j.hom '' S)ᶜ).twistedChainComplexCoeff L
        ((TopCat.toSSet.map j).app (op ⦋0⦌) (TopCat.toSSetObj₀Equiv.symm v)) hρ' := by
    revert hρ'
    rw [TauCeti.TopCat.toSSet_map_app_toSSetObj₀Equiv_symm j v]
    intro
    rfl
  rw [eq_of_heq hcoeff]
  exact @TopPair.twistedChainComplexMapOfFstEq_f_comp_twistedChainComplexCoeff _ _ _ _ p j
    (TopPair.ofSubsetMap_fst _ _) ((TopCat.mono_iff_injective j).2 hj) L _
    (TopCat.toSSetObj₀Equiv.symm v) hρV hρ'

/-- **Discrete check.** On a discrete space in degree zero, open restriction along an open
embedding `j : V ⟶ X` corresponds under `borelMooreHomologyZeroIsoPi` to precomposing families
of point coefficients with `j`. -/
theorem borelMooreHomologyRestrict_zero_comp_isoPi {V X : TopCat.{v}}
    [DiscreteTopology X] [DiscreteTopology V] [SigmaCompactSpace V]
    (j : V ⟶ X) (hj : IsOpenEmbedding j.hom)
    (L : LocalCoefficientSystem.{u, v, max v w} R X)
    (x : borelMooreHomology L 0) (v : V) :
    (borelMooreHomologyZeroIsoPi ((pullback j.hom).obj L)).hom.hom
        ((borelMooreHomologyRestrict j hj L 0).hom x) v =
      (borelMooreHomologyZeroIsoPi L).hom.hom x (j.hom v) := by
  -- Pick a stage `n` of `CompactExhaustion.choice V` containing `v`. Since `X` is discrete, the
  -- differential `d 1 0` of `C(X, X \ j '' K n; L)` vanishes, so evaluating the coefficient on the
  -- 0-simplex `j v` descends to degree-0 relative homology (`eval`). Applying `eval` to both sides
  -- of `borelMooreHomologyRestrict_comp_locallyFiniteChainComplexToRelative` recovers the
  -- `v`-coordinate of the restricted class on the left and the `(j v)`-coordinate of `x` on the
  -- right.
  let K := CompactExhaustion.choice V
  obtain ⟨n, hn⟩ := K.exists_mem v
  have hρ : ¬Set.range (TopCat.simplexMap (TopCat.toSSetObj₀Equiv.symm (j.hom v))) ⊆
      Set.range (TopPair.ofSubset (j.hom '' K n)ᶜ).map :=
    TopPair.not_range_simplexMap_subset_range_ofSubset_compl_map_iff.2
      ⟨j.hom v, ⟨toTopInitialVertex _, rfl⟩, ⟨v, hn, rfl⟩⟩
  have hρV : ¬Set.range (TopCat.simplexMap (TopCat.toSSetObj₀Equiv.symm v)) ⊆
      Set.range (TopPair.ofSubset (K n)ᶜ).map :=
    TopPair.not_range_simplexMap_subset_range_ofSubset_compl_map_iff.2
      ⟨v, ⟨toTopInitialVertex _, rfl⟩, hn⟩
  have : TotallyDisconnectedSpace (TopPair.ofSubset (j.hom '' K n)ᶜ).fst :=
    inferInstanceAs (TotallyDisconnectedSpace X)
  have hd0 := TopPair.twistedChainComplex_d_one_zero_eq_zero (TopPair.ofSubset (j.hom '' K n)ᶜ) L
  have hzigH := borelMooreHomologyRestrict_comp_locallyFiniteChainComplexToRelative j hj L 0 n
  let eval := ((TopPair.ofSubset (j.hom '' K n)ᶜ).twistedChainComplex L).isoHomologyι₀.hom ≫
    (((TopPair.ofSubset (j.hom '' K n)ᶜ).twistedChainComplex L).pOpcyclesIso 1 0
      (by simp) hd0).inv ≫
    (TopPair.ofSubset (j.hom '' K n)ᶜ).twistedChainComplexCoeff L
      (TopCat.toSSetObj₀Equiv.symm (j.hom v)) hρ
  have hLHS : eval.hom ((HomologicalComplex.homologyMap
        ((TopPair.ofSubset (K n)ᶜ).locallyFiniteChainComplexToRelative ((pullback j.hom).obj L)
            (K.isCompact n).compl_range_ofSubset_compl_map ≫
          TopPair.twistedChainComplexMapOfFstEq (TopPair.ofSubsetMap j
            (Set.SurjOn.mapsTo_compl (Set.surjOn_image j.hom (K n)) hj.injective))
            (TopPair.ofSubsetMap_fst _ _) L) 0).hom
      ((borelMooreHomologyRestrict j hj L 0).hom x)) =
      (borelMooreHomologyZeroIsoPi ((pullback j.hom).obj L)).hom.hom
        ((borelMooreHomologyRestrict j hj L 0).hom x) v := by
    conv_lhs => rw [borelMooreHomologyZero_eq_of_isoPi ((pullback j.hom).obj L)
      ((borelMooreHomologyRestrict j hj L 0).hom x)]
    have hc := (Category.assoc _ _ _).trans <| congrArg
      (((TopPair.ofSubset (K n)ᶜ).locallyFiniteChainComplexToRelative ((pullback j.hom).obj L)
          (K.isCompact n).compl_range_ofSubset_compl_map).f 0 ≫ ·)
      (ofSubsetMap_zero_comp_coeff j hj.injective L hρ hρV)
    let y0 : (((pullback j.hom).obj L).locallyFiniteChainComplex).X 0 :=
      (eqToHom (locallyFiniteChainComplex_X ((pullback j.hom).obj L) 0).symm).hom
        (((pullback j.hom).obj L).locallyFiniteChainsZeroEquivPi.symm
          ((borelMooreHomologyZeroIsoPi ((pullback j.hom).obj L)).hom.hom
            ((borelMooreHomologyRestrict j hj L 0).hom x)))
    exact (evalZeroRelativeCoeff_comp
        (TopPair.ofSubset (j.hom '' K n)ᶜ) L _ hd0 _ hρ y0).trans <|
      (congrArg (fun f ↦ f.hom y0) hc).trans <|
        (TopPair.twistedChainComplexCoeff_locallyFiniteChainComplexToRelative_f_apply
          (TopPair.ofSubset (K n)ᶜ) ((pullback j.hom).obj L)
          (K.isCompact n).compl_range_ofSubset_compl_map _ _ hρV).trans
          (locallyFiniteChainsZeroEquivPi_symm_apply ((pullback j.hom).obj L) _ v)
  have hRHS : eval.hom ((HomologicalComplex.homologyMap
        ((TopPair.ofSubset (j.hom '' K n)ᶜ).locallyFiniteChainComplexToRelative L
          ((K.isCompact n).image j.hom.continuous).compl_range_ofSubset_compl_map) 0).hom x) =
      (borelMooreHomologyZeroIsoPi L).hom.hom x (j.hom v) := by
    conv_lhs => rw [borelMooreHomologyZero_eq_of_isoPi L x]
    exact (evalZeroRelativeCoeff_comp (TopPair.ofSubset (j.hom '' K n)ᶜ) L _ hd0 _ hρ _).trans <|
      (TopPair.twistedChainComplexCoeff_locallyFiniteChainComplexToRelative_f_apply
        (TopPair.ofSubset (j.hom '' K n)ᶜ) L
        ((K.isCompact n).image j.hom.continuous).compl_range_ofSubset_compl_map _ _ hρ).trans
        (locallyFiniteChainsZeroEquivPi_symm_apply L _ (j.hom v))
  exact hLHS.symm.trans <| (congrArg (fun f ↦ eval.hom (f.hom x)) hzigH).trans hRHS

/-- **Check: restricting a countable discrete set to its even points deletes the odd
coordinates.** -/
example (L : LocalCoefficientSystem.{u, 0, w} R (TopCat.of ℕ))
    (x : borelMooreHomology L 0) (n : Set.ofPred Even) :
    (borelMooreHomologyZeroIsoPi
      ((pullback (TopCat.ofHom (ContinuousMap.subtypeVal (Set.ofPred Even))).hom).obj L)).hom.hom
        ((borelMooreHomologyRestrict
          (TopCat.ofHom (ContinuousMap.subtypeVal (Set.ofPred Even)))
          (isOpen_discrete _).isOpenEmbedding_subtypeVal L 0).hom x) n =
      (borelMooreHomologyZeroIsoPi L).hom.hom x n.val :=
  borelMooreHomologyRestrict_zero_comp_isoPi
    (TopCat.ofHom (ContinuousMap.subtypeVal (Set.ofPred Even)))
    (isOpen_discrete _).isOpenEmbedding_subtypeVal L x n

end TauCeti.LocalCoefficientSystem
