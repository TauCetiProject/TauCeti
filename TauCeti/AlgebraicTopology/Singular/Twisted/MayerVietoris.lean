/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.Small.MayerVietoris
public import TauCeti.AlgebraicTopology.Singular.Twisted.Small.QuasiIso
public import TauCeti.Topology.Category.TopCat.Subspace
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# The Mayer–Vietoris sequence in singular homology with local coefficients

Let `U` and `V` be open subsets of a topological space `X` with `U ∪ V = X`, and let `L` be a local
coefficient system of `R`-modules on `X`, with arbitrary module fibres over an arbitrary ring.
This file constructs the Mayer–Vietoris long exact sequence of singular homology with
coefficients in `L`,
`⋯ ⟶ Hₙ(U ∩ V; L) ⟶ Hₙ(U; L) ⊞ Hₙ(V; L) ⟶ Hₙ(X; L) ⟶ Hₙ₋₁(U ∩ V; L) ⟶ ⋯`,
where `L` is restricted (pulled back) to `U ∩ V`, `U` and `V`. The first map is `(i_U, -i_V)` and
the second is `j_U + j_V`, the `i` and `j` being induced by the inclusions. The connecting
morphism is natural in morphisms of local systems and in maps of covered spaces.

The construction is the one of Hatcher, §2.2 and §3.H. The twisted chains of `U ∩ V`, of `U` and
`V`, and the chains subordinate to the cover form the short exact sequence
`TauCeti.LocalCoefficientSystem.shortExact_smallTwistedMayerVietorisShortComplex`. The twisted
chains of a subspace `A` with `L` restricted to `A` are identified with the twisted chains of `X`
supported in `A` (`TauCeti.LocalCoefficientSystem.subspaceTwistedChainComplexIso`), and the
small-chain theorem `TauCeti.LocalCoefficientSystem.quasiIso_smallTwistedChainComplexι` identifies
the homology of the chains subordinate to the cover with `Hₙ(X; L)`. The long exact homology
sequence of the short exact sequence then becomes the Mayer–Vietoris sequence.
The maps of the sequence on subspaces are induced by
`TauCeti.LocalCoefficientSystem.subsetTwistedChainComplexMap`, and its naturality in the space
uses `TauCeti.LocalCoefficientSystem.restrictTwistedChainComplexMap` and the action of maps on
small chains, `TauCeti.LocalCoefficientSystem.smallTwistedChainComplexMap`.

## Main definitions and results

* `TauCeti.LocalCoefficientSystem.twistedMayerVietorisToBiprod`,
  `TauCeti.LocalCoefficientSystem.twistedMayerVietorisFromBiprod`: the maps `(i_U, -i_V)` and
  `j_U + j_V`.
* `TauCeti.LocalCoefficientSystem.twistedMayerVietorisδ`: the connecting morphism
  `Hₙ(X; L) ⟶ Hₘ(U ∩ V; L)`, `m + 1 = n`.
* `TauCeti.LocalCoefficientSystem.twistedMayerVietoris_exact₁`, `twistedMayerVietoris_exact₂`,
  `twistedMayerVietoris_exact₃`: exactness at `Hₘ(U ∩ V; L)`, at `Hₙ(U; L) ⊞ Hₙ(V; L)` and at
  `Hₙ(X; L)`.
* `TauCeti.LocalCoefficientSystem.epi_twistedMayerVietorisFromBiprod_zero`: surjectivity at the
  degree-zero end.
* `TauCeti.LocalCoefficientSystem.isIso_twistedMayerVietorisToBiprod_of_isZero`: when
  `Hₙ₊₁(X; L)` and `Hₙ(X; L)` vanish, `Hₙ(U ∩ V; L) ≅ Hₙ(U; L) ⊞ Hₙ(V; L)`.
* `TauCeti.LocalCoefficientSystem.twistedMayerVietorisδ_coefficient_naturality`,
  `TauCeti.LocalCoefficientSystem.twistedMayerVietorisδ_naturality`: naturality of the connecting
  morphism in the coefficients and in the space.

The constant-coefficient sequence is `TopCat.mayerVietorisδ` and its exactness lemmas, in
`TauCeti.AlgebraicTopology.Singular.MayerVietoris.Basic`.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2 (the Mayer–Vietoris sequences, pp. 149–150) and
  Section 3.H (local coefficients, p. 333).
-/

public section

noncomputable section

open CategoryTheory Limits Topology

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] {X : TopCat.{v}}
  (L : LocalCoefficientSystem.{u, v, max v w} R X)

section MayerVietoris

variable (U V : Set X)

/-- The first map `Hₙ(U ∩ V; L) ⟶ Hₙ(U; L) ⊞ Hₙ(V; L)` of the Mayer–Vietoris sequence with local
coefficients, `(i_U, -i_V)`, where `i_U` and `i_V` are induced by the inclusions. -/
def twistedMayerVietorisToBiprod (n : ℕ) :
    ((pullback (X := TopCat.of ↥(U ∩ V)) (ContinuousMap.subtypeVal (U ∩ V))).obj
      L).twistedHomology n ⟶
      ((pullback (X := TopCat.of ↥U) (ContinuousMap.subtypeVal U)).obj L).twistedHomology n ⊞
        ((pullback (X := TopCat.of ↥V) (ContinuousMap.subtypeVal V)).obj L).twistedHomology n :=
  biprod.lift
    (HomologicalComplex.homologyMap (subsetTwistedChainComplexMap L Set.inter_subset_left) n)
    (-HomologicalComplex.homologyMap (subsetTwistedChainComplexMap L Set.inter_subset_right) n)

/-- The second map `Hₙ(U; L) ⊞ Hₙ(V; L) ⟶ Hₙ(X; L)` of the Mayer–Vietoris sequence with local
coefficients, `j_U + j_V`, where `j_U` and `j_V` are induced by the inclusions. -/
def twistedMayerVietorisFromBiprod (n : ℕ) :
    ((pullback (X := TopCat.of ↥U) (ContinuousMap.subtypeVal U)).obj L).twistedHomology n ⊞
        ((pullback (X := TopCat.of ↥V) (ContinuousMap.subtypeVal V)).obj L).twistedHomology n ⟶
      L.twistedHomology n :=
  biprod.desc (twistedHomologyMap (TopCat.ofHom (ContinuousMap.subtypeVal U)) L n)
    (twistedHomologyMap (TopCat.ofHom (ContinuousMap.subtypeVal V)) L n)

/-- The first component of the first map is induced by the inclusion `U ∩ V ⊆ U`. -/
@[reassoc (attr := simp)]
lemma twistedMayerVietorisToBiprod_fst (n : ℕ) :
    twistedMayerVietorisToBiprod L U V n ≫ biprod.fst =
      HomologicalComplex.homologyMap (subsetTwistedChainComplexMap L Set.inter_subset_left) n :=
  biprod.lift_fst _ _

/-- The second component of the first map is minus the map induced by `U ∩ V ⊆ V`. -/
@[reassoc (attr := simp)]
lemma twistedMayerVietorisToBiprod_snd (n : ℕ) :
    twistedMayerVietorisToBiprod L U V n ≫ biprod.snd =
      -HomologicalComplex.homologyMap (subsetTwistedChainComplexMap L Set.inter_subset_right) n :=
  biprod.lift_snd _ _

/-- On `Hₙ(U; L)` the second map is induced by the inclusion of `U`. -/
@[reassoc (attr := simp)]
lemma inl_twistedMayerVietorisFromBiprod (n : ℕ) :
    biprod.inl ≫ twistedMayerVietorisFromBiprod L U V n =
      twistedHomologyMap (TopCat.ofHom (ContinuousMap.subtypeVal U)) L n :=
  biprod.inl_desc _ _

/-- On `Hₙ(V; L)` the second map is induced by the inclusion of `V`. -/
@[reassoc (attr := simp)]
lemma inr_twistedMayerVietorisFromBiprod (n : ℕ) :
    biprod.inr ≫ twistedMayerVietorisFromBiprod L U V n =
      twistedHomologyMap (TopCat.ofHom (ContinuousMap.subtypeVal V)) L n :=
  biprod.inr_desc _ _

/-- The composite of the first two maps of the Mayer–Vietoris sequence vanishes. -/
@[reassoc (attr := simp)]
lemma twistedMayerVietorisToBiprod_fromBiprod (n : ℕ) :
    twistedMayerVietorisToBiprod L U V n ≫ twistedMayerVietorisFromBiprod L U V n = 0 := by
  simp [twistedMayerVietorisToBiprod, twistedMayerVietorisFromBiprod,
    ← HomologicalComplex.homologyMap_comp]

/-! ### The comparison with small chains -/

/-- The homology of the small-chain complex of the intersection is that of `U ∩ V`. -/
private def homologyIsoInter (n : ℕ) :
    (smallTwistedChainComplex L (fun _ : Unit ↦ U ∩ V)).homology n ≅
      ((pullback (X := TopCat.of ↥(U ∩ V)) (ContinuousMap.subtypeVal (U ∩ V))).obj
        L).twistedHomology n :=
  (HomologicalComplex.homologyFunctor _ _ n).mapIso
    (subspaceTwistedChainComplexIso L (U ∩ V)).symm

-- Homology is an additive functor, so it preserves binary biproducts.
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

/-- The homology of the sum of the small-chain complexes of `U` and `V`. -/
private def homologyIsoBiprod (n : ℕ) :
    (smallTwistedChainComplex L (fun _ : Unit ↦ U) ⊞
        smallTwistedChainComplex L (fun _ : Unit ↦ V)).homology n ≅
      ((pullback (X := TopCat.of ↥U) (ContinuousMap.subtypeVal U)).obj L).twistedHomology n ⊞
        ((pullback (X := TopCat.of ↥V) (ContinuousMap.subtypeVal V)).obj L).twistedHomology n :=
  (HomologicalComplex.homologyFunctor _ _ n).mapBiprod _ _ ≪≫
    biprod.mapIso ((HomologicalComplex.homologyFunctor _ _ n).mapIso
        (subspaceTwistedChainComplexIso L U).symm)
      ((HomologicalComplex.homologyFunctor _ _ n).mapIso (subspaceTwistedChainComplexIso L V).symm)

-- The objects of the homology functor are the stated objects of `homologyIsoBiprod` only up to
-- unfolding, so its components are computed in the functor's objects and then transferred.
private lemma homologyIsoBiprod_hom (n : ℕ) :
    (homologyIsoBiprod L U V n).hom = biprod.lift
      (HomologicalComplex.homologyMap (biprod.fst ≫ (subspaceTwistedChainComplexIso L U).inv) n)
      (HomologicalComplex.homologyMap (biprod.snd ≫ (subspaceTwistedChainComplexIso L V).inv)
        n) := by
  have h : ((HomologicalComplex.homologyFunctor _ _ n).mapBiprod (smallTwistedChainComplex L
        (fun _ : Unit ↦ U)) (smallTwistedChainComplex L (fun _ : Unit ↦ V))).hom ≫
      biprod.map ((HomologicalComplex.homologyFunctor _ _ n).map
          (subspaceTwistedChainComplexIso L U).inv)
        ((HomologicalComplex.homologyFunctor _ _ n).map (subspaceTwistedChainComplexIso L V).inv) =
      biprod.lift ((HomologicalComplex.homologyFunctor _ _ n).map
          (biprod.fst ≫ (subspaceTwistedChainComplexIso L U).inv))
        ((HomologicalComplex.homologyFunctor _ _ n).map
          (biprod.snd ≫ (subspaceTwistedChainComplexIso L V).inv)) := by
    apply biprod.hom_ext
    · rw [Category.assoc, biprod.map_fst, Functor.mapBiprod_hom, biprod.lift_fst_assoc,
        biprod.lift_fst, Functor.map_comp]
    · rw [Category.assoc, biprod.map_snd, Functor.mapBiprod_hom, biprod.lift_snd_assoc,
        biprod.lift_snd, Functor.map_comp]
  exact h

private lemma shortExact_mk_smallTwistedMayerVietoris :
    (ShortComplex.mk _ _ (smallTwistedMayerVietorisToBiprod_fromBiprod L U V)).ShortExact := by
  rw [← smallTwistedMayerVietorisShortComplex_def]
  exact shortExact_smallTwistedMayerVietorisShortComplex L U V

private lemma smallTwistedMayerVietorisToBiprod_fst_inv :
    smallTwistedMayerVietorisToBiprod L U V ≫ biprod.fst ≫
        (subspaceTwistedChainComplexIso L U).inv =
      (subspaceTwistedChainComplexIso L (U ∩ V)).inv ≫
        subsetTwistedChainComplexMap L Set.inter_subset_left := by
  rw [← cancel_epi (subspaceTwistedChainComplexIso L (U ∩ V)).hom,
    ← cancel_mono (subspaceTwistedChainComplexIso L U).hom]
  apply (cancel_mono (smallTwistedChainComplexι L (fun _ : Unit ↦ U))).1
  simp

private lemma smallTwistedMayerVietorisToBiprod_snd_inv :
    smallTwistedMayerVietorisToBiprod L U V ≫ biprod.snd ≫
        (subspaceTwistedChainComplexIso L V).inv =
      -((subspaceTwistedChainComplexIso L (U ∩ V)).inv ≫
        subsetTwistedChainComplexMap L Set.inter_subset_right) := by
  rw [← cancel_epi (subspaceTwistedChainComplexIso L (U ∩ V)).hom,
    ← cancel_mono (subspaceTwistedChainComplexIso L V).hom]
  apply (cancel_mono (smallTwistedChainComplexι L (fun _ : Unit ↦ V))).1
  simp

private lemma homologyMap_toBiprod_comp_homologyIsoBiprod_hom (n : ℕ) :
    HomologicalComplex.homologyMap (smallTwistedMayerVietorisToBiprod L U V) n ≫
        (homologyIsoBiprod L U V n).hom =
      (homologyIsoInter L U V n).hom ≫ twistedMayerVietorisToBiprod L U V n := by
  apply biprod.hom_ext
  · simp only [homologyIsoBiprod_hom, homologyIsoInter, Category.assoc, biprod.lift_fst,
      ← HomologicalComplex.homologyMap_comp, smallTwistedMayerVietorisToBiprod_fst_inv,
      twistedMayerVietorisToBiprod_fst, Functor.mapIso_hom, Iso.symm_hom,
      HomologicalComplex.homologyFunctor_map]
  · simp only [homologyIsoBiprod_hom, homologyIsoInter, Category.assoc, biprod.lift_snd,
      ← HomologicalComplex.homologyMap_comp, smallTwistedMayerVietorisToBiprod_snd_inv,
      twistedMayerVietorisToBiprod_snd, Functor.mapIso_hom, Iso.symm_hom,
      HomologicalComplex.homologyFunctor_map, HomologicalComplex.homologyMap_neg,
      Preadditive.comp_neg]

private lemma homologyMap_fromBiprod_comp_ι (n : ℕ) :
    HomologicalComplex.homologyMap (smallTwistedMayerVietorisFromBiprod L U V) n ≫
        HomologicalComplex.homologyMap (smallTwistedChainComplexι L (Bool.rec U V)) n =
      (homologyIsoBiprod L U V n).hom ≫ twistedMayerVietorisFromBiprod L U V n := by
  rw [homologyIsoBiprod_hom, twistedMayerVietorisFromBiprod, biprod.lift_desc]
  simp only [twistedHomologyMap, ← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_add, smallTwistedMayerVietorisFromBiprod_comp_ι,
    Category.assoc, subspaceTwistedChainComplexIso_inv_twistedChainComplexMap]

variable {U V} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)

include hU hV hUV in
private lemma quasiIso_smallTwistedChainComplexι_bool :
    QuasiIso (smallTwistedChainComplexι L (Bool.rec U V)) :=
  quasiIso_smallTwistedChainComplexι L _ (fun b ↦ by cases b <;> assumption) <|
    Set.eq_univ_of_forall fun x ↦ by
      rcases (hUV ▸ Set.mem_univ x : x ∈ U ∪ V) with h | h
      exacts [Set.mem_iUnion.2 ⟨false, h⟩, Set.mem_iUnion.2 ⟨true, h⟩]

/-- The homology of the chains subordinate to the cover `U, V` is that of `X`. -/
private def homologyIsoUnion (n : ℕ) :
    (smallTwistedChainComplex L (Bool.rec U V)).homology n ≅ L.twistedHomology n :=
  have := quasiIso_smallTwistedChainComplexι_bool L hU hV hUV
  asIso (HomologicalComplex.homologyMap (smallTwistedChainComplexι L (Bool.rec U V)) n)

/-- The **Mayer–Vietoris connecting morphism** `Hₙ(X; L) ⟶ Hₘ(U ∩ V; L)`, `m + 1 = n`, for an open
cover of `X` by `U` and `V`: the connecting morphism of the short exact sequence of twisted chains
supported in `U ∩ V`, in `U` and `V`, and subordinate to the cover, with `Hₙ(X; L)` and
`Hₘ(U ∩ V; L)` identified with the homology of its outer terms. -/
def twistedMayerVietorisδ (n m : ℕ) (h : m + 1 = n := by lia) :
    L.twistedHomology n ⟶
      ((pullback (X := TopCat.of ↥(U ∩ V)) (ContinuousMap.subtypeVal (U ∩ V))).obj
        L).twistedHomology m :=
  (homologyIsoUnion L hU hV hUV n).inv ≫
    (shortExact_mk_smallTwistedMayerVietoris L U V).δ n m h ≫ (homologyIsoInter L U V m).hom

/-- The connecting morphism followed by the first map vanishes. -/
@[reassoc (attr := simp)]
lemma twistedMayerVietorisδ_toBiprod (n m : ℕ) (h : m + 1 = n := by lia) :
    twistedMayerVietorisδ L hU hV hUV n m h ≫ twistedMayerVietorisToBiprod L U V m = 0 := by
  rw [twistedMayerVietorisδ, Category.assoc, Category.assoc,
    ← homologyMap_toBiprod_comp_homologyIsoBiprod_hom,
    (shortExact_mk_smallTwistedMayerVietoris L U V).δ_comp_assoc n m h, zero_comp, comp_zero]

/-- The second map followed by the connecting morphism vanishes. -/
@[reassoc (attr := simp)]
lemma twistedMayerVietorisFromBiprod_δ (n m : ℕ) (h : m + 1 = n := by lia) :
    twistedMayerVietorisFromBiprod L U V n ≫ twistedMayerVietorisδ L hU hV hUV n m h = 0 := by
  have := quasiIso_smallTwistedChainComplexι_bool L hU hV hUV
  rw [← cancel_epi (homologyIsoBiprod L U V n).hom, comp_zero, ← Category.assoc,
    ← homologyMap_fromBiprod_comp_ι, twistedMayerVietorisδ, homologyIsoUnion, asIso_inv,
    Category.assoc, IsIso.hom_inv_id_assoc,
    (shortExact_mk_smallTwistedMayerVietoris L U V).comp_δ_assoc n m h, zero_comp]

/-- **Exactness of the Mayer–Vietoris sequence with local coefficients at `Hₘ(U ∩ V; L)`.** -/
lemma twistedMayerVietoris_exact₁ (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (twistedMayerVietorisδ_toBiprod L hU hV hUV n m h)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    ((shortExact_mk_smallTwistedMayerVietoris L U V).homology_exact₁ n m h)
  refine ShortComplex.isoMk (homologyIsoUnion L hU hV hUV n) (homologyIsoInter L U V m)
    (homologyIsoBiprod L U V m) ?_ (homologyMap_toBiprod_comp_homologyIsoBiprod_hom L U V m).symm
  simp [twistedMayerVietorisδ]

include hU hV hUV in
/-- **Exactness of the Mayer–Vietoris sequence with local coefficients at
`Hₙ(U; L) ⊞ Hₙ(V; L)`.** -/
lemma twistedMayerVietoris_exact₂ (n : ℕ) :
    (ShortComplex.mk _ _ (twistedMayerVietorisToBiprod_fromBiprod L U V n)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    ((shortExact_mk_smallTwistedMayerVietoris L U V).homology_exact₂ n)
  exact ShortComplex.isoMk (homologyIsoInter L U V n) (homologyIsoBiprod L U V n)
    (homologyIsoUnion L hU hV hUV n) (homologyMap_toBiprod_comp_homologyIsoBiprod_hom L U V n).symm
    (homologyMap_fromBiprod_comp_ι L U V n).symm

/-- **Exactness of the Mayer–Vietoris sequence with local coefficients at `Hₙ(X; L)`.** -/
lemma twistedMayerVietoris_exact₃ (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (twistedMayerVietorisFromBiprod_δ L hU hV hUV n m h)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    ((shortExact_mk_smallTwistedMayerVietoris L U V).homology_exact₃ n m h)
  refine ShortComplex.isoMk (homologyIsoBiprod L U V n) (homologyIsoUnion L hU hV hUV n)
    (homologyIsoInter L U V m) (homologyMap_fromBiprod_comp_ι L U V n).symm ?_
  simp [twistedMayerVietorisδ]

include hU hV hUV in
/-- If `Hₙ₊₁(X; L)` and `Hₙ(X; L)` vanish, the first map `Hₙ(U ∩ V; L) ⟶ Hₙ(U; L) ⊞ Hₙ(V; L)` of
the Mayer–Vietoris sequence of an open cover is an isomorphism. -/
lemma isIso_twistedMayerVietorisToBiprod_of_isZero (n : ℕ)
    (h₁ : IsZero (L.twistedHomology (n + 1))) (h₀ : IsZero (L.twistedHomology n)) :
    IsIso (twistedMayerVietorisToBiprod L U V n) := by
  have := (twistedMayerVietoris_exact₁ L hU hV hUV (n + 1) n).mono_g (h₁.eq_of_src _ _)
  have := (twistedMayerVietoris_exact₂ L hU hV hUV n).epi_f (h₀.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

include hU hV hUV in
/-- The map `H₀(U; L) ⊞ H₀(V; L) ⟶ H₀(X; L)` at the end of the Mayer–Vietoris sequence is an
epimorphism. -/
lemma epi_twistedMayerVietorisFromBiprod_zero : Epi (twistedMayerVietorisFromBiprod L U V 0) := by
  have : Epi (smallTwistedMayerVietorisFromBiprod L U V) :=
    (shortExact_mk_smallTwistedMayerVietoris L U V).epi_g
  have : Epi (HomologicalComplex.homologyMap (smallTwistedMayerVietorisFromBiprod L U V) 0) :=
    HomologicalComplex.epi_homologyMap_of_epi_of_not_rel _ _ (by simp)
  have := quasiIso_smallTwistedChainComplexι_bool L hU hV hUV
  have h : twistedMayerVietorisFromBiprod L U V 0 = (homologyIsoBiprod L U V 0).inv ≫
      HomologicalComplex.homologyMap (smallTwistedMayerVietorisFromBiprod L U V) 0 ≫
        HomologicalComplex.homologyMap (smallTwistedChainComplexι L (Bool.rec U V)) 0 := by
    rw [Iso.eq_inv_comp, homologyMap_fromBiprod_comp_ι]
  rw [h]
  infer_instance

end MayerVietoris

section CoefficientNaturality

variable {L} {K : LocalCoefficientSystem.{u, v, max v w} R X} (η : L ⟶ K) (U V : Set X)

/-- Change of coefficients as a morphism of the short exact sequences of small chains. -/
private def smallTwistedMayerVietorisCoefficientMap :
    ShortComplex.mk _ _ (smallTwistedMayerVietorisToBiprod_fromBiprod L U V) ⟶
      ShortComplex.mk _ _ (smallTwistedMayerVietorisToBiprod_fromBiprod K U V) where
  τ₁ := smallTwistedChainComplexCoefficientMap (fun _ : Unit ↦ U ∩ V) η
  τ₂ := biprod.map (smallTwistedChainComplexCoefficientMap (fun _ : Unit ↦ U) η)
    (smallTwistedChainComplexCoefficientMap (fun _ : Unit ↦ V) η)
  τ₃ := smallTwistedChainComplexCoefficientMap (Bool.rec U V) η
  comm₁₂ := by
    apply biprod.hom_ext
    · apply (cancel_mono (smallTwistedChainComplexι K (fun _ : Unit ↦ U))).1
      simp
    · apply (cancel_mono (smallTwistedChainComplexι K (fun _ : Unit ↦ V))).1
      simp
  comm₂₃ := by
    apply (cancel_mono (smallTwistedChainComplexι K (Bool.rec U V))).1
    apply biprod.hom_ext' <;> simp

private lemma homologyIsoInter_hom_naturality (n : ℕ) :
    (homologyIsoInter L U V n).hom ≫ twistedHomologyCoefficientMap
        ((pullback (X := TopCat.of ↥(U ∩ V)) (ContinuousMap.subtypeVal (U ∩ V))).map η) n =
      HomologicalComplex.homologyMap
          (smallTwistedChainComplexCoefficientMap (fun _ : Unit ↦ U ∩ V) η) n ≫
        (homologyIsoInter K U V n).hom := by
  simp only [homologyIsoInter, Functor.mapIso_hom, Iso.symm_hom,
    HomologicalComplex.homologyFunctor_map, ← HomologicalComplex.homologyMap_comp]
  congr 1
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  apply (cancel_mono (smallTwistedChainComplexι K (fun _ : Unit ↦ U ∩ V))).1
  simp [twistedChainComplexMap_naturality]

variable {U V} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)

/-- **Naturality of the Mayer–Vietoris connecting morphism in the coefficients.** A morphism of
local coefficient systems `η : L ⟶ K` commutes with the connecting morphisms, acting on `U ∩ V`
through its restriction. -/
@[reassoc]
lemma twistedMayerVietorisδ_coefficient_naturality (n m : ℕ) (h : m + 1 = n := by lia) :
    twistedMayerVietorisδ L hU hV hUV n m h ≫ twistedHomologyCoefficientMap
        ((pullback (X := TopCat.of ↥(U ∩ V)) (ContinuousMap.subtypeVal (U ∩ V))).map η) m =
      twistedHomologyCoefficientMap η n ≫ twistedMayerVietorisδ K hU hV hUV n m h := by
  have := quasiIso_smallTwistedChainComplexι_bool L hU hV hUV
  have := quasiIso_smallTwistedChainComplexι_bool K hU hV hUV
  have hunion : HomologicalComplex.homologyMap (smallTwistedChainComplexι L (Bool.rec U V)) n ≫
      twistedHomologyCoefficientMap η n =
        HomologicalComplex.homologyMap (smallTwistedChainComplexCoefficientMap (Bool.rec U V) η)
            n ≫
          HomologicalComplex.homologyMap (smallTwistedChainComplexι K (Bool.rec U V)) n := by
    simp only [← HomologicalComplex.homologyMap_comp, smallTwistedChainComplexCoefficientMap_ι]
  have hinv : (homologyIsoUnion L hU hV hUV n).inv ≫
      HomologicalComplex.homologyMap (smallTwistedChainComplexCoefficientMap (Bool.rec U V) η)
          n =
        twistedHomologyCoefficientMap η n ≫ (homologyIsoUnion K hU hV hUV n).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact hunion.symm
  have key : (shortExact_mk_smallTwistedMayerVietoris L U V).δ n m h ≫
      HomologicalComplex.homologyMap
          (smallTwistedChainComplexCoefficientMap (fun _ : Unit ↦ U ∩ V) η) m =
        HomologicalComplex.homologyMap (smallTwistedChainComplexCoefficientMap (Bool.rec U V) η)
            n ≫
          (shortExact_mk_smallTwistedMayerVietoris K U V).δ n m h :=
    HomologicalComplex.HomologySequence.δ_naturality
      (smallTwistedMayerVietorisCoefficientMap η U V) _ _ n m h
  rw [twistedMayerVietorisδ, twistedMayerVietorisδ, Category.assoc, Category.assoc,
    homologyIsoInter_hom_naturality, reassoc_of% key, reassoc_of% hinv]

end CoefficientNaturality

section SpaceNaturality

variable {Y : TopCat.{v}} (f : X ⟶ Y) (M : LocalCoefficientSystem.{u, v, max v w} R Y)
  {U V : Set X} {U' V' : Set Y} (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V')

/-- Pushing chains forward along `f` as a morphism of the short exact sequences of small
chains. -/
private def smallTwistedMayerVietorisSpaceMap :
    ShortComplex.mk _ _
        (smallTwistedMayerVietorisToBiprod_fromBiprod ((pullback f.hom).obj M) U V) ⟶
      ShortComplex.mk _ _ (smallTwistedMayerVietorisToBiprod_fromBiprod M U' V') where
  τ₁ := smallTwistedChainComplexMap (fun _ : Unit ↦ U ∩ V) (fun _ : Unit ↦ U' ∩ V') f M id
    fun _ ↦ hfU.inter_inter hfV
  τ₂ := biprod.map
    (smallTwistedChainComplexMap (fun _ : Unit ↦ U) (fun _ : Unit ↦ U') f M id fun _ ↦ hfU)
    (smallTwistedChainComplexMap (fun _ : Unit ↦ V) (fun _ : Unit ↦ V') f M id fun _ ↦ hfV)
  τ₃ := smallTwistedChainComplexMap (Bool.rec U V) (Bool.rec U' V') f M id fun b ↦ by
    cases b <;> assumption
  comm₁₂ := by
    apply biprod.hom_ext
    · apply (cancel_mono (smallTwistedChainComplexι M (fun _ : Unit ↦ U'))).1
      simp
    · apply (cancel_mono (smallTwistedChainComplexι M (fun _ : Unit ↦ V'))).1
      simp
  comm₂₃ := by
    apply (cancel_mono (smallTwistedChainComplexι M (Bool.rec U' V'))).1
    apply biprod.hom_ext' <;> simp

private lemma homologyIsoInter_hom_space_naturality (n : ℕ) :
    (homologyIsoInter ((pullback f.hom).obj M) U V n).hom ≫
        HomologicalComplex.homologyMap
          (restrictTwistedChainComplexMap f M (hfU.inter_inter hfV)) n =
      HomologicalComplex.homologyMap (smallTwistedChainComplexMap (fun _ : Unit ↦ U ∩ V)
          (fun _ : Unit ↦ U' ∩ V') f M id fun _ ↦ hfU.inter_inter hfV) n ≫
        (homologyIsoInter M U' V' n).hom := by
  simp only [homologyIsoInter, Functor.mapIso_hom, Iso.symm_hom,
    HomologicalComplex.homologyFunctor_map, ← HomologicalComplex.homologyMap_comp]
  congr 1
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  apply (cancel_mono (smallTwistedChainComplexι M (fun _ : Unit ↦ U' ∩ V'))).1
  simp

variable (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)
  (hU' : IsOpen U') (hV' : IsOpen V') (hUV' : U' ∪ V' = Set.univ)

/-- **Naturality of the Mayer–Vietoris connecting morphism in the space.** A map `f : X ⟶ Y`
carrying `U` into `U'` and `V` into `V'` commutes with the connecting morphisms, where `X` carries
the coefficients `f⁎M` and `U ∩ V ⟶ U' ∩ V'` is the restriction of `f`. -/
@[reassoc]
lemma twistedMayerVietorisδ_naturality (n m : ℕ) (h : m + 1 = n := by lia) :
    twistedMayerVietorisδ ((pullback f.hom).obj M) hU hV hUV n m h ≫
        HomologicalComplex.homologyMap
          (restrictTwistedChainComplexMap f M (hfU.inter_inter hfV)) m =
      twistedHomologyMap f M n ≫ twistedMayerVietorisδ M hU' hV' hUV' n m h := by
  have := quasiIso_smallTwistedChainComplexι_bool ((pullback f.hom).obj M) hU hV hUV
  have := quasiIso_smallTwistedChainComplexι_bool M hU' hV' hUV'
  have hinv : (homologyIsoUnion ((pullback f.hom).obj M) hU hV hUV n).inv ≫
      HomologicalComplex.homologyMap (smallTwistedChainComplexMap (Bool.rec U V) (Bool.rec U' V')
        f M id fun b ↦ by cases b <;> assumption) n =
        twistedHomologyMap f M n ≫ (homologyIsoUnion M hU' hV' hUV' n).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    simp only [homologyIsoUnion, asIso_hom, ← HomologicalComplex.homologyMap_comp,
      smallTwistedChainComplexMap_ι]
  have key : (shortExact_mk_smallTwistedMayerVietoris ((pullback f.hom).obj M) U V).δ n m h ≫
      HomologicalComplex.homologyMap (smallTwistedChainComplexMap (fun _ : Unit ↦ U ∩ V)
          (fun _ : Unit ↦ U' ∩ V') f M id fun _ ↦ hfU.inter_inter hfV) m =
        HomologicalComplex.homologyMap (smallTwistedChainComplexMap (Bool.rec U V)
          (Bool.rec U' V') f M id fun b ↦ by cases b <;> assumption) n ≫
          (shortExact_mk_smallTwistedMayerVietoris M U' V').δ n m h :=
    HomologicalComplex.HomologySequence.δ_naturality
      (smallTwistedMayerVietorisSpaceMap f M hfU hfV) _ _ n m h
  rw [twistedMayerVietorisδ, twistedMayerVietorisδ, Category.assoc, Category.assoc,
    homologyIsoInter_hom_space_naturality f M hfU hfV, reassoc_of% key, reassoc_of% hinv]

end SpaceNaturality

end TauCeti.LocalCoefficientSystem
