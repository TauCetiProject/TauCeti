/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import TauCeti.Topology.Sheaves.Cech.Colimit
import Mathlib.Algebra.Category.Grp.AB
import TauCeti.Algebra.Homology.Ext.Basic
import TauCeti.Algebra.Homology.ShortComplex.ShortExact
import TauCeti.CategoryTheory.Sites.SheafCohomology.Cech.LongExactSequence
import TauCeti.CategoryTheory.Sites.SheafCohomology.LongExactSequence
import TauCeti.Topology.Sheaves.Cech.LocallyZero
import TauCeti.Topology.Sheaves.Exact
import TauCeti.Topology.Sheaves.Flasque.Basic
import TauCeti.Topology.Sheaves.InjectiveImage

/-!
# Vanishing of degree one Čech cohomology implies vanishing of sheaf cohomology

Let `F` be a sheaf of abelian groups on a topological space `X` and `W` an open subset of `X`. If
the Čech cohomology `ČH¹(W, F)` vanishes, in the cover-colimit sense of
`TauCeti.Topology.cechCohomology` and for the restriction `V ↦ F(V)` of `F` to the subspace `W`,
then so does the sheaf cohomology `H¹(W, F)`
(`TauCeti.Topology.subsingleton_H'_one_of_isZero_cechCohomology`).

This is the form in which Čech computations feed the comparison of the Čech cohomology of a cover
with sheaf cohomology: the degree one Leray theorem asks for `H¹(U i, F) = 0` on the members `U i`
of a cover, while acyclicity results for concrete sheaves, such as Forster's vanishing of `H¹` of
the holomorphic structure sheaf on discs, are proved by Čech methods.

Embed `F` into the chosen injective sheaf `I`, with cokernel sheaf `Q`. Since `I` has no `H¹`, it
suffices that every section `s` of `Q` over `W` lifts to `I` (`Sheaf.H'.subsingleton_X₁_one`). Let
`G ⊆ Q` be the image presheaf of `I ⟶ Q` and `C = Q / G` the cokernel presheaf. The sequences of
presheaves `0 ⟶ F ⟶ I ⟶ G ⟶ 0` and `0 ⟶ G ⟶ Q ⟶ C ⟶ 0` are exact on sections over every open, so
their restrictions to `W` give long exact sequences of cover-colimit Čech cohomology
(`TauCeti.CategoryTheory.cechCohomology_exact₂`, `cechCohomology_exact₃`).

* From `ČH⁰(W, I) ⟶ ČH⁰(W, G) ⟶ ČH¹(W, F) = 0`, the first map is onto.
* Every section of `Q` lifts to `I` near each point, so every section of `C` is locally zero, and
  `ČH⁰(W, C) = 0` (`TauCeti.Topology.isZero_cechCohomology_zero_obj_of_locally_eq_zero`). From
  `ČH⁰(W, G) ⟶ ČH⁰(W, Q) ⟶ ČH⁰(W, C) = 0`, the first map is onto.

So `ČH⁰(W, I) ⟶ ČH⁰(W, Q)` is onto. As `I` and `Q` are sheaves, this map is `I(W) ⟶ Q(W)`
(`TauCeti.Topology.cechCohomologyZeroIso_hom_naturality`).

## Main results

* `TauCeti.Topology.subsingleton_H'_one_of_isZero_cechCohomology`: if the restriction of `F` to an
  open `W` has vanishing degree one Čech cohomology, then `H¹(W, F) = 0`.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §12, where `H¹` of a sheaf on a Riemann surface is defined as the Čech cohomology.
* R. Hartshorne, *Algebraic Geometry*, Exercise III.4.4, where the degree one Čech cohomology of
  an arbitrary space is compared with sheaf cohomology by the same lifting argument.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace TauCeti.Topology

variable {X : TopCat.{u}} (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

/-- The sequence of presheaves `0 ⟶ G ⟶ Q ⟶ C ⟶ 0`, where `G` is the image presheaf of the map
`I ⟶ Q` from the chosen injective sheaf containing `F` to its cokernel `Q`, and `C` is the
cokernel presheaf of `G ⟶ Q`. -/
private abbrev imageCokernelSequence : ShortComplex ((Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  ShortComplex.cokernelSequence (image.ι (cokernel.π (Injective.ι F)).hom)

/-- The sequence `0 ⟶ G ⟶ Q ⟶ C ⟶ 0` is exact on every open. -/
private lemma imageCokernelSequence_map_shortExact (V : (Opens X)ᵒᵖ) :
    ((imageCokernelSequence F).map ((evaluation _ AddCommGrpCat.{u}).obj V)).ShortExact :=
  (TauCeti.cokernelSequence_shortExact (image.ι (cokernel.π (Injective.ι F)).hom)).map_of_exact _

/-- Every section of the cokernel presheaf `C = Q / G` is locally zero, because sections of `Q`
lift locally to the injective sheaf `I`. -/
private lemma imageCokernelSequence_locally_eq_zero (W : Opens X)
    (s : (imageCokernelSequence F).X₃.obj (op W)) (x : X) (hx : x ∈ W) :
    ∃ (V : Opens X) (hVW : V ≤ W), x ∈ V ∧
      (imageCokernelSequence F).X₃.map (homOfLE hVW).op s = 0 := by
  have : Epi ((imageCokernelSequence F).g.app (op W)) := inferInstance
  obtain ⟨q, rfl⟩ := (AddCommGrpCat.epi_iff_surjective _).1 this s
  obtain ⟨V, -, hxV, hVW, t, ht⟩ := TopCat.Sheaf.exists_mem_lift_of_epi (B := Set.univ)
    (fun _ _ V _ x hx ↦ ⟨V, trivial, hx, le_rfl⟩) (cokernel.π (Injective.ι F)) (Set.mem_univ W)
    q x hx
  refine ⟨V, hVW, hxV, ?_⟩
  -- the image of the lift `t` in `Q` lies in `G`, so it vanishes in `C`
  have hzero : (cokernel.π (image.ι (cokernel.π (Injective.ι F)).hom)).app (op V)
      ((cokernel.π (Injective.ι F)).hom.app (op V) t) = 0 := by
    have hfac : (cokernel.π (Injective.ι F)).hom.app (op V) t =
        (image.ι (cokernel.π (Injective.ι F)).hom).app (op V)
          ((factorThruImage (cokernel.π (Injective.ι F)).hom).app (op V) t) :=
      (ConcreteCategory.congr_hom
        (NatTrans.congr_app (image.fac (cokernel.π (Injective.ι F)).hom) (op V)) t).symm
    rw [hfac]
    refine (ConcreteCategory.congr_hom (NatTrans.congr_app
      (cokernel.condition (image.ι (cokernel.π (Injective.ι F)).hom)) (op V)) _).trans ?_
    simp
  rw [← NatTrans.naturality_apply]
  -- `ht` is stated for the presheaf of the sheaf `Q` and `hzero` for the cokernel map `Q ⟶ C`,
  -- which are the middle term and the second map of the sequence only up to unfolding
  -- `imageCokernelSequence`, so they are combined as terms
  exact (congrArg (fun y ↦ (imageCokernelSequence F).g.app (op V) y) ht).symm.trans hzero

variable {F} in
/-- The restriction of the cokernel presheaf `C = Q / G` to an open subspace `W` is locally zero. -/
private lemma restrict_imageCokernelSequence_locally_eq_zero (W : Opens X)
    (W' : Opens ((Opens.toTopCat X).obj W))
    (s : (imageCokernelSequence F).X₃.obj (op (W.isOpenEmbedding.isOpenMap.functor.obj W')))
    (x : (Opens.toTopCat X).obj W) (hx : x ∈ W') :
    ∃ (V : Opens ((Opens.toTopCat X).obj W)) (hVW : V ≤ W'), x ∈ V ∧
      (W.isOpenEmbedding.isOpenMap.functor.op ⋙ (imageCokernelSequence F).X₃).map
        (homOfLE hVW).op s = 0 := by
  obtain ⟨V, hVW, hxV, hV⟩ := imageCokernelSequence_locally_eq_zero F _ s x.1 ⟨x, hx, rfl⟩
  -- the preimage of `V` in `W` lies in `W'`
  have hle : (Opens.map W.inclusion').obj V ≤ W' := fun y hy ↦ by
    obtain ⟨z, hz, hzy⟩ := hVW hy
    exact Subtype.ext hzy ▸ hz
  refine ⟨_, hle, hxV, ?_⟩
  have : W.isOpenEmbedding.isOpenMap.functor.map (homOfLE hle) =
      W.isOpenEmbedding.isOpenMap.adjunction.counit.app V ≫ homOfLE hVW :=
    Subsingleton.elim _ _
  rw [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op, this, op_comp, Functor.map_comp,
    ConcreteCategory.comp_apply, hV, map_zero]

/-- If the restriction of `F` to an open `W` has vanishing degree one Čech cohomology, then every
section over `W` of the cokernel `Q` of the chosen embedding of `F` into an injective sheaf lifts to
that injective sheaf. The open `W` appears as the image of the top open of the subspace `W`. -/
private lemma surjective_app_functor_obj_top (W : Opens X)
    (h : IsZero ((cechCohomology ((Opens.toTopCat X).obj W) AddCommGrpCat.{u} 1).obj
      (W.isOpenEmbedding.isOpenMap.functor.op ⋙ F.obj))) :
    Function.Surjective ((cokernel.π (Injective.ι F)).hom.app
      (op (W.isOpenEmbedding.isOpenMap.functor.obj ⊤))) := by
  let Y := (Opens.toTopCat X).obj W
  let Φ := W.isOpenEmbedding.isOpenMap.functor
  -- restriction of presheaves on `X` to the subspace `W`
  let R := (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj Φ.op
  have hS₁ (U : PointOpenCover Y) :
      (((injectiveImageSequence F).map R).map
        (cechComplexFunctor U.toFormalCoproduct.obj)).ShortExact :=
    TauCeti.CategoryTheory.shortExact_map_cechComplexFunctor _ _ fun _ _ ↦
      injectiveImageSequence_map_shortExact F _
  have hS₂ (U : PointOpenCover Y) :
      (((imageCokernelSequence F).map R).map
        (cechComplexFunctor U.toFormalCoproduct.obj)).ShortExact :=
    TauCeti.CategoryTheory.shortExact_map_cechComplexFunctor _ _ fun _ _ ↦
      imageCokernelSequence_map_shortExact F _
  -- `ČH⁰(W, I) ⟶ ČH⁰(W, G)` is onto, as `ČH¹(W, F) = 0`
  have h₁ : Epi ((cechCohomology Y AddCommGrpCat.{u} 0).map (R.map (injectiveImageSequence F).g)) :=
    (ShortComplex.exact_iff_epi _ (h.eq_zero_of_tgt _)).1
      (TauCeti.CategoryTheory.cechCohomology_exact₃ _ _ hS₁ 0)
  -- `ČH⁰(W, G) ⟶ ČH⁰(W, Q)` is onto, as `ČH⁰(W, C) = 0`; the map `G ⟶ Q` is the first map
  -- `(imageCokernelSequence F).f` of the sequence up to unfolding `ShortComplex.cokernelSequence`
  have h₂ : Epi ((cechCohomology Y AddCommGrpCat.{u} 0).map
      (R.map (image.ι (cokernel.π (Injective.ι F)).hom))) :=
    (ShortComplex.exact_iff_epi _ ((isZero_cechCohomology_zero_obj_of_locally_eq_zero _
      (restrict_imageCokernelSequence_locally_eq_zero W)).eq_zero_of_tgt _)).1
      (TauCeti.CategoryTheory.cechCohomology_exact₂ _ _ hS₂ 0)
  -- so `ČH⁰(W, I) ⟶ ČH⁰(W, Q)` is onto, for the restrictions of `I` and `Q` as sheaves on `W`
  have := W.isOpenEmbedding.functor_isContinuous
  let P := Φ.sheafPushforwardContinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
  have h₃ : Epi ((cechCohomology Y AddCommGrpCat.{u} 0).map
      (P.map (cokernel.π (Injective.ι F))).hom) := by
    -- the restriction of a morphism of sheaves is its whiskering by `Φ.op`
    have hfac : (P.map (cokernel.π (Injective.ι F))).hom =
        R.map ((injectiveImageSequence F).g ≫ image.ι (cokernel.π (Injective.ι F)).hom) :=
      congrArg R.map (image.fac _).symm
    have h₄ := epi_comp
      ((cechCohomology Y AddCommGrpCat.{u} 0).map (R.map (injectiveImageSequence F).g))
      ((cechCohomology Y AddCommGrpCat.{u} 0).map
        (R.map (image.ι (cokernel.π (Injective.ι F)).hom)))
    rwa [← Functor.map_comp, ← Functor.map_comp, ← hfac] at h₄
  -- in degree `0`, the Čech cohomology of a sheaf is its global sections, naturally
  have hnat := (Iso.eq_comp_inv _).2
    (cechCohomologyZeroIso_hom_naturality _ (P.map (cokernel.π (Injective.ι F))))
  rw [Functor.sheafPushforwardContinuous_map_hom_app] at hnat
  rw [← AddCommGrpCat.epi_iff_surjective, hnat]
  exact epi_comp' (epi_comp' (IsIso.epi_of_iso (cechCohomologyZeroIso _).hom) h₃)
    (IsIso.epi_of_iso (cechCohomologyZeroIso _).inv)

/-- **Čech `H¹` vanishing implies sheaf `H¹` vanishing.** Let `F` be a sheaf of abelian groups on
`X` and `W` an open subset. If the restriction of `F` to the subspace `W` has vanishing degree one
Čech cohomology, the colimit over the point-neighborhood covers of `W`, then the sheaf cohomology
`H¹(W, F)` vanishes. -/
theorem subsingleton_H'_one_of_isZero_cechCohomology (W : Opens X)
    (h : IsZero ((cechCohomology ((Opens.toTopCat X).obj W) AddCommGrpCat.{u} 1).obj
      (W.isOpenEmbedding.isOpenMap.functor.op ⋙ F.obj))) :
    Subsingleton (_root_.CategoryTheory.Sheaf.H'.{u} F 1 W) := by
  rw [← Opens.isOpenEmbedding_obj_top W]
  exact Sheaf.H'.subsingleton_X₁_one (injectiveCokernelSequence_shortExact F) _
    (surjective_app_functor_obj_top F W h)
    (subsingleton_H'_succ_of_isFlasque (Injective.under F) 0 _)

end TauCeti.Topology
