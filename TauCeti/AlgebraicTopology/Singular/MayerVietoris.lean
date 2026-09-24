/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.MayerVietoris
public import TauCeti.AlgebraicTopology.Singular.Subdivision.Small.Equiv

/-!
# The Mayer–Vietoris sequence in singular homology

Let `U` and `V` be open subsets of a topological space `X` with `U ∪ V = X`, and let `R` be an
object of an abelian category with coproducts. This file constructs the Mayer–Vietoris long exact
sequence of singular homology with coefficients in `R`,
`⋯ ⟶ Hₙ(U ∩ V) ⟶ Hₙ(U) ⊞ Hₙ(V) ⟶ Hₙ(X) ⟶ Hₙ₋₁(U ∩ V) ⟶ ⋯`,
whose first map is `(i_U, -i_V)` and whose second map is `j_U + j_V`, the `i` and `j` being the
maps induced by the inclusions. The connecting morphism is natural in maps of covered spaces.

The construction is the one of Hatcher. For any two subsets `U` and `V` of `X`, the singular
simplicial sets of `U ∩ V`, `U` and `V` form a pushout square with the subcomplex of singular
simplices of `X` lying in `U` or in `V` (`TopCat.isPushout_toSSet_inter_smallSingularSubcomplex`),
so the Mayer–Vietoris sequence of simplicial sets applies to it. When `U` and `V` are open and
cover `X`, the small-chain theorem (`TauCeti.smallSingularHomologyIso`), which is also the core
of the proof of excision, identifies the homology of that subcomplex with the singular homology
of `X`.

## Main definitions and results

* `TopCat.isPushout_toSSet_inter_smallSingularSubcomplex`: the pushout square of singular
  simplicial sets of an intersection.
* `TopCat.mayerVietorisδ`: the Mayer–Vietoris connecting morphism `Hₙ(X) ⟶ Hₘ(U ∩ V)`,
  `m + 1 = n`, characterized by `TopCat.homologyMap_ι_comp_mayerVietorisδ`. The other two maps
  of the sequence are `SSet.mayerVietorisToBiprod` and `SSet.mayerVietorisFromBiprod` applied to
  the maps of singular simplicial sets induced by the inclusions.
* `TopCat.mayerVietoris_exact₁`, `TopCat.mayerVietoris_exact₂`, `TopCat.mayerVietoris_exact₃`:
  exactness at `Hₘ(U ∩ V)`, at `Hₙ(U) ⊞ Hₙ(V)` and at `Hₙ(X)`.
* `TopCat.mayerVietorisδ_naturality`: naturality of the connecting morphism.

## References

* A. Hatcher, *Algebraic Topology*, Section 2.2, the Mayer–Vietoris sequences.
-/

public section

noncomputable section

open CategoryTheory Limits Topology

universe w v u

namespace TopCat

variable {X : TopCat.{w}}

/-- The inclusion of a subspace is a monomorphism of topological spaces. -/
instance mono_ofHom_subtypeVal (S : Set X) : Mono (ofHom (ContinuousMap.subtypeVal S)) :=
  (TopCat.mono_iff_injective _).mpr Subtype.val_injective

/-- The inclusion of one subspace in another is a monomorphism of topological spaces. -/
instance mono_ofHom_inclusion {S T : Set X} (h : S ⊆ T) :
    Mono (ofHom (ContinuousMap.inclusion h)) :=
  (TopCat.mono_iff_injective _).mpr (Set.inclusion_injective h)

private lemma range_ofHom_subtypeVal (S : Set X) :
    Set.range (ofHom (ContinuousMap.subtypeVal S)) = S :=
  Subtype.range_coe

private lemma isInducing_ofHom_subtypeVal (S : Set X) :
    IsInducing (ofHom (ContinuousMap.subtypeVal S)) :=
  IsInducing.subtypeVal

variable (U V : Set X)

/-- The square of inclusions of `U ∩ V`, `U` and `V` into `X` commutes. -/
lemma commSq_ofHom_inter :
    CommSq (ofHom (ContinuousMap.inclusion (Set.inter_subset_left (t := V))))
      (ofHom (ContinuousMap.inclusion (Set.inter_subset_right (s := U))))
      (ofHom (ContinuousMap.subtypeVal U)) (ofHom (ContinuousMap.subtypeVal V)) :=
  ⟨rfl⟩

/-- **The singular simplicial sets of an intersection form a pushout square.** For subsets `U` and
`V` of `X`, the singular simplicial sets of `U ∩ V`, `U` and `V` form a pushout square with the
subcomplex of singular simplices of `X` whose image lies in `U` or in `V`. -/
theorem isPushout_toSSet_inter_smallSingularSubcomplex :
    IsPushout (toSSet.map (ofHom (ContinuousMap.inclusion (Set.inter_subset_left (t := V)))))
      (toSSet.map (ofHom (ContinuousMap.inclusion (Set.inter_subset_right (s := U)))))
      (toSmallSingularSubcomplex ![U, V] (Matrix.cons_val_zero U ![V]).superset)
      (toSmallSingularSubcomplex ![U, V]
        ((Matrix.cons_val_one U ![V]).trans (Matrix.cons_val_zero V ![])).superset) where
  w := by
    rw [← cancel_mono (X.smallSingularSubcomplex ![U, V]).ι, Category.assoc, Category.assoc,
      toSmallSingularSubcomplex_ι, toSmallSingularSubcomplex_ι, ← Functor.map_comp,
      ← Functor.map_comp, (commSq_ofHom_inter U V).w]
  isColimit' := ⟨evaluationJointlyReflectsColimits _ fun n ↦ by
    refine (isColimitMapCoconePushoutCoconeEquiv _ _).2 (IsPushout.isColimit ?_)
    have : Mono ((X.smallSingularSubcomplex ![U, V]).ι.app n) :=
      (CategoryTheory.mono_iff_injective _).mpr Subtype.val_injective
    refine Types.isPushout_of_isPullback_of_mono (k := (X.smallSingularSubcomplex ![U, V]).ι.app n)
      (r' := (toSSet.map (ofHom (ContinuousMap.subtypeVal U))).app n)
      (b' := (toSSet.map (ofHom (ContinuousMap.subtypeVal V))).app n) ?_
      (congr_app (toSmallSingularSubcomplex_ι ![U, V] (Matrix.cons_val_zero U ![V]).superset) n)
      (congr_app (toSmallSingularSubcomplex_ι ![U, V]
        ((Matrix.cons_val_one U ![V]).trans (Matrix.cons_val_zero V ![])).superset) n) ?_
      (fun _ _ _ _ h ↦ injective_of_mono ((toSSet.map _).app n) h)
    · rw [Types.isPullback_iff]
      refine ⟨?_, fun _ _ h ↦ injective_of_mono ((toSSet.map _).app n) h.1, fun x₂ x₃ h ↦ ?_⟩
      · simp only [evaluation_obj_map, ← NatTrans.comp_app, ← Functor.map_comp,
          (commSq_ofHom_inter U V).w]
      -- A simplex of `U` which is also a simplex of `V` is a simplex of `U ∩ V`.
      obtain ⟨x₁, hx₁⟩ := ((isInducing_ofHom_subtypeVal (U ∩ V)).mem_range_toSSet_map_app_iff n
        ((toSSet.map (ofHom (ContinuousMap.subtypeVal U))).app n x₂)).mpr (by
          rw [range_ofHom_subtypeVal]
          rintro _ ⟨z, rfl⟩
          refine ⟨((TopCat.of U).toSSetObjEquiv n x₂ z).2, ?_⟩
          rw [h]
          exact ((TopCat.of V).toSSetObjEquiv n x₃ z).2)
      exact ⟨x₁, injective_of_mono ((toSSet.map (ofHom (ContinuousMap.subtypeVal U))).app n) hx₁,
        injective_of_mono ((toSSet.map (ofHom (ContinuousMap.subtypeVal V))).app n)
          (hx₁.trans h)⟩
    · refine Set.eq_univ_of_forall fun σ ↦ ?_
      obtain ⟨i, hi⟩ := (mem_smallSingularSubcomplex_iff _ _ σ.1).mp σ.2
      fin_cases i
      · obtain ⟨τ, hτ⟩ := ((isInducing_ofHom_subtypeVal U).mem_range_toSSet_map_app_iff n
          σ.1).mpr (by rw [range_ofHom_subtypeVal]; exact hi)
        exact Or.inl ⟨τ, Subtype.ext ((toSmallSingularSubcomplex_app_coe _ _ τ).trans hτ)⟩
      · obtain ⟨τ, hτ⟩ := ((isInducing_ofHom_subtypeVal V).mem_range_toSSet_map_app_iff n
          σ.1).mpr (by rw [range_ofHom_subtypeVal]; exact hi)
        exact Or.inr ⟨τ, Subtype.ext ((toSmallSingularSubcomplex_app_coe _ _ τ).trans hτ)⟩⟩

/-! ### The Mayer–Vietoris sequence of an open cover by two sets -/

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C)
  {U V} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = Set.univ)

include hU hV in
private lemma isOpen_vecCons : ∀ i, IsOpen (![U, V] i) := by
  simp [Fin.forall_fin_two, hU, hV]

include hUV in
private lemma iUnion_vecCons : ⋃ i, ![U, V] i = Set.univ := by
  rw [← hUV]
  ext
  simp [Fin.exists_fin_two]

/-- The Mayer–Vietoris connecting morphism `Hₙ(X) ⟶ Hₘ(U ∩ V)`, where `m + 1 = n`, for an open
cover of `X` by `U` and `V`. It is the connecting morphism of the Mayer–Vietoris sequence of the
singular simplicial sets of `U ∩ V`, `U` and `V`, precomposed with the inverse of the small-chain
isomorphism. -/
def mayerVietorisδ (n m : ℕ) (h : m + 1 = n := by lia) :
    (toSSet.obj X).homology R n ⟶ (toSSet.obj (of ↥(U ∩ V))).homology R m :=
  (TauCeti.smallSingularHomologyIso R ![U, V] (isOpen_vecCons hU hV) (iUnion_vecCons hUV) n).inv ≫
    SSet.mayerVietorisδ R (isPushout_toSSet_inter_smallSingularSubcomplex U V) n m h

/-- The Mayer–Vietoris connecting morphism of the open cover restricts, on the homology of the
singular simplices lying in `U` or in `V`, to that of the pushout square of singular simplicial
sets. Since that homology maps isomorphically onto `Hₙ(X)`, this characterizes it. -/
@[reassoc (attr := simp)]
lemma homologyMap_ι_comp_mayerVietorisδ (n m : ℕ) (h : m + 1 = n := by lia) :
    SSet.homologyMap (X.smallSingularSubcomplex ![U, V]).ι R n ≫ mayerVietorisδ R hU hV hUV n m h =
      SSet.mayerVietorisδ R (isPushout_toSSet_inter_smallSingularSubcomplex U V) n m h := by
  rw [mayerVietorisδ, SSet.homologyMap, ← TauCeti.smallSingularHomologyIso_hom R ![U, V]
    (isOpen_vecCons hU hV) (iUnion_vecCons hUV), Iso.hom_inv_id_assoc]

private lemma mayerVietorisFromBiprod_comp_homologyMap_ι (n : ℕ) :
    SSet.mayerVietorisFromBiprod R
        (toSmallSingularSubcomplex ![U, V] (Matrix.cons_val_zero U ![V]).superset)
        (toSmallSingularSubcomplex ![U, V]
          ((Matrix.cons_val_one U ![V]).trans (Matrix.cons_val_zero V ![])).superset) n ≫
      SSet.homologyMap (X.smallSingularSubcomplex ![U, V]).ι R n =
    SSet.mayerVietorisFromBiprod R (toSSet.map (ofHom (ContinuousMap.subtypeVal U)))
      (toSSet.map (ofHom (ContinuousMap.subtypeVal V))) n := by
  ext <;> simp [← SSet.homologyMap_comp]

@[reassoc (attr := simp)]
lemma mayerVietorisδ_toBiprod (n m : ℕ) (h : m + 1 = n := by lia) :
    mayerVietorisδ R hU hV hUV n m h ≫
      SSet.mayerVietorisToBiprod R
        (toSSet.map (ofHom (ContinuousMap.inclusion (Set.inter_subset_left (t := V)))))
        (toSSet.map (ofHom (ContinuousMap.inclusion (Set.inter_subset_right (s := U))))) m = 0 := by
  simp [mayerVietorisδ]

@[reassoc (attr := simp)]
lemma mayerVietorisFromBiprod_δ (n m : ℕ) (h : m + 1 = n := by lia) :
    SSet.mayerVietorisFromBiprod R (toSSet.map (ofHom (ContinuousMap.subtypeVal U)))
        (toSSet.map (ofHom (ContinuousMap.subtypeVal V))) n ≫
      mayerVietorisδ R hU hV hUV n m h = 0 := by
  rw [← mayerVietorisFromBiprod_comp_homologyMap_ι, Category.assoc,
    homologyMap_ι_comp_mayerVietorisδ R hU hV hUV n m h, SSet.mayerVietorisFromBiprod_δ R _ n m h]

/-- **Exactness of the Mayer–Vietoris sequence at `Hₘ(U ∩ V)`.** -/
lemma mayerVietoris_exact₁ (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (mayerVietorisδ_toBiprod R hU hV hUV n m h)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (SSet.mayerVietoris_exact₁ R (isPushout_toSSet_inter_smallSingularSubcomplex U V) n m h)
  refine ShortComplex.isoMk
    (TauCeti.smallSingularHomologyIso R _ (isOpen_vecCons hU hV) (iUnion_vecCons hUV) n)
    (Iso.refl _) (Iso.refl _) ?_ (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id])
  dsimp only
  rw [Iso.refl_hom, Category.comp_id, TauCeti.smallSingularHomologyIso_hom,
    homologyMap_ι_comp_mayerVietorisδ R hU hV hUV n m h]

include hU hV hUV in
/-- **Exactness of the Mayer–Vietoris sequence at `Hₙ(U) ⊞ Hₙ(V)`.** -/
lemma mayerVietoris_exact₂ (n : ℕ) :
    (ShortComplex.mk _ _
      (SSet.mayerVietorisToBiprod_fromBiprod R ((commSq_ofHom_inter U V).map toSSet) n)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (SSet.mayerVietoris_exact₂ R (isPushout_toSSet_inter_smallSingularSubcomplex U V) n)
  refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (TauCeti.smallSingularHomologyIso R _ (isOpen_vecCons hU hV) (iUnion_vecCons hUV) n)
    (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]) ?_
  dsimp only
  rw [TauCeti.smallSingularHomologyIso_hom, Iso.refl_hom, Category.id_comp,
    mayerVietorisFromBiprod_comp_homologyMap_ι]

/-- **Exactness of the Mayer–Vietoris sequence at `Hₙ(X)`.** -/
lemma mayerVietoris_exact₃ (n m : ℕ) (h : m + 1 = n := by lia) :
    (ShortComplex.mk _ _ (mayerVietorisFromBiprod_δ R hU hV hUV n m h)).Exact := by
  refine (ShortComplex.exact_iff_of_iso ?_).1
    (SSet.mayerVietoris_exact₃ R (isPushout_toSSet_inter_smallSingularSubcomplex U V) n m h)
  refine ShortComplex.isoMk (Iso.refl _)
    (TauCeti.smallSingularHomologyIso R _ (isOpen_vecCons hU hV) (iUnion_vecCons hUV) n)
    (Iso.refl _) ?_ ?_
  · dsimp only
    rw [TauCeti.smallSingularHomologyIso_hom, Iso.refl_hom, Category.id_comp,
      mayerVietorisFromBiprod_comp_homologyMap_ι]
  · dsimp only
    rw [Iso.refl_hom, Category.comp_id, TauCeti.smallSingularHomologyIso_hom,
    homologyMap_ι_comp_mayerVietorisδ R hU hV hUV n m h]

variable {Y : TopCat.{w}} {U' V' : Set Y} (hU' : IsOpen U') (hV' : IsOpen V')
  (hUV' : U' ∪ V' = Set.univ) (f : X ⟶ Y) (hfU : Set.MapsTo f U U') (hfV : Set.MapsTo f V V')

/-- **Naturality of the Mayer–Vietoris connecting morphism.** A map `f : X ⟶ Y` carrying `U` into
`U'` and `V` into `V'` commutes with the connecting morphisms, where `U ∩ V ⟶ U' ∩ V'` is the
restriction of `f`. -/
@[reassoc]
lemma mayerVietorisδ_naturality (n m : ℕ) (h : m + 1 = n := by lia) :
    mayerVietorisδ R hU hV hUV n m h ≫
        SSet.homologyMap (toSSet.map (ofHom ⟨(hfU.inter_inter hfV).restrict,
          f.hom.continuous.restrict (hfU.inter_inter hfV)⟩)) R m =
      SSet.homologyMap (toSSet.map f) R n ≫ mayerVietorisδ R hU' hV' hUV' n m h := by
  have hf : ∀ i, Set.MapsTo f (![U, V] i) (![U', V'] (id i)) := by
    simp [Fin.forall_fin_two, hfU, hfV]
  have hsmall := TauCeti.smallSingularHomologyIso_naturality R ![U, V] (isOpen_vecCons hU hV)
    (iUnion_vecCons hUV) ![U', V'] f id hf (isOpen_vecCons hU' hV') (iUnion_vecCons hUV') n
  have hnat := SSet.mayerVietorisδ_naturality R
    (toSSet.map (ofHom ⟨(hfU.inter_inter hfV).restrict,
      f.hom.continuous.restrict (hfU.inter_inter hfV)⟩))
    (toSSet.map (ofHom ⟨hfU.restrict, f.hom.continuous.restrict hfU⟩))
    (toSSet.map (ofHom ⟨hfV.restrict, f.hom.continuous.restrict hfV⟩))
    (X.smallSingularSubcomplexMap ![U, V] ![U', V'] f id hf)
    (isPushout_toSSet_inter_smallSingularSubcomplex U V)
    (isPushout_toSSet_inter_smallSingularSubcomplex U' V') ?_ ?_ ?_ ?_ n m h
  · rw [mayerVietorisδ, mayerVietorisδ, Category.assoc, hnat, ← Category.assoc,
      ← Category.assoc]
    congr 1
    rw [Iso.inv_comp_eq, ← Category.assoc, hsmall, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  -- The four squares of singular simplicial sets commute because the underlying squares of
  -- continuous maps do, pointwise by definition.
  · rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  · rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  · rw [← cancel_mono (Y.smallSingularSubcomplex ![U', V']).ι, Category.assoc, Category.assoc,
      smallSingularSubcomplexMap_ι, toSmallSingularSubcomplex_ι_assoc, toSmallSingularSubcomplex_ι,
      ← Functor.map_comp, ← Functor.map_comp]
    rfl
  · rw [← cancel_mono (Y.smallSingularSubcomplex ![U', V']).ι, Category.assoc, Category.assoc,
      smallSingularSubcomplexMap_ι, toSmallSingularSubcomplex_ι_assoc, toSmallSingularSubcomplex_ι,
      ← Functor.map_comp, ← Functor.map_comp]
    rfl

end TopCat
