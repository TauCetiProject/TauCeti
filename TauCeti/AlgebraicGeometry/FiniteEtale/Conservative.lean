/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.Exactness
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

/-!
# Conservativity of geometric fibre functors over a connected base

Let `x : Spec Ω ⟶ S` be a geometric point of a scheme `S`, with `Ω` separably closed. The
geometric fibre `FiniteEtaleScheme.fiber x` of a finite étale `S`-scheme `Z` is nonempty exactly
when the image of `x` lies in the image of `Z`. When `S` is connected, the image of a finite
étale morphism is open and closed, so it is either empty or all of `S`; hence a finite étale
`S`-scheme is empty exactly when its geometric fibre at `x` is.

From this we deduce that over a connected base a family of morphisms of finite étale schemes is
jointly surjective exactly when it is jointly surjective on a geometric fibre, and that the
geometric fibre functor reflects epimorphisms, monomorphisms and isomorphisms. The last is the
axiom (G6) for a fibre functor in the sense of Lenstra, that is, the field `reflectsIsos` of
Mathlib's `CategoryTheory.PreGaloisCategory.FiberFunctor`.

## Main results

* `TauCeti.FiniteEtaleScheme.nonempty_fiber_obj_iff_range_subset_range`: the geometric fibre
  of `Z` at `x` is nonempty if and only if the image of `x` lies in the image of `Z`.
* `TauCeti.FiniteEtaleScheme.nonempty_fiber_obj_ofHom_ι_iff`: for an open and closed subscheme
  `U` of the base, the geometric fibre of `U` at `x` is nonempty if and only if `x` lies in `U`.
* `TauCeti.FiniteEtaleScheme.nonempty_fiber_obj_iff_nonempty`: over a connected base, the
  geometric fibre of `Z` is nonempty if and only if `Z` is nonempty.
* `TauCeti.FiniteEtaleScheme.iUnion_range_eq_univ_iff`: over a connected base, a family of
  morphisms of finite étale schemes is jointly surjective if and only if it is jointly surjective
  on a geometric fibre.
* Over a connected base, `FiniteEtaleScheme.fiber x` reflects epimorphisms and monomorphisms.
  As finite étale schemes form a balanced category, it then reflects isomorphisms by Mathlib's
  `CategoryTheory.Functor.reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms`.

For joint surjectivity, the complement of the images of finitely many of the maps `f i` into `X`
is open and closed in `X`, hence a finite étale `S`-scheme. A point of its geometric fibre would
lift through some `f i` by joint surjectivity on fibres, which is impossible, so the complement is
empty. Reflecting epimorphisms is the case of a single map. For monomorphisms we apply it to
the diagonal of `f`, which is a split monomorphism, hence an isomorphism once it is an
epimorphism.

## References

* H. W. Lenstra, *Galois theory for schemes*, Definition 3.1 and Section 5.
* The Stacks Project, Section 58.5 (tag 0BL8), *Finite étale covers of schemes*.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.FiniteEtaleScheme

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The geometric fibre of a finite étale `S`-scheme `Z` at `x : Spec Ω ⟶ S` is nonempty if and
only if the image of `x` lies in the image of `Z`. -/
theorem nonempty_fiber_obj_iff_range_subset_range (x : Spec (.of Ω) ⟶ S)
    (Z : FiniteEtaleScheme S) :
    Nonempty ((fiber x).obj Z) ↔ Set.range x ⊆ Set.range Z.obj.hom := by
  constructor
  · rintro ⟨y⟩ _ ⟨p, rfl⟩
    let g := (fiberCompInclIso x).hom.app Z y
    exact ⟨g.left p, by rw [← Scheme.Hom.comp_apply]; exact congrArg (· p) (Over.w g)⟩
  · intro h
    obtain ⟨p⟩ : Nonempty (Spec (.of Ω)) := inferInstance
    obtain ⟨z, hz⟩ := h ⟨p, rfl⟩
    obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback z p hz
    -- The base change `W` of `Z` to `Spec Ω` has the point `w`. If its finite set were empty,
    -- `W` would be initial, hence empty, as the classification is an equivalence.
    by_contra hW
    have hi : IsInitial ((pullback x).obj Z) :=
      (IsInitial.isInitialIffObj (equivOfIsSepClosed Ω).functor _).symm
        ((Concrete.initial_iff_empty_of_preserves_of_reflects _).mpr
          (not_nonempty_iff.mp hW)).some
    have : IsEmpty ((pullback x).obj Z).obj.left := isInitial_iff_isEmpty.mp
      ⟨hi.isInitialObj ((finiteEtaleSchemeProperty (Spec (.of Ω))).ι ⋙ Over.forget _) _⟩
    exact this.false w

/-- Let `U` be an open subscheme of the base whose inclusion is finite, that is, `U` is also
closed. The geometric fibre at `x` of `U`, as a finite étale `S`-scheme, is nonempty exactly when
`x` lies in `U`. -/
theorem nonempty_fiber_obj_ofHom_ι_iff (U : S.Opens) [IsFinite U.ι] (x : Spec (.of Ω) ⟶ S) :
    Nonempty ((fiber x).obj (ofHom U.ι)) ↔ x default ∈ U := by
  rw [nonempty_fiber_obj_iff_range_subset_range, Set.range_unique, Set.singleton_subset_iff,
    ofHom_obj]
  -- The structure morphism `(Over.mk U.ι).hom` is `U.ι` (`Over.mk_hom`), but its codomain is
  -- written differently, so `rw` cannot replace it under the coercion to functions.
  exact Iff.of_eq (congrArg (x default ∈ ·) (Scheme.Opens.range_ι U))

/-- Over a connected base `S`, a finite étale `S`-scheme is nonempty if and only if its
geometric fibre at a geometric point `x` is nonempty: its image is open and closed in `S`. -/
theorem nonempty_fiber_obj_iff_nonempty [PreconnectedSpace S] (x : Spec (.of Ω) ⟶ S)
    (Z : FiniteEtaleScheme S) : Nonempty ((fiber x).obj Z) ↔ Nonempty Z.obj.left := by
  rw [nonempty_fiber_obj_iff_range_subset_range]
  obtain ⟨p⟩ : Nonempty (Spec (.of Ω)) := inferInstance
  refine ⟨fun h ↦ ⟨(h ⟨p, rfl⟩).choose⟩, fun ⟨z⟩ ↦ ?_⟩
  have : IsClopen (Set.range Z.obj.hom) :=
    ⟨Z.obj.hom.isClosedMap.isClosed_range, Z.obj.hom.isOpenMap.isOpen_range⟩
  rw [this.eq_univ ⟨_, z, rfl⟩]
  exact Set.subset_univ _

/-- If the image of a lift `s` of a geometric point lies in the range of a morphism `f` of finite
étale schemes, then `s` lifts through `f` on geometric fibres. -/
private theorem mem_range_fiber_map_of_mem_range (x : Spec (.of Ω) ⟶ S)
    {X Y : FiniteEtaleScheme S} (f : Y ⟶ X) (s : (fiber x ⋙ FintypeCat.incl).obj X)
    (p : Spec (.of Ω)) (hs : ((fiberCompInclIso x).hom.app X s).left p ∈ Set.range f.hom.left) :
    s ∈ Set.range ((fiber x ⋙ FintypeCat.incl).map f) := by
  set s' := (fiberCompInclIso x).hom.app X s
  -- The point `s'` of `X` lifts to `Y`, seen as a finite étale `X`-scheme `Z`.
  let Z : FiniteEtaleScheme X.obj.left :=
    ⟨Over.mk f.hom.left, (finiteEtaleSchemeProperty_iff _).mpr
      ⟨(inferInstance : IsFinite f.hom.left), (inferInstance : Etale f.hom.left)⟩⟩
  obtain ⟨a⟩ := (nonempty_fiber_obj_iff_range_subset_range s'.left Z).mpr (by
    rintro _ ⟨q, rfl⟩
    rw [Subsingleton.elim q p]
    exact hs)
  let a' := (fiberCompInclIso s'.left).hom.app Z a
  have ha : a'.left ≫ f.hom.left = s'.left := Over.w a'
  let t : Over.mk x ⟶ Y.obj := Over.homMk a'.left (by
    rw [← Over.w f.hom, ← Category.assoc, ha]; exact Over.w s')
  refine ⟨(fiberCompInclIso x).inv.app Y t, ?_⟩
  apply ((fiberCompInclIso x).app X).toEquiv.injective
  have h := NatTrans.naturality_apply (fiberCompInclIso x).hom f ((fiberCompInclIso x).inv.app Y t)
  refine h.trans ?_
  simp only [Iso.app_hom, Iso.toEquiv_fun, Iso.inv_hom_id_app_apply]
  exact Over.OverMorphism.ext ha

/-- **Joint surjectivity on a geometric fibre.** Over a connected base, a family of morphisms of
finite étale schemes is jointly surjective exactly when it is jointly surjective on the geometric
fibre at any geometric point. -/
theorem iUnion_range_eq_univ_iff [PreconnectedSpace S] (x : Spec (.of Ω) ⟶ S)
    {X : FiniteEtaleScheme S} {ι : Type*} {Y : ι → FiniteEtaleScheme S} (f : ∀ i, Y i ⟶ X) :
    ⋃ i, Set.range (f i).hom.left = .univ ↔
      ∀ s : (fiber x ⋙ FintypeCat.incl).obj X, ∃ i,
        s ∈ Set.range ((fiber x ⋙ FintypeCat.incl).map (f i)) := by
  obtain ⟨p⟩ : Nonempty (Spec (.of Ω)) := inferInstance
  refine ⟨fun h s ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
      (h ▸ Set.mem_univ (((fiberCompInclIso x).hom.app X s).left p))
    exact ⟨i, mem_range_fiber_map_of_mem_range x (f i) s p hi⟩
  have : Finite ((fiber x ⋙ FintypeCat.incl).obj X) := inferInstanceAs (Finite ((fiber x).obj X))
  choose j hj using h
  -- The points of `X` missed by the finitely many maps `f (j s)` form an open and closed set.
  let C : Set X.obj.left := ⋂ s, (Set.range (f (j s)).hom.left)ᶜ
  have hC : IsClosed C := isClosed_iInter fun s ↦
    (f (j s)).hom.left.isOpenMap.isOpen_range.isClosed_compl
  let U : X.obj.left.Opens := ⟨C, isOpen_iInter_of_finite fun s ↦
    (f (j s)).hom.left.isClosedMap.isClosed_range.isOpen_compl⟩
  have hU : (U : Set X.obj.left) = C := rfl
  let v := clopenSubschemeι U hC
  refine Set.eq_univ_of_forall fun y ↦ by_contra fun hy ↦ ?_
  -- The complement `C` contains `y`, so its geometric fibre has a point `a`, whose image in the
  -- fibre of `X` comes from a point `b` of the fibre of some `Y (j s)`.
  obtain ⟨q, -⟩ : y ∈ Set.range v.hom.left := by
    rw [range_clopenSubschemeι_hom_left]
    exact Set.mem_iInter.mpr fun s hs ↦ hy (Set.mem_iUnion.mpr ⟨_, hs⟩)
  obtain ⟨a⟩ := (nonempty_fiber_obj_iff_nonempty x (clopenSubscheme U hC)).mpr ⟨q⟩
  set s := (fiber x ⋙ FintypeCat.incl).map v a
  obtain ⟨b, hb⟩ := hj s
  -- The corresponding lifts of `x` to `Y (j s)` and to `C` agree in `X`.
  have h₁ := NatTrans.naturality_apply (fiberCompInclIso x).hom (f (j s)) b
  have h₂ := NatTrans.naturality_apply (fiberCompInclIso x).hom v a
  have h : (fiberCompInclIso x).hom.app _ b ≫ (f (j s)).hom =
      (fiberCompInclIso x).hom.app _ a ≫ v.hom := by
    simpa using h₁.symm.trans ((congrArg ((fiberCompInclIso x).hom.app X) hb).trans h₂)
  have hp := congrArg (fun g : Over.mk x ⟶ X.obj ↦ g.left p) h
  simp only [Over.comp_left, Scheme.Hom.comp_apply] at hp
  have hv : v.hom.left (((fiberCompInclIso x).hom.app _ a).left p) ∈ C := by
    rw [← hU, ← range_clopenSubschemeι_hom_left U hC]
    exact Set.mem_range_self _
  exact Set.mem_iInter.mp hv s ⟨_, hp⟩

/-- Over a connected base, a geometric fibre functor reflects epimorphisms: this is the case of
a single morphism in `iUnion_range_eq_univ_iff`. -/
instance [PreconnectedSpace S] (x : Spec (.of Ω) ⟶ S) : (fiber x).ReflectsEpimorphisms where
  reflects {X Y} f hf := by
    rw [epi_iff_surjective]
    refine ⟨Set.range_eq_univ.mp ?_⟩
    rw [← Set.iUnion_const (ι := Unit) (Set.range f.hom.left)]
    refine (iUnion_range_eq_univ_iff x (fun _ : Unit ↦ f)).mpr fun s ↦ ⟨⟨⟩, ?_⟩
    exact surjective_of_epi (FintypeCat.incl.map ((fiber x).map f)) s

/-- Over a connected base, a geometric fibre functor reflects monomorphisms: if `f` is injective
on geometric fibres, its diagonal is an epimorphism on fibres, hence an epimorphism, and a split
monomorphism. -/
instance [PreconnectedSpace S] (x : Spec (.of Ω) ⟶ S) : (fiber x).ReflectsMonomorphisms where
  reflects {X Y} f hf := by
    -- Adapted from Mathlib's `ReflectsMonomorphisms` instance for
    -- `CategoryTheory.PreGaloisCategory.FiberFunctor` in
    -- `Mathlib/CategoryTheory/Galois/Basic.lean`, which uses that fibre functors reflect
    -- isomorphisms; here we only know that `fiber x` reflects epimorphisms.
    have : IsIso ((fiber x).map (pullback.fst f f)) := by
      rw [← PreservesPullback.iso_hom_fst]
      have := isIso_fst_of_mono ((fiber x).map f)
      infer_instance
    have : IsIso ((fiber x).map (pullback.diagonal f)) := isIso_of_comp_hom_eq_id _ (by
      rw [← Functor.map_comp, pullback.diagonal_fst, CategoryTheory.Functor.map_id])
    have : Epi (pullback.diagonal f) := (fiber x).epi_of_epi_map inferInstance
    have : IsIso (pullback.diagonal f) := isIso_of_epi_of_isSplitMono _
    exact (pullback.isIso_diagonal_iff f).mp this

end TauCeti.FiniteEtaleScheme
