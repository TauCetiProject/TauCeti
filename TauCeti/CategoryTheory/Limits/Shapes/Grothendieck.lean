/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.CategoryTheory.Grothendieck.Basic
public import Mathlib.CategoryTheory.Limits.Final

/-!
# Fiberwise limits over a Grothendieck construction

For a diagram on a Grothendieck construction, taking limits on the fibers is covariant
in the base whenever restriction along each transition induces an isomorphism of limits.
The limit of this fiberwise diagram is the limit of the original diagram, naturally
in that diagram. Initial transition functors supply the restriction hypothesis through
Mathlib's `Functor.Initial.limit_pre_isIso`.

The functor and cone constructions are reducible on objects and cone points: the fiber
limits and the original cone points are retained as their actual carriers.

The construction uses Mathlib's fiber inclusions `Grothendieck.ι`, their transformations
`Grothendieck.ιNatTrans`, and the inverse of `limit.pre`. It is the limit counterpart of
Mathlib's `fiberwiseColimit`, with an additional restriction hypothesis because the
Grothendieck construction is covariant in its fibers.

Restricting the total diagram along Mathlib's `Grothendieck.pre C G` for `G : D' ⥤ D`
corresponds to restricting the fiberwise diagram along `G`. Consequently, when `G` is initial,
restriction along `Grothendieck.pre C G` is an isomorphism of limits under the same hypothesis on
the transition functors, which need not themselves be initial.

Adapted from `Mei/CategoryTheory/Limits/Grothendieck.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`bac6f02d25746bc1c2ec808601d4e9284911c475` (Apache 2.0). The construction is the
limit counterpart of Mathlib's `CategoryTheory/Limits/Shapes/Grothendieck.lean`.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

universe v u v' u' v'' u'' w z

namespace CategoryTheory.Limits

variable {D : Type u} [Category.{v} D] {C : D ⥤ Cat.{w, z}}
  {V : Type u'} [Category.{v'} V]
  (F : Grothendieck C ⥤ V)
  [∀ d, HasLimit (Grothendieck.ι C d ⋙ F)]
  [∀ {d e} (f : d ⟶ e), HasLimit ((C.map f).toFunctor ⋙ (Grothendieck.ι C e ⋙ F))]
  [∀ {d e} (f : d ⟶ e), IsIso (limit.pre (Grothendieck.ι C e ⋙ F) (C.map f).toFunctor)]

namespace FiberwiseLimit

/-- The map between fiber limits induced by a base arrow. -/
noncomputable def map {d e : D} (f : d ⟶ e) :
    limit (Grothendieck.ι C d ⋙ F) ⟶ limit (Grothendieck.ι C e ⋙ F) :=
  limMap (whiskerRight (Grothendieck.ιNatTrans f) F ≫
    (Functor.associator _ _ _).hom) ≫
      inv (limit.pre (Grothendieck.ι C e ⋙ F) (C.map f).toFunctor)

/-- Restricting the target projection computes the fiber map. -/
@[reassoc (attr := simp)]
theorem map_π {d e : D} (f : d ⟶ e) (x : C.obj d) :
    map F f ≫ limit.π (Grothendieck.ι C e ⋙ F) ((C.map f).toFunctor.obj x) =
      limit.π (Grothendieck.ι C d ⋙ F) x ≫ F.map ((Grothendieck.ιNatTrans f).app x) := by
  simp [map, limit.inv_pre_π]

/-- The fiber map intertwines every arrow in the total category over the given base arrow. -/
@[reassoc]
theorem map_π_of_hom {X Y : Grothendieck C} (h : X ⟶ Y) :
    map F h.base ≫ limit.π (Grothendieck.ι C Y.base ⋙ F) Y.fiber =
      limit.π (Grothendieck.ι C X.base ⋙ F) X.fiber ≫ F.map h := by
  rw [← limit.w (Grothendieck.ι C Y.base ⋙ F) h.fiber]
  simp only [Functor.comp_map]
  rw [← Category.assoc (obj := V), map_π, Category.assoc (obj := V), ← F.map_comp,
    Grothendieck.ιNatTrans_app_comp_ι_map]
  rfl

/-- The fiber map of an identity arrow is the identity. -/
@[simp]
theorem map_id (d : D) : map F (𝟙 d) = 𝟙 _ := by
  apply limit.hom_ext
  intro x
  have h := map_π_of_hom F (𝟙 (⟨d, x⟩ : Grothendieck C))
  erw [F.map_id, Category.comp_id] at h
  simpa only [Grothendieck.id_base, Category.id_comp (obj := V)] using h

/-- The fiber maps respect composition in the base. -/
@[reassoc, simp]
theorem map_comp {d e b : D} (f : d ⟶ e) (g : e ⟶ b) :
    map F (f ≫ g) = map F f ≫ map F g := by
  apply (cancel_mono (limit.pre (Grothendieck.ι C b ⋙ F) (C.map (f ≫ g)).toFunctor)).mp
  apply limit.hom_ext
  intro x
  simp only [Category.assoc (obj := V), limit.pre_π]
  rw [map_π, ← limit.w (Grothendieck.ι C b ⋙ F) (eqToHom (by simp :
    (C.map g).toFunctor.obj ((C.map f).toFunctor.obj x) =
      (C.map (f ≫ g)).toFunctor.obj x))]
  simp only [Functor.comp_map, ← Category.assoc (obj := V), map_π]
  simp only [Category.assoc (obj := V), ← F.map_comp,
    Category.assoc (obj := Grothendieck C), Grothendieck.ιNatTrans_app_comp]

end FiberwiseLimit

/-- The diagram obtained by taking limits on the fibers and inverting restriction along
base transitions. -/
noncomputable abbrev fiberwiseLimit : D ⥤ V where
  obj d := limit (Grothendieck.ι C d ⋙ F)
  map f := FiberwiseLimit.map F f
  map_id := FiberwiseLimit.map_id F
  map_comp := FiberwiseLimit.map_comp F

@[simp]
theorem fiberwiseLimit_obj (d : D) :
    (fiberwiseLimit F).obj d = limit (Grothendieck.ι C d ⋙ F) := (rfl)

@[simp]
theorem fiberwiseLimit_map {d e : D} (f : d ⟶ e) :
    (fiberwiseLimit F).map f = FiberwiseLimit.map F f := (rfl)

namespace FiberwiseLimit

section Pre

variable {D' : Type u''} [Category.{v''} D'] (G : D' ⥤ D)

/-- A cone on the fiber limits restricted along `G` induces a cone on the total diagram
restricted along `Grothendieck.pre C G`. -/
noncomputable abbrev preCone (c : Cone (G ⋙ fiberwiseLimit F)) :
    Cone (Grothendieck.pre C G ⋙ F) where
  pt := c.pt
  π :=
    { app X := c.π.app X.base ≫ limit.π (Grothendieck.ι C (G.obj X.base) ⋙ F) X.fiber
      naturality X Y h := by
        have w := map_π_of_hom F ((Grothendieck.pre C G).map h)
        simp only [Grothendieck.pre_map_base, Grothendieck.pre_obj_base,
          Grothendieck.pre_obj_fiber] at w
        simp only [Functor.const_obj_obj, Functor.comp_obj, Functor.const_obj_map,
          Category.id_comp, Functor.comp_map, ← c.w h.base]
        -- The middle objects are `(Grothendieck.ι C (G.obj Y.base) ⋙ F).obj Y.fiber` and
        -- `F.obj ((Grothendieck.pre C G).obj Y)`, equal only by unfolding `Grothendieck.ι` and
        -- `Grothendieck.pre`, so the reassociation is checked by `exact` rather than rewritten.
        exact (Category.assoc _ _ _).trans
          ((c.π.app X.base ≫= w).trans (Category.assoc _ _ _).symm) }

@[simp]
theorem preCone_pt (c : Cone (G ⋙ fiberwiseLimit F)) : (preCone F G c).pt = c.pt := (rfl)

@[simp]
theorem preCone_π_app (c : Cone (G ⋙ fiberwiseLimit F)) (X : Grothendieck (G ⋙ C)) :
    (preCone F G c).π.app X =
      c.π.app X.base ≫ limit.π (Grothendieck.ι C (G.obj X.base) ⋙ F) X.fiber := (rfl)

/-- A cone on the total diagram restricted along `Grothendieck.pre C G` induces a cone on the
fiber limits restricted along `G`. -/
noncomputable abbrev coneOfPreCone (s : Cone (Grothendieck.pre C G ⋙ F)) :
    Cone (G ⋙ fiberwiseLimit F) where
  pt := s.pt
  π :=
    { app d' := limit.lift (Grothendieck.ι C (G.obj d') ⋙ F)
        { pt := s.pt
          π :=
            { app x := s.π.app ⟨d', x⟩
              naturality x y g := by
                let g' : (⟨d', x⟩ : Grothendieck (G ⋙ C)) ⟶ ⟨d', y⟩ :=
                  ⟨𝟙 d', eqToHom (by simp) ≫ g⟩
                have e : (Grothendieck.pre C G).map g' = (Grothendieck.ι C (G.obj d')).map g := by
                  fapply Grothendieck.ext
                  · simp [g']
                  · simp [g']
                    -- Mathlib's `Grothendieck.ι` has no simp lemmas; its `map g` is
                    -- `⟨𝟙 _, eqToHom _ ≫ g⟩` by definition.
                    rfl
                -- `erw` unfolds the composite diagram and the fiber inclusion in the
                -- source of this identity morphism.
                erw [Category.id_comp (obj := V)]
                rw [Functor.comp_map, ← e]
                exact (s.w g').symm } }
      naturality d₁ d₂ h := by
        -- `erw` unfolds `(G ⋙ fiberwiseLimit F).obj` to the chosen fiber limit.
        erw [Category.id_comp (obj := V)]
        apply (cancel_mono (limit.pre (Grothendieck.ι C (G.obj d₂) ⋙ F)
          (C.map (G.map h)).toFunctor)).mp
        apply limit.hom_ext
        intro x
        simp only [Category.assoc (obj := V), Functor.comp_map,
          limit.pre_π, map_π, limit.lift_π_assoc, limit.lift_π]
        exact (s.w ((Grothendieck.ιNatTrans (F := G ⋙ C) h).app x)).symm }

@[simp]
theorem coneOfPreCone_pt (s : Cone (Grothendieck.pre C G ⋙ F)) :
    (coneOfPreCone F G s).pt = s.pt := (rfl)

/-- Each fiber component of the induced cone projects to the original cone's legs. -/
@[reassoc]
theorem coneOfPreCone_π_app_π (s : Cone (Grothendieck.pre C G ⋙ F)) (d' : D')
    (x : C.obj (G.obj d')) :
    (coneOfPreCone F G s).π.app d' ≫ limit.π (Grothendieck.ι C (G.obj d') ⋙ F) x =
      s.π.app ⟨d', x⟩ :=
  limit.lift_π _ _

/-- A limiting cone on the fiber limits restricted along `G` gives a limiting cone on the total
diagram restricted along `Grothendieck.pre C G`. -/
noncomputable def isLimitPreCone {c : Cone (G ⋙ fiberwiseLimit F)} (hc : IsLimit c) :
    IsLimit (preCone F G c) where
  lift s := hc.lift (coneOfPreCone F G s)
  fac s X := by
    -- `erw` identifies the objects of `G ⋙ fiberwiseLimit F` and `pre C G ⋙ F`
    -- with the fiber limits and total-diagram objects used by these projection lemmas.
    erw [preCone_π_app, hc.fac_assoc, coneOfPreCone_π_app_π]
  uniq s m hm := by
    apply hc.uniq (coneOfPreCone F G s) m
    intro d'
    apply limit.hom_ext
    intro x
    -- `erw` unfolds `(G ⋙ fiberwiseLimit F).obj d'` to reassociate at the fiber limit.
    erw [Category.assoc (obj := V), coneOfPreCone_π_app_π]
    exact hm ⟨d', x⟩

/-- A limiting cone on the total diagram restricted along `Grothendieck.pre C G` gives a limiting
cone on the fiber limits restricted along `G`. -/
noncomputable def isLimitConeOfPreCone {s : Cone (Grothendieck.pre C G ⋙ F)} (hs : IsLimit s) :
    IsLimit (coneOfPreCone F G s) where
  lift c := hs.lift (preCone F G c)
  fac c d' := by
    apply limit.hom_ext
    intro x
    rw [Category.assoc, coneOfPreCone_π_app_π]
    exact hs.fac (preCone F G c) ⟨d', x⟩
  uniq c m hm := by
    apply hs.uniq (preCone F G c) m
    rintro ⟨d', x⟩
    rw [preCone_π_app, ← hm d', Category.assoc]
    exact (m ≫= coneOfPreCone_π_app_π F G s d' x).symm

end Pre

/-- A cone on the total diagram induces a cone on its fiber limits. This is
`coneOfPreCone` along the identity of the base. -/
noncomputable abbrev coneOfCone (c : Cone F) : Cone (fiberwiseLimit F) :=
  coneOfPreCone F (𝟭 D) c

@[simp]
theorem coneOfCone_pt (c : Cone F) : (coneOfCone F c).pt = c.pt := (rfl)

/-- The component of `coneOfCone` at a base object is the lift of the whiskered cone. It is not
a simp lemma: simp unfolds the reducible `coneOfCone` itself. -/
theorem coneOfCone_π_app (c : Cone F) (d : D) :
    (coneOfCone F c).π.app d = limit.lift _ (c.whisker (Grothendieck.ι C d)) := (rfl)

/-- A cone on the fiber limits induces a cone on the total diagram. This is `preCone` along
the identity of the base. -/
noncomputable abbrev totalCone (c : Cone (fiberwiseLimit F)) : Cone F :=
  preCone F (𝟭 D) c

@[simp]
theorem totalCone_pt (c : Cone (fiberwiseLimit F)) : (totalCone F c).pt = c.pt := (rfl)

@[simp]
theorem totalCone_π_app (c : Cone (fiberwiseLimit F)) (X : Grothendieck C) :
    (totalCone F c).π.app X =
      c.π.app X.base ≫ limit.π (Grothendieck.ι C X.base ⋙ F) X.fiber := (rfl)

/-- A limiting cone on the fiber limits gives a limiting cone on the total diagram. -/
noncomputable def isLimitTotalCone {c : Cone (fiberwiseLimit F)} (hc : IsLimit c) :
    IsLimit (totalCone F c) :=
  isLimitPreCone F (𝟭 D) hc

/-- A limiting cone on the total diagram gives a limiting cone on the fiber limits. -/
noncomputable def isLimitConeOfCone {c : Cone F} (hc : IsLimit c) :
    IsLimit (coneOfCone F c) :=
  isLimitConeOfPreCone F (𝟭 D) hc

end FiberwiseLimit

/-- Existence of a limit is equivalent to existence of the iterated fiberwise limit. -/
theorem hasLimit_fiberwiseLimit_iff : HasLimit (fiberwiseLimit F) ↔ HasLimit F := by
  constructor
  · intro h
    exact ⟨⟨_, FiberwiseLimit.isLimitTotalCone F (limit.isLimit _)⟩⟩
  · intro h
    exact ⟨⟨_, FiberwiseLimit.isLimitConeOfCone F (limit.isLimit _)⟩⟩

/-- Taking the total limit agrees with first taking limits on fibers and then on the base. -/
noncomputable def limitFiberwiseLimitIso [HasLimit F] [HasLimit (fiberwiseLimit F)] :
    limit F ≅ limit (fiberwiseLimit F) :=
  (limit.isLimit F).conePointUniqueUpToIso
    (FiberwiseLimit.isLimitTotalCone F (limit.isLimit _))

/-- The comparison to the iterated limit preserves every fiber projection. -/
@[reassoc (attr := simp)]
theorem limitFiberwiseLimitIso_hom_π [HasLimit F] [HasLimit (fiberwiseLimit F)]
    (d : D) (x : C.obj d) :
    (limitFiberwiseLimitIso F).hom ≫ limit.π (fiberwiseLimit F) d ≫
        limit.π (Grothendieck.ι C d ⋙ F) x = limit.π F ⟨d, x⟩ := by
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ (⟨d, x⟩ : Grothendieck C)

/-- The inverse comparison computes the projection at every object of the total category. -/
@[reassoc (attr := simp)]
theorem limitFiberwiseLimitIso_inv_π [HasLimit F] [HasLimit (fiberwiseLimit F)]
    (X : Grothendieck C) :
    (limitFiberwiseLimitIso F).inv ≫ limit.π F X =
      limit.π (fiberwiseLimit F) X.base ≫
        limit.π (Grothendieck.ι C X.base ⋙ F) X.fiber := by
  exact IsLimit.conePointUniqueUpToIso_inv_comp _ _ X

section Naturality

variable {F} {G H : Grothendieck C ⥤ V}
  [∀ d, HasLimit (Grothendieck.ι C d ⋙ G)]
  [∀ {d e} (f : d ⟶ e), HasLimit ((C.map f).toFunctor ⋙ (Grothendieck.ι C e ⋙ G))]
  [∀ {d e} (f : d ⟶ e), IsIso (limit.pre (Grothendieck.ι C e ⋙ G) (C.map f).toFunctor)]
  [∀ d, HasLimit (Grothendieck.ι C d ⋙ H)]
  [∀ {d e} (f : d ⟶ e), HasLimit ((C.map f).toFunctor ⋙ (Grothendieck.ι C e ⋙ H))]
  [∀ {d e} (f : d ⟶ e), IsIso (limit.pre (Grothendieck.ι C e ⋙ H) (C.map f).toFunctor)]

/-- A transformation of total diagrams induces a transformation of their fiber limits. -/
noncomputable def fiberwiseLimitMap (α : F ⟶ G) : fiberwiseLimit F ⟶ fiberwiseLimit G where
  app d := limMap (whiskerLeft (Grothendieck.ι C d) α)
  naturality d e f := by
    apply (cancel_mono (limit.pre (Grothendieck.ι C e ⋙ G) (C.map f).toFunctor)).mp
    apply limit.hom_ext
    intro x
    dsimp only [fiberwiseLimit]
    simp only [Category.assoc (obj := V), limit.pre_π]
    erw [limMap_π, FiberwiseLimit.map_π_assoc, FiberwiseLimit.map_π, limMap_π_assoc]
    exact congrArg (fun t => limit.π (Grothendieck.ι C d ⋙ F) x ≫ t)
      (α.naturality ((Grothendieck.ιNatTrans f).app x))

@[simp]
theorem fiberwiseLimitMap_app (α : F ⟶ G) (d : D) :
    (fiberwiseLimitMap α).app d = limMap (whiskerLeft (Grothendieck.ι C d) α) := (rfl)

/-- Fiberwise limits preserve identity transformations. -/
@[simp]
theorem fiberwiseLimitMap_id : fiberwiseLimitMap (𝟙 F) = 𝟙 (fiberwiseLimit F) := by
  apply NatTrans.ext
  funext d
  apply limit.hom_ext
  intro x
  simp [Category.id_comp (obj := V)]

/-- Fiberwise limits preserve composition of transformations. -/
@[simp]
theorem fiberwiseLimitMap_comp (α : F ⟶ G) (β : G ⟶ H) :
    fiberwiseLimitMap (α ≫ β) = fiberwiseLimitMap α ≫ fiberwiseLimitMap β := by
  apply NatTrans.ext
  funext d
  apply limit.hom_ext
  intro x
  simp [Category.assoc (obj := V)]

/-- The total-to-iterated limit comparison is natural in the total diagram. -/
@[reassoc]
theorem limitFiberwiseLimitIso_naturality (α : F ⟶ G)
    [HasLimit F] [HasLimit G] [HasLimit (fiberwiseLimit F)] [HasLimit (fiberwiseLimit G)] :
    limMap α ≫ (limitFiberwiseLimitIso G).hom =
      (limitFiberwiseLimitIso F).hom ≫ limMap (fiberwiseLimitMap α) := by
  apply limit.hom_ext
  intro d
  apply limit.hom_ext
  intro x
  simp only [Category.assoc (obj := V), limMap_π, fiberwiseLimitMap_app]
  rw [limitFiberwiseLimitIso_hom_π]
  erw [limMap_π α (⟨d, x⟩ : Grothendieck C), limitFiberwiseLimitIso_hom_π_assoc]
  rfl

end Naturality

section Pre

variable {D' : Type u''} [Category.{v''} D'] (G : D' ⥤ D)

/-- Existence of a limit of the fiberwise diagram restricted along `G` is equivalent to existence
of a limit of the total diagram restricted along `Grothendieck.pre C G`. -/
theorem hasLimit_comp_fiberwiseLimit_iff :
    HasLimit (G ⋙ fiberwiseLimit F) ↔ HasLimit (Grothendieck.pre C G ⋙ F) :=
  ⟨fun _ => ⟨⟨_, FiberwiseLimit.isLimitPreCone F G (limit.isLimit _)⟩⟩,
    fun _ => ⟨⟨_, FiberwiseLimit.isLimitConeOfPreCone F G (limit.isLimit _)⟩⟩⟩

/-- Restriction along `Grothendieck.pre C G` preserves existence of limits when `G` is initial. -/
instance hasLimit_grothendieckPre_comp [G.Initial] [HasLimit F] :
    HasLimit (Grothendieck.pre C G ⋙ F) := by
  have := (hasLimit_fiberwiseLimit_iff F).mpr ‹_›
  exact (hasLimit_comp_fiberwiseLimit_iff F G).mp inferInstance

/-- Restriction along `Grothendieck.pre C G` is an isomorphism of limits when `G` is initial.
No initiality of the transition functors is needed, only invertibility of the restrictions of
fiber limits along them. -/
instance isIso_limit_pre_grothendieckPre [G.Initial] [HasLimit F] :
    IsIso (limit.pre F (Grothendieck.pre C G)) := by
  have := (hasLimit_fiberwiseLimit_iff F).mpr ‹_›
  have h : limit.pre F (Grothendieck.pre C G) = (limitFiberwiseLimitIso F).hom ≫
      limit.pre (fiberwiseLimit F) G ≫ ((FiberwiseLimit.isLimitPreCone F G
        (limit.isLimit _)).conePointUniqueUpToIso (limit.isLimit _)).hom := by
    apply limit.hom_ext
    intro X
    rw [limit.pre_π, Category.assoc, Category.assoc, limit.conePointUniqueUpToIso_hom_comp]
    -- The leg of `preCone` at `X` is a fiber projection at `(Grothendieck.pre C G).obj X`, which
    -- is `⟨G.obj X.base, X.fiber⟩` by definition, so `exact` matches it with
    -- `limitFiberwiseLimitIso_hom_π`.
    exact (((limitFiberwiseLimitIso F).hom ≫= limit.pre_π_assoc _ _ _ _).trans
      (limitFiberwiseLimitIso_hom_π F _ _)).symm
  rw [h]
  infer_instance

end Pre

end CategoryTheory.Limits
