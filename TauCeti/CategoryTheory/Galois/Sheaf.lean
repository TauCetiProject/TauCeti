/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.TypeValuedFlat
public import Mathlib.CategoryTheory.Sites.JointlySurjective
public import Mathlib.CategoryTheory.Sites.Point.Category
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import TauCeti.CategoryTheory.Action.EssentiallySmall
public import TauCeti.CategoryTheory.Galois.ContAction

/-!
# Sheaves on finite continuous `G`-sets

Let `G` be a topological group. The finite continuous `G`-sets `ContAction FintypeCat G` carry the
*jointly surjective* topology `ContAction.jointlySurjectiveTopology G`, whose covering families are
the families of `G`-maps that are jointly surjective on underlying sets. This file shows that, for
compact `G` (for instance a profinite Galois group), sheaves of sets for this topology are the
same as sets with a `G`-action whose stabilizers are open, the continuous `G`-actions on discrete
sets (`ContAction.sheafEquiv`).

The forgetful functor is a point of the site (`ContAction.point`) in the sense of
`CategoryTheory.GrothendieckTopology.Point`, and `G` acts on it by translation. The equivalence
sends a sheaf to its stalk at this point with the induced `G`-action (`ContAction.fromSheaf`),
and a `G`-set `X` to the sheaf of `G`-maps into `X` (`ContAction.toSheaf`). The germ maps
identify a sheaf with `G`-maps into its stalk: separation and gluing are checked on Galois
objects, on whose underlying set `G` acts transitively. Evaluation of germs identifies the stalk
of `G`-maps into `X` with `X`: every point of `X` lies in a finite orbit, which is a finite
continuous `G`-set because `G` is compact and stabilizers are open.

## Main definitions

* `ContAction.jointlySurjectiveTopology G`: the jointly surjective topology on finite continuous
  `G`-sets.
* `ContAction.isSmooth G`, `ContAction.SmoothSet G`: `G`-sets whose stabilizers are open, and
  their category.
* `ContAction.point G`: the forgetful functor as a point of the site.
* `ContAction.stalk G`: the stalk of a presheaf at this point, as a `G`-set.
* `ContAction.homPresheaf G`: the presheaf of `G`-maps into a `G`-set.
* `ContAction.sheafEquiv G`: for compact `G`, sheaves of sets on finite continuous `G`-sets are
  equivalent to smooth `G`-sets.

## Main results

* `ContAction.mem_jointlySurjectiveTopology_iff`,
  `ContAction.ofArrows_mem_jointlySurjectiveTopology_iff`: the covering sieves and families are
  the jointly surjective ones.
* `ContAction.isSheaf_homPresheaf`: `G`-maps into a `G`-set form a sheaf.

## References

* [A. Grothendieck, M. Artin, J.-L. Verdier, *SGA 4*, Exposé IV, 2.7 and Exposé VIII, 2]
-/

@[expose] public section

open CategoryTheory Limits Opposite PreGaloisCategory FintypeCatDiscrete

universe u

namespace ContAction

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The underlying set of a finite continuous `G`-set, as a functor to types. -/
abbrev fiberFunctor : ContAction FintypeCat.{u} G ⥤ Type u :=
  forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u} ⋙ FintypeCat.incl

/-- `G` acts on the underlying set of a finite continuous `G`-set. -/
instance instMulActionFiberFunctorObj (S : ContAction FintypeCat.{u} G) :
    MulAction G ((fiberFunctor G).obj S) :=
  inferInstanceAs (MulAction G S.obj.V)

/-- The jointly surjective topology on finite continuous `G`-sets: its covering sieves are
those whose maps are jointly surjective on underlying sets. -/
noncomputable abbrev jointlySurjectiveTopology :
    GrothendieckTopology (ContAction FintypeCat.{u} G) :=
  (Types.jointlySurjectivePrecoverage.comap (fiberFunctor G)).toGrothendieck

variable {G}

/-- A sieve covers for the jointly surjective topology exactly when its maps are jointly
surjective on underlying sets. -/
theorem mem_jointlySurjectiveTopology_iff {S : ContAction FintypeCat.{u} G} {R : Sieve S} :
    R ∈ jointlySurjectiveTopology G S ↔
      ∀ s : (fiberFunctor G).obj S, ∃ (T : ContAction FintypeCat.{u} G) (f : T ⟶ S),
        R f ∧ s ∈ Set.range ((fiberFunctor G).map f) := by
  have : (Types.jointlySurjectivePrecoverage.comap (fiberFunctor G)).IsStableUnderBaseChange :=
    isStableUnderBaseChange_comap_jointlySurjectivePrecoverage _ fun f g _ ↦
      (isIso_iff_bijective _).1 inferInstance |>.2
  rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition]
  refine ⟨fun ⟨R', hR', hle⟩ s ↦ ?_, fun h ↦ ⟨R.arrows, ?_, le_rfl⟩⟩
  · obtain ⟨T, f, hf, hs⟩ :=
      (Presieve.mem_comap_jointlySurjectivePrecoverage_iff _).1 hR' s
    exact ⟨T, f, hle _ _ hf, hs⟩
  · exact (Presieve.mem_comap_jointlySurjectivePrecoverage_iff _).2 h

/-- A family of maps generates a covering sieve for the jointly surjective topology exactly when
it is jointly surjective on underlying sets. -/
theorem ofArrows_mem_jointlySurjectiveTopology_iff {S : ContAction FintypeCat.{u} G} {ι : Type*}
    {T : ι → ContAction FintypeCat.{u} G} {f : ∀ i, T i ⟶ S} :
    Sieve.ofArrows T f ∈ jointlySurjectiveTopology G S ↔
      ∀ s : (fiberFunctor G).obj S, ∃ i, s ∈ Set.range ((fiberFunctor G).map (f i)) := by
  rw [mem_jointlySurjectiveTopology_iff]
  refine ⟨fun h s ↦ ?_, fun h s ↦ ?_⟩
  · obtain ⟨_, _, ⟨_, g, _, ⟨i⟩, rfl⟩, t, rfl⟩ := h s
    exact ⟨i, (fiberFunctor G).map g t, rfl⟩
  · obtain ⟨i, t, rfl⟩ := h s
    exact ⟨_, f i, Sieve.ofArrows_mk _ _ i, t, rfl⟩

variable (G)

/-- Finite types form an essentially small category. -/
instance instEssentiallySmallFintypeCat : EssentiallySmall.{u} FintypeCat.{u} :=
  .mk' FintypeCat.Skeleton.equivalence.symm

/-- Finite continuous `G`-sets form an essentially small category. -/
instance instEssentiallySmallIsContinuous :
    ObjectProperty.EssentiallySmall.{u} (Action.isContinuous FintypeCat.{u} G) :=
  .of_le (Q := ⊤) le_top

/-- The forgetful functor is a point of the jointly surjective topology. -/
noncomputable abbrev point : (jointlySurjectiveTopology G).Point where
  fiber := fiberFunctor G
  isCofiltered := Functor.isCofiltered_elements _
  initiallySmall := initiallySmall_of_essentiallySmall _
  jointly_surjective R hR s := by
    obtain ⟨T, f, hf, t, rfl⟩ := mem_jointlySurjectiveTopology_iff.1 hR s
    exact ⟨T, f, hf, t, rfl⟩

variable {G}

omit [IsTopologicalGroup G] in
/-- Morphisms of finite continuous `G`-sets are `G`-equivariant. -/
theorem fiberFunctor_map_smul {S T : ContAction FintypeCat.{u} G} (f : S ⟶ T) (g : G)
    (s : (fiberFunctor G).obj S) :
    (fiberFunctor G).map f (g • s) = g • (fiberFunctor G).map f s :=
  ConcreteCategory.congr_hom (f.hom.comm g) s

omit [IsTopologicalGroup G] in
/-- Stabilizers of points of a finite continuous `G`-set are open. -/
theorem isOpen_stabilizer (S : ContAction FintypeCat.{u} G) (s : (fiberFunctor G).obj S) :
    IsOpen (MulAction.stabilizer G s : Set G) :=
  have : DiscreteTopology ((forget₂ (Action FintypeCat.{u} G) TopCat).obj S.obj) := ⟨rfl⟩
  have : ContinuousSMul G ((forget₂ (Action FintypeCat.{u} G) TopCat).obj S.obj) := S.property
  stabilizer_isOpen G (X := (forget₂ (Action FintypeCat.{u} G) TopCat).obj S.obj) s

variable (G)

/-- An element `g : G` acts on the point `point G` by translation. -/
@[simps]
def pointSMul (g : G) : point G ⟶ point G where
  hom :=
    { app S := TypeCat.ofHom fun (s : (fiberFunctor G).obj S) ↦ g • s
      naturality S T f := by ext s; exact (fiberFunctor_map_smul f g s).symm }

variable {G}

/-- The action of `G` on the underlying set of a `G`-set. -/
instance instMulActionV (X : Action (Type u) G) : MulAction G X.V :=
  Action.instMulAction X

/-- The identity acts trivially on the point. -/
theorem pointSMul_one : pointSMul G 1 = 𝟙 _ := by
  ext S s
  exact one_smul G (s : (fiberFunctor G).obj S)

/-- The translations of the point compose as the group law. -/
theorem pointSMul_mul (g h : G) : pointSMul G (g * h) = pointSMul G g ≫ pointSMul G h := by
  ext S s
  exact mul_smul g h (s : (fiberFunctor G).obj S)

variable (G)

/-- The stalk of a presheaf at `point G`, with `G` acting by translating the point. -/
@[simps]
noncomputable def stalk : ((ContAction FintypeCat.{u} G)ᵒᵖ ⥤ Type u) ⥤ Action (Type u) G where
  obj P :=
    { V := (point G).presheafFiber.obj P
      ρ :=
        { toFun g := .of ((pointSMul G g).presheafFiber.app P)
          map_one' := by
            ext1; rw [pointSMul_one, GrothendieckTopology.Point.Hom.presheafFiber_id]; rfl
          map_mul' g h := by
            ext1; rw [pointSMul_mul, GrothendieckTopology.Point.Hom.presheafFiber_comp]; rfl } }
  map f :=
    { hom := (point G).presheafFiber.map f
      comm g := ((pointSMul G g).presheafFiber.naturality f).symm }

variable {G}

/-- The germ at `s` of a section `z` over `S`, as an element of the stalk. -/
noncomputable abbrev germ (P : (ContAction FintypeCat.{u} G)ᵒᵖ ⥤ Type u)
    (S : ContAction FintypeCat.{u} G) (s : (fiberFunctor G).obj S) (z : P.obj (op S)) :
    ((stalk G).obj P).V :=
  (point G).toPresheafFiber S s P z

/-- `G` acts on germs by translating the point. -/
theorem smul_germ (P : (ContAction FintypeCat.{u} G)ᵒᵖ ⥤ Type u)
    (S : ContAction FintypeCat.{u} G) (s : (fiberFunctor G).obj S) (z : P.obj (op S)) (g : G) :
    g • germ P S s z = germ P S (g • s) z := by
  change ((point G).toPresheafFiber S s P ≫ (pointSMul G g).presheafFiber.app P) z = _
  simp only [GrothendieckTopology.Point.Hom.presheafFiber_app,
    GrothendieckTopology.Point.toPresheafFiber_presheafFiberDesc]
  rfl

/-- Germs are compatible with restriction. -/
theorem germ_map (P : (ContAction FintypeCat.{u} G)ᵒᵖ ⥤ Type u)
    {S T : ContAction FintypeCat.{u} G} (f : S ⟶ T) (s : (fiberFunctor G).obj S)
    (z : P.obj (op T)) :
    germ P S s (P.map f.op z) = germ P T ((fiberFunctor G).map f s) z :=
  (point G).toPresheafFiber_w_apply f s P z

variable (G)

/-- A `G`-set is smooth when every stabilizer is open; for the discrete topology on the set,
this is continuity of the action (`continuousSMul_iff_stabilizer_isOpen`). -/
def isSmooth : ObjectProperty (Action (Type u) G) :=
  fun X ↦ ∀ x : X.V, IsOpen (MulAction.stabilizer G x : Set G)

/-- The category of smooth `G`-sets: sets with an action of `G` whose stabilizers are open. -/
abbrev SmoothSet : Type (u + 1) := (isSmooth G).FullSubcategory

variable {G}

/-- The stalk of a presheaf is a smooth `G`-set. -/
theorem isSmooth_stalk (P : (ContAction FintypeCat.{u} G)ᵒᵖ ⥤ Type u) :
    isSmooth G ((stalk G).obj P) := by
  intro p
  obtain ⟨S, s, z, rfl⟩ := (point G).toPresheafFiber_jointly_surjective (P := P) p
  refine Subgroup.isOpen_mono (fun g (hg : g • s = s) ↦ ?_) (isOpen_stabilizer S s)
  change g • germ P S s z = germ P S s z
  rw [smul_germ, hg]

/-- A morphism of finite continuous `G`-sets as a `G`-map of underlying sets. -/
def fiberHom {S T : ContAction FintypeCat.{u} G} (f : S ⟶ T) :
    (fiberFunctor G).obj S →[G] (fiberFunctor G).obj T where
  toFun := (fiberFunctor G).map f
  map_smul' := fiberFunctor_map_smul f

/-- A morphism of `G`-sets as a `G`-map. -/
def actionHom {X Y : Action (Type u) G} (f : X ⟶ Y) : X.V →[G] Y.V where
  toFun := f.hom
  map_smul' g x := ConcreteCategory.congr_hom (f.comm g) x

variable (G)

/-- The presheaf of `G`-maps from finite continuous `G`-sets into a fixed `G`-set. -/
@[simps]
def homPresheaf : Action (Type u) G ⥤ (ContAction FintypeCat.{u} G)ᵒᵖ ⥤ Type u where
  obj X :=
    { obj S := (fiberFunctor G).obj S.unop →[G] X.V
      map f := TypeCat.ofHom fun φ ↦ φ.comp (fiberHom f.unop)
      map_id _ := rfl
      map_comp _ _ := rfl }
  map f := { app S := TypeCat.ofHom fun φ ↦ (actionHom f).comp φ }
  map_id _ := rfl
  map_comp _ _ := rfl

variable {G}

/-- A section of `(homPresheaf G).obj X` over `S` is a `G`-map from `S` to `X`. -/
def homPresheafObjEquiv (X : Action (Type u) G) (S : ContAction FintypeCat.{u} G) :
    ((homPresheaf G).obj X).obj (op S) ≃ ((fiberFunctor G).obj S →[G] X.V) :=
  Equiv.refl _

omit [IsTopologicalGroup G] in
/-- Restriction of `G`-maps is precomposition. -/
theorem homPresheafObjEquiv_map (X : Action (Type u) G) {S T : ContAction FintypeCat.{u} G}
    (f : T ⟶ S) (φ : ((homPresheaf G).obj X).obj (op S)) (t : (fiberFunctor G).obj T) :
    homPresheafObjEquiv X T (((homPresheaf G).obj X).map f.op φ) t =
      homPresheafObjEquiv X S φ ((fiberFunctor G).map f t) :=
  rfl

omit [IsTopologicalGroup G] in
/-- Sections of `(homPresheaf G).obj X` are determined by their values. -/
theorem homPresheafObj_ext {X : Action (Type u) G} {S : ContAction FintypeCat.{u} G}
    {φ ψ : ((homPresheaf G).obj X).obj (op S)}
    (h : ∀ s, homPresheafObjEquiv X S φ s = homPresheafObjEquiv X S ψ s) : φ = ψ :=
  (homPresheafObjEquiv X S).injective (MulActionHom.ext h)

/-- The underlying set of a pullback of finite continuous `G`-sets is the fibre product. -/
theorem exists_fiberFunctor_pullback {S T₁ T₂ : ContAction FintypeCat.{u} G} (f₁ : T₁ ⟶ S)
    (f₂ : T₂ ⟶ S) (t₁ : (fiberFunctor G).obj T₁) (t₂ : (fiberFunctor G).obj T₂)
    (h : (fiberFunctor G).map f₁ t₁ = (fiberFunctor G).map f₂ t₂) :
    ∃ p : (fiberFunctor G).obj (pullback f₁ f₂),
      (fiberFunctor G).map (pullback.fst f₁ f₂) p = t₁ ∧
        (fiberFunctor G).map (pullback.snd f₁ f₂) p = t₂ :=
  ⟨(fiberPullbackEquiv (forget₂ _ FintypeCat.{u}) f₁ f₂).symm ⟨(t₁, t₂), h⟩,
    fiberPullbackEquiv_symm_fst_apply .., fiberPullbackEquiv_symm_snd_apply ..⟩

/-- `G`-maps into a fixed `G`-set form a sheaf for the jointly surjective topology. -/
theorem isSheaf_homPresheaf (X : Action (Type u) G) :
    Presheaf.IsSheaf (jointlySurjectiveTopology G) ((homPresheaf G).obj X) := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro S R hR x hx
  have key {T₁ T₂ : ContAction FintypeCat.{u} G} (f₁ : T₁ ⟶ S) (f₂ : T₂ ⟶ S) (h₁ : R f₁)
      (h₂ : R f₂) (t₁ : (fiberFunctor G).obj T₁) (t₂ : (fiberFunctor G).obj T₂)
      (h : (fiberFunctor G).map f₁ t₁ = (fiberFunctor G).map f₂ t₂) :
      homPresheafObjEquiv X T₁ (x f₁ h₁) t₁ = homPresheafObjEquiv X T₂ (x f₂ h₂) t₂ := by
    obtain ⟨p, hp₁, hp₂⟩ := exists_fiberFunctor_pullback f₁ f₂ t₁ t₂ h
    have := congr(homPresheafObjEquiv X _
      $(hx (pullback.fst f₁ f₂) (pullback.snd f₁ f₂) h₁ h₂ pullback.condition) p)
    rw [homPresheafObjEquiv_map, homPresheafObjEquiv_map, hp₁, hp₂] at this
    exact this
  choose T f hf ht using fun s ↦ mem_jointlySurjectiveTopology_iff.1 hR s
  choose t ht using ht
  let y s := homPresheafObjEquiv X (T s) (x (f s) (hf s))
  refine ⟨(homPresheafObjEquiv X S).symm ⟨fun s ↦ y s (t s), fun g s ↦ ?_⟩,
    fun T' f' hf' ↦ ?_, fun b hb ↦ ?_⟩
  · refine (key (f (g • s)) (f s) (hf _) (hf s) (t (g • s)) (g • t s) ?_).trans
      ((y s).map_smul g (t s))
    rw [ht, fiberFunctor_map_smul, ht]
  · refine homPresheafObj_ext fun t' ↦ ?_
    exact key (f _) f' (hf _) hf' (t _) t' (ht _)
  · refine homPresheafObj_ext fun s ↦ ?_
    have := congr(homPresheafObjEquiv X (T s) $(hb (f s) (hf s)) (t s))
    rw [homPresheafObjEquiv_map, ht] at this
    exact this

/-- Evaluation of germs of `G`-maps into `X` at the point. -/
noncomputable def evalStalk (X : Action (Type u) G) :
    ((stalk G).obj ((homPresheaf G).obj X)).V ⟶ X.V :=
  (point G).presheafFiberDesc
    (fun S s ↦ TypeCat.ofHom fun φ : (fiberFunctor G).obj S →[G] X.V ↦ φ s) (fun _ _ _ _ ↦ rfl)

/-- Evaluating the germ at `s` of a `G`-map `φ` gives `φ s`. -/
theorem evalStalk_germ (X : Action (Type u) G) (S : ContAction FintypeCat.{u} G)
    (s : (fiberFunctor G).obj S) (φ : ((homPresheaf G).obj X).obj (op S)) :
    evalStalk X (germ _ S s φ) = homPresheafObjEquiv X S φ s :=
  ConcreteCategory.congr_hom ((point G).toPresheafFiber_presheafFiberDesc
    (P := (homPresheaf G).obj X)
    (fun S s ↦ TypeCat.ofHom fun φ : (fiberFunctor G).obj S →[G] X.V ↦ φ s)
    (fun _ _ _ _ ↦ rfl) S s) φ

/-- Evaluation of germs is `G`-equivariant. -/
theorem evalStalk_smul (X : Action (Type u) G) (g : G)
    (p : ((stalk G).obj ((homPresheaf G).obj X)).V) :
    evalStalk X (g • p) = g • evalStalk X p := by
  obtain ⟨S, s, φ, rfl⟩ :=
    (point G).toPresheafFiber_jointly_surjective (P := (homPresheaf G).obj X) p
  exact (congrArg (evalStalk X) (smul_germ _ S s φ g)).trans
    ((evalStalk_germ X S (g • s) φ).trans (((homPresheafObjEquiv X S φ).map_smul
      g s).trans (congrArg (g • ·) (evalStalk_germ X S s φ).symm)))

/-- Evaluation of germs as a morphism of `G`-sets. -/
noncomputable def evalAction (X : Action (Type u) G) :
    (stalk G).obj ((homPresheaf G).obj X) ⟶ X where
  hom := evalStalk X
  comm g := by ext p; exact evalStalk_smul X g p

/-- An action on a finite set with open stabilizers is continuous. -/
theorem isContinuous_of_isOpen_stabilizer (X : Action FintypeCat.{u} G)
    (h : ∀ x : X.V, IsOpen (MulAction.stabilizer G x : Set G)) :
    Action.isContinuous FintypeCat G X := by
  have : DiscreteTopology ((forget₂ (Action FintypeCat.{u} G) TopCat).obj X) := ⟨rfl⟩
  exact (continuousSMul_iff_stabilizer_isOpen
    (X := (forget₂ (Action FintypeCat.{u} G) TopCat).obj X)).2 h

variable (G)

/-- The `G`-equivariant germs of a section of a presheaf. -/
noncomputable def germHom (P : (ContAction FintypeCat.{u} G)ᵒᵖ ⥤ Type u)
    (S : ContAction FintypeCat.{u} G) (z : P.obj (op S)) :
    (fiberFunctor G).obj S →[G] ((stalk G).obj P).V where
  toFun s := germ P S s z
  map_smul' g s := (smul_germ P S s z g).symm

/-- A presheaf maps to the presheaf of `G`-maps into its stalk, by taking germs. -/
noncomputable def germNatTrans :
    𝟭 ((ContAction FintypeCat.{u} G)ᵒᵖ ⥤ Type u) ⟶ stalk G ⋙ homPresheaf G where
  app P :=
    { app S := TypeCat.ofHom (germHom G P S.unop)
      naturality S T f := by
        ext z
        exact homPresheafObj_ext fun s ↦ germ_map P f.unop s z }
  naturality P Q f := by
    ext S z
    exact homPresheafObj_ext fun s ↦
      ((point G).toPresheafFiber_naturality_apply f S.unop s z).symm

variable {G}

/-- Sections of a sheaf are determined by their germs. -/
theorem germ_ext (P : Sheaf (jointlySurjectiveTopology G) (Type u))
    {S : ContAction FintypeCat.{u} G} {z₁ z₂ : P.obj.obj (op S)}
    (h : ∀ s, germ P.obj S s z₁ = germ P.obj S s z₂) : z₁ = z₂ := by
  choose T f t hft hz using fun s ↦
    ((point G).toPresheafFiber_eq_iff' (P := P.obj) S s z₁ z₂).1 (h s)
  have hR : Sieve.ofArrows T f ∈ jointlySurjectiveTopology G S :=
    mem_jointlySurjectiveTopology_iff.2 fun s ↦ ⟨T s, f s, Sieve.ofArrows_mk _ _ s, t s, hft s⟩
  exact (((isSheaf_iff_isSheaf_of_type _ _).1 P.property).isSheafFor _ hR).isSeparatedFor.ext
    fun _ _ ⟨s⟩ ↦ hz s

/-- Every `G`-map into the stalk of a sheaf is given by the germs of a section. -/
theorem germHom_surjective (P : Sheaf (jointlySurjectiveTopology G) (Type u))
    (S : ContAction FintypeCat.{u} G) : Function.Surjective (germHom G P.obj S) := by
  intro φ
  choose T t c hc using
    fun s ↦ (point G).toPresheafFiber_jointly_surjective (P := P.obj) (φ s)
  choose A q a hA hq using fun s ↦ exists_hom_from_galois_of_fiber
    (forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u}) (S ⨯ T s)
    ((fiberBinaryProductEquiv (forget₂ _ FintypeCat.{u}) S (T s)).symm (s, t s))
  let p s : A s ⟶ S := q s ≫ prod.fst
  obtain ⟨d, hd_def⟩ : ∃ d : ∀ s, P.obj.obj (op (A s)),
      ∀ s, d s = P.obj.map (q s ≫ prod.snd).op (c s) :=
    ⟨_, fun _ ↦ rfl⟩
  have hpa s : (fiberFunctor G).map (p s) (a s) = s := by
    change (forget₂ _ FintypeCat.{u}).map prod.fst
      ((forget₂ _ FintypeCat.{u}).map (q s) (a s)) = s
    rw [hq, fiberBinaryProductEquiv_symm_fst_apply]
  have hd s b : germ P.obj (A s) b (d s) = φ ((fiberFunctor G).map (p s) b) := by
    have : MulAction.IsPretransitive G
        ((forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u}).obj (A s)) :=
      isPretransitive_of_isConnected (A s)
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G (a s) b
    rw [← smul_germ, fiberFunctor_map_smul, map_smul, hpa, hd_def, germ_map]
    congr 1
    change germ P.obj (T s) ((forget₂ _ FintypeCat.{u}).map prod.snd
      ((forget₂ _ FintypeCat.{u}).map (q s) (a s))) (c s) = φ s
    rw [hq, fiberBinaryProductEquiv_symm_snd_apply]
    exact hc s
  have hR : Sieve.ofArrows A p ∈ jointlySurjectiveTopology G S :=
    mem_jointlySurjectiveTopology_iff.2 fun s ↦ ⟨A s, p s, Sieve.ofArrows_mk _ _ s, a s, hpa s⟩
  obtain ⟨z, hz, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1
    (((isSheaf_iff_isSheaf_of_type _ _).1 P.property).isSheafFor _ hR) d
    fun i j Z gi gj h ↦ germ_ext P fun y ↦ by
      rw [germ_map, germ_map, hd, hd]
      exact congrArg φ congr((fiberFunctor G).map $h y)
  refine ⟨z, ?_⟩
  ext s
  change germ P.obj S s z = φ s
  rw [← hpa s, ← germ_map, hz, hd]

variable (G)

/-- Sheaves on finite continuous `G`-sets give smooth `G`-sets, by taking the stalk. -/
noncomputable def fromSheaf : Sheaf (jointlySurjectiveTopology G) (Type u) ⥤ SmoothSet G :=
  ObjectProperty.lift _ (sheafToPresheaf _ _ ⋙ stalk G) fun P ↦ isSmooth_stalk P.obj

/-- Smooth `G`-sets give sheaves on finite continuous `G`-sets, by taking `G`-maps into them. -/
noncomputable def toSheaf : SmoothSet G ⥤ Sheaf (jointlySurjectiveTopology G) (Type u) :=
  ObjectProperty.lift _ ((isSmooth G).ι ⋙ homPresheaf G) fun X ↦ isSheaf_homPresheaf X.obj

/-- The unit of `sheafEquiv`: a sheaf maps to `G`-maps into its stalk. -/
noncomputable def sheafEquivUnit : 𝟭 _ ⟶ fromSheaf G ⋙ toSheaf G where
  app P := ObjectProperty.homMk ((germNatTrans G).app P.obj)
  naturality _ _ f := ObjectProperty.hom_ext _ ((germNatTrans G).naturality f.hom)

/-- The counit of `sheafEquiv`: evaluation of germs of `G`-maps into a smooth `G`-set. -/
noncomputable def sheafEquivCounit : toSheaf G ⋙ fromSheaf G ⟶ 𝟭 _ where
  app X := ObjectProperty.homMk (evalAction X.obj)
  naturality X Y f := by
    refine ObjectProperty.hom_ext _ (Action.hom_ext _ _ ?_)
    ext p
    obtain ⟨S, s, φ, rfl⟩ :=
      (point G).toPresheafFiber_jointly_surjective (P := (homPresheaf G).obj X.obj) p
    change evalStalk Y.obj ((point G).presheafFiber.map ((homPresheaf G).map f.hom)
      (germ _ S s φ)) = f.hom.hom (evalStalk X.obj (germ _ S s φ))
    rw [GrothendieckTopology.Point.toPresheafFiber_naturality_apply]
    exact (evalStalk_germ Y.obj S s _).trans
      (congrArg f.hom.hom (evalStalk_germ X.obj S s φ)).symm

instance instIsIsoSheafEquivUnit : IsIso (sheafEquivUnit G) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun P ↦ ?_
  have : IsIso ((germNatTrans G).app P.obj) := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun S ↦ ?_
    exact (isIso_iff_bijective _).2 ⟨fun z₁ z₂ h ↦ germ_ext P fun s ↦
      congr(homPresheafObjEquiv _ _ $h s), germHom_surjective P S.unop⟩
  have : IsIso ((ObjectProperty.ι _).map ((sheafEquivUnit G).app P)) := this
  exact (ObjectProperty.fullyFaithfulι _).isIso_of_isIso_map ((sheafEquivUnit G).app P)

variable {G}

variable [CompactSpace G]

/-- For compact `G`, orbits in a smooth `G`-set are finite. -/
theorem finite_orbit {X : Action (Type u) G} (hX : isSmooth G X) (x : X.V) :
    Finite (MulAction.orbit G x) :=
  have := Subgroup.quotient_finite_of_isOpen _ (hX x)
  (MulAction.orbitEquivQuotientStabilizer G x).finite_iff.2 this

/-- The orbit of a point of a smooth `G`-set, as a finite continuous `G`-set. -/
noncomputable def orbitObj {X : Action (Type u) G} (hX : isSmooth G X) (x : X.V) :
    ContAction FintypeCat.{u} G :=
  have := finite_orbit hX x
  have := Fintype.ofFinite (MulAction.orbit G x)
  ⟨Action.FintypeCat.ofMulAction G (FintypeCat.of (MulAction.orbit G x)),
    isContinuous_of_isOpen_stabilizer _ fun y ↦ by
      convert hX y.val using 2
      ext g
      exact Subtype.ext_iff⟩

/-- The inclusion of an orbit, as a `G`-map. -/
def orbitHom {X : Action (Type u) G} (hX : isSmooth G X) (x : X.V) :
    (fiberFunctor G).obj (orbitObj hX x) →[G] X.V where
  toFun y := (y : MulAction.orbit G x).val
  map_smul' _ _ := rfl

/-- For compact `G`, the stalk of `G`-maps into a smooth `G`-set `X` is `X`. -/
theorem evalStalk_bijective {X : Action (Type u) G} (hX : isSmooth G X) :
    Function.Bijective (evalStalk X) := by
  refine ⟨fun p₁ p₂ h ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨S, s, φ₁, φ₂, rfl, rfl⟩ :=
      (point G).toPresheafFiber_jointly_surjective₂ (P := (homPresheaf G).obj X) p₁ p₂
    replace h := (evalStalk_germ X S s φ₁).symm.trans (h.trans (evalStalk_germ X S s φ₂))
    refine ((point G).toPresheafFiber_eq_iff' S s φ₁ φ₂).2 ?_
    obtain ⟨A, f, a, hA, rfl⟩ :=
      exists_hom_from_galois_of_fiber (forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u}) S s
    refine ⟨A, f, a, rfl, ?_⟩
    have : MulAction.IsPretransitive G
        ((forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u}).obj A) :=
      isPretransitive_of_isConnected A
    refine homPresheafObj_ext fun b ↦ ?_
    obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G a b
    rw [homPresheafObjEquiv_map, homPresheafObjEquiv_map, fiberFunctor_map_smul, map_smul,
      map_smul]
    exact congrArg (g • ·) h
  · exact ⟨germ _ (orbitObj hX x) ⟨x, MulAction.mem_orbit_self x⟩ (orbitHom hX x),
      evalStalk_germ _ _ _ _⟩

variable (G)

instance instIsIsoSheafEquivCounit : IsIso (sheafEquivCounit G) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun X ↦ ?_
  have : IsIso (evalAction X.obj).hom :=
    (isIso_iff_bijective _).2 (evalStalk_bijective X.property)
  have : IsIso ((isSmooth G).ι.map ((sheafEquivCounit G).app X)) :=
    Action.isIso_of_hom_isIso (evalAction X.obj)
  exact (ObjectProperty.fullyFaithfulι _).isIso_of_isIso_map ((sheafEquivCounit G).app X)

/-- **Sheaves on finite continuous `G`-sets are smooth `G`-sets.** For a compact group `G`,
sheaves of sets on the site of finite continuous `G`-sets with the jointly surjective topology
are equivalent to sets with a `G`-action whose stabilizers are open. -/
noncomputable def sheafEquiv : Sheaf (jointlySurjectiveTopology G) (Type u) ≌ SmoothSet G :=
  .mk (fromSheaf G) (toSheaf G) (asIso (sheafEquivUnit G)) (asIso (sheafEquivCounit G))

end ContAction
