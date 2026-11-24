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
public import TauCeti.CategoryTheory.Action.Smooth
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
* `ContAction.point G`: the forgetful functor as a point of the site.
* `ContAction.stalk G`: the stalk of a presheaf at this point, as a `G`-set.
* `ContAction.homPresheaf G`: the presheaf of `G`-maps into a `G`-set.
* `ContAction.sheafEquiv G`: for compact `G`, sheaves of sets on finite continuous `G`-sets are
  equivalent to smooth `G`-sets (`Action.SmoothSet G`, from
  `TauCeti.CategoryTheory.Action.Smooth`).

## Main results

* `ContAction.mem_jointlySurjectiveTopology_iff`,
  `ContAction.ofArrows_mem_jointlySurjectiveTopology_iff`: the covering sieves and families are
  the jointly surjective ones.
* `ContAction.isSheaf_homPresheaf`: `G`-maps into a `G`-set form a sheaf.

## References

* [A. Grothendieck, M. Artin, J.-L. Verdier, *SGA 4*, Exposé IV, 2.7 and Exposé VIII, 2]
-/

public section

open CategoryTheory Limits Opposite PreGaloisCategory FintypeCatDiscrete

universe u

namespace ContAction

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

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

/-- The forgetful functor is a point of the jointly surjective topology. -/
noncomputable abbrev point : (jointlySurjectiveTopology G).Point where
  fiber := fiberFunctor G
  isCofiltered := Functor.isCofiltered_elements _
  initiallySmall := initiallySmall_of_essentiallySmall _
  jointly_surjective R hR s := by
    obtain ⟨T, f, hf, t, rfl⟩ := mem_jointlySurjectiveTopology_iff.1 hR s
    exact ⟨T, f, hf, t, rfl⟩

/-- An element `g : G` acts on the point `point G` by translation. -/
@[expose, simps]
def pointSMul (g : G) : point G ⟶ point G where
  hom :=
    { app S := TypeCat.ofHom fun (s : (fiberFunctor G).obj S) ↦ g • s
      naturality S T f := by ext s; exact (fiberFunctor_map_smul f g s).symm }

variable {G}

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
@[expose, simps]
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
@[simp]
theorem smul_germ (P : (ContAction FintypeCat.{u} G)ᵒᵖ ⥤ Type u)
    (S : ContAction FintypeCat.{u} G) (s : (fiberFunctor G).obj S) (z : P.obj (op S)) (g : G) :
    g • germ P S s z = germ P S (g • s) z := by
  -- By definition of `stalk`, `g` acts on the stalk by the map of fibres that the translation
  -- `pointSMul G g` induces.
  change (pointSMul G g).presheafFiber.app P ((point G).toPresheafFiber S s P z) = _
  exact ConcreteCategory.congr_hom ((point G).toPresheafFiber_presheafFiberDesc (P := P) _ _ S s) z

/-- Germs are compatible with restriction. -/
theorem germ_map (P : (ContAction FintypeCat.{u} G)ᵒᵖ ⥤ Type u)
    {S T : ContAction FintypeCat.{u} G} (f : S ⟶ T) (s : (fiberFunctor G).obj S)
    (z : P.obj (op T)) :
    germ P S s (P.map f.op z) = germ P T ((fiberFunctor G).map f s) z :=
  (point G).toPresheafFiber_w_apply f s P z

/-- The stalk of a presheaf is a smooth `G`-set. -/
theorem isSmooth_stalk (P : (ContAction FintypeCat.{u} G)ᵒᵖ ⥤ Type u) :
    Action.isSmooth G ((stalk G).obj P) := by
  refine (Action.isSmooth_iff _).2 fun p ↦ ?_
  obtain ⟨S, s, z, rfl⟩ := (point G).toPresheafFiber_jointly_surjective (P := P) p
  refine Subgroup.isOpen_mono (fun g hg ↦ MulAction.mem_stabilizer_iff.2 ?_)
    (isOpen_stabilizer S s)
  rw [smul_germ, MulAction.mem_stabilizer_iff.1 hg]

variable (G)

/-- The presheaf of `G`-maps from finite continuous `G`-sets into a fixed `G`-set. -/
@[expose]
def homPresheaf : Action (Type u) G ⥤ (ContAction FintypeCat.{u} G)ᵒᵖ ⥤ Type u where
  obj X :=
    { obj S := (fiberFunctor G).obj S.unop →[G] X.V
      map f := TypeCat.ofHom fun φ ↦ φ.comp (fiberHom f.unop)
      map_id _ := rfl
      map_comp _ _ := rfl }
  map f := { app S := TypeCat.ofHom fun φ ↦ f.toMulActionHom.comp φ }
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
  (rfl)

omit [IsTopologicalGroup G] in
/-- A morphism of `G`-sets acts on `G`-maps into its source by postcomposition. -/
theorem homPresheafObjEquiv_map_app {X Y : Action (Type u) G} (f : X ⟶ Y)
    (S : ContAction FintypeCat.{u} G) (φ : ((homPresheaf G).obj X).obj (op S))
    (s : (fiberFunctor G).obj S) :
    homPresheafObjEquiv Y S (((homPresheaf G).map f).app (op S) φ) s =
      f.hom (homPresheafObjEquiv X S φ s) :=
  (rfl)

omit [IsTopologicalGroup G] in
/-- Sections of `(homPresheaf G).obj X` are determined by their values. -/
theorem homPresheafObj_ext {X : Action (Type u) G} {S : ContAction FintypeCat.{u} G}
    {φ ψ : ((homPresheaf G).obj X).obj (op S)}
    (h : ∀ s, homPresheafObjEquiv X S φ s = homPresheafObjEquiv X S ψ s) : φ = ψ :=
  (homPresheafObjEquiv X S).injective (MulActionHom.ext h)

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
    (fun S s ↦ TypeCat.ofHom fun φ ↦ homPresheafObjEquiv X S φ s) (fun _ _ _ _ ↦ rfl)

/-- Evaluating the germ at `s` of a `G`-map `φ` gives `φ s`. -/
@[simp]
theorem evalStalk_germ (X : Action (Type u) G) (S : ContAction FintypeCat.{u} G)
    (s : (fiberFunctor G).obj S) (φ : ((homPresheaf G).obj X).obj (op S)) :
    evalStalk X (germ _ S s φ) = homPresheafObjEquiv X S φ s :=
  ConcreteCategory.congr_hom ((point G).toPresheafFiber_presheafFiberDesc
    (P := (homPresheaf G).obj X)
    (fun S s ↦ TypeCat.ofHom fun φ ↦ homPresheafObjEquiv X S φ s) (fun _ _ _ _ ↦ rfl) S s) φ

/-- Evaluation of germs is `G`-equivariant. -/
theorem evalStalk_smul (X : Action (Type u) G) (g : G)
    (p : ((stalk G).obj ((homPresheaf G).obj X)).V) :
    evalStalk X (g • p) = g • evalStalk X p := by
  obtain ⟨S, s, φ, rfl⟩ :=
    (point G).toPresheafFiber_jointly_surjective (P := (homPresheaf G).obj X) p
  rw [smul_germ, evalStalk_germ, evalStalk_germ, map_smul]

/-- Evaluation of germs as a morphism of `G`-sets. -/
noncomputable def evalAction (X : Action (Type u) G) :
    (stalk G).obj ((homPresheaf G).obj X) ⟶ X where
  hom := evalStalk X
  comm g := by ext p; exact evalStalk_smul X g p

/-- The underlying map of `evalAction X` is evaluation of germs. -/
@[simp]
theorem evalAction_hom (X : Action (Type u) G) : (evalAction X).hom = evalStalk X :=
  (rfl)

variable (G)

/-- The `G`-equivariant germs of a section of a presheaf. -/
noncomputable def germHom (P : (ContAction FintypeCat.{u} G)ᵒᵖ ⥤ Type u)
    (S : ContAction FintypeCat.{u} G) (z : P.obj (op S)) :
    (fiberFunctor G).obj S →[G] ((stalk G).obj P).V where
  toFun s := germ P S s z
  map_smul' g s := (smul_germ P S s z g).symm

variable {G}

/-- `germHom G P S z` sends a point to the germ of `z` there. -/
theorem germHom_apply (P : (ContAction FintypeCat.{u} G)ᵒᵖ ⥤ Type u)
    (S : ContAction FintypeCat.{u} G) (z : P.obj (op S)) (s : (fiberFunctor G).obj S) :
    germHom G P S z s = germ P S s z :=
  (rfl)

variable (G)

/-- A presheaf maps to the presheaf of `G`-maps into its stalk, by taking germs. -/
noncomputable def germNatTrans :
    𝟭 ((ContAction FintypeCat.{u} G)ᵒᵖ ⥤ Type u) ⟶ stalk G ⋙ homPresheaf G where
  app P :=
    { app S := TypeCat.ofHom fun z ↦ (homPresheafObjEquiv _ S.unop).symm (germHom G P S.unop z)
      naturality S T f := by
        ext z
        exact homPresheafObj_ext fun s ↦ germ_map P f.unop s z }
  naturality P Q f := by
    ext S z
    exact homPresheafObj_ext fun s ↦
      ((point G).toPresheafFiber_naturality_apply f S.unop s z).symm

variable {G}

/-- The section of `G`-maps into the stalk given by a section of a presheaf sends a point to the
germ of the section there. -/
theorem homPresheafObjEquiv_germNatTrans_app_app (P : (ContAction FintypeCat.{u} G)ᵒᵖ ⥤ Type u)
    (S : (ContAction FintypeCat.{u} G)ᵒᵖ) (z : P.obj S) :
    homPresheafObjEquiv _ S.unop (((germNatTrans G).app P).app S z) = germHom G P S.unop z :=
  (rfl)

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
  -- `(fiberFunctor G).map` applies `(forget₂ _ FintypeCat).map`, in which `hq` is stated.
  have hpa s : (fiberFunctor G).map (p s) (a s) = s := by
    change (forget₂ _ FintypeCat.{u}).map prod.fst
      ((forget₂ _ FintypeCat.{u}).map (q s) (a s)) = s
    rw [hq, fiberBinaryProductEquiv_symm_fst_apply]
  have hpt s : (fiberFunctor G).map (q s ≫ prod.snd) (a s) = t s := by
    change (forget₂ _ FintypeCat.{u}).map prod.snd
      ((forget₂ _ FintypeCat.{u}).map (q s) (a s)) = t s
    rw [hq, fiberBinaryProductEquiv_symm_snd_apply]
  have hd s b : germ P.obj (A s) b (d s) = φ ((fiberFunctor G).map (p s) b) := by
    refine congr($(mulActionHom_ext_of_isConnected (φ := germHom G P.obj (A s) (d s))
      (ψ := φ.comp (fiberHom (p s))) (a s) ?_) b)
    rw [germHom_apply, MulActionHom.comp_apply, fiberHom_apply, hpa, hd_def, germ_map, hpt]
    exact hc s
  have hR : Sieve.ofArrows A p ∈ jointlySurjectiveTopology G S :=
    mem_jointlySurjectiveTopology_iff.2 fun s ↦ ⟨A s, p s, Sieve.ofArrows_mk _ _ s, a s, hpa s⟩
  obtain ⟨z, hz, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1
    (((isSheaf_iff_isSheaf_of_type _ _).1 P.property).isSheafFor _ hR) d
    fun i j Z gi gj h ↦ germ_ext P fun y ↦ by
      rw [germ_map, germ_map, hd, hd]
      exact congrArg φ congr((fiberFunctor G).map $h y)
  refine ⟨z, MulActionHom.ext fun s ↦ ?_⟩
  rw [germHom_apply, ← hpa s, ← germ_map, hz, hd]

variable (G)

/-- Sheaves on finite continuous `G`-sets give smooth `G`-sets, by taking the stalk. -/
@[expose]
noncomputable def fromSheaf :
    Sheaf (jointlySurjectiveTopology G) (Type u) ⥤ Action.SmoothSet G :=
  ObjectProperty.lift _ (sheafToPresheaf _ _ ⋙ stalk G) fun P ↦ isSmooth_stalk P.obj

/-- Smooth `G`-sets give sheaves on finite continuous `G`-sets, by taking `G`-maps into them. -/
@[expose]
noncomputable def toSheaf : Action.SmoothSet G ⥤ Sheaf (jointlySurjectiveTopology G) (Type u) :=
  ObjectProperty.lift _ ((Action.isSmooth G).ι ⋙ homPresheaf G) fun X ↦ isSheaf_homPresheaf X.obj

variable {G}

/-- The `G`-set underlying `(fromSheaf G).obj P` is the stalk of `P`. -/
@[simp]
theorem fromSheaf_obj_obj (P : Sheaf (jointlySurjectiveTopology G) (Type u)) :
    ((fromSheaf G).obj P).obj = (stalk G).obj P.obj :=
  (rfl)

/-- The presheaf underlying `(toSheaf G).obj X` is the presheaf of `G`-maps into `X`. -/
@[simp]
theorem toSheaf_obj_obj (X : Action.SmoothSet G) :
    ((toSheaf G).obj X).obj = (homPresheaf G).obj X.obj :=
  (rfl)

variable (G)

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
    -- `toSheaf G ⋙ fromSheaf G` sends `f` to the map of stalks induced by postcomposition.
    change evalStalk Y.obj ((point G).presheafFiber.map ((homPresheaf G).map f.hom)
      (germ _ S s φ)) = f.hom.hom (evalStalk X.obj (germ _ S s φ))
    rw [GrothendieckTopology.Point.toPresheafFiber_naturality_apply, evalStalk_germ,
      evalStalk_germ, homPresheafObjEquiv_map_app]

variable {G}

/-- The unit of `sheafEquiv` at a sheaf `P` takes germs of sections of `P`. -/
@[simp]
theorem sheafEquivUnit_app_hom (P : Sheaf (jointlySurjectiveTopology G) (Type u)) :
    ((sheafEquivUnit G).app P).hom = (germNatTrans G).app P.obj :=
  (rfl)

/-- The counit of `sheafEquiv` at a smooth `G`-set `X` evaluates germs. -/
@[simp]
theorem sheafEquivCounit_app_hom (X : Action.SmoothSet G) :
    ((sheafEquivCounit G).app X).hom = evalAction X.obj :=
  (rfl)

variable (G)

instance instIsIsoSheafEquivUnit : IsIso (sheafEquivUnit G) := by
  have (P : Sheaf (jointlySurjectiveTopology G) (Type u)) : IsIso ((sheafEquivUnit G).app P) := by
    have (S : (ContAction FintypeCat.{u} G)ᵒᵖ) : IsIso (((germNatTrans G).app P.obj).app S) :=
      (isIso_iff_bijective _).2 ⟨fun z₁ z₂ h ↦ germ_ext P fun s ↦ by
        have := congr(homPresheafObjEquiv _ _ $h s)
        rwa [homPresheafObjEquiv_germNatTrans_app_app, homPresheafObjEquiv_germNatTrans_app_app,
          germHom_apply, germHom_apply] at this, germHom_surjective P S.unop⟩
    have : IsIso ((germNatTrans G).app P.obj) := NatIso.isIso_of_isIso_app _
    have : IsIso ((ObjectProperty.ι _).map ((sheafEquivUnit G).app P)) := by
      rw [ObjectProperty.ι_map, sheafEquivUnit_app_hom]
      exact this
    exact (ObjectProperty.fullyFaithfulι _).isIso_of_isIso_map ((sheafEquivUnit G).app P)
  exact NatIso.isIso_of_isIso_app _

variable {G}

variable [CompactSpace G]

/-- The orbit of a point of a smooth `G`-set, as a finite continuous `G`-set. -/
@[expose]
noncomputable def orbitObj {X : Action (Type u) G} (hX : Action.isSmooth G X) (x : X.V) :
    ContAction FintypeCat.{u} G :=
  have := hX.finite_orbit x
  have := Fintype.ofFinite (MulAction.orbit G x)
  ⟨Action.FintypeCat.ofMulAction G (FintypeCat.of (MulAction.orbit G x)),
    (Action.isContinuous_iff_isOpen_stabilizer _).2 fun y ↦ by
      convert (Action.isSmooth_iff X).1 hX y.val using 2
      ext g
      exact Subtype.ext_iff⟩

/-- The inclusion of an orbit, as a `G`-map. -/
def orbitHom {X : Action (Type u) G} (hX : Action.isSmooth G X) (x : X.V) :
    (fiberFunctor G).obj (orbitObj hX x) →[G] X.V where
  toFun y := (y : MulAction.orbit G x).val
  map_smul' _ _ := rfl

/-- `orbitHom hX x` sends a point of the orbit of `x` to itself. -/
theorem orbitHom_apply {X : Action (Type u) G} (hX : Action.isSmooth G X) (x : X.V)
    (y : (fiberFunctor G).obj (orbitObj hX x)) :
    orbitHom hX x y = (y : MulAction.orbit G x).val :=
  (rfl)

/-- For compact `G`, the stalk of `G`-maps into a smooth `G`-set `X` is `X`. -/
theorem evalStalk_bijective {X : Action (Type u) G} (hX : Action.isSmooth G X) :
    Function.Bijective (evalStalk X) := by
  refine ⟨fun p₁ p₂ h ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨S, s, φ₁, φ₂, rfl, rfl⟩ :=
      (point G).toPresheafFiber_jointly_surjective₂ (P := (homPresheaf G).obj X) p₁ p₂
    rw [evalStalk_germ, evalStalk_germ] at h
    refine ((point G).toPresheafFiber_eq_iff' S s φ₁ φ₂).2 ?_
    obtain ⟨A, f, a, hA, rfl⟩ :=
      exists_hom_from_galois_of_fiber (forget₂ (ContAction FintypeCat.{u} G) FintypeCat.{u}) S s
    refine ⟨A, f, a, rfl, homPresheafObj_ext fun b ↦ ?_⟩
    simp only [homPresheafObjEquiv_map]
    exact congr($(mulActionHom_ext_of_isConnected
      (φ := (homPresheafObjEquiv X S φ₁).comp (fiberHom f))
      (ψ := (homPresheafObjEquiv X S φ₂).comp (fiberHom f)) a h) b)
  · refine ⟨germ _ (orbitObj hX x) ⟨x, MulAction.mem_orbit_self x⟩
      ((homPresheafObjEquiv X _).symm (orbitHom hX x)), ?_⟩
    refine (evalStalk_germ _ _ _ _).trans ?_
    simp only [Equiv.apply_symm_apply]
    exact orbitHom_apply hX x _

variable (G)

instance instIsIsoSheafEquivCounit : IsIso (sheafEquivCounit G) := by
  have (X : Action.SmoothSet G) : IsIso ((sheafEquivCounit G).app X) := by
    have : IsIso (evalAction X.obj).hom := by
      rw [evalAction_hom, isIso_iff_bijective]
      exact evalStalk_bijective X.property
    have : IsIso ((Action.isSmooth G).ι.map ((sheafEquivCounit G).app X)) := by
      rw [ObjectProperty.ι_map, sheafEquivCounit_app_hom]
      exact Action.isIso_of_hom_isIso (evalAction X.obj)
    exact (ObjectProperty.fullyFaithfulι _).isIso_of_isIso_map ((sheafEquivCounit G).app X)
  exact NatIso.isIso_of_isIso_app _

/-- **Sheaves on finite continuous `G`-sets are smooth `G`-sets.** For a compact group `G`,
sheaves of sets on the site of finite continuous `G`-sets with the jointly surjective topology
are equivalent to sets with a `G`-action whose stabilizers are open. -/
noncomputable def sheafEquiv :
    Sheaf (jointlySurjectiveTopology G) (Type u) ≌ Action.SmoothSet G :=
  .mk (fromSheaf G) (toSheaf G) (asIso (sheafEquivUnit G)) (asIso (sheafEquivCounit G))

/-- The functor of `sheafEquiv` takes stalks. -/
@[simp]
theorem sheafEquiv_functor : (sheafEquiv G).functor = fromSheaf G :=
  (rfl)

/-- The inverse of `sheafEquiv` takes `G`-maps into a smooth `G`-set. -/
@[simp]
theorem sheafEquiv_inverse : (sheafEquiv G).inverse = toSheaf G :=
  (rfl)

end ContAction
