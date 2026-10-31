/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Algebra.RegularFunctions
public import TauCeti.AlgebraicGeometry.Modules.GlobalSections
public import TauCeti.AlgebraicGeometry.RelativeSpec.Basic

/-!
# Functoriality of the algebra of regular functions

A scheme `p : V ⟶ X` over `X` has a commutative `𝒪ₓ`-algebra of regular functions, carried by
the actual pushforward `p_* 𝒪_V` (`AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebra`).
This file makes that algebra contravariantly functorial in schemes over `X`: a morphism
`g : V ⟶ W` over `X` pulls back regular functions, giving a morphism of `𝒪ₓ`-algebras
`q_* 𝒪_W ⟶ p_* 𝒪_V`.

The morphism of algebras is the pushforward along `q` of the unit `𝒪_W ⟶ g_* 𝒪_V` of the
function algebra of `g`, transported along the identification `q_* g_* ≅ (g ≫ q)_* = p_*` of lax
monoidal functors, using Mathlib's `Functor.mapCommMon` and `Functor.mapCommMonNatTrans`. The
comparison `f_* (q_* 𝒪_T) ≅ (q ≫ f)_* 𝒪_T` of function algebras over two bases, through which
relative spectra over `Y` and over `X` are related under base change, is natural in `T`.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebraMap g h`: the morphism of function
  algebras `q_* 𝒪_W ⟶ p_* 𝒪_V` induced by `g : V ⟶ W` with `h : g ≫ q = p`;
* `AlgebraicGeometry.Scheme.Hom.sectionsAlgHom_pushforwardStructureAlgebraMap_apply`: on
  sections over `U`, it is the map `Γ(W, q⁻¹ U) ⟶ Γ(V, p⁻¹ U)` induced by `g`;
* `AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebraΓRingEquiv_symm_sectionsAlgHom`:
  on global sections, it is `g.appTop : Γ(W, ⊤) ⟶ Γ(V, ⊤)`;
* `AlgebraicGeometry.Scheme.Hom.freeHomPushforwardEquiv_comp`: the description of module maps
  from a free sheaf to `q_* 𝒪_W` as families of global functions on `W` is natural in `W`;
* `AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebraMap_id` and
  `AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebraMap_comp`: functoriality;
* `AlgebraicGeometry.Scheme.Hom.globalSectionsSmul_pushforwardStructureAlgebraMap`: it is linear
  over global functions, multiplication by `c` on `q_* 𝒪_W` matching multiplication by `g^♯ c` on
  `p_* 𝒪_V`;
* `AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebraCompIso_hom_naturality`: the
  comparison `f_* (q_* 𝒪_T) ≅ (q ≫ f)_* 𝒪_T` of function algebras is natural in `T`;
* `TauCeti.AlgebraicGeometry.overFunctions X`: the function-algebra functor `q ↦ q_* 𝒪_T` on all
  schemes over `X`.

## References

* The Stacks Project, [Tag 01LL](https://stacks.math.columbia.edu/tag/01LL) (relative
  spectrum).
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique II*, §1.3.
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace TauCeti

universe u

noncomputable section

variable {X V W : Scheme.{u}} {p : V ⟶ X} {q : W ⟶ X}

/-- The morphism of function algebras `q_* 𝒪_W ⟶ p_* 𝒪_V` induced by a morphism `g : V ⟶ W` of
schemes over `X`: pullback of regular functions along `g`. It is the pushforward along `q` of
the unit `𝒪_W ⟶ g_* 𝒪_V` of the function algebra of `g`, followed by the identification
`q_* g_* ≅ (g ≫ q)_* = p_*` of lax monoidal functors. -/
def _root_.AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebraMap (g : V ⟶ W)
    (h : g ≫ q = p) : q.pushforwardStructureAlgebra ⟶ p.pushforwardStructureAlgebra :=
  (Scheme.Modules.pushforward q).mapCommMon.map
      (default : CommMon.trivial W.Modules ⟶ g.pushforwardStructureAlgebra) ≫
    Functor.mapCommMonCompIso.inv.app (CommMon.trivial V.Modules) ≫
    (Functor.mapCommMonNatTrans (Scheme.Modules.pushforwardComp g q).hom).app _ ≫
    (Functor.mapCommMonNatTrans (Scheme.Modules.pushforwardCongr h).hom).app _

/-- As a morphism of modules, the morphism of function algebras induced by `g` is the
pushforward along `q` of the map `𝒪_W ⟶ g_* 𝒪_V` given by `g` on sections, followed by the
identification `q_* g_* ≅ (g ≫ q)_* = p_*`. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebraMap_hom (g : V ⟶ W)
    (h : g ≫ q = p) :
    (Scheme.Hom.pushforwardStructureAlgebraMap g h).hom.hom =
      (Scheme.Modules.pushforward q).map
          (SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom) ≫
        (Scheme.Modules.pushforwardComp g q).hom.app _ ≫
          (Scheme.Modules.pushforwardCongr h).hom.app _ := by
  unfold Scheme.Hom.pushforwardStructureAlgebraMap Scheme.Hom.pushforwardStructureAlgebra
  simp only [CommMon.comp_hom, Functor.mapCommMonNatTrans_app_hom_hom,
    Functor.mapCommMonCompIso_inv_app_hom_hom]
  exact congrArg (· ≫ _)
    ((Scheme.Modules.pushforward q).congr_map (Scheme.Hom.pushforwardStructureAlgebra_one g))

/-- On sections over an open `U` of the base, the morphism of function algebras induced by `g`
is the pullback `Γ(W, q⁻¹ U) ⟶ Γ(V, p⁻¹ U)` of regular functions along `g`. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.sectionsAlgHom_pushforwardStructureAlgebraMap_apply
    (g : V ⟶ W) (h : g ≫ q = p) (U : X.Opens) (x : Γ(q.pushforwardStructureAlgebra.X, U)) :
    CommMon.sectionsAlgHom (Scheme.Hom.pushforwardStructureAlgebraMap g h) U x =
      (p.pushforwardStructureAlgebraSectionsRingEquiv U).symm
        (g.appLE (q ⁻¹ᵁ U) (p ⁻¹ᵁ U) (by subst h; exact le_rfl)
          (q.pushforwardStructureAlgebraSectionsRingEquiv U x)) := by
  rw [Scheme.Hom.pushforwardStructureAlgebraSectionsRingEquiv_apply,
    Scheme.Hom.pushforwardStructureAlgebraSectionsRingEquiv_symm_apply,
    CommMon.sectionsAlgHom_apply, Scheme.Hom.pushforwardStructureAlgebraMap_hom]
  -- On sections over `U`, `pushforwardComp` is the identity, `pushforwardCongr` is the
  -- restriction `Γ(V, (g ≫ q)⁻¹ U) ⟶ Γ(V, p⁻¹ U)` of the structure sheaf, and
  -- `unitToPushforwardObjUnit` is `g.app (q⁻¹ U)`; their composite is `appLE` by definition.
  rfl

/-- On global sections, the morphism of function algebras induced by `g : V ⟶ W` over `X` is the
pullback `Γ(W, ⊤) ⟶ Γ(V, ⊤)` of global functions along `g`. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebraΓRingEquiv_symm_sectionsAlgHom
    (g : V ⟶ W) (h : g ≫ q = p) (x : Γ(q.pushforwardStructureAlgebra.X, ⊤)) :
    p.pushforwardStructureAlgebraΓRingEquiv.symm
        (CommMon.sectionsAlgHom (Scheme.Hom.pushforwardStructureAlgebraMap g h) ⊤ x) =
      g.appTop (q.pushforwardStructureAlgebraΓRingEquiv.symm x) := by
  subst h
  rw [Scheme.Hom.pushforwardStructureAlgebraΓRingEquiv_symm_apply,
    Scheme.Hom.pushforwardStructureAlgebraΓRingEquiv_symm_apply,
    Scheme.Hom.sectionsAlgHom_pushforwardStructureAlgebraMap_apply, RingEquiv.apply_symm_apply,
    ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.appLE, CommRingCat.comp_apply]
  exact (ConcreteCategory.congr_hom
    (g.naturality (homOfLE (by simp : (⊤ : W.Opens) ≤ q ⁻¹ᵁ ⊤)).op) _).symm

/-- The bijection `Scheme.Hom.freeHomPushforwardEquiv` is natural in the scheme over `X`:
composing a module map with pullback of regular functions along `g : V ⟶ W` pulls back its family
of global functions along `g`. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.freeHomPushforwardEquiv_comp (g : V ⟶ W)
    (h : g ≫ q = p) (I : Type u) (φ : SheafOfModules.free (R := X.ringCatSheaf) I ⟶
      (Scheme.Modules.pushforward q).obj (𝟙_ W.Modules)) :
    p.freeHomPushforwardEquiv I (φ ≫ (Scheme.Hom.pushforwardStructureAlgebraMap g h).hom.hom) =
      g.appTop ∘ q.freeHomPushforwardEquiv I φ :=
  -- By `SheafOfModules.freeHomEquiv_comp_apply`, the global section of `φ ≫ ψ` at a basis
  -- element is the image under `ψ` of that of `φ`.
  funext fun i ↦ (p.freeHomPushforwardEquiv_apply I _ i).trans <|
    ((congrArg (Scheme.Hom.pushforwardStructureAlgebraΓRingEquiv p).symm
      (CommMon.sectionsAlgHom_apply (Scheme.Hom.pushforwardStructureAlgebraMap g h) ⊤
        ((SheafOfModules.freeHomEquiv _ φ i).val (Opposite.op ⊤))).symm).trans
      (Scheme.Hom.pushforwardStructureAlgebraΓRingEquiv_symm_sectionsAlgHom g h _)).trans
    (congrArg g.appTop (q.freeHomPushforwardEquiv_apply I φ i).symm)

/-- The identity of a scheme over `X` induces the identity of its function algebra. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebraMap_id :
    Scheme.Hom.pushforwardStructureAlgebraMap (𝟙 V) (Category.id_comp p) = 𝟙 _ := by
  refine CommMon.hom_ext_of_sectionsAlgHom fun U ↦ AlgHom.ext fun x ↦ ?_
  have hid : Scheme.Hom.appLE (𝟙 V) (p ⁻¹ᵁ U) (p ⁻¹ᵁ U) le_rfl = 𝟙 _ :=
    (Scheme.Hom.appLE_eq_app (𝟙 V)).trans (Scheme.Hom.id_app (p ⁻¹ᵁ U))
  simp only [Scheme.Hom.sectionsAlgHom_pushforwardStructureAlgebraMap_apply, hid,
    CommMon.sectionsAlgHom_id, AlgHom.id_apply, CommRingCat.id_apply, RingEquiv.symm_apply_apply]

variable {V' : Scheme.{u}} {p' : V' ⟶ X}

/-- Pullback of regular functions is contravariantly functorial in morphisms over `X`. -/
lemma _root_.AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebraMap_comp (g : V' ⟶ V)
    (g' : V ⟶ W) (h : g ≫ p = p') (h' : g' ≫ q = p) :
    Scheme.Hom.pushforwardStructureAlgebraMap (g ≫ g') (by rw [Category.assoc, h', h]) =
      Scheme.Hom.pushforwardStructureAlgebraMap g' h' ≫
        Scheme.Hom.pushforwardStructureAlgebraMap g h := by
  refine CommMon.hom_ext_of_sectionsAlgHom fun U ↦ AlgHom.ext fun x ↦ ?_
  simp only [CommMon.sectionsAlgHom_comp, AlgHom.comp_apply,
    Scheme.Hom.sectionsAlgHom_pushforwardStructureAlgebraMap_apply, RingEquiv.apply_symm_apply]
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

/-- Pullback of regular functions along `g : V ⟶ W` over `X` is linear over the global functions
of `W`: multiplying a function on `W` by `c` and then pulling back is pulling back and then
multiplying by `g^♯ c`. -/
@[reassoc]
lemma _root_.AlgebraicGeometry.Scheme.Hom.globalSectionsSmul_pushforwardStructureAlgebraMap
    (g : V ⟶ W) (h : g ≫ q = p) (c : Γ(W, ⊤)) :
    (Scheme.Modules.pushforward q).map (Scheme.Modules.globalSectionsSmul (𝟙_ W.Modules) c) ≫
        (Scheme.Hom.pushforwardStructureAlgebraMap g h).hom.hom =
      (Scheme.Hom.pushforwardStructureAlgebraMap g h).hom.hom ≫
        (Scheme.Modules.pushforward p).map
          (Scheme.Modules.globalSectionsSmul (𝟙_ V.Modules) (g.appTop c)) := by
  -- `g^♯ : 𝒪_W ⟶ g_* 𝒪_V` is linear over `Γ(W, ⊤)`, where `c` acts on `g_* 𝒪_V` through
  -- `g^♯ c`; `u` types `g^♯` in `W.Modules`, whose unit `𝟙_` is `SheafOfModules.unit`, so that
  -- the composites below are formed there rather than in the category of sheaves of modules
  let u : 𝟙_ W.Modules ⟶ (Scheme.Modules.pushforward g).obj (𝟙_ V.Modules) :=
    SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom
  have h₁ : (Scheme.Modules.pushforward q).map
        (Scheme.Modules.globalSectionsSmul (𝟙_ W.Modules) c) ≫
          (Scheme.Modules.pushforward q).map u =
      (Scheme.Modules.pushforward q).map u ≫
        (Scheme.Modules.pushforward q).map ((Scheme.Modules.pushforward g).map
          (Scheme.Modules.globalSectionsSmul (𝟙_ V.Modules) (g.appTop c))) := by
    rw [← Functor.map_comp, ← Functor.map_comp, Scheme.Modules.pushforward_map_globalSectionsSmul,
      Scheme.Modules.globalSectionsSmul_naturality]
  -- then `q_* g_* ≅ (g ≫ q)_* = p_*` is natural
  have h₂ := (Scheme.Modules.pushforwardComp g q).hom.naturality
    (Scheme.Modules.globalSectionsSmul (𝟙_ V.Modules) (g.appTop c))
  have h₃ := (Scheme.Modules.pushforwardCongr h).hom.naturality
    (Scheme.Modules.globalSectionsSmul (𝟙_ V.Modules) (g.appTop c))
  rw [Scheme.Hom.pushforwardStructureAlgebraMap_hom]
  exact ((reassoc_of% h₁) _).trans (congrArg (_ ≫ ·) (((reassoc_of% h₂) _).trans
    (congrArg (_ ≫ ·) h₃)))

variable {Y T T' : Scheme.{u}}

/-- The comparison `f_* (q_* 𝒪_T) ≅ (q ≫ f)_* 𝒪_T` is natural in the scheme `T` over `Y`: it
intertwines the pushforward along `f` of pullback of regular functions along `g : T' ⟶ T` with
pullback of regular functions along `g` over `X`. -/
@[reassoc]
lemma _root_.AlgebraicGeometry.Scheme.Hom.pushforwardStructureAlgebraCompIso_hom_naturality
    {q : T ⟶ Y} {q' : T' ⟶ Y} (f : Y ⟶ X) (g : T' ⟶ T) (hg : g ≫ q = q') :
    (Scheme.Modules.pushforward f).mapCommMon.map
          (Scheme.Hom.pushforwardStructureAlgebraMap g hg) ≫
        (q'.pushforwardStructureAlgebraCompIso f).hom =
      (q.pushforwardStructureAlgebraCompIso f).hom ≫
        Scheme.Hom.pushforwardStructureAlgebraMap g (by rw [← Category.assoc, hg]) := by
  subst hg
  apply CommMon.hom_ext
  apply Scheme.Modules.hom_ext
  intro U
  simp only [CommMon.comp_hom, Functor.mapCommMon_map_hom_hom,
    Scheme.Hom.pushforwardStructureAlgebraCompIso_hom_hom_hom,
    Scheme.Hom.pushforwardStructureAlgebraMap_hom]
  -- On sections over `U`, `pushforwardComp` and `pushforwardCongr` are identities and both
  -- sides are `g.app` on `(g ≫ q ≫ f)⁻¹ U`; `simp` cannot split the composites because they
  -- mix the `X.Modules` and underlying sheaf category instances.
  rfl

end

end TauCeti

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

/-- The function-algebra functor on all schemes over `X`: `q : T ⟶ X` goes to its algebra of
regular functions `q_* 𝒪_T`, and a morphism over `X` goes to pullback of regular functions along
it. -/
@[expose]
def overFunctions (X : Scheme.{u}) : (Over X)ᵒᵖ ⥤ CommMon X.Modules where
  obj T := T.unop.hom.pushforwardStructureAlgebra
  map g := Scheme.Hom.pushforwardStructureAlgebraMap g.unop.left (Over.w g.unop)
  map_id _ := Scheme.Hom.pushforwardStructureAlgebraMap_id
  map_comp g g' := Scheme.Hom.pushforwardStructureAlgebraMap_comp g'.unop.left g.unop.left
    (Over.w g'.unop) (Over.w g.unop)

/-- The function algebra of `q : T ⟶ X` is `q_* 𝒪_T`. -/
@[simp]
lemma overFunctions_obj {X : Scheme.{u}} (T : (Over X)ᵒᵖ) :
    (overFunctions X).obj T = T.unop.hom.pushforwardStructureAlgebra :=
  (rfl)

/-- A morphism over `X` acts on function algebras by pullback of regular functions. -/
@[simp]
lemma overFunctions_map {X : Scheme.{u}} {T T' : (Over X)ᵒᵖ} (g : T ⟶ T') :
    (overFunctions X).map g =
      Scheme.Hom.pushforwardStructureAlgebraMap g.unop.left (Over.w g.unop) :=
  (rfl)

end

end TauCeti.AlgebraicGeometry
