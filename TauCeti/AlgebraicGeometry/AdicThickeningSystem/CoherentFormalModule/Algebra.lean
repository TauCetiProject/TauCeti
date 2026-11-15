/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.Basic
public import TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.Monoidal
public import TauCeti.AlgebraicGeometry.RelativeSpec.PullbackAlgebra

/-!
# Descent of algebra morphisms from formal completions

Let `X` be a scheme, `I` an ideal sheaf on `X`, and `A` and `B` quasicoherent commutative
`𝒪_X`-algebras whose underlying `𝒪_X`-modules are finitely presented. Pulling `A` and `B` back
along the closed immersions `toScheme X I n : V(I ^ (n + 1)) ⟶ X` produces inverse systems of
quasicoherent algebras on the levels of the formal completion `X.formalCompletion I`, with
reduction isomorphisms `algebraTransitionIso X I A n` induced by `ι n ≫ toScheme X I (n + 1) =
toScheme X I n`.

When the completion functor `Scheme.formalCompletion.completionFunctor X I` on finitely presented
`𝒪_X`-modules is faithful (respectively fully faithful):

* **Faithfulness** (`algebra_hom_ext_of_faithful_completionFunctor`): two algebra morphisms
  `f, g : A ⟶ B` whose pullbacks to every infinitesimal neighbourhood `V(I ^ (n + 1))` agree are
  equal, since their underlying module morphisms have equal images under `completionFunctor X I`.
* **Fullness** (`existsUnique_algebra_hom_of_completionFunctor`, `descAlgebraOfCompletionFunctor`):
  every compatible family of algebra morphisms `φ n : toScheme n ^* A ⟶ toScheme n ^* B` across
  all levels `n` is the pullback family of a unique algebra morphism `f : A ⟶ B`. Fullness of
  `completionFunctor X I` lifts the compatible family of underlying module maps to a module map
  `ψ : A.obj.X ⟶ B.obj.X`, and faithfulness of `completionFunctor X I` applied to `𝟙_ X.Modules`
  and `A.obj.X ⊗ A.obj.X` (both finitely presented by `isFinitePresentation_unit` and
  `Scheme.Modules.isFinitePresentation_tensorObj`) shows that `ψ` preserves the unit and
  multiplication because all of its reductions `φ n` do.

This is the algebraic half of the formal comparison for finite étale covers (Stacks, Lemma 58.17.1
(Tag 0EL8)): once a morphism of finite étale covers over `V(I)` has been lifted to all
infinitesimal neighbourhoods `V(I ^ (n + 1))`, its pullback on finite-presentation coordinate
algebras descends to `X`.

## Main declarations

* `TauCeti.AlgebraicGeometry.QuasicoherentAlgebra.pullbackCongr`: congruence isomorphism for
  algebra pullback along equal scheme morphisms.
* `AlgebraicGeometry.Scheme.formalCompletion.algebraTransitionIso`: the canonical isomorphism
  `ι n ^* (toScheme (n + 1) ^* A) ≅ toScheme n ^* A` of pulled-back quasicoherent algebras.
* `AlgebraicGeometry.Scheme.formalCompletion.algebra_hom_ext_of_faithful_completionFunctor`:
  faithfulness of `completionFunctor X I` implies faithfulness on finitely presented quasicoherent
  algebras.
* `AlgebraicGeometry.Scheme.formalCompletion.existsUnique_algebra_hom_of_completionFunctor` and
  `AlgebraicGeometry.Scheme.formalCompletion.descAlgebraOfCompletionFunctor`: full faithfulness of
  `completionFunctor X I` algebraizes compatible families of algebra morphisms on `X/V(I)`.

## References

* [The Stacks Project, Lemma 58.17.1 (Tag 0EL8)](https://stacks.math.columbia.edu/tag/0EL8).
* [The Stacks Project, Section 30.23 (Tag 087W)](https://stacks.math.columbia.edu/tag/087W).
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry
open scoped MonObj

universe u

namespace TauCeti.AlgebraicGeometry.QuasicoherentAlgebra

/-- Equal scheme morphisms induce canonically isomorphic algebra pullback functors. -/
noncomputable def pullbackCongr {X Y : Scheme.{u}} {f f' : Y ⟶ X} (h : f = f') :
    pullback f ≅ pullback f' :=
  eqToIso (h ▸ rfl)

/-- On underlying modules, `pullbackCongr` is `Scheme.Modules.pullbackCongr`. -/
@[simp]
theorem pullbackCongr_hom_app_hom_hom_hom {X Y : Scheme.{u}} {f f' : Y ⟶ X} (h : f = f')
    (A : QuasicoherentAlgebra X) :
    ((pullbackCongr h).hom.app A).hom.hom.hom =
      eqToHom (pullback_obj_X f A) ≫ (Scheme.Modules.pullbackCongr h).hom.app A.obj.X ≫
        eqToHom (pullback_obj_X f' A).symm := by
  subst h
  -- At `rfl`, both congruence comparisons reduce to identity morphisms on the carrier.
  change 𝟙 _ = _
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp, eqToHom_trans, eqToHom_refl]
  rfl

/-- On underlying modules, the inverse of `pullbackCongr` is the inverse of
`Scheme.Modules.pullbackCongr`. -/
@[simp]
theorem pullbackCongr_inv_app_hom_hom_hom {X Y : Scheme.{u}} {f f' : Y ⟶ X} (h : f = f')
    (A : QuasicoherentAlgebra X) :
    ((pullbackCongr h).inv.app A).hom.hom.hom =
      eqToHom (pullback_obj_X f' A) ≫ (Scheme.Modules.pullbackCongr h).inv.app A.obj.X ≫
        eqToHom (pullback_obj_X f A).symm := by
  subst h
  -- As in `pullbackCongr_hom_app_hom_hom_hom`, both congruence comparisons are identities at `rfl`.
  change 𝟙 _ = _
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp, eqToHom_trans, eqToHom_refl]
  rfl

end TauCeti.AlgebraicGeometry.QuasicoherentAlgebra

namespace AlgebraicGeometry.Scheme.formalCompletion

open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.AdicThickeningSystem

section EqToHomHelpers

-- The carrier of `(QuasicoherentAlgebra.pullback f).obj A` mixes `Y.Modules` with the underlying
-- `SheafOfModules` category, so `rw` at `implicit` transparency rejects motives containing that
-- carrier. Isolating the `eqToHom` cancellations in an abstract category `C` lets us apply them as
-- typed terms at `default` transparency without unfolding `Modules.pullback`.

private lemma eq_eqToHom_conj_of_eq_symm_conj {C : Type*} [Category* C] {X₁ X₂ Y₁ Y₂ : C}
    (p : X₁ = X₂) (q : Y₁ = Y₂) {g : X₁ ⟶ Y₁} {m : X₂ ⟶ Y₂}
    (h : m = eqToHom p.symm ≫ g ≫ eqToHom q) :
    g = eqToHom p ≫ m ≫ eqToHom q.symm := by
  subst p q h
  simp

private lemma eqToHom_conj_comp {C : Type*} [Category* C] {X₁ X₂ Y₁ Y₂ Z₁ Z₂ : C}
    (p : X₁ = X₂) (q : Y₁ = Y₂) (r : Z₁ = Z₂) (u : X₂ ⟶ Y₂) (v : Y₂ ⟶ Z₂) :
    (eqToHom p ≫ u ≫ eqToHom q.symm) ≫ (eqToHom q ≫ v ≫ eqToHom r.symm) =
      eqToHom p ≫ (u ≫ v) ≫ eqToHom r.symm := by
  subst p q r
  simp

private lemma eq_of_eqToHom_conj_eq {C : Type*} [Category* C] {X₁ X₂ Y₁ Y₂ : C}
    (p : X₁ = X₂) (q : Y₁ = Y₂) {u v : X₂ ⟶ Y₂}
    (h : eqToHom p ≫ u ≫ eqToHom q.symm = eqToHom p ≫ v ≫ eqToHom q.symm) :
    u = v := by
  subst p q
  simpa using h

private lemma map_eqToHom_conj {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {X₁ X₂ Y₁ Y₂ : C} {W₁ Z₁ : D}
    (pX : W₁ = F.obj X₁) (hX : X₁ = X₂) (pY : Z₁ = F.obj Y₁) (hY : Y₁ = Y₂)
    {g : X₁ ⟶ Y₁} {m : X₂ ⟶ Y₂} (hg : g = eqToHom hX ≫ m ≫ eqToHom hY.symm) :
    eqToHom pX ≫ F.map g ≫ eqToHom pY.symm =
      eqToHom (pX.trans (congrArg F.obj hX)) ≫ F.map m ≫
        eqToHom (pY.trans (congrArg F.obj hY)).symm := by
  subst pX hX pY hY hg
  simp

private lemma unit_comp_of_eqToHom_conj {C : Type*} [Category* C] [MonoidalCategory C]
    {U A₁ A₂ B₁ B₂ : C} (pA : A₁ = A₂) (pB : B₁ = B₂) {v : 𝟙_ C ⟶ U} [Epi v]
    {η₁ : 𝟙_ C ⟶ A₁} {η₂ : 𝟙_ C ⟶ B₁} {uA : U ⟶ A₂} {uB : U ⟶ B₂}
    {g : A₁ ⟶ B₁} {m : A₂ ⟶ B₂}
    (hη₁ : η₁ = v ≫ uA ≫ eqToHom pA.symm) (hη₂ : η₂ = v ≫ uB ≫ eqToHom pB.symm)
    (hg : g = eqToHom pA ≫ m ≫ eqToHom pB.symm) (hone : η₁ ≫ g = η₂) :
    uA ≫ m = uB := by
  subst pA pB hη₁ hη₂ hg
  rw [← cancel_epi v]
  simpa using hone

private lemma mul_comp_of_eqToHom_conj {C : Type*} [Category* C] [MonoidalCategory C]
    {TA TB A₁ A₂ B₁ B₂ : C} (pA : A₁ = A₂) (pB : B₁ = B₂)
    {dA : A₂ ⊗ A₂ ⟶ TA} [Epi dA] {dB : B₂ ⊗ B₂ ⟶ TB}
    {μ₁ : A₁ ⊗ A₁ ⟶ A₁} {μ₂ : B₁ ⊗ B₁ ⟶ B₁}
    {mA : TA ⟶ A₂} {mB : TB ⟶ B₂}
    {g : A₁ ⟶ B₁} {m : A₂ ⟶ B₂} {m₂ : TA ⟶ TB}
    (hμ₁ : μ₁ = (eqToHom pA ⊗ₘ eqToHom pA) ≫ dA ≫ mA ≫ eqToHom pA.symm)
    (hμ₂ : μ₂ = (eqToHom pB ⊗ₘ eqToHom pB) ≫ dB ≫ mB ≫ eqToHom pB.symm)
    (hg : g = eqToHom pA ≫ m ≫ eqToHom pB.symm)
    (hd : (m ⊗ₘ m) ≫ dB = dA ≫ m₂)
    (hmul : μ₁ ≫ g = (g ⊗ₘ g) ≫ μ₂) :
    mA ≫ m = m₂ ≫ mB := by
  subst pA pB hμ₁ hμ₂ hg
  rw [← cancel_epi dA]
  have h : dA ≫ mA ≫ m = ((m ⊗ₘ m) ≫ dB) ≫ mB := by simpa using hmul
  exact h.trans (by rw [hd, Category.assoc])

end EqToHomHelpers

variable (X : Scheme.{u}) (I : X.IdealSheafData)

/-- The canonical reduction isomorphism `ι n ^* (toScheme (n + 1) ^* A) ≅ toScheme n ^* A` of the
system of quasicoherent algebras obtained by pulling `A` back to the levels of
`X.formalCompletion I`. -/
noncomputable def algebraTransitionIso (A : QuasicoherentAlgebra X) (n : ℕ) :
    (QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).obj
        ((QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).obj A) ≅
      (QuasicoherentAlgebra.pullback (toScheme X I n)).obj A :=
  (QuasicoherentAlgebra.pullbackComp ((X.formalCompletion I).ι n) (toScheme X I (n + 1)) ≪≫
    QuasicoherentAlgebra.pullbackCongr (ι_toScheme X I n)).app A

/-- On underlying modules, `algebraTransitionIso` is the reduction isomorphism of the coherent
formal module `(completionFunctor X I).obj ⟨A.obj.X, _⟩`, up to the carrier identifications of
`QuasicoherentAlgebra.pullback`. -/
theorem algebraTransitionIso_hom_hom_hom_hom (A : QuasicoherentAlgebra X)
    [A.obj.X.IsFinitePresentation] (n : ℕ) :
    ((algebraTransitionIso X I A n).hom).hom.hom.hom =
      eqToHom ((QuasicoherentAlgebra.pullback_obj_X _ _).trans
          (congrArg _ (QuasicoherentAlgebra.pullback_obj_X _ A))) ≫
        (((completionFunctor X I).obj ⟨A.obj.X, ‹_›⟩).transitionIso n).hom ≫
          eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A).symm := by
  let ιₙ := (X.formalCompletion I).ι n
  let i₁ := toScheme X I (n + 1)
  let i₀ := toScheme X I n
  have hcomp :
      ((algebraTransitionIso X I A n).hom).hom.hom.hom =
        ((QuasicoherentAlgebra.pullbackComp ιₙ i₁).hom.app A).hom.hom.hom ≫
          ((QuasicoherentAlgebra.pullbackCongr (ι_toScheme X I n)).hom.app A).hom.hom.hom := rfl
  exact hcomp.trans
    ((congrArg₂ (CategoryStruct.comp (obj := ((X.formalCompletion I).X n).Modules))
        (QuasicoherentAlgebra.pullbackComp_hom_app_hom_hom_hom ιₙ i₁ A)
        (QuasicoherentAlgebra.pullbackCongr_hom_app_hom_hom_hom (ι_toScheme X I n) A)).trans
      (eqToHom_conj_comp (C := ((X.formalCompletion I).X n).Modules)
        ((QuasicoherentAlgebra.pullback_obj_X ιₙ _).trans
          (congrArg _ (QuasicoherentAlgebra.pullback_obj_X i₁ A)))
        (QuasicoherentAlgebra.pullback_obj_X (ιₙ ≫ i₁) A)
        (QuasicoherentAlgebra.pullback_obj_X i₀ A)
        ((Modules.pullbackComp ιₙ i₁).hom.app A.obj.X)
        ((Modules.pullbackCongr (ι_toScheme X I n)).hom.app A.obj.X)))

/-- Pullback of an algebra morphism `f : A ⟶ B` to the levels of `X.formalCompletion I` commutes
with the reduction isomorphisms `algebraTransitionIso`. -/
@[reassoc (attr := simp)]
theorem pullback_map_algebraTransitionIso_hom {A B : QuasicoherentAlgebra X} (f : A ⟶ B) (n : ℕ) :
    (QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map
        ((QuasicoherentAlgebra.pullback (toScheme X I (n + 1))).map f) ≫
      (algebraTransitionIso X I B n).hom =
      (algebraTransitionIso X I A n).hom ≫
        (QuasicoherentAlgebra.pullback (toScheme X I n)).map f :=
  (QuasicoherentAlgebra.pullbackComp ((X.formalCompletion I).ι n) (toScheme X I (n + 1)) ≪≫
    QuasicoherentAlgebra.pullbackCongr (ι_toScheme X I n)).hom.naturality f

/-- **Faithfulness of completion on finitely presented quasicoherent algebras.** If the completion
functor on finitely presented `𝒪_X`-modules is faithful, then morphisms between quasicoherent
`𝒪_X`-algebras with finitely presented underlying modules are determined by their pullbacks to all
infinitesimal neighbourhoods `V(I ^ (n + 1))`. -/
theorem algebra_hom_ext_of_faithful_completionFunctor
    [(completionFunctor X I).Faithful] {A B : QuasicoherentAlgebra X}
    [A.obj.X.IsFinitePresentation] [B.obj.X.IsFinitePresentation] {f g : A ⟶ B}
    (h : ∀ n, (QuasicoherentAlgebra.pullback (toScheme X I n)).map f =
      (QuasicoherentAlgebra.pullback (toScheme X I n)).map g) :
    f = g := by
  apply ObjectProperty.hom_ext
  apply CommMon.hom_ext
  have hfp : (ObjectProperty.homMk f.hom.hom.hom :
      (⟨A.obj.X, ‹_›⟩ : FinitelyPresentedSheaf X) ⟶ ⟨B.obj.X, ‹_›⟩) =
      ObjectProperty.homMk g.hom.hom.hom := by
    apply (completionFunctor X I).map_injective
    refine CoherentFormalModule.hom_ext fun n ↦ ?_
    exact eq_of_eqToHom_conj_eq (C := ((X.formalCompletion I).X n).Modules)
      (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A)
      (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) B)
      ((QuasicoherentAlgebra.pullback_map_hom_hom_hom (toScheme X I n) f).symm.trans
        ((congrArg (fun k ↦ k.hom.hom.hom) (h n)).trans
          (QuasicoherentAlgebra.pullback_map_hom_hom_hom (toScheme X I n) g)))
  exact congrArg (fun k ↦ k.hom) hfp

/-- The underlying module map at level `n` of a family of algebra morphisms on
`X.formalCompletion I`, transported along `QuasicoherentAlgebra.pullback_obj_X`. -/
private noncomputable abbrev algebraFamilyAppModuleHom
    {A B : QuasicoherentAlgebra X}
    (φ : ∀ n, (QuasicoherentAlgebra.pullback (toScheme X I n)).obj A ⟶
      (QuasicoherentAlgebra.pullback (toScheme X I n)).obj B)
    (n : ℕ) :
    (Modules.pullback (toScheme X I n)).obj A.obj.X ⟶
      (Modules.pullback (toScheme X I n)).obj B.obj.X :=
  eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A).symm ≫
    (φ n).hom.hom.hom ≫
      eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) B)

/-- Compatibility of `algebraFamilyAppModuleHom` with the transition isomorphisms of
`completionFunctor X I`. -/
private theorem algebraFamilyAppModuleHom_naturality
    {A B : QuasicoherentAlgebra X} [A.obj.X.IsFinitePresentation] [B.obj.X.IsFinitePresentation]
    (φ : ∀ n, (QuasicoherentAlgebra.pullback (toScheme X I n)).obj A ⟶
      (QuasicoherentAlgebra.pullback (toScheme X I n)).obj B)
    (hφ : ∀ n, (QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map (φ (n + 1)) ≫
      (algebraTransitionIso X I B n).hom = (algebraTransitionIso X I A n).hom ≫ φ n)
    (n : ℕ) :
    (Modules.pullback ((X.formalCompletion I).ι n)).map
        (algebraFamilyAppModuleHom X I φ (n + 1)) ≫
      (((completionFunctor X I).obj ⟨B.obj.X, ‹_›⟩).transitionIso n).hom =
    (((completionFunctor X I).obj ⟨A.obj.X, ‹_›⟩).transitionIso n).hom ≫
      algebraFamilyAppModuleHom X I φ n := by
  let ιₙ := (X.formalCompletion I).ι n
  let i₁ := toScheme X I (n + 1)
  let i₀ := toScheme X I n
  let m := algebraFamilyAppModuleHom X I φ
  have hφk (k : ℕ) : (φ k).hom.hom.hom =
      eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I k) A) ≫ m k ≫
        eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I k) B).symm :=
    eq_eqToHom_conj_of_eq_symm_conj (C := ((X.formalCompletion I).X k).Modules)
      (QuasicoherentAlgebra.pullback_obj_X (toScheme X I k) A)
      (QuasicoherentAlgebra.pullback_obj_X (toScheme X I k) B) rfl
  let pA₁ :=
    (QuasicoherentAlgebra.pullback_obj_X ιₙ ((QuasicoherentAlgebra.pullback i₁).obj A)).trans
      (congrArg (Modules.pullback ιₙ).obj (QuasicoherentAlgebra.pullback_obj_X i₁ A))
  let pB₁ :=
    (QuasicoherentAlgebra.pullback_obj_X ιₙ ((QuasicoherentAlgebra.pullback i₁).obj B)).trans
      (congrArg (Modules.pullback ιₙ).obj (QuasicoherentAlgebra.pullback_obj_X i₁ B))
  let pA₀ := QuasicoherentAlgebra.pullback_obj_X i₀ A
  let pB₀ := QuasicoherentAlgebra.pullback_obj_X i₀ B
  have hmap : ((QuasicoherentAlgebra.pullback ιₙ).map (φ (n + 1))).hom.hom.hom =
      eqToHom pA₁ ≫ (Modules.pullback ιₙ).map (m (n + 1)) ≫ eqToHom pB₁.symm :=
    (QuasicoherentAlgebra.pullback_map_hom_hom_hom ιₙ (φ (n + 1))).trans
      (map_eqToHom_conj (C := ((X.formalCompletion I).X (n + 1)).Modules)
        (D := ((X.formalCompletion I).X n).Modules) (Modules.pullback ιₙ)
        (QuasicoherentAlgebra.pullback_obj_X ιₙ ((QuasicoherentAlgebra.pullback i₁).obj A))
        (QuasicoherentAlgebra.pullback_obj_X i₁ A)
        (QuasicoherentAlgebra.pullback_obj_X ιₙ ((QuasicoherentAlgebra.pullback i₁).obj B))
        (QuasicoherentAlgebra.pullback_obj_X i₁ B) (hφk (n + 1)))
  have hL :
      ((QuasicoherentAlgebra.pullback ιₙ).map (φ (n + 1)) ≫
          (algebraTransitionIso X I B n).hom).hom.hom.hom =
        eqToHom pA₁ ≫ ((Modules.pullback ιₙ).map (m (n + 1)) ≫
            (((completionFunctor X I).obj ⟨B.obj.X, ‹_›⟩).transitionIso n).hom) ≫
          eqToHom pB₀.symm :=
    (congrArg₂ (CategoryStruct.comp (obj := ((X.formalCompletion I).X n).Modules))
        hmap (algebraTransitionIso_hom_hom_hom_hom X I B n)).trans
      (eqToHom_conj_comp (C := ((X.formalCompletion I).X n).Modules) pA₁ pB₁ pB₀
        ((Modules.pullback ιₙ).map (m (n + 1)))
        (((completionFunctor X I).obj ⟨B.obj.X, ‹_›⟩).transitionIso n).hom)
  have hR :
      ((algebraTransitionIso X I A n).hom ≫ φ n).hom.hom.hom =
        eqToHom pA₁ ≫
          ((((completionFunctor X I).obj ⟨A.obj.X, ‹_›⟩).transitionIso n).hom ≫ m n) ≫
            eqToHom pB₀.symm :=
    (congrArg₂ (CategoryStruct.comp (obj := ((X.formalCompletion I).X n).Modules))
        (algebraTransitionIso_hom_hom_hom_hom X I A n) (hφk n)).trans
      (eqToHom_conj_comp (C := ((X.formalCompletion I).X n).Modules) pA₁ pA₀ pB₀
        (((completionFunctor X I).obj ⟨A.obj.X, ‹_›⟩).transitionIso n).hom (m n))
  exact eq_of_eqToHom_conj_eq (C := ((X.formalCompletion I).X n).Modules) pA₁ pB₀
    (hL.symm.trans ((congrArg (fun k ↦ k.hom.hom.hom) (hφ n)).trans hR))

/-- A compatible family of algebra morphisms on the levels of `X.formalCompletion I` induces a
morphism of coherent formal modules between the completions of the underlying finitely presented
modules. -/
private noncomputable def coherentFormalModuleHomOfAlgebraFamily
    {A B : QuasicoherentAlgebra X} [A.obj.X.IsFinitePresentation] [B.obj.X.IsFinitePresentation]
    (φ : ∀ n, (QuasicoherentAlgebra.pullback (toScheme X I n)).obj A ⟶
      (QuasicoherentAlgebra.pullback (toScheme X I n)).obj B)
    (hφ : ∀ n, (QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map (φ (n + 1)) ≫
      (algebraTransitionIso X I B n).hom = (algebraTransitionIso X I A n).hom ≫ φ n) :
    (completionFunctor X I).obj ⟨A.obj.X, ‹_›⟩ ⟶ (completionFunctor X I).obj ⟨B.obj.X, ‹_›⟩ where
  app := algebraFamilyAppModuleHom X I φ
  naturality := algebraFamilyAppModuleHom_naturality X I φ hφ

/-- If `ψ : A.obj.X ⟶ B.obj.X` reduces at every level `n` of `X.formalCompletion I` to the
underlying map of an algebra morphism `φ n`, and `completionFunctor X I` is faithful, then `ψ`
preserves the algebra unit. -/
private theorem isMonHom_one_of_pullback_algebraFamily [(completionFunctor X I).Faithful]
    {A B : QuasicoherentAlgebra X} [B.obj.X.IsFinitePresentation]
    (φ : ∀ n, (QuasicoherentAlgebra.pullback (toScheme X I n)).obj A ⟶
      (QuasicoherentAlgebra.pullback (toScheme X I n)).obj B)
    {ψ : A.obj.X ⟶ B.obj.X}
    (hψ : ∀ n, (Modules.pullback (toScheme X I n)).map ψ =
      eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A).symm ≫
        (φ n).hom.hom.hom ≫
          eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) B)) :
    η[A.obj.X] ≫ ψ = η[B.obj.X] := by
  have hfp : (ObjectProperty.homMk (η[A.obj.X] ≫ ψ) :
      (⟨𝟙_ X.Modules, inferInstanceAs (𝟙_ X.Modules).IsFinitePresentation⟩ :
          FinitelyPresentedSheaf X) ⟶ ⟨B.obj.X, ‹_›⟩) =
      ObjectProperty.homMk η[B.obj.X] := by
    apply (completionFunctor X I).map_injective
    refine CoherentFormalModule.hom_ext fun n ↦ ?_
    let iₙ := toScheme X I n
    have hφn : (φ n).hom.hom.hom =
        eqToHom (QuasicoherentAlgebra.pullback_obj_X iₙ A) ≫
          (Modules.pullback iₙ).map ψ ≫
            eqToHom (QuasicoherentAlgebra.pullback_obj_X iₙ B).symm :=
      eq_eqToHom_conj_of_eq_symm_conj (C := ((X.formalCompletion I).X n).Modules)
        (QuasicoherentAlgebra.pullback_obj_X iₙ A)
        (QuasicoherentAlgebra.pullback_obj_X iₙ B) (hψ n)
    have hone := unit_comp_of_eqToHom_conj (C := ((X.formalCompletion I).X n).Modules)
      (QuasicoherentAlgebra.pullback_obj_X iₙ A)
      (QuasicoherentAlgebra.pullback_obj_X iₙ B)
      (QuasicoherentAlgebra.pullback_obj_one iₙ A)
      (QuasicoherentAlgebra.pullback_obj_one iₙ B)
      hφn (IsMonHom.one_hom (φ n).hom.hom.hom)
    exact ((Modules.pullback iₙ).map_comp η[A.obj.X] ψ).trans hone
  exact congrArg (fun k ↦ k.hom) hfp

/-- If `ψ : A.obj.X ⟶ B.obj.X` reduces at every level `n` of `X.formalCompletion I` to the
underlying map of an algebra morphism `φ n`, and `completionFunctor X I` is faithful, then `ψ`
preserves multiplication. -/
private theorem isMonHom_mul_of_pullback_algebraFamily [(completionFunctor X I).Faithful]
    {A B : QuasicoherentAlgebra X} [A.obj.X.IsFinitePresentation] [B.obj.X.IsFinitePresentation]
    (φ : ∀ n, (QuasicoherentAlgebra.pullback (toScheme X I n)).obj A ⟶
      (QuasicoherentAlgebra.pullback (toScheme X I n)).obj B)
    {ψ : A.obj.X ⟶ B.obj.X}
    (hψ : ∀ n, (Modules.pullback (toScheme X I n)).map ψ =
      eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A).symm ≫
        (φ n).hom.hom.hom ≫
          eqToHom (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) B)) :
    μ[A.obj.X] ≫ ψ = (ψ ⊗ₘ ψ) ≫ μ[B.obj.X] := by
  have hfp : (ObjectProperty.homMk (μ[A.obj.X] ≫ ψ) :
      (⟨A.obj.X ⊗ A.obj.X, inferInstanceAs (A.obj.X ⊗ A.obj.X).IsFinitePresentation⟩ :
          FinitelyPresentedSheaf X) ⟶ ⟨B.obj.X, ‹_›⟩) =
      ObjectProperty.homMk ((ψ ⊗ₘ ψ) ≫ μ[B.obj.X]) := by
    apply (completionFunctor X I).map_injective
    refine CoherentFormalModule.hom_ext fun n ↦ ?_
    let iₙ := toScheme X I n
    let δA := Functor.OplaxMonoidal.δ (Modules.pullback iₙ) A.obj.X A.obj.X
    let δB := Functor.OplaxMonoidal.δ (Modules.pullback iₙ) B.obj.X B.obj.X
    have hφn : (φ n).hom.hom.hom =
        eqToHom (QuasicoherentAlgebra.pullback_obj_X iₙ A) ≫
          (Modules.pullback iₙ).map ψ ≫
            eqToHom (QuasicoherentAlgebra.pullback_obj_X iₙ B).symm :=
      eq_eqToHom_conj_of_eq_symm_conj (C := ((X.formalCompletion I).X n).Modules)
        (QuasicoherentAlgebra.pullback_obj_X iₙ A)
        (QuasicoherentAlgebra.pullback_obj_X iₙ B) (hψ n)
    have hδ : ((Modules.pullback iₙ).map ψ ⊗ₘ (Modules.pullback iₙ).map ψ) ≫ inv δB =
        inv δA ≫ (Modules.pullback iₙ).map (ψ ⊗ₘ ψ) := by
      rw [IsIso.comp_inv_eq, Category.assoc, ← Functor.OplaxMonoidal.δ_natural,
        IsIso.inv_hom_id_assoc]
    have hmul := mul_comp_of_eqToHom_conj (C := ((X.formalCompletion I).X n).Modules)
      (QuasicoherentAlgebra.pullback_obj_X iₙ A)
      (QuasicoherentAlgebra.pullback_obj_X iₙ B)
      (QuasicoherentAlgebra.pullback_obj_mul iₙ A)
      (QuasicoherentAlgebra.pullback_obj_mul iₙ B)
      hφn hδ (IsMonHom.mul_hom (φ n).hom.hom.hom)
    exact ((Modules.pullback iₙ).map_comp μ[A.obj.X] ψ).trans
      (hmul.trans ((Modules.pullback iₙ).map_comp (ψ ⊗ₘ ψ) μ[B.obj.X]).symm)
  exact congrArg (fun k ↦ k.hom) hfp

/-- **Algebraization of compatible algebra morphisms along a formal completion.** When the
completion functor on finitely presented `𝒪_X`-modules is full and faithful, every compatible
family of morphisms `φ n : toScheme n ^* A ⟶ toScheme n ^* B` between quasicoherent `𝒪_X`-algebras
with finitely presented underlying modules arises from a unique algebra morphism `f : A ⟶ B`. -/
theorem existsUnique_algebra_hom_of_completionFunctor
    [(completionFunctor X I).Full] [(completionFunctor X I).Faithful]
    {A B : QuasicoherentAlgebra X} [A.obj.X.IsFinitePresentation] [B.obj.X.IsFinitePresentation]
    (φ : ∀ n, (QuasicoherentAlgebra.pullback (toScheme X I n)).obj A ⟶
      (QuasicoherentAlgebra.pullback (toScheme X I n)).obj B)
    (hφ : ∀ n, (QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map (φ (n + 1)) ≫
      (algebraTransitionIso X I B n).hom = (algebraTransitionIso X I A n).hom ≫ φ n) :
    ∃! f : A ⟶ B, ∀ n, (QuasicoherentAlgebra.pullback (toScheme X I n)).map f = φ n := by
  let Φ := coherentFormalModuleHomOfAlgebraFamily X I φ hφ
  let ψ : A.obj.X ⟶ B.obj.X := ((completionFunctor X I).preimage Φ).hom
  have hψ (n : ℕ) : (Modules.pullback (toScheme X I n)).map ψ = Φ.app n :=
    (completionFunctor_map_app X I ((completionFunctor X I).preimage Φ) n).symm.trans
      (congrArg (·.app n) ((completionFunctor X I).map_preimage Φ))
  let f : A ⟶ B := ObjectProperty.homMk (CommMon.homMk
    (Mon.Hom.mk' ψ
      (isMonHom_one_of_pullback_algebraFamily X I φ hψ)
      (isMonHom_mul_of_pullback_algebraFamily X I φ hψ)))
  have hf (n : ℕ) : (QuasicoherentAlgebra.pullback (toScheme X I n)).map f = φ n := by
    apply ObjectProperty.hom_ext
    apply CommMon.hom_ext
    exact (QuasicoherentAlgebra.pullback_map_hom_hom_hom (toScheme X I n) f).trans
      (eq_eqToHom_conj_of_eq_symm_conj (C := ((X.formalCompletion I).X n).Modules)
        (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) A)
        (QuasicoherentAlgebra.pullback_obj_X (toScheme X I n) B) (hψ n)).symm
  exact ⟨f, hf, fun g hg ↦
    algebra_hom_ext_of_faithful_completionFunctor X I fun n ↦ (hg n).trans (hf n).symm⟩

/-- The unique algebra morphism `A ⟶ B` descending a compatible family of algebra morphisms on the
levels of `X.formalCompletion I`, when `completionFunctor X I` is full and faithful. -/
noncomputable def descAlgebraOfCompletionFunctor
    [(completionFunctor X I).Full] [(completionFunctor X I).Faithful]
    {A B : QuasicoherentAlgebra X} [A.obj.X.IsFinitePresentation] [B.obj.X.IsFinitePresentation]
    (φ : ∀ n, (QuasicoherentAlgebra.pullback (toScheme X I n)).obj A ⟶
      (QuasicoherentAlgebra.pullback (toScheme X I n)).obj B)
    (hφ : ∀ n, (QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map (φ (n + 1)) ≫
      (algebraTransitionIso X I B n).hom = (algebraTransitionIso X I A n).hom ≫ φ n) :
    A ⟶ B :=
  (existsUnique_algebra_hom_of_completionFunctor X I φ hφ).exists.choose

/-- Pulling `descAlgebraOfCompletionFunctor X I φ hφ` back to level `n` of `X.formalCompletion I`
recovers `φ n`. -/
@[simp]
theorem pullback_toScheme_map_descAlgebraOfCompletionFunctor
    [(completionFunctor X I).Full] [(completionFunctor X I).Faithful]
    {A B : QuasicoherentAlgebra X} [A.obj.X.IsFinitePresentation] [B.obj.X.IsFinitePresentation]
    (φ : ∀ n, (QuasicoherentAlgebra.pullback (toScheme X I n)).obj A ⟶
      (QuasicoherentAlgebra.pullback (toScheme X I n)).obj B)
    (hφ : ∀ n, (QuasicoherentAlgebra.pullback ((X.formalCompletion I).ι n)).map (φ (n + 1)) ≫
      (algebraTransitionIso X I B n).hom = (algebraTransitionIso X I A n).hom ≫ φ n)
    (n : ℕ) :
    (QuasicoherentAlgebra.pullback (toScheme X I n)).map
        (descAlgebraOfCompletionFunctor X I φ hφ) = φ n :=
  (existsUnique_algebra_hom_of_completionFunctor X I φ hφ).exists.choose_spec n

end AlgebraicGeometry.Scheme.formalCompletion
