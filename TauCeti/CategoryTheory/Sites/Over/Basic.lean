/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Over

/-!
# Sheaves on `Over S` as sheaves on `C`

Let `P` be a presheaf of types on `Over S`. The presheaf `CategoryTheory.Over.sigmaPresheaf P`
on `C` sends `T` to the pairs `⟨h, s⟩` of a morphism `h : T ⟶ S` and an element `s` of
`P (T, h)`. This is the formula for the extension `j_!` of presheaves along the localization
`Over S ⥤ C` (Stacks, Chapter *Sites and Sheaves*, Section *Localization*). It is also the
`Over S` analogue of Mathlib's `CategoryTheory.yonedaCollectionPresheaf` for a representable
presheaf, indexed directly by morphisms to `S` rather than through the Yoneda lemma, and with
values in an arbitrary universe.

When `S` is a sheaf (for instance, when the topology is subcanonical), `P` is a sheaf for the
induced topology `J.over S` if and only if `sigmaPresheaf P` is a sheaf for `J`
(`CategoryTheory.Over.isSheaf_over_iff_isSheaf_sigmaPresheaf`). This lets criteria for sheaves on
`C` be applied to presheaves on `Over S`: for instance Mathlib's reduction of sheaves for a
quasi-compact topology on schemes to the Zariski topology and single coverings of affine schemes
(`AlgebraicGeometry.isSheaf_type_propQCTopology_iff`, Stacks, Tag 022H), which is stated for
presheaves on the category of all schemes.

## Main declarations

* `CategoryTheory.Over.sigmaPresheaf`: the presheaf `T ↦ Σ (h : T ⟶ S), P (T, h)` on `C`.
* `CategoryTheory.Over.isSheafFor_sigmaPresheaf`: the sheaf condition for `sigmaPresheaf P` with
  respect to a sieve on `T`, from the sheaf conditions for `S` and for `P` over every `h : T ⟶ S`.
* `CategoryTheory.Over.isSheafFor_of_isSheafFor_sigmaPresheaf`: conversely, the sheaf condition
  for `P` with respect to a sieve on `Y : Over S`, from the sheaf condition for `sigmaPresheaf P`
  with respect to the corresponding sieve on `Y.left`.
* `CategoryTheory.Over.isSheaf_over_iff_isSheaf_sigmaPresheaf`: `P` is a sheaf for `J.over S`
  if and only if `sigmaPresheaf P` is a sheaf for `J`, when `S` is a sheaf for `J`.

## References

* The Stacks Project, Chapter *Sites and Sheaves*, Section *Localization*, for the extension
  `j_!` of presheaves along a localization.
-/

public section

universe w v u

open CategoryTheory Opposite TypeCat

namespace CategoryTheory.Over

variable {C : Type u} [Category.{v} C] {S : C} (P : (Over S)ᵒᵖ ⥤ Type w)

/-- For `h = h'`, transporting `s ∈ P (T, h')` along the identity of `T`, viewed as a morphism
`(T, h) ⟶ (T, h')` over `S`, does not change the pair `⟨h', s⟩`. -/
private lemma sigma_mk_map_homMk_id {T : C} {h h' : T ⟶ S} (e : h = h') (s : P.obj (op (mk h'))) :
    (⟨h, P.map (homMk (𝟙 T) (by simp [e]) : mk h ⟶ mk h').op s⟩ :
      Σ k : T ⟶ S, P.obj (op (mk k))) = ⟨h', s⟩ := by
  subst e
  have : (homMk (𝟙 T) (by simp) : mk h ⟶ mk h) = 𝟙 _ := by ext; rfl
  rw [this, op_id, Functor.map_id_apply]

/-- The presheaf `T ↦ Σ (h : T ⟶ S), P (T, h)` on `C` attached to a presheaf of types `P` on
`Over S`: a morphism `g : T' ⟶ T` sends `⟨h, s⟩` to `⟨g ≫ h, g^* s⟩`. -/
-- Exposed so that consumers can use sigma pairs and their projections in the object types.
@[expose, simps obj]
def sigmaPresheaf : Cᵒᵖ ⥤ Type (max v w) where
  obj T := Σ h : T.unop ⟶ S, P.obj (op (mk h))
  map g := ↾fun x ↦ ⟨g.unop ≫ x.1, P.map (homMk g.unop rfl : mk (g.unop ≫ x.1) ⟶ mk x.1).op x.2⟩
  map_id T := by
    ext ⟨h, s⟩ : 3
    exact sigma_mk_map_homMk_id P (Category.id_comp h) s
  map_comp f g := by
    ext ⟨h, s⟩ : 3
    refine Eq.trans ?_ (sigma_mk_map_homMk_id P (Category.assoc g.unop f.unop h)
      (P.map (homMk g.unop rfl : mk (g.unop ≫ f.unop ≫ h) ⟶ mk (f.unop ≫ h)).op
        (P.map (homMk f.unop rfl : mk (f.unop ≫ h) ⟶ mk h).op s)))
    refine congrArg (Sigma.mk _) ?_
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
    congr 2
    exact congrArg P.map (Quiver.Hom.unop_inj (by ext; simp))

variable {P}

/-- Restricting a pair along `g` composes its structure morphism with `g.unop` and restricts
its section along the resulting morphism over `S`. -/
lemma sigmaPresheaf_map {T T' : Cᵒᵖ} (g : T ⟶ T') (h : T.unop ⟶ S)
    (s : P.obj (op (mk h))) :
    (sigmaPresheaf P).map g ⟨h, s⟩ =
      ⟨g.unop ≫ h, P.map (homMk g.unop rfl : mk (g.unop ≫ h) ⟶ mk h).op s⟩ := (rfl)

/-- Restricting the pair `⟨Y.hom, s⟩` along the underlying morphism of `f : Z ⟶ Y` over `S`
gives the pair `⟨Z.hom, f^* s⟩`. -/
@[simp]
lemma sigmaPresheaf_map_left_mk {Y Z : Over S} (f : Z ⟶ Y) (s : P.obj (op Y)) :
    (sigmaPresheaf P).map f.left.op ⟨Y.hom, s⟩ = ⟨Z.hom, P.map f.op s⟩ := by
  refine (sigma_mk_map_homMk_id P (Over.w f).symm
    (P.map (homMk f.left rfl : mk (f.left ≫ Y.hom) ⟶ Y).op s)).symm.trans ?_
  refine congrArg (Sigma.mk _) ?_
  rw [← Functor.map_comp_apply, ← op_comp]
  exact congrArg (fun g ↦ P.map g s) (congrArg Quiver.Hom.op (by ext; simp))

/-- **Sheaves on `Over S` give sheaves on `C`.** If `S` is a sheaf for a sieve `R` on `T` and
`P` is a sheaf for the corresponding sieve on `(T, h)` for every `h : T ⟶ S`, then
`sigmaPresheaf P` is a sheaf for `R`. -/
theorem isSheafFor_sigmaPresheaf {T : C} (R : Sieve T)
    (hS : Presieve.IsSheafFor (yoneda.obj S) R.arrows)
    (hP : ∀ h : T ⟶ S, Presieve.IsSheafFor P ((Sieve.overEquiv (mk h)).symm R).arrows) :
    Presieve.IsSheafFor (sigmaPresheaf P) R.arrows := by
  intro x hx
  -- The first components of `x` glue to a morphism `h : T ⟶ S`.
  obtain ⟨h, hh, -⟩ := hS (fun _ g hg ↦ (x g hg).1)
    (fun _ _ _ g₁ g₂ f₁ f₂ h₁ h₂ e ↦ congrArg Sigma.fst (hx g₁ g₂ h₁ h₂ e))
  have hfst {Z : C} (g : Z ⟶ T) (hg : R g) : (x g hg).1 = g ≫ h := (hh g hg).symm
  -- The second components form a family of elements of `P` over `(T, h)`.
  obtain ⟨z, hz⟩ : ∃ z : Presieve.FamilyOfElements P ((Sieve.overEquiv (mk h)).symm R).arrows,
      ∀ {Z : Over S} (f : Z ⟶ mk h) (hf),
        (⟨Z.hom, z f hf⟩ : (sigmaPresheaf P).obj (op Z.left)) = x f.left hf :=
    ⟨fun Z f hf ↦ P.map (homMk (𝟙 Z.left) (by simpa using (hfst f.left hf).trans (Over.w f)) :
      Z ⟶ mk (x f.left hf).1).op (x f.left hf).2,
      fun f hf ↦ sigma_mk_map_homMk_id P ((hfst _ hf).trans (Over.w f)).symm _⟩
  have hzc : z.Compatible := by
    intro Z₁ Z₂ W g₁ g₂ f₁ f₂ h₁ h₂ e
    refine sigma_mk_injective (β := fun k : W.left ⟶ S ↦ P.obj (op (mk k))) ?_
    rw [← sigmaPresheaf_map_left_mk g₁, ← sigmaPresheaf_map_left_mk g₂, hz, hz]
    exact hx g₁.left g₂.left h₁ h₂ (by simpa using congrArg CommaMorphism.left e)
  obtain ⟨t, ht, -⟩ := hP h z hzc
  have hamalg : x.IsAmalgamation ⟨h, t⟩ := by
    intro Z g hg
    have hg' : ((Sieve.overEquiv (mk h)).symm R).arrows
        (homMk g rfl : mk (g ≫ h) ⟶ mk h) :=
      (Sieve.overEquiv_symm_iff R (homMk g rfl : mk (g ≫ h) ⟶ mk h)).mpr hg
    exact (sigmaPresheaf_map_left_mk (homMk g rfl : mk (g ≫ h) ⟶ mk h) t).trans
      ((congrArg (Sigma.mk (β := fun k : Z ⟶ S ↦ P.obj (op (mk k))) _)
        (ht _ hg')).trans (hz _ hg'))
  refine ⟨⟨h, t⟩, hamalg, fun ⟨h', t'⟩ ht' ↦ ?_⟩
  -- A second amalgamation `⟨h', t'⟩` has `h' = h`, and then `t'` amalgamates `z`.
  obtain rfl : h = h' := hS.isSeparatedFor.ext fun Z g hg ↦
    ((congrArg Sigma.fst (ht' g hg)).trans (hfst g hg)).symm
  refine congrArg (Sigma.mk _) ((hP h).isSeparatedFor.ext fun Z f hf ↦ ?_)
  refine sigma_mk_injective (β := fun k : Z.left ⟶ S ↦ P.obj (op (mk k))) ?_
  rw [← sigmaPresheaf_map_left_mk, ← sigmaPresheaf_map_left_mk]
  exact (ht' f.left hf).trans (hamalg f.left hf).symm

/-- **Sheaves on `C` give sheaves on `Over S`.** If `S` is separated for the sieve on `Y.left`
corresponding to a sieve `R` on `Y : Over S`, and `sigmaPresheaf P` is a sheaf for it, then `P`
is a sheaf for `R`. -/
theorem isSheafFor_of_isSheafFor_sigmaPresheaf {Y : Over S} (R : Sieve Y)
    (hS : Presieve.IsSeparatedFor (yoneda.obj S) (Sieve.overEquiv Y R).arrows)
    (hP : Presieve.IsSheafFor (sigmaPresheaf P) (Sieve.overEquiv Y R).arrows) :
    Presieve.IsSheafFor P R.arrows := by
  intro x hx
  -- The family `g ↦ ⟨g ≫ Y.hom, x g⟩` on the sieve of `Y.left`.
  let x' : Presieve.FamilyOfElements (sigmaPresheaf P) (Sieve.overEquiv Y R).arrows :=
    fun _ g hg ↦ ⟨g ≫ Y.hom, x (homMk g rfl) ((Sieve.overEquiv_iff R g).mp hg)⟩
  have hx'congr {W : C} {g g' : W ⟶ Y.left} (e : g = g') (hg hg') : x' g hg = x' g' hg' := by
    subst e
    rfl
  have hx' {Z : Over S} (f : Z ⟶ Y) (hf : R f) :
      x' f.left (Sieve.image_mem_functorPushforward _ R hf) = ⟨Z.hom, x f hf⟩ := by
    refine (sigma_mk_map_homMk_id P (Over.w f).symm _).symm.trans (congrArg (Sigma.mk _) ?_)
    rw [← hx.to_sieveCompatible]
    congr 1
    ext
    simp
  have hx'c : x'.Compatible := by
    intro W₁ W₂ V g₁ g₂ f₁ f₂ h₁ h₂ e
    have h₁' := (Sieve.overEquiv_iff R f₁).mp h₁
    have h₂' := (Sieve.overEquiv_iff R f₂).mp h₂
    refine (sigmaPresheaf_map_left_mk (homMk g₁ rfl : mk (g₁ ≫ f₁ ≫ Y.hom) ⟶ mk (f₁ ≫ Y.hom))
      (x _ h₁')).trans ?_
    refine Eq.trans ?_ (sigmaPresheaf_map_left_mk
      (homMk g₂ rfl : mk (g₂ ≫ f₂ ≫ Y.hom) ⟶ mk (f₂ ≫ Y.hom)) (x _ h₂')).symm
    rw [← hx.to_sieveCompatible, ← hx.to_sieveCompatible, ← hx', ← hx']
    exact hx'congr (by simpa using e) ((Sieve.overEquiv Y R).downward_closed h₁ g₁)
      ((Sieve.overEquiv Y R).downward_closed h₂ g₂)
  obtain ⟨⟨h, t⟩, ht, huniq⟩ := hP x' hx'c
  -- The amalgamation lies over `Y.hom`, since `S` is separated.
  obtain rfl : h = Y.hom := hS.ext fun Z g hg ↦ congrArg Sigma.fst (ht g hg)
  refine ⟨t, fun Z f hf ↦ ?_, fun t' ht' ↦ ?_⟩
  · refine sigma_mk_injective (β := fun k : Z.left ⟶ S ↦ P.obj (op (mk k))) ?_
    rw [← sigmaPresheaf_map_left_mk, ← hx' f hf]
    exact ht _ (Sieve.image_mem_functorPushforward _ R hf)
  · refine sigma_mk_injective (β := fun k : Y.left ⟶ S ↦ P.obj (op (mk k)))
      (huniq ⟨Y.hom, t'⟩ fun Z g hg ↦ ?_)
    exact (sigmaPresheaf_map_left_mk (homMk g rfl : mk (g ≫ Y.hom) ⟶ Y) t').trans
      (congrArg (Sigma.mk (β := fun k : Z ⟶ S ↦ P.obj (op (mk k))) _)
        (ht' _ ((Sieve.overEquiv_iff R g).mp hg)))

/-- **Sheaves on `Over S` are sheaves on `C`.** If `S` is a sheaf for a topology `J` on `C`, then
a presheaf of types `P` on `Over S` is a sheaf for the induced topology `J.over S` if and only if
`sigmaPresheaf P : T ↦ Σ (h : T ⟶ S), P (T, h)` is a sheaf for `J`. -/
theorem isSheaf_over_iff_isSheaf_sigmaPresheaf (J : GrothendieckTopology C)
    (hS : Presieve.IsSheaf J (yoneda.obj S)) :
    Presieve.IsSheaf (J.over S) P ↔ Presieve.IsSheaf J (sigmaPresheaf P) :=
  ⟨fun hP _ R hR ↦ isSheafFor_sigmaPresheaf R (hS R hR) fun h ↦
      hP _ (J.overEquiv_symm_mem_over (mk h) R hR),
    fun hP _ R hR ↦ isSheafFor_of_isSheafFor_sigmaPresheaf R (hS _ hR).isSeparatedFor (hP _ hR)⟩

end CategoryTheory.Over
