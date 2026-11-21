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
* `CategoryTheory.PreOneHypercover.over` and
  `CategoryTheory.GrothendieckTopology.OneHypercover.over`: lift a (pre-)`1`-hypercover of
  `Y.left` in `C` to a (pre-)`1`-hypercover of `Y` in `Over X`.
* `CategoryTheory.GrothendieckTopology.isLeftAdjoint_overPullback`: pullback of sheaves to the
  over site `J.over U` is a left adjoint whenever pointwise right Kan extensions along
  `(Over.forget U).op` exist.
* `CategoryTheory.GrothendieckTopology.ofArrows_mem_over_iff`: a family of morphisms of `Over U`
  generates a covering sieve for `J.over U` if and only if the underlying family of morphisms of
  `C` generates a covering sieve for `J`.

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

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- Lift a pre-`1`-hypercover of `Y.left` in `C` to a pre-`1`-hypercover of `Y` in `Over X`. -/
-- Exposed so that consumers retain definitional access to the index types `I₀` and `I₁`.
@[expose, simps I₀ X f I₁ Y p₁ p₂]
def PreOneHypercover.over {X : C} (Y : Over X) (E : PreOneHypercover.{w} Y.left) :
    PreOneHypercover.{w} Y where
  I₀ := E.I₀
  X i := Over.mk (E.f i ≫ Y.hom)
  f i := Over.homMk (E.f i) rfl
  I₁ := E.I₁
  Y _ _ k := Over.mk (E.p₁ k ≫ E.f _ ≫ Y.hom)
  p₁ _ _ k := Over.homMk (E.p₁ k) rfl
  p₂ _ _ k := Over.homMk (E.p₂ k) (by simp [← Category.assoc, E.w])
  w _ _ k := Over.OverMorphism.ext (E.w k)

/-- Forgetting the lift of a pre-`1`-hypercover `E` along `Over.forget X` recovers `E`. -/
@[simp]
lemma PreOneHypercover.map_over_forget {X : C} (Y : Over X) (E : PreOneHypercover.{w} Y.left) :
    (E.over Y).map (Over.forget X) = E :=
  rfl

/-- Lifting the forgetful image of a pre-`1`-hypercover `E` in `Over X` back to `Over X` recovers
`E`. -/
@[simp]
lemma PreOneHypercover.over_map_forget {X : C} {Y : Over X} (E : PreOneHypercover.{w} Y) :
    (E.map (Over.forget X)).over Y = E := by
  obtain ⟨⟨I₀, X₀, f₀⟩, I₁, Y₀, p₁, p₂, w⟩ := E
  have hX (i : I₀) : Over.mk ((f₀ i).left ≫ Y.hom) = X₀ i := by
    rw [Over.w (f₀ i)]; rfl
  have hY ⦃i₁ i₂ : I₀⦄ (k : I₁ i₁ i₂) :
      Over.mk ((p₁ k).left ≫ (f₀ i₁).left ≫ Y.hom) = Y₀ k := by
    rw [Over.w (f₀ i₁), Over.w (p₁ k)]; rfl
  have h_over : ∀ {A B : Over X} (g : A ⟶ B) {A' B' : Over X},
      A' = A → B' = B → ∀ (g' : A'.left ⟶ B'.left), g' ≍ g.left →
      ∀ (w : g' ≫ B'.hom = A'.hom), (Over.homMk g' w : A' ⟶ B') ≍ g := by
    intro A B g A' B' hA hB g' hg w
    subst hA hB
    obtain rfl : g' = g.left := eq_of_heq hg
    exact heq_of_eq (Over.OverMorphism.ext rfl)
  dsimp only [PreOneHypercover.over, PreOneHypercover.map]
  congr 1
  · congr 1
    · funext i; exact hX i
    · refine Function.hfunext rfl fun i i' hi ↦ ?_
      subst hi
      exact h_over (f₀ i) (hX i) rfl (f₀ i).left .rfl rfl
  · funext i₁ i₂ k; exact hY k
  · refine Function.hfunext rfl fun i₁ i₁' hi₁ ↦ ?_
    subst hi₁
    refine Function.hfunext rfl fun i₂ i₂' hi₂ ↦ ?_
    subst hi₂
    refine Function.hfunext rfl fun k k' hk ↦ ?_
    subst hk
    exact h_over (p₁ k) (hY k) (hX i₁) (p₁ k).left .rfl rfl
  · refine Function.hfunext rfl fun i₁ i₁' hi₁ ↦ ?_
    subst hi₁
    refine Function.hfunext rfl fun i₂ i₂' hi₂ ↦ ?_
    subst hi₂
    refine Function.hfunext rfl fun k k' hk ↦ ?_
    subst hk
    exact h_over (p₂ k) (hY k) (hX i₂) (p₂ k).left .rfl _
  · refine Function.hfunext rfl fun i₁ i₁' hi₁ ↦ ?_
    subst hi₁
    refine Function.hfunext rfl fun i₂ i₂' hi₂ ↦ ?_
    subst hi₂
    refine Function.hfunext rfl fun k k' hk ↦ ?_
    subst hk
    have h_comp : ∀ {A B C : Over X} (f : A ⟶ B) (g : B ⟶ C) {A' B' C' : Over X},
        A' = A → B' = B → C' = C →
        ∀ {f' : A' ⟶ B'} {g' : B' ⟶ C'}, f' ≍ f → g' ≍ g → f' ≫ g' ≍ f ≫ g := by
      intro A B C f g A' B' C' hA hB hC f' g' hf hg
      subst hA hB hC
      rw [eq_of_heq hf, eq_of_heq hg]
    have h_eq : ∀ {A : Over X} {L R : A ⟶ Y} {A' : Over X}, A' = A →
        ∀ {L' R' : A' ⟶ Y}, L' ≍ L → R' ≍ R → (L' = R') = (L = R) := by
      intro A L R A' hA L' R' hL hR
      subst hA
      rw [eq_of_heq hL, eq_of_heq hR]
    have h_prop_heq : ∀ {P Q : Prop} {hp : P} {hq : Q}, P = Q → hp ≍ hq := by
      intro P Q hp hq h; subst h; rfl
    refine h_prop_heq (h_eq (hY k) ?_ ?_)
    · exact h_comp (p₁ k) (f₀ i₁) (hY k) (hX i₁) rfl
        (h_over (p₁ k) (hY k) (hX i₁) (p₁ k).left .rfl rfl)
        (h_over (f₀ i₁) (hX i₁) rfl (f₀ i₁).left .rfl rfl)
    · exact h_comp (p₂ k) (f₀ i₂) (hY k) (hX i₂) rfl
        (h_over (p₂ k) (hY k) (hX i₂) (p₂ k).left .rfl _)
        (h_over (f₀ i₂) (hX i₂) rfl (f₀ i₂).left .rfl rfl)

/-- Lift a `J`-`1`-hypercover of `Y.left` in `C` to a `(J.over X)`-`1`-hypercover of `Y` in
`Over X`. -/
-- Exposed so that consumers retain definitional access to the index types `I₀` and `I₁`.
@[expose, simps! toPreOneHypercover]
def GrothendieckTopology.OneHypercover.over {J : GrothendieckTopology C} {X : C}
    (Y : Over X) (E : J.OneHypercover.{w} Y.left) :
    (J.over X).OneHypercover.{w} Y where
  toPreOneHypercover := E.toPreOneHypercover.over Y
  mem₀ := by
    rw [GrothendieckTopology.mem_over_iff, PreZeroHypercover.sieve₀, Sieve.overEquiv_ofArrows]
    exact E.mem₀
  mem₁ i₁ i₂ W q₁ q₂ hw := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_preOneHypercover_sieve₁]
    exact E.mem₁ i₁ i₂ q₁.left q₂.left congr($(hw).left)

/-- Forgetting the lift of a `J`-`1`-hypercover `E` along `Over.forget X` recovers `E`. -/
@[simp]
lemma GrothendieckTopology.OneHypercover.map_over_forget {J : GrothendieckTopology C} {X : C}
    (Y : Over X) (E : J.OneHypercover.{w} Y.left) :
    (E.over Y).map (Over.forget X) J = E :=
  rfl

/-- Lifting the forgetful image of a `(J.over X)`-`1`-hypercover `E` back to `Over X` recovers
`E`. -/
@[simp]
lemma GrothendieckTopology.OneHypercover.over_map_forget {J : GrothendieckTopology C} {X : C}
    {Y : Over X} (E : (J.over X).OneHypercover.{w} Y) :
    (E.map (Over.forget X) J).over Y = E := by
  cases E
  dsimp only [GrothendieckTopology.OneHypercover.over, GrothendieckTopology.OneHypercover.map]
  congr 1
  exact PreOneHypercover.over_map_forget _

end CategoryTheory

namespace CategoryTheory.GrothendieckTopology

/-- Pullback of sheaves to the over site `J.over U` is a left adjoint whenever pointwise right Kan
extensions along `(Over.forget U).op` exist. -/
instance isLeftAdjoint_overPullback {C : Type*} [Category* C] (J : GrothendieckTopology C)
    (A : Type*) [Category* A] (U : C)
    [∀ F : (Over U)ᵒᵖ ⥤ A, (Over.forget U).op.HasPointwiseRightKanExtension F] :
    (J.overPullback A U).IsLeftAdjoint :=
  ((Over.forget U).sheafAdjunctionCocontinuous A (J.over U) J).isLeftAdjoint

/-- A family of morphisms `g i : Z i ⟶ Y` of `Over U` generates a covering sieve of `Y` for
`J.over U` if and only if the underlying family `(g i).left` generates a covering sieve of `Y.left`
for `J`. -/
lemma ofArrows_mem_over_iff {C : Type*} [Category* C] (J : GrothendieckTopology C) {U : C}
    {Y : Over U} {I : Type*} (Z : I → Over U) (g : ∀ i, Z i ⟶ Y) :
    Sieve.ofArrows Z g ∈ J.over U Y ↔
      Sieve.ofArrows (fun i ↦ (Z i).left) (fun i ↦ (g i).left) ∈ J Y.left := by
  rw [mem_over_iff, Sieve.overEquiv_ofArrows]

end CategoryTheory.GrothendieckTopology
