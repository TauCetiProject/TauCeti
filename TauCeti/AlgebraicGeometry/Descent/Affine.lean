/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Pullbacks
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.DescentDatum
public import TauCeti.RingTheory.Flat.EffectiveDescent

/-!
# Effective faithfully flat descent for affine schemes

Let `R → S` be a map of commutative rings and `p = Spec.map (algebraMap R S) : Spec S ⟶ Spec R`.
This file identifies descent data, in the sense of `TauCeti.DescentDatum p`, on an affine scheme
`Spec B ⟶ Spec S` with descent data on the `S`-algebra `B` relative to `R → S` in the sense of
`TauCeti.Algebra.DescentDatum R S B`: the action `Spec S ×_{Spec R} Spec B ⟶ Spec B` is `Spec`
of the coaction `B → S ⊗[R] B`. Through this dictionary, effective descent for algebras gives
effective descent for affine schemes.

## Main declarations

* `TauCeti.Algebra.DescentDatum.spec`: the descent datum on `Spec B` with action
  `Spec (S ⊗[R] B) ⟶ Spec B` given by `Spec` of the coaction.
* `TauCeti.Algebra.DescentDatum.specEquiv`: every descent datum on `Spec B` relative to `p`
  arises in this way from a unique descent datum on `B`.
* `TauCeti.Algebra.DescentDatum.Hom.spec`: a morphism of descent data on algebras gives a
  morphism, in the opposite direction, of the descent data on their spectra; it preserves
  identities and reverses composition (`Hom.id_spec`, `Hom.comp_spec`).
* `TauCeti.Algebra.DescentDatum.specBaseChangeHom`: for an `R`-algebra `A`, the canonical
  descent datum on `Spec A ×_{Spec R} Spec S` is isomorphic to the descent datum on
  `Spec (S ⊗[R] A)` given by `Spec` of the canonical coaction.
* `TauCeti.Algebra.DescentDatum.specDescendedHom` and
  `TauCeti.DescentDatum.exists_isAffine_baseChange_hom_isIso`: **effective descent for affine
  schemes.** If `S` is flat over `R` (for instance if `p` is faithfully flat), every descent
  datum on `Spec B` relative to `p` is isomorphic to the canonical descent datum on the base
  change of the affine scheme `Spec D.descended` over `Spec R`; transporting along
  `X ≅ Spec Γ(X, ⊤)`, the same holds for every affine scheme `X` over `Spec S`.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII,
  Théorème 2.1.
* The Stacks Project, Chapter *Descent*, Section *Descent data for schemes over schemes*.
-/

public section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace TauCeti

namespace Algebra

namespace DescentDatum

universe u

variable {R S B : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]

/-- `Spec (S ⊗[R] B)` is the fibre product of `Spec S ⟶ Spec R` and `Spec B ⟶ Spec S ⟶ Spec R`. -/
private theorem isPullback_spec_tensorProduct (R S B : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [CommRing B] [Algebra R B] [Algebra S B] [IsScalarTower R S B] :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] B)))
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B).toRingHom))
      (Spec.algebraMap R S) ((Over.mk (Spec.algebraMap S B)).hom ≫ Spec.algebraMap R S) := by
  have h := isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R S B)
  rw [IsScalarTower.algebraMap_eq R S B, CommRingCat.ofHom_comp, Spec.map_comp] at h
  exact h

variable (R S B) in
/-- The identification of `Spec (S ⊗[R] B)` with the fibre product `Spec S ×_{Spec R} Spec B`
on which descent data act. -/
private noncomputable def tensorIso : Spec (.of (S ⊗[R] B)) ≅
    pullback (Spec.algebraMap R S) ((Over.mk (Spec.algebraMap S B)).hom ≫ Spec.algebraMap R S) :=
  (isPullback_spec_tensorProduct R S B).isoPullback

@[reassoc]
private theorem tensorIso_hom_fst :
    (tensorIso R S B).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] B)) :=
  IsPullback.isoPullback_hom_fst _

@[reassoc]
private theorem tensorIso_hom_snd :
    (tensorIso R S B).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B).toRingHom) :=
  IsPullback.isoPullback_hom_snd _

@[reassoc]
private theorem tensorIso_inv_fst :
    (tensorIso R S B).inv ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] B)) = pullback.fst _ _ :=
  IsPullback.isoPullback_inv_fst _

@[reassoc]
private theorem tensorIso_inv_snd :
    (tensorIso R S B).inv ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B).toRingHom) = pullback.snd _ _ :=
  IsPullback.isoPullback_inv_snd _

/-- `Spec (S ⊗[R] (S ⊗[R] B))` is the iterated fibre product on which the cocycle condition of a
descent datum on `Spec B` is stated. -/
private theorem isPullback_spec_tensorProduct₃ :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] (S ⊗[R] B))))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
          S ⊗[R] B →ₐ[R] S ⊗[R] (S ⊗[R] B)).toRingHom) ≫ (tensorIso R S B).hom)
      (Spec.algebraMap R S)
      (pullback.fst (Spec.algebraMap R S) ((Over.mk (Spec.algebraMap S B)).hom ≫
        Spec.algebraMap R S) ≫ Spec.algebraMap R S) := by
  refine (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R S (S ⊗[R] B))).of_iso (Iso.refl _) (Iso.refl _)
    (tensorIso R S B) (Iso.refl _) (by simp) (by simp) (by simp) ?_
  rw [Iso.refl_hom, Category.comp_id, tensorIso_hom_fst_assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]

/-- The identification of `Spec (S ⊗[R] (S ⊗[R] B))` with `Spec S ×_{Spec R} (Spec S ×_{Spec R}
Spec B)`. -/
private noncomputable def tensorIso₃ : Spec (.of (S ⊗[R] (S ⊗[R] B))) ≅
    pullback (Spec.algebraMap R S) (pullback.fst (Spec.algebraMap R S)
      ((Over.mk (Spec.algebraMap S B)).hom ≫ Spec.algebraMap R S) ≫ Spec.algebraMap R S) :=
  (isPullback_spec_tensorProduct₃ (R := R) (S := S) (B := B)).isoPullback

/-- Under the identifications with tensor products, `(s₁, (s₂, x)) ↦ (s₁, a (s₂, x))` is
`Spec (id ⊗ θ)` when `a : Spec S ×_{Spec R} Spec B ⟶ Spec B` is `Spec` of an `R`-algebra map
`θ : B → S ⊗[R] B`. -/
private theorem tensorIso₃_hom_lift (θ : B →ₐ[R] S ⊗[R] B)
    (a : pullback (Spec.algebraMap R S) ((Over.mk (Spec.algebraMap S B)).hom ≫
      Spec.algebraMap R S) ⟶ Spec (.of B))
    (ha : a = (tensorIso R S B).inv ≫ Spec.map (CommRingCat.ofHom θ.toRingHom)) (h) :
    tensorIso₃.hom ≫ pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ a) h =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id R S) θ).toRingHom) ≫ (tensorIso R S B).hom := by
  subst ha
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pullback.lift_fst, Category.assoc, tensorIso_hom_fst, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    refine (IsPullback.isoPullback_hom_fst _).trans ?_
    congr 2
    ext s
    simp
  · rw [Category.assoc, pullback.lift_snd, Category.assoc, tensorIso_hom_snd, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, tensorIso₃, IsPullback.isoPullback_hom_snd_assoc, Category.assoc,
      Iso.hom_inv_id_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun φ ↦ Spec.map (CommRingCat.ofHom φ)) (RingHom.ext fun b ↦ by simp)

/-- The normalisation `π x · x = x` of a descent datum on `Spec B` acting through `Spec` of `θ`
is the counit equation for `θ`. -/
private theorem lift_act_iff (θ : B →ₐ[S] S ⊗[R] B) (h) :
    pullback.lift (Over.mk (Spec.algebraMap S B)).hom (𝟙 _) h ≫ (tensorIso R S B).inv ≫
        Spec.map (CommRingCat.ofHom θ.toRingHom) = 𝟙 _ ↔
      ∀ b, Algebra.TensorProduct.mulLeft (θ b) = b := by
  have hlift : pullback.lift (Over.mk (Spec.algebraMap S B)).hom (𝟙 _) h ≫
      (tensorIso R S B).inv = Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.mulLeft : S ⊗[R] B →ₐ[S] B).toRingHom) := by
    rw [Iso.comp_inv_eq]
    refine pullback.hom_ext ?_ ?_
    · have : (Algebra.TensorProduct.mulLeft : S ⊗[R] B →ₐ[S] B).toRingHom.comp
          Algebra.TensorProduct.includeLeftRingHom = algebraMap S B := by
        ext s
        simp
      rw [pullback.lift_fst, Category.assoc, tensorIso_hom_fst, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, this]
      simp only [Over.mk_hom]
    · rw [pullback.lift_snd, Category.assoc, tensorIso_hom_snd, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp]
      simp only [Over.mk_left]
      convert (Spec.map_id (.of B)).symm using 2
      ext b
      simp
  rw [reassoc_of% hlift, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  simp only [Over.mk_left]
  rw [← Spec.map_id, Spec.map_injective.eq_iff]
  refine ⟨fun h b ↦ congr($h b), fun h ↦ ?_⟩
  ext b
  exact h b

/-- The cocycle condition of a descent datum on `Spec B` acting through `Spec` of `θ` is the
coassociativity of `θ`. -/
private theorem act_assoc_iff (θ : B →ₐ[S] S ⊗[R] B)
    (a : pullback (Spec.algebraMap R S) ((Over.mk (Spec.algebraMap S B)).hom ≫
      Spec.algebraMap R S) ⟶ Spec (.of B))
    (ha : a = (tensorIso R S B).inv ≫ Spec.map (CommRingCat.ofHom θ.toRingHom)) (h₁ h₂) :
    pullback.lift (pullback.fst (Spec.algebraMap R S) (pullback.fst (Spec.algebraMap R S)
        ((Over.mk (Spec.algebraMap S B)).hom ≫ Spec.algebraMap R S) ≫ Spec.algebraMap R S))
        (pullback.snd _ _ ≫ a) h₁ ≫ a =
      pullback.lift (pullback.fst (Spec.algebraMap R S) (pullback.fst (Spec.algebraMap R S)
        ((Over.mk (Spec.algebraMap S B)).hom ≫ Spec.algebraMap R S) ≫ Spec.algebraMap R S))
        (pullback.snd _ _ ≫ pullback.snd _ _) h₂ ≫ a ↔
      ∀ b, Algebra.TensorProduct.map (AlgHom.id R S) (θ.restrictScalars R) (θ b) =
        Algebra.TensorProduct.map (AlgHom.id R S) Algebra.TensorProduct.includeRight (θ b) := by
  rw [← cancel_epi (tensorIso₃ (R := R) (S := S) (B := B)).hom, ← Category.assoc,
    ← Category.assoc, tensorIso₃_hom_lift (θ.restrictScalars R) a ha,
    tensorIso₃_hom_lift Algebra.TensorProduct.includeRight _ tensorIso_inv_snd.symm, ha,
    Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    Spec.map_injective.eq_iff]
  refine ⟨fun h b ↦ congr($h b), fun h ↦ ?_⟩
  ext b
  exact h b

/-- The descent datum on `Spec B ⟶ Spec S` relative to `Spec S ⟶ Spec R` defined by a descent
datum `D` on `B`: the action `Spec S ×_{Spec R} Spec B = Spec (S ⊗[R] B) ⟶ Spec B` is `Spec` of
the coaction of `D`. -/
noncomputable def spec (D : DescentDatum R S B) :
    TauCeti.DescentDatum (Spec.algebraMap R S) (Over.mk (Spec.algebraMap S B)) where
  act := (tensorIso R S B).inv ≫ Spec.map (CommRingCat.ofHom D.coaction.toRingHom)
  act_hom := by
    have : Spec.map (CommRingCat.ofHom D.coaction.toRingHom) ≫ Spec.algebraMap S B =
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] B)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext s
      simp [Algebra.TensorProduct.algebraMap_apply]
    exact (Category.assoc _ _ _).trans ((congrArg _ this).trans tensorIso_inv_fst)
  lift_act := (lift_act_iff D.coaction _).2 D.counit_coaction
  act_assoc := (act_assoc_iff D.coaction _ rfl _ _).2 D.coassoc

private theorem spec_act (D : DescentDatum R S B) :
    D.spec.act = (tensorIso R S B).inv ≫ Spec.map (CommRingCat.ofHom D.coaction.toRingHom) :=
  rfl

/-- The action of `D.spec` is `Spec` of the coaction of `D`, through the canonical map
`Spec (S ⊗[R] B) ⟶ Spec S ×_{Spec R} Spec B`. -/
@[reassoc (attr := simp)]
theorem lift_spec_act (D : DescentDatum R S B)
    (h : Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] B)) ≫ Spec.algebraMap R S =
        Spec.map (CommRingCat.ofHom
          ((Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B) : B →+* S ⊗[R] B)) ≫
          Spec.algebraMap S B ≫ Spec.algebraMap R S) :
    pullback.lift _ _ h ≫ D.spec.act = Spec.map (CommRingCat.ofHom D.coaction.toRingHom) := by
  have : pullback.lift _ _ h = (tensorIso R S B).hom := by
    refine pullback.hom_ext ?_ ?_
    · exact (pullback.lift_fst _ _ _).trans tensorIso_hom_fst.symm
    · exact (pullback.lift_snd _ _ _).trans tensorIso_hom_snd.symm
  rw [this, spec_act, Iso.hom_inv_id_assoc]

/-- The coaction `B → S ⊗[R] B` whose `Spec` is the action of a descent datum on `Spec B`. -/
private noncomputable def coactionOfSpec
    (D : TauCeti.DescentDatum (Spec.algebraMap R S) (Over.mk (Spec.algebraMap S B))) :
    B →ₐ[S] S ⊗[R] B where
  toRingHom := (Spec.preimage ((tensorIso R S B).hom ≫ D.act :
    Spec (.of (S ⊗[R] B)) ⟶ Spec (.of B))).hom
  commutes' s := by
    have h : Spec.map (CommRingCat.ofHom (algebraMap S B) ≫
        Spec.preimage ((tensorIso R S B).hom ≫ D.act : Spec (.of (S ⊗[R] B)) ⟶ Spec (.of B))) =
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] B)) := by
      rw [Spec.map_comp, Spec.map_preimage, Category.assoc]
      exact (congrArg _ D.act_hom).trans tensorIso_hom_fst
    simpa [Algebra.TensorProduct.algebraMap_apply] using congr($(Spec.map_injective h).hom s)

private theorem coactionOfSpec_toRingHom
    (D : TauCeti.DescentDatum (Spec.algebraMap R S) (Over.mk (Spec.algebraMap S B))) :
    (coactionOfSpec D).toRingHom = (Spec.preimage ((tensorIso R S B).hom ≫ D.act :
      Spec (.of (S ⊗[R] B)) ⟶ Spec (.of B))).hom :=
  rfl

private theorem coactionOfSpec_apply
    (D : TauCeti.DescentDatum (Spec.algebraMap R S) (Over.mk (Spec.algebraMap S B))) (b : B) :
    coactionOfSpec D b = (Spec.preimage ((tensorIso R S B).hom ≫ D.act :
      Spec (.of (S ⊗[R] B)) ⟶ Spec (.of B))).hom b :=
  rfl

private theorem inv_spec_coactionOfSpec
    (D : TauCeti.DescentDatum (Spec.algebraMap R S) (Over.mk (Spec.algebraMap S B))) :
    (tensorIso R S B).inv ≫ Spec.map (CommRingCat.ofHom (coactionOfSpec D).toRingHom) =
      D.act := by
  rw [coactionOfSpec_toRingHom, CommRingCat.ofHom_hom, Spec.map_preimage, Iso.inv_hom_id_assoc]

/-- The descent datum on `B` whose `Spec` is a given descent datum on `Spec B`. -/
private noncomputable def ofSpec
    (D : TauCeti.DescentDatum (Spec.algebraMap R S) (Over.mk (Spec.algebraMap S B))) :
    DescentDatum R S B where
  coaction := coactionOfSpec D
  counit_coaction := (lift_act_iff _ _).1 (by rw [inv_spec_coactionOfSpec]; exact D.lift_act)
  coassoc := (act_assoc_iff _ D.act (inv_spec_coactionOfSpec D).symm _ _).1 D.act_assoc

private theorem ofSpec_coaction
    (D : TauCeti.DescentDatum (Spec.algebraMap R S) (Over.mk (Spec.algebraMap S B))) :
    (ofSpec D).coaction = coactionOfSpec D :=
  rfl

variable (R S B) in
/-- Descent data on `Spec B ⟶ Spec S` relative to `Spec S ⟶ Spec R` are the same as descent
data on the `S`-algebra `B` relative to `R → S`: the action is `Spec` of the coaction. -/
noncomputable def specEquiv :
    DescentDatum R S B ≃
      TauCeti.DescentDatum (Spec.algebraMap R S) (Over.mk (Spec.algebraMap S B)) where
  toFun := spec
  invFun := ofSpec
  left_inv D := by
    refine DescentDatum.ext (AlgHom.ext fun b ↦ ?_)
    rw [ofSpec_coaction, coactionOfSpec_apply, spec_act, Iso.hom_inv_id_assoc,
      Spec.preimage_map, CommRingCat.hom_ofHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  right_inv D := TauCeti.DescentDatum.ext (inv_spec_coactionOfSpec D)

@[simp]
theorem specEquiv_apply (D : DescentDatum R S B) : specEquiv R S B D = D.spec :=
  (rfl)

@[simp]
theorem spec_specEquiv_symm
    (D : TauCeti.DescentDatum (Spec.algebraMap R S) (Over.mk (Spec.algebraMap S B))) :
    ((specEquiv R S B).symm D).spec = D :=
  (specEquiv R S B).apply_symm_apply D

section Hom

variable {B' B'' : Type u} [CommRing B'] [Algebra R B'] [Algebra S B'] [IsScalarTower R S B']
  [CommRing B''] [Algebra R B''] [Algebra S B''] [IsScalarTower R S B'']
  {D : DescentDatum R S B} {D' : DescentDatum R S B'} {D'' : DescentDatum R S B''}

/-- Under the identifications with tensor products, `id ×_{Spec R} Spec f` is `Spec (id ⊗ f)`. -/
private theorem tensorIso_hom_map (f : B →ₐ[S] B')
    (g : (Over.mk (Spec.algebraMap S B')).left ⟶ (Over.mk (Spec.algebraMap S B)).left)
    (hg : g = Spec.map (CommRingCat.ofHom f.toRingHom)) (h₁ h₂) :
    (tensorIso R S B').hom ≫ pullback.map _ _ _ _ (𝟙 _) g (𝟙 _) h₁ h₂ =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id R S) (f.restrictScalars R)).toRingHom) ≫
        (tensorIso R S B).hom := by
  subst hg
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pullback.lift_fst, Category.comp_id, tensorIso_hom_fst, Category.assoc,
      tensorIso_hom_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext s
    simp
  · rw [Category.assoc, pullback.lift_snd, tensorIso_hom_snd_assoc, Category.assoc,
      tensorIso_hom_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    exact congrArg (fun φ ↦ Spec.map (CommRingCat.ofHom φ)) (RingHom.ext fun b ↦ by simp)

/-- A morphism of descent data on algebras induces a morphism, in the opposite direction, of the
descent data on their spectra. -/
noncomputable def Hom.spec (f : Hom D D') : TauCeti.DescentDatum.Hom D'.spec D.spec where
  hom := Over.homMk (Spec.map (CommRingCat.ofHom f.toAlgHom.toRingHom)) <| by
    have : Spec.map (CommRingCat.ofHom f.toAlgHom.toRingHom) ≫ Spec.algebraMap S B =
        Spec.algebraMap S B' := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext b
      simp
    exact this
  map_act := by
    rw [← cancel_epi (tensorIso R S B').hom, ← Category.assoc,
      tensorIso_hom_map f.toAlgHom _ (Over.homMk_left _ _) _ _, spec_act, spec_act]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Over.homMk_left]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    ext b
    exact (f.coaction_toAlgHom b).symm

@[simp]
theorem Hom.spec_hom_left (f : Hom D D') :
    f.spec.hom.left = Spec.map (CommRingCat.ofHom f.toAlgHom.toRingHom) :=
  (rfl)

variable (D) in
/-- `Hom.spec` preserves identities. -/
@[simp]
theorem Hom.id_spec : (Hom.id D).spec = TauCeti.DescentDatum.Hom.id D.spec :=
  TauCeti.DescentDatum.Hom.ext (Over.OverMorphism.ext (by simp))

/-- `Hom.spec` reverses composition. -/
@[simp]
theorem Hom.comp_spec (g : Hom D' D'') (f : Hom D D') : (g.comp f).spec = f.spec.comp g.spec := by
  refine TauCeti.DescentDatum.Hom.ext (Over.OverMorphism.ext ?_)
  rw [spec_hom_left, TauCeti.DescentDatum.Hom.comp_hom, Over.comp_left, spec_hom_left,
    spec_hom_left, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext b
  simp

end Hom

section BaseChange

variable (A : Type u) [CommRing A] [Algebra R A]

/-- The canonical descent datum on the base change `Spec A ×_{Spec R} Spec S` of an affine scheme
`Spec A` over `Spec R` is `Spec` of the canonical descent datum on `S ⊗[R] A`: the identification
`Spec A ×_{Spec R} Spec S ≅ Spec (S ⊗[R] A)` is an isomorphism of descent data. -/
noncomputable def specBaseChangeHom :
    TauCeti.DescentDatum.Hom
      (TauCeti.DescentDatum.baseChange (Spec.algebraMap R S) (Over.mk (Spec.algebraMap R A)))
      (baseChange R S A).spec where
  hom := (Over.isoMk (pullbackSymmetry _ _ ≪≫ pullbackSpecIso R S A) <| by
    simp [pullbackSpecIso_hom_fst']).hom
  map_act := by
    have h₁ : Spec.map (CommRingCat.ofHom (baseChange R S A).coaction.toRingHom) ≫
        (pullbackSpecIso R S A).inv ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] (S ⊗[R] A))) := by
      rw [pullbackSpecIso_inv_fst, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext s
      simp [Algebra.TensorProduct.one_def]
    have h₂ : Spec.map (CommRingCat.ofHom (baseChange R S A).coaction.toRingHom) ≫
        (pullbackSpecIso R S A).inv ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight :
            S ⊗[R] A →ₐ[R] S ⊗[R] (S ⊗[R] A)).toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom) := by
      rw [pullbackSpecIso_inv_snd, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
      congr 2
      ext a
      simp
    have h₃ : (pullbackSpecIso R S A).hom ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom) =
        pullback.snd _ _ :=
      pullbackSpecIso_hom_snd R S A
    rw [← cancel_mono (pullbackSpecIso R S A).inv]
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, spec_act, h₁, tensorIso_inv_fst, Over.isoMk_hom_left,
        Iso.trans_hom, Iso.hom_inv_id_assoc, pullback.lift_fst, Category.comp_id]
      have e : (pullbackSymmetry (Over.mk (Spec.algebraMap R A)).hom (Spec.algebraMap R S)).hom ≫
          pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
            (Spec.map (CommRingCat.ofHom (algebraMap R A))) = pullback.snd _ _ :=
        pullbackSymmetry_hom_comp_fst _ _
      rw [e]
      exact (TauCeti.DescentDatum.baseChange_act_snd _ _).symm
    · simp only [Category.assoc, spec_act, h₂, tensorIso_inv_snd_assoc, Over.isoMk_hom_left,
        Iso.trans_hom, Iso.hom_inv_id_assoc, pullback.lift_snd_assoc, h₃]
      have e : (pullbackSymmetry (Over.mk (Spec.algebraMap R A)).hom (Spec.algebraMap R S)).hom ≫
          pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
            (Spec.map (CommRingCat.ofHom (algebraMap R A))) = pullback.fst _ _ :=
        pullbackSymmetry_hom_comp_snd _ _
      rw [e]
      exact (TauCeti.DescentDatum.baseChange_act_fst _ _).symm

@[simp]
theorem specBaseChangeHom_hom_left :
    (specBaseChangeHom (R := R) (S := S) A).hom.left =
      (pullbackSymmetry _ _).hom ≫ (pullbackSpecIso R S A).hom :=
  (rfl)

instance : IsIso (specBaseChangeHom (R := R) (S := S) A).hom := by
  rw [specBaseChangeHom]
  infer_instance

end BaseChange

section Effective

variable [Module.Flat R S] (D : DescentDatum R S B)

/-- **Effective descent for affine schemes.** If `S` is flat over `R`, the descent datum
`D.spec` on `Spec B` is isomorphic (`isIso_specDescendedHom_hom`) to the canonical descent datum
on the base change of the affine scheme `Spec D.descended` over `Spec R`. -/
noncomputable def specDescendedHom :
    TauCeti.DescentDatum.Hom
      (TauCeti.DescentDatum.baseChange (Spec.algebraMap R S)
        (Over.mk (Spec.algebraMap R D.descended)))
      D.spec :=
  (Hom.spec D.toBaseChangeDescended).comp (specBaseChangeHom D.descended)

@[simp]
theorem specDescendedHom_hom :
    D.specDescendedHom.hom =
      (specBaseChangeHom D.descended).hom ≫ D.toBaseChangeDescended.spec.hom := by
  rw [specDescendedHom, TauCeti.DescentDatum.Hom.comp_hom]

instance isIso_specDescendedHom_hom : IsIso D.specDescendedHom.hom := by
  have : IsIso (CommRingCat.ofHom D.toBaseChangeDescended.toAlgHom.toRingHom) := by
    rw [toBaseChangeDescended_toAlgHom]
    exact (ConcreteCategory.isIso_iff_bijective _).mpr D.baseChangeEquiv.symm.bijective
  have : IsIso ((Over.forget _).map (Hom.spec D.toBaseChangeDescended).hom) := by
    rw [Over.forget_map, Hom.spec_hom_left]
    infer_instance
  have : IsIso (Hom.spec D.toBaseChangeDescended).hom :=
    isIso_of_reflects_iso _ (Over.forget _)
  rw [specDescendedHom_hom]
  infer_instance

end Effective

end DescentDatum

end Algebra

namespace DescentDatum

open Algebra.DescentDatum

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- **Effective descent for affine schemes.** Let `S` be flat over `R` (for instance faithfully
flat). Every descent datum on an affine scheme `X ⟶ Spec S` relative to `Spec S ⟶ Spec R` is
effective: it is isomorphic to the canonical descent datum on the base change of an affine
scheme over `Spec R`. -/
theorem exists_isAffine_baseChange_hom_isIso [Module.Flat R S] {X : Over (Spec (.of S))}
    [IsAffine X.left] (D : DescentDatum (Spec.algebraMap R S) X) :
    ∃ X₀ : Over (Spec (.of R)), IsAffine X₀.left ∧
      ∃ f : Hom (baseChange (Spec.algebraMap R S) X₀) D, IsIso f.hom := by
  -- Present `X` as `Spec B ⟶ Spec S` for `B = Γ(X, ⊤)`, an `S`-algebra through `X.hom`.
  let φ : CommRingCat.of S ⟶ Γ(X.left, ⊤) := (Scheme.ΓSpecIso (.of S)).inv ≫ X.hom.appTop
  let _ : Algebra S Γ(X.left, ⊤) := φ.hom.toAlgebra
  let _ : Algebra R Γ(X.left, ⊤) := (φ.hom.comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R S Γ(X.left, ⊤) := .of_algebraMap_eq fun _ ↦ rfl
  let e : Over.mk (Spec.algebraMap S Γ(X.left, ⊤)) ≅ X := (Over.isoMk X.left.isoSpec <| by
    simp only [Over.mk_hom, Spec.algebraMap, RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom]
    rw [Spec.map_comp, Scheme.isoSpec_hom_naturality_assoc, Scheme.isoSpec_Spec_hom,
      ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.comp_id]).symm
  obtain ⟨E, g, hg⟩ : ∃ (E : Algebra.DescentDatum R S Γ(X.left, ⊤)) (g : Hom E.spec D),
      IsIso g.hom := by
    refine ⟨(specEquiv R S _).symm (transport e D), ?_⟩
    rw [spec_specEquiv_symm]
    exact ⟨transportHom e D, by rw [transportHom_hom]; infer_instance⟩
  refine ⟨_, inferInstanceAs (IsAffine (Spec _)), g.comp E.specDescendedHom, ?_⟩
  rw [Hom.comp_hom]
  infer_instance

end DescentDatum

end TauCeti
