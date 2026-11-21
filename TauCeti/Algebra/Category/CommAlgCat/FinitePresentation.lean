/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import TauCeti.Algebra.Category.CommAlgCat.BaseChange
public import TauCeti.Algebra.Category.CommAlgCat.FilteredColimits

/-!
# Finitely presented algebras over a filtered colimit of base changes

Let `D` be a small filtered diagram of commutative `R`-algebras with colimit `H`, and let `T` be
an `R`-algebra. Then `H ⊗[R] T` is the filtered colimit of the algebras `D j ⊗[R] T`, since base
change along `R → T` is a left adjoint (`CommAlgCat.extendRestrictScalarsAdj`). Consequently
`Hom_R(S, - ⊗[R] T)` commutes with this colimit when `S` is finitely presented: an `R`-algebra
map `S → H ⊗[R] T` factors through some `D j ⊗[R] T`, and two maps into a stage that agree in the
colimit already agree at a later stage.

Applying both statements to an `H`-algebra isomorphism `H ⊗[R] S ≃ H ⊗[R] T` and its inverse,
for `S` and `T` finitely presented, shows that the isomorphism is the base change of a
`D j`-algebra isomorphism `D j ⊗[R] S ≃ D j ⊗[R] T` at some stage. This is the affine case of
the descent of morphisms of finitely presented schemes along limits of affine schemes.

## Main results

* `TauCeti.CommAlgCat.exists_algHom_comp_eq_of_isColimit`: an `R`-algebra map from a finitely
  presented `R`-algebra into `H ⊗[R] T` factors through a stage `D j ⊗[R] T`.
* `TauCeti.CommAlgCat.exists_algHom_comp_eq_comp_of_isColimit`: two `R`-algebra maps from an
  essentially finite type `R`-algebra into a stage that agree in `H ⊗[R] T` agree at a later stage.
* `TauCeti.CommAlgCat.exists_algEquiv_tensorProduct_of_isColimit`: an `H`-algebra isomorphism
  `H ⊗[R] S ≃ H ⊗[R] T` between base changes of finitely presented `R`-algebras is the base
  change of an isomorphism at some stage.

## References

* [Stacks Project, Lemma 10.127.8](https://stacks.math.columbia.edu/tag/05N9), for maps out of
  finitely presented algebras into filtered colimits, which Mathlib proves as
  `RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit` and
  `RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit`.
* [Stacks Project, Lemma 32.10.1](https://stacks.math.columbia.edu/tag/01ZM), whose affine case
  is the descent of isomorphisms.
-/

public section

open CategoryTheory Limits
open Algebra.TensorProduct (comm includeRight liftEquivRight map)
open scoped TensorProduct

universe u

namespace TauCeti.CommAlgCat

variable {R : Type u} [CommRing R] {J : Type u} [SmallCategory J] [IsFiltered J]
  {D : J ⥤ CommAlgCat.{u} R} {c : Cocone D}
  {T : Type u} [CommRing T] [Algebra R T]

variable (T) in
/-- The rings `T ⊗[R] D j`, the base changes of the stages, as a diagram of commutative rings. -/
private noncomputable abbrev tensorDiagram : J ⥤ CommRingCat.{u} :=
  D ⋙ CommAlgCat.extendScalars.{u, u, u} R T ⋙ forget₂ (CommAlgCat.{u} T) CommRingCat.{u}

variable (T) in
/-- The structure maps `R → T ⊗[R] D j`, as a natural transformation from the constant diagram. -/
private noncomputable def tensorStructureMap :
    (Functor.const J).obj (CommRingCat.of R) ⟶ tensorDiagram (D := D) T where
  app j := CommRingCat.ofHom (algebraMap R (T ⊗[R] D.obj j))
  naturality j k f := by
    ext x
    exact ((map (AlgHom.id R T) (D.map f).hom).commutes x).symm

variable (T) in
/-- `T ⊗[R] H` is the filtered colimit of the rings `T ⊗[R] D j`. -/
private noncomputable def isColimitTensor (hc : IsColimit c) :
    IsColimit ((forget₂ (CommAlgCat.{u} T) CommRingCat.{u}).mapCocone
      ((CommAlgCat.extendScalars.{u, u, u} R T).mapCocone c)) := by
  have : PreservesColimitsOfShape J
      (forget₂ (CommAlgCat.{u} T) CommRingCat.{u} ⋙ forget CommRingCat.{u}) :=
    preservesColimitsOfShape_of_natIso (eqToIso HasForget₂.forget_comp).symm
  have : PreservesColimitsOfShape J (forget₂ (CommAlgCat.{u} T) CommRingCat.{u}) :=
    preservesColimitsOfShape_of_reflects_of_preserves _ (forget CommRingCat.{u})
  exact isColimitOfPreserves _ (isColimitOfPreserves _ hc)

/-- An `R`-algebra map from a finitely presented `R`-algebra into `T ⊗[R] H` factors through
`T ⊗[R] D j` for some stage `j`. This is the form with `T` on the left used in the proofs. -/
private theorem exists_algHom_comp_eq_of_isColimit_left (hc : IsColimit c) {S : Type u}
    [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S] (g : S →ₐ[R] T ⊗[R] c.pt) :
    ∃ (j : J) (g' : S →ₐ[R] T ⊗[R] D.obj j), (map (AlgHom.id R T) (c.ι.app j).hom).comp g' = g := by
  obtain ⟨j, g', hg', hg⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
    (CommRingCat.of R) (tensorDiagram (D := D) T) (tensorStructureMap T)
    (CommRingCat.ofHom (algebraMap R S)) _ (isColimitTensor T hc)
    (RingHom.finitePresentation_algebraMap.mpr inferInstance) (CommRingCat.ofHom g.toRingHom)
    fun j ↦ by ext x; simp [tensorStructureMap]
  refine ⟨j, { g'.hom with commutes' := fun x ↦ congr(CommRingCat.Hom.hom $hg' x) },
    AlgHom.ext fun x ↦ ?_⟩
  exact congr(CommRingCat.Hom.hom $hg x).symm

/-- An `R`-algebra map from a finitely presented `R`-algebra `S` into `H ⊗[R] T`, for `H` the
colimit of a small filtered diagram `D` of `R`-algebras, factors through `D j ⊗[R] T` for some
stage `j`. -/
theorem exists_algHom_comp_eq_of_isColimit (hc : IsColimit c) {S : Type u} [CommRing S]
    [Algebra R S] [Algebra.FinitePresentation R S] (g : S →ₐ[R] c.pt ⊗[R] T) :
    ∃ (j : J) (g' : S →ₐ[R] D.obj j ⊗[R] T),
      (map (c.ι.app j).hom (AlgHom.id R T)).comp g' = g := by
  obtain ⟨j, g', hg'⟩ := exists_algHom_comp_eq_of_isColimit_left hc
    ((comm R c.pt T).toAlgHom.comp g)
  refine ⟨j, (comm R T (D.obj j)).toAlgHom.comp g', ?_⟩
  ext x
  have hx := congr($hg' x)
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] at hx ⊢
  rw [← Algebra.TensorProduct.comm_comp_map_apply, hx, ← Algebra.TensorProduct.comm_symm]
  exact (comm R c.pt T).symm_apply_apply _

/-- The ring map underlying the base change `T ⊗[R] A → T ⊗[R] B` of an `R`-algebra map does not
depend on whether it is read over `R` or over `T`. -/
private theorem map_id_apply_eq {A B : Type u} [CommRing A] [Algebra R A] [CommRing B]
    [Algebra R B] (φ : A →ₐ[R] B) (x : T ⊗[R] A) :
    map (AlgHom.id T T) φ x = map (AlgHom.id R T) φ x := by
  induction x using TensorProduct.inductionOn with
  | tmul t a => simp
  | add y z hy hz => simp only [map_add, hy, hz]

/-- Two `R`-algebra maps from an essentially finite type `R`-algebra into `T ⊗[R] D j` that agree
in `T ⊗[R] H` agree at a later stage. This is the form with `T` on the left used in the proofs. -/
private theorem exists_algHom_comp_eq_comp_of_isColimit_left (hc : IsColimit c) {S : Type u}
    [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S] {j : J}
    {g₁ g₂ : S →ₐ[R] T ⊗[R] D.obj j} (h : (map (AlgHom.id R T) (c.ι.app j).hom).comp g₁ =
      (map (AlgHom.id R T) (c.ι.app j).hom).comp g₂) :
    ∃ (k : J) (f : j ⟶ k), (map (AlgHom.id R T) (D.map f).hom).comp g₁ =
      (map (AlgHom.id R T) (D.map f).hom).comp g₂ := by
  obtain ⟨k, f₁, f₂, hk⟩ := RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit
    (CommRingCat.of R) (tensorDiagram (D := D) T) (tensorStructureMap T)
    (CommRingCat.ofHom (algebraMap R S)) _ (isColimitTensor T hc)
    (RingHom.essFiniteType_algebraMap.mpr inferInstance) (CommRingCat.ofHom g₁.toRingHom)
    (by ext x; simp [tensorStructureMap]) (CommRingCat.ofHom g₂.toRingHom)
    (by ext x; simp [tensorStructureMap])
    (by ext x; simpa [map_id_apply_eq] using congr($h x))
  -- The two maps `j ⟶ k` need not agree; coequalize them.
  refine ⟨IsFiltered.coeq f₁ f₂, f₁ ≫ IsFiltered.coeqHom f₁ f₂, AlgHom.ext fun x ↦ ?_⟩
  have hx := congr(map (AlgHom.id T T) (D.map (IsFiltered.coeqHom f₁ f₂)).hom
    (CommRingCat.Hom.hom $hk x))
  simp only [AlgHom.comp_apply, ← map_id_apply_eq]
  conv_rhs => rw [IsFiltered.coeq_condition f₁ f₂]
  simpa [Algebra.TensorProduct.map_id_comp] using hx

/-- Two `R`-algebra maps from an essentially finite type `R`-algebra `S` into `D j ⊗[R] T` that
agree in `H ⊗[R] T`, for `H` the colimit of a small filtered diagram `D` of `R`-algebras, agree
at a later stage. -/
theorem exists_algHom_comp_eq_comp_of_isColimit (hc : IsColimit c) {S : Type u} [CommRing S]
    [Algebra R S] [Algebra.EssFiniteType R S] {j : J} {g₁ g₂ : S →ₐ[R] D.obj j ⊗[R] T}
    (h : (map (c.ι.app j).hom (AlgHom.id R T)).comp g₁ =
      (map (c.ι.app j).hom (AlgHom.id R T)).comp g₂) :
    ∃ (k : J) (f : j ⟶ k), (map (D.map f).hom (AlgHom.id R T)).comp g₁ =
      (map (D.map f).hom (AlgHom.id R T)).comp g₂ := by
  -- Move `T` to the left, where the stages are the base changes of `D` along `R → T`.
  have hcomm {A B : CommAlgCat.{u} R} (φ : A ⟶ B) (g : S →ₐ[R] A ⊗[R] T) :
      (map (AlgHom.id R T) φ.hom).comp ((comm R A T).toAlgHom.comp g) =
          (comm R B T).toAlgHom.comp ((map φ.hom (AlgHom.id R T)).comp g) := by
    rw [← AlgHom.comp_assoc, ← AlgHom.comp_assoc, Algebra.TensorProduct.comm_comp_map]
  obtain ⟨k, f, hk⟩ := exists_algHom_comp_eq_comp_of_isColimit_left hc
    (g₁ := (comm R (D.obj j) T).toAlgHom.comp g₁)
    (g₂ := (comm R (D.obj j) T).toAlgHom.comp g₂)
    (by rw [hcomm, hcomm, h])
  refine ⟨k, f, ?_⟩
  rw [hcomm, hcomm] at hk
  exact (AlgHom.cancel_left (comm R (D.obj k) T).injective).mp hk

section Descent

variable {A B M N : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  [CommRing M] [Algebra R M] [CommRing N] [Algebra R N]

/-- `liftEquivRight` restricts to the given map on `M`. -/
private theorem liftEquivRight_comp_includeRight (φ : M →ₐ[R] A ⊗[R] N) :
    ((liftEquivRight R A M _ φ).restrictScalars R).comp includeRight = φ := by
  ext; simp

/-- `liftEquivRight` is compatible with base change along an `R`-algebra map `ρ : A → B`. -/
private theorem liftEquivRight_comp_map (ρ : A →ₐ[R] B) (φ : M →ₐ[R] A ⊗[R] N) :
    ((liftEquivRight R _ _ _ ((map ρ (AlgHom.id R N)).comp φ)).restrictScalars R).comp
        (map ρ (AlgHom.id R M)) =
      (map ρ (AlgHom.id R N)).comp ((liftEquivRight R _ _ _ φ).restrictScalars R) := by
  ext <;> simp

/-- `liftEquivRight` of the restriction of an `A`-algebra map `A ⊗[R] M → A ⊗[R] N` to `M`
recovers it. -/
private theorem liftEquivRight_restrictScalars_comp_includeRight (e : A ⊗[R] M →ₐ[A] A ⊗[R] N) :
    liftEquivRight R A M _ ((e.restrictScalars R).comp includeRight) = e :=
  Algebra.TensorProduct.ext (Subsingleton.elim _ _) (liftEquivRight_comp_includeRight _)

/-- If two maps `φ : M → A ⊗[R] N` and `ψ : N → A ⊗[R] M` extend to mutually inverse maps after
base change along `ρ : A → B` on `M`, then the base-changed extensions compose to the identity. -/
private theorem liftEquivRight_comp_liftEquivRight (ρ : A →ₐ[R] B) (φ : M →ₐ[R] A ⊗[R] N)
    (ψ : N →ₐ[R] A ⊗[R] M)
    (h : (map ρ (AlgHom.id R M)).comp
        (((liftEquivRight R _ _ _ ψ).restrictScalars R).comp φ) =
      (map ρ (AlgHom.id R M)).comp includeRight) :
    (liftEquivRight R _ _ _ ((map ρ (AlgHom.id R M)).comp ψ)).comp
        (liftEquivRight R _ _ _ ((map ρ (AlgHom.id R N)).comp φ)) = AlgHom.id B _ := by
  refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AlgHom.ext fun x ↦ ?_)
  have h₁ := congr($(liftEquivRight_comp_includeRight ((map ρ (AlgHom.id R N)).comp φ)) x)
  have h₂ := congr($(liftEquivRight_comp_map ρ ψ) (φ x))
  have h₃ := congr($h x)
  simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at h₁ h₂ h₃ ⊢
  rw [h₁, h₂, h₃]
  simp

end Descent

omit [IsFiltered J] in
/-- Base change along a transition map followed by the colimit leg is the colimit leg. -/
private theorem map_ι_comp_map {M : Type u} [CommRing M] [Algebra R M] {j k : J} (f : j ⟶ k) :
    (map (c.ι.app k).hom (AlgHom.id R M)).comp (map (D.map f).hom (AlgHom.id R M)) =
      map (c.ι.app j).hom (AlgHom.id R M) := by
  rw [← Algebra.TensorProduct.map_comp, AlgHom.comp_id, ← CommAlgCat.hom_comp, c.w f]

omit [IsFiltered J] in
/-- Base change along two composable transition maps is base change along their composite. -/
private theorem map_comp_map {M : Type u} [CommRing M] [Algebra R M] {j k l : J} (f : j ⟶ k)
    (g : k ⟶ l) :
    (map (D.map g).hom (AlgHom.id R M)).comp (map (D.map f).hom (AlgHom.id R M)) =
      map (D.map (f ≫ g)).hom (AlgHom.id R M) := by
  rw [← Algebra.TensorProduct.map_comp, AlgHom.comp_id, ← CommAlgCat.hom_comp, D.map_comp]

/-- One half of the descent of an isomorphism: if `φ` and `ψ` are stage models of the
restrictions of `e` and `e⁻¹` to `S` and `T`, then `liftEquivRight ψ` after `φ` becomes the
inclusion of `S` at a later stage. -/
private theorem exists_liftEquivRight_comp_eq_includeRight (hc : IsColimit c) {S : Type u}
    [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S]
    (e : c.pt ⊗[R] S ≃ₐ[c.pt] c.pt ⊗[R] T) {j : J}
    (φ : S →ₐ[R] D.obj j ⊗[R] T) (ψ : T →ₐ[R] D.obj j ⊗[R] S)
    (hφ : (map (c.ι.app j).hom (AlgHom.id R T)).comp φ =
      (e.toAlgHom.restrictScalars R).comp includeRight)
    (hψ : (map (c.ι.app j).hom (AlgHom.id R S)).comp ψ =
      (e.symm.toAlgHom.restrictScalars R).comp includeRight) :
    ∃ (k : J) (f : j ⟶ k),
      (map (D.map f).hom (AlgHom.id R S)).comp
          (((liftEquivRight R _ _ _ ψ).restrictScalars R).comp φ) =
        (map (D.map f).hom (AlgHom.id R S)).comp includeRight := by
  refine exists_algHom_comp_eq_comp_of_isColimit hc ?_
  rw [← AlgHom.comp_assoc, ← liftEquivRight_comp_map, hψ,
    liftEquivRight_restrictScalars_comp_includeRight, AlgHom.comp_assoc, hφ]
  ext s
  simp

/-- An `H`-algebra isomorphism `H ⊗[R] S ≃ H ⊗[R] T`, for `H` the colimit of a small filtered
diagram `D` of `R`-algebras and `S`, `T` finitely presented `R`-algebras, is the base change of a
`D j`-algebra isomorphism `D j ⊗[R] S ≃ D j ⊗[R] T` at some stage `j`: the two agree on `S`. -/
theorem exists_algEquiv_tensorProduct_of_isColimit (hc : IsColimit c) {S : Type u} [CommRing S]
    [Algebra R S] [Algebra.FinitePresentation R S] [Algebra.FinitePresentation R T]
    (e : c.pt ⊗[R] S ≃ₐ[c.pt] c.pt ⊗[R] T) :
    ∃ (j : J) (e' : D.obj j ⊗[R] S ≃ₐ[D.obj j] D.obj j ⊗[R] T), ∀ s : S,
      map (c.ι.app j).hom (AlgHom.id R T) (e' (1 ⊗ₜ s)) = e (1 ⊗ₜ s) := by
  -- Descend the restrictions of `e` and `e⁻¹` to a common stage `j`.
  obtain ⟨j₁, φ₁, hφ₁⟩ := exists_algHom_comp_eq_of_isColimit hc
    ((e.toAlgHom.restrictScalars R).comp includeRight)
  obtain ⟨j₂, ψ₂, hψ₂⟩ := exists_algHom_comp_eq_of_isColimit hc
    ((e.symm.toAlgHom.restrictScalars R).comp includeRight)
  let j := IsFiltered.max j₁ j₂
  let φ := (map (D.map (IsFiltered.leftToMax j₁ j₂)).hom (AlgHom.id R T)).comp φ₁
  let ψ := (map (D.map (IsFiltered.rightToMax j₁ j₂)).hom (AlgHom.id R S)).comp ψ₂
  have hφ : (map (c.ι.app j).hom (AlgHom.id R T)).comp φ =
      (e.toAlgHom.restrictScalars R).comp includeRight := by
    rw [← hφ₁, ← map_ι_comp_map (IsFiltered.leftToMax j₁ j₂), AlgHom.comp_assoc]
  have hψ : (map (c.ι.app j).hom (AlgHom.id R S)).comp ψ =
      (e.symm.toAlgHom.restrictScalars R).comp includeRight := by
    rw [← hψ₂, ← map_ι_comp_map (IsFiltered.rightToMax j₁ j₂), AlgHom.comp_assoc]
  -- Both composites become the identity at a common later stage `l`, reached by `ρ`.
  obtain ⟨k₁, f₁, h₁⟩ := exists_liftEquivRight_comp_eq_includeRight hc e φ ψ hφ hψ
  obtain ⟨k₂, f₂, h₂⟩ :=
    exists_liftEquivRight_comp_eq_includeRight hc e.symm ψ φ hψ (by simpa using hφ)
  obtain ⟨l, g₁, g₂, hg⟩ := IsFiltered.span f₁ f₂
  let ρ := (D.map (f₁ ≫ g₁)).hom
  have h₁' := congr((map (D.map g₁).hom (AlgHom.id R S)).comp $h₁)
  have h₂' := congr((map (D.map g₂).hom (AlgHom.id R T)).comp $h₂)
  simp only [← AlgHom.comp_assoc, map_comp_map, ← hg] at h₁' h₂'
  refine ⟨l, AlgEquiv.ofAlgHom
    (liftEquivRight R _ _ _ ((map ρ (AlgHom.id R T)).comp φ))
    (liftEquivRight R _ _ _ ((map ρ (AlgHom.id R S)).comp ψ))
    (liftEquivRight_comp_liftEquivRight ρ ψ φ (by simpa only [AlgHom.comp_assoc] using h₂'))
    (liftEquivRight_comp_liftEquivRight ρ φ ψ (by simpa only [AlgHom.comp_assoc] using h₁')),
    fun s ↦ ?_⟩
  have hs := congr($hφ s)
  rw [← map_ι_comp_map (f₁ ≫ g₁)] at hs
  simpa [ρ, ← Algebra.TensorProduct.one_def] using hs

end TauCeti.CommAlgCat
