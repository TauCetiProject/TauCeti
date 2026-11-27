/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import TauCeti.Algebra.Category.CommAlgCat.BaseChange
public import TauCeti.Algebra.Category.CommAlgCat.FilteredColimits
import TauCeti.RingTheory.TensorProduct.LiftEquiv

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

* `CategoryTheory.Limits.IsColimit.exists_algHom_comp_eq`: an `R`-algebra map from a finitely
  presented `R`-algebra into `H ⊗[R] T` factors through a stage `D j ⊗[R] T`.
* `CategoryTheory.Limits.IsColimit.exists_algHom_comp_eq_comp`: two `R`-algebra maps from an
  essentially finite type `R`-algebra into a stage that agree in `H ⊗[R] T` agree at a later stage.
* `CategoryTheory.Limits.IsColimit.exists_algEquiv_tensorProduct`: an `H`-algebra isomorphism
  `H ⊗[R] S ≃ H ⊗[R] T` between base changes of finitely presented `R`-algebras is the base
  change of an isomorphism at some stage.

## References

* [Stacks Project, Lemma 10.127.8](https://stacks.math.columbia.edu/tag/05N9), for maps out of
  finitely presented algebras into filtered colimits, which Mathlib proves as
  `RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit` and
  `RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit`.
* [Stacks Project, Lemma 32.10.1](https://stacks.math.columbia.edu/tag/01ZM), whose affine case
  is the descent of isomorphisms.

## Implementation notes

The index category `J` may live in any universes no larger than that of the rings, so that, for
instance, `ℕ`-indexed colimits of rings in any universe are covered. The `UnivLE` hypotheses
express this smallness; they let the forgetful functors to commutative rings and to types preserve
colimits of shape `J` (`CategoryTheory.Limits.preservesFilteredColimitsOfSize_of_univLE`).
-/

public section

open CategoryTheory Limits
open Algebra.TensorProduct (comm includeRight liftEquivRight map)
open AlgHom (liftEquivRight_comp_liftEquivRight_eq_id liftEquivRight_comp_map)
open scoped TensorProduct

universe u v w

namespace TauCeti.CommAlgCat

variable {R : Type u} [CommRing R] {J : Type v} [Category.{w} J] [IsFiltered J]
  [UnivLE.{v, u}] [UnivLE.{w, u}] {D : J ⥤ CommAlgCat.{u} R} {c : Cocone D}
  {T : Type u} [CommRing T] [Algebra R T]

variable (T) in
/-- The rings `T ⊗[R] D j`, the base changes of the stages, as a diagram of commutative rings. -/
private noncomputable abbrev tensorDiagram : J ⥤ CommRingCat.{u} :=
  D ⋙ CommAlgCat.extendScalars.{u, u, u} R T ⋙ forget₂ (CommAlgCat.{u} T) CommRingCat.{u}

omit [IsFiltered J] [UnivLE.{v, u}] [UnivLE.{w, u}] in
/-- The transition maps of the diagram `T ⊗[R] D j` are the base changes of those of `D`. -/
private theorem tensorDiagram_map {j k : J} (f : j ⟶ k) :
    (tensorDiagram (D := D) T).map f =
      CommRingCat.ofHom (map (AlgHom.id R T) (D.map f).hom).toRingHom := by
  rw [Functor.comp_map, Functor.comp_map, CommAlgCat.forget₂_commRingCat_map_extendScalars_map]

variable (T) in
/-- The structure maps `R → T ⊗[R] D j`, as a natural transformation from the constant diagram. -/
private noncomputable def tensorStructureMap :
    (Functor.const J).obj (CommRingCat.of R) ⟶ tensorDiagram (D := D) T where
  app j := CommRingCat.ofHom (algebraMap R (T ⊗[R] D.obj j))
  naturality j k f := by
    rw [tensorDiagram_map]
    ext x
    exact ((map (AlgHom.id R T) (D.map f).hom).commutes x).symm

variable (T) in
/-- `T ⊗[R] H` is the filtered colimit of the rings `T ⊗[R] D j`. -/
private noncomputable def isColimitTensor (hc : IsColimit c) :
    IsColimit ((forget₂ (CommAlgCat.{u} T) CommRingCat.{u}).mapCocone
      ((CommAlgCat.extendScalars.{u, u, u} R T).mapCocone c)) := by
  have : PreservesFilteredColimitsOfSize.{w, v} (forget₂ (CommAlgCat.{u} T) CommRingCat.{u}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u, u, w, v} _
  exact isColimitOfPreserves _ (isColimitOfPreserves _ hc)

omit [IsFiltered J] [UnivLE.{v, u}] [UnivLE.{w, u}] in
/-- The legs `T ⊗[R] D j → T ⊗[R] H` of the colimit cocone of `isColimitTensor` are the base
changes of the legs of `c`. -/
private theorem isColimitTensor_ι_app (j : J) :
    ((forget₂ (CommAlgCat.{u} T) CommRingCat.{u}).mapCocone
      ((CommAlgCat.extendScalars.{u, u, u} R T).mapCocone c)).ι.app j =
      CommRingCat.ofHom (map (AlgHom.id R T) (c.ι.app j).hom).toRingHom := by
  rw [Functor.mapCocone_ι_app, Functor.mapCocone_ι_app,
    CommAlgCat.forget₂_commRingCat_map_extendScalars_map]

/-- An `R`-algebra map from a finitely presented `R`-algebra into `T ⊗[R] H` factors through
`T ⊗[R] D j` for some stage `j`. This is the form with `T` on the left used in the proofs. -/
private theorem exists_algHom_comp_eq_of_isColimit_left (hc : IsColimit c) {S : Type u}
    [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S] (g : S →ₐ[R] T ⊗[R] c.pt) :
    ∃ (j : J) (g' : S →ₐ[R] T ⊗[R] D.obj j), (map (AlgHom.id R T) (c.ι.app j).hom).comp g' = g := by
  have : PreservesFilteredColimitsOfSize.{w, v} (forget CommRingCat.{u}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u, u, w, v} _
  obtain ⟨j, g', hg', hg⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
    (CommRingCat.of R) (tensorDiagram (D := D) T) (tensorStructureMap T)
    (CommRingCat.ofHom (algebraMap R S)) _ (isColimitTensor.{u, v, w} T hc)
    (RingHom.finitePresentation_algebraMap.mpr inferInstance) (CommRingCat.ofHom g.toRingHom)
    fun j ↦ by
      rw [isColimitTensor_ι_app]
      ext x
      simp [tensorStructureMap]
  refine ⟨j, { g'.hom with commutes' := fun x ↦ congr(CommRingCat.Hom.hom $hg' x) },
    AlgHom.ext fun x ↦ ?_⟩
  rw [isColimitTensor_ι_app] at hg
  exact congr(CommRingCat.Hom.hom $hg x).symm

/-- An `R`-algebra map from a finitely presented `R`-algebra `S` into `H ⊗[R] T`, for `H` the
colimit of a small filtered diagram `D` of `R`-algebras, factors through `D j ⊗[R] T` for some
stage `j`. -/
theorem _root_.CategoryTheory.Limits.IsColimit.exists_algHom_comp_eq (hc : IsColimit c)
    {S : Type u} [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
    (g : S →ₐ[R] c.pt ⊗[R] T) :
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

/-- Two `R`-algebra maps from an essentially finite type `R`-algebra into `T ⊗[R] D j` that agree
in `T ⊗[R] H` agree at a later stage. This is the form with `T` on the left used in the proofs. -/
private theorem exists_algHom_comp_eq_comp_of_isColimit_left (hc : IsColimit c) {S : Type u}
    [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S] {j : J}
    {g₁ g₂ : S →ₐ[R] T ⊗[R] D.obj j} (h : (map (AlgHom.id R T) (c.ι.app j).hom).comp g₁ =
      (map (AlgHom.id R T) (c.ι.app j).hom).comp g₂) :
    ∃ (k : J) (f : j ⟶ k), (map (AlgHom.id R T) (D.map f).hom).comp g₁ =
      (map (AlgHom.id R T) (D.map f).hom).comp g₂ := by
  have : PreservesFilteredColimitsOfSize.{w, v} (forget CommRingCat.{u}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u, u, w, v} _
  have hstr (g : S →ₐ[R] T ⊗[R] D.obj j) : CommRingCat.ofHom (algebraMap R S) ≫
      CommRingCat.ofHom g.toRingHom = (tensorStructureMap T).app j := by
    ext x
    simp [tensorStructureMap]
  obtain ⟨k, f₁, f₂, hk⟩ := RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit
    (CommRingCat.of R) (tensorDiagram (D := D) T) (tensorStructureMap T)
    (CommRingCat.ofHom (algebraMap R S)) _ (isColimitTensor.{u, v, w} T hc)
    (RingHom.essFiniteType_algebraMap.mpr inferInstance) (CommRingCat.ofHom g₁.toRingHom)
    (hstr g₁) (CommRingCat.ofHom g₂.toRingHom) (hstr g₂) (by
      rw [isColimitTensor_ι_app]
      ext x
      exact congr($h x))
  have hk' : (map (AlgHom.id R T) (D.map f₁).hom).comp g₁ =
      (map (AlgHom.id R T) (D.map f₂).hom).comp g₂ := by
    rw [tensorDiagram_map, tensorDiagram_map] at hk
    ext x
    exact congr(CommRingCat.Hom.hom $hk x)
  -- The two maps `j ⟶ k` need not agree; coequalize them.
  refine ⟨IsFiltered.coeq f₁ f₂, f₁ ≫ IsFiltered.coeqHom f₁ f₂, ?_⟩
  conv_rhs => rw [IsFiltered.coeq_condition f₁ f₂]
  simp only [D.map_comp, CommAlgCat.hom_comp, Algebra.TensorProduct.map_id_comp,
    AlgHom.comp_assoc, hk']

/-- Two `R`-algebra maps from an essentially finite type `R`-algebra `S` into `D j ⊗[R] T` that
agree in `H ⊗[R] T`, for `H` the colimit of a small filtered diagram `D` of `R`-algebras, agree
at a later stage. -/
theorem _root_.CategoryTheory.Limits.IsColimit.exists_algHom_comp_eq_comp (hc : IsColimit c)
    {S : Type u} [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S] {j : J}
    {g₁ g₂ : S →ₐ[R] D.obj j ⊗[R] T}
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

omit [IsFiltered J] [UnivLE.{v, u}] [UnivLE.{w, u}] in
/-- A factorization `φ` of `g` through the stage `D j ⊗[R] M` gives one through any later stage,
by base change along the transition map. -/
private theorem map_ι_comp_map_comp {M N : Type u} [CommRing M] [Algebra R M] [Semiring N]
    [Algebra R N] {j k : J} (f : j ⟶ k) {φ : N →ₐ[R] D.obj j ⊗[R] M} {g : N →ₐ[R] c.pt ⊗[R] M}
    (h : (map (c.ι.app j).hom (AlgHom.id R M)).comp φ = g) :
    (map (c.ι.app k).hom (AlgHom.id R M)).comp ((map (D.map f).hom (AlgHom.id R M)).comp φ) =
      g := by
  rw [← AlgHom.comp_assoc, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id, ← CommAlgCat.hom_comp,
    c.w f, h]

/-- Half of the descent of an isomorphism: if `φ` and `ψ` are stage models of the restrictions of
`e` and `e⁻¹` to `S` and `T`, then from some transition `f` on, the extensions of `φ` and `ψ`
compose to the identity of `D l ⊗[R] S`. -/
private theorem exists_liftEquivRight_comp_liftEquivRight_eq_id (hc : IsColimit c) {S : Type u}
    [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S]
    (e : c.pt ⊗[R] S ≃ₐ[c.pt] c.pt ⊗[R] T) {j : J}
    (φ : S →ₐ[R] D.obj j ⊗[R] T) (ψ : T →ₐ[R] D.obj j ⊗[R] S)
    (hφ : (map (c.ι.app j).hom (AlgHom.id R T)).comp φ =
      (e.toAlgHom.restrictScalars R).comp includeRight)
    (hψ : (map (c.ι.app j).hom (AlgHom.id R S)).comp ψ =
      (e.symm.toAlgHom.restrictScalars R).comp includeRight) :
    ∃ (k : J) (f : j ⟶ k), ∀ ⦃l : J⦄ (g : k ⟶ l),
      (liftEquivRight R _ _ _ ((map (D.map (f ≫ g)).hom (AlgHom.id R S)).comp ψ)).comp
          (liftEquivRight R _ _ _ ((map (D.map (f ≫ g)).hom (AlgHom.id R T)).comp φ)) =
        AlgHom.id _ _ := by
  have he : liftEquivRight R c.pt T _ ((e.symm.toAlgHom.restrictScalars R).comp includeRight) =
      e.symm.toAlgHom :=
    (liftEquivRight R c.pt T _).apply_symm_apply _
  -- The composite of `φ` with the extension of `ψ` is the inclusion of `S` in the colimit.
  obtain ⟨k, f, hk⟩ := hc.exists_algHom_comp_eq_comp
    (g₁ := ((liftEquivRight R _ _ _ ψ).restrictScalars R).comp φ) (g₂ := includeRight) (by
      rw [← AlgHom.comp_assoc, ← liftEquivRight_comp_map (B := c.pt), hψ, he, AlgHom.comp_assoc,
        hφ]
      ext s
      simp)
  refine ⟨k, f, fun l g ↦ liftEquivRight_comp_liftEquivRight_eq_id _ _ ?_⟩
  have hl := congr((map (D.map g).hom (AlgHom.id R S)).comp $hk)
  simp only [← AlgHom.comp_assoc] at hl
  rw [← Algebra.TensorProduct.map_comp, AlgHom.comp_id, ← CommAlgCat.hom_comp, ← D.map_comp] at hl
  rw [← AlgHom.comp_assoc, liftEquivRight_comp_map, AlgHom.comp_assoc]
  simpa only [AlgHom.comp_assoc, Algebra.TensorProduct.map_comp_includeRight, AlgHom.comp_id]
    using hl

/-- An `H`-algebra isomorphism `H ⊗[R] S ≃ H ⊗[R] T`, for `H` the colimit of a small filtered
diagram `D` of `R`-algebras and `S`, `T` finitely presented `R`-algebras, is the base change of a
`D j`-algebra isomorphism `D j ⊗[R] S ≃ D j ⊗[R] T` at some stage `j`: the two agree on `S`. -/
theorem _root_.CategoryTheory.Limits.IsColimit.exists_algEquiv_tensorProduct (hc : IsColimit c)
    {S : Type u} [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
    [Algebra.FinitePresentation R T]
    (e : c.pt ⊗[R] S ≃ₐ[c.pt] c.pt ⊗[R] T) :
    ∃ (j : J) (e' : D.obj j ⊗[R] S ≃ₐ[D.obj j] D.obj j ⊗[R] T), ∀ s : S,
      map (c.ι.app j).hom (AlgHom.id R T) (e' (1 ⊗ₜ s)) = e (1 ⊗ₜ s) := by
  -- Descend the restrictions of `e` and `e⁻¹` to a common stage `j`.
  obtain ⟨j₁, φ₁, hφ₁⟩ :=
    hc.exists_algHom_comp_eq ((e.toAlgHom.restrictScalars R).comp includeRight)
  obtain ⟨j₂, ψ₂, hψ₂⟩ :=
    hc.exists_algHom_comp_eq ((e.symm.toAlgHom.restrictScalars R).comp includeRight)
  let φ := (map (D.map (IsFiltered.leftToMax j₁ j₂)).hom (AlgHom.id R T)).comp φ₁
  let ψ := (map (D.map (IsFiltered.rightToMax j₁ j₂)).hom (AlgHom.id R S)).comp ψ₂
  have hφ := map_ι_comp_map_comp (IsFiltered.leftToMax j₁ j₂) hφ₁
  have hψ := map_ι_comp_map_comp (IsFiltered.rightToMax j₁ j₂) hψ₂
  -- Both composites become the identity at a common later stage `l`, reached by `f₁ ≫ g₁`.
  obtain ⟨k₁, f₁, h₁⟩ := exists_liftEquivRight_comp_liftEquivRight_eq_id hc e φ ψ hφ hψ
  obtain ⟨k₂, f₂, h₂⟩ :=
    exists_liftEquivRight_comp_liftEquivRight_eq_id hc e.symm ψ φ hψ (by simpa using hφ)
  obtain ⟨l, g₁, g₂, hg⟩ := IsFiltered.span f₁ f₂
  refine ⟨l, AlgEquiv.ofAlgHom
    (liftEquivRight R _ _ _ ((map (D.map (f₁ ≫ g₁)).hom (AlgHom.id R T)).comp φ))
    (liftEquivRight R _ _ _ ((map (D.map (f₁ ≫ g₁)).hom (AlgHom.id R S)).comp ψ))
    (hg ▸ h₂ g₂) (h₁ g₁), fun s ↦ ?_⟩
  have hs := congr($(map_ι_comp_map_comp (f₁ ≫ g₁) hφ) s)
  simpa [φ, ← Algebra.TensorProduct.one_def] using hs

end TauCeti.CommAlgCat
