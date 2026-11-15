/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Hom
public import TauCeti.CategoryTheory.CStar.Basic
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Basic

/-!
# Automatic contractivity and isometry of linear dagger functors

Every additive `ℂ`-linear dagger-preserving functor `F : C ⥤ D` between C\*-categories is
automatically norm-contractive on all Hom spaces (`CategoryTheory.Functor.norm_map_le`), hence
continuous (`CategoryTheory.Functor.mapCLM`), with closed kernel ideal components
(`CategoryTheory.Functor.isClosed_kerIdeal_hom`). When `F` is also faithful, `F.map` is
automatically isometric on all Hom spaces (`CategoryTheory.Functor.norm_map`,
`CategoryTheory.Functor.mapLinearIsometry`) and order-embedding on endomorphism C\*-algebras.

Applying automatic isometry to the identity functor `(𝟭 C)` shows that a complex linear dagger
category `(C, †)` admits at most one `CStarCategory` norm and metric structure
(`TauCeti.CStarCategory.norm_eq`, `TauCeti.CStarCategory.ext`).

The proofs avoid constructing 2×2 linking algebras: for an arbitrary arrow `f : X ⟶ Y`, the
composite `f ≫ dagger f` lies in `End X`, where `F.mapEndStarAlgHom ℂ X` is a unital
star-algebra homomorphism between C\*-algebras (`NonUnitalStarAlgHom.norm_apply_le`, and
`NonUnitalStarAlgHom.norm_map` when `F` is faithful); the C\*-identity `‖f ≫ dagger f‖ = ‖f‖ ^ 2`
then transfers the norm bound or norm equality from `End X` to `X ⟶ Y`.

## References

* P. Ghez, R. Lima, J. E. Roberts, *W\*-categories*, Pacific J. Math. **120** (1985),
  Proposition 1.13.
* P. D. Mitchener, *C\*-categories*, Proc. London Math. Soc. (3) **84** (2002),
  Proposition 2.10 and Corollary 2.12.
-/

public section

noncomputable section

open CategoryTheory TauCeti

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [DaggerCategory C] [Preadditive C]
  [CategoryTheory.Linear ℂ C]
variable {D : Type u₂} [Category.{v₂} D] [DaggerCategory D] [Preadditive D]
  [CategoryTheory.Linear ℂ D]
variable [instC : CStarCategory C] [instD : CStarCategory D]
variable (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.PreservesDagger]

/-! ### Automatic contractivity and continuity -/

/-- Every additive `ℂ`-linear dagger-preserving functor between C\*-categories is norm-contractive
on all Hom spaces. -/
theorem norm_map_le {X Y : C} (f : X ⟶ Y) : ‖F.map f‖ ≤ ‖f‖ := by
  have hsq : ‖F.map f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    calc
      ‖F.map f‖ ^ 2 = ‖F.map f ≫ dagger (F.map f)‖ := (norm_comp_dagger_self (F.map f)).symm
      _ = ‖F.map (f ≫ dagger f)‖ := by rw [← F.map_dagger, ← F.map_comp]
      _ = ‖End.of (F.map (f ≫ dagger f))‖ := (End.norm_of _).symm
      _ = ‖F.mapEndStarAlgHom ℂ X (End.of (f ≫ dagger f))‖ := by rw [F.mapEndStarAlgHom_of ℂ]
      _ ≤ ‖End.of (f ≫ dagger f)‖ :=
        NonUnitalStarAlgHom.norm_apply_le (F.mapEndStarAlgHom ℂ X) (End.of (f ≫ dagger f))
      _ = ‖f‖ ^ 2 := by rw [End.norm_of, norm_comp_dagger_self]
  exact nonneg_le_nonneg_of_sq_le_sq (norm_nonneg f) (by simpa only [sq] using hsq)

/-- `ℝ≥0`-norm contractivity of an additive `ℂ`-linear dagger-preserving functor. -/
theorem nnNorm_map_le {X Y : C} (f : X ⟶ Y) : ‖F.map f‖₊ ≤ ‖f‖₊ :=
  F.norm_map_le f

/-- `F.map` bundled as a continuous `ℂ`-linear map on Hom spaces, of operator norm at most `1`. -/
def mapCLM (X Y : C) : (X ⟶ Y) →L[ℂ] (F.obj X ⟶ F.obj Y) :=
  LinearMap.mkContinuous (F.mapLinearMap ℂ) 1 fun f => by
    simpa [one_mul] using F.norm_map_le f

/-- Evaluation of `Functor.mapCLM`. -/
@[simp] theorem mapCLM_apply (X Y : C) (f : X ⟶ Y) :
    F.mapCLM X Y f = F.map f := (rfl)

/-- Forgetting continuity from `Functor.mapCLM` recovers `Functor.mapLinearMap`. -/
@[simp] theorem mapCLM_toLinearMap (X Y : C) :
    (F.mapCLM X Y).toLinearMap = F.mapLinearMap ℂ := (rfl)

/-- `Functor.mapCLM` has operator norm at most `1`. -/
theorem norm_mapCLM_le_one (X Y : C) : ‖F.mapCLM X Y‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- `F.map` is `1`-Lipschitz on every Hom space. -/
theorem lipschitzWith_map (X Y : C) :
    LipschitzWith 1 (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  AddMonoidHomClass.lipschitz_of_bound_nnNorm F.mapAddHom 1 fun f => by
    simpa only [mapAddHom_apply, one_mul] using F.nnNorm_map_le f

/-- `F.map` is automatically continuous on every Hom space. -/
@[continuity, fun_prop] theorem continuous_map (X Y : C) :
    Continuous (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  (F.mapCLM X Y).continuous

/-- Each Hom subgroup `(F.kerIdeal).hom X Y` of morphisms killed by `F` is closed in `X ⟶ Y`. -/
theorem isClosed_kerIdeal_hom (X Y : C) :
    IsClosed ((F.kerIdeal.hom X Y : Set (X ⟶ Y))) := by
  have hker : (F.kerIdeal.hom X Y : Set (X ⟶ Y)) = ((F.mapCLM X Y).ker : Set (X ⟶ Y)) := by
    ext f
    simp [LinearMap.mem_ker]
  rw [hker]
  exact (F.mapCLM X Y).isClosed_ker

/-- An additive `ℂ`-linear dagger-preserving functor is monotone on endomorphism C\*-algebras. -/
theorem mapEnd_mono (X : C) : Monotone (F.mapEndStarAlgHom ℂ X) :=
  OrderHomClass.mono (F.mapEndStarAlgHom ℂ X)

/-! ### Automatic isometry of faithful linear dagger functors -/

section Faithful

variable [F.Faithful]

/-- Every faithful additive `ℂ`-linear dagger-preserving functor between C\*-categories is
isometric on all Hom spaces. -/
@[simp] theorem norm_map {X Y : C} (f : X ⟶ Y) : ‖F.map f‖ = ‖f‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), ← norm_comp_dagger_self,
    ← norm_comp_dagger_self f, ← F.map_dagger, ← F.map_comp,
    ← End.norm_of (F.map (f ≫ dagger f)), ← F.mapEndStarAlgHom_of ℂ,
    NonUnitalStarAlgHom.norm_map (F.mapEndStarAlgHom ℂ X) (F.mapEndStarAlgHom_injective ℂ X),
    End.norm_of]

/-- `ℝ≥0`-norm preservation for a faithful additive `ℂ`-linear dagger-preserving functor. -/
@[simp] theorem nnNorm_map {X Y : C} (f : X ⟶ Y) : ‖F.map f‖₊ = ‖f‖₊ :=
  Subtype.ext (F.norm_map f)

/-- `F.map` is an isometry on every Hom space when `F` is faithful. -/
theorem isometry_map (X Y : C) :
    Isometry (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  AddMonoidHomClass.isometry_of_norm F.mapAddHom F.norm_map

/-- `F.map` bundled as a `ℂ`-linear isometry on Hom spaces when `F` is faithful. -/
def mapLinearIsometry (X Y : C) : (X ⟶ Y) →ₗᵢ[ℂ] (F.obj X ⟶ F.obj Y) where
  toLinearMap := F.mapLinearMap ℂ
  norm_map' := F.norm_map

/-- Evaluation of `Functor.mapLinearIsometry`. -/
@[simp] theorem mapLinearIsometry_apply (X Y : C) (f : X ⟶ Y) :
    F.mapLinearIsometry X Y f = F.map f := (rfl)

/-- Converting `Functor.mapLinearIsometry` to a continuous linear map recovers `Functor.mapCLM`. -/
@[simp] theorem mapLinearIsometry_toContinuousLinearMap (X Y : C) :
    (F.mapLinearIsometry X Y).toContinuousLinearMap = F.mapCLM X Y := by
  ext; rfl

/-- A faithful additive `ℂ`-linear dagger-preserving functor reflects the spectral order on
endomorphism C\*-algebras. -/
@[simp] theorem mapEndStarAlgHom_le_iff (X : C) {a b : End X} :
    F.mapEndStarAlgHom ℂ X a ≤ F.mapEndStarAlgHom ℂ X b ↔ a ≤ b :=
  NonUnitalStarAlgHom.map_le_map_iff (F.mapEndStarAlgHom ℂ X) (F.mapEndStarAlgHom_injective ℂ X)

/-- A full and faithful additive `ℂ`-linear dagger-preserving functor induces a `ℂ`-linear
isometric equivalence on every Hom space. -/
def mapLinearIsometryEquiv [F.Full] (X Y : C) :
    (X ⟶ Y) ≃ₗᵢ[ℂ] (F.obj X ⟶ F.obj Y) :=
  LinearIsometryEquiv.ofSurjective (F.mapLinearIsometry X Y) F.map_surjective

/-- Evaluation of `Functor.mapLinearIsometryEquiv`. -/
@[simp] theorem mapLinearIsometryEquiv_apply [F.Full] (X Y : C) (f : X ⟶ Y) :
    F.mapLinearIsometryEquiv X Y f = F.map f := (rfl)

/-- Applying `(Functor.mapLinearIsometryEquiv).symm` computes `F.preimage`. -/
@[simp] theorem mapLinearIsometryEquiv_symm_apply [F.Full] (X Y : C)
    (g : F.obj X ⟶ F.obj Y) :
    (F.mapLinearIsometryEquiv X Y).symm g = F.preimage g := by
  apply F.map_injective
  simpa only [F.map_preimage, mapLinearIsometryEquiv_apply] using
    (F.mapLinearIsometryEquiv X Y).apply_symm_apply g

end Faithful

end CategoryTheory.Functor

namespace CategoryTheory.NatTrans

variable {C : Type u₁} [Category.{v₁} C] [DaggerCategory C]
variable {D : Type u₂} [Category.{v₂} D] [DaggerCategory D] [Preadditive D] [Linear ℂ D]
variable [CStarCategory D]
variable {F G : C ⥤ D} [F.PreservesDagger] [G.PreservesDagger]

/-- Componentwise norm equality for the pointwise dagger of a natural transformation. -/
theorem norm_dagger_app (α : F ⟶ G) (X : C) :
    ‖α.dagger.app X‖ = ‖α.app X‖ := by
  simp

end CategoryTheory.NatTrans

namespace TauCeti.CStarCategory

variable {C : Type u₁} [Category.{v₁} C] [DaggerCategory C] [Preadditive C] [Linear ℂ C]

/-- **Uniqueness of the C\*-category norm:** any two `CStarCategory` structures on the same complex
linear dagger category `(C, †)` assign the exact same norm to every morphism. -/
theorem norm_eq (inst₁ inst₂ : CStarCategory C) {X Y : C} (f : X ⟶ Y) :
    @Norm.norm _ (inst₁.homNorm X Y) f = @Norm.norm _ (inst₂.homNorm X Y) f :=
  Functor.norm_map (instC := inst₂) (instD := inst₁) (𝟭 C) f

/-- Any two `CStarCategory` structures on `(C, †)` have identical `homNorm` fields. -/
theorem homNorm_eq (inst₁ inst₂ : CStarCategory C) :
    inst₁.homNorm = inst₂.homNorm := by
  funext X Y
  have hnorm_ext : ∀ (a b : Norm (X ⟶ Y)), a.norm = b.norm → a = b := by
    rintro ⟨_⟩ ⟨_⟩ rfl; rfl
  exact hnorm_ext _ _ (funext fun f => norm_eq inst₁ inst₂ f)

/-- **Extensionality of `CStarCategory`:** a `ℂ`-linear dagger category admits at most one
`CStarCategory` structure, since the norm determines the metric and all remaining fields are
propositions. -/
@[ext] theorem ext (inst₁ inst₂ : CStarCategory C) : inst₁ = inst₂ := by
  cases inst₁ with
  | mk n₁ m₁ d₁ _ _ _ _ _ =>
  cases inst₂ with
  | mk n₂ m₂ d₂ _ _ _ _ _ =>
  have hn : n₁ = n₂ := homNorm_eq ⟨n₁, m₁, d₁, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›⟩
    ⟨n₂, m₂, d₂, ‹_›, ‹_›, ‹_›, ‹_›, ‹_›⟩
  subst hn
  have hm : m₁ = m₂ := by
    funext X Y
    apply MetricSpace.ext
    have hdist_ext : ∀ (a b : Dist (X ⟶ Y)), a.dist = b.dist → a = b := by
      rintro ⟨_⟩ ⟨_⟩ rfl; rfl
    exact hdist_ext _ _ (funext fun f => funext fun g => (d₁ f g).trans (d₂ f g).symm)
  subst hm
  rfl

instance instSubsingleton : Subsingleton (CStarCategory C) :=
  ⟨ext⟩

end TauCeti.CStarCategory
