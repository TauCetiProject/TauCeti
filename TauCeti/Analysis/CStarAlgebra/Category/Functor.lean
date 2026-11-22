/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import TauCeti.Analysis.CStarAlgebra.Category.Basic
public import TauCeti.CategoryTheory.Dagger.Functor
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import TauCeti.CategoryTheory.Linear.FullyFaithful

/-!
# Automatic contractivity and isometricity of linear dagger functors

A complex linear dagger-preserving functor `F` between C*-categories restricts, on each object
`X`, to a unital star algebra homomorphism `F.mapEndStarAlgHom ℂ X : End X →⋆ₐ[ℂ] End (F.obj X)`
of C*-algebras. Such homomorphisms are contractive, monotone in the spectral order, and isometric
(and order-reflecting) when injective. The C*-identity `‖f‖² = ‖f†f‖` transfers these facts to
arrows between different objects:

* Every complex linear dagger functor is contractive on Hom spaces (`Functor.norm_map_le`),
  bundling to a `1`-Lipschitz continuous linear map `Functor.mapCLM` with norm-closed kernel
  morphism ideal `Functor.isClosed_kerIdeal`.
* A faithful complex linear dagger functor is isometric on Hom spaces (`Functor.norm_map`),
  bundling to `Functor.mapLinearIsometry` (and `Functor.mapLinearIsometryEquiv` when full), and
  preserves and reflects the spectral order on `End X`. Conversely, norm preservation on all
  arrows characterizes faithfulness (`Functor.faithful_iff_forall_norm_map_eq`).
* Conjugation by a unitary object isomorphism `CategoryTheory.Iso.endStarAlgEquiv` is isometric
  and an order isomorphism on endomorphism C*-algebras.

As in `TauCeti.Analysis.CStarAlgebra.Category.HomSpace`, topological and continuous-linear-map
statements use the canonical norm-induced structures `CStarCategory.normedAddCommGroup` and
`CStarCategory.normedSpace`, activated locally so no global instances leak to downstream modules.

## References

* P. Ghez, R. Lima, J. E. Roberts, *W\*-categories*, Pacific J. Math. 120 (1985), 79–109.
* P. D. Mitchener, *C\*-categories*, Proc. London Math. Soc. (3) 84 (2002), 375–404.
-/

public section

noncomputable section

open CategoryTheory TauCeti

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

attribute [local instance] CStarCategory.normedAddCommGroup CStarCategory.normedSpace

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [CategoryTheory.Linear ℂ C]
  [DaggerCategory C] [DaggerPreadditive C] [DaggerLinear ℂ C]
  [∀ X Y : C, Norm (X ⟶ Y)] [CStarCategory C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [CategoryTheory.Linear ℂ D]
  [DaggerCategory D] [DaggerPreadditive D] [DaggerLinear ℂ D]
  [∀ X Y : D, Norm (X ⟶ Y)] [CStarCategory D]
variable (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.PreservesDagger]

/-! ### Automatic contractivity, Hom-space CLM, and closed kernel ideal -/

omit [DaggerPreadditive C] [DaggerLinear ℂ C] [∀ X Y : C, Norm (X ⟶ Y)] [CStarCategory C] in
/-- The square of the norm of `F.map f` is the norm of `F.map (f ≫ dagger f)`. -/
private theorem sq_norm_map {X Y : C} (f : X ⟶ Y) :
    ‖F.map f‖ ^ 2 = ‖F.mapEndStarAlgHom ℂ X (.of (f ≫ dagger f))‖ := by
  rw [End.norm_def, mapEndStarAlgHom_asHom, F.map_comp, F.map_dagger,
    CStarCategory.norm_self_comp_dagger]

/-- A complex linear dagger functor between C*-categories is contractive on Hom spaces. -/
theorem norm_map_le {X Y : C} (f : X ⟶ Y) : ‖F.map f‖ ≤ ‖f‖ := by
  refine (pow_le_pow_iff_left₀ (CStarCategory.norm_nonneg _) (CStarCategory.norm_nonneg f)
    two_ne_zero).1 ?_
  rw [sq_norm_map, ← CStarCategory.norm_self_comp_dagger, ← End.norm_of]
  exact NonUnitalStarAlgHom.norm_apply_le _ _

/-- Nonnegative-norm version of `CategoryTheory.Functor.norm_map_le`. -/
theorem nnNorm_map_le {X Y : C} (f : X ⟶ Y) : ‖F.map f‖₊ ≤ ‖f‖₊ :=
  F.norm_map_le f

/-- The action of a `ℂ`-linear dagger functor on Hom spaces bundled as a continuous linear map. -/
def mapCLM (X Y : C) : (X ⟶ Y) →L[ℂ] (F.obj X ⟶ F.obj Y) :=
  (F.mapLinearMap ℂ).mkContinuous 1 fun f => by
    simpa using F.norm_map_le f

/-- Evaluation of `F.mapCLM` applies `F.map`. -/
@[simp] theorem mapCLM_apply (X Y : C) (f : X ⟶ Y) :
    F.mapCLM X Y f = F.map f := (rfl)

/-- Forgetting continuity from `F.mapCLM` recovers `F.mapLinearMap ℂ`. -/
@[simp] theorem mapCLM_toLinearMap (X Y : C) :
    (F.mapCLM X Y).toLinearMap = F.mapLinearMap ℂ := (rfl)

/-- The operator norm of `F.mapCLM X Y` is at most `1`. -/
theorem norm_mapCLM_le (X Y : C) : ‖F.mapCLM X Y‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- `F.map` is `1`-Lipschitz on every Hom space (with its norm-induced metric). -/
theorem lipschitzWith_map (X Y : C) :
    LipschitzWith 1 (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  AddMonoidHomClass.lipschitz_of_bound_nnNorm (F.mapLinearMap ℂ) 1 fun f => by
    simpa using F.nnNorm_map_le f

/-- `F.map` is continuous on every Hom space (with its norm-induced topology). -/
@[fun_prop] theorem continuous_map (X Y : C) :
    Continuous (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  (F.mapCLM X Y).continuous

/-- Each Hom-space component of the kernel morphism ideal `F.kerIdeal` of a `ℂ`-linear dagger
functor between C*-categories is norm-closed. -/
theorem isClosed_kerIdeal (X Y : C) :
    IsClosed (F.kerIdeal.hom X Y : Set (X ⟶ Y)) := by
  have hset : (F.kerIdeal.hom X Y : Set (X ⟶ Y)) = ((F.mapCLM X Y).ker : Set (X ⟶ Y)) := by
    ext f
    simp
  rw [hset]
  exact (F.mapCLM X Y).isClosed_ker

/-! ### Faithful and fully faithful linear dagger functors -/

/-- A faithful complex linear dagger functor between C*-categories is isometric on Hom
spaces. -/
@[simp] theorem norm_map [F.Faithful] {X Y : C} (f : X ⟶ Y) : ‖F.map f‖ = ‖f‖ := by
  refine (pow_left_inj₀ (CStarCategory.norm_nonneg _) (CStarCategory.norm_nonneg f)
    two_ne_zero).1 ?_
  have hinj := F.mapEndAlgHom_injective ℂ X
  rw [← toAlgHom_mapEndStarAlgHom, StarAlgHom.coe_toAlgHom] at hinj
  rw [sq_norm_map, ← CStarCategory.norm_self_comp_dagger, ← End.norm_of]
  exact NonUnitalStarAlgHom.norm_map _ hinj _

/-- Nonnegative-norm version of `CategoryTheory.Functor.norm_map`. -/
@[simp] theorem nnNorm_map [F.Faithful] {X Y : C} (f : X ⟶ Y) : ‖F.map f‖₊ = ‖f‖₊ :=
  Subtype.ext (F.norm_map f)

/-- A faithful `ℂ`-linear dagger functor induces an isometry on every Hom space. -/
theorem isometry_map [F.Faithful] (X Y : C) :
    Isometry (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) :=
  AddMonoidHomClass.isometry_of_norm (F.mapLinearMap ℂ) F.norm_map

/-- The Hom-space action of a faithful `ℂ`-linear dagger functor bundled as a `ℂ`-linear
isometry. -/
def mapLinearIsometry [F.Faithful] (X Y : C) :
    (X ⟶ Y) →ₗᵢ[ℂ] (F.obj X ⟶ F.obj Y) where
  toLinearMap := F.mapLinearMap ℂ
  norm_map' := F.norm_map

/-- Evaluation of `F.mapLinearIsometry` applies `F.map`. -/
@[simp] theorem mapLinearIsometry_apply [F.Faithful] (X Y : C) (f : X ⟶ Y) :
    F.mapLinearIsometry X Y f = F.map f := (rfl)

/-- A `ℂ`-linear dagger functor between C*-categories is faithful if and only if it preserves the
norm of every morphism. -/
theorem faithful_iff_forall_norm_map_eq :
    F.Faithful ↔ ∀ ⦃X Y : C⦄ (f : X ⟶ Y), ‖F.map f‖ = ‖f‖ := by
  refine ⟨fun _ _ _ f => F.norm_map f, fun h => ⟨fun {X Y} f g hfg => ?_⟩⟩
  refine sub_eq_zero.mp (CStarCategory.norm_eq_zero.mp ?_)
  rw [← h (f - g), F.map_sub, hfg, sub_self, CStarCategory.norm_zero]

/-- A faithful `ℂ`-linear dagger functor reflects and preserves the spectral order on `End X`. -/
@[simp] theorem mapEndStarAlgHom_le_iff [F.Faithful] (X : C) {a b : End X} :
    F.mapEndStarAlgHom ℂ X a ≤ F.mapEndStarAlgHom ℂ X b ↔ a ≤ b := by
  have hinj := F.mapEndAlgHom_injective ℂ X
  rw [← toAlgHom_mapEndStarAlgHom, StarAlgHom.coe_toAlgHom] at hinj
  exact NonUnitalStarAlgHom.map_le_map_iff (F.mapEndStarAlgHom ℂ X) hinj

/-- A faithful `ℂ`-linear dagger functor reflects and preserves positivity in `End X`. -/
@[simp] theorem mapEndStarAlgHom_nonneg_iff [F.Faithful] (X : C) {a : End X} :
    0 ≤ F.mapEndStarAlgHom ℂ X a ↔ 0 ≤ a := by
  simpa only [map_zero] using F.mapEndStarAlgHom_le_iff X (a := 0) (b := a)

/-- The Hom-space action of a fully faithful `ℂ`-linear dagger functor bundled as a `ℂ`-linear
isometric equivalence. -/
def mapLinearIsometryEquiv [F.Full] [F.Faithful] (X Y : C) :
    (X ⟶ Y) ≃ₗᵢ[ℂ] (F.obj X ⟶ F.obj Y) where
  __ := F.homLinearEquiv ℂ X Y
  norm_map' f := by simp

/-- Forward evaluation of `F.mapLinearIsometryEquiv` applies `F.map`. -/
@[simp] theorem mapLinearIsometryEquiv_apply [F.Full] [F.Faithful] (X Y : C) (f : X ⟶ Y) :
    F.mapLinearIsometryEquiv X Y f = F.map f := by
  simp [mapLinearIsometryEquiv]

/-- Inverse evaluation of `F.mapLinearIsometryEquiv` applies `F.preimage`. -/
@[simp] theorem mapLinearIsometryEquiv_symm_apply [F.Full] [F.Faithful] (X Y : C)
    (g : F.obj X ⟶ F.obj Y) :
    (F.mapLinearIsometryEquiv X Y).symm g = F.preimage g := by
  apply (F.mapLinearIsometryEquiv X Y).injective
  simp

/-- Taking `F.preimage` along a fully faithful `ℂ`-linear dagger functor preserves norms. -/
@[simp] theorem norm_preimage [F.Full] [F.Faithful] {X Y : C} (g : F.obj X ⟶ F.obj Y) :
    ‖F.preimage g‖ = ‖g‖ := by
  rw [← F.norm_map (F.preimage g), F.map_preimage]

end CategoryTheory.Functor
