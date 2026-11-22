/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Monoidal
import TauCeti.Data.Set.Prod

/-!
# Fibre inclusions, projections, and discrete-factor products in `TopCat`

For spaces `X` and `F` and a point `x : X`, `TopCat.prodFiberInclusion X F x : F ⟶ X ⊗ F` is the
inclusion `f ↦ (x, f)` of the fibre of the first projection over `x`, built from the cartesian
monoidal structure of `TopCat`. Its composites with the projections are the constant map at `x`
and the identity, so it is a split monomorphism, and it is natural in `X` and in `F`.

We also record `TopCat.ofHom_fst` and `TopCat.ofHom_snd`, identifying
`TopCat.ofHom ContinuousMap.fst` and `TopCat.ofHom ContinuousMap.snd` with the cartesian
projections `fst` and `snd`, and `TopCat.mapsTo_tensorHom_compl_singleton` showing that a product of
maps preserving singleton complements preserves the complement of the pair. When `X` has the
discrete topology, `TopCat.sigmaConstIsoProd X Y` identifies the disjoint union
`TopCat.of (Σ _ : X, Y)` with the product `X ⊗ Y`, matching each summand inclusion `TopCat.sigmaι`
with `TopCat.prodFiberInclusion`.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory

universe u

namespace TopCat

/-- `TopCat.ofHom ContinuousMap.fst` is the cartesian first projection `fst (of X) (of Y)`. -/
@[simp]
lemma ofHom_fst {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] :
    TopCat.ofHom (ContinuousMap.fst : C(X × Y, X)) = fst (of X) (of Y) :=
  TopCat.ext fun _ ↦ rfl

/-- `TopCat.ofHom ContinuousMap.snd` is the cartesian second projection `snd (of X) (of Y)`. -/
@[simp]
lemma ofHom_snd {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] :
    TopCat.ofHom (ContinuousMap.snd : C(X × Y, Y)) = snd (of X) (of Y) :=
  TopCat.ext fun _ ↦ rfl

/-- The product of two continuous maps carrying `{x₁}ᶜ` into `{y₁}ᶜ` and `{x₂}ᶜ` into `{y₂}ᶜ`
carries `{(x₁, x₂)}ᶜ` into `{(y₁, y₂)}ᶜ`. -/
lemma mapsTo_tensorHom_compl_singleton {V₁ V₂ W₁ W₂ : Type u} [TopologicalSpace V₁]
    [TopologicalSpace V₂] [TopologicalSpace W₁] [TopologicalSpace W₂] {x₁ : V₁} {x₂ : V₂}
    {y₁ : W₁} {y₂ : W₂} (g₁ : TopCat.of V₁ ⟶ TopCat.of W₁) (g₂ : TopCat.of V₂ ⟶ TopCat.of W₂)
    (hg₁ : Set.MapsTo g₁ ({x₁}ᶜ : Set V₁) ({y₁}ᶜ : Set W₁))
    (hg₂ : Set.MapsTo g₂ ({x₂}ᶜ : Set V₂) ({y₂}ᶜ : Set W₂)) :
    Set.MapsTo (g₁ ⊗ₘ g₂) ({(x₁, x₂)}ᶜ : Set (V₁ × V₂)) ({(y₁, y₂)}ᶜ : Set (W₁ × W₂)) := by
  rw [Set.compl_singleton_prod, Set.compl_singleton_prod]
  exact fun _ h ↦ h.imp (fun hx ↦ hg₁ hx) (fun hx ↦ hg₂ hx)

variable (X F : TopCat.{u})

/-- The inclusion `f ↦ (x, f)` of the fibre `F` over `x : X` into the product `X × F`. -/
def prodFiberInclusion (x : X) : F ⟶ X ⊗ F :=
  lift (TopCat.const x) (𝟙 F)

lemma prodFiberInclusion_def (x : X) : prodFiberInclusion X F x = lift (TopCat.const x) (𝟙 F) :=
  (rfl)

@[simp]
lemma prodFiberInclusion_apply (x : X) (f : F) :
    prodFiberInclusion X F x f = ((x, f) : ↑(X ⊗ F)) := by
  rw [prodFiberInclusion_def, TopCat.lift_apply, TopCat.const_apply, ConcreteCategory.id_apply]

@[reassoc (attr := simp)]
lemma prodFiberInclusion_fst (x : X) : prodFiberInclusion X F x ≫ fst X F = TopCat.const x :=
  lift_fst _ _

@[reassoc (attr := simp)]
lemma prodFiberInclusion_snd (x : X) : prodFiberInclusion X F x ≫ snd X F = 𝟙 F :=
  lift_snd _ _

/-- The fibre inclusion is a split monomorphism, with retraction the second projection. -/
instance isSplitMono_prodFiberInclusion (x : X) : IsSplitMono (prodFiberInclusion X F x) :=
  .mk' ⟨snd X F, prodFiberInclusion_snd X F x⟩

variable {X F}

/-- The fibre inclusion is natural in the base. -/
@[reassoc (attr := simp)]
lemma prodFiberInclusion_whiskerRight {Y : TopCat.{u}} (f : X ⟶ Y) (x : X) :
    prodFiberInclusion X F x ≫ f ▷ F = prodFiberInclusion Y F (f x) := by
  ext <;> simp

/-- The fibre inclusion is natural in the fibre. -/
@[reassoc (attr := simp)]
lemma prodFiberInclusion_whiskerLeft {G : TopCat.{u}} (g : F ⟶ G) (x : X) :
    prodFiberInclusion X F x ≫ X ◁ g = g ≫ prodFiberInclusion X G x := by
  ext <;> simp

/-- The fibre inclusion is natural in the base and the fibre jointly. -/
@[reassoc (attr := simp)]
lemma prodFiberInclusion_tensorHom {Y G : TopCat.{u}} (f : X ⟶ Y) (g : F ⟶ G) (x : X) :
    prodFiberInclusion X F x ≫ (f ⊗ₘ g) = g ≫ prodFiberInclusion Y G (f x) := by
  ext <;> simp

/-- For a discrete space `X` and any space `Y`, the isomorphism `(Σ _ : X, Y) ≅ X ⊗ Y` in `TopCat`
identifying the product with the disjoint union of copies of `Y` indexed by `X`. -/
def sigmaConstIsoProd (X Y : TopCat.{u}) [DiscreteTopology X] :
    TopCat.of (Σ _ : X, Y) ≅ X ⊗ Y where
  hom := ConcreteCategory.ofHom ⟨fun p ↦ (p.1, p.2),
    continuous_sigma_iff.2 fun _ ↦ by fun_prop⟩
  inv := ConcreteCategory.ofHom ⟨fun q ↦ ⟨q.1, q.2⟩,
    continuous_prod_of_discrete_left.2 fun a ↦
      continuous_sigmaMk (σ := fun _ : X ↦ (Y : Type u)) (i := a)⟩
  hom_inv_id := TopCat.ext fun ⟨_, _⟩ ↦ rfl
  inv_hom_id := TopCat.ext fun ⟨_, _⟩ ↦ rfl

/-- The forward map of `TopCat.sigmaConstIsoProd` pairs the index `p.1` with `p.2`. -/
@[simp]
theorem sigmaConstIsoProd_hom_apply (X Y : TopCat.{u}) [DiscreteTopology X] (p : Σ _ : X, Y) :
    (sigmaConstIsoProd X Y).hom p = (p.1, p.2) := (rfl)

/-- The inverse map of `TopCat.sigmaConstIsoProd` indexes `q.2` by `q.1`. -/
@[simp]
theorem sigmaConstIsoProd_inv_apply (X Y : TopCat.{u}) [DiscreteTopology X]
    (q : (X ⊗ Y : TopCat.{u})) :
    (sigmaConstIsoProd X Y).inv q = ⟨q.1, q.2⟩ := (rfl)

/-- Each summand inclusion composes with `(sigmaConstIsoProd X Y).hom` to
`TopCat.prodFiberInclusion`. -/
@[reassoc (attr := simp)]
theorem sigmaι_comp_sigmaConstIsoProd_hom (X Y : TopCat.{u}) [DiscreteTopology X] (x : X) :
    sigmaι (fun _ : X ↦ Y) x ≫ (sigmaConstIsoProd X Y).hom = prodFiberInclusion X Y x :=
  TopCat.ext fun y ↦ (prodFiberInclusion_apply X Y x y).symm

/-- Fibre inclusion at `x : X` composes with `(sigmaConstIsoProd X Y).inv` to the summand
inclusion `TopCat.sigmaι`. -/
@[reassoc (attr := simp)]
theorem prodFiberInclusion_comp_sigmaConstIsoProd_inv (X Y : TopCat.{u}) [DiscreteTopology X]
    (x : X) :
    prodFiberInclusion X Y x ≫ (sigmaConstIsoProd X Y).inv = sigmaι (fun _ : X ↦ Y) x :=
  TopCat.ext fun y ↦ (TopCat.comp_app _ _ y).trans
    (congrArg (sigmaConstIsoProd X Y).inv (prodFiberInclusion_apply X Y x y))

end TopCat
