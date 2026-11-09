/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.Basic

/-!
# Levelwise pullbacks of adic thickening systems

Let `f : 𝔛 ⟶ 𝔖` and `g : 𝔜 ⟶ 𝔖` be morphisms of adic thickening systems such that `g` is adic
(`IsAdicHom g`). Because each transition square of `g` is cartesian, the levelwise fibre products
`Limits.pullback (f.app n) (g.app n)` with transitions `Limits.pullback.map` satisfy:

* the first-projection squares to `𝔛` are cartesian, so the levelwise transitions are thickenings
  and the first projection is an adic morphism;
* the ideal sheaves of the transitions and level maps are the inverse images along the first
  projections of those on `𝔛`, so the adic power equation is inherited from `𝔛` via
  `Scheme.IdealSheafData.comap_pow`.

Notice that `f` itself need not be adic: for instance, pulling back the canonical morphism
`Spf A ⟶ ofScheme.obj (Spec A)` along the adic morphism `ofScheme.map (X ⟶ Spec A)` forms the
tower of reductions `(X ×_{Spec A} Spec (A ⧸ I ^ (n + 1)))_n` as an adic thickening system. When
`f` is also adic, the second projection is adic as well (`isAdicHom_pullback_snd`). Moreover,
`pullback f g` is a categorical pullback of `f` and `g` in `AdicThickeningSystem`
(`isPullback_pullback`).

## Main definitions

* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.pullback`: the levelwise fibre product of
  `f : 𝔛 ⟶ 𝔖` and an adic morphism `g : 𝔜 ⟶ 𝔖`.
* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.pullback.fst`,
  `TauCeti.AlgebraicGeometry.AdicThickeningSystem.pullback.snd`,
  `TauCeti.AlgebraicGeometry.AdicThickeningSystem.pullback.lift`: projections and universal lift.

## Main results

* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.pullback_X`: `(pullback f g).X n` is
  `Limits.pullback (f.app n) (g.app n)`.
* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.isAdicHom_pullback_fst`,
  `TauCeti.AlgebraicGeometry.AdicThickeningSystem.isAdicHom_pullback_snd`: stability of adic
  morphisms under levelwise base change.
* `TauCeti.AlgebraicGeometry.AdicThickeningSystem.isPullback_pullback`: `pullback f g` is a
  pullback square in the category `AdicThickeningSystem`.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.AdicThickeningSystem

variable {𝔛 𝔜 𝔖 : AdicThickeningSystem.{u}}

/-- When `g` is adic, the first-projection square from the levelwise fibre product to `𝔛` is
cartesian at every level `n`: pasting with the right-hand pullback square for `P (n + 1)` matches
the horizontal paste of the pullback square for `P n` with the adic square of `g`. -/
private lemma isPullback_pullbackMap_fst (f : 𝔛 ⟶ 𝔖) (g : 𝔜 ⟶ 𝔖) [IsAdicHom g] (n : ℕ) :
    IsPullback
      (Limits.pullback.map (f.app n) (g.app n) (f.app (n + 1)) (g.app (n + 1))
        (𝔛.ι n) (𝔜.ι n) (𝔖.ι n) (f.naturality n).symm (g.naturality n).symm)
      (Limits.pullback.fst (f.app n) (g.app n))
      (Limits.pullback.fst (f.app (n + 1)) (g.app (n + 1))) (𝔛.ι n) := by
  have hout : IsPullback
      (Limits.pullback.map (f.app n) (g.app n) (f.app (n + 1)) (g.app (n + 1))
          (𝔛.ι n) (𝔜.ι n) (𝔖.ι n) (f.naturality n).symm (g.naturality n).symm ≫
        Limits.pullback.snd (f.app (n + 1)) (g.app (n + 1)))
      (Limits.pullback.fst (f.app n) (g.app n))
      (g.app (n + 1)) (𝔛.ι n ≫ f.app (n + 1)) := by
    rw [Limits.pullback.lift_snd, f.naturality]
    exact (IsPullback.of_hasPullback (f.app n) (g.app n)).flip.paste_horiz
      (IsAdicHom.isPullback (f := g) n)
  exact hout.of_right (by simp)
    (IsPullback.of_hasPullback (f.app (n + 1)) (g.app (n + 1))).flip

/-- Symmetrically, when `f` is adic, the second-projection square from the levelwise fibre product
to `𝔜` is cartesian at every level `n`. -/
private lemma isPullback_pullbackMap_snd (f : 𝔛 ⟶ 𝔖) (g : 𝔜 ⟶ 𝔖) [IsAdicHom f] (n : ℕ) :
    IsPullback
      (Limits.pullback.map (f.app n) (g.app n) (f.app (n + 1)) (g.app (n + 1))
        (𝔛.ι n) (𝔜.ι n) (𝔖.ι n) (f.naturality n).symm (g.naturality n).symm)
      (Limits.pullback.snd (f.app n) (g.app n))
      (Limits.pullback.snd (f.app (n + 1)) (g.app (n + 1))) (𝔜.ι n) := by
  have hout : IsPullback
      (Limits.pullback.map (f.app n) (g.app n) (f.app (n + 1)) (g.app (n + 1))
          (𝔛.ι n) (𝔜.ι n) (𝔖.ι n) (f.naturality n).symm (g.naturality n).symm ≫
        Limits.pullback.fst (f.app (n + 1)) (g.app (n + 1)))
      (Limits.pullback.snd (f.app n) (g.app n))
      (f.app (n + 1)) (𝔜.ι n ≫ g.app (n + 1)) := by
    rw [Limits.pullback.lift_fst, g.naturality]
    exact (IsPullback.of_hasPullback (f.app n) (g.app n)).paste_horiz
      (IsAdicHom.isPullback (f := f) n)
  exact hout.of_right (by simp)
    (IsPullback.of_hasPullback (f.app (n + 1)) (g.app (n + 1)))

/-- Pasting `isPullback_pullbackMap_fst` across the first `m` transitions shows that the level map
of the levelwise fibre product is the base change of `𝔛.levelMap m`. -/
private lemma isPullback_levelMap_pullback_fst (f : 𝔛 ⟶ 𝔖) (g : 𝔜 ⟶ 𝔖) [IsAdicHom g] (m : ℕ) :
    IsPullback
      (TauCeti.AlgebraicGeometry.levelMap
        (fun n ↦ Limits.pullback (f.app n) (g.app n))
        (fun n ↦ Limits.pullback.map (f.app n) (g.app n) (f.app (n + 1)) (g.app (n + 1))
          (𝔛.ι n) (𝔜.ι n) (𝔖.ι n) (f.naturality n).symm (g.naturality n).symm) m)
      (Limits.pullback.fst (f.app 0) (g.app 0))
      (Limits.pullback.fst (f.app m) (g.app m)) (𝔛.levelMap m) := by
  induction m with
  | zero =>
    rw [TauCeti.AlgebraicGeometry.levelMap_zero, 𝔛.levelMap_zero]
    exact IsPullback.of_horiz_isIso
      (fst := 𝟙 (Limits.pullback (f.app 0) (g.app 0))) (g := 𝟙 (𝔛.X 0)) ⟨by simp⟩
  | succ m ih =>
    rw [TauCeti.AlgebraicGeometry.levelMap_succ, 𝔛.levelMap_succ]
    exact ih.paste_horiz (isPullback_pullbackMap_fst f g m)

/-- The levelwise fibre product of `f : 𝔛 ⟶ 𝔖` along an adic morphism `g : 𝔜 ⟶ 𝔖`. -/
-- `@[expose]` is forced by dependent typing of component morphisms: without `(pullback f g).X n`
-- reducing definitionally to `Limits.pullback (f.app n) (g.app n)`, `pullback_ι`, `fst_app`,
-- `snd_app`, and `lift_app` do not typecheck.
@[expose, simps X ι]
noncomputable def pullback (f : 𝔛 ⟶ 𝔖) (g : 𝔜 ⟶ 𝔖) [IsAdicHom g] :
    AdicThickeningSystem.{u} where
  X n := Limits.pullback (f.app n) (g.app n)
  ι n := Limits.pullback.map (f.app n) (g.app n) (f.app (n + 1)) (g.app (n + 1))
    (𝔛.ι n) (𝔜.ι n) (𝔖.ι n) (f.naturality n).symm (g.naturality n).symm
  isThickening n := by
    rw [← (isPullback_pullbackMap_fst f g n).isoPullback_hom_fst]
    infer_instance
  adic n := by
    have hι := Scheme.IdealSheafData.ker_eq_comap_of_isPullback (𝔛.ι n)
      (isPullback_pullbackMap_fst f g n)
    have hlev := Scheme.IdealSheafData.ker_eq_comap_of_isPullback (𝔛.levelMap (n + 1))
      (isPullback_levelMap_pullback_fst f g (n + 1))
    rw [hι, hlev, 𝔛.ker_ι n, Scheme.IdealSheafData.comap_pow]

theorem pullback_reduction (f : 𝔛 ⟶ 𝔖) (g : 𝔜 ⟶ 𝔖) [IsAdicHom g] (n : ℕ) :
    (pullback f g).reduction n = Limits.pullback (f.app n) (g.app n) := by
  rw [reduction_eq, pullback_X]

namespace pullback

/-- The first projection `pullback f g ⟶ 𝔛` of the levelwise fibre product. -/
noncomputable def fst (f : 𝔛 ⟶ 𝔖) (g : 𝔜 ⟶ 𝔖) [IsAdicHom g] : pullback f g ⟶ 𝔛 where
  app n := Limits.pullback.fst (f.app n) (g.app n)
  naturality _ := by simp [AdicThickeningSystem.pullback]

@[simp]
theorem fst_app (f : 𝔛 ⟶ 𝔖) (g : 𝔜 ⟶ 𝔖) [IsAdicHom g] (n : ℕ) :
    (fst f g).app n = Limits.pullback.fst (f.app n) (g.app n) :=
  (rfl)

/-- The second projection `pullback f g ⟶ 𝔜` of the levelwise fibre product. -/
noncomputable def snd (f : 𝔛 ⟶ 𝔖) (g : 𝔜 ⟶ 𝔖) [IsAdicHom g] : pullback f g ⟶ 𝔜 where
  app n := Limits.pullback.snd (f.app n) (g.app n)
  naturality _ := by simp [AdicThickeningSystem.pullback]

@[simp]
theorem snd_app (f : 𝔛 ⟶ 𝔖) (g : 𝔜 ⟶ 𝔖) [IsAdicHom g] (n : ℕ) :
    (snd f g).app n = Limits.pullback.snd (f.app n) (g.app n) :=
  (rfl)

@[reassoc]
theorem condition (f : 𝔛 ⟶ 𝔖) (g : 𝔜 ⟶ 𝔖) [IsAdicHom g] :
    fst f g ≫ f = snd f g ≫ g := by
  ext n
  exact Limits.pullback.condition

/-- Universal lift into the levelwise fibre product `pullback f g`. -/
noncomputable def lift {𝔚 : AdicThickeningSystem.{u}} {f : 𝔛 ⟶ 𝔖} {g : 𝔜 ⟶ 𝔖} [IsAdicHom g]
    (u : 𝔚 ⟶ 𝔛) (v : 𝔚 ⟶ 𝔜) (h : u ≫ f = v ≫ g) : 𝔚 ⟶ pullback f g where
  app n := Limits.pullback.lift (u.app n) (v.app n) (congrArg (fun k ↦ k.app n) h)
  naturality _ := by
    refine Limits.pullback.hom_ext ?_ ?_
    · simp [AdicThickeningSystem.pullback]
    · simp [AdicThickeningSystem.pullback]

@[simp]
theorem lift_app {𝔚 : AdicThickeningSystem.{u}} {f : 𝔛 ⟶ 𝔖} {g : 𝔜 ⟶ 𝔖} [IsAdicHom g]
    (u : 𝔚 ⟶ 𝔛) (v : 𝔚 ⟶ 𝔜) (h : u ≫ f = v ≫ g) (n : ℕ) :
    (lift u v h).app n =
      Limits.pullback.lift (u.app n) (v.app n) (congrArg (fun k ↦ k.app n) h) :=
  (rfl)

@[reassoc (attr := simp)]
theorem lift_fst {𝔚 : AdicThickeningSystem.{u}} {f : 𝔛 ⟶ 𝔖} {g : 𝔜 ⟶ 𝔖} [IsAdicHom g]
    (u : 𝔚 ⟶ 𝔛) (v : 𝔚 ⟶ 𝔜) (h : u ≫ f = v ≫ g) :
    lift u v h ≫ fst f g = u := by
  ext n
  rw [comp_app]
  simp [AdicThickeningSystem.pullback]

@[reassoc (attr := simp)]
theorem lift_snd {𝔚 : AdicThickeningSystem.{u}} {f : 𝔛 ⟶ 𝔖} {g : 𝔜 ⟶ 𝔖} [IsAdicHom g]
    (u : 𝔚 ⟶ 𝔛) (v : 𝔚 ⟶ 𝔜) (h : u ≫ f = v ≫ g) :
    lift u v h ≫ snd f g = v := by
  ext n
  rw [comp_app]
  simp [AdicThickeningSystem.pullback]

theorem hom_ext {𝔚 : AdicThickeningSystem.{u}} {f : 𝔛 ⟶ 𝔖} {g : 𝔜 ⟶ 𝔖} [IsAdicHom g]
    {m₁ m₂ : 𝔚 ⟶ pullback f g} (h₁ : m₁ ≫ fst f g = m₂ ≫ fst f g)
    (h₂ : m₁ ≫ snd f g = m₂ ≫ snd f g) : m₁ = m₂ := by
  ext n
  exact Limits.pullback.hom_ext (congrArg (fun k ↦ k.app n) h₁) (congrArg (fun k ↦ k.app n) h₂)

end pullback

/-- The base change of an adic morphism `g` along any morphism `f` is adic. -/
instance isAdicHom_pullback_fst (f : 𝔛 ⟶ 𝔖) (g : 𝔜 ⟶ 𝔖) [IsAdicHom g] :
    IsAdicHom (pullback.fst f g) where
  isPullback := isPullback_pullbackMap_fst f g

/-- When `f` is also adic, the second projection `pullback f g ⟶ 𝔜` is adic as well. -/
instance isAdicHom_pullback_snd (f : 𝔛 ⟶ 𝔖) (g : 𝔜 ⟶ 𝔖) [IsAdicHom f] [IsAdicHom g] :
    IsAdicHom (pullback.snd f g) where
  isPullback := isPullback_pullbackMap_snd f g

/-- The levelwise fibre product `pullback f g` forms a pullback square in the category
`AdicThickeningSystem`. -/
theorem isPullback_pullback (f : 𝔛 ⟶ 𝔖) (g : 𝔜 ⟶ 𝔖) [IsAdicHom g] :
    IsPullback (pullback.fst f g) (pullback.snd f g) f g where
  w := pullback.condition f g
  isLimit' :=
    ⟨PullbackCone.IsLimit.mk _
      (fun s ↦ pullback.lift s.fst s.snd s.condition)
      (fun s ↦ pullback.lift_fst s.fst s.snd s.condition)
      (fun s ↦ pullback.lift_snd s.fst s.snd s.condition)
      (fun s _ h₁ h₂ ↦ pullback.hom_ext
        (h₁.trans (pullback.lift_fst s.fst s.snd s.condition).symm)
        (h₂.trans (pullback.lift_snd s.fst s.snd s.condition).symm))⟩

instance hasPullback_of_isAdicHom (f : 𝔛 ⟶ 𝔖) (g : 𝔜 ⟶ 𝔖) [IsAdicHom g] :
    HasPullback f g :=
  (isPullback_pullback f g).hasPullback

instance hasPullback_of_isAdicHom_left (f : 𝔛 ⟶ 𝔖) (g : 𝔜 ⟶ 𝔖) [IsAdicHom f] :
    HasPullback f g :=
  (isPullback_pullback g f).flip.hasPullback

end TauCeti.AlgebraicGeometry.AdicThickeningSystem
