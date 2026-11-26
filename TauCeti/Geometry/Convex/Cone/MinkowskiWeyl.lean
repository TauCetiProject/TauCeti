/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Convex.Cone.FiniteGeneration
public import TauCeti.Geometry.Convex.Cone.FiniteDuality

/-!
# Minkowski–Weyl duality for pointed cones

In finite-dimensional spaces over a linearly ordered field, finite generation
is equivalent to having finitely many defining linear inequalities. The two
directions combine finite generation under halfspace cuts with the algebraic
separation theorem for finitely generated cones. No topological closedness is
assumed in this argument, and cones with lineality are allowed.

Consequently finitely generated cones are closed under intersection
(`Submodule.FG.cone_inf`) and under preimages by linear maps
(`Submodule.FG.cone_comap`). Farkas' lemma for an intersection with a preimage,
`PointedCone.dual_flip_inf_comap`, describes the dual of `σ ⊓ τ.comap f` as
`dual σ ⊔ f.dualMap (dual τ)`.

## Provenance

Adapted from `Mei/Geometry/Convex/Cone/MinkowskiWeyl.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`68536122a97fed8e87bc6870b9427151971b9ab2`, licensed under Apache 2.0.
-/

public section

namespace Submodule.FG

variable {K V : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup V] [Module K V] [Module.Finite K V] {C : PointedCone K V}

/-- A finitely generated cone in a finite-dimensional space is cut out by
finitely many algebraic linear inequalities under evaluation. -/
theorem cone_dualFG (hC : C.FG) :
    C.DualFG (LinearMap.id : Module.Dual K V →ₗ[K] Module.Dual K V) := by
  let p : Module.Dual K V →ₗ[K] Module.Dual K V := LinearMap.id
  have hdual : (PointedCone.dual p.flip C).FG :=
    (PointedCone.DualFG.dual_of_fg p.flip hC).fg
  have hresult := PointedCone.DualFG.dual_of_fg p hdual
  rwa [hC.cone_dual_dual_flip_id] at hresult

end Submodule.FG

namespace PointedCone

variable {K V : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup V] [Module K V] [Module.Finite K V] {C : PointedCone K V}

/-- **Minkowski–Weyl:** a pointed cone is finitely generated exactly when it is
cut out by finitely many linear halfspaces, including when it has lineality. -/
theorem fg_iff_dualFG :
    C.FG ↔ C.DualFG (LinearMap.id : Module.Dual K V →ₗ[K] Module.Dual K V) :=
  ⟨Submodule.FG.cone_dualFG, DualFG.fg⟩

end PointedCone

namespace Submodule.FG

variable {K V W : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup V] [Module K V] [Module.Finite K V] [AddCommGroup W] [Module K W]
  [Module.Finite K W] {C D : PointedCone K V} {τ : PointedCone K W}

/-- The intersection of two finitely generated cones in a finite-dimensional space is finitely
generated: both are cut out by finitely many inequalities. -/
theorem cone_inf (hC : C.FG) (hD : D.FG) : (C ⊓ D).FG :=
  (hC.cone_dualFG.inf hD.cone_dualFG).fg

/-- The preimage of a finitely generated cone under a linear map of finite-dimensional spaces is
finitely generated: it is cut out by the pullbacks of finitely many inequalities. -/
theorem cone_comap (hτ : τ.FG) (f : V →ₗ[K] W) : (τ.comap f).FG := by
  obtain ⟨s, hs⟩ := hτ.cone_dualFG
  refine PointedCone.DualFG.fg
    (p := (LinearMap.id : Module.Dual K W →ₗ[K] Module.Dual K W).compl₂ f) ⟨s, ?_⟩
  rw [← hs]
  ext x
  simp

end Submodule.FG

namespace PointedCone

variable {K V W : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup V] [Module K V] [Module.Finite K V] [AddCommGroup W] [Module K W]
  [Module.Finite K W] {σ : PointedCone K V} {τ : PointedCone K W}

/-- **Farkas' lemma for an intersection with a preimage.** For finitely generated cones `σ ⊆ V`
and `τ ⊆ W` and a linear map `f : V → W`, a linear functional is nonnegative on
`σ ⊓ τ.comap f` exactly when it is the sum of a functional nonnegative on `σ` and the pullback
along `f` of a functional nonnegative on `τ`. -/
theorem dual_flip_inf_comap (hσ : σ.FG) (hτ : τ.FG) (f : V →ₗ[K] W) :
    dual (LinearMap.id : Module.Dual K V →ₗ[K] Module.Dual K V).flip (σ ⊓ τ.comap f) =
      dual (LinearMap.id : Module.Dual K V →ₗ[K] Module.Dual K V).flip σ ⊔
        (dual (LinearMap.id : Module.Dual K W →ₗ[K] Module.Dual K W).flip τ).map
          f.dualMap := by
  refine le_antisymm (fun ℓ hℓ ↦ ?_) (sup_le (dual_anti inf_le_left) ?_)
  · have hA : (dual (LinearMap.id : Module.Dual K V →ₗ[K] Module.Dual K V).flip σ ⊔
        (dual (LinearMap.id : Module.Dual K W →ₗ[K] Module.Dual K W).flip τ).map
          f.dualMap).FG :=
      (DualFG.dual_of_fg _ hσ).fg.sup ((DualFG.dual_of_fg _ hτ).fg.map _)
    by_contra hℓA
    -- A functional outside the finitely generated cone `A` is separated from it by a point `x`
    -- of `V`; the bipolar theorem puts `x` in `σ ⊓ τ.comap f`, where `ℓ x < 0`.
    obtain ⟨Λ, hΛ, hΛℓ⟩ := hA.exists_cone_dual_nonneg_and_lt_zero hℓA
    obtain ⟨x, rfl⟩ := (Module.evalEquiv K V).surjective Λ
    have hx : x ∈ σ ⊓ τ.comap f := by
      refine Submodule.mem_inf.2 ⟨?_, ?_⟩
      · rw [← hσ.cone_dual_dual_flip_id]
        exact fun a ha ↦ by simpa using hΛ a (Submodule.mem_sup_left ha)
      · rw [mem_comap, ← hτ.cone_dual_dual_flip_id]
        exact fun b hb ↦ by
          simpa using hΛ _ (Submodule.mem_sup_right (Submodule.mem_map_of_mem hb))
    exact (hℓ hx).not_gt (by simpa using hΛℓ)
  · rintro _ ⟨b, hb, rfl⟩ x hx
    simpa using hb hx.2

end PointedCone
