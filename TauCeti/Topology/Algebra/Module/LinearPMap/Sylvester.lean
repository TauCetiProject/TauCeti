/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import TauCeti.Topology.Algebra.Module.LinearPMap.Intertwining

/-!
# Sylvester equations for partial linear maps

The domain-aware Sylvester equation `A X - X B = C` for partially defined
operators `A` and `B` and continuous linear maps `X` and `C` between topological modules.

The equation requires `X` to carry the domain of `B` into that of `A`.
It specializes the ordinary Sylvester equation of continuous linear maps and is preserved by
addition, negation, subtraction, and scalar multiplication of solutions and
right-hand sides. The homogeneous equation `A X - X B = 0` says exactly that `X`
intertwines `B` with `A` in the domain-aware sense of `LinearPMap.Intertwines`.

Adapted from the Kitware DKPS formalization,
`ForTauCeti/Analysis/InnerProductSpace/LinearPMap/Sylvester.lean`.
-/

public section

namespace LinearPMap

variable {𝕜 E F : Type*} [Ring 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
  [AddCommGroup F] [TopologicalSpace F] [Module 𝕜 F]

/-- A domain-aware Sylvester equation `A X - X B = C`: `X` maps the domain
of `B` into the domain of `A`, and the operator identity holds there. -/
structure SylvesterEquation
    (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F)
    (X C : F →L[𝕜] E) : Prop where
  /-- The continuous unknown carries the domain of `B` into that of `A`. -/
  mapsTo_domain : ∀ x : B.domain, X (x : F) ∈ A.domain
  /-- The Sylvester identity on vectors in the domain of `B`. -/
  equation : ∀ x : B.domain,
    A ⟨X (x : F), mapsTo_domain x⟩ - X (B x) = C (x : F)

namespace SylvesterEquation

variable {X Y C D : F →L[𝕜] E}

/-- The domain-aware equation for full-domain partial operators is equivalent
to the ordinary Sylvester equation between everywhere-defined continuous linear maps. -/
@[simp] theorem toPMap_top_iff [IsTopologicalAddGroup E] {A : E →L[𝕜] E} {B : F →L[𝕜] F} :
    SylvesterEquation (A.toLinearMap.toPMap ⊤) (B.toLinearMap.toPMap ⊤) X C ↔
      A ∘L X - X ∘L B = C := by
  refine ⟨fun h => ?_, fun h => ⟨fun _ => Submodule.mem_top, fun x => ?_⟩⟩
  · ext x
    simpa [LinearMap.toPMap_apply] using h.equation ⟨x, Submodule.mem_top⟩
  · rcases x with ⟨x, hx⟩
    simpa [LinearMap.toPMap_apply] using DFunLike.congr_fun h x

/-- An ordinary Sylvester equation between everywhere-defined continuous linear maps induces
an equation between the corresponding full-domain partial operators. -/
theorem toPMap_top [IsTopologicalAddGroup E] {A : E →L[𝕜] E} {B : F →L[𝕜] F}
    (hEq : A ∘L X - X ∘L B = C) :
    SylvesterEquation (A.toLinearMap.toPMap ⊤) (B.toLinearMap.toPMap ⊤) X C :=
  toPMap_top_iff.mpr hEq

/-- The zero map solves the homogeneous domain-aware equation. -/
theorem zero (A : E →ₗ.[𝕜] E) (B : F →ₗ.[𝕜] F) : SylvesterEquation A B 0 0 where
  mapsTo_domain _ := A.domain.zero_mem
  equation _ := by simpa using congrArg A ((Submodule.mk_eq_zero _ A.domain.zero_mem).mpr rfl)

variable {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}

/-- Domain-aware Sylvester equations are preserved by addition. -/
theorem add [ContinuousAdd E] (hX : SylvesterEquation A B X C)
    (hY : SylvesterEquation A B Y D) : SylvesterEquation A B (X + Y) (C + D) where
  mapsTo_domain x := A.domain.add_mem (hX.mapsTo_domain x) (hY.mapsTo_domain x)
  equation x := by
    -- The domain vector `(X + Y) x` is the sum of the domain vectors `X x` and `Y x`.
    have hsum : (⟨(X + Y) x, A.domain.add_mem (hX.mapsTo_domain x) (hY.mapsTo_domain x)⟩ :
        A.domain) = ⟨X x, hX.mapsTo_domain x⟩ + ⟨Y x, hY.mapsTo_domain x⟩ := by ext; simp
    rw [hsum, A.map_add]
    simpa [add_sub_add_comm] using congr($(hX.equation x) + $(hY.equation x))

/-- Domain-aware Sylvester equations are preserved by negation. -/
theorem neg [IsTopologicalAddGroup E] (hX : SylvesterEquation A B X C) :
    SylvesterEquation A B (-X) (-C) where
  mapsTo_domain x := A.domain.neg_mem (hX.mapsTo_domain x)
  equation x := by
    -- The domain vector `(-X) x` is the negative of the domain vector `X x`.
    have hneg : (⟨(-X) x, A.domain.neg_mem (hX.mapsTo_domain x)⟩ : A.domain) =
        -⟨X x, hX.mapsTo_domain x⟩ := by ext; simp
    rw [hneg, A.map_neg]
    simpa [neg_add_eq_sub] using congr(-$(hX.equation x))

/-- Domain-aware Sylvester equations are preserved by subtraction. -/
theorem sub [IsTopologicalAddGroup E] (hX : SylvesterEquation A B X C)
    (hY : SylvesterEquation A B Y D) : SylvesterEquation A B (X - Y) (C - D) := by
  simpa [sub_eq_add_neg] using hX.add hY.neg

/-- Domain-aware Sylvester equations are preserved by scalar multiplication. -/
theorem smul [SMulCommClass 𝕜 𝕜 E] [ContinuousConstSMul 𝕜 E]
    (hX : SylvesterEquation A B X C) (c : 𝕜) : SylvesterEquation A B (c • X) (c • C) where
  mapsTo_domain x := A.domain.smul_mem c (hX.mapsTo_domain x)
  equation x := by
    -- The domain vector `(c • X) x` is `c` times the domain vector `X x`.
    have hsmul : (⟨(c • X) x, A.domain.smul_mem c (hX.mapsTo_domain x)⟩ : A.domain) =
        c • ⟨X x, hX.mapsTo_domain x⟩ := by ext; simp
    rw [hsmul, A.map_smul]
    simpa [smul_sub] using congr(c • $(hX.equation x))

end SylvesterEquation

/-- The homogeneous domain-aware Sylvester equation `A X - X B = 0` says exactly that `X`
intertwines `B` with `A`. -/
theorem sylvesterEquation_zero_iff_intertwines {A : E →ₗ.[𝕜] E} {B : F →ₗ.[𝕜] F}
    {X : F →L[𝕜] E} : SylvesterEquation A B X 0 ↔ B.Intertwines A X :=
  ⟨fun h => ⟨h.mapsTo_domain, fun x => (sub_eq_zero.mp (by simpa using h.equation x)).symm⟩,
    fun h => ⟨h.mem_domain, fun x => by simpa using sub_eq_zero.mpr (h.apply_eq x).symm⟩⟩

end LinearPMap
