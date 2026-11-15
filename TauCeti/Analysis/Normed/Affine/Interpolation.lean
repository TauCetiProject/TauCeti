/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Affine interpolation on independent points

Arbitrary values on an affinely independent set in a finite-dimensional normed affine space
over a complete nontrivially normed field extend to a continuous affine map. In particular, an
affine map that is injective on a set with affinely independent image has a continuous affine
left inverse on the affine span of that set, hence on its convex hull. This allows inverse
simplicial maps to be checked one simplex at a time.

The construction extends the independent set to an affine basis and uses Mathlib's
continuous barycentric coordinates. See Rourke--Sanderson, *Introduction to Piecewise-Linear
Topology*, Chapter 1, for affine maps of simplices.
-/

public section

open Set

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

namespace AffineIndependent

variable {V P F : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [MetricSpace P] [NormedAddTorsor V P]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul 𝕜 F] {s : Set P}

/-- Values on an affinely independent set extend to a continuous affine map of the ambient
space. The set need not span the ambient space, and may be empty. -/
theorem exists_continuousAffineMap_eqOn (hs : AffineIndependent 𝕜 ((↑) : s → P))
    (f : P → F) : ∃ A : P →ᴬ[𝕜] F, EqOn A f s := by
  classical
  obtain ⟨t, hst, ht, hspan⟩ := exists_subset_affineIndependent_affineSpan_eq_top hs
  let b : AffineBasis t 𝕜 P := ⟨Subtype.val, ht, by simpa using hspan⟩
  have : Finite t := b.finite
  let : Fintype t := Fintype.ofFinite t
  let c (i : t) : P →ᴬ[𝕜] 𝕜 := ⟨b.coord i, continuous_barycentric_coord b i⟩
  let A : P →ᴬ[𝕜] F := ∑ i : t,
    ((ContinuousLinearMap.id 𝕜 𝕜).smulRight (f i)).toContinuousAffineMap.comp (c i)
  refine ⟨A, fun x hx => ?_⟩
  have hcoord (i : t) : b.coord i x = if i = ⟨x, hst hx⟩ then 1 else 0 :=
    b.coord_apply i ⟨x, hst hx⟩
  -- Evaluation at `x` is additive, so it distributes over the sum defining `A`.
  calc
    A x = AddMonoidHom.mk' (fun A : P →ᴬ[𝕜] F => A x) (fun _ _ => rfl) A := rfl
    _ = f x := by simp [A, c, hcoord]

end AffineIndependent

namespace AffineMap

variable {E V P : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]
  [MetricSpace P] [NormedAddTorsor V P] {s : Set E}

/-- An affine map that is injective on a set whose image is affinely independent has a
continuous affine left inverse on the affine span of that set. -/
theorem exists_leftInvOn_affineSpan (A : E →ᵃ[𝕜] P)
    (hA : AffineIndependent 𝕜 ((↑) : (A '' s) → P)) (hinj : InjOn A s) :
    ∃ B : P →ᴬ[𝕜] E, LeftInvOn B A (affineSpan 𝕜 s) := by
  obtain ⟨B, hB⟩ := hA.exists_continuousAffineMap_eqOn (Function.invFunOn A s)
  have heq : EqOn (B.toAffineMap.comp A) (id 𝕜 E) s := fun x hx =>
    (hB ⟨x, hx, rfl⟩).trans (hinj.leftInvOn_invFunOn hx)
  exact ⟨B, fun x hx => eqOn_affineSpan heq hx⟩

end AffineMap
