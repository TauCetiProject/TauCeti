/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.WeakDual
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# Weak-star double annihilators

The annihilator of a submodule of a topological vector space is weak-star closed. Conversely,
the annihilator of the preannihilator of a submodule of its continuous dual is its weak-star
closure. These statements use `Submodule.orthogonalBilin` for the canonical `topDualPairing`;
`StrongDual.toWeakDual` explicitly transports the continuous dual to the weak-star topology.
No completeness, separation, or local convexity of the original space is needed.

The double-annihilator theorem is the standard duality result discussed in Megginson,
*An Introduction to Banach Space Theory*, §2.6. Its formal proof uses Mathlib's weak
representation theorem `LinearMap.dualEmbedding_surjective` and geometric Hahn--Banach
separation in the weak dual.
-/

public section

open Set

namespace Submodule

variable {𝕜 E : Type*}

section Closedness

variable [NontriviallyNormedField 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

/-- The annihilator of a submodule, transported to the weak dual, is weak-star closed. -/
theorem isClosed_map_orthogonalBilin_topDualPairing_flip (F : Submodule 𝕜 E) :
    IsClosed ((F.orthogonalBilin (topDualPairing 𝕜 E).flip).map
      StrongDual.toWeakDual.toLinearMap : Set (WeakDual 𝕜 E)) := by
  have heq : ((F.orthogonalBilin (topDualPairing 𝕜 E).flip).map
      StrongDual.toWeakDual.toLinearMap : Set (WeakDual 𝕜 E)) =
      ⋂ x : F, {f | f x = 0} := by
    ext f
    refine (mem_map_equiv (e := StrongDual.toWeakDual (𝕜 := 𝕜) (E := E)) _).trans ?_
    simp only [mem_orthogonalBilin, mem_iInter, mem_ofPred_eq, Subtype.forall,
      LinearMap.flip_apply, topDualPairing_apply, StrongDual.symm_toWeakDual,
      WeakDual.toStrongDual_apply]
  rw [heq]
  exact isClosed_iInter fun x ↦ isClosed_eq (WeakDual.eval_continuous (x : E)) continuous_const

end Closedness

variable [RCLike 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]

/-- The double annihilator of a submodule of the continuous dual, transported to the weak dual,
is its weak-star closure. The first orthogonal complement is the preannihilator in `E`; the
second is its annihilator in the continuous dual. -/
theorem map_orthogonalBilin_flip_orthogonalBilin_eq_topologicalClosure
    (G : Submodule 𝕜 (StrongDual 𝕜 E)) :
    ((G.orthogonalBilin (topDualPairing 𝕜 E)).orthogonalBilin
      (topDualPairing 𝕜 E).flip).map StrongDual.toWeakDual.toLinearMap =
      (G.map StrongDual.toWeakDual.toLinearMap).topologicalClosure := by
  -- The weak-dual synonym inherits these structures from the canonical dual pairing.
  let : AddCommGroup (WeakDual 𝕜 E) :=
    inferInstanceAs (AddCommGroup (WeakBilin (topDualPairing 𝕜 E)))
  let : IsTopologicalAddGroup (WeakDual 𝕜 E) :=
    inferInstanceAs (IsTopologicalAddGroup (WeakBilin (topDualPairing 𝕜 E)))
  let : IsScalarTower ℝ 𝕜 (WeakDual 𝕜 E) :=
    inferInstanceAs (IsScalarTower ℝ 𝕜 (StrongDual 𝕜 E))
  let : LocallyConvexSpace ℝ (WeakDual 𝕜 E) :=
    inferInstanceAs (LocallyConvexSpace ℝ (WeakBilin (topDualPairing 𝕜 E)))
  let H := G.map StrongDual.toWeakDual.toLinearMap
  apply le_antisymm
  · rintro _ ⟨f, hf, rfl⟩
    by_contra hn
    obtain ⟨l, u, hG, hf'⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜)
      (H.topologicalClosure.restrictScalars ℝ).convex H.isClosed_topologicalClosure hn
    obtain ⟨x, rfl⟩ := LinearMap.dualEmbedding_surjective (topDualPairing 𝕜 E) l
    -- The representing functional and the restricted canonical pairing evaluate at `x`.
    have hG_eval : ∀ g ∈ H.topologicalClosure, RCLike.re (g x) < u := hG
    have hf_eval : u < RCLike.re (f x) := hf'
    have hx : x ∈ G.orthogonalBilin (topDualPairing 𝕜 E) := by
      rw [mem_orthogonalBilin_iff_le_ker_flip, LinearMap.le_ker_iff_comp_subtype_eq_zero]
      by_contra hne
      obtain ⟨g, hg⟩ := LinearMap.surjective hne (((u + 1 : ℝ) : 𝕜))
      have hg_eval : (g : StrongDual 𝕜 E) x = ((u + 1 : ℝ) : 𝕜) := hg
      have hscalar := hG_eval (StrongDual.toWeakDual (g : StrongDual 𝕜 E))
        (H.le_topologicalClosure (mem_map.mpr ⟨g, g.property, rfl⟩))
      rw [StrongDual.toWeakDual_apply, hg_eval, RCLike.ofReal_re] at hscalar
      linarith
    have hu := hG_eval (StrongDual.toWeakDual (0 : StrongDual 𝕜 E))
      (by simpa only [map_zero] using H.topologicalClosure.zero_mem)
    simp only [StrongDual.toWeakDual_apply, zero_apply, RCLike.zero_re] at hu
    have hfx := (mem_orthogonalBilin.mp hf) x hx
    simp only [LinearMap.flip_apply, topDualPairing_apply] at hfx
    rw [hfx, RCLike.zero_re] at hf_eval
    exact (hu.trans hf_eval).false
  · exact H.topologicalClosure_minimal
      (map_mono (G.le_orthogonalBilin_flip_orthogonalBilin (B := topDualPairing 𝕜 E)))
      (G.orthogonalBilin (topDualPairing 𝕜 E)).isClosed_map_orthogonalBilin_topDualPairing_flip

end Submodule
