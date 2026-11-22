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
import TauCeti.Analysis.LocallyConvex.WeakDual.Basic

/-!
# Weak-star double annihilators

The annihilator of a submodule of a topological module is weak-star closed; this needs only a
commutative topological semiring of scalars in which points are closed. Conversely, over `ℝ` or
`ℂ`, the annihilator of the preannihilator of a submodule of the continuous dual is its
weak-star closure. These statements use `Submodule.orthogonalBilin` for the canonical
`topDualPairing`; `StrongDual.toWeakDual` explicitly transports the continuous dual to the
weak-star topology. No completeness, separation, or local convexity of the original space is
needed.

The double-annihilator theorem is the standard duality result discussed in Megginson,
*An Introduction to Banach Space Theory*, §2.6. Its formal proof uses the weak representation
theorem `WeakDual.exists_forall_apply_eq_apply` and geometric Hahn--Banach separation in the
weak dual.
-/

public section

open Set

namespace Submodule

variable {𝕜 E : Type*}

section Closedness

variable [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜]
  [T1Space 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

/-- The annihilator of a submodule, transported to the weak dual, is weak-star closed. -/
theorem isClosed_map_orthogonalBilin_topDualPairing_flip (F : Submodule 𝕜 E) :
    IsClosed ((F.orthogonalBilin (topDualPairing 𝕜 E).flip).map
      StrongDual.toWeakDual.toLinearMap : Set (WeakDual 𝕜 E)) := by
  have heq : ((F.orthogonalBilin (topDualPairing 𝕜 E).flip).map
      StrongDual.toWeakDual.toLinearMap : Set (WeakDual 𝕜 E)) =
      ⋂ x ∈ F, (fun f : WeakDual 𝕜 E ↦ f x) ⁻¹' {0} := by
    ext f
    refine (mem_map_equiv (e := StrongDual.toWeakDual (𝕜 := 𝕜) (E := E)) _).trans ?_
    simp
  rw [heq]
  exact isClosed_biInter fun x _ ↦ isClosed_singleton.preimage (WeakDual.eval_continuous x)

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
  let H := G.map StrongDual.toWeakDual.toLinearMap
  apply le_antisymm
  · rintro _ ⟨f, hf, rfl⟩
    by_contra hn
    obtain ⟨l, u, hG, hf'⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜)
      (H.topologicalClosure.restrictScalars ℝ).convex H.isClosed_topologicalClosure hn
    obtain ⟨x, hx⟩ := WeakDual.exists_forall_apply_eq_apply l
    have hG' : ∀ g ∈ G, RCLike.re (g x) < u := fun g hg ↦ by
      simpa only [hx, LinearEquiv.coe_coe, StrongDual.toWeakDual_apply] using
        hG _ (H.le_topologicalClosure (mem_map_of_mem hg))
    -- A real upper bound on a functional over a subspace forces the functional to vanish there.
    have hxG : x ∈ G.orthogonalBilin (topDualPairing 𝕜 E) := by
      refine mem_orthogonalBilin.mpr fun g hg ↦ ?_
      rw [topDualPairing_apply]
      by_contra hne
      have hlt := hG' _ (G.smul_mem (((u + 1 : ℝ) : 𝕜) / g x) hg)
      rw [smul_apply, smul_eq_mul, div_mul_cancel₀ _ hne, RCLike.ofReal_re] at hlt
      linarith
    have hfx : f x = 0 := by simpa using mem_orthogonalBilin.mp hf x hxG
    have hu := hG' 0 G.zero_mem
    rw [hx, LinearEquiv.coe_coe, StrongDual.toWeakDual_apply, hfx, map_zero] at hf'
    rw [zero_apply, map_zero] at hu
    exact (hu.trans hf').false
  · exact H.topologicalClosure_minimal
      (map_mono (G.le_orthogonalBilin_flip_orthogonalBilin (B := topDualPairing 𝕜 E)))
      (G.orthogonalBilin (topDualPairing 𝕜 E)).isClosed_map_orthogonalBilin_topDualPairing_flip

end Submodule
