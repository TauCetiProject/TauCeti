/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Baire.Lemmas

/-!
# The complement of finitely many closed hyperplanes is dense

Over a nontrivially normed field `𝕜`, a proper subspace of a topological vector space has empty
interior (`Submodule.eq_top_of_nonempty_interior'`). So the kernel of a nonzero continuous linear
functional is a closed hyperplane with dense complement, and the points at which finitely many
nonzero continuous linear functionals all take nonzero values form a dense open set
(`ContinuousLinearMap.dense_setOf_forall_apply_ne_zero`). This is the generic-position statement
behind choices of a parameter avoiding finitely many hyperplanes, such as a regular element of a
torus at which prescribed functionals take pairwise distinct values.
-/

public section

open Set

namespace ContinuousLinearMap

variable {𝕜 E ι : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [TopologicalSpace E]
  [ContinuousAdd E] [Module 𝕜 E] [ContinuousSMul 𝕜 E]

/-- **Finitely many nonzero functionals are simultaneously nonzero on a dense set.** For finitely
many nonzero continuous linear functionals `fᵢ` on a topological vector space over a nontrivially
normed field, the points at which every `fᵢ` is nonzero form a dense set; it is open, as a finite
intersection of complements of closed hyperplanes. -/
theorem dense_setOf_forall_apply_ne_zero [Finite ι] {f : ι → E →L[𝕜] 𝕜} (hf : ∀ i, f i ≠ 0) :
    Dense {x | ∀ i, f i x ≠ 0} := by
  rw [show {x | ∀ i, f i x ≠ 0} = ⋂₀ range fun i ↦ {x | f i x ≠ 0} by ext; simp]
  refine (finite_range _).dense_sInter ?_ ?_ <;> rintro _ ⟨i, rfl⟩
  · exact isOpen_ne_fun (f i).continuous continuous_const
  · -- The kernel of `f i` is a proper subspace, so it has empty interior.
    have h : interior (LinearMap.ker (f i : E →ₗ[𝕜] 𝕜) : Set E) = ∅ := by
      by_contra hne
      have htop := (LinearMap.ker (f i : E →ₗ[𝕜] 𝕜)).eq_top_of_nonempty_interior'
        (ne_empty_iff_nonempty.1 hne)
      refine hf i (ext fun x ↦ ?_)
      have hx : x ∈ LinearMap.ker (f i : E →ₗ[𝕜] 𝕜) := htop ▸ Submodule.mem_top
      simpa using hx
    have hd := interior_eq_empty_iff_dense_compl.1 h
    convert hd using 1
    ext x
    simp

end ContinuousLinearMap
