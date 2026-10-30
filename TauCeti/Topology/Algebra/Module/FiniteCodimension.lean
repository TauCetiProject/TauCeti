/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Dense subspaces and closed subspaces of finite codimension

Let `E` be a topological vector space over a complete nontrivially normed field, `S` a closed
subspace of finite codimension and `D` a dense subspace. Then `D` meets every coset of `S`, that
is `S ⊔ D = E`, and `S ∩ D` is dense in `S`.

These facts compare a dense subalgebra with its ambient algebra modulo ideals of finite
codimension: the residue algebras agree, and the ideal is recovered as the closure of its
intersection with the dense subalgebra. A typical case is a dense subalgebra of an affinoid
algebra modulo a maximal ideal, whose residue field is finite over the base field.
-/

public section

namespace Submodule

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [Module 𝕜 E]
  [ContinuousSMul 𝕜 E] {S D : Submodule 𝕜 E}

/-- A closed subspace of finite codimension and a dense subspace together span the whole space.
Equivalently, every class of `E ⧸ S` has a representative in `D`. -/
theorem sup_eq_top_of_dense [FiniteDimensional 𝕜 (E ⧸ S)] (hS : IsClosed (S : Set E))
    (hD : Dense (D : Set E)) : S ⊔ D = ⊤ := by
  have hclosed := isClosed_mono_of_finiteDimensional_quotient hS (le_sup_left (b := D))
  refine eq_top_iff'.2 fun x ↦ ?_
  rw [← SetLike.mem_coe, ← hclosed.closure_eq]
  exact closure_mono (SetLike.coe_subset_coe.2 le_sup_right) (hD x)

/-- A closed subspace `S` of finite codimension is the closure of its intersection with a dense
subspace `D`. -/
theorem closure_inf_eq_of_dense [FiniteDimensional 𝕜 (E ⧸ S)] (hS : IsClosed (S : Set E))
    (hD : Dense (D : Set E)) : closure ((S ⊓ D : Submodule 𝕜 E) : Set E) = S := by
  -- A linear section `r` of `D → E ⧸ S` gives the continuous map `h x = x - r (x mod S)`. It
  -- fixes `S` pointwise and sends `D` into `S ⊓ D`, so it carries the density of `D` to `S`.
  have hsurj : LinearMap.range (S.mkQ ∘ₗ D.subtype) = ⊤ := by
    refine LinearMap.range_eq_top.2 fun q ↦ ?_
    obtain ⟨x, rfl⟩ := S.mkQ_surjective q
    obtain ⟨s, hs, d, hd, rfl⟩ := mem_sup.1 ((sup_eq_top_of_dense hS hD).ge (mem_top (x := x)))
    exact ⟨⟨d, hd⟩, by simp [(Quotient.mk_eq_zero S).2 hs]⟩
  obtain ⟨r, hr⟩ := (S.mkQ ∘ₗ D.subtype).exists_rightInverse_of_surjective hsurj
  have hr' (q : E ⧸ S) : Quotient.mk (r q : E) = q := LinearMap.congr_fun hr q
  let h : E → E := fun x ↦ x - D.subtype (r (S.mkQ x))
  have hcont : Continuous h :=
    continuous_id.sub ((D.subtype ∘ₗ r).continuous_of_finiteDimensional.comp S.continuous_mkQ)
  have hD' : h '' D ⊆ ((S ⊓ D : Submodule 𝕜 E) : Set E) := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨(Quotient.mk_eq_zero S).1 (by simp [h, hr']), D.sub_mem hx (r _).2⟩
  refine subset_antisymm (closure_minimal (by simp) hS) fun x hx ↦ ?_
  have hx' : h x = x := by simp [h, (Quotient.mk_eq_zero S).2 hx]
  rw [← hx']
  exact closure_mono hD' (image_closure_subset_closure_image hcont (Set.mem_image_of_mem h (hD x)))

end Submodule
