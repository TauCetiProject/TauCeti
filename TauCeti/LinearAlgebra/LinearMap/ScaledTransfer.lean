/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Transferring endomorphisms up to scalar multiples

If a scalar multiple of an endomorphism followed by a linear map belongs to the span of
composites in the opposite order, this transfer can be composed. Along a chain of linear maps,
the cost is the product of the individual scalars. This applies to intertwining identities
whose denominators have been cleared.
-/

public section

open Submodule

namespace LinearMap

/-- If `F` transfers `T` to the span of the operators in `S` up to `c`, and `G` transfers each
operator in `S` to the span of the operators in `U` up to `d`, then `G ∘ F` transfers `T` up to
`d * c`. The operators in either set need not commute. -/
theorem mul_smul_comp_mem_span_of_smul_comp_mem_span
    {R V W X : Type*} [CommSemiring R] [AddCommMonoid V] [AddCommMonoid W] [AddCommMonoid X]
    [Module R V] [Module R W] [Module R X]
    (F : V →ₗ[R] W) (G : W →ₗ[R] X) {T : Module.End R V}
    {S : Set (Module.End R W)} {U : Set (Module.End R X)} {c d : R}
    (hF : c • F.comp T ∈ span R ((fun s ↦ s.comp F) '' S))
    (hG : ∀ s ∈ S, d • G.comp s ∈ span R ((fun u ↦ u.comp G) '' U)) :
    (d * c) • (G.comp F).comp T ∈ span R ((fun u ↦ u.comp (G.comp F)) '' U) := by
  let P := d • compRight R (M := V) G
  let Q := lcomp R X F
  have hm : (span R ((fun s ↦ s.comp F) '' S)).map P ≤
      span R ((fun u ↦ u.comp (G.comp F)) '' U) := by
    rw [map_span, span_le]
    rintro _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩
    have h := apply_mem_span_image_of_mem_span Q (hG s hs)
    rw [Set.image_image] at h
    simpa only [P, Q, LinearMap.smul_apply, compRight_apply, map_smul, lcomp_apply', comp_assoc,
      SetLike.mem_coe] using h
  simpa only [P, LinearMap.smul_apply, compRight_apply, comp_smul, smul_smul, comp_assoc] using
    hm (mem_map_of_mem (f := P) hF)

/-- Transfer a distinguished operator through a succession of linear maps, clearing one scalar
at each step. `C j` is the composite of the first `j` maps; only the maps up to `C n` matter.
Each step can have its own family of available endomorphisms and its own scalar. -/
theorem prod_smul_comp_mem_span_of_smul_comp_mem_span
    {R : Type*} [CommSemiring R] {V : ℕ → Type*} [∀ j, AddCommMonoid (V j)]
    [∀ j, Module R (V j)] {n : ℕ}
    (C : ∀ j, V 0 →ₗ[R] V j) (L : ∀ j, V j →ₗ[R] V (j + 1))
    (S : ∀ j, Set (Module.End R (V j))) (c : ℕ → R) {T : Module.End R (V 0)}
    (hT : T ∈ S 0) (h0 : C 0 = LinearMap.id)
    (hC : ∀ j < n, C (j + 1) = (L j).comp (C j))
    (hL : ∀ j < n, ∀ s ∈ S j, c j • (L j).comp s ∈ span R ((fun u ↦ u.comp (L j)) '' S (j + 1))) :
    (∏ j ∈ Finset.range n, c j) • (C n).comp T ∈ span R ((fun u ↦ u.comp (C n)) '' S n) := by
  induction n with
  | zero =>
    simpa [h0] using (subset_span (R := R) hT : T ∈ span R (S 0))
  | succ n ih =>
    rw [Finset.prod_range_succ, mul_comm, hC n (Nat.lt_succ_self n)]
    exact (C n).mul_smul_comp_mem_span_of_smul_comp_mem_span (L n)
      (ih (fun j hj ↦ hC j (Nat.lt_succ_of_lt hj)) (fun j hj ↦ hL j (Nat.lt_succ_of_lt hj)))
      (hL n (Nat.lt_succ_self n))

end LinearMap
