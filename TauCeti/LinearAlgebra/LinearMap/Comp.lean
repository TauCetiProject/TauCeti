/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Span.Defs

/-!
# Composites of intertwining linear maps

A linear map `f : M → N` intertwines endomorphisms `dM` and `dN` when `dN ∘ f = f ∘ dM`. This
file records that intertwining is stable under composition, the step behind the composition law
of cochain maps assembled from maps commuting with differentials. It also records that
precomposition with a retraction of a section is a section of precomposition
(`LinearMap.lcomp_comp_lcomp_eq_id`), and that a composite `P ∘ L` is bijective exactly when `L`
is injective, `P` is onto, and the kernel of `P` is complementary to the range of `L`
(`LinearMap.bijective_comp_iff`).
-/

public section

namespace LinearMap

variable {R M N P : Type*} [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
  [Module R M] [Module R N] [Module R P]

/-- If `f` intertwines `dM` with `dN` and `g` intertwines `dN` with `dP`, then `g ∘ f`
intertwines `dM` with `dP`. -/
theorem comp_comm_comp {dM : M →ₗ[R] M} {dN : N →ₗ[R] N} {dP : P →ₗ[R] P} {f : M →ₗ[R] N}
    {g : N →ₗ[R] P} (hg : dP ∘ₗ g = g ∘ₗ dN) (hf : dN ∘ₗ f = f ∘ₗ dM) :
    dP ∘ₗ (g ∘ₗ f) = (g ∘ₗ f) ∘ₗ dM := by
  rw [← comp_assoc, hg, comp_assoc, hf, comp_assoc]

/-- Precomposition with a retraction `p` of a section `i` is a section of precomposition with
`i`: `lcomp R N i ∘ₗ lcomp R N p = id`. -/
theorem lcomp_comp_lcomp_eq_id {R M N F : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [AddCommMonoid F] [Module R F] {i : M →ₗ[R] F}
    {p : F →ₗ[R] M} (hpi : p ∘ₗ i = .id) : lcomp R N i ∘ₗ lcomp R N p = .id := by
  ext x : 1
  simp [lcomp_apply', comp_assoc, hpi]

section Ring

variable {R E F Y : Type*} [Ring R] [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
  [AddCommGroup Y] [Module R Y]

/-- A composite `P ∘ L` is bijective exactly when `L` is injective, `P` is onto, and the kernel of
`P` is complementary to the range of `L`. -/
theorem bijective_comp_iff {L : E →ₗ[R] F} {P : F →ₗ[R] Y} :
    Function.Bijective (P ∘ₗ L) ↔
      Function.Injective L ∧ IsCompl (range L) (ker P) ∧ Function.Surjective P := by
  constructor
  · rintro ⟨hinj, hsurj⟩
    refine ⟨fun x y hxy ↦ hinj (by simp [hxy]), ⟨?_, ?_⟩, fun y ↦ ?_⟩
    · rw [Submodule.disjoint_def]
      rintro _ ⟨x, rfl⟩ hx
      rw [mem_ker] at hx
      rw [hinj (show (P ∘ₗ L) x = (P ∘ₗ L) 0 by simpa using hx), map_zero]
    · rw [codisjoint_iff, eq_top_iff]
      intro f _
      obtain ⟨x, hx⟩ := hsurj (P f)
      refine Submodule.mem_sup.mpr ⟨L x, ⟨x, rfl⟩, f - L x, ?_, add_sub_cancel _ _⟩
      simpa [sub_eq_zero] using hx.symm
    · obtain ⟨x, hx⟩ := hsurj y
      exact ⟨L x, hx⟩
  · rintro ⟨hL, hc, hP⟩
    refine ⟨fun x y hxy ↦ hL ?_, fun y ↦ ?_⟩
    · have hmem : L (x - y) ∈ range L ⊓ ker P :=
        ⟨⟨x - y, rfl⟩, by simpa [mem_ker, sub_eq_zero] using hxy⟩
      rw [hc.inf_eq_bot, Submodule.mem_bot, map_sub, sub_eq_zero] at hmem
      exact hmem
    · obtain ⟨f, rfl⟩ := hP y
      have hf : f ∈ range L ⊔ ker P := hc.sup_eq_top ▸ Submodule.mem_top
      obtain ⟨_, ⟨x, rfl⟩, w, hw, rfl⟩ := Submodule.mem_sup.mp hf
      exact ⟨x, by simp [mem_ker.mp hw]⟩

end Ring

end LinearMap
