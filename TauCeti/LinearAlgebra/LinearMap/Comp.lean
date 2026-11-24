/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.LinearAlgebra.Span.Defs

/-!
# Composites of intertwining linear maps

A linear map `f : M → N` intertwines endomorphisms `dM` and `dN` when `dN ∘ f = f ∘ dM`. This
file records that intertwining is stable under composition, the step behind the composition law
of cochain maps assembled from maps commuting with differentials. It also records that
precomposition with a retraction of a section is a section of precomposition
(`LinearMap.lcomp_comp_lcomp_eq_id`), that powers of precomposition by an endomorphism equal
precomposition by the corresponding power (`LinearMap.lcomp_pow`), that commuting squares
`f' ∘ e₁ = e₂ ∘ f` and `g' ∘ e₁' = e₂' ∘ g` give the commuting square of products
(`LinearMap.prodMap_comp_prodCongr_eq_of_comp_eq`), that negation commutes with every linear
map (`LinearMap.comp_neg_eq_neg_comp`), and that a composite `P ∘ L` is bijective exactly when
`L` is injective, `P` is onto, and the kernel of `P` is complementary to the range of `L`
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

/-- The `n`-th power of precomposition by an endomorphism `T` is precomposition by `T ^ n`. -/
@[simp]
theorem lcomp_pow {R S M D : Type*} [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid D]
    [Module R M] [Module R D] [Module S D] [SMulCommClass R S D] (T : Module.End R M) (n : ℕ) :
    (lcomp S D T : Module.End S (M →ₗ[R] D)) ^ n = lcomp S D (T ^ n) := by
  induction n with
  | zero => ext φ x; simp
  | succ n ih =>
    rw [pow_succ, pow_succ', Module.End.mul_eq_comp, Module.End.mul_eq_comp, ih]
    ext φ x
    simp [lcomp_apply]

/-- Commuting squares `f' ∘ e₁ = e₂ ∘ f` and `g' ∘ e₁' = e₂' ∘ g` of linear maps give the
commuting square `(f' × g') ∘ (e₁ × e₁') = (e₂ × e₂') ∘ (f × g)` of their products. -/
theorem prodMap_comp_prodCongr_eq_of_comp_eq {M' N' P P' Q Q' : Type*} [AddCommMonoid M']
    [Module R M'] [AddCommMonoid N'] [Module R N'] [AddCommMonoid P] [Module R P]
    [AddCommMonoid P'] [Module R P'] [AddCommMonoid Q] [Module R Q] [AddCommMonoid Q']
    [Module R Q'] {f : M →ₗ[R] N} {g : M' →ₗ[R] N'} {f' : P →ₗ[R] Q} {g' : P' →ₗ[R] Q'}
    {e₁ : M ≃ₗ[R] P} {e₂ : N ≃ₗ[R] Q} {e₁' : M' ≃ₗ[R] P'} {e₂' : N' ≃ₗ[R] Q'}
    (hf : f' ∘ₗ e₁.toLinearMap = e₂.toLinearMap ∘ₗ f)
    (hg : g' ∘ₗ e₁'.toLinearMap = e₂'.toLinearMap ∘ₗ g) :
    f'.prodMap g' ∘ₗ (e₁.prodCongr e₁').toLinearMap =
      (e₂.prodCongr e₂').toLinearMap ∘ₗ f.prodMap g := by
  rw [LinearEquiv.coe_prodCongr, LinearEquiv.coe_prodCongr, prodMap_comp, prodMap_comp, hf, hg]

/-- Negation of source and target commutes with a linear map: `f ∘ (-1) = (-1) ∘ f`. -/
theorem comp_neg_eq_neg_comp {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) :
    f ∘ₗ (LinearEquiv.neg R).toLinearMap = (LinearEquiv.neg R).toLinearMap ∘ₗ f := by
  ext
  simp

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
