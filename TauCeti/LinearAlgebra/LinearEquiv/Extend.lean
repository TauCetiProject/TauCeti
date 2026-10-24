/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Projection

/-!
# Extending injective linear maps to linear equivalences

Two injective linear maps `f : U → V` and `g : U → W` into finite-dimensional vector spaces of
the same dimension differ by a linear equivalence: there is `e : V ≃ W` with `e ∘ f = g`. Choose
complements of the ranges of `f` and `g`; they have the same dimension, so an arbitrary linear
equivalence between them, together with `g ∘ f⁻¹` on the range of `f`, assembles to `e`.

Taking for `f` the inclusion of a coordinate subspace, this is the linear algebra behind the normal
form of an immersion: an injective derivative extends to an invertible one.
-/

public section

namespace LinearMap

variable {K U V W : Type*} [DivisionRing K] [AddCommGroup U] [Module K U] [AddCommGroup V]
  [Module K V] [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]

/-- Two injective linear maps `f : U → V` and `g : U → W` into finite-dimensional vector spaces of
the same dimension differ by a linear equivalence `e : V ≃ W`, in the sense that `e ∘ f = g`. -/
theorem exists_linearEquiv_comp_eq (f : U →ₗ[K] V) (g : U →ₗ[K] W) (hf : Function.Injective f)
    (hg : Function.Injective g) (h : Module.finrank K V = Module.finrank K W) :
    ∃ e : V ≃ₗ[K] W, e.toLinearMap ∘ₗ f = g := by
  have : FiniteDimensional K U := Module.Finite.of_injective f hf
  obtain ⟨C, hC⟩ := (range f).exists_isCompl
  obtain ⟨D, hD⟩ := (range g).exists_isCompl
  have hCD : Module.finrank K C = Module.finrank K D := by
    have := Submodule.finrank_add_eq_of_isCompl hC
    have := Submodule.finrank_add_eq_of_isCompl hD
    rw [finrank_range_of_inj hf] at *
    rw [finrank_range_of_inj hg] at *
    omega
  -- On the range of `f` the equivalence is `g ∘ f⁻¹`; on the complements it is arbitrary.
  let a : range f ≃ₗ[K] range g :=
    (LinearEquiv.ofInjective f hf).symm.trans (LinearEquiv.ofInjective g hg)
  refine ⟨(Submodule.prodEquivOfIsCompl _ _ hC).symm.trans
    ((a.prodCongr (LinearEquiv.ofFinrankEq C D hCD)).trans
      (Submodule.prodEquivOfIsCompl _ _ hD)), ?_⟩
  ext u
  have hu : (Submodule.prodEquivOfIsCompl _ _ hC).symm (f u) = (⟨f u, mem_range_self f u⟩, 0) :=
    Submodule.prodEquivOfIsCompl_symm_apply_left _ _ hC (⟨f u, mem_range_self f u⟩ : range f)
  have ha : a ⟨f u, mem_range_self f u⟩ = (⟨g u, mem_range_self g u⟩ : range g) := by
    have : (LinearEquiv.ofInjective f hf).symm ⟨f u, mem_range_self f u⟩ = u :=
      (LinearEquiv.ofInjective f hf).symm_apply_eq.2 rfl
    ext
    simp [a, this]
  simp [hu, ha]

end LinearMap
