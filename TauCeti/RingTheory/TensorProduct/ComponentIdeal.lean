/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Ideal.Span
public import TauCeti.LinearAlgebra.TensorProduct.Basis

/-!
# The ideal cut out by the vanishing of a tensor

Let `A` be a commutative semiring, `W` a commutative `A`-algebra and `M` an `A`-module. An element
`e : W ⊗[A] M` is a family of elements of `M` parametrised by `Spec W`, and its vanishing locus is
cut out by the ideal `TensorProduct.componentIdeal e` of `W`, spanned by the components
`(W ⊗ φ) e` of `e` against all linear functionals `φ : M →ₗ[A] A`. When `M` is projective, an
`A`-algebra homomorphism `g : W →ₐ[A] T` kills `e`, in the sense that `(g ⊗ M) e = 0`, exactly when
`g` kills this ideal; when `M` is moreover finite, the ideal is finitely generated.

Geometrically: the locus where a section of a finite locally free module vanishes is a closed
subscheme, of finite presentation over the base. This is used to cut out closed conditions, such
as compatibility with comultiplication, inside a scheme representing a functor of points.

## Main definitions

* `TensorProduct.componentIdeal e`: the ideal of `W` spanned by the components of
  `e : W ⊗[A] M` against the linear functionals on `M`.

## Main results

* `TensorProduct.componentIdeal_le_ker_iff`: for `M` projective, `g : W →ₐ[A] T` kills
  `componentIdeal e` if and only if `(g ⊗ M) e = 0`.
* `TensorProduct.componentIdeal_eq_bot_iff`: for `M` projective, `componentIdeal e = ⊥` if and only
  if `e = 0`.
* `TensorProduct.componentIdeal_fg`: for `M` finite and projective, `componentIdeal e` is finitely
  generated.
-/

public section

open scoped TensorProduct

namespace TensorProduct

variable {A W T M : Type*} [CommSemiring A] [CommSemiring W] [Algebra A W] [CommSemiring T]
  [Algebra A T] [AddCommMonoid M] [Module A M]

/-- The ideal of `W` spanned by the components `(W ⊗ φ) e` of `e : W ⊗[A] M` against all linear
functionals `φ : M →ₗ[A] A`. When `M` is projective it cuts out the vanishing locus of `e`, see
`TensorProduct.componentIdeal_le_ker_iff`. -/
def componentIdeal (e : W ⊗[A] M) : Ideal W :=
  Ideal.span (Set.range fun φ : Module.Dual A M ↦ φ.tensorComponent e)

/-- The component of `e` against `φ` lies in `componentIdeal e`. -/
theorem tensorComponent_mem_componentIdeal (e : W ⊗[A] M) (φ : Module.Dual A M) :
    φ.tensorComponent e ∈ componentIdeal e :=
  Ideal.subset_span ⟨φ, rfl⟩

/-- An ideal contains `componentIdeal e` exactly when it contains every component of `e`. -/
theorem componentIdeal_le_iff {e : W ⊗[A] M} {I : Ideal W} :
    componentIdeal e ≤ I ↔ ∀ φ : Module.Dual A M, φ.tensorComponent e ∈ I := by
  simp [componentIdeal, Ideal.span_le, Set.range_subset_iff]

/-- **The vanishing locus of a tensor.** For a projective `A`-module `M`, an `A`-algebra
homomorphism `g : W →ₐ[A] T` kills `componentIdeal e` if and only if it kills `e`, that is,
`(g ⊗ M) e = 0` in `T ⊗[A] M`. -/
theorem componentIdeal_le_ker_iff [Module.Projective A M] (e : W ⊗[A] M) (g : W →ₐ[A] T) :
    componentIdeal e ≤ RingHom.ker g ↔ g.toLinearMap.rTensor M e = 0 := by
  rw [componentIdeal_le_iff]
  -- the component of `(g ⊗ M) e` against `φ` is the image under `g` of the component of `e`
  have h (φ : Module.Dual A M) :
      φ.tensorComponent (g.toLinearMap.rTensor M e) = g (φ.tensorComponent e) := by
    rw [LinearMap.rTensor_def, LinearMap.tensorComponent_map, LinearMap.comp_id,
      AlgHom.toLinearMap_apply]
  refine ⟨fun hg ↦ tensor_eq_of_forall_tensorComponent_eq fun φ ↦ ?_, fun hg φ ↦ ?_⟩
  · rw [h, map_zero]
    exact hg φ
  · rw [RingHom.mem_ker, ← AlgHom.coe_toRingHom, RingHom.coe_coe, ← h, hg, map_zero]

/-- For a projective `A`-module `M`, `componentIdeal e` vanishes if and only if `e` does. -/
@[simp]
theorem componentIdeal_eq_bot_iff [Module.Projective A M] {e : W ⊗[A] M} :
    componentIdeal e = ⊥ ↔ e = 0 := by
  refine ⟨fun h ↦ tensor_eq_of_forall_tensorComponent_eq fun φ ↦ ?_, fun h ↦ ?_⟩
  · simpa [h] using tensorComponent_mem_componentIdeal e φ
  · simp [componentIdeal, h]

/-- For a finite projective `A`-module `M`, `componentIdeal e` is finitely generated: it is spanned
by the components of `e` against finitely many functionals generating `Module.Dual A M`. -/
theorem componentIdeal_fg [Module.Finite A M] [Module.Projective A M] (e : W ⊗[A] M) :
    (componentIdeal e).FG := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := Module.Dual A M)
  refine ⟨s.image fun φ ↦ φ.tensorComponent e, le_antisymm ?_ ?_⟩
  · rw [Finset.coe_image, Ideal.span_le]
    rintro _ ⟨φ, -, rfl⟩
    exact tensorComponent_mem_componentIdeal e φ
  · rw [componentIdeal_le_iff]
    intro φ
    -- the components of `e` depend `A`-linearly on the functional
    have hφ : φ ∈ Submodule.span A (s : Set (Module.Dual A M)) := hs ▸ Submodule.mem_top
    induction hφ using Submodule.span_induction with
    | mem ψ hψ => exact Ideal.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hψ))
    | zero => simp
    | add ψ χ _ _ hψ hχ =>
      simpa [LinearMap.tensorComponent_def, LinearMap.lTensor_add] using add_mem hψ hχ
    | smul a ψ _ hψ =>
      simpa [LinearMap.tensorComponent_def, LinearMap.lTensor_smul] using
        Submodule.smul_of_tower_mem _ a hψ

end TensorProduct
