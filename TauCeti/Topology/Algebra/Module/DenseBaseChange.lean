/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.Topology.Algebra.Module.ModuleTopology

/-!
# Density of a finite module in its scalar extensions

Let `R` be a commutative semiring and `(A i)` a family of topological `R`-algebras, not
necessarily commutative, such that the diagonal image of `R` is dense in `∏ i, A i`. Then for
every finite `R`-module `M`, the diagonal image of `M` is dense in `∏ i, A i ⊗[R] M`, where each
`A i ⊗[R] M` carries its `A i`-module topology (`DenseRange.pi_one_tmul`).

This is how approximation statements pass from a ring to its finite modules: in strong
approximation, the `S`-integers of a global field are dense in the product of the completions at a
set of places that, together with the places where they are integral, omits at least one place,
and the same then holds for every finite projective module over them, as needed to approximate
global sections of a vector bundle on an affine curve.

The proof chooses a surjection `Rⁿ → M`. The free module `Rⁿ` is dense in `∏ i, (A i)ⁿ`
coordinatewise, and the base change of the surjection is a continuous surjection
`(A i)ⁿ → A i ⊗[R] M` for the module topologies. No projectivity of `M` is needed.

## Main results

* `DenseRange.pi_one_tmul`: if `R` is dense in `∏ i, A i`, a finite `R`-module `M` is dense in
  `∏ i, A i ⊗[R] M`.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §15.
* L. Moret-Bailly, *Groupes de Picard et problèmes de Skolem II*, Ann. Sci. ÉNS 22 (1989),
  proof of Lemme 3.8, where approximation in a finite projective module is reduced to the free
  case.
-/

public section

open scoped TensorProduct

variable {R : Type*} [CommSemiring R] {ι : Type*} {A : ι → Type*}
  [∀ i, Semiring (A i)] [∀ i, Algebra R (A i)] [∀ i, TopologicalSpace (A i)]
  [∀ i, IsTopologicalSemiring (A i)]

/-- **Density of a finite module in its scalar extensions.** If `R` is dense in the product of
topological `R`-algebras `A i`, then a finite `R`-module `M` is dense in the product of its scalar
extensions `A i ⊗[R] M`, each with its `A i`-module topology. -/
theorem DenseRange.pi_one_tmul (h : DenseRange fun r : R ↦ fun i ↦ algebraMap R (A i) r)
    (M : Type*) [AddCommMonoid M] [Module R M] [Module.Finite R M]
    [∀ i, TopologicalSpace (A i ⊗[R] M)] [∀ i, IsModuleTopology (A i) (A i ⊗[R] M)] :
    DenseRange fun m : M ↦ fun i ↦ (1 : A i) ⊗ₜ[R] m := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
  -- In each factor, the base change of `π` is a continuous `A i`-linear surjection from
  -- `(A i)ⁿ` onto `A i ⊗[R] M`. We identify `(A i)ⁿ` with `A i ⊗[R] Rⁿ` through the
  -- base-changed standard basis, since `TensorProduct.piScalarRight` needs `A i` commutative.
  let Φ (i : ι) : (Fin n → A i) →ₗ[A i] A i ⊗[R] M :=
    π.baseChange (A i) ∘ₗ
      (Algebra.TensorProduct.basis (A i) (Pi.basisFun R (Fin n))).equivFun.symm.toLinearMap
  have hΦc (i : ι) : Continuous (Φ i) :=
    have := IsModuleTopology.toContinuousAdd (A i) (A i ⊗[R] M)
    IsModuleTopology.continuous_of_linearMap (Φ i)
  have hΦs (i : ι) : Function.Surjective (Φ i) :=
    (π.baseChange_surjective (A i) hπ).comp (LinearEquiv.surjective _)
  -- Assemble the factors: from `n` points of `∏ i, A i` to a point of `∏ i, A i ⊗[R] M`.
  let Ψ : (Fin n → ∀ i, A i) → ∀ i, A i ⊗[R] M := fun c i ↦ Φ i fun j ↦ c j i
  have hΨc : Continuous Ψ := continuous_pi fun i ↦
    (hΦc i).comp (continuous_pi fun j ↦ (continuous_apply i).comp (continuous_apply j))
  have hΨs : Function.Surjective Ψ := fun y ↦ by
    choose c hc using fun i ↦ hΦs i (y i)
    exact ⟨fun j i ↦ c i j, funext hc⟩
  -- The image of `Rⁿ` is dense in `(∏ i, A i)ⁿ`; its image under `Ψ` is that of `M`.
  have hdense := hΨs.denseRange.comp (DenseRange.piMap fun _ : Fin n ↦ h) hΨc
  have heq : (fun m : M ↦ fun i ↦ (1 : A i) ⊗ₜ[R] m) ∘ π =
      Ψ ∘ Pi.map fun _ : Fin n ↦ fun r : R ↦ fun i ↦ algebraMap R (A i) r := by
    funext r i
    simp only [Function.comp_apply, Pi.map_apply, Ψ, Φ, LinearMap.coe_comp,
      LinearEquiv.coe_coe]
    -- In the base-changed standard basis, `1 ⊗ₜ r` has coordinates `algebraMap R (A i) (r j)`.
    have hr : (Algebra.TensorProduct.basis (A i) (Pi.basisFun R (Fin n))).equivFun.symm
        (fun j ↦ algebraMap R (A i) (r j)) = 1 ⊗ₜ[R] r := by
      rw [LinearEquiv.symm_apply_eq]
      funext j
      simp
    rw [hr, LinearMap.baseChange_tmul]
  rw [DenseRange, ← hπ.range_comp, ← DenseRange, heq]
  exact hdense
