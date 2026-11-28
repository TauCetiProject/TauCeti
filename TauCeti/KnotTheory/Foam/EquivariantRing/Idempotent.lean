/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Foam.EquivariantRing.Basic
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain
import TauCeti.Algebra.Category.GradedModuleCat.Retract.Idempotent

/-!
# Homogeneous splittings and bases of idempotents over the equivariant foam ring

Because `ℤ` is a principal ideal domain and every generator of `TauCeti.EquivariantRing N` has
strictly positive degree, every degree-zero idempotent endomorphism on a finite shifted free module
over `EquivariantRing N` splits homogeneously
(`EquivariantRing.exists_homogeneous_splitting_of_idempotent`), and its image admits a finite
homogeneous `EquivariantRing N`-basis
(`EquivariantRing.exists_homogeneous_basis_range_idempotent`).

## Main results

* `TauCeti.EquivariantRing.exists_homogeneous_splitting_of_idempotent`: explicit homogeneous
  splitting `π ∘ₗ ι = id`, `ι ∘ₗ π = p` of a degree-zero idempotent over `EquivariantRing N`.
* `TauCeti.EquivariantRing.exists_homogeneous_basis_range_idempotent`: the image of any degree-zero
  idempotent on a finite sum of shifted copies of `EquivariantRing N` has a finite homogeneous
  basis.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, and T. Y. Lam,
  *Serre's Problem on Projective Modules*, Chapter II, §4, for homogeneous bases of graded
  retracts and idempotent splittings.
* Application context (`gl(N)` foams): L.-H. Robert and E. Wagner, *Symmetric Khovanov–Rozansky
  link homologies*, J. Éc. polytech. Math. 7 (2020), 573–651 (`arXiv:1801.02244`), and
  M. Khovanov and L.-H. Robert, *Foam evaluation and Kronheimer–Mrowka theories*, Adv. Math. 376
  (2021), 107433 (`arXiv:1808.09662`).
-/

public section

namespace TauCeti

namespace EquivariantRing

/-- Any degree-zero idempotent on a finite shifted free module `I → EquivariantRing N` splits
homogeneously through some `Fin n → EquivariantRing N` via maps `ι` and `π` satisfying
`π ∘ₗ ι = id` and `ι ∘ₗ π = p`. -/
theorem exists_homogeneous_splitting_of_idempotent (N : ℕ) {I : Type*} [Finite I] (s : I → ℤ)
    (p : (I → EquivariantRing N) →ₗ[EquivariantRing N] (I → EquivariantRing N))
    (hp : p.comp p = p)
    (hhom : ∀ (d : ℤ) (v : I → EquivariantRing N),
      (∀ j, v j ∈ grading N (d - s j)) → ∀ j, p v j ∈ grading N (d - s j)) :
    ∃ (n : ℕ) (d : Fin n → ℤ)
      (ι : (Fin n → EquivariantRing N) →ₗ[EquivariantRing N] (I → EquivariantRing N))
      (π : (I → EquivariantRing N) →ₗ[EquivariantRing N] (Fin n → EquivariantRing N)),
      π.comp ι = LinearMap.id ∧
      ι.comp π = p ∧
      (∀ (q : ℤ) (u : Fin n → EquivariantRing N),
        (∀ i, u i ∈ grading N (q - d i)) → ∀ j, ι u j ∈ grading N (q - s j)) ∧
      (∀ (q : ℤ) (v : I → EquivariantRing N),
        (∀ j, v j ∈ grading N (q - s j)) → ∀ i, π v i ∈ grading N (q - d i)) :=
  exists_homogeneous_splitting_of_idempotent_of_connected
    (𝒜 := grading N) (fun _ ↦ grading_eq_bot_of_lt_zero N)
    (fun _ hx ↦ grading_zero_eq_range N ▸ hx) s p hp hhom

/-- **Integral homogeneous basis of an idempotent image over `EquivariantRing N`.**
Every degree-zero idempotent `EquivariantRing N`-linear endomorphism `p` on a finite sum of shifted
copies of `EquivariantRing N` (where the `j`th summand has shift `s j`) has a finite
`EquivariantRing N`-basis `b` of `LinearMap.range p` consisting of homogeneous vectors of degrees
`d i`, meaning `(b i).val j ∈ EquivariantRing.grading N (d i - s j)`. -/
theorem exists_homogeneous_basis_range_idempotent (N m : ℕ) (s : Fin m → ℤ)
    (p : (Fin m → EquivariantRing N) →ₗ[EquivariantRing N]
      (Fin m → EquivariantRing N))
    (hp : p.comp p = p)
    (hhom : ∀ (d : ℤ) (v : Fin m → EquivariantRing N),
      (∀ j, v j ∈ grading N (d - s j)) →
      ∀ j, p v j ∈ grading N (d - s j)) :
    ∃ (n : ℕ)
      (b : Module.Basis (Fin n) (EquivariantRing N) (LinearMap.range p))
      (d : Fin n → ℤ),
      ∀ i j, (b i).val j ∈ grading N (d i - s j) :=
  exists_homogeneous_basis_range_idempotent_of_connected
    (𝒜 := grading N)
    (fun _ ↦ grading_eq_bot_of_lt_zero N)
    (fun _ hx ↦ grading_zero_eq_range N ▸ hx) s p hp hhom

end EquivariantRing

end TauCeti
