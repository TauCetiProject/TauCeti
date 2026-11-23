/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Foam.EquivariantRing.Basic
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain
import TauCeti.Algebra.Category.GradedModuleCat.Free.Range
import TauCeti.Algebra.Module.GradedModule.Idempotent.PID

/-!
# Homogeneous splittings and bases of idempotents over the equivariant foam ring

Because `ℤ` is a principal ideal domain and every generator of `TauCeti.EquivariantRing N` has
strictly positive degree, every degree-zero idempotent endomorphism on a finite shifted free module
over `EquivariantRing N` splits homogeneously
(`EquivariantRing.exists_homogeneous_splitting_of_idempotent`), its image admits a finite
homogeneous `EquivariantRing N`-basis (`TauCeti.exists_homogeneous_basis_range_idempotent`), and
the multiset of basis shifts is uniquely determined
(`EquivariantRing.multiset_map_eq_of_homogeneous_basis_range_idempotent`).

## Main results

* `TauCeti.EquivariantRing.exists_homogeneous_splitting_of_idempotent`: explicit homogeneous
  splitting `π ∘ₗ ι = id`, `ι ∘ₗ π = p` of a degree-zero idempotent over `EquivariantRing N`.
* `TauCeti.EquivariantRing.multiset_map_eq_of_homogeneous_basis_range_idempotent`: uniqueness of the
  multiset of basis shifts.
* `TauCeti.exists_homogeneous_basis_range_idempotent`: the image of any degree-zero idempotent on a
  finite sum of shifted copies of `EquivariantRing N` has a finite homogeneous basis.

## References

* L.-H. Robert and E. Wagner, *Symmetric Khovanov–Rozansky link homologies*, J. Éc. polytech.
  Math. 7 (2020), 573–651, Lemma 3.30.
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
    (𝒜 := grading N) (fun _ hm ↦ grading_eq_bot_of_lt_zero N hm)
    (fun _ ha ↦ grading_zero_eq_range N ▸ ha) s p hp hhom

/-- Any two finite homogeneous bases of the range of a degree-zero endomorphism on
`I → EquivariantRing N` (`[Finite I]`) have the same multiset of basis shifts. -/
theorem multiset_map_eq_of_homogeneous_basis_range_idempotent (N : ℕ) {I : Type*} [Finite I]
    (s : I → ℤ)
    (p : (I → EquivariantRing N) →ₗ[EquivariantRing N] (I → EquivariantRing N))
    (hhom : ∀ (d : ℤ) (v : I → EquivariantRing N),
      (∀ j, v j ∈ grading N (d - s j)) → ∀ j, p v j ∈ grading N (d - s j))
    {n₁ n₂ : ℕ}
    (b₁ : Module.Basis (Fin n₁) (EquivariantRing N) (LinearMap.range p)) (d₁ : Fin n₁ → ℤ)
    (hb₁ : ∀ i j, (b₁ i).val j ∈ grading N (d₁ i - s j))
    (b₂ : Module.Basis (Fin n₂) (EquivariantRing N) (LinearMap.range p)) (d₂ : Fin n₂ → ℤ)
    (hb₂ : ∀ i j, (b₂ i).val j ∈ grading N (d₂ i - s j)) :
    Multiset.map d₁ Finset.univ.val = Multiset.map d₂ Finset.univ.val :=
  GradedModuleCat.multiset_map_eq_of_homogeneous_basis_range
    (𝒜 := grading N) (fun _ hm ↦ grading_eq_bot_of_lt_zero N hm)
    (fun _ ha ↦ grading_zero_eq_range N ▸ ha) s p hhom b₁ d₁ hb₁ b₂ d₂ hb₂

end EquivariantRing

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
      (∀ j, v j ∈ EquivariantRing.grading N (d - s j)) →
      ∀ j, p v j ∈ EquivariantRing.grading N (d - s j)) :
    ∃ (n : ℕ)
      (b : Module.Basis (Fin n) (EquivariantRing N) (LinearMap.range p))
      (d : Fin n → ℤ),
      ∀ i j, (b i).val j ∈ EquivariantRing.grading N (d i - s j) :=
  exists_homogeneous_basis_range_idempotent_of_connected
    (𝒜 := EquivariantRing.grading N)
    (fun _ hm ↦ EquivariantRing.grading_eq_bot_of_lt_zero N hm)
    (fun _ ha ↦ EquivariantRing.grading_zero_eq_range N ▸ ha) s p hp hhom

end TauCeti
