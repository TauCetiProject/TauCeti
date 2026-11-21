/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.UpperBound.Lattice
public import TauCeti.Algebra.MvPolynomial.Laurent.Subalgebra

/-!
# Cluster upper bounds of Laurent subalgebras

Given a family of initial coordinates `x : I → F` in a division `C`-algebra `F` and a family of
adjacent coordinate tuples `adjacent : K → I → F`, the one-step *upper bound*
`TauCeti.upperBound C x adjacent` is the intersection of the initial Laurent subalgebra
`TauCeti.laurentSubalgebra C x` with the Laurent subalgebras of all adjacent tuples. This
specializes the lattice-valued `TauCeti.Mutation.upperBound` to `Subalgebra C F`.

Defining `upperBound` directly on `I → F` over any division semiring avoids bundling unit proofs at
each mutation step and accommodates noncommutative division algebras as well as degenerate
specialization coordinates.

## Main definitions

* `TauCeti.upperBound`: the intersection
  `laurentSubalgebra C x ⊓ ⨅ k, laurentSubalgebra C (adjacent k)`.

## Main results

* `TauCeti.Mutation.upperBound_laurentSubalgebra`: compatibility with `TauCeti.Mutation.upperBound`.
* `TauCeti.le_upperBound_iff`, `TauCeti.mem_upperBound_iff`,
  `TauCeti.upperBound_le_laurentSubalgebra`, and `TauCeti.upperBound_le_laurentSubalgebra_adjacent`:
  universal-property and membership characterization of `upperBound`.
* `TauCeti.map_upperBound_of_injective`: transport along injective `C`-algebra homomorphisms of
  division semirings.

## References

* A. Berenstein, S. Fomin, and A. Zelevinsky, *Cluster algebras III: Upper bounds and double Bruhat
  cells*, Duke Math. J. 126 (2005), 1–52, §1.
* A. Berenstein and A. Zelevinsky, *Quantum cluster algebras*, Adv. Math. 195 (2005), 405–455, §5.
-/

public section

namespace TauCeti

section UpperBound

variable (C : Type*) {I K F : Type*} [CommSemiring C] [DivisionSemiring F] [Algebra C F]

/-- The one-step cluster upper bound over `C`: the intersection of the Laurent subalgebra of the
initial coordinates `x` with the Laurent subalgebras of all adjacent coordinate tuples. -/
def upperBound (x : I → F) (adjacent : K → I → F) : Subalgebra C F :=
  laurentSubalgebra C x ⊓ ⨅ k, laurentSubalgebra C (adjacent k)

/-- Unfolds `TauCeti.upperBound`. -/
theorem upperBound_def (x : I → F) (adjacent : K → I → F) :
    upperBound C x adjacent = laurentSubalgebra C x ⊓ ⨅ k, laurentSubalgebra C (adjacent k) :=
  (rfl)

/-- `TauCeti.upperBound` is `TauCeti.Mutation.upperBound` specialized to the chart map sending a
state to the Laurent subalgebra of its coordinates. -/
theorem Mutation.upperBound_laurentSubalgebra {V : Type*} (μ : K → V → V) (coord : V → I → F)
    (s : V) :
    Mutation.upperBound μ (fun t ↦ laurentSubalgebra C (coord t)) s =
      TauCeti.upperBound C (coord s) (fun k ↦ coord (μ k s)) := by
  rw [Mutation.upperBound_def, TauCeti.upperBound_def]

/-- A `C`-subalgebra lies in `upperBound C x adjacent` if and only if it lies in the initial
Laurent subalgebra and in every adjacent Laurent subalgebra. -/
@[simp]
theorem le_upperBound_iff {x : I → F} {adjacent : K → I → F} {S : Subalgebra C F} :
    S ≤ upperBound C x adjacent ↔
      S ≤ laurentSubalgebra C x ∧ ∀ k, S ≤ laurentSubalgebra C (adjacent k) := by
  simp [upperBound_def]

/-- An element of `F` belongs to `upperBound C x adjacent` if and only if it belongs to the initial
Laurent subalgebra and to every adjacent Laurent subalgebra. -/
@[simp]
theorem mem_upperBound_iff {x : I → F} {adjacent : K → I → F} {z : F} :
    z ∈ upperBound C x adjacent ↔
      z ∈ laurentSubalgebra C x ∧ ∀ k, z ∈ laurentSubalgebra C (adjacent k) := by
  simp [upperBound_def, Algebra.mem_iInf]

/-- The upper bound is contained in the initial Laurent subalgebra. -/
theorem upperBound_le_laurentSubalgebra (x : I → F) (adjacent : K → I → F) :
    upperBound C x adjacent ≤ laurentSubalgebra C x :=
  inf_le_left

/-- The upper bound is contained in each adjacent Laurent subalgebra. -/
theorem upperBound_le_laurentSubalgebra_adjacent (x : I → F) (adjacent : K → I → F) (k : K) :
    upperBound C x adjacent ≤ laurentSubalgebra C (adjacent k) :=
  inf_le_right.trans (iInf_le _ k)

/-- With no mutable directions, the upper bound is the initial Laurent subalgebra. -/
@[simp]
theorem upperBound_of_isEmpty [IsEmpty K] (x : I → F) (adjacent : K → I → F) :
    upperBound C x adjacent = laurentSubalgebra C x := by
  simp [upperBound_def]

end UpperBound

/-- An injective `C`-algebra homomorphism between division semirings maps the upper bound onto the
upper bound of the pushed-forward coordinates. -/
theorem map_upperBound_of_injective {C I K F G : Type*} [CommSemiring C] [DivisionSemiring F]
    [Algebra C F] [DivisionSemiring G] [Algebra C G] {φ : F →ₐ[C] G} (hφ : Function.Injective φ)
    (x : I → F) (adjacent : K → I → F) :
    (upperBound C x adjacent).map φ = upperBound C (φ ∘ x) (fun k ↦ φ ∘ adjacent k) := by
  ext y
  rw [Subalgebra.mem_map, mem_upperBound_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [mem_upperBound_iff] at hz
    refine ⟨?_, fun k ↦ ?_⟩
    · rw [← map_laurentSubalgebra]
      exact ⟨z, hz.1, rfl⟩
    · rw [← map_laurentSubalgebra]
      exact ⟨z, hz.2 k, rfl⟩
  · rintro ⟨hy₀, hy⟩
    rw [← map_laurentSubalgebra] at hy₀
    obtain ⟨z, hz₀, rfl⟩ := hy₀
    refine ⟨z, (mem_upperBound_iff C).mpr ⟨hz₀, fun k ↦ ?_⟩, rfl⟩
    have hzk := hy k
    rw [← map_laurentSubalgebra] at hzk
    obtain ⟨z', hz', hzz'⟩ := hzk
    exact hφ hzz' ▸ hz'

end TauCeti
