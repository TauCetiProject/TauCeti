/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.LatticeOverPairs.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.LinearAlgebra.Pi

/-!
# Twisted lattices from locally integral Gram matrices

When each twist has coordinates in which its Gram matrix is integral at the primes that allow
it, testing integrality of the coordinates suffices to construct a twisted lattice. The two
vectors in the pairing are tested at different embeddings: the first at the conjugate embedding,
so that conjugation of its coordinates puts them in the same local ring as the second vector.

For class-sum inner products without stabilizer denominators, the coordinate matrix is the block
diagonal matrix of the coefficient pairings. This is the integral pairing used by
`New.Data.targetLattice` in `grh/src/New/Reduction/IntegralTargetForms.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean) at `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open Matrix
open scoped ComplexOrder InnerProductSpace

namespace TauCeti.TwistedLattice

variable {T : Type*} [One T] {C S : T → Type*} {V : Type*} [∀ t, Fintype (C t)]
variable [∀ t, NormedAddCommGroup (S t)] [∀ t, InnerProductSpace ℂ (S t)]
variable [AddCommMonoid V] [Module ℂ V]

/-- Construct a twisted lattice by testing each lift in its own coordinates. The Gram entries
need only be integral at embeddings over primes at which that twist is allowed. The matrix of
the distinguished twist must be positive definite on its whole coordinate space. -/
noncomputable def ofIntegralGram (lift : ∀ t, V →ₗ[ℂ] S t) (allowed : T → Nat.Primes → Prop)
    (coord : ∀ t, S t →ₗ[ℂ] (C t → ℂ)) (G : ∀ t, Matrix (C t) (C t) ℚ)
    (hpos : ((G 1).map (algebraMap ℚ ℂ)).PosDef)
    (hinner : ∀ t (x y : S t),
      ⟪x, y⟫_ℂ = star (coord t x) ⬝ᵥ ((G t).map (algebraMap ℚ ℂ) *ᵥ coord t y))
    (hG : ∀ t (ι : PrimePadicIso), allowed t ι.primeIndex →
      ∀ i j, algebraMap ℚ ℂ (G t i j) ∈ ι.integers) : TwistedLattice S (C 1) V where
  lift := lift
  allowed := allowed
  integral t ι _ := (Submodule.pi Set.univ
    (fun _ ↦ (⊥ : Subalgebra ι.integers ℂ).toSubmodule)).comap
      ((coord t).restrictScalars ι.integers)
  norm_iso_inner_le_one t ι ht {x y} hx hy := by
    have hcoord (κ : PrimePadicIso) {z : S t}
        (hz : ((coord t).restrictScalars κ.integers) z ∈ Submodule.pi Set.univ
          (fun _ ↦ (⊥ : Subalgebra κ.integers ℂ).toSubmodule)) (i : C t) :
        coord t z i ∈ κ.integers := by
      simpa only [Subalgebra.mem_toSubmodule, Algebra.mem_bot,
        Algebra.coe_algebraMap_ofSubsemiring, Subtype.range_coe_subtype,
        Set.mem_ofPred_eq, LinearMap.restrictScalars_apply] using Submodule.mem_pi.mp hz i trivial
    rw [← PrimePadicIso.mem_integers, hinner t, dotProduct]
    refine Subring.sum_mem _ fun i _ ↦ mul_mem (PrimePadicIso.mem_integers_conj.mp
      (hcoord ι.conj (Submodule.mem_comap.mp hx) i)) ?_
    rw [mulVec, dotProduct]
    exact Subring.sum_mem _ fun j _ ↦ mul_mem (hG t ι ht i j)
      (hcoord ι (Submodule.mem_comap.mp hy) j)
  coord := coord 1
  gram := G 1
  posDef_gram := hpos
  inner_eq_dotProduct := hinner 1

variable (lift : ∀ t, V →ₗ[ℂ] S t) (allowed : T → Nat.Primes → Prop)
variable (coord : ∀ t, S t →ₗ[ℂ] (C t → ℂ)) (G : ∀ t, Matrix (C t) (C t) ℚ)
variable (hpos : ((G 1).map (algebraMap ℚ ℂ)).PosDef)
variable (hinner : ∀ t (x y : S t),
  ⟪x, y⟫_ℂ = star (coord t x) ⬝ᵥ ((G t).map (algebraMap ℚ ℂ) *ᵥ coord t y))
variable (hG : ∀ t (ι : PrimePadicIso), allowed t ι.primeIndex →
  ∀ i j, algebraMap ℚ ℂ (G t i j) ∈ ι.integers)

/-- The lift maps are the supplied maps, independently of the Gram data. -/
@[simp] theorem ofIntegralGram_lift :
    (ofIntegralGram lift allowed coord G hpos hinner hG).lift = lift := (rfl)

/-- The construction preserves the given rule for allowed twists. -/
@[simp] theorem ofIntegralGram_allowed :
    (ofIntegralGram lift allowed coord G hpos hinner hG).allowed = allowed := (rfl)

/-- The archimedean coordinates are those of the distinguished twist. -/
@[simp] theorem ofIntegralGram_coord :
    (ofIntegralGram lift allowed coord G hpos hinner hG).coord = coord 1 := (rfl)

/-- The archimedean Gram matrix is that of the distinguished twist. -/
@[simp] theorem ofIntegralGram_gram :
    (ofIntegralGram lift allowed coord G hpos hinner hG).gram = G 1 := (rfl)

/-- An element of a twist target is integral exactly when all its coordinates are integral at
that embedding. -/
@[simp] theorem mem_integral_ofIntegralGram_iff (t : T) (ι : PrimePadicIso)
    (ht : (ofIntegralGram lift allowed coord G hpos hinner hG).allowed t ι.primeIndex) {x : S t} :
    x ∈ (ofIntegralGram lift allowed coord G hpos hinner hG).integral t ι ht ↔
      ∀ i, coord t x i ∈ ι.integers := by
  simp only [ofIntegralGram, Submodule.mem_comap, Submodule.mem_pi, Set.mem_univ, true_implies,
    LinearMap.restrictScalars_apply, Subalgebra.mem_toSubmodule, Algebra.mem_bot,
    Algebra.coe_algebraMap_ofSubsemiring, Subtype.range_coe_subtype, Set.mem_ofPred_eq]

end TauCeti.TwistedLattice
