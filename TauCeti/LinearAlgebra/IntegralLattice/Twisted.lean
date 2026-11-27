/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import TauCeti.NumberTheory.Height.FamilyOverPairs.Basic

/-!
# Twisted lattices

In a twisted lattice, integrality is tested after applying every twist allowed at the given
prime. At the archimedean places only the distinguished twist is used: a rational Gram matrix
allows one to measure its coordinates after a field automorphism of `ℂ`. The mixed pairing at
conjugate prime-adic embeddings is what allows separate integral changes of basis in the two
arguments of a Gram pairing.

The construction follows `New.TwistedLattice` in `New/Reduction/Lattices/TwistedLattice.lean`
of [grh-lean](https://github.com/lsernau/grh-lean) at `72fead102f663d5c7a407964a13dc0cf9d977207`.
-/

public section

open Complex Matrix
open scoped ComplexOrder InnerProductSpace

namespace TauCeti

/-- A family of twists out of `V`, with local integral submodules for allowed twists and a
rational coordinate pairing for the distinguished twist `1`. -/
structure TwistedLattice {T : Type*} [One T] (S : T → Type*) (C V : Type*) [Fintype C]
    [∀ t, NormedAddCommGroup (S t)] [∀ t, InnerProductSpace ℂ (S t)]
    [AddCommMonoid V] [Module ℂ V] where
  /-- The linear map for each twist. -/
  lift (t : T) : V →ₗ[ℂ] S t
  /-- The twists allowed at each rational prime. -/
  allowed : T → Nat.Primes → Prop
  /-- Integral vectors in the target of a twist, defined only where the twist is allowed. -/
  integral (t : T) (ι : PrimePadicIso) : allowed t ι.primeIndex → Submodule ι.integers (S t)
  /-- Pairing vectors integral at conjugate embeddings gives an integral scalar. -/
  norm_iso_inner_le_one (t : T) (ι : PrimePadicIso) (ht : allowed t ι.primeIndex)
      {x y : S t} (hx : x ∈ integral t ι.conj (by simpa using ht))
      (hy : y ∈ integral t ι ht) :
      ‖ι.iso ⟪x, y⟫_ℂ‖ ≤ 1
  /-- Coordinates of vectors in the target of the distinguished twist. -/
  coord : S 1 →ₗ[ℂ] (C → ℂ)
  /-- The rational Gram matrix representing the inner product in these coordinates. -/
  gram : Matrix C C ℚ
  /-- The coordinate pairing is positive definite on the ambient complex coordinate space. -/
  posDef_gram : (gram.map (algebraMap ℚ ℂ)).PosDef
  /-- The coordinate pairing agrees with the inner product on the distinguished target. -/
  inner_eq_dotProduct (x y : S 1) :
      ⟪x, y⟫_ℂ = star (coord x) ⬝ᵥ ((gram.map (algebraMap ℚ ℂ)) *ᵥ coord y)

namespace TwistedLattice

variable {T C V : Type*} [One T] [Fintype C] [AddCommMonoid V] [Module ℂ V]
variable {S : T → Type*} [∀ t, NormedAddCommGroup (S t)] [∀ t, InnerProductSpace ℂ (S t)]

/-- The lifts, allowed twists, integral submodules at allowed twists, and rational coordinates
with their Gram matrix determine the twisted lattice. -/
@[ext] theorem ext {L L' : TwistedLattice S C V}
    (hlift : ∀ t, L.lift t = L'.lift t) (hallowed : L.allowed = L'.allowed)
    (hintegral : ∀ t ι (ht : L.allowed t ι.primeIndex) (ht' : L'.allowed t ι.primeIndex),
      L.integral t ι ht = L'.integral t ι ht')
    (hcoord : L.coord = L'.coord) (hgram : L.gram = L'.gram) : L = L' := by
  cases L
  cases L'
  cases hallowed
  cases funext hlift
  cases funext fun t ↦ funext fun ι ↦ funext fun ht ↦ hintegral t ι ht ht
  cases hcoord
  cases hgram
  rfl

variable (L : TwistedLattice S C V)

/-- The reference submodule of vectors integral at `ι`: the intersection of the preimages of
all integral submodules for twists allowed at that prime. -/
noncomputable def integralVectors (ι : PrimePadicIso) : Submodule ι.integers V :=
  ⨅ (t : T) (ht : L.allowed t ι.primeIndex),
    (L.integral t ι ht).comap ((L.lift t).restrictScalars ι.integers)

/-- A vector is integral exactly when its lift is integral at every allowed twist. -/
@[simp] theorem mem_integralVectors_iff (ι : PrimePadicIso) {x : V} :
    x ∈ L.integralVectors ι ↔
      ∀ t (ht : L.allowed t ι.primeIndex), L.lift t x ∈ L.integral t ι ht := by
  simp only [integralVectors, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply]

/-- The integral vectors form the largest submodule whose images in all allowed targets are
integral. -/
theorem le_integralVectors_iff (ι : PrimePadicIso) (M : Submodule ι.integers V) :
    M ≤ L.integralVectors ι ↔ ∀ t (ht : L.allowed t ι.primeIndex),
      M.map ((L.lift t).restrictScalars ι.integers) ≤ L.integral t ι ht := by
  simp only [integralVectors, le_iInf_iff, Submodule.map_le_iff_le_comap]

/-- Integral vectors at conjugate embeddings have integral pairing after any allowed lift. -/
theorem norm_iso_inner_lift_le_one (ι : PrimePadicIso) {t : T} (ht : L.allowed t ι.primeIndex)
    {x y : V} (hx : x ∈ L.integralVectors ι.conj) (hy : y ∈ L.integralVectors ι) :
    ‖ι.iso ⟪L.lift t x, L.lift t y⟫_ℂ‖ ≤ 1 :=
  L.norm_iso_inner_le_one t ι ht ((L.mem_integralVectors_iff ι.conj).mp hx t (by simpa using ht))
    ((L.mem_integralVectors_iff ι).mp hy t ht)

/-- The squared norm obtained by applying `σ` to the coordinates of the distinguished lift. -/
noncomputable def normSqAt (σ : ℂ ≃+* ℂ) (x : V) : ℝ :=
  let v := fun i ↦ σ (L.coord (L.lift 1 x) i)
  (star v ⬝ᵥ ((L.gram.map (algebraMap ℚ ℂ)) *ᵥ v)).re

/-- The conjugated squared norm is computed in the same rational Gram matrix. -/
theorem normSqAt_def (σ : ℂ ≃+* ℂ) (x : V) :
    L.normSqAt σ x =
      (star (fun i ↦ σ (L.coord (L.lift 1 x) i)) ⬝ᵥ
        ((L.gram.map (algebraMap ℚ ℂ)) *ᵥ fun i ↦ σ (L.coord (L.lift 1 x) i))).re := (rfl)

/-- The conjugated squared norm is nonnegative at every automorphism. -/
theorem normSqAt_nonneg (σ : ℂ ≃+* ℂ) (x : V) : 0 ≤ L.normSqAt σ x := by
  rw [L.normSqAt_def]
  exact (Complex.nonneg_iff.mp (L.posDef_gram.posSemidef.dotProduct_mulVec_nonneg _)).1

/-- At the identity automorphism the conjugated norm is the original squared norm of the
distinguished lift. -/
@[simp] theorem normSqAt_refl (x : V) : L.normSqAt (RingEquiv.refl ℂ) x = ‖L.lift 1 x‖ ^ 2 := by
  rw [L.normSqAt_def]
  simp only [RingEquiv.refl_apply, ← L.inner_eq_dotProduct]
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (L.lift 1 x)

end TwistedLattice

end TauCeti
