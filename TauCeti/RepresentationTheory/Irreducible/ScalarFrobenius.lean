/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Irreducible.ConjugatePow
import TauCeti.Algebra.Group.Semiconj

/-!
# Scalar powers of Frobenius in a spanning tame representation

Suppose Frobenius conjugates tame inertia to its `q`-th power. If the first `n` iterates of the
`q`-power map on a residual inertia eigenvalue are distinct, mixed powers of inverse Frobenius
and inertia span the `n × n` matrix algebra over the local coefficient ring. Consequently an
inverse Frobenius power is scalar exactly when the corresponding iterated `q`-power fixes the
inertia matrix.

The scalar conclusion at the rank is the one in
`New.Selmer.IsLatticeIn.span_range_eq_top_of_map_pow_eq_map_conj`, in
`grh/src/Lib/GaloisRep/Pseudocharacter/Pseudorepresentations.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean) at `72fead1`.
-/

public section

open Matrix IsLocalRing

namespace MonoidHom

/-- If `φ` conjugates `τ` to its `q`-th power under `u`, and the reduction of `u τ` has an
eigenvalue with `#n` distinct iterated `q`-powers, then `u ((φ⁻¹)^k)` is scalar exactly when
`(u τ)^(q^k) = u τ`. In particular this detects a scalar Frobenius power over the coefficient
ring itself, not just over its residue field. -/
theorem map_inv_pow_mem_range_scalar_iff {R G n : Type*} [CommRing R] [IsLocalRing R]
    [Group G] [Fintype n] [DecidableEq n] (u : G →* Matrix n n R) {τ φ : G} {q : ℕ}
    (h : u (φ * τ * φ⁻¹) = u τ ^ q) {μ : ResidueField R}
    (hμ : ((u τ).map (residue R)).charpoly.IsRoot μ)
    (hdist : Function.Injective fun i : Fin (Fintype.card n) ↦ μ ^ q ^ (i : ℕ)) (k : ℕ) :
    u (φ⁻¹ ^ k) ∈ Set.range (scalar n : R →+* Matrix n n R) ↔ u τ ^ q ^ k = u τ := by
  have hF : IsUnit (u φ⁻¹) := (Group.isUnit φ⁻¹).map u
  have hTF := semiconjBy_map_inv_of_map_conj_eq_pow h
  have hpow := hTF.pow_left_pow_pow k
  rw [map_pow]
  constructor
  · rintro ⟨c, hc⟩
    have hcomm : Commute (u φ⁻¹ ^ k) (u τ) :=
      hc ▸ (scalar_commute c (Commute.all c) (u τ))
    exact (hF.pow k).mul_left_cancel (hpow.eq.trans hcomm.eq.symm)
  · intro hperiod
    rw [hperiod] at hpow
    have hcomm : Commute (u τ) (u φ⁻¹ ^ k) := Commute.symm hpow
    have hspan := IsLocalRing.span_range_pow_mul_pow_eq_top_of_mul_eq_mul_pow
      (A := u τ) (B := u φ⁻¹) (q := q) hTF.eq.symm hF hμ hdist
    refine mem_range_scalar_of_commute_of_span_eq_top hspan ?_
    rintro ⟨a, b⟩
    exact ((Commute.self_pow (u φ⁻¹) k).pow_left (a : ℕ)).mul_left
      (hcomm.pow_left (b : ℕ))

end MonoidHom
