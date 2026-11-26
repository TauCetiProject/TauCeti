/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Eigenspace.ConjugatePow
public import TauCeti.LinearAlgebra.Matrix.Spanning
public import TauCeti.RepresentationTheory.Irreducible
import TauCeti.Algebra.Group.Semiconj

/-!
# Irreducibility from an element conjugate to a power of itself

Let `ρ` be a representation of a group `G`, and let `τ, φ ∈ G` satisfy `ρ (φ τ φ⁻¹) = ρ τ ^ q`.
If `ρ τ` has an eigenvalue `μ` whose `q`-power orbit `μ, μ ^ q, μ ^ q ^ 2, …` has the maximal
length `dim V` (the `μ ^ q ^ i`, `i < dim V`, are pairwise distinct), then the image of `ρ` spans
`End V`, so `ρ` is absolutely irreducible. The eigenvalues of `ρ τ` are then exactly this orbit,
permuted cyclically by conjugation with `φ`, and no proper nonzero subspace is stable under both.

This is the criterion of residual irreducibility for Galois representations in which `τ` is a
generator of tame inertia and `φ` a Frobenius element at an auxiliary place, where
`φ τ φ⁻¹ = τ ^ q` with `q` the order of the residue field. Its form over a local coefficient ring
`R` is stronger: for `u : G →* M_n(R)` with `u (φ τ φ⁻¹) = u τ ^ q` and an eigenvalue `μ` of the
reduction of `u τ` with `n` pairwise distinct powers `μ ^ q ^ i` in the residue field, the image of
`u` spans `M_n(R)` itself, by Nakayama's lemma. Consequently, for `n` nonempty, the reduction of `u`
along any ring homomorphism to a field is absolutely irreducible
(`MonoidHom.isIrreducible_map_of_span_range_eq_top`).

The hypothesis on `μ` holds when the characteristic polynomial of `ρ τ` is the product of `X - x`
over the roots `x` of a polynomial over `𝔽_q` that is irreducible of degree `dim V`: these roots
form one orbit of `x ↦ x ^ q` of length `dim V`.

## Main results

* `Representation.span_range_eq_top_of_map_conj_eq_pow`: over a field, the image of `ρ` spans
  `End V`.
* `Representation.isIrreducible_of_map_conj_eq_pow`: so `ρ` is irreducible.
* `IsLocalRing.span_range_pow_mul_pow_eq_top_of_mul_eq_mul_pow`: over a local ring, if
  `A * B = B * A ^ q` with `B` invertible and the reduction of `A` has an eigenvalue with `n`
  distinct powers `μ ^ q ^ i`, the `B ^ a * A ^ b`, `a, b < n`, span `M_n(R)`.
* `MonoidHom.span_range_eq_top_of_map_conj_eq_pow`: over a local ring, the image of
  `u : G →* M_n(R)` spans `M_n(R)`.

## Provenance

Adapted from `New.Selmer.IsLatticeIn.span_range_eq_top_of_map_pow_eq_map_conj` in
`src/Lib/GaloisRep/Pseudocharacter/Pseudorepresentations.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), which states
the criterion for an `O`-lattice in an `ℓ`-adic representation with coefficients in a finite
extension `O` of `ℤ_ℓ`; here the coefficients are an arbitrary local ring. grh-lean calls the
spanning statement "a case of Burnside's theorem, lifted to `O` by Nakayama's lemma". There the
lift from the residue field is a determinant computation in a basis of matrix units; here it is
`IsLocalRing.span_range_eq_top_of_span_range_map_residue_eq_top`.

## References

* R. Taylor, *Galois representations associated to Siegel modular forms of low weight*, Duke
  Math. J. 63 (1991), 281–332 (for the role of spanning lattices and stable lattices).
-/

public section

open Function Module Submodule

namespace Representation

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  {ρ : Representation k G V} {τ φ : G} {q : ℕ} {μ : k}

/-- **An element conjugate to its `q`-th power with a full eigenvalue orbit forces spanning.**
Let `ρ (φ τ φ⁻¹) = ρ τ ^ q`, and let `ρ τ` have an eigenvalue `μ` whose powers `μ ^ q ^ i`,
`i < dim V`, are pairwise distinct. Then the image of `ρ` spans `End V`: it contains the basis
`ρ (φ⁻¹) ^ a * ρ τ ^ b`, `a, b < dim V`, of
`Module.End.span_range_pow_mul_pow_eq_top_of_mul_eq_mul_pow`. -/
theorem span_range_eq_top_of_map_conj_eq_pow [FiniteDimensional k V]
    (h : ρ (φ * τ * φ⁻¹) = ρ τ ^ q) (hμ : End.HasEigenvalue (ρ τ) μ)
    (hdist : Injective fun i : Fin (finrank k V) ↦ μ ^ q ^ (i : ℕ)) :
    span k (Set.range ρ) = ⊤ := by
  have hTF : ρ τ * ρ φ⁻¹ = ρ φ⁻¹ * ρ τ ^ q :=
    (MonoidHom.semiconjBy_map_inv_of_map_conj_eq_pow h).eq.symm
  have hF : Injective (ρ φ⁻¹) :=
    ((End.isUnit_iff _).mp ((Group.isUnit φ⁻¹).map ρ)).injective
  refine eq_top_mono (span_mono ?_)
    (End.span_range_pow_mul_pow_eq_top_of_mul_eq_mul_pow hTF hF hμ hdist)
  rintro _ ⟨p, rfl⟩
  exact ⟨φ⁻¹ ^ (p.1 : ℕ) * τ ^ (p.2 : ℕ), by rw [map_mul, map_pow, map_pow]⟩

/-- **Irreducibility from an element conjugate to its `q`-th power.** Let `ρ (φ τ φ⁻¹) = ρ τ ^ q`,
and let `ρ τ` have an eigenvalue `μ` whose powers `μ ^ q ^ i`, `i < dim V`, are pairwise
distinct. Then `ρ` is irreducible; indeed its image spans `End V`
(`Representation.span_range_eq_top_of_map_conj_eq_pow`), so it stays irreducible after any
extension of scalars. -/
theorem isIrreducible_of_map_conj_eq_pow [FiniteDimensional k V]
    (h : ρ (φ * τ * φ⁻¹) = ρ τ ^ q) (hμ : End.HasEigenvalue (ρ τ) μ)
    (hdist : Injective fun i : Fin (finrank k V) ↦ μ ^ q ^ (i : ℕ)) :
    ρ.IsIrreducible := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have : Nontrivial V := nontrivial_of_ne v 0 hv.2
  have := (AlgHom.id k (End k V)).isIrreducible_toMonoidHom_comp_of_span_eq_top surjective_id ρ
    (span_range_eq_top_of_map_conj_eq_pow h hμ hdist)
  rwa [show (AlgHom.id k (End k V) : End k V →* End k V).comp ρ = ρ from
    MonoidHom.ext fun _ ↦ by simp] at this

end Representation

namespace IsLocalRing

variable {R n : Type*} [CommRing R] [IsLocalRing R]

/-- **A matrix conjugate to a power of itself, over a local ring.** Let `A * B = B * A ^ q` in
`M_n(R)` with `B` invertible, and let the reduction of `A` have an eigenvalue `μ` in the residue
field whose powers `μ ^ q ^ i`, `i < n`, are pairwise distinct. Then the matrices `B ^ a * A ^ b`,
`a, b < n`, span `M_n(R)`: their reductions span over the residue field
(`Matrix.span_range_pow_mul_pow_eq_top_of_mul_eq_mul_pow`), and Nakayama's lemma lifts this. -/
theorem span_range_pow_mul_pow_eq_top_of_mul_eq_mul_pow [Fintype n] [DecidableEq n]
    {A B : Matrix n n R} {q : ℕ} (hAB : A * B = B * A ^ q) (hB : IsUnit B) {μ : ResidueField R}
    (hμ : (A.map (residue R)).charpoly.IsRoot μ)
    (hdist : Injective fun i : Fin (Fintype.card n) ↦ μ ^ q ^ (i : ℕ)) :
    span R (Set.range fun p : Fin (Fintype.card n) × Fin (Fintype.card n) ↦
      B ^ (p.1 : ℕ) * A ^ (p.2 : ℕ)) = ⊤ := by
  let f := (residue R).mapMatrix (m := n)
  have hAB' : f A * f B = f B * f A ^ q := by rw [← map_mul, ← map_pow, ← map_mul, hAB]
  refine span_range_eq_top_of_span_range_map_residue_eq_top ?_
  convert Matrix.span_range_pow_mul_pow_eq_top_of_mul_eq_mul_pow hAB' (hB.map f) hμ hdist
    using 3 with p
  simp [f, ← RingHom.mapMatrix_apply]

end IsLocalRing

namespace MonoidHom

open IsLocalRing

variable {R G n : Type*} [CommRing R] [Group G] [Fintype n] [DecidableEq n]
  {u : G →* Matrix n n R} {τ φ : G} {q : ℕ}

/-- **Spanning over a local ring from an element conjugate to its `q`-th power.** Let `R` be a
local ring and `u : G →* M_n(R)` with `u (φ τ φ⁻¹) = u τ ^ q`, and let the reduction of `u τ` have
an eigenvalue `μ` in the residue field whose powers `μ ^ q ^ i`, `i < n`, are pairwise distinct.
Then the image of `u` spans `M_n(R)`: it contains the matrices `u (φ⁻¹) ^ a * u τ ^ b`, which span
by `IsLocalRing.span_range_pow_mul_pow_eq_top_of_mul_eq_mul_pow`. -/
theorem span_range_eq_top_of_map_conj_eq_pow [IsLocalRing R]
    (h : u (φ * τ * φ⁻¹) = u τ ^ q) {μ : ResidueField R}
    (hμ : ((u τ).map (residue R)).charpoly.IsRoot μ)
    (hdist : Injective fun i : Fin (Fintype.card n) ↦ μ ^ q ^ (i : ℕ)) :
    span R (Set.range u) = ⊤ := by
  refine eq_top_mono (span_mono ?_) (IsLocalRing.span_range_pow_mul_pow_eq_top_of_mul_eq_mul_pow
    (semiconjBy_map_inv_of_map_conj_eq_pow h).eq.symm ((Group.isUnit φ⁻¹).map u) hμ hdist)
  rintro _ ⟨p, rfl⟩
  exact ⟨φ⁻¹ ^ (p.1 : ℕ) * τ ^ (p.2 : ℕ), by rw [map_mul, map_pow, map_pow]⟩

end MonoidHom
