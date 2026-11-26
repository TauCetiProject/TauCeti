/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Spanning
public import TauCeti.RepresentationTheory.Irreducible
-- Non-public: the iterated semiconjugation is used in a proof only.
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
`u` spans `M_n(R)` itself, by Nakayama's lemma. Consequently the reduction of `u` along any ring
homomorphism to a field is absolutely irreducible, and, if moreover `u (τ ^ q ^ n) = u τ`, the
element `u (φ ^ n)`, which commutes with the whole image, is scalar.

In the roadmap's criterion the characteristic polynomial of `ρ τ` is the product of `X - x` over
the roots `x` of a label, a polynomial over a finite field `𝔽_g` whose roots are permuted by
`x ↦ x ^ g`.
The results here are the case of a single label irreducible of degree `dim V`: its roots form
one Frobenius orbit of length `dim V`.

## Main results

* `Representation.span_range_eq_top_of_map_conj_eq_pow`: over a field, the image of `ρ` spans
  `End V`.
* `Representation.isIrreducible_of_map_conj_eq_pow`: so `ρ` is irreducible.
* `MonoidHom.span_range_eq_top_of_map_conj_eq_pow`: over a local ring, the image of
  `u : G →* M_n(R)` spans `M_n(R)`.
* `MonoidHom.map_pow_card_mem_range_scalar_of_map_conj_eq_pow`: if moreover
  `u (τ ^ q ^ n) = u τ`, then `u (φ ^ n)` is a scalar matrix.
* `MonoidHom.isIrreducible_map_of_span_range_eq_top`: if the image of `u : G →* M_n(R)` spans
  `M_n(R)`, its reduction along any ring homomorphism `R →+* k` to a field is irreducible.

## Provenance

Adapted from `New.Selmer.IsLatticeIn.span_range_eq_top_of_map_pow_eq_map_conj` and
`New.Selmer.eq_bot_or_eq_top_of_span_eq_top` in
`src/Lib/GaloisRep/Pseudocharacter/Pseudorepresentations.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), which states
the criterion for an `O`-lattice in an `ℓ`-adic representation with coefficients in a finite
extension `O` of `ℤ_ℓ`; here the coefficients are an arbitrary local ring. grh-lean calls the
spanning statement "a case of Burnside's theorem, lifted to `O` by Nakayama's lemma".

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
  have hTF : ρ τ * ρ φ⁻¹ = ρ φ⁻¹ * ρ τ ^ q := by
    rw [← h, ← map_mul, ← map_mul]
    congr 1
    group
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
  exact (AlgHom.id k (End k V)).isIrreducible_toMonoidHom_comp_of_span_eq_top surjective_id ρ
    (span_range_eq_top_of_map_conj_eq_pow h hμ hdist)

end Representation

namespace MonoidHom

open IsLocalRing

variable {R G n : Type*} [CommRing R] [Group G] [Fintype n] [DecidableEq n]
  {u : G →* Matrix n n R} {τ φ : G} {q : ℕ}

/-- If `u (φ τ φ⁻¹) = u τ ^ q`, then `T = u τ` and `F = u φ⁻¹` satisfy `T * F = F * T ^ q`. -/
private theorem map_mul_map_inv_eq (h : u (φ * τ * φ⁻¹) = u τ ^ q) :
    u τ * u φ⁻¹ = u φ⁻¹ * u τ ^ q := by
  rw [← h, ← map_mul, ← map_mul]
  congr 1
  group

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
    (map_mul_map_inv_eq h) ((Group.isUnit φ⁻¹).map u) hμ hdist)
  rintro _ ⟨p, rfl⟩
  exact ⟨φ⁻¹ ^ (p.1 : ℕ) * τ ^ (p.2 : ℕ), by rw [map_mul, map_pow, map_pow]⟩

/-- **The `n`-th power of the Frobenius element acts by a scalar.** In the situation of
`MonoidHom.span_range_eq_top_of_map_conj_eq_pow`, assume moreover `u (τ ^ q ^ n) = u τ`. Then
`u (φ ^ n)` commutes with `u τ` and `u φ⁻¹`, hence with a family spanning `M_n(R)`, so it is a
scalar matrix. -/
theorem map_pow_card_mem_range_scalar_of_map_conj_eq_pow [IsLocalRing R]
    (h : u (φ * τ * φ⁻¹) = u τ ^ q) {μ : ResidueField R}
    (hμ : ((u τ).map (residue R)).charpoly.IsRoot μ)
    (hdist : Injective fun i : Fin (Fintype.card n) ↦ μ ^ q ^ (i : ℕ))
    (hfix : u (τ ^ q ^ Fintype.card n) = u τ) :
    u (φ ^ Fintype.card n) ∈ Set.range (Matrix.scalar n) := by
  set N := Fintype.card n
  have hTF := map_mul_map_inv_eq h
  -- `u (φ⁻¹ ^ N)` commutes with `u τ`, hence so does its inverse `u (φ ^ N)`.
  have hcomm_inv : Commute (u (φ⁻¹ ^ N)) (u τ) := by
    have := (SemiconjBy.pow_left_pow_pow hTF.symm N).eq
    rwa [← map_pow, ← map_pow, hfix] at this
  have h1 : u (φ ^ N) * u (φ⁻¹ ^ N) = 1 := by
    rw [← map_mul, inv_pow, mul_inv_cancel, map_one]
  have h2 : u (φ⁻¹ ^ N) * u (φ ^ N) = 1 := by
    rw [← map_mul, inv_pow, inv_mul_cancel, map_one]
  have hcomm : Commute (u (φ ^ N)) (u τ) := calc
    u (φ ^ N) * u τ = u (φ ^ N) * (u τ * u (φ⁻¹ ^ N)) * u (φ ^ N) := by
      rw [mul_assoc, mul_assoc, h2, mul_one]
    _ = u τ * u (φ ^ N) := by rw [← hcomm_inv.eq, ← mul_assoc, h1, one_mul]
  refine Matrix.mem_range_scalar_of_commute_of_span_eq_top
    (IsLocalRing.span_range_pow_mul_pow_eq_top_of_mul_eq_mul_pow hTF
      ((Group.isUnit φ⁻¹).map u) hμ hdist)
    fun p ↦ ((Commute.pow_left ?_ _).mul_left (hcomm.symm.pow_left _))
  exact ((Commute.self_pow φ N).inv_left).map u

/-- **A spanning image has absolutely irreducible reductions.** If the image of a monoid
homomorphism `u : G →* M_n(R)` spans `M_n(R)`, then for every ring homomorphism `f : R →+* k` to a
field and `n` nonempty, the representation `g ↦ (u g).map f` of `G` on `kⁿ` is irreducible: its
image spans `M_n(k)` (`Matrix.span_range_map_eq_top`), so it stays irreducible after any extension
of `k`. For `R` local and `f` the residue map this is the absolute irreducibility of the residual
representation. -/
theorem isIrreducible_map_of_span_range_eq_top {M k : Type*} [Monoid M] [Field k] [Nonempty n]
    (u : M →* Matrix n n R) (hu : span R (Set.range u) = ⊤) (f : R →+* k) :
    Representation.IsIrreducible
      (((Matrix.toLinAlgEquiv' (R := k) (n := n)).toAlgHom : Matrix n n k →* End k (n → k)).comp
        ((f.mapMatrix (m := n)).toMonoidHom.comp u)) :=
  Matrix.toLinAlgEquiv'.toAlgHom.isIrreducible_toMonoidHom_comp_of_span_eq_top
    Matrix.toLinAlgEquiv'.surjective ((f.mapMatrix (m := n)).toMonoidHom.comp u)
    (Matrix.span_range_map_eq_top f hu)

end MonoidHom
