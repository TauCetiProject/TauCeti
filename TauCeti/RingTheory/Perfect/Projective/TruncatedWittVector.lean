/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Flat.Basic
public import TauCeti.RingTheory.WittVector.Truncated.Basic

import Mathlib.LinearAlgebra.TensorProduct.Quotient
import TauCeti.Algebra.Module.Projective.Nilpotent
import TauCeti.RingTheory.Ideal.Operations
import TauCeti.RingTheory.Perfect.Projective.Basic

/-!
# Frobenius modules over truncated Witt vectors are projective

Let `R` be a perfect ring of characteristic `p`, let `W_n(R)` be its ring of truncated Witt vectors
of length `n`, and let `a ≥ 1`. The Witt vector Frobenius `φ` of `W_n(R)` raises each Witt
coordinate to the `p`-th power (`TruncatedWittVector.map (frobenius R p)`), and `φ^a` raises each
coordinate to the `p ^ a`-th power. Since `R` is perfect, `φ^a` is an automorphism, so a
`φ^a`-module structure on a `W_n(R)`-module `M`, that is, an isomorphism
`W_n(R) ⊗_{W_n(R), φ^a} M ≅ M`, is the same as an additive automorphism `F` of `M` with
`F (c • x) = φ^a(c) • F x`.

A finitely presented `W_n(R)`-module `M` with such an `F`, which is flat over `ℤ ⧸ pⁿ`, is
projective. No constant-rank hypothesis is needed, and the case `n = 0` is trivial.

The flatness hypothesis cannot be dropped: for `R ≠ 0` the `W₂(R)`-module `W₂(R) ⧸ p` carries the
Frobenius induced by `φ`, but it is not flat over `ℤ ⧸ p²` and not projective over `W₂(R)`.

The proof reduces modulo `p`. Since `W_n(R) ⧸ p ≃+* R` (`TruncatedWittVector.quotientPEquiv`) and
`φ^a(c)` is congruent to `c ^ p ^ a` modulo `p`, the reduction `M ⧸ p M` is a finitely presented
module over a perfect ring with an invertible `φ^a`-linearization, hence projective
(`TauCeti.projective_of_addEquiv_iterateFrobenius`). By the equational criterion for flatness over
`ℤ ⧸ pⁿ`, an element of `M` killed by `p` is a combination of elements of `M` with coefficients in
`ℤ ⧸ pⁿ` killed by `p`, and these coefficients act through the annihilator of `p` in `W_n(R)`. As
`p` is nilpotent in `W_n(R)`, projectivity of `M ⧸ p M` then lifts to `M`
(`Module.Projective.of_quotient_smul_top`).

## Main results

* `TauCeti.projective_of_flat_of_addEquiv_map_iterateFrobenius`: a finitely presented
  `W_n(R)`-module, flat over `ℤ ⧸ pⁿ`, with an invertible `φ^a`-linearization for some `a ≥ 1`, is
  projective.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  Lemma 3.2.12 and Proposition 3.2.13.
-/

public section

namespace TauCeti

open Module TruncatedWittVector

variable {R M : Type*} [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] {n : ℕ}
  [AddCommGroup M] [Module (TruncatedWittVector p n R) M]

variable [PerfectRing R p]

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm in
/-- The reduction modulo `p` of a finitely presented `W_n(R)`-module with an invertible
`φ^a`-linearization is projective over `W_n(R) ⧸ p ≃+* R`. -/
private theorem projective_quotient_smul_top [NeZero n]
    [FinitePresentation (TruncatedWittVector p n R) M] {a : ℕ} (ha : a ≠ 0) (F : M ≃+ M)
    (hF : ∀ (c : TruncatedWittVector p n R) (x : M),
      F (c • x) = TruncatedWittVector.map (iterateFrobenius R p a) c • F x) :
    Projective (TruncatedWittVector p n R ⧸ Ideal.span {(p : TruncatedWittVector p n R)})
      (M ⧸ Ideal.span {(p : TruncatedWittVector p n R)} •
        (⊤ : Submodule (TruncatedWittVector p n R) M)) := by
  set A := TruncatedWittVector p n R
  set I := Ideal.span {(p : A)}
  let e : A ⧸ I ≃+* R := quotientPEquiv
  have he (c : A) : e (Ideal.Quotient.mk I c) = constantCoeff c := quotientPEquiv_mk c
  have : FinitePresentation (A ⧸ I) (M ⧸ I • (⊤ : Submodule A M)) :=
    .of_equiv ((TensorProduct.quotTensorEquivQuotSMul M I).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective)
  -- The reduction of `F`.
  let σ : A ≃+* A := mapEquiv (iterateFrobeniusEquiv R p a)
  have hφ : (iterateFrobeniusEquiv R p a : R →+* R) = iterateFrobenius R p a :=
    RingHom.ext fun r ↦ by rw [RingEquiv.coe_toRingHom, coe_iterateFrobeniusEquiv]
  have hσ (c : A) : σ c = TruncatedWittVector.map (iterateFrobenius R p a) c := by
    rw [mapEquiv_apply, hφ]
  let Fσ : M ≃ₛₗ[(σ : A →+* A)] M :=
    { F with map_smul' := fun c x ↦ by simpa [hσ] using hF c x }
  have hmem (y : M) : y ∈ I • (⊤ : Submodule A M) ↔ ∃ z : M, p • z = y := by
    simp [I, Submodule.mem_span_singleton_smul_top_iff, Nat.cast_smul_eq_nsmul]
  have hI : (I • (⊤ : Submodule A M)).map (Fσ : M →ₛₗ[(σ : A →+* A)] M) = I • ⊤ := by
    ext y
    simp only [Submodule.mem_map, hmem]
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨F z, by simp [Fσ]⟩
    · rintro ⟨z, rfl⟩
      exact ⟨p • F.symm z, ⟨F.symm z, rfl⟩, by simp [Fσ]⟩
  refine projective_of_addEquiv_iterateFrobenius p ha
    (Submodule.Quotient.equiv _ _ Fσ hI).toAddEquiv fun b x ↦ ?_
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  -- `φ^a(c)` is congruent to `c ^ p ^ a` modulo `p`.
  have hc : iterateFrobenius (A ⧸ I) p a (Ideal.Quotient.mk I c) = Ideal.Quotient.mk I (σ c) := by
    apply e.injective
    simp [iterateFrobenius_def, he, hσ]
  -- The reduction of `F` acts on representatives (`Submodule.Quotient.equiv_apply`).
  have hmk (y : M) : (Submodule.Quotient.equiv _ _ Fσ hI).toAddEquiv (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (F y) := by
    simp [Fσ]
  rw [hc, Module.Quotient.mk_smul_mk, hmk, hmk, hF, ← hσ, Module.Quotient.mk_smul_mk]

/-- **Frobenius modules over truncated Witt vectors are projective.** Let `R` be a perfect ring of
characteristic `p` and `a ≥ 1`. A finitely presented module `M` over `W_n(R)`, flat over `ℤ ⧸ pⁿ`,
with an additive automorphism `F` satisfying `F (c • x) = φ^a(c) • F x` for the Witt vector
Frobenius `φ`, that is, with an invertible `φ^a`-linearization, is projective. -/
theorem projective_of_flat_of_addEquiv_map_iterateFrobenius
    [FinitePresentation (TruncatedWittVector p n R) M] [Module (ZMod (p ^ n)) M]
    [Flat (ZMod (p ^ n)) M] {a : ℕ} (ha : a ≠ 0) (F : M ≃+ M)
    (hF : ∀ (c : TruncatedWittVector p n R) (x : M),
      F (c • x) = TruncatedWittVector.map (iterateFrobenius R p a) c • F x) :
    Projective (TruncatedWittVector p n R) M := by
  rcases n.eq_zero_or_pos with rfl | hn
  · have : Subsingleton (TruncatedWittVector p 0 R) := ⟨fun x y ↦ ext fun i ↦ i.elim0⟩
    have : Subsingleton M := Module.subsingleton (TruncatedWittVector p 0 R) M
    infer_instance
  have : NeZero n := ⟨hn.ne'⟩
  have := projective_quotient_smul_top p ha F hF
  exact Projective.of_quotient_smul_top
    ⟨n, by rw [← Nat.cast_pow, CharP.cast_eq_zero]⟩
    (Flat.mem_annihilator_smul_top_of_smul_eq_zero (m := p ^ n) p)

end TauCeti
