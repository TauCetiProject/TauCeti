/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.Basic
public import TauCeti.RingTheory.Perfectoid.PseudoUniformizerRoots.Basic
import Mathlib.RingTheory.Teichmuller
import TauCeti.RingTheory.Jacobson.Associated

/-!
# Existence of pseudouniformisers with compatible `p`-power roots

Every perfectoid Tate ring `R` has a pseudouniformiser with compatible `p`-power roots
(Scholze, *Étale cohomology of diamonds*, Lemma 3.10). More precisely, let `R` be a complete
Hausdorff uniform Huber ring and `ϖ₁ ∈ R°` a pseudouniformiser with `ϖ₁ ^ p ∣ p` in `R°` such that
every element of `R°` is a `p`-th power modulo `ϖ₁ ^ p`. Then some compatible system
`ϖ♭ = (ϖ ^ (1 / p ^ n))ₙ` of `p`-power roots in `R°` has `ϖ ≡ ϖ₁` modulo `ϖ₁ ^ p R°`. So
`ϖ = ϖ₁ u` for a unit `u` of `R°`, and `ϖ` is again a pseudouniformiser with `ϖ ^ p ∣ p` in `R°`.

The proof follows Scholze. The ring `R°` is open and bounded, hence `ϖ₁ ^ p`-adically complete.
Frobenius on `R° ⧸ (ϖ₁ ^ p)` is surjective by hypothesis, so the class of `ϖ₁` is the zeroth term
of an element of the perfection `lim_{x ↦ x ^ p} R° ⧸ (ϖ₁ ^ p)`. That perfection is
multiplicatively isomorphic to `lim_{x ↦ x ^ p} R°` (Mathlib's `Perfection.quotientMulEquiv`,
built from the Teichmüller map), and the corresponding compatible system in `R°` is `ϖ♭`. The
unit `u` comes from `ϖ₁` lying in the Jacobson radical of the complete ring `R°`; this is where
`p ≥ 2` is used.

## Main results

* `TauCeti.Perfectoid.PseudoUniformizerRoots.exists_pow_dvd_rootPB_zero_sub_and_associated`:
  a pseudouniformiser `ϖ₁` with `ϖ₁ ^ p ∣ p` in `R°`, for which Frobenius
  `R° ⧸ (ϖ₁) → R° ⧸ (ϖ₁ ^ p)` is surjective, is congruent modulo `ϖ₁ ^ p`, and associated in `R°`,
  to a pseudouniformiser with compatible roots.
* `TauCeti.Perfectoid.PseudoUniformizerRoots.nonempty`: every perfectoid Tate ring has a
  pseudouniformiser with compatible `p`-power roots.

## References

* P. Scholze, *Étale cohomology of diamonds*, Lemma 3.10 and its proof.
* B. Bhatt, *Lecture notes for a class on perfectoid spaces*, Lemma 6.2.2 and its proof.
* B. Bhatt, M. Morrow, P. Scholze, *Integral p-adic Hodge theory*, Lemma 3.9.
-/

public section

open TauCeti.Huber

namespace TauCeti.Perfectoid.PseudoUniformizerRoots

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [IsTopologicalRing R] [CompleteSpace R]

section Uniform

variable [T0Space R] [IsHuberRing R] [IsUniform R] [Nontrivial R] (ϖ₁ : powerBoundedSubring R)
  (hϖ₁ : IsPseudoUniformizer (ϖ₁ : R)) (hdvd : ϖ₁ ^ p ∣ (p : powerBoundedSubring R))
  (hs : ∀ x : powerBoundedSubring R, ∃ y, ϖ₁ ^ p ∣ x - y ^ p)

include hϖ₁ hdvd hs in
/-- For nonzero `R`, the compatible system of `p`-power roots in `R°` lifting `ϖ₁`: Frobenius on
`R° ⧸ (ϖ₁ ^ p)` is surjective, so the class of `ϖ₁` is the zeroth term of an element of the
perfection of `R° ⧸ (ϖ₁ ^ p)`, which lifts along the Teichmüller isomorphism
`Perfection.quotientMulEquiv`, `R°` being `ϖ₁ ^ p`-adically complete. -/
private theorem exists_coeffMonoidHom_zero_sub_dvd :
    ∃ ψ : Perfection (powerBoundedSubring R) p,
      ϖ₁ ^ p ∣ Perfection.coeffMonoidHom _ p 0 ψ - ϖ₁ := by
  have hp : p.Prime := Fact.out
  set I : Ideal (powerBoundedSubring R) := Ideal.span {ϖ₁ ^ p}
  have : IsAdicComplete I (powerBoundedSubring R) :=
    IsUniform.isAdicComplete_span_singleton _ <| by
      rw [SubmonoidClass.coe_pow]
      exact isPseudoUniformizer_iff.mpr
        ⟨hϖ₁.isUnit.pow p, hϖ₁.isTopologicallyNilpotent.pow hp.ne_zero⟩
  -- `R° ⧸ (ϖ₁ ^ p)` is nonzero, as `ϖ₁ ^ p` lies in the Jacobson radical, and has
  -- characteristic `p`, as `ϖ₁ ^ p ∣ p`
  have hI : I ≠ ⊤ := fun h ↦ by
    have h' := IsAdicComplete.le_jacobson_bot I
    rw [h, top_le_iff, Ideal.jacobson_eq_top_iff] at h'
    exact bot_ne_top h'
  have : Nontrivial (powerBoundedSubring R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have : CharP (powerBoundedSubring R ⧸ I) p := (CharP.charP_iff_prime_eq_zero hp).mpr <| by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton.mpr hdvd
  have hfrob : Function.Surjective (frobenius (powerBoundedSubring R ⧸ I) p) := by
    intro x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, hy⟩ := hs x
    refine ⟨Ideal.Quotient.mk I y, ?_⟩
    rw [frobenius_def, ← map_pow, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact dvd_sub_comm.mp hy
  obtain ⟨z, hz⟩ := Perfection.coeff_surjective hfrob 0 (Ideal.Quotient.mk I ϖ₁)
  refine ⟨(Perfection.quotientMulEquiv p I).symm z, ?_⟩
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq,
    Perfection.coeff_zero_symm_quotientMulEquiv, Perfection.mk_teichmuller₀, hz]

end Uniform

/-- **Pseudouniformisers with compatible roots, with a prescribed pseudouniformiser.** Let `R`
be a complete Hausdorff uniform Huber ring and `ϖ₁ ∈ R°` a pseudouniformiser with
`ϖ₁ ^ p ∣ p` in `R°` such that every element of `R°` is a `p`-th power modulo `ϖ₁ ^ p`. Then some
pseudouniformiser `ϖ` with compatible `p`-power roots has `ϖ ≡ ϖ₁` modulo `ϖ₁ ^ p` and is
associated to `ϖ₁` in `R°` (Scholze, *Étale cohomology of diamonds*, proof of Lemma 3.10). -/
theorem exists_pow_dvd_rootPB_zero_sub_and_associated [T0Space R] [IsHuberRing R] [IsUniform R]
    (ϖ₁ : powerBoundedSubring R)
    (hϖ₁ : IsPseudoUniformizer (ϖ₁ : R)) (hdvd : ϖ₁ ^ p ∣ (p : powerBoundedSubring R))
    (hs : ∀ x : powerBoundedSubring R, ∃ y, ϖ₁ ^ p ∣ x - y ^ p) :
    ∃ ϖ : PseudoUniformizerRoots p R, ϖ₁ ^ p ∣ ϖ.rootPB 0 - ϖ₁ ∧ Associated ϖ₁ (ϖ.rootPB 0) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · -- the zero ring: every compatible system works
    have : Subsingleton (powerBoundedSubring R) := ⟨fun _ _ ↦ Subtype.ext (Subsingleton.elim _ _)⟩
    refine ⟨⟨1, isPseudoUniformizer_iff.mpr ⟨isUnit_of_subsingleton _, ?_⟩,
      ⟨0, Subsingleton.elim _ _⟩⟩, ⟨0, Subsingleton.elim _ _⟩, ⟨1, Subsingleton.elim _ _⟩⟩
    rw [Subsingleton.elim (Perfection.coeffMonoidHom R p 0 1) 0]
    exact .zero
  obtain ⟨ψ, hψ⟩ := exists_coeffMonoidHom_zero_sub_dvd ϖ₁ hϖ₁ hdvd hs
  -- `ϖ₁` lies in the Jacobson radical of the complete ring `R°`, and `p ≥ 2`, so the zeroth term
  -- `ϖ₁ + ϖ₁ ^ p c` of `ψ` is `ϖ₁ u` for a unit `u` of `R°`
  have hp : p.Prime := Fact.out
  obtain ⟨u, hu⟩ : Associated ϖ₁ (Perfection.coeffMonoidHom _ p 0 ψ) := by
    have := IsUniform.isAdicComplete_span_singleton ϖ₁ hϖ₁
    have hj := IsAdicComplete.le_jacobson_bot _ (Ideal.mem_span_singleton_self ϖ₁)
    refine associated_of_mul_dvd_sub_of_mem_jacobson
      (Ideal.pow_mem_of_mem _ hj (p - 1) (Nat.sub_pos_of_lt hp.one_lt)) ?_
    rwa [← pow_succ', Nat.sub_add_cancel hp.one_le]
  -- the zeroth term `ϖ₁ u` is a pseudouniformiser whose `p`-th power divides `p` in `R°`
  have hpu : IsPseudoUniformizer (Perfection.coeffMonoidHom (powerBoundedSubring R) p 0 ψ : R) := by
    rw [← hu, Subring.coe_mul]
    refine isPseudoUniformizer_iff.mpr
      ⟨hϖ₁.isUnit.mul (u.isUnit.map (powerBoundedSubring R).subtype), ?_⟩
    rw [mul_comm]
    exact (mem_powerBoundedSubring.mp (u : powerBoundedSubring R).2).isTopologicallyNilpotent_mul
      hϖ₁.isTopologicallyNilpotent
  refine ⟨ofPowerBounded ψ hpu ((Associated.pow_pow ⟨u, hu⟩).dvd_iff_dvd_left.mp hdvd), ?_, ?_⟩
  · rwa [rootPB_ofPowerBounded]
  · rw [rootPB_ofPowerBounded]
    exact ⟨u, hu⟩

/-- **Every perfectoid Tate ring has a pseudouniformiser with compatible `p`-power roots**
(Scholze, *Étale cohomology of diamonds*, Lemma 3.10). -/
instance nonempty [T2Space R] [IsTateRing R] [IsPerfectoidTateRing p R] :
    Nonempty (PseudoUniformizerRoots p R) := by
  have := IsPerfectoidTateRing.isUniform p (R := R)
  obtain ⟨ϖ₁, hϖ₁, hdvd, hs, -⟩ :=
    IsPerfectoidTateRing.exists_pseudoUniformizer (p := p) (R := R)
  obtain ⟨ϖ, -⟩ := exists_pow_dvd_rootPB_zero_sub_and_associated ϖ₁ hϖ₁ hdvd hs
  exact ⟨ϖ⟩

end TauCeti.Perfectoid.PseudoUniformizerRoots
