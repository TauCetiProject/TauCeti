/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.Pair.Complete
public import TauCeti.RingTheory.Perfectoid.PseudoUniformizerRoots.Existence

/-!
# Frobenius on rings of integral elements of perfectoid rings

For a perfectoid Tate ring `R`, every ring of integral elements `R⁺` satisfies the
Frobenius condition: Frobenius on `R⁺/p` is surjective, as is the power map modulo `ϖ p`,
and the relative Frobenius `R⁺/ϖ → R⁺/ϖᵖ` is bijective. These assertions do not require
a perfectoid base field or any restriction on the characteristic.

The passage from `R°` to `R⁺` uses approximation modulo `ϖ p` in `R°`. The quotient
of the approximation error by `p` is topologically nilpotent, hence lies in `R⁺`.
Integral closedness then puts the approximate root in `R⁺` as well.

We also produce a pseudouniformiser whose `p`-th power divides `p` with a
topologically nilpotent quotient in `R⁺`. The surjectivity statement on Mathlib's
`ModP` carrier is the Frobenius hypothesis needed by `surjective_fontaineTheta`.

## References

* B. Bhatt, M. Morrow, P. Scholze, *Integral p-adic Hodge theory*, proof of Lemma 3.20.
* P. Scholze, *Étale cohomology of diamonds*, Definition 3.1 and Remark 3.2.
-/

public section

open TauCeti.Perfectoid

namespace TauCeti.Huber.IsRingOfIntegralElements

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] [UniformSpace R]
  [IsUniformAddGroup R] [IsTopologicalRing R] [IsTateRing R] [CompleteSpace R] [T2Space R]
  [IsPerfectoidTateRing p R] {Rplus : Subring R}

/-- Every element of any ring of integral elements of a perfectoid Tate ring is a
`p`-th power modulo `p`, including when the ambient ring is zero. -/
theorem exists_natCast_dvd_sub_pow (hplus : IsRingOfIntegralElements Rplus)
    (x : Rplus) : ∃ y : Rplus, (p : Rplus) ∣ x - y ^ p := by
  obtain ⟨ϖ, hϖ, hdvd, -, -⟩ :=
    IsPerfectoidTateRing.exists_pseudoUniformizer (p := p) (R := R)
  have := IsPerfectoidTateRing.isUniform p (R := R)
  obtain ⟨y, z, hz⟩ := exists_mul_natCast_dvd_sub_pow_of_forall_exists_natCast_dvd_sub_pow
    (isRingOfIntegralElements_powerBoundedSubring R) hϖ hdvd
    IsPerfectoidTateRing.exists_natCast_dvd_sub_pow
    (⟨x, hplus.le_powerBoundedSubring x.2⟩ : powerBoundedSubring R)
  have hzR : (x : R) - (y : R) ^ p = (ϖ : R) * p * (z : R) := by
    simpa only [map_sub, map_pow, map_mul, map_natCast, Subring.subtype_apply]
      using congrArg (powerBoundedSubring R).subtype hz
  have hϖz : (ϖ : R) * (z : R) ∈ Rplus :=
    hplus.mem_of_isTopologicallyNilpotent <| by
      rw [mul_comm]
      exact (mem_powerBoundedSubring.mp z.2).isTopologicallyNilpotent_mul
        hϖ.isTopologicallyNilpotent
  have hy : (y : R) ∈ Rplus := by
    apply hplus.mem_of_pow_mem (Fact.out : p.Prime).pos
    have heq : (y : R) ^ p = x - p * ((ϖ : R) * z) := by
      linear_combination -hzR
    rw [heq]
    exact Rplus.sub_mem x.2 (Rplus.mul_mem (natCast_mem Rplus p) hϖz)
  refine ⟨⟨y, hy⟩, ⟨⟨(ϖ : R) * z, hϖz⟩, ?_⟩⟩
  apply Rplus.subtype_injective
  simp only [map_sub, map_pow, map_mul, map_natCast, Subring.subtype_apply]
  linear_combination hzR

/-- A ring of integral elements of a perfectoid Tate ring contains a pseudouniformiser
whose `p`-th power divides `p` with topologically nilpotent quotient. -/
theorem exists_pseudoUniformizer_natCast_eq_pow_mul
    (hplus : IsRingOfIntegralElements Rplus) :
    ∃ ϖ : Rplus, IsPseudoUniformizer (ϖ : R) ∧
      ∃ c : Rplus, (p : Rplus) = ϖ ^ p * c ∧ IsTopologicallyNilpotent (c : R) := by
  obtain ⟨r⟩ := PseudoUniformizerRoots.nonempty (p := p) (R := R)
  obtain ⟨c, hc⟩ := r.rootPB_pow_dvd 0
  have hnil : IsTopologicallyNilpotent ((r.rootPB 0 : R) ^ (p - 1) * (c : R)) := by
    rw [r.coe_rootPB, mul_comm]
    exact (mem_powerBoundedSubring.mp c.2).isTopologicallyNilpotent_mul
      (r.isPseudoUniformizer_root_zero.isTopologicallyNilpotent.pow
        (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt).ne')
  refine ⟨⟨r.root 1, hplus.mem_of_isTopologicallyNilpotent
    (r.isPseudoUniformizer_root 1).isTopologicallyNilpotent⟩,
    r.isPseudoUniformizer_root 1,
    ⟨⟨(r.rootPB 0 : R) ^ (p - 1) * c, hplus.mem_of_isTopologicallyNilpotent hnil⟩, ?_, hnil⟩⟩
  apply Subtype.ext
  have hroot : r.root 1 ^ p = r.root 0 := r.root_succ_pow 0
  have hcR : (p : R) = r.root 0 ^ p * (c : R) := by
    simpa only [map_natCast, map_mul, map_pow, Subring.subtype_apply, r.coe_rootPB]
      using congrArg (powerBoundedSubring R).subtype hc
  simp only [Subring.coe_natCast, Subring.coe_mul, Subring.coe_pow, r.coe_rootPB]
  rw [hroot, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (Fact.out : p.Prime).one_le]
  exact hcR

/-- In any ring of integral elements, perfectoid Frobenius is surjective even modulo
`ϖ p` for every pseudouniformiser with `ϖᵖ ∣ p` in that ring. -/
theorem exists_mul_natCast_dvd_sub_pow (hplus : IsRingOfIntegralElements Rplus)
    {ϖ : Rplus} (hϖ : IsPseudoUniformizer (ϖ : R)) (hdvd : ϖ ^ p ∣ (p : Rplus))
    (x : Rplus) : ∃ y : Rplus, ϖ * p ∣ x - y ^ p := by
  have := IsPerfectoidTateRing.isUniform p (R := R)
  exact hplus.exists_mul_natCast_dvd_sub_pow_of_forall_exists_natCast_dvd_sub_pow hϖ hdvd
    (hplus.exists_natCast_dvd_sub_pow) x

/-- Relative Frobenius on any ring of integral elements of a perfectoid Tate ring is
bijective for every pseudouniformiser satisfying the required divisibility in that ring. -/
theorem bijective_frobeniusModPow (hplus : IsRingOfIntegralElements Rplus)
    {ϖ : Rplus} (hϖ : IsPseudoUniformizer (ϖ : R)) (hdvd : ϖ ^ p ∣ (p : Rplus)) :
    Function.Bijective (frobeniusModPow p hdvd) := by
  have := hplus.isIntegrallyClosedIn
  exact ⟨frobeniusModPow_injective (B := R) hdvd hϖ.isUnit,
    (frobeniusModPow_surjective_iff hdvd).mpr fun x ↦
      (hplus.exists_natCast_dvd_sub_pow x).imp fun _ ↦ hdvd.trans⟩

/-- The prime is not a unit in any ring of integral elements of a nonzero perfectoid
Tate ring. This supplies the `Fact` hypothesis in Mathlib's integral tilt and Frobenius. -/
theorem not_isUnit_natCast [Nontrivial R] (hplus : IsRingOfIntegralElements Rplus) :
    ¬ IsUnit (p : Rplus) := by
  have := IsPerfectoidTateRing.isUniform p (R := R)
  obtain ⟨ϖ, -, c, hc, hnil⟩ := hplus.exists_pseudoUniformizer_natCast_eq_pow_mul (p := p)
  apply hplus.not_isUnit_of_isTopologicallyNilpotent
  have hcR : (p : R) = (ϖ : R) ^ p * (c : R) := by exact_mod_cast hc
  rw [Subring.coe_natCast, hcR]
  exact (hplus.isPowerBounded_of_mem (Rplus.pow_mem ϖ.2 p)).isTopologicallyNilpotent_mul hnil

/-- Frobenius on Mathlib's `ModP R⁺ p` is surjective for every ring of integral elements
of a perfectoid Tate ring. The nonunit hypothesis required to form this Frobenius is
supplied by `not_isUnit_natCast` when the ambient ring is nonzero. -/
theorem surjective_frobenius_modP (hplus : IsRingOfIntegralElements Rplus)
    [Fact (¬ IsUnit (p : Rplus))] :
    Function.Surjective (frobenius (ModP Rplus p) p) :=
  (surjective_frobenius_modP_iff Rplus).mpr (hplus.exists_natCast_dvd_sub_pow)

end TauCeti.Huber.IsRingOfIntegralElements
