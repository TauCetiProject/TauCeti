/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.Basic
import TauCeti.RingTheory.Huber.Perfect

/-!
# Perfectoid Tate rings of characteristic `p`

In characteristic `p`, the perfectoid Tate rings are exactly the perfect complete Hausdorff Tate
rings (Scholze, *Étale cohomology of diamonds*, Proposition 3.5).

* A perfectoid Tate ring of characteristic `p` is perfect. It is reduced, so Frobenius is
  injective. For surjectivity, every `x ∈ R°` is a `p`-th power modulo `p`
  (`TauCeti.Perfectoid.IsPerfectoidTateRing.exists_natCast_dvd_sub_pow`), and `p = 0`, so `x` is a
  `p`-th power. Any `x ∈ R` has `ϖ ^ (p n) x ∈ R°` for some `n`, so it is a `p`-th power too.
* Conversely, a perfect complete Hausdorff Tate ring of characteristic `p` is uniform
  (`TauCeti.Huber.IsUniform.of_perfectRing`), hence perfectoid
  (`TauCeti.Perfectoid.IsPerfectoidTateRing.of_perfectRing`).

## Main results

* `TauCeti.Perfectoid.IsPerfectoidTateRing.perfectRing`: a perfectoid Tate ring of
  characteristic `p` is perfect.
* `TauCeti.Perfectoid.IsPerfectoidTateRing.of_perfectRing`: a perfect complete Hausdorff Tate ring
  of characteristic `p` is perfectoid.
* `TauCeti.Perfectoid.isPerfectoidTateRing_iff_perfectRing`: in characteristic `p`, a complete
  Hausdorff Tate ring is perfectoid exactly when it is perfect.

## References

* P. Scholze, *Étale cohomology of diamonds*, Proposition 3.5.
* P. Scholze, *Perfectoid spaces*, Proposition 5.9.
* K. S. Kedlaya, R. Liu, *Relative p-adic Hodge theory: foundations*, Remark 3.3.4.
-/

public section

open TauCeti.Huber

namespace TauCeti.Perfectoid

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [IsTopologicalRing R] [IsTateRing R] [CompleteSpace R] [T2Space R] [CharP R p]

/-- In a perfectoid Tate ring of characteristic `p`, every power-bounded element has a `p`-th
root: it is a `p`-th power modulo `p = 0`. -/
private theorem IsPerfectoidTateRing.exists_pow_eq [IsPerfectoidTateRing p R]
    (x : powerBoundedSubring R) : ∃ s : R, s ^ p = x := by
  obtain ⟨y, hy⟩ := IsPerfectoidTateRing.exists_natCast_dvd_sub_pow (p := p) x
  have hp : (p : powerBoundedSubring R) = 0 := Subtype.ext (CharP.cast_eq_zero R p)
  rw [hp, zero_dvd_iff, sub_eq_zero] at hy
  exact ⟨y, by rw [hy]; rfl⟩

/-- **A perfectoid Tate ring of characteristic `p` is perfect** (Scholze, *Étale cohomology of
diamonds*, Proposition 3.5). -/
theorem IsPerfectoidTateRing.perfectRing [IsPerfectoidTateRing p R] : PerfectRing R p := by
  have := IsPerfectoidTateRing.isReduced p (R := R)
  refine PerfectRing.ofSurjective R p fun x ↦ ?_
  obtain ⟨ϖ, hϖ⟩ := IsTateRing.exists_isPseudoUniformizer (A := R)
  obtain ⟨n, hn⟩ := exists_mul_pow_mem_of_isTopologicallyNilpotent hϖ.isTopologicallyNilpotent
    (isOpen_powerBoundedSubring R) x
  -- `x * ϖ ^ (p * n)` is a power-bounded `p`-th power, so `x` is a `p`-th power
  have hmem : x * ϖ ^ (p * n) ∈ powerBoundedSubring R := by
    obtain ⟨q, hq⟩ := Nat.exists_eq_add_of_le (Nat.le_mul_of_pos_left n (Fact.out : p.Prime).pos)
    rw [hq, pow_add, ← mul_assoc]
    have hϖq : IsPowerBounded (ϖ ^ q) :=
      (IsPowerBounded.of_isTopologicallyNilpotent hϖ.isTopologicallyNilpotent).pow q
    exact (powerBoundedSubring R).mul_mem hn (mem_powerBoundedSubring.mpr hϖq)
  obtain ⟨s, hs⟩ := IsPerfectoidTateRing.exists_pow_eq (p := p) ⟨_, hmem⟩
  refine ⟨s * ((hϖ.isUnit.unit⁻¹ : Rˣ) : R) ^ n, ?_⟩
  calc frobenius R p (s * ((hϖ.isUnit.unit⁻¹ : Rˣ) : R) ^ n)
      = x * ((hϖ.isUnit.unit⁻¹ : Rˣ) * ϖ) ^ (p * n) := by
        rw [frobenius_def, mul_pow, hs]
        ring
    _ = x := by rw [hϖ.isUnit.val_inv_mul, one_pow, mul_one]

/-- **A perfect complete Hausdorff Tate ring of characteristic `p` is perfectoid** (Scholze,
*Étale cohomology of diamonds*, Proposition 3.5): it is uniform, every pseudouniformiser works,
`ϖ ^ p ∣ p = 0` being automatic, and Frobenius is bijective. -/
theorem IsPerfectoidTateRing.of_perfectRing [PerfectRing R p] : IsPerfectoidTateRing p R := by
  have := IsUniform.of_perfectRing (R := R) p
  obtain ⟨ϖ, hϖ⟩ := IsTateRing.exists_isPseudoUniformizer (A := R)
  have hp : (p : powerBoundedSubring R) = 0 := Subtype.ext (CharP.cast_eq_zero R p)
  exact .of_forall_exists_pow_eq ⟨ϖ, mem_powerBoundedSubring.mpr
    (IsPowerBounded.of_isTopologicallyNilpotent hϖ.isTopologicallyNilpotent)⟩ hϖ
    (hp ▸ dvd_zero _) fun x ↦
      (surjective_frobenius R p x).imp fun _ h ↦ by rwa [frobenius_def] at h

/-- **In characteristic `p`, perfectoid means perfect** (Scholze, *Étale cohomology of diamonds*,
Proposition 3.5): a complete Hausdorff Tate ring of characteristic `p` is a perfectoid Tate ring
exactly when it is a perfect ring. -/
theorem isPerfectoidTateRing_iff_perfectRing : IsPerfectoidTateRing p R ↔ PerfectRing R p :=
  ⟨fun _ ↦ IsPerfectoidTateRing.perfectRing, fun _ ↦ .of_perfectRing⟩

end TauCeti.Perfectoid
