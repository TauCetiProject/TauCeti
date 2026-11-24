/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.IsUniformGroup.Constructions
public import TauCeti.RingTheory.AdicCompletion.Frobenius
public import TauCeti.RingTheory.Huber.Prod
public import TauCeti.RingTheory.Ideal.Quotient.Frobenius
public import TauCeti.RingTheory.IntegralClosure.IntegrallyClosed
import TauCeti.RingTheory.Jacobson.Associated

/-!
# Perfectoid Tate rings

Fix a prime `p`. A complete Hausdorff Tate ring `R`, with power-bounded subring `R°`, is a
*perfectoid Tate ring* if

* `R` is uniform, that is, `R°` is bounded; and
* some pseudouniformiser `ϖ ∈ R°` satisfies `ϖ ^ p ∣ p` in `R°`, and Frobenius
  `Φ : R° ⧸ (ϖ) → R° ⧸ (ϖ ^ p)`, `[x] ↦ [x ^ p]`, is bijective.

No perfectoid base field is fixed, and both characteristic `0` and characteristic `p` are allowed.
Uniformity is not implied by the second condition, and the divisibility `ϖ ^ p ∣ p` must hold in
`R°`, not merely in `R`, where it is automatic since `ϖ` is a unit of `R`. It makes `[x] ↦ [x ^ p]`
a ring homomorphism `R° ⧸ (ϖ) → R° ⧸ (ϖ ^ p)` (`TauCeti.frobeniusModPow`). Bijectivity of Frobenius
on `R° ⧸ (p)` alone is not enough: it holds on `ℤ_p ⧸ p = 𝔽_p`, yet `ℚ_p` is not perfectoid, as the
definition asks for the different map modulo `ϖ ^ p`.

The class `TauCeti.Perfectoid.IsPerfectoidTateRing` states the second condition elementwise, and
`TauCeti.Perfectoid.isPerfectoidTateRing_iff` recovers the bijectivity of
`TauCeti.frobeniusModPow`. Injectivity of `Φ` is automatic, because `R°` is integrally closed in
`R` and `ϖ` is a unit of `R` (`TauCeti.frobeniusModPow_injective`). So only
surjectivity of `Φ` has to be checked (`TauCeti.Perfectoid.IsPerfectoidTateRing.of_surjective`).

Since `R°` is `ϖ`-adically complete, surjectivity of `Φ` is equivalent to surjectivity of
Frobenius on `R° ⧸ (p)` once some `ϖ` with `ϖ ^ p ∣ p` in `R°` is given
(`TauCeti.tfae_forall_exists_dvd_sub_pow`). Consequently the perfectoid condition can be tested
modulo `p`.

The condition can also be tested on any open bounded subring `A₀` in place of `R°`: if a
pseudouniformiser `π ∈ A₀` has `π ^ p ∣ p` in `A₀` and Frobenius `A₀ ⧸ (π) → A₀ ⧸ (π ^ p)` is
bijective, then `R` is perfectoid (Bhatt–Morrow–Scholze, Lemma 3.21). Injectivity makes `A₀` closed
under `p`-th roots, hence `π R° ⊆ A₀`, so `R` is uniform; surjectivity and completeness of `A₀`
give a unit multiple of `π` with a `p`-th root, through which approximate `p`-th roots in `A₀`
yield approximate `p`-th roots in `R°`. This applies to untilts, where `𝕎 R⁺ ⧸ (ξ)` is an open
bounded subring whose relation to the power-bounded elements is not known in advance.

## Main definitions

* `TauCeti.Perfectoid.IsPerfectoidTateRing p R`: `R` is a perfectoid Tate ring.

## Main results

* `TauCeti.Perfectoid.isPerfectoidTateRing_iff`: the definition in terms of bijectivity of
  `Φ : R° ⧸ (ϖ) → R° ⧸ (ϖ ^ p)`.
* `TauCeti.Perfectoid.IsPerfectoidTateRing.of_surjective`: surjectivity of `Φ` suffices.
* `TauCeti.Perfectoid.IsPerfectoidTateRing.isUniform`,
  `TauCeti.Perfectoid.IsPerfectoidTateRing.isReduced`,
  `TauCeti.Perfectoid.IsPerfectoidTateRing.isTopologicallyNilpotent_natCast`: perfectoid Tate
  rings are uniform, reduced, and have `p` topologically nilpotent.
* `TauCeti.Perfectoid.IsPerfectoidTateRing.of_ringEquiv`: the notion is invariant under
  isomorphisms of topological rings.
* `TauCeti.Perfectoid.IsPerfectoidTateRing.prod`: a product of perfectoid Tate rings is perfectoid,
  and `TauCeti.Perfectoid.isPerfectoidTateRing_prod_iff`: conversely, so are its factors.
* `TauCeti.Perfectoid.isPerfectoidTateRing_of_subsingleton`: the zero ring is.
* `TauCeti.Perfectoid.isPerfectoidTateRing_iff_frobenius_surjective_modP`: a uniform `R` is
  perfectoid exactly when some pseudouniformiser `ϖ ∈ R°` has `ϖ ^ p ∣ p` in `R°` and Frobenius on
  `R° ⧸ (p)` is surjective.
* `TauCeti.Perfectoid.IsPerfectoidTateRing.exists_natCast_dvd_sub_pow`: in a perfectoid Tate
  ring every element of `R°` is a `p`-th power modulo `p`.
* `TauCeti.Perfectoid.IsPerfectoidTateRing.of_bijective_frobeniusModPow`: a complete Hausdorff
  Tate ring with an open bounded subring `A₀` and a pseudouniformiser `π ∈ A₀` such that
  `π ^ p ∣ p` in `A₀` and Frobenius `A₀ ⧸ (π) → A₀ ⧸ (π ^ p)` is bijective is perfectoid
  (Bhatt–Morrow–Scholze, Lemma 3.21).

## References

* P. Scholze, *Étale cohomology of diamonds*, Definition 3.1 and Remarks 3.2–3.3.
* P. Scholze, *Perfectoid spaces*, Definition 5.1 and Proposition 5.8.
* B. Bhatt, M. Morrow, P. Scholze, *Integral p-adic Hodge theory*, Lemmas 3.9 and 3.21 and §3.2.
-/

public section

open TauCeti.Huber

namespace TauCeti.Perfectoid

section Definition

/-- A complete Hausdorff Tate ring `R` is a *perfectoid Tate ring* if (a) `R` is uniform, i.e.
the power-bounded subring `R°` is bounded, and (b) some pseudouniformiser `ϖ ∈ R°` has
`ϖ ^ p ∣ p` in `R°` and Frobenius `R° ⧸ (ϖ) → R° ⧸ (ϖ ^ p)`, `[x] ↦ [x ^ p]`, is bijective
(Scholze, *Étale cohomology of diamonds*, Definition 3.1). Condition (b) is stated elementwise:
every `x ∈ R°` is a `p`-th power modulo `ϖ ^ p`, and `ϖ ^ p ∣ y ^ p` forces `ϖ ∣ y`; see
`isPerfectoidTateRing_iff` for the form with `frobeniusModPow`. -/
class IsPerfectoidTateRing (p : ℕ) (R : Type*) [CommRing R] [UniformSpace R]
    [IsUniformAddGroup R] [IsTopologicalRing R] [IsTateRing R] [CompleteSpace R] [T2Space R] :
    Prop where
  /-- (a) `R` is uniform: the power-bounded subring `R°` is bounded. -/
  isBounded_powerBoundedSubring : IsBounded (powerBoundedSubring R : Set R)
  /-- (b) a pseudouniformiser `ϖ ∈ R°` with `ϖ ^ p ∣ p` in `R°` for which Frobenius
  `R° ⧸ (ϖ) → R° ⧸ (ϖ ^ p)` is surjective and injective. -/
  exists_pseudoUniformizer : ∃ ϖ : powerBoundedSubring R, IsPseudoUniformizer (ϖ : R) ∧
    ϖ ^ p ∣ (p : powerBoundedSubring R) ∧
    (∀ x : powerBoundedSubring R, ∃ y, ϖ ^ p ∣ x - y ^ p) ∧
    ∀ y : powerBoundedSubring R, ϖ ^ p ∣ y ^ p → ϖ ∣ y

variable (p : ℕ) {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [IsTopologicalRing R] [IsTateRing R] [CompleteSpace R] [T2Space R]

/-- A perfectoid Tate ring is uniform. -/
theorem IsPerfectoidTateRing.isUniform [IsPerfectoidTateRing p R] : IsUniform R :=
  isUniform_iff_isBounded_powerBoundedSubring.mpr
    (IsPerfectoidTateRing.isBounded_powerBoundedSubring (p := p))

/-- A perfectoid Tate ring is reduced, being a Hausdorff uniform Tate ring (Scholze,
*Perfectoid spaces*, proof of Proposition 5.8). -/
theorem IsPerfectoidTateRing.isReduced [IsPerfectoidTateRing p R] : IsReduced R :=
  have := IsPerfectoidTateRing.isUniform p (R := R)
  IsUniform.isReduced

/-- In a perfectoid Tate ring, `p` is topologically nilpotent: for `p ≠ 0`, `ϖ ^ p ∣ p` in `R°` for
a pseudouniformiser `ϖ`, and for `p = 0` the cast is `0`. -/
theorem IsPerfectoidTateRing.isTopologicallyNilpotent_natCast
    [IsPerfectoidTateRing p R] : IsTopologicallyNilpotent (p : R) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simpa using IsTopologicallyNilpotent.zero
  obtain ⟨ϖ, hϖ, ⟨c, hc⟩, -, -⟩ := IsPerfectoidTateRing.exists_pseudoUniformizer (p := p) (R := R)
  have hp' : (p : R) = (c : R) * (ϖ : R) ^ p := by
    simpa [mul_comm] using congrArg (powerBoundedSubring R).subtype hc
  rw [hp']
  exact (mem_powerBoundedSubring.mp c.property).isTopologicallyNilpotent_mul
    (hϖ.isTopologicallyNilpotent.pow hp)

variable (R) in
/-- **The zero ring is a perfectoid Tate ring**: `0` is a topologically nilpotent unit, and all
the quotients in the definition vanish. -/
theorem isPerfectoidTateRing_of_subsingleton [Subsingleton R] : IsPerfectoidTateRing p R where
  isBounded_powerBoundedSubring := isBounded_iff.mpr fun _ hU ↦ ⟨Set.univ, Filter.univ_mem,
    fun x _ ↦ Subsingleton.elim (0 : R) x ▸ mem_of_mem_nhds hU⟩
  exists_pseudoUniformizer := ⟨0, isPseudoUniformizer_iff.mpr ⟨isUnit_of_subsingleton _, .zero⟩,
    ⟨0, Subsingleton.elim _ _⟩, fun _ ↦ ⟨0, ⟨0, Subsingleton.elim _ _⟩⟩,
    fun _ _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

variable {p}

/-- **Surjectivity of Frobenius suffices**: a uniform complete Hausdorff Tate ring with a
pseudouniformiser `ϖ ∈ R°` such that `ϖ ^ p ∣ p` in `R°` and every element of `R°` is a `p`-th
power modulo `ϖ ^ p` is perfectoid; injectivity of Frobenius is automatic (Scholze, *Étale
cohomology of diamonds*, Remark 3.2). -/
theorem IsPerfectoidTateRing.of_surjective [NeZero p] [IsUniform R] (ϖ : powerBoundedSubring R)
    (hϖ : IsPseudoUniformizer (ϖ : R)) (h : ϖ ^ p ∣ (p : powerBoundedSubring R))
    (hs : ∀ x : powerBoundedSubring R, ∃ y, ϖ ^ p ∣ x - y ^ p) : IsPerfectoidTateRing p R where
  isBounded_powerBoundedSubring := IsUniform.isBounded_powerBoundedSubring
  exists_pseudoUniformizer := ⟨ϖ, hϖ, h, hs, fun _ ↦
    (IsIntegrallyClosedIn.pow_dvd_pow_iff (A := R) (NeZero.ne p) hϖ.isUnit).mp⟩

/-- **Perfectoid Tate rings via Frobenius**: `R` is perfectoid exactly when it is uniform and
some pseudouniformiser `ϖ ∈ R°` with `ϖ ^ p ∣ p` in `R°` makes Frobenius
`R° ⧸ (ϖ) → R° ⧸ (ϖ ^ p)` bijective. -/
theorem isPerfectoidTateRing_iff [Fact p.Prime] :
    IsPerfectoidTateRing p R ↔ IsUniform R ∧ ∃ ϖ : powerBoundedSubring R,
      IsPseudoUniformizer (ϖ : R) ∧ ∃ h : ϖ ^ p ∣ (p : powerBoundedSubring R),
        Function.Bijective (frobeniusModPow p h) := by
  refine ⟨fun hR ↦ ⟨hR.isUniform p, ?_⟩, fun ⟨_, ϖ, hϖ, h, hbij⟩ ↦ ?_⟩
  · obtain ⟨ϖ, hϖ, h, hs, hi⟩ := hR.exists_pseudoUniformizer
    exact ⟨ϖ, hϖ, h, (frobeniusModPow_injective_iff h).mpr hi,
      (frobeniusModPow_surjective_iff h).mpr hs⟩
  · exact .of_surjective ϖ hϖ h ((frobeniusModPow_surjective_iff h).mp hbij.2)

/-- A uniform complete Hausdorff Tate ring with a pseudouniformiser `ϖ ∈ R°` such that
`ϖ ^ p ∣ p` in `R°`, and in which every element of `R°` has a `p`-th root in `R`, is perfectoid:
the roots are power-bounded because `R°` is integrally closed in `R`. -/
theorem IsPerfectoidTateRing.of_forall_exists_pow_eq [IsUniform R]
    (ϖ : powerBoundedSubring R) (hϖ : IsPseudoUniformizer (ϖ : R))
    (h : ϖ ^ p ∣ (p : powerBoundedSubring R))
    (hroot : ∀ x : powerBoundedSubring R, ∃ y : R, y ^ p = x) : IsPerfectoidTateRing p R := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · obtain ⟨y, hy⟩ := hroot 0
    have : Subsingleton R := subsingleton_of_zero_eq_one (by simpa using hy.symm)
    exact isPerfectoidTateRing_of_subsingleton 0 R
  have : NeZero p := ⟨hp.ne'⟩
  refine .of_surjective ϖ hϖ h fun x ↦ ?_
  obtain ⟨y, hy⟩ := hroot x
  obtain ⟨z, rfl⟩ := IsIntegrallyClosedIn.exists_algebraMap_eq_of_isIntegral_pow
    (R := powerBoundedSubring R) (x := y) hp (hy ▸ isIntegral_algebraMap)
  have hx : x = z ^ p := Subtype.ext hy.symm
  refine ⟨z, ?_⟩
  rw [hx, sub_self]
  exact dvd_zero _

/-- **Perfectoid Tate rings transport along isomorphisms of topological rings.** -/
theorem IsPerfectoidTateRing.of_ringEquiv {S : Type*} [CommRing S] [UniformSpace S]
    [IsUniformAddGroup S] [IsTopologicalRing S] [IsTateRing S] [CompleteSpace S] [T2Space S]
    [IsPerfectoidTateRing p R] (e : R ≃+* S) (he : Continuous e) (he' : Continuous e.symm) :
    IsPerfectoidTateRing p S := by
  have := IsPerfectoidTateRing.isUniform p (R := R)
  have := IsUniform.of_ringEquiv e he he'
  obtain ⟨ϖ, hϖ, h, hs, hi⟩ := IsPerfectoidTateRing.exists_pseudoUniformizer (p := p) (R := R)
  set f := powerBoundedSubringEquiv e he he'
  refine ⟨IsUniform.isBounded_powerBoundedSubring, f ϖ, ?_, ?_, fun x ↦ ?_, fun y hy ↦ ?_⟩
  · rw [powerBoundedSubringEquiv_apply]
    exact hϖ.map he
  · simpa using map_dvd f h
  · obtain ⟨y, hy⟩ := hs (f.symm x)
    exact ⟨f y, by simpa using map_dvd f hy⟩
  · simpa using map_dvd f (hi (f.symm y) (by simpa using map_dvd f.symm hy))

end Definition

section FrobeniusModP

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [IsTopologicalRing R] [IsTateRing R] [CompleteSpace R] [T2Space R]

/-- **Frobenius on `R° ⧸ p` is surjective** for a perfectoid Tate ring `R`: every element of `R°`
is a `p`-th power modulo `p`. This follows from the perfectoid condition modulo `ϖ ^ p` by
successive approximation in the `ϖ`-adically complete ring `R°` (Bhatt–Morrow–Scholze,
*Integral p-adic Hodge theory*, Lemma 3.9). -/
theorem IsPerfectoidTateRing.exists_natCast_dvd_sub_pow [IsPerfectoidTateRing p R]
    (x : powerBoundedSubring R) : ∃ y, (p : powerBoundedSubring R) ∣ x - y ^ p := by
  have := IsPerfectoidTateRing.isUniform p (R := R)
  obtain ⟨ϖ, hϖ, h, hs, -⟩ := IsPerfectoidTateRing.exists_pseudoUniformizer (p := p) (R := R)
  have := IsUniform.isAdicComplete_span_singleton ϖ hϖ
  have hiff := (tfae_forall_exists_dvd_sub_pow ϖ h).out 1 2
  exact hiff.mp hs x

/-- **Perfectoid Tate rings via Frobenius modulo `p`**: a uniform complete Hausdorff Tate ring `R`
is perfectoid exactly when some pseudouniformiser `ϖ ∈ R°` has `ϖ ^ p ∣ p` in `R°` and Frobenius
on `R° ⧸ p` is surjective, that is, every element of `R°` is a `p`-th power modulo `p` (Scholze,
*Étale cohomology of diamonds*, Remark 3.2). Uniformity cannot be dropped, and neither can the
pseudouniformiser: Frobenius on `ℤ_p ⧸ p` is surjective, yet `ℚ_p` is not perfectoid. -/
theorem isPerfectoidTateRing_iff_frobenius_surjective_modP [IsUniform R] :
    IsPerfectoidTateRing p R ↔ ∃ ϖ : powerBoundedSubring R, IsPseudoUniformizer (ϖ : R) ∧
      ϖ ^ p ∣ (p : powerBoundedSubring R) ∧
        ∀ x : powerBoundedSubring R, ∃ y, (p : powerBoundedSubring R) ∣ x - y ^ p := by
  refine ⟨fun _ ↦ ?_, fun ⟨ϖ, hϖ, h, hs⟩ ↦
    .of_surjective ϖ hϖ h fun x ↦ (hs x).imp fun _ ↦ h.trans⟩
  obtain ⟨ϖ, hϖ, h, -, -⟩ := IsPerfectoidTateRing.exists_pseudoUniformizer (p := p) (R := R)
  exact ⟨ϖ, hϖ, h, IsPerfectoidTateRing.exists_natCast_dvd_sub_pow⟩

end FrobeniusModP

section RingOfDefinition

variable {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R] [UniformSpace R] [IsTopologicalRing R]
  [IsTateRing R]

/-- Let `A₀ ⊆ R°` be a subring and `π ∈ A₀` a unit of `R`, associated in `A₀` to a `p`-th power
`t ^ p`, such that `π R° ⊆ A₀` and every element of `A₀` is a `p`-th power modulo `π p`. Then every
element of `R°` is a `p`-th power modulo `p`: if `π x ≡ y ^ p` modulo `π p`, then
`x ≡ (y / t) ^ p` modulo `p`. -/
private theorem exists_natCast_dvd_sub_pow_of_mul_mem {A₀ : Subring R}
    (hA₀ : ∀ a : A₀, IsPowerBounded (a : R)) {π t : A₀} {u : A₀ˣ} (hπ : IsUnit (π : R))
    (hu : π * u = t ^ p) (hmem : ∀ x : R, IsPowerBounded x → (π : R) * x ∈ A₀)
    (hs : ∀ a : A₀, ∃ y, π * p ∣ a - y ^ p) (x : powerBoundedSubring R) :
    ∃ y, (p : powerBoundedSubring R) ∣ x - y ^ p := by
  have hp : p.Prime := Fact.out
  have hu' : (π : R) * (u : A₀) = (t : R) ^ p := by
    rw [← Subring.coe_mul, hu, Subring.coe_pow]
  have hT : IsUnit ((t : R) ^ p) := hu' ▸ hπ.mul ((u.isUnit).map A₀.subtype)
  obtain ⟨y, c, hc⟩ := hs ⟨_, hmem _ ((hA₀ u).mul (mem_powerBoundedSubring.mp x.property))⟩
  have hc' : (π : R) * (u : A₀) * x - (y : R) ^ p = π * p * c := by
    simpa [mul_assoc] using congrArg Subtype.val hc
  have hTt : IsUnit (t : R) := (isUnit_pow_iff hp.ne_zero).mp hT
  set z : R := y * ↑hTt.unit⁻¹
  have hz : (t : R) * z = y := by rw [mul_left_comm, hTt.mul_val_inv, mul_one]
  set d : R := c * ((u⁻¹ : A₀ˣ) : A₀)
  have hd : d ∈ A₀ := A₀.mul_mem c.property ((u⁻¹ : A₀ˣ) : A₀).property
  have hzd : z ^ p = x - p * d := by
    have hud : ((u : A₀) : R) * ((u⁻¹ : A₀ˣ) : A₀) = 1 := by
      rw [← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
    refine hT.mul_left_cancel ?_
    rw [← mul_pow, hz, ← hu']
    linear_combination (-1 : R) * hc' + (π : R) * p * c * hud
  have hpd : (p : R) * d ∈ powerBoundedSubring R :=
    mem_powerBoundedSubring.mpr (hA₀ ⟨_, A₀.mul_mem (natCast_mem A₀ p) hd⟩)
  have hzb : z ∈ powerBoundedSubring R := mem_powerBoundedSubring.mpr <|
    IsPowerBounded.of_pow hp.ne_zero (hzd ▸ mem_powerBoundedSubring.mp (sub_mem x.property hpd))
  exact ⟨⟨z, hzb⟩, ⟨d, mem_powerBoundedSubring.mpr (hA₀ ⟨d, hd⟩)⟩, Subtype.ext (by simp [hzd])⟩

variable [IsUniformAddGroup R] [CompleteSpace R] [T2Space R]

/-- **Perfectoid Tate rings from a ring of definition with bijective Frobenius**
(Bhatt–Morrow–Scholze, *Integral p-adic Hodge theory*, Lemma 3.21). Let `R` be a complete
Hausdorff Tate ring, `A₀ ⊆ R` an open bounded subring and `π ∈ A₀` a pseudouniformiser of `R` with
`π ^ p ∣ p` in `A₀` such that Frobenius `A₀ ⧸ (π) → A₀ ⧸ (π ^ p)` is bijective. Then `R` is a
perfectoid Tate ring. By `TauCeti.Perfectoid.IsIntegralPerfectoid.of_bijective_frobeniusModPow`,
such an `A₀` is an integral perfectoid ring; `A₀` need not be integrally closed in `R`, but
`π R° ⊆ A₀` (`TauCeti.Huber.mul_mem_of_isPowerBounded_of_pow_dvd_pow`). -/
theorem IsPerfectoidTateRing.of_bijective_frobeniusModPow {A₀ : Subring R}
    (hA₀o : IsOpen (A₀ : Set R)) (hA₀b : IsBounded (A₀ : Set R)) {π : A₀}
    (hπ : IsPseudoUniformizer (π : R)) (h : π ^ p ∣ (p : A₀))
    (hbij : Function.Bijective (frobeniusModPow p h)) : IsPerfectoidTateRing p R := by
  have hp : p.Prime := Fact.out
  have hinj := (frobeniusModPow_injective_iff h).mp hbij.1
  have := isUniform_of_pow_dvd_pow hA₀o hA₀b hπ hp.one_lt hinj
  have := A₀.isAdicComplete_span_singleton hA₀o hA₀b π hπ
  -- every element of `A₀` is a `p`-th power modulo `π p`
  have hs := exists_mul_dvd_sub_pow ((frobeniusModPow_surjective_iff h).mp hbij.2)
  have hA₀ (a : A₀) : IsPowerBounded (a : R) := hA₀b.isPowerBounded_of_mem a.property
  -- `π` is associated to a `p`-th power `t ^ p`, since `p` lies in the Jacobson radical of `A₀`
  obtain ⟨t, ht⟩ := hs π
  have hp_jac : (p : A₀) ∈ (⊥ : Ideal A₀).jacobson := by
    rw [Ideal.jacobson_bot]
    exact IsAdicComplete.le_jacobson _
      (Ideal.mem_span_singleton.mpr ((dvd_pow_self π hp.ne_zero).trans h))
  obtain ⟨u, hu⟩ := associated_of_mul_dvd_sub_of_mem_jacobson hp_jac (dvd_sub_comm.mp ht)
  -- the pseudouniformiser `ϖ = t ^ p = u π ∈ R°` has `ϖ ^ p ∣ p`
  let ϖ : powerBoundedSubring R := ⟨(t : R) ^ p, mem_powerBoundedSubring.mpr ((hA₀ t).pow p)⟩
  have hϖu : (ϖ : R) = (u : A₀) * π := by
    rw [mul_comm, ← Subring.coe_mul, hu, Subring.coe_pow]
  have hϖ : IsPseudoUniformizer (ϖ : R) := hϖu ▸ isPseudoUniformizer_iff.mpr
    ⟨(u.isUnit.map A₀.subtype).mul hπ.isUnit,
      (hA₀ u).isTopologicallyNilpotent_mul hπ.isTopologicallyNilpotent⟩
  have hϖp : ϖ ^ p ∣ (p : powerBoundedSubring R) := by
    obtain ⟨c, hc⟩ := (Associated.pow_pow (n := p) ⟨u, hu⟩).symm.dvd.trans h
    refine ⟨⟨c, mem_powerBoundedSubring.mpr (hA₀ c)⟩, Subtype.ext ?_⟩
    simpa using congrArg Subtype.val hc
  exact isPerfectoidTateRing_iff_frobenius_surjective_modP.mpr ⟨ϖ, hϖ, hϖp,
    exists_natCast_dvd_sub_pow_of_mul_mem hA₀ hπ.isUnit hu
      (fun _ ↦ mul_mem_of_isPowerBounded_of_pow_dvd_pow hA₀o hπ hp.one_lt hinj) hs⟩

end RingOfDefinition

section Prod

variable {p : ℕ} {R S : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [IsTopologicalRing R] [IsTateRing R] [CompleteSpace R] [T2Space R] [CommRing S] [UniformSpace S]
  [IsUniformAddGroup S] [IsTopologicalRing S] [IsTateRing S] [CompleteSpace S] [T2Space S]

/-- The first factor of a perfectoid product is perfectoid: the first component of a
pseudouniformiser of `R × S` witnessing the perfectoid condition witnesses it for `R`. -/
private theorem IsPerfectoidTateRing.of_prod_left [IsPerfectoidTateRing p (R × S)] :
    IsPerfectoidTateRing p R := by
  have := IsPerfectoidTateRing.isUniform p (R := R × S)
  have : IsUniform R := (isUniform_prod_iff.mp ‹_›).1
  obtain ⟨ϖ, hϖ, h, hs, hi⟩ := IsPerfectoidTateRing.exists_pseudoUniformizer (p := p) (R := R × S)
  refine ⟨IsUniform.isBounded_powerBoundedSubring, (powerBoundedSubringProdEquiv R S ϖ).1, ?_, ?_,
    fun x ↦ ?_, fun y hy ↦ ?_⟩
  · simpa using (isPseudoUniformizer_prod_iff.mp hϖ).1
  · simpa using (dvd_iff_powerBoundedSubringProdEquiv.mp h).1
  · obtain ⟨y, hy⟩ := hs ((powerBoundedSubringProdEquiv R S).symm (x, 0))
    exact ⟨(powerBoundedSubringProdEquiv R S y).1,
      by simpa using (dvd_iff_powerBoundedSubringProdEquiv.mp hy).1⟩
  · -- test the injectivity condition of `R × S` on `(y, 0)`
    have hdvd : ϖ ^ p ∣ ((powerBoundedSubringProdEquiv R S).symm (y, 0)) ^ p :=
      dvd_iff_powerBoundedSubringProdEquiv.mpr ⟨by simpa using hy,
        by simpa using pow_dvd_pow_of_dvd (dvd_zero (powerBoundedSubringProdEquiv R S ϖ).2) p⟩
    simpa using (dvd_iff_powerBoundedSubringProdEquiv.mp (hi _ hdvd)).1

/-- **A product of perfectoid Tate rings is perfectoid**, directly from the definition: if `ϖ_R` and
`ϖ_S` witness the perfectoid condition for `R` and `S`, then `(ϖ_R, ϖ_S)` witnesses it for `R × S`,
because `(R × S)° = R° × S°` and divisibility in it is componentwise. -/
instance IsPerfectoidTateRing.prod [IsPerfectoidTateRing p R] [IsPerfectoidTateRing p S] :
    IsPerfectoidTateRing p (R × S) := by
  have := IsPerfectoidTateRing.isUniform p (R := R)
  have := IsPerfectoidTateRing.isUniform p (R := S)
  obtain ⟨ϖ, hϖ, h, hs, hi⟩ := IsPerfectoidTateRing.exists_pseudoUniformizer (p := p) (R := R)
  obtain ⟨ϖ', hϖ', h', hs', hi'⟩ :=
    IsPerfectoidTateRing.exists_pseudoUniformizer (p := p) (R := S)
  refine ⟨IsUniform.isBounded_powerBoundedSubring, (powerBoundedSubringProdEquiv R S).symm (ϖ, ϖ'),
    ?_, ?_, fun x ↦ ?_, fun y hy ↦ ?_⟩
  · exact isPseudoUniformizer_prod_iff.mpr ⟨by simpa using hϖ, by simpa using hϖ'⟩
  · exact dvd_iff_powerBoundedSubringProdEquiv.mpr ⟨by simpa using h, by simpa using h'⟩
  · obtain ⟨y, hy⟩ := hs (powerBoundedSubringProdEquiv R S x).1
    obtain ⟨y', hy'⟩ := hs' (powerBoundedSubringProdEquiv R S x).2
    exact ⟨(powerBoundedSubringProdEquiv R S).symm (y, y'),
      dvd_iff_powerBoundedSubringProdEquiv.mpr ⟨by simpa using hy, by simpa using hy'⟩⟩
  · obtain ⟨hy, hy'⟩ := dvd_iff_powerBoundedSubringProdEquiv.mp hy
    exact dvd_iff_powerBoundedSubringProdEquiv.mpr
      ⟨by simpa using hi _ (by simpa using hy), by simpa using hi' _ (by simpa using hy')⟩

/-- **A product is perfectoid exactly when both factors are**: for complete Hausdorff Tate rings
`R` and `S`, `R × S` is a perfectoid Tate ring exactly when `R` and `S` are. -/
@[simp]
theorem isPerfectoidTateRing_prod_iff :
    IsPerfectoidTateRing p (R × S) ↔ IsPerfectoidTateRing p R ∧ IsPerfectoidTateRing p S := by
  -- the second factor is handled by swapping the factors, an isomorphism of topological rings
  refine ⟨fun _ ↦ ⟨.of_prod_left (S := S), ?_⟩, fun ⟨_, _⟩ ↦ inferInstance⟩
  have : IsPerfectoidTateRing p (S × R) :=
    .of_ringEquiv (RingEquiv.prodComm (R := R) (S := S)) continuous_swap continuous_swap
  exact .of_prod_left (S := R)

end Prod

end TauCeti.Perfectoid
