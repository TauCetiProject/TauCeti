/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.RingTheory.RamificationInertia.Basic

/-!
# Ramification indices in finite flat towers

This file records consequences of the fundamental identity for ramification and inertia in a finite
flat extension of domains. The number of primes above a prime and each prime's contribution are at
most the rank of the extension. Ramification also cancels in a tower: by multiplicativity, the
relative ramification index is one exactly when the absolute ramification index at the top equals
the absolute ramification index at the intermediate prime. Where the residue field extensions are
separable, relative ramification index one is relative unramifiedness.

The cancellation result is the local step used in the finite-place half of the genus-field
construction. At a rational prime dividing a prime discriminant, both the quadratic base and the
prime-discriminant compositum have absolute ramification index two; cancellation then shows that
the compositum is unramified over the quadratic base.

## Main results

* `TauCeti.RamificationInertia.ncard_primesOver_le_finrank`: the number of primes above a prime is
  at most the rank of a finite flat extension.
* `TauCeti.RamificationInertia.ramificationIdx_mul_inertiaDeg_le_finrank`: the contribution of one
  prime to the fundamental identity is at most the rank of the extension.
* `TauCeti.RamificationInertia.ramificationIdx_le_finrank`: a ramification index is at most the
  rank of a finite flat extension.
* `TauCeti.RamificationInertia.ramificationIdx_eq_one_iff_ramificationIdx_eq`: the relative
  ramification index in a tower is one if and only if the absolute ramification indices at the
  two levels agree.
* `TauCeti.RamificationInertia.isUnramifiedIn_of_forall_eq_ramificationIdx`: if that equality
  holds at every prime above an intermediate prime with separable residue field extensions, then
  the intermediate prime is unramified in the top ring.
* `TauCeti.RamificationInertia.isUnramifiedIn_of_forall_ramificationIdx_le`: it suffices to bound
  every absolute ramification index upstairs by the intermediate absolute ramification index.
* `TauCeti.RamificationInertia.isUnramifiedIn_of_finrank_le_of_under_ramificationIdx_eq_one`: a
  transverse unramified subextension of sufficiently small relative degree supplies that bound.
* `TauCeti.RamificationInertia.isUnramifiedAt_of_isUnramifiedIn`: unramifiedness over the
  base descends from an integral extension to the subring below it, for `S` integral and
  torsion-free over the Dedekind domain `R`, with `R` and `S` both essentially of finite type over
  the base `A` and `A ≤ R ≤ S` a scalar tower. The base ring and the ideal are arbitrary.
-/

public section

open Ideal Module

namespace TauCeti.RamificationInertia

section Bounds

variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
  [Module.Finite R S] [Module.Flat R S]

/-- **There are at most `Module.finrank R S` primes above a prime.** Every ramification index and
inertia degree in the fundamental identity is positive, so every prime above `p` contributes at
least one to the rank. -/
theorem ncard_primesOver_le_finrank (p : Ideal R) :
    (p.primesOver S).ncard ≤ finrank R S := by
  by_cases hp : p.IsPrime
  swap
  · have : p.primesOver S = ∅ := Set.eq_empty_of_forall_notMem fun P hP ↦
      hp (hP.2.over.symm ▸ hP.1.under R)
    simp [this]
  have : Fintype (p.primesOver S) := (Algebra.QuasiFinite.finite_primesOver p).fintype
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Fintype.card_eq_sum_ones,
    ← Ideal.sum_ramification_inertia_eq_finrank p S]
  refine Finset.sum_le_sum fun q _ ↦ ?_
  have : q.1.IsPrime := q.2.1
  exact Nat.succ_le_of_lt (Nat.mul_pos (q.1.ramificationIdx_pos R) (q.1.inertiaDeg_pos R))

variable (R) in
/-- **One prime's contribution to the fundamental identity is at most the extension rank.**
For a prime `q` of `S`, the product of its ramification index and inertia degree over `R` is at
most `Module.finrank R S`. -/
theorem ramificationIdx_mul_inertiaDeg_le_finrank (q : Ideal S) [q.IsPrime] :
    q.ramificationIdx R * q.inertiaDeg R ≤ finrank R S := by
  have : Fintype ((q.under R).primesOver S) :=
    (Algebra.QuasiFinite.finite_primesOver (q.under R)).fintype
  rw [← Ideal.sum_ramification_inertia_eq_finrank (q.under R) S]
  exact Finset.single_le_sum (f := fun Q : (q.under R).primesOver S ↦
    Q.1.ramificationIdx R * Q.1.inertiaDeg R) (fun _ _ ↦ Nat.zero_le _)
    (Finset.mem_univ ⟨q, inferInstance, inferInstance⟩)

variable (R) in
/-- **A ramification index is at most the rank of a finite flat extension.** For a prime `q` of
`S`, `e(q / R) ≤ Module.finrank R S`. -/
theorem ramificationIdx_le_finrank (q : Ideal S) [q.IsPrime] :
    q.ramificationIdx R ≤ finrank R S :=
  (Nat.le_mul_of_pos_right _ (q.inertiaDeg_pos R)).trans
    (ramificationIdx_mul_inertiaDeg_le_finrank R q)

end Bounds

section Tower

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  [Algebra S T] [IsScalarTower R S T] [Module.Finite R S] [Module.Flat S T]

/-- **Ramification-index cancellation in a tower.** Let `r` be a prime of `T` above a prime `q`
of `S`. The relative ramification index `e(r / q)` is one if and only if the absolute
ramification indices of `r` and `q` over `R` agree, by multiplicativity
`e(r / R) = e(q / R) * e(r / S)` and positivity of `e(q / R)` in a finite extension. -/
theorem ramificationIdx_eq_one_iff_ramificationIdx_eq (q : Ideal S) (r : Ideal T)
    [q.IsPrime] [r.LiesOver q] :
    r.ramificationIdx S = 1 ↔ r.ramificationIdx R = q.ramificationIdx R := by
  rw [Ideal.ramificationIdx_tower (R := R) q r, Nat.mul_eq_left (q.ramificationIdx_pos R).ne']

/-- **Absolute ramification-index equality implies relative unramifiedness.** Let `q` be a prime
of `S` with separable residue field extensions above it. If every prime `r` of `T` above `q` has
the same absolute ramification index over `R` as `q`, then `q` is unramified in `T`. This is the
all-primes form of `ramificationIdx_eq_one_iff_ramificationIdx_eq`. -/
theorem isUnramifiedIn_of_forall_eq_ramificationIdx [Algebra.EssFiniteType S T] (q : Ideal S)
    [q.IsPrime] [Algebra.HasSeparableResidueFieldsAt S T q]
    (h : ∀ (r : Ideal T) [r.IsPrime], r.LiesOver q →
      r.ramificationIdx R = q.ramificationIdx R) : Algebra.IsUnramifiedIn T q := by
  intro r _ hr
  have he := (ramificationIdx_eq_one_iff_ramificationIdx_eq q r).mpr (h r hr)
  obtain ⟨rfl⟩ := hr
  exact Ideal.ramificationIdx_eq_one_iff.mp he

/-- **No increase in absolute ramification implies relative unramifiedness.** Let `q` be a prime
of `S` with separable residue field extensions above it. If every prime `r` of `T` above `q` has
absolute ramification index at most that of `q`, then `q` is unramified in `T`. The reverse
inequality is automatic from multiplicativity in the tower, so the absolute indices are equal and
`isUnramifiedIn_of_forall_eq_ramificationIdx` applies. -/
theorem isUnramifiedIn_of_forall_ramificationIdx_le [Module.Finite S T] (q : Ideal S)
    [q.IsPrime] [Algebra.HasSeparableResidueFieldsAt S T q]
    (h : ∀ (r : Ideal T) [r.IsPrime], r.LiesOver q →
      r.ramificationIdx R ≤ q.ramificationIdx R) : Algebra.IsUnramifiedIn T q := by
  have := Module.Finite.trans (R := R) S T
  refine isUnramifiedIn_of_forall_eq_ramificationIdx (R := R) q fun r _ hr ↦ ?_
  exact (h r hr).antisymm (Ideal.ramificationIdx_below_le (R := R) q r)

/-- **A transverse unramified subextension cancels the base ramification.** Suppose `T` is also an
extension of a domain `U` over `R`. Let `q` be a prime of `S` with separable residue field
extensions above it, assume `Module.finrank U T ≤ e(q / R)`, and assume that for every prime `r`
above `q`, its contraction to `U` has absolute ramification index one. Then `q` is unramified in
`T`.

Indeed, the tower through `U` identifies `e(r / R)` with `e(r / U)`, which is at most
`Module.finrank U T`; hence `e(r / R) ≤ e(q / R)`, and
`isUnramifiedIn_of_forall_ramificationIdx_le` applies. For a biquadratic compositum at a shared
ramified prime, `S / R` has ramification index two while `T / U` has degree two. -/
theorem isUnramifiedIn_of_finrank_le_of_under_ramificationIdx_eq_one [Module.Finite S T]
    {U : Type*} [CommRing U] [IsDomain U] [Algebra R U] [Algebra U T] [IsScalarTower R U T]
    [Module.Finite U T] [Module.Flat U T] (q : Ideal S) [q.IsPrime]
    [Algebra.HasSeparableResidueFieldsAt S T q] (hrank : finrank U T ≤ q.ramificationIdx R)
    (hunr : ∀ (r : Ideal T) [r.IsPrime], r.LiesOver q →
      (r.under U).ramificationIdx R = 1) : Algebra.IsUnramifiedIn T q := by
  refine isUnramifiedIn_of_forall_ramificationIdx_le (R := R) q fun r _ hr ↦ ?_
  calc
    r.ramificationIdx R = (r.under U).ramificationIdx R * r.ramificationIdx U :=
      Ideal.ramificationIdx_tower (R := R) (r.under U) r
    _ = r.ramificationIdx U := by rw [hunr r hr, one_mul]
    _ ≤ finrank U T := ramificationIdx_le_finrank U r
    _ ≤ q.ramificationIdx R := hrank

end Tower

section Descent

variable {A R S : Type*} [CommRing A] [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDomain S]
  [Algebra A R] [Algebra A S] [Algebra R S] [IsScalarTower A R S] [Algebra.IsIntegral R S]
  [Module.IsTorsionFree R S] [Algebra.EssFiniteType A R] [Algebra.EssFiniteType A S]

-- Source. Recovered from the retired PR #5538, at commit
-- 70421db267d9bd6252256f873d27e99e739a931c.

/-- **Unramifiedness descends to a subring.** If an ideal `I` of the base `A` is unramified in `S`,
then every prime of an intermediate ring `R` lying over `I` is unramified over `A`. The direction
is descent, not ascent: the hypothesis is upstairs and the conclusion downstairs.

`A` and `I` are arbitrary; the hypotheses that carry the argument are the ambient ones on `R` and
`S`. Its number-field instance is `NumberField.isUnramifiedAway_of_intermediateField`, which
quantifies it over the places outside a finite set. -/
theorem isUnramifiedAt_of_isUnramifiedIn {I : Ideal A} (hur : Algebra.IsUnramifiedIn S I)
    (𝔮 : Ideal R) [𝔮.IsPrime] [𝔮.LiesOver I] :
    Algebra.IsUnramifiedAt A 𝔮 := by
  obtain ⟨P, _, _⟩ := (inferInstance : Nonempty (𝔮.primesOver S))
  have : Algebra.IsUnramifiedAt A P := hur P ‹_› (.trans P 𝔮 I)
  exact .of_liesOver A 𝔮 P

end Descent

end TauCeti.RamificationInertia
