/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Lagrange
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Order
public import TauCeti.Topology.Algebra.Group.Profinite.Sylow.Basic
import Mathlib.Topology.Separation.Connected

/-!
# The order of a Sylow pro-`p` subgroup

A Sylow pro-`p` subgroup `P` of a profinite group `G` carries the whole `p`-part of the
supernatural order of `G`: its order is the `p`-primary part of `profiniteOrder G`. At `p` this
is Lagrange's theorem, since the index of `P` is prime to `p`; away from `p` both sides vanish,
because `P` is pro-`p`.

The degenerate case of this formula is a prime `p` that does not divide the order of `G`. Then
every Sylow pro-`p` subgroup is trivial, and conversely the trivial subgroup is Sylow pro-`p`
exactly for such primes.

## Main results

* `TauCeti.IsProPSylow.profiniteOrder_eq`: the order of a Sylow pro-`p` subgroup is the
  `p`-primary part of the order of the group.
* `TauCeti.IsProPSylow.eq_bot_iff`: a Sylow pro-`p` subgroup is trivial exactly when `p` does not
  divide the order of the group.
* `TauCeti.isProPSylow_bot_iff`: the trivial subgroup is Sylow pro-`p` exactly when `p` does not
  divide the order of the group.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.3.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {P : Subgroup G}

/-- **The order of a Sylow pro-`p` subgroup is the `p`-part of the order of the group.** For a
Sylow pro-`q` subgroup `P` of a profinite group `G`, the supernatural order of `P` is the
`q`-primary part of the supernatural order of `G`. -/
theorem IsProPSylow.profiniteOrder_eq {q : Nat.Primes} (hP : IsProPSylow q P) :
    profiniteOrder P = Supernatural.primaryPart q (profiniteOrder G) := by
  have : Fact (q : ℕ).Prime := ⟨q.prop⟩
  have : CompactSpace P := isCompact_iff_compactSpace.mp hP.isClosed.isCompact
  obtain ⟨hclosed, hpro, hindex⟩ :=
    (isProPSylow_iff_isClosed_and_isProP_and_not_dvd_profiniteIndex q).mp hP
  ext ℓ
  by_cases hℓ : ℓ = q
  · subst hℓ
    rw [Supernatural.coe_prime_dvd_iff, not_not] at hindex
    rw [Supernatural.primaryPart_apply_self, P.profiniteOrder_apply_eq_add_profiniteIndex hclosed,
      hindex, add_zero]
  · rw [Supernatural.primaryPart_apply_of_ne hℓ]
    exact isProP_iff_profiniteOrder_apply_eq_zero.mp hpro ℓ fun h ↦ hℓ (Subtype.ext h)

/-- **A Sylow pro-`p` subgroup is trivial exactly when `p` does not divide the order.** A Sylow
pro-`q` subgroup of a profinite group `G` is trivial if and only if the exponent of `q` in the
supernatural order of `G` is zero. -/
theorem IsProPSylow.eq_bot_iff {q : Nat.Primes} (hP : IsProPSylow q P) :
    P = ⊥ ↔ profiniteOrder G q = 0 := by
  have : CompactSpace P := isCompact_iff_compactSpace.mp hP.isClosed.isCompact
  rw [← not_ne_iff, ← P.nontrivial_iff_ne_bot, not_nontrivial_iff_subsingleton,
    ← profiniteOrder_eq_bot_iff, hP.profiniteOrder_eq, Supernatural.primaryPart_eq_bot_iff]

/-- **The trivial subgroup is Sylow pro-`p` exactly when `p` does not divide the order.** The
trivial subgroup of a profinite group `G` is a Sylow pro-`q` subgroup if and only if the exponent
of `q` in the supernatural order of `G` is zero. -/
@[simp]
theorem isProPSylow_bot_iff (q : Nat.Primes) :
    IsProPSylow q (⊥ : Subgroup G) ↔ profiniteOrder G q = 0 := by
  refine ⟨fun h ↦ h.eq_bot_iff.mp rfl, fun h ↦ ?_⟩
  have hclosed : IsClosed ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.coe_bot]
    exact isClosed_singleton
  refine (isProPSylow_iff_isClosed_and_isProP_and_not_dvd_profiniteIndex q).mpr
    ⟨hclosed, IsPGroup.of_bot.isProP, ?_⟩
  rw [Supernatural.coe_prime_dvd_iff, not_not]
  have hlagrange := (⊥ : Subgroup G).profiniteOrder_apply_eq_add_profiniteIndex hclosed q
  rw [h] at hlagrange
  exact (add_eq_zero.mp hlagrange.symm).2

end TauCeti
