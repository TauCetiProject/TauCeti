/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Transgression
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Frattini

/-!
# Transgression for extensions inside the Frattini subgroup

Let `G` be a profinite group, `p` a prime, and `N` a closed normal subgroup contained in the
pro-`p` Frattini subgroup `Φ(G) = proPFrattini p G`. Let `M` be a discrete abelian group killed
by `p` on which `G` acts trivially, for instance `𝔽_p`. Then every continuous `1`-cocycle on `G`
with values in `M` is a continuous homomorphism to an elementary abelian `p`-group, so it
vanishes on `Φ(G)` and hence on `N`: **restriction `H¹(G, M) → H¹(N, M)` is zero**. By exactness
of the five-term sequence

```text
0 → H¹(G ⧸ N, M ^ N) → H¹(G, M) → H¹(N, M) ^ (G ⧸ N) → H²(G ⧸ N, M ^ N) → H²(G, M),
```

the transgression `H¹(N, M) ^ (G ⧸ N) → H²(G ⧸ N, M ^ N)` is then injective, and it is
bijective as soon as `H²(G, M)` vanishes.

The free pro-`p` specialization is in `TauCeti.Topology.Algebra.Group.Profinite.Free.Transgression`.

## Main results

* `TauCeti.explicitRes1_eq_zero_of_le_proPFrattini`: restriction on `H¹` with trivial
  coefficients killed by `p` vanishes on a subgroup of the pro-`p` Frattini subgroup.
* `TauCeti.transgression_injective_of_le_proPFrattini`: the transgression of such a subgroup is
  injective.
* `TauCeti.transgression_bijective_of_le_proPFrattini`: it is bijective when `H²(G, M) = 0`.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.9.5).
* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), §1.4.
* J.-P. Serre, *Galois Cohomology*, Chapter I, §4.3.
-/

public section

namespace TauCeti

open ContCohomology

universe u v

variable {p : ℕ} [Fact p.Prime]

section Frattini

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]
  {M : Type v} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]

omit [ContinuousSMul G M] in
/-- A continuous `1`-cocycle for a trivial action on a discrete group killed by `p` vanishes on
the pro-`p` Frattini subgroup: it is a continuous homomorphism to an elementary abelian group
(`TauCeti.ContCohomology.Z1EquivOfSmulEqSelf`). -/
private theorem apply_eq_zero_of_mem_proPFrattini (htriv : ∀ (g : G) (m : M), g • m = m)
    (hpM : ∀ m : M, p • m = 0) (c : Z1 G M) {g : G} (hg : g ∈ proPFrattini p G) :
    (c : G → M) g = 0 := by
  let φ := Additive.toMul (Z1EquivOfSmulEqSelf htriv c)
  have hker : IsClosed (φ.toMonoidHom.ker : Set G) := by
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage φ.continuous
  have hexp : Monoid.exponent (Multiplicative M) ∣ p :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x ↦ by
      rw [← ofAdd_toAdd x, ← ofAdd_nsmul, hpM, ofAdd_zero]
  have h := MonoidHom.mem_ker.mp
    (proPFrattini_le_ker_of_exponent_dvd Fact.out φ.toMonoidHom hker hexp hg)
  simpa [φ] using h

/-- **Restriction to a subgroup of the Frattini subgroup vanishes.** For a profinite group `G`,
a subgroup `N ≤ proPFrattini p G`, and a discrete abelian group `M` killed by `p` with trivial
action, restriction `H¹(G, M) → H¹(N, M)` is zero. -/
theorem explicitRes1_eq_zero_of_le_proPFrattini {N : Subgroup G}
    (hN : N ≤ proPFrattini p G) (htriv : ∀ (g : G) (m : M), g • m = m)
    (hpM : ∀ m : M, p • m = 0) : explicitRes1 G M N = 0 := by
  refine AddMonoidHom.ext fun x ↦ ?_
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    rw [explicitRes1_mk, AddMonoidHom.zero_apply, H1pi_eq_zero_iff]
    convert zero_mem (B1 N M) using 1
    funext n
    simpa only [cocyclesMap1_apply, ContinuousMonoidHom.subgroupSubtype_apply,
      AddMonoidHom.id_apply, Pi.zero_apply] using
      apply_eq_zero_of_mem_proPFrattini htriv hpM c (hN n.2)

variable {N : Subgroup G} [N.Normal]

/-- **Transgression is injective below the Frattini subgroup.** For a closed normal subgroup
`N ≤ proPFrattini p G` of a profinite group and a discrete abelian group `M` killed by `p` with
trivial action, the transgression `H¹(N, M) ^ (G ⧸ N) → H²(G ⧸ N, M ^ N)` is injective. -/
theorem transgression_injective_of_le_proPFrattini (hNc : IsClosed (N : Set G))
    (hN : N ≤ proPFrattini p G) (htriv : ∀ (g : G) (m : M), g • m = m)
    (hpM : ∀ m : M, p • m = 0) : Function.Injective (transgression G M N hNc) := by
  refine (transgression_injective_iff G M N hNc).2 (AddMonoidHom.ext fun x ↦ Subtype.ext ?_)
  simp [coe_explicitResConj1, explicitRes1_eq_zero_of_le_proPFrattini hN htriv hpM]

/-- **Transgression is bijective below the Frattini subgroup when `H²(G, M)` vanishes.** For a
closed normal subgroup `N ≤ proPFrattini p G` of a profinite group and a discrete abelian group
`M` killed by `p` with trivial action and `H²(G, M) = 0`, the transgression
`H¹(N, M) ^ (G ⧸ N) → H²(G ⧸ N, M ^ N)` is bijective. -/
theorem transgression_bijective_of_le_proPFrattini [Subsingleton (H2 G M)]
    (hNc : IsClosed (N : Set G)) (hN : N ≤ proPFrattini p G)
    (htriv : ∀ (g : G) (m : M), g • m = m) (hpM : ∀ m : M, p • m = 0) :
    Function.Bijective (transgression G M N hNc) :=
  ⟨transgression_injective_of_le_proPFrattini hNc hN htriv hpM,
    (transgression_surjective_iff G M N hNc).2 (AddMonoidHom.ext fun _ ↦ Subsingleton.elim _ _)⟩

end Frattini

end TauCeti
