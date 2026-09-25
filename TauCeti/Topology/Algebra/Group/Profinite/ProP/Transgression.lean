/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Transgression
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Cohomology
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

The case of interest is a minimal presentation `1 → R → F → G → 1` of a pro-`p` group: `F` is a
free pro-`p` group, whose `H²` with finite `p`-primary coefficients vanishes
(`TauCeti.freeProP.subsingleton_H2`), and `R ≤ Φ(F)`, which for a finite generating type
characterizes the presentations with the minimal number of generators
(`TauCeti.presentedProP.subset_proPFrattini_iff_card_eq`). For such a presentation the
transgression identifies the `F`-invariant classes of `H¹(R, 𝔽_p)` with `H²(F ⧸ R, 𝔽_p)`. This
is the first step of the interpretation of `dim H²(G, 𝔽_p)` as the number of relations of `G`.

## Main results

* `TauCeti.explicitRes1_eq_zero_of_le_proPFrattini`: restriction on `H¹` with trivial
  coefficients killed by `p` vanishes on a subgroup of the pro-`p` Frattini subgroup.
* `TauCeti.transgression_injective_of_le_proPFrattini`: the transgression of such a subgroup is
  injective.
* `TauCeti.transgression_bijective_of_le_proPFrattini`: it is bijective when `H²(G, M) = 0`.
* `TauCeti.freeProP.transgression_bijective`: **for a closed normal subgroup `R` of a free
  pro-`p` group `F` with `R ≤ Φ(F)`, the transgression
  `H¹(R, M) ^ (F ⧸ R) → H²(F ⧸ R, M ^ R)` is bijective**, for every finite abelian group `M` of
  exponent dividing `p` with trivial action.

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

namespace freeProP

variable {X : Type u} {M : Type u} [CommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [Finite M] [MulDistribMulAction (freeProP p X) M] [ContinuousSMul (freeProP p X) M]

/-- **The transgression of a minimal presentation is an isomorphism.** Let `F = freeProP p X`
and let `R` be a closed normal subgroup of `F` contained in its pro-`p` Frattini subgroup, as for
the relation subgroup of a minimal presentation. For a finite abelian group `M` of exponent
dividing `p` with trivial `F`-action, for instance `𝔽_p`, the transgression
`H¹(R, M) ^ (F ⧸ R) → H²(F ⧸ R, M ^ R)` is bijective. -/
theorem transgression_bijective (R : Subgroup (freeProP p X)) [R.Normal]
    (hRc : IsClosed (R : Set (freeProP p X))) (hR : R ≤ proPFrattini p (freeProP p X))
    (htriv : ∀ (g : freeProP p X) (m : M), g • m = m) (hexp : ∀ m : M, m ^ p = 1) :
    Function.Bijective (transgression (freeProP p X) (Additive M) R hRc) :=
  haveI := subsingleton_H2 (X := X) (IsPGroup.isProP (p := p) fun m ↦ ⟨1, by simpa using hexp m⟩)
  transgression_bijective_of_le_proPFrattini hRc hR
    (fun g m ↦ by rw [← ofMul_toMul m, ← Additive.ofMul_smul, htriv])
    (fun m ↦ by rw [← ofMul_toMul m, ← ofMul_pow, hexp, ofMul_one])

end freeProP

end TauCeti
