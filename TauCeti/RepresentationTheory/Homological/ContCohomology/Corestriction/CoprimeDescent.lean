/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Exponent
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.FiveTerm

/-!
# Descent along a normal subgroup of index prime to the coefficients

Let `N` be an open normal subgroup of finite index in a topological group `G`, and let `M` be a
continuous `G`-module killed by an integer `e` prime to the index `[G : N]`. Then restriction
identifies the low-degree cohomology of `G` with the invariants of the conjugation action on that
of `N`:

```text
H⁰(G, M) ≃ H⁰(N, M)^{G/N},    H¹(G, M) ≃ H¹(N, M)^{G/N}.
```

In degree zero this is the equality `M^G = (M^N)^G` and needs no hypothesis on the index
(`TauCeti.ContCohomology.explicitRes0_injective`,
`TauCeti.ContCohomology.mem_range_explicitRes0_iff`). In degree one it rests on two composites of
restriction and the corestriction `TauCeti.ContCohomology.explicitCor1`:

* `cor ∘ res = [G : N]` on `H¹(G, M)` (`TauCeti.ContCohomology.explicitCor1_comp_res1`, for any
  open subgroup of finite index);
* `res ∘ cor = ∑_{gN ∈ G/N} g` on `H¹(N, M)`, `g` acting by the conjugation
  `TauCeti.ContCohomology.explicitConj1` (`explicitRes1_explicitCor1_of_normal`), hence
  `res ∘ cor = [G : N]` on the invariants `TauCeti.ContCohomology.H1ConjInvariants`.

On cochains the second identity holds exactly, for every transversal: when `N` is normal, the
transversal word of an element `n ∈ N` at the coset `u` is the conjugate `(t u)⁻¹ n (t u)`
(`TauCeti.lWord_of_mem_of_normal`), so the corestriction cochain restricted to `N` is the sum of
the conjugates of the cocycle (`cochainsCor1_apply_of_mem`).

As `e` kills both `H¹(G, M)` and `H¹(N, M)`, multiplication by `[G : N]` is bijective on them
(`TauCeti.nsmul_right_bijective_of_coprime`). So restriction is injective on `H¹(G, M)`
(`explicitRes1_injective_of_coprime`, for any open subgroup of finite index), and the
corestriction divided by `[G : N]` is a section of it on the invariants, so restriction onto the
invariants is bijective (`explicitResConj1_bijective_of_coprime`).

## Main results

* `TauCeti.ContCohomology.explicitRes1_explicitCor1_of_normal`: `res ∘ cor = ∑_{gN} g` on
  `H¹(N, M)` for a normal subgroup `N`.
* `TauCeti.ContCohomology.explicitRes1_explicitCor1_of_mem_H1ConjInvariants`:
  `res (cor x) = [G : N] • x` on the conjugation invariants.
* `TauCeti.ContCohomology.explicitRes1_injective_of_coprime`: restriction to an open subgroup of
  finite index prime to an exponent of `M` is injective on `H¹`.
* `TauCeti.ContCohomology.explicitResConj1_bijective_of_coprime`: restriction
  `H¹(G, M) → H¹(N, M)^{G/N}` is bijective for an open normal subgroup of index prime to an
  exponent of `M`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.5.7), (1.6.2)
  and the proof of (7.3.1).
* J.-P. Serre, *Galois Cohomology*, Chapter I, §2.4.
-/

public section

namespace TauCeti.ContCohomology

universe u v

/-! ### Degree zero -/

section DegreeZero

variable (G : Type u) [Group G] (M : Type v) [AddCommGroup M] [DistribMulAction G M]
  (N : Subgroup G)

/-- Restriction in degree zero is injective: it does not change the underlying element. -/
theorem explicitRes0_injective : Function.Injective (explicitRes0 G M N) :=
  fun x y h => Subtype.ext (by simpa only [coe_explicitRes0] using congrArg Subtype.val h)

/-- **Restriction in degree zero onto the invariants.** An `N`-invariant element is the
restriction of a `G`-invariant one exactly when `G` fixes it, so `H⁰(G, M) → H⁰(N, M)^G` is
bijective, with no hypothesis on `N`. -/
theorem mem_range_explicitRes0_iff (x : H0 N M) :
    x ∈ (explicitRes0 G M N).range ↔ ∀ g : G, g • (x : M) = x := by
  constructor
  · rintro ⟨y, rfl⟩ g
    rw [coe_explicitRes0]
    exact y.2 g
  · intro hx
    exact ⟨⟨x, fun g => hx g⟩, Subtype.ext (coe_explicitRes0 G M N _)⟩

end DegreeZero

/-! ### The restriction of a corestriction to a normal subgroup -/

section Cochain

variable (G : Type u) [Group G] (M : Type v) [AddCommGroup M] [DistribMulAction G M]
  (N : Subgroup G) [N.Normal] [N.FiniteIndex] (t : G ⧸ N → G)
  (ht : ∀ u : G ⧸ N, (QuotientGroup.mk (t u) : G ⧸ N) = u)

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

/-- **The corestriction cochain on a normal subgroup is a sum of conjugates.** For `N` normal and
`γ ∈ N`, the degree-one corestriction cochain of `f : N → M` over the transversal `t` takes the
value `∑ u, t u • f ((t u)⁻¹ γ (t u))` at `γ`. -/
theorem cochainsCor1_apply_of_mem (f : N → M) {γ : G} (hγ : γ ∈ N) :
    cochainsCor1 G M N t ht f γ =
      ∑ u : G ⧸ N, t u • f ⟨(t u)⁻¹ * γ * t u, ‹N.Normal›.conj_mem' γ hγ (t u)⟩ := by
  rw [cochainsCor1_apply]
  refine Finset.sum_congr rfl fun u _ => ?_
  congr 2
  exact Subtype.ext (lWord_of_mem_of_normal N t hγ u)

end Cochain

section Cohomology

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

section Normal

variable (N : Subgroup G) [N.Normal] [N.FiniteIndex] (hN : IsOpen (N : Set G))

/-- **`res ∘ cor = ∑_{gN} g` on `H¹(N, M)`** for an open normal subgroup `N` of finite index
(NSW (1.5.6) for a normal subgroup): restricting the corestriction of a class is the sum of its
conjugates `t u • x` (`TauCeti.ContCohomology.explicitConj1`) over any transversal `t` of
`G ⧸ N`. -/
theorem explicitRes1_explicitCor1_of_normal (t : G ⧸ N → G)
    (ht : ∀ u : G ⧸ N, (QuotientGroup.mk (t u) : G ⧸ N) = u) (x : H1 N M) :
    explicitRes1 G M N (explicitCor1 G M N hN x) = ∑ u : G ⧸ N, t u • x := by
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    rw [explicitCor1_eq_transversal G M N t ht hN, explicitCor1Transversal_mk, explicitRes1_mk]
    simp only [smul_mk]
    rw [← QuotientAddGroup.mk_sum]
    congr 1
    refine Subtype.ext (funext fun n => ?_)
    rw [AddSubgroup.val_finsetSum, Finset.sum_apply, cocyclesMap1_apply, AddMonoidHom.id_apply,
      ContinuousMonoidHom.subgroupSubtype_apply, coe_cocyclesCor1,
      cochainsCor1_apply_of_mem G M N t ht _ n.2]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [cocyclesMap1_apply, DistribSMul.toAddMonoidHom_apply,
      Subgroup.inverseConjugationHom_apply]

/-- **`res ∘ cor = [G : N]` on the conjugation invariants** of `H¹(N, M)`, for an open normal
subgroup `N` of finite index. -/
theorem explicitRes1_explicitCor1_of_mem_H1ConjInvariants {x : H1 N M}
    (hx : x ∈ H1ConjInvariants G M N) :
    explicitRes1 G M N (explicitCor1 G M N hN x) = N.index • x := by
  rw [explicitRes1_explicitCor1_of_normal G M N hN Quotient.out Quotient.out_eq]
  have hx' : ∀ u : G ⧸ N, (u.out : G) • x = x := fun u =>
    (explicitConj1_apply_eq_smul N u.out x).symm.trans
      ((mem_H1ConjInvariants_iff G M N).1 hx u.out)
  simp only [hx', Finset.sum_const, Finset.card_univ, Subgroup.index_eq_card,
    Nat.card_eq_fintype_card]

end Normal

variable {G M}

/-- **Restriction is injective on `H¹` for an index prime to the coefficients.** If an integer
`e` prime to the index of the open subgroup `U` of finite index kills `M`, then
`H¹(G, M) → H¹(U, M)` is injective, because `cor ∘ res = [G : U]` is invertible on `H¹(G, M)`. -/
theorem explicitRes1_injective_of_coprime (U : Subgroup G) [U.FiniteIndex]
    (hU : IsOpen (U : Set G)) {e : ℕ} (he : ∀ y : M, e • y = 0) (hcop : U.index.Coprime e) :
    Function.Injective (explicitRes1 G M U) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  refine (nsmul_right_bijective_of_coprime (nsmul_H1_eq_zero he) hcop).injective ?_
  simp only [← explicitCor1_comp_res1 G M U hU x, hx, map_zero, nsmul_zero]

/-- **Restriction onto the conjugation invariants is bijective for an index prime to the
coefficients** (NSW, proof of (7.3.1)). If `N` is an open normal subgroup of finite index and an
integer `e` prime to `[G : N]` kills `M`, then restriction `H¹(G, M) → H¹(N, M)^{G/N}` is
bijective: `cor ∘ res = [G : N]` and `res ∘ cor = [G : N]` on the invariants, and `[G : N]` is
invertible modulo `e`. -/
theorem explicitResConj1_bijective_of_coprime (N : Subgroup G) [N.Normal] [N.FiniteIndex]
    (hN : IsOpen (N : Set G)) {e : ℕ} (he : ∀ y : M, e • y = 0) (hcop : N.index.Coprime e) :
    Function.Bijective (explicitResConj1 G M N) := by
  refine ⟨fun x y h => explicitRes1_injective_of_coprime N hN he hcop ?_, fun y => ?_⟩
  · simpa only [coe_explicitResConj1] using congrArg Subtype.val h
  · -- Divide the corestriction of `y` by the index in `H¹(G, M)`; its restriction is `y` after
    -- cancelling the index in `H¹(N, M)`.
    obtain ⟨x, hx⟩ := (nsmul_right_bijective_of_coprime (nsmul_H1_eq_zero (G := G) he)
      hcop).surjective (explicitCor1 G M N hN y)
    refine ⟨x, Subtype.ext ((nsmul_right_bijective_of_coprime
      (nsmul_H1_eq_zero (G := N) he) hcop).injective ?_)⟩
    simp only [coe_explicitResConj1, ← map_nsmul, hx,
      explicitRes1_explicitCor1_of_mem_H1ConjInvariants G M N hN y.2]

end Cohomology

end TauCeti.ContCohomology
