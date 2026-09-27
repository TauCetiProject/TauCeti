/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.FiveTerm
public import TauCeti.Topology.Algebra.Group.LowerCentralSeries

/-!
# Conjugation-invariant classes in `H¹` with trivial coefficients

Let `N` be a normal subgroup of a topological group `G` and `M` a topological `G`-module on which
`G` acts trivially. Then `H¹(N, M)` is the group of continuous homomorphisms `N → M`
(`TauCeti.ContCohomology.H1EquivOfSmulEqSelf`), and `G` acts on it through conjugation on `N`.
The invariant classes `H¹(N, M)^G` are the continuous homomorphisms `N → M` that are constant on
the conjugacy classes of `G` in `N` (`mem_H1ConjInvariants_iff_of_smul_eq_self`).

When `M` is killed by `p`, for instance `M = 𝔽_p`, such a homomorphism kills the `p`-th powers as
well as the commutators `⁅N, G⁆`. If moreover `M` is a `T1Space`, so that the kernel of a continuous
homomorphism into `M` is closed, the homomorphism factors through the quotient `N ⧸ Nᵖ[N, G]` of `N`
by the closed subgroup `TauCeti.pLowerCentralStep p N`, and conversely. Hence
`H¹(N, M)^G ≃ Hom_cont(N ⧸ Nᵖ[N, G], M)` (`H1ConjInvariantsEquivOfSmulEqSelf`), for a closed
normal subgroup `N` and a `T1Space` `M` killed by `p`. For `M = 𝔽_p` the right-hand side is the
continuous `𝔽_p`-dual of `N ⧸ Nᵖ[N, G]`; for a profinite group `G` its dimension is the topological
generator rank of that quotient, which is worked out in
`TauCeti.Topology.Algebra.Group.Profinite.ProP.InvariantDual`.

The invariant classes are the domain of the transgression in the five-term exact sequence of a
group extension `1 → N → G → G ⧸ N → 1`. For a minimal presentation `1 → R → F → G → 1` of a
pro-`p` group by a free pro-`p` group, the transgression is an isomorphism, and the identification
`H¹(R, 𝔽_p)^F ≃ Hom_cont(R ⧸ Rᵖ[R, F], 𝔽_p)` is what lets `H²(G, 𝔽_p)` count the generators of
`R` as a closed normal subgroup of `F`.

## Main results

* `TauCeti.ContCohomology.mem_H1ConjInvariants_iff_of_smul_eq_self`: for trivial coefficients, a
  class in `H¹(N, M)` is conjugation-invariant exactly when the continuous homomorphism `N → M` it
  represents is constant on the conjugacy classes of `G` in `N`.
* `TauCeti.ContCohomology.H1ConjInvariantsEquivOfSmulEqSelf`: for trivial `T1Space` coefficients
  killed by `p` and a closed normal subgroup `N`, `H¹(N, M)^G` is the group of continuous
  homomorphisms `N ⧸ Nᵖ[N, G] → M`.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, (3.9.5).
* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), §1.4.
-/

public section

namespace TauCeti.ContCohomology

universe uG uM

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type uM} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  {N : Subgroup G} [N.Normal] (htriv : ∀ (g : G) (m : M), g • m = m)

include htriv

/-! ### Invariant classes as conjugation-invariant homomorphisms -/

/-- For trivial coefficients, the class of a continuous `1`-cocycle on `N` is conjugation-invariant
exactly when the cocycle is constant on the conjugacy classes of `G` in `N`. -/
theorem mk_mem_H1ConjInvariants_iff_of_smul_eq_self {c : Z1 N M} :
    (c : H1 N M) ∈ H1ConjInvariants G M N ↔
      ∀ (g : G) (n : N), (c : N → M) (MulAut.conjNormal g n) = (c : N → M) n := by
  have hconj (g : G) (n : N) :
      Subgroup.inverseConjugationHom N g n = MulAut.conjNormal g⁻¹ n :=
    Subtype.ext (by simp)
  simp only [mem_H1ConjInvariants_iff, explicitConj1_apply_eq_smul, smul_mk, H1pi_eq_iff,
    B1_eq_bot_of_smul_eq_self (fun (n : N) (m : M) ↦ htriv n m), AddSubgroup.mem_bot,
    sub_eq_zero, funext_iff, cocyclesMap1_apply, DistribSMul.toAddMonoidHom_apply, htriv, hconj]
  refine ⟨fun h g n ↦ ?_, fun h g n ↦ h g⁻¹ n⟩
  simpa only [inv_inv] using h g⁻¹ n

/-- For trivial coefficients, a class in `H¹(N, M)` is conjugation-invariant exactly when the
continuous homomorphism `N → M` it represents is constant on the conjugacy classes of `G` in
`N`. -/
theorem mem_H1ConjInvariants_iff_of_smul_eq_self {x : H1 N M} :
    x ∈ H1ConjInvariants G M N ↔ ∀ (g : G) (n : N),
      Additive.toMul (H1EquivOfSmulEqSelf (fun (n : N) (m : M) ↦ htriv n m) x)
          (MulAut.conjNormal g n) =
        Additive.toMul (H1EquivOfSmulEqSelf (fun (n : N) (m : M) ↦ htriv n m) x) n := by
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    rw [mk_mem_H1ConjInvariants_iff_of_smul_eq_self htriv]
    simp only [H1EquivOfSmulEqSelf_mk, Z1EquivOfSmulEqSelf_apply, EmbeddingLike.apply_eq_iff_eq]

/-! ### Coefficients killed by `p`: characters of `N ⧸ Nᵖ[N, G]` -/

section Quotient

variable (p : ℕ) [T1Space M] (hN : IsClosed (N : Set G)) (hpM : ∀ m : M, p • m = 0)
include hN hpM

/-- For `T1Space` coefficients killed by `p`, the continuous homomorphism `N → M` representing a
conjugation-invariant class kills `Nᵖ[N, G]`: its kernel is closed, so the characteristic property
of `pLowerCentralStep` applies. -/
theorem pLowerCentralStep_subgroupOf_le_ker_of_mem_H1ConjInvariants {x : H1 N M}
    (hx : x ∈ H1ConjInvariants G M N) :
    (pLowerCentralStep p N).subgroupOf N ≤
      (Additive.toMul (H1EquivOfSmulEqSelf (fun (n : N) (m : M) ↦ htriv n m) x)).ker := by
  set φ : N →ₜ* Multiplicative M :=
    Additive.toMul (H1EquivOfSmulEqSelf (fun (n : N) (m : M) ↦ htriv n m) x)
  have : T1Space (Multiplicative M) := ‹T1Space M›
  have hker : IsClosed ((φ.ker : Subgroup N) : Set N) := by
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage φ.continuous
  have hA : ∀ a : Multiplicative M, a ^ p = 1 := fun a ↦ by
    rw [← ofAdd_toAdd a, ← ofAdd_nsmul, hpM, ofAdd_zero]
  exact (pLowerCentralStep_subgroupOf_le_ker_iff hN φ.toMonoidHom hker).mpr
    ⟨fun n ↦ hA _, fun g n ↦ (mem_H1ConjInvariants_iff_of_smul_eq_self htriv).mp hx g n⟩

/-- **Conjugation-invariant classes as characters of `N ⧸ Nᵖ[N, G]`.** For a closed normal
subgroup `N` of `G` and `T1Space` coefficients `M` with trivial `G`-action killed by `p`, the
`G`-invariant classes in `H¹(N, M)` are the continuous homomorphisms `N ⧸ Nᵖ[N, G] → M`. A class
is sent to the character of the quotient induced by the continuous homomorphism `N → M` it
represents. -/
noncomputable def H1ConjInvariantsEquivOfSmulEqSelf :
    H1ConjInvariants G M N ≃+
      Additive ((N ⧸ (pLowerCentralStep p N).subgroupOf N) →ₜ* Multiplicative M) where
  toFun x := Additive.ofMul (ContinuousMonoidHom.quotientLift _
    (Additive.toMul (H1EquivOfSmulEqSelf (fun (n : N) (m : M) ↦ htriv n m) x.1))
    (pLowerCentralStep_subgroupOf_le_ker_of_mem_H1ConjInvariants htriv p hN hpM x.2))
  invFun ψ := ⟨(H1EquivOfSmulEqSelf (fun (n : N) (m : M) ↦ htriv n m)).symm
      (Additive.ofMul ((Additive.toMul ψ).comp (ContinuousMonoidHom.quotientMk _))),
    (mem_H1ConjInvariants_iff_of_smul_eq_self htriv).mpr fun g n ↦ by
      simp only [AddEquiv.apply_symm_apply, toMul_ofMul, ContinuousMonoidHom.comp_toFun,
        ContinuousMonoidHom.quotientMk_apply, mk_conjNormal_eq]⟩
  left_inv x := Subtype.ext <| by
    simp only [toMul_ofMul, ContinuousMonoidHom.quotientLift_comp_quotientMk, ofMul_toMul,
      AddEquiv.symm_apply_apply]
  right_inv ψ := Additive.toMul.injective <| by
    simp only [toMul_ofMul, AddEquiv.apply_symm_apply]
    exact (ContinuousMonoidHom.quotientLift_unique _ _ _ _ fun n ↦ rfl).symm
  map_add' x y := Additive.toMul.injective <| by
    ext q
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
    simp only [toMul_ofMul, toMul_add, ContinuousMonoidHom.mul_apply,
      ContinuousMonoidHom.quotientLift_mk, AddSubgroup.coe_add, map_add]

/-- The character of `N ⧸ Nᵖ[N, G]` attached to a conjugation-invariant class takes, at the class
of `n`, the value at `n` of the continuous homomorphism `N → M` representing the class. -/
@[simp]
theorem H1ConjInvariantsEquivOfSmulEqSelf_apply_mk (x : H1ConjInvariants G M N) (n : N) :
    Additive.toMul (H1ConjInvariantsEquivOfSmulEqSelf htriv p hN hpM x)
        (n : N ⧸ (pLowerCentralStep p N).subgroupOf N) =
      Additive.toMul (H1EquivOfSmulEqSelf (fun (n : N) (m : M) ↦ htriv n m) x.1) n := by
  rw [H1ConjInvariantsEquivOfSmulEqSelf]
  simp only [AddEquiv.coe_mk, Equiv.coe_fn_mk, toMul_ofMul, ContinuousMonoidHom.quotientLift_mk]

/-- The conjugation-invariant class attached to a character `ψ` of `N ⧸ Nᵖ[N, G]` is represented by
the composite of `ψ` with the quotient map. -/
@[simp]
theorem H1ConjInvariantsEquivOfSmulEqSelf_symm_apply_coe
    (ψ : Additive ((N ⧸ (pLowerCentralStep p N).subgroupOf N) →ₜ* Multiplicative M)) :
    ((H1ConjInvariantsEquivOfSmulEqSelf htriv p hN hpM).symm ψ : H1 N M) =
      (H1EquivOfSmulEqSelf (fun (n : N) (m : M) ↦ htriv n m)).symm
        (Additive.ofMul ((Additive.toMul ψ).comp (ContinuousMonoidHom.quotientMk _))) := by
  rw [H1ConjInvariantsEquivOfSmulEqSelf]
  simp only [AddEquiv.symm_mk, AddEquiv.coe_mk, Equiv.coe_fn_symm_mk]

end Quotient

end TauCeti.ContCohomology
