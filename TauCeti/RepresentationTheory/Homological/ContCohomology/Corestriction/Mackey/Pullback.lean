/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Mackey.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Pullback
import TauCeti.Algebra.Group.Subgroup.Map

/-!
# The Mackey formula along a continuous homomorphism

Let `U` be an open subgroup of finite index of a topological group `G`, `M` a `G`-module, and
`(φ, f)` a compatible pair from `(G, M)` to `(H, N)`: a continuous homomorphism `φ : H → G` and a
coefficient map `f : M → N` with `f (φ h • m) = h • f m`. Pulling back a corestricted class along
`(φ, f)` splits over the double cosets `φ(H) \ G / U` (NSW (1.5.6)):

```text
(φ, f)^* ∘ cor^G_U = ∑_{φ(H) s U} cor^H_{H_s} ∘ (ψ_s, f ∘ s)^*,   H_s = φ⁻¹(sUs⁻¹),
```

where `ψ_s : H → G` is the conjugate `h ↦ s⁻¹ φ(h) s` of `φ`, which maps `H_s` into `U`, and the
coefficient map is `m ↦ f (s • m)` (`TauCeti.ContCohomology.explicitMap2_explicitCor2_eq_sum`).
The representatives `s` of the double cosets are arbitrary, and so are the continuous
homomorphisms `ψ_s`, given with their values: for a Galois group they arise as maps along
conjugate embeddings rather than as conjugates of `φ`.

This is the form in which corestriction is localized: for the decomposition map `φ : G_{K_v} → G_K`
of a place `v` of a number field `K`, the double cosets `φ(G_{K_v}) \ G_K / U` classically index the
places `w` above `v` of the fixed field `F` of `U`, and `H_s` is the absolute Galois group of the
completion `F_w`.

The proof factors `φ` through its range `D = φ(H)`. The subgroup Mackey formula
(`TauCeti.ContCohomology.explicitCor2_mackey`) computes the restriction of `cor^G_U` to `D`, and the
surjection `H → D` induces bijections `H ⧸ φ⁻¹(D ⊓ sUs⁻¹) ≃ D ⧸ (D ⊓ sUs⁻¹)`, so pullback along it
commutes with each corestriction `cor^D_{D ⊓ sUs⁻¹}`
(`TauCeti.ContCohomology.explicitCor2_pullback`).

## Main results

* `TauCeti.ContCohomology.explicitMap2_explicitCor2_eq_sum`: the Mackey formula for pullback of
  degree-two corestriction along a continuous homomorphism.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.5.6).
* K. S. Brown, *Cohomology of Groups*, Chapter III, §9.
-/

public section

namespace TauCeti.ContCohomology

universe u v w z

variable {G : Type u} {H : Type v} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
  {M : Type w} {N : Type z} [AddCommGroup M] [AddCommGroup N]
  [DistribMulAction G M] [DistribMulAction H N]
  (φ : H →ₜ* G) (f : M →+ N) (hequiv : ∀ h m, f (φ h • m) = h • f m) (U : Subgroup G)

include hequiv in
/-- **The conjugate of a compatible pair**: if `ψ h = s⁻¹ φ(h) s` for all `h`, then `ψ`, restricted
to the preimage of `U`, and the coefficient map `m ↦ f (s • m)` form a compatible pair. -/
theorem comp_toAddMonoidHom_subgroupComap_smul (s : G) (ψ : H →ₜ* G)
    (hψ : ∀ h, ψ h = s⁻¹ * φ h * s) (x : U.comap (ψ : H →* G)) (m : M) :
    (f.comp (DistribSMul.toAddMonoidHom M s)) (ψ.subgroupComap U x • m) =
      x • (f.comp (DistribSMul.toAddMonoidHom M s)) m := by
  simp only [AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply, Subgroup.smul_def,
    ContinuousMonoidHom.subgroupComap_apply_coe, hψ, smul_smul, ← hequiv]
  group

variable [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul G M]
  [TopologicalSpace N] [IsTopologicalAddGroup N] [ContinuousSMul H N]

/-- Corestriction from a subgroup `W` of a pullback along `κ : W → U` depends only on the subgroup
and on the values of `κ`. -/
private theorem explicitCor2_explicitMap2_congr [ContinuousMul G] [ContinuousMul H]
    {W₁ W₂ : Subgroup H} [W₁.FiniteIndex] [W₂.FiniteIndex] (hW : W₁ = W₂)
    (hW₁ : IsOpen (W₁ : Set H)) (hW₂ : IsOpen (W₂ : Set H)) (κ₁ : W₁ →ₜ* U) (κ₂ : W₂ →ₜ* U)
    (hκ : ∀ x : W₁, (κ₁ x : G) = κ₂ ⟨x, hW ▸ x.2⟩) (g : M →+ N) (hg : Continuous g)
    (hg₁ : ∀ x m, g (κ₁ x • m) = x • g m) (hg₂ : ∀ x m, g (κ₂ x • m) = x • g m) (y : H2 U M) :
    explicitCor2 H N W₁ hW₁ (explicitMap2 U M W₁ N κ₁ g hg hg₁ y) =
      explicitCor2 H N W₂ hW₂ (explicitMap2 U M W₂ N κ₂ g hg hg₂ y) := by
  subst hW
  obtain rfl : κ₁ = κ₂ := ContinuousMonoidHom.ext fun x ↦ Subtype.ext (hκ x)
  rfl

variable [IsTopologicalGroup G] [ContinuousMul H] (hf : Continuous f) [U.FiniteIndex]
  (hU : IsOpen (U : Set G))

/-- The summand of the Mackey formula along a surjection `φ' : H → R` onto a subgroup `R` of `G`:
pulling back along `φ'` the Mackey summand `cor^R_{R ⊓ sUs⁻¹} ∘ (s)_*` is corestriction from
`φ'⁻¹(sUs⁻¹)` of the pullback along `h ↦ s⁻¹ φ'(h) s`, since `φ'` induces a bijection
`H ⧸ φ'⁻¹(R ⊓ sUs⁻¹) ≃ R ⧸ (R ⊓ sUs⁻¹)`. -/
private theorem explicitMap2_explicitMackeyTerm2 (R : Subgroup G) (φ' : H →ₜ* R)
    (hφ' : Function.Surjective φ') (hequiv' : ∀ h m, f ((φ' h : G) • m) = h • f m) (s : G)
    (ψ : H →ₜ* G) (hψ : ∀ h, ψ h = s⁻¹ * φ' h * s) (x : H2 U M) :
    explicitMap2 R M H N φ' f hf hequiv' (explicitMackeyTerm2 G M U R hU s x) =
      explicitCor2 H N (U.comap (ψ : H →* G)) (hU.preimage ψ.continuous)
        (explicitMap2 U M (U.comap (ψ : H →* G)) N (ψ.subgroupComap U)
          (f.comp (DistribSMul.toAddMonoidHom M s))
          (hf.comp ((continuous_const_smul s).congr fun _ ↦ rfl))
          (comp_toAddMonoidHom_subgroupComap_smul ((ContinuousMonoidHom.subgroupSubtype R).comp φ')
            f hequiv' U s ψ hψ) x) := by
  let Rs := (TauCeti.mackeySubgroup s U R).subgroupOf R
  have hRs : IsOpen (Rs : Set R) := U.isOpen_mackeySubgroup_subgroupOf R hU s
  have hker : (φ' : H →* R).ker ≤ Rs.comap (φ' : H →* R) := fun h hh ↦ by
    rw [Subgroup.mem_comap, (φ' : H →* R).mem_ker.1 hh]
    exact Rs.one_mem
  let e : H ⧸ Rs.comap (φ' : H →* R) ≃ R ⧸ Rs :=
    QuotientGroup.congrOfSurjectiveOfKerLe (φ' : H →* R) hφ' hker
      (Subgroup.map_comap_eq_self_of_surjective hφ' Rs)
  rw [explicitMackeyTerm2_apply,
    explicitCor2_pullback Rs (Rs.comap (φ' : H →* R)) φ' (φ'.subgroupComap Rs)
      (φ'.subgroupComap_apply_coe Rs) e
      (fun h ↦ QuotientGroup.congrOfSurjectiveOfKerLe_mk _ hφ' hker _ h) f hf hequiv' hRs
      (hRs.preimage φ'.continuous),
    ← AddMonoidHom.comp_apply (explicitMap2 Rs M _ N _ f hf _),
    ← explicitMap2_comp (↥U) M _ M (U.continuousMackeyToH R s) _ _ _ _ N (φ'.subgroupComap Rs) f hf]
  -- Both sides corestrict from `φ'⁻¹(sUs⁻¹)` a pullback along `h ↦ s⁻¹ φ'(h) s`.
  refine explicitCor2_explicitMap2_congr U ?_ _ _ _ _ (fun h ↦ ?_) _ _ _ _ x
  · ext h
    simp only [Rs, Subgroup.mem_comap, Subgroup.mem_subgroupOf, TauCeti.mem_mackeySubgroup_iff,
      MonoidHom.coe_ofClass, hψ]
    exact and_iff_right (φ' h).2
  · simp [hψ]

/-- **The Mackey formula along a continuous homomorphism** (NSW (1.5.6)): for a compatible pair
`(φ, f)` and an open subgroup `U` of finite index, pulling back the corestriction of a class
`x ∈ H²(U, M)` along `(φ, f)` is the sum over the double cosets `φ(H) \ G / U` of the
corestrictions from `H_s = ψ_s⁻¹(U) = φ⁻¹(sUs⁻¹)` of the pullbacks of `x` along `ψ_s` and
`m ↦ f (s • m)`, for any choice of representatives `s = r D` and any continuous homomorphisms
`ψ_s` with `ψ_s h = s⁻¹ φ(h) s`. -/
theorem explicitMap2_explicitCor2_eq_sum
    (r : DoubleCoset.Quotient ((φ : H →* G).range : Set G) (U : Set G) → G)
    (hr : ∀ D, DoubleCoset.mk (φ : H →* G).range U (r D) = D)
    (ψ : DoubleCoset.Quotient ((φ : H →* G).range : Set G) (U : Set G) → H →ₜ* G)
    (hψ : ∀ D h, ψ D h = (r D)⁻¹ * φ h * r D) (x : H2 U M) :
    explicitMap2 G M H N φ f hf hequiv (explicitCor2 G M U hU x) =
      letI := Fintype.ofFinite (DoubleCoset.Quotient ((φ : H →* G).range : Set G) (U : Set G))
      ∑ D, explicitCor2 H N (U.comap (ψ D : H →* G)) (hU.preimage (ψ D).continuous)
        (explicitMap2 U M (U.comap (ψ D : H →* G)) N ((ψ D).subgroupComap U)
          (f.comp (DistribSMul.toAddMonoidHom M (r D)))
          (hf.comp ((continuous_const_smul (r D)).congr fun _ ↦ rfl))
          (comp_toAddMonoidHom_subgroupComap_smul φ f hequiv U (r D) (ψ D) (hψ D)) x) := by
  let _ := Fintype.ofFinite (DoubleCoset.Quotient ((φ : H →* G).range : Set G) (U : Set G))
  -- `φ` is the inclusion of its range after the surjection `φ'` onto it.
  let φ' : H →ₜ* (φ : H →* G).range :=
    { toMonoidHom := (φ : H →* G).rangeRestrict
      continuous_toFun := φ.continuous.subtype_mk _ }
  have hcomp : (ContinuousMonoidHom.subgroupSubtype _).comp φ' = φ := rfl
  -- Pullback along `φ` is restriction to the range followed by pullback along `φ'`, and the
  -- restriction of the corestriction to the range is the subgroup Mackey formula.
  have hfac : explicitMap2 G M H N φ f hf hequiv =
      (explicitMap2 _ M H N φ' f hf hequiv).comp (explicitRes2 G M (φ : H →* G).range) := by
    rw [explicitRes2_eq_explicitMap2]
    exact (explicitMap2_congr_of_eq G M H N _ _ _ _ hcomp.symm (AddMonoidHom.comp_id f).symm).trans
      (explicitMap2_comp G M _ M (ContinuousMonoidHom.subgroupSubtype _) (AddMonoidHom.id M)
        continuous_id (ContinuousMonoidHom.id_subgroupSubtype_smul M _) H N φ' f hf hequiv)
  rw [hfac, AddMonoidHom.comp_apply, explicitCor2_mackey G M U _ r hr hU x, map_sum]
  exact Finset.sum_congr rfl fun D _ ↦ explicitMap2_explicitMackeyTerm2 f U hf hU _ φ'
    (φ : H →* G).rangeRestrict_surjective hequiv (r D) (ψ D) (hψ D) x

end TauCeti.ContCohomology
