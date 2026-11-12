/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Basic

/-!
# Pullback of corestriction along a transitive coset map

Let `φ : H → G` carry a finite-index subgroup `V` into `U`. If the induced map
`H / V → G / U` is a bijection, pullback along a compatible coefficient map commutes with
corestriction in degrees zero, one and two. Neither injectivity nor surjectivity of `φ` is needed.
This includes inflation along a quotient and the transitive-orbit case of the Mackey formula.
In localizing a corestricted Galois class, it allows passage from a local absolute Galois group
to its image before applying the subgroup Mackey formula.

The coset bijection is supplied as an equivalence with its value on representatives. For
compatible transversals the identity already holds on arbitrary cochains; independence of the
transversal gives the public identities on cohomology. The action on the coefficients need not
be trivial. The groups need not be compact and the coefficients need not be discrete: openness
and finite index of the two subgroups suffice.

The bijection hypothesis is essential. For an inclusion whose image has several orbits on
`G / U`, pullback of corestriction is a sum of corestrictions, not a single corestriction.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., I §5,
  especially (1.5.6).
* K. S. Brown, *Cohomology of Groups*, III §9.
-/

public section

namespace TauCeti.ContCohomology

universe u v w z

variable {G : Type u} {H : Type v} [Group G] [Group H]
  {M : Type w} {N : Type z} [AddCommGroup M] [AddCommGroup N]
  [DistribMulAction G M] [DistribMulAction H N]
  (U : Subgroup G) (V : Subgroup H) [U.FiniteIndex] [V.FiniteIndex]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

section Cochains

variable (φ : H →* G) (κ : V →* U) (hκ : ∀ v : V, (κ v : G) = φ v)
  (e : H ⧸ V ≃ G ⧸ U) (he : ∀ h : H, e h = (φ h : G ⧸ U))
  (f : M →+ N) (hf : ∀ h m, f (φ h • m) = h • f m)
  (t : G ⧸ U → G) (ht : ∀ q, (t q : G ⧸ U) = q)
  (s : H ⧸ V → H) (hs : ∀ q, (s q : H ⧸ V) = q)
  (hst : ∀ q, t (e q) = φ (s q))

include hκ he hf in
/-- Pullback commutes with the norm on invariants if it induces a bijection on coset spaces.
No topology is required in degree zero. -/
theorem explicitCor0_pullback (m : H0 U M) :
    explicitMap0 G M φ f hf (explicitCor0 G M U m) =
      explicitCor0 H N V
        (explicitMap0 U M κ f (fun v m ↦ by
          simpa only [Subgroup.smul_def, hκ] using hf v m) m) := by
  let t : G ⧸ U → G := fun q ↦ φ (e.symm q).out
  have ht (q : G ⧸ U) : (t q : G ⧸ U) = q :=
    (he (e.symm q).out).symm.trans
      ((congrArg e (QuotientGroup.out_eq' (e.symm q))).trans (e.apply_symm_apply q))
  have hst (q : H ⧸ V) : t (e q) = φ q.out := by simp [t]
  rw [explicitCor0_eq_transversal G M U t ht]
  apply Subtype.ext
  simp only [coe_explicitMap0, coe_explicitCor0Transversal, coe_explicitCor0, map_sum]
  rw [← e.sum_comp]
  exact Finset.sum_congr rfl fun q _ ↦ by rw [hst, hf]

include hκ he hf hst in
/-- Pullback commutes with the degree-one corestriction cochain when the transversals agree
under the induced coset bijection. No cocycle or continuity hypothesis is required. -/
theorem cochainsCor1_pullback (c : U → M) (h : H) :
    f (cochainsCor1 G M U t ht c (φ h)) =
      cochainsCor1 H N V s hs (fun v ↦ f (c (κ v))) h := by
  have hw (q : H ⧸ V) :
      (⟨lWord U t (e q) (φ h), lWord_mem U t ht (e q) (φ h)⟩ : U) =
        κ ⟨lWord V s q h, lWord_mem V s hs q h⟩ := by
    apply Subtype.ext
    exact (lWord_map V s U t φ e he hst q h).trans
      (hκ ⟨lWord V s q h, lWord_mem V s hs q h⟩).symm
  simp only [cochainsCor1_apply, map_sum]
  rw [← e.sum_comp]
  exact Finset.sum_congr rfl fun q _ ↦ by rw [hst, hf, hw]

include hκ he hf hst in
/-- Pullback commutes with the degree-two corestriction cochain when the transversals agree
under the induced coset bijection. No cocycle or continuity hypothesis is required. -/
theorem cochainsCor2_pullback (c : U × U → M) (h j : H) :
    f (cochainsCor2 G M U t ht c (φ h, φ j)) =
      cochainsCor2 H N V s hs (fun p ↦ f (c (κ p.1, κ p.2))) (h, j) := by
  have hw (q : H ⧸ V) (a : H) :
      (⟨lWord U t (e q) (φ a), lWord_mem U t ht (e q) (φ a)⟩ : U) =
        κ ⟨lWord V s q a, lWord_mem V s hs q a⟩ := by
    apply Subtype.ext
    exact (lWord_map V s U t φ e he hst q a).trans
      (hκ ⟨lWord V s q a, lWord_mem V s hs q a⟩).symm
  have heh (q : H ⧸ V) : (φ h)⁻¹ • e q = e (h⁻¹ • q) := by
    rw [apply_smul_of_apply_mk V φ e he, map_inv]
  simp only [cochainsCor2_apply, map_sum]
  rw [← e.sum_comp]
  exact Finset.sum_congr rfl fun q _ ↦ by rw [hst, hf, heh, hw, hw]

end Cochains

section Cohomology

variable [TopologicalSpace G] [TopologicalSpace H]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul G M]
  [TopologicalSpace N] [IsTopologicalAddGroup N] [ContinuousSMul H N]
  (φ : H →ₜ* G) (κ : V →ₜ* U) (hκ : ∀ v : V, (κ v : G) = φ v)
  (e : H ⧸ V ≃ G ⧸ U) (he : ∀ h : H, e h = (φ h : G ⧸ U))
  (f : M →+ N) (hf : Continuous f) (hequiv : ∀ h m, f (φ h • m) = h • f m)
  (hU : IsOpen (U : Set G)) (hV : IsOpen (V : Set H))

section DegreeOne

variable [SeparatelyContinuousMul G] [SeparatelyContinuousMul H]

include he in
/-- Pullback along a compatible pair commutes with degree-one corestriction if the induced
map of coset spaces is bijective. The subgroup homomorphism `κ` is the restriction of `φ`. -/
theorem explicitCor1_pullback (x : H1 U M) :
    explicitMap1 G M H N φ f hf hequiv (explicitCor1 G M U hU x) =
      explicitCor1 H N V hV
        (explicitMap1 U M V N κ f hf (fun v m ↦ by
          simpa only [Subgroup.smul_def, hκ] using hequiv v m) x) := by
  let t : G ⧸ U → G := fun q ↦ φ (e.symm q).out
  have ht (q : G ⧸ U) : (t q : G ⧸ U) = q :=
    (he (e.symm q).out).symm.trans
      ((congrArg e (QuotientGroup.out_eq' (e.symm q))).trans (e.apply_symm_apply q))
  have hst (q : H ⧸ V) : t (e q) = φ q.out := by simp [t]
  rw [explicitCor1_eq_transversal G M U t ht]
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    rw [explicitCor1Transversal_mk, explicitMap1_mk, explicitMap1_mk, explicitCor1_mk]
    apply congrArg (fun c : Z1 H N ↦ (c : H1 H N))
    apply Subtype.ext
    funext h
    simp only [cocyclesMap1_apply, coe_cocyclesCor1]
    simpa only [cochainsCor1_apply, cocyclesMap1_apply,
      ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_ofClass] using
      cochainsCor1_pullback U V φ.toMonoidHom κ.toMonoidHom hκ e he f hequiv
        t ht Quotient.out Quotient.out_eq hst c h

end DegreeOne

variable [ContinuousMul G] [ContinuousMul H]

include he in
/-- Pullback along a compatible pair commutes with degree-two corestriction if the induced
map of coset spaces is bijective. This permits replacing the source group by its image before
using a subgroup Mackey formula. -/
theorem explicitCor2_pullback (x : H2 U M) :
    explicitMap2 G M H N φ f hf hequiv (explicitCor2 G M U hU x) =
      explicitCor2 H N V hV
        (explicitMap2 U M V N κ f hf (fun v m ↦ by
          simpa only [Subgroup.smul_def, hκ] using hequiv v m) x) := by
  let t : G ⧸ U → G := fun q ↦ φ (e.symm q).out
  have ht (q : G ⧸ U) : (t q : G ⧸ U) = q :=
    (he (e.symm q).out).symm.trans
      ((congrArg e (QuotientGroup.out_eq' (e.symm q))).trans (e.apply_symm_apply q))
  have hst (q : H ⧸ V) : t (e q) = φ q.out := by simp [t]
  rw [explicitCor2_eq_transversal G M U t ht]
  induction x using QuotientAddGroup.induction_on with
  | _ c =>
    rw [explicitCor2Transversal_mk, explicitMap2_mk, explicitMap2_mk, explicitCor2_mk]
    apply congrArg (fun c : Z2 H N ↦ (c : H2 H N))
    apply Subtype.ext
    funext p
    obtain ⟨h, j⟩ := p
    simp only [cocyclesMap2_apply, coe_cocyclesCor2]
    simpa only [cochainsCor2_apply, cocyclesMap2_apply,
      ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_ofClass] using
      cochainsCor2_pullback U V φ.toMonoidHom κ.toMonoidHom hκ e he f hequiv
        t ht Quotient.out Quotient.out_eq hst c h j

end Cohomology

end TauCeti.ContCohomology
