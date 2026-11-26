/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Tactic.Group
import TauCeti.GroupTheory.Coset.Basic

/-!
# Gelfand's trick for spherical Hecke operators

Let `G` be a group, `K : Subgroup G`, `A` a commutative semiring, and `π : Representation A G W`
a representation of `G` on an `A`-module `W`. A function `f : G → A` is a **Hecke function**
(`Subgroup.IsHeckeFunction K f`) if it is left and right `K`-invariant and supported on finitely
many left cosets `g K`. On `K`-fixed vectors `v` (`∀ k ∈ K, π k v = v`), `f` acts by the finite
sum `Representation.heckeOp π K f v = ∑ᶠ q : G ⧸ K, f q.out • π q.out v`.

The convolution of two Hecke functions `f'` and `f` is defined by
`Subgroup.heckeConv K f' f x = ∑ᶠ q : G ⧸ K, f' q.out * f (q.out⁻¹ * x)`, is again a Hecke
function (`Subgroup.IsHeckeFunction.heckeConv`), and corresponds to composition of Hecke operators
on `K`-fixed vectors (`Subgroup.IsHeckeFunction.heckeOp_comp`).

If `τ : G ≃* G` is a group automorphism such that `τ g⁻¹ ∈ K * g * K` (that is,
`∃ a ∈ K, ∃ b ∈ K, τ g⁻¹ = a * g * b`) for every `g : G`, then `τ` automatically preserves `K`
and:
1. For any ring endomorphism `σ : A →+* A` and `G`-invariant pairing `B : W →ₛₗ[σ] W' →ₗ[A] Z`,
   `f^∨(g) = σ (f g⁻¹)` is again a Hecke function and
   `B (π.heckeOp K f v) v' = B v (π'.heckeOp K f^∨ v')` (`IsHeckeFunction.heckeOp_adjoint`).
2. Any two Hecke operators commute on `K`-fixed vectors (`Subgroup.IsHeckeFunction.heckeOp_comm`).

## References

* J. Tits, *Reductive groups over local fields*, Automorphic Forms, Representations and
  L-Functions, Proc. Sympos. Pure Math. 33 (1979), §3.3.3.
* T. Tamagawa, *On the ζ-functions of a division algebra*, Ann. of Math. **77** (1963), 387–405.
* Adapted from `src/Lib/General/LinearAlgebra/IntegralLattices.lean` in `grh-lean`
  (<https://github.com/lsernau/grh-lean>, Apache 2.0, Copyright 2026 Anthropic, PBC).
-/

public section

noncomputable section

open QuotientGroup

/-! ### Abstract Hecke functions, convolution, and Gelfand's trick -/

section AbstractHecke

variable {G A W W' Z : Type*} [Group G] [CommSemiring A]
  [AddCommMonoid W] [Module A W] [AddCommMonoid W'] [Module A W'] [AddCommMonoid Z] [Module A Z]

/-- A function `f : G → A` is a **Hecke function** for a subgroup `K : Subgroup G` if it is
supported on finitely many left cosets `g K` and is left and right `K`-invariant. -/
def Subgroup.IsHeckeFunction (K : Subgroup G) (f : G → A) : Prop :=
  {q : G ⧸ K | f q.out ≠ 0}.Finite ∧ ∀ g : G, ∀ k ∈ K, f (k * g) = f g ∧ f (g * k) = f g

/-- Characterization of `Subgroup.IsHeckeFunction`. -/
theorem Subgroup.isHeckeFunction_iff {K : Subgroup G} {f : G → A} :
    K.IsHeckeFunction f ↔
      {q : G ⧸ K | f q.out ≠ 0}.Finite ∧ ∀ g : G, ∀ k ∈ K, f (k * g) = f g ∧ f (g * k) = f g :=
  Iff.rfl

/-- A Hecke function is supported on finitely many left cosets of `K`. -/
theorem Subgroup.IsHeckeFunction.finite_support {K : Subgroup G} {f : G → A}
    (hf : K.IsHeckeFunction f) : {q : G ⧸ K | f q.out ≠ 0}.Finite :=
  hf.1

/-- A Hecke function is left `K`-invariant. -/
theorem Subgroup.IsHeckeFunction.mul_left {K : Subgroup G} {f : G → A}
    (hf : K.IsHeckeFunction f) (g : G) {k : G} (hk : k ∈ K) : f (k * g) = f g :=
  (hf.2 g k hk).1

/-- A Hecke function is right `K`-invariant. -/
theorem Subgroup.IsHeckeFunction.mul_right {K : Subgroup G} {f : G → A}
    (hf : K.IsHeckeFunction f) (g : G) {k : G} (hk : k ∈ K) : f (g * k) = f g :=
  (hf.2 g k hk).2

private theorem support_smul_subset {K : Subgroup G} {f : G → A} {M : Type*} [AddCommMonoid M]
    [Module A M] (x : G ⧸ K → M) :
    (Function.support fun q : G ⧸ K ↦ f q.out • x q) ⊆ {q : G ⧸ K | f q.out ≠ 0} :=
  fun _ hq h0 ↦ hq (by simp [h0])

private theorem finite_support_smul {K : Subgroup G} {f : G → A}
    (hf : {q : G ⧸ K | f q.out ≠ 0}.Finite) {M : Type*} [AddCommMonoid M] [Module A M]
    (x : G ⧸ K → M) :
    (Function.support fun q : G ⧸ K ↦ f q.out • x q).Finite :=
  hf.subset (support_smul_subset x)

/-- The Hecke operator attached to `f : G → A` on a representation `π : Representation A G W`,
defined by summing `f q.out • π q.out v` over left cosets `q : G ⧸ K`. -/
def Representation.heckeOp (π : Representation A G W) (K : Subgroup G) (f : G → A) (v : W) : W :=
  ∑ᶠ q : G ⧸ K, f q.out • π q.out v

/-- Definitional unfolding of `Representation.heckeOp`. -/
theorem Representation.heckeOp_def (π : Representation A G W) (K : Subgroup G) (f : G → A) (v : W) :
    π.heckeOp K f v = ∑ᶠ q : G ⧸ K, f q.out • π q.out v :=
  (rfl)

@[simp] theorem Representation.heckeOp_zero_right (π : Representation A G W) (K : Subgroup G)
    (f : G → A) : π.heckeOp K f 0 = 0 := by
  simp [heckeOp_def]

@[simp] theorem Representation.heckeOp_zero_left (π : Representation A G W) (K : Subgroup G)
    (v : W) : π.heckeOp K 0 v = 0 := by
  simp [heckeOp_def]

theorem Representation.heckeOp_add_right {K : Subgroup G} (π : Representation A G W) {f : G → A}
    (hf : K.IsHeckeFunction f) (v w : W) :
    π.heckeOp K f (v + w) = π.heckeOp K f v + π.heckeOp K f w := by
  simp only [heckeOp_def, map_add, smul_add]
  exact finsum_add_distrib (finite_support_smul hf.finite_support _)
    (finite_support_smul hf.finite_support _)

theorem Representation.heckeOp_smul_right {K : Subgroup G} (π : Representation A G W) {f : G → A}
    (hf : K.IsHeckeFunction f) (c : A) (v : W) :
    π.heckeOp K f (c • v) = c • π.heckeOp K f v := by
  simp only [heckeOp_def, map_smul, smul_comm _ c]
  exact (map_finsum (LinearMap.lsmul A W c) (finite_support_smul hf.finite_support _)).symm

theorem Representation.heckeOp_add_left {K : Subgroup G} (π : Representation A G W) {f f' : G → A}
    (hf : K.IsHeckeFunction f) (hf' : K.IsHeckeFunction f') (v : W) :
    π.heckeOp K (f + f') v = π.heckeOp K f v + π.heckeOp K f' v := by
  simp only [heckeOp_def, Pi.add_apply, add_smul]
  exact finsum_add_distrib (finite_support_smul hf.finite_support _)
    (finite_support_smul hf'.finite_support _)

theorem Representation.heckeOp_smul_left {K : Subgroup G} (π : Representation A G W) {f : G → A}
    (hf : K.IsHeckeFunction f) (c : A) (v : W) :
    π.heckeOp K (c • f) v = c • π.heckeOp K f v := by
  simp only [heckeOp_def, Pi.smul_apply, smul_eq_mul, mul_smul]
  exact (map_finsum (LinearMap.lsmul A W c) (finite_support_smul hf.finite_support _)).symm

/-- The indicator function of `K` acts as the identity on `K`-fixed vectors. -/
theorem Representation.heckeOp_indicator_one {K : Subgroup G} (π : Representation A G W) {v : W}
    (hv : ∀ k ∈ K, π k v = v) :
    π.heckeOp K (Set.indicator (K : Set G) 1) v = v := by
  rw [heckeOp_def, finsum_eq_single _ (QuotientGroup.mk (1 : G))]
  · obtain ⟨⟨k, hk⟩, h1⟩ := QuotientGroup.mk_out_eq_mul K 1
    have hout : ((QuotientGroup.mk (1 : G) : G ⧸ K).out : G) ∈ K := by
      simpa [h1] using hk
    simp [hv _ hout]
  · intro q hq
    have hout : q.out ∉ (K : Set G) := fun hmem ↦ hq <| by
      rw [← Quotient.out_eq q]
      exact QuotientGroup.eq.2 (by simpa [leftRel_apply] using K.inv_mem hmem)
    simp [Set.indicator_of_notMem hout]

/-- The Hecke operator of a bi-`K`-invariant function sends `K`-fixed vectors to `K`-fixed
vectors. -/
theorem Representation.heckeOp_mem_fixed {K : Subgroup G} (π : Representation A G W) {f : G → A}
    {v : W} (hf : K.IsHeckeFunction f) (hv : ∀ k ∈ K, π k v = v) {k : G} (hk : k ∈ K) :
    π k (π.heckeOp K f v) = π.heckeOp K f v := by
  rw [heckeOp_def, map_finsum (π k) (finite_support_smul hf.finite_support _)]
  have hcongr : ∀ a b : G, leftRel K a b ↔ leftRel K (k * a) (k * b) := fun a b ↦ by
    simp [leftRel_apply, mul_assoc]
  refine (finsum_congr fun q ↦ ?_).trans
    (finsum_comp_equiv (Quotient.congr (Equiv.mulLeft k) hcongr))
  obtain ⟨k', hk', heq⟩ := QuotientGroup.out_congr_eq_mul (Equiv.mulLeft k) hcongr q
  rw [heq, Equiv.coe_mulLeft, hf.mul_right _ hk', hf.mul_left _ hk, map_smul, map_mul, map_mul,
    mul_apply_eq_comp, mul_apply_eq_comp, hv k' hk']

private theorem mem_iff_of_doubleCoset {K : Subgroup G} {τ : G ≃* G}
    (hτg : ∀ g : G, ∃ a ∈ K, ∃ b ∈ K, τ g⁻¹ = a * g * b) (g : G) :
    τ g ∈ K ↔ g ∈ K := by
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, hg⟩ := hτg g
    have hτinv : τ g⁻¹ ∈ K := by simpa [map_inv] using K.inv_mem h
    have heq : g = a⁻¹ * τ g⁻¹ * b⁻¹ := by rw [hg]; group
    rw [heq]
    exact K.mul_mem (K.mul_mem (K.inv_mem ha) hτinv) (K.inv_mem hb)
  · intro h
    obtain ⟨a, ha, b, hb, hg⟩ := hτg g⁻¹
    rw [inv_inv] at hg
    rw [hg]
    exact K.mul_mem (K.mul_mem ha (K.inv_mem h)) hb

private theorem heckeOp_adjoint_term {K : Subgroup G} {f : G → A} (hf : K.IsHeckeFunction f)
    (τ : G ≃* G) (hτg : ∀ g : G, ∃ a ∈ K, ∃ b ∈ K, τ g⁻¹ = a * g * b)
    {σ : A →+* A} {π : Representation A G W} {π' : Representation A G W'}
    (B : W →ₛₗ[σ] W' →ₗ[A] Z) {v : W} {v' : W'}
    (hv : ∀ k ∈ K, π k v = v) (hv' : ∀ k ∈ K, π' k v' = v')
    (hB : ∀ (g : G) (x : W) (y : W'), B (π g x) (π' g y) = B x y) (g : G) :
    f (τ g)⁻¹ = f g ∧ B v (π' (τ g) v') = B (π g v) v' := by
  obtain ⟨a, ha, b, hb, hg⟩ := hτg g⁻¹
  rw [inv_inv] at hg
  have hmove (x : G) (w : W) (w' : W') : B w (π' x w') = B (π x⁻¹ w) w' := by
    rw [← hB x⁻¹ w (π' x w'), ← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one,
      one_apply_eq_self]
  refine ⟨?_, ?_⟩
  · have hinv : (τ g)⁻¹ = b⁻¹ * g * a⁻¹ := by rw [hg]; group
    rw [hinv, hf.mul_right _ (K.inv_mem ha), hf.mul_left _ (K.inv_mem hb)]
  · rw [hg, map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp, hv' b hb, hmove,
      hv _ (K.inv_mem ha), hmove, inv_inv]

/-- **Gelfand's trick (adjointness).** If `τ : G ≃* G` sends every `g⁻¹` into `K * g * K`, then
for any Hecke function `f`, ring endomorphism `σ`, and `G`-invariant `σ`-sesquilinear pairing `B`,
the dual function `g ↦ σ (f g⁻¹)` is a Hecke function and
`B (π.heckeOp K f v) v' = B v (π'.heckeOp K (fun g ↦ σ (f g⁻¹)) v')`. -/
theorem Subgroup.IsHeckeFunction.heckeOp_adjoint {K : Subgroup G} {f : G → A}
    (hf : K.IsHeckeFunction f) (τ : G ≃* G)
    (hτg : ∀ g : G, ∃ a ∈ K, ∃ b ∈ K, τ g⁻¹ = a * g * b)
    {σ : A →+* A} {π : Representation A G W} {π' : Representation A G W'}
    (B : W →ₛₗ[σ] W' →ₗ[A] Z) {v : W} {v' : W'}
    (hv : ∀ k ∈ K, π k v = v) (hv' : ∀ k ∈ K, π' k v' = v')
    (hB : ∀ (g : G) (x : W) (y : W'), B (π g x) (π' g y) = B x y) :
    K.IsHeckeFunction (fun g ↦ σ (f g⁻¹)) ∧
      B (π.heckeOp K f v) v' = B v (π'.heckeOp K (fun g ↦ σ (f g⁻¹)) v') := by
  have hτK : ∀ g : G, τ g ∈ K ↔ g ∈ K := mem_iff_of_doubleCoset hτg
  have hcongr : ∀ a b : G, leftRel K a b ↔ leftRel K (τ a) (τ b) := fun a b ↦ by
    simp [leftRel_apply, ← map_inv, ← map_mul, hτK]
  let e : G ⧸ K ≃ G ⧸ K := Quotient.congr τ.toEquiv hcongr
  have hq_term (q : G ⧸ K) :
      f (e q).out⁻¹ = f q.out ∧ B v (π' (e q).out v') = B (π q.out v) v' := by
    obtain ⟨k, hk, heq⟩ := QuotientGroup.out_congr_eq_mul τ.toEquiv hcongr q
    rw [heq, mul_inv_rev, hf.mul_left _ (K.inv_mem hk), map_mul, mul_apply_eq_comp, hv' k hk]
    exact heckeOp_adjoint_term hf τ hτg B hv hv' hB q.out
  have hfin_adj : {q : G ⧸ K | σ (f q.out⁻¹) ≠ 0}.Finite := by
    refine (hf.finite_support.image e).subset fun q hq ↦ ⟨e.symm q, ?_, e.apply_symm_apply q⟩
    have h1 := (hq_term (e.symm q)).1
    rw [e.apply_symm_apply] at h1
    exact fun h0 ↦ hq (by rw [h1, h0, map_zero])
  have hinv_adj : ∀ g : G, ∀ k ∈ K,
      σ (f (k * g)⁻¹) = σ (f g⁻¹) ∧ σ (f (g * k)⁻¹) = σ (f g⁻¹) := fun g k hk ↦ by
    rw [mul_inv_rev, mul_inv_rev, hf.mul_right _ (K.inv_mem hk), hf.mul_left _ (K.inv_mem hk)]
    exact ⟨rfl, rfl⟩
  refine ⟨⟨hfin_adj, hinv_adj⟩, ?_⟩
  rw [Representation.heckeOp_def, Representation.heckeOp_def, ← LinearMap.flip_apply B _ v',
    map_finsum (B.flip v') (finite_support_smul hf.finite_support _),
    map_finsum (B v) (finite_support_smul (f := fun g ↦ σ (f g⁻¹)) hfin_adj _)]
  refine (finsum_congr fun q ↦ ?_).trans (finsum_comp_equiv e)
  simp only [LinearMap.flip_apply, map_smulₛₗ, RingHom.id_apply, (hq_term q).1, (hq_term q).2]

/-- The Hecke convolution of `f'` and `f` with respect to `K`:
`(K.heckeConv f' f) x = ∑ᶠ q : G ⧸ K, f' q.out * f (q.out⁻¹ * x)`. -/
def Subgroup.heckeConv (K : Subgroup G) (f' f : G → A) (x : G) : A :=
  ∑ᶠ q : G ⧸ K, f' q.out * f (q.out⁻¹ * x)

/-- Evaluation of `Subgroup.heckeConv`. -/
@[simp] theorem Subgroup.heckeConv_apply (K : Subgroup G) (f' f : G → A) (x : G) :
    K.heckeConv f' f x = ∑ᶠ q : G ⧸ K, f' q.out * f (q.out⁻¹ * x) :=
  (rfl)

private theorem mem_conv_prod_image {K : Subgroup G} {f f' : G → A}
    (hf : K.IsHeckeFunction f) {q s : G ⧸ K} (hq' : f' q.out ≠ 0)
    (hs' : f (q.out⁻¹ * s.out) ≠ 0) :
    s ∈ (fun p : (G ⧸ K) × (G ⧸ K) ↦ (↑(p.1.out * p.2.out) : G ⧸ K)) ''
      ({q | f' q.out ≠ 0} ×ˢ {r | f r.out ≠ 0}) := by
  let r₀ : G ⧸ K := QuotientGroup.mk (q.out⁻¹ * s.out)
  obtain ⟨⟨k, hk⟩, hr₀⟩ := QuotientGroup.mk_out_eq_mul K (q.out⁻¹ * s.out)
  refine ⟨(q, r₀), ⟨hq', ?_⟩, ?_⟩
  · simpa only [Set.mem_ofPred_eq, r₀, hr₀, hf.mul_right _ hk] using hs'
  · simp only [r₀]
    rw [hr₀, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
    exact (QuotientGroup.eq.2 (by simpa [leftRel_apply] using K.inv_mem hk)).symm.trans
      (Quotient.out_eq s)

/-- The Hecke convolution of two Hecke functions is a Hecke function. -/
theorem Subgroup.IsHeckeFunction.heckeConv {K : Subgroup G} {f' f : G → A}
    (hf' : K.IsHeckeFunction f') (hf : K.IsHeckeFunction f) :
    K.IsHeckeFunction (K.heckeConv f' f) := by
  refine ⟨?_, fun x k hk ↦ ⟨?_, ?_⟩⟩
  · refine ((hf'.finite_support.prod hf.finite_support).image
      (fun p : (G ⧸ K) × (G ⧸ K) ↦ (↑(p.1.out * p.2.out) : G ⧸ K))).subset fun s hs ↦ ?_
    have hex : ∃ q : G ⧸ K, f' q.out * f (q.out⁻¹ * s.out) ≠ 0 := by
      by_contra h; push Not at h
      exact hs (by simp [Subgroup.heckeConv_apply, finsum_eq_zero_of_forall_eq_zero h])
    obtain ⟨q, hq⟩ := hex
    exact mem_conv_prod_image hf (left_ne_zero_of_mul hq) (right_ne_zero_of_mul hq)
  · simp only [Subgroup.heckeConv_apply]
    have hcongr : ∀ a b : G, leftRel K a b ↔ leftRel K (k * a) (k * b) := fun a b ↦ by
      simp [leftRel_apply, mul_assoc]
    refine ((finsum_congr fun q ↦ ?_).trans
      (finsum_comp_equiv (Quotient.congr (Equiv.mulLeft k) hcongr))).symm
    obtain ⟨k', hk', heq⟩ := QuotientGroup.out_congr_eq_mul (Equiv.mulLeft k) hcongr q
    have hinv : (k * q.out * k')⁻¹ * (k * x) = k'⁻¹ * (q.out⁻¹ * x) := by group
    rw [heq, Equiv.coe_mulLeft, hf'.mul_right _ hk', hf'.mul_left _ hk, hinv,
      hf.mul_left _ (K.inv_mem hk')]
  · simp only [Subgroup.heckeConv_apply]
    refine finsum_congr fun q ↦ ?_
    rw [← mul_assoc, hf.mul_right _ hk]

/-- Composition of two Hecke operators on a `K`-fixed vector is the Hecke operator of their
convolution. -/
theorem Subgroup.IsHeckeFunction.heckeOp_comp {K : Subgroup G} {π : Representation A G W}
    {f f' : G → A} {v : W} (hf : K.IsHeckeFunction f) (hf' : K.IsHeckeFunction f')
    (hv : ∀ k ∈ K, π k v = v) :
    π.heckeOp K f' (π.heckeOp K f v) = π.heckeOp K (K.heckeConv f' f) v := by
  have hfin_f := finite_support_smul hf.finite_support (fun q : G ⧸ K ↦ π q.out v)
  have hS : ((fun p : (G ⧸ K) × (G ⧸ K) ↦ (↑(p.1.out * p.2.out) : G ⧸ K)) ''
      ({q | f' q.out ≠ 0} ×ˢ {r | f r.out ≠ 0})).Finite :=
    (hf'.finite_support.prod hf.finite_support).image _
  have hinner (q : G ⧸ K) :
      π q.out (π.heckeOp K f v) = ∑ r ∈ hfin_f.toFinset, f r.out • π (q.out * r.out) v := by
    rw [Representation.heckeOp_def, finsum_eq_sum _ hfin_f, map_sum]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [map_smul, map_mul, mul_apply_eq_comp]
  rw [Representation.heckeOp_def,
    finsum_eq_sum_of_support_subset _ (s := hf'.finite_support.toFinset)
      (fun q hq ↦ hf'.finite_support.mem_toFinset.2 (support_smul_subset _ hq))]
  simp_rw [hinner, Finset.smul_sum, smul_smul]
  have hstep : ∀ q ∈ hf'.finite_support.toFinset,
      ∑ r ∈ hfin_f.toFinset, (f' q.out * f r.out) • π (q.out * r.out) v =
        ∑ s ∈ hS.toFinset, (f' q.out * f (q.out⁻¹ * s.out)) • π s.out v := fun q hq ↦ by
    have hcongr : ∀ a b : G, leftRel K a b ↔ leftRel K (q.out * a) (q.out * b) := fun a b ↦ by
      simp [leftRel_apply, mul_assoc]
    have h1 := (finsum_eq_sum_of_support_subset (f := fun r : G ⧸ K ↦
      (f' q.out * f r.out) • π (q.out * r.out) v) fun r hr ↦
      hfin_f.mem_toFinset.2 fun h0 ↦ hr (by
        dsimp only at h0 ⊢
        rw [mul_smul, map_mul, mul_apply_eq_comp, ← map_smul, h0, map_zero, smul_zero])).symm
    have h2 : (∑ᶠ r : G ⧸ K, (f' q.out * f r.out) • π (q.out * r.out) v) =
        ∑ᶠ s : G ⧸ K, (f' q.out * f (q.out⁻¹ * s.out)) • π s.out v := by
      refine (finsum_congr fun r ↦ ?_).trans
        (finsum_comp_equiv (Quotient.congr (Equiv.mulLeft q.out) hcongr))
      obtain ⟨k, hk, heq⟩ := QuotientGroup.out_congr_eq_mul (Equiv.mulLeft q.out) hcongr r
      rw [heq, Equiv.coe_mulLeft, ← mul_assoc, inv_mul_cancel_left, hf.mul_right _ hk]
      conv_rhs => rw [map_mul, mul_apply_eq_comp, hv k hk]
    exact h1.trans <| h2.trans <| finsum_eq_sum_of_support_subset _ fun s hs ↦
      hS.mem_toFinset.2 (mem_conv_prod_image hf (hf'.finite_support.mem_toFinset.1 hq)
        fun h0 ↦ hs (by simp [h0]))
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm, Representation.heckeOp_def,
    finsum_eq_sum_of_support_subset _ (s := hS.toFinset) fun r hr ↦ ?_]
  · refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [← Finset.sum_smul, Subgroup.heckeConv_apply,
      finsum_eq_sum_of_support_subset _ (s := hf'.finite_support.toFinset)
        (fun q hq ↦ hf'.finite_support.mem_toFinset.2 (left_ne_zero_of_mul hq))]
  · have hex : ∃ q : G ⧸ K, f' q.out * f (q.out⁻¹ * r.out) ≠ 0 := by
      by_contra h; push Not at h
      exact hr (by simp [Subgroup.heckeConv_apply, finsum_eq_zero_of_forall_eq_zero h])
    obtain ⟨q, hq⟩ := hex
    exact hS.mem_toFinset.2 (mem_conv_prod_image hf
      (left_ne_zero_of_mul hq) (right_ne_zero_of_mul hq))

/-- **Gelfand's trick (commutativity).** If `τ : G ≃* G` sends every `g⁻¹` into `K * g * K`, then
any two Hecke operators commute on `K`-fixed vectors. -/
theorem Subgroup.IsHeckeFunction.heckeOp_comm {K : Subgroup G} {π : Representation A G W}
    {f f' : G → A} {v : W} (hf : K.IsHeckeFunction f) (hf' : K.IsHeckeFunction f')
    (hv : ∀ k ∈ K, π k v = v) (τ : G ≃* G)
    (hτg : ∀ g : G, ∃ a ∈ K, ∃ b ∈ K, τ g⁻¹ = a * g * b) :
    π.heckeOp K f (π.heckeOp K f' v) = π.heckeOp K f' (π.heckeOp K f v) := by
  have hτK : ∀ g : G, τ g ∈ K ↔ g ∈ K := mem_iff_of_doubleCoset hτg
  have happly_τ (h : G → A) (hh : K.IsHeckeFunction h) (g : G) : h (τ g⁻¹) = h g := by
    obtain ⟨a, ha, b, hb, hg⟩ := hτg g
    rw [hg, hh.mul_right _ hb, hh.mul_left _ ha]
  rw [hf'.heckeOp_comp hf hv, hf.heckeOp_comp hf' hv]
  congr 1
  funext x
  simp only [Subgroup.heckeConv_apply]
  obtain ⟨a, ha, b, hb, hb_eq⟩ := hτg x
  let φ : G ≃ G := τ.toEquiv.trans (Equiv.mulLeft (x * b))
  have hcongr : ∀ g g' : G, leftRel K g g' ↔ leftRel K (φ g) (φ g') := fun g g' ↦ by
    simp [φ, leftRel_apply, ← map_inv, ← map_mul, hτK, mul_assoc]
  refine (finsum_congr fun q ↦ ?_).trans (finsum_comp_equiv (Quotient.congr φ hcongr))
  obtain ⟨k, hk, heq⟩ := QuotientGroup.out_congr_eq_mul φ hcongr q
  have hf'_eq : f' (x * b * τ q.out * k) = f' (q.out⁻¹ * x) := by
    rw [← happly_τ f' hf' (q.out⁻¹ * x), hf'.mul_right _ hk]
    have hmul : τ (q.out⁻¹ * x)⁻¹ = a * (x * b * τ q.out) := by
      rw [mul_inv_rev, inv_inv, map_mul, hb_eq]; group
    rw [hmul, hf'.mul_left _ ha]
  have hf_eq : f ((x * b * τ q.out * k)⁻¹ * x) = f q.out := by
    rw [← happly_τ f hf q.out]
    have hmul : (x * b * τ q.out * k)⁻¹ * x = k⁻¹ * (τ q.out⁻¹ * b⁻¹) := by
      rw [map_inv]; group
    rw [hmul, hf.mul_left _ (K.inv_mem hk), hf.mul_right _ (K.inv_mem hb)]
  rw [heq]
  simp only [φ, Equiv.trans_apply, Equiv.coe_mulLeft, MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe,
    hf'_eq, hf_eq]
  exact mul_comm _ _

end AbstractHecke

end
