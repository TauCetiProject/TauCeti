/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.FiniteSupport.Basic
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
(`Subgroup.map_mem_iff_of_inv_mem_doubleCoset`) and:
1. For any ring endomorphism `σ : A →+* A`, the dual function `f^∨(g) = σ (f g⁻¹)` is again a
   Hecke function (`Subgroup.IsHeckeFunction.dual`), and for any `G`-invariant pairing
   `B : W →ₛₗ[σ] W' →ₗ[A] Z`, `B (π.heckeOp K f v) v' = B v (π'.heckeOp K f^∨ v')`
   (`Subgroup.IsHeckeFunction.heckeOp_adjoint`).
2. Convolution of Hecke functions is commutative (`Subgroup.IsHeckeFunction.heckeConv_comm`), so
   any two Hecke operators commute on `K`-fixed vectors (`Subgroup.IsHeckeFunction.heckeOp_comm`).

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

/-- The zero function is a Hecke function. -/
theorem Subgroup.isHeckeFunction_zero (K : Subgroup G) : K.IsHeckeFunction (0 : G → A) :=
  ⟨by simp, fun _ _ _ ↦ ⟨rfl, rfl⟩⟩

/-- The sum of two Hecke functions is a Hecke function. -/
theorem Subgroup.IsHeckeFunction.add {K : Subgroup G} {f f' : G → A}
    (hf : K.IsHeckeFunction f) (hf' : K.IsHeckeFunction f') :
    K.IsHeckeFunction (f + f') := by
  refine ⟨(hf.finite_support.union hf'.finite_support).subset fun q hq ↦ ?_,
    fun g k hk ↦ ⟨by simp [hf.mul_left g hk, hf'.mul_left g hk],
      by simp [hf.mul_right g hk, hf'.mul_right g hk]⟩⟩
  by_contra h
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at h
  exact hq (by simp [h.1, h.2])

/-- A scalar multiple of a Hecke function is a Hecke function. -/
theorem Subgroup.IsHeckeFunction.smul {K : Subgroup G} {f : G → A}
    (c : A) (hf : K.IsHeckeFunction f) : K.IsHeckeFunction (c • f) :=
  ⟨hf.finite_support.subset fun _ hq h0 ↦ hq (by simp [h0]),
    fun g k hk ↦ ⟨by simp [hf.mul_left g hk], by simp [hf.mul_right g hk]⟩⟩

/-- The indicator function of `K` is a Hecke function. -/
theorem Subgroup.isHeckeFunction_indicator_one (K : Subgroup G) :
    K.IsHeckeFunction (Set.indicator (K : Set G) (1 : G → A)) := by
  refine ⟨(Set.finite_singleton (QuotientGroup.mk (1 : G))).subset fun q hq ↦ ?_,
    fun g k hk ↦ ⟨?_, ?_⟩⟩
  · have hout : q.out ∈ (K : Set G) := by
      by_contra h
      exact hq (Set.indicator_of_notMem h _)
    exact Set.mem_singleton_iff.2 (QuotientGroup.out_mem_iff.1 hout)
  · by_cases hg : g ∈ K
    · simp [Set.indicator_of_mem (K.mul_mem hk hg), Set.indicator_of_mem hg]
    · have hkg : k * g ∉ (K : Set G) := fun h ↦ hg (by simpa using K.mul_mem (K.inv_mem hk) h)
      simp [Set.indicator_of_notMem hkg, Set.indicator_of_notMem hg]
  · by_cases hg : g ∈ K
    · simp [Set.indicator_of_mem (K.mul_mem hg hk), Set.indicator_of_mem hg]
    · have hgk : g * k ∉ (K : Set G) := fun h ↦ hg (by simpa using K.mul_mem h (K.inv_mem hk))
      simp [Set.indicator_of_notMem hgk, Set.indicator_of_notMem hg]

/-- The Hecke operator attached to `f : G → A` on a representation `π : Representation A G W`,
defined by summing `f q.out • π q.out v` over left cosets `q : G ⧸ K`. -/
def Representation.heckeOp (π : Representation A G W) (K : Subgroup G) (f : G → A) (v : W) : W :=
  ∑ᶠ q : G ⧸ K, f q.out • π q.out v

/-- Definitional unfolding of `Representation.heckeOp`. -/
theorem Representation.heckeOp_def (π : Representation A G W) (K : Subgroup G) (f : G → A) (v : W) :
    π.heckeOp K f v = ∑ᶠ q : G ⧸ K, f q.out • π q.out v :=
  (rfl)

/-- On a `K`-fixed vector, the Hecke operator of a right `K`-invariant function can be computed
using any section `s : G ⧸ K → G` of `QuotientGroup.mk`. -/
theorem Representation.heckeOp_eq_finsum_of_mk {K : Subgroup G} (π : Representation A G W)
    {f : G → A} {v : W} (hf : ∀ g : G, ∀ k ∈ K, f (g * k) = f g) (hv : ∀ k ∈ K, π k v = v)
    (s : G ⧸ K → G) (hs : ∀ q : G ⧸ K, QuotientGroup.mk (s q) = q) :
    π.heckeOp K f v = ∑ᶠ q : G ⧸ K, f (s q) • π (s q) v := by
  rw [heckeOp_def]
  refine finsum_congr fun q ↦ ?_
  obtain ⟨⟨k, hk⟩, hsq⟩ := QuotientGroup.mk_out_eq_mul K (s q)
  rw [hs q] at hsq
  rw [hsq, hf _ _ hk, map_mul, mul_apply_eq_comp, hv k hk]

@[simp] theorem Representation.heckeOp_zero_right (π : Representation A G W) (K : Subgroup G)
    (f : G → A) : π.heckeOp K f 0 = 0 := by
  simp [heckeOp_def]

@[simp] theorem Representation.heckeOp_zero_left (π : Representation A G W) (K : Subgroup G)
    (v : W) : π.heckeOp K 0 v = 0 := by
  simp [heckeOp_def]

theorem Representation.heckeOp_add_right {K : Subgroup G} (π : Representation A G W) {f : G → A}
    (hf : {q : G ⧸ K | f q.out ≠ 0}.Finite) (v w : W) :
    π.heckeOp K f (v + w) = π.heckeOp K f v + π.heckeOp K f w := by
  simp only [heckeOp_def, map_add, smul_add]
  exact finsum_add_distrib (Function.HasFiniteSupport.smul_left hf _)
    (Function.HasFiniteSupport.smul_left hf _)

theorem Representation.heckeOp_smul_right {K : Subgroup G} (π : Representation A G W) {f : G → A}
    (hf : {q : G ⧸ K | f q.out ≠ 0}.Finite) (c : A) (v : W) :
    π.heckeOp K f (c • v) = c • π.heckeOp K f v := by
  simp only [heckeOp_def, map_smul, smul_comm _ c]
  exact (map_finsum (LinearMap.lsmul A W c) (Function.HasFiniteSupport.smul_left hf _)).symm

theorem Representation.heckeOp_add_left {K : Subgroup G} (π : Representation A G W) {f f' : G → A}
    (hf : {q : G ⧸ K | f q.out ≠ 0}.Finite) (hf' : {q : G ⧸ K | f' q.out ≠ 0}.Finite) (v : W) :
    π.heckeOp K (f + f') v = π.heckeOp K f v + π.heckeOp K f' v := by
  simp only [heckeOp_def, Pi.add_apply, add_smul]
  exact finsum_add_distrib (Function.HasFiniteSupport.smul_left hf _)
    (Function.HasFiniteSupport.smul_left hf' _)

theorem Representation.heckeOp_smul_left {K : Subgroup G} (π : Representation A G W) {f : G → A}
    (hf : {q : G ⧸ K | f q.out ≠ 0}.Finite) (c : A) (v : W) :
    π.heckeOp K (c • f) v = c • π.heckeOp K f v := by
  simp only [heckeOp_def, Pi.smul_apply, smul_eq_mul, mul_smul]
  exact (map_finsum (LinearMap.lsmul A W c) (Function.HasFiniteSupport.smul_left hf _)).symm

/-- The indicator function of `K` acts as the identity on `K`-fixed vectors. -/
theorem Representation.heckeOp_indicator_one {K : Subgroup G} (π : Representation A G W) {v : W}
    (hv : ∀ k ∈ K, π k v = v) :
    π.heckeOp K (Set.indicator (K : Set G) 1) v = v := by
  rw [heckeOp_def, finsum_eq_single _ (QuotientGroup.mk (1 : G))]
  · have hout : ((QuotientGroup.mk (1 : G) : G ⧸ K).out : G) ∈ K :=
      QuotientGroup.out_mem_iff.2 rfl
    simp [hv _ hout]
  · intro q hq
    have hout : q.out ∉ (K : Set G) := fun hmem ↦
      hq (QuotientGroup.out_mem_iff.1 hmem)
    simp [Set.indicator_of_notMem hout]

/-- The Hecke operator of a bi-`K`-invariant function sends `K`-fixed vectors to `K`-fixed
vectors. -/
theorem Representation.heckeOp_mem_fixed {K : Subgroup G} (π : Representation A G W) {f : G → A}
    {v : W} (hf : K.IsHeckeFunction f) (hv : ∀ k ∈ K, π k v = v) {k : G} (hk : k ∈ K) :
    π k (π.heckeOp K f v) = π.heckeOp K f v := by
  have hfin : (Function.support fun q : G ⧸ K ↦ f q.out • π q.out v).Finite :=
    Function.HasFiniteSupport.smul_left hf.finite_support _
  rw [heckeOp_def, map_finsum (π k) hfin]
  have h1 : (∑ᶠ q : G ⧸ K, π k (f q.out • π q.out v)) =
      ∑ᶠ q : G ⧸ K, f (k * q.out) • π (k * q.out) v :=
    finsum_congr fun q ↦ by rw [map_smul, map_mul, mul_apply_eq_comp, hf.mul_left _ hk]
  rw [h1]
  exact QuotientGroup.finsum_mulLeft_eq k (fun g ↦ f g • π g v) fun g k' hk' ↦ by
    rw [hf.mul_right _ hk', map_mul, mul_apply_eq_comp, hv k' hk']

private theorem apply_map_inv_of_doubleCoset {K : Subgroup G} {f : G → A}
    (hf : K.IsHeckeFunction f) (τ : G ≃* G)
    (hτg : ∀ g : G, ∃ a ∈ K, ∃ b ∈ K, τ g⁻¹ = a * g * b) (g : G) :
    f (τ g⁻¹) = f g := by
  obtain ⟨a, ha, b, hb, hg⟩ := hτg g
  rw [hg, hf.mul_right _ hb, hf.mul_left _ ha]

/-- If `τ : G ≃* G` sends every `g⁻¹` into `K * g * K`, then for any Hecke function `f` and ring
endomorphism `σ : A →+* A`, the dual function `g ↦ σ (f g⁻¹)` is again a Hecke function. -/
theorem Subgroup.IsHeckeFunction.dual {K : Subgroup G} {f : G → A} (hf : K.IsHeckeFunction f)
    (σ : A →+* A) (τ : G ≃* G) (hτg : ∀ g : G, ∃ a ∈ K, ∃ b ∈ K, τ g⁻¹ = a * g * b) :
    K.IsHeckeFunction (fun g ↦ σ (f g⁻¹)) := by
  let e := K.quotientEquivOfInvMemDoubleCoset τ hτg
  refine ⟨(hf.finite_support.image e).subset fun q hq ↦ ⟨e.symm q, ?_, e.apply_symm_apply q⟩,
    fun g k hk ↦ ⟨?_, ?_⟩⟩
  · obtain ⟨k, hk, heq⟩ := K.out_quotientEquivOfInvMemDoubleCoset_eq_mul τ hτg (e.symm q)
    rw [e.apply_symm_apply] at heq
    have h1 : f q.out⁻¹ = f (e.symm q).out := by
      rw [heq, mul_inv_rev, hf.mul_left _ (K.inv_mem hk), ← map_inv,
        apply_map_inv_of_doubleCoset hf τ hτg]
    exact fun h0 ↦ hq (by dsimp only; rw [h1, h0, map_zero])
  · dsimp only; rw [mul_inv_rev, hf.mul_right _ (K.inv_mem hk)]
  · dsimp only; rw [mul_inv_rev, hf.mul_left _ (K.inv_mem hk)]

/-- **Gelfand's trick (adjointness).** If `τ : G ≃* G` sends every `g⁻¹` into `K * g * K`, then
for any Hecke function `f`, ring endomorphism `σ`, and `G`-invariant `σ`-sesquilinear pairing `B`,
`B (π.heckeOp K f v) v' = B v (π'.heckeOp K (fun g ↦ σ (f g⁻¹)) v')`. -/
theorem Subgroup.IsHeckeFunction.heckeOp_adjoint {K : Subgroup G} {f : G → A}
    (hf : K.IsHeckeFunction f) (τ : G ≃* G)
    (hτg : ∀ g : G, ∃ a ∈ K, ∃ b ∈ K, τ g⁻¹ = a * g * b)
    {σ : A →+* A} {π : Representation A G W} {π' : Representation A G W'}
    (B : W →ₛₗ[σ] W' →ₗ[A] Z) {v : W} {v' : W'}
    (hv : ∀ k ∈ K, π k v = v) (hv' : ∀ k ∈ K, π' k v' = v')
    (hB : ∀ (g : G) (x : W) (y : W'), B (π g x) (π' g y) = B x y) :
    B (π.heckeOp K f v) v' = B v (π'.heckeOp K (fun g ↦ σ (f g⁻¹)) v') := by
  let e := K.quotientEquivOfInvMemDoubleCoset τ hτg
  have hmove (x : G) (w : W) (w' : W') : B w (π' x w') = B (π x⁻¹ w) w' := by
    rw [← hB x⁻¹ w (π' x w'), ← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one,
      one_apply_eq_self]
  have hq_term (q : G ⧸ K) :
      f (e q).out⁻¹ = f q.out ∧ B v (π' (e q).out v') = B (π q.out v) v' := by
    obtain ⟨k, hk, heq⟩ := K.out_quotientEquivOfInvMemDoubleCoset_eq_mul τ hτg q
    obtain ⟨a, ha, b, hb, hg⟩ := hτg q.out⁻¹
    rw [inv_inv] at hg
    have heq' : (e q).out = a * q.out⁻¹ * (b * k) := by
      simpa [e, hg, mul_assoc] using heq
    refine ⟨?_, ?_⟩
    · rw [heq, mul_inv_rev, hf.mul_left _ (K.inv_mem hk), ← map_inv,
        apply_map_inv_of_doubleCoset hf τ hτg]
    · have hbk : π' (a * q.out⁻¹ * (b * k)) v' = π' a (π' q.out⁻¹ v') := by
        simp [map_mul, hv' _ hk, hv' _ hb]
      rw [heq', hbk, hmove a, hv _ (K.inv_mem ha), hmove q.out⁻¹, inv_inv]
  have hfin : (Function.support fun q : G ⧸ K ↦ f q.out • π q.out v).Finite :=
    Function.HasFiniteSupport.smul_left hf.finite_support _
  have hfin' : (Function.support fun q : G ⧸ K ↦ σ (f q.out⁻¹) • π' q.out v').Finite :=
    Function.HasFiniteSupport.smul_left (hf.dual σ τ hτg).finite_support _
  rw [Representation.heckeOp_def, Representation.heckeOp_def, ← LinearMap.flip_apply B _ v',
    map_finsum (B.flip v') hfin, map_finsum (B v) hfin']
  refine (finsum_congr fun q ↦ ?_).trans (finsum_comp_equiv e)
  simp only [LinearMap.flip_apply, map_smulₛₗ, RingHom.id_apply, (hq_term q).1, (hq_term q).2]

/-- The Hecke convolution of `f'` and `f` with respect to `K`:
`(K.heckeConv f' f) x = ∑ᶠ q : G ⧸ K, f' q.out * f (q.out⁻¹ * x)`. -/
def Subgroup.heckeConv (K : Subgroup G) (f' f : G → A) (x : G) : A :=
  ∑ᶠ q : G ⧸ K, f' q.out * f (q.out⁻¹ * x)

/-- Definitional unfolding of `Subgroup.heckeConv`. -/
theorem Subgroup.heckeConv_def (K : Subgroup G) (f' f : G → A) (x : G) :
    K.heckeConv f' f x = ∑ᶠ q : G ⧸ K, f' q.out * f (q.out⁻¹ * x) :=
  (rfl)

@[simp] theorem Subgroup.heckeConv_zero_left (K : Subgroup G) (f : G → A) :
    K.heckeConv 0 f = 0 := by
  funext x
  simp [heckeConv_def]

@[simp] theorem Subgroup.heckeConv_zero_right (K : Subgroup G) (f' : G → A) :
    K.heckeConv f' 0 = 0 := by
  funext x
  simp [heckeConv_def]

theorem Subgroup.heckeConv_add_left (K : Subgroup G) {f₁ f₂ : G → A}
    (hf₁ : {q : G ⧸ K | f₁ q.out ≠ 0}.Finite) (hf₂ : {q : G ⧸ K | f₂ q.out ≠ 0}.Finite)
    (f : G → A) :
    K.heckeConv (f₁ + f₂) f = K.heckeConv f₁ f + K.heckeConv f₂ f := by
  funext x
  simp only [heckeConv_def, Pi.add_apply, add_mul]
  exact finsum_add_distrib (Function.HasFiniteSupport.mul_left hf₁ _)
    (Function.HasFiniteSupport.mul_left hf₂ _)

theorem Subgroup.heckeConv_add_right (K : Subgroup G) {f' : G → A}
    (hf' : {q : G ⧸ K | f' q.out ≠ 0}.Finite) (f₁ f₂ : G → A) :
    K.heckeConv f' (f₁ + f₂) = K.heckeConv f' f₁ + K.heckeConv f' f₂ := by
  funext x
  simp only [heckeConv_def, Pi.add_apply, mul_add]
  exact finsum_add_distrib (Function.HasFiniteSupport.mul_left hf' _)
    (Function.HasFiniteSupport.mul_left hf' _)

theorem Subgroup.heckeConv_smul_left (K : Subgroup G) {f' : G → A}
    (hf' : {q : G ⧸ K | f' q.out ≠ 0}.Finite) (c : A) (f : G → A) :
    K.heckeConv (c • f') f = c • K.heckeConv f' f := by
  funext x
  simp only [heckeConv_def, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact (map_finsum (LinearMap.lsmul A A c) (Function.HasFiniteSupport.mul_left hf' _)).symm

theorem Subgroup.heckeConv_smul_right (K : Subgroup G) {f' : G → A}
    (hf' : {q : G ⧸ K | f' q.out ≠ 0}.Finite) (c : A) (f : G → A) :
    K.heckeConv f' (c • f) = c • K.heckeConv f' f := by
  funext x
  simp only [heckeConv_def, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
  exact (map_finsum (LinearMap.lsmul A A c) (Function.HasFiniteSupport.mul_left hf' _)).symm

/-- The indicator function of `K` is a left unit for Hecke convolution on left `K`-invariant
functions. -/
@[simp] theorem Subgroup.heckeConv_indicator_one_left {K : Subgroup G} {f : G → A}
    (hf : ∀ g : G, ∀ k ∈ K, f (k * g) = f g) :
    K.heckeConv (Set.indicator (K : Set G) 1) f = f := by
  funext x
  rw [heckeConv_def, finsum_eq_single _ (QuotientGroup.mk (1 : G))]
  · have hout : ((QuotientGroup.mk (1 : G) : G ⧸ K).out : G) ∈ K :=
      QuotientGroup.out_mem_iff.2 rfl
    simp [hf x _ (K.inv_mem hout)]
  · intro q hq
    have hout : q.out ∉ (K : Set G) := fun hmem ↦
      hq (QuotientGroup.out_mem_iff.1 hmem)
    simp [Set.indicator_of_notMem hout]

/-- The indicator function of `K` is a right unit for Hecke convolution on right `K`-invariant
functions. -/
@[simp] theorem Subgroup.heckeConv_indicator_one_right {K : Subgroup G} {f' : G → A}
    (hf' : ∀ g : G, ∀ k ∈ K, f' (g * k) = f' g) :
    K.heckeConv f' (Set.indicator (K : Set G) 1) = f' := by
  funext x
  rw [heckeConv_def, finsum_eq_single _ (QuotientGroup.mk x)]
  · obtain ⟨⟨k, hk⟩, hkx⟩ := QuotientGroup.mk_out_eq_mul K x
    simp [hkx, hf' x _ hk, K.inv_mem hk]
  · intro q hq
    have hnot : q.out⁻¹ * x ∉ (K : Set G) := fun hmem ↦ by
      apply hq
      rw [← Quotient.out_eq q]
      exact QuotientGroup.eq.2 hmem
    simp [Set.indicator_of_notMem hnot]

private theorem mem_conv_prod_image {K : Subgroup G} {f f' : G → A}
    (hf_right : ∀ g : G, ∀ k ∈ K, f (g * k) = f g) {q s : G ⧸ K} (hq' : f' q.out ≠ 0)
    (hs' : f (q.out⁻¹ * s.out) ≠ 0) :
    s ∈ (fun p : (G ⧸ K) × (G ⧸ K) ↦ (↑(p.1.out * p.2.out) : G ⧸ K)) ''
      ({q | f' q.out ≠ 0} ×ˢ {r | f r.out ≠ 0}) := by
  let r₀ : G ⧸ K := QuotientGroup.mk (q.out⁻¹ * s.out)
  obtain ⟨⟨k, hk⟩, hr₀⟩ := QuotientGroup.mk_out_eq_mul K (q.out⁻¹ * s.out)
  refine ⟨(q, r₀), ⟨hq', ?_⟩, ?_⟩
  · simpa only [Set.mem_ofPred_eq, r₀, hr₀, hf_right _ _ hk] using hs'
  · simp only [r₀]
    rw [hr₀, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
    exact (QuotientGroup.eq.2 (by simpa [leftRel_apply] using K.inv_mem hk)).symm.trans
      (Quotient.out_eq s)

private theorem mem_conv_prod_image_of_heckeConv_ne_zero {K : Subgroup G} {f f' : G → A}
    (hf_right : ∀ g : G, ∀ k ∈ K, f (g * k) = f g) {s : G ⧸ K} (hs : K.heckeConv f' f s.out ≠ 0) :
    s ∈ (fun p : (G ⧸ K) × (G ⧸ K) ↦ (↑(p.1.out * p.2.out) : G ⧸ K)) ''
      ({q | f' q.out ≠ 0} ×ˢ {r | f r.out ≠ 0}) := by
  have hex : ∃ q : G ⧸ K, f' q.out * f (q.out⁻¹ * s.out) ≠ 0 := by
    by_contra h; push Not at h
    exact hs (by simp [Subgroup.heckeConv_def, finsum_eq_zero_of_forall_eq_zero h])
  obtain ⟨q, hq⟩ := hex
  exact mem_conv_prod_image hf_right (left_ne_zero_of_mul hq) (right_ne_zero_of_mul hq)

/-- The Hecke convolution of two Hecke functions is a Hecke function. -/
theorem Subgroup.IsHeckeFunction.heckeConv {K : Subgroup G} {f' f : G → A}
    (hf' : K.IsHeckeFunction f') (hf : K.IsHeckeFunction f) :
    K.IsHeckeFunction (K.heckeConv f' f) := by
  refine ⟨((hf'.finite_support.prod hf.finite_support).image _).subset fun _ hs ↦
      mem_conv_prod_image_of_heckeConv_ne_zero (fun g _ hk ↦ hf.mul_right g hk) hs,
    fun x k hk ↦ ⟨?_, ?_⟩⟩
  · simp only [Subgroup.heckeConv_def]
    have h1 : (∑ᶠ q : G ⧸ K, f' (k * q.out) * f ((k * q.out)⁻¹ * (k * x))) =
        ∑ᶠ q : G ⧸ K, f' q.out * f (q.out⁻¹ * x) :=
      finsum_congr fun q ↦ by
        have hinv : (k * q.out)⁻¹ * (k * x) = q.out⁻¹ * x := by group
        rw [hf'.mul_left _ hk, hinv]
    rw [← h1]
    exact (QuotientGroup.finsum_mulLeft_eq k (fun g ↦ f' g * f (g⁻¹ * (k * x))) fun g k' hk' ↦ by
      rw [hf'.mul_right _ hk', mul_inv_rev, mul_assoc, hf.mul_left _ (K.inv_mem hk')]).symm
  · simp only [Subgroup.heckeConv_def]
    exact finsum_congr fun q ↦ by rw [← mul_assoc, hf.mul_right _ hk]

/-- Composition of two Hecke operators on a `K`-fixed vector is the Hecke operator of their
convolution, assuming finite coset support and right `K`-invariance of `f`. -/
theorem Representation.heckeOp_comp {K : Subgroup G} (π : Representation A G W)
    {f f' : G → A} {v : W}
    (hf_supp : {q : G ⧸ K | f q.out ≠ 0}.Finite)
    (hf_right : ∀ g : G, ∀ k ∈ K, f (g * k) = f g)
    (hf'_supp : {q : G ⧸ K | f' q.out ≠ 0}.Finite)
    (hv : ∀ k ∈ K, π k v = v) :
    π.heckeOp K f' (π.heckeOp K f v) = π.heckeOp K (K.heckeConv f' f) v := by
  have hfin_f : (Function.support fun q : G ⧸ K ↦ f q.out • π q.out v).Finite :=
    Function.HasFiniteSupport.smul_left hf_supp _
  have hS : ((fun p : (G ⧸ K) × (G ⧸ K) ↦ (↑(p.1.out * p.2.out) : G ⧸ K)) ''
      ({q | f' q.out ≠ 0} ×ˢ {r | f r.out ≠ 0})).Finite :=
    (hf'_supp.prod hf_supp).image _
  have hinner (q : G ⧸ K) :
      π q.out (π.heckeOp K f v) = ∑ r ∈ hfin_f.toFinset, f r.out • π (q.out * r.out) v := by
    rw [Representation.heckeOp_def, finsum_eq_sum _ hfin_f, map_sum]
    exact Finset.sum_congr rfl fun r _ ↦ by rw [map_smul, map_mul, mul_apply_eq_comp]
  rw [Representation.heckeOp_def,
    finsum_eq_sum_of_support_subset (f := fun q : G ⧸ K ↦ f' q.out • π q.out (π.heckeOp K f v))
      (s := hf'_supp.toFinset) (fun q hq ↦ hf'_supp.mem_toFinset.2
        (Function.support_smul_subset_left (fun q : G ⧸ K ↦ f' q.out) _ hq))]
  simp_rw [hinner, Finset.smul_sum, smul_smul]
  have hstep : ∀ q ∈ hf'_supp.toFinset,
      ∑ r ∈ hfin_f.toFinset, (f' q.out * f r.out) • π (q.out * r.out) v =
        ∑ s ∈ hS.toFinset, (f' q.out * f (q.out⁻¹ * s.out)) • π s.out v := fun q hq ↦ by
    have h1 := (finsum_eq_sum_of_support_subset (f := fun r : G ⧸ K ↦
      (f' q.out * f r.out) • π (q.out * r.out) v) fun r hr ↦
      hfin_f.mem_toFinset.2 fun h0 ↦ hr (by
        dsimp only at h0 ⊢
        rw [mul_smul, map_mul, mul_apply_eq_comp, ← map_smul, h0, map_zero, smul_zero])).symm
    have h2 : (∑ᶠ r : G ⧸ K, (f' q.out * f r.out) • π (q.out * r.out) v) =
        ∑ᶠ s : G ⧸ K, (f' q.out * f (q.out⁻¹ * s.out)) • π s.out v := by
      have h3 : (∑ᶠ r : G ⧸ K, (f' q.out * f r.out) • π (q.out * r.out) v) =
          ∑ᶠ r : G ⧸ K, (f' q.out * f (q.out⁻¹ * (q.out * r.out))) • π (q.out * r.out) v :=
        finsum_congr fun r ↦ by rw [inv_mul_cancel_left]
      rw [h3]
      exact QuotientGroup.finsum_mulLeft_eq q.out (fun g ↦ (f' q.out * f (q.out⁻¹ * g)) • π g v)
        fun g k hk ↦ by rw [← mul_assoc, hf_right _ _ hk, map_mul, mul_apply_eq_comp, hv k hk]
    exact h1.trans <| h2.trans <| finsum_eq_sum_of_support_subset _ fun s hs ↦
      hS.mem_toFinset.2 (mem_conv_prod_image hf_right (hf'_supp.mem_toFinset.1 hq)
        fun h0 ↦ hs (by simp [h0]))
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm, Representation.heckeOp_def,
    finsum_eq_sum_of_support_subset (f := fun s : G ⧸ K ↦ K.heckeConv f' f s.out • π s.out v)
      (s := hS.toFinset) fun _ hr ↦
        hS.mem_toFinset.2 (mem_conv_prod_image_of_heckeConv_ne_zero hf_right
          (Function.support_smul_subset_left (fun s : G ⧸ K ↦ K.heckeConv f' f s.out) _ hr))]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [← Finset.sum_smul, Subgroup.heckeConv_def,
    finsum_eq_sum_of_support_subset _ (s := hf'_supp.toFinset)
      (fun q hq ↦ hf'_supp.mem_toFinset.2 (left_ne_zero_of_mul hq))]

/-- Composition of two Hecke operators on a `K`-fixed vector is the Hecke operator of their
convolution. -/
theorem Subgroup.IsHeckeFunction.heckeOp_comp {K : Subgroup G} {π : Representation A G W}
    {f f' : G → A} {v : W} (hf : K.IsHeckeFunction f) (hf' : K.IsHeckeFunction f')
    (hv : ∀ k ∈ K, π k v = v) :
    π.heckeOp K f' (π.heckeOp K f v) = π.heckeOp K (K.heckeConv f' f) v :=
  π.heckeOp_comp hf.finite_support (fun g _ hk ↦ hf.mul_right g hk) hf'.finite_support hv

/-- **Gelfand's trick (commutativity of convolution).** If `τ : G ≃* G` sends every `g⁻¹` into
`K * g * K`, then Hecke convolution is commutative on Hecke functions. -/
theorem Subgroup.IsHeckeFunction.heckeConv_comm {K : Subgroup G} {f f' : G → A}
    (hf : K.IsHeckeFunction f) (hf' : K.IsHeckeFunction f') (τ : G ≃* G)
    (hτg : ∀ g : G, ∃ a ∈ K, ∃ b ∈ K, τ g⁻¹ = a * g * b) :
    K.heckeConv f f' = K.heckeConv f' f := by
  funext x
  simp only [Subgroup.heckeConv_def]
  obtain ⟨a, ha, b, hb, hb_eq⟩ := hτg x
  have hshift := (QuotientGroup.finsum_mulLeft_eq (x * b) (fun g ↦ f' g * f (g⁻¹ * x))
    fun g k hk ↦ by
      rw [hf'.mul_right _ hk, mul_inv_rev, mul_assoc, hf.mul_left _ (K.inv_mem hk)]).symm
  rw [hshift]
  refine (finsum_congr fun q ↦ ?_).trans
    (finsum_comp_equiv (K.quotientEquivOfInvMemDoubleCoset τ hτg))
  obtain ⟨k, hk, heq⟩ := K.out_quotientEquivOfInvMemDoubleCoset_eq_mul τ hτg q
  have hf'_eq : f' (x * b * (τ q.out * k)) = f' (q.out⁻¹ * x) := by
    rw [← apply_map_inv_of_doubleCoset hf' τ hτg (q.out⁻¹ * x), ← mul_assoc, hf'.mul_right _ hk]
    have hmul : τ (q.out⁻¹ * x)⁻¹ = a * (x * b * τ q.out) := by
      rw [mul_inv_rev, inv_inv, map_mul, hb_eq]; group
    rw [hmul, hf'.mul_left _ ha]
  have hf_eq : f ((x * b * (τ q.out * k))⁻¹ * x) = f q.out := by
    rw [← apply_map_inv_of_doubleCoset hf τ hτg q.out]
    have hmul : (x * b * (τ q.out * k))⁻¹ * x = k⁻¹ * (τ q.out⁻¹ * b⁻¹) := by
      rw [map_inv]; group
    rw [hmul, hf.mul_left _ (K.inv_mem hk), hf.mul_right _ (K.inv_mem hb)]
  rw [heq, hf'_eq, hf_eq, mul_comm]

/-- **Gelfand's trick (commutativity of operators).** If `τ : G ≃* G` sends every `g⁻¹` into
`K * g * K`, then any two Hecke operators commute on `K`-fixed vectors. -/
theorem Subgroup.IsHeckeFunction.heckeOp_comm {K : Subgroup G} {π : Representation A G W}
    {f f' : G → A} {v : W} (hf : K.IsHeckeFunction f) (hf' : K.IsHeckeFunction f')
    (hv : ∀ k ∈ K, π k v = v) (τ : G ≃* G)
    (hτg : ∀ g : G, ∃ a ∈ K, ∃ b ∈ K, τ g⁻¹ = a * g * b) :
    π.heckeOp K f (π.heckeOp K f' v) = π.heckeOp K f' (π.heckeOp K f v) := by
  rw [hf'.heckeOp_comp hf hv, hf.heckeOp_comp hf' hv, hf.heckeConv_comm hf' τ hτg]

end AbstractHecke

end
