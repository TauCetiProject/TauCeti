/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.GroupTheory.Coset.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.InverseTranspose
public import TauCeti.NumberTheory.HeckeRing.GLn.FractionRing
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Gelfand's trick for `GL_n` over a valuation ring

Let `G` be a group, `K : Subgroup G`, `A` a commutative semiring, and `π : Representation A G W`
a representation of `G` on an `A`-module `W`. A function `f : G → A` is a **Hecke function**
(`TauCeti.IsHeckeFunction K f`) if it is left and right `K`-invariant and supported on finitely
many left cosets `g K`. On `K`-fixed vectors `v` (`∀ k ∈ K, π k v = v`), `f` acts by the finite
sum `TauCeti.heckeOp π K f v = ∑ᶠ q : G ⧸ K, f q.out • π q.out v`.

If `τ : G ≃* G` is a group automorphism preserving `K` such that `τ g⁻¹ ∈ K * g * K` (specifically
`∃ k ∈ K, τ g⁻¹ = τ k * g * k`) for every `g : G`, then:
1. For any ring endomorphism `σ : A →+* A` and `G`-invariant pairing `B : W →ₛₗ[σ] W' →ₗ[A] Z`,
   `f^∨(g) = σ (f g⁻¹)` is again a Hecke function and
   `B (heckeOp π K f v) v' = B v (heckeOp π' K f^∨ v')` (`TauCeti.IsHeckeFunction.heckeOp_adjoint`).
2. Any two Hecke operators commute on `K`-fixed vectors (`TauCeti.IsHeckeFunction.heckeOp_comm`).

For `G = GL n F` over a field `F` with a valuation subring `O : ValuationSubring F` and
`K = GL n O` (`HeckeRing.GLn.integralGL O F n`), pivot elimination over `O` factors every matrix as
`k * diagonal d * k'` with `k, k' ∈ K` (`TauCeti.exists_mul_diagonal_mul_of_valuationSubring`).
Consequently the inverse-transpose automorphism `g ↦ (g⁻¹)ᵀ`
(`Matrix.GeneralLinearGroup.inverseTranspose`) satisfies Gelfand's condition
(`TauCeti.exists_inverseTranspose_inv_eq`), yielding both adjointness and commutativity of
spherical Hecke operators for `GL_n(F)` (`heckeOp_adjoint_gl`, `heckeOp_comm_gl`).

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

namespace TauCeti

/-! ### Abstract Hecke functions and Gelfand's trick -/

section AbstractHecke

variable {G A W W' Z : Type*} [Group G] [CommSemiring A]
  [AddCommMonoid W] [Module A W] [AddCommMonoid W'] [Module A W'] [AddCommMonoid Z] [Module A Z]

/-- A function `f : G → A` is a **Hecke function** for a subgroup `K : Subgroup G` if it is
supported on finitely many left cosets `g K` and is left and right `K`-invariant. -/
def IsHeckeFunction (K : Subgroup G) (f : G → A) : Prop :=
  {q : G ⧸ K | f q.out ≠ 0}.Finite ∧ ∀ g : G, ∀ k ∈ K, f (k * g) = f g ∧ f (g * k) = f g

/-- The Hecke operator attached to `f : G → A` on a representation `π : Representation A G W`,
defined by summing `f q.out • π q.out v` over left cosets `q : G ⧸ K`. -/
def heckeOp (π : Representation A G W) (K : Subgroup G) (f : G → A) (v : W) : W :=
  ∑ᶠ q : G ⧸ K, f q.out • π q.out v

/-- The Hecke operator of a bi-`K`-invariant function sends `K`-fixed vectors to `K`-fixed
vectors. -/
theorem heckeOp_mem_fixed {K : Subgroup G} {π : Representation A G W} {f : G → A} {v : W}
    (hf : IsHeckeFunction K f) (hv : ∀ k ∈ K, π k v = v) {k : G} (hk : k ∈ K) :
    π k (heckeOp π K f v) = heckeOp π K f v := by
  have hfin : (Function.support fun q : G ⧸ K ↦ f q.out • π q.out v).Finite :=
    hf.1.subset fun q hq h0 ↦ hq (by simp [h0])
  conv_lhs =>
    rw [heckeOp, finsum_eq_sum _ hfin, map_sum,
      ← finsum_eq_sum_of_support_subset _ fun q hq ↦ hfin.mem_toFinset.2 fun h0 ↦ hq (by simp [h0])]
  rw [heckeOp]
  let e : G ⧸ K ≃ G ⧸ K :=
    Quotient.congr (Equiv.mulLeft k) fun a b ↦ by simp [leftRel_apply, mul_assoc]
  refine (finsum_congr fun q ↦ ?_).trans (finsum_comp_equiv e)
  obtain ⟨⟨k', hk'⟩, hq'⟩ := QuotientGroup.mk_out_eq_mul K (k * q.out)
  have heq : (e q).out = k * q.out * k' := by
    have : e q = QuotientGroup.mk (k * q.out) := by
      conv_lhs => rw [← Quotient.out_eq q]
      rfl
    rw [this, hq']
  rw [heq, (hf.2 _ k' hk').2, (hf.2 _ k hk).1, map_smul, map_mul, map_mul,
    mul_apply_eq_comp, mul_apply_eq_comp, hv k' hk']

private theorem heckeOp_adjoint_term {K : Subgroup G} {f : G → A} (hf : IsHeckeFunction K f)
    (τ : G ≃* G) (hτK : ∀ g : G, τ g ∈ K ↔ g ∈ K)
    (hτg : ∀ g : G, ∃ k ∈ K, τ g⁻¹ = τ k * g * k)
    {σ : A →+* A} {π : Representation A G W} {π' : Representation A G W'}
    (B : W →ₛₗ[σ] W' →ₗ[A] Z) {v : W} {v' : W'}
    (hv : ∀ k ∈ K, π k v = v) (hv' : ∀ k ∈ K, π' k v' = v')
    (hB : ∀ (g : G) (x : W) (y : W'), B (π g x) (π' g y) = B x y) (g : G) :
    f (τ g)⁻¹ = f g ∧ B v (π' (τ g) v') = B (π g v) v' := by
  obtain ⟨k, hk, hg⟩ := hτg g⁻¹
  rw [inv_inv] at hg
  have hk' : τ k ∈ K := (hτK k).2 hk
  have hmove (x : G) (w : W) (w' : W') : B w (π' x w') = B (π x⁻¹ w) w' := by
    rw [← hB x⁻¹ w (π' x w'), ← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one,
      one_apply_eq_self]
  refine ⟨?_, ?_⟩
  · have hinv : (τ g)⁻¹ = k⁻¹ * g * (τ k)⁻¹ := by
      rw [hg, mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc]
    rw [hinv, (hf.2 _ _ (K.inv_mem hk')).2, (hf.2 _ _ (K.inv_mem hk)).1]
  · rw [hg, map_mul, map_mul, mul_apply_eq_comp, mul_apply_eq_comp, hv' k hk, hmove,
      hv _ (K.inv_mem hk'), hmove, inv_inv]

/-- **Gelfand's trick (adjointness).** If `τ : G ≃* G` preserves `K` and sends every `g⁻¹` into
`K * g * K` via `τ g⁻¹ = τ k * g * k`, then for any Hecke function `f`, ring endomorphism `σ`,
and `G`-invariant `σ`-sesquilinear pairing `B`, the dual function `g ↦ σ (f g⁻¹)` is a Hecke
function and `B (heckeOp π K f v) v' = B v (heckeOp π' K (fun g ↦ σ (f g⁻¹)) v')`. -/
theorem IsHeckeFunction.heckeOp_adjoint {K : Subgroup G} {f : G → A} (hf : IsHeckeFunction K f)
    (τ : G ≃* G) (hτK : ∀ g : G, τ g ∈ K ↔ g ∈ K)
    (hτg : ∀ g : G, ∃ k ∈ K, τ g⁻¹ = τ k * g * k)
    {σ : A →+* A} {π : Representation A G W} {π' : Representation A G W'}
    (B : W →ₛₗ[σ] W' →ₗ[A] Z) {v : W} {v' : W'}
    (hv : ∀ k ∈ K, π k v = v) (hv' : ∀ k ∈ K, π' k v' = v')
    (hB : ∀ (g : G) (x : W) (y : W'), B (π g x) (π' g y) = B x y) :
    IsHeckeFunction K (fun g ↦ σ (f g⁻¹)) ∧
      B (heckeOp π K f v) v' = B v (heckeOp π' K (fun g ↦ σ (f g⁻¹)) v') := by
  let e : G ⧸ K ≃ G ⧸ K :=
    Quotient.congr τ.toEquiv fun a b ↦ by
      simp [leftRel_apply, ← map_inv, ← map_mul, hτK]
  have hq_term (q : G ⧸ K) :
      f (e q).out⁻¹ = f q.out ∧ B v (π' (e q).out v') = B (π q.out v) v' := by
    obtain ⟨⟨k, hk⟩, hq'⟩ := QuotientGroup.mk_out_eq_mul K (τ q.out)
    have heq : (e q).out = τ q.out * k := by
      have : e q = QuotientGroup.mk (τ q.out) := by
        conv_lhs => rw [← Quotient.out_eq q]
        rfl
      rw [this, hq']
    rw [heq, mul_inv_rev, (hf.2 _ _ (K.inv_mem hk)).1, map_mul, mul_apply_eq_comp, hv' k hk]
    exact heckeOp_adjoint_term hf τ hτK hτg B hv hv' hB q.out
  have hfin_adj : {q : G ⧸ K | σ (f q.out⁻¹) ≠ 0}.Finite := by
    refine (hf.1.image e).subset fun q hq ↦ ⟨e.symm q, ?_, e.apply_symm_apply q⟩
    have h1 := (hq_term (e.symm q)).1
    rw [e.apply_symm_apply] at h1
    exact fun h0 ↦ hq (by rw [h1, h0, map_zero])
  have hinv_adj : ∀ g : G, ∀ k ∈ K,
      σ (f (k * g)⁻¹) = σ (f g⁻¹) ∧ σ (f (g * k)⁻¹) = σ (f g⁻¹) := fun g k hk ↦ by
    rw [mul_inv_rev, mul_inv_rev, (hf.2 _ _ (K.inv_mem hk)).2, (hf.2 _ _ (K.inv_mem hk)).1]
    exact ⟨rfl, rfl⟩
  refine ⟨⟨hfin_adj, hinv_adj⟩, ?_⟩
  have hfin₁ : (Function.support fun q : G ⧸ K ↦ f q.out • π q.out v).Finite :=
    hf.1.subset fun q hq h0 ↦ hq (by simp [h0])
  have hfin₂ : (Function.support fun q : G ⧸ K ↦ σ (f q.out⁻¹) • π' q.out v').Finite :=
    hfin_adj.subset fun q hq h0 ↦ hq (by simp [h0])
  rw [heckeOp, heckeOp, finsum_eq_sum _ hfin₁, finsum_eq_sum _ hfin₂, map_sum, map_sum,
    LinearMap.sum_apply,
    ← finsum_eq_sum_of_support_subset _ fun q hq ↦ hfin₁.mem_toFinset.2 fun h0 ↦ hq (by simp [h0]),
    ← finsum_eq_sum_of_support_subset _ fun q hq ↦ hfin₂.mem_toFinset.2 fun h0 ↦ hq (by simp [h0])]
  refine (finsum_congr fun q ↦ ?_).trans (finsum_comp_equiv e)
  rw [map_smulₛₗ, LinearMap.smul_apply, map_smul, (hq_term q).1, (hq_term q).2]

private theorem mem_conv_prod_image {K : Subgroup G} {f f' : G → A}
    (hf : IsHeckeFunction K f) {q s : G ⧸ K} (hq' : f' q.out ≠ 0)
    (hs' : f (q.out⁻¹ * s.out) ≠ 0) :
    s ∈ (fun p : (G ⧸ K) × (G ⧸ K) ↦ (↑(p.1.out * p.2.out) : G ⧸ K)) ''
      ({q | f' q.out ≠ 0} ×ˢ {r | f r.out ≠ 0}) := by
  let r₀ : G ⧸ K := QuotientGroup.mk (q.out⁻¹ * s.out)
  obtain ⟨⟨k, hk⟩, hr₀⟩ := QuotientGroup.mk_out_eq_mul K (q.out⁻¹ * s.out)
  refine ⟨(q, r₀), ⟨hq', ?_⟩, ?_⟩
  · simpa only [Set.mem_ofPred_eq, r₀, hr₀, (hf.2 _ k hk).2] using hs'
  · simp only [r₀]
    rw [hr₀, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
    exact (QuotientGroup.eq.2 (by simpa [leftRel_apply] using K.inv_mem hk)).symm.trans
      (Quotient.out_eq s)

/-- Composition of two Hecke operators on a `K`-fixed vector is the Hecke operator of their
convolution. -/
theorem IsHeckeFunction.heckeOp_comp {K : Subgroup G} {π : Representation A G W} {f f' : G → A}
    {v : W} (hf : IsHeckeFunction K f) (hf' : IsHeckeFunction K f') (hv : ∀ k ∈ K, π k v = v) :
    heckeOp π K f' (heckeOp π K f v) =
      heckeOp π K (fun x : G ↦ ∑ᶠ q : G ⧸ K, f' q.out * f (q.out⁻¹ * x)) v := by
  have hfin_f : (Function.support fun q : G ⧸ K ↦ f q.out • π q.out v).Finite :=
    hf.1.subset fun q hq h0 ↦ hq (by simp [h0])
  have hS : ((fun p : (G ⧸ K) × (G ⧸ K) ↦ (↑(p.1.out * p.2.out) : G ⧸ K)) ''
      ({q | f' q.out ≠ 0} ×ˢ {r | f r.out ≠ 0})).Finite :=
    (hf'.1.prod hf.1).image _
  have hinner (q : G ⧸ K) :
      π q.out (heckeOp π K f v) = ∑ r ∈ hfin_f.toFinset, f r.out • π (q.out * r.out) v := by
    rw [heckeOp, finsum_eq_sum _ hfin_f, map_sum]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    rw [map_smul, map_mul, mul_apply_eq_comp]
  rw [heckeOp, finsum_eq_sum_of_support_subset _ (s := hf'.1.toFinset)
    (fun q hq ↦ hf'.1.mem_toFinset.2 fun h0 ↦ hq (by simp [h0]))]
  simp_rw [hinner, Finset.smul_sum, smul_smul]
  have hstep : ∀ q ∈ hf'.1.toFinset,
      ∑ r ∈ hfin_f.toFinset, (f' q.out * f r.out) • π (q.out * r.out) v =
        ∑ s ∈ hS.toFinset, (f' q.out * f (q.out⁻¹ * s.out)) • π s.out v := fun q hq ↦ by
    let φ : G ⧸ K ≃ G ⧸ K :=
      Quotient.congr (Equiv.mulLeft q.out) fun a b ↦ by simp [leftRel_apply, mul_assoc]
    have h1 := (finsum_eq_sum_of_support_subset (f := fun r : G ⧸ K ↦
      (f' q.out * f r.out) • π (q.out * r.out) v) fun r hr ↦
      hfin_f.mem_toFinset.2 fun h0 ↦ hr (by
        dsimp only at h0 ⊢
        rw [mul_smul, map_mul, mul_apply_eq_comp, ← map_smul, h0, map_zero, smul_zero])).symm
    have h2 : (∑ᶠ r : G ⧸ K, (f' q.out * f r.out) • π (q.out * r.out) v) =
        ∑ᶠ s : G ⧸ K, (f' q.out * f (q.out⁻¹ * s.out)) • π s.out v := by
      refine (finsum_congr fun r ↦ ?_).trans (finsum_comp_equiv φ)
      have hφ : φ r = QuotientGroup.mk (q.out * r.out) := by
        conv_lhs => rw [← Quotient.out_eq r]
        rfl
      obtain ⟨⟨k, hk⟩, hk'⟩ := QuotientGroup.mk_out_eq_mul K (q.out * r.out)
      rw [hφ, hk', ← mul_assoc, inv_mul_cancel_left, (hf.2 _ k hk).2]
      conv_rhs => rw [map_mul, mul_apply_eq_comp, hv k hk]
    exact h1.trans <| h2.trans <| finsum_eq_sum_of_support_subset _ fun s hs ↦
      hS.mem_toFinset.2 (mem_conv_prod_image hf (hf'.1.mem_toFinset.1 hq)
        fun h0 ↦ hs (by simp [h0]))
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm, heckeOp,
    finsum_eq_sum_of_support_subset _ (s := hS.toFinset) fun r hr ↦ ?_]
  · refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [← Finset.sum_smul, finsum_eq_sum_of_support_subset _ (s := hf'.1.toFinset)
      (fun q hq ↦ hf'.1.mem_toFinset.2 fun h0 ↦ hq (by simp [h0]))]
  · have hex : ∃ q : G ⧸ K, f' q.out * f (q.out⁻¹ * r.out) ≠ 0 := by
      by_contra h; push Not at h
      exact hr (by simp [finsum_eq_zero_of_forall_eq_zero h])
    obtain ⟨q, hq⟩ := hex
    exact hS.mem_toFinset.2 (mem_conv_prod_image hf
      (fun h0 ↦ hq (by rw [h0, zero_mul])) (fun h0 ↦ hq (by rw [h0, mul_zero])))

/-- **Gelfand's trick (commutativity).** If `τ : G ≃* G` preserves `K` and sends every `g⁻¹` into
`K * g * K` via `τ g⁻¹ = τ k * g * k`, then any two Hecke operators commute on `K`-fixed
vectors. -/
theorem IsHeckeFunction.heckeOp_comm {K : Subgroup G} {π : Representation A G W} {f f' : G → A}
    {v : W} (hf : IsHeckeFunction K f) (hf' : IsHeckeFunction K f') (hv : ∀ k ∈ K, π k v = v)
    (τ : G ≃* G) (hτK : ∀ g : G, τ g ∈ K ↔ g ∈ K)
    (hτg : ∀ g : G, ∃ k ∈ K, τ g⁻¹ = τ k * g * k) :
    heckeOp π K f (heckeOp π K f' v) = heckeOp π K f' (heckeOp π K f v) := by
  have happly_τ (h : G → A) (hh : IsHeckeFunction K h) (g : G) : h (τ g⁻¹) = h g := by
    obtain ⟨k, hk, hg⟩ := hτg g
    rw [hg, (hh.2 _ k hk).2, (hh.2 _ _ ((hτK k).2 hk)).1]
  rw [hf'.heckeOp_comp hf hv, hf.heckeOp_comp hf' hv]
  congr 1
  funext x
  obtain ⟨b, hb_mem, hb_eq⟩ := hτg x
  have hb_mem' : τ b ∈ K := (hτK b).2 hb_mem
  let e : G ⧸ K ≃ G ⧸ K :=
    Quotient.congr (τ.toEquiv.trans (Equiv.mulLeft (x * b))) fun g g' ↦ by
      simp [leftRel_apply, ← map_inv, ← map_mul, hτK, mul_assoc]
  refine (finsum_congr fun q ↦ ?_).trans (finsum_comp_equiv e)
  obtain ⟨⟨k, hk⟩, hk'⟩ := QuotientGroup.mk_out_eq_mul K (x * b * τ q.out)
  have heq : (e q).out = x * b * τ q.out * k := by
    have : e q = QuotientGroup.mk (x * b * τ q.out) := by
      conv_lhs => rw [← Quotient.out_eq q]
      rfl
    rw [this, hk']
  have hf'_eq : f' (x * b * τ q.out * k) = f' (q.out⁻¹ * x) := by
    rw [← happly_τ f' hf' (q.out⁻¹ * x), mul_inv_rev, inv_inv, map_mul, hb_eq,
      (hf'.2 _ k hk).2, mul_assoc (τ b), mul_assoc (τ b), (hf'.2 _ _ hb_mem').1, mul_assoc]
  have hf_eq : f ((x * b * τ q.out * k)⁻¹ * x) = f q.out := by
    rw [← happly_τ f hf q.out, mul_inv_rev, mul_inv_rev, mul_inv_rev, mul_assoc k⁻¹,
      (hf.2 _ _ (K.inv_mem hk)).1, mul_assoc (τ q.out)⁻¹, mul_assoc b⁻¹, inv_mul_cancel,
      mul_one, (hf.2 _ _ (K.inv_mem hb_mem)).2, map_inv]
  rw [heq, hf'_eq, hf_eq, mul_comm]

end AbstractHecke

/-! ### `GL_n` over a valuation subring -/

section GLnValuation

open Matrix Matrix.GeneralLinearGroup HeckeRing.GLn

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- One pivot elimination step over a `CommRing` homomorphism `algebraMap R A`: if every entry
`M i j` is an `R`-multiple `algebraMap R A (w i j) * M p p` of the `(p, p)` entry and the
remaining block diagonalizes over `R`, then `M` diagonalizes over `R`. -/
private theorem exists_eq_mul_diagonal_mul_of_pivot_dvd {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] {M : Matrix n n A} {p : n} {w : n → n → R}
    (hw : ∀ i j : n, algebraMap R A (w i j) * M p p = M i j)
    {k l : GL {i : n // i ≠ p} R} {d : {i : n // i ≠ p} → A}
    (h_block : (M - of fun i : n ↦ algebraMap R A (w i p) • M p).toBlock (· ≠ p) (· ≠ p) =
      (GeneralLinearGroup.map (algebraMap R A) k).val * diagonal d *
        (GeneralLinearGroup.map (algebraMap R A) l).val) :
    ∃ (lower upper : GL n R) (D : n → A),
      M = (GeneralLinearGroup.map (algebraMap R A) lower).val * diagonal D *
        (GeneralLinearGroup.map (algebraMap R A) upper).val := by
  let e : {i : n // i = p} ⊕ {i : n // i ≠ p} ≃ n := Equiv.sumCompl (· = p)
  let lower : GL n R :=
    GeneralLinearGroup.mk'' (reindex e e (fromBlocks 1 0 (of fun i j ↦ w i j) k)) (by simp)
  let upper : GL n R :=
    GeneralLinearGroup.mk'' (reindex e e (fromBlocks 1 (of fun i j ↦ w i j) 0 l)) (by simp)
  let D : n → A := Sum.elim (fun _ ↦ M p p) d ∘ e.symm
  have block_entry (i j : {i : n // i ≠ p}) :
      M i j - algebraMap R A (w i p) * M p j =
        ∑ s : {i : n // i ≠ p}, algebraMap R A (k.val i s) * d s * algebraMap R A (l.val s j) := by
    have h := congrFun (congrFun h_block i) j
    simpa [Matrix.mul_apply, Matrix.diagonal_apply, GeneralLinearGroup.map,
      Algebra.smul_def] using h
  have default_val : ((default : {i : n // i = p}) : n) = p := rfl
  refine ⟨lower, upper, D, (reindex e.symm e.symm).injective ?_⟩
  suffices M.submatrix e e =
      fromBlocks 1 0 ((of fun i j ↦ w i.val j.val).map (algebraMap R A))
          (GeneralLinearGroup.map (algebraMap R A) k).val *
        diagonal (Sum.elim (fun _ : {i : n // i = p} ↦ M p p) d) *
        fromBlocks 1 ((of fun i j ↦ w i.val j.val).map (algebraMap R A)) 0
          (GeneralLinearGroup.map (algebraMap R A) l).val by
    simp [this, lower, upper, D, ← submatrix_mul_equiv _ _ _ e, fromBlocks_map, submatrix_map,
      Function.comp_assoc, GeneralLinearGroup.map]
  rw [← fromBlocks_diagonal, fromBlocks_multiply, fromBlocks_multiply]
  ext (i | i) (j | j)
  · simp [e, Unique.eq_default, default_val]
  · simp [e, mul_comm (M p p), Unique.eq_default i, default_val, hw]
  · simp [e, Unique.eq_default j, default_val, hw]
  · suffices M i j = algebraMap R A (w i p) * M p p * algebraMap R A (w p j) +
        ∑ s : {i : n // i ≠ p}, algebraMap R A (k.val i s) * d s * algebraMap R A (l.val s j) by
      simpa [e, Matrix.mul_apply, Matrix.diagonal_apply, default_val, GeneralLinearGroup.map]
    rw [← block_entry, ← hw p j]
    ring

/-- Every nonempty finite matrix over a field `F` has an entry that `O`-divides all other entries
for any valuation subring `O : ValuationSubring F`. -/
private theorem exists_pivot_dvd_valuationSubring {m : Type u} [Finite m]
    {F : Type*} [Field F] (O : ValuationSubring F) (p : m) (y : Matrix m m F) :
    ∃ ij₀ : m × m, ∀ ij : m × m, ∃ w : O, algebraMap O F w * y ij₀.1 ij₀.2 = y ij.1 ij.2 := by
  classical
  let : Fintype m := Fintype.ofFinite m
  obtain ⟨ij₀, -, hij₀⟩ := Finset.exists_max_image Finset.univ
    (fun ij : m × m ↦ O.valuation (y ij.1 ij.2)) ⟨(p, p), Finset.mem_univ _⟩
  exact ⟨ij₀, fun ij ↦ (O.valuation_le_iff _ _).1 (hij₀ ij (Finset.mem_univ _))⟩

/-- **Diagonalization over a valuation subring.** For a valuation subring `O` of a field `F`,
every square matrix `y : Matrix n n F` factors as `k * diagonal d * k'` with
`k, k' ∈ HeckeRing.GLn.integralGL O F n`. -/
theorem exists_mul_diagonal_mul_of_valuationSubring {F : Type*} [Field F] (O : ValuationSubring F)
    (y : Matrix n n F) :
    ∃ (k : GL n F), k ∈ integralGL O F n ∧
      ∃ (k' : GL n F), k' ∈ integralGL O F n ∧
        ∃ d : n → F, y = k.val * diagonal d * k'.val := by
  suffices ∀ {m : Type u} [Fintype m] [DecidableEq m] (y : Matrix m m F),
      ∃ (k k' : GL m O) (d : m → F),
        y = (GeneralLinearGroup.map (algebraMap O F) k).val * diagonal d *
          (GeneralLinearGroup.map (algebraMap O F) k').val by
    obtain ⟨k, k', d, h⟩ := this y
    exact ⟨GeneralLinearGroup.map (algebraMap O F) k, ⟨k, rfl⟩,
      GeneralLinearGroup.map (algebraMap O F) k', ⟨k', rfl⟩, d, h⟩
  intro m _ _ y
  induction h : Fintype.card m generalizing m with
  | zero =>
    have : IsEmpty m := Fintype.card_eq_zero_iff.1 h
    exact ⟨1, 1, 0, ext fun i ↦ IsEmpty.elim inferInstance i⟩
  | succ r ih =>
    obtain ⟨p⟩ : Nonempty m := Fintype.card_pos_iff.1 (by omega)
    obtain ⟨⟨i₀, j₀⟩, hij₀⟩ := exists_pivot_dvd_valuationSubring O p y
    let a : GL m O :=
      GeneralLinearGroup.mk'' ((Equiv.swap p i₀).permMatrix O) (by
        simp; split_ifs <;> simp)
    let b : GL m O :=
      GeneralLinearGroup.mk'' ((Equiv.swap p j₀).permMatrix O) (by
        simp; split_ifs <;> simp)
    set M : Matrix m m F :=
      (GeneralLinearGroup.map (algebraMap O F) a).val * y *
        (GeneralLinearGroup.map (algebraMap O F) b).val with hM
    have hM_entry (i j : m) : M i j = y (Equiv.swap p i₀ i) (Equiv.swap p j₀ j) := by
      simp [hM, a, b, GeneralLinearGroup.map, Matrix.mul_apply, Equiv.Perm.permMatrix, apply_ite]
      simp [Equiv.swap_apply_eq_iff]
    have hpivot (i j : m) : ∃ w : O, algebraMap O F w * M p p = M i j := by
      simpa only [hM_entry, Equiv.swap_apply_left] using hij₀ (Equiv.swap p i₀ i, Equiv.swap p j₀ j)
    choose w hw using hpivot
    obtain ⟨k, l, d, h_block⟩ :=
      ih ((M - of fun i : m ↦ algebraMap O F (w i p) • M p).toBlock (· ≠ p) (· ≠ p)) (by simp [h])
    obtain ⟨lower, upper, D, factor⟩ := exists_eq_mul_diagonal_mul_of_pivot_dvd hw h_block
    refine ⟨a⁻¹ * lower, upper * b⁻¹, D, ?_⟩
    simp only [map_mul, map_inv, Units.val_mul, Matrix.mul_assoc, Units.eq_inv_mul_iff_mul_eq]
    simpa only [← Matrix.mul_assoc, Units.eq_mul_inv_iff_mul_eq, hM] using factor

/-- **Gelfand's double-coset condition for `GL_n(F)` over a valuation subring `O`.**
For every `g ∈ GL n F`, there is `k ∈ GL n O` such that `gᵀ = (kᵀ)⁻¹ * g * k`
(written via `inverseTranspose g⁻¹ = inverseTranspose k * g * k`). -/
theorem exists_inverseTranspose_inv_eq {F : Type*} [Field F] (O : ValuationSubring F)
    (g : GL n F) :
    ∃ k ∈ integralGL O F n, inverseTranspose g⁻¹ = inverseTranspose k * g * k := by
  obtain ⟨k, hk, l, hl, d, h_smith⟩ := exists_mul_diagonal_mul_of_valuationSubring O g.val
  have hk_tr : (transposeMulEquiv n k).unop ∈ integralGL O F n := by
    rw [unop_transposeMulEquiv_eq_inverseTranspose_inv, inverseTranspose_mem_integralGL]
    exact Subgroup.inv_mem _ hk
  refine ⟨l⁻¹ * (transposeMulEquiv n k).unop,
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hl) hk_tr, Units.ext ?_⟩
  rw [map_mul, unop_transposeMulEquiv_eq_inverseTranspose_inv, inverseTranspose_inverseTranspose,
    Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, coe_inverseTranspose,
    coe_inverseTranspose, coe_inverseTranspose, inv_inv, inv_inv, inv_inv, h_smith]
  simp only [transpose_mul, diagonal_transpose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (k⁻¹).val k.val, Units.inv_mul, Matrix.one_mul,
    ← Matrix.mul_assoc l.val (l⁻¹).val, Units.mul_inv, Matrix.one_mul]

/-- **Gelfand's trick (adjointness) for `GL_n(F)` over a valuation subring `O`.** -/
theorem IsHeckeFunction.heckeOp_adjoint_gl {A W W' Z F : Type*} [CommSemiring A]
    [AddCommMonoid W] [Module A W] [AddCommMonoid W'] [Module A W'] [AddCommMonoid Z] [Module A Z]
    [Field F] (O : ValuationSubring F) {f : GL n F → A}
    (hf : IsHeckeFunction (integralGL O F n) f) {σ : A →+* A}
    {π : Representation A (GL n F) W} {π' : Representation A (GL n F) W'}
    (B : W →ₛₗ[σ] W' →ₗ[A] Z) {v : W} {v' : W'}
    (hv : ∀ k ∈ integralGL O F n, π k v = v)
    (hv' : ∀ k ∈ integralGL O F n, π' k v' = v')
    (hB : ∀ (g : GL n F) (x : W) (y : W'), B (π g x) (π' g y) = B x y) :
    IsHeckeFunction (integralGL O F n) (fun g ↦ σ (f g⁻¹)) ∧
      B (heckeOp π (integralGL O F n) f v) v' =
        B v (heckeOp π' (integralGL O F n) (fun g ↦ σ (f g⁻¹)) v') :=
  hf.heckeOp_adjoint inverseTranspose (fun _ ↦ inverseTranspose_mem_integralGL)
    (exists_inverseTranspose_inv_eq O) B hv hv' hB

/-- **Gelfand's trick (commutativity) for `GL_n(F)` over a valuation subring `O`.** -/
theorem IsHeckeFunction.heckeOp_comm_gl {A W F : Type*} [CommSemiring A]
    [AddCommMonoid W] [Module A W] [Field F] (O : ValuationSubring F) {f f' : GL n F → A}
    {π : Representation A (GL n F) W} {v : W}
    (hf : IsHeckeFunction (integralGL O F n) f)
    (hf' : IsHeckeFunction (integralGL O F n) f')
    (hv : ∀ k ∈ integralGL O F n, π k v = v) :
    heckeOp π (integralGL O F n) f (heckeOp π (integralGL O F n) f' v) =
      heckeOp π (integralGL O F n) f' (heckeOp π (integralGL O F n) f v) :=
  hf.heckeOp_comm hf' hv inverseTranspose (fun _ ↦ inverseTranspose_mem_integralGL)
    (exists_inverseTranspose_inv_eq O)

end GLnValuation

end TauCeti

end
