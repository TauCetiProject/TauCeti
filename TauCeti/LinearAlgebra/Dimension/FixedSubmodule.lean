/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FixedSubmodule
import TauCeti.LinearAlgebra.FixedSubmodule

/-!
# Dimensions of common fixed submodules

This file computes the dimension of the common fixed submodule of a finite family of commuting
idempotent endomorphisms when each new fixed-point condition has an explicitly equivalent
complementary eigenspace. The only input on the scalars is rank-nullity, so the results hold over
any ring with `HasRankNullity`, such as a division ring or a commutative domain.

## Main results

* `IsIdempotentElem.two_mul_finrank_fixedSubmodule`: an idempotent whose fixed submodule is
  linearly equivalent to its kernel has a fixed submodule of half the dimension.
* `LinearMap.finrank_fixedSubmodule_restrict`: the fixed submodule of the restriction of `f` to an
  invariant submodule `p` has the dimension of `p ⊓ f.fixedSubmodule`.
* `TauCeti.two_mul_finrank_iInf_fixedSubmodule_insert`: adjoining one such idempotent halves the
  common fixed-space dimension.
* `TauCeti.pow_card_mul_finrank_iInf_fixedSubmodule`: iterating the construction multiplies the
  common fixed-space dimension by a power of two.
-/

public section

universe u

open Module

namespace TauCeti

/-- If the fixed submodule of an idempotent endomorphism `q` is linearly equivalent to the kernel
of `q`, then it has half the dimension of the space. In infinite dimension both sides are `0`. -/
theorem _root_.IsIdempotentElem.two_mul_finrank_fixedSubmodule {K : Type*} {W : Type u} [Ring K]
    [HasRankNullity.{u} K] [AddCommGroup W] [Module K W] {q : Module.End K W}
    (hq : IsIdempotentElem q) (e : q.fixedSubmodule ≃ₗ[K] LinearMap.ker q) :
    2 * finrank K q.fixedSubmodule = finrank K W := by
  -- For an idempotent, the range is exactly the submodule of fixed vectors.
  have hr : LinearMap.range q = q.fixedSubmodule := by
    ext x
    rw [LinearMap.IsIdempotentElem.mem_range_iff hq, LinearMap.mem_fixedSubmodule_iff]
  -- Rank-nullity for `q`, with its kernel replaced by the equivalent fixed submodule.
  have h : 2 * Module.rank K q.fixedSubmodule = Module.rank K W := by
    rw [two_mul, ← q.rank_range_add_rank_ker, hr, e.rank_eq]
  -- `finrank` is `Cardinal.toNat` of the rank, which is multiplicative, also on infinite ranks.
  rw [finrank, finrank, ← h, Cardinal.toNat_mul, Cardinal.toNat_ofNat]

/-- If `f` maps a submodule `p` into itself, then the fixed submodule of the restriction of `f`
to `p` has the same dimension as `p ⊓ f.fixedSubmodule`. -/
theorem _root_.LinearMap.finrank_fixedSubmodule_restrict {K V : Type*} [Semiring K]
    [AddCommMonoid V] [Module K V] {f : V →ₗ[K] V} {p : Submodule K V} (hf : ∀ x ∈ p, f x ∈ p) :
    finrank K (f.restrict hf).fixedSubmodule = finrank K ↥(p ⊓ f.fixedSubmodule) := by
  rw [LinearMap.fixedSubmodule_restrict hf, ← Submodule.finrank_map_subtype_eq,
    Submodule.map_comap_subtype]

/-- If two endomorphisms exchange the fixed and zero eigenspaces of an idempotent inside the
common fixed space of a commuting family, adjoining that idempotent halves the dimension.

The maps `u` and `v` are stated on the ambient module so callers can supply natural operators;
the commuting hypotheses ensure that their restrictions preserve the previous common fixed
space. -/
theorem two_mul_finrank_iInf_fixedSubmodule_insert
    {K ι : Type*} {V : Type u} [Ring K] [HasRankNullity.{u} K] [AddCommGroup V] [Module K V]
    [DecidableEq ι]
    (p : ι → Module.End K V) (s : Finset ι) (a : ι)
    (hpa : IsIdempotentElem (p a))
    (hcomm : ∀ i ∈ s, Commute (p i) (p a))
    (u v : Module.End K V)
    (huS : ∀ i ∈ s, Commute (p i) u)
    (hvS : ∀ i ∈ s, Commute (p i) v)
    (hu0 : ∀ x, p a x = x → p a (u x) = 0)
    (hv1 : ∀ x, p a x = 0 → p a (v x) = v x)
    (hvu : ∀ x, p a x = x → v (u x) = x)
    (huv : ∀ x, p a x = 0 → u (v x) = x) :
    2 * finrank K ((⨅ i ∈ insert a s, (p i).fixedSubmodule) : Submodule K V) =
      finrank K ((⨅ i ∈ s, (p i).fixedSubmodule) : Submodule K V) := by
  let S : Submodule K V := ⨅ i ∈ s, (p i).fixedSubmodule
  -- A map commuting with each `p i` maps the fixed points of `p i` to themselves, so preserves `S`.
  have hS {f : Module.End K V} (hf : ∀ i ∈ s, Commute (p i) f) : ∀ x ∈ S, f x ∈ S :=
    LinearMap.iInf_invariant f fun i => LinearMap.iInf_invariant f fun hi x hx => by
      have hfi : Function.Semiconj f (p i) (p i) := fun y => by
        simpa only [Module.End.mul_apply] using LinearMap.congr_fun (hf i hi).eq.symm y
      rw [LinearMap.mem_fixedSubmodule_iff, ← Function.mem_fixedPoints_iff] at hx ⊢
      exact hfi.mapsTo_fixedPoints hx
  let q : Module.End K S := (p a).restrict (hS hcomm)
  have hq : IsIdempotentElem q := LinearMap.ext fun x => Subtype.ext <| by
    simpa only [q, Module.End.mul_apply, LinearMap.coe_restrict_apply] using
      LinearMap.congr_fun hpa.eq (x : V)
  -- Membership in the fixed submodule and in the kernel of `q` is read off in `V`.
  have hf {x : S} : x ∈ q.fixedSubmodule ↔ p a x = x := by
    rw [LinearMap.mem_fixedSubmodule_iff, Subtype.ext_iff, LinearMap.coe_restrict_apply]
  have hk {x : S} : x ∈ LinearMap.ker q ↔ p a x = 0 := by
    rw [LinearMap.mem_ker, Subtype.ext_iff, LinearMap.coe_restrict_apply, ZeroMemClass.coe_zero]
  -- `u` and `v` restrict to mutually inverse maps between the fixed vectors and the kernel of `q`.
  let e : q.fixedSubmodule ≃ₗ[K] LinearMap.ker q := .ofLinearMap
    ((u.restrict (hS huS)).restrict fun x hx => hk.mpr <| by
      simpa only [LinearMap.coe_restrict_apply] using hu0 x (hf.mp hx))
    ((v.restrict (hS hvS)).restrict fun x hx => hf.mpr <| by
      simpa only [LinearMap.coe_restrict_apply] using hv1 x (hk.mp hx))
    (by ext x; simpa only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.coe_restrict_apply]
      using huv x (hk.mp x.2))
    (by ext x; simpa only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.coe_restrict_apply]
      using hvu x (hf.mp x.2))
  -- Inside `S`, the new common fixed space is the fixed space of `q`.
  rw [Finset.iInf_insert, inf_comm, ← LinearMap.finrank_fixedSubmodule_restrict (hS hcomm),
    hq.two_mul_finrank_fixedSubmodule e]

/-- A finite family of commuting idempotent endomorphisms has common fixed-space dimension
`2 ^ (-|t|)` times the ambient dimension when each idempotent's fixed and zero pieces are
exchanged by inverse endomorphisms that commute with the other idempotents. -/
theorem pow_card_mul_finrank_iInf_fixedSubmodule
    {K ι : Type*} {V : Type u} [Ring K] [HasRankNullity.{u} K] [AddCommGroup V] [Module K V]
    (p : ι → Module.End K V) (t : Finset ι)
    (hp : ∀ a ∈ t, IsIdempotentElem (p a))
    (hcomm : (t : Set ι).Pairwise fun a b => Commute (p a) (p b))
    (u v : ι → Module.End K V)
    (huS : ∀ a ∈ t, ∀ i ∈ t, i ≠ a → Commute (p i) (u a))
    (hvS : ∀ a ∈ t, ∀ i ∈ t, i ≠ a → Commute (p i) (v a))
    (hu0 : ∀ a ∈ t, ∀ x, p a x = x → p a (u a x) = 0)
    (hv1 : ∀ a ∈ t, ∀ x, p a x = 0 → p a (v a x) = v a x)
    (hvu : ∀ a ∈ t, ∀ x, p a x = x → v a (u a x) = x)
    (huv : ∀ a ∈ t, ∀ x, p a x = 0 → u a (v a x) = x) :
    2 ^ t.card * finrank K ((⨅ i ∈ t, (p i).fixedSubmodule) : Submodule K V) =
      finrank K V := by
  classical
  induction t using Finset.induction with
  | empty =>
      have hempty : (⨅ i ∈ (∅ : Finset ι), (p i).fixedSubmodule) =
          (⊤ : Submodule K V) := by
        ext x
        simp
      rw [hempty]
      simp
  | @insert a s ha ih =>
      have hrec : 2 * finrank K
          ((⨅ i ∈ insert a s, (p i).fixedSubmodule) : Submodule K V) =
          finrank K ((⨅ i ∈ s, (p i).fixedSubmodule) : Submodule K V) :=
        two_mul_finrank_iInf_fixedSubmodule_insert p s a (hp a (by simp))
          (fun i hi => hcomm (by simp [hi]) (by simp) (by
            exact fun hia => ha (hia ▸ hi))) (u a) (v a)
          (fun i hi => huS a (by simp) i (by simp [hi]) (by
            exact fun hia => ha (hia ▸ hi)))
          (fun i hi => hvS a (by simp) i (by simp [hi]) (by
            exact fun hia => ha (hia ▸ hi)))
          (hu0 a (by simp)) (hv1 a (by simp)) (hvu a (by simp)) (huv a (by simp))
      have ih' := ih (fun b hb => hp b (by simp [hb]))
        (hcomm.mono (by simp))
        (fun b hb i hi hne => huS b (by simp [hb]) i (by simp [hi]) hne)
        (fun b hb i hi hne => hvS b (by simp [hb]) i (by simp [hi]) hne)
        (fun b hb => hu0 b (by simp [hb]))
        (fun b hb => hv1 b (by simp [hb]))
        (fun b hb => hvu b (by simp [hb]))
        (fun b hb => huv b (by simp [hb]))
      rw [Finset.card_insert_of_notMem ha, pow_succ]
      calc
        2 ^ s.card * 2 * finrank K
            ((⨅ i ∈ insert a s, (p i).fixedSubmodule) : Submodule K V) =
            2 ^ s.card * (2 * finrank K
              ((⨅ i ∈ insert a s, (p i).fixedSubmodule) : Submodule K V)) :=
          Nat.mul_assoc _ _ _
        _ = 2 ^ s.card * finrank K
            ((⨅ i ∈ s, (p i).fixedSubmodule) : Submodule K V) := by rw [hrec]
        _ = finrank K V := ih'

end TauCeti
