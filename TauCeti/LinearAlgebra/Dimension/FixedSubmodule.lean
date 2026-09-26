/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FixedSubmodule
import TauCeti.LinearAlgebra.FixedSubmodule

/-!
# Dimensions of common fixed submodules

This file computes the dimension of the common fixed submodule of a finite family of commuting
idempotent endomorphisms when each new fixed-point condition has an explicitly equivalent
complementary eigenspace.

## Main results

* `IsIdempotentElem.two_mul_finrank_fixedSubmodule`: an idempotent whose fixed vectors and kernel
  are exchanged by maps that are mutually inverse there has a fixed submodule of half the dimension.
* `LinearMap.finrank_fixedSubmodule_restrict`: the fixed submodule of the restriction of `f` to an
  invariant submodule `p` has the dimension of `p ⊓ f.fixedSubmodule`.
* `TauCeti.two_mul_finrank_iInf_fixedSubmodule_insert`: adjoining one such idempotent halves the
  common fixed-space dimension.
* `TauCeti.pow_card_mul_finrank_iInf_fixedSubmodule`: iterating the construction multiplies the
  common fixed-space dimension by a power of two.
-/

public section

open Module

namespace TauCeti

/-- If `u` maps the fixed vectors of an idempotent endomorphism `q` of a finite-dimensional space
into the kernel of `q`, `v` maps the kernel into the fixed vectors, and these two restrictions are
mutually inverse, then the fixed submodule of `q` has half the dimension of the space. -/
theorem _root_.IsIdempotentElem.two_mul_finrank_fixedSubmodule {K W : Type*} [DivisionRing K]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] {q : Module.End K W}
    (hq : IsIdempotentElem q) (u v : Module.End K W) (hu0 : ∀ x, q x = x → q (u x) = 0)
    (hv1 : ∀ x, q x = 0 → q (v x) = v x) (hvu : ∀ x, q x = x → v (u x) = x)
    (huv : ∀ x, q x = 0 → u (v x) = x) :
    2 * finrank K q.fixedSubmodule = finrank K W := by
  have hf {x} := LinearMap.mem_fixedSubmodule_iff (f := q) (v := x)
  -- For an idempotent, the range is exactly the submodule of fixed vectors.
  have hr : LinearMap.range q = q.fixedSubmodule := by
    ext x
    rw [LinearMap.IsIdempotentElem.mem_range_iff hq, hf]
  -- `u` and `v` restrict to mutually inverse maps between the fixed vectors and the kernel of `q`.
  let e : q.fixedSubmodule ≃ₗ[K] LinearMap.ker q := .ofLinearMap
    (u.restrict fun x hx => LinearMap.mem_ker.mpr (hu0 x (hf.mp hx)))
    (v.restrict fun x hx => hf.mpr (hv1 x (LinearMap.mem_ker.mp hx)))
    (by ext x; simpa only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.coe_restrict_apply]
      using huv x (LinearMap.mem_ker.mp x.2))
    (by ext x; simpa only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.coe_restrict_apply]
      using hvu x (hf.mp x.2))
  -- Rank-nullity for `q`, with its kernel replaced by the isomorphic fixed submodule.
  rw [two_mul, ← q.finrank_range_add_finrank_ker, hr, e.finrank_eq]

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
    {K V ι : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [DecidableEq ι]
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
  have hS {f : Module.End K V} (hf : ∀ i ∈ s, Commute (p i) f) : ∀ x ∈ S, f x ∈ S :=
    LinearMap.iInf_invariant f fun i => LinearMap.iInf_invariant f fun hi _ =>
      (hf i hi).apply_mem_fixedSubmodule
  let q : Module.End K S := (p a).restrict (hS hcomm)
  have hq : IsIdempotentElem q := LinearMap.ext fun x => Subtype.ext <| by
    simpa only [q, Module.End.mul_apply, LinearMap.coe_restrict_apply] using
      LinearMap.congr_fun hpa.eq (x : V)
  -- Inside `S`, the new common fixed space is the fixed space of `q`.
  rw [Finset.iInf_insert, inf_comm, ← LinearMap.finrank_fixedSubmodule_restrict (hS hcomm),
    hq.two_mul_finrank_fixedSubmodule (u.restrict (hS huS)) (v.restrict (hS hvS))]
  -- The four exchange hypotheses restrict from `V` to `S`.
  all_goals
    intro x hx
    simp only [q, Subtype.ext_iff, LinearMap.coe_restrict_apply, ZeroMemClass.coe_zero] at hx ⊢
  exacts [hu0 _ hx, hv1 _ hx, hvu _ hx, huv _ hx]

/-- A finite family of commuting idempotent endomorphisms has common fixed-space dimension
`2 ^ (-|t|)` times the ambient dimension when each idempotent's fixed and zero pieces are
exchanged by inverse endomorphisms that commute with the other idempotents. -/
theorem pow_card_mul_finrank_iInf_fixedSubmodule
    {K V ι : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
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
