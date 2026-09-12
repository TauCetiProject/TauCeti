/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FixedSubmodule

/-!
# Dimensions of common fixed submodules

This file computes the dimension of the common fixed submodule of a finite family of commuting
idempotent endomorphisms when each new fixed-point condition has an explicitly equivalent
complementary eigenspace.

## Main results

* `TauCeti.two_mul_finrank_iInf_fixedSubmodule_insert`: adjoining one such idempotent halves the
  common fixed-space dimension.
* `TauCeti.pow_card_mul_finrank_iInf_fixedSubmodule`: iterating the construction multiplies the
  common fixed-space dimension by a power of two.
-/

public section

open Module

namespace TauCeti

/-- If two endomorphisms exchange the fixed and zero eigenspaces of an idempotent inside the
common fixed space of a commuting family, adjoining that idempotent halves the dimension.

The maps `u` and `v` are stated on the ambient module so callers can supply natural operators;
the commuting hypotheses ensure that their restrictions preserve the previous common fixed
space. -/
theorem two_mul_finrank_iInf_fixedSubmodule_insert
    {K V ι : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [DecidableEq ι]
    (p : ι → Module.End K V) (s : Finset ι) (a : ι) (ha : a ∉ s)
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
  let A : Submodule K V := ⨅ i ∈ insert a s, (p i).fixedSubmodule
  let B : Submodule K V := S ⊓ LinearMap.ker (p a)
  have hAS : A ≤ S := by
    intro x hx
    have hx' : ∀ i ∈ insert a s, p i x = x := by
      simpa only [A, Submodule.mem_iInf, LinearMap.mem_fixedSubmodule_iff] using hx
    simpa only [S, Submodule.mem_iInf, LinearMap.mem_fixedSubmodule_iff] using
      (fun i hi => hx' i (Finset.mem_insert_of_mem hi))
  have hAfix : ∀ x ∈ A, p a x = x := by
    intro x hx
    have hx' : ∀ i ∈ insert a s, p i x = x := by
      simpa only [A, Submodule.mem_iInf, LinearMap.mem_fixedSubmodule_iff] using hx
    exact hx' a (Finset.mem_insert_self a s)
  -- Decompose the previous common fixed space into the `1`- and `0`-eigenspaces of `p a`.
  have hsup : A ⊔ B = S := by
    apply le_antisymm
    · exact sup_le hAS inf_le_left
    · intro x hx
      have hx' : ∀ i ∈ s, p i x = x := by
        simpa only [S, Submodule.mem_iInf, LinearMap.mem_fixedSubmodule_iff] using hx
      have hpxS : p a x ∈ S := by
        simpa only [S, Submodule.mem_iInf, LinearMap.mem_fixedSubmodule_iff] using fun i hi =>
          calc
            p i (p a x) = p a (p i x) := LinearMap.congr_fun (hcomm i hi).eq x
            _ = p a x := congrArg (p a) (hx' i hi)
      have hpxS' : ∀ i ∈ s, p i (p a x) = p a x := by
        simpa only [S, Submodule.mem_iInf, LinearMap.mem_fixedSubmodule_iff] using hpxS
      have hrestS : x - p a x ∈ S := S.sub_mem hx hpxS
      have hpxA : p a x ∈ A := by
        simp only [A, Submodule.mem_iInf, LinearMap.mem_fixedSubmodule_iff]
        intro i hi
        rw [Finset.mem_insert] at hi
        rcases hi with rfl | hi
        · exact congrArg (fun f : Module.End K V => f x) hpa.eq
        · exact hpxS' i hi
      have hrestB : x - p a x ∈ B := by
        dsimp only [B]
        refine ⟨hrestS, LinearMap.mem_ker.mpr ?_⟩
        rw [map_sub]
        exact sub_eq_zero.mpr (congrArg (fun f : Module.End K V => f x) hpa.eq).symm
      rw [← add_sub_cancel (p a x) x]
      exact Submodule.add_mem _ (Submodule.mem_sup_left hpxA) (Submodule.mem_sup_right hrestB)
  have hinf : A ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    apply (Submodule.mem_bot K).mpr
    rw [← hAfix x hx.1, LinearMap.mem_ker.mp hx.2.2]
  -- The supplied exchange maps restrict to inverse maps between those two eigenspaces.
  let U : A →ₗ[K] B :=
    (u.domRestrict A).codRestrict B fun x => by
      dsimp only [B]
      refine ⟨?_, LinearMap.mem_ker.mpr (hu0 x (hAfix x x.2))⟩
      have hxA : ∀ i ∈ insert a s, p i x = x := by
        simpa only [A, Submodule.mem_iInf, LinearMap.mem_fixedSubmodule_iff] using x.2
      have hxS : ∀ i ∈ s, p i x = x :=
        fun i hi => hxA i (Finset.mem_insert_of_mem hi)
      have huS_mem : u (x : V) ∈ (⨅ i ∈ s, (p i).fixedSubmodule) := by
        simp only [Submodule.mem_iInf, LinearMap.mem_fixedSubmodule_iff]
        intro i hi
        exact
          calc
          p i (u x) = u (p i x) := LinearMap.congr_fun (huS i hi).eq x
          _ = u x := congrArg u (hxS i hi)
      exact huS_mem
  let W : B →ₗ[K] A :=
    (v.domRestrict B).codRestrict A fun x => by
      have hxS : ∀ i ∈ s, p i x = x := by
        have hxS' : (x : V) ∈ (⨅ i ∈ s, (p i).fixedSubmodule) := x.2.1
        simpa only [Submodule.mem_iInf, LinearMap.mem_fixedSubmodule_iff] using hxS'
      simp only [LinearMap.domRestrict_apply, A, Submodule.mem_iInf,
        LinearMap.mem_fixedSubmodule_iff]
      intro i hi
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · exact hv1 x (LinearMap.mem_ker.mp x.2.2)
      · calc
          p i (v x) = v (p i x) := LinearMap.congr_fun (hvS i hi).eq x
          _ = v x := congrArg v (hxS i hi)
  let e : A ≃ₗ[K] B := LinearEquiv.ofLinearMap U W
    (LinearMap.ext fun x => Subtype.ext (huv x (LinearMap.mem_ker.mp x.2.2)))
    (LinearMap.ext fun x => Subtype.ext (hvu x (hAfix x x.2)))
  -- Equal dimensions of complementary summands give the desired factor of two.
  have hrank := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [hsup, hinf, finrank_bot, add_zero] at hrank
  calc
    2 * finrank K ((⨅ i ∈ insert a s, (p i).fixedSubmodule) : Submodule K V) =
        2 * finrank K A := rfl
    _ = finrank K A + finrank K A := two_mul _
    _ = finrank K A + finrank K B := by rw [e.finrank_eq]
    _ = finrank K S := hrank.symm
    _ = finrank K ((⨅ i ∈ s, (p i).fixedSubmodule) : Submodule K V) := rfl

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
        two_mul_finrank_iInf_fixedSubmodule_insert p s a ha (hp a (by simp))
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
