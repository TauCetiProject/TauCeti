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
  have hAS : A ≤ S := by
    intro x hx
    have hx' : ∀ i ∈ insert a s, p i x = x := by
      simpa only [A, Submodule.mem_iInf, LinearMap.mem_fixedSubmodule_iff] using hx
    simpa only [S, Submodule.mem_iInf, LinearMap.mem_fixedSubmodule_iff] using
      (fun i hi => hx' i (Finset.mem_insert_of_mem hi))
  have hpS : ∀ x ∈ S, p a x ∈ S := by
    intro x hx
    have hx' : ∀ i ∈ s, p i x = x := by
      simpa only [S, Submodule.mem_iInf, LinearMap.mem_fixedSubmodule_iff] using hx
    simpa only [S, Submodule.mem_iInf, LinearMap.mem_fixedSubmodule_iff] using fun i hi =>
      calc
        p i (p a x) = p a (p i x) := LinearMap.congr_fun (hcomm i hi).eq x
        _ = p a x := congrArg (p a) (hx' i hi)
  let q : Module.End K S := (p a).restrict hpS
  have hq : IsIdempotentElem q := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simpa only [q, Module.End.mul_apply, LinearMap.coe_restrict_apply] using
      LinearMap.congr_fun hpa.eq (x : V)
  have hqrange : LinearMap.range q = A.comap S.subtype := by
    ext x
    rw [LinearMap.IsIdempotentElem.mem_range_iff hq]
    constructor
    · intro hx
      have hxa : p a (x : V) = x := by
        simpa only [q, LinearMap.coe_restrict_apply] using congrArg Subtype.val hx
      have hxS : ∀ i ∈ s, p i (x : V) = x := by
        simpa only [S, Submodule.mem_iInf, LinearMap.mem_fixedSubmodule_iff] using x.2
      simp only [Submodule.mem_comap, A, Submodule.mem_iInf,
        LinearMap.mem_fixedSubmodule_iff]
      intro i hi
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · exact hxa
      · exact hxS i hi
    · intro hx
      have hx' : ∀ i ∈ insert a s, p i (S.subtype x) = S.subtype x := by
        simpa only [Submodule.mem_comap, A, Submodule.mem_iInf,
          LinearMap.mem_fixedSubmodule_iff] using hx
      apply Subtype.ext
      convert hx' a (Finset.mem_insert_self a s) using 1 <;> rfl
  have huS' : ∀ x ∈ S, u x ∈ S := by
    intro x hx
    have hx' : ∀ i ∈ s, p i x = x := by
      simpa only [S, Submodule.mem_iInf, LinearMap.mem_fixedSubmodule_iff] using hx
    simpa only [S, Submodule.mem_iInf, LinearMap.mem_fixedSubmodule_iff] using fun i hi =>
      calc
        p i (u x) = u (p i x) := LinearMap.congr_fun (huS i hi).eq x
        _ = u x := congrArg u (hx' i hi)
  have hvS' : ∀ x ∈ S, v x ∈ S := by
    intro x hx
    have hx' : ∀ i ∈ s, p i x = x := by
      simpa only [S, Submodule.mem_iInf, LinearMap.mem_fixedSubmodule_iff] using hx
    simpa only [S, Submodule.mem_iInf, LinearMap.mem_fixedSubmodule_iff] using fun i hi =>
      calc
        p i (v x) = v (p i x) := LinearMap.congr_fun (hvS i hi).eq x
        _ = v x := congrArg v (hx' i hi)
  let uS : Module.End K S := u.restrict huS'
  let vS : Module.End K S := v.restrict hvS'
  let U : LinearMap.range q →ₗ[K] LinearMap.ker q :=
    uS.restrict fun x hx => by
      have hxfix : p a (x : V) = x := by
        have hx' := LinearMap.IsIdempotentElem.mem_range_iff hq |>.mp hx
        simpa only [q, LinearMap.coe_restrict_apply] using congrArg Subtype.val hx'
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      simpa only [q, uS, LinearMap.coe_restrict_apply, ZeroMemClass.coe_zero] using
        hu0 (x : V) hxfix
  let W : LinearMap.ker q →ₗ[K] LinearMap.range q :=
    vS.restrict fun x hx => by
      apply LinearMap.IsIdempotentElem.mem_range_iff hq |>.mpr
      have hxzero : p a (x : V) = 0 := by
        have hx' := LinearMap.mem_ker.mp hx
        simpa only [q, LinearMap.coe_restrict_apply, ZeroMemClass.coe_zero] using
          congrArg Subtype.val hx'
      apply Subtype.ext
      simpa only [q, vS, LinearMap.coe_restrict_apply] using hv1 (x : V) hxzero
  let e : LinearMap.range q ≃ₗ[K] LinearMap.ker q := LinearEquiv.ofLinearMap U W
    (LinearMap.ext fun x => Subtype.ext (Subtype.ext (by
      have hxzero : p a (x : V) = 0 := by
        have hx' := LinearMap.mem_ker.mp x.2
        simpa only [q, LinearMap.coe_restrict_apply, ZeroMemClass.coe_zero] using
          congrArg Subtype.val hx'
      simpa only [U, W, uS, vS, LinearMap.comp_apply, LinearMap.id_apply,
        LinearMap.coe_restrict_apply] using
        huv (x : V) hxzero)))
    (LinearMap.ext fun x => Subtype.ext (Subtype.ext (by
      have hxfix : p a (x : V) = x := by
        have hx' := LinearMap.IsIdempotentElem.mem_range_iff hq |>.mp x.2
        simpa only [q, LinearMap.coe_restrict_apply] using congrArg Subtype.val hx'
      simpa only [U, W, uS, vS, LinearMap.comp_apply, LinearMap.id_apply,
        LinearMap.coe_restrict_apply] using
        hvu (x : V) hxfix)))
  have hrank := Submodule.finrank_add_eq_of_isCompl
    (LinearMap.IsIdempotentElem.isCompl hq)
  have hrangeA : finrank K (LinearMap.range q) = finrank K A := by
    rw [hqrange]
    exact (Submodule.comapSubtypeEquivOfLe hAS).finrank_eq
  calc
    2 * finrank K ((⨅ i ∈ insert a s, (p i).fixedSubmodule) : Submodule K V) =
        2 * finrank K A := rfl
    _ = 2 * finrank K (LinearMap.range q) := by rw [hrangeA]
    _ = finrank K (LinearMap.range q) + finrank K (LinearMap.range q) := two_mul _
    _ = finrank K (LinearMap.range q) + finrank K (LinearMap.ker q) := by
      rw [e.finrank_eq]
    _ = finrank K S := hrank
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
