/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Normalizer actions on orbit quotients

Let a group `G` act on a type `X`, and let `H ≤ G`. The normalizer `N_G(H)` acts on the
orbit quotient `X / H`: a normalizing element sends each `H`-orbit to another `H`-orbit.
Moreover, the subgroup `H`, viewed inside its normalizer, acts trivially on `X / H`, so the
action descends to an action of the quotient group `N_G(H) / H`.

This is the group-action bookkeeping needed by the universal-covers roadmap before the
deck group of the cover attached to a subgroup `H ≤ π₁(X, x₀)` is identified with
`N(H) / H`. The file deliberately proves only the abstract orbit-quotient descent: no
covering-space hypotheses are involved.

## Main declarations

* `TauCeti.normalizerOrbitEquiv`: a normalizer element acts as a permutation of
  `X / H`.
* `TauCeti.normalizerOrbitHom`: the corresponding homomorphism
  `N_G(H) →* Equiv.Perm (X / H)`.
* `TauCeti.normalizerQuotientOrbitHom`: the descended homomorphism
  `N_G(H) / H →* Equiv.Perm (X / H)`.
* `TauCeti.normalizerQuotientMulAction`: the descended action of `N_G(H) / H` on
  `X / H`.

## References

This supplies a prerequisite for the Tau Ceti universal-covers roadmap, Stage 2: the
normalizer quotient `N(H)/H` is the algebraic object that later appears as the deck group
of the cover associated to `H`.
-/

namespace TauCeti

variable {G X : Type*} [Group G] [MulAction G X] (H : Subgroup G)

/-- Two quotient representatives are equal exactly when they lie in the same subgroup
orbit. This uses the orientation of `MulAction.orbitRel_apply`: the left point is a member of
the orbit of the right point. -/
lemma orbitRel_quotient_mk_eq_iff (x y : X) :
    (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) = Quotient.mk'' y ↔
      x ∈ MulAction.orbit H y := by
  rw [Quotient.eq'', MulAction.orbitRel_apply]

/-- A normalizer element preserves the orbit relation of the restricted `H`-action. -/
lemma normalizer_smul_orbitRel_iff (n : Subgroup.normalizer (H : Set G)) (x y : X) :
    MulAction.orbitRel H X ((n : G) • x) ((n : G) • y) ↔
      MulAction.orbitRel H X x y := by
  rw [MulAction.orbitRel_apply, MulAction.orbitRel_apply]
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨⟨(n : G)⁻¹ * (h : G) * (n : G), ?_⟩, ?_⟩
    · exact (Subgroup.mem_normalizer_iff''.mp n.2 (h : G)).mp h.2
    · -- The orbit witness lives in the subgroup action; expose the ambient `G` action
      -- before conjugating the equality by `n⁻¹`.
      change ((n : G)⁻¹ * (h : G) * (n : G)) • y = x
      simpa [mul_smul, MulAction.subgroup_smul_def] using
        congrArg (fun z => ((n : G)⁻¹) • z) hh
  · rintro ⟨h, hh⟩
    refine ⟨⟨(n : G) * (h : G) * (n : G)⁻¹, ?_⟩, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp n.2 (h : G)).mp h.2
    · -- The orbit witness lives in the subgroup action; expose the ambient `G` action
      -- before conjugating the equality by `n`.
      change ((n : G) * (h : G) * (n : G)⁻¹) • ((n : G) • y) = (n : G) • x
      simpa [mul_smul, MulAction.subgroup_smul_def] using
        congrArg (fun z => (n : G) • z) hh

/-- A normalizer element acts as a permutation of the orbit quotient `X / H`. -/
noncomputable def normalizerOrbitEquiv (n : Subgroup.normalizer (H : Set G)) :
    MulAction.orbitRel.Quotient H X ≃ MulAction.orbitRel.Quotient H X :=
  Quotient.congr
    { toFun := fun x => (n : G) • x
      invFun := fun x => ((n : G)⁻¹) • x
      left_inv := by intro x; simp
      right_inv := by intro x; simp }
    fun x y => (normalizer_smul_orbitRel_iff H n x y).symm

/-- On representatives, the normalizer action on the orbit quotient is the ambient action. -/
@[simp]
lemma normalizerOrbitEquiv_mk (n : Subgroup.normalizer (H : Set G)) (x : X) :
    normalizerOrbitEquiv H n (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) =
      Quotient.mk'' ((n : G) • x) :=
  rfl

/-- The normalizer acts on the orbit quotient `X / H`. -/
noncomputable def normalizerOrbitHom :
    Subgroup.normalizer (H : Set G) →* Equiv.Perm (MulAction.orbitRel.Quotient H X) where
  toFun := normalizerOrbitEquiv H
  map_one' := by
    ext q
    induction q using Quotient.inductionOn' with
    | h x => simp [normalizerOrbitEquiv]
  map_mul' n m := by
    ext q
    induction q using Quotient.inductionOn' with
    | h x => simp [normalizerOrbitEquiv, mul_smul]

/-- On representatives, the normalizer homomorphism acts by the ambient action. -/
@[simp]
lemma normalizerOrbitHom_apply_mk (n : Subgroup.normalizer (H : Set G)) (x : X) :
    normalizerOrbitHom H n (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) =
      Quotient.mk'' ((n : G) • x) :=
  rfl

/-- Elements of `H`, viewed as elements of its normalizer, act trivially on `X / H`. -/
lemma subgroupOfNormalizer_le_ker_normalizerOrbitHom :
    H.subgroupOf (Subgroup.normalizer (H : Set G)) ≤
      MonoidHom.ker (normalizerOrbitHom (X := X) H) := by
  intro h hh
  ext q
  induction q using Quotient.inductionOn' with
  | h x =>
      simp only [Equiv.Perm.coe_one, id_eq]
      refine Quotient.sound ?_
      exact ⟨⟨(h : G), hh⟩, rfl⟩

/-- The action of `N_G(H)` on `X / H` descends to the quotient group `N_G(H) / H`. -/
noncomputable def normalizerQuotientOrbitHom :
    (Subgroup.normalizer (H : Set G) ⧸ H.subgroupOf (Subgroup.normalizer (H : Set G))) →*
      Equiv.Perm (MulAction.orbitRel.Quotient H X) :=
  QuotientGroup.lift (H.subgroupOf (Subgroup.normalizer (H : Set G)))
    (normalizerOrbitHom (X := X) H)
    (subgroupOfNormalizer_le_ker_normalizerOrbitHom (X := X) H)

/-- The descended action of `N_G(H) / H` on the subgroup-orbit quotient `X / H`. -/
noncomputable instance normalizerQuotientMulAction :
    MulAction
      (Subgroup.normalizer (H : Set G) ⧸ H.subgroupOf (Subgroup.normalizer (H : Set G)))
      (MulAction.orbitRel.Quotient H X) :=
  MulAction.ofEndHom <|
    (MulAction.toEndHom (M := Equiv.Perm (MulAction.orbitRel.Quotient H X))).comp
      (normalizerQuotientOrbitHom (X := X) H)

/-- On representatives, the descended normalizer-quotient action is the ambient action. -/
@[simp]
lemma normalizerQuotientOrbitHom_mk (n : Subgroup.normalizer (H : Set G)) (x : X) :
    normalizerQuotientOrbitHom H (QuotientGroup.mk n)
        (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) =
      Quotient.mk'' ((n : G) • x) := by
  rw [normalizerQuotientOrbitHom, QuotientGroup.lift_mk]
  rfl

/-- On representatives, the descended normalizer-quotient action is the ambient action. -/
@[simp]
lemma normalizerQuotient_smul_mk (n : Subgroup.normalizer (H : Set G)) (x : X) :
    (QuotientGroup.mk n :
        Subgroup.normalizer (H : Set G) ⧸ H.subgroupOf (Subgroup.normalizer (H : Set G))) •
        (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) =
      Quotient.mk'' ((n : G) • x) := by
  rw [show
    (QuotientGroup.mk n :
        Subgroup.normalizer (H : Set G) ⧸ H.subgroupOf (Subgroup.normalizer (H : Set G))) •
        (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) =
      normalizerQuotientOrbitHom H (QuotientGroup.mk n)
        (Quotient.mk'' x : MulAction.orbitRel.Quotient H X) from rfl]
  exact normalizerQuotientOrbitHom_mk H n x

end TauCeti
