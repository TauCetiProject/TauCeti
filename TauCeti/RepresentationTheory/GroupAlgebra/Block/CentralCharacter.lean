/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.RepresentationTheory.GroupAlgebra.Block.Principal
import TauCeti.RingTheory.Idempotents.Corner.Local

/-!
# Central characters of blocks

Let `k` be a field, `G` a finite group (or monoid) and `e_B` a block idempotent of `k[G]`, a
primitive idempotent of the centre `Z(k[G])`. The centre is a finite-dimensional commutative
`k`-algebra, hence Artinian, so the block's part `Z(k[G]) e_B` of the centre is a local ring;
`TauCeti.IsBlockIdempotent.exists_mul_mul_eq_or` states this inside `Z(k[G])`.

A **central character** of `B` is a `k`-algebra homomorphism `λ_B : Z(k[G]) → k` with
`λ_B(e_B) = 1`. A block has at most one (`TauCeti.IsBlockIdempotent.algHom_ext`): if two differed
at `x`, a rescaling `w` of `x - λ_B(x)` would have `λ_B(w) = 0` and `μ(w) = 1`, but in the local
ring `Z(k[G]) e_B` one of `w e_B` and `(1 - w) e_B` is invertible, and both homomorphisms send
`e_B` to `1`. Over an algebraically closed field a central character exists
(`TauCeti.IsBlockIdempotent.centralCharacter`): `e_B` is not nilpotent, so it lies outside some
prime ideal `𝔪` of the Artinian ring `Z(k[G])`, which is maximal with residue field finite over
`k`, hence `k`. It vanishes on every central element orthogonal to `e_B`, in particular on the
other block idempotents. The augmentation is the central character of the principal block, over
every field (`TauCeti.centerAugmentationAlgHom_eq`).

This is the central-character part of ModularCharactersAndBlocks §6.2, over an algebraically
closed field. Over a field `k` that splits `G` the residue field of `Z(k[G]) e_B` is also `k`;
that needs the semisimple quotient `k[G] / rad k[G] = ∏ M_{n_i}(k)` and is not proved here, and
neither are the defect classes built from `λ_B`.

## Main definitions

* `TauCeti.IsBlockIdempotent.centralCharacter`: over an algebraically closed field, the central
  character `λ_B : Z(k[G]) →ₐ[k] k` of a block.
* `TauCeti.centerAugmentationAlgHom`: the augmentation `Z(k[G]) →ₐ[k] k`.

## Main results

* `TauCeti.IsBlockIdempotent.exists_mul_mul_eq_or`: for every central `w`, `w e_B` or
  `(1 - w) e_B` is invertible in `Z(k[G]) e_B`.
* `TauCeti.IsBlockIdempotent.algHom_ext`: two `k`-algebra homomorphisms `Z(k[G]) → k` taking the
  value `1` at `e_B` are equal.
* `TauCeti.IsBlockIdempotent.centralCharacter_self`,
  `TauCeti.IsBlockIdempotent.centralCharacter_eq_zero_of_mul_eq_zero`: `λ_B(e_B) = 1`, and
  `λ_B(e) = 0` for every `e` with `e_B e = 0`.
* `TauCeti.centerAugmentationAlgHom_eq`: a `k`-algebra homomorphism `Z(k[G]) → k` taking the value
  `1` at the principal block idempotent is the augmentation.
-/

public section

noncomputable section

namespace TauCeti

open MonoidAlgebra

variable {k G : Type*} [Field k] [Monoid G] [Finite G]
  {b : Subalgebra.center k (MonoidAlgebra k G)}

/-- The centre of `k[G]` is a finite-dimensional `k`-vector space, for a finite monoid `G`. -/
theorem moduleFinite_center : Module.Finite k (Subalgebra.center k (MonoidAlgebra k G)) :=
  have : IsNoetherian k (Subalgebra.center k (MonoidAlgebra k G)) :=
    isNoetherian_submodule' (Subalgebra.toSubmodule (Subalgebra.center k (MonoidAlgebra k G)))
  inferInstance

/-- The centre of `k[G]` is an Artinian ring, for a finite monoid `G`. -/
theorem isArtinianRing_center : IsArtinianRing (Subalgebra.center k (MonoidAlgebra k G)) :=
  have := moduleFinite_center (k := k) (G := G)
  IsArtinianRing.of_finite k _

namespace IsBlockIdempotent

/-- **The centre of a block is local.** For a block idempotent `e_B` of `k[G]` and a central `w`,
one of `w e_B` and `(1 - w) e_B` is invertible in `Z(k[G]) e_B`: there is a central `z` with
`w z e_B = e_B`, or one with `(1 - w) z e_B = e_B`. -/
theorem exists_mul_mul_eq_or (hb : IsBlockIdempotent b)
    (w : Subalgebra.center k (MonoidAlgebra k G)) :
    (∃ z, w * z * b = b) ∨ ∃ z, (1 - w) * z * b = b := by
  have := isArtinianRing_center (k := k) (G := G)
  have hloc := IsPrimitiveIdempotent.isLocalRing_corner hb
  have he := hb.isIdempotentElem
  have hsum : he.compress w + he.compress (1 - w) = 1 := by
    rw [← IsIdempotentElem.compress_add, add_sub_cancel, IsIdempotentElem.compress_one]
  have key : ∀ v : Subalgebra.center k (MonoidAlgebra k G), IsUnit (he.compress v) →
      ∃ z, v * z * b = b := by
    rintro v ⟨u, hu⟩
    refine ⟨(u⁻¹ : Units _).val.val, ?_⟩
    have h := congrArg Subtype.val u.mul_inv
    rw [hu, IsIdempotentElem.Corner.val_mul, IsIdempotentElem.val_compress,
      IsIdempotentElem.Corner.val_one] at h
    have h1 := he.mul_corner_val (u⁻¹ : Units _).val
    have h2 := he.corner_val_mul (u⁻¹ : Units _).val
    set t := (u⁻¹ : Units _).val.val
    calc v * t * b = v * t := by rw [mul_assoc, h2]
      _ = b * v * b * t := by
          rw [show b * v * b * t = v * (b * (b * t)) by ring, h1, h1]
      _ = b := h
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hsum with h | h
  · exact Or.inl (key _ h)
  · exact Or.inr (key _ h)

/-- **A block has at most one central character.** Two `k`-algebra homomorphisms
`Z(k[G]) → k` taking the value `1` at the block idempotent `e_B` are equal. -/
theorem algHom_ext (hb : IsBlockIdempotent b)
    {φ ψ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k} (hφ : φ b = 1) (hψ : ψ b = 1) :
    φ = ψ := by
  ext x
  by_contra hne
  -- `w` rescales `x - φ(x)` so that `φ(w) = 0` and `ψ(w) = 1`.
  set w := algebraMap k _ (ψ x - φ x)⁻¹ * (x - algebraMap k _ (φ x))
  have hd : ψ x - φ x ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  have hφw : φ w = 0 := by simp [w]
  have hψw : ψ w = 1 := by simp [w, inv_mul_cancel₀ hd]
  rcases hb.exists_mul_mul_eq_or w with ⟨z, hz⟩ | ⟨z, hz⟩
  · have := congrArg φ hz
    rw [map_mul, map_mul, hφw, hφ] at this
    simp at this
  · have := congrArg ψ hz
    rw [map_mul, map_mul, map_sub, map_one, hψw, hψ] at this
    simp at this

variable [IsAlgClosed k]

/-- **Existence of the central character** over an algebraically closed field: some
`k`-algebra homomorphism `Z(k[G]) → k` takes the value `1` at the block idempotent `e_B`. -/
theorem exists_algHom_apply_eq_one (hb : IsBlockIdempotent b) :
    ∃ φ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k, φ b = 1 := by
  have := moduleFinite_center (k := k) (G := G)
  have := isArtinianRing_center (k := k) (G := G)
  -- `e_B` is not nilpotent, so it lies outside some prime ideal `𝔪`, which is maximal.
  have hnil : b ∉ nilradical (Subalgebra.center k (MonoidAlgebra k G)) := by
    rw [mem_nilradical]
    rintro ⟨n, hn⟩
    have h := hb.isIdempotentElem.pow_succ_eq n
    rw [pow_succ, hn, zero_mul] at h
    exact hb.ne_zero h.symm
  rw [nilradical_eq_sInf, Submodule.mem_sInf] at hnil
  simp only [not_forall] at hnil
  obtain ⟨𝔪, h𝔪, hb𝔪⟩ := hnil
  have : Ideal.IsPrime 𝔪 := h𝔪
  have : Ideal.IsMaximal 𝔪 := IsArtinianRing.isMaximal_of_isPrime 𝔪
  let := Ideal.Quotient.field 𝔪
  let e : k ≃ₐ[k] _ ⧸ 𝔪 :=
    AlgEquiv.ofBijective (Algebra.ofId k _) IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k 𝔪), ?_⟩
  have hidem : IsIdempotentElem (e.symm (Ideal.Quotient.mkₐ k 𝔪 b)) :=
    hb.isIdempotentElem.map (e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k 𝔪))
  refine (IsIdempotentElem.iff_eq_zero_or_one.1 hidem).resolve_left fun h ↦ hb𝔪 ?_
  have h' := e.symm.injective (h.trans (map_zero e.symm).symm)
  rw [Ideal.Quotient.mkₐ_eq_mk] at h'
  exact Ideal.Quotient.eq_zero_iff_mem.1 h'

/-- The **central character** `λ_B : Z(k[G]) → k` of a block `B` of `k[G]`, over an
algebraically closed field `k`: the unique `k`-algebra homomorphism with `λ_B(e_B) = 1`. -/
noncomputable def centralCharacter (hb : IsBlockIdempotent b) :
    Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k :=
  hb.exists_algHom_apply_eq_one.choose

/-- The central character of `B` takes the value `1` at `e_B`. -/
@[simp]
theorem centralCharacter_self (hb : IsBlockIdempotent b) : hb.centralCharacter b = 1 :=
  hb.exists_algHom_apply_eq_one.choose_spec

/-- **Characterization of the central character.** Over an algebraically closed field, the
central character of `B` is the only `k`-algebra homomorphism `Z(k[G]) → k` taking the value `1`
at `e_B`. -/
theorem eq_centralCharacter_iff (hb : IsBlockIdempotent b)
    (φ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k) :
    φ = hb.centralCharacter ↔ φ b = 1 :=
  ⟨fun h ↦ h ▸ hb.centralCharacter_self, fun h ↦ hb.algHom_ext h hb.centralCharacter_self⟩

/-- The central character of `B` vanishes at every central `e` with `e_B e = 0`, in particular
at the block idempotents of the other blocks. -/
theorem centralCharacter_eq_zero_of_mul_eq_zero (hb : IsBlockIdempotent b)
    {e : Subalgebra.center k (MonoidAlgebra k G)} (h : b * e = 0) :
    hb.centralCharacter e = 0 := by
  have := congrArg hb.centralCharacter h
  rwa [map_mul, centralCharacter_self, one_mul, map_zero] at this

end IsBlockIdempotent

variable (k G) in
/-- The augmentation `Z(k[G]) → k`, as a `k`-algebra homomorphism. -/
noncomputable def centerAugmentationAlgHom : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k :=
  { centerAugmentation k G with
    commutes' c := by
      change centerAugmentation k G (algebraMap k _ c) = c
      rw [centerAugmentation_apply]
      simp [Algebra.algebraMap_eq_smul_one] }

omit [Finite G] in
@[simp]
theorem centerAugmentationAlgHom_apply (x : Subalgebra.center k (MonoidAlgebra k G)) :
    centerAugmentationAlgHom k G x = centerAugmentation k G x :=
  (rfl)

/-- **The augmentation is the central character of the principal block.** Over every field, a
`k`-algebra homomorphism `Z(k[G]) → k` taking the value `1` at the principal block idempotent is
the augmentation. -/
theorem centerAugmentationAlgHom_eq {φ : Subalgebra.center k (MonoidAlgebra k G) →ₐ[k] k}
    (hφ : φ (principalBlockIdempotent k G) = 1) : φ = centerAugmentationAlgHom k G :=
  (isBlockIdempotent_principalBlockIdempotent k G).algHom_ext hφ <| by
    rw [centerAugmentationAlgHom_apply, centerAugmentation_principalBlockIdempotent]

end TauCeti
