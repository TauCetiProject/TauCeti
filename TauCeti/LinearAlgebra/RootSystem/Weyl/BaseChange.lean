/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.BaseChange
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-!
# Weyl groups under entrywise base change

A root pairing on standard lattices, with dot-product pairing,
has the same Weyl group after an injective extension of coefficients. The comparison
preserves the root-index permutation and sends each indexed reflection to the corresponding
reflection. It also intertwines the weight-space actions along the entrywise algebra map.

This applies to simply connected integral root data, whose roots need not span the character
lattice. In particular, it connects their explicit Weyl-group computations to those on the
rational root systems, where classification by Cartan matrices applies. Neither finiteness
of the root index set nor reducedness or crystallographicity is required.

No spanning hypothesis on the roots or coroots is required.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Chapter VI, §1.
-/

public section

namespace TauCeti

open RootPairing Function Matrix

variable {ι κ R : Type*} (S : Type*) [Fintype κ] [CommRing R] [CommRing S] [Algebra R S]
  [FaithfulSMul R S] (P : RootPairing ι R (κ → R) (κ → R))
  (hP : ∀ x y, P.toLinearMap x y = x ⬝ᵥ y)

local notation "Q" => rootPairingBaseChange S P hP
local notation "A" => Pi.algebraMap κ R S

private theorem ofIdx_smul_piAlgebraMap (i : ι) (x : κ → R) :
    weylGroup.ofIdx Q i • A x = A (weylGroup.ofIdx P i • x) := by
  simp only [weylGroup.ofIdx_smul, Equiv.reflection_smul, reflection_apply,
    coroot', coroot_rootPairingBaseChange, root_rootPairingBaseChange, Pi.algebraMap]
  ext j
  simp [Function.comp_apply, hP, ← RingHom.map_dotProduct, Algebra.smul_def]

private theorem exists_weylGroup_smul_piAlgebraMap (w : P.weylGroup) :
    ∃ v : (Q).weylGroup, ∀ x : κ → R, v • A x = A (w • x) := by
  obtain ⟨w, hw⟩ := w
  -- The construction uses Mathlib's `RootPairing.weylGroup.induction` on indexed reflections.
  induction hw using weylGroup.induction with
  | mem i => exact ⟨weylGroup.ofIdx Q i, ofIdx_smul_piAlgebraMap S P hP i⟩
  | one => exact ⟨1, by simp⟩
  | mul w₁ w₂ hw₁ hw₂ ih₁ ih₂ =>
    obtain ⟨v₁, hv₁⟩ := ih₁
    obtain ⟨v₂, hv₂⟩ := ih₂
    refine ⟨v₁ * v₂, fun x => ?_⟩
    rw [← Submonoid.mk_mul_mk _ _ _ hw₁ hw₂, mul_smul, hv₂, hv₁, mul_smul]

private theorem weylGroup_ext_piAlgebraMap {v w : (Q).weylGroup}
    (h : ∀ x : κ → R, v • A x = w • A x) : v = w := by
  apply Subtype.ext
  apply Equiv.weightHom_injective Q
  apply LinearEquiv.toLinearMap_injective
  exact LinearMap.ext_on_range
    (span_range_piAlgebraMap_eq_top S (v := id) (by simp)) h

private noncomputable def weylGroupBaseChangeHom : P.weylGroup →* (Q).weylGroup where
  toFun w := (exists_weylGroup_smul_piAlgebraMap S P hP w).choose
  map_one' := weylGroup_ext_piAlgebraMap S P hP fun x => by
    simpa only [one_smul] using (exists_weylGroup_smul_piAlgebraMap S P hP 1).choose_spec x
  map_mul' w₁ w₂ := weylGroup_ext_piAlgebraMap S P hP fun x => by
    rw [(exists_weylGroup_smul_piAlgebraMap S P hP (w₁ * w₂)).choose_spec,
      mul_smul (exists_weylGroup_smul_piAlgebraMap S P hP w₁).choose,
      (exists_weylGroup_smul_piAlgebraMap S P hP w₂).choose_spec,
      (exists_weylGroup_smul_piAlgebraMap S P hP w₁).choose_spec, mul_smul]

private theorem weylGroupBaseChangeHom_smul (w : P.weylGroup) (x : κ → R) :
    weylGroupBaseChangeHom S P hP w • A x = A (w • x) :=
  (exists_weylGroup_smul_piAlgebraMap S P hP w).choose_spec x

private theorem weylGroupBaseChangeHom_ofIdx (i : ι) :
    weylGroupBaseChangeHom S P hP (weylGroup.ofIdx P i) = weylGroup.ofIdx Q i := by
  apply weylGroup_ext_piAlgebraMap S P hP
  intro x
  rw [weylGroupBaseChangeHom_smul, ofIdx_smul_piAlgebraMap]

private theorem weylGroupBaseChangeHom_bijective : Bijective (weylGroupBaseChangeHom S P hP) := by
  constructor
  · intro v w h
    apply weylGroup.ext
    intro x
    apply piAlgebraMap_injective S
    rw [← weylGroupBaseChangeHom_smul S P hP, ← weylGroupBaseChangeHom_smul S P hP, h]
  · rintro ⟨v, hv⟩
    induction hv using weylGroup.induction with
    | mem i => exact ⟨weylGroup.ofIdx P i, weylGroupBaseChangeHom_ofIdx S P hP i⟩
    | one => exact ⟨1, map_one _⟩
    | mul v₁ v₂ hv₁ hv₂ ih₁ ih₂ =>
      obtain ⟨w₁, hw₁⟩ := ih₁
      obtain ⟨w₂, hw₂⟩ := ih₂
      refine ⟨w₁ * w₂, ?_⟩
      rw [map_mul, hw₁, hw₂, Submonoid.mk_mul_mk]

/-- Entrywise extension of coefficients identifies Weyl groups.
The identification preserves the permutation of root indices. -/
noncomputable def weylGroupBaseChangeEquiv : P.weylGroup ≃* (Q).weylGroup :=
  MulEquiv.ofBijective (weylGroupBaseChangeHom S P hP) (weylGroupBaseChangeHom_bijective S P hP)

/-- Entrywise scalar extension intertwines the Weyl-group actions on weight vectors. -/
@[simp]
theorem weylGroupBaseChangeEquiv_smul (w : P.weylGroup) (x : κ → R) :
    weylGroupBaseChangeEquiv S P hP w • A x = A (w • x) := by
  rw [weylGroupBaseChangeEquiv, MulEquiv.ofBijective_apply]
  exact weylGroupBaseChangeHom_smul S P hP w x

/-- The inverse comparison intertwines the Weyl-group actions on weight vectors. -/
@[simp low]
theorem weylGroupBaseChangeEquiv_symm_smul (w : (Q).weylGroup) (x : κ → R) :
    w • A x = A ((weylGroupBaseChangeEquiv S P hP).symm w • x) := by
  simpa only [MulEquiv.apply_symm_apply] using
    weylGroupBaseChangeEquiv_smul S P hP ((weylGroupBaseChangeEquiv S P hP).symm w) x

/-- The base-change comparison leaves the root-index permutation unchanged.
This is a rewrite rule, not a simp rule: `weylGroupToPerm` simplifies to `indexEquiv`. -/
theorem weylGroupToPerm_weylGroupBaseChangeEquiv (w : P.weylGroup) :
    (Q).weylGroupToPerm (weylGroupBaseChangeEquiv S P hP w) = P.weylGroupToPerm w := by
  ext i
  apply (Q).root.injective
  rw [← weylGroup_apply_root, root_rootPairingBaseChange, weylGroupBaseChangeEquiv_smul,
    weylGroup_apply_root, root_rootPairingBaseChange]

/-- The inverse comparison also leaves the root-index permutation unchanged.
As in the forward direction, use this with `rw` rather than `simp`. -/
theorem weylGroupToPerm_weylGroupBaseChangeEquiv_symm (w : (Q).weylGroup) :
    P.weylGroupToPerm ((weylGroupBaseChangeEquiv S P hP).symm w) =
      (Q).weylGroupToPerm w := by
  rw [← weylGroupToPerm_weylGroupBaseChangeEquiv S P hP, MulEquiv.apply_symm_apply]

/-- Base change sends each indexed reflection to the reflection with the same index. -/
@[simp]
theorem weylGroupBaseChangeEquiv_ofIdx (i : ι) :
    weylGroupBaseChangeEquiv S P hP (weylGroup.ofIdx P i) = weylGroup.ofIdx Q i := by
  rw [weylGroupBaseChangeEquiv, MulEquiv.ofBijective_apply]
  exact weylGroupBaseChangeHom_ofIdx S P hP i

/-- The inverse base-change comparison preserves indexed reflections. -/
@[simp]
theorem weylGroupBaseChangeEquiv_symm_ofIdx (i : ι) :
    (weylGroupBaseChangeEquiv S P hP).symm (weylGroup.ofIdx Q i) =
      weylGroup.ofIdx P i := by
  rw [← weylGroupBaseChangeEquiv_ofIdx S P hP, MulEquiv.symm_apply_apply]

end TauCeti
