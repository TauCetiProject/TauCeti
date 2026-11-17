/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Frobenius
public import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Decomposition and inertia groups in the absolute Galois group of a field

Let `F` be a field, `F̄ = AlgebraicClosure F`, `G_F = Field.absoluteGaloisGroup F`, and let
`O = integralClosure (𝓞 F) F̄` be the integral closure of the ring of integers of `F` in `F̄`. For a
number field `F` this is the ring of all algebraic integers in `F̄`, and its maximal ideals are the
primes of `F̄` above the finite places of `F`. Each `σ ∈ G_F` restricts to an `𝓞 F`-algebra
automorphism `toIntegralClosure F σ` of `O`, which makes `O` a `G_F`-ring. For an ideal `Q` of `O`
this file defines

* the **decomposition group** `D_Q = {σ | σ • Q = Q}`, Mathlib's `MulAction.stabilizer`;
* the **inertia group** `I_Q = {σ | ∀ x ∈ O, σ x - x ∈ Q}`, Mathlib's `Ideal.inertia`;
* the **wild inertia group** `P_Q`: the `σ` with `σ(x)/x ≡ 1` modulo the maximal ideal of the
  localization `O_Q`, for all nonzero `x ∈ O`. Clearing denominators, `σ ∈ P_Q` when every
  `x ∈ O` admits `s ∈ 1 + Q` and `q ∈ Q` with `s (σ x - x) = q x`;
* the predicate `IsArithFrobAtIntegralPrime σ Q`, that `σ x ≡ x ^ q mod Q` for all `x ∈ O`, where
  `q` is the cardinality of the residue field of `𝓞 F` below `Q`; it is Mathlib's
  `AlgHom.IsArithFrobAt` for `toIntegralClosure F σ`.

At a maximal ideal `Q` above a finite place of a number field, `P_Q` is the inverse limit of the
first lower ramification groups of the finite Galois subextensions at the primes below `Q`
(Serre, *Corps locaux*, IV §2, Proposition 6 and its corollaries, which characterise `G_1` by
`σ(x)/x ≡ 1` modulo the maximal ideal); it is the largest closed normal pro-`p` subgroup of `I_Q`.

## Main definitions

* `TauCeti.GaloisRep.toIntegralClosure F σ`: the action of `σ ∈ G_F` on `O`.
* `TauCeti.GaloisRep.instMulSemiringActionIntegralClosure`: the resulting action of `G_F` on `O`.
* `TauCeti.GaloisRep.decompositionGroup F Q`, `TauCeti.GaloisRep.inertiaGroup F Q` and
  `TauCeti.GaloisRep.wildInertiaGroup F Q`: `D_Q`, `I_Q` and `P_Q` as subgroups of `G_F`.
* `TauCeti.GaloisRep.IsArithFrobAtIntegralPrime σ Q`: `σ` is an arithmetic Frobenius at `Q`.

## Main results

* `TauCeti.GaloisRep.decompositionGroup_smul`, `TauCeti.GaloisRep.inertiaGroup_smul` and
  `TauCeti.GaloisRep.wildInertiaGroup_smul`: `D_{τQ} = τ D_Q τ⁻¹`, and likewise for `I` and `P`.
* `TauCeti.GaloisRep.wildInertiaGroup_le_inertiaGroup` and
  `TauCeti.GaloisRep.inertiaGroup_le_decompositionGroup`: `P_Q ≤ I_Q ≤ D_Q`.
* `TauCeti.GaloisRep.normal_inertiaGroup_subgroupOf_decompositionGroup` and
  `TauCeti.GaloisRep.normal_wildInertiaGroup_subgroupOf_decompositionGroup`: `I_Q` and `P_Q` are
  normal in `D_Q`.
* `TauCeti.GaloisRep.IsArithFrobAtIntegralPrime.mem_decompositionGroup`: arithmetic Frobenius
  elements at a prime `Q` lie in `D_Q`.
* `TauCeti.GaloisRep.IsArithFrobAtIntegralPrime.isArithFrobAtIntegralPrime_iff_mul_inv_mem`:
  given one arithmetic Frobenius `σ` at `Q`, the arithmetic Frobenius elements at `Q` are exactly
  the coset `I_Q σ`.
* `TauCeti.GaloisRep.IsArithFrobAtIntegralPrime.conj`: conjugating a Frobenius at `Q` by `τ` gives
  a Frobenius at `τ • Q`.

## References

* P. Deligne, *Les constantes des équations fonctionnelles des fonctions L*, 1973, 3.12.
* J.-P. Serre, *Corps locaux*, Chapter IV, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter I, §9.
-/

public section

noncomputable section

open NumberField Pointwise

namespace TauCeti.GaloisRep

variable (F : Type*) [Field F]

/-- The automorphism of the integral closure `O` of `𝓞 F` in `F̄` induced by `σ ∈ G_F`: Mathlib's
`AlgEquiv.mapIntegralClosure` of `σ`, viewed as an `𝓞 F`-algebra automorphism of `F̄`. -/
@[expose] def toIntegralClosure (σ : Field.absoluteGaloisGroup F) :
    integralClosure (𝓞 F) (AlgebraicClosure F) ≃ₐ[𝓞 F]
      integralClosure (𝓞 F) (AlgebraicClosure F) :=
  ((σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F).restrictScalars (𝓞 F)).mapIntegralClosure

variable {F}

/-- `toIntegralClosure F σ` acts on `O` as `σ` acts on `F̄`. -/
@[simp]
theorem coe_toIntegralClosure_apply (σ : Field.absoluteGaloisGroup F)
    (x : integralClosure (𝓞 F) (AlgebraicClosure F)) :
    (toIntegralClosure F σ x : AlgebraicClosure F) =
      DFunLike.coe (F := AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) σ (x : AlgebraicClosure F) :=
  rfl

/-- The action of `G_F` on the integral closure `O` of `𝓞 F` in `F̄`, by
`σ • x = toIntegralClosure F σ x`. -/
instance instMulSemiringActionIntegralClosure :
    MulSemiringAction (Field.absoluteGaloisGroup F)
      (integralClosure (𝓞 F) (AlgebraicClosure F)) where
  smul σ x := toIntegralClosure F σ x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero σ := map_zero (toIntegralClosure F σ)
  smul_add σ := map_add (toIntegralClosure F σ)
  smul_one σ := map_one (toIntegralClosure F σ)
  smul_mul σ := map_mul (toIntegralClosure F σ)

/-- The action of `G_F` on `O` is through `toIntegralClosure`. -/
theorem smul_def (σ : Field.absoluteGaloisGroup F)
    (x : integralClosure (𝓞 F) (AlgebraicClosure F)) :
    σ • x = toIntegralClosure F σ x :=
  rfl

/-- The action of `G_F` on `O` is the restriction of its action on `F̄`. -/
@[simp]
theorem coe_smul (σ : Field.absoluteGaloisGroup F)
    (x : integralClosure (𝓞 F) (AlgebraicClosure F)) :
    ((σ • x : integralClosure (𝓞 F) (AlgebraicClosure F)) : AlgebraicClosure F) =
      DFunLike.coe (F := AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) σ (x : AlgebraicClosure F) :=
  rfl

/-- `G_F` acts on `O` by `𝓞 F`-algebra automorphisms. -/
instance : SMulCommClass (Field.absoluteGaloisGroup F) (𝓞 F)
    (integralClosure (𝓞 F) (AlgebraicClosure F)) where
  smul_comm σ r x := map_smul (toIntegralClosure F σ) r x

/-- `toIntegralClosure F σ` is the `𝓞 F`-algebra automorphism by which `σ` acts on `O`. -/
theorem toIntegralClosure_eq_toAlgEquiv (σ : Field.absoluteGaloisGroup F) :
    toIntegralClosure F σ = MulSemiringAction.toAlgEquiv (𝓞 F)
      (integralClosure (𝓞 F) (AlgebraicClosure F)) σ :=
  rfl

/-! ### Decomposition, inertia and wild inertia groups -/

variable (F) (Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F)))

/-- The **decomposition group** `D_Q` of an ideal `Q` of the integral closure `O` of `𝓞 F` in
`F̄`: the `σ ∈ G_F` with `σ • Q = Q`. -/
def decompositionGroup : Subgroup (Field.absoluteGaloisGroup F) :=
  MulAction.stabilizer (Field.absoluteGaloisGroup F) Q

/-- `D_Q` is the stabilizer of `Q`. -/
theorem decompositionGroup_def :
    decompositionGroup F Q = MulAction.stabilizer (Field.absoluteGaloisGroup F) Q :=
  (rfl)

/-- The **inertia group** `I_Q` of an ideal `Q` of `O`: the `σ ∈ G_F` with `σ x - x ∈ Q` for every
`x ∈ O`. Its carrier is that of `AddSubgroup.inertia Q.toAddSubgroup G_F`. -/
def inertiaGroup : Subgroup (Field.absoluteGaloisGroup F) :=
  Q.inertia (Field.absoluteGaloisGroup F)

/-- `I_Q` is Mathlib's inertia subgroup of `Q` viewed as an additive subgroup; the carriers agree
definitionally. -/
theorem inertiaGroup_def :
    inertiaGroup F Q = Q.toAddSubgroup.inertia (Field.absoluteGaloisGroup F) :=
  (rfl)

/-- The **wild inertia group** `P_Q` of an ideal `Q` of `O`: the `σ ∈ G_F` such that for every
`x ∈ O` there are `s ∈ 1 + Q` and `q ∈ Q` with `s (σ x - x) = q x`. For a maximal ideal `Q`, these
are the `σ` with `σ(x)/x ≡ 1` modulo the maximal ideal of `O_Q` for every nonzero `x`; above a
finite place of a number field this is the largest closed normal pro-`p` subgroup of `I_Q`. -/
def wildInertiaGroup : Subgroup (Field.absoluteGaloisGroup F) where
  carrier := {σ | ∀ x, ∃ s q, s - 1 ∈ Q ∧ q ∈ Q ∧ s * (σ • x - x) = q * x}
  one_mem' x := ⟨1, 0, by simp, Q.zero_mem, by simp⟩
  mul_mem' {σ τ} hσ hτ x := by
    obtain ⟨s₁, q₁, hs₁, hq₁, h₁⟩ := hτ x
    obtain ⟨s₂, q₂, hs₂, hq₂, h₂⟩ := hσ (τ • x)
    refine ⟨s₁ * s₂, q₂ * (s₁ + q₁) + s₂ * q₁, ?_, ?_, ?_⟩
    · have : s₁ * s₂ - 1 = s₁ * (s₂ - 1) + (s₁ - 1) := by ring
      rw [this]
      exact Q.add_mem (Q.mul_mem_left _ hs₂) hs₁
    · exact Q.add_mem (Q.mul_mem_right _ hq₂) (Q.mul_mem_left _ hq₁)
    · rw [mul_smul]
      linear_combination s₁ * h₂ + (s₂ + q₂) * h₁
  inv_mem' {σ} hσ x := by
    obtain ⟨s, q, hs, hq, h⟩ := hσ (σ⁻¹ • x)
    refine ⟨s + q, -q, ?_, Q.neg_mem hq, ?_⟩
    · rw [add_sub_right_comm]
      exact Q.add_mem hs hq
    · rw [smul_inv_smul] at h
      linear_combination -h

variable {F Q}

/-- `σ ∈ D_Q` exactly when `σ • Q = Q`. -/
theorem mem_decompositionGroup_iff {σ : Field.absoluteGaloisGroup F} :
    σ ∈ decompositionGroup F Q ↔ σ • Q = Q :=
  MulAction.mem_stabilizer_iff

/-- `σ ∈ I_Q` exactly when `σ x - x ∈ Q` for every `x ∈ O`. -/
theorem mem_inertiaGroup_iff {σ : Field.absoluteGaloisGroup F} :
    σ ∈ inertiaGroup F Q ↔ ∀ x, σ • x - x ∈ Q :=
  Ideal.mem_inertia

/-- `σ ∈ P_Q` exactly when every `x ∈ O` has `s ∈ 1 + Q` and `q ∈ Q` with `s (σ x - x) = q x`. -/
theorem mem_wildInertiaGroup_iff {σ : Field.absoluteGaloisGroup F} :
    σ ∈ wildInertiaGroup F Q ↔
      ∀ x, ∃ s q, s - 1 ∈ Q ∧ q ∈ Q ∧ s * (σ • x - x) = q * x :=
  Iff.rfl

variable (F Q)

/-- `I_Q ≤ D_Q`. -/
theorem inertiaGroup_le_decompositionGroup : inertiaGroup F Q ≤ decompositionGroup F Q :=
  Ideal.inertia_le_stabilizer Q

/-- `P_Q ≤ I_Q`. -/
theorem wildInertiaGroup_le_inertiaGroup : wildInertiaGroup F Q ≤ inertiaGroup F Q := by
  intro σ hσ x
  obtain ⟨s, q, hs, hq, h⟩ := hσ x
  have : σ • x - x = q * x - (s - 1) * (σ • x - x) := by linear_combination h
  rw [this]
  exact Q.sub_mem (Q.mul_mem_right _ hq) (Q.mul_mem_right _ hs)

/-- `D_{τQ} = τ D_Q τ⁻¹`. -/
theorem decompositionGroup_smul (τ : Field.absoluteGaloisGroup F) :
    decompositionGroup F (τ • Q) = (decompositionGroup F Q).map (MulAut.conj τ).toMonoidHom :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj τ Q

/-- `I_{τQ} = τ I_Q τ⁻¹`. -/
theorem inertiaGroup_smul (τ : Field.absoluteGaloisGroup F) :
    inertiaGroup F (τ • Q) = (inertiaGroup F Q).map (MulAut.conj τ) :=
  Ideal.inertia_smul τ Q

variable {F Q} in
/-- If `τ⁻¹ σ τ ∈ P_Q` then `σ ∈ P_{τQ}`. -/
theorem mem_wildInertiaGroup_smul_of_mem {σ τ : Field.absoluteGaloisGroup F}
    (h : τ⁻¹ * σ * τ ∈ wildInertiaGroup F Q) : σ ∈ wildInertiaGroup F (τ • Q) := by
  intro x
  obtain ⟨s, q, hs, hq, h⟩ := h (τ⁻¹ • x)
  refine ⟨τ • s, τ • q, ?_, Ideal.smul_mem_pointwise_smul τ q Q hq, ?_⟩
  · rw [← smul_one τ, ← smul_sub]
    exact Ideal.smul_mem_pointwise_smul τ _ Q hs
  · have := congrArg (τ • ·) h
    simp only [smul_mul', smul_sub, mul_smul, smul_inv_smul] at this
    exact this

/-- `P_{τQ} = τ P_Q τ⁻¹`. -/
theorem wildInertiaGroup_smul (τ : Field.absoluteGaloisGroup F) :
    wildInertiaGroup F (τ • Q) = (wildInertiaGroup F Q).map (MulAut.conj τ) := by
  ext σ
  rw [Subgroup.map_equiv_eq_comap_symm, Subgroup.mem_comap]
  refine ⟨fun h ↦ ?_, fun h ↦ mem_wildInertiaGroup_smul_of_mem (by simpa [mul_assoc] using h)⟩
  have := mem_wildInertiaGroup_smul_of_mem (Q := τ • Q) (τ := τ⁻¹) (σ := τ⁻¹ * σ * τ)
    (by simpa [mul_assoc] using h)
  simpa [smul_smul] using this

/-- `I_Q` is normal in `D_Q`. -/
instance normal_inertiaGroup_subgroupOf_decompositionGroup :
    ((inertiaGroup F Q).subgroupOf (decompositionGroup F Q)).Normal := by
  rw [inertiaGroup_def, decompositionGroup_def, AddSubgroup.subgroupOf_inertia]
  exact inferInstanceAs (Q.inertia (MulAction.stabilizer _ Q)).Normal

/-- `P_Q` is normal in `D_Q`. -/
instance normal_wildInertiaGroup_subgroupOf_decompositionGroup :
    ((wildInertiaGroup F Q).subgroupOf (decompositionGroup F Q)).Normal := by
  refine ⟨fun σ hσ τ ↦ ?_⟩
  rw [Subgroup.mem_subgroupOf] at hσ ⊢
  have hτ : (τ : Field.absoluteGaloisGroup F) • Q = Q := mem_decompositionGroup_iff.mp τ.2
  have : (τ : Field.absoluteGaloisGroup F) * σ * (τ : Field.absoluteGaloisGroup F)⁻¹ ∈
      wildInertiaGroup F ((τ : Field.absoluteGaloisGroup F) • Q) := by
    rw [wildInertiaGroup_smul]
    exact ⟨σ, hσ, rfl⟩
  rwa [hτ] at this

/-! ### Arithmetic Frobenius elements -/

variable {F} in
/-- `σ ∈ G_F` is an **arithmetic Frobenius** at an ideal `Q` of `O` if `σ x ≡ x ^ q mod Q` for all
`x ∈ O`, where `q` is the cardinality of the residue ring of `𝓞 F` below `Q`: Mathlib's
`AlgHom.IsArithFrobAt` for `toIntegralClosure F σ`. -/
def IsArithFrobAtIntegralPrime (σ : Field.absoluteGaloisGroup F)
    (Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F))) : Prop :=
  (toIntegralClosure F σ).toAlgHom.IsArithFrobAt Q

variable {F Q}

/-- `IsArithFrobAtIntegralPrime` is Mathlib's group-action `IsArithFrobAt` for the action of `G_F`
on `O`. -/
theorem isArithFrobAtIntegralPrime_iff {σ : Field.absoluteGaloisGroup F} :
    IsArithFrobAtIntegralPrime σ Q ↔ IsArithFrobAt (𝓞 F) σ Q :=
  Iff.rfl

namespace IsArithFrobAtIntegralPrime

variable {σ τ : Field.absoluteGaloisGroup F}

/-- An arithmetic Frobenius at a prime `Q` lies in the decomposition group `D_Q`. -/
theorem mem_decompositionGroup [Q.IsPrime] (h : IsArithFrobAtIntegralPrime σ Q) :
    σ ∈ decompositionGroup F Q :=
  IsArithFrobAt.mem_stabilizer h

/-- Two arithmetic Frobenius elements at `Q` differ by an element of `I_Q`. -/
theorem mul_inv_mem_inertiaGroup (hσ : IsArithFrobAtIntegralPrime σ Q)
    (hτ : IsArithFrobAtIntegralPrime τ Q) : τ * σ⁻¹ ∈ inertiaGroup F Q :=
  IsArithFrobAt.mul_inv_mem_inertia hτ hσ

/-- Given one arithmetic Frobenius `σ` at `Q`, the arithmetic Frobenius elements at `Q` are the
coset `I_Q σ`. -/
theorem isArithFrobAtIntegralPrime_iff_mul_inv_mem (hσ : IsArithFrobAtIntegralPrime σ Q) :
    IsArithFrobAtIntegralPrime τ Q ↔ τ * σ⁻¹ ∈ inertiaGroup F Q := by
  refine ⟨hσ.mul_inv_mem_inertiaGroup, fun h ↦ ?_⟩
  rw [isArithFrobAtIntegralPrime_iff] at hσ ⊢
  intro x
  have := Q.add_mem (mem_inertiaGroup_iff.mp h (σ • x)) (hσ x)
  simpa [mul_smul] using this

/-- Conjugating an arithmetic Frobenius at `Q` by `τ` gives an arithmetic Frobenius at `τ • Q`. -/
theorem conj (h : IsArithFrobAtIntegralPrime σ Q) (τ : Field.absoluteGaloisGroup F) :
    IsArithFrobAtIntegralPrime (τ * σ * τ⁻¹) (τ • Q) :=
  isArithFrobAtIntegralPrime_iff.mpr ((isArithFrobAtIntegralPrime_iff.mp h).conj τ)

end IsArithFrobAtIntegralPrime

end TauCeti.GaloisRep
