/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Basic
public import Mathlib.Analysis.Normed.Algebra.Unitization
public import TauCeti.Analysis.Normed.Algebra.Character.Basic
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.PuncturedCompact

import Mathlib.Analysis.Normed.Module.WeakDual

/-!
# Character space of a nonunital normed algebra and its unitization

For a nonunital Banach algebra `A` over a proper nontrivially normed field `𝕜`, every nonzero
multiplicative linear functional has norm at most `1`, so `WeakDual.characterSpace 𝕜 A ∪ {0}` is
compact in the weak-star topology and `WeakDual.characterSpace 𝕜 A` is locally compact Hausdorff.

For any nonunital normed `𝕜`-algebra `A`, its unitization `Unitization 𝕜 A` carries the canonical
augmentation character `Unitization.fstCharacter 𝕜 A : (r, a) ↦ r`. Extending each nonunital
character `φ` of `A` by `(r, a) ↦ r + φ a` and restricting characters of `Unitization 𝕜 A` unequal
to `fstCharacter 𝕜 A` along `Unitization.inr` gives a canonical homeomorphism
`Unitization.characterSpaceComplFstHomeomorph 𝕜 A : characterSpace 𝕜 A ≃ₜ {fstCharacter 𝕜 A}ᶜ`,
and hence `OnePoint (characterSpace 𝕜 A) ≃ₜ characterSpace 𝕜 (Unitization 𝕜 A)` when `A` is a
complete regular normed algebra and `𝕜` is proper.

We also record the two degenerate/unital regimes:
* when `A` is subsingleton, `fstCharacter 𝕜 A` is the unique character of `Unitization 𝕜 A` and
  its complement is empty;
* when `A` already has an identity, `{fstCharacter 𝕜 A}` is isolated (open) in
  `characterSpace 𝕜 (Unitization 𝕜 A)`, so `{fstCharacter 𝕜 A}ᶜ` is closed (and compact when `A`
  is a complete regular normed algebra and `𝕜` is proper).

## Main declarations

* `WeakDual.CharacterSpace.instLocallyCompactSpace`: `characterSpace 𝕜 A` is locally compact for
  any nonunital Banach algebra `A` over a proper nontrivially normed field `𝕜`.
* `WeakDual.CharacterSpace.equivNonUnitalAlgHom`: `characterSpace 𝕜 A ≃ {φ : A →ₙₐ[𝕜] 𝕜 // φ ≠ 0}`.
* `TauCeti.nonUnitalGelfandTransform`: the nonunital Gelfand transform
  `A →ₙₐ[𝕜] C₀(characterSpace 𝕜 A, 𝕜)` for a nonunital Banach algebra `A`.
* `Unitization.fstCharacter`: the augmentation character `(r, a) ↦ r` on `Unitization 𝕜 A`.
* `Unitization.characterSpaceComplFstHomeomorph`: the homeomorphism
  `characterSpace 𝕜 A ≃ₜ ({fstCharacter 𝕜 A}ᶜ : Set (characterSpace 𝕜 (Unitization 𝕜 A)))`.
* `Unitization.onePointCharacterSpaceHomeomorph`: the homeomorphism
  `OnePoint (characterSpace 𝕜 A) ≃ₜ characterSpace 𝕜 (Unitization 𝕜 A)`.
* `Unitization.isOpen_singleton_fstCharacter`: `{fstCharacter 𝕜 A}` is open when `A` is unital.

## References

* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Academic Press (1990), §2.1.
* H. G. Dales, *Banach Algebras and Automatic Continuity*, Clarendon Press (2000), §1.5.
-/

public section

open Topology WeakDual
open scoped OnePoint

namespace WeakDual.CharacterSpace

section NonUnitalBanach

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [CompleteSpace A]

/-- Every character of a nonunital Banach algebra has operator norm at most `1`. -/
theorem norm_toStrongDual_le_one (φ : characterSpace 𝕜 A) :
    ‖toStrongDual (φ : WeakDual 𝕜 A)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a ↦ by
    simpa using NonUnitalAlgHom.norm_apply_le_self φ a

/-- Nonzero nonunital algebra homomorphisms `A →ₙₐ[𝕜] 𝕜` on a nonunital Banach algebra correspond
bijectively to elements of `characterSpace 𝕜 A`, mirroring `WeakDual.CharacterSpace.equivAlgHom`
in the unital setting. -/
noncomputable def equivNonUnitalAlgHom :
    characterSpace 𝕜 A ≃ {φ : A →ₙₐ[𝕜] 𝕜 // φ ≠ 0} where
  toFun φ := ⟨toNonUnitalAlgHom φ, fun h ↦
    φ.prop.1 <| ContinuousLinearMap.ext fun a ↦ congr($h a)⟩
  invFun φ := ⟨{ toFun := φ.1
                 map_add' := map_add φ.1
                 map_smul' := map_smul φ.1
                 cont := map_continuous φ.1 },
    ⟨fun h ↦ φ.2 <| NonUnitalAlgHom.ext fun a ↦ congr($h a), map_mul φ.1⟩⟩
  left_inv _ := ext fun _ ↦ rfl
  right_inv _ := Subtype.ext <| NonUnitalAlgHom.ext fun _ ↦ rfl

/-- `equivNonUnitalAlgHom` preserves pointwise evaluation. -/
@[simp]
theorem equivNonUnitalAlgHom_apply (φ : characterSpace 𝕜 A) (a : A) :
    (equivNonUnitalAlgHom φ).1 a = φ a := (rfl)

/-- `equivNonUnitalAlgHom.symm` preserves pointwise evaluation. -/
@[simp]
theorem equivNonUnitalAlgHom_symm_apply (φ : {φ : A →ₙₐ[𝕜] 𝕜 // φ ≠ 0}) (a : A) :
    equivNonUnitalAlgHom.symm φ a = φ.1 a := (rfl)

variable (𝕜 A) in
/-- For a nonunital Banach algebra over a proper nontrivially normed field,
`characterSpace 𝕜 A ∪ {0}` is weak-star compact in `WeakDual 𝕜 A`. -/
theorem isCompact_union_zero [ProperSpace 𝕜] :
    IsCompact (characterSpace 𝕜 A ∪ {0} : Set (WeakDual 𝕜 A)) :=
  (isCompact_closedBall 0 1).of_isClosed_subset (union_zero_isClosed 𝕜 A) fun φ hφ ↦ by
    rcases hφ with hφ | rfl
    · exact mem_closedBall_zero_iff.mpr (norm_toStrongDual_le_one ⟨φ, hφ⟩)
    · simp

/-- The character space of a nonunital Banach algebra over a proper nontrivially normed field is
locally compact: `characterSpace 𝕜 A ∪ {0}` is compact by Banach–Alaoglu and `{0}` is removed as a
closed singleton. -/
instance instLocallyCompactSpace [ProperSpace 𝕜] : LocallyCompactSpace (characterSpace 𝕜 A) := by
  let K : Set (WeakDual 𝕜 A) := characterSpace 𝕜 A ∪ {0}
  have hK : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_union_zero 𝕜 A)
  have hopen : Topology.IsOpenEmbedding (Set.inclusion (Set.subset_union_left : _ ⊆ K)) := by
    refine ⟨Topology.IsEmbedding.inclusion _, ?_⟩
    convert (isOpen_compl_singleton (x := (⟨0, Or.inr rfl⟩ : K)))
    ext ⟨φ, hφ⟩
    simp only [Set.mem_range, Set.inclusion, Set.mem_compl_iff, Set.mem_singleton_iff,
      Subtype.ext_iff]
    exact ⟨by rintro ⟨ψ, rfl⟩; exact ψ.2.1,
      fun h0 ↦ ⟨⟨φ, hφ.resolve_right (Set.notMem_singleton_iff.mpr h0)⟩, rfl⟩⟩
  exact hopen.locallyCompactSpace

end NonUnitalBanach

end WeakDual.CharacterSpace

namespace TauCeti

open scoped ZeroAtInfty

/-- The **nonunital Gelfand transform** of a nonunital Banach algebra `A` over a proper nontrivially
normed field `𝕜`, sending `a : A` to the continuous function `φ ↦ φ a` vanishing at infinity on
`characterSpace 𝕜 A`. -/
noncomputable def nonUnitalGelfandTransform (𝕜 A : Type*) [NontriviallyNormedField 𝕜]
    [ProperSpace 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [CompleteSpace A] :
    A →ₙₐ[𝕜] C₀(characterSpace 𝕜 A, 𝕜) where
  toFun a :=
    { toFun φ := φ a
      continuous_toFun := (eval_continuous a).comp continuous_subtype_val
      zero_at_infty' := by
        let K : Set (WeakDual 𝕜 A) := characterSpace 𝕜 A ∪ {0}
        have : CompactSpace K :=
          isCompact_iff_compactSpace.mp (CharacterSpace.isCompact_union_zero 𝕜 A)
        let z₀ : K := ⟨0, Or.inr rfl⟩
        let e : characterSpace 𝕜 A ≃ₜ ({z₀}ᶜ : Set K) :=
          { toFun φ := ⟨⟨φ.1, Or.inl φ.2⟩, Subtype.coe_ne_coe.mp φ.2.1⟩
            invFun ψ := ⟨ψ.1.1, ψ.1.2.resolve_right
              (Set.notMem_singleton_iff.mpr (Subtype.coe_ne_coe.mpr ψ.2))⟩
            left_inv _ := rfl
            right_inv _ := rfl
            continuous_toFun :=
              Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _
            continuous_invFun :=
              Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _ }
        exact (((eval_continuous a).comp continuous_subtype_val).tendsto z₀).comp
          ((OnePoint.tendsto_subtype_val_cocompact_compl_singleton z₀).comp
            (cocompact_tendsto e.toCocompactMap)) }
  map_smul' r a := ZeroAtInftyContinuousMap.ext fun φ ↦ map_smul φ r a
  map_zero' := ZeroAtInftyContinuousMap.ext fun φ ↦ map_zero φ
  map_add' a b := ZeroAtInftyContinuousMap.ext fun φ ↦ map_add φ a b
  map_mul' a b := ZeroAtInftyContinuousMap.ext fun φ ↦ map_mul φ a b

/-- `nonUnitalGelfandTransform 𝕜 A a` evaluates at `φ : characterSpace 𝕜 A` to `φ a`. -/
@[simp]
theorem nonUnitalGelfandTransform_apply {𝕜 A : Type*} [NontriviallyNormedField 𝕜]
    [ProperSpace 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [CompleteSpace A]
    (a : A) (φ : characterSpace 𝕜 A) :
    nonUnitalGelfandTransform 𝕜 A a φ = φ a := by
  rfl

end TauCeti

namespace Unitization

section NonUnitalNormedAlgebra

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A]
  [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]

variable (𝕜 A) in
/-- The canonical augmentation character `(r, a) ↦ r` on `Unitization 𝕜 A`, viewed as an element
of `characterSpace 𝕜 (Unitization 𝕜 A)`. -/
noncomputable def fstCharacter : characterSpace 𝕜 (Unitization 𝕜 A) :=
  ⟨StrongDual.toWeakDual
    { toFun := fun x ↦ x.fst
      map_add' := fst_add
      map_smul' := fst_smul
      cont := Unitization.continuous_fst }, by
    rw [CharacterSpace.eq_set_map_one_map_mul]
    exact ⟨fst_one (A := A), fst_mul⟩⟩

/-- `fstCharacter 𝕜 A` evaluates to the scalar coordinate `x.fst`. -/
@[simp]
theorem fstCharacter_apply (x : Unitization 𝕜 A) : fstCharacter 𝕜 A x = x.fst := by
  rfl

/-- `fstCharacter 𝕜 A` vanishes on `A`. -/
theorem fstCharacter_inr (a : A) : fstCharacter 𝕜 A a = 0 :=
  fst_inr 𝕜 a

/-- `fstCharacter 𝕜 A` acts as the identity on scalars `inl k`. -/
theorem fstCharacter_inl (k : 𝕜) : fstCharacter 𝕜 A (inl k) = k :=
  fst_inl A k

/-- `CharacterSpace.toAlgHom` sends `fstCharacter 𝕜 A` to `fstHom 𝕜 A`. -/
@[simp]
theorem toAlgHom_fstCharacter :
    CharacterSpace.toAlgHom (fstCharacter 𝕜 A) = fstHom 𝕜 A :=
  AlgHom.ext fun _ ↦ by rfl

/-- Extend a character `φ : characterSpace 𝕜 A` to a character of `Unitization 𝕜 A` distinct from
`fstCharacter 𝕜 A` via `(r, a) ↦ r + φ a`. -/
private noncomputable def liftCharacter (φ : characterSpace 𝕜 A) :
    ({fstCharacter 𝕜 A}ᶜ : Set (characterSpace 𝕜 (Unitization 𝕜 A))) :=
  ⟨⟨StrongDual.toWeakDual
      { toFun := fun x ↦ x.fst + φ x.snd
        map_add' := fun x y ↦ by rw [fst_add, snd_add, map_add]; abel
        map_smul' := fun r x ↦ by
          rw [fst_smul, snd_smul, map_smul]
          simp [smul_eq_mul, mul_add]
        cont := Unitization.continuous_fst.add
          ((map_continuous φ).comp Unitization.continuous_snd) },
    by
      rw [CharacterSpace.eq_set_map_one_map_mul]
      refine ⟨by simp, fun x y ↦ ?_⟩
      simpa [lift_apply] using map_mul (lift (CharacterSpace.toNonUnitalAlgHom φ)) x y⟩,
    fun h ↦ φ.prop.1 <| toStrongDual.injective <| ContinuousLinearMap.ext fun a ↦ by
      have ha : (0 : 𝕜) + φ a = fstCharacter 𝕜 A a := DFunLike.congr_fun h (a : Unitization 𝕜 A)
      simpa using ha⟩

/-- Restrict a character `ψ` of `Unitization 𝕜 A` distinct from `fstCharacter 𝕜 A` to a character
of `A` along `Unitization.inr`. -/
private noncomputable def restrictCharacter
    (ψ : ({fstCharacter 𝕜 A}ᶜ : Set (characterSpace 𝕜 (Unitization 𝕜 A)))) :
    characterSpace 𝕜 A :=
  ⟨StrongDual.toWeakDual
    { toFun := fun a ↦ ψ.1 a
      map_add' := fun a b ↦ by rw [inr_add, map_add]
      map_smul' := fun r a ↦ by rw [inr_smul, map_smul]; rfl
      cont := (map_continuous ψ.1).comp
        (continuous_induced_rng.mpr (continuous_const.prodMk continuous_id)) },
    ⟨fun h0 ↦ ψ.2 <| algHom_ext'' (R := 𝕜) (A := A) fun a ↦
        DFunLike.congr_fun h0 a,
      fun a b ↦ by simp [inr_mul]⟩⟩

variable (𝕜 A) in
/-- Extending characters of `A` to `Unitization 𝕜 A` and restricting along `inr` give a canonical
homeomorphism `characterSpace 𝕜 A ≃ₜ {fstCharacter 𝕜 A}ᶜ`. -/
noncomputable def characterSpaceComplFstHomeomorph :
    characterSpace 𝕜 A ≃ₜ ({fstCharacter 𝕜 A}ᶜ : Set (characterSpace 𝕜 (Unitization 𝕜 A))) where
  toFun := liftCharacter
  invFun := restrictCharacter
  left_inv φ := CharacterSpace.ext fun a ↦ zero_add (φ a)
  right_inv ψ := Subtype.ext <| algHom_ext'' (R := 𝕜) (A := A) fun a ↦ zero_add (ψ.1 a)
  continuous_toFun :=
    Continuous.subtype_mk (Continuous.subtype_mk
      (WeakDual.continuous_of_continuous_eval
        (g := fun φ : characterSpace 𝕜 A ↦ ((liftCharacter φ).1 : WeakDual 𝕜 (Unitization 𝕜 A)))
        fun x ↦ continuous_const.add ((eval_continuous x.snd).comp continuous_subtype_val)) _) _
  continuous_invFun :=
    Continuous.subtype_mk
      (WeakDual.continuous_of_continuous_eval
        (g := fun ψ : ({fstCharacter 𝕜 A}ᶜ : Set _) ↦ (restrictCharacter ψ : WeakDual 𝕜 A))
        fun a ↦ (eval_continuous (a : Unitization 𝕜 A)).comp
          (continuous_subtype_val.comp continuous_subtype_val)) _

/-- `characterSpaceComplFstHomeomorph 𝕜 A φ` evaluates on `x` to `x.fst + φ x.snd`. -/
@[simp]
theorem characterSpaceComplFstHomeomorph_apply_coe (φ : characterSpace 𝕜 A)
    (x : Unitization 𝕜 A) :
    (characterSpaceComplFstHomeomorph 𝕜 A φ : characterSpace 𝕜 (Unitization 𝕜 A)) x =
      x.fst + φ x.snd := by
  rfl

/-- `characterSpaceComplFstHomeomorph 𝕜 A φ` agrees with `φ` on `A`. -/
theorem characterSpaceComplFstHomeomorph_apply_inr (φ : characterSpace 𝕜 A) (a : A) :
    (characterSpaceComplFstHomeomorph 𝕜 A φ : characterSpace 𝕜 (Unitization 𝕜 A)) a = φ a := by
  simp

/-- The inverse of `characterSpaceComplFstHomeomorph 𝕜 A` restricts along `Unitization.inr`. -/
@[simp]
theorem characterSpaceComplFstHomeomorph_symm_apply
    (ψ : ({fstCharacter 𝕜 A}ᶜ : Set (characterSpace 𝕜 (Unitization 𝕜 A)))) (a : A) :
    (characterSpaceComplFstHomeomorph 𝕜 A).symm ψ a = ψ.1 a := by
  rfl

/-- When `A` is subsingleton, `fstCharacter 𝕜 A` is the unique character of `Unitization 𝕜 A`. -/
noncomputable instance instUniqueCharacterSpace [Subsingleton A] :
    Unique (characterSpace 𝕜 (Unitization 𝕜 A)) where
  default := fstCharacter 𝕜 A
  uniq ψ := algHom_ext'' fun a ↦ by simp [Subsingleton.elim a 0]

/-- When `A` is subsingleton, the punctured character space `{fstCharacter 𝕜 A}ᶜ` is empty. -/
instance instIsEmptyComplFstCharacter [Subsingleton A] :
    IsEmpty ({fstCharacter 𝕜 A}ᶜ : Set (characterSpace 𝕜 (Unitization 𝕜 A))) :=
  (characterSpaceComplFstHomeomorph 𝕜 A).symm.toEquiv.isEmpty

variable (𝕜 A) in
/-- When `A` is a complete regular normed algebra and `𝕜` is proper, the one-point
compactification of `characterSpace 𝕜 A` is canonically homeomorphic to
`characterSpace 𝕜 (Unitization 𝕜 A)`, sending `∞` to `fstCharacter 𝕜 A`. -/
noncomputable def onePointCharacterSpaceHomeomorph [RegularNormedAlgebra 𝕜 A] [ProperSpace 𝕜]
    [CompleteSpace A] :
    OnePoint (characterSpace 𝕜 A) ≃ₜ characterSpace 𝕜 (Unitization 𝕜 A) :=
  (characterSpaceComplFstHomeomorph 𝕜 A).onePointCongr.trans
    (OnePoint.complSingletonHomeomorph (fstCharacter 𝕜 A))

/-- `onePointCharacterSpaceHomeomorph 𝕜 A` sends `∞` to `fstCharacter 𝕜 A`. -/
@[simp]
theorem onePointCharacterSpaceHomeomorph_infty [RegularNormedAlgebra 𝕜 A] [ProperSpace 𝕜]
    [CompleteSpace A] :
    onePointCharacterSpaceHomeomorph 𝕜 A ∞ = fstCharacter 𝕜 A := by
  simp [onePointCharacterSpaceHomeomorph]

/-- `onePointCharacterSpaceHomeomorph 𝕜 A` sends a finite character `φ` to its unitized lift. -/
@[simp]
theorem onePointCharacterSpaceHomeomorph_coe [RegularNormedAlgebra 𝕜 A] [ProperSpace 𝕜]
    [CompleteSpace A] (φ : characterSpace 𝕜 A) :
    onePointCharacterSpaceHomeomorph 𝕜 A φ = (characterSpaceComplFstHomeomorph 𝕜 A φ).1 := by
  simp [onePointCharacterSpaceHomeomorph]

end NonUnitalNormedAlgebra

section Unital

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]

/-- When `A` is unital, a character of `Unitization 𝕜 A` sends `(1 : A)` to either `0` or `1`. -/
theorem apply_inr_one_eq_zero_or_one (ψ : characterSpace 𝕜 (Unitization 𝕜 A)) :
    ψ ((1 : A) : Unitization 𝕜 A) = 0 ∨ ψ ((1 : A) : Unitization 𝕜 A) = 1 := by
  have hidem : ψ ((1 : A) : Unitization 𝕜 A) * (ψ ((1 : A) : Unitization 𝕜 A) - 1) = 0 := by
    rw [mul_sub, mul_one, ← map_mul, ← inr_mul, one_mul, sub_self]
  exact (mul_eq_zero.mp hidem).imp id sub_eq_zero.mp

/-- When `A` is unital, a character of `Unitization 𝕜 A` vanishes at `(1 : A)` if and only if it is
`fstCharacter 𝕜 A`. -/
@[simp]
theorem apply_inr_one_eq_zero_iff (ψ : characterSpace 𝕜 (Unitization 𝕜 A)) :
    ψ ((1 : A) : Unitization 𝕜 A) = 0 ↔ ψ = fstCharacter 𝕜 A := by
  refine ⟨fun h0 ↦ algHom_ext'' fun a ↦ ?_, fun h ↦ h ▸ fstCharacter_inr 1⟩
  calc ψ (a : Unitization 𝕜 A)
      _ = ψ ((a * 1 : A) : Unitization 𝕜 A) := by rw [mul_one]
      _ = ψ (a : Unitization 𝕜 A) * ψ ((1 : A) : Unitization 𝕜 A) := by rw [inr_mul, map_mul]
      _ = fstCharacter 𝕜 A a := by simp [h0]

/-- When `A` is unital, `{fstCharacter 𝕜 A}` is isolated (open) in
`characterSpace 𝕜 (Unitization 𝕜 A)`. -/
theorem isOpen_singleton_fstCharacter :
    IsOpen ({fstCharacter 𝕜 A} : Set (characterSpace 𝕜 (Unitization 𝕜 A))) := by
  have heq : ({fstCharacter 𝕜 A} : Set (characterSpace 𝕜 (Unitization 𝕜 A))) =
      (fun ψ : characterSpace 𝕜 (Unitization 𝕜 A) ↦ ψ ((1 : A) : Unitization 𝕜 A)) ⁻¹'
        ({1}ᶜ : Set 𝕜) := by
    ext ψ
    rcases apply_inr_one_eq_zero_or_one ψ with h0 | h1
    · simp [(apply_inr_one_eq_zero_iff ψ).mp h0]
    · exact ⟨fun hψ ↦ absurd (hψ ▸ h1) (by simp), fun hne ↦ False.elim (hne h1)⟩
  rw [heq]
  exact isOpen_compl_singleton.preimage <|
    (eval_continuous ((1 : A) : Unitization 𝕜 A)).comp continuous_subtype_val

/-- When `A` is unital, `{fstCharacter 𝕜 A}ᶜ` is closed in `characterSpace 𝕜 (Unitization 𝕜 A)`. -/
theorem isClosed_compl_singleton_fstCharacter :
    IsClosed ({fstCharacter 𝕜 A}ᶜ : Set (characterSpace 𝕜 (Unitization 𝕜 A))) :=
  isOpen_singleton_fstCharacter.isClosed_compl

/-- When `A` is a unital regular Banach algebra over a proper nontrivially normed field `𝕜`, the
punctured character space `{fstCharacter 𝕜 A}ᶜ` is compact. -/
theorem compactSpace_compl_singleton_fstCharacter [RegularNormedAlgebra 𝕜 A] [ProperSpace 𝕜]
    [CompleteSpace A] :
    CompactSpace ({fstCharacter 𝕜 A}ᶜ : Set (characterSpace 𝕜 (Unitization 𝕜 A))) :=
  OnePoint.compactSpace_compl_singleton_of_isOpen isOpen_singleton_fstCharacter

end Unital

end Unitization
