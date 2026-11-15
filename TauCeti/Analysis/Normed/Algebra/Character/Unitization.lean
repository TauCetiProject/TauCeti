/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.GelfandDuality
public import Mathlib.Analysis.Normed.Algebra.Unitization
public import Mathlib.RingTheory.TwoSidedIdeal.Kernel
public import TauCeti.Analysis.Normed.Algebra.Character.Basic
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.ComplSingleton
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Star

import Mathlib.Analysis.Normed.Module.WeakDual
import TauCeti.Analysis.Normed.Algebra.Unitization.Basic

/-!
# Nonunital character spaces, the nonunital Gelfand transform, and unitizations

For a nonunital Banach algebra `A` over a normed field `𝕜`, every nonunital scalar character
`φ : A →ₙₐ[𝕜] 𝕜` is contractive (`NonUnitalAlgHom.norm_apply_le_self`), so `characterSpace 𝕜 A`
identifies with `{φ : A →ₙₐ[𝕜] 𝕜 // φ ≠ 0}` and lies inside the closed unit ball of the dual.
When `𝕜` is a proper nontrivially normed field (such as `ℝ` or `ℂ`), Banach–Alaoglu makes
`characterSpace 𝕜 A ∪ {0}` compact in `WeakDual 𝕜 A`. Removing `{0}` exhibits `characterSpace 𝕜 A`
as an open subset of a compact Hausdorff space, hence locally compact, and shows that point
evaluation `a ↦ (φ ↦ φ a)` vanishes at infinity on `characterSpace 𝕜 A`. This defines the
nonunital Gelfand transform
`WeakDual.nonUnitalGelfandTransform 𝕜 A : A →ₙₐ[𝕜] C₀(characterSpace 𝕜 A, 𝕜)`,
which preserves the quasispectrum on commutative complex Banach algebras.

When `A` is a regular normed Banach algebra over a complete nontrivially normed field `𝕜`, its
minimal unitization `Unitization 𝕜 A` carries a canonical scalar-projection character
`WeakDual.CharacterSpace.fstCharacter 𝕜 A` (`(r, a) ↦ r`). Lifting nonunital characters to
`Unitization 𝕜 A` identifies `characterSpace 𝕜 A` homeomorphically with the punctured space
`({fstCharacter 𝕜 A}ᶜ : Set (characterSpace 𝕜 (Unitization 𝕜 A)))`, and when `𝕜` is proper this
realizes `characterSpace 𝕜 (Unitization 𝕜 A)` as the one-point compactification
`OnePoint (characterSpace 𝕜 A)`.

## Main declarations

* `WeakDual.CharacterSpace.equivNonUnitalAlgHom`: identifies `characterSpace 𝕜 A` with nonzero
  nonunital algebra homomorphisms `{φ : A →ₙₐ[𝕜] 𝕜 // φ ≠ 0}`.
* `WeakDual.CharacterSpace.isCompact_union_zero` and
  `WeakDual.CharacterSpace.instLocallyCompactSpace`: compactness of `characterSpace 𝕜 A ∪ {0}` and
  local compactness of `characterSpace 𝕜 A` over proper fields.
* `WeakDual.nonUnitalGelfandTransform`: the nonunital Gelfand transform
  `A →ₙₐ[𝕜] C₀(characterSpace 𝕜 A, 𝕜)`, with quasispectrum preservation
  `quasispectrum.nonUnitalGelfandTransform_eq` on commutative complex Banach algebras.
* `WeakDual.CharacterSpace.fstCharacter` and `WeakDual.CharacterSpace.liftUnitization`: the
  scalar-projection character `(r, a) ↦ r` on `Unitization 𝕜 A` and the canonical lift of
  `φ : characterSpace 𝕜 A` to `characterSpace 𝕜 (Unitization 𝕜 A)`.
* `WeakDual.CharacterSpace.homeoComplFstCharacter` and
  `WeakDual.CharacterSpace.onePointHomeoUnitization`: the homeomorphisms
  `characterSpace 𝕜 A ≃ₜ ({fstCharacter 𝕜 A}ᶜ : Set (characterSpace 𝕜 (Unitization 𝕜 A)))` and
  `OnePoint (characterSpace 𝕜 A) ≃ₜ characterSpace 𝕜 (Unitization 𝕜 A)`.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §§2.2–2.3.
* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*, §II.2.2.
* G. J. Murphy, *C*-Algebras and Operator Theory*, §§2.1–2.2.
* Parallels Mathlib's unital character-space API (`WeakDual.characterSpace`,
  `WeakDual.CharacterSpace.equivAlgHom`, `WeakDual.gelfandTransform`, and
  `spectrum.gelfandTransform_eq` in `Mathlib.Topology.Algebra.Module.Spaces.CharacterSpace`,
  `Mathlib.Analysis.Normed.Algebra.Spectrum`, and `Mathlib.Analysis.CStarAlgebra.GelfandDuality`),
  and uses `NonUnitalAlgHom.norm_apply_le_self` from
  `TauCeti.Analysis.Normed.Algebra.Character.Basic`.
-/

public section

open Filter Topology OnePoint
open scoped ZeroAtInfty

namespace NonUnitalAlgHom

section NormedField

variable {𝕜 A : Type*} [NormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [CompleteSpace A]

/-- A nonunital scalar character of a Banach algebra bundled as a continuous linear functional,
mirroring `AlgHom.toContinuousLinearMap`. -/
def toContinuousLinearMap (φ : A →ₙₐ[𝕜] 𝕜) : StrongDual 𝕜 A where
  toFun := φ
  map_add' := map_add φ
  map_smul' := map_smul φ
  cont := map_continuous φ

@[simp]
theorem coe_toContinuousLinearMap (φ : A →ₙₐ[𝕜] 𝕜) : ⇑φ.toContinuousLinearMap = φ := (rfl)

end NormedField

section NontriviallyNormedField

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [CompleteSpace A]

/-- Every nonunital scalar character of a Banach algebra has operator norm at most `1`. -/
theorem norm_toContinuousLinearMap_le (φ : A →ₙₐ[𝕜] 𝕜) : ‖φ.toContinuousLinearMap‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => by simpa using norm_apply_le_self φ a

end NontriviallyNormedField

end NonUnitalAlgHom

namespace WeakDual

namespace CharacterSpace

section Topological

variable {𝕜 A : Type*} [CommRing 𝕜] [NoZeroDivisors 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [NonUnitalSemiring A] [TopologicalSpace A] [Module 𝕜 A]

/-- Any character of `A` maps a left multiplicative identity of `A` to `1`. -/
theorem apply_eq_one_of_forall_mul_eq (φ : characterSpace 𝕜 A) {e : A}
    (he : ∀ a : A, e * a = a) : φ e = 1 := by
  have hex : ∃ a : A, φ a ≠ 0 := by
    by_contra! h
    exact φ.prop.1 (ContinuousLinearMap.ext h)
  obtain ⟨a, ha⟩ := hex
  have hmul : (φ e - 1) * φ a = 0 := by
    rw [sub_mul, one_mul, ← map_mul, he a, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right ha)

end Topological

section NonUnital

variable {𝕜 A : Type*} [NormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [CompleteSpace A]

/-- The character space of a nonunital Banach algebra is in bijection with its nonzero nonunital
scalar algebra homomorphisms. -/
noncomputable def equivNonUnitalAlgHom : characterSpace 𝕜 A ≃ {φ : A →ₙₐ[𝕜] 𝕜 // φ ≠ 0} where
  toFun φ := ⟨toNonUnitalAlgHom φ, fun h =>
    φ.prop.1 (ContinuousLinearMap.ext fun a => DFunLike.congr_fun h a)⟩
  invFun φ := ⟨φ.1.toContinuousLinearMap, ⟨fun h =>
    φ.2 (DFunLike.ext _ _ fun a => DFunLike.congr_fun h a), map_mul φ.1⟩⟩
  left_inv φ := by ext a; rfl
  right_inv φ := by ext a; rfl

@[simp]
theorem equivNonUnitalAlgHom_coe (φ : characterSpace 𝕜 A) :
    ⇑(equivNonUnitalAlgHom φ : A →ₙₐ[𝕜] 𝕜) = φ := (rfl)

@[simp]
theorem equivNonUnitalAlgHom_symm_coe (φ : {φ : A →ₙₐ[𝕜] 𝕜 // φ ≠ 0}) :
    ⇑(equivNonUnitalAlgHom.symm φ) = φ.1 := (rfl)

end NonUnital

section NormBound

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [NonUnitalNormedRing A] [NormedSpace 𝕜 A]
  [CompleteSpace A]

/-- Every element of the character space of a nonunital Banach algebra has dual norm at most `1`. -/
theorem norm_le_one (φ : characterSpace 𝕜 A) : ‖toStrongDual (φ : WeakDual 𝕜 A)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a =>
    (one_mul ‖a‖).symm ▸ NonUnitalAlgHom.norm_apply_le_self φ a

end NormBound

section ProperSpace

variable (𝕜 A : Type*) [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
  [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [CompleteSpace A]

/-- In a nonunital Banach algebra over a proper nontrivially normed field,
`characterSpace 𝕜 A ∪ {0}` is weak-star compact. -/
theorem isCompact_union_zero : IsCompact (characterSpace 𝕜 A ∪ {0}) := by
  refine (isCompact_closedBall 0 1).of_isClosed_subset (union_zero_isClosed 𝕜 A) ?_
  rintro φ (hφ | rfl)
  · rw [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    exact norm_le_one ⟨φ, hφ⟩
  · simp

instance instCompactSpaceUnionZero :
    CompactSpace (characterSpace 𝕜 A ∪ {0} : Set (WeakDual 𝕜 A)) :=
  isCompact_iff_compactSpace.mp (isCompact_union_zero 𝕜 A)

/-- The zero functional as a basepoint of `(characterSpace 𝕜 A ∪ {0} : Set (WeakDual 𝕜 A))`. -/
private noncomputable def zeroInUnionZero : (characterSpace 𝕜 A ∪ {0} : Set (WeakDual 𝕜 A)) :=
  ⟨0, Or.inr rfl⟩

/-- `characterSpace 𝕜 A` is homeomorphic to the complement of `0` inside the compact Hausdorff space
`characterSpace 𝕜 A ∪ {0}`. -/
private def homeoComplZeroInUnionZero :
    characterSpace 𝕜 A ≃ₜ
      ({zeroInUnionZero 𝕜 A}ᶜ : Set (characterSpace 𝕜 A ∪ {0} : Set (WeakDual 𝕜 A))) where
  toFun φ := ⟨⟨φ.1, Or.inl φ.2⟩, fun h => φ.2.1 (congrArg Subtype.val h)⟩
  invFun ψ := ⟨ψ.1.1, ψ.1.2.resolve_right fun h => ψ.2 (Subtype.ext h)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := Continuous.subtype_mk
    (Continuous.subtype_mk continuous_subtype_val _) _
  continuous_invFun := Continuous.subtype_mk
    (continuous_subtype_val.comp continuous_subtype_val) _

/-- The character space of a nonunital Banach algebra over a proper nontrivially normed field is
locally compact. -/
instance instLocallyCompactSpace : LocallyCompactSpace (characterSpace 𝕜 A) := by
  have : LocallyCompactSpace
      ({zeroInUnionZero 𝕜 A}ᶜ : Set (characterSpace 𝕜 A ∪ {0} : Set (WeakDual 𝕜 A))) :=
    isOpen_compl_singleton.locallyCompactSpace
  exact (homeoComplZeroInUnionZero 𝕜 A).isOpenEmbedding.locallyCompactSpace

/-- Evaluation at any element `a : A` vanishes along the cocompact filter on
`characterSpace 𝕜 A`. -/
theorem tendsto_eval_cocompact (a : A) :
    Tendsto (fun φ : characterSpace 𝕜 A => φ a) (cocompact (characterSpace 𝕜 A)) (𝓝 0) := by
  let F : C((characterSpace 𝕜 A ∪ {0} : Set (WeakDual 𝕜 A)), 𝕜) :=
    ⟨fun x => x.1 a, (eval_continuous (𝕜 := 𝕜) a).comp continuous_subtype_val⟩
  have hF : F (zeroInUnionZero 𝕜 A) = 0 := by simp [F, zeroInUnionZero]; rfl
  refine (zero_at_infty ((F.restrictComplSingleton hF).comp
    (homeoComplZeroInUnionZero 𝕜 A).toCocompactMap)).congr fun φ => ?_
  simp [F, homeoComplZeroInUnionZero]

end ProperSpace

end CharacterSpace

section NonUnitalGelfandTransform

variable (𝕜 A : Type*) [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
  [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [CompleteSpace A]

/-- The **nonunital Gelfand transform** of a nonunital Banach algebra `A` over a proper nontrivially
normed field `𝕜`, sending `a : A` to evaluation `φ ↦ φ a` as a continuous function vanishing at
infinity on `characterSpace 𝕜 A`. -/
noncomputable def nonUnitalGelfandTransform : A →ₙₐ[𝕜] C₀(characterSpace 𝕜 A, 𝕜) where
  toFun a :=
    { toFun := fun φ => φ a
      continuous_toFun := (eval_continuous (𝕜 := 𝕜) a).comp continuous_subtype_val
      zero_at_infty' := CharacterSpace.tendsto_eval_cocompact 𝕜 A a }
  map_smul' _ _ := by ext; simp
  map_zero' := by ext; simp
  map_add' _ _ := by ext; simp
  map_mul' _ _ := by ext; simp

@[simp]
theorem nonUnitalGelfandTransform_apply (a : A) (φ : characterSpace 𝕜 A) :
    nonUnitalGelfandTransform 𝕜 A a φ = φ a := (rfl)

/-- The nonunital Gelfand transform of a Banach algebra is norm-contractive. -/
theorem norm_nonUnitalGelfandTransform_le (a : A) :
    ‖nonUnitalGelfandTransform 𝕜 A a‖ ≤ ‖a‖ :=
  (ZeroAtInftyContinuousMap.norm_le (norm_nonneg a)).2 fun φ => by
    simpa using NonUnitalAlgHom.norm_apply_le_self φ a

/-- On a unital Banach algebra `B`, the nonunital Gelfand transform agrees with the unital
`gelfandTransform` lifted from `C(characterSpace 𝕜 B, 𝕜)` to `C₀(characterSpace 𝕜 B, 𝕜)`. -/
theorem nonUnitalGelfandTransform_eq_liftZeroAtInfty {B : Type*}
    [NormedRing B] [NormedAlgebra 𝕜 B] [CompleteSpace B] (b : B) :
    nonUnitalGelfandTransform 𝕜 B b =
      ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty (gelfandTransform 𝕜 B b) := by
  ext φ
  simp

end NonUnitalGelfandTransform

section CommBanachAlgebra

variable {A : Type*} [NonUnitalNormedCommRing A] [NormedSpace ℂ A] [IsScalarTower ℂ A A]
  [SMulCommClass ℂ A A] [CompleteSpace A]

/-- In a commutative complex Banach algebra, a scalar `z : ℂ` lies in `quasispectrum ℂ a` if and
only if either `z = 0` or `z = φ a` for some character `φ : characterSpace ℂ A`. -/
theorem CharacterSpace.mem_quasispectrum_iff_eq_zero_or_exists {a : A} {z : ℂ} :
    z ∈ quasispectrum ℂ a ↔ z = 0 ∨ ∃ φ : characterSpace ℂ A, φ a = z := by
  refine ⟨fun hz => ?_, ?_⟩
  · by_cases hz0 : z = 0
    · exact Or.inl hz0
    · right
      rw [Unitization.quasispectrum_eq_spectrum_inr ℂ a,
        ← AlgEquiv.spectrum_eq (WithLp.unitizationAlgEquiv ℂ).symm (a : Unitization ℂ A)] at hz
      obtain ⟨χ, hχ⟩ := CharacterSpace.mem_spectrum_iff_exists.mp hz
      let ψ : A →ₙₐ[ℂ] ℂ :=
        ((CharacterSpace.toAlgHom χ).comp (WithLp.unitizationAlgEquiv ℂ).symm.toAlgHom)
          |>.toNonUnitalAlgHom.comp (Unitization.inrNonUnitalAlgHom ℂ A)
      have hψa : ψ a = z := hχ
      have hψ0 : ψ ≠ 0 := fun h => hz0 (hψa.symm.trans (DFunLike.congr_fun h a))
      exact ⟨CharacterSpace.equivNonUnitalAlgHom.symm ⟨ψ, hψ0⟩, by simpa using hψa⟩
  · rintro (rfl | ⟨φ, rfl⟩)
    · exact quasispectrum.zero_mem ℂ a
    · exact NonUnitalAlgHom.apply_mem_quasispectrum φ a

/-- The nonunital Gelfand transform of a commutative complex Banach algebra preserves the
quasispectrum, extending `spectrum.gelfandTransform_eq` to the nonunital setting. -/
theorem _root_.quasispectrum.nonUnitalGelfandTransform_eq (a : A) :
    quasispectrum ℂ (nonUnitalGelfandTransform ℂ A a) = quasispectrum ℂ a := by
  ext z
  rw [ZeroAtInftyContinuousMap.quasispectrum_eq_insert_zero_range,
    CharacterSpace.mem_quasispectrum_iff_eq_zero_or_exists]
  simp only [Set.mem_insert_iff, Set.mem_range, nonUnitalGelfandTransform_apply]

end CommBanachAlgebra

namespace CharacterSpace

section Unitization

variable {𝕜 A : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
  [RegularNormedAlgebra 𝕜 A] [CompleteSpace A]

variable (𝕜 A) in
/-- The canonical scalar-projection character `(r, a) ↦ r` on `Unitization 𝕜 A`. -/
noncomputable def fstCharacter : characterSpace 𝕜 (Unitization 𝕜 A) :=
  equivAlgHom.symm (Unitization.fstHom 𝕜 A)

@[simp]
theorem fstCharacter_apply (x : Unitization 𝕜 A) :
    fstCharacter 𝕜 A x = x.fst := by
  simp [fstCharacter]

theorem fstCharacter_inl (r : 𝕜) :
    fstCharacter 𝕜 A (Unitization.inl r) = r := by
  simp

theorem fstCharacter_inr (a : A) :
    fstCharacter 𝕜 A (a : Unitization 𝕜 A) = 0 := by
  simp

@[simp]
theorem toAlgHom_fstCharacter :
    toAlgHom (fstCharacter 𝕜 A) = Unitization.fstHom 𝕜 A :=
  equivAlgHom.apply_symm_apply _

@[simp]
theorem mem_ker_fstCharacter {x : Unitization 𝕜 A} :
    x ∈ TwoSidedIdeal.ker (fstCharacter 𝕜 A) ↔ x.fst = 0 := by
  simp [TwoSidedIdeal.mem_ker]

/-- Lift a nonunital character `φ : characterSpace 𝕜 A` to the unital character
`(r, a) ↦ r + φ a` on `Unitization 𝕜 A`. -/
noncomputable def liftUnitization (φ : characterSpace 𝕜 A) :
    characterSpace 𝕜 (Unitization 𝕜 A) :=
  equivAlgHom.symm (Unitization.lift (toNonUnitalAlgHom φ))

@[simp]
theorem liftUnitization_apply (φ : characterSpace 𝕜 A) (x : Unitization 𝕜 A) :
    liftUnitization φ x = x.fst + φ x.snd := by
  simp [liftUnitization]

theorem liftUnitization_inl (φ : characterSpace 𝕜 A) (r : 𝕜) :
    liftUnitization φ (Unitization.inl r) = r := by
  simp

theorem liftUnitization_inr (φ : characterSpace 𝕜 A) (a : A) :
    liftUnitization φ (a : Unitization 𝕜 A) = φ a := by
  simp

theorem liftUnitization_injective :
    Function.Injective (liftUnitization (𝕜 := 𝕜) (A := A)) := by
  intro φ ψ h
  ext a
  simpa using congrArg (fun χ : characterSpace 𝕜 (Unitization 𝕜 A) => χ (a : Unitization 𝕜 A)) h

@[simp]
theorem liftUnitization_ne_fstCharacter (φ : characterSpace 𝕜 A) :
    liftUnitization φ ≠ fstCharacter 𝕜 A := by
  intro h
  refine φ.prop.1 (DFunLike.ext _ _ fun a => ?_)
  have ha : φ a = 0 := by
    simpa using congrArg (fun χ : characterSpace 𝕜 (Unitization 𝕜 A) => χ (a : Unitization 𝕜 A)) h
  exact ha

/-- Restrict a character `χ ≠ fstCharacter 𝕜 A` of `Unitization 𝕜 A` to a character of `A`. -/
noncomputable def restrictComplFstCharacter
    (χ : ({fstCharacter 𝕜 A}ᶜ : Set (characterSpace 𝕜 (Unitization 𝕜 A)))) :
    characterSpace 𝕜 A :=
  equivNonUnitalAlgHom.symm
    ⟨Unitization.lift.symm (toAlgHom χ.1), fun h => by
      refine χ.2 (ext fun x => ?_)
      induction x with
      | inl_add_inr r a =>
        have hr : χ.1 (Unitization.inl r) = r := by
          simp [← Unitization.algebraMap_eq_inl, AlgHomClass.commutes]
        have ha : χ.1 (a : Unitization 𝕜 A) = 0 := DFunLike.congr_fun h a
        simp [hr, ha]⟩

@[simp]
theorem restrictComplFstCharacter_apply
    (χ : ({fstCharacter 𝕜 A}ᶜ : Set (characterSpace 𝕜 (Unitization 𝕜 A)))) (a : A) :
    restrictComplFstCharacter χ a = χ.1 (a : Unitization 𝕜 A) := by
  simp [restrictComplFstCharacter]
  rfl

@[simp]
theorem restrictComplFstCharacter_liftUnitization (φ : characterSpace 𝕜 A) :
    restrictComplFstCharacter ⟨liftUnitization φ, liftUnitization_ne_fstCharacter φ⟩ = φ := by
  ext a
  simp

@[simp]
theorem liftUnitization_restrictComplFstCharacter
    (χ : ({fstCharacter 𝕜 A}ᶜ : Set (characterSpace 𝕜 (Unitization 𝕜 A)))) :
    liftUnitization (restrictComplFstCharacter χ) = χ.1 := by
  ext x
  induction x with
  | inl_add_inr r a =>
    have hr : χ.1 (Unitization.inl r) = r := by
      simp [← Unitization.algebraMap_eq_inl, AlgHomClass.commutes]
    simp [hr]

/-- Every character of `Unitization 𝕜 A` is either `fstCharacter 𝕜 A` or the lift of a character of
`A`. -/
theorem eq_fstCharacter_or_exists_liftUnitization (χ : characterSpace 𝕜 (Unitization 𝕜 A)) :
    χ = fstCharacter 𝕜 A ∨ ∃ φ : characterSpace 𝕜 A, liftUnitization φ = χ := by
  by_cases hχ : χ = fstCharacter 𝕜 A
  · exact Or.inl hχ
  · exact Or.inr ⟨restrictComplFstCharacter ⟨χ, hχ⟩,
      liftUnitization_restrictComplFstCharacter ⟨χ, hχ⟩⟩

theorem exists_liftUnitization_eq {χ : characterSpace 𝕜 (Unitization 𝕜 A)} :
    (∃ φ : characterSpace 𝕜 A, liftUnitization φ = χ) ↔ χ ≠ fstCharacter 𝕜 A :=
  ⟨fun ⟨φ, hφ⟩ => hφ ▸ liftUnitization_ne_fstCharacter φ,
    fun hχ => ⟨restrictComplFstCharacter ⟨χ, hχ⟩,
      liftUnitization_restrictComplFstCharacter ⟨χ, hχ⟩⟩⟩

@[simp]
theorem range_liftUnitization :
    Set.range (liftUnitization (𝕜 := 𝕜) (A := A)) = {fstCharacter 𝕜 A}ᶜ :=
  Set.ext fun _ => Set.mem_range.trans exists_liftUnitization_eq

@[fun_prop]
theorem continuous_liftUnitization :
    Continuous (liftUnitization (𝕜 := 𝕜) (A := A)) := by
  refine Continuous.subtype_mk (continuous_of_continuous_eval fun x => ?_) _
  exact continuous_const.add ((eval_continuous (𝕜 := 𝕜) x.snd).comp continuous_subtype_val)

@[fun_prop]
theorem continuous_restrictComplFstCharacter :
    Continuous (restrictComplFstCharacter (𝕜 := 𝕜) (A := A)) := by
  refine Continuous.subtype_mk (continuous_of_continuous_eval fun a => ?_) _
  exact (eval_continuous (𝕜 := 𝕜) (a : Unitization 𝕜 A)).comp
    (continuous_subtype_val.comp continuous_subtype_val)

variable (𝕜 A) in
/-- Lifting nonunital characters identifies `characterSpace 𝕜 A` homeomorphically with the
complement of `fstCharacter 𝕜 A` inside `characterSpace 𝕜 (Unitization 𝕜 A)`. -/
noncomputable def homeoComplFstCharacter :
    characterSpace 𝕜 A ≃ₜ ({fstCharacter 𝕜 A}ᶜ : Set (characterSpace 𝕜 (Unitization 𝕜 A))) where
  toFun φ := ⟨liftUnitization φ, liftUnitization_ne_fstCharacter φ⟩
  invFun := restrictComplFstCharacter
  left_inv := restrictComplFstCharacter_liftUnitization
  right_inv χ := Subtype.ext (liftUnitization_restrictComplFstCharacter χ)
  continuous_toFun := Continuous.subtype_mk continuous_liftUnitization _
  continuous_invFun := continuous_restrictComplFstCharacter

@[simp]
theorem homeoComplFstCharacter_apply_coe (φ : characterSpace 𝕜 A) :
    (homeoComplFstCharacter 𝕜 A φ : characterSpace 𝕜 (Unitization 𝕜 A)) = liftUnitization φ := (rfl)

@[simp]
theorem homeoComplFstCharacter_symm_apply
    (χ : ({fstCharacter 𝕜 A}ᶜ : Set (characterSpace 𝕜 (Unitization 𝕜 A)))) :
    (homeoComplFstCharacter 𝕜 A).symm χ = restrictComplFstCharacter χ := (rfl)

theorem isOpenEmbedding_liftUnitization :
    IsOpenEmbedding (liftUnitization (𝕜 := 𝕜) (A := A)) := by
  have hcomp : (liftUnitization : characterSpace 𝕜 A → characterSpace 𝕜 (Unitization 𝕜 A)) =
      Subtype.val ∘ homeoComplFstCharacter 𝕜 A := rfl
  rw [hcomp]
  exact isOpen_compl_singleton.isOpenEmbedding_subtypeVal.comp
    (homeoComplFstCharacter 𝕜 A).isOpenEmbedding

/-- When `A` is a subsingleton, `fstCharacter 𝕜 A` is the unique character of `Unitization 𝕜 A`. -/
noncomputable instance instUniqueCharacterSpaceUnitization [Subsingleton A] :
    Unique (characterSpace 𝕜 (Unitization 𝕜 A)) where
  default := fstCharacter 𝕜 A
  uniq χ := (eq_fstCharacter_or_exists_liftUnitization χ).resolve_right
    fun ⟨φ, _⟩ => IsEmpty.false φ

/-- When `A` is a subsingleton, the punctured character space `{fstCharacter 𝕜 A}ᶜ` is empty. -/
instance instIsEmptyComplFstCharacter [Subsingleton A] :
    IsEmpty ({fstCharacter 𝕜 A}ᶜ : Set (characterSpace 𝕜 (Unitization 𝕜 A))) :=
  (homeoComplFstCharacter 𝕜 A).symm.isEmpty

/-- If `A` has a left multiplicative identity `e`, then `{fstCharacter 𝕜 A}` is clopen in
`characterSpace 𝕜 (Unitization 𝕜 A)`. -/
theorem isClopen_singleton_fstCharacter_of_forall_mul_eq {e : A} (he : ∀ a : A, e * a = a) :
    IsClopen ({fstCharacter 𝕜 A} : Set (characterSpace 𝕜 (Unitization 𝕜 A))) := by
  refine ⟨isClosed_singleton, ?_⟩
  have hset : ({fstCharacter 𝕜 A} : Set (characterSpace 𝕜 (Unitization 𝕜 A))) =
      gelfandTransform 𝕜 (Unitization 𝕜 A) (e : Unitization 𝕜 A) ⁻¹' ({1}ᶜ : Set 𝕜) := by
    ext χ
    rcases eq_fstCharacter_or_exists_liftUnitization χ with rfl | ⟨φ, rfl⟩
    · simp
    · simp [liftUnitization_ne_fstCharacter φ, apply_eq_one_of_forall_mul_eq φ he]
  rw [hset]
  exact isOpen_compl_singleton.preimage (map_continuous _)

/-- If `A` has a left multiplicative identity `e`, then `fstCharacter 𝕜 A` is an isolated point of
`characterSpace 𝕜 (Unitization 𝕜 A)`. -/
theorem isOpen_singleton_fstCharacter_of_forall_mul_eq {e : A} (he : ∀ a : A, e * a = a) :
    IsOpen ({fstCharacter 𝕜 A} : Set (characterSpace 𝕜 (Unitization 𝕜 A))) :=
  (isClopen_singleton_fstCharacter_of_forall_mul_eq he).2

section ProperUnitization

variable [ProperSpace 𝕜]

variable (𝕜 A) in
/-- Over a proper scalar field, the character space of `Unitization 𝕜 A` is homeomorphic to the
one-point compactification `OnePoint (characterSpace 𝕜 A)`, sending `∞` to `fstCharacter 𝕜 A` and
`φ : characterSpace 𝕜 A` to `liftUnitization φ`. -/
noncomputable def onePointHomeoUnitization :
    OnePoint (characterSpace 𝕜 A) ≃ₜ characterSpace 𝕜 (Unitization 𝕜 A) :=
  OnePoint.equivOfIsEmbeddingOfRangeEq (fstCharacter 𝕜 A) liftUnitization
    isOpenEmbedding_liftUnitization.isEmbedding range_liftUnitization

@[simp]
theorem onePointHomeoUnitization_apply_infty :
    onePointHomeoUnitization 𝕜 A ∞ = fstCharacter 𝕜 A :=
  OnePoint.equivOfIsEmbeddingOfRangeEq_apply_infty _ _ _ _

@[simp]
theorem onePointHomeoUnitization_apply_coe (φ : characterSpace 𝕜 A) :
    onePointHomeoUnitization 𝕜 A φ = liftUnitization φ :=
  OnePoint.equivOfIsEmbeddingOfRangeEq_apply_coe _ _ _ _ φ

/-- Reindexing `nonUnitalGelfandTransform 𝕜 A a` along `homeoComplFstCharacter 𝕜 A` and extending by
`0` at `fstCharacter 𝕜 A` recovers `gelfandTransform 𝕜 (Unitization 𝕜 A) (a : Unitization 𝕜 A)`. -/
theorem extendComplSingleton_congrLeft_nonUnitalGelfandTransform (a : A) :
    ((nonUnitalGelfandTransform 𝕜 A a).comp
      (homeoComplFstCharacter 𝕜 A).symm.toCocompactMap).extendComplSingleton =
      gelfandTransform 𝕜 (Unitization 𝕜 A) (a : Unitization 𝕜 A) := by
  ext χ
  rcases eq_fstCharacter_or_exists_liftUnitization χ with rfl | ⟨φ, rfl⟩
  · simp
  · rw [ZeroAtInftyContinuousMap.extendComplSingleton_apply_of_ne _
      (liftUnitization_ne_fstCharacter φ)]
    have hsymm :
        (homeoComplFstCharacter 𝕜 A).symm ⟨liftUnitization φ, liftUnitization_ne_fstCharacter φ⟩ =
          φ :=
      restrictComplFstCharacter_liftUnitization φ
    simp [hsymm]

end ProperUnitization

end Unitization

end CharacterSpace

end WeakDual
