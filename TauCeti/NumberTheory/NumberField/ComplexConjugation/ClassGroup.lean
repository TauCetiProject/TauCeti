/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CMField
public import TauCeti.NumberTheory.Padics.PadicIntegers
public import TauCeti.RingTheory.ClassGroup.Galois
public import TauCeti.RingTheory.Idempotents.SquareRootOne
import TauCeti.NumberTheory.ClassGroup.Equiv
import TauCeti.NumberTheory.NumberField.RingOfIntegers.Transport

/-!
# Complex conjugation on ideal class groups of CM number fields

Let `K` be a CM number field (`NumberField.IsCMField K`), with maximal real subfield
`K⁺ = NumberField.maximalRealSubfield K` and canonical complex conjugation
`c = NumberField.IsCMField.complexConj K : K ≃ₐ[K⁺] K`. Pushing ideal classes forward along the
restriction of `c` to `𝓞 K` defines an involution `TauCeti.cmClassComplexConjMulAut K` on
`ClassGroup (𝓞 K)` and, after base change along any commutative ring `R`, an `R`-linear involution
`TauCeti.cmClassComplexConj R K` on `R ⊗[ℤ] Additive (ClassGroup (𝓞 K))`.

Since `K / K⁺` is quadratic with Galois group `{1, c}`, the relative norm `N` and ideal-class
extension `j` between `K⁺` and `K` satisfy
* `N ∘ j = 2 • id` (`TauCeti.cmClassRelNorm_comp_extended`),
* `j ∘ N = id + c` (`TauCeti.cmClassExtended_comp_relNorm`), and
* `c ∘ j = j` and `N ∘ c = N`.

When `2` is invertible in `R` (in particular for `R = ℤ_[p]` with `p` an odd prime), the
complementary idempotents `½ (1 ± c)` split `R ⊗[ℤ] Additive (ClassGroup (𝓞 K))` into its plus
and minus eigenspaces `A⁺ = ker (c - 1)` and `A⁻ = ker (c + 1)`, the extension map `j` induces an
`R`-linear isomorphism `R ⊗[ℤ] Additive (ClassGroup (𝓞 K⁺)) ≃ₗ[R] A⁺`
(`TauCeti.cmRealClassEquivPlus`), and `A⁻ = ker N` (`TauCeti.cmClassMinusSubmodule_eq_ker_relNorm`).

Without inverting `2` (in particular for `R = ℤ_[2]`), the three minus-type modules
* the norm kernel `ker N` (`TauCeti.cmNormKernel R K`),
* the anti-invariants `ker (c + 1)` (`TauCeti.cmClassMinusSubmodule R K`), and
* the quotient `A / (1 + c) A` (`TauCeti.cmMinusQuotient R K`)

remain distinct in general, linked by canonical `R`-linear comparison maps
`ker N ↪ ker (c + 1) → A / (1 + c) A` whose kernels and cokernels are annihilated by `2`. In any
tower `K ⊆ L` of CM number fields, complex conjugation commutes with `algebraMap K L`, so the
relative norm `N_{L/K}` commutes with `c`, preserves all three modules, and is compatible with the
comparison maps.

## Main definitions

* `TauCeti.cmClassComplexConjMulAut`: the complex-conjugation involution on `ClassGroup (𝓞 K)`.
* `TauCeti.cmClassComplexConj`: the `R`-linear complex-conjugation involution on
  `R ⊗[ℤ] Additive (ClassGroup (𝓞 K))`.
* `TauCeti.cmClassPlusSubmodule`, `TauCeti.cmClassMinusSubmodule`: the `+1` and `-1` eigenspaces
  of complex conjugation.
* `TauCeti.cmClassPlusProjector`, `TauCeti.cmClassMinusProjector`: the idempotents `½ (1 ± c)` when
  `2` is invertible in `R`.
* `TauCeti.cmRealClassEquivPlus` and `TauCeti.cmRealClassEquivPlusPadic`: the isomorphism
  `A_R(K⁺) ≃ₗ[R] A_R(K)⁺` when `2` is invertible, and its `ℤ_[p]` specialization for odd `p`.
* `TauCeti.cmNormKernel`, `TauCeti.cmMinusQuotient`: the norm kernel `ker N` and the quotient
  `A_R(K) / (1 + c) A_R(K)`.
* `TauCeti.cmNormKernelToMinus`, `TauCeti.cmMinusToMinusQuotient`: the canonical comparison maps
  `ker N ↪ ker (c + 1) → A / (1 + c) A`.
* `TauCeti.cmMinusQuotientRelNormMap`: the relative norm induced on `A_R(_) / (1 + c) A_R(_)` in a
  tower of CM fields.

## Main results

* `TauCeti.cmClassRelNorm_comp_extended` and `TauCeti.cmClassExtended_comp_relNorm`: `N ∘ j = 2`
  and `j ∘ N = 1 + c`.
* `TauCeti.isCompl_cmClassPlus_cmClassMinus`, `TauCeti.cmClassMinusSubmodule_eq_ker_relNorm`,
  `TauCeti.isCompl_cmClassPlus_cmClassMinus_padic`, and
  `TauCeti.cmClassMinusSubmodule_eq_ker_relNorm_padic`: the plus/minus splitting and `A⁻ = ker N`
  when `2` is invertible (in particular over `ℤ_[p]` for odd `p`).
* `TauCeti.two_smul_mem_cmNormKernel_of_mem_minus`,
  `TauCeti.two_smul_eq_zero_of_mem_ker_cmMinusToMinusQuotient`, and
  `TauCeti.two_smul_mem_range_cmMinusToMinusQuotient`: the 2-torsion bounds on the comparison
  defects.
* `TauCeti.relNormBaseChange_comp_cmClassComplexConj` and
  `TauCeti.relNormBaseChange_mem_cmNormKernel`: compatibility of complex conjugation and the
  minus-type boundary trio with relative norms in CM towers.
-/

public section

open NumberField NumberField.IsCMField
open scoped NumberField TensorProduct

namespace TauCeti

section MulAut

variable (K : Type*) [Field K] [NumberField K] [IsCMField K]

/-- **Complex conjugation on the class group of a CM field**: pushes ideal classes forward along
`IsCMField.complexConj K`. -/
noncomputable def cmClassComplexConjMulAut : MulAut (ClassGroup (𝓞 K)) :=
  ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv (complexConj K).toRingEquiv)

theorem cmClassComplexConjMulAut_apply (c : ClassGroup (𝓞 K)) :
    cmClassComplexConjMulAut K c =
      ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv (complexConj K).toRingEquiv) c := by
  rfl

/-- Complex conjugation on `ClassGroup (𝓞 K)` is an involution. -/
@[simp]
theorem cmClassComplexConjMulAut_involutive (c : ClassGroup (𝓞 K)) :
    cmClassComplexConjMulAut K (cmClassComplexConjMulAut K c) = c := by
  have hsq : (complexConj K).toRingEquiv.trans (complexConj K).toRingEquiv = RingEquiv.refl K :=
    RingEquiv.ext fun x ↦ complexConj_apply_apply K x
  change ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv (complexConj K).toRingEquiv)
      (ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv (complexConj K).toRingEquiv) c) = c
  rw [← MulEquiv.trans_apply, ← ClassGroup.mulEquiv_trans, ← RingOfIntegers.mapRingEquiv_trans,
    hsq, RingOfIntegers.mapRingEquiv_refl, ClassGroup.mulEquiv_refl, MulEquiv.refl_apply]

end MulAut

section Basic

variable (R : Type*) [CommRing R] (K : Type*) [Field K] [NumberField K] [IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- **Complex conjugation on the base-changed class module** of a CM field `K`: the `R`-linear
involution on `R ⊗[ℤ] Additive (ClassGroup (𝓞 K))` induced by `IsCMField.complexConj K`. -/
noncomputable def cmClassComplexConj :
    Module.End R (R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :=
  ClassGroup.mulEquivBaseChange R (RingOfIntegers.mapRingEquiv (complexConj K).toRingEquiv)

@[simp]
theorem cmClassComplexConj_tmul (r : R) (c : ClassGroup (𝓞 K)) :
    cmClassComplexConj R K (r ⊗ₜ[ℤ] Additive.ofMul c) =
      r ⊗ₜ[ℤ] Additive.ofMul (cmClassComplexConjMulAut K c) :=
  ClassGroup.mulEquivBaseChange_tmul R _ r c

/-- Complex conjugation on `R ⊗[ℤ] Additive (ClassGroup (𝓞 K))` squares to the identity. -/
@[simp]
theorem cmClassComplexConj_comp_self :
    (cmClassComplexConj R K).comp (cmClassComplexConj R K) = LinearMap.id := by
  ext c
  obtain ⟨c, rfl⟩ := Additive.ofMul.surjective c
  simp

/-- Multiplicative form of `TauCeti.cmClassComplexConj_comp_self` in `Module.End R _`. -/
@[simp]
theorem cmClassComplexConj_mul_self :
    cmClassComplexConj R K * cmClassComplexConj R K = 1 :=
  cmClassComplexConj_comp_self R K

/-- Applying complex conjugation twice fixes every vector. -/
@[simp]
theorem cmClassComplexConj_apply_apply (x : R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :
    cmClassComplexConj R K (cmClassComplexConj R K x) = x :=
  LinearMap.congr_fun (cmClassComplexConj_comp_self R K) x

/-- Complex conjugation fixes the image of ideal-class extension from `K⁺`. -/
@[simp]
theorem cmClassComplexConj_comp_extendedBaseChange :
    (cmClassComplexConj R K).comp (ClassGroup.extendedBaseChange R (𝓞 K⁺) (𝓞 K)) =
      ClassGroup.extendedBaseChange R (𝓞 K⁺) (𝓞 K) := by
  have h := ClassGroup.mulEquivBaseChange_comp_extendedBaseChange R
    (RingEquiv.refl (𝓞 K⁺)) (RingOfIntegers.mapRingEquiv (complexConj K).toRingEquiv)
    fun r ↦ RingOfIntegers.ext (by
      change complexConj K (algebraMap K⁺ K r) = algebraMap K⁺ K r
      exact (complexConj K).commutes r)
  have hrefl : ClassGroup.mulEquivBaseChange R (RingEquiv.refl (𝓞 K⁺)) = LinearMap.id := by
    ext c
    obtain ⟨c, rfl⟩ := Additive.ofMul.surjective c
    simp [ClassGroup.mulEquiv_refl]
  simpa [cmClassComplexConj, hrefl] using h

/-- Relative norm to `K⁺` is invariant under complex conjugation. -/
@[simp]
theorem relNormBaseChange_comp_cmClassComplexConj_self :
    (ClassGroup.relNormBaseChange R (𝓞 K⁺) (𝓞 K)).comp (cmClassComplexConj R K) =
      ClassGroup.relNormBaseChange R (𝓞 K⁺) (𝓞 K) := by
  have h := ClassGroup.mulEquivBaseChange_comp_relNormBaseChange R
    (RingEquiv.refl (𝓞 K⁺)) (RingOfIntegers.mapRingEquiv (complexConj K).toRingEquiv)
    fun r ↦ RingOfIntegers.ext (by
      change complexConj K (algebraMap K⁺ K r) = algebraMap K⁺ K r
      exact (complexConj K).commutes r)
  have hrefl : ClassGroup.mulEquivBaseChange R (RingEquiv.refl (𝓞 K⁺)) = LinearMap.id := by
    ext c
    obtain ⟨c, rfl⟩ := Additive.ofMul.surjective c
    simp [ClassGroup.mulEquiv_refl]
  simpa [cmClassComplexConj, hrefl] using h.symm

/-- **Extend then norm for `K / K⁺` is multiplication by `2`.** -/
theorem cmClassRelNorm_comp_extended :
    (ClassGroup.relNormBaseChange R (𝓞 K⁺) (𝓞 K)).comp
        (ClassGroup.extendedBaseChange R (𝓞 K⁺) (𝓞 K)) =
      (2 : R) • LinearMap.id := by
  rw [ClassGroup.relNormBaseChange_comp_extendedBaseChange,
    ← IsFractionRing.finrank_eq (𝓞 K⁺) K⁺ (𝓞 K) K,
    Algebra.IsQuadraticExtension.finrank_eq_two K⁺ K]
  simp

open scoped Classical in
/-- The Galois group `Gal(K/K⁺)` consists of `1` and `complexConj K`. -/
private theorem gal_cm_eq_pair :
    (Finset.univ : Finset (K ≃ₐ[K⁺] K)) = {(1 : K ≃ₐ[K⁺] K), complexConj K} := by
  have hcard : Fintype.card (K ≃ₐ[K⁺] K) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank K⁺ K,
      Algebra.IsQuadraticExtension.finrank_eq_two K⁺ K]
  have hsub : ({(1 : K ≃ₐ[K⁺] K), complexConj K} : Finset (K ≃ₐ[K⁺] K)) ⊆ Finset.univ :=
    Finset.subset_univ _
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [Finset.card_pair (complexConj_ne_one K).symm, Finset.card_univ, hcard]

/-- **Norm then extend for `K / K⁺` is `1 + c`.** -/
theorem cmClassExtended_comp_relNorm :
    (ClassGroup.extendedBaseChange R (𝓞 K⁺) (𝓞 K)).comp
        (ClassGroup.relNormBaseChange R (𝓞 K⁺) (𝓞 K)) =
      LinearMap.id + cmClassComplexConj R K := by
  classical
  ext c
  obtain ⟨c, rfl⟩ := Additive.ofMul.surjective c
  have hprod := ClassGroup.extendedHom_relNorm_ringOfIntegers K⁺ K c
  rw [gal_cm_eq_pair K, Finset.prod_pair (complexConj_ne_one K).symm] at hprod
  have h1 : ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv (1 : K ≃ₐ[K⁺] K).toRingEquiv) c =
      c := by
    change ClassGroup.mulEquiv (RingOfIntegers.mapRingEquiv (RingEquiv.refl K)) c = c
    rw [RingOfIntegers.mapRingEquiv_refl, ClassGroup.mulEquiv_refl, MulEquiv.refl_apply]
  rw [h1] at hprod
  simp [hprod, cmClassComplexConjMulAut, TensorProduct.tmul_add]

/-- The **plus submodule** `A⁺ = ker (c - 1)` of `R ⊗[ℤ] Additive (ClassGroup (𝓞 K))`. -/
noncomputable def cmClassPlusSubmodule :
    Submodule R (R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :=
  LinearMap.ker (cmClassComplexConj R K - LinearMap.id)

/-- The **minus submodule** (anti-invariants) `A⁻ = ker (c + 1)` of
`R ⊗[ℤ] Additive (ClassGroup (𝓞 K))`. -/
noncomputable def cmClassMinusSubmodule :
    Submodule R (R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :=
  LinearMap.ker (cmClassComplexConj R K + LinearMap.id)

section MemLemmas

variable {R K}

@[simp]
theorem mem_cmClassPlusSubmodule_iff {x : R ⊗[ℤ] Additive (ClassGroup (𝓞 K))} :
    x ∈ cmClassPlusSubmodule R K ↔ cmClassComplexConj R K x = x := by
  simp [cmClassPlusSubmodule, sub_eq_zero]

@[simp]
theorem mem_cmClassMinusSubmodule_iff {x : R ⊗[ℤ] Additive (ClassGroup (𝓞 K))} :
    x ∈ cmClassMinusSubmodule R K ↔ cmClassComplexConj R K x = -x := by
  simp [cmClassMinusSubmodule, add_eq_zero_iff_eq_neg]

end MemLemmas

/-- The **norm kernel** `ker (N_{K/K⁺})` inside `R ⊗[ℤ] Additive (ClassGroup (𝓞 K))`. -/
noncomputable def cmNormKernel :
    Submodule R (R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :=
  LinearMap.ker (ClassGroup.relNormBaseChange R (𝓞 K⁺) (𝓞 K))

@[simp]
theorem mem_cmNormKernel_iff {R K : Type*} [CommRing R] [Field K] [NumberField K]
    {x : R ⊗[ℤ] Additive (ClassGroup (𝓞 K))} :
    x ∈ cmNormKernel R K ↔
      ClassGroup.relNormBaseChange R (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) x = 0 :=
  Iff.rfl

/-- The **minus quotient** `A / (1 + c) A` of `R ⊗[ℤ] Additive (ClassGroup (𝓞 K))`. -/
abbrev cmMinusQuotient : Type _ :=
  (R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) ⧸
    LinearMap.range (LinearMap.id + cmClassComplexConj R K)

end Basic

section InvertibleTwo

variable (R : Type*) [CommRing R] [Invertible (2 : R)]
  (K : Type*) [Field K] [NumberField K] [IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- **The plus projector** `½ (1 + c)` on `R ⊗[ℤ] Additive (ClassGroup (𝓞 K))` when `2` is
invertible in `R`. -/
noncomputable def cmClassPlusProjector :
    Module.End R (R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :=
  halfOneAdd R (cmClassComplexConj R K)

theorem cmClassPlusProjector_eq :
    cmClassPlusProjector R K = halfOneAdd R (cmClassComplexConj R K) := by
  rfl

/-- **The minus projector** `½ (1 - c)` on `R ⊗[ℤ] Additive (ClassGroup (𝓞 K))` when `2` is
invertible in `R`. -/
noncomputable def cmClassMinusProjector :
    Module.End R (R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) :=
  halfOneAdd R (-cmClassComplexConj R K)

theorem cmClassMinusProjector_eq :
    cmClassMinusProjector R K = halfOneAdd R (-cmClassComplexConj R K) := by
  rfl

/-- The plus projector fixes every element of the plus submodule `A⁺`. -/
theorem cmClassPlusProjector_apply_of_mem {x : R ⊗[ℤ] Additive (ClassGroup (𝓞 K))}
    (hx : x ∈ cmClassPlusSubmodule R K) :
    cmClassPlusProjector R K x = x := by
  rw [cmClassPlusProjector_eq, halfOneAdd_def, LinearMap.smul_apply, LinearMap.add_apply,
    one_apply_eq_self, mem_cmClassPlusSubmodule_iff.mp hx, ← two_smul R, invOf_smul_smul]

/-- The minus projector fixes every element of the minus submodule `A⁻`. -/
theorem cmClassMinusProjector_apply_of_mem {x : R ⊗[ℤ] Additive (ClassGroup (𝓞 K))}
    (hx : x ∈ cmClassMinusSubmodule R K) :
    cmClassMinusProjector R K x = x := by
  rw [cmClassMinusProjector_eq, halfOneAdd_def, LinearMap.smul_apply, LinearMap.add_apply,
    one_apply_eq_self, LinearMap.neg_apply, mem_cmClassMinusSubmodule_iff.mp hx, neg_neg,
    ← two_smul R, invOf_smul_smul]

theorem range_cmClassPlusProjector :
    LinearMap.range (cmClassPlusProjector R K) = cmClassPlusSubmodule R K := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [mem_cmClassPlusSubmodule_iff]
    exact LinearMap.congr_fun (mul_halfOneAdd R (cmClassComplexConj_mul_self R K)) y
  · intro hx
    exact ⟨x, cmClassPlusProjector_apply_of_mem R K hx⟩

theorem range_cmClassMinusProjector :
    LinearMap.range (cmClassMinusProjector R K) = cmClassMinusSubmodule R K := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [mem_cmClassMinusSubmodule_iff]
    exact LinearMap.congr_fun (mul_halfOneAdd_neg R (cmClassComplexConj_mul_self R K)) y
  · intro hx
    exact ⟨x, cmClassMinusProjector_apply_of_mem R K hx⟩

/-- **Plus/minus direct-sum splitting** when `2` is invertible in `R`:
`A = A⁺ ⊕ A⁻`. -/
theorem isCompl_cmClassPlus_cmClassMinus :
    IsCompl (cmClassPlusSubmodule R K) (cmClassMinusSubmodule R K) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hxPlus hxMinus
    have h2 : (2 : R) • x = 0 := by
      rw [two_smul]
      calc x + x = cmClassComplexConj R K x + x := by rw [mem_cmClassPlusSubmodule_iff.mp hxPlus]
        _ = -x + x := by rw [mem_cmClassMinusSubmodule_iff.mp hxMinus]
        _ = 0 := neg_add_cancel x
    simpa [invOf_smul_smul] using congrArg ((⅟2 : R) • ·) h2
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hsplit : cmClassPlusProjector R K x + cmClassMinusProjector R K x = x :=
      LinearMap.congr_fun (halfOneAdd_add_halfOneAdd_neg R (cmClassComplexConj R K)) x
    rw [← hsplit]
    exact Submodule.add_mem_sup
      ((range_cmClassPlusProjector R K).le ⟨x, rfl⟩)
      ((range_cmClassMinusProjector R K).le ⟨x, rfl⟩)

/-- **Real-class / plus-part equivalence** when `2` is invertible in `R`: ideal-class extension
identifies `R ⊗[ℤ] Additive (ClassGroup (𝓞 K⁺))` with `A⁺`, with inverse `½ N_{K/K⁺}`. -/
noncomputable def cmRealClassEquivPlus :
    (R ⊗[ℤ] Additive (ClassGroup (𝓞 K⁺))) ≃ₗ[R] cmClassPlusSubmodule R K :=
  LinearEquiv.ofLinearMap
    ((ClassGroup.extendedBaseChange R (𝓞 K⁺) (𝓞 K)).codRestrict (cmClassPlusSubmodule R K)
      fun x ↦ mem_cmClassPlusSubmodule_iff.mpr <|
        LinearMap.congr_fun (cmClassComplexConj_comp_extendedBaseChange R K) x)
    ((⅟2 : R) • (ClassGroup.relNormBaseChange R (𝓞 K⁺) (𝓞 K)).comp
      (cmClassPlusSubmodule R K).subtype)
    (LinearMap.ext fun y ↦ Subtype.ext <| by
      have hcomp := LinearMap.congr_fun (cmClassExtended_comp_relNorm R K) y.1
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, Submodule.coe_subtype, map_smul,
        SetLike.val_smul, LinearMap.id_apply, LinearMap.codRestrict_apply, LinearMap.add_apply]
        at hcomp ⊢
      rw [hcomp, mem_cmClassPlusSubmodule_iff.mp y.2, ← two_smul R, invOf_smul_smul])
    (LinearMap.ext fun x ↦ by
      have hcomp := LinearMap.congr_fun (cmClassRelNorm_comp_extended R K) x
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, Submodule.coe_subtype,
        LinearMap.codRestrict_apply, LinearMap.id_apply] at hcomp ⊢
      rw [hcomp, invOf_smul_smul])

@[simp]
theorem coe_cmRealClassEquivPlus_apply (x : R ⊗[ℤ] Additive (ClassGroup (𝓞 K⁺))) :
    (cmRealClassEquivPlus R K x : R ⊗[ℤ] Additive (ClassGroup (𝓞 K))) =
      ClassGroup.extendedBaseChange R (𝓞 K⁺) (𝓞 K) x := by
  rfl

@[simp]
theorem cmRealClassEquivPlus_symm_apply (y : cmClassPlusSubmodule R K) :
    (cmRealClassEquivPlus R K).symm y =
      (⅟2 : R) • ClassGroup.relNormBaseChange R (𝓞 K⁺) (𝓞 K) y.1 := by
  rfl

/-- **Minus part equals the norm kernel** when `2` is invertible in `R`: `A⁻ = ker N_{K/K⁺}`. -/
theorem cmClassMinusSubmodule_eq_ker_relNorm :
    cmClassMinusSubmodule R K = cmNormKernel R K := by
  ext x
  rw [mem_cmClassMinusSubmodule_iff, mem_cmNormKernel_iff]
  constructor
  · intro hx
    have h2 : (2 : R) • ClassGroup.relNormBaseChange R (𝓞 K⁺) (𝓞 K) x = 0 := by
      have hnj := LinearMap.congr_fun (cmClassRelNorm_comp_extended R K)
        (ClassGroup.relNormBaseChange R (𝓞 K⁺) (𝓞 K) x)
      have hjn := LinearMap.congr_fun (cmClassExtended_comp_relNorm R K) x
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
        LinearMap.add_apply] at hnj hjn
      rw [← hnj, hjn, hx, add_neg_cancel, map_zero]
    simpa [invOf_smul_smul] using congrArg ((⅟2 : R) • ·) h2
  · intro hx
    have hjn := LinearMap.congr_fun (cmClassExtended_comp_relNorm R K) x
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply] at hjn
    rw [hx, map_zero] at hjn
    exact eq_neg_of_add_eq_zero_right hjn.symm

end InvertibleTwo

section OddPrime

/-- For an odd prime `p`, `2` is a unit in `ℤ_[p]`. -/
theorem isUnit_two_padicInt (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    IsUnit (2 : ℤ_[p]) := by
  simpa using (PadicInt.isUnit_natCast_iff (p := p) (n := 2)).mpr fun h ↦
    hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h)

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K] [IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- **Odd-prime real-class / plus-part equivalence** for any CM number field: ideal-class
extension from `K⁺` gives a `ℤ_[p]`-linear isomorphism `A_p(K⁺) ≃ₗ[ℤ_[p]] A_p(K)⁺`. -/
noncomputable def cmRealClassEquivPlusPadic (hp2 : p ≠ 2) :
    (ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K⁺))) ≃ₗ[ℤ_[p]] cmClassPlusSubmodule ℤ_[p] K :=
  let : Invertible (2 : ℤ_[p]) := (isUnit_two_padicInt p hp2).invertible
  cmRealClassEquivPlus ℤ_[p] K

@[simp]
theorem coe_cmRealClassEquivPlusPadic_apply (hp2 : p ≠ 2)
    (x : ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K⁺))) :
    (cmRealClassEquivPlusPadic p K hp2 x : ℤ_[p] ⊗[ℤ] Additive (ClassGroup (𝓞 K))) =
      ClassGroup.extendedBaseChange ℤ_[p] (𝓞 K⁺) (𝓞 K) x := by
  rfl

/-- For an odd prime `p` and any CM number field `K`, the minus submodule equals the norm kernel:
`A_p(K)⁻ = ker N_{K/K⁺}`. -/
theorem cmClassMinusSubmodule_eq_ker_relNorm_padic (hp2 : p ≠ 2) :
    cmClassMinusSubmodule ℤ_[p] K = cmNormKernel ℤ_[p] K := by
  let : Invertible (2 : ℤ_[p]) := (isUnit_two_padicInt p hp2).invertible
  exact cmClassMinusSubmodule_eq_ker_relNorm ℤ_[p] K

/-- For an odd prime `p` and any CM number field `K`, `A_p(K)` splits as `A_p(K)⁺ ⊕ A_p(K)⁻`. -/
theorem isCompl_cmClassPlus_cmClassMinus_padic (hp2 : p ≠ 2) :
    IsCompl (cmClassPlusSubmodule ℤ_[p] K) (cmClassMinusSubmodule ℤ_[p] K) := by
  let : Invertible (2 : ℤ_[p]) := (isUnit_two_padicInt p hp2).invertible
  exact isCompl_cmClassPlus_cmClassMinus ℤ_[p] K

end OddPrime

section BoundaryTrio

variable (R : Type*) [CommRing R] (K : Type*) [Field K] [NumberField K] [IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- **The norm kernel always lies inside the anti-invariants**: `ker N_{K/K⁺} ≤ ker (c + 1)`. -/
theorem cmNormKernel_le_minusSubmodule :
    cmNormKernel R K ≤ cmClassMinusSubmodule R K := by
  intro x hx
  rw [mem_cmClassMinusSubmodule_iff]
  have hjn := LinearMap.congr_fun (cmClassExtended_comp_relNorm R K) x
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply] at hjn
  rw [mem_cmNormKernel_iff.mp hx, map_zero] at hjn
  exact eq_neg_of_add_eq_zero_right hjn.symm

/-- **First comparison map** `ker N_{K/K⁺} ↪ ker (c + 1)`. -/
noncomputable def cmNormKernelToMinus :
    cmNormKernel R K →ₗ[R] cmClassMinusSubmodule R K :=
  Submodule.inclusion (cmNormKernel_le_minusSubmodule R K)

theorem cmNormKernelToMinus_injective : Function.Injective (cmNormKernelToMinus R K) :=
  Submodule.inclusion_injective (cmNormKernel_le_minusSubmodule R K)

/-- **The cokernel of `ker N_{K/K⁺} ↪ ker (c + 1)` is killed by `2`**: for every anti-invariant
`x ∈ ker (c + 1)`, `2 • x ∈ ker N_{K/K⁺}`. -/
theorem two_smul_mem_cmNormKernel_of_mem_minus {x : R ⊗[ℤ] Additive (ClassGroup (𝓞 K))}
    (hx : x ∈ cmClassMinusSubmodule R K) :
    (2 : R) • x ∈ cmNormKernel R K := by
  rw [mem_cmNormKernel_iff, map_smul]
  have hnj := LinearMap.congr_fun (cmClassRelNorm_comp_extended R K)
    (ClassGroup.relNormBaseChange R (𝓞 K⁺) (𝓞 K) x)
  have hjn := LinearMap.congr_fun (cmClassExtended_comp_relNorm R K) x
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.add_apply] at hnj hjn
  rw [← hnj, hjn, mem_cmClassMinusSubmodule_iff.mp hx, add_neg_cancel, map_zero]

/-- **Second comparison map** `ker (c + 1) → A / (1 + c) A`. -/
noncomputable def cmMinusToMinusQuotient :
    cmClassMinusSubmodule R K →ₗ[R] cmMinusQuotient R K :=
  (Submodule.mkQ _).comp (cmClassMinusSubmodule R K).subtype

/-- **The kernel of `ker (c + 1) → A / (1 + c) A` is killed by `2`.** -/
theorem two_smul_eq_zero_of_mem_ker_cmMinusToMinusQuotient
    {x : cmClassMinusSubmodule R K} (hx : x ∈ LinearMap.ker (cmMinusToMinusQuotient R K)) :
    (2 : R) • x = 0 := by
  apply Subtype.ext
  change (2 : R) • x.1 = 0
  have hmem : x.1 ∈ LinearMap.range (LinearMap.id + cmClassComplexConj R K) :=
    (Submodule.Quotient.mk_eq_zero _).mp hx
  obtain ⟨y, hy⟩ := hmem
  have hc : cmClassComplexConj R K x.1 = x.1 := by
    rw [← hy, LinearMap.add_apply, LinearMap.id_apply, map_add, cmClassComplexConj_apply_apply,
      add_comm]
  rw [two_smul]
  nth_rw 2 [← hc]
  rw [mem_cmClassMinusSubmodule_iff.mp x.2, add_neg_cancel]

/-- **The cokernel of `ker (c + 1) → A / (1 + c) A` is killed by `2`**: for every class `q` in
`A / (1 + c) A`, `2 • q` lies in the image of `ker (c + 1)`. -/
theorem two_smul_mem_range_cmMinusToMinusQuotient (q : cmMinusQuotient R K) :
    (2 : R) • q ∈ LinearMap.range (cmMinusToMinusQuotient R K) := by
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hmem : y - cmClassComplexConj R K y ∈ cmClassMinusSubmodule R K := by
    rw [mem_cmClassMinusSubmodule_iff, map_sub, cmClassComplexConj_apply_apply, neg_sub]
  refine ⟨⟨y - cmClassComplexConj R K y, hmem⟩, ?_⟩
  change Submodule.Quotient.mk (y - cmClassComplexConj R K y) =
    (2 : R) • Submodule.Quotient.mk y
  rw [← Submodule.Quotient.mk_smul, eq_comm, Submodule.Quotient.eq]
  refine ⟨y, ?_⟩
  rw [two_smul, LinearMap.add_apply, LinearMap.id_apply]
  abel

end BoundaryTrio

section Tower

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
  [IsCMField K] [IsCMField L] [Algebra K L]

/-- **Complex conjugation is functorial in extensions of CM fields**: `algebraMap K L` commutes
with `IsCMField.complexConj`. -/
theorem algebraMap_complexConj (x : K) :
    algebraMap K L (complexConj K x) = complexConj L (algebraMap K L x) := by
  let φ : L →+* ℂ := Classical.choice inferInstance
  apply φ.injective
  have hK := complexEmbedding_complexConj K (φ.comp (algebraMap K L)) x
  have hL := complexEmbedding_complexConj L φ (algebraMap K L x)
  simpa only [RingHom.comp_apply] using hK.trans hL.symm

variable (R : Type*) [CommRing R]

/-- **Relative norm commutes with complex conjugation** in a tower of CM number fields. -/
theorem relNormBaseChange_comp_cmClassComplexConj :
    (ClassGroup.relNormBaseChange R (𝓞 K) (𝓞 L)).comp (cmClassComplexConj R L) =
      (cmClassComplexConj R K).comp (ClassGroup.relNormBaseChange R (𝓞 K) (𝓞 L)) :=
  (ClassGroup.mulEquivBaseChange_comp_relNormBaseChange R
    (RingOfIntegers.mapRingEquiv (complexConj K).toRingEquiv)
    (RingOfIntegers.mapRingEquiv (complexConj L).toRingEquiv)
    fun r ↦ RingOfIntegers.ext (by
      change complexConj L (algebraMap K L r) = algebraMap K L (complexConj K r)
      exact (algebraMap_complexConj K L r).symm)).symm

/-- **Ideal-class extension commutes with complex conjugation** in a tower of CM number fields. -/
theorem cmClassComplexConj_comp_extendedBaseChange_tower :
    (cmClassComplexConj R L).comp (ClassGroup.extendedBaseChange R (𝓞 K) (𝓞 L)) =
      (ClassGroup.extendedBaseChange R (𝓞 K) (𝓞 L)).comp (cmClassComplexConj R K) :=
  ClassGroup.mulEquivBaseChange_comp_extendedBaseChange R
    (RingOfIntegers.mapRingEquiv (complexConj K).toRingEquiv)
    (RingOfIntegers.mapRingEquiv (complexConj L).toRingEquiv)
    fun r ↦ RingOfIntegers.ext (by
      change complexConj L (algebraMap K L r) = algebraMap K L (complexConj K r)
      exact (algebraMap_complexConj K L r).symm)

/-- Relative norm carries `A⁺(L)` into `A⁺(K)` in a CM tower. -/
theorem relNormBaseChange_mem_cmClassPlusSubmodule {x : R ⊗[ℤ] Additive (ClassGroup (𝓞 L))}
    (hx : x ∈ cmClassPlusSubmodule R L) :
    ClassGroup.relNormBaseChange R (𝓞 K) (𝓞 L) x ∈ cmClassPlusSubmodule R K := by
  rw [mem_cmClassPlusSubmodule_iff,
    ← LinearMap.comp_apply, ← relNormBaseChange_comp_cmClassComplexConj K L R,
    LinearMap.comp_apply, mem_cmClassPlusSubmodule_iff.mp hx]

/-- Relative norm carries anti-invariants `ker (c + 1)` at `L` into those at `K` in a CM tower. -/
theorem relNormBaseChange_mem_cmClassMinusSubmodule {x : R ⊗[ℤ] Additive (ClassGroup (𝓞 L))}
    (hx : x ∈ cmClassMinusSubmodule R L) :
    ClassGroup.relNormBaseChange R (𝓞 K) (𝓞 L) x ∈ cmClassMinusSubmodule R K := by
  rw [mem_cmClassMinusSubmodule_iff,
    ← LinearMap.comp_apply, ← relNormBaseChange_comp_cmClassComplexConj K L R,
    LinearMap.comp_apply, mem_cmClassMinusSubmodule_iff.mp hx, map_neg]

omit [IsCMField K] [IsCMField L] in
/-- Relative norm carries the norm kernel `ker N_{L/L⁺}` into `ker N_{K/K⁺}` in a tower of number
fields. -/
theorem relNormBaseChange_mem_cmNormKernel {x : R ⊗[ℤ] Additive (ClassGroup (𝓞 L))}
    (hx : x ∈ cmNormKernel R L) :
    ClassGroup.relNormBaseChange R (𝓞 K) (𝓞 L) x ∈ cmNormKernel R K := by
  let Kplus := NumberField.maximalRealSubfield K
  let Lplus := NumberField.maximalRealSubfield L
  -- `algebraMap K L` restricts to a ring homomorphism `K⁺ →+* L⁺`, hence `𝓞 K⁺ →+* 𝓞 L⁺`.
  let fReal : Kplus →+* Lplus :=
    { toFun a := ⟨algebraMap K L a.1, fun φ ↦ a.2 (φ.comp (algebraMap K L))⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' a b := Subtype.ext (map_mul _ _ _)
      map_zero' := Subtype.ext (map_zero _)
      map_add' a b := Subtype.ext (map_add _ _ _) }
  let fInt : 𝓞 Kplus →+* 𝓞 Lplus :=
    { toFun a := ⟨fReal a.1, a.2.map fReal.toIntAlgHom⟩
      map_one' := RingOfIntegers.ext (map_one fReal)
      map_mul' a b := RingOfIntegers.ext (map_mul fReal a.1 b.1)
      map_zero' := RingOfIntegers.ext (map_zero fReal)
      map_add' a b := RingOfIntegers.ext (map_add fReal a.1 b.1) }
  let : Algebra (𝓞 Kplus) (𝓞 Lplus) := fInt.toAlgebra
  let : Algebra (𝓞 Kplus) (𝓞 L) :=
    ((algebraMap (𝓞 K) (𝓞 L)).comp (algebraMap (𝓞 Kplus) (𝓞 K))).toAlgebra
  have : IsScalarTower (𝓞 Kplus) (𝓞 K) (𝓞 L) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower (𝓞 Kplus) (𝓞 Lplus) (𝓞 L) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ RingOfIntegers.ext rfl
  have : Module.Finite (𝓞 Kplus) (𝓞 Lplus) := by
    have : Module.Finite ℤ (𝓞 Lplus) := inferInstance
    exact Module.Finite.of_restrictScalars_finite ℤ (𝓞 Kplus) (𝓞 Lplus)
  have : Module.Finite (𝓞 Kplus) (𝓞 L) := by
    have : Module.Finite ℤ (𝓞 L) := inferInstance
    exact Module.Finite.of_restrictScalars_finite ℤ (𝓞 Kplus) (𝓞 L)
  have hfInt : Function.Injective fInt := fun a b h ↦
    RingOfIntegers.ext (Subtype.ext ((algebraMap K L).injective
      (congrArg (fun x : 𝓞 Lplus ↦ (x.1 : L)) h)))
  have : Module.IsTorsionFree (𝓞 Kplus) (𝓞 Lplus) :=
    Module.IsTorsionFree.of_smul_eq_zero fun r m h ↦
      (mul_eq_zero.mp h).imp (fun hr ↦ hfInt (by simpa using hr)) id
  have : Module.IsTorsionFree (𝓞 Kplus) (𝓞 L) :=
    Module.IsTorsionFree.trans (S := 𝓞 Kplus) (R := 𝓞 K) (M := 𝓞 L)
  rw [mem_cmNormKernel_iff] at hx ⊢
  have h1 := LinearMap.congr_fun
    (ClassGroup.relNormBaseChange_comp_relNormBaseChange R (𝓞 Kplus) (𝓞 K) (𝓞 L)) x
  have h2 := LinearMap.congr_fun
    (ClassGroup.relNormBaseChange_comp_relNormBaseChange R (𝓞 Kplus) (𝓞 Lplus) (𝓞 L)) x
  simp only [LinearMap.comp_apply] at h1 h2
  rw [h1, ← h2, hx, map_zero]

/-- **Relative norm induced on the minus quotient** `A / (1 + c) A` in a CM tower. -/
noncomputable def cmMinusQuotientRelNormMap :
    cmMinusQuotient R L →ₗ[R] cmMinusQuotient R K :=
  Submodule.mapQ _ _ (ClassGroup.relNormBaseChange R (𝓞 K) (𝓞 L)) <| by
    rintro _ ⟨y, rfl⟩
    refine ⟨ClassGroup.relNormBaseChange R (𝓞 K) (𝓞 L) y, ?_⟩
    have hc := LinearMap.congr_fun (relNormBaseChange_comp_cmClassComplexConj K L R) y
    simp only [LinearMap.comp_apply] at hc
    simp only [LinearMap.add_apply, LinearMap.id_apply, map_add, hc]

@[simp]
theorem cmMinusQuotientRelNormMap_mk (x : R ⊗[ℤ] Additive (ClassGroup (𝓞 L))) :
    cmMinusQuotientRelNormMap K L R (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (ClassGroup.relNormBaseChange R (𝓞 K) (𝓞 L) x) := by
  rfl

/-- **Naturality of the comparison map `ker (c + 1) → A / (1 + c) A`** under relative norm in a CM
tower. -/
theorem cmMinusQuotientRelNormMap_comp_cmMinusToMinusQuotient (x : cmClassMinusSubmodule R L) :
    cmMinusQuotientRelNormMap K L R (cmMinusToMinusQuotient R L x) =
      cmMinusToMinusQuotient R K
        ⟨ClassGroup.relNormBaseChange R (𝓞 K) (𝓞 L) x.1,
          relNormBaseChange_mem_cmClassMinusSubmodule K L R x.2⟩ := by
  rfl

end Tower

end TauCeti
