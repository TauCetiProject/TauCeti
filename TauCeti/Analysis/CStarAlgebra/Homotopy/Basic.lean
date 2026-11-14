/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Analysis.CStarAlgebra.Hom
public import TauCeti.Topology.ContinuousMap.GlueHalves
public import TauCeti.Topology.ContinuousMap.Star
import Mathlib.Topology.Order.IntermediateValue

/-!
# Path algebras, homotopies of `⋆`-homomorphisms, and contractible C⋆-algebras

For a topological `⋆`-algebra `B`, the path algebra `C(unitInterval, B)` carries pointwise
`⋆`-algebra operations (and, when `B` is a C⋆-algebra, a `NonUnitalCStarAlgebra` / `CStarAlgebra`
instance from `Mathlib.Analysis.CStarAlgebra.ContinuousMap`). A homotopy between two non-unital
`⋆`-homomorphisms `φ₀, φ₁ : A →⋆ₙₐ[𝕜] B` is a non-unital `⋆`-homomorphism
`Φ : A →⋆ₙₐ[𝕜] C(unitInterval, B)` whose endpoint evaluations at `0` and `1` agree with `φ₀` and
`φ₁` (Blackadar, *Operator Algebras*, II.5.5.10).

## Main declarations

* `NonUnitalStarAlgHom.Homotopy` and `NonUnitalStarAlgHom.Homotopic`: bundled homotopies and the
  homotopy equivalence relation on `A →⋆ₙₐ[𝕜] B`, with `refl`, `symm`, `trans`, `eval`, `compRight`,
  and `compLeft`.
* `NonUnitalStarAlgHom.Homotopy.eq_zero_of_isIdempotentElem`: in any non-unital normed `⋆`-algebra,
  a homotopy from `.id` to `0` forces every idempotent element to vanish.
* `TauCeti.StarHomotopyEquiv`: extensional homotopy equivalences between C⋆-algebras (`refl`,
  `symm`, `trans`, `ofStarAlgEquiv`).
* `TauCeti.IsContractibleCStarAlgebra`: contractibility of a C⋆-algebra (`id` homotopic to `0`),
  preserved under `StarHomotopyEquiv`, and refuted for nontrivial unital C⋆-algebras.

## References

* Bruce Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*, II.5.5.10.
-/

public section

open Set Topology unitInterval

namespace NonUnitalStarAlgHom

section Homotopy

variable {𝕜 A B : Type*} [Monoid 𝕜]
  [NonUnitalNonAssocSemiring A] [DistribMulAction 𝕜 A] [Star A]
  [TopologicalSpace B] [NonUnitalNonAssocSemiring B] [IsTopologicalSemiring B]
  [DistribMulAction 𝕜 B] [ContinuousConstSMul 𝕜 B] [Star B] [ContinuousStar B]

/-- A homotopy between two non-unital `⋆`-algebra homomorphisms `φ₀, φ₁ : A →⋆ₙₐ[𝕜] B` is a
non-unital `⋆`-algebra homomorphism `toHom : A →⋆ₙₐ[𝕜] C(unitInterval, B)` evaluating to `φ₀` at `0`
and to `φ₁` at `1`. -/
@[ext]
structure Homotopy (φ₀ φ₁ : A →⋆ₙₐ[𝕜] B) where
  /-- The underlying path-algebra `⋆`-homomorphism `A →⋆ₙₐ[𝕜] C(unitInterval, B)`. -/
  toHom : A →⋆ₙₐ[𝕜] C(I, B)
  /-- At `t = 0`, `toHom` agrees with `φ₀`. -/
  eval_zero : ∀ a, toHom a 0 = φ₀ a
  /-- At `t = 1`, `toHom` agrees with `φ₁`. -/
  eval_one : ∀ a, toHom a 1 = φ₁ a

/-- Two non-unital `⋆`-algebra homomorphisms are homotopic if there is a `Homotopy` between them. -/
abbrev Homotopic (φ₀ φ₁ : A →⋆ₙₐ[𝕜] B) : Prop :=
  Nonempty (Homotopy φ₀ φ₁)

namespace Homotopy

variable {φ₀ φ₁ φ₂ : A →⋆ₙₐ[𝕜] B}

attribute [simp] eval_zero eval_one

/-- Evaluate a homotopy of `⋆`-homomorphisms at time `t : unitInterval`. -/
def eval (H : Homotopy φ₀ φ₁) (t : I) : A →⋆ₙₐ[𝕜] B :=
  (ContinuousMap.evalNonUnitalStarAlgHom 𝕜 B t).comp H.toHom

@[simp]
theorem eval_apply (H : Homotopy φ₀ φ₁) (t : I) (a : A) :
    H.eval t a = H.toHom a t := by
  simp [eval]

@[simp]
theorem eval_at_zero (H : Homotopy φ₀ φ₁) : H.eval 0 = φ₀ := by
  ext a
  simp

@[simp]
theorem eval_at_one (H : Homotopy φ₀ φ₁) : H.eval 1 = φ₁ := by
  ext a
  simp

/-- Constant homotopy from `φ` to itself. -/
def refl (φ : A →⋆ₙₐ[𝕜] B) : Homotopy φ φ where
  toHom := (ContinuousMap.constNonUnitalStarAlgHom 𝕜 I B).comp φ
  eval_zero _ := by simp
  eval_one _ := by simp

@[simp]
theorem refl_toHom_apply (φ : A →⋆ₙₐ[𝕜] B) (a : A) (t : I) :
    (refl φ).toHom a t = φ a := by
  simp [refl]

/-- Reverse a homotopy using `unitInterval.symmHomeomorph` (`t ↦ 1 - t`). -/
def symm (H : Homotopy φ₀ φ₁) : Homotopy φ₁ φ₀ where
  toHom := (ContinuousMap.compNonUnitalStarAlgHom' 𝕜 B unitInterval.symmHomeomorph).comp H.toHom
  eval_zero a := by simp
  eval_one a := by simp

@[simp]
theorem symm_toHom_apply (H : Homotopy φ₀ φ₁) (a : A) (t : I) :
    H.symm.toHom a t = H.toHom a (σ t) := by
  simp [symm]

/-- Concatenate two homotopies `H₀ : Homotopy φ₀ φ₁` and `H₁ : Homotopy φ₁ φ₂`. -/
noncomputable def trans (H₀ : Homotopy φ₀ φ₁) (H₁ : Homotopy φ₁ φ₂) : Homotopy φ₀ φ₂ where
  toHom :=
    { toFun a := ContinuousMap.concatPath (H₀.toHom a) (H₁.toHom a)
        ((H₀.eval_one a).trans (H₁.eval_zero a).symm)
      map_smul' r a := by
        ext t
        by_cases ht : (t : ℝ) ≤ 2⁻¹
        · simp [ContinuousMap.concatPath_of_le _ _ _ ht, map_smul]
        · simp [ContinuousMap.concatPath_of_not_le _ _ _ ht, map_smul]
      map_zero' := by
        ext t
        by_cases ht : (t : ℝ) ≤ 2⁻¹
        · simp [ContinuousMap.concatPath_of_le _ _ _ ht]
        · simp [ContinuousMap.concatPath_of_not_le _ _ _ ht]
      map_add' a b := by
        ext t
        by_cases ht : (t : ℝ) ≤ 2⁻¹
        · simp [ContinuousMap.concatPath_of_le _ _ _ ht, map_add]
        · simp [ContinuousMap.concatPath_of_not_le _ _ _ ht, map_add]
      map_mul' a b := by
        ext t
        by_cases ht : (t : ℝ) ≤ 2⁻¹
        · simp [ContinuousMap.concatPath_of_le _ _ _ ht, map_mul]
        · simp [ContinuousMap.concatPath_of_not_le _ _ _ ht, map_mul]
      map_star' a := by
        ext t
        by_cases ht : (t : ℝ) ≤ 2⁻¹
        · simp [ContinuousMap.concatPath_of_le _ _ _ ht, map_star]
        · simp [ContinuousMap.concatPath_of_not_le _ _ _ ht, map_star] }
  eval_zero _ := by simp
  eval_one _ := by simp

/-- Precompose a homotopy `H : Homotopy φ₀ φ₁` on the right with `ψ : C →⋆ₙₐ[𝕜] A`. -/
def compRight {C : Type*} [NonUnitalNonAssocSemiring C] [DistribMulAction 𝕜 C] [Star C]
    (H : Homotopy φ₀ φ₁) (ψ : C →⋆ₙₐ[𝕜] A) : Homotopy (φ₀.comp ψ) (φ₁.comp ψ) where
  toHom := H.toHom.comp ψ
  eval_zero c := H.eval_zero (ψ c)
  eval_one c := H.eval_one (ψ c)

@[simp]
theorem compRight_toHom_apply {C : Type*} [NonUnitalNonAssocSemiring C] [DistribMulAction 𝕜 C]
    [Star C] (H : Homotopy φ₀ φ₁) (ψ : C →⋆ₙₐ[𝕜] A) (c : C) :
    (H.compRight ψ).toHom c = H.toHom (ψ c) :=
  (rfl)

/-- Postcompose a homotopy `H : Homotopy φ₀ φ₁` on the left with a continuous `ψ : B →⋆ₙₐ[𝕜] C`. -/
def compLeft {C : Type*} [TopologicalSpace C] [NonUnitalNonAssocSemiring C]
    [IsTopologicalSemiring C] [DistribMulAction 𝕜 C] [ContinuousConstSMul 𝕜 C]
    [Star C] [ContinuousStar C]
    (H : Homotopy φ₀ φ₁) (ψ : B →⋆ₙₐ[𝕜] C) (hψ : Continuous ψ) :
    Homotopy (ψ.comp φ₀) (ψ.comp φ₁) where
  toHom := (ContinuousMap.compNonUnitalStarAlgHom I ψ hψ).comp H.toHom
  eval_zero _ := by simp
  eval_one _ := by simp

@[simp]
theorem compLeft_toHom_apply {C : Type*} [TopologicalSpace C] [NonUnitalNonAssocSemiring C]
    [IsTopologicalSemiring C] [DistribMulAction 𝕜 C] [ContinuousConstSMul 𝕜 C]
    [Star C] [ContinuousStar C]
    (H : Homotopy φ₀ φ₁) (ψ : B →⋆ₙₐ[𝕜] C) (hψ : Continuous ψ) (a : A) (t : I) :
    (H.compLeft ψ hψ).toHom a t = ψ (H.toHom a t) := by
  simp [compLeft]

theorem homotopic (H : Homotopy φ₀ φ₁) : Homotopic φ₀ φ₁ :=
  ⟨H⟩

end Homotopy

namespace Homotopic

@[refl]
theorem refl (φ : A →⋆ₙₐ[𝕜] B) : Homotopic φ φ :=
  ⟨.refl φ⟩

@[symm]
theorem symm {φ₀ φ₁ : A →⋆ₙₐ[𝕜] B} : Homotopic φ₀ φ₁ → Homotopic φ₁ φ₀ :=
  fun ⟨H⟩ => ⟨H.symm⟩

@[trans]
theorem trans {φ₀ φ₁ φ₂ : A →⋆ₙₐ[𝕜] B} :
    Homotopic φ₀ φ₁ → Homotopic φ₁ φ₂ → Homotopic φ₀ φ₂ :=
  fun ⟨H₀⟩ ⟨H₁⟩ => ⟨H₀.trans H₁⟩

theorem equivalence : Equivalence (Homotopic (𝕜 := 𝕜) (A := A) (B := B)) :=
  ⟨refl, symm, trans⟩

theorem compRight {C : Type*} [NonUnitalNonAssocSemiring C] [DistribMulAction 𝕜 C] [Star C]
    {φ₀ φ₁ : A →⋆ₙₐ[𝕜] B} (h : Homotopic φ₀ φ₁) (ψ : C →⋆ₙₐ[𝕜] A) :
    Homotopic (φ₀.comp ψ) (φ₁.comp ψ) :=
  let ⟨H⟩ := h; ⟨H.compRight ψ⟩

theorem compLeft {C : Type*} [TopologicalSpace C] [NonUnitalNonAssocSemiring C]
    [IsTopologicalSemiring C] [DistribMulAction 𝕜 C] [ContinuousConstSMul 𝕜 C]
    [Star C] [ContinuousStar C]
    {φ₀ φ₁ : A →⋆ₙₐ[𝕜] B} (h : Homotopic φ₀ φ₁) (ψ : B →⋆ₙₐ[𝕜] C) (hψ : Continuous ψ) :
    Homotopic (ψ.comp φ₀) (ψ.comp φ₁) :=
  let ⟨H⟩ := h; ⟨H.compLeft ψ hψ⟩

theorem comp {C : Type*} [TopologicalSpace C] [NonUnitalNonAssocSemiring C]
    [IsTopologicalSemiring C] [DistribMulAction 𝕜 C] [ContinuousConstSMul 𝕜 C]
    [Star C] [ContinuousStar C]
    {ψ₀ ψ₁ : B →⋆ₙₐ[𝕜] C} {φ₀ φ₁ : A →⋆ₙₐ[𝕜] B}
    (hψ : Homotopic ψ₀ ψ₁) (hφ : Homotopic φ₀ φ₁) (hψ₀ : Continuous ψ₀) :
    Homotopic (ψ₀.comp φ₀) (ψ₁.comp φ₁) :=
  (hφ.compLeft ψ₀ hψ₀).trans (hψ.compRight φ₁)

end Homotopic

end Homotopy

section NormedIdempotent

/-- In any non-unital normed `⋆`-algebra, a homotopy from the identity homomorphism to `0` forces
every idempotent element to vanish: the norms of a continuous path of idempotents take values in
`{0} ∪ [1, ∞)` on the connected interval `[0, 1]`. -/
theorem Homotopy.eq_zero_of_isIdempotentElem {𝕜 A : Type*} [Monoid 𝕜] [NonUnitalNormedRing A]
    [DistribMulAction 𝕜 A] [ContinuousConstSMul 𝕜 A] [StarAddMonoid A] [ContinuousStar A]
    (H : Homotopy (.id 𝕜 A) (0 : A →⋆ₙₐ[𝕜] A)) {e : A} (he : IsIdempotentElem e) : e = 0 := by
  by_contra he0
  have he_pos : 0 < ‖e‖ := norm_pos_iff.mpr he0
  have he_one : 1 ≤ ‖e‖ := by
    have hmul : ‖e‖ * 1 ≤ ‖e‖ * ‖e‖ := by
      simpa only [mul_one, he.eq] using norm_mul_le e e
    exact le_of_mul_le_mul_left hmul he_pos
  let g : I → ℝ := fun t => ‖H.toHom e t‖
  have hg : Continuous g := (H.toHom e).continuous.norm
  have hg0 : g 0 = ‖e‖ := by simp [g]
  have hg1 : g 1 = 0 := by simp [g]
  obtain ⟨t, ht⟩ : (2⁻¹ : ℝ) ∈ Set.range g :=
    intermediate_value_univ (1 : I) 0 hg ⟨by rw [hg1]; positivity, by rw [hg0]; linarith⟩
  have hidem_t : H.toHom e t * H.toHom e t = H.toHom e t := by
    rw [← ContinuousMap.mul_apply, ← map_mul, he.eq]
  have hle : ‖H.toHom e t‖ ≤ ‖H.toHom e t‖ * ‖H.toHom e t‖ := by
    simpa only [hidem_t] using norm_mul_le (H.toHom e t) (H.toHom e t)
  have hgt : ‖H.toHom e t‖ = 2⁻¹ := ht
  rw [hgt] at hle
  norm_num at hle

end NormedIdempotent

end NonUnitalStarAlgHom

namespace TauCeti

open scoped CStarAlgebra

/-- A homotopy equivalence between complex C⋆-algebras consists of `⋆`-homomorphisms
`toFun : A →⋆ₙₐ[ℂ] B` and `invFun : B →⋆ₙₐ[ℂ] A` such that both composites are homotopic to the
respective identity `⋆`-homomorphisms, modeled on `ContinuousMap.HomotopyEquiv`. -/
@[ext]
structure StarHomotopyEquiv (A B : Type*) [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] where
  /-- Forward `⋆`-homomorphism `A →⋆ₙₐ[ℂ] B`. -/
  toFun : A →⋆ₙₐ[ℂ] B
  /-- Backward `⋆`-homomorphism `B →⋆ₙₐ[ℂ] A`. -/
  invFun : B →⋆ₙₐ[ℂ] A
  /-- `invFun.comp toFun` is homotopic to `.id ℂ A`. -/
  left_inv : (invFun.comp toFun).Homotopic (.id ℂ A)
  /-- `toFun.comp invFun` is homotopic to `.id ℂ B`. -/
  right_inv : (toFun.comp invFun).Homotopic (.id ℂ B)

namespace StarHomotopyEquiv

variable {A B C : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C]

/-- Identity homotopy equivalence of a C⋆-algebra. -/
def refl (A : Type*) [NonUnitalCStarAlgebra A] : StarHomotopyEquiv A A where
  toFun := .id ℂ A
  invFun := .id ℂ A
  left_inv := .refl (.id ℂ A)
  right_inv := .refl (.id ℂ A)

/-- Symmetry of C⋆-homotopy equivalence. -/
def symm (e : StarHomotopyEquiv A B) : StarHomotopyEquiv B A where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv

@[simp]
theorem symm_symm (e : StarHomotopyEquiv A B) : e.symm.symm = e :=
  (rfl)

/-- Transitivity of C⋆-homotopy equivalence. -/
def trans (e₁ : StarHomotopyEquiv A B) (e₂ : StarHomotopyEquiv B C) :
    StarHomotopyEquiv A C where
  toFun := e₂.toFun.comp e₁.toFun
  invFun := e₁.invFun.comp e₂.invFun
  left_inv :=
    have hassoc : (e₁.invFun.comp e₂.invFun).comp (e₂.toFun.comp e₁.toFun) =
        e₁.invFun.comp ((e₂.invFun.comp e₂.toFun).comp e₁.toFun) := rfl
    hassoc ▸ ((e₂.left_inv.compRight e₁.toFun).compLeft e₁.invFun
      (map_continuous e₁.invFun)).trans e₁.left_inv
  right_inv :=
    have hassoc : (e₂.toFun.comp e₁.toFun).comp (e₁.invFun.comp e₂.invFun) =
        e₂.toFun.comp ((e₁.toFun.comp e₁.invFun).comp e₂.invFun) := rfl
    hassoc ▸ ((e₁.right_inv.compRight e₂.invFun).compLeft e₂.toFun
      (map_continuous e₂.toFun)).trans e₂.right_inv

/-- Every `⋆`-algebra isomorphism `A ≃⋆ₐ[ℂ] B` induces a C⋆-homotopy equivalence. -/
def ofStarAlgEquiv (e : A ≃⋆ₐ[ℂ] B) : StarHomotopyEquiv A B where
  toFun := e.toNonUnitalStarAlgHom
  invFun := e.symm.toNonUnitalStarAlgHom
  left_inv := by
    have h : e.symm.toNonUnitalStarAlgHom.comp e.toNonUnitalStarAlgHom =
        NonUnitalStarAlgHom.id ℂ A :=
      NonUnitalStarAlgHom.ext e.symm_apply_apply
    exact h ▸ .refl (NonUnitalStarAlgHom.id ℂ A)
  right_inv := by
    have h : e.toNonUnitalStarAlgHom.comp e.symm.toNonUnitalStarAlgHom =
        NonUnitalStarAlgHom.id ℂ B :=
      NonUnitalStarAlgHom.ext e.apply_symm_apply
    exact h ▸ .refl (NonUnitalStarAlgHom.id ℂ B)

@[simp]
theorem refl_toFun (A : Type*) [NonUnitalCStarAlgebra A] : (refl A).toFun = .id ℂ A :=
  (rfl)

@[simp]
theorem refl_invFun (A : Type*) [NonUnitalCStarAlgebra A] : (refl A).invFun = .id ℂ A :=
  (rfl)

@[simp]
theorem symm_toFun (e : StarHomotopyEquiv A B) : e.symm.toFun = e.invFun :=
  (rfl)

@[simp]
theorem symm_invFun (e : StarHomotopyEquiv A B) : e.symm.invFun = e.toFun :=
  (rfl)

@[simp]
theorem trans_toFun (e₁ : StarHomotopyEquiv A B) (e₂ : StarHomotopyEquiv B C) :
    (e₁.trans e₂).toFun = e₂.toFun.comp e₁.toFun :=
  (rfl)

@[simp]
theorem trans_invFun (e₁ : StarHomotopyEquiv A B) (e₂ : StarHomotopyEquiv B C) :
    (e₁.trans e₂).invFun = e₁.invFun.comp e₂.invFun :=
  (rfl)

@[simp]
theorem ofStarAlgEquiv_toFun (e : A ≃⋆ₐ[ℂ] B) :
    (ofStarAlgEquiv e).toFun = e.toNonUnitalStarAlgHom :=
  (rfl)

@[simp]
theorem ofStarAlgEquiv_invFun (e : A ≃⋆ₐ[ℂ] B) :
    (ofStarAlgEquiv e).invFun = e.symm.toNonUnitalStarAlgHom :=
  (rfl)

end StarHomotopyEquiv

/-- A C⋆-algebra `A` is contractible if its identity `⋆`-homomorphism is homotopic to `0`. -/
abbrev IsContractibleCStarAlgebra (A : Type*) [NonUnitalCStarAlgebra A] : Prop :=
  NonUnitalStarAlgHom.Homotopic (.id ℂ A) (0 : A →⋆ₙₐ[ℂ] A)

namespace IsContractibleCStarAlgebra

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

theorem eq_zero_of_isIdempotentElem (hA : IsContractibleCStarAlgebra A) {e : A}
    (he : IsIdempotentElem e) : e = 0 :=
  let ⟨H⟩ := hA; H.eq_zero_of_isIdempotentElem he

/-- Contractibility is preserved along `StarHomotopyEquiv`. -/
theorem of_starHomotopyEquiv (e : StarHomotopyEquiv A B) (hA : IsContractibleCStarAlgebra A) :
    IsContractibleCStarAlgebra B := by
  obtain ⟨H⟩ := hA
  have h1 : NonUnitalStarAlgHom.Homotopic (e.toFun.comp e.invFun) (0 : B →⋆ₙₐ[ℂ] B) := by
    have hzero : e.toFun.comp ((0 : A →⋆ₙₐ[ℂ] A).comp e.invFun) = 0 := by
      ext b
      simp
    exact hzero ▸ ⟨(H.compRight e.invFun).compLeft e.toFun (map_continuous e.toFun)⟩
  exact e.right_inv.symm.trans h1

theorem iff_of_starHomotopyEquiv (e : StarHomotopyEquiv A B) :
    IsContractibleCStarAlgebra A ↔ IsContractibleCStarAlgebra B :=
  ⟨of_starHomotopyEquiv e, of_starHomotopyEquiv e.symm⟩

theorem iff_of_starAlgEquiv (e : A ≃⋆ₐ[ℂ] B) :
    IsContractibleCStarAlgebra A ↔ IsContractibleCStarAlgebra B :=
  iff_of_starHomotopyEquiv (.ofStarAlgEquiv e)

/-- No nontrivial unital C⋆-algebra is contractible, since `1 ≠ 0` is idempotent. -/
theorem not_of_nontrivial {A : Type*} [CStarAlgebra A] [Nontrivial A] :
    ¬IsContractibleCStarAlgebra A := fun hA =>
  one_ne_zero (hA.eq_zero_of_isIdempotentElem IsIdempotentElem.one)

end IsContractibleCStarAlgebra

end TauCeti
