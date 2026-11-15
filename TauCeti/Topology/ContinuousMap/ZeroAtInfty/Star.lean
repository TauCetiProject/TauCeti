/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Star
public import Mathlib.Topology.ContinuousMap.Units
public import Mathlib.Topology.ContinuousMap.ZeroAtInftyUnitization
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Basic

/-!
# `⋆`-algebra equivalences and quasispectra on `C₀(α, E)`

This file equips `C₀(α, E)` with functorial `⋆`-algebra homomorphisms and equivalences, together
with the computation of the scalar quasispectrum on `C₀(X, 𝕜)`:

* `ZeroAtInftyContinuousMap.compNonUnitalStarAlgHom` and
  `ZeroAtInftyContinuousMap.congrLeftStarAlgEquiv`: precomposition with a cocompact map as a
  nonunital `⋆`-algebra homomorphism, and reindexing along a homeomorphism as a `⋆`-algebra
  equivalence `C₀(α, E) ≃⋆ₐ[R] C₀(β, E)`.
* `ContinuousMap.liftZeroAtInftyLinearIsometryEquiv` and
  `ContinuousMap.liftZeroAtInftyStarAlgEquiv`: when `α` is compact, `C(α, E)` identifies
  isometrically and `⋆`-isomorphically with `C₀(α, E)` via
  `ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty`.
* `ZeroAtInftyContinuousMap.quasispectrum_eq_insert_zero_range`: on an `R₁` topological space `X`
  and complete normed field `𝕜`, the quasispectrum of `f : C₀(X, 𝕜)` is `insert 0 (Set.range f)`.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*, §II.2.2.
* G. J. Murphy, *C*-Algebras and Operator Theory*, §2.1.
-/

public section

open OnePoint
open scoped ZeroAtInfty

namespace ZeroAtInftyContinuousMap

section FunctorialStar

variable {R E α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
  [TopologicalSpace E]

/-- Precomposition with a cocompact map as a nonunital `⋆`-algebra homomorphism on `C₀`. -/
def compNonUnitalStarAlgHom [Semiring R] [NonUnitalNonAssocSemiring E] [IsTopologicalSemiring E]
    [Module R E] [ContinuousConstSMul R E] [StarRing E] [ContinuousStar E]
    (g : CocompactMap β γ) : C₀(γ, E) →⋆ₙₐ[R] C₀(β, E) where
  __ := compNonUnitalAlgHom g
  map_star' _ := rfl

@[simp]
theorem compNonUnitalStarAlgHom_apply [Semiring R] [NonUnitalNonAssocSemiring E]
    [IsTopologicalSemiring E] [Module R E] [ContinuousConstSMul R E] [StarRing E] [ContinuousStar E]
    (g : CocompactMap β γ) (f : C₀(γ, E)) (x : β) :
    compNonUnitalStarAlgHom (R := R) g f x = f (g x) := (rfl)

variable (R E) in
/-- Reindexing `C₀(α, E)` along a homeomorphism `e : α ≃ₜ β` as a `⋆`-algebra equivalence
`f ↦ f ∘ e.symm`, complementing `ZeroAtInftyContinuousMap.congrLeft`. -/
def congrLeftStarAlgEquiv [Semiring R] [NonUnitalNonAssocSemiring E] [IsTopologicalSemiring E]
    [Module R E] [ContinuousConstSMul R E] [StarRing E] [ContinuousStar E]
    (e : α ≃ₜ β) : C₀(α, E) ≃⋆ₐ[R] C₀(β, E) where
  toFun f := f.comp e.symm.toCocompactMap
  invFun f := f.comp e.toCocompactMap
  left_inv f := by ext; simp
  right_inv f := by ext; simp
  map_smul' _ _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

@[simp]
theorem congrLeftStarAlgEquiv_apply [Semiring R] [NonUnitalNonAssocSemiring E]
    [IsTopologicalSemiring E] [Module R E] [ContinuousConstSMul R E] [StarRing E] [ContinuousStar E]
    (e : α ≃ₜ β) (f : C₀(α, E)) (y : β) :
    congrLeftStarAlgEquiv R E e f y = f (e.symm y) := (rfl)

@[simp]
theorem congrLeftStarAlgEquiv_symm [Semiring R] [NonUnitalNonAssocSemiring E]
    [IsTopologicalSemiring E] [Module R E] [ContinuousConstSMul R E] [StarRing E] [ContinuousStar E]
    (e : α ≃ₜ β) :
    (congrLeftStarAlgEquiv R E e).symm = congrLeftStarAlgEquiv R E e.symm := (rfl)

@[simp]
theorem congrLeftStarAlgEquiv_refl [Semiring R] [NonUnitalNonAssocSemiring E]
    [IsTopologicalSemiring E] [Module R E] [ContinuousConstSMul R E] [StarRing E]
    [ContinuousStar E] :
    congrLeftStarAlgEquiv R E (Homeomorph.refl α) = StarAlgEquiv.refl R C₀(α, E) := (rfl)

theorem congrLeftStarAlgEquiv_trans [Semiring R] [NonUnitalNonAssocSemiring E]
    [IsTopologicalSemiring E] [Module R E] [ContinuousConstSMul R E] [StarRing E] [ContinuousStar E]
    (e : α ≃ₜ β) (e' : β ≃ₜ γ) :
    congrLeftStarAlgEquiv R E (e.trans e') =
      (congrLeftStarAlgEquiv R E e).trans (congrLeftStarAlgEquiv R E e') := (rfl)

end FunctorialStar

section Quasispectrum

variable {X 𝕜 : Type*} [TopologicalSpace X] [R1Space X] [NormedField 𝕜] [CompleteSpace 𝕜]

/-- On an `R₁` space `X`, the quasispectrum of `f : C₀(X, 𝕜)` over a complete normed field `𝕜` is
`insert 0 (Set.range f)`. -/
theorem quasispectrum_eq_insert_zero_range (f : C₀(X, 𝕜)) :
    quasispectrum 𝕜 f = insert 0 (Set.range f) := by
  rw [Unitization.quasispectrum_eq_spectrum_inr 𝕜 f,
    ← AlgEquiv.spectrum_eq (unitizationAlgEquiv X 𝕜 𝕜) (f : Unitization 𝕜 C₀(X, 𝕜)),
    coe_unitizationAlgEquiv, unitizationEquiv_inr, ContinuousMap.spectrum_eq_range]
  ext z
  constructor
  · rintro ⟨p, rfl⟩
    induction p using OnePoint.rec with
    | infty => exact Or.inl rfl
    | coe x => exact Or.inr ⟨x, rfl⟩
  · rintro (rfl | ⟨x, rfl⟩)
    · exact ⟨∞, rfl⟩
    · exact ⟨x, rfl⟩

end Quasispectrum

end ZeroAtInftyContinuousMap

namespace ContinuousMap

section LiftZeroAtInfty

variable {R α E : Type*} [TopologicalSpace α] [CompactSpace α]

/-- On a compact space `α`, `ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty` preserves the
supremum norm. -/
@[simp]
theorem norm_liftZeroAtInfty [SeminormedAddCommGroup E] (f : C(α, E)) :
    ‖ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty f‖ = ‖f‖ :=
  le_antisymm
    ((ZeroAtInftyContinuousMap.norm_le (norm_nonneg f)).2 fun x => f.norm_coe_le_norm x)
    ((f.norm_le (norm_nonneg _)).2 fun x =>
      (ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty f).norm_coe_le_norm x)

variable (R α E) in
/-- On a compact space `α`, `C(α, E)` is linearly isometric to `C₀(α, E)` via
`ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty`. -/
noncomputable def liftZeroAtInftyLinearIsometryEquiv [Semiring R] [SeminormedAddCommGroup E]
    [Module R E] [ContinuousConstSMul R E] : C(α, E) ≃ₗᵢ[R] C₀(α, E) where
  toEquiv := ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' := norm_liftZeroAtInfty

@[simp]
theorem coe_liftZeroAtInftyLinearIsometryEquiv [Semiring R] [SeminormedAddCommGroup E]
    [Module R E] [ContinuousConstSMul R E] :
    ⇑(liftZeroAtInftyLinearIsometryEquiv R α E) =
      ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty := (rfl)

@[simp]
theorem coe_liftZeroAtInftyLinearIsometryEquiv_symm [Semiring R] [SeminormedAddCommGroup E]
    [Module R E] [ContinuousConstSMul R E] :
    ⇑(liftZeroAtInftyLinearIsometryEquiv R α E).symm =
      ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty.symm := (rfl)

variable (R α E) in
/-- On a compact space `α`, `C(α, E)` is `⋆`-isomorphic to `C₀(α, E)` via
`ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty`. -/
def liftZeroAtInftyStarAlgEquiv [Semiring R] [TopologicalSpace E] [NonUnitalNonAssocSemiring E]
    [IsTopologicalSemiring E] [Module R E] [ContinuousConstSMul R E] [StarRing E]
    [ContinuousStar E] : C(α, E) ≃⋆ₐ[R] C₀(α, E) where
  toEquiv := ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty
  map_smul' _ _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

@[simp]
theorem coe_liftZeroAtInftyStarAlgEquiv [Semiring R] [TopologicalSpace E]
    [NonUnitalNonAssocSemiring E] [IsTopologicalSemiring E] [Module R E] [ContinuousConstSMul R E]
    [StarRing E] [ContinuousStar E] :
    ⇑(liftZeroAtInftyStarAlgEquiv R α E) =
      ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty := (rfl)

@[simp]
theorem coe_liftZeroAtInftyStarAlgEquiv_symm [Semiring R] [TopologicalSpace E]
    [NonUnitalNonAssocSemiring E] [IsTopologicalSemiring E] [Module R E] [ContinuousConstSMul R E]
    [StarRing E] [ContinuousStar E] :
    ⇑(liftZeroAtInftyStarAlgEquiv R α E).symm =
      ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty.symm := (rfl)

end LiftZeroAtInfty

end ContinuousMap
