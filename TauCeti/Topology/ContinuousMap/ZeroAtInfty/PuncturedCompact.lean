/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.NonUnitalSubalgebra
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Star
public import Mathlib.Topology.ContinuousMap.ZeroAtInftyUnitization
public import TauCeti.Algebra.Algebra.Unitization
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Basic

/-!
# Functions vanishing at infinity on a punctured compact Hausdorff space

When `K` is a compact Hausdorff space and `x₀ : K`, the punctured space `({x₀}ᶜ : Set K)` is
locally compact Hausdorff and its one-point compactification identifies with `K` by sending `∞` to
`x₀` (`OnePoint.complSingletonHomeomorph`). Under this identification:

* extending by `0` at `x₀` (`ZeroAtInftyContinuousMap.extendComplSingleton`) embeds
  `C₀(({x₀}ᶜ : Set K), R)` isometrically onto the closed `⋆`-ideal
  `{F : C(K, R) | F x₀ = 0}` (`ContinuousMap.restrictComplSingletonStarAlgEquiv`);
* combining this with `ZeroAtInftyContinuousMap.unitizationStarAlgEquiv` identifies the forced
  unitization `Unitization R C₀(({x₀}ᶜ : Set K), R)` with `C(K, R)` so that the scalar
  augmentation `Unitization.fstStarAlgHom` corresponds to evaluation at `x₀`
  (`ZeroAtInftyContinuousMap.unitizationComplSingletonStarAlgEquiv`).

We also record `⋆`-algebra equivalences on `C₀(X, R)` induced by homeomorphisms of `X`
(`Homeomorph.compZeroAtInftyStarAlgEquiv'`) and, when `X` is compact, the isometric `⋆`-algebra
identification `C(X, R) ≃⋆ₐ[S] C₀(X, R)` (`ContinuousMap.liftZeroAtInftyStarAlgEquiv`).

## Main declarations

* `OnePoint.complSingletonHomeomorph`: `OnePoint ({x₀}ᶜ : Set K) ≃ₜ K` sending `∞` to `x₀`.
* `ZeroAtInftyContinuousMap.extendComplSingleton`: extension by zero at `x₀` from
  `C₀(({x₀}ᶜ : Set K), R)` to `C(K, R)`.
* `ContinuousMap.restrictComplSingleton`: restriction of `F : C(K, R)` with `F x₀ = 0` to
  `C₀(({x₀}ᶜ : Set K), R)`.
* `ContinuousMap.idealOfSetStarSubalgebra`: the closed nonunital `⋆`-subalgebra of `C(X, R)` of
  functions vanishing on `sᶜ`.
* `ContinuousMap.restrictComplSingletonStarAlgEquiv`: the `⋆`-algebra equivalence
  `{F : C(K, R) | F x₀ = 0} ≃⋆ₐ[S] C₀(({x₀}ᶜ : Set K), R)`.
* `ZeroAtInftyContinuousMap.unitizationComplSingletonStarAlgEquiv`: the `⋆`-algebra equivalence
  `Unitization R C₀(({x₀}ᶜ : Set K), R) ≃⋆ₐ[S] C(K, R)`.
* `Homeomorph.compZeroAtInftyStarAlgEquiv'`: precomposition `C₀(Y, R) ≃⋆ₐ[S] C₀(X, R)` along a
  homeomorphism `X ≃ₜ Y`.
* `ContinuousMap.liftZeroAtInftyStarAlgEquiv`: the canonical `⋆`-algebra equivalence
  `C(X, R) ≃⋆ₐ[S] C₀(X, R)` for compact `X`.

## References

* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Academic Press (1990), §2.1.
-/

public section

open Filter Topology
open scoped ZeroAtInfty

namespace OnePoint

variable {K : Type*} [TopologicalSpace K]

/-- The complement of a singleton in a locally compact `T₁` space is locally compact. -/
theorem locallyCompactSpace_compl_singleton [LocallyCompactSpace K] [T1Space K] (x₀ : K) :
    LocallyCompactSpace ({x₀}ᶜ : Set K) :=
  isOpen_compl_singleton.locallyCompactSpace

/-- If `{x₀}` is isolated (open) in a compact space `K`, then its complement `{x₀}ᶜ` is compact. -/
theorem compactSpace_compl_singleton_of_isOpen [CompactSpace K] {x₀ : K}
    (hx₀ : IsOpen ({x₀} : Set K)) : CompactSpace ({x₀}ᶜ : Set K) :=
  isCompact_iff_compactSpace.mp hx₀.isClosed_compl.isCompact

variable [CompactSpace K] [T2Space K]

/-- The one-point compactification of a punctured compact Hausdorff space `({x₀}ᶜ : Set K)` is
canonically homeomorphic to `K`, sending `∞` to `x₀` and `(x : {x₀}ᶜ)` to `x.1`. -/
noncomputable def complSingletonHomeomorph (x₀ : K) : OnePoint ({x₀}ᶜ : Set K) ≃ₜ K :=
  equivOfIsEmbeddingOfRangeEq x₀ Subtype.val Topology.IsEmbedding.subtypeVal Subtype.range_coe

/-- `complSingletonHomeomorph x₀` maps a finite point `x : {x₀}ᶜ` to `x.1`. -/
@[simp]
theorem complSingletonHomeomorph_coe (x₀ : K) (x : ({x₀}ᶜ : Set K)) :
    complSingletonHomeomorph x₀ x = x.1 := by rfl

/-- `complSingletonHomeomorph x₀` maps `∞` to `x₀`. -/
@[simp]
theorem complSingletonHomeomorph_infty (x₀ : K) :
    complSingletonHomeomorph x₀ ∞ = x₀ := by rfl

/-- The inverse of `complSingletonHomeomorph x₀` sends `x₀` to `∞`. -/
@[simp]
theorem complSingletonHomeomorph_symm_self (x₀ : K) :
    (complSingletonHomeomorph x₀).symm x₀ = ∞ :=
  (Homeomorph.symm_apply_eq _).2 (complSingletonHomeomorph_infty x₀).symm

/-- The inverse of `complSingletonHomeomorph x₀` sends `x.1` back to `(x : OnePoint _)`. -/
@[simp]
theorem complSingletonHomeomorph_symm_coe (x₀ : K) (x : ({x₀}ᶜ : Set K)) :
    (complSingletonHomeomorph x₀).symm x.1 = x :=
  (Homeomorph.symm_apply_eq _).2 (complSingletonHomeomorph_coe x₀ x).symm

/-- For `x ≠ x₀`, `(complSingletonHomeomorph x₀).symm x` is the finite point `⟨x, hx⟩`. -/
theorem complSingletonHomeomorph_symm_of_ne {x₀ x : K} (hx : x ≠ x₀) :
    (complSingletonHomeomorph x₀).symm x = (⟨x, hx⟩ : ({x₀}ᶜ : Set K)) :=
  complSingletonHomeomorph_symm_coe x₀ ⟨x, hx⟩

/-- Along the cocompact filter of `{x₀}ᶜ`, the subtype inclusion into a compact Hausdorff space `K`
converges to the puncture `x₀`. -/
theorem tendsto_subtype_val_cocompact_compl_singleton (x₀ : K) :
    Tendsto (Subtype.val : ({x₀}ᶜ : Set K) → K) (cocompact ({x₀}ᶜ : Set K)) (𝓝 x₀) := by
  simpa [coclosedCompact_eq_cocompact, Function.comp_def] using
    ((complSingletonHomeomorph x₀).continuous.tendsto ∞).comp tendsto_coe_infty

end OnePoint

namespace ZeroAtInftyContinuousMap

section ExtendComplSingleton

variable {K R S : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K] [TopologicalSpace R]

/-- Extend a function `f ∈ C₀(({x₀}ᶜ : Set K), R)` on a punctured compact Hausdorff space by `0` at
`x₀`, producing a continuous map on `K`. -/
noncomputable def extendComplSingleton [Zero R] {x₀ : K} (f : C₀(({x₀}ᶜ : Set K), R)) : C(K, R) :=
  f.toOnePoint.comp (OnePoint.complSingletonHomeomorph x₀).symm

/-- The extension by zero vanishes at the puncture `x₀`. -/
@[simp]
theorem extendComplSingleton_self [Zero R] {x₀ : K} (f : C₀(({x₀}ᶜ : Set K), R)) :
    f.extendComplSingleton x₀ = 0 := by
  simp [extendComplSingleton]

/-- On `{x₀}ᶜ`, `extendComplSingleton` agrees with the original function. -/
@[simp]
theorem extendComplSingleton_coe [Zero R] {x₀ : K} (f : C₀(({x₀}ᶜ : Set K), R))
    (x : ({x₀}ᶜ : Set K)) : f.extendComplSingleton x.1 = f x := by
  simp [extendComplSingleton]

/-- Away from `x₀`, `extendComplSingleton` evaluates to `f ⟨x, hx⟩`. -/
theorem extendComplSingleton_of_ne [Zero R] {x₀ x : K} (f : C₀(({x₀}ᶜ : Set K), R))
    (hx : x ≠ x₀) : f.extendComplSingleton x = f ⟨x, hx⟩ :=
  extendComplSingleton_coe f ⟨x, hx⟩

/-- Extending by zero at `x₀` is injective. -/
theorem extendComplSingleton_injective [Zero R] (x₀ : K) :
    Function.Injective (extendComplSingleton (K := K) (R := R) (x₀ := x₀)) := fun f g h ↦
  ext fun x ↦ by simpa using congr($h x.1)

/-- Extending the zero function gives the zero continuous map. -/
@[simp]
theorem extendComplSingleton_zero [Zero R] (x₀ : K) :
    (0 : C₀(({x₀}ᶜ : Set K), R)).extendComplSingleton = 0 := by
  ext x
  simp [extendComplSingleton]

/-- Extension by zero at `x₀` commutes with addition. -/
@[simp]
theorem extendComplSingleton_add [AddZeroClass R] [ContinuousAdd R] {x₀ : K}
    (f g : C₀(({x₀}ᶜ : Set K), R)) :
    (f + g).extendComplSingleton = f.extendComplSingleton + g.extendComplSingleton := by
  ext x
  simp [extendComplSingleton]

/-- Extension by zero at `x₀` commutes with subtraction. -/
@[simp]
theorem extendComplSingleton_sub [AddGroup R] [IsTopologicalAddGroup R] {x₀ : K}
    (f g : C₀(({x₀}ᶜ : Set K), R)) :
    (f - g).extendComplSingleton = f.extendComplSingleton - g.extendComplSingleton := by
  ext x
  simp [extendComplSingleton]

/-- Extension by zero at `x₀` commutes with multiplication. -/
@[simp]
theorem extendComplSingleton_mul [MulZeroClass R] [ContinuousMul R] {x₀ : K}
    (f g : C₀(({x₀}ᶜ : Set K), R)) :
    (f * g).extendComplSingleton = f.extendComplSingleton * g.extendComplSingleton := by
  ext x
  simp [extendComplSingleton]

/-- Extension by zero at `x₀` commutes with scalar multiplication. -/
@[simp]
theorem extendComplSingleton_smul [Zero R] [SMulZeroClass S R] [ContinuousConstSMul S R] {x₀ : K}
    (s : S) (f : C₀(({x₀}ᶜ : Set K), R)) :
    (s • f).extendComplSingleton = s • f.extendComplSingleton := by
  ext x
  simp [extendComplSingleton]

/-- Extension by zero at `x₀` commutes with `star`. -/
@[simp]
theorem extendComplSingleton_star [AddMonoid R] [StarAddMonoid R] [ContinuousStar R] {x₀ : K}
    (f : C₀(({x₀}ᶜ : Set K), R)) :
    (star f).extendComplSingleton = star f.extendComplSingleton := by
  ext x
  simp [extendComplSingleton]

/-- Extension by zero at `x₀` preserves the supremum norm. -/
@[simp]
theorem norm_extendComplSingleton {E : Type*} [SeminormedAddCommGroup E] {x₀ : K}
    (f : C₀(({x₀}ᶜ : Set K), E)) : ‖f.extendComplSingleton‖ = ‖f‖ := by
  refine le_antisymm ((ContinuousMap.norm_le _ (norm_nonneg f)).2 fun x ↦ ?_)
    ((norm_le (norm_nonneg _)).2 fun x ↦ by
      simpa using f.extendComplSingleton.norm_coe_le_norm x.1)
  rcases eq_or_ne x x₀ with rfl | hx
  · simp
  · simpa [extendComplSingleton_of_ne f hx] using norm_coe_le_norm f ⟨x, hx⟩

/-- Extension by zero at `x₀` is an isometry `C₀(({x₀}ᶜ : Set K), E) → C(K, E)`. -/
theorem isometry_extendComplSingleton {E : Type*} [SeminormedAddCommGroup E] (x₀ : K) :
    Isometry (extendComplSingleton (K := K) (R := E) (x₀ := x₀)) :=
  Isometry.of_dist_eq fun f g ↦ by simp [dist_eq_norm, ← extendComplSingleton_sub]

/-- The forced unitization `Unitization R C₀(({x₀}ᶜ : Set K), R)` of functions vanishing at
infinity on a punctured compact Hausdorff space is canonically `⋆`-isomorphic to `C(K, R)`, sending
`(r, f)` to `const K r + f.extendComplSingleton`. -/
noncomputable def unitizationComplSingletonStarAlgEquiv (S R : Type*)
    [CommSemiring S] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [StarRing R]
    [ContinuousStar R] [Algebra S R] (x₀ : K) :
    Unitization R C₀(({x₀}ᶜ : Set K), R) ≃⋆ₐ[S] C(K, R) :=
  (unitizationStarAlgEquiv ({x₀}ᶜ : Set K) R S).trans
    ((OnePoint.complSingletonHomeomorph x₀).symm.compStarAlgEquiv' S R)

/-- At the puncture `x₀`, `unitizationComplSingletonStarAlgEquiv` extracts the scalar coordinate. -/
@[simp]
theorem unitizationComplSingletonStarAlgEquiv_apply_self (S R : Type*)
    [CommSemiring S] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [StarRing R]
    [ContinuousStar R] [Algebra S R] (x₀ : K) (u : Unitization R C₀(({x₀}ᶜ : Set K), R)) :
    unitizationComplSingletonStarAlgEquiv S R x₀ u x₀ = u.fst := by
  simp [unitizationComplSingletonStarAlgEquiv]

/-- Away from `x₀`, `unitizationComplSingletonStarAlgEquiv` evaluates to `u.fst + u.snd x`. -/
@[simp]
theorem unitizationComplSingletonStarAlgEquiv_apply_coe (S R : Type*)
    [CommSemiring S] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [StarRing R]
    [ContinuousStar R] [Algebra S R] (x₀ : K) (u : Unitization R C₀(({x₀}ᶜ : Set K), R))
    (x : ({x₀}ᶜ : Set K)) :
    unitizationComplSingletonStarAlgEquiv S R x₀ u x.1 = u.fst + u.snd x := by
  simp [unitizationComplSingletonStarAlgEquiv]

/-- On `inr f`, `unitizationComplSingletonStarAlgEquiv` is `f.extendComplSingleton`. -/
@[simp]
theorem unitizationComplSingletonStarAlgEquiv_inr (S R : Type*)
    [CommSemiring S] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [StarRing R]
    [ContinuousStar R] [Algebra S R] (x₀ : K) (f : C₀(({x₀}ᶜ : Set K), R)) :
    unitizationComplSingletonStarAlgEquiv S R x₀ f = f.extendComplSingleton := by
  ext x
  simp [unitizationComplSingletonStarAlgEquiv, extendComplSingleton]

/-- Under `unitizationComplSingletonStarAlgEquiv R R x₀`, evaluation at `x₀` corresponds to the
scalar augmentation `Unitization.fstStarAlgHom`. -/
@[simp]
theorem evalStarAlgHom_comp_unitizationComplSingletonStarAlgEquiv (R : Type*)
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [StarRing R] [ContinuousStar R]
    (x₀ : K) :
    (ContinuousMap.evalStarAlgHom R R x₀).comp
        (unitizationComplSingletonStarAlgEquiv R R x₀).toStarAlgHom =
      Unitization.fstStarAlgHom R C₀(({x₀}ᶜ : Set K), R) :=
  StarAlgHom.ext fun _ ↦ by simp

end ExtendComplSingleton

end ZeroAtInftyContinuousMap

namespace ContinuousMap

section RestrictComplSingleton

variable {K R : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K] [TopologicalSpace R]

/-- Restrict a continuous map `F : C(K, R)` vanishing at `x₀` to an element of
`C₀(({x₀}ᶜ : Set K), R)`. -/
def restrictComplSingleton [Zero R] (F : C(K, R)) (x₀ : K) (hF : F x₀ = 0) :
    C₀(({x₀}ᶜ : Set K), R) where
  toFun x := F x.1
  continuous_toFun := F.continuous.comp continuous_subtype_val
  zero_at_infty' := by
    simpa [hF, Function.comp_def] using
      (F.continuous.tendsto x₀).comp (OnePoint.tendsto_subtype_val_cocompact_compl_singleton x₀)

/-- `F.restrictComplSingleton x₀ hF` evaluates to `F x.1` at `x : {x₀}ᶜ`. -/
@[simp]
theorem restrictComplSingleton_apply [Zero R] (F : C(K, R)) (x₀ : K) (hF : F x₀ = 0)
    (x : ({x₀}ᶜ : Set K)) : F.restrictComplSingleton x₀ hF x = F x.1 := (rfl)

/-- Restricting `f.extendComplSingleton` back to `{x₀}ᶜ` recovers `f`. -/
@[simp]
theorem restrictComplSingleton_extendComplSingleton [Zero R] {x₀ : K}
    (f : C₀(({x₀}ᶜ : Set K), R)) :
    f.extendComplSingleton.restrictComplSingleton x₀ f.extendComplSingleton_self = f := by
  ext x
  simp

/-- Extending `F.restrictComplSingleton x₀ hF` by zero at `x₀` recovers `F`. -/
@[simp]
theorem extendComplSingleton_restrictComplSingleton [Zero R] (F : C(K, R)) (x₀ : K)
    (hF : F x₀ = 0) : (F.restrictComplSingleton x₀ hF).extendComplSingleton = F := by
  ext x
  rcases eq_or_ne x x₀ with rfl | hx
  · simp [hF]
  · simp [ZeroAtInftyContinuousMap.extendComplSingleton_of_ne _ hx]

/-- The image of `ZeroAtInftyContinuousMap.extendComplSingleton` at `x₀` is the set of continuous
functions on `K` vanishing at `x₀`. -/
theorem range_extendComplSingleton [Zero R] (x₀ : K) :
    Set.range (ZeroAtInftyContinuousMap.extendComplSingleton (K := K) (R := R) (x₀ := x₀)) =
      {F : C(K, R) | F x₀ = 0} := by
  ext F
  exact ⟨by rintro ⟨f, rfl⟩; exact f.extendComplSingleton_self,
    fun hF ↦ ⟨F.restrictComplSingleton x₀ hF, F.extendComplSingleton_restrictComplSingleton x₀ hF⟩⟩

/-- Restricting `F : C(K, E)` with `F x₀ = 0` to `{x₀}ᶜ` preserves the supremum norm. -/
@[simp]
theorem norm_restrictComplSingleton {E : Type*} [SeminormedAddCommGroup E] (F : C(K, E)) (x₀ : K)
    (hF : F x₀ = 0) : ‖F.restrictComplSingleton x₀ hF‖ = ‖F‖ := by
  rw [← (F.restrictComplSingleton x₀ hF).norm_extendComplSingleton,
    F.extendComplSingleton_restrictComplSingleton x₀ hF]

end RestrictComplSingleton

section IdealOfSetStarSubalgebra

variable {X : Type*} [TopologicalSpace X]

/-- The nonunital `⋆`-subalgebra of `C(X, R)` consisting of functions vanishing outside `s`. When
`R` is a commutative topological `⋆`-ring, this is the `⋆`-subalgebra counterpart of
`ContinuousMap.idealOfSet`. -/
def idealOfSetStarSubalgebra (S R : Type*) [CommSemiring S] [TopologicalSpace R]
    [NonUnitalNonAssocSemiring R] [IsTopologicalSemiring R] [StarAddMonoid R] [ContinuousStar R]
    [Module S R] [ContinuousConstSMul S R] (s : Set X) :
    NonUnitalStarSubalgebra S C(X, R) where
  carrier := {f : C(X, R) | ∀ x ∈ sᶜ, f x = 0}
  mul_mem' {f _} hf _ x hx := by simp [hf x hx]
  zero_mem' _ _ := rfl
  add_mem' {f g} hf hg x hx := by simp [hf x hx, hg x hx]
  smul_mem' c {f} hf x hx := by simp [hf x hx]
  star_mem' {f} hf x hx := by simp [hf x hx]

/-- Membership in `idealOfSetStarSubalgebra S R s` means vanishing at every point outside `s`. -/
theorem mem_idealOfSetStarSubalgebra {S R : Type*} [CommSemiring S] [TopologicalSpace R]
    [NonUnitalNonAssocSemiring R] [IsTopologicalSemiring R] [StarAddMonoid R] [ContinuousStar R]
    [Module S R] [ContinuousConstSMul S R] {s : Set X} {f : C(X, R)} :
    f ∈ idealOfSetStarSubalgebra S R s ↔ ∀ ⦃x : X⦄, x ∈ sᶜ → f x = 0 := (Iff.rfl)

/-- Membership in `idealOfSetStarSubalgebra S R {x₀}ᶜ` is equivalent to vanishing at `x₀`. -/
@[simp]
theorem mem_idealOfSetStarSubalgebra_compl_singleton {S R : Type*} [CommSemiring S]
    [TopologicalSpace R] [NonUnitalNonAssocSemiring R] [IsTopologicalSemiring R] [StarAddMonoid R]
    [ContinuousStar R] [Module S R] [ContinuousConstSMul S R] (x₀ : X) (f : C(X, R)) :
    f ∈ idealOfSetStarSubalgebra S R ({x₀}ᶜ : Set X) ↔ f x₀ = 0 := by
  simp [mem_idealOfSetStarSubalgebra]

/-- When `R` is Hausdorff, `idealOfSetStarSubalgebra S R s` is closed in `C(X, R)` (and therefore
inherits completeness whenever `C(X, R)` is complete). -/
instance isClosed_idealOfSetStarSubalgebra {S R : Type*} [CommSemiring S] [TopologicalSpace R]
    [NonUnitalNonAssocSemiring R] [IsTopologicalSemiring R] [StarAddMonoid R] [ContinuousStar R]
    [Module S R] [ContinuousConstSMul S R] [T2Space R] (s : Set X) :
    IsClosed (idealOfSetStarSubalgebra S R s : Set C(X, R)) := by
  have hcoe : (idealOfSetStarSubalgebra S R s : Set C(X, R)) =
      ⋂ x ∈ sᶜ, {f : C(X, R) | f x = 0} := by
    ext f
    simp [mem_idealOfSetStarSubalgebra]
  rw [hcoe]
  exact isClosed_biInter fun x _ ↦ isClosed_eq (continuous_eval_const x) continuous_const

/-- For a compact Hausdorff space `K` and `x₀ : K`, restricting to `{x₀}ᶜ` and extending by zero at
`x₀` form a `⋆`-algebra equivalence between `{F : C(K, R) | F x₀ = 0}` and
`C₀(({x₀}ᶜ : Set K), R)`. -/
noncomputable def restrictComplSingletonStarAlgEquiv {K : Type*} [TopologicalSpace K]
    [CompactSpace K] [T2Space K] (S R : Type*) [CommSemiring S] [TopologicalSpace R]
    [NonUnitalNonAssocSemiring R] [IsTopologicalSemiring R] [StarRing R] [ContinuousStar R]
    [Module S R] [ContinuousConstSMul S R] (x₀ : K) :
    idealOfSetStarSubalgebra S R ({x₀}ᶜ : Set K) ≃⋆ₐ[S] C₀(({x₀}ᶜ : Set K), R) where
  toFun F := F.1.restrictComplSingleton x₀
    ((mem_idealOfSetStarSubalgebra_compl_singleton x₀ F.1).mp F.2)
  invFun f := ⟨f.extendComplSingleton,
    (mem_idealOfSetStarSubalgebra_compl_singleton x₀ _).mpr f.extendComplSingleton_self⟩
  left_inv F := Subtype.ext <| F.1.extendComplSingleton_restrictComplSingleton x₀ _
  right_inv f := restrictComplSingleton_extendComplSingleton f
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_star' _ := rfl
  map_smul' _ _ := rfl

/-- `restrictComplSingletonStarAlgEquiv` evaluates at `x : {x₀}ᶜ` by evaluating the underlying
continuous map at `x.1`. -/
@[simp]
theorem restrictComplSingletonStarAlgEquiv_apply {K : Type*} [TopologicalSpace K]
    [CompactSpace K] [T2Space K] (S R : Type*) [CommSemiring S] [TopologicalSpace R]
    [NonUnitalNonAssocSemiring R] [IsTopologicalSemiring R] [StarRing R] [ContinuousStar R]
    [Module S R] [ContinuousConstSMul S R] (x₀ : K)
    (F : idealOfSetStarSubalgebra S R ({x₀}ᶜ : Set K)) (x : ({x₀}ᶜ : Set K)) :
    restrictComplSingletonStarAlgEquiv S R x₀ F x = F.1 x.1 := by rfl

/-- The inverse of `restrictComplSingletonStarAlgEquiv` embeds `f` via `extendComplSingleton`. -/
@[simp]
theorem coe_restrictComplSingletonStarAlgEquiv_symm_apply {K : Type*} [TopologicalSpace K]
    [CompactSpace K] [T2Space K] (S R : Type*) [CommSemiring S] [TopologicalSpace R]
    [NonUnitalNonAssocSemiring R] [IsTopologicalSemiring R] [StarRing R] [ContinuousStar R]
    [Module S R] [ContinuousConstSMul S R] (x₀ : K) (f : C₀(({x₀}ᶜ : Set K), R)) :
    ((restrictComplSingletonStarAlgEquiv S R x₀).symm f : C(K, R)) = f.extendComplSingleton := by
  rfl

end IdealOfSetStarSubalgebra

section CompactLift

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- On a compact space `X`, every continuous map vanishes at infinity, giving a canonical
`⋆`-algebra equivalence `C(X, R) ≃⋆ₐ[S] C₀(X, R)` upgrading
`ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty`. -/
def liftZeroAtInftyStarAlgEquiv (S R : Type*) [Semiring S] [TopologicalSpace R]
    [NonUnitalNonAssocSemiring R] [IsTopologicalSemiring R] [StarRing R] [ContinuousStar R]
    [Module S R] [ContinuousConstSMul S R] : C(X, R) ≃⋆ₐ[S] C₀(X, R) where
  toEquiv := ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_star' _ := rfl
  map_smul' _ _ := rfl

/-- `liftZeroAtInftyStarAlgEquiv` acts as the identity on underlying functions. -/
@[simp]
theorem liftZeroAtInftyStarAlgEquiv_apply (S R : Type*) [Semiring S] [TopologicalSpace R]
    [NonUnitalNonAssocSemiring R] [IsTopologicalSemiring R] [StarRing R] [ContinuousStar R]
    [Module S R] [ContinuousConstSMul S R] (f : C(X, R)) (x : X) :
    liftZeroAtInftyStarAlgEquiv S R f x = f x := (rfl)

/-- The inverse of `liftZeroAtInftyStarAlgEquiv` forgets the zero-at-infinity witness. -/
@[simp]
theorem liftZeroAtInftyStarAlgEquiv_symm_apply (S R : Type*) [Semiring S] [TopologicalSpace R]
    [NonUnitalNonAssocSemiring R] [IsTopologicalSemiring R] [StarRing R] [ContinuousStar R]
    [Module S R] [ContinuousConstSMul S R] (f : C₀(X, R)) :
    (liftZeroAtInftyStarAlgEquiv S R).symm f = f.toContinuousMap := (rfl)

/-- On a compact space, lifting `f : C(X, E)` to `C₀(X, E)` preserves the supremum norm. -/
@[simp]
theorem norm_liftZeroAtInfty {E : Type*} [SeminormedAddCommGroup E] (f : C(X, E)) :
    ‖ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty f‖ = ‖f‖ :=
  le_antisymm ((ZeroAtInftyContinuousMap.norm_le (norm_nonneg f)).2 fun x ↦ f.norm_coe_le_norm x)
    ((norm_le _ (norm_nonneg _)).2 fun x ↦
      ZeroAtInftyContinuousMap.norm_coe_le_norm
        (ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty f) x)

end CompactLift

end ContinuousMap

namespace Homeomorph

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A homeomorphism `e : X ≃ₜ Y` induces a `⋆`-algebra equivalence `C₀(Y, R) ≃⋆ₐ[S] C₀(X, R)` by
precomposition, mirroring `Homeomorph.compStarAlgEquiv'` on `C(Y, R)`. -/
def compZeroAtInftyStarAlgEquiv' (S R : Type*) [Semiring S] [TopologicalSpace R]
    [NonUnitalNonAssocSemiring R] [IsTopologicalSemiring R] [StarRing R] [ContinuousStar R]
    [Module S R] [ContinuousConstSMul S R] (e : X ≃ₜ Y) : C₀(Y, R) ≃⋆ₐ[S] C₀(X, R) where
  toFun f := f.comp e.toCocompactMap
  invFun f := f.comp e.symm.toCocompactMap
  left_inv f := by ext y; simp
  right_inv f := by ext x; simp
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_star' _ := rfl
  map_smul' _ _ := rfl

/-- `e.compZeroAtInftyStarAlgEquiv' S R` precomposes with `e`. -/
@[simp]
theorem compZeroAtInftyStarAlgEquiv'_apply (S R : Type*) [Semiring S] [TopologicalSpace R]
    [NonUnitalNonAssocSemiring R] [IsTopologicalSemiring R] [StarRing R] [ContinuousStar R]
    [Module S R] [ContinuousConstSMul S R] (e : X ≃ₜ Y) (f : C₀(Y, R)) (x : X) :
    e.compZeroAtInftyStarAlgEquiv' S R f x = f (e x) := (rfl)

/-- The inverse of `e.compZeroAtInftyStarAlgEquiv' S R` precomposes with `e.symm`. -/
@[simp]
theorem compZeroAtInftyStarAlgEquiv'_symm (S R : Type*) [Semiring S] [TopologicalSpace R]
    [NonUnitalNonAssocSemiring R] [IsTopologicalSemiring R] [StarRing R] [ContinuousStar R]
    [Module S R] [ContinuousConstSMul S R] (e : X ≃ₜ Y) :
    (e.compZeroAtInftyStarAlgEquiv' S R).symm = e.symm.compZeroAtInftyStarAlgEquiv' S R := (rfl)

/-- Precomposing with `Homeomorph.refl X` is the identity `⋆`-algebra equivalence on `C₀(X, R)`. -/
@[simp]
theorem compZeroAtInftyStarAlgEquiv'_refl (S R : Type*) [Semiring S] [TopologicalSpace R]
    [NonUnitalNonAssocSemiring R] [IsTopologicalSemiring R] [StarRing R] [ContinuousStar R]
    [Module S R] [ContinuousConstSMul S R] :
    (Homeomorph.refl X).compZeroAtInftyStarAlgEquiv' S R = StarAlgEquiv.refl S C₀(X, R) := by
  ext f x
  rfl

/-- `compZeroAtInftyStarAlgEquiv'` is contravariantly functorial under `Homeomorph.trans`. -/
theorem compZeroAtInftyStarAlgEquiv'_trans {Z : Type*} [TopologicalSpace Z] (S R : Type*)
    [Semiring S] [TopologicalSpace R] [NonUnitalNonAssocSemiring R] [IsTopologicalSemiring R]
    [StarRing R] [ContinuousStar R] [Module S R] [ContinuousConstSMul S R]
    (e₁ : X ≃ₜ Y) (e₂ : Y ≃ₜ Z) :
    (e₁.trans e₂).compZeroAtInftyStarAlgEquiv' S R =
      (e₂.compZeroAtInftyStarAlgEquiv' S R).trans (e₁.compZeroAtInftyStarAlgEquiv' S R) := by
  ext f x
  rfl

end Homeomorph
