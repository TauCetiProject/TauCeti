/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.HopfAlgebra.Integral.Positive
import TauCeti.Algebra.HopfAlgebra.Antipode

/-!
# Algebraic Haar functionals on Hopf star algebras

On any bialgebra `H` over a commutative semiring `R`, a left invariant integral `φ` and a right
invariant integral `ψ` satisfy `φ a * ψ 1 = ψ a * φ 1` for every `a : H`. In particular, a
normalized left invariant integral and a normalized right invariant integral coincide whenever both
exist, so a normalized two-sided invariant integral is unique. When `H` is a Hopf algebra, the
antipode interchanges left and right invariant integrals: if `h` is right invariant then
`h ∘ S` is left invariant, and symmetrically. Uniqueness then forces every normalized left or right
invariant integral on a Hopf algebra to be invariant under the antipode, `h (S a) = h a`, and hence
two-sided invariant.

For a complex star bialgebra `A`, `TauCeti.AlgebraicHaar A` bundles a normalized two-sided
invariant integral that is algebraically positive on squares, `0 ≤ h (star a * a)`. Over a complex
Hopf star algebra it is unique (`Subsingleton`), preserves the star and antipode, and is strictly
positive on nonzero squares `star a * a` and `a * star a`.

## Main declarations

* `LinearMap.IsLeftInvariantIntegral.apply_mul_one_eq`: compatibility between a left invariant
  integral and a right invariant integral on a bialgebra.
* `LinearMap.IsLeftInvariantIntegral.eq_of_isRightInvariantIntegral`: uniqueness of normalized
  invariant integrals on a bialgebra.
* `LinearMap.IsRightInvariantIntegral.comp_antipode` and
  `LinearMap.IsLeftInvariantIntegral.comp_antipode`: composing an invariant integral with the
  antipode reverses its handedness.
* `LinearMap.IsRightInvariantIntegral.map_antipode` and
  `LinearMap.IsLeftInvariantIntegral.map_antipode`: a normalized one-sided invariant integral on a
  Hopf algebra is antipode-invariant.
* `TauCeti.AlgebraicHaar`: a positive normalized two-sided invariant integral on a complex star
  bialgebra, with `Subsingleton`, `map_star`, `map_antipode`, and strict positivity on nonzero
  squares.

## References

* T. Timmermann, *An Invitation to Quantum Groups and Duality*, EMS, 2008, Proposition 2.2.2 and
  Section 3.2.
* S. Neshveyev and L. Tuset, *Compact Quantum Groups and Their Representation Categories*, SMF,
  2013, Theorem 1.6.6.
-/

public section

open Coalgebra HopfAlgebra TensorProduct WithConv
open scoped ComplexOrder

namespace LinearMap

section Bialgebra

variable {R H : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H]

/-- A left invariant integral `φ` and a right invariant integral `ψ` satisfy
`φ a * ψ 1 = ψ a * φ 1` on every element `a`. -/
theorem IsLeftInvariantIntegral.apply_mul_one_eq {φ ψ : H →ₗ[R] R}
    (hφ : φ.IsLeftInvariantIntegral) (hψ : ψ.IsRightInvariantIntegral) (a : H) :
    φ a * ψ 1 = ψ a * φ 1 := by
  let r := ℛ R a
  have hL : ψ (∑ i ∈ r.index, φ (r.right i) • r.left i) = φ a * ψ 1 := by
    rw [hφ.sum_smul r, map_smul, smul_eq_mul]
  have hR : φ (∑ i ∈ r.index, ψ (r.left i) • r.right i) = ψ a * φ 1 := by
    rw [hψ.sum_smul r, map_smul, smul_eq_mul]
  rw [← hL, ← hR, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by
    simp only [map_smul, smul_eq_mul, mul_comm]

/-- Any normalized left invariant integral equals any normalized right invariant integral. -/
theorem IsLeftInvariantIntegral.eq_of_isRightInvariantIntegral {φ ψ : H →ₗ[R] R}
    (hφ : φ.IsLeftInvariantIntegral) (hψ : ψ.IsRightInvariantIntegral)
    (hφ1 : φ 1 = 1) (hψ1 : ψ 1 = 1) : φ = ψ := by
  ext a
  simpa [hφ1, hψ1] using hφ.apply_mul_one_eq hψ a

end Bialgebra

section HopfAlgebra

variable {R H : Type*} [CommSemiring R] [Semiring H] [HopfAlgebra R H] {h : H →ₗ[R] R}

private theorem comul_antipode_eq_sum {a : H} {ι : Type*} (r : Coalgebra.Repr R a ι) :
    Coalgebra.comul (R := R) (HopfAlgebra.antipode R a) =
      ∑ i ∈ r.index,
        HopfAlgebra.antipode R (r.right i) ⊗ₜ[R] HopfAlgebra.antipode R (r.left i) := by
  rw [TauCeti.HopfAlgebra.antipode_comul_antidistrib_apply, ← r.eq, map_sum, map_sum]
  rfl

private def scalarConv (φ : H →ₗ[R] R) : WithConv (H →ₗ[R] H) :=
  toConv (Algebra.linearMap R H ∘ₗ φ)

private theorem isLeftInvariantIntegral_iff_id_mul (φ : H →ₗ[R] R) :
    φ.IsLeftInvariantIntegral ↔ toConv LinearMap.id * scalarConv φ = scalarConv φ := by
  rw [isLeftInvariantIntegral_iff, ← WithConv.ofConv_injective.eq_iff, LinearMap.ext_iff]
  refine forall_congr' fun a ↦ ?_
  let r := ℛ R a
  have h1 : TensorProduct.rid R H (φ.lTensor H (Coalgebra.comul a)) =
      (toConv LinearMap.id * scalarConv φ).ofConv a := by
    rw [← r.eq, map_sum, map_sum, r.convMul_apply]
    exact Finset.sum_congr rfl fun i _ ↦ by simp [scalarConv, ← Algebra.commutes, Algebra.smul_def]
  rw [h1]
  simp [scalarConv, Algebra.algebraMap_eq_smul_one]

private theorem isRightInvariantIntegral_iff_mul_id (φ : H →ₗ[R] R) :
    φ.IsRightInvariantIntegral ↔ scalarConv φ * toConv LinearMap.id = scalarConv φ := by
  rw [isRightInvariantIntegral_iff, ← WithConv.ofConv_injective.eq_iff, LinearMap.ext_iff]
  refine forall_congr' fun a ↦ ?_
  let r := ℛ R a
  have h1 : TensorProduct.lid R H (φ.rTensor H (Coalgebra.comul a)) =
      (scalarConv φ * toConv LinearMap.id).ofConv a := by
    rw [← r.eq, map_sum, map_sum, r.convMul_apply]
    exact Finset.sum_congr rfl fun i _ ↦ by simp [scalarConv, Algebra.smul_def]
  rw [h1]
  simp [scalarConv, Algebra.algebraMap_eq_smul_one]

/-- Precomposing a right invariant integral with the antipode produces a left invariant
integral. -/
theorem IsRightInvariantIntegral.comp_antipode (hh : h.IsRightInvariantIntegral) :
    (h ∘ₗ HopfAlgebra.antipode R).IsLeftInvariantIntegral := by
  let S : H →ₗ[R] H := HopfAlgebra.antipode R
  have hS : toConv S * scalarConv (h ∘ₗ S) = scalarConv (h ∘ₗ S) := by
    apply WithConv.ofConv_injective
    ext a
    let r := ℛ R a
    have hhSa := isRightInvariantIntegral_iff.mp hh (S a)
    rw [comul_antipode_eq_sum r, map_sum, map_sum] at hhSa
    rw [r.convMul_apply]
    simpa [scalarConv, S, ← Algebra.commutes, Algebra.smul_def] using hhSa
  rw [isLeftInvariantIntegral_iff_id_mul]
  calc toConv LinearMap.id * scalarConv (h ∘ₗ S)
      = (toConv LinearMap.id * toConv S) * scalarConv (h ∘ₗ S) := by rw [mul_assoc, hS]
    _ = scalarConv (h ∘ₗ S) := by rw [LinearMap.id_mul_antipode, one_mul]

/-- Precomposing a left invariant integral with the antipode produces a right invariant
integral. -/
theorem IsLeftInvariantIntegral.comp_antipode (hh : h.IsLeftInvariantIntegral) :
    (h ∘ₗ HopfAlgebra.antipode R).IsRightInvariantIntegral := by
  let S : H →ₗ[R] H := HopfAlgebra.antipode R
  have hS : scalarConv (h ∘ₗ S) * toConv S = scalarConv (h ∘ₗ S) := by
    apply WithConv.ofConv_injective
    ext a
    let r := ℛ R a
    have hhSa := isLeftInvariantIntegral_iff.mp hh (S a)
    rw [comul_antipode_eq_sum r, map_sum, map_sum] at hhSa
    rw [r.convMul_apply]
    simpa [scalarConv, S, Algebra.smul_def] using hhSa
  rw [isRightInvariantIntegral_iff_mul_id]
  calc scalarConv (h ∘ₗ S) * toConv LinearMap.id
      = scalarConv (h ∘ₗ S) * (toConv S * toConv LinearMap.id) := by rw [← mul_assoc, hS]
    _ = scalarConv (h ∘ₗ S) := by rw [LinearMap.antipode_mul_id, mul_one]

/-- A normalized right invariant integral on a Hopf algebra is invariant under the antipode. -/
theorem IsRightInvariantIntegral.map_antipode (hr : h.IsRightInvariantIntegral) (h1 : h 1 = 1)
    (a : H) : h (HopfAlgebra.antipode R a) = h a := by
  have heq : h ∘ₗ HopfAlgebra.antipode R = h :=
    hr.comp_antipode.eq_of_isRightInvariantIntegral hr (by simp [h1]) h1
  exact LinearMap.congr_fun heq a

/-- A normalized left invariant integral on a Hopf algebra is invariant under the antipode. -/
theorem IsLeftInvariantIntegral.map_antipode (hl : h.IsLeftInvariantIntegral) (h1 : h 1 = 1)
    (a : H) : h (HopfAlgebra.antipode R a) = h a := by
  have heq : h = h ∘ₗ HopfAlgebra.antipode R :=
    hl.eq_of_isRightInvariantIntegral hl.comp_antipode h1 (by simp [h1])
  exact (LinearMap.congr_fun heq a).symm

/-- Every normalized right invariant integral on a Hopf algebra is also left invariant. -/
theorem IsRightInvariantIntegral.isLeftInvariantIntegral (hr : h.IsRightInvariantIntegral)
    (h1 : h 1 = 1) : h.IsLeftInvariantIntegral := by
  have heq : h ∘ₗ HopfAlgebra.antipode R = h := LinearMap.ext (hr.map_antipode h1)
  exact heq ▸ hr.comp_antipode

/-- Every normalized left invariant integral on a Hopf algebra is also right invariant. -/
theorem IsLeftInvariantIntegral.isRightInvariantIntegral (hl : h.IsLeftInvariantIntegral)
    (h1 : h 1 = 1) : h.IsRightInvariantIntegral := by
  have heq : h ∘ₗ HopfAlgebra.antipode R = h := LinearMap.ext (hl.map_antipode h1)
  exact heq ▸ hl.comp_antipode

end HopfAlgebra

end LinearMap

namespace TauCeti

/-- An algebraic Haar functional on a complex star bialgebra `A`: a normalized two-sided invariant
linear functional `h : A →ₗ[ℂ] ℂ` that is nonnegative on every square `star a * a`. -/
structure AlgebraicHaar (A : Type*) [Ring A] [StarRing A] [Bialgebra ℂ A] extends A →ₗ[ℂ] ℂ where
  /-- Normalization on the multiplicative unit. -/
  map_one' : toLinearMap 1 = 1
  /-- Left invariance `(id ⊗ h) Δ(a) = h(a) 1`. -/
  left_invariant' : toLinearMap.IsLeftInvariantIntegral
  /-- Right invariance `(h ⊗ id) Δ(a) = h(a) 1`. -/
  right_invariant' : toLinearMap.IsRightInvariantIntegral
  /-- Algebraic positivity on squares `star a * a`. -/
  map_star_mul_self_nonneg : ∀ a, 0 ≤ toLinearMap (star a * a)

namespace AlgebraicHaar

section Bialgebra

variable {A : Type*} [Ring A] [StarRing A] [Bialgebra ℂ A]

instance : FunLike (AlgebraicHaar A) A ℂ where
  coe h := h.toLinearMap
  coe_injective := fun ⟨_, _, _, _, _⟩ ⟨_, _, _, _, _⟩ H ↦ by
    congr
    exact DFunLike.coe_injective H

instance : LinearMapClass (AlgebraicHaar A) ℂ A ℂ where
  map_add h := h.toLinearMap.map_add
  map_smulₛₗ h := h.toLinearMap.map_smul

/-- Algebraic Haar functionals are determined by their values on elements. -/
@[ext]
theorem ext {h₁ h₂ : AlgebraicHaar A} (H : ∀ a, h₁ a = h₂ a) : h₁ = h₂ :=
  DFunLike.ext h₁ h₂ H

/-- Applying the underlying linear map of an `AlgebraicHaar` functional agrees with function
coercion. -/
@[simp]
theorem toLinearMap_apply (h : AlgebraicHaar A) (a : A) : h.toLinearMap a = h a := (rfl)

/-- Applying a newly constructed `AlgebraicHaar` functional evaluates the underlying linear map. -/
@[simp]
theorem mk_apply (f : A →ₗ[ℂ] ℂ) (h1 hl hr hp) (a : A) :
    (AlgebraicHaar.mk f h1 hl hr hp) a = f a := (rfl)

/-- An algebraic Haar functional is unique whenever it exists. -/
instance : Subsingleton (AlgebraicHaar A) where
  allEq h₁ h₂ := ext <| LinearMap.congr_fun <|
    h₁.left_invariant'.eq_of_isRightInvariantIntegral h₂.right_invariant' h₁.map_one' h₂.map_one'

/-- Forget invariance and normalization to view an `AlgebraicHaar` functional as a
`StarPositiveFunctional`. -/
def toStarPositiveFunctional (h : AlgebraicHaar A) : StarPositiveFunctional A where
  toLinearMap := h.toLinearMap
  square_nonneg := h.map_star_mul_self_nonneg

/-- Coercing `toStarPositiveFunctional` to a function agrees with coercing `h`. -/
@[simp]
theorem toStarPositiveFunctional_apply (h : AlgebraicHaar A) (a : A) :
    h.toStarPositiveFunctional a = h a := (rfl)

/-- The underlying linear map of `toStarPositiveFunctional` is `h.toLinearMap`. -/
@[simp]
theorem toLinearMap_toStarPositiveFunctional (h : AlgebraicHaar A) :
    h.toStarPositiveFunctional.toLinearMap = h.toLinearMap := (rfl)

/-- An algebraic Haar functional takes the value `1` at `1`. -/
@[simp]
theorem map_one (h : AlgebraicHaar A) : h 1 = 1 := h.map_one'

/-- Left invariance of an algebraic Haar functional. -/
theorem isLeftInvariantIntegral (h : AlgebraicHaar A) : h.toLinearMap.IsLeftInvariantIntegral :=
  h.left_invariant'

/-- Right invariance of an algebraic Haar functional. -/
theorem isRightInvariantIntegral (h : AlgebraicHaar A) : h.toLinearMap.IsRightInvariantIntegral :=
  h.right_invariant'

/-- Left-slice identity `(id ⊗ h) Δ(a) = h(a) 1`. -/
theorem rid_lTensor_comul (h : AlgebraicHaar A) (a : A) :
    TensorProduct.rid ℂ A (h.toLinearMap.lTensor A (Coalgebra.comul a)) = h a • (1 : A) :=
  LinearMap.isLeftInvariantIntegral_iff.mp h.left_invariant' a

/-- Right-slice identity `(h ⊗ id) Δ(a) = h(a) 1`. -/
theorem lid_rTensor_comul (h : AlgebraicHaar A) (a : A) :
    TensorProduct.lid ℂ A (h.toLinearMap.rTensor A (Coalgebra.comul a)) = h a • (1 : A) :=
  LinearMap.isRightInvariantIntegral_iff.mp h.right_invariant' a

/-- The underlying linear map of an algebraic Haar functional is nonzero. -/
theorem toLinearMap_ne_zero (h : AlgebraicHaar A) : h.toLinearMap ≠ 0 :=
  fun h0 ↦ one_ne_zero (h.map_one'.symm.trans (by simp [h0]))

/-- Any algebra admitting an algebraic Haar functional is nontrivial. -/
theorem nontrivial (h : AlgebraicHaar A) : Nontrivial A :=
  nontrivial_of_ne 1 0 fun h10 ↦ one_ne_zero (by rw [← h.map_one, h10, map_zero])

/-- Nonnegativity on right-handed squares `a * star a`. -/
theorem map_mul_star_self_nonneg (h : AlgebraicHaar A) (a : A) : 0 ≤ h (a * star a) := by
  simpa using h.map_star_mul_self_nonneg (star a)

/-- An algebraic Haar functional preserves the involution. -/
@[simp]
theorem map_star [StarModule ℂ A] (h : AlgebraicHaar A) (a : A) : h (star a) = star (h a) :=
  h.toStarPositiveFunctional.map_star a

end Bialgebra

section HopfAlgebra

variable {A : Type*} [Ring A] [StarRing A] [HopfAlgebra ℂ A]

/-- Construct an `AlgebraicHaar` functional on a complex Hopf algebra from a normalized positive
right invariant integral, deducing left invariance automatically via the antipode. -/
def ofIsRightInvariantIntegral (f : A →ₗ[ℂ] ℂ) (h1 : f 1 = 1)
    (hr : f.IsRightInvariantIntegral) (hpos : ∀ a, 0 ≤ f (star a * a)) : AlgebraicHaar A where
  toLinearMap := f
  map_one' := h1
  left_invariant' := hr.isLeftInvariantIntegral h1
  right_invariant' := hr
  map_star_mul_self_nonneg := hpos

/-- Applying `ofIsRightInvariantIntegral` evaluates the underlying linear functional. -/
@[simp]
theorem ofIsRightInvariantIntegral_apply (f : A →ₗ[ℂ] ℂ) (h1 : f 1 = 1)
    (hr : f.IsRightInvariantIntegral) (hpos : ∀ a, 0 ≤ f (star a * a)) (a : A) :
    ofIsRightInvariantIntegral f h1 hr hpos a = f a := (rfl)

/-- Construct an `AlgebraicHaar` functional on a complex Hopf algebra from a normalized positive
left invariant integral, deducing right invariance automatically via the antipode. -/
def ofIsLeftInvariantIntegral (f : A →ₗ[ℂ] ℂ) (h1 : f 1 = 1)
    (hl : f.IsLeftInvariantIntegral) (hpos : ∀ a, 0 ≤ f (star a * a)) : AlgebraicHaar A where
  toLinearMap := f
  map_one' := h1
  left_invariant' := hl
  right_invariant' := hl.isRightInvariantIntegral h1
  map_star_mul_self_nonneg := hpos

/-- Applying `ofIsLeftInvariantIntegral` evaluates the underlying linear functional. -/
@[simp]
theorem ofIsLeftInvariantIntegral_apply (f : A →ₗ[ℂ] ℂ) (h1 : f 1 = 1)
    (hl : f.IsLeftInvariantIntegral) (hpos : ∀ a, 0 ≤ f (star a * a)) (a : A) :
    ofIsLeftInvariantIntegral f h1 hl hpos a = f a := (rfl)

/-- An algebraic Haar functional on a Hopf algebra is invariant under the antipode. -/
@[simp]
theorem map_antipode (h : AlgebraicHaar A) (a : A) : h (HopfAlgebra.antipode ℂ a) = h a :=
  h.isRightInvariantIntegral.map_antipode h.map_one a

variable [StarModule ℂ A]

/-- An algebraic Haar functional on a Hopf star algebra vanishes on `star a * a` only at `0`. -/
@[simp]
theorem map_star_mul_self_eq_zero_iff (h : AlgebraicHaar A) {a : A} :
    h (star a * a) = 0 ↔ a = 0 :=
  h.isRightInvariantIntegral.map_star_mul_self_eq_zero_iff h.toLinearMap_ne_zero
    h.map_star_mul_self_nonneg

/-- An algebraic Haar functional on a Hopf star algebra vanishes on `a * star a` only at `0`. -/
@[simp]
theorem map_mul_star_self_eq_zero_iff (h : AlgebraicHaar A) {a : A} :
    h (a * star a) = 0 ↔ a = 0 := by
  simpa [star_eq_zero] using h.map_star_mul_self_eq_zero_iff (a := star a)

/-- Strict positivity of an algebraic Haar functional on `star a * a` for `a ≠ 0`. -/
theorem map_star_mul_self_pos (h : AlgebraicHaar A) {a : A} (ha : a ≠ 0) :
    0 < h (star a * a) :=
  h.isRightInvariantIntegral.map_star_mul_self_pos h.toLinearMap_ne_zero
    h.map_star_mul_self_nonneg ha

/-- Strict positivity of an algebraic Haar functional on `a * star a` for `a ≠ 0`. -/
theorem map_mul_star_self_pos (h : AlgebraicHaar A) {a : A} (ha : a ≠ 0) :
    0 < h (a * star a) := by
  simpa using h.map_star_mul_self_pos (a := star a) (star_ne_zero.mpr ha)

end HopfAlgebra

end AlgebraicHaar

end TauCeti
