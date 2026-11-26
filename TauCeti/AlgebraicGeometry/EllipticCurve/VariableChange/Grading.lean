/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.StrictHopfAlgebroid
public import TauCeti.RingTheory.GradedAlgebra.Polynomial
public import TauCeti.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# The even homological grading of the strict Weierstrass Hopf algebroid

Both `A = ℤ[a₁, a₂, a₃, a₄, a₆]` and Bauer's strict arrow ring `A[r, s, t]` (`StrictArrowRing`),
together with the composable-pair ring `A[r, s, t] ⊗_A A[r, s, t]` (`StrictPairRing`), carry
nonnegative `GradedAlgebra` structures in even homological degrees `|aᵢ| = 2i` (`baseGrading`) and
`(|r|, |s|, |t|) = (4, 2, 6)` (`strictArrowGrading`, `strictPairGrading`), doubling the modular
weights `coefficientWeight`, `strictWeight`, and `strictPairWeight`. All odd-degree pieces vanish,
all structure maps of `(A, A[r, s, t])` preserve homological degrees, and `strictLeftUnit`,
`strictRightUnit`, `strictLeft`, `strictRight`, `strictCoproduct`, and `strictConjugation` reflect
homogeneity.

## Main definitions and results

* `WeierstrassCurve.map_toLaurent_toPolynomial_eq_scaling` and
  `WeierstrassCurve.VariableChange.map_toLaurent_toPolynomial_eq_scaling_mul_mul_inv`: applying
  `toLaurent ∘ toPolynomial 𝒜` scales a graded Weierstrass curve by `T (-w)` and conjugates a
  graded change of variables by `scaling _ (T (-w))`.
* `TauCeti.WeierstrassHopfAlgebroid.baseDegree`, `strictDegree`, `strictPairDegree`, `baseGrading`,
  `strictArrowGrading`, `strictPairGrading`, and odd-degree vanishing (`*_eq_bot_of_odd`).
* `TauCeti.WeierstrassHopfAlgebroid.strictLeftUnit_mem_strictArrowGrading_iff`,
  `strictRightUnit_mem_strictArrowGrading_iff`, `strictCounit_mem_baseGrading`,
  `strictCounitLeft_mem_strictArrowGrading`, `strictCounitRight_mem_strictArrowGrading`,
  `strictCoproduct_mem_strictPairGrading_iff`, and `strictConjugation_mem_strictArrowGrading_iff`.

## References

* T. Bauer, *Computation of the homotopy of the spectrum tmf*, Geom. Topol. Monogr. 13 (2008), §3.
-/

public section

noncomputable section

namespace WeierstrassCurve

open TauCeti.GradedAlgebra

/-- Applying `toLaurent ∘ toPolynomial 𝒜` to a Weierstrass curve whose coefficients `aᵢ` lie in
degree `w * i` scales its constant base change by `T (-w)`. -/
theorem map_toLaurent_toPolynomial_eq_scaling {B σ : Type*} [CommRing B] [SetLike σ B]
    [AddSubmonoidClass σ B] (𝒜 : ℕ → σ) [GradedRing 𝒜] (w : ℕ) {W : WeierstrassCurve B}
    (hW : ∀ i, W.specialize (MvPolynomial.X i) ∈ 𝒜 (w * coefficientWeight i)) :
    W.map (Polynomial.toLaurent.comp (toPolynomial 𝒜)) =
      VariableChange.scaling _
        (unitOfInvertible (LaurentPolynomial.T (w : ℤ) : LaurentPolynomial B))⁻¹ •
        W.map LaurentPolynomial.C := by
  have hspec : (W.map (Polynomial.toLaurent.comp (toPolynomial 𝒜))).specialize =
      (VariableChange.scaling _
        (unitOfInvertible (LaurentPolynomial.T (w : ℤ) : LaurentPolynomial B))⁻¹ •
          W.map LaurentPolynomial.C).specialize := by
    refine MvPolynomial.ringHom_ext' (RingHom.ext fun _ ↦ by simp) fun i ↦ by
      simp [-specialize_X, specialize_map, toPolynomial_of_mem (hW i), Polynomial.toLaurent_C_mul_T,
        specialize_mk_smul, LaurentPolynomial.T_pow, mul_comm (w : ℤ),
        mul_comm (LaurentPolynomial.T _) (LaurentPolynomial.C _)]
  rw [← map_specialize (W.map _), hspec, map_specialize]

/-- Applying `toLaurent ∘ toPolynomial 𝒜` to a Weierstrass change of variables `C = (u, r, s, t)`
with `u ∈ 𝒜 0`, `r ∈ 𝒜 (w * 2)`, `s ∈ 𝒜 w`, `t ∈ 𝒜 (w * 3)` conjugates its constant base change by
`scaling _ (T (-w))`. -/
theorem VariableChange.map_toLaurent_toPolynomial_eq_scaling_mul_mul_inv {B σ : Type*} [CommRing B]
    [SetLike σ B] [AddSubmonoidClass σ B] (𝒜 : ℕ → σ) [GradedRing 𝒜] (w : ℕ)
    {C : VariableChange B} (hu : (C.u : B) ∈ 𝒜 0) (hr : C.r ∈ 𝒜 (w * 2)) (hs : C.s ∈ 𝒜 w)
    (ht : C.t ∈ 𝒜 (w * 3)) :
    C.map (Polynomial.toLaurent.comp (toPolynomial 𝒜)) =
      VariableChange.scaling _
        (unitOfInvertible (LaurentPolynomial.T (w : ℤ) : LaurentPolynomial B))⁻¹ *
        C.map LaurentPolynomial.C *
        (VariableChange.scaling _
          (unitOfInvertible (LaurentPolynomial.T (w : ℤ) : LaurentPolynomial B))⁻¹)⁻¹ := by
  rw [← _root_.map_inv]
  ext
  · simp [VariableChange.mul_def, toPolynomial_of_mem hu]
  · simp [VariableChange.mul_def, toPolynomial_of_mem hr, Polynomial.toLaurent_C_mul_T,
      LaurentPolynomial.T_pow, mul_comm (2 : ℤ)]
  · simp [VariableChange.mul_def, toPolynomial_of_mem hs, Polynomial.toLaurent_C_mul_T,
      mul_comm (LaurentPolynomial.T _) (LaurentPolynomial.C _)]
  · simp [VariableChange.mul_def, toPolynomial_of_mem ht, Polynomial.toLaurent_C_mul_T,
      LaurentPolynomial.T_pow, mul_comm (3 : ℤ)]

end WeierstrassCurve

namespace TauCeti.WeierstrassHopfAlgebroid

open MvPolynomial _root_.WeierstrassCurve

/-! ### Grading on `A = ℤ[a₁, a₂, a₃, a₄, a₆]` -/

/-- The homological degree `2 * i` of the Weierstrass coefficient `aᵢ` (`2, 4, 6, 8, 12`). -/
def baseDegree (i : Coeff) : ℕ := 2 * coefficientWeight i

@[simp] theorem baseDegree_apply (i : Coeff) : baseDegree i = 2 * coefficientWeight i := (rfl)

/-- The even homological grading on `A = ℤ[a₁, a₂, a₃, a₄, a₆]`, placing `aᵢ` in degree `2i`. -/
def baseGrading (n : ℕ) : Submodule ℤ (MvPolynomial Coeff ℤ) :=
  weightedHomogeneousSubmodule ℤ baseDegree n

/-- Definitional characterization of `baseGrading` as the weighted homogeneous submodule for
`baseDegree`. -/
theorem baseGrading_def (n : ℕ) :
    baseGrading n = weightedHomogeneousSubmodule ℤ baseDegree n := (rfl)

/-- Membership in `baseGrading n` is weighted homogeneity of degree `n` for `baseDegree`. -/
theorem mem_baseGrading_iff {n : ℕ} {p : MvPolynomial Coeff ℤ} :
    p ∈ baseGrading n ↔ p.IsWeightedHomogeneous baseDegree n :=
  mem_weightedHomogeneousSubmodule ℤ baseDegree n p

/-- The Weierstrass coefficient generator `X i` has homological degree `2 * coefficientWeight i`. -/
@[simp] theorem X_mem_baseGrading (i : Coeff) : X i ∈ baseGrading (2 * coefficientWeight i) :=
  isWeightedHomogeneous_X ℤ baseDegree i

-- Marked `@[no_expose]` so `baseGrading` stays unexposed while reusing `weightedGradedAlgebra`.
/-- The ring `A = ℤ[a₁, ⋯, a₆]` is graded by even homological degrees `|aᵢ| = 2i`. -/
@[no_expose] instance : GradedAlgebra baseGrading := MvPolynomial.weightedGradedAlgebra ℤ baseDegree

/-- Membership in `baseGrading (2 * k)` is weighted homogeneity of modular weight `k`. -/
theorem mem_baseGrading_two_mul_iff {k : ℕ} {p : MvPolynomial Coeff ℤ} :
    p ∈ baseGrading (2 * k) ↔ p.IsWeightedHomogeneous coefficientWeight k :=
  isWeightedHomogeneous_smul_weight_iff (s := (2 : ℕ)) (mul_right_injective₀ two_ne_zero)

/-- Every odd-degree graded piece of `A = ℤ[a₁, ⋯, a₆]` vanishes. -/
theorem baseGrading_eq_bot_of_odd {n : ℕ} (hn : Odd n) : baseGrading n = ⊥ :=
  WeightedHomogeneousSubmodule.eq_bot_of_odd (fun _ ↦ even_two_mul _) hn

/-- A ring homomorphism out of `A = ℤ[a₁, ⋯, a₆]` is graded (with degree shift `e`) iff it sends
each Weierstrass coefficient generator `X i` into degree `e (2 * coefficientWeight i)`. -/
theorem baseGrading_map_mem_iff {C₀ σ ι : Type*} [CommRing C₀] [SetLike σ C₀]
    [AddSubgroupClass σ C₀] [AddCommMonoid ι] (𝒜 : ι → σ) [SetLike.GradedMonoid 𝒜] (e : ℕ →+ ι)
    (f : MvPolynomial Coeff ℤ →+* C₀) :
    (∀ ⦃n⦄ ⦃p⦄, p ∈ baseGrading n → f p ∈ 𝒜 (e n)) ↔
      ∀ i : Coeff, f (X i) ∈ 𝒜 (e (2 * coefficientWeight i)) :=
  WeightedHomogeneousSubmodule.map_mem_iff baseDegree 𝒜 e f

/-! ### Grading on `A[r, s, t]` (`StrictArrowRing`) -/

/-- The homological degrees `2 * strictWeight i` of the generators of `A[r, s, t]`: `2i` on `aᵢ`
and `4, 2, 6` on `r, s, t`. -/
def strictDegree (i : Coeff ⊕ Fin 3) : ℕ := 2 * strictWeight i

@[simp] theorem strictDegree_inl (i : Coeff) : strictDegree (.inl i) = 2 * coefficientWeight i := by
  simp [strictDegree]
@[simp] theorem strictDegree_inr_zero : strictDegree (.inr 0) = 4 := by simp [strictDegree]
@[simp] theorem strictDegree_inr_one : strictDegree (.inr 1) = 2 := by simp [strictDegree]
@[simp] theorem strictDegree_inr_two : strictDegree (.inr 2) = 6 := by simp [strictDegree]

/-- The even homological grading on `A[r, s, t]`, placing `aᵢ` in degree `2i` and `r, s, t` in
degrees `4, 2, 6`. -/
def strictArrowGrading (n : ℕ) : Submodule ℤ StrictArrowRing :=
  weightedHomogeneousSubmodule ℤ strictDegree n

/-- Definitional characterization of `strictArrowGrading` as the weighted homogeneous submodule for
`strictDegree`. -/
theorem strictArrowGrading_def (n : ℕ) :
    strictArrowGrading n = weightedHomogeneousSubmodule ℤ strictDegree n := (rfl)

/-- Membership in `strictArrowGrading n` is weighted homogeneity of degree `n` for
`strictDegree`. -/
theorem mem_strictArrowGrading_iff {n : ℕ} {x : StrictArrowRing} :
    x ∈ strictArrowGrading n ↔ x.IsWeightedHomogeneous strictDegree n :=
  mem_weightedHomogeneousSubmodule ℤ strictDegree n x

-- Marked `@[no_expose]` so `strictArrowGrading` stays unexposed.
/-- The strict arrow ring `A[r, s, t]` is graded by even homological degrees. -/
@[no_expose] instance : GradedAlgebra strictArrowGrading :=
  MvPolynomial.weightedGradedAlgebra ℤ strictDegree

/-- Membership in `strictArrowGrading (2 * k)` is weighted homogeneity of weight `k` for
`strictWeight`. -/
theorem mem_strictArrowGrading_two_mul_iff {k : ℕ} {x : StrictArrowRing} :
    x ∈ strictArrowGrading (2 * k) ↔ x.IsWeightedHomogeneous strictWeight k :=
  isWeightedHomogeneous_smul_weight_iff (s := (2 : ℕ)) (mul_right_injective₀ two_ne_zero)

/-- Every generator `X i` of `A[r, s, t]` has homological degree `strictDegree i`. -/
theorem X_mem_strictArrowGrading (i : Coeff ⊕ Fin 3) :
    X i ∈ strictArrowGrading (strictDegree i) :=
  isWeightedHomogeneous_X ℤ strictDegree i

@[simp] theorem X_inl_mem_strictArrowGrading (i : Coeff) :
    X (.inl i) ∈ strictArrowGrading (2 * coefficientWeight i) := by
  simpa using X_mem_strictArrowGrading (.inl i)
@[simp] theorem X_inr_zero_mem_strictArrowGrading : X (.inr 0) ∈ strictArrowGrading 4 := by
  simpa using X_mem_strictArrowGrading (.inr 0)
@[simp] theorem X_inr_one_mem_strictArrowGrading : X (.inr 1) ∈ strictArrowGrading 2 := by
  simpa using X_mem_strictArrowGrading (.inr 1)
@[simp] theorem X_inr_two_mem_strictArrowGrading : X (.inr 2) ∈ strictArrowGrading 6 := by
  simpa using X_mem_strictArrowGrading (.inr 2)

/-- Every odd-degree graded piece of `A[r, s, t]` vanishes. -/
theorem strictArrowGrading_eq_bot_of_odd {n : ℕ} (hn : Odd n) : strictArrowGrading n = ⊥ :=
  WeightedHomogeneousSubmodule.eq_bot_of_odd (fun _ ↦ even_two_mul _) hn

/-- A ring homomorphism out of `A[r, s, t]` is graded (with degree shift `e`) iff it sends each
generator `X i` into `𝒜 (e (strictDegree i))`. -/
theorem strictArrowGrading_map_mem_iff {C₀ σ ι : Type*} [CommRing C₀] [SetLike σ C₀]
    [AddSubgroupClass σ C₀] [AddCommMonoid ι] (𝒜 : ι → σ) [SetLike.GradedMonoid 𝒜] (e : ℕ →+ ι)
    (f : StrictArrowRing →+* C₀) :
    (∀ ⦃n⦄ ⦃x⦄, x ∈ strictArrowGrading n → f x ∈ 𝒜 (e n)) ↔
      ∀ i : Coeff ⊕ Fin 3, f (X i) ∈ 𝒜 (e (strictDegree i)) :=
  WeightedHomogeneousSubmodule.map_mem_iff strictDegree 𝒜 e f

/-- The strict counit preserves homological degrees. -/
theorem strictCounit_mem_baseGrading {n : ℕ} {x : StrictArrowRing} (hx : x ∈ strictArrowGrading n) :
    strictCounit x ∈ baseGrading n :=
  IsWeightedHomogeneous.map_smul_weight (2 : ℕ) isWeightedHomogeneous_strictCounit hx

/-- The strict left unit preserves homological degrees. -/
theorem strictLeftUnit_mem_strictArrowGrading {n : ℕ} {p : MvPolynomial Coeff ℤ}
    (hp : p ∈ baseGrading n) : strictLeftUnit p ∈ strictArrowGrading n :=
  IsWeightedHomogeneous.map_smul_weight (2 : ℕ) isWeightedHomogeneous_strictLeftUnit hp

/-- The strict left unit preserves and reflects homological degrees. -/
@[simp] theorem strictLeftUnit_mem_strictArrowGrading_iff {n : ℕ} {p : MvPolynomial Coeff ℤ} :
    strictLeftUnit p ∈ strictArrowGrading n ↔ p ∈ baseGrading n :=
  ⟨fun hx ↦ by simpa using strictCounit_mem_baseGrading hx, strictLeftUnit_mem_strictArrowGrading⟩

/-- The strict right unit preserves homological degrees. -/
theorem strictRightUnit_mem_strictArrowGrading {n : ℕ} {p : MvPolynomial Coeff ℤ}
    (hp : p ∈ baseGrading n) : strictRightUnit p ∈ strictArrowGrading n :=
  IsWeightedHomogeneous.map_smul_weight (2 : ℕ) isWeightedHomogeneous_strictRightUnit hp

/-- The strict right unit preserves and reflects homological degrees. -/
@[simp] theorem strictRightUnit_mem_strictArrowGrading_iff {n : ℕ} {p : MvPolynomial Coeff ℤ} :
    strictRightUnit p ∈ strictArrowGrading n ↔ p ∈ baseGrading n :=
  ⟨fun hx ↦ by simpa using strictCounit_mem_baseGrading hx, strictRightUnit_mem_strictArrowGrading⟩

/-- The strict conjugation preserves homological degrees. -/
theorem strictConjugation_mem_strictArrowGrading {n : ℕ} {x : StrictArrowRing}
    (hx : x ∈ strictArrowGrading n) : strictConjugation x ∈ strictArrowGrading n :=
  IsWeightedHomogeneous.map_smul_weight (2 : ℕ) isWeightedHomogeneous_strictConjugation hx

/-- The strict conjugation preserves and reflects homological degrees. -/
@[simp] theorem strictConjugation_mem_strictArrowGrading_iff {n : ℕ} {x : StrictArrowRing} :
    strictConjugation x ∈ strictArrowGrading n ↔ x ∈ strictArrowGrading n :=
  ⟨fun hx ↦ by simpa using strictConjugation_mem_strictArrowGrading hx,
    strictConjugation_mem_strictArrowGrading⟩

/-! ### Grading on `A[r, s, t] ⊗_A A[r, s, t]` (`StrictPairRing`) and the coproduct -/

/-- The homological degrees `2 * strictPairWeight i` on `A[r, s, t] ⊗_A A[r, s, t]`: `2i` on `aᵢ`
and `4, 2, 6` on both `r₁, s₁, t₁` and `r₂, s₂, t₂`. -/
def strictPairDegree (i : Coeff ⊕ (Fin 3 ⊕ Fin 3)) : ℕ := 2 * strictPairWeight i

@[simp] theorem strictPairDegree_inl (i : Coeff) :
    strictPairDegree (.inl i) = 2 * coefficientWeight i := by simp [strictPairDegree]
@[simp] theorem strictPairDegree_inr_inl (j : Fin 3) :
    strictPairDegree (.inr (.inl j)) = strictDegree (.inr j) := by
  simp [strictPairDegree, strictDegree]
@[simp] theorem strictPairDegree_inr_inr (j : Fin 3) :
    strictPairDegree (.inr (.inr j)) = strictDegree (.inr j) := by
  simp [strictPairDegree, strictDegree]

/-- The even homological grading on `A[r, s, t] ⊗_A A[r, s, t]`. -/
def strictPairGrading (n : ℕ) : Submodule ℤ StrictPairRing :=
  weightedHomogeneousSubmodule ℤ strictPairDegree n

/-- Definitional characterization of `strictPairGrading` as the weighted homogeneous submodule for
`strictPairDegree`. -/
theorem strictPairGrading_def (n : ℕ) :
    strictPairGrading n = weightedHomogeneousSubmodule ℤ strictPairDegree n := (rfl)

/-- Membership in `strictPairGrading n` is weighted homogeneity of degree `n` for
`strictPairDegree`. -/
theorem mem_strictPairGrading_iff {n : ℕ} {x : StrictPairRing} :
    x ∈ strictPairGrading n ↔ x.IsWeightedHomogeneous strictPairDegree n :=
  mem_weightedHomogeneousSubmodule ℤ strictPairDegree n x

-- Marked `@[no_expose]` so `strictPairGrading` stays unexposed.
/-- The composable-pair ring `A[r, s, t] ⊗_A A[r, s, t]` is graded by even homological degrees. -/
@[no_expose] instance : GradedAlgebra strictPairGrading :=
  MvPolynomial.weightedGradedAlgebra ℤ strictPairDegree

/-- Membership in `strictPairGrading (2 * k)` is weighted homogeneity of weight `k` for
`strictPairWeight`. -/
theorem mem_strictPairGrading_two_mul_iff {k : ℕ} {x : StrictPairRing} :
    x ∈ strictPairGrading (2 * k) ↔ x.IsWeightedHomogeneous strictPairWeight k :=
  isWeightedHomogeneous_smul_weight_iff (s := (2 : ℕ)) (mul_right_injective₀ two_ne_zero)

/-- Every generator `X i` of `A[r, s, t] ⊗_A A[r, s, t]` has degree `strictPairDegree i`. -/
theorem X_mem_strictPairGrading (i : Coeff ⊕ (Fin 3 ⊕ Fin 3)) :
    X i ∈ strictPairGrading (strictPairDegree i) :=
  isWeightedHomogeneous_X ℤ strictPairDegree i

/-- Every odd-degree graded piece of `A[r, s, t] ⊗_A A[r, s, t]` vanishes. -/
theorem strictPairGrading_eq_bot_of_odd {n : ℕ} (hn : Odd n) : strictPairGrading n = ⊥ :=
  WeightedHomogeneousSubmodule.eq_bot_of_odd (fun _ ↦ even_two_mul _) hn

/-- A ring homomorphism out of `A[r, s, t] ⊗_A A[r, s, t]` is graded (with degree shift `e`) iff
it sends each generator `X i` into `𝒜 (e (strictPairDegree i))`. -/
theorem strictPairGrading_map_mem_iff {C₀ σ ι : Type*} [CommRing C₀] [SetLike σ C₀]
    [AddSubgroupClass σ C₀] [AddCommMonoid ι] (𝒜 : ι → σ) [SetLike.GradedMonoid 𝒜] (e : ℕ →+ ι)
    (f : StrictPairRing →+* C₀) :
    (∀ ⦃n⦄ ⦃x⦄, x ∈ strictPairGrading n → f x ∈ 𝒜 (e n)) ↔
      ∀ i : Coeff ⊕ (Fin 3 ⊕ Fin 3), f (X i) ∈ 𝒜 (e (strictPairDegree i)) :=
  WeightedHomogeneousSubmodule.map_mem_iff strictPairDegree 𝒜 e f

/-- The left-factor counit `strictCounitLeft` preserves homological degrees. -/
theorem strictCounitLeft_mem_strictArrowGrading {n : ℕ} {x : StrictPairRing}
    (hx : x ∈ strictPairGrading n) : strictCounitLeft x ∈ strictArrowGrading n := by
  refine (strictPairGrading_map_mem_iff strictArrowGrading (.id ℕ) strictCounitLeft).mpr
    (fun i ↦ ?_) hx
  rcases i with i | (j | j)
  · simp
  · simp [zero_mem]
  · simpa using X_mem_strictArrowGrading (.inr j)

/-- The right-factor counit `strictCounitRight` preserves homological degrees. -/
theorem strictCounitRight_mem_strictArrowGrading {n : ℕ} {x : StrictPairRing}
    (hx : x ∈ strictPairGrading n) : strictCounitRight x ∈ strictArrowGrading n := by
  refine (strictPairGrading_map_mem_iff strictArrowGrading (.id ℕ) strictCounitRight).mpr
    (fun i ↦ ?_) hx
  rcases i with i | (j | j)
  · simp
  · simpa using X_mem_strictArrowGrading (.inr j)
  · simp [zero_mem]

/-- The left factor `strictLeft` preserves homological degrees. -/
theorem strictLeft_mem_strictPairGrading {n : ℕ} {x : StrictArrowRing}
    (hx : x ∈ strictArrowGrading n) : strictLeft x ∈ strictPairGrading n := by
  refine (strictArrowGrading_map_mem_iff strictPairGrading (.id ℕ) strictLeft).mpr
    (fun i ↦ ?_) hx
  rcases i with i | j
  · simpa using X_mem_strictPairGrading (.inl i)
  · simpa using X_mem_strictPairGrading (.inr (.inl j))

/-- `strictLeft` preserves and reflects homological degrees. -/
@[simp] theorem strictLeft_mem_strictPairGrading_iff {n : ℕ} {x : StrictArrowRing} :
    strictLeft x ∈ strictPairGrading n ↔ x ∈ strictArrowGrading n :=
  ⟨fun hx ↦ by simpa only [← RingHom.comp_apply, strictCounitRight_comp_strictLeft,
      RingHom.id_apply] using strictCounitRight_mem_strictArrowGrading hx,
    strictLeft_mem_strictPairGrading⟩

/-- The right factor `strictRight` preserves homological degrees. -/
theorem strictRight_mem_strictPairGrading {n : ℕ} {x : StrictArrowRing}
    (hx : x ∈ strictArrowGrading n) : strictRight x ∈ strictPairGrading n := by
  refine (strictArrowGrading_map_mem_iff strictPairGrading (.id ℕ) strictRight).mpr
    (fun i ↦ ?_) hx
  rcases i with i | j
  · simp
  · simpa using X_mem_strictPairGrading (.inr (.inr j))

/-- `strictRight` preserves and reflects homological degrees. -/
@[simp] theorem strictRight_mem_strictPairGrading_iff {n : ℕ} {x : StrictArrowRing} :
    strictRight x ∈ strictPairGrading n ↔ x ∈ strictArrowGrading n :=
  ⟨fun hx ↦ by simpa only [← RingHom.comp_apply, strictCounitLeft_comp_strictRight,
      RingHom.id_apply] using strictCounitLeft_mem_strictArrowGrading hx,
    strictRight_mem_strictPairGrading⟩

/-- The strict coproduct preserves homological degrees. -/
theorem strictCoproduct_mem_strictPairGrading {n : ℕ} {x : StrictArrowRing}
    (hx : x ∈ strictArrowGrading n) : strictCoproduct x ∈ strictPairGrading n :=
  IsWeightedHomogeneous.map_smul_weight (2 : ℕ) isWeightedHomogeneous_strictCoproduct hx

/-- The strict coproduct preserves and reflects homological degrees. -/
@[simp] theorem strictCoproduct_mem_strictPairGrading_iff {n : ℕ} {x : StrictArrowRing} :
    strictCoproduct x ∈ strictPairGrading n ↔ x ∈ strictArrowGrading n :=
  ⟨fun hx ↦ by simpa only [← RingHom.comp_apply, strictCounitLeft_comp_strictCoproduct,
      RingHom.id_apply] using strictCounitLeft_mem_strictArrowGrading hx,
    strictCoproduct_mem_strictPairGrading⟩

end TauCeti.WeierstrassHopfAlgebroid
