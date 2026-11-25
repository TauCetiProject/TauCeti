/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.RingTheory.TwoSidedIdeal.Basic
public import TauCeti.Analysis.CStarAlgebra.TracialFunctional

/-!
# Traces on C⋆-algebras and their square-integrable ideal

A **trace** on a C⋆-algebra `B` is a map `τ : B → ℝ≥0∞`, of which only the values on the
positive cone `B₊` matter, that is additive and positively homogeneous on `B₊` (with `0 · ∞ = 0`)
and satisfies `τ(x⋆x) = τ(xx⋆)` for every `x ∈ B` (Dixmier 1963, Définition 2, p. 224). This is
`TauCeti.IsTrace`. A trace is faithful (`TauCeti.IsFaithfulTrace`) if a positive element of trace
zero is zero.

The **finite part** `𝔪_τ⁺ = {x ∈ B₊ : τ(x) < ∞}` (`TauCeti.finitePart`) is a hereditary
convex cone, since a trace is monotone on `B₊`. The **square-integrable elements**
`𝔫_τ = {x : τ(x⋆x) < ∞}` (`TauCeti.sqIntegrable`) form a self-adjoint two-sided ideal
(`TauCeti.IsTrace.sqIntegrableIdeal`, Dixmier 1963, Lemme 3, p. 226): it is a left ideal
because `x⋆a⋆ax ≤ ‖a⋆a‖ x⋆x`, it is closed under addition because
`(x + y)⋆(x + y) ≤ (x + y)⋆(x + y) + (x - y)⋆(x - y) = 2(x⋆x + y⋆y)`, it is self-adjoint by the
trace identity, and so it is also a right ideal.

Traces are stable under the zero map, sums, multiples by `c ∈ [0, ∞]`, and pullback along a
star homomorphism, which preserves faithfulness for injective homomorphisms. A positive tracial
functional (`TauCeti.PositiveTracialFunctional`) defines a trace
(`TauCeti.PositiveTracialFunctional.isTrace_toTrace`) that is finite everywhere
(`TauCeti.PositiveTracialFunctional.toTrace_lt_top`).

## Main definitions

* `TauCeti.IsTrace`: traces `B → ℝ≥0∞`.
* `TauCeti.IsFaithfulTrace`: faithful traces.
* `TauCeti.finitePart`: the finite part `𝔪_τ⁺`.
* `TauCeti.sqIntegrable`: the square-integrable elements `𝔫_τ`.
* `TauCeti.IsTrace.sqIntegrableIdeal`: `𝔫_τ` as a two-sided ideal.
* `TauCeti.PositiveTracialFunctional.toTrace`: the trace of a positive tracial functional.

## Main results

* `TauCeti.IsTrace.map_zero`, `TauCeti.IsTrace.mono`: `τ(0) = 0` and monotonicity on `B₊`.
* `TauCeti.IsTrace.mem_finitePart_of_le`, `TauCeti.IsTrace.add_mem_finitePart`,
  `TauCeti.IsTrace.smul_mem_finitePart`: `𝔪_τ⁺` is a hereditary convex cone.
* `TauCeti.IsTrace.star_mem_sqIntegrable`, `TauCeti.IsTrace.smul_mem_sqIntegrable`: `𝔫_τ` is
  self-adjoint and a complex subspace.
* `TauCeti.IsTrace.comp`, `TauCeti.IsFaithfulTrace.comp`: pullback along star homomorphisms.
* `TauCeti.PositiveTracialFunctional.isTrace_toTrace`,
  `TauCeti.PositiveTracialFunctional.toTrace_lt_top`: a positive tracial functional is a trace
  that is finite everywhere.

## References

* Jacques Dixmier, *Traces sur les C*-algèbres*, Ann. Inst. Fourier (Grenoble) 13 (1963),
  219–262. Chapitre I: Définition 2, p. 224; Lemme 3, p. 226.
-/

public section

open scoped ENNReal NNReal ComplexOrder

namespace TauCeti

variable {A B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

/-- A **trace** on a C⋆-algebra `B`: a map `τ : B → ℝ≥0∞`, of which only the values on `B₊`
matter, additive and positively homogeneous on `B₊` and satisfying `τ(x⋆x) = τ(xx⋆)`
(Dixmier 1963, Définition 2, p. 224). -/
structure IsTrace (τ : B → ℝ≥0∞) : Prop where
  /-- Additivity on the positive cone. -/
  map_add_of_nonneg ⦃x y : B⦄ : 0 ≤ x → 0 ≤ y → τ (x + y) = τ x + τ y
  /-- Positive homogeneity on the positive cone, with `0 · ∞ = 0`. -/
  map_nnreal_smul_of_nonneg (c : ℝ≥0) ⦃x : B⦄ : 0 ≤ x → τ ((c : ℝ) • x) = c * τ x
  /-- The trace identity. -/
  map_star_mul_self (x : B) : τ (star x * x) = τ (x * star x)

variable {τ : B → ℝ≥0∞}

/-- A trace is **faithful** if a positive element of trace zero is zero. -/
def IsFaithfulTrace (τ : B → ℝ≥0∞) : Prop :=
  ∀ ⦃x : B⦄, 0 ≤ x → τ x = 0 → x = 0

omit [StarOrderedRing B] in
/-- Unfolds `IsFaithfulTrace`. -/
theorem isFaithfulTrace_iff : IsFaithfulTrace τ ↔ ∀ ⦃x : B⦄, 0 ≤ x → τ x = 0 → x = 0 :=
  Iff.rfl

omit [StarOrderedRing B] in
/-- A positive element of trace zero under a faithful trace is zero. -/
theorem IsFaithfulTrace.eq_zero (hτ : IsFaithfulTrace τ) {x : B} (hx : 0 ≤ x) (h0 : τ x = 0) :
    x = 0 :=
  hτ hx h0

/-- The **finite part** `𝔪_τ⁺ = {x ∈ B₊ : τ(x) < ∞}` of a trace. -/
def finitePart (τ : B → ℝ≥0∞) : Set B :=
  {x | 0 ≤ x ∧ τ x < ∞}

omit [StarOrderedRing B] in
/-- Membership in `𝔪_τ⁺`. -/
@[simp]
theorem mem_finitePart {x : B} : x ∈ finitePart τ ↔ 0 ≤ x ∧ τ x < ∞ :=
  Iff.rfl

/-- The **square-integrable elements** `𝔫_τ = {x : τ(x⋆x) < ∞}` of a trace. -/
def sqIntegrable (τ : B → ℝ≥0∞) : Set B :=
  {x | τ (star x * x) < ∞}

omit [PartialOrder B] [StarOrderedRing B] in
/-- Membership in `𝔫_τ`. -/
@[simp]
theorem mem_sqIntegrable {x : B} : x ∈ sqIntegrable τ ↔ τ (star x * x) < ∞ :=
  Iff.rfl

omit [PartialOrder B] [StarOrderedRing B] in
/-- `|c|² x⋆x = (cx)⋆(cx)` for a complex scalar `c`. -/
private theorem star_smul_mul_smul (c : ℂ) (x : B) :
    star (c • x) * (c • x) = ((‖c‖₊ ^ 2 : ℝ≥0) : ℝ) • (star x * x) := by
  simp [star_smul, smul_mul_smul_comm, Complex.conj_mul', ← Complex.coe_smul]

namespace IsTrace

omit [StarOrderedRing B] in
/-- A trace vanishes at `0`. -/
theorem map_zero (hτ : IsTrace τ) : τ 0 = 0 := by
  simpa using hτ.map_nnreal_smul_of_nonneg 0 le_rfl

/-- A trace is monotone on the positive cone. -/
theorem mono (hτ : IsTrace τ) {x y : B} (hy : 0 ≤ y) (hyx : y ≤ x) : τ y ≤ τ x := by
  rw [← add_sub_cancel y x, hτ.map_add_of_nonneg hy (sub_nonneg.mpr hyx)]
  exact le_self_add

/-- The finite part is hereditary: `0 ≤ y ≤ x ∈ 𝔪_τ⁺` gives `y ∈ 𝔪_τ⁺`. -/
theorem mem_finitePart_of_le (hτ : IsTrace τ) {x y : B} (hx : x ∈ finitePart τ) (hy : 0 ≤ y)
    (hyx : y ≤ x) : y ∈ finitePart τ :=
  ⟨hy, (hτ.mono hy hyx).trans_lt hx.2⟩

/-- `𝔪_τ⁺` is closed under addition. -/
theorem add_mem_finitePart (hτ : IsTrace τ) {x y : B} (hx : x ∈ finitePart τ)
    (hy : y ∈ finitePart τ) : x + y ∈ finitePart τ :=
  ⟨add_nonneg hx.1 hy.1, by
    rw [hτ.map_add_of_nonneg hx.1 hy.1]
    exact ENNReal.add_lt_top.mpr ⟨hx.2, hy.2⟩⟩

/-- `𝔪_τ⁺` is closed under multiplication by nonnegative reals. -/
theorem smul_mem_finitePart (hτ : IsTrace τ) (c : ℝ≥0) {x : B} (hx : x ∈ finitePart τ) :
    (c : ℝ) • x ∈ finitePart τ :=
  ⟨smul_nonneg c.property hx.1, by
    rw [hτ.map_nnreal_smul_of_nonneg c hx.1]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top hx.2⟩

omit [StarOrderedRing B] in
/-- `0 ∈ 𝔪_τ⁺`. -/
theorem zero_mem_finitePart (hτ : IsTrace τ) : (0 : B) ∈ finitePart τ :=
  ⟨le_rfl, by simp [hτ.map_zero]⟩

/-! ### The square-integrable ideal -/

/-- The parallelogram bound `τ((x + y)⋆(x + y)) ≤ 2 (τ(x⋆x) + τ(y⋆y))`, written as
`(τ(x⋆x) + τ(y⋆y)) + (τ(x⋆x) + τ(y⋆y))`. -/
theorem map_star_add_mul_add_le (hτ : IsTrace τ) (x y : B) :
    τ (star (x + y) * (x + y)) ≤
      (τ (star x * x) + τ (star y * y)) + (τ (star x * x) + τ (star y * y)) := by
  have hz : 0 ≤ star x * x + star y * y := add_nonneg (star_mul_self_nonneg x)
    (star_mul_self_nonneg y)
  have hpar : star (x + y) * (x + y) + star (x - y) * (x - y) =
      (star x * x + star y * y) + (star x * x + star y * y) := by
    simp only [star_add, star_sub, add_mul, sub_mul, mul_add, mul_sub]
    abel
  rw [← hτ.map_add_of_nonneg (star_mul_self_nonneg x) (star_mul_self_nonneg y),
    ← hτ.map_add_of_nonneg hz hz, ← hpar, hτ.map_add_of_nonneg (star_mul_self_nonneg _)
    (star_mul_self_nonneg _)]
  exact le_self_add

/-- Left multiplication: `τ((ax)⋆(ax)) ≤ ‖a⋆a‖ τ(x⋆x)`. -/
theorem map_star_mul_mul_le (hτ : IsTrace τ) (a x : B) :
    τ (star (a * x) * (a * x)) ≤ ‖star a * a‖₊ * τ (star x * x) := by
  rw [← hτ.map_nnreal_smul_of_nonneg _ (star_mul_self_nonneg x)]
  refine hτ.mono (star_mul_self_nonneg _) ?_
  rw [coe_nnNorm, star_mul, mul_assoc, ← mul_assoc (star a), ← mul_assoc]
  exact CStarAlgebra.star_left_conjugate_le_norm_smul x (star a * a)

omit [StarOrderedRing B] in
/-- The trace identity applied to `x⋆`: `τ((x⋆)⋆x⋆) = τ(x⋆x)`. -/
theorem map_star_star_mul_star (hτ : IsTrace τ) (x : B) :
    τ (star (star x) * star x) = τ (star x * x) := by
  rw [star_star, hτ.map_star_mul_self]

omit [StarOrderedRing B] in
/-- `𝔫_τ` is self-adjoint. -/
theorem star_mem_sqIntegrable (hτ : IsTrace τ) {x : B} (hx : x ∈ sqIntegrable τ) :
    star x ∈ sqIntegrable τ := by
  rwa [mem_sqIntegrable, hτ.map_star_star_mul_star]

/-- `𝔫_τ` is closed under multiplication by complex scalars. -/
theorem smul_mem_sqIntegrable (hτ : IsTrace τ) (c : ℂ) {x : B} (hx : x ∈ sqIntegrable τ) :
    c • x ∈ sqIntegrable τ := by
  rw [mem_sqIntegrable, star_smul_mul_smul,
    hτ.map_nnreal_smul_of_nonneg _ (star_mul_self_nonneg x)]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top hx

/-- The square-integrable elements `𝔫_τ` of a trace as a two-sided ideal
(Dixmier 1963, Lemme 3, p. 226). -/
def sqIntegrableIdeal (hτ : IsTrace τ) : TwoSidedIdeal B :=
  .mk' (sqIntegrable τ)
    (by simp [hτ.map_zero])
    (fun {x y} hx hy ↦ (hτ.map_star_add_mul_add_le x y).trans_lt <| by
      rw [mem_sqIntegrable] at hx hy
      simp [ENNReal.add_lt_top, hx, hy])
    (fun {x} hx ↦ by simpa using hx)
    (fun {a x} hx ↦ (hτ.map_star_mul_mul_le a x).trans_lt
      (ENNReal.mul_lt_top ENNReal.coe_lt_top hx))
    (fun {x a} hx ↦ by
      have h := hτ.map_star_mul_mul_le (star a) (star x)
      rw [← star_mul, star_star] at h
      rw [mem_sqIntegrable, hτ.map_star_mul_self]
      exact h.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top (hτ.star_mem_sqIntegrable hx)))

/-- The carrier of `hτ.sqIntegrableIdeal` is `𝔫_τ`. -/
@[simp]
theorem coe_sqIntegrableIdeal (hτ : IsTrace τ) : (hτ.sqIntegrableIdeal : Set B) = sqIntegrable τ :=
  Set.ext fun _ ↦ TwoSidedIdeal.mem_mk' ..

/-- Membership in `hτ.sqIntegrableIdeal` is membership in `𝔫_τ`. -/
@[simp]
theorem mem_sqIntegrableIdeal (hτ : IsTrace τ) {x : B} :
    x ∈ hτ.sqIntegrableIdeal ↔ x ∈ sqIntegrable τ :=
  TwoSidedIdeal.mem_mk' ..

/-! ### Constructions -/

omit [StarOrderedRing B] in
/-- The zero map is a trace. -/
protected theorem zero : IsTrace (0 : B → ℝ≥0∞) :=
  ⟨by simp, by simp, by simp⟩

omit [StarOrderedRing B] in
/-- The sum of two traces is a trace. -/
protected theorem add {σ : B → ℝ≥0∞} (hτ : IsTrace τ) (hσ : IsTrace σ) : IsTrace (τ + σ) where
  map_add_of_nonneg x y hx hy := by
    simp only [Pi.add_apply, hτ.map_add_of_nonneg hx hy, hσ.map_add_of_nonneg hx hy]
    ring
  map_nnreal_smul_of_nonneg c x hx := by
    simp [hτ.map_nnreal_smul_of_nonneg c hx, hσ.map_nnreal_smul_of_nonneg c hx, mul_add]
  map_star_mul_self x := by simp [hτ.map_star_mul_self, hσ.map_star_mul_self]

omit [StarOrderedRing B] in
/-- A multiple `c τ` of a trace by `c ∈ [0, ∞]` is a trace. -/
protected theorem const_mul (hτ : IsTrace τ) (c : ℝ≥0∞) : IsTrace fun x ↦ c * τ x where
  map_add_of_nonneg x y hx hy := by rw [hτ.map_add_of_nonneg hx hy, mul_add]
  map_nnreal_smul_of_nonneg d x hx := by rw [hτ.map_nnreal_smul_of_nonneg d hx, mul_left_comm]
  map_star_mul_self x := by rw [hτ.map_star_mul_self]

end IsTrace

variable [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  {F : Type*} [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

/-- The pullback `τ ∘ φ` of a trace along a star homomorphism is a trace. -/
protected theorem IsTrace.comp (hτ : IsTrace τ) (φ : F) : IsTrace (τ ∘ φ) where
  map_add_of_nonneg x y hx hy := by
    simp only [Function.comp_apply, map_add]
    exact hτ.map_add_of_nonneg (map_nonneg φ hx) (map_nonneg φ hy)
  map_nnreal_smul_of_nonneg c x hx := by
    simp only [Function.comp_apply]
    rw [← Complex.coe_smul, map_smul, Complex.coe_smul,
      hτ.map_nnreal_smul_of_nonneg c (map_nonneg φ hx)]
  map_star_mul_self x := by
    simp only [Function.comp_apply, map_mul, map_star, hτ.map_star_mul_self]

/-- The pullback of a faithful trace along an injective star homomorphism is faithful. -/
theorem IsFaithfulTrace.comp (hτ : IsFaithfulTrace τ) {φ : F} (hφ : Function.Injective φ) :
    IsFaithfulTrace (τ ∘ φ) := fun x hx h0 ↦
  hφ <| by simpa using hτ (map_nonneg φ hx) h0

/-! ### Bounded traces -/

namespace PositiveTracialFunctional

/-- The trace `x ↦ Re ω(x)` of a positive tracial functional `ω`, finite everywhere. -/
noncomputable def toTrace (ω : PositiveTracialFunctional B) : B → ℝ≥0∞ :=
  fun x ↦ ENNReal.ofReal (ω x).re

/-- The value of `ω.toTrace`. -/
@[simp]
theorem toTrace_apply (ω : PositiveTracialFunctional B) (x : B) :
    ω.toTrace x = ENNReal.ofReal (ω x).re :=
  (rfl)

/-- The trace of a positive tracial functional is finite everywhere. -/
theorem toTrace_lt_top (ω : PositiveTracialFunctional B) (x : B) : ω.toTrace x < ∞ :=
  ENNReal.ofReal_lt_top

/-- A positive tracial functional is a trace. -/
theorem isTrace_toTrace (ω : PositiveTracialFunctional B) : IsTrace ω.toTrace where
  map_add_of_nonneg x y hx hy := by
    simp only [toTrace_apply, map_add, Complex.add_re]
    exact ENNReal.ofReal_add (Complex.nonneg_iff.mp (map_nonneg ω hx)).1
      (Complex.nonneg_iff.mp (map_nonneg ω hy)).1
  map_nnreal_smul_of_nonneg c x _ := by
    simp [← Complex.coe_smul, ENNReal.ofReal_mul]
  map_star_mul_self x := by simp only [toTrace_apply, map_mul_comm]

end PositiveTracialFunctional

end TauCeti
