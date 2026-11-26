/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Semisimple
public import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RepresentationTheory.Submodule
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Algebra.GroupWithZero
import TauCeti.LinearAlgebra.Pi
import TauCeti.LinearAlgebra.Trace.Idempotent
import TauCeti.RepresentationTheory.Semisimple

/-!
# Rank-two representations from a trace with an odd involution

A function `T : G → K` on a monoid behaves like the character of a rank-two representation when
`T 1 = 2` and `T` satisfies the polarized Cayley–Hamilton identity of `2 × 2` matrices in three
variables. Such a function need not be the character of a representation over `K` itself. This file
shows that it is when `2 ≠ 0` in `K` and some involution `c ∈ G` has `T c = 0`, and that the
representation is then unique among semisimple ones. For Galois pseudocharacters `c` is a complex
conjugation, and this is how an odd rank-two pseudocharacter with values in a field is realized by a
representation over that same field.

## Main results

* `TauCeti.exists_isSemisimpleRepresentation_character_eq_of_odd_involution`: a rank-two trace
  with an odd involution is the character of a semisimple representation on `K²`.
* `TauCeti.exists_continuous_isSemisimpleRepresentation_character_eq_of_odd_involution`: if the
  trace is moreover continuous, the representation can be taken with continuous matrix entries.
* `Representation.nonempty_equiv_of_character_eq_of_odd_involution`: two semisimple
  representations on planes with the same character, vanishing at an involution, are equivalent.

## Implementation notes

Extend `T` linearly to a trace form `τ` on the monoid algebra `K[G]` and let `e = (1 + c) / 2`, an
idempotent with `τ e = 1`. The trace identity gives `τ (e y e w) = τ (e y) τ (e w)`, and the same
for `1 - e`. So `a y = τ (e y)` and `d y = τ ((1 - e) y)` behave as the diagonal entries of a
matrix, and `x y z = τ (e y (1 - e) z)` as the product of an upper-right and a lower-left entry;
this pairing has rank at most one. Normalizing by one nonzero value `x y₀ z₀`, or taking the
diagonal matrices when `x` vanishes, gives an algebra map `K[G] → M₂(K)` with trace `τ`.

Conversely, `e` acts on a representation with this character as an idempotent of trace one, that is,
as `diag(1, 0)` in a suitable basis. In that basis the diagonal entries are `a` and `d` and the
products of the off-diagonal entries are given by `x`. When `x` is nonzero this determines the
matrices up to conjugation by `diag(1, t)`; when `x` vanishes, semisimplicity forces both
off-diagonal entries to vanish.

## References

* A. Wiles, *On ordinary λ-adic representations associated to modular forms*, Invent. Math. 94
  (1988), §2.2.
* L. Pan, *The Fontaine–Mazur conjecture in the residually reducible case*, J. Amer. Math. Soc. 35
  (2022), §§2.1.1–2.1.6.
-/

open scoped MonoidAlgebra Matrix
open Module

namespace TauCeti

section TraceAlgebra

variable {K A : Type*} [Field K] [Ring A] [Algebra K A]

/-- A linear form `τ` on an algebra satisfying the identities of the trace of a rank-two
representation: `τ 1 = 2`, `τ (u v) = τ (v u)`, and the polarized Cayley–Hamilton identity. -/
private structure IsRankTwoTrace (τ : A →ₗ[K] K) : Prop where
  map_one : τ 1 = 2
  comm : ∀ u v, τ (u * v) = τ (v * u)
  identity : ∀ u v w, τ (u * v * w) + τ (u * w * v) - τ (u * w) * τ v - τ (w * v) * τ u -
      τ (v * u) * τ w + τ u * τ v * τ w = 0

namespace IsRankTwoTrace

variable {τ : A →ₗ[K] K} (hτ : IsRankTwoTrace τ)
include hτ

/-- Cyclic invariance of `τ`, with both sides given up to reassociation. -/
private lemma cyc (p q : A) {s r : A} (hs : s = p * q) (hr : q * p = r) : τ s = τ r := by
  rw [hs, hτ.comm, hr]

/-- For an idempotent `f` of trace one, `f A f` is the line `K f` modulo the kernel of the trace
pairing: `τ (f y f w) = τ (f y) τ (f w)`. -/
private lemma trace_mul_idem {f : A} (hf : IsIdempotentElem f) (hf1 : τ f = 1) (y w : A) :
    τ (f * y * f * w) = τ (f * y) * τ (f * w) := by
  set z := f * y * f with hz
  have hfz : f * z = z := by rw [hz, ← mul_assoc, ← mul_assoc, hf.eq]
  have hzf : z * f = z := by rw [hz, mul_assoc, hf.eq]
  have h := hτ.identity f z w
  have h1 : τ (f * w * z) = τ (z * w) := by rw [hτ.comm, ← mul_assoc, hzf]
  have h3 : τ z = τ (f * y) := by rw [hz, hτ.comm, ← mul_assoc, hf.eq]
  rw [hfz, h1, hτ.comm w z, hzf, hf1] at h
  rw [← h3]
  linear_combination h

private lemma trace_one_sub {e : A} (he1 : τ e = 1) : τ (1 - e) = 1 := by
  rw [map_sub, hτ.map_one, he1]; norm_num

variable {e : A} (he : IsIdempotentElem e) (he1 : τ e = 1)
include he he1

/-- `trace_mul_idem` for the complementary idempotent `1 - e`. -/
private lemma trace_mul_idem' (y w : A) :
    τ ((1 - e) * y * (1 - e) * w) = τ ((1 - e) * y) * τ ((1 - e) * w) :=
  hτ.trace_mul_idem he.one_sub (hτ.trace_one_sub he1) y w

private lemma trace_mul_mul (y z : A) :
    τ (e * (y * z)) = τ (e * y) * τ (e * z) + τ (e * y * (1 - e) * z) := by
  rw [show e * (y * z) = e * y * e * z + e * y * (1 - e) * z by noncomm_ring, map_add,
    hτ.trace_mul_idem he he1]

private lemma trace_one_sub_mul_mul (y z : A) :
    τ ((1 - e) * (y * z)) = τ (e * z * (1 - e) * y) + τ ((1 - e) * y) * τ ((1 - e) * z) := by
  have h : τ ((1 - e) * y * e * z) = τ (e * z * (1 - e) * y) :=
    hτ.cyc ((1 - e) * y) (e * z) (by noncomm_ring) (by noncomm_ring)
  rw [show (1 - e) * (y * z) = (1 - e) * y * (1 - e) * z + (1 - e) * y * e * z by
      noncomm_ring, map_add, hτ.trace_mul_idem' he he1, h]
  ring

private lemma trace_offDiag_mul_left (y z z₀ : A) :
    τ (e * (y * z) * (1 - e) * z₀) =
      τ (e * y) * τ (e * z * (1 - e) * z₀) + τ (e * y * (1 - e) * z₀) * τ ((1 - e) * z) := by
  have h₁ := hτ.trace_mul_idem he he1 y (z * (1 - e) * z₀)
  have h₂ := hτ.trace_mul_idem' he he1 z (z₀ * e * y)
  have h₃ : τ (e * y * (1 - e) * z * (1 - e) * z₀) =
      τ ((1 - e) * z * (1 - e) * (z₀ * e * y)) :=
    hτ.cyc (e * y) ((1 - e) * z * (1 - e) * z₀) (by noncomm_ring) (by noncomm_ring)
  have h₄ : τ ((1 - e) * (z₀ * e * y)) = τ (e * y * (1 - e) * z₀) :=
    hτ.cyc ((1 - e) * z₀) (e * y) (by noncomm_ring) (by noncomm_ring)
  have h₅ : e * (z * (1 - e) * z₀) = e * z * (1 - e) * z₀ := by noncomm_ring
  rw [show e * (y * z) * (1 - e) * z₀ = e * y * e * (z * (1 - e) * z₀) +
      e * y * (1 - e) * z * (1 - e) * z₀ by noncomm_ring, map_add, h₁, h₃, h₂, h₄, h₅]
  ring

private lemma trace_offDiag_mul_right (y₀ y z : A) :
    τ (e * y₀ * (1 - e) * (y * z)) =
      τ (e * y₀ * (1 - e) * y) * τ (e * z) + τ ((1 - e) * y) * τ (e * y₀ * (1 - e) * z) := by
  have h₁ : τ (e * y₀ * (1 - e) * y * e * z) = τ (e * z * e * (y₀ * (1 - e) * y)) :=
    hτ.cyc (e * y₀ * (1 - e) * y) (e * z) (by noncomm_ring) (by noncomm_ring)
  have h₂ := hτ.trace_mul_idem he he1 z (y₀ * (1 - e) * y)
  have h₃ : τ (e * y₀ * (1 - e) * y * (1 - e) * z) =
      τ ((1 - e) * y * (1 - e) * (z * e * y₀)) :=
    hτ.cyc (e * y₀) ((1 - e) * y * (1 - e) * z) (by noncomm_ring) (by noncomm_ring)
  have h₄ := hτ.trace_mul_idem' he he1 y (z * e * y₀)
  have h₅ : τ ((1 - e) * (z * e * y₀)) = τ (e * y₀ * (1 - e) * z) :=
    hτ.cyc ((1 - e) * z) (e * y₀) (by noncomm_ring) (by noncomm_ring)
  have h₆ : e * (y₀ * (1 - e) * y) = e * y₀ * (1 - e) * y := by noncomm_ring
  rw [show e * y₀ * (1 - e) * (y * z) = e * y₀ * (1 - e) * y * e * z +
      e * y₀ * (1 - e) * y * (1 - e) * z by noncomm_ring, map_add, h₁, h₂, h₃, h₄, h₅, h₆]
  ring

/-- The off-diagonal pairing `x y z = τ (e y (1 - e) z)` has rank at most one. -/
private lemma trace_offDiag_mul_trace_offDiag (y z y₀ z₀ : A) :
    τ (e * y * (1 - e) * z) * τ (e * y₀ * (1 - e) * z₀) =
      τ (e * y * (1 - e) * z₀) * τ (e * y₀ * (1 - e) * z) := by
  have h₁ := hτ.trace_mul_idem he he1 (y * (1 - e) * z₀) (y₀ * (1 - e) * z)
  have h₂ := hτ.trace_mul_idem' he he1 (z₀ * e * y₀) (z * e * y)
  have h₃ : τ ((1 - e) * (z₀ * e * y₀) * (1 - e) * (z * e * y)) =
      τ (e * (y * (1 - e) * z₀) * e * (y₀ * (1 - e) * z)) :=
    hτ.cyc ((1 - e) * (z₀ * e * y₀) * (1 - e) * z) (e * y) (by noncomm_ring) (by noncomm_ring)
  have h₄ : τ ((1 - e) * (z₀ * e * y₀)) = τ (e * y₀ * (1 - e) * z₀) :=
    hτ.cyc ((1 - e) * z₀) (e * y₀) (by noncomm_ring) (by noncomm_ring)
  have h₅ : τ ((1 - e) * (z * e * y)) = τ (e * y * (1 - e) * z) :=
    hτ.cyc ((1 - e) * z) (e * y) (by noncomm_ring) (by noncomm_ring)
  have h₆ : e * (y * (1 - e) * z₀) = e * y * (1 - e) * z₀ := by noncomm_ring
  have h₇ : e * (y₀ * (1 - e) * z) = e * y₀ * (1 - e) * z := by noncomm_ring
  rw [h₃, h₁, h₄, h₅, h₆, h₇] at h₂
  linear_combination -h₂

omit hτ he1 in
private lemma trace_offDiag_one_left (z : A) : τ (e * (1 - e) * z) = 0 := by
  rw [mul_sub, mul_one, he.eq, sub_self, zero_mul, map_zero]

omit he1 in
private lemma trace_offDiag_one_right (y : A) : τ (e * y * (1 - e)) = 0 := by
  rw [hτ.cyc (e * y) (1 - e) (r := 0) (by noncomm_ring) (by
    rw [← mul_assoc, sub_mul, one_mul, he.eq, sub_self, zero_mul]), map_zero]

/-- The matrix entries `x y z₀ / x y₀ z₀` and `x y₀ z` multiply to `x y z`, when either
`x y₀ z₀ ≠ 0` or the pairing `x` vanishes. -/
private lemma div_mul_trace_offDiag {y₀ z₀ : A} (hx : τ (e * y₀ * (1 - e) * z₀) ≠ 0 ∨
    ∀ y z, τ (e * y * (1 - e) * z) = 0) (y z : A) :
    τ (e * y * (1 - e) * z₀) / τ (e * y₀ * (1 - e) * z₀) * τ (e * y₀ * (1 - e) * z) =
      τ (e * y * (1 - e) * z) := by
  rcases hx with hx | hx
  · rw [div_mul_eq_mul_div, div_eq_iff hx, ← hτ.trace_offDiag_mul_trace_offDiag he he1]
  · simp [hx]

/-- The matrix model: `u ↦ !![τ (e u), x u z₀ / x y₀ z₀; x y₀ u, τ ((1 - e) u)]`. -/
private noncomputable def model {y₀ z₀ : A} (hx : τ (e * y₀ * (1 - e) * z₀) ≠ 0 ∨
    ∀ y z, τ (e * y * (1 - e) * z) = 0) : A →ₐ[K] Matrix (Fin 2) (Fin 2) K :=
  AlgHom.ofLinearMap
    { toFun u := !![τ (e * u), τ (e * u * (1 - e) * z₀) / τ (e * y₀ * (1 - e) * z₀);
        τ (e * y₀ * (1 - e) * u), τ ((1 - e) * u)]
      map_add' u v := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [mul_add, add_mul, add_div]
      map_smul' r u := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [mul_div_assoc] }
    (by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [hτ.trace_one_sub he1, he1, trace_offDiag_one_left he,
          hτ.trace_offDiag_one_right he])
    (fun y z => by
      have h := hτ.div_mul_trace_offDiag he he1 hx
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, hτ.trace_mul_mul he he1,
          hτ.trace_offDiag_mul_left he he1, hτ.trace_offDiag_mul_right he he1,
          hτ.trace_one_sub_mul_mul he he1, ← h y z, ← h z y] <;>
        ring)

private lemma model_apply {y₀ z₀ : A} (hx : τ (e * y₀ * (1 - e) * z₀) ≠ 0 ∨
    ∀ y z, τ (e * y * (1 - e) * z) = 0) (u : A) :
    model hτ he he1 hx u = !![τ (e * u), τ (e * u * (1 - e) * z₀) / τ (e * y₀ * (1 - e) * z₀);
        τ (e * y₀ * (1 - e) * u), τ ((1 - e) * u)] := rfl

private lemma trace_model {y₀ z₀ : A} (hx : τ (e * y₀ * (1 - e) * z₀) ≠ 0 ∨
    ∀ y z, τ (e * y * (1 - e) * z) = 0) (u : A) : (model hτ he he1 hx u).trace = τ u := by
  rw [model_apply, Matrix.trace_fin_two_of, sub_mul, one_mul, map_sub]
  ring

private lemma model_idem {y₀ z₀ : A} (hx : τ (e * y₀ * (1 - e) * z₀) ≠ 0 ∨
    ∀ y z, τ (e * y * (1 - e) * z) = 0) : model hτ he he1 hx e = !![1, 0; 0, 0] := by
  have h₁ : e * y₀ * (1 - e) * e = 0 := by
    rw [mul_assoc, sub_mul, one_mul, he.eq, sub_self, mul_zero]
  have h₂ : (1 - e) * e = 0 := by rw [sub_mul, one_mul, he.eq, sub_self]
  rw [model_apply, he.eq, he1, trace_offDiag_one_left he, h₁, h₂]
  simp

/-- The two off-diagonal entries of the model vanish identically together. -/
private lemma model_offDiag_iff {y₀ z₀ : A} (hx : τ (e * y₀ * (1 - e) * z₀) ≠ 0 ∨
    ∀ y z, τ (e * y * (1 - e) * z) = 0) :
    (∀ u, model hτ he he1 hx u 0 1 = 0) ↔ ∀ u, model hτ he he1 hx u 1 0 = 0 := by
  have hzero : τ (e * y₀ * (1 - e) * z₀) = 0 → ∀ y z, τ (e * y * (1 - e) * z) = 0 :=
    fun h => hx.resolve_left (not_not.mpr h)
  constructor
  · intro h u
    simpa [model_apply] using hzero (by simpa [model_apply] using h y₀) y₀ u
  · intro h u
    simp [model_apply, hzero (by simpa [model_apply] using h z₀)]

end IsRankTwoTrace

end TraceAlgebra

section Group

variable {K G : Type*} [Field K] [Monoid G]

/-- The `K`-linear extension of a function `T : G → K` to the monoid algebra. -/
private noncomputable def traceLin (T : G → K) : K[G] →ₗ[K] K :=
  (Finsupp.linearCombination K T).comp (MonoidAlgebra.coeffLinearEquiv K).toLinearMap

omit [Monoid G] in
private lemma traceLin_apply (T : G → K) (u : K[G]) :
    traceLin T u = Finsupp.linearCombination K T u.coeff := rfl

omit [Monoid G] in
private lemma traceLin_single (T : G → K) (g : G) (r : K) :
    traceLin T (MonoidAlgebra.single g r) = r * T g := by
  rw [traceLin_apply, MonoidAlgebra.coeff_single, Finsupp.linearCombination_single, smul_eq_mul]

private lemma traceLin_of (T : G → K) (g : G) : traceLin T (MonoidAlgebra.of K G g) = T g := by
  rw [MonoidAlgebra.of_apply, traceLin_single, one_mul]

/-- The rank-two trace identities of `T` on `G` extend to its linearization on `K[G]`. -/
private lemma isRankTwoTrace_traceLin {T : G → K} (h_one : T 1 = 2)
    (h_comm : ∀ g h : G, T (g * h) = T (h * g))
    (h_trace : ∀ g h k : G,
      T (g * h * k) + T (g * k * h) - T (g * k) * T h - T (k * h) * T g -
        T (h * g) * T k + T g * T h * T k = 0) :
    IsRankTwoTrace (traceLin T) where
  map_one := by rw [MonoidAlgebra.one_def, traceLin_single, one_mul, h_one]
  comm u v := by
    induction u using MonoidAlgebra.induction_linear with
    | zero => simp
    | add u₁ u₂ h₁ h₂ => simp [add_mul, mul_add, h₁, h₂]
    | single g r =>
      induction v using MonoidAlgebra.induction_linear with
      | zero => simp
      | add v₁ v₂ h₁ h₂ => simp [add_mul, mul_add, h₁, h₂]
      | single h s => simp [MonoidAlgebra.single_mul_single, traceLin_single, h_comm g h, mul_comm]
  identity u v w := by
    induction u using MonoidAlgebra.induction_linear with
    | zero => simp
    | add u₁ u₂ h₁ h₂ => simp only [add_mul, mul_add, map_add]; linear_combination h₁ + h₂
    | single g r =>
      induction v using MonoidAlgebra.induction_linear with
      | zero => simp
      | add v₁ v₂ h₁ h₂ => simp only [add_mul, mul_add, map_add]; linear_combination h₁ + h₂
      | single h s =>
        induction w using MonoidAlgebra.induction_linear with
        | zero => simp
        | add w₁ w₂ h₁ h₂ => simp only [add_mul, mul_add, map_add]; linear_combination h₁ + h₂
        | single k t =>
          simp only [MonoidAlgebra.single_mul_single, traceLin_single]
          linear_combination (r * s * t) * h_trace g h k

/-- The idempotent `(1 + c) / 2` of `K[G]` attached to an involution `c`. -/
private noncomputable def halfOnePlus (c : G) : K[G] := (2 : K)⁻¹ • (1 + MonoidAlgebra.of K G c)

private lemma isIdempotentElem_halfOnePlus (h2 : (2 : K) ≠ 0) {c : G} (hc : c * c = 1) :
    IsIdempotentElem (halfOnePlus (K := K) c) := by
  have hcc : MonoidAlgebra.of K G c * MonoidAlgebra.of K G c = 1 := by
    rw [← map_mul, hc, map_one]
  have hsq : (1 + MonoidAlgebra.of K G c) * (1 + MonoidAlgebra.of K G c) =
      (2 : K) • (1 + MonoidAlgebra.of K G c) := by
    rw [two_smul]
    simp only [mul_add, add_mul, one_mul, mul_one, hcc]
    abel
  rw [IsIdempotentElem, halfOnePlus, smul_mul_smul_comm, hsq, smul_smul]
  congr 1
  field_simp

private lemma traceLin_halfOnePlus {T : G → K} (h2 : (2 : K) ≠ 0) (h_one : T 1 = 2) {c : G}
    (h_odd : T c = 0) : traceLin T (halfOnePlus c) = 1 := by
  simp [halfOnePlus, MonoidAlgebra.one_def, traceLin_single, h_one, h_odd, h2]

private lemma continuous_traceLin_mul_of_mul [TopologicalSpace G] [ContinuousMul G]
    [TopologicalSpace K] [IsTopologicalSemiring K] {T : G → K} (hT : Continuous T)
    (u v : K[G]) : Continuous fun g => traceLin T (u * MonoidAlgebra.of K G g * v) := by
  induction u using MonoidAlgebra.induction_linear with
  | zero => simpa using continuous_const
  | add u₁ u₂ h₁ h₂ => simp only [add_mul, map_add]; exact h₁.add h₂
  | single h r =>
    induction v using MonoidAlgebra.induction_linear with
    | zero => simpa using continuous_const
    | add v₁ v₂ h₁ h₂ => simp only [mul_add, map_add]; exact h₁.add h₂
    | single k s =>
      simp only [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, traceLin_single,
        mul_one]
      exact continuous_const.mul
        (hT.comp ((continuous_const.mul continuous_id).mul continuous_const))

/-- A subrepresentation is stable under the action of the monoid algebra. -/
private lemma asAlgebraHom_mem {V : Type*} [AddCommGroup V] [Module K V]
    {ρ : Representation K G V} (W : Subrepresentation ρ) {v : V} (hv : v ∈ W.toSubmodule)
    (u : K[G]) : ρ.asAlgebraHom u v ∈ W.toSubmodule :=
  ρ.asAlgebraHom_mem_of_forall_mem W.toSubmodule (fun g _ hv => W.apply_mem_toSubmodule g hv) v
    hv u

/-- A representation on `K²` whose group-algebra action is given by matrices `N u`, in which some
`q` acts as the projection `diag(1, 0)`, and whose two off-diagonal entries vanish identically
together, is semisimple. -/
private lemma isSemisimpleRepresentation_of_offDiag {ρ : Representation K G (Fin 2 → K)}
    {N : K[G] →ₐ[K] Matrix (Fin 2) (Fin 2) K}
    (hN : ∀ u v, ρ.asAlgebraHom u v = N u *ᵥ v) {q : K[G]} (hq : N q = !![1, 0; 0, 0])
    (hsym : (∀ u, N u 0 1 = 0) ↔ ∀ u, N u 1 0 = 0) : ρ.IsSemisimpleRepresentation := by
  have hmem (W : Subrepresentation ρ) {v : Fin 2 → K} (hv : v ∈ W.toSubmodule) (u : K[G]) :
      N u *ᵥ v ∈ W.toSubmodule :=
    hN u v ▸ asAlgebraHom_mem W hv u
  have hproj (i : Fin 2) : ∃ q, N q = Matrix.single i i 1 := by
    fin_cases i
    · exact ⟨q, by rw [hq]; ext j k; fin_cases j <;> fin_cases k <;> simp⟩
    · exact ⟨1 - q, by rw [map_sub, map_one, hq]; ext j k; fin_cases j <;> fin_cases k <;> simp⟩
  -- A subrepresentation with a vector of nonzero `i`-th coordinate contains `e_i`.
  have hsingle (W : Subrepresentation ρ) (i : Fin 2) (hi : ∃ w ∈ W.toSubmodule, w i ≠ 0) :
      Pi.single i 1 ∈ W.toSubmodule := by
    obtain ⟨w, hw, hwi⟩ := hi
    obtain ⟨q, hq⟩ := hproj i
    have := W.toSubmodule.smul_mem (w i)⁻¹ (hmem W hw q)
    rwa [hq, Matrix.single_mulVec, one_mul, ← Pi.single, ← Pi.single_smul, smul_eq_mul,
      inv_mul_cancel₀ hwi] at this
  -- If `e_i ∈ W` while no vector of `W` has a nonzero `j`-th coordinate, then the `(j, i)` entry
  -- vanishes, and by `hsym` so does the `(i, j)` entry.
  have hoff (W : Subrepresentation ρ) {i j : Fin 2} (hij : i ≠ j)
      (hi : ∃ w ∈ W.toSubmodule, w i ≠ 0) (hj : ¬ ∃ w ∈ W.toSubmodule, w j ≠ 0) (u : K[G]) :
      N u i j = 0 := by
    have hji (u : K[G]) : N u j i = 0 := by_contra fun hne => hj
      ⟨_, hmem W (hsingle W i hi) u, by rwa [Matrix.mulVec_single_one, Matrix.col_apply]⟩
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hsym.mpr hji u
    · exact hsym.mp hji u
    · exact absurd rfl hij
  -- A complement of `W` is the subspace of vectors vanishing where some vector of `W` does not.
  refine ⟨fun W => ⟨⟨Submodule.pi {i | ∃ w ∈ W.toSubmodule, w i ≠ 0} fun _ => ⊥,
    fun g v hv => Submodule.mem_pi.mpr fun i hi => (Submodule.mem_bot K).mpr ?_⟩,
    Subrepresentation.isCompl_toSubmodule.mp
      (Submodule.isCompl_pi_bot_of_single_mem (hsingle W))⟩⟩
  -- This complement is stable: write the `i`-th coordinate of `ρ g v` over `i` and `j`.
  rw [← Representation.asAlgebraHom_of, hN, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hv' (k : Fin 2) (hk : ∃ w ∈ W.toSubmodule, w k ≠ 0) : v k = 0 :=
    (Submodule.mem_bot K).mp (Submodule.mem_pi.mp hv k hk)
  fin_cases i
  · by_cases h₁ : ∃ w ∈ W.toSubmodule, w 1 ≠ 0
    · simp [hv' 0 hi, hv' 1 h₁]
    · simp [hv' 0 hi, hoff W (i := 0) (j := 1) (by decide) hi h₁]
  · by_cases h₀ : ∃ w ∈ W.toSubmodule, w 0 ≠ 0
    · simp [hv' 0 h₀, hv' 1 hi]
    · simp [hv' 1 hi, hoff W (i := 1) (j := 0) (by decide) hi h₀]

private lemma trace_asAlgebraHom_halfOnePlus {V : Type*} [AddCommGroup V] [Module K V]
    {ρ : Representation K G V} (h2 : (2 : K) ≠ 0) (hV : finrank K V = 2) {c : G}
    (h_odd : ρ.character c = 0) :
    LinearMap.trace K V (ρ.asAlgebraHom (halfOnePlus c)) = 1 := by
  have := Module.finite_of_finrank_eq_succ hV
  rw [Representation.character] at h_odd
  simp [halfOnePlus, hV, h2, h_odd]

variable {V : Type*} [AddCommGroup V] [Module K V]

/-- In a basis adapted to the idempotent `e`, the diagonal entries of the matrices of a
representation and the products of their off-diagonal entries are traces. -/
private lemma toMatrix_entries {ρ : Representation K G V} (b : Basis (Fin 2) K V)
    {e : K[G]} (hb : LinearMap.toMatrix b b (ρ.asAlgebraHom e) = !![1, 0; 0, 0])
    (y z : K[G]) :
    LinearMap.toMatrix b b (ρ.asAlgebraHom y) 0 0 =
        LinearMap.trace K V (ρ.asAlgebraHom (e * y)) ∧
      LinearMap.toMatrix b b (ρ.asAlgebraHom y) 1 1 =
        LinearMap.trace K V (ρ.asAlgebraHom ((1 - e) * y)) ∧
      LinearMap.toMatrix b b (ρ.asAlgebraHom y) 0 1 *
          LinearMap.toMatrix b b (ρ.asAlgebraHom z) 1 0 =
        LinearMap.trace K V (ρ.asAlgebraHom (e * y * (1 - e) * z)) := by
  simp only [LinearMap.trace_eq_matrix_trace K b, map_mul, LinearMap.toMatrix_mul, map_sub,
    map_one, LinearMap.toMatrix_one, hb]
  rw [Matrix.eta_fin_two (LinearMap.toMatrix b b (ρ.asAlgebraHom y)),
    Matrix.eta_fin_two (LinearMap.toMatrix b b (ρ.asAlgebraHom z))]
  simp [Matrix.one_fin_two, Matrix.trace_fin_two]

/-- A vector of a plane is the sum of its two coordinates along a basis. -/
private lemma repr_smul_add_repr_smul (b : Basis (Fin 2) K V) {i j : Fin 2} (hij : i ≠ j)
    (v : V) : b.repr v i • b i + b.repr v j • b j = v := by
  conv_rhs => rw [← b.sum_repr v, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · rfl
  · exact add_comm _ _
  · exact absurd rfl hij

/-- A complement of the line through `b i` on which the `i`-th coordinate vanishes contains
`b j`. -/
private lemma mem_of_isCompl_span_singleton (b : Basis (Fin 2) K V) {i j : Fin 2} (hij : i ≠ j)
    {W : Submodule K V} (hW : IsCompl (K ∙ b i) W) (hWi : ∀ w ∈ W, b.repr w i = 0) : b j ∈ W := by
  obtain ⟨w, hw, hw0⟩ : ∃ w ∈ W, w ≠ 0 := by
    rw [← Submodule.ne_bot_iff]
    rintro rfl
    have htop := hW.sup_eq_top
    rw [sup_bot_eq] at htop
    have hjL : b j ∈ K ∙ b i := htop ▸ Submodule.mem_top
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hjL
    simpa [hij] using congrArg (fun v => b.repr v j) hr
  have hw' := repr_smul_add_repr_smul b hij w
  rw [hWi w hw, zero_smul, zero_add] at hw'
  set r := b.repr w j
  have hr : r ≠ 0 := fun h0 => hw0 (by rw [← hw', h0, zero_smul])
  have := W.smul_mem r⁻¹ hw
  rwa [← hw', smul_smul, inv_mul_cancel₀ hr, one_smul] at this

/-- In a semisimple representation on a plane with basis `b`, if some `q` acts as the projection
onto `b i` along `b j` and the line through `b i` is stable, then so is the line through `b j`. -/
private lemma toMatrix_offDiag_eq_zero {ρ : Representation K G V}
    [ρ.IsSemisimpleRepresentation] (b : Basis (Fin 2) K V) {i j : Fin 2} (hij : i ≠ j)
    {q : K[G]} (hq : LinearMap.toMatrix b b (ρ.asAlgebraHom q) = Matrix.single i i 1)
    (h : ∀ u, LinearMap.toMatrix b b (ρ.asAlgebraHom u) j i = 0) (u : K[G]) :
    LinearMap.toMatrix b b (ρ.asAlgebraHom u) i j = 0 := by
  have hexp (u : K[G]) (k : Fin 2) : ρ.asAlgebraHom u (b k) =
      LinearMap.toMatrix b b (ρ.asAlgebraHom u) i k • b i +
        LinearMap.toMatrix b b (ρ.asAlgebraHom u) j k • b j := by
    rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
      repr_smul_add_repr_smul b hij]
  have hline {r : K} : r • b i ∈ K ∙ b i :=
    Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  -- The line `L` through `b i` is a subrepresentation; let `W` be a complement.
  have hL (g : G) : ∃ t : K, ρ g (b i) = t • b i :=
    ⟨_, by rw [← Representation.asAlgebraHom_of, hexp, h, zero_smul, add_zero]⟩
  obtain ⟨W, hLW⟩ := exists_isCompl (Subrepresentation.spanSingleton (b i) hL)
  have hLW' : IsCompl (K ∙ b i) W.toSubmodule := by
    rw [← Subrepresentation.toSubmodule_spanSingleton (b i) hL]
    exact Subrepresentation.isCompl_toSubmodule.mpr hLW
  have hsmul {r : K} (hr : r • b i ∈ W) : r = 0 :=
    (smul_eq_zero.mp (Submodule.disjoint_def.mp hLW'.disjoint _ hline hr)).resolve_right
      (b.ne_zero i)
  -- `q` projects `W` into `L ⊓ W = 0`, so `W` is the line through `b j`.
  have hbj : b j ∈ W := mem_of_isCompl_span_singleton b hij hLW' fun w hw => hsmul <| by
    have hq' : ρ.asAlgebraHom q w = b.repr w i • b i := by
      conv_lhs => rw [← repr_smul_add_repr_smul b hij w]
      rw [map_add, map_smul, map_smul, hexp, hexp, hq]
      simp [hij]
    exact hq' ▸ asAlgebraHom_mem W hw q
  apply hsmul
  have := W.toSubmodule.sub_mem (asAlgebraHom_mem W hbj u)
    (W.toSubmodule.smul_mem (LinearMap.toMatrix b b (ρ.asAlgebraHom u) j j) hbj)
  rwa [hexp, add_sub_cancel_right] at this

/-- Two representations on planes are equivalent when, in some bases, the matrices of the second
are those of the first conjugated by `diag(1, t)` with `t ≠ 0`. -/
private lemma nonempty_equiv_of_toMatrix {W : Type*} [AddCommGroup W] [Module K W]
    {ρ : Representation K G V} {σ : Representation K G W} (b₁ : Basis (Fin 2) K V)
    (b₂ : Basis (Fin 2) K W) {N₁ N₂ : K[G] → Matrix (Fin 2) (Fin 2) K}
    (hN₁ : ∀ u, LinearMap.toMatrix b₁ b₁ (ρ.asAlgebraHom u) = N₁ u)
    (hN₂ : ∀ u, LinearMap.toMatrix b₂ b₂ (σ.asAlgebraHom u) = N₂ u) {t : K} (ht : t ≠ 0)
    (h₀₀ : ∀ u, N₁ u 0 0 = N₂ u 0 0) (h₁₁ : ∀ u, N₁ u 1 1 = N₂ u 1 1)
    (h₀₁ : ∀ u, N₁ u 0 1 = N₂ u 0 1 * t) (h₁₀ : ∀ u, t * N₁ u 1 0 = N₂ u 1 0) :
    Nonempty (ρ.Equiv σ) := by
  set D : Matrix (Fin 2) (Fin 2) K := !![1, 0; 0, t]
  let := D.invertibleOfIsUnitDet (isUnit_iff_ne_zero.mpr (by simpa [D] using ht))
  have hD (g : G) : D * LinearMap.toMatrix b₁ b₁ (ρ g) =
      LinearMap.toMatrix b₂ b₂ (σ g) * D := by
    rw [← Representation.asAlgebraHom_of, ← Representation.asAlgebraHom_of, hN₁, hN₂,
      Matrix.eta_fin_two (N₁ _), Matrix.eta_fin_two (N₂ _)]
    simp only [D, Matrix.mul_fin_two, one_mul, zero_mul, add_zero, zero_add, mul_one, mul_zero]
    rw [h₀₀, h₁₁, h₀₁, h₁₀, mul_comm t]
  let φ : V ≃ₗ[K] W := b₁.equivFun ≪≫ₗ D.toLinearEquiv' ‹_› ≪≫ₗ b₂.equivFun.symm
  refine ⟨Representation.Equiv.mk φ fun g => ?_⟩
  ext v
  apply b₂.equivFun.injective
  have h₁ := LinearMap.toMatrix_mulVec_repr b₁ b₁ (ρ g) v
  have h₂ := LinearMap.toMatrix_mulVec_repr b₂ b₂ (σ g) (φ v)
  have hφ (v : V) : ⇑(b₂.repr (φ v)) = D *ᵥ ⇑(b₁.repr v) := by
    rw [← Basis.equivFun_apply, ← Basis.equivFun_apply]
    simp only [φ, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rw [← LinearEquiv.coe_coe, Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Basis.equivFun_apply]
  rw [hφ, ← h₂, hφ, ← h₁, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  exact congrArg (· *ᵥ _) (hD g)

/-- In a semisimple representation on a plane, in a basis adapted to the idempotent `e`, if the
off-diagonal entries pair to zero then both vanish. -/
private lemma diagonal_of_offDiag_mul_eq_zero {ρ : Representation K G V}
    [ρ.IsSemisimpleRepresentation] (b : Basis (Fin 2) K V) {e : K[G]}
    (hb : LinearMap.toMatrix b b (ρ.asAlgebraHom e) = !![1, 0; 0, 0])
    (hzero : ∀ y z, LinearMap.toMatrix b b (ρ.asAlgebraHom y) 0 1 *
      LinearMap.toMatrix b b (ρ.asAlgebraHom z) 1 0 = 0) (u : K[G]) :
    LinearMap.toMatrix b b (ρ.asAlgebraHom u) 0 1 = 0 ∧
      LinearMap.toMatrix b b (ρ.asAlgebraHom u) 1 0 = 0 := by
  have hb₀ : LinearMap.toMatrix b b (ρ.asAlgebraHom e) = Matrix.single 0 0 1 := by
    rw [hb]; ext i j; fin_cases i <;> fin_cases j <;> simp
  have hb₁ : LinearMap.toMatrix b b (ρ.asAlgebraHom (1 - e)) = Matrix.single 1 1 1 := by
    rw [map_sub, map_one, map_sub, LinearMap.toMatrix_one, hb]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  by_cases h₀₁ : ∀ y, LinearMap.toMatrix b b (ρ.asAlgebraHom y) 0 1 = 0
  · exact ⟨h₀₁ u, toMatrix_offDiag_eq_zero b (by decide) hb₁ h₀₁ u⟩
  · push Not at h₀₁
    obtain ⟨y, hy⟩ := h₀₁
    have h₁₀ (z : K[G]) : LinearMap.toMatrix b b (ρ.asAlgebraHom z) 1 0 = 0 :=
      (mul_eq_zero.mp (hzero y z)).resolve_left hy
    exact ⟨toMatrix_offDiag_eq_zero b (by decide) hb₀ h₁₀ u, h₁₀ u⟩

/-- The representation built from the matrix model: a rank-two trace with an odd involution is the
character of a semisimple representation on `K²`, each of whose matrix entries is
`g ↦ τ (u g v) * r` for the linear extension `τ` of `T` and some `u v : K[G]`, `r : K`. -/
private lemma exists_isSemisimpleRepresentation_character_eq_traceLin (h2 : (2 : K) ≠ 0)
    (T : G → K) (h_one : T 1 = 2)
    (h_trace : ∀ g h k : G,
      T (g * h * k) + T (g * k * h) - T (g * k) * T h - T (k * h) * T g -
        T (h * g) * T k + T g * T h * T k = 0)
    {c : G} (hc : c * c = 1) (h_odd : T c = 0) :
    ∃ ρ : Representation K G (Fin 2 → K), ρ.IsSemisimpleRepresentation ∧ ρ.character = T ∧
      ∀ i j : Fin 2, ∃ (u v : K[G]) (r : K),
        ∀ g, ρ g (Pi.single j 1) i = traceLin T (u * MonoidAlgebra.of K G g * v) * r := by
  have h_comm (g h : G) : T (g * h) = T (h * g) := by
    have := h_trace g h 1
    rw [mul_one, mul_one, one_mul, h_one] at this
    exact mul_left_cancel₀ h2 (by linear_combination this)
  have hτ := isRankTwoTrace_traceLin h_one h_comm h_trace
  have he := isIdempotentElem_halfOnePlus (K := K) h2 hc
  have he1 := traceLin_halfOnePlus h2 h_one h_odd
  set τ := traceLin T
  set e : K[G] := halfOnePlus c
  -- Normalize the off-diagonal entries by a nonzero value of the pairing, if there is one.
  obtain ⟨y₀, z₀, hx⟩ : ∃ y₀ z₀ : K[G], τ (e * y₀ * (1 - e) * z₀) ≠ 0 ∨
      ∀ y z, τ (e * y * (1 - e) * z) = 0 := by
    by_cases h : ∃ y₀ z₀ : K[G], τ (e * y₀ * (1 - e) * z₀) ≠ 0
    · obtain ⟨y₀, z₀, h⟩ := h
      exact ⟨y₀, z₀, .inl h⟩
    · push Not at h
      exact ⟨0, 0, .inr h⟩
  set M := hτ.model he he1 hx
  let ρ : Representation K G (Fin 2 → K) :=
    (MonoidAlgebra.lift K _ G).symm (Matrix.toLinAlgEquiv'.toAlgHom.comp M)
  have hρA (u : K[G]) (v : Fin 2 → K) : ρ.asAlgebraHom u v = M u *ᵥ v := by
    simp [ρ, Representation.asAlgebraHom_def]
  have hρ (g : G) : ρ g = Matrix.toLin' (M (MonoidAlgebra.of K G g)) := by
    refine LinearMap.ext fun v => ?_
    rw [← Representation.asAlgebraHom_of, hρA, Matrix.toLin'_apply]
  refine ⟨ρ, isSemisimpleRepresentation_of_offDiag hρA (hτ.model_idem he he1 hx)
    (hτ.model_offDiag_iff he he1 hx), ?_, fun i j => ?_⟩
  · ext g
    rw [Representation.character, hρ, Matrix.trace_toLin'_eq, hτ.trace_model, traceLin_of]
  · simp only [hρ, Matrix.toLin'_apply, Matrix.mulVec_single_one, Matrix.col_apply]
    fin_cases i <;> fin_cases j <;> simp only [M, IsRankTwoTrace.model_apply]
    · exact ⟨e, 1, 1, fun g => by simp⟩
    · exact ⟨e, (1 - e) * z₀, (τ (e * y₀ * (1 - e) * z₀))⁻¹, fun g => by
        simp [mul_assoc, div_eq_mul_inv]⟩
    · exact ⟨e * y₀ * (1 - e), 1, 1, fun g => by simp⟩
    · exact ⟨1 - e, 1, 1, fun g => by simp⟩

/-- **Odd-involution field descent: existence.** Let `T : G → K` be a function on a monoid
satisfying the identities of the trace of a rank-two representation: `T 1 = 2` and the polarized
Cayley–Hamilton identity in three variables (which, as `2 ≠ 0`, implies `T (g h) = T (h g)`). If
some involution `c` has `T c = 0`, then `T` is the character of a semisimple representation of `G`
on `K²`. -/
public theorem exists_isSemisimpleRepresentation_character_eq_of_odd_involution
    (h2 : (2 : K) ≠ 0) (T : G → K) (h_one : T 1 = 2)
    (h_trace : ∀ g h k : G,
      T (g * h * k) + T (g * k * h) - T (g * k) * T h - T (k * h) * T g -
        T (h * g) * T k + T g * T h * T k = 0)
    {c : G} (hc : c * c = 1) (h_odd : T c = 0) :
    ∃ ρ : Representation K G (Fin 2 → K), ρ.IsSemisimpleRepresentation ∧ ρ.character = T :=
  let ⟨ρ, hss, hchar, _⟩ :=
    exists_isSemisimpleRepresentation_character_eq_traceLin h2 T h_one h_trace hc h_odd
  ⟨ρ, hss, hchar⟩

/-- **Odd-involution field descent: existence, continuous version.** If, in
`exists_isSemisimpleRepresentation_character_eq_of_odd_involution`, the monoid `G` and the field
`K` are topological and `T` is continuous, then `T` is the character of a semisimple
representation of `G` on `K²` whose matrix entries are continuous. -/
public theorem exists_continuous_isSemisimpleRepresentation_character_eq_of_odd_involution
    [TopologicalSpace G] [ContinuousMul G] [TopologicalSpace K] [IsTopologicalSemiring K]
    (h2 : (2 : K) ≠ 0) (T : G → K) (hT : Continuous T) (h_one : T 1 = 2)
    (h_trace : ∀ g h k : G,
      T (g * h * k) + T (g * k * h) - T (g * k) * T h - T (k * h) * T g -
        T (h * g) * T k + T g * T h * T k = 0)
    {c : G} (hc : c * c = 1) (h_odd : T c = 0) :
    ∃ ρ : Representation K G (Fin 2 → K),
      ρ.IsSemisimpleRepresentation ∧
      Continuous (fun g => fun i j : Fin 2 => ρ g (Pi.single j 1) i) ∧
      ρ.character = T := by
  obtain ⟨ρ, hss, hchar, hent⟩ :=
    exists_isSemisimpleRepresentation_character_eq_traceLin h2 T h_one h_trace hc h_odd
  refine ⟨ρ, hss, continuous_pi fun i => continuous_pi fun j => ?_, hchar⟩
  obtain ⟨u, v, r, h⟩ := hent i j
  simp only [h]
  exact (continuous_traceLin_mul_of_mul hT u v).mul continuous_const

end Group

end TauCeti

namespace Representation

open TauCeti

variable {K G V W : Type*} [Field K] [Monoid G] [AddCommGroup V] [Module K V] [AddCommGroup W]
  [Module K W]

/-- **Odd-involution field descent: uniqueness.** Over a field with `2 ≠ 0`, two semisimple
representations on planes with the same character are equivalent, provided some involution `c` of
`G` has character value `0`. -/
public theorem nonempty_equiv_of_character_eq_of_odd_involution (ρ : Representation K G V)
    (σ : Representation K G W) [ρ.IsSemisimpleRepresentation] [σ.IsSemisimpleRepresentation]
    (hV : finrank K V = 2) (hW : finrank K W = 2) (h : ρ.character = σ.character)
    (h2 : (2 : K) ≠ 0) {c : G} (hc : c * c = 1) (h_odd : ρ.character c = 0) :
    Nonempty (ρ.Equiv σ) := by
  have he := isIdempotentElem_halfOnePlus (K := K) h2 hc
  set e : K[G] := halfOnePlus c
  obtain ⟨b₁, hb₁⟩ := LinearMap.exists_basis_toMatrix_eq_of_isIdempotentElem_of_trace_eq_one hV
    (he.map ρ.asAlgebraHom) (trace_asAlgebraHom_halfOnePlus h2 hV h_odd)
  obtain ⟨b₂, hb₂⟩ := LinearMap.exists_basis_toMatrix_eq_of_isIdempotentElem_of_trace_eq_one hW
    (he.map σ.asAlgebraHom) (trace_asAlgebraHom_halfOnePlus h2 hW (h ▸ h_odd))
  obtain ⟨N₁, hN₁⟩ : ∃ N : K[G] → Matrix (Fin 2) (Fin 2) K,
      ∀ u, LinearMap.toMatrix b₁ b₁ (ρ.asAlgebraHom u) = N u := ⟨_, fun _ => rfl⟩
  obtain ⟨N₂, hN₂⟩ : ∃ N : K[G] → Matrix (Fin 2) (Fin 2) K,
      ∀ u, LinearMap.toMatrix b₂ b₂ (σ.asAlgebraHom u) = N u := ⟨_, fun _ => rfl⟩
  have e₁ := toMatrix_entries b₁ hb₁
  have e₂ := toMatrix_entries b₂ hb₂
  simp only [hN₁, hN₂, ← trace_asAlgebraHom_eq_of_character_eq h] at e₁ e₂
  have h₀₀ (u : K[G]) : N₁ u 0 0 = N₂ u 0 0 := by rw [(e₁ u u).1, (e₂ u u).1]
  have h₁₁ (u : K[G]) : N₁ u 1 1 = N₂ u 1 1 := by rw [(e₁ u u).2.1, (e₂ u u).2.1]
  have hx (y z : K[G]) : N₁ y 0 1 * N₁ z 1 0 = N₂ y 0 1 * N₂ z 1 0 := by
    rw [(e₁ y z).2.2, (e₂ y z).2.2]
  -- It suffices to conjugate the matrices of `ρ` into those of `σ` by `diag(1, t)`, `t ≠ 0`.
  suffices ∃ t : K, t ≠ 0 ∧ ∀ u, N₁ u 0 1 = N₂ u 0 1 * t ∧ t * N₁ u 1 0 = N₂ u 1 0 by
    obtain ⟨t, ht, hN⟩ := this
    exact nonempty_equiv_of_toMatrix b₁ b₂ hN₁ hN₂ ht h₀₀ h₁₁ (fun u => (hN u).1)
      fun u => (hN u).2
  by_cases hx₀ : ∃ y₀ z₀, N₁ y₀ 0 1 * N₁ z₀ 1 0 ≠ 0
  · -- The off-diagonal pairing is nonzero: normalize by its value at `(y₀, z₀)`.
    obtain ⟨y₀, z₀, hyz⟩ := hx₀
    have hyz₂ : N₂ y₀ 0 1 * N₂ z₀ 1 0 ≠ 0 := hx y₀ z₀ ▸ hyz
    obtain ⟨hs₁, hr₁⟩ := mul_ne_zero_iff.mp hyz
    obtain ⟨hs₂, -⟩ := mul_ne_zero_iff.mp hyz₂
    refine ⟨N₁ y₀ 0 1 / N₂ y₀ 0 1, div_ne_zero hs₁ hs₂, fun u => ⟨?_, ?_⟩⟩
    · have h₁ := hx u z₀
      have h₂ := hx y₀ z₀
      field_simp
      apply mul_right_cancel₀ hr₁
      linear_combination N₂ y₀ 0 1 * h₁ - N₂ u 0 1 * h₂
    · have := hx y₀ u
      field_simp
      linear_combination this
  · -- The off-diagonal pairing vanishes: by semisimplicity both matrices are diagonal.
    push Not at hx₀
    have hd₁ := diagonal_of_offDiag_mul_eq_zero b₁ hb₁ fun y z => by rw [hN₁, hN₁]; exact hx₀ y z
    have hd₂ := diagonal_of_offDiag_mul_eq_zero b₂ hb₂ fun y z => by
      rw [hN₂, hN₂, ← hx]; exact hx₀ y z
    simp only [hN₁, hN₂] at hd₁ hd₂
    exact ⟨1, one_ne_zero, fun u => by simp [(hd₁ u).1, (hd₁ u).2, (hd₂ u).1, (hd₂ u).2]⟩

end Representation
