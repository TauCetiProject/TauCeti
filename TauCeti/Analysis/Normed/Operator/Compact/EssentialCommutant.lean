/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import TauCeti.Analysis.Normed.Operator.Compact.Basic
public import TauCeti.Analysis.Normed.Operator.Compact.HilbertAdjoint
import Mathlib.Tactic.NoncommRing

/-!
# The essential commutant of a set of operators

The *essential commutant* of a set `s` of bounded operators on a normed space `E` consists of the
operators `T` that commute with every `x ∈ s` modulo compact operators: the commutator
`T x - x T` is compact. Since the compact operators form a closed two-sided ideal, the essential
commutant is a subalgebra (`ContinuousLinearMap.essentialCommutant`), closed when `E` is complete
(`ContinuousLinearMap.isClosed_essentialCommutant`). On a Hilbert space it is closed under the
adjoint as soon as `s` is (`ContinuousLinearMap.star_mem_essentialCommutant`), so it is then a
C⋆-subalgebra of `E →L[ℂ] E`, and therefore closed under the continuous functional calculus
(`ContinuousLinearMap.cfc_mem_essentialCommutant`).

For a Fredholm module `(H, π, F)` the operator `F` lies in the essential commutant of the range of
`π`, so every continuous function of a self-adjoint `F` again has compact commutators with the
representation. This is what allows `F` to be replaced by a function of itself, such as the
contraction `sin (π F / 2)`, without leaving the class of Fredholm modules.

## References

* W. Arveson, *An Invitation to C⋆-Algebras*, Graduate Texts in Mathematics 39, Springer (1976),
  §3.5.
* N. Higson, J. Roe, *Analytic K-Homology*, Oxford Mathematical Monographs (2000), §8.2.
-/

public section

namespace ContinuousLinearMap

section Normed

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The **essential commutant** of a set `s` of operators: the operators `T` whose commutator
`T x - x T` with every `x ∈ s` is compact. -/
def essentialCommutant (s : Set (E →L[𝕜] E)) : Subalgebra 𝕜 (E →L[𝕜] E) where
  carrier := {T | ∀ x ∈ s, IsCompactOperator ⇑(T * x - x * T)}
  mul_mem' {S T} hS hT x hx := by
    rw [show S * T * x - x * (S * T) = S * (T * x - x * T) + (S * x - x * S) * T by
      noncomm_ring, FunLike.coe_add]
    exact ((hT x hx).mul_left S).add ((hS x hx).mul_right T)
  add_mem' {S T} hS hT x hx := by
    rw [show (S + T) * x - x * (S + T) = (S * x - x * S) + (T * x - x * T) by noncomm_ring,
      FunLike.coe_add]
    exact (hS x hx).add (hT x hx)
  algebraMap_mem' r x _ := by
    rw [Algebra.commutes, sub_self]
    exact isCompactOperator_zero

@[simp]
theorem mem_essentialCommutant {s : Set (E →L[𝕜] E)} {T : E →L[𝕜] E} :
    T ∈ essentialCommutant s ↔ ∀ x ∈ s, IsCompactOperator ⇑(T * x - x * T) :=
  Iff.rfl

/-- On a Banach space the essential commutant of any set of operators is norm closed. -/
theorem isClosed_essentialCommutant [CompleteSpace E] (s : Set (E →L[𝕜] E)) :
    IsClosed (essentialCommutant s : Set (E →L[𝕜] E)) := by
  have : (essentialCommutant s : Set (E →L[𝕜] E)) =
      ⋂ x ∈ s, (fun T => T * x - x * T) ⁻¹' {K | IsCompactOperator ⇑K} := by
    ext T; simp
  rw [this]
  exact isClosed_biInter fun x _ =>
    (isClosed_setOfPred_isCompactOperator).preimage (by fun_prop)

end Normed

section Hilbert

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The essential commutant of a set of Hilbert-space operators closed under the adjoint is
itself closed under the adjoint. -/
theorem star_mem_essentialCommutant {s : Set (E →L[𝕜] E)} (hs : ∀ x ∈ s, star x ∈ s)
    {T : E →L[𝕜] E} (hT : T ∈ essentialCommutant s) : star T ∈ essentialCommutant s := by
  intro x hx
  have h := (hT (star x) (hs x hx)).star
  rw [star_sub, star_mul, star_mul, star_star, ← neg_sub, FunLike.coe_neg] at h
  simpa only [neg_neg] using h.neg

end Hilbert

section CFC

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {𝕜 : Type*} [RCLike 𝕜] [SMul 𝕜 ℂ] [Algebra 𝕜 (H →L[ℂ] H)] [IsScalarTower 𝕜 ℂ (H →L[ℂ] H)]
  [StarModule 𝕜 (H →L[ℂ] H)]
  {p : (H →L[ℂ] H) → Prop} [ContinuousFunctionalCalculus 𝕜 (H →L[ℂ] H) p]

/-- **The essential commutant is closed under the continuous functional calculus.** If `s` is
closed under the adjoint and `T` commutes with every element of `s` modulo compact operators, then
so does `f(T)`, for every function `f`. This applies both to the real functional calculus of a
self-adjoint `T` and to the complex functional calculus of a normal `T`. -/
theorem cfc_mem_essentialCommutant {s : Set (H →L[ℂ] H)} (hs : ∀ x ∈ s, star x ∈ s) (f : 𝕜 → 𝕜)
    {T : H →L[ℂ] H} (hT : T ∈ essentialCommutant s) : cfc f T ∈ essentialCommutant s := by
  let S : StarSubalgebra ℂ (H →L[ℂ] H) :=
    { essentialCommutant s with star_mem' := star_mem_essentialCommutant hs }
  have : IsClosed (S : Set (H →L[ℂ] H)) := isClosed_essentialCommutant s
  exact cfc_mem (𝕜' := ℂ) (s := S) f hT

end CFC

end ContinuousLinearMap
