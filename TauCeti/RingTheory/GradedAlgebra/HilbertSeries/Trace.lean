/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.GradedAlgebra.HilbertSeries.RegularElement
public import TauCeti.LinearAlgebra.Trace.Exchange
import TauCeti.LinearAlgebra.Trace.Exact

/-!
# Graded traces modulo a homogeneous regular element

Let `A` be a nonnegatively graded algebra over a field, with finite-dimensional pieces.
Suppose `T` preserves the grading, commutes with multiplication by a homogeneous regular
element `f` of degree `d`, and induces `Q` on `A/(f)`. Then the trace series of `Q` is the
trace series of `T` multiplied by `1 - t^d`.

In particular, a graded algebra automorphism fixing `f` satisfies the multiplication
compatibility. Applied to group elements and invariant relations, this is the equivariant
one-relation exact-sequence formula for computing graded coinvariant characters. Unlike a
Hilbert series, its coefficients record the action of each element, not only dimensions.
No finite-order, characteristic-zero, or positivity assumption on `d` is needed.

The maps are linear, rather than necessarily multiplicative, so the result also applies
to endomorphisms of the multiplication/quotient exact sequence. Compatibility with the
quotient map supplies preservation of the quotient pieces.

## Main results

* `trace_quotientPiece_span_singleton_add`: trace additivity in degrees at least `d`.
* `trace_quotientPiece_span_singleton_of_lt`: traces are unchanged below `d`.
* `mk_trace_quotientPiece_span_singleton`: the trace-series identity.

## References

* R. P. Stanley, *Invariants of finite groups and their applications to combinatorics*,
  Bull. Amer. Math. Soc. (N.S.) **1** (1979), §3.

The exact sequences are those of `HilbertSeries.RegularElement`; trace additivity uses
`LinearMap.trace_eq_add_of_exact`.
-/

public section

namespace TauCeti.GradedAlgebra

variable {k A : Type*} [CommRing A]

section CommRing

variable [CommRing k] [Algebra k A]
  (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜] {f : A} {d : ℕ}
  (T : A →ₗ[k] A) (Q : (A ⧸ Ideal.span {f}) →ₗ[k] (A ⧸ Ideal.span {f}))
  (hT : ∀ n x, x ∈ 𝒜 n → T x ∈ 𝒜 n)
  (hQ : ∀ x, Q (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (T x))

/-- Below the degree of a homogeneous relation, a compatible quotient endomorphism has
the same trace as the original endomorphism. Regularity and finite-dimensionality are
not needed for this statement, and the coefficient ring need not be a field. -/
theorem trace_quotientPiece_span_singleton_of_lt (hf : f ∈ 𝒜 d) {n : ℕ} (hn : n < d) :
    LinearMap.trace k (quotientPiece 𝒜 (Ideal.span {f}) n)
        (Q.restrict (apply_mem_quotientPiece 𝒜 _ T Q hT hQ n)) =
      LinearMap.trace k (𝒜 n) (T.restrict (hT n)) := by
  have hQ' := apply_mem_quotientPiece 𝒜 _ T Q hT hQ n
  rw [quotientPiece_def] at hQ'
  rw [LinearMap.trace_restrict_congr (quotientPiece_def 𝒜 _ n) Q _ hQ']
  let e := LinearEquiv.ofBijective _ (bijective_submoduleMap_span_singleton_of_lt 𝒜 hf hn)
  have he : e.conj (T.restrict (hT n)) = Q.restrict hQ' := by
    ext x
    obtain ⟨y, rfl⟩ := e.surjective x
    simp only [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply]
    simpa [e] using (hQ y).symm
  rw [← he]
  exact LinearMap.trace_conj' _ e

end CommRing

section Field

variable [Field k] [Algebra k A]
  (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜] {f : A} {d : ℕ}
  (T : A →ₗ[k] A) (Q : (A ⧸ Ideal.span {f}) →ₗ[k] (A ⧸ Ideal.span {f}))
  (hT : ∀ n x, x ∈ 𝒜 n → T x ∈ 𝒜 n)
  (hQ : ∀ x, Q (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (T x))

/-- The trace in degree `d + n` before quotienting is the sum of the quotient trace
and the original degree-`n` trace, for an endomorphism commuting with multiplication
by the homogeneous regular relation. -/
theorem trace_quotientPiece_span_singleton_add (hf : f ∈ 𝒜 d)
    (hreg : IsLeftRegular f) (hmul : ∀ x, T (f * x) = f * T x)
    (n : ℕ) [Module.Finite k (𝒜 (d + n))] :
    LinearMap.trace k (quotientPiece 𝒜 (Ideal.span {f}) (d + n))
        (Q.restrict (apply_mem_quotientPiece 𝒜 _ T Q hT hQ (d + n))) +
      LinearMap.trace k (𝒜 n) (T.restrict (hT n)) =
      LinearMap.trace k (𝒜 (d + n)) (T.restrict (hT (d + n))) := by
  have hQ' := apply_mem_quotientPiece 𝒜 _ T Q hT hQ (d + n)
  rw [quotientPiece_def] at hQ'
  rw [LinearMap.trace_restrict_congr (quotientPiece_def 𝒜 _ (d + n)) Q _ hQ']
  let μ : 𝒜 n →ₗ[k] 𝒜 (d + n) :=
    ((LinearMap.mulLeft k f).domRestrict (𝒜 n)).codRestrict (𝒜 (d + n))
      (fun x ↦ SetLike.mul_mem_graded hf x.2)
  let q := (Ideal.Quotient.mkₐ k (Ideal.span {f})).toLinearMap.submoduleMap (𝒜 (d + n))
  have hμ : Function.Injective μ := fun x y h ↦
    Subtype.ext (hreg (congrArg Subtype.val h))
  have hex : Function.Exact μ q := exact_mulLeft_submoduleMap_span_singleton 𝒜 hf hreg n
  have h := LinearMap.trace_eq_add_of_exact hμ (LinearMap.submoduleMap_surjective _ _) hex
    (f := T.restrict (hT (d + n))) (fN := T.restrict (hT n))
    (fQ := Q.restrict hQ')
    (by ext x; exact hmul x)
    (by ext x; exact (hQ x).symm)
  exact (add_comm _ _).trans h.symm

/-- Quotienting by a homogeneous regular element of degree `d` multiplies the graded
trace series by `1 - t^d`, provided the endomorphism commutes with multiplication by
that element. The coefficients lie in the original field, in arbitrary characteristic. -/
theorem mk_trace_quotientPiece_span_singleton [∀ n, Module.Finite k (𝒜 n)]
    (hf : f ∈ 𝒜 d) (hreg : IsLeftRegular f) (hmul : ∀ x, T (f * x) = f * T x) :
    PowerSeries.mk (fun n ↦
      LinearMap.trace k (quotientPiece 𝒜 (Ideal.span {f}) n)
        (Q.restrict (apply_mem_quotientPiece 𝒜 _ T Q hT hQ n))) =
      PowerSeries.mk (fun n ↦ LinearMap.trace k (𝒜 n) (T.restrict (hT n))) *
        (1 - PowerSeries.X ^ d) := by
  ext n
  rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
    PowerSeries.coeff_mul_X_pow']
  split_ifs with hdn
  · have h := trace_quotientPiece_span_singleton_add 𝒜 T Q hT hQ hf hreg hmul (n - d)
    rw [Nat.add_sub_of_le hdn] at h
    simpa only [PowerSeries.coeff_mk] using eq_sub_iff_add_eq.mpr h
  · rw [sub_zero]
    exact trace_quotientPiece_span_singleton_of_lt 𝒜 T Q hT hQ hf (Nat.lt_of_not_ge hdn)

end Field

end TauCeti.GradedAlgebra
