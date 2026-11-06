/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.GradedAlgebra.HilbertSeries.RegularElement
public import TauCeti.LinearAlgebra.Trace.Exchange
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Submodule
public import Mathlib.RingTheory.Regular.RegularSequence
import TauCeti.LinearAlgebra.Trace.Exact
import TauCeti.RingTheory.GradedAlgebra.Homogeneous.Quotient

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

Iterating over a homogeneous weakly regular sequence multiplies the trace series by one factor
`1 - t^d` for each element. Here `T` need only commute with multiplication by the elements of the
sequence; it then preserves the ideal they generate, and induces the endomorphism of each
intermediate quotient used in the induction.

## Main results

* `trace_quotientPiece_span_singleton_add`: trace additivity in degrees at least `d`.
* `trace_quotientPiece_span_singleton_of_lt`: traces are unchanged below `d`.
* `mk_trace_quotientPiece_span_singleton`: the trace-series identity.
* `trace_quotientPiece_of_eq_bot`: quotienting by the zero ideal does not change traces.
* `mk_trace_quotientPiece_sup_span_singleton`: the trace-series identity for one further element,
  regular modulo a homogeneous ideal.
* `mk_trace_quotientPiece_of_isWeaklyRegular`: the trace-series identity for a homogeneous weakly
  regular sequence.

## References

* R. P. Stanley, *Invariants of finite groups and their applications to combinatorics*,
  Bull. Amer. Math. Soc. (N.S.) **1** (1979), §3.

The exact sequences are those of `HilbertSeries.RegularElement`; trace additivity uses
`LinearMap.trace_eq_add_of_exact`. The induction over a sequence follows the dimension version
`mk_finrank_quotientPiece_of_isWeaklyRegular` in `HilbertSeries.RegularSequence`.
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

section Bot

variable [CommRing k] [Algebra k A] (𝒜 : ℕ → Submodule k A)
  (T : A →ₗ[k] A) (hT : ∀ n x, x ∈ 𝒜 n → T x ∈ 𝒜 n)

/-- Quotienting by the zero ideal does not change the traces of a compatible endomorphism. The
family `𝒜` need not be a grading. -/
theorem trace_quotientPiece_of_eq_bot {J : Ideal A} (hJ : J = ⊥) (Q : (A ⧸ J) →ₗ[k] (A ⧸ J))
    (hQ : ∀ x, Q (Ideal.Quotient.mk J x) = Ideal.Quotient.mk J (T x)) (n : ℕ) :
    LinearMap.trace k (quotientPiece 𝒜 J n)
        (Q.restrict (apply_mem_quotientPiece 𝒜 J T Q hT hQ n)) =
      LinearMap.trace k (𝒜 n) (T.restrict (hT n)) := by
  -- The quotient map by the zero ideal is an isomorphism intertwining `T` and `Q`.
  have hinj : Function.Injective (Ideal.Quotient.mkₐ k J) := by
    intro x y h
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq, hJ, Submodule.mem_bot, sub_eq_zero] at h
    exact h
  let e := LinearEquiv.ofBijective (Ideal.Quotient.mkₐ k J).toLinearMap
    ⟨hinj, Ideal.Quotient.mkₐ_surjective k J⟩
  exact LinearMap.trace_restrict_eq_of_linearEquiv e (quotientPiece_def 𝒜 J n).symm
    (fun x ↦ (hQ x).symm) _ _

end Bot

section RegularSequence

variable [Field k] [Algebra k A]
  (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜]
  (T : A →ₗ[k] A) (hT : ∀ n x, x ∈ 𝒜 n → T x ∈ 𝒜 n)

/-- Quotienting further by a homogeneous element `f` of degree `d`, regular modulo a homogeneous
ideal `I`, multiplies the graded trace series by `1 - t^d`, provided the endomorphism `T` commutes
with multiplication by `f`. Here `Q₀` and `Q` are the endomorphisms induced by `T` on `A ⧸ I` and
on `A ⧸ J`, where `J = I ⊔ (f)`. -/
theorem mk_trace_quotientPiece_sup_span_singleton [∀ n, Module.Finite k (𝒜 n)] {I : Ideal A}
    (hI : I.IsHomogeneous 𝒜) {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hreg : IsSMulRegular (A ⧸ I) f)
    (hmul : ∀ x, T (f * x) = f * T x) (Q₀ : (A ⧸ I) →ₗ[k] (A ⧸ I))
    (hQ₀ : ∀ x, Q₀ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (T x))
    (J : Ideal A) (hJ : I ⊔ Ideal.span {f} = J) (Q : (A ⧸ J) →ₗ[k] (A ⧸ J))
    (hQ : ∀ x, Q (Ideal.Quotient.mk J x) = Ideal.Quotient.mk J (T x)) :
    PowerSeries.mk (fun n ↦ LinearMap.trace k (quotientPiece 𝒜 J n)
        (Q.restrict (apply_mem_quotientPiece 𝒜 J T Q hT hQ n))) =
      PowerSeries.mk (fun n ↦ LinearMap.trace k (quotientPiece 𝒜 I n)
        (Q₀.restrict (apply_mem_quotientPiece 𝒜 I T Q₀ hT hQ₀ n))) * (1 - PowerSeries.X ^ d) := by
  let := gradedAlgebraQuotientPiece 𝒜 I hI
  have hleft : IsLeftRegular (Ideal.Quotient.mk I f) := by
    intro x y hxy
    apply hreg
    simpa only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq] using hxy
  -- Identify the quotient of `A ⧸ I` by the class of `f` with `A ⧸ J`, and transport `Q` to it.
  have hspan : Ideal.span {Ideal.Quotient.mk I f} =
      (Ideal.span {f}).map (Ideal.Quotient.mkₐ k I) := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.Quotient.mkₐ_eq_mk]
  let e := ((Ideal.quotientEquivAlgOfEq k hspan).trans
    (DoubleQuot.quotQuotEquivQuotSupₐ k I (Ideal.span {f}))).trans (Ideal.quotientEquivAlgOfEq k hJ)
  have he (x : A) : e (Ideal.Quotient.mk _ (Ideal.Quotient.mk I x)) = Ideal.Quotient.mk J x := by
    simp only [e, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
      DoubleQuot.coe_quotQuotEquivQuotSupₐ]
    -- `DoubleQuot.quotQuotMk I J x` is by definition the class of the class of `x`.
    exact (congrArg _ (DoubleQuot.quotQuotEquivQuotSup_quotQuotMk I _ x)).trans
      (Ideal.quotientEquivAlgOfEq_mk _ _ _)
  let Q' := e.toLinearEquiv.symm.conj Q
  have hQ' (y : A ⧸ I) : Q' (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ (Q₀ y) := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm, LinearEquiv.symm_apply_eq]
    simp only [AlgEquiv.toLinearEquiv_apply, he, hQ, hQ₀]
  have hmul' (y : A ⧸ I) : Q₀ (Ideal.Quotient.mk I f * y) = Ideal.Quotient.mk I f * Q₀ y := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul, hQ₀, hQ₀, hmul, map_mul]
  rw [← mk_trace_quotientPiece_span_singleton (quotientPiece 𝒜 I) Q₀ Q'
    (apply_mem_quotientPiece 𝒜 I T Q₀ hT hQ₀) hQ' (mk_mem_quotientPiece 𝒜 I hf) hleft hmul']
  ext n
  simp only [PowerSeries.coeff_mk]
  refine LinearMap.trace_restrict_eq_of_linearEquiv e.toLinearEquiv ?_ (fun y ↦ ?_) _ _
  · simp only [quotientPiece_def, ← Submodule.map_comp]
    exact congrArg (Submodule.map · (𝒜 n)) (LinearMap.ext he)
  · simp [Q', LinearEquiv.conj_apply]

/-- Quotienting by a homogeneous weakly regular sequence multiplies the graded trace series by
one factor `1 - t^d` for each element, provided the endomorphism `T` commutes with multiplication
by every element of the sequence; `Q` is the endomorphism it induces on the quotient. The quotient
is taken by any ideal `J` equal to the ideal generated by the sequence, such as an ideal defined
independently and shown to be generated by it. A list of element-degree pairs keeps the degrees
attached to their chosen elements, including when an element is zero or has degree zero. The
coefficients lie in the original field, in arbitrary characteristic. -/
theorem mk_trace_quotientPiece_of_isWeaklyRegular [∀ n, Module.Finite k (𝒜 n)]
    (fs : List (A × ℕ)) (hhom : ∀ p ∈ fs, p.1 ∈ 𝒜 p.2)
    (hreg : RingTheory.Sequence.IsWeaklyRegular A (fs.map Prod.fst))
    (hmul : ∀ p ∈ fs, ∀ x, T (p.1 * x) = p.1 * T x)
    (J : Ideal A) (hJ : Ideal.ofList (fs.map Prod.fst) = J)
    (Q : (A ⧸ J) →ₗ[k] (A ⧸ J))
    (hQ : ∀ x, Q (Ideal.Quotient.mk J x) = Ideal.Quotient.mk J (T x)) :
    PowerSeries.mk (fun n ↦ LinearMap.trace k (quotientPiece 𝒜 J n)
        (Q.restrict (apply_mem_quotientPiece 𝒜 J T Q hT hQ n))) =
      PowerSeries.mk (fun n ↦ LinearMap.trace k (𝒜 n) (T.restrict (hT n))) *
        (fs.map fun p ↦ (1 - PowerSeries.X ^ p.2 : PowerSeries k)).prod := by
  subst hJ
  induction fs using List.reverseRecOn with
  | nil =>
    rw [List.map_nil (f := fun p : A × ℕ ↦ (1 - PowerSeries.X ^ p.2 : PowerSeries k)),
      List.prod_nil, mul_one]
    ext n
    simp only [PowerSeries.coeff_mk]
    exact trace_quotientPiece_of_eq_bot 𝒜 T hT (by simp) Q hQ n
  | append_singleton fs p ih =>
    have hfs : ∀ q ∈ fs, q ∈ fs ++ [p] := fun q hq ↦ List.mem_append_left _ hq
    have hpmem : p ∈ fs ++ [p] := List.mem_append_right _ (List.mem_singleton_self p)
    rw [List.map_append, List.map_singleton,
      RingTheory.Sequence.isWeaklyRegular_append_iff] at hreg
    let I := Ideal.ofList (fs.map Prod.fst)
    -- `T` preserves `I`, which is spanned by elements commuting with `T`, so it induces an
    -- endomorphism `Q₀` of `A ⧸ I`.
    have hTI : I.restrictScalars k ≤ (I.restrictScalars k).comap T := by
      intro x hx
      suffices h : ∀ a, T (a * x) ∈ I by simpa using h 1
      induction hx using Submodule.span_induction with
      | mem f hf =>
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hf
        intro a
        rw [mul_comm, hmul q (hfs q hq)]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span hf)
      | zero => simp
      | add x y _ _ hx hy => intro a; rw [mul_add, map_add]; exact add_mem (hx a) (hy a)
      | smul b x _ hx => intro a; rw [smul_eq_mul, ← mul_assoc]; exact hx (a * b)
    let Q₀ : (A ⧸ I) →ₗ[k] (A ⧸ I) :=
      (Submodule.Quotient.restrictScalarsEquiv k I).conj ((I.restrictScalars k).mapQ _ T hTI)
    have hQ₀ (x : A) : Q₀ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk I (T x) := by
      rw [LinearEquiv.conj_apply_apply, ← Ideal.Quotient.mk_eq_mk,
        Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.mapQ_apply,
        Submodule.Quotient.restrictScalarsEquiv_mk, Ideal.Quotient.mk_eq_mk]
    -- Native regular sequences use the module quotient by `I • ⊤`; transport to `A ⧸ I`.
    have hIeq : (I • ⊤ : Submodule A A) = I := by
      rw [Ideal.smul_eq_mul, Ideal.mul_top]
    have hregp : IsSMulRegular (A ⧸ I) p.1 :=
      ((Submodule.quotEquivOfEq _ _ hIeq).isSMulRegular_congr p.1).1
        ((RingTheory.Sequence.isWeaklyRegular_singleton_iff _ _).1 hreg.2)
    have hI : I.IsHomogeneous 𝒜 := by
      apply Ideal.homogeneous_span
      intro x hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
      exact ⟨q.2, hhom q (hfs q hq)⟩
    have hJ : I ⊔ Ideal.span {p.1} = Ideal.ofList ((fs ++ [p]).map Prod.fst) := by
      rw [List.map_append, List.map_singleton, Ideal.ofList_append, Ideal.ofList_singleton]
    rw [List.map_append (f := fun p : A × ℕ ↦ (1 - PowerSeries.X ^ p.2 : PowerSeries k)),
      List.map_singleton, List.prod_append, List.prod_singleton, ← mul_assoc,
      ← ih (fun q hq ↦ hhom q (hfs q hq)) hreg.1 (fun q hq ↦ hmul q (hfs q hq)) Q₀ hQ₀]
    exact mk_trace_quotientPiece_sup_span_singleton 𝒜 T hT hI (hhom p hpmem) hregp
      (hmul p hpmem) Q₀ hQ₀ _ hJ Q hQ

end RegularSequence

end TauCeti.GradedAlgebra
