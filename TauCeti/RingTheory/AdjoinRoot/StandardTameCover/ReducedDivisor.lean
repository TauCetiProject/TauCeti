/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdjoinRoot.StandardTameCover.Basic
import TauCeti.RingTheory.AdjoinRoot.Basic
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import TauCeti.RingTheory.Smooth.Regular
import TauCeti.RingTheory.RegularLocalRing.Basic

/-!
# The reduced divisor in a product of standard tame covers

In `A[x]/(x^e - f)`, when `e > 0` and `A/(f)` is reduced, the radical of `(f)` is
`(x)`. For a finite product of such algebras with possibly different exponents, the tuple
of roots still generates the radical of `(f)`. Its quotient is a product of copies of
`A/(f)`. If `f` is a nonzerodivisor, so is that tuple; if `A/(f)` is regular, so is the
quotient. These are the affine local-model assertions that the reduced inverse image
of a regular divisor is a regular effective Cartier divisor.

The exponents need only be positive: neither their invertibility nor Noetherianity of
`A` is needed for the radical computation or the nonzerodivisor assertion.

## References

* The Stacks Project, Lemma 58.31.6, https://stacks.math.columbia.edu/tag/0EYH.
-/

public section

open Polynomial

namespace TauCeti

variable {A : Type*} [CommRing A] {ι : Type*}

/-- The reduced inverse image of `(f)` in a positive-degree root cover is cut out by the root,
provided `A/(f)` is reduced. -/
theorem standardTameCover_radical_span (f : A) {e : ℕ} (he : e ≠ 0)
    [IsReduced (A ⧸ Ideal.span {f})] :
    (Ideal.span {algebraMap A (standardTameCover A f e) f}).radical =
      Ideal.span {AdjoinRoot.root (X ^ e - C f)} := by
  have : IsReduced (standardTameCover A f e ⧸
      Ideal.span {AdjoinRoot.root (X ^ e - C f)}) :=
    isReduced_of_injective (standardTameCoverQuotientSpanRootAlgEquiv f he)
      (standardTameCoverQuotientSpanRootAlgEquiv f he).injective
  have hr := (Ideal.isRadical_iff_quotient_reduced
    (Ideal.span {AdjoinRoot.root (X ^ e - C f)})).mpr inferInstance
  rw [AdjoinRoot.algebraMap_eq, ← AdjoinRoot.root_X_pow_sub_C_pow,
    ← Ideal.span_singleton_pow, Ideal.radical_pow _ he, hr.radical]

section Product

variable (f : A) (e : ι → ℕ) (he : ∀ i, e i ≠ 0)

/-- Quotienting a product of root covers by its tuple of roots gives a product of
copies of `A/(f)`. -/
noncomputable def standardTameCoverPiQuotientSpanRootAlgEquiv :
    ((∀ i, standardTameCover A f (e i)) ⧸
      Ideal.span {fun i ↦ AdjoinRoot.root (X ^ e i - C f)}) ≃ₐ[A]
      (ι → A ⧸ Ideal.span {f}) := by
  let φ : (∀ i, standardTameCover A f (e i)) →ₐ[A] (ι → A ⧸ Ideal.span {f}) :=
    AlgHom.pi fun i ↦ ((standardTameCoverQuotientSpanRootAlgEquiv f (he i)).toAlgHom.comp
      (Ideal.Quotient.mkₐ A _)).comp (Pi.evalAlgHom A _ i)
  have hker : RingHom.ker φ =
      Ideal.span {fun i ↦ AdjoinRoot.root (X ^ e i - C f)} := by
    rw [← Ideal.pi_span]
    ext x
    rw [RingHom.mem_ker, Ideal.mem_pi]
    simp [φ, funext_iff, Ideal.Quotient.eq_zero_iff_mem]
  have hφ : Function.Surjective φ := by
    intro a
    choose b hb using fun i ↦ (standardTameCoverQuotientSpanRootAlgEquiv f (he i)).surjective (a i)
    choose c hc using fun i ↦ Ideal.Quotient.mk_surjective (b i)
    exact ⟨c, funext fun i ↦ by simpa [φ, hc i] using hb i⟩
  exact (Ideal.quotientEquivAlgOfEq A hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hφ)

/-- The quotient comparison applies the individual root-quotient comparisons in each entry. -/
@[simp]
theorem standardTameCoverPiQuotientSpanRootAlgEquiv_mk
    (a : ∀ i, standardTameCover A f (e i)) (i : ι) :
    standardTameCoverPiQuotientSpanRootAlgEquiv f e he (Ideal.Quotient.mk _ a) i =
      standardTameCoverQuotientSpanRootAlgEquiv f (he i) (Ideal.Quotient.mk _ (a i)) := by
  -- The first-isomorphism comparison is induced by the coordinatewise quotient map.
  rfl

/-- The inverse quotient comparison sends a tuple of constant classes to the corresponding
tuple of constants in the root covers. -/
@[simp]
theorem standardTameCoverPiQuotientSpanRootAlgEquiv_symm_mk (a : ι → A) :
    (standardTameCoverPiQuotientSpanRootAlgEquiv f e he).symm
        (fun i ↦ Ideal.Quotient.mk _ (a i)) =
      Ideal.Quotient.mk _ (fun i ↦ AdjoinRoot.of _ (a i)) := by
  apply (standardTameCoverPiQuotientSpanRootAlgEquiv f e he).injective
  ext i
  simp

include he in
/-- The tuple of roots generates the radical of `(f)` in a finite product of positive-degree
root covers. The exponents may vary among the factors. -/
theorem standardTameCoverPi_radical_span [Finite ι] [IsReduced (A ⧸ Ideal.span {f})] :
    (Ideal.span {algebraMap A (∀ i, standardTameCover A f (e i)) f}).radical =
      Ideal.span {fun i ↦ AdjoinRoot.root (X ^ e i - C f)} := by
  classical
  let := Fintype.ofFinite ι
  let g : ∀ i, standardTameCover A f (e i) := fun i ↦ AdjoinRoot.root _
  have : IsReduced ((∀ i, standardTameCover A f (e i)) ⧸ Ideal.span {g}) :=
    isReduced_of_injective (standardTameCoverPiQuotientSpanRootAlgEquiv f e he)
      (standardTameCoverPiQuotientSpanRootAlgEquiv f e he).injective
  have hr := (Ideal.isRadical_iff_quotient_reduced (Ideal.span {g})).mpr inferInstance
  apply le_antisymm
  · apply hr.radical_le_iff.mpr
    rw [Ideal.span_singleton_le_iff_mem, ← Ideal.pi_span]
    intro i
    rw [Pi.algebraMap_apply, AdjoinRoot.algebraMap_eq, ← AdjoinRoot.root_X_pow_sub_C_pow (e i) f]
    exact (Ideal.span {g i}).pow_mem_of_mem (Ideal.mem_span_singleton_self _) _
      (Nat.pos_of_ne_zero (he i))
  · rw [Ideal.span_singleton_le_iff_mem]
    refine ⟨∑ i, e i, ?_⟩
    rw [← Ideal.pi_span]
    intro i
    have hle : e i ≤ ∑ j, e j := Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    have hpow : g i ^ e i ∈ Ideal.span {algebraMap A (standardTameCover A f (e i)) f} := by
      rw [AdjoinRoot.root_X_pow_sub_C_pow, ← AdjoinRoot.algebraMap_eq]
      exact Ideal.mem_span_singleton_self _
    exact Ideal.pow_mem_of_pow_mem _ hpow hle

include he in
/-- A tuple of roots is a nonzerodivisor whenever the defining equation is one. -/
theorem standardTameCoverPi_root_mem_nonZeroDivisors (hf : f ∈ nonZeroDivisors A) :
    (fun i : ι ↦ (AdjoinRoot.root (X ^ e i - C f) : standardTameCover A f (e i))) ∈
      nonZeroDivisors (∀ i, standardTameCover A f (e i)) := by
  have hg (i : ι) : AdjoinRoot.root (X ^ e i - C f) ∈
      nonZeroDivisors (standardTameCover A f (e i)) :=
    (standardTameCover_root_mem_nonZeroDivisors_iff (f := f) (he i)).mpr hf
  refine mem_nonZeroDivisors_iff_right.mpr fun a ha ↦ ?_
  funext i
  exact (mem_nonZeroDivisors_iff_right.mp (hg i)) (a i) (congrFun ha i)

end Product

/-- In any finite product of standard tame covers, the reduced inverse image of `(f)` is
principal and generated by a nonzerodivisor. Its coordinate ring is a finite product of copies
of `A/(f)`. This statement is invariant under the choice of the product presentation. -/
theorem IsFiniteProductOfStandardTameCovers.exists_radical_span_eq_and_quotient_algEquiv
    {C : Type*} [CommRing C] [Algebra A C] {f : A}
    (h : IsFiniteProductOfStandardTameCovers A C f) (hf : f ∈ nonZeroDivisors A)
    [IsReduced (A ⧸ Ideal.span {f})] :
    ∃ (ι : Type) (_ : Fintype ι) (g : C), g ∈ nonZeroDivisors C ∧
      (Ideal.span {algebraMap A C f}).radical = Ideal.span {g} ∧
      Nonempty ((C ⧸ Ideal.span {g}) ≃ₐ[A] (ι → A ⧸ Ideal.span {f})) := by
  obtain ⟨ι, _, e, he, -, ⟨σ⟩⟩ := (isFiniteProductOfStandardTameCovers_iff f).mp h
  have he₀ (i : ι) : e i ≠ 0 := Nat.ne_of_gt (he i)
  let x : ∀ i, standardTameCover A f (e i) := fun i ↦ AdjoinRoot.root _
  let g : C := σ.symm x
  have hmapg : (Ideal.span {g}).map σ.toRingHom = Ideal.span {x} := by
    simp [Ideal.map_span, g]
  have hmapf : (Ideal.span {algebraMap A C f}).map σ.toRingHom =
      Ideal.span {algebraMap A (∀ i, standardTameCover A f (e i)) f} := by
    simp [Ideal.map_span]
  have hg : g ∈ nonZeroDivisors C := mem_nonZeroDivisors_of_injective σ.injective
    (by simpa [g] using standardTameCoverPi_root_mem_nonZeroDivisors f e he₀ hf)
  have hrad : (Ideal.span {algebraMap A C f}).radical = Ideal.span {g} := by
    apply σ.toRingEquiv.idealComapOrderIso.symm.injective
    -- The order isomorphism maps along the ring equivalence; use its underlying ring hom
    -- to apply the ideal-map API.
    change (Ideal.span {algebraMap A C f}).radical.map σ.toRingHom =
      (Ideal.span {g}).map σ.toRingHom
    rw [Ideal.map_radical_of_surjective (f := σ.toRingHom) σ.surjective
      (by simp), hmapf, hmapg]
    exact standardTameCoverPi_radical_span f e he₀
  exact ⟨ι, inferInstance, g, hg, hrad,
    ⟨(Ideal.quotientEquivAlg _ _ σ hmapg.symm).trans
      (standardTameCoverPiQuotientSpanRootAlgEquiv f e he₀)⟩⟩

/-- The reduced inverse image of a regular divisor in a finite product of standard tame covers
is regular. This is the coordinate-ring assertion for the reduced divisor in Stacks 0EYH. -/
@[stacks 0EYH "regularity of the reduced divisor in the standard local models"]
theorem IsFiniteProductOfStandardTameCovers.isRegularRing_quotient_radical_span
    {C : Type*} [CommRing C] [Algebra A C] {f : A}
    (h : IsFiniteProductOfStandardTameCovers A C f)
    [IsRegularRing (A ⧸ Ideal.span {f})] :
    IsRegularRing (C ⧸ (Ideal.span {algebraMap A C f}).radical) := by
  obtain ⟨ι, _, e, he, -, ⟨σ⟩⟩ := (isFiniteProductOfStandardTameCovers_iff f).mp h
  have he₀ (i : ι) : e i ≠ 0 := Nat.ne_of_gt (he i)
  have hmap : (Ideal.span {algebraMap A C f}).radical.map σ.toRingHom =
      Ideal.span {fun i ↦ AdjoinRoot.root (X ^ e i - Polynomial.C f)} := by
    rw [Ideal.map_radical_of_surjective (f := σ.toRingHom) σ.surjective (by simp)]
    simpa [Ideal.map_span] using standardTameCoverPi_radical_span f e he₀
  let τ := (Ideal.quotientEquivAlg _ _ σ hmap.symm).trans
    (standardTameCoverPiQuotientSpanRootAlgEquiv f e he₀)
  have : Algebra.Etale (A ⧸ Ideal.span {f}) (ι → A ⧸ Ideal.span {f}) := inferInstance
  have : IsRegularRing (ι → A ⧸ Ideal.span {f}) :=
    IsRegularRing.of_smooth (R := A ⧸ Ideal.span {f})
  exact .of_ringEquiv τ.symm.toRingEquiv

end TauCeti
