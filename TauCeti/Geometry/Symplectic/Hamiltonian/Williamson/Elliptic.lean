/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson
public import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.Toral
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Lagrange

/-!
# Williamson's classification of nondegenerate families: the elliptic case

Let `(V, ω)` be a finite-dimensional real symplectic vector space. A family `Q` of quadratic forms
on `V` is nondegenerate (`TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily`) when the
Hamiltonian endomorphisms `A_{Q i}` generate a Cartan subalgebra `𝔥` of `sp(V, ω)`. Williamson's
classification puts such a family, up to its span, into a normal form made of elliptic,
hyperbolic and focus-focus blocks in a suitable Darboux basis. This file proves the classification
for the Cartan subalgebras of **compact type**, those containing the Hamiltonian endomorphism of a
positive definite form:

`∃ P ∈ span Q, P positive definite  ↔  span Q = span (I₁, …, Iₙ)`

for the elliptic blocks `Iₖ = (xₖ² + yₖ²) / 2` (`TauCeti.SymplecticForm.elliptic`) of some
Darboux basis `(q₁, p₁, …, qₙ, pₙ)`
(`TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily.exists_posDef_mem_span_iff`). In
particular every form in the span of such a family is a combination `∑ₖ cₖ Iₖ` of harmonic
oscillators in these common coordinates. For a single positive definite form this is Williamson's
theorem `TauCeti.SymplecticForm.exists_isDarbouxBasis_eq_sum_smul_elliptic_of_posDef`; the point
here is that one Darboux basis serves the whole family.

The proof has three steps.

* **The complex structure of `P` is a polynomial in `A_P`.** For a positive definite `P`,
  Williamson's theorem gives a compatible complex structure `J` and a Darboux basis with
  `pₖ = J qₖ` on which `A_P = -νₖ J` with `νₖ > 0`. Since `A_P² = -νₖ²` on the `k`-th plane, a
  Lagrange interpolating polynomial `s` with `s(-νₖ²) = 1 / νₖ` gives `J = -A_P s(A_P²)`
  (`TauCeti.SymplecticForm.exists_compatible_mem_adjoin_hamiltonianEnd_of_posDef`). Hence every
  endomorphism commuting with `A_P` is `J`-complex-linear
  (`TauCeti.SymplecticForm.exists_compatible_forall_isComplexLinearMap_of_commute_hamiltonianEnd`).
* **Simultaneous diagonalization.** The `A_{Q i}` commute with each other and with `A_P`, since
  `𝔥` is abelian, so they are commuting `J`-complex-linear elements of `sp(V, ω)`. They act on
  every line `span(qₖ, J qₖ)` of a common Darboux basis by complex numbers
  (`TauCeti.SymplecticForm.exists_isDarbouxBasis_forall_apply_eq_of_skewAdjoint`), which are
  purely imaginary because `polar (Q i)` is symmetric
  (`TauCeti.SymplecticForm.IsDarbouxBasis.eq_zero_of_hamiltonianEnd_apply_eq`). So every `Q i`
  is a combination of the elliptic blocks of that basis.
* **Equality of spans.** The elliptic blocks Poisson-commute with every `Q i`, and a Cartan
  subalgebra is its own centralizer
  (`IsNondegenerateQuadraticFamily.mem_span_of_forall_quadraticPoissonBracket_eq_zero` in the
  namespace `TauCeti.SymplecticForm`), so the blocks lie in the span of `Q`.

Conversely the total oscillator `∑ₖ Iₖ` is positive definite
(`TauCeti.SymplecticForm.posDef_sum_elliptic`). The hyperbolic and focus-focus cases of
Williamson's classification are not treated here.

## Main results

All declarations are in the namespace `TauCeti.SymplecticForm`.

* `exists_compatible_mem_adjoin_hamiltonianEnd_of_posDef`: a compatible complex structure adapted
  to a positive definite `P` is a polynomial in `A_P`.
* `exists_compatible_forall_isComplexLinearMap_of_commute_hamiltonianEnd`: every endomorphism
  commuting with `A_P` is complex linear for it.
* `IsNondegenerateQuadraticFamily.exists_isDarbouxBasis_span_eq_span_elliptic`: a nondegenerate
  family whose span contains a positive definite form spans the elliptic blocks of a Darboux basis.
* `IsNondegenerateQuadraticFamily.exists_posDef_mem_span_iff`: this characterizes the
  nondegenerate families of purely elliptic type.

## References

* J. Williamson, *On the algebraic problem concerning the normal forms of linear dynamical
  systems*, American Journal of Mathematics 58 (1936), 141–163.
* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Appendix 6.
* A. V. Bolsinov and A. T. Fomenko, *Integrable Hamiltonian Systems: Geometry, Topology,
  Classification*, Chapman & Hall/CRC, 2004, Section 1.8.
-/

public section

open Module Polynomial

namespace TauCeti.SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] {ω : SymplecticForm V}
  {P : QuadraticForm ℝ V}

variable (ω) in
/-- **The complex structure of a positive definite Hamiltonian is a polynomial in it.** For a
positive definite quadratic form `P` there is a complex structure `J` compatible with `ω` lying in
the subalgebra of `End(V)` generated by the Hamiltonian endomorphism `A_P`. -/
theorem exists_compatible_mem_adjoin_hamiltonianEnd_of_posDef (hP : P.PosDef) :
    ∃ J : AlmostComplexStructure V, ω.Compatible J ∧
      J.toLinearMap ∈ Algebra.adjoin ℝ {ω.hamiltonianEnd P} := by
  obtain ⟨J, n, b, ν, hJ, -, hbJ, hν, hA⟩ :=
    ω.exists_compatible_isDarbouxBasis_hamiltonianEnd_apply_eq_of_posDef hP
  set A := ω.hamiltonianEnd P
  -- Every basis vector of the `k`-th plane is an eigenvector of `A²` with eigenvalue `-νₖ²`.
  have hA2 (k : Fin n) (a : Fin 2) : (A * A).HasEigenvector (-ν k ^ 2) (b (k, a)) := by
    refine ⟨Module.End.mem_eigenspace_iff.2 ?_, b.ne_zero _⟩
    obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
    · rw [mul_apply_eq_comp, (hA k).1, map_smul, (hA k).2, smul_smul]
      ring_nf
    · rw [mul_apply_eq_comp, (hA k).2, map_smul, (hA k).1, smul_smul]
      ring_nf
  -- A Lagrange polynomial `s` with `s(-νₖ²) = 1 / νₖ`.
  let s : ℝ[X] := Lagrange.interpolate (Finset.univ.image fun k ↦ -ν k ^ 2) id
    fun x ↦ (√(-x))⁻¹
  have hs (k : Fin n) : s.eval (-ν k ^ 2) = (ν k)⁻¹ := by
    have := Lagrange.eval_interpolate_at_node (fun x ↦ (√(-x))⁻¹) (Set.injOn_id _)
      (Finset.mem_image_of_mem (fun k ↦ -ν k ^ 2) (Finset.mem_univ k))
    rw [id, neg_neg, Real.sqrt_sq (hν k).le] at this
    exact this
  -- On the `k`-th plane `J = -A / νₖ`, so `J = -A s(A²)`.
  have hJA : J.toLinearMap = -(A * aeval (A * A) s) := by
    refine b.ext fun ⟨k, a⟩ ↦ ?_
    rw [LinearMap.neg_apply, mul_apply_eq_comp,
      Module.End.aeval_apply_of_hasEigenvector (hA2 k a), hs, map_smul]
    obtain rfl | rfl : a = 0 ∨ a = 1 := by omega
    · rw [(hA k).1, ← hbJ, smul_smul, mul_neg, inv_mul_cancel₀ (hν k).ne', neg_smul, one_smul,
        neg_neg]
    · rw [(hA k).2, smul_smul, inv_mul_cancel₀ (hν k).ne', one_smul, hbJ]
      exact J.apply_apply _
  refine ⟨J, hJ, ?_⟩
  rw [hJA]
  refine neg_mem (mul_mem (Algebra.self_mem_adjoin_singleton ℝ A) ?_)
  rw [show A * A = aeval A (X * X : ℝ[X]) by simp, ← aeval_comp]
  exact aeval_mem_adjoin_singleton ℝ _

variable (ω) in
/-- For a positive definite quadratic form `P` there is a complex structure `J` compatible with `ω`
for which every endomorphism commuting with the Hamiltonian endomorphism `A_P` is complex linear.
-/
theorem exists_compatible_forall_isComplexLinearMap_of_commute_hamiltonianEnd (hP : P.PosDef) :
    ∃ J : AlmostComplexStructure V, ω.Compatible J ∧
      ∀ B : Module.End ℝ V, Commute B (ω.hamiltonianEnd P) → IsComplexLinearMap J J B := by
  obtain ⟨J, hJ, hJA⟩ := ω.exists_compatible_mem_adjoin_hamiltonianEnd_of_posDef hP
  exact ⟨J, hJ, fun B hB ↦ (Algebra.commute_of_mem_adjoin_singleton_of_commute hJA hB).eq⟩

namespace IsNondegenerateQuadraticFamily

variable {ι : Type*} {Q : ι → QuadraticForm ℝ V}

/-- **Williamson's classification, elliptic case.** If the span of a nondegenerate family `Q` of
quadratic forms contains a positive definite form, then there is a Darboux basis whose elliptic
blocks `Iₖ = (xₖ² + yₖ²) / 2` span the same space as `Q`. -/
theorem exists_isDarbouxBasis_span_eq_span_elliptic (h : ω.IsNondegenerateQuadraticFamily Q)
    (hP : P ∈ Submodule.span ℝ (Set.range Q)) (hPpos : P.PosDef) :
    ∃ (n : ℕ) (b : Basis (Fin n × Fin 2) ℝ V), ω.IsDarbouxBasis b ∧
      Submodule.span ℝ (Set.range Q) = Submodule.span ℝ (Set.range (elliptic b)) := by
  obtain ⟨J, hJ, hJcomm⟩ :=
    ω.exists_compatible_forall_isComplexLinearMap_of_commute_hamiltonianEnd hPpos
  -- The `A_{Q i}` are commuting `J`-complex-linear elements of `sp(V, ω)`.
  obtain ⟨n, b, c, hb, -, hc⟩ := exists_isDarbouxBasis_forall_apply_eq_of_skewAdjoint hJ
    (fun i ↦ ω.hamiltonianEnd (Q i))
    (fun i j _ ↦ (quadraticPoissonBracket_eq_zero_iff ω).1 (h.quadraticPoissonBracket_eq_zero i j))
    (fun i ↦ ω.hamiltonianEnd_mem_skewAdjointLieSubalgebra (Q i)) fun i ↦
      hJcomm _ <| (quadraticPoissonBracket_eq_zero_iff ω).1 <|
        ω.quadraticPoissonBracket_eq_zero_of_mem_span h.quadraticPoissonBracket_eq_zero
          (Submodule.subset_span ⟨i, rfl⟩) hP
  -- Each `A_{Q i}` rotates every plane `span(qₖ, pₖ)`, so `Q i = ∑ₖ -(Im cᵢₖ) Iₖ`.
  have hQ (i : ι) : Q i = ∑ k, -(c i k).im • elliptic b k :=
    hb.eq_sum_smul_elliptic_of_hamiltonianEnd_apply_eq fun k ↦ by
      rw [(hc i k).1, (hc i k).2, hb.eq_zero_of_hamiltonianEnd_apply_eq (hc i k).1 (hc i k).2,
        zero_smul, zero_smul, zero_add, add_zero, neg_neg]
      exact ⟨rfl, rfl⟩
  refine ⟨n, b, hb, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)⟩
  · rintro _ ⟨i, rfl⟩
    rw [hQ i]
    exact Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  -- The elliptic blocks commute with every `Q i`, so they lie in the Cartan subalgebra.
  · rintro _ ⟨k, rfl⟩
    refine h.mem_span_of_forall_quadraticPoissonBracket_eq_zero fun i ↦ ?_
    rw [quadraticPoissonBracket_eq_zero_iff, hQ i, map_sum]
    refine Commute.sum_right _ _ _ fun l _ ↦ ?_
    rw [map_smul]
    exact ((quadraticPoissonBracket_eq_zero_iff ω).1
      (hb.quadraticPoissonBracket_elliptic k l)).smul_right _

/-- **Nondegenerate families of elliptic type.** The span of a nondegenerate family `Q` of
quadratic forms contains a positive definite form exactly when it is the span of the elliptic
blocks `Iₖ = (xₖ² + yₖ²) / 2` of some Darboux basis. -/
theorem exists_posDef_mem_span_iff (h : ω.IsNondegenerateQuadraticFamily Q) :
    (∃ P ∈ Submodule.span ℝ (Set.range Q), P.PosDef) ↔
      ∃ (n : ℕ) (b : Basis (Fin n × Fin 2) ℝ V), ω.IsDarbouxBasis b ∧
        Submodule.span ℝ (Set.range Q) = Submodule.span ℝ (Set.range (elliptic b)) := by
  refine ⟨fun ⟨P, hP, hPpos⟩ ↦ h.exists_isDarbouxBasis_span_eq_span_elliptic hP hPpos,
    fun ⟨n, b, _, hspan⟩ ↦ ⟨∑ k, elliptic b k, ?_, posDef_sum_elliptic b⟩⟩
  rw [hspan]
  exact Submodule.sum_mem _ fun k _ ↦ Submodule.subset_span ⟨k, rfl⟩

end IsNondegenerateQuadraticFamily

end TauCeti.SymplecticForm
