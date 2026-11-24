/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.Toral
public import TauCeti.Geometry.Symplectic.Restrict
public import TauCeti.Geometry.Symplectic.Spectrum
import Mathlib.LinearAlgebra.Semisimple
import TauCeti.LinearAlgebra.Eigenspace.Commute
import TauCeti.LinearAlgebra.QuadraticForm.Prod

/-!
# Splitting nondegenerate quadratic families along symplectic decompositions

Let `(V, ω)` be a finite-dimensional real symplectic vector space and `Q` a nondegenerate family of
quadratic forms on it (`TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily`): the Hamiltonian
endomorphisms `A_{Q i}` generate a Cartan subalgebra `𝔥` of `sp(V, ω)`. Williamson's
classification of such families proceeds by splitting `V` into `ω`-orthogonal symplectic summands
preserved by `𝔥`, such as the sums of generalized eigenspaces of one element for its real,
imaginary and complex eigenvalues, and classifying the family on each summand. This file supplies
the splitting step: nondegeneracy, and the span of the family, decompose along any such summand.

On a direct sum `(V₁ × V₂, ω₁ ⊕ ω₂)`, let `Q₁` and `Q₂` be families on the two summands and write
`Q₁ ⊕ 0` and `0 ⊕ Q₂` for the two families extended by zero.

* The family obtained by concatenating `Q₁ ⊕ 0` and `0 ⊕ Q₂` is nondegenerate exactly when `Q₁`
  and `Q₂` both are (`TauCeti.SymplecticForm.isNondegenerateQuadraticFamily_sumElim_prod_iff`).
  No compatibility between the two families is needed: a Cartan subalgebra of a symplectic Lie
  algebra kills no nonzero vector
  (`IsNondegenerateQuadraticFamily.eq_zero_of_forall_hamiltonianEnd_apply_eq_zero`),
  so no off-diagonal endomorphism normalizes `𝔥₁ × 𝔥₂`.
* A nondegenerate family of block-diagonal forms `Q₁ i ⊕ Q₂ i` has the same span as the
  concatenation of `Q₁ ⊕ 0` and `0 ⊕ Q₂`
  (`TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily.span_range_prod_eq`): `Q₁ i ⊕ 0`
  Poisson-commutes with the family, so it lies in its span. Hence the families `Q₁` and `Q₂` are
  nondegenerate (`TauCeti.SymplecticForm.isNondegenerateQuadraticFamily_prod_iff`).

Inside `V`, a symplectic subspace `L` preserved by every `A_{Q i}` splits `V = L ⊕ L^ω`, where
`L^ω` is preserved too, and the restrictions of a nondegenerate family to `L` and `L^ω` are
nondegenerate (`TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily.restrict`,
`TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily.restrict_orthogonal`). For a form `P` in
the span of the family and an even polynomial `p`, the vectors killed by a power of `p(A_P)` form
such a subspace (`IsNondegenerateQuadraticFamily.restrict_maxGenEigenspace_aeval`). The
Hamiltonian endomorphism of the restriction of a form to such a subspace is the restriction of its
Hamiltonian endomorphism (`TauCeti.SymplecticForm.hamiltonianEnd_comp_subtype`). Since `A_P` is
semisimple, `p(A_P)` vanishes on that subspace
(`Module.End.IsSemisimple.aeval_apply_eq_zero_of_mem_maxGenEigenspace`), and polynomials in `A_P`
commute with the Hamiltonian endomorphisms of the family
(`TauCeti.SymplecticForm.commute_aeval_hamiltonianEnd_of_mem_span`).

On a product of two symplectic planes, any two nondegenerate forms on the planes, extended by zero,
form a nondegenerate family
(`TauCeti.SymplecticForm.isNondegenerateQuadraticFamily_prod_of_finrank_eq_two`).

## Main results

* `IsNondegenerateQuadraticFamily.eq_zero_of_forall_hamiltonianEnd_apply_eq_zero`:
  the Hamiltonian endomorphisms of a nondegenerate family have no common nonzero null vector.
* `TauCeti.SymplecticForm.isNondegenerateQuadraticFamily_sumElim_prod_iff`: direct sums of
  families are nondegenerate exactly when both summands are.
* `TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily.span_range_prod_eq`,
  `TauCeti.SymplecticForm.isNondegenerateQuadraticFamily_prod_iff`: a nondegenerate family of
  block-diagonal forms splits into nondegenerate families on the two summands.
* `TauCeti.SymplecticForm.apply_mem_orthogonal_of_mem_skewAdjointLieSubalgebra`: an element of
  `sp(V, ω)` preserving a subspace preserves its symplectic complement.
* `TauCeti.SymplecticForm.comp_prodEquivOfIsCompl_eq_prod`: along `L × L^ω ≃ V`, a quadratic form
  whose Hamiltonian endomorphism preserves a symplectic subspace `L` is the direct sum of its
  restrictions to `L` and `L^ω`.
* `TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily.restrict`,
  `TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily.restrict_orthogonal`: restrictions of a
  nondegenerate family to an invariant symplectic subspace and its symplectic complement are
  nondegenerate.
* `TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily.restrict_maxGenEigenspace_aeval`:
  restrictions of a nondegenerate family to the generalized eigenspaces cut out by even
  polynomials in one of its Hamiltonian endomorphisms are nondegenerate.
* `TauCeti.SymplecticForm.commute_aeval_hamiltonianEnd_of_mem_span`: for `P` and `R` in the span
  of a Poisson-commuting family, polynomials in `A_P` commute with `A_R`.

## References

* J. Williamson, *On the algebraic problem concerning the normal forms of linear dynamical
  systems*, American Journal of Mathematics 58 (1936), 141–163.
* A. V. Bolsinov and A. T. Fomenko, *Integrable Hamiltonian Systems: Geometry, Topology,
  Classification*, Chapman & Hall/CRC, 2004, Section 1.8.
-/

public section

open Module Polynomial

namespace TauCeti.SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] {ω : SymplecticForm V}
  {ι κ : Type*}

/-! ### Common null vectors -/

/-- **A nondegenerate family has no common null vector.** If every Hamiltonian endomorphism of a
nondegenerate family kills `v`, then `v = 0`. -/
theorem IsNondegenerateQuadraticFamily.eq_zero_of_forall_hamiltonianEnd_apply_eq_zero
    {Q : ι → QuadraticForm ℝ V} (h : ω.IsNondegenerateQuadraticFamily Q) {v : V}
    (hv : ∀ i, ω.hamiltonianEnd (Q i) v = 0) : v = 0 := by
  -- The form `R = (ω v ·)²` has Hamiltonian endomorphism `x ↦ 2 ω v x • v`, which commutes with the
  -- family and is nilpotent; it lies in the span of the family, so it is also semisimple.
  set f := ω.toBilinForm v
  set R := QuadraticMap.linMulLin f f
  have hR : ω.hamiltonianEnd R = (2 : ℝ) • f.smulRight v := by
    refine (ω.eq_hamiltonianEnd_iff.2 fun x y ↦ ?_).symm
    simp only [LinearMap.smul_apply, LinearMap.smulRight_apply, map_smul, LinearMap.smul_apply,
      QuadraticMap.polar, R, QuadraticMap.linMulLin_apply, map_add, smul_eq_mul]
    simp only [f]
    ring
  -- `ω v (A_{Q i} x) = -ω (A_{Q i} v) x = 0`.
  have hf (i : ι) (x : V) : f (ω.hamiltonianEnd (Q i) x) = 0 := by
    have := ω.apply_hamiltonianEnd_right (Q i) v x
    rw [← ω.apply_hamiltonianEnd (Q i) v x, hv i] at this
    simpa [f] using this
  have hmem : R ∈ Submodule.span ℝ (Set.range Q) :=
    h.mem_span_of_forall_quadraticPoissonBracket_eq_zero fun i ↦ by
      rw [quadraticPoissonBracket_eq_zero_iff, hR]
      ext x
      simp [hf, hv]
  -- `A_R` is semisimple, and `A_R² = 0` since `ω v v = 0`, so `A_R = 0`.
  have hnil : IsNilpotent (ω.hamiltonianEnd R) := ⟨2, by ext x; simp [hR, pow_two, f]⟩
  have h0 :=
    Module.End.eq_zero_of_isNilpotent_isSemisimple hnil (h.isSemisimple_hamiltonianEnd hmem)
  by_contra hv0
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra! H
    exact hv0 (ω.nondegenerate.1 v H)
  have := LinearMap.congr_fun h0 x
  simp [hR, hx, hv0] at this

/-! ### Direct sums -/

section Prod

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℝ V₁] [FiniteDimensional ℝ V₁]
  [AddCommGroup V₂] [Module ℝ V₂] [FiniteDimensional ℝ V₂]
  {ω₁ : SymplecticForm V₁} {ω₂ : SymplecticForm V₂}

/-- A quadratic form on `V₁ × V₂` whose Poisson brackets with two nondegenerate families extended
by zero lie in the span of these is a direct sum. -/
private theorem exists_eq_prod_of_forall_quadraticPoissonBracket_mem_span
    {Q₁ : ι → QuadraticForm ℝ V₁} {Q₂ : κ → QuadraticForm ℝ V₂}
    (h₁ : ω₁.IsNondegenerateQuadraticFamily Q₁) (h₂ : ω₂.IsNondegenerateQuadraticFamily Q₂)
    {R : QuadraticForm ℝ (V₁ × V₂)}
    (hR : ∀ k, (ω₁.prod ω₂).quadraticPoissonBracket R
      (Sum.elim (fun i ↦ (Q₁ i).prod 0) (fun j ↦ (0 : QuadraticForm ℝ V₁).prod (Q₂ j)) k) ∈
        Submodule.span ℝ (Set.range
          (Sum.elim (fun i ↦ (Q₁ i).prod 0) fun j ↦ (0 : QuadraticForm ℝ V₁).prod (Q₂ j)))) :
    ∃ (R₁ : QuadraticForm ℝ V₁) (R₂ : QuadraticForm ℝ V₂), R = R₁.prod R₂ := by
  set S := Sum.elim (fun i ↦ (Q₁ i).prod 0) fun j ↦ (0 : QuadraticForm ℝ V₁).prod (Q₂ j)
  set A := (ω₁.prod ω₂).hamiltonianEnd R
  -- The brackets of `R` with the family lie in its span, so they are direct sums and their
  -- Hamiltonian endomorphisms preserve both summands.
  have hprod (k : ι ⊕ κ) : ∃ (a : Module.End ℝ V₁) (b : Module.End ℝ V₂),
      (ω₁.prod ω₂).hamiltonianEnd ((ω₁.prod ω₂).quadraticPoissonBracket R (S k)) =
        a.prodMap b := by
    obtain ⟨P₁, -, P₂, -, hP⟩ := QuadraticMap.mem_span_range_sumElim_prod_iff.1 (hR k)
    exact ⟨_, _, by rw [← hP, hamiltonianEnd_prod]⟩
  -- Hence `A_R` preserves both summands: the `V₁`-component of `A_R (0, w)` is killed by every
  -- `A_{Q₁ i}`, and the `V₂`-component of `A_R (v, 0)` by every `A_{Q₂ j}`.
  have h₁₂ (w : V₂) : (A (0, w)).1 = 0 := by
    refine h₁.eq_zero_of_forall_hamiltonianEnd_apply_eq_zero fun i ↦ ?_
    obtain ⟨a, b, hab⟩ := hprod (.inl i)
    have := congr(($hab (0, w)).1)
    simpa [hamiltonianEnd_quadraticPoissonBracket, Ring.lie_def, Prod.mk_zero_zero, S, A]
      using this
  have h₂₁ (v : V₁) : (A (v, 0)).2 = 0 := by
    refine h₂.eq_zero_of_forall_hamiltonianEnd_apply_eq_zero fun j ↦ ?_
    obtain ⟨a, b, hab⟩ := hprod (.inr j)
    have := congr(($hab (v, 0)).2)
    simpa [hamiltonianEnd_quadraticPoissonBracket, Ring.lie_def, Prod.mk_zero_zero, S, A]
      using this
  have hA : A = (LinearMap.fst ℝ V₁ V₂ ∘ₗ A ∘ₗ LinearMap.inl ℝ V₁ V₂).prodMap
      (LinearMap.snd ℝ V₁ V₂ ∘ₗ A ∘ₗ LinearMap.inr ℝ V₁ V₂) := by
    refine LinearMap.ext fun ⟨v, w⟩ ↦ ?_
    rw [← add_zero v, ← zero_add w, ← Prod.mk_add_mk, map_add]
    ext <;> simp [h₁₂, h₂₁]
  obtain ⟨R₁, R₂, rfl, -, -⟩ := exists_eq_prod_of_hamiltonianEnd_eq_prodMap hA
  exact ⟨R₁, R₂, rfl⟩

/-- **Direct sums of nondegenerate families.** For families `Q₁` and `Q₂` of quadratic forms on
`V₁` and `V₂`, the two families extended by zero form a nondegenerate family on `V₁ × V₂` for the
direct-sum symplectic form exactly when `Q₁` and `Q₂` are both nondegenerate. -/
theorem isNondegenerateQuadraticFamily_sumElim_prod_iff {Q₁ : ι → QuadraticForm ℝ V₁}
    {Q₂ : κ → QuadraticForm ℝ V₂} :
    (ω₁.prod ω₂).IsNondegenerateQuadraticFamily
        (Sum.elim (fun i ↦ (Q₁ i).prod 0) fun j ↦ (0 : QuadraticForm ℝ V₁).prod (Q₂ j)) ↔
      ω₁.IsNondegenerateQuadraticFamily Q₁ ∧ ω₂.IsNondegenerateQuadraticFamily Q₂ := by
  set S := Sum.elim (fun i ↦ (Q₁ i).prod 0) fun j ↦ (0 : QuadraticForm ℝ V₁).prod (Q₂ j)
  constructor
  · intro h
    have hS := h.quadraticPoissonBracket_eq_zero
    have hQ₁ (i j : ι) : ω₁.quadraticPoissonBracket (Q₁ i) (Q₁ j) = 0 := by
      simpa [S] using hS (.inl i) (.inl j)
    have hQ₂ (i j : κ) : ω₂.quadraticPoissonBracket (Q₂ i) (Q₂ j) = 0 := by
      simpa [S] using hS (.inr i) (.inr j)
    -- A form normalizing `Q₁` gives, extended by zero, a form normalizing `S`, and likewise for
    -- `Q₂`.
    refine ⟨isNondegenerateQuadraticFamily_of_forall_mem_span hQ₁ fun R hR ↦ ?_,
      isNondegenerateQuadraticFamily_of_forall_mem_span hQ₂ fun R hR ↦ ?_⟩
    · refine QuadraticMap.prod_zero_mem_span_range_sumElim_prod_iff.1
        (h.mem_span_of_forall_quadraticPoissonBracket_mem_span ?_)
      rintro (i | j)
      · simpa [S] using QuadraticMap.prod_zero_mem_span_range_sumElim_prod_iff.2 (hR i)
      · simp [S]
    · refine QuadraticMap.zero_prod_mem_span_range_sumElim_prod_iff.1
        (h.mem_span_of_forall_quadraticPoissonBracket_mem_span ?_)
      rintro (i | j)
      · simp [S]
      · simpa [S] using QuadraticMap.zero_prod_mem_span_range_sumElim_prod_iff.2 (hR j)
  · rintro ⟨h₁, h₂⟩
    refine isNondegenerateQuadraticFamily_of_forall_mem_span
      (quadraticPoissonBracket_sumElim_prod_eq_zero h₁.quadraticPoissonBracket_eq_zero
        h₂.quadraticPoissonBracket_eq_zero) fun R hR ↦ ?_
    obtain ⟨R₁, R₂, rfl⟩ := exists_eq_prod_of_forall_quadraticPoissonBracket_mem_span h₁ h₂ hR
    -- The two summands normalize `Q₁` and `Q₂`.
    refine QuadraticMap.mem_span_range_sumElim_prod_iff.2 ⟨R₁, ?_, R₂, ?_, rfl⟩
    · refine h₁.mem_span_of_forall_quadraticPoissonBracket_mem_span fun i ↦ ?_
      have := hR (.inl i)
      simp only [S, Sum.elim_inl, quadraticPoissonBracket_prod, quadraticPoissonBracket_zero_right]
        at this
      exact QuadraticMap.prod_zero_mem_span_range_sumElim_prod_iff.1 this
    · refine h₂.mem_span_of_forall_quadraticPoissonBracket_mem_span fun j ↦ ?_
      have := hR (.inr j)
      simp only [S, Sum.elim_inr, quadraticPoissonBracket_prod, quadraticPoissonBracket_zero_right]
        at this
      exact QuadraticMap.zero_prod_mem_span_range_sumElim_prod_iff.1 this

/-- **Products of two symplectic planes.** If `Q₁` and `Q₂` are nondegenerate quadratic forms on
symplectic planes `V₁` and `V₂`, then `Q₁ ⊕ 0` and `0 ⊕ Q₂` form a nondegenerate family on
`V₁ × V₂` for the direct-sum symplectic form. These are the elliptic–elliptic,
elliptic–hyperbolic and hyperbolic–hyperbolic types of Williamson's classification in dimension
four. -/
theorem isNondegenerateQuadraticFamily_prod_of_finrank_eq_two (hV₁ : finrank ℝ V₁ = 2)
    (hV₂ : finrank ℝ V₂ = 2) {Q₁ : QuadraticForm ℝ V₁} {Q₂ : QuadraticForm ℝ V₂}
    (hQ₁ : Q₁.Nondegenerate) (hQ₂ : Q₂.Nondegenerate) :
    (ω₁.prod ω₂).IsNondegenerateQuadraticFamily ![Q₁.prod 0, (0 : QuadraticForm ℝ V₁).prod Q₂] := by
  have h := isNondegenerateQuadraticFamily_sumElim_prod_iff.2
    ⟨(isNondegenerateQuadraticFamily_const_iff (ω := ω₁) (ι := Unit) hV₁ Q₁).2 hQ₁,
      (isNondegenerateQuadraticFamily_const_iff (ω := ω₂) (ι := Unit) hV₂ Q₂).2 hQ₂⟩
  refine (isNondegenerateQuadraticFamily_iff_of_span_eq (congrArg _ ?_)).1 h
  ext
  simp

/-- **Splitting the span of a nondegenerate family of direct sums.** If the direct sums
`Q₁ i ⊕ Q₂ i` form a nondegenerate family on `V₁ × V₂`, then the family has the same span as the
two families `Q₁` and `Q₂` extended by zero: each `Q₁ i ⊕ 0` and each `0 ⊕ Q₂ i` lies in its
span. -/
theorem IsNondegenerateQuadraticFamily.span_range_prod_eq {Q₁ : ι → QuadraticForm ℝ V₁}
    {Q₂ : ι → QuadraticForm ℝ V₂}
    (h : (ω₁.prod ω₂).IsNondegenerateQuadraticFamily fun i ↦ (Q₁ i).prod (Q₂ i)) :
    Submodule.span ℝ (Set.range fun i ↦ (Q₁ i).prod (Q₂ i)) =
      Submodule.span ℝ (Set.range
        (Sum.elim (fun i ↦ (Q₁ i).prod 0) fun i ↦ (0 : QuadraticForm ℝ V₁).prod (Q₂ i))) := by
  have hQ (i j : ι) : ω₁.quadraticPoissonBracket (Q₁ i) (Q₁ j) = 0 ∧
      ω₂.quadraticPoissonBracket (Q₂ i) (Q₂ j) = 0 := by
    simpa using h.quadraticPoissonBracket_eq_zero i j
  -- `Q₁ i ⊕ 0` Poisson-commutes with every `Q₁ j ⊕ Q₂ j`.
  have hmem₁ (i : ι) : (Q₁ i).prod 0 ∈ Submodule.span ℝ (Set.range fun i ↦ (Q₁ i).prod (Q₂ i)) :=
    h.mem_span_of_forall_quadraticPoissonBracket_eq_zero fun j ↦ by simp [(hQ i j).1]
  have hmem₂ (i : ι) : (0 : QuadraticForm ℝ V₁).prod (Q₂ i) ∈
      Submodule.span ℝ (Set.range fun i ↦ (Q₁ i).prod (Q₂ i)) := by
    have : (0 : QuadraticForm ℝ V₁).prod (Q₂ i) = (Q₁ i).prod (Q₂ i) - (Q₁ i).prod 0 := by
      ext
      simp
    rw [this]
    exact sub_mem (Submodule.subset_span ⟨i, rfl⟩) (hmem₁ i)
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨i, rfl⟩
    exact QuadraticMap.mem_span_range_sumElim_prod_iff.2
      ⟨Q₁ i, Submodule.subset_span ⟨i, rfl⟩, Q₂ i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
  · rintro _ ⟨i | i, rfl⟩
    exacts [hmem₁ i, hmem₂ i]

/-- **Nondegenerate families of direct sums.** The direct sums `Q₁ i ⊕ Q₂ i` form a nondegenerate
family on `V₁ × V₂` exactly when `Q₁` and `Q₂` are nondegenerate and the family has the same span
as `Q₁` and `Q₂` extended by zero. The span condition is not automatic: on a product of two
symplectic planes, the single form `Q ⊕ Q` for a positive definite `Q` spans a line in a Cartan
subalgebra of dimension two. -/
theorem isNondegenerateQuadraticFamily_prod_iff {Q₁ : ι → QuadraticForm ℝ V₁}
    {Q₂ : ι → QuadraticForm ℝ V₂} :
    (ω₁.prod ω₂).IsNondegenerateQuadraticFamily (fun i ↦ (Q₁ i).prod (Q₂ i)) ↔
      ω₁.IsNondegenerateQuadraticFamily Q₁ ∧ ω₂.IsNondegenerateQuadraticFamily Q₂ ∧
        Submodule.span ℝ (Set.range fun i ↦ (Q₁ i).prod (Q₂ i)) =
          Submodule.span ℝ (Set.range
            (Sum.elim (fun i ↦ (Q₁ i).prod 0) fun i ↦ (0 : QuadraticForm ℝ V₁).prod (Q₂ i))) := by
  refine ⟨fun h ↦ ?_, fun ⟨h₁, h₂, hs⟩ ↦
    (isNondegenerateQuadraticFamily_iff_of_span_eq hs).2
      (isNondegenerateQuadraticFamily_sumElim_prod_iff.2 ⟨h₁, h₂⟩)⟩
  have hs := h.span_range_prod_eq
  obtain ⟨h₁, h₂⟩ := isNondegenerateQuadraticFamily_sumElim_prod_iff.1
    ((isNondegenerateQuadraticFamily_iff_of_span_eq hs).1 h)
  exact ⟨h₁, h₂, hs⟩

end Prod

/-! ### Invariant symplectic subspaces -/

section Restrict

variable {Q : ι → QuadraticForm ℝ V} {L : Submodule ℝ V}

/-- **Splitting a quadratic form along an invariant symplectic subspace.** If the Hamiltonian
endomorphism of `R` preserves a symplectic subspace `L`, then along the isomorphism
`L × L^ω ≃ V`, `(a, b) ↦ a + b`, the form `R` is the direct sum of its restrictions to `L` and
`L^ω`: the cross term `polar R a b = ω(A_R a, b)` vanishes since `A_R a ∈ L`. -/
theorem comp_prodEquivOfIsCompl_eq_prod (hL : ω.IsSymplectic L) {R : QuadraticForm ℝ V}
    (hR : ∀ v ∈ L, ω.hamiltonianEnd R v ∈ L) :
    R.comp (Submodule.prodEquivOfIsCompl L (ω.orthogonal L) (isSymplectic_iff_isCompl.1 hL) :
        L × ω.orthogonal L →ₗ[ℝ] V) =
      (R.comp L.subtype).prod (R.comp (ω.orthogonal L).subtype) := by
  ext ⟨a, b⟩
  have hab : QuadraticMap.polar R a b = 0 := by
    rw [← ω.apply_hamiltonianEnd]
    exact mem_orthogonal_iff.1 b.property _ (hR a a.property)
  simp only [QuadraticMap.comp_apply, LinearEquiv.coe_coe, Submodule.coe_prodEquivOfIsCompl',
    QuadraticMap.prod_apply, Submodule.subtype_apply]
  rw [QuadraticMap.map_add R, hab, add_zero]

omit [FiniteDimensional ℝ V] in
/-- An element `A` of `sp(V, ω)` preserves the symplectic complement of every subspace it
preserves, since it is skew-adjoint for `ω`. -/
theorem apply_mem_orthogonal_of_mem_skewAdjointLieSubalgebra {A : Module.End ℝ V}
    (hA : A ∈ skewAdjointLieSubalgebra ω.toBilinForm) (hAL : ∀ v ∈ L, A v ∈ L) {v : V}
    (hv : v ∈ ω.orthogonal L) : A v ∈ ω.orthogonal L :=
  mem_orthogonal_iff.2 fun y hy ↦ by
    have := (LinearMap.mem_skewAdjointSubmodule A).1 hA y v
    have h0 : ω (A y) v = 0 := mem_orthogonal_iff.1 hv _ (hAL y hy)
    simpa [h0] using this.symm

/-- Restrictions of a nondegenerate family to an invariant symplectic subspace `L` and to its
symplectic complement are nondegenerate. -/
private theorem IsNondegenerateQuadraticFamily.restrict_and_restrict_orthogonal
    (h : ω.IsNondegenerateQuadraticFamily Q) (hL : ω.IsSymplectic L)
    (hQL : ∀ i, L ∈ Module.End.invtSubmodule (ω.hamiltonianEnd (Q i))) :
    (ω.restrict L hL.nondegenerate_restrict).IsNondegenerateQuadraticFamily
        (fun i ↦ (Q i).comp L.subtype) ∧
      (ω.restrict (ω.orthogonal L)
        hL.orthogonal.nondegenerate_restrict).IsNondegenerateQuadraticFamily
        (fun i ↦ (Q i).comp (ω.orthogonal L).subtype) := by
  -- Along the symplectomorphism `L × L^ω ≃ V`, every `Q i` is the direct sum of its restrictions.
  have he := ω.isSymplectomorphism_prodEquivOfIsCompl (isSymplectic_iff_isCompl.1 hL)
  have hQe : (fun i ↦ (Q i).comp (Submodule.prodEquivOfIsCompl L (ω.orthogonal L)
      (isSymplectic_iff_isCompl.1 hL) : L × ω.orthogonal L →ₗ[ℝ] V)) = fun i ↦
        ((Q i).comp L.subtype).prod ((Q i).comp (ω.orthogonal L).subtype) :=
    funext fun i ↦ comp_prodEquivOfIsCompl_eq_prod hL fun v hv ↦
      (Module.End.mem_invtSubmodule _).1 (hQL i) hv
  have := (isNondegenerateQuadraticFamily_comp_iff he Q).2 h
  rw [hQe] at this
  exact ⟨(isNondegenerateQuadraticFamily_prod_iff.1 this).1,
    (isNondegenerateQuadraticFamily_prod_iff.1 this).2.1⟩

/-- **Restricting a nondegenerate family to an invariant symplectic subspace.** If a symplectic
subspace `L` is preserved by every Hamiltonian endomorphism of a nondegenerate family, the
restrictions of the family to `L` form a nondegenerate family for the restricted symplectic
form. -/
theorem IsNondegenerateQuadraticFamily.restrict (h : ω.IsNondegenerateQuadraticFamily Q)
    (hL : ω.IsSymplectic L) (hQL : ∀ i, L ∈ Module.End.invtSubmodule (ω.hamiltonianEnd (Q i))) :
    (ω.restrict L hL.nondegenerate_restrict).IsNondegenerateQuadraticFamily
      fun i ↦ (Q i).comp L.subtype :=
  (h.restrict_and_restrict_orthogonal hL hQL).1

/-- **Restricting a nondegenerate family to the complement of an invariant symplectic subspace.**
If a symplectic subspace `L` is preserved by every Hamiltonian endomorphism of a nondegenerate
family, the restrictions of the family to the symplectic complement `L^ω` form a nondegenerate
family for the restricted symplectic form. -/
theorem IsNondegenerateQuadraticFamily.restrict_orthogonal
    (h : ω.IsNondegenerateQuadraticFamily Q) (hL : ω.IsSymplectic L)
    (hQL : ∀ i, L ∈ Module.End.invtSubmodule (ω.hamiltonianEnd (Q i))) :
    (ω.restrict (ω.orthogonal L)
      hL.orthogonal.nondegenerate_restrict).IsNondegenerateQuadraticFamily
      fun i ↦ (Q i).comp (ω.orthogonal L).subtype :=
  (h.restrict_and_restrict_orthogonal hL hQL).2

/-- **Restricting a nondegenerate family to a generalized eigenspace.** Let `P` lie in the span of
a nondegenerate family and let `p` be an even polynomial, `p(-X) = p`. The vectors killed by a
power of `p(A_P)` form a symplectic subspace
(`TauCeti.SymplecticForm.isSymplectic_maxGenEigenspace_aeval`), preserved by the family, and the
restrictions of the family to it are nondegenerate. For `p = X² - a²`, `X² + b²` and
`(X² - 2aX + a² + b²)(X² + 2aX + a² + b²)` this splits off the hyperbolic, elliptic and
focus-focus parts of the family. -/
theorem IsNondegenerateQuadraticFamily.restrict_maxGenEigenspace_aeval
    (h : ω.IsNondegenerateQuadraticFamily Q) {P : QuadraticForm ℝ V}
    (hP : P ∈ Submodule.span ℝ (Set.range Q)) {p : ℝ[X]} (hp : p.comp (-X) = p) :
    (ω.restrict ((aeval (ω.hamiltonianEnd P) p).maxGenEigenspace 0)
        (ω.isSymplectic_maxGenEigenspace_aeval (ω.hamiltonianEnd_mem_skewAdjointLieSubalgebra P)
          hp).nondegenerate_restrict).IsNondegenerateQuadraticFamily
      fun i ↦ (Q i).comp ((aeval (ω.hamiltonianEnd P) p).maxGenEigenspace 0).subtype := by
  refine h.restrict (ω.isSymplectic_maxGenEigenspace_aeval
    (ω.hamiltonianEnd_mem_skewAdjointLieSubalgebra P) hp) fun i ↦
      (Module.End.mem_invtSubmodule _).2 <|
        Module.End.mapsTo_genEigenspace_aeval_of_comm ?_ p 0 ⊤
  exact (ω.quadraticPoissonBracket_eq_zero_iff.1 <|
    ω.quadraticPoissonBracket_eq_zero_of_mem_span h.quadraticPoissonBracket_eq_zero
      (Submodule.subset_span ⟨i, rfl⟩) hP).symm

/-- **Hamiltonian endomorphisms of restrictions.** If the Hamiltonian endomorphism of a quadratic
form `R` preserves a symplectic subspace `L`, the Hamiltonian endomorphism of the restriction of
`R` to `L`, for the restricted symplectic form, is the restriction of `A_R`. -/
theorem hamiltonianEnd_comp_subtype (hL : ω.IsSymplectic L) {R : QuadraticForm ℝ V}
    (hR : ∀ v ∈ L, ω.hamiltonianEnd R v ∈ L) :
    (ω.restrict L hL.nondegenerate_restrict).hamiltonianEnd (R.comp L.subtype) =
      (ω.hamiltonianEnd R).restrict hR :=
  ((ω.restrict L hL.nondegenerate_restrict).eq_hamiltonianEnd_iff.2 fun v w ↦ by
    simp [QuadraticMap.polar]).symm

/-- For `P` and `R` in the span of a Poisson-commuting family, every polynomial in `A_P` commutes
with `A_R`. -/
theorem commute_aeval_hamiltonianEnd_of_mem_span
    (hQ : ∀ i j, ω.quadraticPoissonBracket (Q i) (Q j) = 0) {P R : QuadraticForm ℝ V}
    (hP : P ∈ Submodule.span ℝ (Set.range Q)) (hR : R ∈ Submodule.span ℝ (Set.range Q))
    (p : ℝ[X]) : Commute (aeval (ω.hamiltonianEnd P) p) (ω.hamiltonianEnd R) :=
  (Algebra.commute_of_mem_adjoin_singleton_of_commute (aeval_mem_adjoin_singleton ℝ _)
    (ω.quadraticPoissonBracket_eq_zero_iff.1 <|
      ω.quadraticPoissonBracket_eq_zero_of_mem_span hQ hR hP)).symm

end Restrict

end TauCeti.SymplecticForm
