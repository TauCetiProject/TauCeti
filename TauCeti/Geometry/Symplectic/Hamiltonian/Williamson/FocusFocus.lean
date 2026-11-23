/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.FocusFocus
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import TauCeti.Algebra.Lie.SkewAdjoint
import TauCeti.Geometry.Symplectic.Spectrum

/-!
# Williamson's classification: the focus-focus type

Let `(V, ω)` be a four-dimensional real symplectic vector space. The **focus-focus block** of a
Darboux basis `(q₁, p₁, q₂, p₂)` is the pair of quadratic Hamiltonians

`Q₁ = q₁ p₁ + q₂ p₂`,  `Q₂ = q₁ p₂ - q₂ p₁`

(`TauCeti.SymplecticForm.focusFocus`). Their Hamiltonian endomorphisms commute and satisfy
`A_{Q₁}² = 1` and `A_{Q₂}² = -1`. This file proves that these relations characterize the block, and
deduces the focus-focus case of Williamson's classification of Cartan subalgebras of `sp(V, ω)`.

* `TauCeti.SymplecticForm.exists_isDarbouxBasis_apply_eq_of_commute`: if `A₁, A₂ ∈ sp(V, ω)`
  commute with `A₁² = 1` and `A₂² = -1`, some Darboux basis `(q₁, p₁, q₂, p₂)` has `A₁ qᵢ = qᵢ`,
  `A₁ pᵢ = -pᵢ`, `A₂ : q₁ ↦ q₂ ↦ -q₁` and `A₂ : p₁ ↦ p₂ ↦ -p₁`.
* `TauCeti.SymplecticForm.exists_isDarbouxBasis_focusFocus_eq_iff`: **normal form of a
  focus-focus pair.** Two quadratic forms `Q₁`, `Q₂` are the focus-focus block of a Darboux basis
  exactly when they Poisson-commute with `A_{Q₁}² = 1` and `A_{Q₂}² = -1`.
* `TauCeti.SymplecticForm.exists_isDarbouxBasis_span_eq_span_focusFocus_iff`: **Williamson's
  classification, focus-focus type.** A Poisson-commuting family of quadratic forms spans the same
  space as the focus-focus block of a Darboux basis exactly when its span contains a pair with
  `A_{P₁}² = 1` and `A_{P₂}² = -1`. The family is then nondegenerate
  (`isNondegenerateQuadraticFamily_of_mem_span_of_mul_self_eq_one_of_mul_self_eq_neg_one`).

The Darboux basis is built from the eigenspaces `V₊` and `V₋` of the involution `A₁`. Both are
isotropic, since `ω(A₁ u, w) = -ω(u, A₁ w)`, and `A₂` preserves them, acting on each as a complex
structure. Take `q₁ ∈ V₊` nonzero and `q₂ = A₂ q₁`. For a vector `v` with `ω(q₁, v) ≠ 0`, the
projection `m = v - A₁ v` to `V₋` still pairs nontrivially with `q₁`, and a combination `p₁` of
`m` and `A₂ m` has `ω(q₁, p₁) = 1` and `ω(q₂, p₁) = 0`. Then `(q₁, p₁, q₂, A₂ p₁)` is a Darboux
basis (`TauCeti.SymplecticForm.exists_isDarbouxBasis_coe_eq`). For a family whose span contains the
pair, every member Poisson-commutes with both forms, so its Hamiltonian endomorphism is a
combination of `A₁` and `A₂` (`TauCeti.SymplecticForm.exists_eq_smul_add_smul_of_commute`).

## References

* J. Williamson, *On the algebraic problem concerning the normal forms of linear dynamical
  systems*, American Journal of Mathematics 58 (1936), 141–163.
* A. V. Bolsinov and A. T. Fomenko, *Integrable Hamiltonian Systems: Geometry, Topology,
  Classification*, Chapman & Hall/CRC, 2004, Section 1.8.
-/

public section

noncomputable section

open Module

-- `sp(V, ω)` is a Lie subalgebra of `Module.End ℝ V` for the commutator bracket, as in Mathlib's
-- `Mathlib.Algebra.Lie.SkewAdjoint`.
attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti.SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {ω : SymplecticForm V}

/-! ### Darboux bases adapted to a focus-focus pair -/

/-- Let `A₁, A₂ ∈ sp(V, ω)` commute, with `A₁² = 1` and `A₂² = -1`, and let `q ≠ 0` be fixed by
`A₁`. Then some vector `p` negated by `A₁` has `ω(q, p) = 1` and `ω(A₂ q, p) = 0`. -/
private theorem exists_apply_eq_neg_apply_eq_one_apply_eq_zero
    {A₁ A₂ : skewAdjointLieSubalgebra ω.toBilinForm} (h₁ : (A₁ : Module.End ℝ V) * A₁ = 1)
    (h₂ : (A₂ : Module.End ℝ V) * A₂ = -1) (h₁₂ : Commute (A₁ : Module.End ℝ V) A₂) {q : V}
    (hq₀ : q ≠ 0) (hq : (A₁ : Module.End ℝ V) q = q) :
    ∃ p, (A₁ : Module.End ℝ V) p = -p ∧ ω.toBilinForm q p = 1 ∧
      ω.toBilinForm ((A₂ : Module.End ℝ V) q) p = 0 := by
  set a₁ : Module.End ℝ V := (A₁ : Module.End ℝ V)
  set a₂ : Module.End ℝ V := (A₂ : Module.End ℝ V)
  have s₁ (u w : V) : ω.toBilinForm (a₁ u) w = -ω.toBilinForm u (a₁ w) :=
    skewAdjointLieSubalgebra.apply_left A₁ u w
  have s₂ (u w : V) : ω.toBilinForm (a₂ u) w = -ω.toBilinForm u (a₂ w) :=
    skewAdjointLieSubalgebra.apply_left A₂ u w
  obtain ⟨v, hv⟩ : ∃ v, ω.toBilinForm q v ≠ 0 := by
    by_contra! h
    exact hq₀ (ω.nondegenerate.1 q h)
  -- The projection `m = v - A₁ v` of `v` to `V₋` pairs with `q` as `2 ω(q, v) ≠ 0`.
  set m := v - a₁ v with hm_def
  have hm : a₁ m = -m := by
    rw [hm_def, map_sub, ← mul_apply_eq_comp, h₁, one_apply_eq_self, neg_sub]
  set x := ω.toBilinForm q m with hx_def
  set y := ω.toBilinForm (a₂ q) m with hy_def
  have hx : x ≠ 0 := by
    have h := s₁ q v
    rw [hq] at h
    have : x = 2 * ω.toBilinForm q v := by
      rw [hx_def, hm_def, map_sub]
      linarith
    rw [this]
    exact mul_ne_zero two_ne_zero hv
  have hxy : x ^ 2 + y ^ 2 ≠ 0 := by positivity
  -- Since `ω(q, A₂ m) = -y` and `ω(A₂ q, A₂ m) = x`, a combination of `m` and `A₂ m` works.
  have hqa₂m : ω.toBilinForm q (a₂ m) = -y := by rw [hy_def, s₂, neg_neg]
  have ha₂qa₂m : ω.toBilinForm (a₂ q) (a₂ m) = x := by
    rw [s₂, ← mul_apply_eq_comp, h₂, LinearMap.neg_apply, one_apply_eq_self, map_neg, neg_neg]
  refine ⟨(x ^ 2 + y ^ 2)⁻¹ • (x • m - y • a₂ m), ?_, ?_, ?_⟩
  · rw [map_smul, map_sub, map_smul, map_smul, ← mul_apply_eq_comp, h₁₂.eq, mul_apply_eq_comp,
      hm, map_neg]
    module
  · rw [map_smul, map_sub, map_smul, map_smul, hqa₂m, ← hx_def, smul_eq_mul, smul_eq_mul,
      smul_eq_mul]
    field_simp
    ring
  · rw [map_smul, map_sub, map_smul, map_smul, ha₂qa₂m, ← hy_def, smul_eq_mul, smul_eq_mul,
      smul_eq_mul]
    ring

/-- **Darboux bases adapted to a focus-focus pair.** In a four-dimensional symplectic vector
space, let `A₁, A₂ ∈ sp(V, ω)` commute, with `A₁² = 1` and `A₂² = -1`. Then some Darboux basis
`(q₁, p₁, q₂, p₂)` has `A₁ qᵢ = qᵢ` and `A₁ pᵢ = -pᵢ`, while `A₂` sends `q₁ ↦ q₂ ↦ -q₁` and
`p₁ ↦ p₂ ↦ -p₁`. -/
theorem exists_isDarbouxBasis_apply_eq_of_commute (hV : finrank ℝ V = 4)
    {A₁ A₂ : skewAdjointLieSubalgebra ω.toBilinForm} (h₁ : (A₁ : Module.End ℝ V) * A₁ = 1)
    (h₂ : (A₂ : Module.End ℝ V) * A₂ = -1) (h₁₂ : Commute (A₁ : Module.End ℝ V) A₂) :
    ∃ b : Basis (Fin 2 × Fin 2) ℝ V, ω.IsDarbouxBasis b ∧
      (∀ a, (A₁ : Module.End ℝ V) (b a) = if a.2 = 0 then b a else -b a) ∧
      ∀ a, (A₂ : Module.End ℝ V) (b a) = if a.1 = 0 then b (1, a.2) else -b (0, a.2) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have : FiniteDimensional ℝ V := Module.finite_of_finrank_pos (by omega)
  -- `q = q₁` is a nonzero vector of `V₊`, and `p = p₁ ∈ V₋` is dual to it.
  obtain ⟨q, hq₀, hq⟩ := exists_ne_zero_apply_eq_self h₁
  obtain ⟨p, hp, hqp, ha₂qp⟩ := exists_apply_eq_neg_apply_eq_one_apply_eq_zero h₁ h₂ h₁₂ hq₀ hq
  set a₁ : Module.End ℝ V := (A₁ : Module.End ℝ V)
  set a₂ : Module.End ℝ V := (A₂ : Module.End ℝ V)
  have k₂ (u : V) : a₂ (a₂ u) = -u := by
    rw [← mul_apply_eq_comp, h₂, LinearMap.neg_apply, one_apply_eq_self]
  have k₁₂ (u : V) : a₁ (a₂ u) = a₂ (a₁ u) := by
    rw [← mul_apply_eq_comp, h₁₂.eq, mul_apply_eq_comp]
  have s₂ (u w : V) : ω.toBilinForm (a₂ u) w = -ω.toBilinForm u (a₂ w) :=
    skewAdjointLieSubalgebra.apply_left A₂ u w
  have hqa₂p : ω.toBilinForm q (a₂ p) = 0 := by rw [← neg_eq_zero, ← s₂, ha₂qp]
  have ha₂qa₂p : ω.toBilinForm (a₂ q) (a₂ p) = 1 := by rw [s₂, k₂, map_neg, neg_neg, hqp]
  -- `q, A₂ q ∈ V₊` and `p, A₂ p ∈ V₋`, and both eigenspaces of `A₁` are isotropic.
  have hq₂ : a₁ (a₂ q) = a₂ q := by rw [k₁₂, hq]
  have hp₂ : a₁ (a₂ p) = -a₂ p := by rw [k₁₂, hp, map_neg]
  have iso {μ : ℝ} (hμ : μ ≠ 0) {u w : V} (hu : a₁ u = μ • u) (hw : a₁ w = μ • w) :
      ω.toBilinForm u w = 0 :=
    isIsotropic_iff.1 (isIsotropic_genEigenspace ω A₁.property hμ 1) _
      (Module.End.mem_genEigenspace_one.2 hu) _ (Module.End.mem_genEigenspace_one.2 hw)
  obtain ⟨b, hb, hbe⟩ := exists_isDarbouxBasis_coe_eq (ω := ω)
    (v := fun c ↦ ![![q, p], ![a₂ q, a₂ p]] c.1 c.2) (by omega)
    (fun i j ↦ by
      beta_reduce
      fin_cases i <;> fin_cases j <;>
        exact iso one_ne_zero (by simp [hq, hq₂]) (by simp [hq, hq₂]))
    (fun i j ↦ by
      beta_reduce
      fin_cases i <;> fin_cases j <;>
        exact iso (μ := -1) (by norm_num) (by simp [hp, hp₂]) (by simp [hp, hp₂]))
    (fun i j ↦ by
      beta_reduce
      fin_cases i <;> fin_cases j <;> simp [hqp, ha₂qp, hqa₂p, ha₂qa₂p])
  refine ⟨b, hb, fun c ↦ ?_, fun c ↦ ?_⟩ <;> rw [hbe] <;> obtain ⟨i, j⟩ := c <;>
    fin_cases i <;> fin_cases j <;> simp [hq, hp, k₁₂, k₂]

/-! ### Quadratic forms -/

variable [FiniteDimensional ℝ V]

/-- **Normal form of a focus-focus pair.** On a four-dimensional symplectic vector space, two
quadratic forms `Q₁`, `Q₂` are the focus-focus block `q₁ p₁ + q₂ p₂`, `q₁ p₂ - q₂ p₁` of some
Darboux basis `(q₁, p₁, q₂, p₂)` exactly when their Hamiltonian endomorphisms satisfy
`A_{Q₁}² = 1` and `A_{Q₂}² = -1` and the forms Poisson-commute. -/
theorem exists_isDarbouxBasis_focusFocus_eq_iff (hV : finrank ℝ V = 4)
    {Q₁ Q₂ : QuadraticForm ℝ V} :
    (∃ b : Basis (Fin 2 × Fin 2) ℝ V, ω.IsDarbouxBasis b ∧ focusFocus b = ![Q₁, Q₂]) ↔
      ω.hamiltonianEnd Q₁ * ω.hamiltonianEnd Q₁ = 1 ∧
        ω.hamiltonianEnd Q₂ * ω.hamiltonianEnd Q₂ = -1 ∧ ω.quadraticPoissonBracket Q₁ Q₂ = 0 := by
  constructor
  · rintro ⟨b, hb, h⟩
    obtain rfl : focusFocus b 0 = Q₁ := congrFun h 0
    obtain rfl : focusFocus b 1 = Q₂ := congrFun h 1
    exact ⟨hb.hamiltonianEnd_focusFocus_zero_mul_self, hb.hamiltonianEnd_focusFocus_one_mul_self,
      hb.quadraticPoissonBracket_focusFocus⟩
  · rintro ⟨h₁, h₂, h₁₂⟩
    obtain ⟨b, hb, hA₁, hA₂⟩ := exists_isDarbouxBasis_apply_eq_of_commute hV
      (A₁ := ω.hamiltonianEndEquiv Q₁) (A₂ := ω.hamiltonianEndEquiv Q₂) (by simpa using h₁)
      (by simpa using h₂) (by simpa using (quadraticPoissonBracket_eq_zero_iff ω).1 h₁₂)
    refine ⟨b, hb, funext fun i ↦ ω.hamiltonianEnd_injective (b.ext fun c ↦ ?_)⟩
    fin_cases i
    · simpa [hb.hamiltonianEnd_focusFocus_zero_apply] using (hA₁ c).symm
    · simpa [hb.hamiltonianEnd_focusFocus_one_apply] using (hA₂ c).symm

/-- **Williamson's classification, focus-focus type.** On a four-dimensional symplectic vector
space, a Poisson-commuting family `Q` of quadratic forms spans the same space as the focus-focus
block of some Darboux basis exactly when its span contains forms `P₁`, `P₂` with
`A_{P₁}² = 1` and `A_{P₂}² = -1`. -/
theorem exists_isDarbouxBasis_span_eq_span_focusFocus_iff (hV : finrank ℝ V = 4) {ι : Type*}
    {Q : ι → QuadraticForm ℝ V} (hQ : ∀ i j, ω.quadraticPoissonBracket (Q i) (Q j) = 0) :
    (∃ b : Basis (Fin 2 × Fin 2) ℝ V, ω.IsDarbouxBasis b ∧
        Submodule.span ℝ (Set.range Q) = Submodule.span ℝ (Set.range (focusFocus b))) ↔
      ∃ P₁ ∈ Submodule.span ℝ (Set.range Q), ∃ P₂ ∈ Submodule.span ℝ (Set.range Q),
        ω.hamiltonianEnd P₁ * ω.hamiltonianEnd P₁ = 1 ∧
          ω.hamiltonianEnd P₂ * ω.hamiltonianEnd P₂ = -1 := by
  constructor
  · rintro ⟨b, hb, h⟩
    exact ⟨focusFocus b 0, h ▸ Submodule.subset_span ⟨0, rfl⟩, focusFocus b 1,
      h ▸ Submodule.subset_span ⟨1, rfl⟩, hb.hamiltonianEnd_focusFocus_zero_mul_self,
      hb.hamiltonianEnd_focusFocus_one_mul_self⟩
  · rintro ⟨P₁, hP₁, P₂, hP₂, h₁, h₂⟩
    have hbr {R R' : QuadraticForm ℝ V} (hR : R ∈ Submodule.span ℝ (Set.range Q))
        (hR' : R' ∈ Submodule.span ℝ (Set.range Q)) : ω.quadraticPoissonBracket R R' = 0 :=
      ω.quadraticPoissonBracket_eq_zero_of_mem_span hQ hR hR'
    obtain ⟨b, hb, hbP⟩ :=
      (exists_isDarbouxBasis_focusFocus_eq_iff hV).2 ⟨h₁, h₂, hbr hP₁ hP₂⟩
    refine ⟨b, hb, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)⟩
    · -- Each `Q i` commutes with `A_{P₁}` and `A_{P₂}`, so `A_{Q i}` is a combination of them.
      rintro _ ⟨i, rfl⟩
      have hi := Submodule.subset_span (R := ℝ) (Set.mem_range_self (f := Q) i)
      obtain ⟨s, t, hst⟩ := exists_eq_smul_add_smul_of_commute hV
        (A₁ := ω.hamiltonianEndEquiv P₁) (A₂ := ω.hamiltonianEndEquiv P₂)
        (B := ω.hamiltonianEndEquiv (Q i)) (by simpa using h₁) (by simpa using h₂)
        (by simpa using (quadraticPoissonBracket_eq_zero_iff ω).1 (hbr hP₁ hP₂))
        (by simpa using (quadraticPoissonBracket_eq_zero_iff ω).1 (hbr hP₁ hi))
        (by simpa using (quadraticPoissonBracket_eq_zero_iff ω).1 (hbr hP₂ hi))
      have hQi : Q i = s • focusFocus b 0 + t • focusFocus b 1 := by
        refine ω.hamiltonianEndEquiv.injective ?_
        simp [hst, hbP]
      rw [SetLike.mem_coe, hQi]
      exact add_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
    · rintro _ ⟨i, rfl⟩
      fin_cases i
      · simpa [hbP] using hP₁
      · simpa [hbP] using hP₂

/-- **A Poisson-commuting family containing a focus-focus pair is nondegenerate.** On a
four-dimensional symplectic vector space, if the span of a Poisson-commuting family `Q` of
quadratic forms contains forms `P₁`, `P₂` with `A_{P₁}² = 1` and `A_{P₂}² = -1`, then the
Hamiltonian endomorphisms of `Q` span a Cartan subalgebra of `sp(V, ω)`. -/
theorem isNondegenerateQuadraticFamily_of_mem_span_of_mul_self_eq_one_of_mul_self_eq_neg_one
    (hV : finrank ℝ V = 4) {ι : Type*} {Q : ι → QuadraticForm ℝ V}
    (hQ : ∀ i j, ω.quadraticPoissonBracket (Q i) (Q j) = 0) {P₁ P₂ : QuadraticForm ℝ V}
    (hP₁ : P₁ ∈ Submodule.span ℝ (Set.range Q)) (hP₂ : P₂ ∈ Submodule.span ℝ (Set.range Q))
    (h₁ : ω.hamiltonianEnd P₁ * ω.hamiltonianEnd P₁ = 1)
    (h₂ : ω.hamiltonianEnd P₂ * ω.hamiltonianEnd P₂ = -1) :
    ω.IsNondegenerateQuadraticFamily Q := by
  obtain ⟨b, hb, h⟩ :=
    (exists_isDarbouxBasis_span_eq_span_focusFocus_iff hV hQ).2 ⟨P₁, hP₁, P₂, hP₂, h₁, h₂⟩
  exact (isNondegenerateQuadraticFamily_iff_of_span_eq h).2
    hb.isNondegenerateQuadraticFamily_focusFocus

end TauCeti.SymplecticForm
