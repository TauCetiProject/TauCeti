/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.FocusFocus
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import TauCeti.Algebra.Lie.SkewAdjoint
import TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.Splitting
import TauCeti.Geometry.Symplectic.Plane
import TauCeti.Geometry.Symplectic.Spectrum
import TauCeti.LinearAlgebra.Eigenspace.Commute
import TauCeti.LinearAlgebra.Eigenspace.Semisimple

/-!
# Williamson's classification: the focus-focus type

Let `(V, ω)` be a four-dimensional real symplectic vector space. The **focus-focus block** of a
Darboux basis `(q₁, p₁, q₂, p₂)` is the pair of quadratic Hamiltonians

`Q₁ = q₁ p₁ + q₂ p₂`,  `Q₂ = q₁ p₂ - q₂ p₁`

(`TauCeti.SymplecticForm.focusFocus`). Their Hamiltonian endomorphisms commute and satisfy
`A_{Q₁}² = 1` and `A_{Q₂}² = -1`. This file proves that these relations characterize the block, and
deduces the focus-focus case of Williamson's classification of Cartan subalgebras of `sp(V, ω)`,
first in dimension four and then in every dimension `4n`.

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

## The focus-focus type in every dimension

In a Darboux basis `(q₀, p₀, …, q₂ₙ₋₁, p₂ₙ₋₁)` of a space of dimension `4n`, the
**focus-focus blocks** (`TauCeti.SymplecticForm.focusFocusBlocks`) are the focus-focus pairs of
the planes `2j` and `2j + 1`, for `j < n`:

`Q₁ⱼ = q₂ⱼ p₂ⱼ + q₂ⱼ₊₁ p₂ⱼ₊₁`,  `Q₂ⱼ = q₂ⱼ p₂ⱼ₊₁ - q₂ⱼ₊₁ p₂ⱼ`.

They Poisson-commute
(`TauCeti.SymplecticForm.IsDarbouxBasis.quadraticPoissonBracket_focusFocusBlocks`), and the
Hamiltonian endomorphism of `∑ⱼ (aⱼ Q₁ⱼ + bⱼ Q₂ⱼ)` has the eigenvalues `±aⱼ ± bⱼ i` on the
`j`-th block. Over `ℝ`, a complex eigenvalue `a + bi` of `A ∈ sp(V, ω)` with eigenvector `v + iw`
is recorded as a vector `v ≠ 0` with `A v = a v - b w` and `A w = b v + a w`.

* `IsNondegenerateQuadraticFamily.exists_isDarbouxBasis_span_eq_span_focusFocusBlocks`:
  **Williamson's classification, focus-focus type, in every dimension.** If the span of a
  nondegenerate family `Q` contains a form `P` whose Hamiltonian endomorphism has `dim V / 4`
  distinct eigenvalues in the open first quadrant, then `Q` spans the same space as the
  focus-focus blocks of some Darboux basis.
* `IsNondegenerateQuadraticFamily.exists_mem_span_card_mul_four_eq_finrank_iff`: this
  characterizes the nondegenerate families of focus-focus type.

For an eigenvalue `a + bi`, `a, b > 0`, of `A = A_P`, the vectors killed by a power of
`f(A) = (A² - 2aA + a² + b²)(A² + 2aA + a² + b²)`
(`TauCeti.SymplecticForm.focusFocusPoly`) form a symplectic subspace `G`, since `f` is even, and
the family restricts to a nondegenerate family on `G`
(`TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily.restrict_maxGenEigenspace_aeval`).
Distinct eigenvalues in the first quadrant give coprime polynomials `f`
(`TauCeti.SymplecticForm.isCoprime_focusFocusPoly_focusFocusPoly_comp_neg_X`), so the subspaces
`G` are pairwise `ω`-orthogonal
(`TauCeti.SymplecticForm.apply_eq_zero_of_mem_maxGenEigenspace_aeval_focusFocusPoly`). Each has
dimension at least four, because on a plane `A²` is a homothety and `f(A)` would be invertible
(`TauCeti.SymplecticForm.four_le_finrank_maxGenEigenspace_aeval_focusFocusPoly`); as there are
`dim V / 4` of them, each has dimension exactly four.
Since `A` is semisimple, `f(A)` vanishes on `G`, and there the odd polynomials

`A₁ = ((3a² - b²) A - A³) / (2a(a² + b²))`,  `A₂ = ((3b² - a²) A + A³) / (2b(a² + b²))`

in `A` satisfy `A₁² = 1`, `A₂² = -1` and `A = a A₁ + b A₂`. Their quadratic forms on `G` commute
with the restricted family, so they lie in its span, and the four-dimensional classification
applies on each `G`. The resulting Darboux bases of the subspaces `G` assemble to one of `V`.

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

/-! ### The focus-focus type in every dimension -/

open Polynomial

/-- The real polynomial `(X² - 2aX + a² + b²)(X² + 2aX + a² + b²)`, whose complex roots are
`±a ± bi`. Its generalized kernel at a Hamiltonian endomorphism with eigenvalue `a + bi`,
`a, b ≠ 0`, is a symplectic subspace of dimension at least four
(`four_le_finrank_maxGenEigenspace_aeval_focusFocusPoly`). -/
noncomputable def focusFocusPoly (a b : ℝ) : ℝ[X] :=
  (X ^ 2 - C (2 * a) * X + C (a ^ 2 + b ^ 2)) * (X ^ 2 + C (2 * a) * X + C (a ^ 2 + b ^ 2))

/-- The defining formula of `focusFocusPoly a b`. -/
theorem focusFocusPoly_def (a b : ℝ) :
    focusFocusPoly a b =
      (X ^ 2 - C (2 * a) * X + C (a ^ 2 + b ^ 2)) * (X ^ 2 + C (2 * a) * X + C (a ^ 2 + b ^ 2)) :=
  (rfl)

/-- The value of `(X² - 2aX + a² + b²)(X² + 2aX + a² + b²)` at `x` is
`((x - a)² + b²)((x + a)² + b²)`. -/
theorem aeval_focusFocusPoly {R : Type*} [CommRing R] [Algebra ℝ R] (x : R) (a b : ℝ) :
    aeval x (focusFocusPoly a b) =
      ((x - algebraMap ℝ R a) ^ 2 + algebraMap ℝ R b ^ 2) *
        ((x + algebraMap ℝ R a) ^ 2 + algebraMap ℝ R b ^ 2) := by
  simp only [focusFocusPoly, map_mul, map_add, map_sub, map_pow, aeval_X, aeval_C, map_ofNat]
  ring

/-- The polynomial `focusFocusPoly a b` is even. -/
theorem focusFocusPoly_comp_neg_X (a b : ℝ) :
    (focusFocusPoly a b).comp (-X) = focusFocusPoly a b := by
  simp only [focusFocusPoly, mul_comp, add_comp, sub_comp, pow_comp, X_comp, C_comp]
  ring

/-- The complex roots of `(X² - 2aX + a² + b²)(X² + 2aX + a² + b²)`, `b ≠ 0`, are the numbers
`±a ± bi`, so their real and imaginary parts have absolute values `|a|` and `|b|`. -/
theorem abs_re_eq_and_abs_im_eq_of_aeval_focusFocusPoly_eq_zero {a b : ℝ} (hb : b ≠ 0) {w : ℂ}
    (hw : aeval w (focusFocusPoly a b) = 0) : |w.re| = |a| ∧ |w.im| = |b| := by
  rw [aeval_focusFocusPoly] at hw
  simp only [Complex.coe_algebraMap] at hw
  -- A root of `(w - c)² + b²` has real part `c` and imaginary part `±b`.
  have key {c : ℝ} (h : (w - c) ^ 2 + (b : ℂ) ^ 2 = 0) : w.re = c ∧ |w.im| = |b| := by
    have h1 := congrArg Complex.re h
    have h2 := congrArg Complex.im h
    simp only [pow_two, Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, Complex.add_im, Complex.mul_im,
      Complex.zero_im] at h1 h2
    have hre : w.re = c := by
      by_contra hne
      have him : w.im = 0 := by
        have : (w.re - c) * (2 * w.im) = 0 := by linarith
        simpa [sub_ne_zero.2 hne] using this
      rw [him] at h1
      have : (w.re - c) ^ 2 + b ^ 2 = 0 := by linarith
      exact hb (by nlinarith [sq_nonneg (w.re - c), sq_nonneg b])
    refine ⟨hre, sq_eq_sq_iff_abs_eq_abs _ _ |>.1 ?_⟩
    rw [hre] at h1
    linarith
  rcases mul_eq_zero.1 hw with h | h
  · obtain ⟨h1, h2⟩ := key h
    exact ⟨by rw [h1], h2⟩
  · obtain ⟨h1, h2⟩ := key (c := -a) (by simpa using h)
    exact ⟨by rw [h1, abs_neg], h2⟩

/-- For distinct points `a + bi` and `a' + b'i` of the open first quadrant, the polynomial
`(X² - 2aX + a² + b²)(X² + 2aX + a² + b²)` and the reflection of its analogue for `(a', b')` are
coprime. -/
theorem isCoprime_focusFocusPoly_focusFocusPoly_comp_neg_X {a b a' b' : ℝ} (ha : 0 < a)
    (hb : 0 < b) (ha' : 0 < a') (hb' : 0 < b') (hne : a ≠ a' ∨ b ≠ b') :
    IsCoprime (focusFocusPoly a b) ((focusFocusPoly a' b').comp (-X)) := by
  rw [focusFocusPoly_comp_neg_X]
  refine (isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℝ ℂ _ _).2 fun w ↦ ?_
  by_contra! hw
  obtain ⟨h₁, h₂⟩ := abs_re_eq_and_abs_im_eq_of_aeval_focusFocusPoly_eq_zero hb.ne' hw.1
  obtain ⟨h₁', h₂'⟩ := abs_re_eq_and_abs_im_eq_of_aeval_focusFocusPoly_eq_zero hb'.ne' hw.2
  rw [abs_of_pos ha] at h₁
  rw [abs_of_pos hb] at h₂
  rw [abs_of_pos ha'] at h₁'
  rw [abs_of_pos hb'] at h₂'
  rcases hne with h | h
  · exact h (h₁.symm.trans h₁')
  · exact h (h₂.symm.trans h₂')

/-- For `a, b ≠ 0` the polynomial `(X² - 2aX + a² + b²)(X² + 2aX + a² + b²)` is coprime to
`X² - μ` for every real `μ`: the squares of its roots `±a ± bi` are not real. -/
theorem isCoprime_focusFocusPoly_X_sq_sub_C {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (μ : ℝ) :
    IsCoprime (focusFocusPoly a b) (X ^ 2 - C μ) := by
  refine (isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℝ ℂ _ _).2 fun w ↦ ?_
  by_contra! hw
  obtain ⟨h₁, h₂⟩ := abs_re_eq_and_abs_im_eq_of_aeval_focusFocusPoly_eq_zero hb hw.1
  -- `w² = μ` is real, so `2 w.re w.im = 0`, while `|w.re| = |a|` and `|w.im| = |b|` are positive.
  have hre : w.re ≠ 0 := fun h0 ↦ ha (abs_eq_zero.1 (by rw [← h₁, h0, abs_zero]))
  have him : w.im ≠ 0 := fun h0 ↦ hb (abs_eq_zero.1 (by rw [← h₂, h0, abs_zero]))
  have hsq : w ^ 2 = μ := by simpa [sub_eq_zero] using hw.2
  have h := congrArg Complex.im hsq
  simp only [pow_two, Complex.mul_im, Complex.ofReal_im] at h
  exact mul_ne_zero hre him (by linear_combination h / 2)

omit [FiniteDimensional ℝ V] in
/-- For `A ∈ sp(V, ω)` and distinct points `z` and `z'` of the open first quadrant, `ω` pairs the
vectors killed by a power of `focusFocusPoly z.re z.im` evaluated at `A` trivially with those
killed by a power of `focusFocusPoly z'.re z'.im` evaluated at `A`. -/
theorem apply_eq_zero_of_mem_maxGenEigenspace_aeval_focusFocusPoly {A : Module.End ℝ V}
    (hA : A ∈ skewAdjointLieSubalgebra ω.toBilinForm) {z z' : ℂ} (hz : 0 < z.re ∧ 0 < z.im)
    (hz' : 0 < z'.re ∧ 0 < z'.im) (hzz' : z ≠ z') {v w : V}
    (hv : v ∈ (aeval A (focusFocusPoly z.re z.im)).maxGenEigenspace 0)
    (hw : w ∈ (aeval A (focusFocusPoly z'.re z'.im)).maxGenEigenspace 0) : ω v w = 0 := by
  refine ((LinearMap.mem_skewAdjointSubmodule A).1 hA).apply_eq_zero_of_mem_maxGenEigenspace_aeval
    (isCoprime_focusFocusPoly_focusFocusPoly_comp_neg_X hz.1 hz.2 hz'.1 hz'.2 ?_) hv hw
  by_contra! h
  exact hzz' (Complex.ext h.1 h.2)

/-- **The focus-focus pair as odd polynomials.** For `a, b > 0` there are odd polynomials `p₁`,
`p₂` with `p₁² ≡ 1` and `p₂² ≡ -1` modulo `f = (X² - 2aX + a² + b²)(X² + 2aX + a² + b²)`, namely
`p₁ = ((3a² - b²) X - X³) / (2a(a² + b²))` and `p₂ = ((3b² - a²) X + X³) / (2b(a² + b²))`: on the
roots `±a ± bi` of `f`, they take the values `±1` and `±i`. -/
private theorem exists_odd_mul_self_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ p₁ p₂ s₁ s₂ : ℝ[X], p₁.comp (-X) = -p₁ ∧ p₂.comp (-X) = -p₂ ∧
      p₁ * p₁ = 1 + s₁ * focusFocusPoly a b ∧ p₂ * p₂ = -1 + s₂ * focusFocusPoly a b := by
  set c₁ := (2 * a * (a ^ 2 + b ^ 2))⁻¹
  set c₂ := (2 * b * (a ^ 2 + b ^ 2))⁻¹
  have hc₁ : C c₁ * (2 * C a * (C a ^ 2 + C b ^ 2)) = 1 := by
    have h : c₁ * (2 * a * (a ^ 2 + b ^ 2)) = 1 := inv_mul_cancel₀ (by positivity)
    simpa only [map_mul, map_add, map_pow, map_ofNat, map_one] using congrArg C h
  have hc₂ : C c₂ * (2 * C b * (C a ^ 2 + C b ^ 2)) = 1 := by
    have h : c₂ * (2 * b * (a ^ 2 + b ^ 2)) = 1 := inv_mul_cancel₀ (by positivity)
    simpa only [map_mul, map_add, map_pow, map_ofNat, map_one] using congrArg C h
  refine ⟨C c₁ * (C (3 * a ^ 2 - b ^ 2) * X - X ^ 3), C c₂ * (C (3 * b ^ 2 - a ^ 2) * X + X ^ 3),
    C c₁ ^ 2 * (X ^ 2 - C (4 * a ^ 2)), C c₂ ^ 2 * (X ^ 2 + C (4 * b ^ 2)), ?_, ?_, ?_, ?_⟩
  · simp only [mul_comp, sub_comp, pow_comp, X_comp, C_comp]
    ring
  · simp only [mul_comp, add_comp, pow_comp, X_comp, C_comp]
    ring
  · simp only [focusFocusPoly, map_mul, map_add, map_sub, map_pow, map_ofNat]
    linear_combination (C c₁ * (2 * C a * (C a ^ 2 + C b ^ 2)) + 1) * hc₁
  · simp only [focusFocusPoly, map_mul, map_add, map_sub, map_pow, map_ofNat]
    linear_combination (-(C c₂ * (2 * C b * (C a ^ 2 + C b ^ 2)) + 1)) * hc₂

omit [FiniteDimensional ℝ V] in
/-- If `A v = a v - b w` and `A w = b v + a w`, so that `v + iw` is an eigenvector of `A` for the
eigenvalue `a + bi`, then `focusFocusPoly a b` evaluated at `A` kills `v`: already its factor
`A² - 2aA + a² + b²` does. -/
theorem aeval_focusFocusPoly_apply_eq_zero {A : Module.End ℝ V} {a b : ℝ} {v w : V}
    (hAv : A v = a • v - b • w) (hAw : A w = b • v + a • w) :
    aeval A (focusFocusPoly a b) v = 0 := by
  have hq : aeval A (X ^ 2 - C (2 * a) * X + C (a ^ 2 + b ^ 2)) v = 0 := by
    simp only [map_add, map_sub, map_mul, aeval_X, aeval_C, LinearMap.add_apply,
      LinearMap.sub_apply, pow_two, mul_apply_eq_comp, Algebra.algebraMap_eq_smul_one,
      LinearMap.smul_apply, one_apply_eq_self, hAv, hAw, map_sub, map_smul]
    module
  rw [focusFocusPoly, mul_comm, map_mul, mul_apply_eq_comp, hq, map_zero]

/-- If `A ∈ sp(V, ω)` has the eigenvalue `a + bi`, `a, b ≠ 0`, with eigenvector `v + iw`, then the
vectors killed by a power of `(A² - 2aA + a² + b²)(A² + 2aA + a² + b²)` form a subspace of
dimension at least four. -/
theorem four_le_finrank_maxGenEigenspace_aeval_focusFocusPoly {A : Module.End ℝ V}
    (hA : A ∈ skewAdjointLieSubalgebra ω.toBilinForm) {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    {v w : V} (hv : v ≠ 0) (hAv : A v = a • v - b • w) (hAw : A w = b • v + a • w) :
    4 ≤ finrank ℝ ((aeval A (focusFocusPoly a b)).maxGenEigenspace 0) := by
  set G := (aeval A (focusFocusPoly a b)).maxGenEigenspace 0
  have hGs : ω.IsSymplectic G :=
    ω.isSymplectic_maxGenEigenspace_aeval hA (focusFocusPoly_comp_neg_X a b)
  have hfv := aeval_focusFocusPoly_apply_eq_zero hAv hAw
  have hvG : v ∈ G := (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨1, by simpa using hfv⟩
  obtain ⟨r, hr⟩ := (ω.restrict G hGs.nondegenerate_restrict).even_finrank
  have h2le := hGs.two_le_finrank_of_mem hvG hv
  -- On a plane, `A² = κ` and the polynomial acts as `(κ + a² + b²)² - 4a²κ > 0`.
  have hne2 : finrank ℝ G ≠ 2 := by
    intro h2
    have hmaps : ∀ x ∈ G, A x ∈ G := fun _ hx ↦
      Module.End.mapsTo_genEigenspace_aeval_of_comm (Commute.refl A) _ 0 ⊤ hx
    obtain ⟨κ, hκ⟩ := exists_mul_self_eq_smul_one (ω := ω.restrict G hGs.nondegenerate_restrict)
      h2 ⟨_, restrict_mem_skewAdjointLieSubalgebra hA hGs.nondegenerate_restrict hmaps⟩
    have hAAv : (A ^ 2) v = κ • v := by
      simpa [pow_two, mul_apply_eq_comp, LinearMap.coe_restrict_apply] using
        congrArg Subtype.val (LinearMap.congr_fun hκ ⟨v, hvG⟩)
    have hf : focusFocusPoly a b =
        ((X + C (a ^ 2 + b ^ 2)) ^ 2 - C (4 * a ^ 2) * X).comp (X ^ 2) := by
      simp only [focusFocusPoly, add_comp, sub_comp, mul_comp, pow_comp, X_comp, C_comp]
      simp only [map_mul, map_add, map_pow, map_ofNat]
      ring
    rw [hf, aeval_comp, aeval_X_pow, Module.End.aeval_apply_of_mem_apply_eq_smul hAAv] at hfv
    have hpos : 0 < eval κ ((X + C (a ^ 2 + b ^ 2)) ^ 2 - C (4 * a ^ 2) * X) := by
      simp only [eval_sub, eval_pow, eval_add, eval_X, eval_C, eval_mul]
      nlinarith [sq_nonneg (κ + b ^ 2 - a ^ 2), mul_pos (pow_pos (abs_pos.2 ha) 2)
        (pow_pos (abs_pos.2 hb) 2), sq_abs a, sq_abs b]
    exact hv ((smul_eq_zero.1 hfv).resolve_left hpos.ne')
  omega

/-- If `dim V = 4k` and `k` pairwise `ω`-orthogonal symplectic subspaces have dimension at least
four, they all have dimension four. -/
private theorem finrank_eq_four_of_four_le {k : ℕ} (hk : k * 4 = finrank ℝ V)
    {G : Fin k → Submodule ℝ V} (hGs : ∀ j, ω.IsSymplectic (G j))
    (horth : Pairwise fun j j' ↦ ∀ v ∈ G j, ∀ w ∈ G j', ω v w = 0)
    (h4 : ∀ j, 4 ≤ finrank ℝ (G j)) (j : Fin k) : finrank ℝ (G j) = 4 := by
  have hsum : ∑ j, finrank ℝ (G j) ≤ finrank ℝ V := by
    simpa using sum_finrank_le_finrank_of_pairwise_apply_eq_zero hGs horth (W := ⊤) fun _ ↦ le_top
  refine le_antisymm (not_lt.1 fun hlt ↦ ?_) (h4 j)
  have := Finset.sum_lt_sum (s := Finset.univ) (fun j _ ↦ h4 j) ⟨j, Finset.mem_univ _, hlt⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
  omega

variable {ι : Type*} {Q : ι → QuadraticForm ℝ V}

/-- **The focus-focus pair on one block.** Let `P` lie in the span of a nondegenerate family `Q`,
let `a, b > 0`, and suppose that the vectors killed by a power of
`(A_P² - 2aA_P + a² + b²)(A_P² + 2aA_P + a² + b²)` form a four-dimensional subspace `G`. Then the
restriction of `Q` to `G` spans the focus-focus block of a Darboux basis of `G`. -/
private theorem exists_isDarbouxBasis_block (h : ω.IsNondegenerateQuadraticFamily Q)
    {P : QuadraticForm ℝ V} (hP : P ∈ Submodule.span ℝ (Set.range Q)) {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b)
    (hG : finrank ℝ ((aeval (ω.hamiltonianEnd P) (focusFocusPoly a b)).maxGenEigenspace 0) = 4) :
    ∃ b' : Basis (Fin 2 × Fin 2) ℝ
        ((aeval (ω.hamiltonianEnd P) (focusFocusPoly a b)).maxGenEigenspace 0),
      (ω.restrict _ (ω.isSymplectic_maxGenEigenspace_aeval
        (ω.hamiltonianEnd_mem_skewAdjointLieSubalgebra P)
        (focusFocusPoly_comp_neg_X a b)).nondegenerate_restrict).IsDarbouxBasis b' ∧
      Submodule.span ℝ (Set.range fun i ↦
          (Q i).comp
            ((aeval (ω.hamiltonianEnd P) (focusFocusPoly a b)).maxGenEigenspace 0).subtype) =
        Submodule.span ℝ (Set.range (focusFocus b')) := by
  set A := ω.hamiltonianEnd P with hA_def
  set G := (aeval A (focusFocusPoly a b)).maxGenEigenspace 0
  have hA : A ∈ skewAdjointLieSubalgebra ω.toBilinForm :=
    ω.hamiltonianEnd_mem_skewAdjointLieSubalgebra P
  have hGs : ω.IsSymplectic G :=
    ω.isSymplectic_maxGenEigenspace_aeval hA (focusFocusPoly_comp_neg_X a b)
  set ω' := ω.restrict G hGs.nondegenerate_restrict
  have hnd := h.restrict_maxGenEigenspace_aeval hP (focusFocusPoly_comp_neg_X a b)
  have hcomm {R : QuadraticForm ℝ V} (hR : R ∈ Submodule.span ℝ (Set.range Q)) (p : ℝ[X]) :
      Commute (aeval A p) (ω.hamiltonianEnd R) :=
    commute_aeval_hamiltonianEnd_of_mem_span h.quadraticPoissonBracket_eq_zero hP hR p
  have hmaps (p : ℝ[X]) : Set.MapsTo (aeval A p) G G :=
    Module.End.mapsTo_genEigenspace_aeval_of_comm (hA_def ▸ (hcomm hP p).symm) _ 0 ⊤
  -- The focus-focus pair on `G`: odd polynomials `p₁`, `p₂` with `p₁(A)² = 1`, `p₂(A)² = -1`.
  obtain ⟨p₁, p₂, s₁, s₂, hp₁, hp₂, hp₁sq, hp₂sq⟩ := exists_odd_mul_self_eq ha hb
  -- On `G`, `p(A)² = r(A) + s(A) f(A)` acts as `r(A)`, since `f(A)` kills `G`.
  have hsq {p r s : ℝ[X]} (hp : p * p = r + s * focusFocusPoly a b) {v : V} (hv : v ∈ G) :
      aeval A p (aeval A p v) = aeval A r v := by
    have hf : aeval A (focusFocusPoly a b) v = 0 :=
      (h.isSemisimple_hamiltonianEnd hP).aeval_apply_eq_zero_of_mem_maxGenEigenspace hv
    simpa [hf] using LinearMap.congr_fun (congrArg (aeval A) hp) v
  -- The forms on `G` whose Hamiltonian endomorphisms are the restrictions of `p₁(A)`, `p₂(A)`.
  have hmem (p : ℝ[X]) (hp : p.comp (-X) = -p) :
      (aeval A p).restrict (hmaps p) ∈ skewAdjointLieSubalgebra ω'.toBilinForm :=
    restrict_mem_skewAdjointLieSubalgebra ((LinearMap.mem_skewAdjointSubmodule _).2 <|
      ((LinearMap.mem_skewAdjointSubmodule A).1 hA).aeval_of_comp_neg_X_eq_neg hp) _ _
  -- They commute with the restricted family, so they come from forms in its span.
  have hspan (p : ℝ[X]) (hp : p.comp (-X) = -p) :
      ∃ R ∈ Submodule.span ℝ (Set.range fun i ↦ (Q i).comp G.subtype),
        ω'.hamiltonianEnd R = (aeval A p).restrict (hmaps p) := by
    refine hnd.exists_mem_span_hamiltonianEnd_eq (hmem p hp) fun i ↦ ?_
    have hQi := hcomm (Submodule.subset_span ⟨i, rfl⟩) (X : ℝ[X])
    rw [aeval_X] at hQi
    have hmapsQ : Set.MapsTo (ω.hamiltonianEnd (Q i)) G G :=
      Module.End.mapsTo_genEigenspace_aeval_of_comm hQi _ 0 ⊤
    rw [hamiltonianEnd_comp_subtype hGs fun v hv ↦ hmapsQ hv]
    exact LinearMap.restrict_commute (hcomm (Submodule.subset_span ⟨i, rfl⟩) p) _ _
  obtain ⟨R₁, hR₁, hAR₁⟩ := hspan p₁ hp₁
  obtain ⟨R₂, hR₂, hAR₂⟩ := hspan p₂ hp₂
  -- The restrictions of `p(A)` and of `r(A)` evaluate on `G` as on `V`, definitionally.
  refine (exists_isDarbouxBasis_span_eq_span_focusFocus_iff hG
    hnd.quadraticPoissonBracket_eq_zero).2 ⟨R₁, hR₁, R₂, hR₂, ?_, ?_⟩
  · rw [hAR₁]
    exact LinearMap.ext fun v ↦ Subtype.ext <| (hsq hp₁sq v.property).trans (by simp)
  · rw [hAR₂]
    exact LinearMap.ext fun v ↦ Subtype.ext <| (hsq hp₂sq v.property).trans (by simp)

/-- On the blocks of a Darboux basis assembled from Darboux bases of orthogonal four-dimensional
subspaces `G j`, a quadratic form `R` whose Hamiltonian endomorphism preserves every `G j`, and
whose restriction to each `G j` lies in the span of the focus-focus block of `b' j`, lies in the
span of the focus-focus blocks of the assembled basis. -/
private theorem mem_span_focusFocusBlocks_of_blocks {k : ℕ} {G : Fin k → Submodule ℝ V}
    (hGs : ∀ j, ω.IsSymplectic (G j)) {b' : ∀ j, Basis (Fin 2 × Fin 2) ℝ (G j)}
    (hb' : ∀ j, (ω.restrict (G j) (hGs j).nondegenerate_restrict).IsDarbouxBasis (b' j))
    {bas : Basis (Fin (k * 2) × Fin 2) ℝ V} (hbas : ω.IsDarbouxBasis bas)
    (hbas_apply : ∀ j i x, bas (finProdFinEquiv (j, i), x) = b' j (i, x))
    {R : QuadraticForm ℝ V} (hRG : ∀ j, Set.MapsTo (ω.hamiltonianEnd R) (G j) (G j))
    (hR : ∀ j, R.comp (G j).subtype ∈ Submodule.span ℝ (Set.range (focusFocus (b' j)))) :
    R ∈ Submodule.span ℝ (Set.range (focusFocusBlocks bas)) := by
  choose d hd using fun j ↦ (Submodule.mem_span_range_iff_exists_fun ℝ).1 (hR j)
  -- `R = ∑ⱼ ∑ₗ d j l • Bⱼₗ`, as both sides have the same Hamiltonian endomorphism.
  have hRd : R = ∑ j, ∑ l, d j l • focusFocusBlocks bas (j, l) := by
    refine ω.hamiltonianEnd_injective (bas.ext fun ⟨m, x⟩ ↦ ?_)
    obtain ⟨⟨j', i'⟩, rfl⟩ := finProdFinEquiv.surjective m
    -- The restricted Hamiltonian endomorphism evaluates on `G j'` as `A_R`.
    have hL : ω.hamiltonianEnd R (bas (finProdFinEquiv (j', i'), x)) =
        ((ω.restrict (G j') (hGs j').nondegenerate_restrict).hamiltonianEnd
          (R.comp (G j').subtype) (b' j' (i', x)) : V) := by
      rw [hbas_apply, hamiltonianEnd_comp_subtype (hGs j') fun v hv ↦ hRG j' hv,
        LinearMap.coe_restrict_apply]
    rw [hL, ← hd j']
    simp only [Fin.sum_univ_two, map_sum, map_add, map_smul, LinearMap.sum_apply,
      LinearMap.add_apply, LinearMap.smul_apply,
      hbas.hamiltonianEnd_focusFocusBlocks_zero_apply,
      hbas.hamiltonianEnd_focusFocusBlocks_one_apply]
    fin_cases i' <;> fin_cases x <;>
      simp [(hb' j').hamiltonianEnd_focusFocus_zero_apply,
        (hb' j').hamiltonianEnd_focusFocus_one_apply, hbas_apply, smul_ite,
        Finset.sum_add_distrib, Finset.sum_ite_eq]
  rw [hRd]
  exact Submodule.sum_mem _ fun j _ ↦ Submodule.sum_mem _ fun l _ ↦
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨(j, l), rfl⟩)

namespace IsNondegenerateQuadraticFamily

/-- **Williamson's classification, focus-focus type, in every dimension.** Let `Q` be a
nondegenerate family of quadratic forms on `V`, and suppose that its span contains a form `P`
whose Hamiltonian endomorphism has `dim V / 4` distinct eigenvalues `z = a + bi` with `a, b > 0`,
listed in `s`: for each of them there are `v ≠ 0` and `w` with `A_P v = a v - b w` and
`A_P w = b v + a w`, so that `A_P (v + iw) = z (v + iw)`. Then the span of `Q` is the span of the
focus-focus blocks of some Darboux basis. -/
theorem exists_isDarbouxBasis_span_eq_span_focusFocusBlocks
    (h : ω.IsNondegenerateQuadraticFamily Q) {P : QuadraticForm ℝ V}
    (hP : P ∈ Submodule.span ℝ (Set.range Q)) {s : Finset ℂ} (hs : s.card * 4 = finrank ℝ V)
    (hs0 : ∀ z ∈ s, 0 < z.re ∧ 0 < z.im)
    (hPs : ∀ z ∈ s, ∃ v w : V, v ≠ 0 ∧ ω.hamiltonianEnd P v = z.re • v - z.im • w ∧
      ω.hamiltonianEnd P w = z.im • v + z.re • w) :
    ∃ (n : ℕ) (b : Basis (Fin (n * 2) × Fin 2) ℝ V), ω.IsDarbouxBasis b ∧
      Submodule.span ℝ (Set.range Q) = Submodule.span ℝ (Set.range (focusFocusBlocks b)) := by
  set A := ω.hamiltonianEnd P
  have hA : A ∈ skewAdjointLieSubalgebra ω.toBilinForm :=
    ω.hamiltonianEnd_mem_skewAdjointLieSubalgebra P
  -- Index the eigenvalues `aⱼ + cⱼ i` by `Fin k`; `G j` is the block of the `j`-th one.
  set k := s.card
  set e : Fin k ≃ s := s.equivFin.symm
  set a : Fin k → ℝ := fun j ↦ (e j : ℂ).re
  set c : Fin k → ℝ := fun j ↦ (e j : ℂ).im
  have ha (j : Fin k) : 0 < a j := (hs0 _ (e j).property).1
  have hc (j : Fin k) : 0 < c j := (hs0 _ (e j).property).2
  set G : Fin k → Submodule ℝ V := fun j ↦ (aeval A (focusFocusPoly (a j) (c j))).maxGenEigenspace 0
  have hGs (j : Fin k) : ω.IsSymplectic (G j) :=
    ω.isSymplectic_maxGenEigenspace_aeval hA (focusFocusPoly_comp_neg_X _ _)
  have horth : Pairwise fun j j' ↦ ∀ v ∈ G j, ∀ w ∈ G j', ω v w = 0 :=
    fun j j' hjj' _ hv _ hw ↦ apply_eq_zero_of_mem_maxGenEigenspace_aeval_focusFocusPoly hA
      (hs0 _ (e j).property) (hs0 _ (e j').property)
      (fun h ↦ hjj' (e.injective (Subtype.ext h))) hv hw
  have hG4 : ∀ j, finrank ℝ (G j) = 4 := finrank_eq_four_of_four_le hs hGs horth fun j ↦ by
    obtain ⟨v, w, hv, hAv, hAw⟩ := hPs _ (e j).property
    exact four_le_finrank_maxGenEigenspace_aeval_focusFocusPoly hA (ha j).ne' (hc j).ne' hv hAv hAw
  -- A Darboux basis of each block in which the restricted family spans the focus-focus pair; they
  -- assemble to a Darboux basis of `V`.
  choose b' hb' hspan' using fun j ↦ exists_isDarbouxBasis_block h hP (ha j) (hc j) (hG4 j)
  obtain ⟨bas, hbas, hbas_apply⟩ := exists_isDarbouxBasis_of_blocks
    ((Equiv.sigmaEquivProd (Fin k) (Fin 2)).trans finProdFinEquiv) (by rw [← hs]; ring) horth
    (v := fun j a ↦ (b' j a : V)) (fun j a ↦ (b' j a).property)
    (fun j i i' ↦ by simpa using (hb' j).apply_fst_fst i i')
    (fun j i i' ↦ by simpa using (hb' j).apply_snd_snd i i')
    (fun j i i' ↦ by simpa using (hb' j).apply_fst_snd i i')
  refine ⟨k, bas, hbas, h.span_eq_of_span_le hbas.quadraticPoissonBracket_focusFocusBlocks
    (Submodule.span_le.2 ?_)⟩
  rintro _ ⟨i, rfl⟩
  refine mem_span_focusFocusBlocks_of_blocks hGs hb' hbas
    (fun j i x ↦ by simpa using hbas_apply j i x) (fun j ↦ ?_) fun j ↦ ?_
  · exact Module.End.mapsTo_genEigenspace_aeval_of_comm (ω.quadraticPoissonBracket_eq_zero_iff.1
      (ω.quadraticPoissonBracket_eq_zero_of_mem_span h.quadraticPoissonBracket_eq_zero hP
        (Submodule.subset_span ⟨i, rfl⟩))) _ 0 ⊤
  · rw [← hspan' j]
    exact Submodule.subset_span ⟨i, rfl⟩

/-- **Nondegenerate families of focus-focus type.** The span of a nondegenerate family `Q`
contains a form `P` whose Hamiltonian endomorphism has `dim V / 4` distinct eigenvalues `a + bi`
with `a, b > 0`, each with an eigenvector `v + iw`, `v ≠ 0`, exactly when it is the span of the
focus-focus blocks of some Darboux basis. -/
theorem exists_mem_span_card_mul_four_eq_finrank_iff (h : ω.IsNondegenerateQuadraticFamily Q) :
    (∃ P ∈ Submodule.span ℝ (Set.range Q), ∃ s : Finset ℂ, s.card * 4 = finrank ℝ V ∧
        (∀ z ∈ s, 0 < z.re ∧ 0 < z.im) ∧ ∀ z ∈ s, ∃ v w : V, v ≠ 0 ∧
          ω.hamiltonianEnd P v = z.re • v - z.im • w ∧
          ω.hamiltonianEnd P w = z.im • v + z.re • w) ↔
      ∃ (n : ℕ) (b : Basis (Fin (n * 2) × Fin 2) ℝ V), ω.IsDarbouxBasis b ∧
        Submodule.span ℝ (Set.range Q) = Submodule.span ℝ (Set.range (focusFocusBlocks b)) := by
  refine ⟨fun ⟨P, hP, s, hs, hs0, hPs⟩ ↦
    h.exists_isDarbouxBasis_span_eq_span_focusFocusBlocks hP hs hs0 hPs,
    fun ⟨n, b, hb, hspan⟩ ↦ ?_⟩
  -- The form `∑ⱼ ((j + 1) Q₁ⱼ + Q₂ⱼ)` has the eigenvalues `(j + 1) + i`, with eigenvectors
  -- `q₂ⱼ₊₁ + i q₂ⱼ`.
  let z : Fin n → ℂ := fun j ↦ (((j : ℕ) : ℝ) + 1 : ℝ) + Complex.I
  have hz : Function.Injective z := fun j j' hjj' ↦ by
    have := congrArg Complex.re hjj'
    simp only [z, Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero, add_left_inj,
      Nat.cast_inj] at this
    exact Fin.ext this
  set P := ∑ j : Fin n,
    ((((j : ℕ) : ℝ) + 1) • focusFocusBlocks b (j, 0) + focusFocusBlocks b (j, 1))
  have hAP (j : Fin n) (i : Fin 2) :
      ω.hamiltonianEnd P (b (finProdFinEquiv (j, i), 0)) =
        (((j : ℕ) : ℝ) + 1) • b (finProdFinEquiv (j, i), 0) +
          if i = 0 then b (finProdFinEquiv (j, 1), 0) else -b (finProdFinEquiv (j, 0), 0) := by
    simp [P, map_sum, LinearMap.sum_apply, hb.hamiltonianEnd_focusFocusBlocks_zero_apply,
      hb.hamiltonianEnd_focusFocusBlocks_one_apply, smul_ite, Finset.sum_add_distrib,
      Finset.sum_ite_eq]
  refine ⟨P, hspan ▸ Submodule.sum_mem _ fun j _ ↦ add_mem
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(j, 0), rfl⟩))
      (Submodule.subset_span ⟨(j, 1), rfl⟩),
    Finset.univ.image z, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hz, Finset.card_univ, Fintype.card_fin,
      finrank_eq_card_basis b]
    simp only [Fintype.card_prod, Fintype.card_fin]
    ring
  · simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index]
    rintro _ j rfl
    simp only [z, Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero, Complex.add_im,
      Complex.ofReal_im, Complex.I_im, zero_add, zero_lt_one, and_true]
    positivity
  · simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index]
    rintro _ j rfl
    refine ⟨b (finProdFinEquiv (j, 1), 0), b (finProdFinEquiv (j, 0), 0), b.ne_zero _, ?_, ?_⟩ <;>
      simp [z, hAP, add_comm, sub_eq_add_neg]

end IsNondegenerateQuadraticFamily

end TauCeti.SymplecticForm
