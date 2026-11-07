/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.EngelSubalgebra
public import TauCeti.Geometry.Symplectic.Hamiltonian.Quadratic
import Mathlib.Algebra.Lie.AdjointAction.Basic
import Mathlib.FieldTheory.Separable
import TauCeti.Algebra.Lie.AdjointAction.Basic
import TauCeti.Algebra.Lie.Subalgebra.Engel
import TauCeti.Geometry.Symplectic.Plane
import TauCeti.LinearAlgebra.End.Prod

/-!
# Nondegenerate rank-zero points of integrable systems

Let `F = (F₁, …, Fₙ)` be an integrable system on a `2n`-dimensional symplectic manifold. A point
where all differentials `dFᵢ` vanish is a singular point of rank zero. There the linearizations of
the Hamiltonian vector fields `X_{Fᵢ}` are the Hamiltonian endomorphisms `A_{½ Hess Fᵢ}` of the
quadratic Taylor terms (`TauCeti.SymplecticForm.fderiv_hamiltonianVectorField`), elements of the
symplectic Lie algebra `sp(V, ω)` of the tangent space. They pairwise commute when the `Fᵢ`
Poisson-commute (`TauCeti.SymplecticForm.commute_fderiv_hamiltonianVectorField`). Following
Williamson and Eliasson, the singular point is **nondegenerate** when they span a Cartan subalgebra
of `sp(V, ω)`. Williamson's theorem then classifies such subalgebras into elliptic, hyperbolic and
focus-focus blocks.

This file sets up this notion on a symplectic vector space, the local model of the tangent space.

* `TauCeti.SymplecticForm.IsNondegenerateQuadraticFamily ω Q`: the Hamiltonian endomorphisms of a
  family `Q` of quadratic forms generate a Cartan subalgebra of `sp(V, ω)`. This depends only on
  the linear span of the family (`isNondegenerateQuadraticFamily_iff_of_span_eq`). By Mathlib's
  `LieSubalgebra.normalizer_eq_self_of_engel_le`, a Poisson-commuting family is nondegenerate as
  soon as it contains the Engel subalgebra of one Hamiltonian endomorphism
  (`isNondegenerateQuadraticFamily_of_engel_le`).
* `TauCeti.SymplecticForm.IsNondegenerateRankZeroPoint ω F x`: `x` is a `C²` critical point of
  `F : E → G` at which the Hessians of the functions `ℓ ∘ F`, `ℓ` a linear functional on `G`, form
  a nondegenerate family. For `G = ℝⁿ` these may be replaced by the Hessians of the components
  (`isNondegenerateRankZeroPoint_pi_iff`), and the notion is invariant under composition with
  maps `g : G → G'` whose differential is injective (`isNondegenerateRankZeroPoint_comp_iff`).

In dimension two the notion reduces to Morse theory: a single quadratic form is a nondegenerate
family exactly when it is a nondegenerate quadratic form
(`isNondegenerateQuadraticFamily_const_iff`), so a nondegenerate rank-zero point of one Hamiltonian
on a symplectic plane is exactly a nondegenerate critical point
(`isNondegenerateRankZeroPoint_iff_isNondegenerateCriticalPoint`). A degenerate form on the plane
is `0` or a multiple of the square of a linear form; its Hamiltonian endomorphism `A` satisfies
`A² = 0`, and the line it spans is strictly smaller than its normalizer in `sp(V, ω)`. The linear
algebra of `sp(V, ω)` on a symplectic plane used here lives in
`TauCeti.Geometry.Symplectic.Plane`.

Nondegeneracy is usually checked through a regular semisimple element. If some form `P` has
semisimple Hamiltonian endomorphism and every form Poisson-commuting with `P`, in particular `P`
itself, lies in the span of a Poisson-commuting family, then the family is nondegenerate
(`isNondegenerateQuadraticFamily_of_isSemisimple`): the Engel subalgebra of a semisimple element
is its centralizer. These hypotheses pass to direct sums. On `(V₁ × V₂, ω₁ ⊕ ω₂)`, if `P₁` and
`P₂` satisfy them for families `Q₁` and `Q₂` and the minimal polynomials of `A_{P₁}` and `A_{P₂}`
are coprime, then every form Poisson-commuting with `P₁ ⊕ P₂` is a direct sum, and the two
families extended by zero form a nondegenerate family
(`isNondegenerateQuadraticFamily_sumElim_prod`). This is how the elliptic, hyperbolic and
focus-focus blocks of Williamson's normal forms assemble. A nondegenerate form on a symplectic
plane satisfies the hypotheses, after rescaling to separate the minimal polynomials, so any two
nondegenerate plane forms give a nondegenerate family on the product of the two planes
(`isNondegenerateQuadraticFamily_prod_of_finrank_eq_two`).

## Main results

* `TauCeti.SymplecticForm.isNondegenerateQuadraticFamily_of_isSemisimple`: a Poisson-commuting
  family is nondegenerate if the forms Poisson-commuting with a form `P` with semisimple
  Hamiltonian endomorphism all lie in its span.
* `TauCeti.SymplecticForm.mem_span_sumElim_prod_of_quadraticPoissonBracket_eq_zero`: the forms on
  a direct sum Poisson-commuting with `P₁ ⊕ P₂` lie in the span of the two families extended by
  zero, when the minimal polynomials of `A_{P₁}` and `A_{P₂}` are coprime.
* `TauCeti.SymplecticForm.isNondegenerateQuadraticFamily_sumElim_prod`: direct sums of
  nondegenerate families witnessed in this way are nondegenerate.
* `TauCeti.SymplecticForm.isNondegenerateQuadraticFamily_prod_of_finrank_eq_two`: two
  nondegenerate forms on symplectic planes give a nondegenerate family on their product.

## References

* J. Williamson, *On the algebraic problem concerning the normal forms of linear dynamical
  systems*, American Journal of Mathematics 58 (1936), 141–163.
* L. H. Eliasson, *Normal forms for Hamiltonian systems with Poisson commuting integrals —
  elliptic case*, Commentarii Mathematici Helvetici 65 (1990), 4–35.
* A. V. Bolsinov and A. T. Fomenko, *Integrable Hamiltonian Systems: Geometry, Topology,
  Classification*, Chapman & Hall/CRC, 2004, Chapter 1.
-/

public section

noncomputable section

open LieSubalgebra Module

-- `sp(V, ω)` is a Lie subalgebra of `Module.End ℝ V` for the commutator bracket, as in Mathlib's
-- `Mathlib.Algebra.Lie.SkewAdjoint`.
attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti.SymplecticForm

section Linear

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] {ω : SymplecticForm V}
  {ι κ : Type*}

/-! ### Nondegenerate families of quadratic forms -/

variable (ω) in
/-- A family `Q` of quadratic forms on a symplectic vector space `(V, ω)` is **nondegenerate** when
the Hamiltonian endomorphisms `A_{Q i}` generate a Cartan subalgebra of the symplectic Lie algebra
`sp(V, ω)`. -/
def IsNondegenerateQuadraticFamily (Q : ι → QuadraticForm ℝ V) : Prop :=
  (lieSpan ℝ (skewAdjointLieSubalgebra ω.toBilinForm)
    (Set.range fun i ↦ ω.hamiltonianEndEquiv (Q i))).IsCartanSubalgebra

/-- Unfolding `IsNondegenerateQuadraticFamily`. -/
theorem isNondegenerateQuadraticFamily_iff (Q : ι → QuadraticForm ℝ V) :
    ω.IsNondegenerateQuadraticFamily Q ↔
      (lieSpan ℝ (skewAdjointLieSubalgebra ω.toBilinForm)
        (Set.range fun i ↦ ω.hamiltonianEndEquiv (Q i))).IsCartanSubalgebra :=
  Iff.rfl

/-- The Lie subalgebra generated by the Hamiltonian endomorphisms of a family depends only on the
linear span of the family. -/
private theorem lieSpan_range_hamiltonianEndEquiv (Q : ι → QuadraticForm ℝ V) :
    lieSpan ℝ (skewAdjointLieSubalgebra ω.toBilinForm)
        (Set.range fun i ↦ ω.hamiltonianEndEquiv (Q i)) =
      lieSpan ℝ (skewAdjointLieSubalgebra ω.toBilinForm)
        ((Submodule.span ℝ (Set.range Q)).map ω.hamiltonianEndEquiv.toLinearMap :
          Set (skewAdjointLieSubalgebra ω.toBilinForm)) := by
  rw [Submodule.map_span, ← Set.range_comp]
  refine le_antisymm (lieSpan_mono Submodule.subset_span) (lieSpan_le.2 ?_)
  exact submodule_span_le_lieSpan

/-- Nondegeneracy of a family of quadratic forms depends only on its linear span. -/
theorem isNondegenerateQuadraticFamily_iff_of_span_eq {Q : ι → QuadraticForm ℝ V}
    {Q' : κ → QuadraticForm ℝ V}
    (h : Submodule.span ℝ (Set.range Q) = Submodule.span ℝ (Set.range Q')) :
    ω.IsNondegenerateQuadraticFamily Q ↔ ω.IsNondegenerateQuadraticFamily Q' := by
  rw [isNondegenerateQuadraticFamily_iff, isNondegenerateQuadraticFamily_iff,
    lieSpan_range_hamiltonianEndEquiv, lieSpan_range_hamiltonianEndEquiv, h]

/-- **Regular elements give Cartan subalgebras.** A family of pairwise Poisson-commuting quadratic
forms is nondegenerate as soon as the Engel subalgebra of the Hamiltonian endomorphism of some
quadratic form `P` is contained in the Lie subalgebra the family generates. -/
theorem isNondegenerateQuadraticFamily_of_engel_le
    {Q : ι → QuadraticForm ℝ V} (hQ : ∀ i j, ω.quadraticPoissonBracket (Q i) (Q j) = 0)
    (P : QuadraticForm ℝ V)
    (hP : engel ℝ (ω.hamiltonianEndEquiv P) ≤ lieSpan ℝ (skewAdjointLieSubalgebra ω.toBilinForm)
      (Set.range fun i ↦ ω.hamiltonianEndEquiv (Q i))) :
    ω.IsNondegenerateQuadraticFamily Q := by
  have : IsLieAbelian (lieSpan ℝ (skewAdjointLieSubalgebra ω.toBilinForm)
      (Set.range fun i ↦ ω.hamiltonianEndEquiv (Q i))) := by
    rw [isLieAbelian_lieSpan_iff]
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    rw [← hamiltonianEndEquiv_quadraticPoissonBracket, hQ, map_zero]
  exact ⟨inferInstance, normalizer_eq_self_of_engel_le _ _ hP⟩

section TwoDim

/-- **Rank-zero nondegeneracy in dimension two.** On a two-dimensional symplectic vector space, a
single quadratic form is a nondegenerate family exactly when it is nondegenerate as a quadratic
form. Such forms are the elliptic (definite) and hyperbolic (indefinite) ones. -/
theorem isNondegenerateQuadraticFamily_const_iff [Nonempty ι] (hV : finrank ℝ V = 2)
    (Q : QuadraticForm ℝ V) :
    ω.IsNondegenerateQuadraticFamily (fun _ : ι ↦ Q) ↔ Q.Nondegenerate := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  rw [isNondegenerateQuadraticFamily_iff, Set.range_const,
    QuadraticMap.nondegenerate_iff_radical_eq_bot, ← ker_hamiltonianEnd ω, LinearMap.ker_eq_bot]
  set A := ω.hamiltonianEndEquiv Q
  have hAQ : (A : Module.End ℝ V) = ω.hamiltonianEnd Q := ω.coe_hamiltonianEndEquiv_apply Q
  obtain ⟨c, hc⟩ := exists_mul_self_eq_smul_one hV A
  rw [← hAQ]
  constructor
  · intro hcartan
    by_contra hinj
    refine not_isCartanSubalgebra_lieSpan_singleton hV (hc.trans ?_) hcartan
    rcases eq_or_ne c 0 with rfl | hc0
    · exact zero_smul _ _
    · refine absurd (fun v w hvw ↦ ?_) hinj
      have := congrArg (A : Module.End ℝ V) hvw
      rw [← mul_apply_eq_comp, ← mul_apply_eq_comp, hc] at this
      simpa [hc0] using this
  · intro hinj
    have hc0 : c ≠ 0 := by
      rintro rfl
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      refine hv ((hinj.comp hinj) ?_)
      simp only [Function.comp_apply, ← mul_apply_eq_comp, hc, zero_smul, map_zero,
        LinearMap.zero_apply]
    have : IsLieAbelian (lieSpan ℝ (skewAdjointLieSubalgebra ω.toBilinForm) {A}) := by simp
    exact ⟨inferInstance,
      normalizer_eq_self_of_engel_le _ _ (engel_le_lieSpan_singleton hV hc0 hc)⟩

end TwoDim

/-! ### Regular semisimple elements -/

/-- **Regular semisimple elements give Cartan subalgebras.** A family of pairwise Poisson-commuting
quadratic forms is nondegenerate as soon as some quadratic form `P` has semisimple Hamiltonian
endomorphism and every quadratic form Poisson-commuting with `P` lies in the span of the family.
-/
theorem isNondegenerateQuadraticFamily_of_isSemisimple {Q : ι → QuadraticForm ℝ V}
    (hQ : ∀ i j, ω.quadraticPoissonBracket (Q i) (Q j) = 0) {P : QuadraticForm ℝ V}
    (hP : (ω.hamiltonianEnd P).IsSemisimple)
    (hPQ : ∀ R, ω.quadraticPoissonBracket R P = 0 → R ∈ Submodule.span ℝ (Set.range Q)) :
    ω.IsNondegenerateQuadraticFamily Q := by
  refine isNondegenerateQuadraticFamily_of_engel_le hQ P fun X hX ↦ ?_
  -- `ad A_P` is semisimple on `sp(V, ω)`, so the Engel subalgebra of `A_P` is its centralizer.
  have hP' : (ω.hamiltonianEndEquiv P : Module.End ℝ V).IsSemisimple := by
    rwa [coe_hamiltonianEndEquiv_apply]
  have had := (skewAdjointLieSubalgebra ω.toBilinForm).isSemisimple_ad_of_isSemisimple_ad
    (x := ω.hamiltonianEndEquiv P) (LieAlgebra.ad_isSemisimple_of_isSemisimple hP')
  rw [mem_engel_iff_lie_eq_zero had.isFinitelySemisimple] at hX
  obtain ⟨R, rfl⟩ := ω.hamiltonianEndEquiv.surjective X
  rw [← hamiltonianEndEquiv_quadraticPoissonBracket, LinearEquiv.map_eq_zero_iff,
    ← neg_quadraticPoissonBracket, neg_eq_zero] at hX
  have hR := Submodule.mem_map_of_mem (f := ω.hamiltonianEndEquiv.toLinearMap) (hPQ R hX)
  rw [Submodule.map_span, ← Set.range_comp] at hR
  exact submodule_span_le_lieSpan hR

/-! ### Direct sums -/

section Prod

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℝ V₁] [FiniteDimensional ℝ V₁]
  [AddCommGroup V₂] [Module ℝ V₂] [FiniteDimensional ℝ V₂]
  {ω₁ : SymplecticForm V₁} {ω₂ : SymplecticForm V₂}
  {Q₁ : ι → QuadraticForm ℝ V₁} {Q₂ : κ → QuadraticForm ℝ V₂}

/-- Two families of pairwise Poisson-commuting quadratic forms on `V₁` and `V₂`, extended by zero
to the direct sum `V₁ × V₂`, form a family of pairwise Poisson-commuting quadratic forms for the
direct-sum symplectic form. -/
theorem quadraticPoissonBracket_sumElim_prod_eq_zero
    (hQ₁ : ∀ i j, ω₁.quadraticPoissonBracket (Q₁ i) (Q₁ j) = 0)
    (hQ₂ : ∀ i j, ω₂.quadraticPoissonBracket (Q₂ i) (Q₂ j) = 0) (i j : ι ⊕ κ) :
    (ω₁.prod ω₂).quadraticPoissonBracket
        (Sum.elim (fun i ↦ (Q₁ i).prod 0) (fun j ↦ (0 : QuadraticForm ℝ V₁).prod (Q₂ j)) i)
        (Sum.elim (fun i ↦ (Q₁ i).prod 0) (fun j ↦ (0 : QuadraticForm ℝ V₁).prod (Q₂ j)) j) =
      0 := by
  rcases i with i | i <;> rcases j with j | j <;> ext <;>
    simp [quadraticPoissonBracket_prod, hQ₁, hQ₂]

/-- **Centralizers in a direct sum.** Let `P₁` and `P₂` be quadratic forms on `V₁` and `V₂` whose
Hamiltonian endomorphisms have coprime minimal polynomials, such that every quadratic form
Poisson-commuting with `Pₖ` lies in the span of the family `Qₖ`. Then every quadratic form on
`V₁ × V₂` Poisson-commuting with `P₁ ⊕ P₂` lies in the span of the two families extended by zero.
-/
theorem mem_span_sumElim_prod_of_quadraticPoissonBracket_eq_zero {P₁ : QuadraticForm ℝ V₁}
    {P₂ : QuadraticForm ℝ V₂}
    (hPQ₁ : ∀ R, ω₁.quadraticPoissonBracket R P₁ = 0 → R ∈ Submodule.span ℝ (Set.range Q₁))
    (hPQ₂ : ∀ R, ω₂.quadraticPoissonBracket R P₂ = 0 → R ∈ Submodule.span ℝ (Set.range Q₂))
    (hc : IsCoprime (minpoly ℝ (ω₁.hamiltonianEnd P₁)) (minpoly ℝ (ω₂.hamiltonianEnd P₂)))
    {R : QuadraticForm ℝ (V₁ × V₂)}
    (hR : (ω₁.prod ω₂).quadraticPoissonBracket R (P₁.prod P₂) = 0) :
    R ∈ Submodule.span ℝ (Set.range
      (Sum.elim (fun i ↦ (Q₁ i).prod 0) (fun j ↦ (0 : QuadraticForm ℝ V₁).prod (Q₂ j)))) := by
  -- `A_R` commutes with `A_{P₁} × A_{P₂}`, so it is a product and `R` is a direct sum.
  rw [quadraticPoissonBracket_eq_zero_iff, hamiltonianEnd_prod,
    Module.End.commute_prodMap_iff_of_isCoprime hc] at hR
  obtain ⟨a, b, ha, hb, hab⟩ := hR
  obtain ⟨R₁, R₂, rfl, rfl, rfl⟩ := exists_eq_prod_of_hamiltonianEnd_eq_prodMap hab
  have h₁ := hPQ₁ R₁ (ω₁.quadraticPoissonBracket_eq_zero_iff.2 ha)
  have h₂ := hPQ₂ R₂ (ω₂.quadraticPoissonBracket_eq_zero_iff.2 hb)
  let L₁ : QuadraticForm ℝ V₁ →ₗ[ℝ] QuadraticForm ℝ (V₁ × V₂) :=
    { toFun R := R.prod 0
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
  let L₂ : QuadraticForm ℝ V₂ →ₗ[ℝ] QuadraticForm ℝ (V₁ × V₂) :=
    { toFun R := (0 : QuadraticForm ℝ V₁).prod R
      map_add' _ _ := by ext; simp
      map_smul' _ _ := by ext; simp }
  have hsum : R₁.prod R₂ = L₁ R₁ + L₂ R₂ := by
    ext
    simp [L₁, L₂]
  have h₁' := Submodule.mem_map_of_mem (f := L₁) h₁
  have h₂' := Submodule.mem_map_of_mem (f := L₂) h₂
  rw [Submodule.map_span] at h₁' h₂'
  rw [hsum]
  refine add_mem (Submodule.span_mono ?_ h₁') (Submodule.span_mono ?_ h₂')
  · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨Sum.inl i, rfl⟩
  · rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact ⟨Sum.inr j, rfl⟩

/-- **Direct sums of nondegenerate families.** Let `Q₁` and `Q₂` be families of pairwise
Poisson-commuting quadratic forms on `V₁` and `V₂`. Suppose that `Pₖ` has semisimple Hamiltonian
endomorphism, that every quadratic form Poisson-commuting with `Pₖ` lies in the span of `Qₖ`, and
that the minimal polynomials of the Hamiltonian endomorphisms of `P₁` and `P₂` are coprime. Then
the two families, extended by zero, form a nondegenerate family on `V₁ × V₂` for the direct-sum
symplectic form, with `P₁ ⊕ P₂` playing the role of `P`. -/
theorem isNondegenerateQuadraticFamily_sumElim_prod
    (hQ₁ : ∀ i j, ω₁.quadraticPoissonBracket (Q₁ i) (Q₁ j) = 0)
    (hQ₂ : ∀ i j, ω₂.quadraticPoissonBracket (Q₂ i) (Q₂ j) = 0) {P₁ : QuadraticForm ℝ V₁}
    {P₂ : QuadraticForm ℝ V₂} (hP₁ : (ω₁.hamiltonianEnd P₁).IsSemisimple)
    (hP₂ : (ω₂.hamiltonianEnd P₂).IsSemisimple)
    (hPQ₁ : ∀ R, ω₁.quadraticPoissonBracket R P₁ = 0 → R ∈ Submodule.span ℝ (Set.range Q₁))
    (hPQ₂ : ∀ R, ω₂.quadraticPoissonBracket R P₂ = 0 → R ∈ Submodule.span ℝ (Set.range Q₂))
    (hc : IsCoprime (minpoly ℝ (ω₁.hamiltonianEnd P₁)) (minpoly ℝ (ω₂.hamiltonianEnd P₂))) :
    (ω₁.prod ω₂).IsNondegenerateQuadraticFamily
      (Sum.elim (fun i ↦ (Q₁ i).prod 0) fun j ↦ (0 : QuadraticForm ℝ V₁).prod (Q₂ j)) :=
  isNondegenerateQuadraticFamily_of_isSemisimple
    (quadraticPoissonBracket_sumElim_prod_eq_zero hQ₁ hQ₂) (P := P₁.prod P₂)
    (by rw [hamiltonianEnd_prod]; exact hP₁.prodMap hP₂)
    fun _ hR ↦ mem_span_sumElim_prod_of_quadraticPoissonBracket_eq_zero hPQ₁ hPQ₂ hc hR

end Prod

/-! ### Symplectic planes -/

section Plane

variable {Q : QuadraticForm ℝ V}

/-- On a symplectic plane, the Hamiltonian endomorphism of a nondegenerate quadratic form squares
to a nonzero homothety. -/
theorem exists_hamiltonianEnd_mul_self_eq_smul_one (hV : finrank ℝ V = 2) (hQ : Q.Nondegenerate) :
    ∃ c : ℝ, c ≠ 0 ∧ ω.hamiltonianEnd Q * ω.hamiltonianEnd Q = c • 1 := by
  obtain ⟨c, hc⟩ := exists_mul_self_eq_smul_one hV (ω.hamiltonianEndEquiv Q)
  refine ⟨c, fun hc0 ↦ ?_, by simpa using hc⟩
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  have hinj : Function.Injective (ω.hamiltonianEnd Q) := by
    rw [← LinearMap.ker_eq_bot, ker_hamiltonianEnd,
      ← QuadraticMap.nondegenerate_iff_radical_eq_bot]
    exact hQ
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  refine hv ((hinj.comp hinj) ?_)
  simpa [hc0] using LinearMap.congr_fun hc v

/-- On a symplectic plane, a nondegenerate quadratic form has semisimple Hamiltonian
endomorphism. -/
theorem isSemisimple_hamiltonianEnd_of_finrank_eq_two (hV : finrank ℝ V = 2)
    (hQ : Q.Nondegenerate) : (ω.hamiltonianEnd Q).IsSemisimple := by
  obtain ⟨c, hc0, hc⟩ := exists_hamiltonianEnd_mul_self_eq_smul_one (ω := ω) hV hQ
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (Polynomial.separable_X_pow_sub_C (n := 2) c (by norm_num) hc0).squarefree ?_
  simp [sq, hc, Algebra.algebraMap_eq_smul_one]

/-- On a symplectic plane, every quadratic form Poisson-commuting with a nondegenerate quadratic
form `Q` is a multiple of `Q`. -/
theorem mem_span_singleton_of_quadraticPoissonBracket_eq_zero (hV : finrank ℝ V = 2)
    (hQ : Q.Nondegenerate) {R : QuadraticForm ℝ V} (hR : ω.quadraticPoissonBracket R Q = 0) :
    R ∈ ℝ ∙ Q := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ℝ) (by omega)
  obtain ⟨c, hc0, hc⟩ := exists_hamiltonianEnd_mul_self_eq_smul_one (ω := ω) hV hQ
  have hA0 : ω.hamiltonianEndEquiv Q ≠ 0 := fun h ↦ by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h' : ω.hamiltonianEnd Q = 0 := by
      rw [← coe_hamiltonianEndEquiv_apply, h, ZeroMemClass.coe_zero]
    have := LinearMap.congr_fun hc v
    simp only [h', mul_zero, LinearMap.zero_apply, LinearMap.smul_apply,
      one_apply_eq_self] at this
    exact hv ((smul_eq_zero.1 this.symm).resolve_left hc0)
  obtain ⟨t, ht⟩ := exists_eq_smul_of_commute hV hA0 (B := ω.hamiltonianEndEquiv R)
    (by simpa using (ω.quadraticPoissonBracket_eq_zero_iff.1 hR).symm)
  exact Submodule.mem_span_singleton.2
    ⟨t, ω.hamiltonianEndEquiv.injective (by rw [map_smul, ht])⟩

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℝ V₁] [FiniteDimensional ℝ V₁]
  [AddCommGroup V₂] [Module ℝ V₂] [FiniteDimensional ℝ V₂]
  {ω₁ : SymplecticForm V₁} {ω₂ : SymplecticForm V₂}

/-- **Products of two symplectic planes.** If `Q₁` and `Q₂` are nondegenerate quadratic forms on
symplectic planes `V₁` and `V₂`, then `Q₁ ⊕ 0` and `0 ⊕ Q₂` form a nondegenerate family on
`V₁ × V₂` for the direct-sum symplectic form. These are the elliptic–elliptic,
elliptic–hyperbolic and hyperbolic–hyperbolic types of Williamson's classification in dimension
four. -/
theorem isNondegenerateQuadraticFamily_prod_of_finrank_eq_two (hV₁ : finrank ℝ V₁ = 2)
    (hV₂ : finrank ℝ V₂ = 2) {Q₁ : QuadraticForm ℝ V₁} {Q₂ : QuadraticForm ℝ V₂}
    (hQ₁ : Q₁.Nondegenerate) (hQ₂ : Q₂.Nondegenerate) :
    (ω₁.prod ω₂).IsNondegenerateQuadraticFamily ![Q₁.prod 0, (0 : QuadraticForm ℝ V₁).prod Q₂] := by
  obtain ⟨c₁, hc₁0, hc₁⟩ := exists_hamiltonianEnd_mul_self_eq_smul_one (ω := ω₁) hV₁ hQ₁
  obtain ⟨c₂, hc₂0, hc₂⟩ := exists_hamiltonianEnd_mul_self_eq_smul_one (ω := ω₂) hV₂ hQ₂
  -- Rescale `Q₂` by `s` so that the squares `c₁` and `s² c₂` of the two Hamiltonian
  -- endomorphisms differ; their minimal polynomials are then coprime.
  obtain ⟨s, hs0, hs⟩ : ∃ s : ℝ, s ≠ 0 ∧ c₁ ≠ s ^ 2 * c₂ := by
    by_cases h : c₁ = c₂
    · exact ⟨2, two_ne_zero, fun h' ↦ hc₂0 (by linarith)⟩
    · exact ⟨1, one_ne_zero, by simpa using h⟩
  have hsc₂ : ω₂.hamiltonianEnd (s • Q₂) * ω₂.hamiltonianEnd (s • Q₂) = (s ^ 2 * c₂) • 1 := by
    rw [map_smul, smul_mul_smul_comm, hc₂, smul_smul, sq]
  have hcop : IsCoprime (minpoly ℝ (ω₁.hamiltonianEnd Q₁))
      (minpoly ℝ (ω₂.hamiltonianEnd (s • Q₂))) := by
    -- `X² - c₁ = (X² - s² c₂) + (s² c₂ - c₁)` differs from `X² - s² c₂` by a unit.
    have hX : IsCoprime (Polynomial.X ^ 2 - Polynomial.C c₁)
        (Polynomial.X ^ 2 - Polynomial.C (s ^ 2 * c₂)) := by
      have hu : IsUnit (Polynomial.C (s ^ 2 * c₂ - c₁)) :=
        Polynomial.isUnit_C.2 (sub_ne_zero.2 hs.symm).isUnit
      convert ((isCoprime_mul_unit_left_left hu 1 _).2 isCoprime_one_left).add_mul_left_left 1
        using 1
      rw [map_sub]
      ring
    refine (hX.of_isCoprime_of_dvd_left
      (minpoly.dvd _ _ ?_)).of_isCoprime_of_dvd_right (minpoly.dvd _ _ ?_)
    · simp [sq, hc₁, Algebra.algebraMap_eq_smul_one]
    · rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sq, hsc₂,
        Algebra.algebraMap_eq_smul_one, sub_self]
  have h := isNondegenerateQuadraticFamily_sumElim_prod (ω₁ := ω₁) (ω₂ := ω₂)
    (Q₁ := fun _ : Unit ↦ Q₁) (Q₂ := fun _ : Unit ↦ Q₂)
    (fun _ _ ↦ ω₁.quadraticPoissonBracket_eq_zero_iff.2 (Commute.refl _))
    (fun _ _ ↦ ω₂.quadraticPoissonBracket_eq_zero_iff.2 (Commute.refl _))
    (isSemisimple_hamiltonianEnd_of_finrank_eq_two hV₁ hQ₁)
    (by
      rw [map_smul]
      exact Module.End.IsSemisimple_smul s
        (isSemisimple_hamiltonianEnd_of_finrank_eq_two hV₂ hQ₂))
    (fun R hR ↦ by
      simpa using mem_span_singleton_of_quadraticPoissonBracket_eq_zero hV₁ hQ₁ hR)
    (fun R hR ↦ by
      rw [quadraticPoissonBracket_smul_right, smul_eq_zero, or_iff_right hs0] at hR
      simpa using mem_span_singleton_of_quadraticPoissonBracket_eq_zero hV₂ hQ₂ hR)
    hcop
  refine (isNondegenerateQuadraticFamily_iff_of_span_eq (congrArg _ ?_)).1 h
  ext
  simp

end Plane

end Linear

/-! ### Nondegenerate rank-zero points of maps -/

section Function

variable {E G G' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup G'] [NormedSpace ℝ G']
  (ω : SymplecticForm E)

/-- A point `x` is a **nondegenerate rank-zero point** of a `C²` map `F : E → G` on a symplectic
vector space `(E, ω)` when the differential of `F` vanishes at `x` and the Hessians at `x` of the
functions `ℓ ∘ F`, for `ℓ` a linear functional on `G`, form a nondegenerate family: their
Hamiltonian endomorphisms generate a Cartan subalgebra of `sp(E, ω)`. For `G = ℝⁿ` these are the
Hessians of the components of `F` (`TauCeti.SymplecticForm.isNondegenerateRankZeroPoint_pi_iff`).
-/
structure IsNondegenerateRankZeroPoint (F : E → G) (x : E) : Prop where
  /-- The map is `C²` at the point. -/
  contDiffAt : ContDiffAt ℝ 2 F x
  /-- The differential vanishes at the point. -/
  fderiv_eq_zero : fderiv ℝ F x = 0
  /-- The Hessians of the functions `ℓ ∘ F` form a nondegenerate family. -/
  isNondegenerateQuadraticFamily :
    ω.IsNondegenerateQuadraticFamily fun ℓ : G →L[ℝ] ℝ ↦ hessianQuadraticForm (ℓ ∘ F) x

variable {ω} {F : E → G} {x : E}

/-- Being a nondegenerate rank-zero point depends only on the germ of the map at the point. -/
theorem IsNondegenerateRankZeroPoint.congr_of_eventuallyEq {F' : E → G}
    (h : ω.IsNondegenerateRankZeroPoint F x) (hF : F =ᶠ[nhds x] F') :
    ω.IsNondegenerateRankZeroPoint F' x := by
  refine ⟨h.contDiffAt.congr_of_eventuallyEq hF.symm, by rw [← hF.fderiv_eq, h.fderiv_eq_zero],
    ?_⟩
  convert h.isNondegenerateQuadraticFamily using 2 with ℓ
  exact hessianQuadraticForm_congr_of_eventuallyEq (hF.fun_comp ℓ).symm

/-- A nondegenerate rank-zero point may be tested on any family of quadratic forms that, at a `C²`
critical point, spans the same space as the Hessians of the functions `ℓ ∘ F`. -/
theorem isNondegenerateRankZeroPoint_iff_of_span_eq {κ : Type*} {Q : κ → QuadraticForm ℝ E}
    (h : ContDiffAt ℝ 2 F x → fderiv ℝ F x = 0 →
      Submodule.span ℝ (Set.range fun ℓ : G →L[ℝ] ℝ ↦ hessianQuadraticForm (ℓ ∘ F) x) =
        Submodule.span ℝ (Set.range Q)) :
    ω.IsNondegenerateRankZeroPoint F x ↔
      ContDiffAt ℝ 2 F x ∧ fderiv ℝ F x = 0 ∧ ω.IsNondegenerateQuadraticFamily Q :=
  ⟨fun hx ↦ ⟨hx.contDiffAt, hx.fderiv_eq_zero, (isNondegenerateQuadraticFamily_iff_of_span_eq
      (h hx.contDiffAt hx.fderiv_eq_zero)).1 hx.isNondegenerateQuadraticFamily⟩,
    fun ⟨hF, h0, hQ⟩ ↦ ⟨hF, h0, (isNondegenerateQuadraticFamily_iff_of_span_eq (h hF h0)).2 hQ⟩⟩

/-- **Nondegenerate rank-zero points in coordinates.** For `F = (F₁, …, Fₙ) : E → ℝⁿ`, a point is a
nondegenerate rank-zero point exactly when it is a `C²` critical point of `F` at which the Hessians
of the components `Fᵢ` form a nondegenerate family. -/
theorem isNondegenerateRankZeroPoint_pi_iff {ι : Type*} [Fintype ι] {F : E → ι → ℝ} :
    ω.IsNondegenerateRankZeroPoint F x ↔ ContDiffAt ℝ 2 F x ∧ fderiv ℝ F x = 0 ∧
      ω.IsNondegenerateQuadraticFamily fun i ↦ hessianQuadraticForm (fun y ↦ F y i) x :=
  isNondegenerateRankZeroPoint_iff_of_span_eq fun hF _ ↦ span_range_hessianQuadraticForm_pi hF

/-- **Invariance under reparametrization of the values.** Composing `F` with a `C²` map `g` whose
differential at `F x` is injective preserves and reflects nondegenerate rank-zero points. -/
theorem isNondegenerateRankZeroPoint_comp_iff [FiniteDimensional ℝ G'] {g : G → G'}
    (hg : ContDiffAt ℝ 2 g (F x)) (hinj : Function.Injective (fderiv ℝ g (F x)))
    (hF : ContDiffAt ℝ 2 F x) :
    ω.IsNondegenerateRankZeroPoint (g ∘ F) x ↔ ω.IsNondegenerateRankZeroPoint F x := by
  have hgF : fderiv ℝ (g ∘ F) x = (fderiv ℝ g (F x)).comp (fderiv ℝ F x) :=
    fderiv_comp x (hg.differentiableAt (by norm_num)) (hF.differentiableAt (by norm_num))
  have h0 : fderiv ℝ (g ∘ F) x = 0 ↔ fderiv ℝ F x = 0 := by
    rw [hgF]
    refine ⟨fun h ↦ ContinuousLinearMap.ext fun v ↦ hinj ?_,
      fun h ↦ by rw [h, ContinuousLinearMap.comp_zero]⟩
    simpa using congr($h v)
  rw [isNondegenerateRankZeroPoint_iff_of_span_eq fun _ h ↦
    congrArg (Submodule.span ℝ) (range_hessianQuadraticForm_comp hg hinj hF (h0.1 h))]
  exact ⟨fun ⟨_, h, hQ⟩ ↦ ⟨hF, h0.1 h, hQ⟩,
    fun h ↦ ⟨hg.comp x hF, h0.2 h.fderiv_eq_zero, h.isNondegenerateQuadraticFamily⟩⟩

/-- **Nondegenerate rank-zero points of one Hamiltonian on a symplectic plane.** On a
two-dimensional symplectic vector space, a point is a nondegenerate rank-zero point of a function
`H` exactly when it is a nondegenerate critical point of `H` in the sense of Morse theory. -/
theorem isNondegenerateRankZeroPoint_iff_isNondegenerateCriticalPoint (hE : finrank ℝ E = 2)
    {H : E → ℝ} : ω.IsNondegenerateRankZeroPoint H x ↔ IsNondegenerateCriticalPoint H x := by
  rw [isNondegenerateCriticalPoint_iff_hessianQuadraticForm_nondegenerate,
    ← isNondegenerateQuadraticFamily_const_iff (ι := Unit) (ω := ω) hE]
  -- Every functional on `ℝ` is a multiple of the identity.
  have hL : Submodule.span ℝ (Set.range fun _ : Unit ↦ ContinuousLinearMap.id ℝ ℝ) = ⊤ := by
    rw [Set.range_const, eq_top_iff]
    exact fun ℓ _ ↦ Submodule.mem_span_singleton.2 ⟨ℓ 1, ContinuousLinearMap.ext_ring (by simp)⟩
  exact isNondegenerateRankZeroPoint_iff_of_span_eq fun hH _ ↦
    span_range_hessianQuadraticForm_comp_left hH hL

end Function

end TauCeti.SymplecticForm
