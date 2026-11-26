/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.EngelSubalgebra
public import TauCeti.Geometry.Symplectic.Hamiltonian.Quadratic
public import TauCeti.Geometry.Symplectic.LinearReduction
import Mathlib.Algebra.Lie.AdjointAction.Basic
import Mathlib.FieldTheory.Separable
import TauCeti.Algebra.Lie.AdjointAction.Basic
import TauCeti.Algebra.Lie.Subalgebra.Cartan
import TauCeti.Algebra.Lie.Subalgebra.Engel
import TauCeti.Geometry.Symplectic.Plane
import TauCeti.LinearAlgebra.End.Prod
import TauCeti.LinearAlgebra.QuadraticForm.Prod

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
  the linear span of the family (`isNondegenerateQuadraticFamily_iff_of_span_eq`), and is
  invariant under linear symplectomorphisms (`isNondegenerateQuadraticFamily_comp_iff`); a family
  of multiples `c j • Q`, not all zero, is nondegenerate exactly when `Q` is
  (`isNondegenerateQuadraticFamily_smul_iff`). In
  particular, forms on `V` and the forms they induce on the reduced space of `⊤` are nondegenerate
  together (`isNondegenerateQuadraticFamily_reduction_iff_of_eq_top`), and reduced forms may be
  tested on any symplectic slice of the reduced space
  (`isNondegenerateQuadraticFamily_reduction_iff_of_slice`). By
  Mathlib's `LieSubalgebra.normalizer_eq_self_of_engel_le`, a Poisson-commuting family is
  nondegenerate as soon as it contains the Engel subalgebra of one Hamiltonian endomorphism
  (`isNondegenerateQuadraticFamily_of_engel_le`).
* `TauCeti.SymplecticForm.IsNondegenerateRankZeroPoint ω F x`: `x` is a `C²` critical point of
  `F : E → G` at which the Hessians of the functions `ℓ ∘ F`, `ℓ` a linear functional on `G`, form
  a nondegenerate family. For `G = ℝⁿ` these may be replaced by the Hessians of the components
  (`isNondegenerateRankZeroPoint_pi_iff`).

In dimension two the notion reduces to Morse theory: a single quadratic form is a nondegenerate
family exactly when it is a nondegenerate quadratic form
(`isNondegenerateQuadraticFamily_const_iff`), so a nondegenerate rank-zero point of one Hamiltonian
on a symplectic plane is exactly a nondegenerate critical point
(`isNondegenerateRankZeroPoint_iff_isNondegenerateCriticalPoint`). A degenerate form on the plane
is `0` or a multiple of the square of a linear form; its Hamiltonian endomorphism `A` satisfies
`A² = 0`, and the line it spans is strictly smaller than its normalizer in `sp(V, ω)`. The linear
algebra of `sp(V, ω)` on a symplectic plane used here lives in
`TauCeti.Geometry.Symplectic.Plane`.

For a Poisson-commuting family, the generated Lie subalgebra of `sp(V, ω)` is the image of its
span, so nondegeneracy says exactly that this span is its own Poisson normalizer: every form whose
Poisson brackets with the members of the family lie in the span lies in the span itself
(`isNondegenerateQuadraticFamily_iff_forall_mem_span`).

Nondegeneracy is usually checked through a regular semisimple element. If some form `P` has
semisimple Hamiltonian endomorphism and every form Poisson-commuting with `P`, in particular `P`
itself, lies in the span of a Poisson-commuting family, then the family is nondegenerate
(`isNondegenerateQuadraticFamily_of_isSemisimple`): the Engel subalgebra of a semisimple element
is its centralizer. These hypotheses pass to direct sums. On `(V₁ × V₂, ω₁ ⊕ ω₂)`, if `P₁` and
`P₂` satisfy them for families `Q₁` and `Q₂` and the minimal polynomials of `A_{P₁}` and `A_{P₂}`
are coprime, then every form Poisson-commuting with `P₁ ⊕ P₂` is a direct sum, and lies in the span
of the two families extended by zero
(`mem_span_sumElim_prod_of_quadraticPoissonBracket_eq_zero`). A nondegenerate form on a
symplectic plane satisfies the hypotheses for the family it spans
(`isSemisimple_hamiltonianEnd_of_finrank_eq_two`,
`mem_span_singleton_of_quadraticPoissonBracket_eq_zero`). Direct sums of arbitrary nondegenerate
families are treated in `TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.Splitting`.

## Main results

* `TauCeti.SymplecticForm.isNondegenerateQuadraticFamily_iff_forall_mem_span`: a
  Poisson-commuting family is nondegenerate exactly when its span is its own Poisson normalizer.
* `TauCeti.SymplecticForm.isNondegenerateQuadraticFamily_of_isSemisimple`: a Poisson-commuting
  family is nondegenerate if the forms Poisson-commuting with a form `P` with semisimple
  Hamiltonian endomorphism all lie in its span.
* `TauCeti.SymplecticForm.isNondegenerateQuadraticFamily_of_forall_quadraticPoissonBracket_eq_zero`:
  a Poisson-commuting family of forms with semisimple Hamiltonian endomorphisms is nondegenerate if
  every form Poisson-commuting with all of them lies in its span.
* `TauCeti.SymplecticForm.mem_span_sumElim_prod_of_quadraticPoissonBracket_eq_zero`: the forms on
  a direct sum Poisson-commuting with `P₁ ⊕ P₂` lie in the span of the two families extended by
  zero, when the minimal polynomials of `A_{P₁}` and `A_{P₂}` are coprime.

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

/-- The Hamiltonian endomorphism of a form in the span of a family lies in the Lie subalgebra of
`sp(V, ω)` generated by the Hamiltonian endomorphisms of the family. -/
theorem hamiltonianEndEquiv_mem_lieSpan_of_mem_span {Q : ι → QuadraticForm ℝ V}
    {R : QuadraticForm ℝ V} (hR : R ∈ Submodule.span ℝ (Set.range Q)) :
    ω.hamiltonianEndEquiv R ∈ lieSpan ℝ (skewAdjointLieSubalgebra ω.toBilinForm)
      (Set.range fun i ↦ ω.hamiltonianEndEquiv (Q i)) := by
  refine submodule_span_le_lieSpan ?_
  have h := Submodule.mem_map_of_mem (f := ω.hamiltonianEndEquiv.toLinearMap) hR
  rwa [Submodule.map_span, ← Set.range_comp] at h

/-- The Lie subalgebra of `sp(V, ω)` generated by the Hamiltonian endomorphisms of a
Poisson-commuting family is abelian. -/
theorem isLieAbelian_lieSpan_hamiltonianEndEquiv {Q : ι → QuadraticForm ℝ V}
    (hQ : ∀ i j, ω.quadraticPoissonBracket (Q i) (Q j) = 0) :
    IsLieAbelian (lieSpan ℝ (skewAdjointLieSubalgebra ω.toBilinForm)
      (Set.range fun i ↦ ω.hamiltonianEndEquiv (Q i))) := by
  rw [isLieAbelian_lieSpan_iff]
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  rw [← hamiltonianEndEquiv_quadraticPoissonBracket, hQ, map_zero]

/-- For a Poisson-commuting family `Q`, the Hamiltonian endomorphism of a form `R` lies in the Lie
subalgebra of `sp(V, ω)` generated by the Hamiltonian endomorphisms of `Q` exactly when `R` lies
in the span of `Q`: that Lie subalgebra is abelian, hence is their linear span. -/
theorem hamiltonianEndEquiv_mem_lieSpan_iff {Q : ι → QuadraticForm ℝ V}
    (hQ : ∀ i j, ω.quadraticPoissonBracket (Q i) (Q j) = 0) {R : QuadraticForm ℝ V} :
    ω.hamiltonianEndEquiv R ∈ lieSpan ℝ (skewAdjointLieSubalgebra ω.toBilinForm)
        (Set.range fun i ↦ ω.hamiltonianEndEquiv (Q i)) ↔
      R ∈ Submodule.span ℝ (Set.range Q) := by
  refine ⟨fun hR ↦ ?_, hamiltonianEndEquiv_mem_lieSpan_of_mem_span⟩
  have hspan := coe_lieSpan_eq_span_of_forall_lie_eq_zero (R := ℝ)
    (isLieAbelian_lieSpan_iff.1 (isLieAbelian_lieSpan_hamiltonianEndEquiv hQ))
  rw [← mem_toSubmodule, hspan, Set.range_comp'] at hR
  exact (Submodule.apply_mem_span_image_iff_mem_span
    (f := ω.hamiltonianEndEquiv.toLinearMap) ω.hamiltonianEndEquiv.injective).1 hR

/-- Nondegeneracy of a family of quadratic forms depends only on its linear span. -/
theorem isNondegenerateQuadraticFamily_iff_of_span_eq {Q : ι → QuadraticForm ℝ V}
    {Q' : κ → QuadraticForm ℝ V}
    (h : Submodule.span ℝ (Set.range Q) = Submodule.span ℝ (Set.range Q')) :
    ω.IsNondegenerateQuadraticFamily Q ↔ ω.IsNondegenerateQuadraticFamily Q' := by
  rw [isNondegenerateQuadraticFamily_iff, isNondegenerateQuadraticFamily_iff,
    lieSpan_range_hamiltonianEndEquiv, lieSpan_range_hamiltonianEndEquiv, h]

/-! ### The normalizer criterion -/

/-- The Lie subalgebra of `sp(V, ω)` generated by the Hamiltonian endomorphisms of a
Poisson-commuting family is the image of the linear span of the family. -/
private theorem toSubmodule_lieSpan_eq_map_span {Q : ι → QuadraticForm ℝ V}
    (hQ : ∀ i j, ω.quadraticPoissonBracket (Q i) (Q j) = 0) :
    (lieSpan ℝ (skewAdjointLieSubalgebra ω.toBilinForm)
        (Set.range fun i ↦ ω.hamiltonianEndEquiv (Q i))).toSubmodule =
      (Submodule.span ℝ (Set.range Q)).map ω.hamiltonianEndEquiv.toLinearMap := by
  rw [Submodule.map_span, ← Set.range_comp]
  refine coe_lieSpan_eq_span_of_forall_lie_eq_zero ?_
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  rw [← hamiltonianEndEquiv_quadraticPoissonBracket, hQ, map_zero]

/-- **Nondegeneracy through the normalizer.** A Poisson-commuting family is nondegenerate as soon
as every quadratic form whose Poisson brackets with the members of the family lie in its span
lies in that span itself. The converse is `isNondegenerateQuadraticFamily_iff_forall_mem_span`. -/
theorem isNondegenerateQuadraticFamily_of_forall_mem_span {Q : ι → QuadraticForm ℝ V}
    (hQ : ∀ i j, ω.quadraticPoissonBracket (Q i) (Q j) = 0)
    (hR : ∀ R, (∀ i, ω.quadraticPoissonBracket R (Q i) ∈ Submodule.span ℝ (Set.range Q)) →
      R ∈ Submodule.span ℝ (Set.range Q)) :
    ω.IsNondegenerateQuadraticFamily Q := by
  have hspan := toSubmodule_lieSpan_eq_map_span hQ
  have : IsLieAbelian (lieSpan ℝ (skewAdjointLieSubalgebra ω.toBilinForm)
      (Set.range fun i ↦ ω.hamiltonianEndEquiv (Q i))) := by
    rw [isLieAbelian_lieSpan_iff]
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    rw [← hamiltonianEndEquiv_quadraticPoissonBracket, hQ, map_zero]
  refine (isNondegenerateQuadraticFamily_iff Q).2
    ⟨inferInstance, le_antisymm (fun X hX ↦ ?_) (le_normalizer _)⟩
  obtain ⟨R, rfl⟩ := ω.hamiltonianEndEquiv.surjective X
  rw [mem_normalizer_iff] at hX
  rw [← mem_toSubmodule, hspan]
  refine Submodule.mem_map_of_mem (hR R fun i ↦ ?_)
  have hi := hX _ (subset_lieSpan ⟨i, rfl⟩)
  rw [← hamiltonianEndEquiv_quadraticPoissonBracket, ← mem_toSubmodule, hspan] at hi
  simpa using (Submodule.mem_map_equiv _).1 hi

/-- **Nondegeneracy through the normalizer.** A Poisson-commuting family is nondegenerate exactly
when every quadratic form whose Poisson brackets with the members of the family lie in its span
lies in that span itself: the Cartan subalgebra it generates is self-normalizing. -/
theorem isNondegenerateQuadraticFamily_iff_forall_mem_span {Q : ι → QuadraticForm ℝ V}
    (hQ : ∀ i j, ω.quadraticPoissonBracket (Q i) (Q j) = 0) :
    ω.IsNondegenerateQuadraticFamily Q ↔
      ∀ R, (∀ i, ω.quadraticPoissonBracket R (Q i) ∈ Submodule.span ℝ (Set.range Q)) →
        R ∈ Submodule.span ℝ (Set.range Q) := by
  refine ⟨fun h R hR ↦ ?_, isNondegenerateQuadraticFamily_of_forall_mem_span hQ⟩
  have := (isNondegenerateQuadraticFamily_iff Q).1 h
  have hspan := toSubmodule_lieSpan_eq_map_span hQ
  have hmem : ω.hamiltonianEndEquiv R ∈
      lieSpan ℝ (skewAdjointLieSubalgebra ω.toBilinForm)
        (Set.range fun i ↦ ω.hamiltonianEndEquiv (Q i)) := by
    rw [← IsCartanSubalgebra.self_normalizing (H := lieSpan ℝ _ _), mem_normalizer_iff]
    intro y hy
    rw [← mem_toSubmodule, hspan, Submodule.map_span, ← Set.range_comp] at hy
    -- `⁅A_R, ·⁆` is linear and maps the generators into the Cartan subalgebra, hence its span.
    refine Submodule.span_le
      (p := (lieSpan ℝ (skewAdjointLieSubalgebra ω.toBilinForm)
        (Set.range fun i ↦ ω.hamiltonianEndEquiv (Q i))).toSubmodule.comap
          (LieAlgebra.ad ℝ _ (ω.hamiltonianEndEquiv R))) |>.2 ?_ hy
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, LieAlgebra.ad_apply, Function.comp_apply,
      LinearEquiv.coe_coe, ← hamiltonianEndEquiv_quadraticPoissonBracket, mem_toSubmodule]
    exact hamiltonianEndEquiv_mem_lieSpan_of_mem_span (hR i)
  rw [← mem_toSubmodule, hspan] at hmem
  simpa using (Submodule.mem_map_equiv _).1 hmem

/-- **Invariance under linear symplectomorphisms.** If `e : V ≃ V'` carries `ω` to `ω'`, a family
`Q` of quadratic forms on `V'` is nondegenerate for `ω'` exactly when its pullback `Q ∘ e` is
nondegenerate for `ω`: conjugation by `e` is a Lie algebra isomorphism `sp(V, ω) ≃ sp(V', ω')`
carrying `A_{Q ∘ e}` to `A_Q`. -/
theorem isNondegenerateQuadraticFamily_comp_iff {V' : Type*} [AddCommGroup V'] [Module ℝ V']
    [FiniteDimensional ℝ V'] {ω' : SymplecticForm V'} {e : V ≃ₗ[ℝ] V'}
    (he : IsSymplectomorphism ω ω' e) (Q : ι → QuadraticForm ℝ V') :
    ω.IsNondegenerateQuadraticFamily (fun i ↦ (Q i).comp (e : V →ₗ[ℝ] V')) ↔
      ω'.IsNondegenerateQuadraticFamily Q := by
  have hB : ω'.toBilinForm.compl₁₂ (e : V →ₗ[ℝ] V') (e : V →ₗ[ℝ] V') = ω.toBilinForm :=
    LinearMap.ext₂ fun v w ↦ he.apply v w
  -- Conjugation by `e` identifies `sp(V, ω)` with `sp(V', ω')`.
  let φ : skewAdjointLieSubalgebra ω.toBilinForm ≃ₗ⁅ℝ⁆ skewAdjointLieSubalgebra ω'.toBilinForm :=
    (LieEquiv.ofEq _ _ (by rw [hB])).trans (skewAdjointLieSubalgebraEquiv ω'.toBilinForm e)
  have hφ : ∀ R : QuadraticForm ℝ V',
      φ (ω.hamiltonianEndEquiv (R.comp (e : V →ₗ[ℝ] V'))) = ω'.hamiltonianEndEquiv R := by
    intro R
    refine Subtype.ext ?_
    simp only [φ, LieEquiv.trans_apply, skewAdjointLieSubalgebraEquiv_apply,
      LieEquiv.ofEq_apply, LinearEquiv.lieConj_apply, coe_hamiltonianEndEquiv_apply]
    refine ω'.eq_hamiltonianEnd_iff.2 fun v w ↦ ?_
    rw [LinearEquiv.conj_apply_apply, ← e.apply_symm_apply w, he.apply, apply_hamiltonianEnd]
    simp [QuadraticMap.polar]
  have hspan : (lieSpan ℝ (skewAdjointLieSubalgebra ω.toBilinForm) (Set.range fun i ↦
      ω.hamiltonianEndEquiv ((Q i).comp (e : V →ₗ[ℝ] V')))).map (φ : _ →ₗ⁅ℝ⁆ _) =
      lieSpan ℝ (skewAdjointLieSubalgebra ω'.toBilinForm)
        (Set.range fun i ↦ ω'.hamiltonianEndEquiv (Q i)) := by
    rw [LieSubalgebra.map_lieSpan, ← Set.range_comp]
    congr 2
    funext i
    exact hφ (Q i)
  rw [isNondegenerateQuadraticFamily_iff, isNondegenerateQuadraticFamily_iff, ← hspan,
    LieSubalgebra.isCartanSubalgebra_map_lieEquiv_iff]

/-- On the zero symplectic vector space every family of quadratic forms is nondegenerate: the
symplectic Lie algebra is zero, and the zero subalgebra is a Cartan subalgebra. -/
theorem isNondegenerateQuadraticFamily_of_subsingleton [Subsingleton V]
    (Q : ι → QuadraticForm ℝ V) : ω.IsNondegenerateQuadraticFamily Q := by
  have : Subsingleton (skewAdjointLieSubalgebra ω.toBilinForm) :=
    ⟨fun a b ↦ Subtype.ext (Subsingleton.elim (a : Module.End ℝ V) b)⟩
  refine ⟨inferInstance, ?_⟩
  ext a
  simp only [Subsingleton.elim a 0, zero_mem]

/-- Over the whole space, nondegeneracy of a family of reduced quadratic forms is nondegeneracy of
the original family. -/
theorem isNondegenerateQuadraticFamily_reduction_iff_of_eq_top {U : Submodule ℝ V} (hU : U = ⊤)
    (Q : ι → QuadraticForm ℝ V)
    (hQ : ∀ i, ∀ w ∈ U ⊓ ω.orthogonal U, ∀ u ∈ U, QuadraticMap.polar (Q i) w u = 0) :
    (ω.reduction U).IsNondegenerateQuadraticFamily
        (fun i ↦ ω.reducedQuadraticForm U (Q i) (hQ i)) ↔
      ω.IsNondegenerateQuadraticFamily Q := by
  subst hU
  rw [← isNondegenerateQuadraticFamily_comp_iff ω.isSymplectomorphism_reducedSpaceTopEquiv]
  congr! with i
  ext v
  simp

/-- A family of multiples `c i • Q` of a single quadratic form, not all zero, is nondegenerate
exactly when `Q` alone is: both span the line of `Q`. -/
theorem isNondegenerateQuadraticFamily_smul_iff {c : ι → ℝ} {i : ι} (hi : c i ≠ 0)
    (Q : QuadraticForm ℝ V) :
    ω.IsNondegenerateQuadraticFamily (fun j ↦ c j • Q) ↔
      ω.IsNondegenerateQuadraticFamily fun _ : Unit ↦ Q := by
  refine isNondegenerateQuadraticFamily_iff_of_span_eq
    (le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_))
  · rintro _ ⟨j, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(), rfl⟩)
  · rintro _ ⟨-, rfl⟩
    have h := Submodule.smul_mem _ (c i)⁻¹ (Submodule.subset_span (R := ℝ) ⟨i, rfl⟩ :
      c i • Q ∈ Submodule.span ℝ (Set.range fun j ↦ c j • Q))
    rwa [smul_smul, inv_mul_cancel₀ hi, one_smul] at h

/-- **Reduced families in the coordinates of a symplectic slice.** If `j : V₀ → V` has image in
`U`, pulls `ω` back to the symplectic form `ω₀` and `V₀` has the dimension of the reduced space of
`U`, then a family of reduced quadratic forms is nondegenerate exactly when the pullbacks `Q i ∘ j`
of the original forms are nondegenerate for `ω₀`. -/
theorem isNondegenerateQuadraticFamily_reduction_iff_of_slice {V₀ : Type*} [AddCommGroup V₀]
    [Module ℝ V₀] [FiniteDimensional ℝ V₀] {ω₀ : SymplecticForm V₀} {U : Submodule ℝ V}
    {j : V₀ →ₗ[ℝ] V} (hjU : ∀ a, j a ∈ U) (hjω : ∀ a b, ω (j a) (j b) = ω₀ a b)
    (hd : finrank ℝ V₀ = finrank ℝ (ω.ReducedSpace U)) (Q : ι → QuadraticForm ℝ V)
    (hQ : ∀ i, ∀ w ∈ U ⊓ ω.orthogonal U, ∀ u ∈ U, QuadraticMap.polar (Q i) w u = 0) :
    (ω.reduction U).IsNondegenerateQuadraticFamily
        (fun i ↦ ω.reducedQuadraticForm U (Q i) (hQ i)) ↔
      ω₀.IsNondegenerateQuadraticFamily fun i ↦ (Q i).comp j := by
  rw [← isNondegenerateQuadraticFamily_comp_iff
    (isSymplectomorphism_reducedSpaceEquivOfSlice hjU hjω hd)]
  congr! with i
  ext a
  simp

/-- **Regular elements give Cartan subalgebras.** A family of pairwise Poisson-commuting quadratic
forms is nondegenerate as soon as the Engel subalgebra of the Hamiltonian endomorphism of some
quadratic form `P` is contained in the Lie subalgebra the family generates. -/
theorem isNondegenerateQuadraticFamily_of_engel_le
    {Q : ι → QuadraticForm ℝ V} (hQ : ∀ i j, ω.quadraticPoissonBracket (Q i) (Q j) = 0)
    (P : QuadraticForm ℝ V)
    (hP : engel ℝ (ω.hamiltonianEndEquiv P) ≤ lieSpan ℝ (skewAdjointLieSubalgebra ω.toBilinForm)
      (Set.range fun i ↦ ω.hamiltonianEndEquiv (Q i))) :
    ω.IsNondegenerateQuadraticFamily Q := by
  have := isLieAbelian_lieSpan_hamiltonianEndEquiv hQ
  exact ⟨inferInstance, normalizer_eq_self_of_engel_le _ _ hP⟩

section TwoDim

/-- On a symplectic plane, the Hamiltonian endomorphism of a nondegenerate quadratic form squares
to a nonzero homothety. -/
theorem exists_hamiltonianEnd_mul_self_eq_smul_one (hV : finrank ℝ V = 2) {Q : QuadraticForm ℝ V}
    (hQ : Q.Nondegenerate) :
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
    obtain ⟨c', hc0, hc'⟩ := exists_hamiltonianEnd_mul_self_eq_smul_one (ω := ω) hV (by
      rwa [QuadraticMap.nondegenerate_iff_radical_eq_bot, ← ker_hamiltonianEnd ω,
        LinearMap.ker_eq_bot, ← hAQ])
    rw [← hAQ] at hc'
    have : IsLieAbelian (lieSpan ℝ (skewAdjointLieSubalgebra ω.toBilinForm) {A}) := by simp
    exact ⟨inferInstance,
      normalizer_eq_self_of_engel_le _ _ (engel_le_lieSpan_singleton hV hc0 hc')⟩

end TwoDim

/-! ### Regular semisimple elements -/

/-- **The Engel subalgebra of a semisimple element is its centralizer.** If `P` has semisimple
Hamiltonian endomorphism `A_P`, every quadratic form `R` with `A_R` in the Engel subalgebra of
`A_P` in `sp(V, ω)` Poisson-commutes with `P`: `ad A_P` is semisimple on `sp(V, ω)`, so its
generalized kernel is its kernel. -/
theorem quadraticPoissonBracket_eq_zero_of_mem_engel {P R : QuadraticForm ℝ V}
    (hP : (ω.hamiltonianEnd P).IsSemisimple)
    (hR : ω.hamiltonianEndEquiv R ∈ engel ℝ (ω.hamiltonianEndEquiv P)) :
    ω.quadraticPoissonBracket R P = 0 := by
  have hP' : (ω.hamiltonianEndEquiv P : Module.End ℝ V).IsSemisimple := by
    rwa [coe_hamiltonianEndEquiv_apply]
  have had := (skewAdjointLieSubalgebra ω.toBilinForm).isSemisimple_ad_of_isSemisimple_ad
    (x := ω.hamiltonianEndEquiv P) (LieAlgebra.ad_isSemisimple_of_isSemisimple hP')
  rwa [mem_engel_iff_lie_eq_zero had.isFinitelySemisimple,
    ← hamiltonianEndEquiv_quadraticPoissonBracket, LinearEquiv.map_eq_zero_iff,
    ← neg_quadraticPoissonBracket, neg_eq_zero] at hR

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
  obtain ⟨R, rfl⟩ := ω.hamiltonianEndEquiv.surjective X
  exact hamiltonianEndEquiv_mem_lieSpan_of_mem_span
    (hPQ R (quadraticPoissonBracket_eq_zero_of_mem_engel hP hX))

/-- **Toral families spanning their centralizer are nondegenerate.** A family of pairwise
Poisson-commuting quadratic forms whose Hamiltonian endomorphisms are semisimple is nondegenerate
as soon as every quadratic form Poisson-commuting with all members of the family lies in its span:
the abelian subalgebra of `sp(V, ω)` the family generates consists of semisimple elements, so its
normalizer is its centralizer. The converse is
`IsNondegenerateQuadraticFamily.mem_span_of_forall_quadraticPoissonBracket_eq_zero` in
`TauCeti.Geometry.Symplectic.Hamiltonian.Williamson.Toral`. -/
theorem isNondegenerateQuadraticFamily_of_forall_quadraticPoissonBracket_eq_zero
    {Q : ι → QuadraticForm ℝ V} (hQ : ∀ i j, ω.quadraticPoissonBracket (Q i) (Q j) = 0)
    (hs : ∀ i, (ω.hamiltonianEnd (Q i)).IsSemisimple)
    (hR : ∀ R, (∀ i, ω.quadraticPoissonBracket R (Q i) = 0) →
      R ∈ Submodule.span ℝ (Set.range Q)) :
    ω.IsNondegenerateQuadraticFamily Q := by
  -- If `{R, Qᵢ}` lies in the span then `ad(A_{Qᵢ})² A_R = 0`, so `A_R` lies in the Engel
  -- subalgebra of the semisimple element `A_{Qᵢ}`, which is its centralizer.
  refine isNondegenerateQuadraticFamily_of_forall_mem_span hQ fun R hRQ ↦ hR R fun i ↦ ?_
  -- `{Qᵢ, {Qᵢ, R}} = 0`, since `{Qᵢ, R} = -{R, Qᵢ}` lies in the span of the Poisson-commuting
  -- family.
  have hQR : ω.quadraticPoissonBracket (Q i) R ∈ Submodule.span ℝ (Set.range Q) := by
    rw [← neg_quadraticPoissonBracket]
    exact neg_mem (hRQ i)
  have h2 : ω.quadraticPoissonBracket (Q i) (ω.quadraticPoissonBracket (Q i) R) = 0 :=
    ω.quadraticPoissonBracket_eq_zero_of_mem_span hQ (Submodule.subset_span ⟨i, rfl⟩) hQR
  have hmem : ω.hamiltonianEndEquiv R ∈ engel ℝ (ω.hamiltonianEndEquiv (Q i)) := by
    refine (mem_engel_iff _ _ _).2 ⟨2, ?_⟩
    rw [pow_two, mul_apply_eq_comp, LieAlgebra.ad_apply, LieAlgebra.ad_apply,
      ← hamiltonianEndEquiv_quadraticPoissonBracket, ← hamiltonianEndEquiv_quadraticPoissonBracket,
      h2, map_zero]
  exact quadraticPoissonBracket_eq_zero_of_mem_engel (hs i) hmem

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
  -- Split `R₁ ⊕ R₂` as `(R₁ ⊕ 0) + (0 ⊕ R₂)` using linearity of the orthogonal product.
  let L := QuadraticMap.prodLinear ℝ V₁ V₂ ℝ
  have hsum : R₁.prod R₂ = (L ∘ₗ LinearMap.inl ℝ _ _) R₁ + (L ∘ₗ LinearMap.inr ℝ _ _) R₂ := by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← map_add]
    simp [L]
  have h₁' := Submodule.mem_map_of_mem (f := L ∘ₗ LinearMap.inl ℝ _ _) h₁
  have h₂' := Submodule.mem_map_of_mem (f := L ∘ₗ LinearMap.inr ℝ _ _) h₂
  rw [Submodule.map_span] at h₁' h₂'
  rw [hsum]
  refine add_mem (Submodule.span_mono ?_ h₁') (Submodule.span_mono ?_ h₂')
  · rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨Sum.inl i, by simp [L]⟩
  · rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact ⟨Sum.inr j, by simp [L]⟩

end Prod

/-! ### Symplectic planes -/

section Plane

variable {Q : QuadraticForm ℝ V}

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

end Plane

end Linear

/-! ### Nondegenerate rank-zero points of maps -/

section Function

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  (ω : SymplecticForm E)

/-- A point `x` is a **nondegenerate rank-zero point** of a `C²` map `F : E → G` on a symplectic
vector space `(E, ω)` when the differential of `F` vanishes at `x` and the Hessians at `x` of the
functions `ℓ ∘ F`, for `ℓ` a linear functional on `G`, form a nondegenerate family: their
Hamiltonian endomorphisms generate a Cartan subalgebra of `sp(E, ω)`. For `G = ℝⁿ` these are the
Hessians of the components of `F` (`TauCeti.SymplecticForm.isNondegenerateRankZeroPoint_pi_iff`).
-/
@[mk_iff]
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
