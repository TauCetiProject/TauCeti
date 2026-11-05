/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ImplicitFunctionTheorem
public import TauCeti.Geometry.Manifold.LinearSlice
public import TauCeti.Geometry.Manifold.Projectivization.Polynomial
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Level

import Mathlib.Analysis.Analytic.Polynomial

/-!
# Smooth projective zero loci are complex submanifolds

Let `p : ι → MvPolynomial (Fin (n + 1)) ℂ` be a finite family of homogeneous polynomials with zero
locus `X = TauCeti.complexProjectiveZeroLocus p ⊆ ℂℙⁿ`, and let `s = X ∩ V`, for an open set
`V ⊆ ℂℙⁿ`, be a relatively open subset of `X` at every point `L` of which the cone Jacobian
`TauCeti.jacobiMatrixAt p L.rep` is surjective (by
`TauCeti.mulVec_surjective_jacobiMatrixAt_iff_of_mk_eq_mk` this does not depend on the
representative). Then `s`, with the topology it inherits from projective space, is a complex
analytic submanifold of pure dimension `n - |ι|`: it carries the atlas
`TauCeti.complexProjectiveZeroLocusChartedSpace`, modelled on `Fin (n - Fintype.card ι) → ℂ`,
which is analytic, and its inclusion into `ℂℙⁿ` is an analytic embedding and an immersion whose
complement is the space `ι → ℂ` of values of the equations.

Two choices of `s` matter. If the cone Jacobian is surjective at every point of `X`, then
`V = univ` makes all of `X` a complex submanifold. If `X` is singular, or the Jacobian test fails
at some of its points, and `A ⊆ ℂℙⁿ` is a closed set containing every point of `X` at which the
cone Jacobian is not surjective, then `V = Aᶜ` makes the complement `U = X \ A` a complex
submanifold of pure dimension `n - |ι|`, whatever `X` and `A` look like near `A`. This is the
Jacobian test for a smooth complement, for instance of a hyperplane section `A = X ∩ H`. The
points of `X` where the cone Jacobian is not surjective form a closed set
(`TauCeti.isOpen_setOfPred_mulVec_surjective_jacobiMatrixAt_rep`), so `A` may be taken to be
that set.
For a single equation `f` the test is that some partial derivative of `f` does not vanish
(`TauCeti.mulVec_surjective_jacobiMatrixAt_iff_exists_eval_pderiv_ne_zero`). The Jacobian test is
sufficient for smoothness, not necessary: the equations `x` and `x²` have the same zero set.

The atlas is built from ambient slice charts. On the standard affine open `U_i`, where the `i`-th
homogeneous coordinate is nonzero, `X` is cut out by the chart equations
`g_i z = (eval z (dehomogenize i (p k)))_k`. At a point of `X ∩ U_i` the derivative of `g_i` is
surjective exactly when the cone Jacobian is, because it is the cone Jacobian with one column
deleted (`TauCeti.surjective_fderiv_eval_dehomogenize_affineChart_iff`), so it is surjective at
the points of `s ∩ U_i`. Near such a point `L`, the
complemented-kernel implicit function theorem gives the coordinates `z ↦ (g_i z, P (z - z_L))` of
`Fin n → ℂ`, where `P` projects onto the kernel `K` of the derivative of `g_i` at `z_L`, the
chart coordinates of `L`; restricted to the neighbourhood where their derivative stays invertible
they have analytic inverse. Reading `K` in `Fin (n - |ι|) → ℂ` and putting the equations last
gives `TauCeti.complexProjectiveZeroLocusSliceChart`, an analytic chart of `ℂℙⁿ` around `L`
whose second component is `g_i` (`TauCeti.complexProjectiveZeroLocusSliceChart_apply_snd`), so
that it flattens `X` onto the slice where that component vanishes
(`TauCeti.isSliceChart_complexProjectiveZeroLocusSliceChart`). Restricted to `V`, it flattens `s`.
The atlas of `s` is the one these restricted charts induce through
`TauCeti.linearSliceChartedSpace`, using at each point the standard chart `i` that `chartAt` uses
for projective space. The ambient chart is built as in
`HasStrictFDerivAt.exists_isSliceChart_preimage_zero`, which flattens a regular zero set in a
normed space, here composed with the affine chart and read in product coordinates.

The chart equations, read as a function `ℂℙⁿ → (ι → ℂ)` on `U_i`, also give the tangent/normal
sequence of `s`. At a point `z` of `s` in `U_i` the sequence
`0 → T_z s → T_z ℂℙⁿ → (ι → ℂ) → 0` formed by the differentials of the inclusion and of the chart
equations is exact, so the normal space of `s` at `z` is identified with the space `ι → ℂ` of
equation values. This is the general statement
`TauCeti.SmoothEmbedding.tangentRange_eq_ker_mfderiv` for embeddings cut out by equations,
applied to the inclusion bundled as `TauCeti.complexProjectiveZeroLocusEmbedding`.

## Main declarations

* `TauCeti.card_le_of_surjective_jacobiMatrixAt`: surjectivity of the cone Jacobian at a point of
  the zero locus forces at most `n` equations.
* `TauCeti.complexProjectiveZeroLocusSliceChart`: the ambient analytic chart of `ℂℙⁿ` flattening
  the zero locus near a point where the cone Jacobian is surjective.
* `TauCeti.isSliceChart_complexProjectiveZeroLocusSliceChart`,
  `TauCeti.contMDiffOn_complexProjectiveZeroLocusSliceChart` and
  `TauCeti.contMDiffOn_complexProjectiveZeroLocusSliceChart_symm`: it is an analytic slice chart.
* `TauCeti.complexProjectiveZeroLocusChartedSpace`: the induced atlas on a relatively open subset
  `s` of the zero locus on which the cone Jacobian is surjective, modelled on
  `Fin (n - Fintype.card ι) → ℂ`.
* `TauCeti.isManifold_complexProjectiveZeroLocus`: such an `s` is an analytic manifold.
* `TauCeti.isImmersionOfComplement_subtypeVal_complexProjectiveZeroLocus` and
  `TauCeti.isSmoothEmbedding_subtypeVal_complexProjectiveZeroLocus`: its inclusion into `ℂℙⁿ` is
  an analytic immersion with complement `ι → ℂ` and an analytic embedding.
* `TauCeti.complexProjectiveZeroLocusEmbedding`: the inclusion as a bundled smooth embedding.
* `TauCeti.tangentRange_complexProjectiveZeroLocusEmbedding` and
  `TauCeti.exact_mfderiv_subtypeVal_complexProjectiveZeroLocus`: the tangent space of `s` is the
  kernel of the differential of the chart equations.
* `TauCeti.complexProjectiveZeroLocusNormalSpaceEquiv`: the normal space of `s` is identified
  with `ι → ℂ` by the differential of the chart equations.

## References

* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Chapter 0, §2, for complex
  submanifolds of projective space cut out by equations of maximal rank.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 5.8 and Corollary 5.14, for slice charts and regular level sets.
-/

public section

open MvPolynomial Set Projectivization
open scoped ContDiff Manifold LinearAlgebra.Projectivization

namespace TauCeti

variable {ι : Type*} {n : ℕ} {p : ι → MvPolynomial (Fin (n + 1)) ℂ} {d : ι → ℕ}

namespace ComplexProjectiveZeroLocus

/-- The equations of the zero locus in the standard affine chart where coordinate `i` is
nonzero. -/
private noncomputable abbrev eqns (p : ι → MvPolynomial (Fin (n + 1)) ℂ) (i : Fin (n + 1)) :
    (Fin n → ℂ) → ι → ℂ :=
  fun z k ↦ eval z (dehomogenize i (p k))

/-- The chart equations are polynomial, hence analytic. -/
private theorem contDiff_eqns [Fintype ι] (p : ι → MvPolynomial (Fin (n + 1)) ℂ) (i : Fin (n + 1))
    {r : ℕ∞ω} : ContDiff ℂ r (eqns p i) :=
  contDiff_pi.2 fun k ↦ (AnalyticOnNhd.eval_mvPolynomial (dehomogenize i (p k))).contDiff

section Finite

variable [Finite ι]

private theorem hasStrictFDerivAt_eqns (p : ι → MvPolynomial (Fin (n + 1)) ℂ)
    (i : Fin (n + 1)) (y : Fin n → ℂ) :
    HasStrictFDerivAt (eqns p i) (fderiv ℂ (eqns p i) y) y := by
  cases nonempty_fintype ι
  exact (contDiff_eqns p i (r := 1)).contDiffAt.hasStrictFDerivAt_fderiv one_ne_zero

variable {i : Fin (n + 1)} {L : ℙ ℂ (Fin (n + 1) → ℂ)}

/-- At a point of the zero locus where the cone Jacobian is surjective, so is the derivative of
the chart equations. -/
private theorem range_fderiv_eqns (hp : ∀ k, (p k).IsHomogeneous (d k))
    (hL : L ∈ complexProjectiveZeroLocus p) (hi : L ∈ affineOpen i)
    (hrank : Function.Surjective (jacobiMatrixAt p L.rep).mulVec) :
    (fderiv ℂ (eqns p i) (affineChart i L)).range = ⊤ :=
  LinearMap.range_eq_top.2
    ((surjective_fderiv_eval_dehomogenize_affineChart_iff i hp hL hi).2 hrank)

end Finite

variable [Fintype ι] {i : Fin (n + 1)} {L : ℙ ℂ (Fin (n + 1) → ℂ)}

/-- Rank–nullity for the surjective derivative of the chart equations. -/
private theorem card_add_finrank_ker_fderiv_eqns (hp : ∀ k, (p k).IsHomogeneous (d k))
    (hL : L ∈ complexProjectiveZeroLocus p) (hi : L ∈ affineOpen i)
    (hrank : Function.Surjective (jacobiMatrixAt p L.rep).mulVec) :
    Fintype.card ι + Module.finrank ℂ (fderiv ℂ (eqns p i) (affineChart i L)).ker = n := by
  have h := LinearMap.finrank_range_add_finrank_ker
    (fderiv ℂ (eqns p i) (affineChart i L) : (Fin n → ℂ) →ₗ[ℂ] ι → ℂ)
  rwa [range_fderiv_eqns hp hL hi hrank, finrank_top, Module.finrank_fintype_fun_eq_card,
    Module.finrank_fin_fun] at h

/-- The implicit-function chart `z ↦ (g_i z, P (z - z_L))` of the chart equations at the chart
coordinates of `L`. -/
private noncomputable def implicitChart (hp : ∀ k, (p k).IsHomogeneous (d k))
    (hL : L ∈ complexProjectiveZeroLocus p) (hi : L ∈ affineOpen i)
    (hrank : Function.Surjective (jacobiMatrixAt p L.rep).mulVec) :
    OpenPartialHomeomorph (Fin n → ℂ)
      ((ι → ℂ) × (fderiv ℂ (eqns p i) (affineChart i L)).ker) :=
  (hasStrictFDerivAt_eqns p i _).implicitToOpenPartialHomeomorphOfComplemented _ _
    (range_fderiv_eqns hp hL hi hrank)
    (ContinuousLinearMap.ker_closedComplemented_of_finiteDimensional_range _)

/-- The neighbourhood of the chart coordinates of `L` on which the implicit-function chart keeps
an invertible derivative. -/
private noncomputable def implicitSource (hp : ∀ k, (p k).IsHomogeneous (d k))
    (hL : L ∈ complexProjectiveZeroLocus p) (hi : L ∈ affineOpen i)
    (hrank : Function.Surjective (jacobiMatrixAt p L.rep).mulVec) : Set (Fin n → ℂ) :=
  (hasStrictFDerivAt_eqns p i _).implicitCoordSource (range_fderiv_eqns hp hL hi hrank)
    (ContinuousLinearMap.ker_closedComplemented_of_finiteDimensional_range _)

private theorem isOpen_implicitSource (hp : ∀ k, (p k).IsHomogeneous (d k))
    (hL : L ∈ complexProjectiveZeroLocus p) (hi : L ∈ affineOpen i)
    (hrank : Function.Surjective (jacobiMatrixAt p L.rep).mulVec) :
    IsOpen (implicitSource hp hL hi hrank) :=
  (hasStrictFDerivAt_eqns p i _).isOpen_implicitCoordSource _ _

/-- Reading the kernel in `Fin (n - |ι|) → ℂ` and putting the equations last. -/
private noncomputable def coordEquiv (hp : ∀ k, (p k).IsHomogeneous (d k))
    (hL : L ∈ complexProjectiveZeroLocus p) (hi : L ∈ affineOpen i)
    (hrank : Function.Surjective (jacobiMatrixAt p L.rep).mulVec) :
    ((ι → ℂ) × (fderiv ℂ (eqns p i) (affineChart i L)).ker) ≃L[ℂ]
      (Fin (n - Fintype.card ι) → ℂ) × (ι → ℂ) :=
  (ContinuousLinearEquiv.prodComm ℂ _ _).trans
    ((ContinuousLinearEquiv.ofFinrankEq (by
      have := card_add_finrank_ker_fderiv_eqns hp hL hi hrank
      rw [Module.finrank_fin_fun]
      omega)).prodCongr (ContinuousLinearEquiv.refl ℂ _))

/-- The identification of the slice-chart model with the model `Fin n → ℂ` of `ℂℙⁿ`, when there
are at most `n` equations. -/
private noncomputable def modelEquiv (h : Fintype.card ι ≤ n) :
    ((Fin (n - Fintype.card ι) → ℂ) × (ι → ℂ)) ≃L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearEquiv.ofFinrankEq (by
    simp only [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    omega)

@[simp]
private theorem coordEquiv_apply_snd (hp : ∀ k, (p k).IsHomogeneous (d k))
    (hL : L ∈ complexProjectiveZeroLocus p) (hi : L ∈ affineOpen i)
    (hrank : Function.Surjective (jacobiMatrixAt p L.rep).mulVec)
    (v : (ι → ℂ) × (fderiv ℂ (eqns p i) (affineChart i L)).ker) :
    (coordEquiv hp hL hi hrank v).2 = v.1 :=
  (rfl)

end ComplexProjectiveZeroLocus

open ComplexProjectiveZeroLocus

variable [Fintype ι] {i : Fin (n + 1)} {L : ℙ ℂ (Fin (n + 1) → ℂ)}

/-- **Equation count at a smooth point.** If the cone Jacobian of a homogeneous family `p` is
surjective at a point of its zero locus in `ℂℙⁿ`, there are at most `n` equations, so the
dimension `n - |ι|` of the zero locus near that point is the honest difference. -/
theorem card_le_of_surjective_jacobiMatrixAt (hp : ∀ k, (p k).IsHomogeneous (d k))
    (hL : L ∈ complexProjectiveZeroLocus p)
    (hrank : Function.Surjective (jacobiMatrixAt p L.rep).mulVec) : Fintype.card ι ≤ n := by
  obtain ⟨i, hi⟩ := exists_mem_affineOpen L
  have := card_add_finrank_ker_fderiv_eqns hp hL hi hrank
  omega

/-- **The slice chart of a smooth projective zero locus.** Let `L` be a point of the zero locus
of a homogeneous family `p`, in the standard affine open `U_i`, at which the cone Jacobian of `p`
is surjective. This is an analytic chart of `ℂℙⁿ` around `L`, modelled on
`(Fin (n - |ι|) → ℂ) × (ι → ℂ)`, whose second component is the family of chart equations
`eval (affineChart i ·) (dehomogenize i (p k))`
(`TauCeti.complexProjectiveZeroLocusSliceChart_apply_snd`) and which therefore flattens the zero
locus onto the slice where that component vanishes
(`TauCeti.isSliceChart_complexProjectiveZeroLocusSliceChart`). Its first component reads the
displacement of the chart coordinates from those of `L` along the kernel of the derivative of the
chart equations at `L`. -/
noncomputable def complexProjectiveZeroLocusSliceChart (hp : ∀ k, (p k).IsHomogeneous (d k))
    (hL : L ∈ complexProjectiveZeroLocus p) (hi : L ∈ affineOpen i)
    (hrank : Function.Surjective (jacobiMatrixAt p L.rep).mulVec) :
    OpenPartialHomeomorph (ℙ ℂ (Fin (n + 1) → ℂ)) ((Fin (n - Fintype.card ι) → ℂ) × (ι → ℂ)) :=
  (affineOpenPartialHomeomorph i).trans
    (((implicitChart hp hL hi hrank).restrOpen (implicitSource hp hL hi hrank)
      (isOpen_implicitSource hp hL hi hrank)).transHomeomorph
      (coordEquiv hp hL hi hrank).toHomeomorph)

section SliceChart

variable (hp : ∀ k, (p k).IsHomogeneous (d k)) (hL : L ∈ complexProjectiveZeroLocus p)
  (hi : L ∈ affineOpen i) (hrank : Function.Surjective (jacobiMatrixAt p L.rep).mulVec)

/-- The slice chart unfolded: the affine chart, then the implicit-function chart of the chart
equations, then the linear identification of its target with the model. -/
private theorem coe_complexProjectiveZeroLocusSliceChart :
    ⇑(complexProjectiveZeroLocusSliceChart hp hL hi hrank) =
      coordEquiv hp hL hi hrank ∘ implicitChart hp hL hi hrank ∘ affineChart i := by
  rw [complexProjectiveZeroLocusSliceChart, OpenPartialHomeomorph.coe_trans,
    OpenPartialHomeomorph.transHomeomorph_apply, OpenPartialHomeomorph.coe_restrOpen,
    coe_affineOpenPartialHomeomorph, ContinuousLinearEquiv.coe_toHomeomorph]
  rfl

private theorem coe_complexProjectiveZeroLocusSliceChart_symm :
    ⇑(complexProjectiveZeroLocusSliceChart hp hL hi hrank).symm =
      (affineChart i).symm ∘ (implicitChart hp hL hi hrank).symm ∘
        (coordEquiv hp hL hi hrank).symm := by
  rw [complexProjectiveZeroLocusSliceChart, OpenPartialHomeomorph.coe_trans_symm,
    OpenPartialHomeomorph.transHomeomorph_symm_apply, OpenPartialHomeomorph.coe_restrOpen_symm,
    coe_affineOpenPartialHomeomorph_symm, ContinuousLinearEquiv.coe_symm_toHomeomorph]

/-- The source of the slice chart: points of `U_i` whose chart coordinates lie in the source of
the implicit-function chart, restricted to where its derivative stays invertible. -/
private theorem complexProjectiveZeroLocusSliceChart_source :
    (complexProjectiveZeroLocusSliceChart hp hL hi hrank).source =
      affineOpen i ∩ affineChart i ⁻¹'
        ((implicitChart hp hL hi hrank).source ∩ implicitSource hp hL hi hrank) := by
  rw [complexProjectiveZeroLocusSliceChart, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.transHomeomorph_source, OpenPartialHomeomorph.restrOpen_source,
    coe_affineOpenPartialHomeomorph]
  simp only [affineOpenPartialHomeomorph_toPartialEquiv, affineChart_source, preimage_inter]

/-- The target of the slice chart: the points whose image under the inverse linear
identification lies in the target of the implicit-function chart, with inverse image in the
neighbourhood where its derivative stays invertible. -/
private theorem complexProjectiveZeroLocusSliceChart_target :
    (complexProjectiveZeroLocusSliceChart hp hL hi hrank).target =
      (coordEquiv hp hL hi hrank).symm ⁻¹' ((implicitChart hp hL hi hrank).target ∩
        (implicitChart hp hL hi hrank).symm ⁻¹' implicitSource hp hL hi hrank) := by
  rw [complexProjectiveZeroLocusSliceChart, OpenPartialHomeomorph.trans_target,
    OpenPartialHomeomorph.transHomeomorph_target, OpenPartialHomeomorph.restrOpen_toPartialEquiv]
  simp

/-- The second component of the slice chart is the family of chart equations of the zero locus in
the standard affine chart `i`. -/
@[simp]
theorem complexProjectiveZeroLocusSliceChart_apply_snd (w : ℙ ℂ (Fin (n + 1) → ℂ)) :
    (complexProjectiveZeroLocusSliceChart hp hL hi hrank w).2 =
      fun k ↦ eval (affineChart i w) (dehomogenize i (p k)) := by
  rw [coe_complexProjectiveZeroLocusSliceChart, Function.comp_apply, coordEquiv_apply_snd,
    Function.comp_apply, implicitChart,
    HasStrictFDerivAt.implicitToOpenPartialHomeomorphOfComplemented_fst]

/-- The source of the slice chart lies in the standard affine open `U_i`. -/
theorem complexProjectiveZeroLocusSliceChart_source_subset :
    (complexProjectiveZeroLocusSliceChart hp hL hi hrank).source ⊆ affineOpen i := by
  rw [complexProjectiveZeroLocusSliceChart_source]
  exact inter_subset_left

/-- The slice chart is defined at its base point. -/
theorem mem_complexProjectiveZeroLocusSliceChart_source :
    L ∈ (complexProjectiveZeroLocusSliceChart hp hL hi hrank).source := by
  rw [complexProjectiveZeroLocusSliceChart_source]
  refine ⟨hi, ?_, ?_⟩
  · exact (hasStrictFDerivAt_eqns p i _).mem_implicitToOpenPartialHomeomorphOfComplemented_source
      _ _
  · exact (hasStrictFDerivAt_eqns p i _).mem_implicitCoordSource _ _

/-- **The slice chart flattens the zero locus.** On its source, a point lies in the zero locus
exactly when its slice-chart coordinates lie in the slice `Fin (n - |ι|) → ℂ` times `0`. -/
theorem isSliceChart_complexProjectiveZeroLocusSliceChart :
    IsSliceChart (complexProjectiveZeroLocusSliceChart hp hL hi hrank)
      ((univ : Set (Fin (n - Fintype.card ι) → ℂ)) ×ˢ ({0} : Set (ι → ℂ)))
      (complexProjectiveZeroLocus p) := by
  refine isSliceChart_iff.2 fun w hw ↦ ?_
  rw [mem_complexProjectiveZeroLocus_iff_eval_affineChart hp
    (complexProjectiveZeroLocusSliceChart_source_subset hp hL hi hrank hw)]
  simp [funext_iff]

/-- The slice chart is analytic, indeed `C^r` for every `r`, on its source. -/
theorem contMDiffOn_complexProjectiveZeroLocusSliceChart (r : ℕ∞ω) :
    ContMDiffOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, (Fin (n - Fintype.card ι) → ℂ) × (ι → ℂ)) r
      (complexProjectiveZeroLocusSliceChart hp hL hi hrank)
      (complexProjectiveZeroLocusSliceChart hp hL hi hrank).source := by
  intro w hw
  have hwi := complexProjectiveZeroLocusSliceChart_source_subset hp hL hi hrank hw
  have hchart : ContMDiffAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) r (affineChart i) w :=
    (contMDiffOn_affineChart i r).contMDiffAt ((isOpen_affineOpen i).mem_nhds hwi)
  have himplicit : ContDiffAt ℂ r (coordEquiv hp hL hi hrank ∘ implicitChart hp hL hi hrank)
      (affineChart i w) :=
    (coordEquiv hp hL hi hrank).contDiff.contDiffAt.comp _
      ((hasStrictFDerivAt_eqns p i _).contDiffAt_implicitToOpenPartialHomeomorphOfComplemented
        (contDiff_eqns p i).contDiffAt _ _)
  rw [coe_complexProjectiveZeroLocusSliceChart]
  exact (himplicit.contMDiffAt.comp w hchart).contMDiffWithinAt

/-- The inverse of the slice chart is analytic, indeed `C^r` for every `r`, on its target. -/
theorem contMDiffOn_complexProjectiveZeroLocusSliceChart_symm (r : ℕ∞ω) :
    ContMDiffOn 𝓘(ℂ, (Fin (n - Fintype.card ι) → ℂ) × (ι → ℂ)) 𝓘(ℂ, Fin n → ℂ) r
      (complexProjectiveZeroLocusSliceChart hp hL hi hrank).symm
      (complexProjectiveZeroLocusSliceChart hp hL hi hrank).target := by
  intro v hv
  -- The target of the slice chart sits over the restricted target of the implicit chart.
  rw [complexProjectiveZeroLocusSliceChart_target] at hv
  obtain ⟨hvt, hvs⟩ := hv
  have hΦ := hasStrictFDerivAt_eqns p i (affineChart i L)
  have hinv : ContDiffAt ℂ r
      ((implicitChart hp hL hi hrank).symm ∘ (coordEquiv hp hL hi hrank).symm) v :=
    (hΦ.contDiffAt_implicitToOpenPartialHomeomorphOfComplemented_symm_of_mem _ _ hvt hvs
      ((contDiff_eqns p i (r := 1)).differentiable one_ne_zero _).hasFDerivAt
      (contDiff_eqns p i).contDiffAt).comp v (coordEquiv hp hL hi hrank).symm.contDiff.contDiffAt
  rw [coe_complexProjectiveZeroLocusSliceChart_symm]
  exact ((contMDiff_affineChart_symm i r _).comp v hinv.contMDiffAt).contMDiffWithinAt

end SliceChart

/-! ### The submanifold structure -/

section Submanifold

variable (hp : ∀ k, (p k).IsHomogeneous (d k)) {s V : Set (ℙ ℂ (Fin (n + 1) → ℂ))}
  (hV : IsOpen V) (hs : s = complexProjectiveZeroLocus p ∩ V)
  (hrank : ∀ L ∈ s, Function.Surjective (jacobiMatrixAt p L.rep).mulVec)

/-- The slice chart at a point `z` of `s`, taken in the standard affine chart that `chartAt` uses
for projective space at `z` and restricted to the open set cutting `s` out of the zero locus. -/
private noncomputable def restrSliceChart (z : s) :
    OpenPartialHomeomorph (ℙ ℂ (Fin (n + 1) → ℂ)) ((Fin (n - Fintype.card ι) → ℂ) × (ι → ℂ)) :=
  (complexProjectiveZeroLocusSliceChart hp (hs.subset z.2).1
    (exists_mem_affineOpen (z : ℙ ℂ (Fin (n + 1) → ℂ))).choose_spec (hrank z z.2)).restrOpen V hV

private theorem restrSliceChart_source (z : s) :
    (restrSliceChart hp hV hs hrank z).source =
      (complexProjectiveZeroLocusSliceChart hp (hs.subset z.2).1
        (exists_mem_affineOpen (z : ℙ ℂ (Fin (n + 1) → ℂ))).choose_spec (hrank z z.2)).source ∩ V :=
  OpenPartialHomeomorph.restrOpen_source _ _ _

private theorem isSliceChart_restrSliceChart (z : s) :
    IsSliceChart (restrSliceChart hp hV hs hrank z)
      ((univ : Set (Fin (n - Fintype.card ι) → ℂ)) ×ˢ ({0} : Set (ι → ℂ))) s := by
  simpa only [restrSliceChart, ← hs] using
    (isSliceChart_complexProjectiveZeroLocusSliceChart hp _ _ _).restrOpen hV

private theorem mem_restrSliceChart_source (z : s) : (z : ℙ ℂ (Fin (n + 1) → ℂ)) ∈
    (restrSliceChart hp hV hs hrank z).source := by
  rw [restrSliceChart_source]
  exact ⟨mem_complexProjectiveZeroLocusSliceChart_source hp _ _ _, (hs.subset z.2).2⟩

private theorem contMDiffOn_restrSliceChart (r : ℕ∞ω) (z : s) :
    ContMDiffOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, (Fin (n - Fintype.card ι) → ℂ) × (ι → ℂ)) r
      (restrSliceChart hp hV hs hrank z) (restrSliceChart hp hV hs hrank z).source := by
  rw [restrSliceChart_source]
  exact (contMDiffOn_complexProjectiveZeroLocusSliceChart hp _ _ _ r).mono inter_subset_left

private theorem contMDiffOn_restrSliceChart_symm (r : ℕ∞ω) (z : s) :
    ContMDiffOn 𝓘(ℂ, (Fin (n - Fintype.card ι) → ℂ) × (ι → ℂ)) 𝓘(ℂ, Fin n → ℂ) r
      (restrSliceChart hp hV hs hrank z).symm (restrSliceChart hp hV hs hrank z).target :=
  (contMDiffOn_complexProjectiveZeroLocusSliceChart_symm hp _ _ _ r).mono fun _ hv ↦ hv.1

/-- **The complex manifold structure of the smooth part of a projective zero locus.** Let `s` be
a relatively open subset of the zero locus of a homogeneous family `p`, that is
`s = complexProjectiveZeroLocus p ∩ V` for an open set `V` of `ℂℙⁿ`, at every point of which the
cone Jacobian of `p` is surjective. Then `s`, with the topology induced from `ℂℙⁿ`, carries the
atlas induced by the slice charts `TauCeti.complexProjectiveZeroLocusSliceChart`, modelled on
`Fin (n - Fintype.card ι) → ℂ`. At a point `L` the chart is taken in the standard affine chart that
`chartAt` uses for projective space at `L`
(`TauCeti.complexProjectiveZeroLocusChartedSpace_chartAt_apply`).

Taking `V = univ` gives the whole zero locus when the cone Jacobian is surjective at all of its
points. Taking for `V` the complement of a closed set `A` gives the complement `X \ A` of `A` in
the zero locus `X`, when `A` contains every point of `X` at which the cone Jacobian is not
surjective. -/
@[instance_reducible]
noncomputable def complexProjectiveZeroLocusChartedSpace :
    ChartedSpace (Fin (n - Fintype.card ι) → ℂ) s :=
  linearSliceChartedSpace (restrSliceChart hp hV hs hrank)
    (isSliceChart_restrSliceChart hp hV hs hrank)
    (mem_restrSliceChart_source hp hV hs hrank)

/-- The chart of `s` at `z` reads the first coordinate of the slice chart at `z`. -/
theorem complexProjectiveZeroLocusChartedSpace_chartAt_apply (z w : s) :
    @chartAt _ _ _ _ (complexProjectiveZeroLocusChartedSpace hp hV hs hrank) z w =
      (complexProjectiveZeroLocusSliceChart hp (hs.subset z.2).1
        (exists_mem_affineOpen (z : ℙ ℂ (Fin (n + 1) → ℂ))).choose_spec (hrank z z.2) w).1 := by
  rw [complexProjectiveZeroLocusChartedSpace, linearSliceChartedSpace_chartAt,
    linearSliceChart_apply, restrSliceChart, OpenPartialHomeomorph.coe_restrOpen]

/-- The chart of `s` at `z` is defined on the part of `s` in the source of the slice chart at
`z`. -/
theorem complexProjectiveZeroLocusChartedSpace_chartAt_source (z : s) :
    (@chartAt _ _ _ _ (complexProjectiveZeroLocusChartedSpace hp hV hs hrank) z).source =
      Subtype.val ⁻¹' (complexProjectiveZeroLocusSliceChart hp (hs.subset z.2).1
        (exists_mem_affineOpen (z : ℙ ℂ (Fin (n + 1) → ℂ))).choose_spec (hrank z z.2)).source := by
  rw [complexProjectiveZeroLocusChartedSpace, linearSliceChartedSpace_chartAt,
    linearSliceChart_source, restrSliceChart_source, preimage_inter, inter_eq_left]
  exact fun w _ ↦ (hs.subset w.2).2

/-- **The smooth part of a projective zero locus is a complex manifold.** With the atlas
`TauCeti.complexProjectiveZeroLocusChartedSpace`, a relatively open subset of the zero locus on
which the cone Jacobian is surjective is an analytic manifold of pure dimension `n - |ι|`; it is
`C^r` for every `r`. -/
theorem isManifold_complexProjectiveZeroLocus (r : ℕ∞ω) :
    letI := complexProjectiveZeroLocusChartedSpace hp hV hs hrank
    IsManifold 𝓘(ℂ, Fin (n - Fintype.card ι) → ℂ) r s :=
  isManifold_linearSliceChartedSpace _ _
    (fun z _ hw ↦ (contMDiffOn_restrSliceChart hp hV hs hrank r z).contMDiffAt
      ((OpenPartialHomeomorph.open_source _).mem_nhds hw))
    (fun z _ hv ↦ (contMDiffOn_restrSliceChart_symm hp hV hs hrank r z).contMDiffAt
      ((OpenPartialHomeomorph.open_target _).mem_nhds hv)) _

/-- **The inclusion of the smooth part of a projective zero locus is an immersion with normal
model `ι → ℂ`.** For the atlas `TauCeti.complexProjectiveZeroLocusChartedSpace`, the inclusion
into `ℂℙⁿ` is a `C^r` immersion, for every `r`, whose complement is the space `ι → ℂ` of values of
the equations. -/
theorem isImmersionOfComplement_subtypeVal_complexProjectiveZeroLocus (r : ℕ∞ω) :
    letI := complexProjectiveZeroLocusChartedSpace hp hV hs hrank
    Manifold.IsImmersionOfComplement (ι → ℂ) 𝓘(ℂ, Fin (n - Fintype.card ι) → ℂ)
      𝓘(ℂ, Fin n → ℂ) r (Subtype.val : s → ℙ ℂ (Fin (n + 1) → ℂ)) :=
  isImmersionOfComplement_subtypeVal_linearSliceChartedSpace _ _
    (fun z ↦ modelEquiv (card_le_of_surjective_jacobiMatrixAt hp (hs.subset z.2).1 (hrank z z.2)))
    (contMDiffOn_restrSliceChart hp hV hs hrank r)
    (contMDiffOn_restrSliceChart_symm hp hV hs hrank r) _

/-- **The smooth part of a projective zero locus is an embedded complex submanifold.** For the
atlas `TauCeti.complexProjectiveZeroLocusChartedSpace`, the inclusion into `ℂℙⁿ` is a `C^r`
embedding for every `r`. -/
theorem isSmoothEmbedding_subtypeVal_complexProjectiveZeroLocus (r : ℕ∞ω) :
    letI := complexProjectiveZeroLocusChartedSpace hp hV hs hrank
    Manifold.IsSmoothEmbedding 𝓘(ℂ, Fin (n - Fintype.card ι) → ℂ) 𝓘(ℂ, Fin n → ℂ) r
      (Subtype.val : s → ℙ ℂ (Fin (n + 1) → ℂ)) :=
  isSmoothEmbedding_subtypeVal_linearSliceChartedSpace _ _
    (fun z ↦ modelEquiv (card_le_of_surjective_jacobiMatrixAt hp (hs.subset z.2).1 (hrank z z.2)))
    (contMDiffOn_restrSliceChart hp hV hs hrank r)
    (contMDiffOn_restrSliceChart_symm hp hV hs hrank r) _

end Submanifold

/-! ### The tangent and normal spaces -/

section TangentNormal

variable (hp : ∀ k, (p k).IsHomogeneous (d k)) {s V : Set (ℙ ℂ (Fin (n + 1) → ℂ))}
  (hV : IsOpen V) (hs : s = complexProjectiveZeroLocus p ∩ V)
  (hrank : ∀ L ∈ s, Function.Surjective (jacobiMatrixAt p L.rep).mulVec)
  (r : ℕ∞ω)

/-- **The smooth part of a projective zero locus as a bundled embedding.** The inclusion of a
relatively open subset `s` of the zero locus on which the cone Jacobian is surjective, with the
atlas `TauCeti.complexProjectiveZeroLocusChartedSpace`, into `ℂℙⁿ` as a `C^r` embedding.
It is built as a structure rather than through `TauCeti.SmoothEmbedding.ofIsSmoothEmbedding`
so that its coercion is `Subtype.val` by definition, which lets the statements below use the
points of `s` rather than their images under the embedding. -/
noncomputable def complexProjectiveZeroLocusEmbedding :
    letI := complexProjectiveZeroLocusChartedSpace hp hV hs hrank
    SmoothEmbedding 𝓘(ℂ, Fin (n - Fintype.card ι) → ℂ) 𝓘(ℂ, Fin n → ℂ) r s
      (ℙ ℂ (Fin (n + 1) → ℂ)) :=
  letI := complexProjectiveZeroLocusChartedSpace hp hV hs hrank
  { toContMDiffMap :=
      ⟨Subtype.val,
        (isSmoothEmbedding_subtypeVal_complexProjectiveZeroLocus hp hV hs hrank r).contMDiff⟩
    isSmoothEmbedding_toFun :=
      isSmoothEmbedding_subtypeVal_complexProjectiveZeroLocus hp hV hs hrank r }

/-- The bundled embedding of the smooth part of a projective zero locus is the inclusion. -/
@[simp]
theorem coe_complexProjectiveZeroLocusEmbedding :
    letI := complexProjectiveZeroLocusChartedSpace hp hV hs hrank
    ⇑(complexProjectiveZeroLocusEmbedding hp hV hs hrank r) = Subtype.val :=
  (rfl)

variable {r}

omit [Fintype ι] in
/-- The chart equations of the zero locus vanish on `s` near each of its points in `U_i`. -/
private theorem eventually_eval_dehomogenize_affineChart_eq_zero
    (hp : ∀ k, (p k).IsHomogeneous (d k)) (hs : s = complexProjectiveZeroLocus p ∩ V) (z : s)
    (hi : (z : ℙ ℂ (Fin (n + 1) → ℂ)) ∈ affineOpen i) :
    ∀ᶠ w : s in nhds z, (fun k ↦ eval (affineChart i w.1) (dehomogenize i (p k))) = 0 := by
  filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds
    ((isOpen_affineOpen i).mem_nhds hi)] with w hw
  exact funext ((mem_complexProjectiveZeroLocus_iff_eval_affineChart hp hw).1
    (hs.subset w.2).1)

/-- The dimensions of `s` and of the space of equation values add up to `n`. -/
private theorem finrank_add_finrank_eq (hp : ∀ k, (p k).IsHomogeneous (d k))
    (hs : s = complexProjectiveZeroLocus p ∩ V)
    (hrank : ∀ L ∈ s, Function.Surjective (jacobiMatrixAt p L.rep).mulVec) (z : s) :
    Module.finrank ℂ (Fin (n - Fintype.card ι) → ℂ) + Module.finrank ℂ (ι → ℂ) =
      Module.finrank ℂ (Fin n → ℂ) := by
  have := card_le_of_surjective_jacobiMatrixAt hp (hs.subset z.2).1 (hrank z z.2)
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  omega

/-- The chart equations of the zero locus are regular at each point of `s` in `U_i`. -/
private theorem isRegularPoint_eval_dehomogenize_affineChart (hp : ∀ k, (p k).IsHomogeneous (d k))
    (hs : s = complexProjectiveZeroLocus p ∩ V)
    (hrank : ∀ L ∈ s, Function.Surjective (jacobiMatrixAt p L.rep).mulVec)
    (z : s) (hi : (z : ℙ ℂ (Fin (n + 1) → ℂ)) ∈ affineOpen i) :
    IsRegularPoint 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ι → ℂ)
      (fun w ↦ fun k ↦ eval (affineChart i w) (dehomogenize i (p k)))
      (z : ℙ ℂ (Fin (n + 1) → ℂ)) :=
  isRegularPoint_iff.2 ((surjective_mfderiv_eval_dehomogenize_affineChart_iff i hp
    (hs.subset z.2).1 hi).2 (hrank z z.2))

/-- **The tangent space of the smooth part of a projective zero locus.** At a point `z` of `s` in
the standard affine open `U_i`, the image of the differential of the inclusion into `ℂℙⁿ` is the
kernel of the differential of the chart equations
`eval (affineChart i ·) (dehomogenize i (p k))`. -/
theorem tangentRange_complexProjectiveZeroLocusEmbedding (hr : r ≠ 0)
    (z : s) (hi : (z : ℙ ℂ (Fin (n + 1) → ℂ)) ∈ affineOpen i) :
    letI := complexProjectiveZeroLocusChartedSpace hp hV hs hrank
    (complexProjectiveZeroLocusEmbedding hp hV hs hrank r).tangentRange z hr =
      (mfderiv 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ι → ℂ)
        (fun w ↦ fun k ↦ eval (affineChart i w) (dehomogenize i (p k))) z).ker :=
  letI := complexProjectiveZeroLocusChartedSpace hp hV hs hrank
  SmoothEmbedding.tangentRange_eq_ker_mfderiv _ z hr
    (eventually_eval_dehomogenize_affineChart_eq_zero hp hs z hi)
    (isRegularPoint_eval_dehomogenize_affineChart hp hs hrank z hi)
    (finrank_add_finrank_eq hp hs hrank z)

/-- **The tangent sequence of the smooth part of a projective zero locus is exact.** At a point
`z` of `s` in the standard affine open `U_i`, the differentials of the inclusion into `ℂℙⁿ` and of
the chart equations form an exact sequence `0 → T_z s → T_z ℂℙⁿ → ι → ℂ → 0`; the differential of
the inclusion is injective since it is an immersion
(`TauCeti.isImmersionOfComplement_subtypeVal_complexProjectiveZeroLocus`), and that of the chart
equations is surjective by `TauCeti.surjective_mfderiv_eval_dehomogenize_affineChart_iff`. -/
theorem exact_mfderiv_subtypeVal_complexProjectiveZeroLocus
    (z : s) (hi : (z : ℙ ℂ (Fin (n + 1) → ℂ)) ∈ affineOpen i) :
    letI := complexProjectiveZeroLocusChartedSpace hp hV hs hrank
    Function.Exact
      (mfderiv 𝓘(ℂ, Fin (n - Fintype.card ι) → ℂ) 𝓘(ℂ, Fin n → ℂ) Subtype.val z)
      (mfderiv 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ι → ℂ)
        (fun w ↦ fun k ↦ eval (affineChart i w) (dehomogenize i (p k))) z) :=
  letI := complexProjectiveZeroLocusChartedSpace hp hV hs hrank
  LinearMap.exact_iff.2
    (tangentRange_complexProjectiveZeroLocusEmbedding hp hV hs hrank (r := 1) one_ne_zero z hi).symm

/-- **The normal space of the smooth part of a projective zero locus.** At a point `z` of `s` in
the standard affine open `U_i`, the differential of the chart equations induces a continuous
linear equivalence from the normal space of `s` in `ℂℙⁿ` onto the space `ι → ℂ` of equation
values (`TauCeti.complexProjectiveZeroLocusNormalSpaceEquiv_normalClass`). -/
noncomputable def complexProjectiveZeroLocusNormalSpaceEquiv (hr : r ≠ 0)
    (z : s) (hi : (z : ℙ ℂ (Fin (n + 1) → ℂ)) ∈ affineOpen i) :
    letI := complexProjectiveZeroLocusChartedSpace hp hV hs hrank
    (complexProjectiveZeroLocusEmbedding hp hV hs hrank r).NormalSpace z hr ≃L[ℂ] (ι → ℂ) :=
  letI := complexProjectiveZeroLocusChartedSpace hp hV hs hrank
  SmoothEmbedding.normalSpaceEquivOfLevel _ z hr
    (eventually_eval_dehomogenize_affineChart_eq_zero hp hs z hi)
    (isRegularPoint_eval_dehomogenize_affineChart hp hs hrank z hi)
    (finrank_add_finrank_eq hp hs hrank z)

/-- The normal-space equivalence of the smooth part of a projective zero locus sends the normal
class of an ambient tangent vector `v` to the differential of the chart equations applied to
`v`. -/
@[simp]
theorem complexProjectiveZeroLocusNormalSpaceEquiv_normalClass (hr : r ≠ 0)
    (z : s) (hi : (z : ℙ ℂ (Fin (n + 1) → ℂ)) ∈ affineOpen i)
    (v : TangentSpace 𝓘(ℂ, Fin n → ℂ) (z : ℙ ℂ (Fin (n + 1) → ℂ))) :
    letI := complexProjectiveZeroLocusChartedSpace hp hV hs hrank
    complexProjectiveZeroLocusNormalSpaceEquiv hp hV hs hrank hr z hi
        ((complexProjectiveZeroLocusEmbedding hp hV hs hrank r).normalClass z hr v) =
      mfderiv 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ι → ℂ)
        (fun w ↦ fun k ↦ eval (affineChart i w) (dehomogenize i (p k))) z v :=
  letI := complexProjectiveZeroLocusChartedSpace hp hV hs hrank
  SmoothEmbedding.normalSpaceEquivOfLevel_normalClass _ _ _ _ _ _ v

end TangentNormal

end TauCeti
