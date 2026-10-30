/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ImplicitFunctionTheorem
public import TauCeti.Geometry.Manifold.LinearSlice
public import TauCeti.Geometry.Manifold.Projectivization.Polynomial

import Mathlib.Analysis.Analytic.Polynomial

/-!
# Smooth projective zero loci are complex submanifolds

Let `p : ι → MvPolynomial (Fin (n + 1)) ℂ` be a finite family of homogeneous polynomials whose
cone Jacobian `TauCeti.jacobiMatrixAt p L.rep` is surjective at every point `L` of the zero locus
`X = TauCeti.complexProjectiveZeroLocus p ⊆ ℂℙⁿ` (by
`TauCeti.mulVec_surjective_jacobiMatrixAt_iff_of_mk_eq_mk` this does not depend on the
representative). Then `X`, with the topology it inherits from projective space, is a complex
analytic submanifold of dimension `n - |ι|`: it carries the atlas
`TauCeti.complexProjectiveZeroLocusChartedSpace`, modelled on `Fin (n - Fintype.card ι) → ℂ`,
which is analytic, and its inclusion into `ℂℙⁿ` is an analytic embedding and an immersion whose
complement is the space `ι → ℂ` of values of the equations.

The atlas is built from ambient slice charts. On the standard affine open `U_i`, where the `i`-th
homogeneous coordinate is nonzero, `X` is cut out by the chart equations
`g_i z = (eval z (dehomogenize i (p k)))_k`, whose derivative is surjective at the points of `X`
because it is the cone Jacobian with one column deleted
(`TauCeti.surjective_fderiv_eval_dehomogenize_affineChart_iff`). Near such a point `L`, the
complemented-kernel implicit function theorem gives the coordinates `z ↦ (g_i z, P (z - z_L))` of
`Fin n → ℂ`, where `P` projects onto the kernel `K` of the derivative of `g_i` at `z_L`, the
chart coordinates of `L`; restricted to the neighbourhood where their derivative stays invertible
they have analytic inverse. Reading `K` in `Fin (n - |ι|) → ℂ` and putting the equations last
gives `TauCeti.complexProjectiveZeroLocusSliceChart`, an analytic chart of `ℂℙⁿ` around `L`
whose second component is `g_i` (`TauCeti.complexProjectiveZeroLocusSliceChart_apply_snd`), so
that it flattens `X` onto the slice where that component vanishes
(`TauCeti.isSliceChart_complexProjectiveZeroLocusSliceChart`). The atlas of `X` is the one these
charts induce through `TauCeti.linearSliceChartedSpace`, using at each point the standard chart
`i` that `chartAt` uses for projective space. The ambient chart is built as in
`HasStrictFDerivAt.exists_isSliceChart_preimage_zero`, which flattens a regular zero set in a
normed space, here composed with the affine chart and read in product coordinates.

## Main declarations

* `TauCeti.card_le_of_surjective_jacobiMatrixAt`: surjectivity of the cone Jacobian at a point of
  the zero locus forces at most `n` equations.
* `TauCeti.complexProjectiveZeroLocusSliceChart`: the ambient analytic chart of `ℂℙⁿ` flattening
  the zero locus near a point where the cone Jacobian is surjective.
* `TauCeti.isSliceChart_complexProjectiveZeroLocusSliceChart`,
  `TauCeti.contMDiffOn_complexProjectiveZeroLocusSliceChart` and
  `TauCeti.contMDiffOn_complexProjectiveZeroLocusSliceChart_symm`: it is an analytic slice chart.
* `TauCeti.complexProjectiveZeroLocusChartedSpace`: the induced atlas on the zero locus, modelled
  on `Fin (n - Fintype.card ι) → ℂ`.
* `TauCeti.isManifold_complexProjectiveZeroLocus`: the zero locus is an analytic manifold.
* `TauCeti.isImmersionOfComplement_subtypeVal_complexProjectiveZeroLocus` and
  `TauCeti.isSmoothEmbedding_subtypeVal_complexProjectiveZeroLocus`: its inclusion into `ℂℙⁿ` is
  an analytic immersion with complement `ι → ℂ` and an analytic embedding.

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
  exact (contDiff_eqns p i (r := 1)).contDiffAt.hasStrictFDerivAt one_ne_zero

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

variable (hp : ∀ k, (p k).IsHomogeneous (d k))
  (hrank : ∀ L ∈ complexProjectiveZeroLocus p, Function.Surjective (jacobiMatrixAt p L.rep).mulVec)

/-- **The complex manifold structure of a smooth projective zero locus.** If the cone Jacobian of
a homogeneous family `p` is surjective at every point of its zero locus, the zero locus, with the
topology induced from `ℂℙⁿ`, carries the atlas induced by the slice charts
`TauCeti.complexProjectiveZeroLocusSliceChart`, modelled on `Fin (n - Fintype.card ι) → ℂ`. At a
point `L` the chart is taken in the standard affine chart that `chartAt` uses for projective space
at `L` (`TauCeti.complexProjectiveZeroLocusChartedSpace_chartAt_apply`). -/
@[instance_reducible]
noncomputable def complexProjectiveZeroLocusChartedSpace :
    ChartedSpace (Fin (n - Fintype.card ι) → ℂ) (complexProjectiveZeroLocus p) :=
  linearSliceChartedSpace
    (fun z ↦ complexProjectiveZeroLocusSliceChart hp z.2
      (exists_mem_affineOpen (z : ℙ ℂ (Fin (n + 1) → ℂ))).choose_spec (hrank z z.2))
    (fun z ↦ isSliceChart_complexProjectiveZeroLocusSliceChart hp z.2 _ (hrank z z.2))
    (fun z ↦ mem_complexProjectiveZeroLocusSliceChart_source hp z.2 _ (hrank z z.2))

/-- The chart of the zero locus at `z` reads the first coordinate of the slice chart at `z`. -/
theorem complexProjectiveZeroLocusChartedSpace_chartAt_apply (z w : complexProjectiveZeroLocus p) :
    @chartAt _ _ _ _ (complexProjectiveZeroLocusChartedSpace hp hrank) z w =
      (complexProjectiveZeroLocusSliceChart hp z.2
        (exists_mem_affineOpen (z : ℙ ℂ (Fin (n + 1) → ℂ))).choose_spec (hrank z z.2) w).1 := by
  rw [complexProjectiveZeroLocusChartedSpace, linearSliceChartedSpace_chartAt,
    linearSliceChart_apply]

/-- The chart of the zero locus at `z` is defined on the part of the zero locus in the source of
the slice chart at `z`. -/
theorem complexProjectiveZeroLocusChartedSpace_chartAt_source (z : complexProjectiveZeroLocus p) :
    (@chartAt _ _ _ _ (complexProjectiveZeroLocusChartedSpace hp hrank) z).source =
      Subtype.val ⁻¹' (complexProjectiveZeroLocusSliceChart hp z.2
        (exists_mem_affineOpen (z : ℙ ℂ (Fin (n + 1) → ℂ))).choose_spec (hrank z z.2)).source := by
  rw [complexProjectiveZeroLocusChartedSpace, linearSliceChartedSpace_chartAt,
    linearSliceChart_source]

/-- **A smooth projective zero locus is a complex manifold.** With the atlas
`TauCeti.complexProjectiveZeroLocusChartedSpace`, the zero locus is an analytic manifold of
dimension `n - |ι|`; it is `C^r` for every `r`. -/
theorem isManifold_complexProjectiveZeroLocus (r : ℕ∞ω) :
    letI := complexProjectiveZeroLocusChartedSpace hp hrank
    IsManifold 𝓘(ℂ, Fin (n - Fintype.card ι) → ℂ) r (complexProjectiveZeroLocus p) :=
  isManifold_linearSliceChartedSpace _ _
    (fun z _ hw ↦ (contMDiffOn_complexProjectiveZeroLocusSliceChart hp z.2 _ (hrank z z.2) r
      ).contMDiffAt ((OpenPartialHomeomorph.open_source _).mem_nhds hw))
    (fun z _ hv ↦ (contMDiffOn_complexProjectiveZeroLocusSliceChart_symm hp z.2 _ (hrank z z.2) r
      ).contMDiffAt ((OpenPartialHomeomorph.open_target _).mem_nhds hv)) _

/-- **The inclusion of a smooth projective zero locus is an immersion with normal model `ι → ℂ`.**
For the atlas `TauCeti.complexProjectiveZeroLocusChartedSpace`, the inclusion into `ℂℙⁿ` is a
`C^r` immersion, for every `r`, whose complement is the space `ι → ℂ` of values of the
equations. -/
theorem isImmersionOfComplement_subtypeVal_complexProjectiveZeroLocus (r : ℕ∞ω) :
    letI := complexProjectiveZeroLocusChartedSpace hp hrank
    Manifold.IsImmersionOfComplement (ι → ℂ) 𝓘(ℂ, Fin (n - Fintype.card ι) → ℂ)
      𝓘(ℂ, Fin n → ℂ) r (Subtype.val : complexProjectiveZeroLocus p → ℙ ℂ (Fin (n + 1) → ℂ)) :=
  isImmersionOfComplement_subtypeVal_linearSliceChartedSpace _ _
    (fun z ↦ modelEquiv (card_le_of_surjective_jacobiMatrixAt hp z.2 (hrank z z.2)))
    (fun z ↦ contMDiffOn_complexProjectiveZeroLocusSliceChart hp z.2 _ (hrank z z.2) r)
    (fun z ↦ contMDiffOn_complexProjectiveZeroLocusSliceChart_symm hp z.2 _ (hrank z z.2) r) _

/-- **A smooth projective zero locus is an embedded complex submanifold.** For the atlas
`TauCeti.complexProjectiveZeroLocusChartedSpace`, the inclusion into `ℂℙⁿ` is a `C^r` embedding
for every `r`. -/
theorem isSmoothEmbedding_subtypeVal_complexProjectiveZeroLocus (r : ℕ∞ω) :
    letI := complexProjectiveZeroLocusChartedSpace hp hrank
    Manifold.IsSmoothEmbedding 𝓘(ℂ, Fin (n - Fintype.card ι) → ℂ) 𝓘(ℂ, Fin n → ℂ) r
      (Subtype.val : complexProjectiveZeroLocus p → ℙ ℂ (Fin (n + 1) → ℂ)) :=
  isSmoothEmbedding_subtypeVal_linearSliceChartedSpace _ _
    (fun z ↦ modelEquiv (card_le_of_surjective_jacobiMatrixAt hp z.2 (hrank z z.2)))
    (fun z ↦ contMDiffOn_complexProjectiveZeroLocusSliceChart hp z.2 _ (hrank z z.2) r)
    (fun z ↦ contMDiffOn_complexProjectiveZeroLocusSliceChart_symm hp z.2 _ (hrank z z.2) r) _

end Submanifold

end TauCeti
