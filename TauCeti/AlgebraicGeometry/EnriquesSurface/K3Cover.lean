/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MvPolynomial.Jacobian
public import TauCeti.Geometry.Manifold.Projectivization.ZeroLocus
import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace
import TauCeti.Geometry.Manifold.Immersion.ModelChange
import TauCeti.Geometry.Manifold.ModelTransport.Diffeomorph
import TauCeti.LinearAlgebra.Vandermonde

/-!
# The K3 cover of an Enriques surface

In `ℂℙ⁵` with homogeneous coordinates `z₀, …, z₅`, consider the three diagonal quadrics
`Q_j = ∑ᵢ tᵢ ^ j zᵢ²`, for `j = 0, 1, 2`, with the pairwise distinct weights `tᵢ = i + 1`. Their
common zero locus `X` is a smooth complete intersection of three quadrics, a K3 surface. The sign
change `σ`, which negates `z₀, z₁, z₂` and fixes `z₃, z₄, z₅`, preserves each `Q_j` and acts on
`X` without fixed points, so the quotient `X / σ` is an Enriques surface and `X` is its K3 cover.

This file proves the two elementary polynomial facts behind this construction.

* *Smoothness.* At every nonzero common zero `v` of the quadrics the cone Jacobian, the `3 × 6`
  matrix with entries `2 tᵢ ^ j vᵢ`, is surjective. A linear relation between its rows is a
  polynomial `g` of degree at most two with `g (tᵢ) vᵢ = 0` for all `i`. A nonzero common zero has
  at least four nonzero coordinates, so `g` has more roots than its degree and vanishes.
* *Freeness.* A line fixed by `σ` lies in one of its two eigenspaces, so all but three of its
  homogeneous coordinates vanish. A common zero with at most three nonzero coordinates is zero.

Both reduce to the same statement about the Vandermonde matrix of the weights: the squares
`wᵢ = vᵢ²` of a common zero satisfy `∑ᵢ tᵢ ^ j wᵢ = 0` for `j < 3`, so if at most three of them
are nonzero, they all vanish (`TauCeti.exists_lt_card_sum_mul_pow_ne_zero`).

The zero locus is the native projective zero locus `TauCeti.complexProjectiveZeroLocus` of the
quadrics, so the Jacobian criterion makes it a complex submanifold of `ℂℙ⁵` of dimension
`5 - 3 = 2`, through the slice-chart atlas `TauCeti.complexProjectiveZeroLocusChartedSpace`. Its
model `Fin (5 - 3) → ℂ` is read in `Fin 2 → ℂ` (`Homeomorph.chartedSpaceComp`), as for the
analytic structure of a complex elliptic curve, and the embedding of the zero locus into `ℂℙ⁵` is
transported along this linear change of model (`Diffeomorph.isSmoothEmbedding_chartedSpaceComp`).

## Main definitions

* `TauCeti.enriquesQuadric j`: the quadric `∑ᵢ (i + 1) ^ j zᵢ²` in six variables.
* `TauCeti.enriquesZeroSet`: the common zero locus of the three quadrics in `ℂℙ⁵`.
* `TauCeti.enriquesInvolutionLinear`: the linear sign change negating the first three
  coordinates.
* `TauCeti.enriquesProjectiveInvolution`: the induced involution of `ℂℙ⁵`.
* `TauCeti.enriquesZeroSetInvolution`: its restriction to the zero locus, the Enriques
  involution of the K3 cover.

## Main results

* `TauCeti.mulVec_surjective_jacobiMatrixAt_enriquesQuadric` and
  `TauCeti.enriquesQuadricJacobian_surjective`: the cone Jacobian of the quadrics is surjective
  at every nonzero common zero, so the zero locus is smooth of codimension three.
* `TauCeti.enriquesProjectiveInvolution_involutive` and
  `TauCeti.enriquesProjectiveInvolution_mem_enriquesZeroSet_iff`: the projective sign change is
  an involution preserving the zero locus.
* `TauCeti.enriquesProjectiveInvolution_no_fixed_point` and
  `TauCeti.enriquesZeroSetInvolution_ne_self`: it has no fixed point on the zero locus.
* `TauCeti.enriquesZeroSet_nonempty`: the zero locus is nonempty.
* `TauCeti.instChartedSpaceEnriquesZeroSet` and `TauCeti.instIsManifoldEnriquesZeroSet`: the zero
  locus is a complex surface, with the analytic atlas induced by the slice charts of `ℂℙ⁵`.
* `TauCeti.isSmoothEmbedding_subtypeVal_enriquesZeroSet`: this complex surface is
  holomorphically embedded in `ℂℙ⁵`.

## References

* I. Dolgachev, *A brief introduction to Enriques surfaces*, arXiv:1412.7744, §3, for the K3
  cover of a general Enriques surface as a complete intersection of three diagonal quadrics in
  `ℙ⁵` with a fixed-point-free sign involution.
* W. Barth, K. Hulek, C. Peters and A. Van de Ven, *Compact Complex Surfaces*, 2nd ed.,
  Springer, 2004, Chapter VIII, §18, for the same construction.
-/

public section

open MvPolynomial Finset
open scoped LinearAlgebra.Projectivization Matrix Manifold ContDiff

namespace TauCeti

/-- The quadric `∑ᵢ (i + 1) ^ j zᵢ²` in the six homogeneous coordinates of `ℂℙ⁵`. For
`j = 0, 1, 2` these are the three diagonal quadrics, with the pairwise distinct weights
`1, …, 6`, whose common zero locus is the K3 cover of an Enriques surface. -/
noncomputable def enriquesQuadric (j : Fin 3) : MvPolynomial (Fin 6) ℂ :=
  ∑ i : Fin 6, ((i.val + 1 : ℂ) ^ j.val) • X i ^ 2

/-- Evaluation of an Enriques quadric. -/
theorem eval_enriquesQuadric (v : Fin 6 → ℂ) (j : Fin 3) :
    eval v (enriquesQuadric j) = ∑ i : Fin 6, ((i.val + 1 : ℂ) ^ j.val) * v i ^ 2 := by
  simp [enriquesQuadric, smul_eq_C_mul]

/-- Each Enriques quadric is homogeneous of degree two. -/
theorem isHomogeneous_enriquesQuadric (j : Fin 3) : (enriquesQuadric j).IsHomogeneous 2 :=
  IsHomogeneous.sum _ _ _ fun i _ ↦ by
    rw [smul_eq_C_mul]
    exact isHomogeneous_C_mul_X_pow _ _ _

/-- The partial derivatives of an Enriques quadric at a point: `∂Q_j/∂zᵢ = 2 (i + 1) ^ j zᵢ`. -/
theorem jacobiMatrixAt_enriquesQuadric_apply (v : Fin 6 → ℂ) (j : Fin 3) (i : Fin 6) :
    jacobiMatrixAt enriquesQuadric v j i = 2 * (i.val + 1 : ℂ) ^ j.val * v i := by
  simp [enriquesQuadric, smul_eq_C_mul, pderiv_X, Pi.single_apply]
  ring

/-- The weights `i + 1` of the Enriques quadrics are pairwise distinct. -/
private theorem injective_enriquesWeight : Function.Injective fun i : Fin 6 ↦ (i.val + 1 : ℂ) :=
  fun a b h ↦ Fin.ext (by exact_mod_cast add_right_cancel h)

/-- **Few nonzero coordinates.** A common zero of the three Enriques quadrics whose coordinates
vanish outside a set of at most three indices is zero: the squares of its coordinates are then
killed by the invertible Vandermonde matrix of the weights of those indices. -/
theorem eq_zero_of_eval_enriquesQuadric_of_card_le {v : Fin 6 → ℂ}
    (hv : ∀ j, eval v (enriquesQuadric j) = 0) {s : Finset (Fin 6)} (hs : #s ≤ 3)
    (hvs : ∀ i ∉ s, v i = 0) : v = 0 := by
  by_contra h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  have his : i ∈ s := by by_contra his; exact hi (hvs i his)
  obtain ⟨k, hk, hne⟩ := exists_lt_card_sum_mul_pow_ne_zero (s := s) (w := fun i ↦ v i ^ 2)
    (injective_enriquesWeight.injOn) ⟨i, his, pow_ne_zero 2 hi⟩
  refine hne ?_
  have hsum := hv ⟨k, hk.trans_le hs⟩
  rw [eval_enriquesQuadric, ← Finset.sum_subset (Finset.subset_univ s)
    fun i _ hi ↦ by simp [hvs i hi]] at hsum
  simpa only [mul_comm] using hsum

/-- At a nonzero common zero of the Enriques quadrics, at least four coordinates are nonzero. -/
theorem lt_card_filter_ne_zero_of_eval_enriquesQuadric {v : Fin 6 → ℂ} (hv0 : v ≠ 0)
    (hv : ∀ j, eval v (enriquesQuadric j) = 0) : 3 < #{i | v i ≠ 0} := by
  by_contra! h
  exact hv0 (eq_zero_of_eval_enriquesQuadric_of_card_le hv h fun i hi ↦ by simpa using hi)

/-- **The Enriques K3 cover is smooth.** At every nonzero common zero of the three Enriques
quadrics, their cone Jacobian is surjective. -/
theorem mulVec_surjective_jacobiMatrixAt_enriquesQuadric {v : Fin 6 → ℂ} (hv0 : v ≠ 0)
    (hv : ∀ j, eval v (enriquesQuadric j) = 0) :
    (jacobiMatrixAt enriquesQuadric v).mulVec.Surjective := by
  refine LinearIndependent.mulVec_surjective (Matrix.vecMul_injective_iff.mp ?_)
  rw [← Matrix.coe_vecMulLinear, ← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  -- Three distinct indices at which `v` does not vanish.
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq
    (lt_card_filter_ne_zero_of_eval_enriquesQuadric hv0 hv).le
  let e := s.equivFin
  refine Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero
    (f := fun k : Fin 3 ↦ ((e.symm (Fin.cast hcard.symm k) : Fin 6).val + 1 : ℂ))
    (fun a b hab ↦ ?_) fun k ↦ ?_
  · simpa using e.symm.injective (Subtype.ext (injective_enriquesWeight hab))
  · set i : Fin 6 := (e.symm (Fin.cast hcard.symm k) : Fin 6)
    have hi : v i ≠ 0 := by simpa using hs (e.symm (Fin.cast hcard.symm k)).2
    have h := congrFun hc i
    simp only [Matrix.vecMulLinear_apply, Matrix.vecMul, dotProduct,
      jacobiMatrixAt_enriquesQuadric_apply, Pi.zero_apply] at h
    have h' : (2 * v i) * ∑ j : Fin 3, c j * ((i.val + 1 : ℂ)) ^ j.val = 0 := by
      rw [Finset.mul_sum, ← h]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    exact (mul_eq_zero.mp h').resolve_left (mul_ne_zero two_ne_zero hi)

/-- **The Enriques K3 cover is smooth**, for the Fréchet derivative of the three quadrics: at
every nonzero common zero `v`, the derivative of `w ↦ (Q₀ w, Q₁ w, Q₂ w)` is surjective. The
hypothesis that `v` is a common zero is needed: at the basis vector `e₀` the derivative has rank
one. -/
theorem enriquesQuadricJacobian_surjective (v : Fin 6 → ℂ) (hv0 : v ≠ 0)
    (hv : ∀ j, eval v (enriquesQuadric j) = 0) :
    Function.Surjective
      (fderiv ℂ (fun w : Fin 6 → ℂ ↦ fun j : Fin 3 ↦ eval w (enriquesQuadric j)) v) :=
  (surjective_fderiv_eval_family_iff _ v).mpr
    (mulVec_surjective_jacobiMatrixAt_enriquesQuadric hv0 hv)

/-- The common zero locus in `ℂℙ⁵` of the three Enriques quadrics: the K3 cover of an Enriques
surface. It is the native projective zero locus of the quadrics. -/
noncomputable def enriquesZeroSet : Set (ℙ ℂ (Fin 6 → ℂ)) :=
  complexProjectiveZeroLocus enriquesQuadric

/-- The class of a nonzero vector lies on the Enriques K3 cover exactly when the vector is a
common zero of the three quadrics. -/
@[simp]
theorem mk_mem_enriquesZeroSet_iff (v : Fin 6 → ℂ) (hv : v ≠ 0) :
    Projectivization.mk ℂ v hv ∈ enriquesZeroSet ↔ ∀ j, eval v (enriquesQuadric j) = 0 :=
  complexProjectiveZeroLocus_mk_iff isHomogeneous_enriquesQuadric v hv

/-- Membership in the Enriques K3 cover can be tested on the chosen representative. -/
theorem mem_enriquesZeroSet_iff (p : ℙ ℂ (Fin 6 → ℂ)) :
    p ∈ enriquesZeroSet ↔ ∀ j, eval p.rep (enriquesQuadric j) = 0 :=
  mem_complexProjectiveZeroLocus_iff_eval_rep isHomogeneous_enriquesQuadric p

/-- The cone Jacobian of the Enriques quadrics is surjective at every point of their projective
zero locus. This is the hypothesis of `TauCeti.complexProjectiveZeroLocusChartedSpace`, which
makes the Enriques K3 cover a complex surface embedded in `ℂℙ⁵`. -/
theorem mulVec_surjective_jacobiMatrixAt_rep_of_mem_enriquesZeroSet {p : ℙ ℂ (Fin 6 → ℂ)}
    (hp : p ∈ enriquesZeroSet) : (jacobiMatrixAt enriquesQuadric p.rep).mulVec.Surjective :=
  mulVec_surjective_jacobiMatrixAt_enriquesQuadric p.rep_ne_zero
    ((mem_enriquesZeroSet_iff p).mp hp)

/-- The point `(i, √3, i√3, 1, 0, 0)` is a common zero of the Enriques quadrics: the squares of
its coordinates are `(-1, 3, -3, 1, 0, 0)`. -/
private theorem eval_enriquesQuadric_witness (j : Fin 3) :
    eval ![Complex.I, (√3 : ℝ), Complex.I * (√3 : ℝ), 1, 0, 0] (enriquesQuadric j) = 0 := by
  have h3 : ((√3 : ℝ) : ℂ) ^ 2 = 3 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [eval_enriquesQuadric]
  fin_cases j <;>
    simp [Fin.sum_univ_six, mul_pow, h3] <;> norm_num

/-- The Enriques K3 cover is nonempty: it contains the line of `(i, √3, i√3, 1, 0, 0)`. -/
theorem enriquesZeroSet_nonempty : enriquesZeroSet.Nonempty :=
  ⟨Projectivization.mk ℂ ![Complex.I, (√3 : ℝ), Complex.I * (√3 : ℝ), 1, 0, 0]
    (Function.ne_iff.mpr ⟨3, by simp⟩),
    (mk_mem_enriquesZeroSet_iff _ _).mpr eval_enriquesQuadric_witness⟩

/-- The linear sign change of `ℂ⁶` negating the first three coordinates and fixing the last
three. -/
noncomputable def enriquesInvolutionLinear : (Fin 6 → ℂ) ≃ₗ[ℂ] (Fin 6 → ℂ) :=
  LinearEquiv.piCongrRight fun i ↦
    if i.val < 3 then LinearEquiv.neg ℂ else LinearEquiv.refl ℂ ℂ

/-- The sign change negates the coordinates of index `0, 1, 2` and fixes the others. -/
@[simp]
theorem enriquesInvolutionLinear_apply (v : Fin 6 → ℂ) (i : Fin 6) :
    enriquesInvolutionLinear v i = if i.val < 3 then -v i else v i := by
  simp only [enriquesInvolutionLinear, LinearEquiv.piCongrRight_apply]
  split_ifs <;> simp

/-- The linear sign change is an involution. -/
@[simp]
theorem enriquesInvolutionLinear_apply_apply (v : Fin 6 → ℂ) :
    enriquesInvolutionLinear (enriquesInvolutionLinear v) = v := by
  ext i
  simp only [enriquesInvolutionLinear_apply]
  split_ifs <;> simp

/-- The linear sign change is its own inverse. -/
@[simp]
theorem enriquesInvolutionLinear_symm : enriquesInvolutionLinear.symm = enriquesInvolutionLinear :=
  LinearEquiv.ext fun v ↦ by
    rw [LinearEquiv.symm_apply_eq, enriquesInvolutionLinear_apply_apply]

/-- The sign change preserves each Enriques quadric. -/
@[simp]
theorem eval_enriquesInvolutionLinear_enriquesQuadric (v : Fin 6 → ℂ) (j : Fin 3) :
    eval (enriquesInvolutionLinear v) (enriquesQuadric j) = eval v (enriquesQuadric j) := by
  simp only [eval_enriquesQuadric, enriquesInvolutionLinear_apply]
  exact Finset.sum_congr rfl fun i _ ↦ by split_ifs <;> simp

/-- The involution of `ℂℙ⁵` induced by the sign change of the first three homogeneous
coordinates. -/
noncomputable def enriquesProjectiveInvolution :
    ℙ ℂ (Fin 6 → ℂ) → ℙ ℂ (Fin 6 → ℂ) :=
  Projectivization.map enriquesInvolutionLinear.toLinearMap enriquesInvolutionLinear.injective

/-- The projective sign change sends the line of `v` to the line of its sign change. -/
@[simp]
theorem enriquesProjectiveInvolution_mk (v : Fin 6 → ℂ) (hv : v ≠ 0) :
    enriquesProjectiveInvolution (Projectivization.mk ℂ v hv) =
      Projectivization.mk ℂ (enriquesInvolutionLinear v)
        ((map_ne_zero_iff _ enriquesInvolutionLinear.injective).mpr hv) :=
  Projectivization.map_mk _ _ v hv

/-- The projective sign change is an involution. -/
@[simp]
theorem enriquesProjectiveInvolution_enriquesProjectiveInvolution (p : ℙ ℂ (Fin 6 → ℂ)) :
    enriquesProjectiveInvolution (enriquesProjectiveInvolution p) = p := by
  induction p using Projectivization.ind with
  | h v hv => simp

/-- The projective sign change is an involution. -/
theorem enriquesProjectiveInvolution_involutive :
    Function.Involutive enriquesProjectiveInvolution :=
  enriquesProjectiveInvolution_enriquesProjectiveInvolution

/-- The projective sign change preserves the Enriques K3 cover. -/
@[simp]
theorem enriquesProjectiveInvolution_mem_enriquesZeroSet_iff (p : ℙ ℂ (Fin 6 → ℂ)) :
    enriquesProjectiveInvolution p ∈ enriquesZeroSet ↔ p ∈ enriquesZeroSet := by
  induction p using Projectivization.ind with
  | h v hv => simp

/-- The projective sign change maps the Enriques K3 cover to itself. -/
theorem mapsTo_enriquesProjectiveInvolution :
    Set.MapsTo enriquesProjectiveInvolution enriquesZeroSet enriquesZeroSet :=
  fun p hp ↦ (enriquesProjectiveInvolution_mem_enriquesZeroSet_iff p).mpr hp

/-- **The Enriques involution is free.** The projective sign change has no fixed point on the
Enriques K3 cover. A fixed line lies in one of the two eigenspaces of the sign change, so its
coordinates vanish outside three indices, and the Vandermonde matrix of their weights forces it
to be zero. The hypothesis is needed: the line of the basis vector `e₀` is fixed. -/
theorem enriquesProjectiveInvolution_no_fixed_point (p : ℙ ℂ (Fin 6 → ℂ))
    (hp : p ∈ enriquesZeroSet) : enriquesProjectiveInvolution p ≠ p := by
  induction p using Projectivization.ind with
  | h v hv =>
  rw [mk_mem_enriquesZeroSet_iff] at hp
  rw [enriquesProjectiveInvolution_mk, Ne, Projectivization.mk_eq_mk_iff']
  rintro ⟨a, ha⟩
  have hai (i : Fin 6) : a * v i = if i.val < 3 then -v i else v i := by
    simpa using congrFun ha i
  by_cases h1 : a = 1
  · -- The line lies in the `+1` eigenspace: the first three coordinates vanish.
    refine hv (eq_zero_of_eval_enriquesQuadric_of_card_le hp (s := {i | 3 ≤ i.val})
      (by decide) fun i hi ↦ ?_)
    have := hai i
    simp only [h1, one_mul, mem_filter, mem_univ, true_and, not_le] at this hi
    simp only [hi, ite_true] at this
    linear_combination this / 2
  · -- The line lies in the `-1` eigenspace: the last three coordinates vanish.
    refine hv (eq_zero_of_eval_enriquesQuadric_of_card_le hp (s := {i | i.val < 3})
      (by decide) fun i hi ↦ ?_)
    have := hai i
    simp only [mem_filter, mem_univ, true_and] at hi
    simp only [hi, ite_false] at this
    exact (mul_eq_zero.mp (by linear_combination this : (a - 1) * v i = 0)).resolve_left
      (sub_ne_zero.mpr h1)

/-- The Enriques involution: the projective sign change, restricted to the Enriques K3 cover. -/
noncomputable def enriquesZeroSetInvolution : enriquesZeroSet → enriquesZeroSet :=
  mapsTo_enriquesProjectiveInvolution.restrict

/-- The Enriques involution acts on the K3 cover as the projective sign change of `ℂℙ⁵`. -/
@[simp]
theorem coe_enriquesZeroSetInvolution (p : enriquesZeroSet) :
    (enriquesZeroSetInvolution p : ℙ ℂ (Fin 6 → ℂ)) = enriquesProjectiveInvolution p :=
  (rfl)

/-- The Enriques involution of the K3 cover is an involution. -/
@[simp]
theorem enriquesZeroSetInvolution_enriquesZeroSetInvolution (p : enriquesZeroSet) :
    enriquesZeroSetInvolution (enriquesZeroSetInvolution p) = p :=
  Subtype.ext (by simp)

/-- The Enriques involution of the K3 cover is an involution. -/
theorem enriquesZeroSetInvolution_involutive : Function.Involutive enriquesZeroSetInvolution :=
  enriquesZeroSetInvolution_enriquesZeroSetInvolution

/-- **The Enriques involution of the K3 cover is free**: it has no fixed point. -/
theorem enriquesZeroSetInvolution_ne_self (p : enriquesZeroSet) : enriquesZeroSetInvolution p ≠ p :=
  fun h ↦ enriquesProjectiveInvolution_no_fixed_point p p.2 (congrArg Subtype.val h)

/-! ### The complex surface structure -/

/-- The atlas of the Enriques K3 cover induced by the analytic slice charts of `ℂℙ⁵`, modelled
on `Fin (5 - 3) → ℂ`. -/
@[instance_reducible]
private noncomputable def enriquesZeroSetSliceChartedSpace :
    ChartedSpace (Fin (5 - Fintype.card (Fin 3)) → ℂ) enriquesZeroSet :=
  complexProjectiveZeroLocusChartedSpace (s := enriquesZeroSet) isHomogeneous_enriquesQuadric
    isOpen_univ (Set.inter_univ _).symm fun _ ↦
      mulVec_surjective_jacobiMatrixAt_rep_of_mem_enriquesZeroSet

/-- The Enriques K3 cover is a `C^r` manifold for its slice-chart atlas. -/
private theorem isManifold_enriquesZeroSetSlice (r : ℕ∞ω) :
    letI := enriquesZeroSetSliceChartedSpace
    IsManifold 𝓘(ℂ, Fin (5 - Fintype.card (Fin 3)) → ℂ) r enriquesZeroSet :=
  isManifold_complexProjectiveZeroLocus (s := enriquesZeroSet) isHomogeneous_enriquesQuadric
    isOpen_univ (Set.inter_univ _).symm
    (fun _ ↦ mulVec_surjective_jacobiMatrixAt_rep_of_mem_enriquesZeroSet) r

/-- The slice-chart model `Fin (5 - 3) → ℂ`, read in `Fin 2 → ℂ`. -/
private noncomputable def enriquesModelEquiv :
    (Fin (5 - Fintype.card (Fin 3)) → ℂ) ≃L[ℂ] (Fin 2 → ℂ) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp)

/-- **The complex charts of the Enriques K3 cover.** The chart at a point reads the tangential
coordinates of the analytic slice chart of `ℂℙ⁵` flattening the zero locus near that point, in
`Fin 2 → ℂ` through `enriquesModelEquiv`. -/
@[no_expose]
noncomputable instance instChartedSpaceEnriquesZeroSet : ChartedSpace (Fin 2 → ℂ) enriquesZeroSet :=
  letI := enriquesZeroSetSliceChartedSpace
  (enriquesModelEquiv.toContDiffDiffeomorph ω).toHomeomorph.chartedSpaceComp enriquesZeroSet

/-- **The Enriques K3 cover is a complex surface.** Its atlas is analytic, and `C^r` for every
`r`. -/
instance instIsManifoldEnriquesZeroSet (r : ℕ∞ω) :
    IsManifold 𝓘(ℂ, Fin 2 → ℂ) r enriquesZeroSet := by
  let := enriquesZeroSetSliceChartedSpace
  have := isManifold_enriquesZeroSetSlice ω
  have : IsManifold 𝓘(ℂ, Fin 2 → ℂ) ω enriquesZeroSet :=
    (enriquesModelEquiv.toContDiffDiffeomorph ω).isManifold_chartedSpaceComp enriquesZeroSet
  exact IsManifold.of_le le_top

/-- **The Enriques K3 cover is holomorphically embedded in `ℂℙ⁵`.** The inclusion of the zero
locus is a `C^r` embedding for every `r`; in particular it is holomorphic. -/
theorem isSmoothEmbedding_subtypeVal_enriquesZeroSet (r : ℕ∞ω) :
    Manifold.IsSmoothEmbedding 𝓘(ℂ, Fin 2 → ℂ) 𝓘(ℂ, Fin 5 → ℂ) r
      (Subtype.val : enriquesZeroSet → ℙ ℂ (Fin 6 → ℂ)) := by
  let := enriquesZeroSetSliceChartedSpace
  have := isManifold_enriquesZeroSetSlice ω
  -- Read the slice-chart embedding in the charts on `Fin 2 → ℂ`.
  exact (enriquesModelEquiv.toContDiffDiffeomorph ω).isSmoothEmbedding_chartedSpaceComp
    enriquesModelEquiv.symm
    (by simp only [modelWithCornersSelf_coe, Set.range_id]
        exact Set.image_univ_of_surjective enriquesModelEquiv.symm.surjective) le_top
    (isSmoothEmbedding_subtypeVal_complexProjectiveZeroLocus (s := enriquesZeroSet)
      isHomogeneous_enriquesQuadric isOpen_univ (Set.inter_univ _).symm
      (fun _ ↦ mulVec_surjective_jacobiMatrixAt_rep_of_mem_enriquesZeroSet) r)

end TauCeti
