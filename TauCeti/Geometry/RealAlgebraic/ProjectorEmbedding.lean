/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.Analysis.Calculus.ContDiff.FinInsertNth
public import TauCeti.Geometry.Manifold.Instances.Projectivization
public import TauCeti.Geometry.RealAlgebraic.Nash.Basic
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Function
public import TauCeti.LinearAlgebra.Projectivization.Projector
public import TauCeti.Topology.Algebra.Projectivization

/-!
# Real projective space as a compact real algebraic set of matrices

The projector map `Projectivization.projector : ℙ K (ι → K) → Matrix ι ι K` sends a line spanned
by `x` to the matrix `x xᵀ / (xᵀ x)`, and is a bijection onto the *projector locus*
`TauCeti.projectorLocus ι K` of symmetric idempotent matrices of trace one
(`Projectivization.range_projector`). Here we add its topological and semialgebraic properties.

The projector map is continuous for the quotient topology on projective space. Over `ℝ`,
projective space is compact and matrices form a Hausdorff space, so the projector map is a closed
embedding: it is a homeomorphism from real projective space onto the projector locus, which is
compact. The locus is cut out by polynomial equations in the matrix entries, hence is
semialgebraic. Together these exhibit real projective space as a compact real algebraic subset of
an affine space, which is the reduction used to transport triangulations of compact semialgebraic
sets to real projective spaces.

The standard affine charts of real projective space are compatible with this model, both
analytically and semialgebraically. Read in the affine chart at `i`, the projector map sends `z`
to the matrix with entries `w a * w b / (wᵀ w)`, where `w = Fin.insertNth i 1 z` and `wᵀ w ≥ 1`.
These entries are Nash functions of `z`, the map is analytic, and its graph is semialgebraic.
Conversely, the chart at `i` reads the coordinates of a line off its projector `A` as the ratios
`A (i.succAbove k) i / A i i` (`Projectivization.affineChart_eq_projector_div`). These ratios are
rational, so analytic and semialgebraic, on the image of the affine open `{x_i ≠ 0}`, where
`A i i > 0`. Being a left inverse, they make the differential of the projector map injective. So
the projector map is an analytic immersion and a homeomorphism onto the compact projector locus,
and its inverse is given in each chart by these rational maps.

## Main results

* `Projectivization.continuous_projector`: the projector map is continuous.
* `Projectivization.isClosedEmbedding_projector`: over `ℝ` the projector map is a closed
  embedding.
* `TauCeti.isClosed_projectorLocus` and `TauCeti.isCompact_projectorLocus`: the projector locus
  is closed, and compact over `ℝ`.
* `TauCeti.isSemialgebraic_projectorLocus`: the projector locus is semialgebraic in the matrix
  entries.
* `TauCeti.isNashAt_projector_affineChart_symm` and `TauCeti.contDiff_projector_affineChart_symm`:
  read in a standard affine chart, the entries of the projector are Nash functions, and the
  projector map is analytic.
* `Projectivization.contMDiff_projector`: the projector map is analytic on real projective space.
* `TauCeti.injective_fderiv_projector_affineChart_symm` and
  `Projectivization.injective_mfderiv_projector`: the projector map is an immersion.
* `TauCeti.isSemialgebraicMap_projector_affineChart_symm`,
  `TauCeti.isSemialgebraic_image_projector_affineOpen` and
  `TauCeti.isSemialgebraicOn_projector_affineChart`: the standard affine charts and their
  inverses, read in the projector model, are semialgebraic.

## References

S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di Pisa
(3) 18 (1964), 449–474, §3, p. 464.
-/

public section

open Matrix MvPolynomial Topology
open scoped ContDiff Manifold LinearAlgebra.Projectivization

namespace Projectivization

open TauCeti

variable {ι K : Type*} [Fintype ι] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [TopologicalSpace K] [IsTopologicalRing K] [ContinuousInv₀ K]

/-- The projector map is continuous for the quotient topology on projective space. -/
theorem continuous_projector : Continuous (projector : ℙ K (ι → K) → Matrix ι ι K) := by
  rw [continuous_iff]
  have hcomp : projector ∘ mk' K = fun x : {x : ι → K // x ≠ 0} ↦ rankOneProjector x.1 :=
    funext fun x ↦ by simp
  simp only [hcomp, rankOneProjector_def]
  exact ((continuous_subtype_val.dotProduct continuous_subtype_val).inv₀ fun x ↦
    dotProduct_self_eq_zero.not.mpr x.2).smul
    (continuous_subtype_val.matrix_vecMulVec continuous_subtype_val)

/-- Over `ℝ` the projector map is a closed embedding, hence a homeomorphism from real projective
space onto the projector locus `TauCeti.projectorLocus ι ℝ`. -/
theorem isClosedEmbedding_projector :
    IsClosedEmbedding (projector : ℙ ℝ (ι → ℝ) → Matrix ι ι ℝ) :=
  continuous_projector.isClosedEmbedding projector_injective

end Projectivization

namespace TauCeti

variable {ι K : Type*} [Fintype ι] [Field K]

/-- The projector locus is closed. -/
theorem isClosed_projectorLocus [TopologicalSpace K] [IsTopologicalRing K] [T2Space K] :
    IsClosed (projectorLocus ι K) := by
  have h : projectorLocus ι K = {A | Aᵀ = A} ∩ {A | A * A = A} ∩ {A | A.trace = 1} := by
    ext A
    simp [IsSymm, IsIdempotentElem, and_assoc]
  rw [h]
  exact ((isClosed_eq continuous_id.matrix_transpose continuous_id).inter
    (isClosed_eq (continuous_id.matrix_mul continuous_id) continuous_id)).inter
    (isClosed_eq continuous_id.matrix_trace continuous_const)

/-- The real projector locus is compact, being the image of compact real projective space. -/
theorem isCompact_projectorLocus : IsCompact (projectorLocus ι ℝ) :=
  Projectivization.range_projector (ι := ι) (K := ℝ) ▸
    isCompact_range Projectivization.continuous_projector

/-- The projector locus is semialgebraic: in the matrix entries `a (i, j)` it is cut out by the
polynomial equations expressing symmetry, idempotence and trace one. -/
theorem isSemialgebraic_projectorLocus [LinearOrder K] :
    IsSemialgebraic {a : ι × ι → K | Matrix.of (Function.curry a) ∈ projectorLocus ι K} := by
  have h : {a : ι × ι → K | Matrix.of (Function.curry a) ∈ projectorLocus ι K} =
      ((⋂ p : ι × ι, {a | eval a (X p.swap) = eval a (X p)}) ∩
        ⋂ p : ι × ι, {a | eval a (∑ k, X (p.1, k) * X (k, p.2)) = eval a (X p)}) ∩
        {a | eval a (∑ i, X (i, i)) = eval a 1} := by
    ext a
    simp [IsSymm, IsIdempotentElem, ← Matrix.ext_iff, Matrix.mul_apply, trace, Prod.forall,
      and_assoc]
  rw [h]
  exact ((IsSemialgebraic.iInter fun _ ↦ isSemialgebraic_eval_eq _ _).inter
    (IsSemialgebraic.iInter fun _ ↦ isSemialgebraic_eval_eq _ _)).inter
    (isSemialgebraic_eval_eq _ _)

/-! ### The standard affine charts -/

section AffineChart

open Projectivization

variable {n : ℕ}

/-- The homogeneous coordinates `Fin.insertNth i 1 z` of a point of the affine chart at `i` have
nonzero dot product with themselves. -/
private theorem insertNth_one_dotProduct_self_ne_zero {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (i : Fin (n + 1)) (z : Fin n → K) :
    Fin.insertNth (α := fun _ ↦ K) i 1 z ⬝ᵥ Fin.insertNth (α := fun _ ↦ K) i 1 z ≠ 0 :=
  dotProduct_self_eq_zero.not.mpr (Fin.insertNth_one_ne_zero i z)

/-- The entries of the projector, read in the standard affine chart at `i`, are Nash functions of
the affine coordinates `z`. With `w = Fin.insertNth i 1 z`, the `(a, b)` entry is the rational
function `w a * w b / (wᵀ w)`, whose denominator never vanishes. -/
theorem isNashAt_projector_affineChart_symm (i a b : Fin (n + 1)) (z : Fin n → ℝ) :
    IsNashAt (fun z ↦ projector ((affineChart i).symm z) a b) z := by
  have hw (l : Fin (n + 1)) :
      IsNashAt (fun z : Fin n → ℝ ↦ Fin.insertNth (α := fun _ ↦ ℝ) i 1 z l) z := by
    induction l using i.succAboveCases with
    | x => simpa using isNashAt_const 1
    | p k => simpa using isNashAt_apply k
  simp only [affineChart_symm_apply, projector_mk, rankOneProjector_apply]
  exact ((hw a).fun_mul (hw b)).fun_div (Finset.fun_isNashAt_sum _ fun k _ ↦ (hw k).fun_mul (hw k))
    (insertNth_one_dotProduct_self_ne_zero i z)

/-- The projector map read in the standard affine chart at `i`, with values in the matrix
coordinates `Fin (n + 1) × Fin (n + 1) → ℝ`, is `C^r` for every `r`; for `r = ω` it is
analytic. -/
theorem contDiff_projector_affineChart_symm (i : Fin (n + 1)) {r : ℕ∞ω} :
    ContDiff ℝ r fun (z : Fin n → ℝ) (q : Fin (n + 1) × Fin (n + 1)) ↦
      projector ((affineChart i).symm z) q.1 q.2 := by
  have hw (l : Fin (n + 1)) :
      ContDiff ℝ r fun z : Fin n → ℝ ↦ Fin.insertNth (α := fun _ ↦ ℝ) i 1 z l :=
    contDiff_pi.1 ((contDiff_const (c := (1 : ℝ))).finInsertNth (F := fun _ ↦ ℝ) i contDiff_id) l
  refine contDiff_pi.2 fun q ↦ ?_
  simp only [affineChart_symm_apply, projector_mk, rankOneProjector_apply]
  exact ((hw q.1).mul (hw q.2)).div (ContDiff.sum fun k _ ↦ (hw k).mul (hw k))
    (insertNth_one_dotProduct_self_ne_zero i)

/-- **The projector map is an immersion in the affine charts.** The derivative of the projector
map read in the standard affine chart at `i` is injective at every point. Indeed the map
`A ↦ (A (i.succAbove k) i / A i i)_k`, differentiable where `A i i ≠ 0`, is a left inverse
(`Projectivization.affineChart_eq_projector_div`). -/
theorem injective_fderiv_projector_affineChart_symm (i : Fin (n + 1)) (z : Fin n → ℝ) :
    Function.Injective (fderiv ℝ (fun (z : Fin n → ℝ) (q : Fin (n + 1) × Fin (n + 1)) ↦
      projector ((affineChart i).symm z) q.1 q.2) z) := by
  set F := fun (z : Fin n → ℝ) (q : Fin (n + 1) × Fin (n + 1)) ↦
    projector ((affineChart i).symm z) q.1 q.2
  set G := fun (A : Fin (n + 1) × Fin (n + 1) → ℝ) (k : Fin n) ↦ A (i.succAbove k, i) / A (i, i)
  have hGF : G ∘ F = id := funext fun z ↦
    (affineChart_eq_projector_div i _).symm.trans ((affineChart i).right_inv (by simp))
  have hii : F z (i, i) ≠ 0 :=
    (projector_apply_self_pos_iff (i := i).mpr (by simp)).ne'
  have happ (q : Fin (n + 1) × Fin (n + 1)) :
      ContDiffAt ℝ 1 (fun A : Fin (n + 1) × Fin (n + 1) → ℝ ↦ A q) (F z) :=
    (contDiff_pi.1 contDiff_id q).contDiffAt
  have hG : DifferentiableAt ℝ G (F z) :=
    (contDiffAt_pi.2 fun k ↦ (happ _).div (happ _) hii).differentiableAt one_ne_zero
  have h := hG.hasFDerivAt.comp z
    ((contDiff_projector_affineChart_symm (r := 1) i).differentiable one_ne_zero z).hasFDerivAt
  rw [hGF] at h
  have hid := h.unique (hasFDerivAt_id z)
  exact Function.LeftInverse.injective (g := fderiv ℝ G (F z)) fun v ↦ DFunLike.congr_fun hid v

section Semialgebraic

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- In matrix coordinates, the inverse of the standard affine chart at `i` followed by the
projector map is a semialgebraic map: its graph is cut out by the polynomial equations
`(wᵀ w) A = w wᵀ`, where `w = Fin.insertNth i 1 z`. -/
theorem isSemialgebraicMap_projector_affineChart_symm (i : Fin (n + 1)) :
    IsSemialgebraicMap fun (z : Fin n → K) (q : Fin (n + 1) × Fin (n + 1)) ↦
      projector ((affineChart i).symm z) q.1 q.2 := by
  rw [← isSemialgebraicOn_univ]
  -- The homogeneous coordinates `w`, as polynomials in the coordinates `z` of the graph.
  let V : Fin (n + 1) → MvPolynomial (Fin n ⊕ (Fin (n + 1) × Fin (n + 1))) K :=
    Fin.insertNth i 1 fun k ↦ X (.inl k)
  refine isSemialgebraicOn_of_forall_eq_iff isSemialgebraic_univ
    (fun q ↦ (∑ r, V r * V r) * X (.inr q) - V q.1 * V q.2) fun z _ A ↦ ?_
  set v : Fin (n + 1) → K := Fin.insertNth i 1 z
  have hs : v ⬝ᵥ v ≠ 0 := insertNth_one_dotProduct_self_ne_zero i z
  have hV (r) : eval (Sum.elim z A) (V r) = v r := by
    obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove i r <;> simp [V, v]
  simp only [map_sub, map_mul, map_sum, hV, eval_X, Sum.elim_inr, funext_iff]
  refine forall_congr' fun q ↦ ?_
  rw [affineChart_symm_apply, projector_mk, rankOneProjector_apply, div_eq_iff hs, sub_eq_zero,
    eq_comm]
  simp [v, dotProduct, mul_comm]

/-- In matrix coordinates, the image of the standard affine open `{x_i ≠ 0}` under the projector
map is semialgebraic: it is the part of the projector locus with nonzero `i`-th diagonal entry. -/
theorem isSemialgebraic_image_projector_affineOpen {ι : Type*} [Fintype ι] (i : ι) :
    IsSemialgebraic {a : ι × ι → K | Matrix.of (Function.curry a) ∈ projector '' affineOpen i} := by
  rw [image_projector_affineOpen]
  convert isSemialgebraic_projectorLocus.inter
    (isSemialgebraic_eval_ne_zero (X (i, i) : MvPolynomial (ι × ι) K)) using 1
  ext a
  simp

/-- In matrix coordinates, the standard affine chart at `i` read in the projector model is
semialgebraic on the image of its domain: it sends a matrix `A` of the image of `{x_i ≠ 0}` to the
ratios `A (i.succAbove k) i / A i i` (`Projectivization.affineChart_eq_projector_div`). -/
theorem isSemialgebraicOn_projector_affineChart (i : Fin (n + 1)) :
    IsSemialgebraicOn (fun (a : Fin (n + 1) × Fin (n + 1) → K) k ↦ a (i.succAbove k, i) / a (i, i))
      {a | Matrix.of (Function.curry a) ∈ projector '' affineOpen i} := by
  refine isSemialgebraicOn_of_forall_eq_iff (isSemialgebraic_image_projector_affineOpen i)
    (fun k ↦ X (.inl (i, i)) * X (.inr k) - X (.inl (i.succAbove k, i))) fun a ha w ↦ ?_
  rw [Set.mem_ofPred_eq, image_projector_affineOpen] at ha
  have hii : a (i, i) ≠ 0 := by simpa using ha.2
  simp only [funext_iff]
  refine forall_congr' fun k ↦ ?_
  rw [div_eq_iff hii, eq_comm, ← sub_eq_zero]
  simp [mul_comm]

end Semialgebraic

end AffineChart

end TauCeti

namespace Projectivization

open TauCeti

variable {n : ℕ}

/-- The projector map, with values in the matrix coordinates `Fin (n + 1) × Fin (n + 1) → ℝ`, is a
`C^r` map on real projective space for every `r`; for `r = ω` it is analytic. -/
theorem contMDiff_projector {r : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin (n + 1) × Fin (n + 1) → ℝ) r
      fun (p : ℙ ℝ (Fin (n + 1) → ℝ)) (q : Fin (n + 1) × Fin (n + 1)) ↦ projector p q.1 q.2 := by
  intro p
  obtain ⟨i, hi⟩ := exists_mem_affineOpen p
  have h := (ContDiff.contMDiff (contDiff_projector_affineChart_symm (r := r) i)).comp_contMDiffOn
    (contMDiffOn_affineChart i r)
  refine (h.congr fun p hp ↦ ?_).contMDiffAt ((isOpen_affineOpen i).mem_nhds hi)
  simp only [Function.comp_apply, (affineChart i).left_inv (by simpa using hp)]

/-- **The projector map is an immersion.** Its differential is injective at every point of real
projective space. -/
theorem injective_mfderiv_projector (p : ℙ ℝ (Fin (n + 1) → ℝ)) :
    Function.Injective (mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin (n + 1) × Fin (n + 1) → ℝ)
      (fun (p : ℙ ℝ (Fin (n + 1) → ℝ)) (q : Fin (n + 1) × Fin (n + 1)) ↦ projector p q.1 q.2)
      p) := by
  have h := (ContMDiffAt.mdifferentiableAt (contMDiff_projector (r := 1) p) one_ne_zero).mfderiv
  simp only [h, ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe]
  refine (ContinuousLinearEquiv.injective _).comp (Function.Injective.comp ?_
    (ContinuousLinearEquiv.injective _))
  -- The preferred chart at `p` is a standard affine chart, and the target model is the identity,
  -- so the map written in charts is the projector map read in that affine chart.
  simp only [writtenInExtChartAt, extChartAt, OpenPartialHomeomorph.extend,
    chartAt_eq_affineOpenPartialHomeomorph,
    coe_affineOpenPartialHomeomorph_symm, fderivWithin_univ, mfld_simps]
  exact injective_fderiv_projector_affineChart_symm _ _

end Projectivization
