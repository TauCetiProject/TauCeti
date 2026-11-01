/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
import TauCeti.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
-- Private: `ContinuousLinearMap.dual_finrank_eq` is used only inside proofs.
import TauCeti.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.Normed.Module.QuadraticMap

/-!
# Nondegeneracy of the bilinear form of a continuous linear map into the dual

A continuous linear map `L : E →L[𝕜] E →L[𝕜] 𝕜` carries a bilinear form
`ContinuousLinearMap.toBilinForm L`, and that form is left-separating exactly when `L` is
injective: both say that no nonzero vector is annihilated by `L`. Reading nondegeneracy of the
form off injectivity of the map is the step that connects the two ways a Hessian is presented —
as a map into the dual space and as a bilinear form — and it has nothing to do with the analysis
that produces the Hessian, so it is recorded here, next to `ContinuousLinearMap.toBilinForm`
itself, rather than with any of its users.

The file also records that the continuous bilinear forms which are symmetric, positive definite
and have a von Neumann bounded unit set form a convex set. These are the fibrewise conditions of a
Riemannian metric, and convexity is what lets local metrics be glued by partitions of unity; the
statement itself involves no manifolds, so it is recorded here with the other facts about
continuous bilinear forms. In finite dimensions, strict diagonal positivity is open, by
transporting `TauCeti.isOpen_setOfPred_dotProduct_mulVec_pos` from matrices through a basis, and
strict diagonal positivity along a compact family is uniform: one constant bounds the whole family
below by a multiple of the squared norm. This gives the uniform coercivity constants of tamed
almost complex structures over compact windows that energy estimates for pseudoholomorphic maps
use.

## Main results

* `ContinuousLinearMap.separatingLeft_toBilinForm_iff_injective`: the bilinear form of a
  continuous linear map into the dual is left-separating if and only if the map is injective.
* `ContinuousLinearMap.isSymm_toBilinForm_iff`: the bilinear form of a continuous linear map into
  the dual is symmetric if and only if the map takes symmetric values.
* `ContinuousLinearMap.ker_toBilinForm`: the kernel of the bilinear form of a continuous linear
  map into the dual is the kernel of the map.
* `ContinuousLinearMap.inf_eq_bot_of_le_ker`: a subspace on which the diagonal of the form has no
  nonzero zeros meets every subspace of the kernel trivially.
* `ContinuousLinearMap.isInvertible_of_injective` and
  `ContinuousLinearMap.isInvertible_of_surjective`: in finite dimensions an injective, equivalently
  a surjective, map into the dual is already invertible, the dual having the same dimension as the
  space (`ContinuousLinearMap.dual_finrank_eq`).
* `ContinuousLinearMap.isInvertible_of_separatingLeft`: in finite dimensions, a map into the dual
  with left-separating bilinear form is invertible.
* `ContinuousLinearMap.isInvertible_of_pos`: in finite dimensions, a map into the dual that is
  positive on nonzero diagonal vectors is invertible.
* `ContinuousLinearMap.exists_pos_forall_le_neg_mul_sq`: a continuous bilinear form negative on
  the nonzero vectors of a finite-dimensional subspace is bounded there by a negative multiple of
  the squared norm.
* `TauCeti.isInvertible_toContinuousBilinearMap_iff_separatingLeft`:
  contraction with a bilinear form is invertible exactly when it is left-separating in
  finite dimensions, identifying covectors with vectors for local contraction equations.
* `ContinuousLinearMap.isVonNBounded_setOf_lt_one_of_pos`: in finite dimensions, positivity on
  nonzero diagonal vectors already implies the bounded-unit-set condition.
* `TauCeti.isOpen_setOf_forall_bilinear_apply_self_pos`: strict diagonal positivity is open
  among all continuous bilinear forms in finite dimensions, without imposing symmetry.
* `IsCompact.exists_pos_forall_mul_norm_sq_le`: in finite dimensions, a family of continuous
  bilinear forms, continuous on a compact set and positive on nonzero diagonal vectors, is bounded
  below on the diagonal by one positive multiple of the squared norm.
* `TauCeti.convex_setOfPred_symm_pos_isVonNBounded`: the continuous bilinear forms on a real
  topological vector space that are symmetric, positive definite and have a von Neumann bounded
  unit set form a convex set; these are the fibrewise conditions of a Riemannian metric.
* `ContinuousLinearEquiv.mem_setOfPred_symm_pos_isVonNBounded_of_inner`: a form reading as an inner
  product through a continuous linear equivalence satisfies these conditions; this supplies the
  local metrics that are glued.
-/

public section

open scoped Matrix

namespace TauCeti

section

variable {𝕜 E : Type*} [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]

/-- The bilinear form of a continuous linear map into the dual space is left-separating exactly
when the map is injective. -/
theorem _root_.ContinuousLinearMap.separatingLeft_toBilinForm_iff_injective (L : E →L[𝕜] E →L[𝕜] 𝕜)
    :
    L.toBilinForm.SeparatingLeft ↔ Function.Injective L := by
  rw [LinearMap.separatingLeft_iff_ker_eq_bot, LinearMap.ker_eq_bot]
  exact ⟨fun h v w hvw ↦ h (LinearMap.ext fun u ↦ by simp [hvw]),
    fun h v w hvw ↦ h (ContinuousLinearMap.ext fun u ↦ by simpa using LinearMap.congr_fun hvw u)⟩

/-- The bilinear form of a continuous linear map into the dual space is symmetric exactly when
the map takes symmetric values. -/
theorem _root_.ContinuousLinearMap.isSymm_toBilinForm_iff {L : E →L[𝕜] E →L[𝕜] 𝕜} :
    L.toBilinForm.IsSymm ↔ ∀ v w, L v w = L w v :=
  LinearMap.isSymm_def

/-- The kernel of the bilinear form of a continuous linear map into the dual space is the kernel of
the map. -/
theorem _root_.ContinuousLinearMap.ker_toBilinForm (L : E →L[𝕜] E →L[𝕜] 𝕜) :
    LinearMap.ker L.toBilinForm = L.ker := by
  ext x
  simp [LinearMap.ext_iff, ContinuousLinearMap.ext_iff]

/-- A subspace on whose nonzero vectors the diagonal of a continuous bilinear form does not vanish
meets every subspace of the kernel of the form trivially. -/
theorem _root_.ContinuousLinearMap.inf_eq_bot_of_le_ker {L : E →L[𝕜] E →L[𝕜] 𝕜}
    {N M : Submodule 𝕜 E} (hN : ∀ x ∈ N, x ≠ 0 → L x x ≠ 0) (hM : M ≤ L.ker) : N ⊓ M = ⊥ := by
  refine eq_bot_iff.2 fun x hx ↦ ?_
  by_contra hx0
  have h : L x = 0 := hM hx.2
  exact hN x hx.1 hx0 (by simp [h])

end

section FiniteDimensional

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] {L : E →L[𝕜] E →L[𝕜] 𝕜}

/-- In finite dimensions an injective continuous linear map into the dual is invertible: injectivity
makes it a linear equivalence onto its range, and the dual has the same finite dimension as the
space, so that range is everything. -/
theorem _root_.ContinuousLinearMap.isInvertible_of_injective
    (hinj : Function.Injective L) : L.IsInvertible :=
  ⟨((L : E →ₗ[𝕜] E →L[𝕜] 𝕜).linearEquivOfInjective hinj
      ContinuousLinearMap.dual_finrank_eq.symm).toContinuousLinearEquiv, by ext v; simp⟩

/-- In finite dimensions a surjective continuous linear map into the dual is invertible: the dual
has the same finite dimension as the space, so surjectivity forces injectivity. -/
theorem _root_.ContinuousLinearMap.isInvertible_of_surjective
    (hsurj : Function.Surjective L) : L.IsInvertible :=
  ContinuousLinearMap.isInvertible_of_injective
    ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank (V₂ := E →L[𝕜] 𝕜)
      ContinuousLinearMap.dual_finrank_eq.symm (f := (L : E →ₗ[𝕜] E →L[𝕜] 𝕜))).2 hsurj)

/-- In finite dimensions, a continuous linear map into the dual whose bilinear form is
left-separating is invertible. This is the musical isomorphism of a nondegenerate metric. -/
theorem _root_.ContinuousLinearMap.isInvertible_of_separatingLeft
    (hsep : L.toBilinForm.SeparatingLeft) : L.IsInvertible :=
  ContinuousLinearMap.isInvertible_of_injective
    ((L.separatingLeft_toBilinForm_iff_injective).1 hsep)

/-- Contraction with a bilinear form on a finite-dimensional space is an invertible
continuous linear map to the continuous dual exactly when the form is left-separating. -/
@[simp low]
theorem isInvertible_toContinuousBilinearMap_iff_separatingLeft
    {b : LinearMap.BilinForm 𝕜 E} :
    b.toContinuousBilinearMap.IsInvertible ↔ b.SeparatingLeft := by
  have hround : b.toContinuousBilinearMap.toBilinForm = b := by
    ext v w
    simp
  have hsep : b.SeparatingLeft ↔ Function.Injective b.toContinuousBilinearMap := by
    simpa only [hround] using
      b.toContinuousBilinearMap.separatingLeft_toBilinForm_iff_injective
  exact ⟨fun hb ↦ hsep.mpr hb.injective,
    fun hb ↦ _root_.ContinuousLinearMap.isInvertible_of_injective (hsep.mp hb)⟩

end FiniteDimensional

/-- In finite dimensions, a continuous linear map into the dual that is positive on nonzero
diagonal vectors is invertible. This is the musical isomorphism of a Riemannian metric. -/
theorem _root_.ContinuousLinearMap.isInvertible_of_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {L : E →L[ℝ] E →L[ℝ] ℝ} (hpos : ∀ v, v ≠ 0 → 0 < L v v) : L.IsInvertible :=
  ContinuousLinearMap.isInvertible_of_separatingLeft fun v hv ↦ by
    by_contra hv0
    exact (hpos v hv0).ne' (hv v)

/-- A continuous bilinear form that is negative on the nonzero vectors of a finite-dimensional
subspace is uniformly negative there: it is bounded by a negative multiple of the squared norm. -/
theorem _root_.ContinuousLinearMap.exists_pos_forall_le_neg_mul_sq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] E →L[ℝ] ℝ) (N : Submodule ℝ E) [FiniteDimensional ℝ N]
    (hN : ∀ x ∈ N, x ≠ 0 → L x x < 0) :
    ∃ c > 0, ∀ x ∈ N, L x x ≤ -(c * ‖x‖ ^ 2) := by
  set Q := L.toBilinForm.toQuadraticMap.restrict N
  have hQ : Q.Anisotropic := fun x hx ↦ by
    by_contra hx0
    have h := hN x x.2 (by simpa using hx0)
    simp only [Q, QuadraticMap.restrict_apply, LinearMap.BilinMap.toQuadraticMap_apply,
      ContinuousLinearMap.toBilinForm_apply] at hx
    linarith
  have hcont : Continuous Q :=
    (L.continuous.comp continuous_subtype_val).clm_apply continuous_subtype_val
  obtain ⟨c, hc, hle⟩ := hQ.exists_pos_mul_norm_sq_le hcont
  refine ⟨c, hc, fun x hx ↦ ?_⟩
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have h := hle ⟨x, hx⟩
  simp only [Q, QuadraticMap.restrict_apply, LinearMap.BilinMap.toQuadraticMap_apply,
    ContinuousLinearMap.toBilinForm_apply, Real.norm_eq_abs, abs_of_neg (hN x hx hx0),
    ← Submodule.norm_coe] at h
  linarith

section Convex

open Bornology Set

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [ContinuousConstSMul ℝ V]

/-- If `c • g ≤ h` on the diagonal for some `c > 0`, then the unit set `{v | h v v < 1}` of `h` is
von Neumann bounded as soon as the unit set of `g` is. -/
theorem isVonNBounded_setOfPred_lt_one_of_le {g h : V →L[ℝ] V →L[ℝ] ℝ} {c : ℝ} (hc : 0 < c)
    (hle : ∀ v, c * g v v ≤ h v v) (hg : IsVonNBounded ℝ {v | g v v < 1}) :
    IsVonNBounded ℝ {v | h v v < 1} := by
  -- The unit set of `h` lies in the image of the unit set of `g` under scaling by `(√c)⁻¹`.
  set r := Real.sqrt c
  have hr : 0 < r := Real.sqrt_pos.mpr hc
  refine (hg.image (r⁻¹ • ContinuousLinearMap.id ℝ V)).subset ?_
  intro v hv
  refine ⟨r • v, ?_, by simp [smul_smul, mul_inv_cancel₀ hr.ne']⟩
  simp only [mem_ofPred_eq, map_smul, smul_apply, smul_eq_mul] at hv ⊢
  calc r * (r * g v v) = c * g v v := by rw [← mul_assoc, Real.mul_self_sqrt hc.le]
    _ ≤ h v v := hle v
    _ < 1 := hv

/-- The fibrewise conditions of a Riemannian metric cut out a convex set: the continuous bilinear
forms on a real topological vector space that are symmetric, positive definite and have a
von Neumann bounded unit set are closed under convex combinations. -/
theorem convex_setOfPred_symm_pos_isVonNBounded :
    Convex ℝ {g : V →L[ℝ] V →L[ℝ] ℝ | (∀ v w, g v w = g w v) ∧ (∀ v, v ≠ 0 → 0 < g v v) ∧
      IsVonNBounded ℝ {v | g v v < 1}} := by
  -- A positive definite form is nonnegative on the diagonal.
  have nonneg {g : V →L[ℝ] V →L[ℝ] ℝ} (hg : ∀ v, v ≠ 0 → 0 < g v v) (v : V) : 0 ≤ g v v := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact (hg v hv).le
  rintro g ⟨hgs, hgp, hgb⟩ g' ⟨hgs', hgp', hgb'⟩ a b ha hb hab
  have hab' (v : V) : (a • g + b • g') v v = a * g v v + b * g' v v := by simp
  refine ⟨fun v w ↦ by simp [hgs v w, hgs' v w], fun v hv ↦ ?_, ?_⟩
  · -- One of the two coefficients is positive.
    rw [hab']
    rcases ha.eq_or_lt with rfl | ha'
    · rw [zero_add] at hab
      subst hab
      simpa using hgp' v hv
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' (hgp v hv))
        (mul_nonneg hb (nonneg hgp' v))
  · -- One of the two coefficients is at least `1 / 2`, and that term dominates.
    rcases le_total (1 / 2 : ℝ) a with ha' | hb'
    · exact isVonNBounded_setOfPred_lt_one_of_le one_half_pos (fun v ↦ by
        rw [hab']; nlinarith [nonneg hgp v, mul_nonneg hb (nonneg hgp' v)]) hgb
    · exact isVonNBounded_setOfPred_lt_one_of_le one_half_pos (fun v ↦ by
        rw [hab']; nlinarith [nonneg hgp' v, mul_nonneg ha (nonneg hgp v)]) hgb'

omit [ContinuousConstSMul ℝ V] in
/-- A continuous bilinear form that reads as the inner product of a real inner product space
through a continuous linear equivalence `L` is symmetric and positive definite, with von Neumann
bounded unit set: these are the fibrewise conditions on a Riemannian metric. -/
theorem _root_.ContinuousLinearEquiv.mem_setOfPred_symm_pos_isVonNBounded_of_inner
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] (L : V ≃L[ℝ] G)
    {g : V →L[ℝ] V →L[ℝ] ℝ}
    (hg : ∀ v w, g v w = inner ℝ (L v) (L w)) :
    g ∈ {g : V →L[ℝ] V →L[ℝ] ℝ | (∀ v w, g v w = g w v) ∧ (∀ v, v ≠ 0 → 0 < g v v) ∧
      IsVonNBounded ℝ {v | g v v < 1}} := by
  refine ⟨fun v w ↦ by rw [hg, hg, real_inner_comm], fun v hv ↦ ?_, ?_⟩
  · rw [hg, real_inner_self_eq_norm_sq]
    have : L v ≠ 0 := by simpa using hv
    positivity
  · -- The unit set is the image of the unit ball of `G` under `L⁻¹`.
    refine ((NormedSpace.isVonNBounded_ball ℝ G 1).image (L.symm : G →L[ℝ] V)).subset ?_
    intro v hv
    refine ⟨L v, ?_, by simp⟩
    rw [mem_ofPred_eq, hg, real_inner_self_eq_norm_sq] at hv
    simpa using (sq_lt_one_iff₀ (norm_nonneg _)).mp hv

end Convex

/-- Strict positivity on nonzero diagonal vectors is open in the space of continuous real
bilinear forms on a finite-dimensional space. Symmetry is not imposed. -/
theorem isOpen_setOf_forall_bilinear_apply_self_pos
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousSMul ℝ E] [Module.Finite ℝ E] :
    IsOpen {b : E →L[ℝ] E →L[ℝ] ℝ | ∀ v, v ≠ 0 → 0 < b v v} := by
  let e := Module.finBasis ℝ E
  let A := fun b : E →L[ℝ] E →L[ℝ] ℝ ↦ b.toBilinForm.toMatrix e
  have hA : Continuous A := by
    apply continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    simpa only [A, LinearMap.BilinForm.toMatrix_apply, ContinuousLinearMap.toBilinForm_apply,
      id_eq] using
      ((continuous_id : Continuous (id : (E →L[ℝ] E →L[ℝ] ℝ) → _)).eval_const
        (e i)).eval_const (e j)
  have heq : {b : E →L[ℝ] E →L[ℝ] ℝ | ∀ v, v ≠ 0 → 0 < b v v} =
      A ⁻¹' {a | ∀ v, v ≠ 0 → 0 < v ⬝ᵥ a *ᵥ v} := by
    ext b
    constructor
    · intro hb v hv
      rw [LinearMap.BilinForm.dotProduct_toMatrix_mulVec]
      exact hb _ (e.equivFun.symm.map_ne_zero_iff.mpr hv)
    · intro hb v hv
      have h := hb (e.equivFun v) (by simpa using hv)
      simpa only [A, LinearMap.BilinForm.dotProduct_toMatrix_mulVec,
        LinearEquiv.symm_apply_apply, ContinuousLinearMap.toBilinForm_apply] using h
  rw [heq]
  exact isOpen_setOfPred_dotProduct_mulVec_pos.preimage hA

/-- **Uniform coercivity over a compact family.** On a finite-dimensional real normed space, let
`b x` be a family of continuous bilinear forms, continuous on a compact set `K`, such that
`b x v v` is positive for every `x ∈ K` and every nonzero `v`. Then one positive constant `c`
gives `c ‖v‖² ≤ b x v v` for every `x ∈ K` and every `v`. Symmetry of the forms is not needed. -/
theorem _root_.IsCompact.exists_pos_forall_mul_norm_sq_le
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K : Set X} (hK : IsCompact K) {b : X → E →L[ℝ] E →L[ℝ] ℝ}
    (hb : ContinuousOn b K) (hpos : ∀ x ∈ K, ∀ v, v ≠ 0 → 0 < b x v v) :
    ∃ c > 0, ∀ x ∈ K, ∀ v, c * ‖v‖ ^ 2 ≤ b x v v := by
  -- The minimum over the compact set `K × S`, with `S` the unit sphere, is the constant.
  have hcont : ContinuousOn (fun p : X × E ↦ b p.1 p.2 p.2) (K ×ˢ Metric.sphere (0 : E) 1) :=
    ((hb.comp continuousOn_fst fun _ (hp : _ ∈ K ×ˢ _) ↦ hp.1).clm_apply
      continuousOn_snd).clm_apply continuousOn_snd
  obtain ⟨c, hc, hle⟩ := (hK.prod (isCompact_sphere 0 1)).exists_forall_le' hcont
    fun p hp ↦ hpos p.1 hp.1 p.2 (ne_zero_of_mem_sphere one_ne_zero ⟨p.2, hp.2⟩)
  refine ⟨c, hc, fun x hx v ↦ ?_⟩
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hu : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : E) 1 := by
    simp [norm_smul, hn.ne']
  have hh := hle (x, ‖v‖⁻¹ • v) ⟨hx, hu⟩
  have heq : b x (‖v‖⁻¹ • v) (‖v‖⁻¹ • v) = (‖v‖ ^ 2)⁻¹ * b x v v := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  rw [heq, le_inv_mul_iff₀ (by positivity)] at hh
  linarith

/-- On a finite-dimensional real normed space, a continuous bilinear form positive on
nonzero diagonal vectors has a bounded unit sublevel set. Symmetry is not needed. -/
theorem _root_.ContinuousLinearMap.isVonNBounded_setOf_lt_one_of_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (b : E →L[ℝ] E →L[ℝ] ℝ) (hb : ∀ v, v ≠ 0 → 0 < b v v) :
    Bornology.IsVonNBounded ℝ {v : E | b v v < 1} := by
  obtain ⟨c, hc, hbound⟩ := (isCompact_singleton (x := ())).exists_pos_forall_mul_norm_sq_le
    (b := fun _ ↦ b) continuousOn_const fun _ _ ↦ hb
  rw [NormedSpace.isVonNBounded_iff']
  refine ⟨Real.sqrt c⁻¹, fun v hv ↦ Real.le_sqrt_of_sq_le ?_⟩
  rw [inv_eq_one_div, le_div_iff₀ hc]
  linarith [hbound () rfl v, show b v v < 1 from hv]

end TauCeti

end
