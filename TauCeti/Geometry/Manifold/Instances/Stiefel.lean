/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.LevelSet.Manifold
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Sym.Card
public import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Stiefel manifolds of orthonormal frames

For a finite-dimensional real inner product space `E` of dimension `n`, the *Stiefel manifold*
`V_k(E)` is the set `TauCeti.stiefel E k` of orthonormal families `v : Fin k → E`. It is a compact
smooth manifold of dimension `k n - (k + 1).choose 2`, modelled here on
`Fin (k * finrank ℝ E - (k + 1).choose 2) → ℝ`. It is nonempty exactly when `k ≤ n`. For `k = 2`
it is the manifold of orthonormal `2`-frames `(u, v)`, of dimension `2 n - 3`, which is also the
unit tangent bundle of the unit sphere of `E`: `v` is a unit vector tangent to the sphere at `u`.

The smooth structure is that of a regular level set. The *Gram map* `TauCeti.gramSym2` sends a
family `v` to its inner products `⟪v i, v j⟫`, indexed by the unordered pairs `s(i, j)` since the
real inner product is symmetric. Orthonormal families are its fibre over the function equal to `1`
on the diagonal and `0` off it. At an orthonormal family `v` its derivative
`a ↦ (s(i, j) ↦ ⟪v i, a j⟫ + ⟪a i, v j⟫)` is surjective: the family `a i = ∑ⱼ (t s(i, j) / 2) • v j`
is sent to `t`. So `TauCeti.levelSetChartedSpace` and `TauCeti.isManifold_levelSet` make the Stiefel
manifold an analytic manifold, of dimension the index of that derivative,
`k n - (k + 1).choose 2`, the dimension of the space of `k`-families minus the number of unordered
pairs of indices.

For this structure the inclusion into `Fin k → E` is smooth, and so is the map
`TauCeti.stiefelProj E k i` sending a frame to its `i`th vector in the unit sphere with Mathlib's
manifold structure.

## Main definitions

* `TauCeti.gramSym2`: the Gram map of `k`-families, with values on unordered pairs of indices.
* `TauCeti.stiefel E k`: the Stiefel manifold of orthonormal `k`-frames of `E`.
* `TauCeti.stiefelProj E k i`: the `i`th vector of a frame, as a point of the unit sphere.

## Main results

* `TauCeti.mem_stiefel_iff`: the points of `TauCeti.stiefel E k` are the orthonormal families.
* `TauCeti.mem_stiefel_two_iff`: the points of `TauCeti.stiefel E 2` are the pairs of orthogonal
  unit vectors.
* `TauCeti.nonempty_stiefel`: the Stiefel manifold is nonempty exactly when `k ≤ finrank ℝ E`.
* `TauCeti.gramSym2Deriv_surjective` and `TauCeti.index_gramSym2Deriv`: the Gram map is regular
  along the Stiefel manifold, with derivative of index `k n - (k + 1).choose 2`.
* `TauCeti.stiefel.instIsManifold`: the Stiefel manifold is a `C^r` manifold for every `r`.
* `TauCeti.isCompact_stiefel`: the Stiefel manifold is compact.
* `TauCeti.contMDiff_coe_stiefel` and `TauCeti.contMDiff_stiefelProj`: the inclusion into
  `Fin k → E` and the projections to the unit sphere are smooth.
* `TauCeti.range_mfderiv_coe_stiefel`: the tangent space of the Stiefel manifold at `v`, as the
  range of the differential of the inclusion, is the kernel of the derivative of the Gram map.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, Chapter 5.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 5 (regular level sets).
-/

public section

open Function Module Set
open scoped ContDiff Manifold RealInnerProductSpace

namespace TauCeti

noncomputable section

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (k : ℕ)

/-! ### The Gram map -/

/-- The **Gram map** of `k`-families of vectors: the family `v` goes to its inner products
`⟪v i, v j⟫`, indexed by the unordered pairs `s(i, j)` since the real inner product is symmetric. -/
def gramSym2 (v : Fin k → E) : Sym2 (Fin k) → ℝ :=
  Sym2.lift ⟨fun i j ↦ ⟪v i, v j⟫, fun _ _ ↦ real_inner_comm _ _⟩

variable {E k} in
@[simp]
theorem gramSym2_mk (v : Fin k → E) (i j : Fin k) : gramSym2 E k v s(i, j) = ⟪v i, v j⟫ := by
  rw [gramSym2, Sym2.lift_mk]

theorem contDiff_gramSym2 {r : ℕ∞ω} : ContDiff ℝ r (gramSym2 E k) := by
  refine contDiff_pi.2 fun s ↦ ?_
  induction s using Sym2.ind with | _ i j => ?_
  simp only [gramSym2_mk]
  exact (contDiff_apply ℝ (fun _ ↦ E) i).inner ℝ (contDiff_apply ℝ (fun _ ↦ E) j)

/-- The derivative of the Gram map at `v`, sending `a` to
`s(i, j) ↦ ⟪v i, a j⟫ + ⟪a i, v j⟫` (`TauCeti.gramSym2Deriv_apply_mk`). -/
def gramSym2Deriv (v : Fin k → E) : (Fin k → E) →L[ℝ] Sym2 (Fin k) → ℝ :=
  ContinuousLinearMap.pi fun s ↦ Sym2.lift
    ⟨fun i j ↦ (fderivInnerCLM ℝ (v i, v j)).comp
      ((ContinuousLinearMap.proj i).prod (ContinuousLinearMap.proj j)), fun i j ↦ by
        ext a
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
          ContinuousLinearMap.proj_apply, fderivInnerCLM_apply]
        rw [add_comm, real_inner_comm (v j), real_inner_comm (a j)]⟩ s

variable {E k} in
@[simp]
theorem gramSym2Deriv_apply_mk (v a : Fin k → E) (i j : Fin k) :
    gramSym2Deriv E k v a s(i, j) = ⟪v i, a j⟫ + ⟪a i, v j⟫ := by
  rw [gramSym2Deriv, ContinuousLinearMap.pi_apply, Sym2.lift_mk, ContinuousLinearMap.comp_apply,
    fderivInnerCLM_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.proj_apply]

/-- `TauCeti.gramSym2Deriv E k v` is the strict derivative of the Gram map at `v`. -/
theorem hasStrictFDerivAt_gramSym2 (v : Fin k → E) :
    HasStrictFDerivAt (gramSym2 E k) (gramSym2Deriv E k v) v := by
  refine hasStrictFDerivAt_pi'.2 fun s ↦ ?_
  induction s using Sym2.ind with | _ i j => ?_
  simp only [gramSym2_mk]
  refine ((hasStrictFDerivAt_apply i v).inner ℝ (hasStrictFDerivAt_apply j v)).congr_fderiv
    (ContinuousLinearMap.ext fun a ↦ ?_)
  simp only [ContinuousLinearMap.comp_apply, fderivInnerCLM_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.proj_apply, gramSym2Deriv_apply_mk]

variable {E k} in
/-- **The Gram map is a submersion at orthonormal families.** The family
`a i = ∑ⱼ (t s(i, j) / 2) • v j` is sent to `t`. -/
theorem gramSym2Deriv_surjective {v : Fin k → E} (hv : Orthonormal ℝ v) :
    Surjective (gramSym2Deriv E k v) := by
  intro t
  refine ⟨fun i ↦ ∑ j, (t s(i, j) / 2) • v j, ?_⟩
  ext s
  induction s using Sym2.ind with | _ i j => ?_
  rw [gramSym2Deriv_apply_mk, hv.inner_right_fintype, hv.inner_left_fintype, Sym2.eq_swap,
    conj_trivial]
  ring

variable {E k} in
/-- At an orthonormal family, the derivative of the Gram map has index
`k n - (k + 1).choose 2`, where `n = finrank ℝ E` and `(k + 1).choose 2` is the number of
unordered pairs of indices. The truncated subtraction is harmless: the index is the dimension
of the kernel, as the derivative is surjective. -/
theorem index_gramSym2Deriv [FiniteDimensional ℝ E] {v : Fin k → E} (hv : Orthonormal ℝ v) :
    (gramSym2Deriv E k v).index = (k * finrank ℝ E - (k + 1).choose 2 : ℕ) := by
  have h₁ := (gramSym2Deriv E k v).index_of_surjective (gramSym2Deriv_surjective hv)
  have h₂ := (gramSym2Deriv E k v).index_eq_of_finiteDimensional
  rw [Module.finrank_pi_fintype, Module.finrank_fintype_fun_eq_card, Sym2.card] at h₂
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h₂
  generalize k * finrank ℝ E = N at h₂ ⊢
  generalize (k + 1).choose 2 = C at h₂ ⊢
  omega

/-! ### The Stiefel manifold -/

/-- The **Stiefel manifold** `V_k(E)` of orthonormal `k`-frames of `E`, as the fibre of the Gram
map `TauCeti.gramSym2` over the function equal to `1` on the diagonal and `0` off it. Its points
are the orthonormal families (`TauCeti.mem_stiefel_iff`).

The body is exposed so that the subtype is, by definition, the level set on which
`TauCeti.levelSetChartedSpace` installs the atlas of `TauCeti.stiefel.instChartedSpace`. -/
@[expose] def stiefel : Set (Fin k → E) :=
  {v | gramSym2 E k v = fun s ↦ if s.IsDiag then 1 else 0}

variable {E k}

/-- The points of the Stiefel manifold are the orthonormal families. -/
@[simp]
theorem mem_stiefel_iff {v : Fin k → E} : v ∈ stiefel E k ↔ Orthonormal ℝ v := by
  classical
  rw [orthonormal_iff_ite, stiefel, mem_ofPred_eq, funext_iff, Sym2.forall]
  simp [Sym2.mk_isDiag_iff]

/-- The points of `TauCeti.stiefel E 2` are the pairs of orthogonal unit vectors. -/
theorem mem_stiefel_two_iff {v : Fin 2 → E} :
    v ∈ stiefel E 2 ↔ ‖v 0‖ = 1 ∧ ‖v 1‖ = 1 ∧ ⟪v 0, v 1⟫ = 0 := by
  simp [mem_stiefel_iff, Orthonormal, Pairwise, Fin.forall_fin_two, real_inner_comm (v 0),
    and_assoc]

/-- The vectors of a frame in the Stiefel manifold are unit vectors. -/
theorem norm_eq_one_of_mem_stiefel {v : Fin k → E} (hv : v ∈ stiefel E k) (i : Fin k) :
    ‖v i‖ = 1 :=
  (mem_stiefel_iff.1 hv).1 i

/-- The Stiefel manifold of orthonormal `k`-frames of `E` is nonempty exactly when
`k ≤ finrank ℝ E`. -/
theorem nonempty_stiefel [FiniteDimensional ℝ E] :
    (stiefel E k).Nonempty ↔ k ≤ finrank ℝ E := by
  refine ⟨fun ⟨v, hv⟩ ↦ ?_, fun h ↦ ⟨_, mem_stiefel_iff.2 <|
    (stdOrthonormalBasis ℝ E).orthonormal.comp _ (Fin.castLE_injective h)⟩⟩
  simpa using (mem_stiefel_iff.1 hv).linearIndependent.fintype_card_le_finrank

variable (E k)

/-- The Stiefel manifold is closed in the space of `k`-families. -/
theorem isClosed_stiefel : IsClosed (stiefel E k) :=
  isClosed_eq (contDiff_gramSym2 E k (r := 0)).continuous continuous_const

/-- The Stiefel manifold of a finite-dimensional space is compact. -/
theorem isCompact_stiefel [FiniteDimensional ℝ E] : IsCompact (stiefel E k) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_stiefel E k)
    ((Metric.isBounded_closedBall (x := 0) (r := 1)).subset fun _ hv ↦
      mem_closedBall_zero_iff.2 ((pi_norm_le_iff_of_nonneg zero_le_one).2 fun i ↦
        (norm_eq_one_of_mem_stiefel hv i).le))

namespace stiefel

instance instCompactSpace [FiniteDimensional ℝ E] : CompactSpace (stiefel E k) :=
  isCompact_iff_compactSpace.1 (isCompact_stiefel E k)

/-- The atlas of the Stiefel manifold, by the implicit-function charts of the regular level set
`TauCeti.stiefel E k` of the Gram map. The model has dimension `k n - (k + 1).choose 2`, where
`n = finrank ℝ E`. -/
instance instChartedSpace [FiniteDimensional ℝ E] :
    ChartedSpace (Fin (k * finrank ℝ E - (k + 1).choose 2) → ℝ) (stiefel E k) :=
  levelSetChartedSpace (fun v _ ↦ hasStrictFDerivAt_gramSym2 E k v)
    (fun _ _ ↦ ContinuousLinearMap.isFredholm_of_finiteDimensional _)
    (fun _ hv ↦ gramSym2Deriv_surjective (mem_stiefel_iff.1 hv))
    (fun _ hv ↦ index_gramSym2Deriv (mem_stiefel_iff.1 hv))

/-- **The Stiefel manifold is a smooth manifold**, indeed a `C^r` manifold for every `r`,
including the analytic case `r = ω`. -/
instance instIsManifold [FiniteDimensional ℝ E] (r : ℕ∞ω) :
    IsManifold 𝓘(ℝ, Fin (k * finrank ℝ E - (k + 1).choose 2) → ℝ) r (stiefel E k) :=
  isManifold_levelSet _ _ _ _ fun _ _ ↦ (contDiff_gramSym2 E k).contDiffAt

end stiefel

/-- The inclusion of the Stiefel manifold into the space of `k`-families is smooth. -/
theorem contMDiff_coe_stiefel [FiniteDimensional ℝ E] {r : ℕ∞ω} :
    ContMDiff 𝓘(ℝ, Fin (k * finrank ℝ E - (k + 1).choose 2) → ℝ) 𝓘(ℝ, Fin k → E) r
      ((↑) : stiefel E k → Fin k → E) :=
  contMDiff_coe_levelSet _ _ _ _ fun _ _ ↦ (contDiff_gramSym2 E k).contDiffAt

variable {E k} in
/-- **The tangent space of the Stiefel manifold.** The differential at `v` of the inclusion into
the space of `k`-families has range the kernel of the derivative `TauCeti.gramSym2Deriv E k v` of
the Gram map: the families `a` with `⟪v i, a j⟫ + ⟪a i, v j⟫ = 0` for all `i` and `j`. -/
theorem range_mfderiv_coe_stiefel [FiniteDimensional ℝ E] (v : stiefel E k) :
    LinearMap.range (mfderiv 𝓘(ℝ, Fin (k * finrank ℝ E - (k + 1).choose 2) → ℝ) 𝓘(ℝ, Fin k → E)
      ((↑) : stiefel E k → Fin k → E) v).toLinearMap = (gramSym2Deriv E k v).ker := by
  have h : HasMFDerivAt 𝓘(ℝ, Fin (k * finrank ℝ E - (k + 1).choose 2) → ℝ) 𝓘(ℝ, Fin k → E)
      ((↑) : stiefel E k → Fin k → E) v _ := hasMFDerivAt_coe_levelSet _ _ _ _ v
  rw [h.mfderiv]
  exact (LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)).trans
    (Submodule.range_subtype _)

/-- The `i`th vector of an orthonormal frame, as a point of the unit sphere. For `k = 2` and
`i = 0` this is the projection of the unit tangent bundle of the sphere to its base. -/
def stiefelProj (i : Fin k) (v : stiefel E k) : Metric.sphere (0 : E) 1 :=
  ⟨v.1 i, mem_sphere_zero_iff_norm.2 (norm_eq_one_of_mem_stiefel v.2 i)⟩

variable {E k} in
@[simp]
theorem coe_stiefelProj (i : Fin k) (v : stiefel E k) : (stiefelProj E k i v : E) = v.1 i :=
  (rfl)

/-- The projection of a frame to its `i`th vector is smooth, for Mathlib's manifold structure on
the unit sphere. The `FiniteDimensional` instance, which also follows from the `Fact`, is the one
the manifold structure of the Stiefel manifold is stated with. -/
theorem contMDiff_stiefelProj [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E = n + 1)]
    {r : ℕ∞ω} (i : Fin k) :
    ContMDiff 𝓘(ℝ, Fin (k * finrank ℝ E - (k + 1).choose 2) → ℝ) (𝓡 n) r
      (stiefelProj E k i) :=
  (((contDiff_apply ℝ (fun _ ↦ E) i).contMDiff).comp
    (contMDiff_coe_stiefel E k)).codRestrict_sphere _

end

end TauCeti
