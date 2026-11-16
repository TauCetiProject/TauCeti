/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberProduct.Iterated.Submersion

/-!
# Canonical diffeomorphisms of iterated submersion fibre products

For a `C^n` submersion `π : Y → M` (`1 ≤ n`) between finite-dimensional boundaryless manifolds,
this file establishes the canonical `C^n` diffeomorphisms relating iterated fibre products
`Y^[k + 1] := TauCeti.IteratedFiberProduct π (k + 1)` to `Y`, binary transverse fibre products,
and permutations or splittings of the factor indices:
* `TauCeti.iteratedFiberProductOneDiffeomorph`: `Y^[1] ≃ₘ^n Y`;
* `TauCeti.iteratedFiberProductEquivDiffeomorph`: permutation symmetry `Y^[k + 1] ≃ₘ^n Y^[k + 1]`;
* `TauCeti.iteratedFiberProductTwoDiffeomorph`: `Y^[2] ≃ₘ^n Y ×_M Y`;
* `TauCeti.iteratedFiberProductSuccDiffeomorph`: recursive splitting
  `Y^[k + 2] ≃ₘ^n Y^[k + 1] ×_M Y`;
* `TauCeti.iteratedFiberProductSplitDiffeomorph`: independence of iteration order
  `Y^[(p + 1) + (q + 1)] ≃ₘ^n Y^[p + 1] ×_M Y^[q + 1]`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer (2013),
  Theorem 6.30 (transverse fibre products).
* M. K. Murray, *Bundle gerbes*, J. London Math. Soc. (2) 54 (1996), 403–416.
-/

public section

open Module
open scoped Manifold ContDiff

namespace TauCeti

open IteratedFiberProduct

section Diffeomorph

variable {EY HY Y EM HM M : Type*}
  [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace HY]
  [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IY : ModelWithCorners ℝ EY HY} {IM : ModelWithCorners ℝ EM HM}
  [TopologicalSpace Y] [ChartedSpace HY Y]
  [TopologicalSpace M] [ChartedSpace HM M]
  {n : ℕ∞ω} {π : Y → M}
  [IsManifold IY n Y] [IsManifold IM n M]
  [IY.Boundaryless] [IM.Boundaryless]
  [FiniteDimensional ℝ EY] [FiniteDimensional ℝ EM]
  (hn : 1 ≤ n) (hπ : Manifold.IsSubmersion IY IM n π)

/-- The `1`-fold iterated fibre product `Y^[1]` is canonically `C^n`-diffeomorphic to `Y`. -/
noncomputable def iteratedFiberProductOneDiffeomorph :
    letI := iteratedFiberProductChartedSpace hn hπ 0
    IteratedFiberProduct π 1 ≃ₘ^n⟮
      𝓘(ℝ, Fin ((0 + 1) * finrank ℝ EY - 0 * finrank ℝ EM) → ℝ), IY⟯ Y :=
  letI := iteratedFiberProductChartedSpace hn hπ 0
  { toFun := IteratedFiberProduct.coord 0
    invFun := IteratedFiberProduct.diag 1
    left_inv := fun y ↦ Subtype.ext (funext fun i ↦ by rw [Subsingleton.elim i 0]; simp)
    right_inv := fun _ ↦ by simp
    contMDiff_toFun := contMDiff_coord hn hπ 0
    contMDiff_invFun := contMDiff_diag hn hπ 0 }

/-- The `1`-fold comparison map is the `0`-th coordinate projection. -/
@[simp]
theorem iteratedFiberProductOneDiffeomorph_apply (y : IteratedFiberProduct π 1) :
    iteratedFiberProductOneDiffeomorph hn hπ y = y.1 0 :=
  IteratedFiberProduct.coord_apply 0 y

/-- The inverse of the `1`-fold comparison map is the constant `1`-tuple. -/
@[simp]
theorem iteratedFiberProductOneDiffeomorph_symm_apply (y : Y) :
    letI := iteratedFiberProductChartedSpace hn hπ 0
    (iteratedFiberProductOneDiffeomorph hn hπ).symm y = IteratedFiberProduct.diag 1 y :=
  (rfl)

/-- Reindexing along a permutation `e : Fin (k + 1) ≃ Fin (k + 1)` is a `C^n`
self-diffeomorphism of `Y^[k + 1]`. -/
noncomputable def iteratedFiberProductEquivDiffeomorph {k : ℕ}
    (e : Fin (k + 1) ≃ Fin (k + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    IteratedFiberProduct π (k + 1) ≃ₘ^n⟮
      𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ),
      𝓘(ℝ, Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ)⟯
      IteratedFiberProduct π (k + 1) :=
  letI := iteratedFiberProductChartedSpace hn hπ k
  { toFun := IteratedFiberProduct.reindex e
    invFun := IteratedFiberProduct.reindex e.symm
    left_inv := fun y ↦ Subtype.ext (funext fun i ↦ by simp)
    right_inv := fun y ↦ Subtype.ext (funext fun i ↦ by simp)
    contMDiff_toFun := contMDiff_reindex hn hπ e
    contMDiff_invFun := contMDiff_reindex hn hπ e.symm }

/-- Evaluating the permutation diffeomorphism reindexes along `e`. -/
@[simp]
theorem iteratedFiberProductEquivDiffeomorph_apply {k : ℕ} (e : Fin (k + 1) ≃ Fin (k + 1))
    (y : IteratedFiberProduct π (k + 1)) :
    iteratedFiberProductEquivDiffeomorph hn hπ e y = y.reindex e :=
  (rfl)

/-- Evaluating the inverse permutation diffeomorphism reindexes along `e.symm`. -/
@[simp]
theorem iteratedFiberProductEquivDiffeomorph_symm_apply {k : ℕ} (e : Fin (k + 1) ≃ Fin (k + 1))
    (y : IteratedFiberProduct π (k + 1)) :
    letI := iteratedFiberProductChartedSpace hn hπ k
    (iteratedFiberProductEquivDiffeomorph hn hπ e).symm y = y.reindex e.symm :=
  (rfl)

/-- The `2`-fold iterated fibre product `Y^[2]` is canonically `C^n`-diffeomorphic to the binary
transverse fibre product `{p : Y × Y // π p.1 = π p.2}`. -/
noncomputable def iteratedFiberProductTwoDiffeomorph :
    letI := iteratedFiberProductChartedSpace hn hπ 1
    letI := transverseFiberProductChartedSpace hn hπ.contMDiff hπ.contMDiff
      (fun p _ ↦ transverse_of_isSubmersion_right hn hπ p)
    IteratedFiberProduct π 2 ≃ₘ^n⟮
      𝓘(ℝ, Fin (2 * finrank ℝ EY - 1 * finrank ℝ EM) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ EY + finrank ℝ EY - finrank ℝ EM) → ℝ)⟯
      {p : Y × Y // π p.1 = π p.2} := by
  letI := iteratedFiberProductChartedSpace hn hπ 1
  letI := transverseFiberProductChartedSpace hn hπ.contMDiff hπ.contMDiff
    (fun p _ ↦ transverse_of_isSubmersion_right hn hπ p)
  have hemb := isSmoothEmbedding_coe_transverseFiberProduct hn hπ.contMDiff hπ.contMDiff
    (fun p _ ↦ transverse_of_isSubmersion_right hn hπ p)
  refine
    { toFun := fun y ↦ ⟨(y.1 0, y.1 1), y.2 0 1⟩
      invFun := fun p ↦ ⟨![p.1.1, p.1.2], fun i j ↦ by
        fin_cases i <;> fin_cases j <;> simp [p.2]⟩
      left_inv := fun y ↦ Subtype.ext (funext fun i ↦ by fin_cases i <;> rfl)
      right_inv := fun _ ↦ rfl
      contMDiff_toFun := hemb.contMDiff_iff_comp.2
        (((contMDiff_coord hn hπ 0).prodMk (contMDiff_coord hn hπ 1)).congr fun y ↦
          Prod.ext (IteratedFiberProduct.coord_apply 0 y).symm
            (IteratedFiberProduct.coord_apply 1 y).symm)
      contMDiff_invFun := (contMDiff_iteratedFiberProduct_iff hn hπ).2 fun i ↦ by
        fin_cases i
        · exact contMDiff_fst.comp hemb.contMDiff
        · exact contMDiff_snd.comp hemb.contMDiff }

/-- The `2`-fold comparison sends a pair tuple `y` to `(y 0, y 1)`. -/
@[simp]
theorem iteratedFiberProductTwoDiffeomorph_apply (y : IteratedFiberProduct π 2) :
    iteratedFiberProductTwoDiffeomorph hn hπ y = ⟨(y.1 0, y.1 1), y.2 0 1⟩ :=
  (rfl)

/-- The inverse of the `2`-fold comparison builds the `2`-tuple `![p.1, p.2]`. -/
@[simp]
theorem iteratedFiberProductTwoDiffeomorph_symm_apply (p : {p : Y × Y // π p.1 = π p.2}) :
    letI := iteratedFiberProductChartedSpace hn hπ 1
    letI := transverseFiberProductChartedSpace hn hπ.contMDiff hπ.contMDiff
      (fun p _ ↦ transverse_of_isSubmersion_right hn hπ p)
    ((iteratedFiberProductTwoDiffeomorph hn hπ).symm p).1 = ![p.1.1, p.1.2] :=
  (rfl)

/-- **Recursive splitting diffeomorphism.** `Y^[k + 2]` is canonically `C^n`-diffeomorphic to
the binary transverse fibre product `Y^[k + 1] ×_M Y` formed from `baseProj` and `π`. -/
noncomputable def iteratedFiberProductSuccDiffeomorph (k : ℕ) :
    letI := iteratedFiberProductChartedSpace hn hπ (k + 1)
    letI := iteratedFiberProductChartedSpace hn hπ k
    letI := isManifold_iteratedFiberProduct hn hπ k
    letI := transverseFiberProductChartedSpace hn (contMDiff_baseProj hn hπ k) hπ.contMDiff
      (fun p _ ↦ transverse_of_isSubmersion_right hn hπ p)
    IteratedFiberProduct π (k + 2) ≃ₘ^n⟮
      𝓘(ℝ, Fin ((k + 2) * finrank ℝ EY - (k + 1) * finrank ℝ EM) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ (Fin ((k + 1) * finrank ℝ EY - k * finrank ℝ EM) → ℝ) +
        finrank ℝ EY - finrank ℝ EM) → ℝ)⟯
      {p : IteratedFiberProduct π (k + 1) × Y // p.1.baseProj = π p.2} := by
  letI := iteratedFiberProductChartedSpace hn hπ (k + 1)
  letI := iteratedFiberProductChartedSpace hn hπ k
  haveI := isManifold_iteratedFiberProduct hn hπ k
  letI := transverseFiberProductChartedSpace hn (contMDiff_baseProj hn hπ k) hπ.contMDiff
    (fun p _ ↦ transverse_of_isSubmersion_right hn hπ p)
  have hemb := isSmoothEmbedding_coe_transverseFiberProduct hn (contMDiff_baseProj hn hπ k)
    hπ.contMDiff (fun p _ ↦ transverse_of_isSubmersion_right hn hπ p)
  let e := iteratedFiberProductSuccHomeomorph (π := π) k
  refine { e.toEquiv with contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · exact hemb.contMDiff_iff_comp.2
      (((contMDiff_reindex hn hπ Fin.castSucc).prodMk
        (contMDiff_coord hn hπ (Fin.last (k + 1)))).congr fun _ ↦ by simp [e])
  · refine (contMDiff_iteratedFiberProduct_iff hn hπ).2 fun i ↦ Fin.lastCases ?_ (fun i' ↦ ?_) i
    · exact (contMDiff_snd.comp hemb.contMDiff).congr fun _ ↦ by simp [e]
    · exact ((contMDiff_coord hn hπ i').comp (contMDiff_fst.comp hemb.contMDiff)).congr
        fun _ ↦ by simp [e]

/-- The recursive splitting diffeomorphism separates the initial `k + 1` coordinates from the
last coordinate. -/
@[simp]
theorem iteratedFiberProductSuccDiffeomorph_apply (k : ℕ) (y : IteratedFiberProduct π (k + 2)) :
    (iteratedFiberProductSuccDiffeomorph hn hπ k y).1 =
      (y.reindex Fin.castSucc, y.1 (Fin.last (k + 1))) :=
  iteratedFiberProductSuccHomeomorph_apply k y

/-- The inverse of the recursive splitting diffeomorphism appends the extra factor by `Fin.snoc`. -/
@[simp]
theorem iteratedFiberProductSuccDiffeomorph_symm_apply (k : ℕ)
    (q : {p : IteratedFiberProduct π (k + 1) × Y // p.1.baseProj = π p.2}) :
    letI := iteratedFiberProductChartedSpace hn hπ (k + 1)
    letI := iteratedFiberProductChartedSpace hn hπ k
    letI := isManifold_iteratedFiberProduct hn hπ k
    letI := transverseFiberProductChartedSpace hn (contMDiff_baseProj hn hπ k) hπ.contMDiff
      (fun p _ ↦ transverse_of_isSubmersion_right hn hπ p)
    ((iteratedFiberProductSuccDiffeomorph hn hπ k).symm q).1 = Fin.snoc q.1.1.1 q.1.2 :=
  iteratedFiberProductSuccHomeomorph_symm_apply k q

/-- **Independence of order of iteration.** For any `p, q : ℕ`, the iterated fibre product
`Y^[(p + 1) + (q + 1)]` is canonically `C^n`-diffeomorphic to the transverse fibre product
`Y^[p + 1] ×_M Y^[q + 1]` over their common base projections. -/
noncomputable def iteratedFiberProductSplitDiffeomorph (p q : ℕ) :
    letI := iteratedFiberProductChartedSpace hn hπ (p + 1 + q)
    letI := iteratedFiberProductChartedSpace hn hπ p
    letI := iteratedFiberProductChartedSpace hn hπ q
    letI := isManifold_iteratedFiberProduct hn hπ p
    letI := isManifold_iteratedFiberProduct hn hπ q
    letI := transverseFiberProductChartedSpace hn (contMDiff_baseProj hn hπ p)
      (contMDiff_baseProj hn hπ q)
      (fun r _ ↦ transverse_of_isSubmersion_right hn (isSubmersion_baseProj hn hπ q) r)
    IteratedFiberProduct π ((p + 1) + (q + 1)) ≃ₘ^n⟮
      𝓘(ℝ, Fin (((p + 1) + (q + 1)) * finrank ℝ EY - (p + 1 + q) * finrank ℝ EM) → ℝ),
      𝓘(ℝ, Fin (finrank ℝ (Fin ((p + 1) * finrank ℝ EY - p * finrank ℝ EM) → ℝ) +
        finrank ℝ (Fin ((q + 1) * finrank ℝ EY - q * finrank ℝ EM) → ℝ) -
        finrank ℝ EM) → ℝ)⟯
      {r : IteratedFiberProduct π (p + 1) × IteratedFiberProduct π (q + 1) //
        r.1.baseProj = r.2.baseProj} := by
  letI := iteratedFiberProductChartedSpace hn hπ (p + 1 + q)
  letI := iteratedFiberProductChartedSpace hn hπ p
  letI := iteratedFiberProductChartedSpace hn hπ q
  haveI := isManifold_iteratedFiberProduct hn hπ p
  haveI := isManifold_iteratedFiberProduct hn hπ q
  letI := transverseFiberProductChartedSpace hn (contMDiff_baseProj hn hπ p)
    (contMDiff_baseProj hn hπ q)
    (fun r _ ↦ transverse_of_isSubmersion_right hn (isSubmersion_baseProj hn hπ q) r)
  have hemb := isSmoothEmbedding_coe_transverseFiberProduct hn (contMDiff_baseProj hn hπ p)
    (contMDiff_baseProj hn hπ q)
    (fun r _ ↦ transverse_of_isSubmersion_right hn (isSubmersion_baseProj hn hπ q) r)
  refine
    { toFun := fun y ↦ ⟨(y.reindex (Fin.castAdd (q + 1)), y.reindex (Fin.natAdd (p + 1))), by simp⟩
      invFun := fun r ↦ ⟨Fin.append r.1.1.1 r.1.2.1, fun i j ↦ by
        refine Fin.addCases (m := p + 1) (n := q + 1) (fun i₁ ↦ ?_) (fun i₂ ↦ ?_) i <;>
          refine Fin.addCases (m := p + 1) (n := q + 1) (fun j₁ ↦ ?_) (fun j₂ ↦ ?_) j <;>
          simp [Fin.append_left, Fin.append_right, map_coord_eq_baseProj, r.2]⟩
      left_inv := fun y ↦ Subtype.ext (funext fun i ↦
        Fin.addCases (m := p + 1) (n := q + 1)
          (fun i₁ ↦ by simp [Fin.append_left]) (fun i₂ ↦ by simp [Fin.append_right]) i)
      right_inv := fun r ↦ Subtype.ext (Prod.ext
        (Subtype.ext (funext fun i ↦ by simp [Fin.append_left]))
        (Subtype.ext (funext fun j ↦ by simp [Fin.append_right])))
      contMDiff_toFun := hemb.contMDiff_iff_comp.2
        ((contMDiff_reindex (m := p) (k := p + 1 + q) hn hπ (Fin.castAdd (q + 1))).prodMk
          (contMDiff_reindex (m := q) (k := p + 1 + q) hn hπ (Fin.natAdd (p + 1))))
      contMDiff_invFun := (contMDiff_iteratedFiberProduct_iff (k := p + 1 + q) hn hπ).2 fun i ↦
        Fin.addCases (m := p + 1) (n := q + 1)
          (fun i₁ ↦ ((contMDiff_coord hn hπ i₁).comp (contMDiff_fst.comp hemb.contMDiff)).congr
            fun _ ↦ by simp [Fin.append_left])
          (fun i₂ ↦ ((contMDiff_coord hn hπ i₂).comp (contMDiff_snd.comp hemb.contMDiff)).congr
            fun _ ↦ by simp [Fin.append_right]) i }

/-- The splitting diffeomorphism splits a `((p + 1) + (q + 1))`-tuple into its first `p + 1`
and last `q + 1` coordinates. -/
@[simp]
theorem iteratedFiberProductSplitDiffeomorph_apply (p q : ℕ)
    (y : IteratedFiberProduct π ((p + 1) + (q + 1))) :
    (iteratedFiberProductSplitDiffeomorph hn hπ p q y).1 =
      (y.reindex (Fin.castAdd (q + 1)), y.reindex (Fin.natAdd (p + 1))) :=
  (rfl)

/-- The inverse of the splitting diffeomorphism concatenates tuples by `Fin.append`. -/
@[simp]
theorem iteratedFiberProductSplitDiffeomorph_symm_apply (p q : ℕ)
    (r : {r : IteratedFiberProduct π (p + 1) × IteratedFiberProduct π (q + 1) //
      r.1.baseProj = r.2.baseProj}) :
    letI := iteratedFiberProductChartedSpace hn hπ (p + 1 + q)
    letI := iteratedFiberProductChartedSpace hn hπ p
    letI := iteratedFiberProductChartedSpace hn hπ q
    letI := isManifold_iteratedFiberProduct hn hπ p
    letI := isManifold_iteratedFiberProduct hn hπ q
    letI := transverseFiberProductChartedSpace hn (contMDiff_baseProj hn hπ p)
      (contMDiff_baseProj hn hπ q)
      (fun r _ ↦ transverse_of_isSubmersion_right hn (isSubmersion_baseProj hn hπ q) r)
    ((iteratedFiberProductSplitDiffeomorph hn hπ p q).symm r).1 = Fin.append r.1.1.1 r.1.2.1 :=
  (rfl)

end Diffeomorph

end TauCeti
