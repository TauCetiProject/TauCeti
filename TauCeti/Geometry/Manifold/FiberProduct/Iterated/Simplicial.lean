/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import TauCeti.Geometry.Manifold.FiberProduct.Iterated.Diffeomorph
import TauCeti.Geometry.Manifold.SmoothEmbedding.LeftInverse

/-!
# Smooth simplicial Čech nerve structure on iterated submersion fibre products

For any map `π : Y → M`, the family `a ↦ IteratedFiberProduct π (a + 1)` forms the Čech nerve of
`π`: a morphism `θ : ⦋a⦌ ⟶ ⦋b⦌` in `SimplexCategory` acts contravariantly by precomposing tuples
with `θ.toOrderHom` (`TauCeti.IteratedFiberProduct.mapSimplex`). Specializing to the coface and
codegeneracy generators `SimplexCategory.δ` and `SimplexCategory.σ` yields the simplicial face and
degeneracy maps

* `TauCeti.IteratedFiberProduct.face i : IteratedFiberProduct π (k + 1) → IteratedFiberProduct π k`
  omitting the `i`-th entry (`y ↦ y ∘ i.succAbove`), and
* `TauCeti.IteratedFiberProduct.degen i : IteratedFiberProduct π k → IteratedFiberProduct π (k + 1)`
  repeating the `i`-th entry (`y ↦ y ∘ i.predAbove`),

satisfying all five simplicial identities unconditionally (`face_comp_face`,
`face_comp_degen_of_le`, `face_castSucc_comp_degen`, `face_succ_comp_degen`,
`face_comp_degen_of_gt`, `degen_comp_degen`).

When `π : Y → M` is a `C^n` submersion (`1 ≤ n`) between boundaryless finite-dimensional real
manifolds and `k ≥ 1`:

* every `mapSimplex θ`, `face i`, and `degen i` is `C^m` for `m ≤ n`;
* every `face i` is a surjective `C^n` submersion (`surjective_face`, `isSubmersion_face`);
* every `degen i` (and `constDiagonal · k`) is a `C^n` smooth embedding (`isSmoothEmbedding_degen`,
  `isSmoothEmbedding_constDiagonal`).

## References

* M. K. Murray, *Bundle gerbes*, J. London Math. Soc. (2) 54 (1996), 403–416, §2.
* C. J. Schommer-Pries, *Central extensions of smooth 2-groups and a finite-dimensional string
  2-group*, Geom. Topol. 15 (2011), 609–676, §2.1 (smooth simplicial manifolds from submersions).
-/

public section

noncomputable section

open CategoryTheory Function
open scoped Manifold ContDiff Simplicial

namespace TauCeti.IteratedFiberProduct

section Combinatorial

variable {Y M : Type*} {π : Y → M}

/-- Contravariant Čech nerve action of a morphism `θ : ⦋a⦌ ⟶ ⦋b⦌` in `SimplexCategory` on
`IteratedFiberProduct π`. -/
def mapSimplex {a b : ℕ} (θ : ⦋a⦌ ⟶ ⦋b⦌) :
    IteratedFiberProduct π (b + 1) → IteratedFiberProduct π (a + 1) :=
  precomp θ.toOrderHom

@[simp]
theorem proj_mapSimplex {a b : ℕ} (θ : ⦋a⦌ ⟶ ⦋b⦌) (y : IteratedFiberProduct π (b + 1))
    (i : Fin (a + 1)) :
    proj i (mapSimplex θ y) = proj (θ.toOrderHom i) y :=
  proj_precomp θ.toOrderHom y i

@[simp]
theorem baseProj_mapSimplex {a b : ℕ} (θ : ⦋a⦌ ⟶ ⦋b⦌) (y : IteratedFiberProduct π (b + 1)) :
    baseProj (mapSimplex θ y) = baseProj y :=
  baseProj_precomp θ.toOrderHom y

@[simp]
theorem mapSimplex_id {a : ℕ} (y : IteratedFiberProduct π (a + 1)) :
    mapSimplex (𝟙 ⦋a⦌) y = y :=
  precomp_id y

theorem mapSimplex_comp {a b c : ℕ} (θ₁ : ⦋a⦌ ⟶ ⦋b⦌) (θ₂ : ⦋b⦌ ⟶ ⦋c⦌) :
    mapSimplex (π := π) (θ₁ ≫ θ₂) = mapSimplex θ₁ ∘ mapSimplex θ₂ := by
  ext y i
  simp [mapSimplex]

/-- The `i`-th simplicial face map `IteratedFiberProduct π (k + 1) → IteratedFiberProduct π k`,
omitting the `i`-th coordinate (`y ↦ y ∘ i.succAbove`). -/
def face {k : ℕ} (i : Fin (k + 1)) :
    IteratedFiberProduct π (k + 1) → IteratedFiberProduct π k :=
  precomp i.succAbove

/-- The `i`-th simplicial degeneracy map
`IteratedFiberProduct π k → IteratedFiberProduct π (k + 1)`, duplicating the `i`-th coordinate
(`y ↦ y ∘ i.predAbove`). -/
def degen {k : ℕ} (i : Fin k) :
    IteratedFiberProduct π k → IteratedFiberProduct π (k + 1) :=
  precomp i.predAbove

@[simp]
theorem proj_face {k : ℕ} (i : Fin (k + 1)) (y : IteratedFiberProduct π (k + 1)) (j : Fin k) :
    proj j (face i y) = proj (i.succAbove j) y :=
  proj_precomp i.succAbove y j

@[simp]
theorem proj_degen {k : ℕ} (i : Fin k) (y : IteratedFiberProduct π k) (j : Fin (k + 1)) :
    proj j (degen i y) = proj (i.predAbove j) y :=
  proj_precomp i.predAbove y j

@[simp]
theorem baseProj_face {k : ℕ} [NeZero k] (i : Fin (k + 1)) (y : IteratedFiberProduct π (k + 1)) :
    baseProj (face i y) = baseProj y :=
  baseProj_precomp i.succAbove y

@[simp]
theorem baseProj_degen {k : ℕ} [NeZero k] (i : Fin k) (y : IteratedFiberProduct π k) :
    baseProj (degen i y) = baseProj y :=
  baseProj_precomp i.predAbove y

@[simp]
theorem mapSimplex_δ {a : ℕ} (i : Fin (a + 2)) :
    mapSimplex (π := π) (SimplexCategory.δ i) = face i :=
  (rfl)

@[simp]
theorem mapSimplex_σ {a : ℕ} (i : Fin (a + 1)) :
    mapSimplex (π := π) (SimplexCategory.σ i) = degen i :=
  (rfl)

/-- First simplicial identity: `face i ∘ face j.succ = face j ∘ face i.castSucc` for `i ≤ j`. -/
theorem face_comp_face {k : ℕ} {i j : Fin (k + 1)} (h : i ≤ j) :
    face i ∘ face (π := π) j.succ = face j ∘ face i.castSucc := by
  rcases k with _ | a
  · funext y
    exact ext fun x ↦ x.elim0
  · simp only [← mapSimplex_δ, ← mapSimplex_comp]
    exact congrArg (mapSimplex (π := π)) (SimplexCategory.δ_comp_δ h)

/-- Second simplicial identity: `face i.castSucc ∘ degen j.succ = degen j ∘ face i` for
`i ≤ j.castSucc`. -/
theorem face_comp_degen_of_le {k : ℕ} {i : Fin (k + 1)} {j : Fin k} (h : i ≤ j.castSucc) :
    face i.castSucc ∘ degen (π := π) j.succ = degen j ∘ face i := by
  rcases k with _ | a
  · exact j.elim0
  · simp only [← mapSimplex_δ, ← mapSimplex_σ, ← mapSimplex_comp]
    exact congrArg (mapSimplex (π := π)) (SimplexCategory.δ_comp_σ_of_le h)

/-- Third simplicial identity (lower): `face i.castSucc ∘ degen i = id`. -/
theorem face_castSucc_comp_degen {k : ℕ} (i : Fin k) :
    face i.castSucc ∘ degen (π := π) i = id := by
  rcases k with _ | a
  · exact i.elim0
  · simp only [← mapSimplex_δ, ← mapSimplex_σ, ← mapSimplex_comp]
    funext y
    exact (congrFun (congrArg (mapSimplex (π := π))
      (SimplexCategory.δ_comp_σ_self (i := i))) y).trans (mapSimplex_id y)

/-- Third simplicial identity (upper): `face i.succ ∘ degen i = id`. -/
theorem face_succ_comp_degen {k : ℕ} (i : Fin k) :
    face i.succ ∘ degen (π := π) i = id := by
  rcases k with _ | a
  · exact i.elim0
  · simp only [← mapSimplex_δ, ← mapSimplex_σ, ← mapSimplex_comp]
    funext y
    exact (congrFun (congrArg (mapSimplex (π := π))
      (SimplexCategory.δ_comp_σ_succ (i := i))) y).trans (mapSimplex_id y)

/-- Fourth simplicial identity: `face i.succ ∘ degen j.castSucc = degen j ∘ face i` for
`j.castSucc < i`. -/
theorem face_comp_degen_of_gt {k : ℕ} {i : Fin (k + 1)} {j : Fin k} (h : j.castSucc < i) :
    face i.succ ∘ degen (π := π) j.castSucc = degen j ∘ face i := by
  rcases k with _ | a
  · exact j.elim0
  · simp only [← mapSimplex_δ, ← mapSimplex_σ, ← mapSimplex_comp]
    exact congrArg (mapSimplex (π := π)) (SimplexCategory.δ_comp_σ_of_gt h)

/-- Fifth simplicial identity: `degen i.castSucc ∘ degen j = degen j.succ ∘ degen i` for `i ≤ j`. -/
theorem degen_comp_degen {k : ℕ} {i j : Fin k} (h : i ≤ j) :
    degen i.castSucc ∘ degen (π := π) j = degen j.succ ∘ degen i := by
  rcases k with _ | a
  · exact i.elim0
  · simp only [← mapSimplex_σ, ← mapSimplex_comp]
    exact congrArg (mapSimplex (π := π)) (SimplexCategory.σ_comp_σ h)

/-- Every face map `face i : IteratedFiberProduct π (k + 1) → IteratedFiberProduct π k` (`k ≥ 1`) is
unconditionally surjective, right-inverted by a degeneracy map. -/
theorem surjective_face {k : ℕ} [NeZero k] (i : Fin (k + 1)) :
    Surjective (face i : IteratedFiberProduct π (k + 1) → IteratedFiberProduct π k) := by
  rcases k with _ | a
  · exact False.elim (NeZero.ne 0 rfl)
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · have h : Fin.last (a + 1) = (Fin.last a).succ := rfl
    rw [h]
    exact LeftInverse.surjective (congrFun (face_succ_comp_degen (π := π) (Fin.last a)))
  · exact LeftInverse.surjective (congrFun (face_castSucc_comp_degen (π := π) j))

end Combinatorial

section Smooth

variable {EY HY Y EM HM M : Type*}
  [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace HY]
  [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IY : ModelWithCorners ℝ EY HY} {IM : ModelWithCorners ℝ EM HM}
  [TopologicalSpace Y] [ChartedSpace HY Y]
  [TopologicalSpace M] [ChartedSpace HM M]
  {n : ℕ∞ω} [IsManifold IY n Y] [IsManifold IM n M]
  [IY.Boundaryless] [IM.Boundaryless]
  [FiniteDimensional ℝ EY] [FiniteDimensional ℝ EM]
  {π : Y → M}

/-- For `m ≤ n`, the Čech nerve map `mapSimplex θ` is `C^m` for every `θ : ⦋a⦌ ⟶ ⦋b⦌`. -/
theorem contMDiff_mapSimplex {a b : ℕ} (hn : 1 ≤ n) (hπ : Manifold.IsSubmersion IY IM n π)
    {m : ℕ∞ω} (hmn : m ≤ n) (θ : ⦋a⦌ ⟶ ⦋b⦌) :
    letI := iteratedFiberProductChartedSpace (a + 1) hn hπ
    letI := iteratedFiberProductChartedSpace (b + 1) hn hπ
    ContMDiff 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM (b + 1)) → ℝ)
      𝓘(ℝ, Fin (iteratedFiberProductDim EY EM (a + 1)) → ℝ) m (mapSimplex (π := π) θ) :=
  contMDiff_precomp hn hπ hmn θ.toOrderHom

/-- For `m ≤ n` and `k ≥ 1`, every face map `face i` is `C^m`. -/
theorem contMDiff_face {k : ℕ} [NeZero k] (hn : 1 ≤ n) (hπ : Manifold.IsSubmersion IY IM n π)
    {m : ℕ∞ω} (hmn : m ≤ n) (i : Fin (k + 1)) :
    letI := iteratedFiberProductChartedSpace k hn hπ
    letI := iteratedFiberProductChartedSpace (k + 1) hn hπ
    ContMDiff 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM (k + 1)) → ℝ)
      𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ) m (face (π := π) i) :=
  contMDiff_precomp hn hπ hmn i.succAbove

/-- For `m ≤ n` and `k ≥ 1`, every degeneracy map `degen i` is `C^m`. -/
theorem contMDiff_degen {k : ℕ} [NeZero k] (hn : 1 ≤ n) (hπ : Manifold.IsSubmersion IY IM n π)
    {m : ℕ∞ω} (hmn : m ≤ n) (i : Fin k) :
    letI := iteratedFiberProductChartedSpace k hn hπ
    letI := iteratedFiberProductChartedSpace (k + 1) hn hπ
    ContMDiff 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ)
      𝓘(ℝ, Fin (iteratedFiberProductDim EY EM (k + 1)) → ℝ) m (degen (π := π) i) :=
  contMDiff_precomp hn hπ hmn i.predAbove

/-- For `m ≤ n` and `k ≥ 1`, the multidiagonal `constDiagonal · k : Y → IteratedFiberProduct π k` is
`C^m`. -/
theorem contMDiff_constDiagonal (k : ℕ) [NeZero k] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) {m : ℕ∞ω} (hmn : m ≤ n) :
    letI := iteratedFiberProductChartedSpace k hn hπ
    ContMDiff IY 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ) m
      (fun y : Y ↦ constDiagonal (π := π) y k) := by
  let := iteratedFiberProductChartedSpace k hn hπ
  exact (contMDiff_iteratedFiberProduct_iff hn hπ hmn).2 fun _ ↦ by
    simp only [proj_constDiagonal]
    rw [← Function.id_def]
    exact contMDiff_id

/-- Every degeneracy map `degen i : IteratedFiberProduct π k → IteratedFiberProduct π (k + 1)`
(`k ≥ 1`) is a `C^n` smooth embedding, left-inverted by `face i.castSucc`. -/
theorem isSmoothEmbedding_degen {k : ℕ} [NeZero k] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) (i : Fin k) :
    letI := iteratedFiberProductChartedSpace k hn hπ
    letI := iteratedFiberProductChartedSpace (k + 1) hn hπ
    Manifold.IsSmoothEmbedding 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ)
      𝓘(ℝ, Fin (iteratedFiberProductDim EY EM (k + 1)) → ℝ) n (degen (π := π) i) := by
  let := iteratedFiberProductChartedSpace k hn hπ
  let := iteratedFiberProductChartedSpace (k + 1) hn hπ
  have := isManifold_iteratedFiberProduct k hn hπ
  have := isManifold_iteratedFiberProduct (k + 1) hn hπ
  exact (contMDiff_degen hn hπ le_rfl i).isSmoothEmbedding_of_leftInverse hn
    (contMDiff_face hn hπ hn i.castSucc) (congrFun (face_castSucc_comp_degen i))

/-- The multidiagonal `constDiagonal · k : Y → IteratedFiberProduct π k` (`k ≥ 1`) is a `C^n` smooth
embedding, left-inverted by `proj 0`. -/
theorem isSmoothEmbedding_constDiagonal (k : ℕ) [NeZero k] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) :
    letI := iteratedFiberProductChartedSpace k hn hπ
    Manifold.IsSmoothEmbedding IY 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ) n
      (fun y : Y ↦ constDiagonal (π := π) y k) := by
  let := iteratedFiberProductChartedSpace k hn hπ
  have := isManifold_iteratedFiberProduct k hn hπ
  exact (contMDiff_constDiagonal k hn hπ le_rfl).isSmoothEmbedding_of_leftInverse hn
    (contMDiff_proj_iteratedFiberProduct k hn hπ hn 0) fun y ↦ proj_constDiagonal y k 0

/-- Every simplicial face map `face i : IteratedFiberProduct π (k + 1) → IteratedFiberProduct π k`
(`k ≥ 1`) is a `C^n` submersion. -/
theorem isSubmersion_face {k : ℕ} [NeZero k] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) (i : Fin (k + 1)) :
    letI := iteratedFiberProductChartedSpace k hn hπ
    letI := iteratedFiberProductChartedSpace (k + 1) hn hπ
    Manifold.IsSubmersion 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM (k + 1)) → ℝ)
      𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ) n (face (π := π) i) := by
  let := iteratedFiberProductChartedSpace k hn hπ
  let := iteratedFiberProductChartedSpace (k + 1) hn hπ
  have := isManifold_iteratedFiberProduct k hn hπ
  have := isManifold_iteratedFiberProduct (k + 1) hn hπ
  have hn0 : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le hn)
  -- First prove `face (Fin.last k)` is a submersion via `iteratedFiberProductSuccRightDiffeomorph`.
  have hsubk := isSubmersion_baseProj_iteratedFiberProduct k hn hπ
  have htrans : ∀ p : IteratedFiberProduct π k × Y,
      baseProj p.1 = π p.2 →
      (mfderiv 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ) IM baseProj p.1).range ⊔
      (((tangentSpaceCast IM (π p.2) (baseProj p.1)).toContinuousLinearMap).comp
        (mfderiv IY IM π p.2)).range = ⊤ :=
    fun p _ ↦ hsubk.transverse_left hn0 π p
  let := transverseFiberProductChartedSpace hn hsubk.contMDiff hπ.contMDiff htrans
  have := isManifold_transverseFiberProduct hn hsubk.contMDiff hπ.contMDiff htrans
  have hfst := isSubmersion_fst_transverseFiberProduct hn hsubk.contMDiff hπ.contMDiff htrans hπ
  have hlast_eq : (face (Fin.last k) : IteratedFiberProduct π (k + 1) → IteratedFiberProduct π k) =
      (fun p ↦ p.1.1) ∘ ⇑(iteratedFiberProductSuccRightDiffeomorph k hn hπ) := by
    ext y j
    simp [Fin.succAbove_last]
  have hlast : Manifold.IsSubmersion
      𝓘(ℝ, Fin (iteratedFiberProductDim EY EM (k + 1)) → ℝ)
      𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ) n (face (π := π) (Fin.last k)) := by
    rw [hlast_eq]
    exact hfst.comp ((iteratedFiberProductSuccRightDiffeomorph k hn hπ).isSubmersion hn0)
  -- Permute `Fin.last k ↦ i` and `j.castSucc ↦ i.succAbove j` to reduce `face i` to
  -- `face (Fin.last k)`.
  let τ : Fin (k + 1) → Fin (k + 1) := Fin.lastCases i i.succAbove
  have hτ_inj : Injective τ := by
    intro a b
    refine Fin.lastCases ?_ (fun a' ↦ ?_) a <;> refine Fin.lastCases ?_ (fun b' ↦ ?_) b <;>
      intro hab
    · rfl
    · simp only [τ, Fin.lastCases_last, Fin.lastCases_castSucc] at hab
      exact False.elim (Fin.succAbove_ne i b' hab.symm)
    · simp only [τ, Fin.lastCases_last, Fin.lastCases_castSucc] at hab
      exact False.elim (Fin.succAbove_ne i a' hab)
    · simp only [τ, Fin.lastCases_castSucc] at hab
      exact congrArg Fin.castSucc (Fin.succAbove_right_injective hab)
  let σ : Equiv.Perm (Fin (k + 1)) := Equiv.ofBijective τ (Finite.injective_iff_bijective.1 hτ_inj)
  have hface_eq : (face i : IteratedFiberProduct π (k + 1) → IteratedFiberProduct π k) =
      face (Fin.last k) ∘ ⇑(iteratedFiberProductPermDiffeomorph (k + 1) hn hπ σ) := by
    ext y j
    simp [σ, τ, Fin.succAbove_last]
  rw [hface_eq]
  exact hlast.comp ((iteratedFiberProductPermDiffeomorph (k + 1) hn hπ σ).isSubmersion hn0)

end Smooth

end TauCeti.IteratedFiberProduct
