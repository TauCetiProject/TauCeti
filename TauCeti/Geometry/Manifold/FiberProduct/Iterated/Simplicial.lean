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

For `π : Y → M`, `a ↦ IteratedFiberProduct π (a + 1)` forms the Čech nerve of `π` via
`mapSimplex θ := precomp θ.toOrderHom`, with `face` and `degen` satisfying all five simplicial
identities. When `π` is a `C^n` submersion (`1 ≤ n`) between boundaryless finite-dimensional real
manifolds and `k ≥ 1`, every `face i` is a surjective `C^n` submersion and every `degen i` is a
`C^n` smooth embedding.

## References
* M. K. Murray, *Bundle gerbes*, J. London Math. Soc. (2) 54 (1996), 403–416, §2.
-/

public section

noncomputable section

open CategoryTheory Function
open scoped Manifold ContDiff Simplicial

namespace TauCeti.IteratedFiberProduct

section Combinatorial

variable {Y M : Type*} {π : Y → M}

/-- Contravariant Čech nerve action of `θ : ⦋a⦌ ⟶ ⦋b⦌` in `SimplexCategory` on
`IteratedFiberProduct π`. -/
def mapSimplex {a b : ℕ} (θ : ⦋a⦌ ⟶ ⦋b⦌) :
    IteratedFiberProduct π (b + 1) → IteratedFiberProduct π (a + 1) :=
  precomp θ.toOrderHom

@[simp] theorem proj_mapSimplex {a b : ℕ} (θ : ⦋a⦌ ⟶ ⦋b⦌) (y : IteratedFiberProduct π (b + 1))
    (i : Fin (a + 1)) : proj i (mapSimplex θ y) = proj (θ.toOrderHom i) y :=
  proj_precomp θ.toOrderHom y i
@[simp] theorem baseProj_mapSimplex {a b : ℕ} (θ : ⦋a⦌ ⟶ ⦋b⦌)
    (y : IteratedFiberProduct π (b + 1)) : baseProj (mapSimplex θ y) = baseProj y :=
  baseProj_precomp θ.toOrderHom y
@[simp] theorem mapSimplex_id {a : ℕ} (y : IteratedFiberProduct π (a + 1)) :
    mapSimplex (𝟙 ⦋a⦌) y = y := precomp_id y
theorem mapSimplex_comp {a b c : ℕ} (θ₁ : ⦋a⦌ ⟶ ⦋b⦌) (θ₂ : ⦋b⦌ ⟶ ⦋c⦌) :
    mapSimplex (π := π) (θ₁ ≫ θ₂) = mapSimplex θ₁ ∘ mapSimplex θ₂ := by ext y i; simp [mapSimplex]

/-- The `i`-th simplicial face map `IteratedFiberProduct π (k + 1) → IteratedFiberProduct π k`. -/
def face {k : ℕ} (i : Fin (k + 1)) :
    IteratedFiberProduct π (k + 1) → IteratedFiberProduct π k := precomp i.succAbove

/-- The `i`-th simplicial degeneracy map
`IteratedFiberProduct π k → IteratedFiberProduct π (k + 1)`. -/
def degen {k : ℕ} (i : Fin k) :
    IteratedFiberProduct π k → IteratedFiberProduct π (k + 1) := precomp i.predAbove

@[simp] theorem proj_face {k : ℕ} (i : Fin (k + 1)) (y : IteratedFiberProduct π (k + 1))
    (j : Fin k) : proj j (face i y) = proj (i.succAbove j) y := proj_precomp i.succAbove y j
@[simp] theorem proj_degen {k : ℕ} (i : Fin k) (y : IteratedFiberProduct π k) (j : Fin (k + 1)) :
    proj j (degen i y) = proj (i.predAbove j) y := proj_precomp i.predAbove y j
@[simp] theorem baseProj_face {k : ℕ} [NeZero k] (i : Fin (k + 1))
    (y : IteratedFiberProduct π (k + 1)) : baseProj (face i y) = baseProj y :=
  baseProj_precomp i.succAbove y
@[simp] theorem baseProj_degen {k : ℕ} [NeZero k] (i : Fin k) (y : IteratedFiberProduct π k) :
    baseProj (degen i y) = baseProj y := baseProj_precomp i.predAbove y
@[simp] theorem mapSimplex_δ {a : ℕ} (i : Fin (a + 2)) :
    mapSimplex (π := π) (SimplexCategory.δ i) = face i := (rfl)
@[simp] theorem mapSimplex_σ {a : ℕ} (i : Fin (a + 1)) :
    mapSimplex (π := π) (SimplexCategory.σ i) = degen i := (rfl)

theorem face_comp_face {k : ℕ} {i j : Fin (k + 1)} (h : i ≤ j) :
    face i ∘ face (π := π) j.succ = face j ∘ face i.castSucc := by
  rcases k with _ | a; · funext y; exact ext fun x ↦ x.elim0
  simp only [← mapSimplex_δ, ← mapSimplex_comp]
  exact congrArg (mapSimplex (π := π)) (SimplexCategory.δ_comp_δ h)

theorem face_comp_degen_of_le {k : ℕ} {i : Fin (k + 1)} {j : Fin k} (h : i ≤ j.castSucc) :
    face i.castSucc ∘ degen (π := π) j.succ = degen j ∘ face i := by
  rcases k with _ | a; · exact j.elim0
  simp only [← mapSimplex_δ, ← mapSimplex_σ, ← mapSimplex_comp]
  exact congrArg (mapSimplex (π := π)) (SimplexCategory.δ_comp_σ_of_le h)

theorem face_castSucc_comp_degen {k : ℕ} (i : Fin k) :
    face i.castSucc ∘ degen (π := π) i = id := by
  rcases k with _ | a; · exact i.elim0
  simp only [← mapSimplex_δ, ← mapSimplex_σ, ← mapSimplex_comp]
  exact funext fun y ↦ (congrFun (congrArg (mapSimplex (π := π))
    (SimplexCategory.δ_comp_σ_self (i := i))) y).trans (mapSimplex_id y)

theorem face_succ_comp_degen {k : ℕ} (i : Fin k) :
    face i.succ ∘ degen (π := π) i = id := by
  rcases k with _ | a; · exact i.elim0
  simp only [← mapSimplex_δ, ← mapSimplex_σ, ← mapSimplex_comp]
  exact funext fun y ↦ (congrFun (congrArg (mapSimplex (π := π))
    (SimplexCategory.δ_comp_σ_succ (i := i))) y).trans (mapSimplex_id y)

theorem face_comp_degen_of_gt {k : ℕ} {i : Fin (k + 1)} {j : Fin k} (h : j.castSucc < i) :
    face i.succ ∘ degen (π := π) j.castSucc = degen j ∘ face i := by
  rcases k with _ | a; · exact j.elim0
  simp only [← mapSimplex_δ, ← mapSimplex_σ, ← mapSimplex_comp]
  exact congrArg (mapSimplex (π := π)) (SimplexCategory.δ_comp_σ_of_gt h)

theorem degen_comp_degen {k : ℕ} {i j : Fin k} (h : i ≤ j) :
    degen i.castSucc ∘ degen (π := π) j = degen j.succ ∘ degen i := by
  rcases k with _ | a; · exact i.elim0
  simp only [← mapSimplex_σ, ← mapSimplex_comp]
  exact congrArg (mapSimplex (π := π)) (SimplexCategory.σ_comp_σ h)

theorem surjective_face {k : ℕ} [NeZero k] (i : Fin (k + 1)) :
    Surjective (face i : IteratedFiberProduct π (k + 1) → IteratedFiberProduct π k) := by
  rcases k with _ | a; · exact False.elim (NeZero.ne 0 rfl)
  exact Fin.lastCases
    (LeftInverse.surjective (congrFun (face_succ_comp_degen (π := π) (Fin.last a))))
    (fun j ↦ LeftInverse.surjective (congrFun (face_castSucc_comp_degen (π := π) j))) i

end Combinatorial

section Smooth

variable {EY HY Y EM HM M : Type*}
  [NormedAddCommGroup EY] [NormedSpace ℝ EY] [TopologicalSpace HY]
  [NormedAddCommGroup EM] [NormedSpace ℝ EM] [TopologicalSpace HM]
  {IY : ModelWithCorners ℝ EY HY} {IM : ModelWithCorners ℝ EM HM}
  [TopologicalSpace Y] [ChartedSpace HY Y] [TopologicalSpace M] [ChartedSpace HM M]
  {n : ℕ∞ω} [IsManifold IY n Y] [IsManifold IM n M] [IY.Boundaryless] [IM.Boundaryless]
  [FiniteDimensional ℝ EY] [FiniteDimensional ℝ EM] {π : Y → M}

theorem contMDiff_mapSimplex {a b : ℕ} (hn : 1 ≤ n) (hπ : Manifold.IsSubmersion IY IM n π)
    {m : ℕ∞ω} (hmn : m ≤ n) (θ : ⦋a⦌ ⟶ ⦋b⦌) :
    letI := iteratedFiberProductChartedSpace (a + 1) hn hπ
    letI := iteratedFiberProductChartedSpace (b + 1) hn hπ
    ContMDiff 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM (b + 1)) → ℝ)
      𝓘(ℝ, Fin (iteratedFiberProductDim EY EM (a + 1)) → ℝ) m (mapSimplex (π := π) θ) :=
  contMDiff_precomp hn hπ hmn θ.toOrderHom

theorem contMDiff_face {k : ℕ} [NeZero k] (hn : 1 ≤ n) (hπ : Manifold.IsSubmersion IY IM n π)
    {m : ℕ∞ω} (hmn : m ≤ n) (i : Fin (k + 1)) :
    letI := iteratedFiberProductChartedSpace k hn hπ
    letI := iteratedFiberProductChartedSpace (k + 1) hn hπ
    ContMDiff 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM (k + 1)) → ℝ)
      𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ) m (face (π := π) i) :=
  contMDiff_precomp hn hπ hmn i.succAbove

theorem contMDiff_degen {k : ℕ} [NeZero k] (hn : 1 ≤ n) (hπ : Manifold.IsSubmersion IY IM n π)
    {m : ℕ∞ω} (hmn : m ≤ n) (i : Fin k) :
    letI := iteratedFiberProductChartedSpace k hn hπ
    letI := iteratedFiberProductChartedSpace (k + 1) hn hπ
    ContMDiff 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ)
      𝓘(ℝ, Fin (iteratedFiberProductDim EY EM (k + 1)) → ℝ) m (degen (π := π) i) :=
  contMDiff_precomp hn hπ hmn i.predAbove

theorem contMDiff_constDiagonal (k : ℕ) [NeZero k] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) {m : ℕ∞ω} (hmn : m ≤ n) :
    letI := iteratedFiberProductChartedSpace k hn hπ
    ContMDiff IY 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ) m
      (fun y : Y ↦ constDiagonal (π := π) y k) := by
  let := iteratedFiberProductChartedSpace k hn hπ
  exact (contMDiff_iteratedFiberProduct_iff hn hπ hmn).2 fun _ ↦ by
    simp only [proj_constDiagonal]; rw [← Function.id_def]; exact contMDiff_id

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

theorem isSmoothEmbedding_constDiagonal (k : ℕ) [NeZero k] (hn : 1 ≤ n)
    (hπ : Manifold.IsSubmersion IY IM n π) :
    letI := iteratedFiberProductChartedSpace k hn hπ
    Manifold.IsSmoothEmbedding IY 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ) n
      (fun y : Y ↦ constDiagonal (π := π) y k) := by
  let := iteratedFiberProductChartedSpace k hn hπ; have := isManifold_iteratedFiberProduct k hn hπ
  exact (contMDiff_constDiagonal k hn hπ le_rfl).isSmoothEmbedding_of_leftInverse hn
    (contMDiff_proj_iteratedFiberProduct k hn hπ hn 0) fun y ↦ proj_constDiagonal y k 0

/-- Every simplicial face map `face i` (`k ≥ 1`) is a `C^n` submersion. -/
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
  have hsubk := isSubmersion_baseProj_iteratedFiberProduct k hn hπ
  let htrans := fun (p : IteratedFiberProduct π k × Y) (_ : baseProj p.1 = π p.2) ↦
    hsubk.transverse_left (IY := IY) hn0 π p
  let := transverseFiberProductChartedSpace hn hsubk.contMDiff hπ.contMDiff htrans
  have := isManifold_transverseFiberProduct hn hsubk.contMDiff hπ.contMDiff htrans
  have hfst := isSubmersion_fst_transverseFiberProduct hn hsubk.contMDiff hπ.contMDiff htrans hπ
  have hlast_eq : (face (Fin.last k) : IteratedFiberProduct π (k + 1) → IteratedFiberProduct π k) =
      (fun p ↦ p.1.1) ∘ ⇑(iteratedFiberProductSuccRightDiffeomorph k hn hπ) := by
    ext y j; simp [Fin.succAbove_last]
  have hlast : Manifold.IsSubmersion 𝓘(ℝ, Fin (iteratedFiberProductDim EY EM (k + 1)) → ℝ)
      𝓘(ℝ, Fin (iteratedFiberProductDim EY EM k) → ℝ) n (face (π := π) (Fin.last k)) :=
    hlast_eq ▸ hfst.comp ((iteratedFiberProductSuccRightDiffeomorph k hn hπ).isSubmersion hn0)
  let τ : Fin (k + 1) → Fin (k + 1) := Fin.lastCases i i.succAbove
  have hτ_inj : Injective τ := fun a b ↦ by
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
    ext y j; simp [σ, τ, Fin.succAbove_last]
  rw [hface_eq]
  exact hlast.comp ((iteratedFiberProductPermDiffeomorph (k + 1) hn hπ σ).isSubmersion hn0)

end Smooth

end TauCeti.IteratedFiberProduct
