/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.Analysis.Convex.SimplicialComplex.Basic
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import TauCeti.Analysis.Analytic.Submanifold.Basic
public import TauCeti.Analysis.Convex.StdSimplex
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Topology.Algebra.Module.Basic
import TauCeti.Analysis.Analytic.Submanifold.Transport
import TauCeti.Analysis.Convex.OpenSimplex
import TauCeti.Analysis.Convex.SimplicialComplex.Carrier

/-!
# Affine subspaces, intrinsic interiors, and open simplices as analytic submanifolds

Over any nontrivially normed field `𝕜`, every linear subspace `W` of `Fin n → 𝕜` is an analytic
submanifold of dimension `Module.finrank 𝕜 W`, every nonempty affine subspace `A` is an analytic
submanifold of dimension `Module.finrank 𝕜 A.direction`, and every nonempty intrinsic interior
`intrinsicInterior 𝕜 s` is an analytic submanifold of dimension `Module.finrank 𝕜 (vectorSpan 𝕜 s)`.
No completeness assumption on `𝕜` is needed: any linear equivalence of `Fin n → 𝕜` is continuous
in both directions because `Fin n → 𝕜` carries the product topology (`LinearMap.continuous_on_pi`).

Over `ℝ`, this equips every nonempty open simplex — the intrinsic interior of the convex hull of a
nonempty finite affinely independent family — with the structure of an analytic submanifold of
dimension one less than its number of vertices, and in particular makes the open standard simplex
in `Fin m → ℝ` (`m ≥ 1`) an `(m - 1)`-dimensional analytic submanifold and each of its open facets
(`m ≥ 2`) an `(m - 2)`-dimensional analytic submanifold.

## Main results

* `Submodule.isAnalyticSubmanifold`: a linear subspace `W ≤ (Fin n → 𝕜)` is a
  `(Module.finrank 𝕜 W)`-dimensional analytic submanifold.
* `AffineSubspace.isAnalyticSubmanifold`: a nonempty affine subspace `A` of `Fin n → 𝕜` is a
  `(Module.finrank 𝕜 A.direction)`-dimensional analytic submanifold.
* `TauCeti.isAnalyticSubmanifold_intrinsicInterior`: a nonempty intrinsic interior
  `intrinsicInterior 𝕜 s` in `Fin n → 𝕜` is a `(Module.finrank 𝕜 (vectorSpan 𝕜 s))`-dimensional
  analytic submanifold.
* `AffineIndependent.isAnalyticSubmanifold_intrinsicInterior_convexHull`,
  `Geometry.SimplicialComplex.isAnalyticSubmanifold_intrinsicInterior_convexHull`: open simplices
  are analytic submanifolds of dimension `card - 1`.
* `TauCeti.isAnalyticSubmanifold_openStdSimplex`,
  `TauCeti.isAnalyticSubmanifold_openStdSimplexFacet`: the open standard simplex in `Fin m → ℝ`
  and its open facets are analytic submanifolds of dimensions `m - 1` and `m - 2`.

## References

* S. G. Krantz and H. R. Parks, *A Primer of Real Analytic Functions*, second edition,
  Birkhäuser, 2002, Chapter 2 (real analytic submanifolds).
* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Annali della Scuola Normale Superiore di
  Pisa (3) 18 (1964), 449–474, §4 (analytic open simplices).
-/

public section

open Set Topology Convexity

section NormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n d : ℕ}

/-- Block concatenation `((Fin d → 𝕜) × (Fin (n - d) → 𝕜)) ≃ₗ[𝕜] (Fin n → 𝕜)` placing the first
factor in coordinates `< d` and the second factor in coordinates `≥ d`. -/
private def joinCoordsLinearEquiv (hd : d ≤ n) :
    ((Fin d → 𝕜) × (Fin (n - d) → 𝕜)) ≃ₗ[𝕜] Fin n → 𝕜 where
  toFun p i := if h : i.val < d then p.1 ⟨i.val, h⟩ else p.2 ⟨i.val - d, by omega⟩
  map_add' p q := by ext i; dsimp; split_ifs <;> rfl
  map_smul' c p := by ext i; dsimp; split_ifs <;> rfl
  invFun y := (fun j ↦ y ⟨j.val, j.isLt.trans_le hd⟩, fun k ↦ y ⟨d + k.val, by omega⟩)
  left_inv p := Prod.ext
    (funext fun j ↦ by simp [j.isLt])
    (funext fun k ↦ by
      have hlt : ¬ d + k.val < d := by omega
      simp [hlt])
  right_inv y := funext fun i ↦ by
    dsimp
    split_ifs with h
    · rfl
    · congr 1; ext; dsimp; omega

/-- Every linear subspace `W` of `Fin n → 𝕜` is an analytic submanifold of dimension
`Module.finrank 𝕜 W`. -/
theorem Submodule.isAnalyticSubmanifold (W : Submodule 𝕜 (Fin n → 𝕜)) :
    TauCeti.IsAnalyticSubmanifold (Module.finrank 𝕜 W) (W : Set (Fin n → 𝕜)) := by
  set d := Module.finrank 𝕜 W
  have hd : d ≤ n := by simpa using W.finrank_le
  obtain ⟨Q, hWQ⟩ := W.exists_isCompl
  have hdimQ : Module.finrank 𝕜 Q = n - d := by
    have hsum : d + Module.finrank 𝕜 Q = n := by
      simpa [d] using Submodule.finrank_add_eq_of_isCompl hWQ
    omega
  let bW : Module.Basis (Fin d) 𝕜 W := Module.finBasis 𝕜 W
  let bQ : Module.Basis (Fin (n - d)) 𝕜 Q := Module.finBasisOfFinrankEq 𝕜 Q hdimQ
  -- Decompose `Fin n → 𝕜` along `W × Q` and place `W` in the first `d` coordinates and `Q` in the
  -- remaining `n - d` coordinates.
  let L : (Fin n → 𝕜) ≃ₗ[𝕜] Fin n → 𝕜 :=
    ((Submodule.prodEquivOfIsCompl W Q hWQ).symm.trans
      (bW.equivFun.prodCongr bQ.equivFun)).trans (joinCoordsLinearEquiv hd)
  let e : (Fin n → 𝕜) ≃L[𝕜] Fin n → 𝕜 :=
    { L with
      continuous_toFun := L.toLinearMap.continuous_on_pi
      continuous_invFun := L.symm.toLinearMap.continuous_on_pi }
  have hpre : e ⁻¹' {y : Fin n → 𝕜 | ∀ i : Fin n, d ≤ i.val → y i = 0} =
      (W : Set (Fin n → 𝕜)) := by
    ext x
    simp only [mem_preimage, mem_ofPred_eq, SetLike.mem_coe]
    constructor
    · intro hx
      have hQ0 : bQ.equivFun ((Submodule.prodEquivOfIsCompl W Q hWQ).symm x).2 = 0 := by
        ext k
        have hk : d ≤ (⟨d + k.val, by omega⟩ : Fin n).val := by simp
        have hlt : ¬ d + k.val < d := by omega
        simpa [e, L, joinCoordsLinearEquiv, hlt] using hx ⟨d + k.val, by omega⟩ hk
      have hxQ : ((Submodule.prodEquivOfIsCompl W Q hWQ).symm x).2 = 0 :=
        bQ.equivFun.injective (by simpa using hQ0)
      have hrepr : x = (((Submodule.prodEquivOfIsCompl W Q hWQ).symm x).1 : Fin n → 𝕜) +
          (((Submodule.prodEquivOfIsCompl W Q hWQ).symm x).2 : Fin n → 𝕜) := by
        simpa using ((Submodule.prodEquivOfIsCompl W Q hWQ).apply_symm_apply x).symm
      rw [hrepr, hxQ, ZeroMemClass.coe_zero, add_zero]
      exact ((Submodule.prodEquivOfIsCompl W Q hWQ).symm x).1.2
    · intro hxW i hi
      have hlt : ¬ i.val < d := not_lt.2 hi
      have hpair : (Submodule.prodEquivOfIsCompl W Q hWQ).symm x = (⟨x, hxW⟩, 0) :=
        (Submodule.prodEquivOfIsCompl W Q hWQ).symm_apply_eq.2 (by simp)
      simp [e, L, joinCoordsLinearEquiv, hlt, hpair]
  rw [← hpre]
  exact (TauCeti.isAnalyticSubmanifold_coordSubspace hd).preimage_continuousLinearEquiv e

/-- Translating an analytic submanifold of `Fin n → 𝕜` preserves its analytic submanifold
structure and dimension. -/
theorem TauCeti.IsAnalyticSubmanifold.add_left {S : Set (Fin n → 𝕜)}
    (hS : TauCeti.IsAnalyticSubmanifold d S) (a : Fin n → 𝕜) :
    TauCeti.IsAnalyticSubmanifold d ((a + ·) '' S) := by
  have himg : (a + ·) '' S = (Homeomorph.addLeft (-a)) ⁻¹' S := by
    ext y
    simp
  rw [himg]
  exact hS.preimage (Homeomorph.addLeft (-a))
    (fun _ _ ↦ analyticAt_const.add analyticAt_id)
    (fun _ _ ↦ analyticAt_const.add analyticAt_id)

/-- Every nonempty affine subspace `A` of `Fin n → 𝕜` is an analytic submanifold of dimension
`Module.finrank 𝕜 A.direction`. -/
theorem AffineSubspace.isAnalyticSubmanifold {A : AffineSubspace 𝕜 (Fin n → 𝕜)}
    (hA : (A : Set (Fin n → 𝕜)).Nonempty) :
    TauCeti.IsAnalyticSubmanifold (Module.finrank 𝕜 A.direction) (A : Set (Fin n → 𝕜)) := by
  obtain ⟨x₀, hx₀⟩ := hA
  have htran : (A : Set (Fin n → 𝕜)) = (x₀ + ·) '' (A.direction : Set (Fin n → 𝕜)) := by
    ext x
    constructor
    · intro hx
      refine ⟨x - x₀, ?_, add_sub_cancel x₀ x⟩
      simpa [vsub_eq_sub] using AffineSubspace.vsub_mem_direction hx hx₀
    · rintro ⟨v, hv, rfl⟩
      simpa [vadd_eq_add, add_comm x₀ v] using AffineSubspace.vadd_mem_of_mem_direction hv hx₀
  rw [htran]
  exact A.direction.isAnalyticSubmanifold.add_left x₀

/-- Every nonempty intrinsic interior `intrinsicInterior 𝕜 s` in `Fin n → 𝕜` is an analytic
submanifold of dimension `Module.finrank 𝕜 (vectorSpan 𝕜 s)`. -/
theorem TauCeti.isAnalyticSubmanifold_intrinsicInterior {s : Set (Fin n → 𝕜)}
    (hne : (intrinsicInterior 𝕜 s).Nonempty) :
    TauCeti.IsAnalyticSubmanifold (Module.finrank 𝕜 (vectorSpan 𝕜 s))
      (intrinsicInterior 𝕜 s) := by
  have hsub : intrinsicInterior 𝕜 s ⊆ (affineSpan 𝕜 s : Set (Fin n → 𝕜)) := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hA : TauCeti.IsAnalyticSubmanifold (Module.finrank 𝕜 (vectorSpan 𝕜 s))
      (affineSpan 𝕜 s : Set (Fin n → 𝕜)) := by
    rw [← direction_affineSpan]
    exact (affineSpan 𝕜 s).isAnalyticSubmanifold (hne.mono hsub)
  refine hA.of_isOpen_preimage_val hsub ?_ hne
  convert isOpen_interior (s := ((↑) : affineSpan 𝕜 s → Fin n → 𝕜) ⁻¹' s) using 1
  ext y
  simp [intrinsicInterior]

end NormedField

section RealSimplex

variable {n m : ℕ}

/-- **Open simplices are analytic submanifolds.** The intrinsic interior of the convex hull of a
nonempty finite affinely independent family `p : ι → Fin n → ℝ` is an analytic submanifold of
dimension `Fintype.card ι - 1`. -/
theorem AffineIndependent.isAnalyticSubmanifold_intrinsicInterior_convexHull
    {ι : Type*} [Fintype ι] [Nonempty ι] {p : ι → Fin n → ℝ} (hp : AffineIndependent ℝ p) :
    TauCeti.IsAnalyticSubmanifold (Fintype.card ι - 1)
      (intrinsicInterior ℝ (convexHull ℝ (range p))) := by
  have hdim : Module.finrank ℝ (vectorSpan ℝ (convexHull ℝ (range p))) = Fintype.card ι - 1 := by
    rw [← direction_affineSpan, affineSpan_convexHull, direction_affineSpan]
    exact hp.finrank_vectorSpan
      (Nat.sub_add_cancel (Nat.succ_le_iff.2 Fintype.card_pos)).symm
  rw [← hdim]
  exact TauCeti.isAnalyticSubmanifold_intrinsicInterior
    ⟨_, hp.centroid_mem_intrinsicInterior_convexHull⟩

/-- Every open face of a geometric simplicial complex in `Fin n → ℝ` is an analytic submanifold of
dimension `s.card - 1`. -/
theorem Geometry.SimplicialComplex.isAnalyticSubmanifold_intrinsicInterior_convexHull
    {K : Geometry.SimplicialComplex ℝ (Fin n → ℝ)} {s : Finset (Fin n → ℝ)} (hs : s ∈ K.faces) :
    TauCeti.IsAnalyticSubmanifold (s.card - 1)
      (intrinsicInterior ℝ (convexHull ℝ (s : Set (Fin n → ℝ)))) := by
  have : Nonempty s := (K.nonempty_of_mem_faces hs).coe_sort
  have hrange : (s : Set (Fin n → ℝ)) = range ((↑) : s → Fin n → ℝ) := by simp
  rw [hrange, ← Fintype.card_coe]
  exact (K.indep hs).isAnalyticSubmanifold_intrinsicInterior_convexHull

namespace TauCeti

/-- For a nonempty set `t` of coordinates of `Fin m`, the open coordinate face of the standard
simplex spanned by `t` is a `(t.card - 1)`-dimensional analytic submanifold. -/
theorem isAnalyticSubmanifold_intrinsicInterior_convexHull_pi_single
    {t : Finset (Fin m)} (ht : t.Nonempty) :
    IsAnalyticSubmanifold (t.card - 1)
      (intrinsicInterior ℝ
        (convexHull ℝ ((fun i : Fin m => (Pi.single i 1 : Fin m → ℝ)) '' t))) := by
  have : Nonempty (t : Set (Fin m)) := ht.coe_sort
  have himg : (fun i : Fin m => (Pi.single i 1 : Fin m → ℝ)) '' (t : Set (Fin m)) =
      range (fun j : (t : Set (Fin m)) => (Pi.single (j : Fin m) 1 : Fin m → ℝ)) := by
    ext x
    simp
  have hcard : Fintype.card (t : Set (Fin m)) = t.card := Fintype.card_coe t
  rw [himg, ← hcard]
  exact (affineIndependent_pi_single
    (t : Set (Fin m))).isAnalyticSubmanifold_intrinsicInterior_convexHull

/-- The open standard simplex `{x ∈ range weights | ∀ i, 0 < x i}` in `Fin m → ℝ` (`m ≥ 1`) is an
`(m - 1)`-dimensional analytic submanifold. -/
theorem isAnalyticSubmanifold_openStdSimplex [NeZero m] :
    IsAnalyticSubmanifold (m - 1)
      {x ∈ range fun s : StdSimplex ℝ (Fin m) => ⇑s.weights | ∀ i, 0 < x i} := by
  rw [← intrinsicInterior_range_stdSimplex_weights, ← convexHull_range_pi_single, ← image_univ]
  simpa using isAnalyticSubmanifold_intrinsicInterior_convexHull_pi_single
    (t := (Finset.univ : Finset (Fin m))) Finset.univ_nonempty

/-- For `m ≥ 2`, the `i`-th open facet `{y ∈ range weights | y i = 0 ∧ ∀ j ≠ i, 0 < y j}` of the
standard simplex in `Fin m → ℝ` is an `(m - 2)`-dimensional analytic submanifold. -/
theorem isAnalyticSubmanifold_openStdSimplexFacet [Nontrivial (Fin m)] (i : Fin m) :
    IsAnalyticSubmanifold (m - 2)
      {y ∈ range fun s : StdSimplex ℝ (Fin m) => ⇑s.weights | y i = 0 ∧ ∀ j ≠ i, 0 < y j} := by
  obtain ⟨j, hj⟩ := exists_ne i
  have hne : (Finset.univ.erase i).Nonempty := ⟨j, Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩⟩
  have hcard : (Finset.univ.erase i).card - 1 = m - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_fin]
    omega
  rw [← intrinsicInterior_facet_stdSimplex_weights, ← convexHull_pi_single_compl_singleton,
    ← hcard]
  have hcoe : ((Finset.univ.erase i : Finset (Fin m)) : Set (Fin m)) = {i}ᶜ := by
    ext k
    simp
  rw [← hcoe]
  exact isAnalyticSubmanifold_intrinsicInterior_convexHull_pi_single hne

end TauCeti

end RealSimplex
