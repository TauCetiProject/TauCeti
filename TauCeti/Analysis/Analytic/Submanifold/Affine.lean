/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import TauCeti.Analysis.Analytic.Submanifold.Basic
public import TauCeti.Analysis.Convex.StdSimplex
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Topology.Algebra.Module.Basic
import TauCeti.Analysis.Analytic.Submanifold.Transport
import TauCeti.Analysis.Convex.Intrinsic
import TauCeti.Analysis.Convex.OpenSimplex

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
dimension one less than its number of vertices, and in particular makes `TauCeti.openStdSimplex ℝ`
in `Fin m → ℝ` (`m ≥ 1`) an `(m - 1)`-dimensional analytic submanifold and each open facet
`TauCeti.openStdSimplexFacet ℝ i` (`m ≥ 2`) an `(m - 2)`-dimensional analytic submanifold.

## Main results

* `Submodule.isAnalyticSubmanifold`: a linear subspace `W ≤ (Fin n → 𝕜)` is a
  `(Module.finrank 𝕜 W)`-dimensional analytic submanifold.
* `AffineSubspace.isAnalyticSubmanifold`: a nonempty affine subspace `A` of `Fin n → 𝕜` is a
  `(Module.finrank 𝕜 A.direction)`-dimensional analytic submanifold.
* `TauCeti.isAnalyticSubmanifold_intrinsicInterior`: a nonempty intrinsic interior
  `intrinsicInterior 𝕜 s` in `Fin n → 𝕜` is a `(Module.finrank 𝕜 (vectorSpan 𝕜 s))`-dimensional
  analytic submanifold.
* `AffineIndependent.isAnalyticSubmanifold_intrinsicInterior_convexHull`: open simplices in
  `Fin n → ℝ` are analytic submanifolds of dimension `Fintype.card ι - 1`.
* `TauCeti.isAnalyticSubmanifold_openStdSimplex`,
  `TauCeti.isAnalyticSubmanifold_openStdSimplexFacet`: `TauCeti.openStdSimplex ℝ (Fin m)` and
  `TauCeti.openStdSimplexFacet ℝ i` are analytic submanifolds of dimensions `m - 1` and `m - 2`.

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

/-- Every linear subspace `W` of `Fin n → 𝕜` is the preimage of the coordinate subspace
`{y | ∀ i : Fin n, Module.finrank 𝕜 W ≤ i.val → y i = 0}` under a continuous linear equivalence
of `Fin n → 𝕜`. -/
private theorem exists_continuousLinearEquiv_preimage_coordSubspace
    (W : Submodule 𝕜 (Fin n → 𝕜)) :
    ∃ e : (Fin n → 𝕜) ≃L[𝕜] Fin n → 𝕜,
      e ⁻¹' {y : Fin n → 𝕜 | ∀ i : Fin n, Module.finrank 𝕜 W ≤ i.val → y i = 0} =
        (W : Set (Fin n → 𝕜)) := by
  set d := Module.finrank 𝕜 W
  have hd : d ≤ n := by simpa using W.finrank_le
  obtain ⟨Q, hWQ⟩ := W.exists_isCompl
  have hdimQ : Module.finrank 𝕜 Q = n - d := by
    have hsum : d + Module.finrank 𝕜 Q = n := by
      simpa [d] using Submodule.finrank_add_eq_of_isCompl hWQ
    omega
  let bW : Module.Basis (Fin d) 𝕜 W := Module.finBasis 𝕜 W
  let bQ : Module.Basis (Fin (n - d)) 𝕜 Q := Module.finBasisOfFinrankEq 𝕜 Q hdimQ
  -- Decompose `Fin n → 𝕜` along `W × Q`, placing `W` in the first `d` coordinates and `Q` in the
  -- remaining `n - d` coordinates.
  let σ : Fin d ⊕ Fin (n - d) ≃ Fin n :=
    finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' hd))
  let joinCoords : ((Fin d → 𝕜) × (Fin (n - d) → 𝕜)) ≃ₗ[𝕜] Fin n → 𝕜 :=
    (LinearEquiv.sumPiEquivProdPi 𝕜 (Fin d) (Fin (n - d)) (fun _ ↦ 𝕜)).symm ≪≫ₗ
      LinearEquiv.funCongrLeft 𝕜 𝕜 σ.symm
  let p := Submodule.prodEquivOfIsCompl W Q hWQ
  let L : (Fin n → 𝕜) ≃ₗ[𝕜] Fin n → 𝕜 :=
    p.symm ≪≫ₗ (bW.equivFun.prodCongr bQ.equivFun) ≪≫ₗ joinCoords
  let e : (Fin n → 𝕜) ≃L[𝕜] Fin n → 𝕜 :=
    { L with
      continuous_toFun := L.toLinearMap.continuous_on_pi
      continuous_invFun := L.symm.toLinearMap.continuous_on_pi }
  refine ⟨e, ?_⟩
  ext x
  simp only [mem_preimage, mem_ofPred_eq, SetLike.mem_coe]
  rw [← σ.forall_congr_right, Sum.forall]
  have hinl : ∀ j : Fin d, d ≤ (σ (Sum.inl j)).val → e x (σ (Sum.inl j)) = 0 := fun j hj ↦ by
    have : (σ (Sum.inl j)).val < d := by simp [σ]
    omega
  have hinr : (∀ k : Fin (n - d), d ≤ (σ (Sum.inr k)).val → e x (σ (Sum.inr k)) = 0) ↔
      (p.symm x).2 = 0 := by
    have hcoord (k : Fin (n - d)) : e x (σ (Sum.inr k)) = bQ.equivFun (p.symm x).2 k := by
      simp [e, L, joinCoords]
    simp_rw [show ∀ k : Fin (n - d), d ≤ (σ (Sum.inr k)).val from fun k ↦ by simp [σ],
      true_implies, hcoord, ← funext_iff, ← Pi.zero_def, ← map_zero bQ.equivFun,
      bQ.equivFun.injective.eq_iff]
  rw [and_iff_right hinl, hinr]
  constructor
  · intro hxQ
    have hrepr : x = ((p.symm x).1 : Fin n → 𝕜) + ((p.symm x).2 : Fin n → 𝕜) := by
      simpa [p] using (p.apply_symm_apply x).symm
    rw [hrepr, hxQ, ZeroMemClass.coe_zero, add_zero]
    exact (p.symm x).1.2
  · intro hxW
    have hpair : p.symm x = (⟨x, hxW⟩, 0) := p.symm_apply_eq.2 (by simp [p])
    simp [hpair]

/-- Every linear subspace `W` of `Fin n → 𝕜` is an analytic submanifold of dimension
`Module.finrank 𝕜 W`. -/
theorem Submodule.isAnalyticSubmanifold (W : Submodule 𝕜 (Fin n → 𝕜)) :
    TauCeti.IsAnalyticSubmanifold (Module.finrank 𝕜 W) (W : Set (Fin n → 𝕜)) := by
  obtain ⟨e, he⟩ := exists_continuousLinearEquiv_preimage_coordSubspace W
  exact he ▸ (TauCeti.isAnalyticSubmanifold_coordSubspace
    (by simpa using W.finrank_le)).preimage_continuousLinearEquiv e

/-- Every nonempty affine subspace `A` of `Fin n → 𝕜` is an analytic submanifold of dimension
`Module.finrank 𝕜 A.direction`. -/
theorem AffineSubspace.isAnalyticSubmanifold {A : AffineSubspace 𝕜 (Fin n → 𝕜)}
    (hA : (A : Set (Fin n → 𝕜)).Nonempty) :
    TauCeti.IsAnalyticSubmanifold (Module.finrank 𝕜 A.direction) (A : Set (Fin n → 𝕜)) := by
  obtain ⟨x₀, hx₀⟩ := hA
  have htran : (A : Set (Fin n → 𝕜)) = (x₀ + ·) '' (A.direction : Set (Fin n → 𝕜)) := by
    ext x
    refine ⟨fun hx ↦ ⟨x - x₀, (AffineSubspace.vsub_right_mem_direction_iff_mem hx₀ x).2 hx,
      add_sub_cancel x₀ x⟩, ?_⟩
    rintro ⟨v, hv, rfl⟩
    simpa using (AffineSubspace.vsub_right_mem_direction_iff_mem hx₀ (x₀ + v)).1 (by simpa using hv)
  rw [htran]
  exact A.direction.isAnalyticSubmanifold.translate x₀

/-- Every nonempty intrinsic interior `intrinsicInterior 𝕜 s` in `Fin n → 𝕜` is an analytic
submanifold of dimension `Module.finrank 𝕜 (vectorSpan 𝕜 s)`. -/
theorem TauCeti.isAnalyticSubmanifold_intrinsicInterior {s : Set (Fin n → 𝕜)}
    (hne : (intrinsicInterior 𝕜 s).Nonempty) :
    TauCeti.IsAnalyticSubmanifold (Module.finrank 𝕜 (vectorSpan 𝕜 s))
      (intrinsicInterior 𝕜 s) := by
  have hsub : intrinsicInterior 𝕜 s ⊆ (affineSpan 𝕜 s : Set (Fin n → 𝕜)) :=
    TauCeti.intrinsicInterior_subset_affineSpan
  have hA : TauCeti.IsAnalyticSubmanifold (Module.finrank 𝕜 (vectorSpan 𝕜 s))
      (affineSpan 𝕜 s : Set (Fin n → 𝕜)) := by
    rw [← direction_affineSpan]
    exact (affineSpan 𝕜 s).isAnalyticSubmanifold (hne.mono hsub)
  exact hA.of_isOpen_preimage_val hsub TauCeti.isOpen_preimage_val_intrinsicInterior hne

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

namespace TauCeti

/-- For a nonempty set `t` of coordinates of `Fin m`, the open coordinate face of the standard
simplex spanned by `t` is a `(t.card - 1)`-dimensional analytic submanifold. -/
theorem isAnalyticSubmanifold_intrinsicInterior_convexHull_pi_single
    {t : Finset (Fin m)} (ht : t.Nonempty) :
    IsAnalyticSubmanifold (t.card - 1)
      (intrinsicInterior ℝ
        (convexHull ℝ ((fun i : Fin m => (Pi.single i 1 : Fin m → ℝ)) '' t))) := by
  have : Nonempty (t : Set (Fin m)) := ht.coe_sort
  have hcard : Fintype.card (t : Set (Fin m)) = t.card := Fintype.card_coe t
  rw [Set.image_eq_range, ← hcard]
  exact (affineIndependent_pi_single ℝ
    (t : Set (Fin m))).isAnalyticSubmanifold_intrinsicInterior_convexHull

/-- The open standard simplex `openStdSimplex ℝ (Fin m)` (`m ≥ 1`) is an `(m - 1)`-dimensional
analytic submanifold. -/
theorem isAnalyticSubmanifold_openStdSimplex [NeZero m] :
    IsAnalyticSubmanifold (m - 1) (openStdSimplex ℝ (Fin m)) := by
  rw [← intrinsicInterior_range_stdSimplex_weights, ← convexHull_range_pi_single, ← image_univ]
  simpa using isAnalyticSubmanifold_intrinsicInterior_convexHull_pi_single
    (t := (Finset.univ : Finset (Fin m))) Finset.univ_nonempty

/-- For `m ≥ 2`, the `i`-th open facet `openStdSimplexFacet ℝ i` of the standard simplex in
`Fin m → ℝ` is an `(m - 2)`-dimensional analytic submanifold. -/
theorem isAnalyticSubmanifold_openStdSimplexFacet [Nontrivial (Fin m)] (i : Fin m) :
    IsAnalyticSubmanifold (m - 2) (openStdSimplexFacet ℝ i) := by
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
