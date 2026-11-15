/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Connected
public import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
public import TauCeti.Topology.CWComplex.Classical.Product
public import TauCeti.Topology.VectorBundle.Contractible
public import TauCeti.Topology.VectorBundle.Riemannian.Pullback
public import TauCeti.Topology.VectorBundle.SphereBundle.DiscBundle
import TauCeti.Topology.FiberBundle.Pullback

/-!
# Relative CW structures on unit disc-sphere bundle pairs

Let `E → X` be a real vector bundle of rank `r` equipped with a continuous Riemannian metric over a
Hausdorff space `X`, and let `(C, D)` be a classical relative CW complex in `X`. Denote by `D(E)`
and `S(E)` the unit disc and unit sphere subbundles (`TauCeti.discBundle`, `TauCeti.sphereBundle`),
and by `π_D : D(E) → X` the bundle projection (`TauCeti.discBundleProj`).

Pulling back `E` along the characteristic map `Φ_j : D^q → X` of each base `q`-cell `j` produces a
continuous Riemannian vector bundle over the contractible compact cube `D^q`, which is isometric to
`D^q × F` (`TauCeti.exists_homeomorph_prod_of_contractibleSpace`). Combining an orthonormal frame of
`F` with the radial homeomorphism `(EuclideanSpace.equiv (Fin r) ℝ).unitBallHomeomorph.symm` between
the sup-norm cube `D^r` and the Euclidean unit ball, and splitting coordinates via
`Fin.appendIsometryOfEq` (base coordinates first, fibre coordinates last), turns each base `q`-cell
into a `(q + r)`-cell in `D(E)`.

This file constructs the resulting classical relative CW structures:

* `TauCeti.thomCellDimension`: the shifted cell dimension `thomCellDimension r q = q + r`;
* `TauCeti.fibreRadialHomeomorph`: the radial homeomorphism `(Fin r → ℝ) ≃ₜ F` sending the sup-norm
  open ball, closed ball, and sphere onto those of `F` (including the rank-zero case `r = 0`);
* `TauCeti.bundleDiskSphereRelCWOver`: the relative CW structure on `π_D ⁻¹' C` relative to
  `(S(E) ∩ π_D ⁻¹' C) ∪ π_D ⁻¹' D` in the ambient subtype `D(E)`;
* `TauCeti.bundleDiskSphereRelCW`: the primary specialization to `C = univ` relative to a closed
  CW subcomplex `A ⊆ X`, giving `RelCWComplex univ (Subtype.val ⁻¹' S(E) ∪ π_D ⁻¹' A)` on `D(E)`;
* `TauCeti.bundleDiskSphereCellEquiv`: identification of the `(q + r)`-cells of
  `(D(E), S(E) ∪ D(E)|_A)` with the `q`-cells of `(X, A)`, together with vanishing of `n`-cells for
  `n < r` and explicit formulas for open cells, closed cells, and cell frontiers;
* preservation of `RelCWComplex.FiniteDimensional`, `RelCWComplex.FiniteType`, and
  `RelCWComplex.Finite`.

The construction requires no orientation on `E`.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, §10.
* A. Hatcher, *Vector Bundles and K-Theory*, §1.1 and §4.D.
-/

public section

noncomputable section

open Bundle Filter Metric Set Topology Topology.RelCWComplex

universe u

namespace TauCeti

/-! ### Shifted cell dimension and radial fibre homeomorphism -/

/-- Dimension of the bundle cell of `(D(E), S(E))` lying over a base `q`-cell of a rank-`r` real
vector bundle `E`: base dimension `q` plus fibre rank `r`. -/
@[expose]
def thomCellDimension (r q : ℕ) : ℕ :=
  q + r

@[simp]
theorem thomCellDimension_zero_left (q : ℕ) : thomCellDimension 0 q = q :=
  (rfl)

@[simp]
theorem thomCellDimension_zero_right (r : ℕ) : thomCellDimension r 0 = r :=
  Nat.zero_add r

theorem le_thomCellDimension (r q : ℕ) : r ≤ thomCellDimension r q :=
  Nat.le_add_left r q

theorem le_thomCellDimension_right (r q : ℕ) : q ≤ thomCellDimension r q :=
  Nat.le_add_right q r

theorem thomCellDimension_injective (r : ℕ) : Function.Injective (thomCellDimension r) :=
  fun _ _ h ↦ Nat.add_right_cancel h

section FibreRadial

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Radial homeomorphism `(Fin r → ℝ) ≃ₜ F` sending the sup-norm unit ball and unit sphere onto the
Euclidean unit ball and unit sphere of `F`: applies
`(EuclideanSpace.equiv (Fin r) ℝ).unitBallHomeomorph.symm` followed by the standard orthonormal
frame `EuclideanSpace ℝ (Fin r) ≃ₗᵢ[ℝ] F`. Works uniformly for all `r : ℕ`, including `r = 0`. -/
def fibreRadialHomeomorph {r : ℕ} (hr : Module.finrank ℝ F = r) : (Fin r → ℝ) ≃ₜ F :=
  (EuclideanSpace.equiv (Fin r) ℝ).unitBallHomeomorph.symm.trans
    (((stdOrthonormalBasis ℝ F).reindex (finCongr hr)).repr.symm.toHomeomorph)

variable {F}

@[simp]
theorem norm_fibreRadialHomeomorph_le_one_iff {r : ℕ} (hr : Module.finrank ℝ F = r)
    {w : Fin r → ℝ} :
    ‖fibreRadialHomeomorph F hr w‖ ≤ 1 ↔ ‖w‖ ≤ 1 := by
  dsimp only [fibreRadialHomeomorph, Homeomorph.trans_apply]
  change ‖((stdOrthonormalBasis ℝ F).reindex (finCongr hr)).repr.symm _‖ ≤ 1 ↔ ‖w‖ ≤ 1
  rw [LinearIsometryEquiv.norm_map,
    (EuclideanSpace.equiv (Fin r) ℝ).norm_unitBallHomeomorph_symm_le_one_iff]

@[simp]
theorem norm_fibreRadialHomeomorph_lt_one_iff {r : ℕ} (hr : Module.finrank ℝ F = r)
    {w : Fin r → ℝ} :
    ‖fibreRadialHomeomorph F hr w‖ < 1 ↔ ‖w‖ < 1 := by
  dsimp only [fibreRadialHomeomorph, Homeomorph.trans_apply]
  change ‖((stdOrthonormalBasis ℝ F).reindex (finCongr hr)).repr.symm _‖ < 1 ↔ ‖w‖ < 1
  rw [LinearIsometryEquiv.norm_map,
    (EuclideanSpace.equiv (Fin r) ℝ).norm_unitBallHomeomorph_symm_lt_one_iff]

@[simp]
theorem norm_fibreRadialHomeomorph_eq_one_iff {r : ℕ} (hr : Module.finrank ℝ F = r)
    {w : Fin r → ℝ} :
    ‖fibreRadialHomeomorph F hr w‖ = 1 ↔ ‖w‖ = 1 := by
  dsimp only [fibreRadialHomeomorph, Homeomorph.trans_apply]
  change ‖((stdOrthonormalBasis ℝ F).reindex (finCongr hr)).repr.symm _‖ = 1 ↔ ‖w‖ = 1
  rw [LinearIsometryEquiv.norm_map,
    (EuclideanSpace.equiv (Fin r) ℝ).norm_unitBallHomeomorph_symm_eq_one_iff]

@[simp]
theorem norm_fibreRadialHomeomorph_symm_le_one_iff {r : ℕ} (hr : Module.finrank ℝ F = r) {y : F} :
    ‖(fibreRadialHomeomorph F hr).symm y‖ ≤ 1 ↔ ‖y‖ ≤ 1 := by
  simpa using (norm_fibreRadialHomeomorph_le_one_iff hr
    (w := (fibreRadialHomeomorph F hr).symm y)).symm

@[simp]
theorem norm_fibreRadialHomeomorph_symm_lt_one_iff {r : ℕ} (hr : Module.finrank ℝ F = r) {y : F} :
    ‖(fibreRadialHomeomorph F hr).symm y‖ < 1 ↔ ‖y‖ < 1 := by
  simpa using (norm_fibreRadialHomeomorph_lt_one_iff hr
    (w := (fibreRadialHomeomorph F hr).symm y)).symm

@[simp]
theorem norm_fibreRadialHomeomorph_symm_eq_one_iff {r : ℕ} (hr : Module.finrank ℝ F = r) {y : F} :
    ‖(fibreRadialHomeomorph F hr).symm y‖ = 1 ↔ ‖y‖ = 1 := by
  simpa using (norm_fibreRadialHomeomorph_eq_one_iff hr
    (w := (fibreRadialHomeomorph F hr).symm y)).symm

end FibreRadial

/-! ### Cellwise pullback trivializations and characteristic maps -/

section Cells

variable {X : Type u} [TopologicalSpace X]
  (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  (E : X → Type u) [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E]

/-- `n`-cells of the disc-sphere relative CW complex over `(C, D)` for a rank-`r` bundle: triples
`⟨q, hqr, j⟩` consisting of a base dimension `q`, a proof `thomCellDimension r q = n`, and a base
`q`-cell `j : cell C q`. -/
private abbrev BundleCell (C : Set X) {D : Set X} [RelCWComplex C D] (r n : ℕ) : Type u :=
  Σ' (q : ℕ) (_ : thomCellDimension r q = n), cell C q

/-- Coordinate splitting `(Fin n → ℝ) ≃ᵢ (Fin q → ℝ) × (Fin r → ℝ)` for `q + r = n`. -/
private abbrev bundleCoordIso {q r n : ℕ} (hqr : thomCellDimension r q = n) :
    (Fin n → ℝ) ≃ᵢ (Fin q → ℝ) × (Fin r → ℝ) :=
  (Fin.appendIsometryOfEq hqr).symm

private lemma bundleCoordIso_zero {q r n : ℕ} (hqr : thomCellDimension r q = n) :
    bundleCoordIso hqr 0 = 0 := by
  ext <;> simp [bundleCoordIso, Fin.appendIsometryOfEq]

private lemma bundleCoordIso_mem_closedBall_iff {q r n : ℕ} (hqr : thomCellDimension r q = n)
    {x : Fin n → ℝ} :
    x ∈ closedBall 0 1 ↔
      (bundleCoordIso hqr x).1 ∈ closedBall 0 1 ∧ (bundleCoordIso hqr x).2 ∈ closedBall 0 1 := by
  rw [mem_closedBall, ← (bundleCoordIso hqr).dist_eq, bundleCoordIso_zero, ← mem_closedBall,
    Prod.zero_eq_mk, ← closedBall_prod_same, mem_prod]

private lemma bundleCoordIso_mem_ball_iff {q r n : ℕ} (hqr : thomCellDimension r q = n)
    {x : Fin n → ℝ} :
    x ∈ ball 0 1 ↔
      (bundleCoordIso hqr x).1 ∈ ball 0 1 ∧ (bundleCoordIso hqr x).2 ∈ ball 0 1 := by
  rw [mem_ball, ← (bundleCoordIso hqr).dist_eq, bundleCoordIso_zero, ← mem_ball,
    Prod.zero_eq_mk, ← ball_prod_same, mem_prod]

/-- The characteristic map of a base `q`-cell `j` restricted to the closed unit cube, as a bundled
continuous map `D^q → X`. -/
private def baseCellContMap {C D : Set X} [RelCWComplex C D] {q : ℕ} (j : cell C q) :
    C(closedBall (0 : Fin q → ℝ) 1, X) :=
  ⟨fun u ↦ map q j u.1, (continuousOn q j).comp_continuous continuous_subtype_val Subtype.prop⟩

private lemma exists_pullback_trivialization {C D : Set X} [RelCWComplex C D] {q : ℕ}
    (j : cell C q) :
    ∃ (h : TotalSpace F ((baseCellContMap j : _ → X) *ᵖ E) ≃ₜ closedBall (0 : Fin q → ℝ) 1 × F)
      (L : ∀ u : closedBall (0 : Fin q → ℝ) 1, ((baseCellContMap j : _ → X) *ᵖ E) u ≃ₗᵢ[ℝ] F),
      ∀ (u : closedBall (0 : Fin q → ℝ) 1) (v : ((baseCellContMap j : _ → X) *ᵖ E) u),
        h ⟨u, v⟩ = (u, L u v) := by
  have : CompactSpace (closedBall (0 : Fin q → ℝ) 1) :=
    isCompact_iff_compactSpace.1 (isCompact_closedBall 0 1)
  have : ContractibleSpace (closedBall (0 : Fin q → ℝ) 1) :=
    (convex_closedBall (0 : Fin q → ℝ) 1).contractibleSpace ⟨0, mem_closedBall_self zero_le_one⟩
  exact exists_homeomorph_prod_of_contractibleSpace F ((baseCellContMap j : _ → X) *ᵖ E)

private def cellPullbackHomeomorph {C D : Set X} [RelCWComplex C D] {q : ℕ} (j : cell C q) :
    TotalSpace F ((baseCellContMap j : _ → X) *ᵖ E) ≃ₜ closedBall (0 : Fin q → ℝ) 1 × F :=
  (exists_pullback_trivialization F E j).choose

private def cellPullbackFrame {C D : Set X} [RelCWComplex C D] {q : ℕ} (j : cell C q) :
    ∀ u : closedBall (0 : Fin q → ℝ) 1, ((baseCellContMap j : _ → X) *ᵖ E) u ≃ₗᵢ[ℝ] F :=
  (exists_pullback_trivialization F E j).choose_spec.choose

private lemma cellPullbackHomeomorph_apply {C D : Set X} [RelCWComplex C D] {q : ℕ} (j : cell C q)
    (u : closedBall (0 : Fin q → ℝ) 1) (v : ((baseCellContMap j : _ → X) *ᵖ E) u) :
    cellPullbackHomeomorph F E j ⟨u, v⟩ = (u, cellPullbackFrame F E j u v) :=
  (exists_pullback_trivialization F E j).choose_spec.choose_spec u v

private lemma cellPullbackHomeomorph_symm_apply {C D : Set X} [RelCWComplex C D] {q : ℕ}
    (j : cell C q) (u : closedBall (0 : Fin q → ℝ) 1) (y : F) :
    (cellPullbackHomeomorph F E j).symm (u, y) = ⟨u, (cellPullbackFrame F E j u).symm y⟩ := by
  apply (cellPullbackHomeomorph F E j).injective
  rw [Homeomorph.apply_symm_apply, cellPullbackHomeomorph_apply,
    LinearIsometryEquiv.apply_symm_apply]

private lemma lift_cellPullbackHomeomorph_symm {C D : Set X} [RelCWComplex C D] {q : ℕ}
    (j : cell C q) (u : closedBall (0 : Fin q → ℝ) 1) (y : F) :
    Pullback.lift (baseCellContMap j) ((cellPullbackHomeomorph F E j).symm (u, y)) =
      ⟨map q j u.1, (cellPullbackFrame F E j u).symm y⟩ := by
  rw [cellPullbackHomeomorph_symm_apply]
  rfl

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace (TotalSpace F E)] [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E] in
private lemma norm_lift_snd {C D : Set X} [RelCWComplex C D] {q : ℕ} (j : cell C q)
    (z : TotalSpace F ((baseCellContMap j : _ → X) *ᵖ E)) :
    ‖(Pullback.lift (baseCellContMap j) z).2‖ = ‖z.2‖ := by
  rcases z with ⟨_, _⟩
  rfl

private lemma norm_cellPullbackHomeomorph_symm_snd {C D : Set X} [RelCWComplex C D] {q : ℕ}
    (j : cell C q) (u : closedBall (0 : Fin q → ℝ) 1) (y : F) :
    ‖((cellPullbackHomeomorph F E j).symm (u, y)).2‖ = ‖y‖ := by
  have h := (cellPullbackHomeomorph F E j).apply_symm_apply (u, y)
  generalize (cellPullbackHomeomorph F E j).symm (u, y) = z at h ⊢
  rcases z with ⟨u', v'⟩
  rw [cellPullbackHomeomorph_apply] at h
  have hsnd := congrArg Prod.snd h
  dsimp only at hsnd
  rw [← hsnd, LinearIsometryEquiv.norm_map]

/-- Continuous product parameterization `D^q × D^r → D(E)` over a base `q`-cell `j`. -/
private def cellProdMap {C D : Set X} [RelCWComplex C D] {q r : ℕ} (hr : Module.finrank ℝ F = r)
    (j : cell C q) (p : closedBall (0 : Fin q → ℝ) 1 × closedBall (0 : Fin r → ℝ) 1) :
    discBundle F E :=
  ⟨Pullback.lift (baseCellContMap j)
      ((cellPullbackHomeomorph F E j).symm (p.1, fibreRadialHomeomorph F hr p.2.1)), by
    rw [mem_discBundle, norm_lift_snd, norm_cellPullbackHomeomorph_symm_snd,
      norm_fibreRadialHomeomorph_le_one_iff]
    exact mem_closedBall_zero_iff.1 p.2.2⟩

private lemma continuous_cellProdMap {C D : Set X} [RelCWComplex C D] {q r : ℕ}
    (hr : Module.finrank ℝ F = r) (j : cell C q) :
    Continuous (cellProdMap F E hr j) :=
  (((Pullback.continuous_lift F E (baseCellContMap j)).comp <|
    (cellPullbackHomeomorph F E j).symm.continuous.comp <|
      continuous_fst.prodMk
        ((fibreRadialHomeomorph F hr).continuous.comp
          (continuous_subtype_val.comp continuous_snd)))).subtype_mk _

private lemma cellProdMap_proj {C D : Set X} [RelCWComplex C D] {q r : ℕ}
    (hr : Module.finrank ℝ F = r) (j : cell C q)
    (p : closedBall (0 : Fin q → ℝ) 1 × closedBall (0 : Fin r → ℝ) 1) :
    (cellProdMap F E hr j p : TotalSpace F E).proj = map q j p.1.1 := by
  dsimp only [cellProdMap]
  rw [lift_cellPullbackHomeomorph_symm]

private lemma norm_cellProdMap_snd {C D : Set X} [RelCWComplex C D] {q r : ℕ}
    (hr : Module.finrank ℝ F = r) (j : cell C q)
    (p : closedBall (0 : Fin q → ℝ) 1 × closedBall (0 : Fin r → ℝ) 1) :
    ‖(cellProdMap F E hr j p : TotalSpace F E).2‖ = ‖fibreRadialHomeomorph F hr p.2.1‖ :=
  (norm_lift_snd F E j _).trans (norm_cellPullbackHomeomorph_symm_snd F E j _ _)

/-- Lift `v ∈ D(E)` with `v.proj = map q j u` to the pullback `(baseCellContMap j)* E`. -/
private def pullbackPointOfEq {C D : Set X} [RelCWComplex C D] {q : ℕ} (j : cell C q)
    (u : closedBall (0 : Fin q → ℝ) 1) (v : discBundle F E)
    (hproj : map q j u.1 = v.1.proj) :
    TotalSpace F ((baseCellContMap j : _ → X) *ᵖ E) :=
  ⟨u, cast (congrArg E hproj.symm) v.1.2⟩

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace (TotalSpace F E)] [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E] in
private lemma lift_pullbackPointOfEq {C D : Set X} [RelCWComplex C D] {q : ℕ} (j : cell C q)
    (u : closedBall (0 : Fin q → ℝ) 1) (v : discBundle F E) (hproj : map q j u.1 = v.1.proj) :
    Pullback.lift (baseCellContMap j) (pullbackPointOfEq F E j u v hproj) = v.1 := by
  rcases v with ⟨⟨b, val⟩, _⟩
  dsimp only at hproj
  subst hproj
  rfl

private lemma norm_pullbackPointOfEq {C D : Set X} [RelCWComplex C D] {q : ℕ} (j : cell C q)
    (u : closedBall (0 : Fin q → ℝ) 1) (v : discBundle F E) (hproj : map q j u.1 = v.1.proj) :
    ‖(cellPullbackHomeomorph F E j (pullbackPointOfEq F E j u v hproj)).2‖ = ‖v.1.2‖ := by
  dsimp only [pullbackPointOfEq]
  rw [cellPullbackHomeomorph_apply, LinearIsometryEquiv.norm_map]
  rcases v with ⟨⟨b, val⟩, _⟩
  dsimp only at hproj
  subst hproj
  rfl

open Classical in
/-- Characteristic `PartialEquiv` of the bundle `(q + r)`-cell over `j : cell C q`. -/
private def bundleCellMap {C D : Set X} [RelCWComplex C D] {r n : ℕ}
    (hr : Module.finrank ℝ F = r) :
    BundleCell C r n → PartialEquiv (Fin n → ℝ) (discBundle F E)
  | ⟨q, hqr, j⟩ =>
    { toFun x :=
        if hx : x ∈ closedBall (0 : Fin n → ℝ) 1 then
          cellProdMap F E hr j
            (⟨(bundleCoordIso hqr x).1, (bundleCoordIso_mem_closedBall_iff hqr).1 hx |>.1⟩,
              ⟨(bundleCoordIso hqr x).2, (bundleCoordIso_mem_closedBall_iff hqr).1 hx |>.2⟩)
        else
          cellProdMap F E hr j
            (⟨0, mem_closedBall_self zero_le_one⟩, ⟨0, mem_closedBall_self zero_le_one⟩)
      invFun v :=
        if hv : v.1.proj ∈ (map q j).target then
          let u : closedBall (0 : Fin q → ℝ) 1 :=
            ⟨(map q j).symm v.1.proj,
              ball_subset_closedBall ((source_eq q j) ▸ (map q j).map_target hv)⟩
          (bundleCoordIso hqr).symm
            (u.1, (fibreRadialHomeomorph F hr).symm
              (cellPullbackHomeomorph F E j
                (pullbackPointOfEq F E j u v ((map q j).right_inv hv))).2)
        else 0
      source := ball (0 : Fin n → ℝ) 1
      target := {v : discBundle F E | v.1.proj ∈ (map q j).target ∧ ‖v.1.2‖ < 1}
      map_source' x hx := by
        have hxc : x ∈ closedBall (0 : Fin n → ℝ) 1 := ball_subset_closedBall hx
        obtain ⟨hx₁, hx₂⟩ := (bundleCoordIso_mem_ball_iff hqr).1 hx
        refine ⟨?_, ?_⟩
        · rw [dite_eq_left hxc, cellProdMap_proj]
          exact (map q j).map_source ((source_eq q j).symm ▸ hx₁)
        · refine lt_of_eq_of_lt
            ((congrArg (fun v : discBundle F E ↦ ‖v.1.2‖) (dite_eq_left hxc)).trans
              (norm_cellProdMap_snd F E hr j _)) ?_
          exact (norm_fibreRadialHomeomorph_lt_one_iff hr).2 (mem_ball_zero_iff.1 hx₂)
      map_target' v hv := by
        dsimp only
        rw [dite_eq_left hv.1, bundleCoordIso_mem_ball_iff hqr, IsometryEquiv.apply_symm_apply]
        refine ⟨(source_eq q j).subset ((map q j).map_target hv.1), ?_⟩
        rw [mem_ball_zero_iff, norm_fibreRadialHomeomorph_symm_lt_one_iff,
          norm_pullbackPointOfEq]
        exact hv.2
      left_inv' x hx := by
        have hxc : x ∈ closedBall (0 : Fin n → ℝ) 1 := ball_subset_closedBall hx
        obtain ⟨hx₁, -⟩ := (bundleCoordIso_mem_ball_iff hqr).1 hx
        have hxt : map q j (bundleCoordIso hqr x).1 ∈ (map q j).target :=
          (map q j).map_source ((source_eq q j).symm ▸ hx₁)
        dsimp only
        set v₀ := cellProdMap F E hr j
          (⟨(bundleCoordIso hqr x).1, (bundleCoordIso_mem_closedBall_iff hqr).1 hxc |>.1⟩,
            ⟨(bundleCoordIso hqr x).2, (bundleCoordIso_mem_closedBall_iff hqr).1 hxc |>.2⟩)
        have hv₀_proj : v₀.1.proj = map q j (bundleCoordIso hqr x).1 := cellProdMap_proj F E hr j _
        have hv₀_t : v₀.1.proj ∈ (map q j).target := hv₀_proj ▸ hxt
        rw [dite_eq_left hxc, dite_eq_left hv₀_t]
        have hu_eq : (map q j).symm v₀.1.proj = (bundleCoordIso hqr x).1 := by
          rw [hv₀_proj]
          exact (map q j).left_inv ((source_eq q j).symm ▸ hx₁)
        have hpt_eq :
            pullbackPointOfEq F E j
                ⟨(map q j).symm v₀.1.proj,
                  ball_subset_closedBall ((source_eq q j) ▸ (map q j).map_target hv₀_t)⟩
                v₀ ((map q j).right_inv hv₀_t) =
              (cellPullbackHomeomorph F E j).symm
                (⟨(bundleCoordIso hqr x).1, (bundleCoordIso_mem_closedBall_iff hqr).1 hxc |>.1⟩,
                  fibreRadialHomeomorph F hr (bundleCoordIso hqr x).2) := by
          apply Bundle.Pullback.totalSpace_ext
          · rw [cellPullbackHomeomorph_symm_apply]
            exact Subtype.ext hu_eq
          · rw [lift_pullbackPointOfEq]
            rfl
        rw [hpt_eq, Homeomorph.apply_symm_apply, Homeomorph.symm_apply_apply,
          hu_eq, Prod.mk.eta, IsometryEquiv.symm_apply_apply]
      right_inv' v hv := by
        let u : closedBall (0 : Fin q → ℝ) 1 :=
          ⟨(map q j).symm v.1.proj,
            ball_subset_closedBall ((source_eq q j) ▸ (map q j).map_target hv.1)⟩
        let z := pullbackPointOfEq F E j u v ((map q j).right_inv hv.1)
        have hw : ‖(fibreRadialHomeomorph F hr).symm (cellPullbackHomeomorph F E j z).2‖ < 1 := by
          rw [norm_fibreRadialHomeomorph_symm_lt_one_iff, norm_pullbackPointOfEq]
          exact hv.2
        set x := (bundleCoordIso hqr).symm
          (u.1, (fibreRadialHomeomorph F hr).symm (cellPullbackHomeomorph F E j z).2)
        have hxc : x ∈ closedBall (0 : Fin n → ℝ) 1 := by
          rw [bundleCoordIso_mem_closedBall_iff hqr, IsometryEquiv.apply_symm_apply]
          exact ⟨u.2, mem_closedBall_zero_iff.2 hw.le⟩
        apply Subtype.ext
        dsimp only
        rw [dite_eq_left hv.1, dite_eq_left hxc]
        dsimp only [cellProdMap]
        have hz_fst : (cellPullbackHomeomorph F E j z).1 = u := by
          dsimp only [z, pullbackPointOfEq]
          rw [cellPullbackHomeomorph_apply]
        have hpair :
            (⟨(bundleCoordIso hqr x).1, (bundleCoordIso_mem_closedBall_iff hqr).1 hxc |>.1⟩,
              fibreRadialHomeomorph F hr (bundleCoordIso hqr x).2) =
              cellPullbackHomeomorph F E j z := by
          ext1
          · apply Subtype.ext
            simp only [x, IsometryEquiv.apply_symm_apply, hz_fst]
          · simp only [x, IsometryEquiv.apply_symm_apply, Homeomorph.apply_symm_apply]
        rw [hpair, Homeomorph.symm_apply_apply, lift_pullbackPointOfEq] }

private lemma bundleCellMap_apply_of_mem_closedBall {C D : Set X} [RelCWComplex C D] {q r n : ℕ}
    (hr : Module.finrank ℝ F = r) (hqr : thomCellDimension r q = n) (j : cell C q) {x : Fin n → ℝ}
    (hx : x ∈ closedBall (0 : Fin n → ℝ) 1) :
    bundleCellMap F E hr ⟨q, hqr, j⟩ x = cellProdMap F E hr j
      (⟨(bundleCoordIso hqr x).1, (bundleCoordIso_mem_closedBall_iff hqr).1 hx |>.1⟩,
        ⟨(bundleCoordIso hqr x).2, (bundleCoordIso_mem_closedBall_iff hqr).1 hx |>.2⟩) := by
  classical
  change (if hx' : x ∈ closedBall (0 : Fin n → ℝ) 1 then _ else _) = _
  rw [dite_eq_left hx]

private lemma continuousOn_bundleCellMap {C D : Set X} [RelCWComplex C D] {r n : ℕ}
    (hr : Module.finrank ℝ F = r) (c : BundleCell C r n) :
    ContinuousOn (bundleCellMap F E hr c) (closedBall 0 1) := by
  rcases c with ⟨q, hqr, j⟩
  rw [continuousOn_iff_continuous_domRestrict]
  have hpair : Continuous (fun x : closedBall (0 : Fin n → ℝ) 1 ↦
      ((⟨(bundleCoordIso hqr x.1).1, (bundleCoordIso_mem_closedBall_iff hqr).1 x.2 |>.1⟩ :
          closedBall (0 : Fin q → ℝ) 1),
        (⟨(bundleCoordIso hqr x.1).2, (bundleCoordIso_mem_closedBall_iff hqr).1 x.2 |>.2⟩ :
          closedBall (0 : Fin r → ℝ) 1))) :=
    ((continuous_fst.comp ((bundleCoordIso hqr).continuous.comp continuous_subtype_val)).subtype_mk
      _).prodMk
      ((continuous_snd.comp
        ((bundleCoordIso hqr).continuous.comp continuous_subtype_val)).subtype_mk _)
  exact ((continuous_cellProdMap F E hr j).comp hpair).congr fun x ↦
    (bundleCellMap_apply_of_mem_closedBall F E hr hqr j x.2).symm

private lemma continuousOn_bundleCellMap_symm {C D : Set X} [RelCWComplex C D] {r n : ℕ}
    (hr : Module.finrank ℝ F = r) (c : BundleCell C r n) :
    ContinuousOn (bundleCellMap F E hr c).symm (bundleCellMap F E hr c).target := by
  rcases c with ⟨q, hqr, j⟩
  rw [continuousOn_iff_continuous_domRestrict]
  let S : Set (discBundle F E) := {v | v.1.proj ∈ (map q j).target ∧ ‖v.1.2‖ < 1}
  have hu : Continuous fun v : S ↦ (map q j).symm v.1.1.proj :=
    continuousOn_iff_continuous_domRestrict.1 <|
      (continuousOn_symm q j).comp
        ((FiberBundle.continuous_proj F E).comp continuous_subtype_val).continuousOn
        fun _ (hv : _ ∈ S) ↦ hv.1
  let g : S → TotalSpace F ((baseCellContMap j : _ → X) *ᵖ E) := fun v ↦
    pullbackPointOfEq F E j
      ⟨(map q j).symm v.1.1.proj,
        ball_subset_closedBall ((source_eq q j) ▸ (map q j).map_target v.2.1)⟩
      v.1 ((map q j).right_inv v.2.1)
  have hg : Continuous g := by
    rw [Bundle.Pullback.continuous_iff]
    refine ⟨hu.subtype_mk _, ?_⟩
    exact (continuous_subtype_val.comp continuous_subtype_val).congr fun v ↦
      (lift_pullbackPointOfEq F E j _ v.1 _).symm
  have hmain : Continuous fun v : S ↦
      (bundleCoordIso hqr).symm
        ((map q j).symm v.1.1.proj,
          (fibreRadialHomeomorph F hr).symm (cellPullbackHomeomorph F E j (g v)).2) :=
    (bundleCoordIso hqr).symm.continuous.comp <|
      hu.prodMk ((fibreRadialHomeomorph F hr).symm.continuous.comp
        (continuous_snd.comp ((cellPullbackHomeomorph F E j).continuous.comp hg)))
  refine hmain.congr fun v ↦ ?_
  classical
  change _ = if hv : v.1.1.proj ∈ (map q j).target then _ else 0
  rw [dite_eq_left v.2.1]

private lemma image_ball_bundleCellMap {C D : Set X} [RelCWComplex C D] {q r n : ℕ}
    (hr : Module.finrank ℝ F = r) (hqr : thomCellDimension r q = n) (j : cell C q) :
    bundleCellMap F E hr ⟨q, hqr, j⟩ '' ball 0 1 =
      {v : discBundle F E | v.1.proj ∈ openCell q j ∧ ‖v.1.2‖ < 1} := by
  have hsrc : (bundleCellMap F E hr ⟨q, hqr, j⟩).source = ball 0 1 := rfl
  have hopen : (map q j).target = openCell q j := by
    rw [← (map q j).image_source_eq_target, source_eq, openCell]
  rw [← hsrc, (bundleCellMap F E hr ⟨q, hqr, j⟩).image_source_eq_target]
  simp only [bundleCellMap, hopen]

/-- Explicit cube coordinates in `D^{q + r}` lifting `(u, v)` with `map q j u = v.proj`. -/
private def bundleCellPreimage {C D : Set X} [RelCWComplex C D] {q r n : ℕ}
    (hr : Module.finrank ℝ F = r) (hqr : thomCellDimension r q = n) (j : cell C q)
    (u : closedBall (0 : Fin q → ℝ) 1) (v : discBundle F E) (hproj : map q j u.1 = v.1.proj) :
    Fin n → ℝ :=
  (bundleCoordIso hqr).symm
    (u.1, (fibreRadialHomeomorph F hr).symm
      (cellPullbackHomeomorph F E j (pullbackPointOfEq F E j u v hproj)).2)

private lemma bundleCellPreimage_mem_closedBall {C D : Set X} [RelCWComplex C D] {q r n : ℕ}
    (hr : Module.finrank ℝ F = r) (hqr : thomCellDimension r q = n) (j : cell C q)
    (u : closedBall (0 : Fin q → ℝ) 1) (v : discBundle F E) (hproj : map q j u.1 = v.1.proj) :
    bundleCellPreimage F E hr hqr j u v hproj ∈ closedBall (0 : Fin n → ℝ) 1 := by
  rw [bundleCoordIso_mem_closedBall_iff hqr, bundleCellPreimage, IsometryEquiv.apply_symm_apply]
  refine ⟨u.2, mem_closedBall_zero_iff.2 ?_⟩
  rw [norm_fibreRadialHomeomorph_symm_le_one_iff, norm_pullbackPointOfEq]
  exact mem_discBundle.1 v.2

private lemma bundleCellMap_bundleCellPreimage {C D : Set X} [RelCWComplex C D] {q r n : ℕ}
    (hr : Module.finrank ℝ F = r) (hqr : thomCellDimension r q = n) (j : cell C q)
    (u : closedBall (0 : Fin q → ℝ) 1) (v : discBundle F E) (hproj : map q j u.1 = v.1.proj) :
    bundleCellMap F E hr ⟨q, hqr, j⟩ (bundleCellPreimage F E hr hqr j u v hproj) = v := by
  set x := bundleCellPreimage F E hr hqr j u v hproj
  have hxc : x ∈ closedBall (0 : Fin n → ℝ) 1 :=
    bundleCellPreimage_mem_closedBall F E hr hqr j u v hproj
  apply Subtype.ext
  rw [bundleCellMap_apply_of_mem_closedBall F E hr hqr j hxc]
  dsimp only [cellProdMap]
  let z := pullbackPointOfEq F E j u v hproj
  have hz_fst : (cellPullbackHomeomorph F E j z).1 = u := by
    dsimp only [z, pullbackPointOfEq]
    rw [cellPullbackHomeomorph_apply]
  have hpair :
      (⟨(bundleCoordIso hqr x).1, (bundleCoordIso_mem_closedBall_iff hqr).1 hxc |>.1⟩,
        fibreRadialHomeomorph F hr (bundleCoordIso hqr x).2) =
        cellPullbackHomeomorph F E j z := by
    ext1
    · apply Subtype.ext
      simp only [x, bundleCellPreimage, IsometryEquiv.apply_symm_apply, hz_fst]
    · simp only [x, bundleCellPreimage, IsometryEquiv.apply_symm_apply, Homeomorph.apply_symm_apply,
        z]
  rw [hpair, Homeomorph.symm_apply_apply, lift_pullbackPointOfEq]

private lemma image_closedBall_bundleCellMap {C D : Set X} [RelCWComplex C D] {q r n : ℕ}
    (hr : Module.finrank ℝ F = r) (hqr : thomCellDimension r q = n) (j : cell C q) :
    bundleCellMap F E hr ⟨q, hqr, j⟩ '' closedBall 0 1 = discBundleProj F E ⁻¹' closedCell q j := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_preimage, discBundleProj_apply, bundleCellMap_apply_of_mem_closedBall F E hr hqr j hx,
      cellProdMap_proj]
    exact mem_image_of_mem _ ((bundleCoordIso_mem_closedBall_iff hqr).1 hx).1
  · rintro ⟨u, hu, hmap⟩
    rw [discBundleProj_apply] at hmap
    exact ⟨bundleCellPreimage F E hr hqr j ⟨u, hu⟩ v hmap,
      bundleCellPreimage_mem_closedBall F E hr hqr j ⟨u, hu⟩ v hmap,
      bundleCellMap_bundleCellPreimage F E hr hqr j ⟨u, hu⟩ v hmap⟩

private lemma image_sphere_bundleCellMap {C D : Set X} [RelCWComplex C D] {q r n : ℕ}
    (hr : Module.finrank ℝ F = r) (hqr : thomCellDimension r q = n) (j : cell C q) :
    bundleCellMap F E hr ⟨q, hqr, j⟩ '' sphere 0 1 =
      discBundleProj F E ⁻¹' cellFrontier q j ∪
        (Subtype.val ⁻¹' sphereBundle F E ∩ discBundleProj F E ⁻¹' closedCell q j) := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxc : x ∈ closedBall (0 : Fin n → ℝ) 1 := sphere_subset_closedBall hx
    have hxs : bundleCoordIso hqr x ∈ sphere 0 1 := by
      rwa [mem_sphere, ← bundleCoordIso_zero hqr, IsometryEquiv.dist_eq]
    rw [Prod.zero_eq_mk, sphere_prod, mem_union, mem_prod, mem_prod] at hxs
    rw [bundleCellMap_apply_of_mem_closedBall F E hr hqr j hxc]
    rcases hxs with ⟨h₁, _⟩ | ⟨h₁, h₂⟩
    · left
      rw [mem_preimage, discBundleProj_apply, cellProdMap_proj]
      exact mem_image_of_mem _ h₁
    · right
      refine ⟨?_, ?_⟩
      · rw [mem_preimage, mem_sphereBundle, norm_cellProdMap_snd,
          norm_fibreRadialHomeomorph_eq_one_iff]
        exact mem_sphere_zero_iff_norm.1 h₂
      · rw [mem_preimage, discBundleProj_apply, cellProdMap_proj]
        exact mem_image_of_mem _ h₁
  · rintro (⟨u, hu, hmap⟩ | ⟨hvs, ⟨u, hu, hmap⟩⟩)
    · rw [discBundleProj_apply] at hmap
      let u' : closedBall (0 : Fin q → ℝ) 1 := ⟨u, sphere_subset_closedBall hu⟩
      refine ⟨bundleCellPreimage F E hr hqr j u' v hmap, ?_,
        bundleCellMap_bundleCellPreimage F E hr hqr j u' v hmap⟩
      rw [mem_sphere, ← (bundleCoordIso hqr).dist_eq, bundleCoordIso_zero, ← mem_sphere,
        Prod.zero_eq_mk, sphere_prod, bundleCellPreimage, IsometryEquiv.apply_symm_apply]
      refine Or.inl ⟨hu, mem_closedBall_zero_iff.2 ?_⟩
      rw [norm_fibreRadialHomeomorph_symm_le_one_iff, norm_pullbackPointOfEq]
      exact mem_discBundle.1 v.2
    · rw [discBundleProj_apply] at hmap
      let u' : closedBall (0 : Fin q → ℝ) 1 := ⟨u, hu⟩
      refine ⟨bundleCellPreimage F E hr hqr j u' v hmap, ?_,
        bundleCellMap_bundleCellPreimage F E hr hqr j u' v hmap⟩
      rw [mem_sphere, ← (bundleCoordIso hqr).dist_eq, bundleCoordIso_zero, ← mem_sphere,
        Prod.zero_eq_mk, sphere_prod, bundleCellPreimage, IsometryEquiv.apply_symm_apply]
      refine Or.inr ⟨hu, mem_sphere_zero_iff_norm.2 ?_⟩
      rw [norm_fibreRadialHomeomorph_symm_eq_one_iff, norm_pullbackPointOfEq]
      exact mem_sphereBundle.1 hvs

private lemma mapsTo_bundleCellMap (C : Set X) {D : Set X} [RelCWComplex C D] {r : ℕ}
    (hr : Module.finrank ℝ F = r) (n : ℕ) (c : BundleCell C r n) :
    ∃ I : ∀ m, Finset (BundleCell C r m),
      MapsTo (bundleCellMap F E hr c) (sphere 0 1)
        (((Subtype.val ⁻¹' sphereBundle F E ∩ discBundleProj F E ⁻¹' C) ∪
            discBundleProj F E ⁻¹' D) ∪
          ⋃ (m < n) (c' ∈ I m), bundleCellMap F E hr c' '' closedBall 0 1) := by
  rcases c with ⟨q, hqr, j⟩
  obtain ⟨I₀, hI₀⟩ := RelCWComplex.mapsTo (C := C) q j
  let liftCell (m : ℕ) (hm : r ≤ m) : cell C (m - r) ↪ BundleCell C r m :=
    ⟨fun k ↦ ⟨m - r, Nat.sub_add_cancel hm, k⟩, fun _ _ h ↦ by cases h; rfl⟩
  refine ⟨fun m ↦ if hm : r ≤ m then (I₀ (m - r)).map (liftCell m hm) else ∅, ?_⟩
  rw [mapsTo_iff_image_subset, image_sphere_bundleCellMap]
  rintro v (hv | ⟨hvs, hvc⟩)
  · have hmem := hI₀.image_subset hv
    rw [mem_union] at hmem
    rcases hmem with hD | hcell
    · exact Or.inl (Or.inr hD)
    · simp only [mem_iUnion, exists_prop] at hcell
      obtain ⟨m, hm, k, hkI, hk⟩ := hcell
      obtain ⟨n', hn'⟩ : ∃ n', n' = m + r := ⟨m + r, rfl⟩
      have hrm : r ≤ n' := by omega
      have hsub : m = n' - r := by omega
      subst hsub
      right
      refine mem_iUnion₂.2 ⟨n', by dsimp only [thomCellDimension] at hqr; omega, ?_⟩
      refine mem_iUnion₂.2 ⟨liftCell n' hrm k, ?_, ?_⟩
      · dsimp only
        rw [dite_eq_left hrm]
        exact Finset.mem_map_of_mem (liftCell n' hrm) hkI
      · rw [image_closedBall_bundleCellMap]
        exact hk
  · exact Or.inl (Or.inl ⟨hvs, closedCell_subset_complex q j hvc⟩)

variable [T2Space X]

/-- **Relative CW structure on the unit disc bundle over an arbitrary classical relative CW pair
`(C, D)` in a Hausdorff base `X`.** For a continuous Riemannian vector bundle `E → X` of rank `r`,
`π_D ⁻¹' C` is a classical relative CW complex in `D(E)` relative to
`(S(E) ∩ π_D ⁻¹' C) ∪ π_D ⁻¹' D`, with one `(q + r)`-cell over each `q`-cell of `(C, D)`. -/
@[instance_reducible]
def bundleDiskSphereRelCWOver (C : Set X) {D : Set X} [RelCWComplex C D] {r : ℕ}
    (hr : Module.finrank ℝ F = r) :
    RelCWComplex (discBundleProj F E ⁻¹' C)
      ((Subtype.val ⁻¹' sphereBundle F E ∩ discBundleProj F E ⁻¹' C) ∪
        discBundleProj F E ⁻¹' D) where
  cell := BundleCell C r
  map _ c := bundleCellMap F E hr c
  source_eq _ := by rintro ⟨_, _, _⟩; rfl
  continuousOn _ c := continuousOn_bundleCellMap F E hr c
  continuousOn_symm _ c := continuousOn_bundleCellMap_symm F E hr c
  pairwiseDisjoint' := by
    rintro ⟨n₁, q₁, rfl, j₁⟩ - ⟨n₂, q₂, rfl, j₂⟩ - hne
    rw [Function.onFun, Set.disjoint_left, image_ball_bundleCellMap, image_ball_bundleCellMap]
    rintro v ⟨hv₁, _⟩ ⟨hv₂, _⟩
    have hq : (⟨q₁, j₁⟩ : Σ q, cell C q) ≠ ⟨q₂, j₂⟩ := by
      intro h
      obtain ⟨rfl, hj⟩ := Sigma.mk.inj_iff.1 h
      obtain rfl := eq_of_heq hj
      exact hne rfl
    exact Set.disjoint_left.1 (disjoint_openCell_of_ne hq) hv₁ hv₂
  disjointBase' _ := by
    rintro ⟨q, rfl, j⟩
    rw [Set.disjoint_left, image_ball_bundleCellMap]
    rintro v ⟨hv₁, hnorm⟩ (⟨hvs, _⟩ | hvD)
    · exact hnorm.ne (mem_sphereBundle.1 hvs)
    · rw [mem_preimage, discBundleProj_apply] at hvD
      exact Set.disjoint_left.1 (disjointBase q j) hv₁ hvD
  mapsTo := mapsTo_bundleCellMap F E C hr
  closed' S hSC := by
    rintro ⟨hcells, hbase⟩
    refine (closed_discBundleProj_preimage F E C S hSC).2 ⟨fun q j ↦ ?_, ?_⟩
    · have h := hcells (thomCellDimension r q) ⟨q, rfl, j⟩
      rwa [image_closedBall_bundleCellMap] at h
    · have hsub :
          S ∩ discBundleProj F E ⁻¹' D =
            (S ∩ ((Subtype.val ⁻¹' sphereBundle F E ∩ discBundleProj F E ⁻¹' C) ∪
              discBundleProj F E ⁻¹' D)) ∩ discBundleProj F E ⁻¹' D := by
        ext v
        simp only [mem_inter_iff, mem_union]
        tauto
      rw [hsub]
      exact hbase.inter ((RelCWComplex.isClosedBase (C := C)).preimage
        (discBundleProj F E).continuous)
  isClosedBase :=
    (((isClosed_sphereBundle F E (continuous_norm_bundle F E)).preimage
      continuous_subtype_val).inter
      ((RelCWComplex.isClosed (C := C)).preimage (discBundleProj F E).continuous)).union
      ((RelCWComplex.isClosedBase (C := C)).preimage (discBundleProj F E).continuous)
  union' := by
    ext v
    simp only [mem_union, mem_iUnion, mem_preimage, mem_inter_iff]
    constructor
    · rintro ((⟨-, hvC⟩ | hvD) | ⟨n, ⟨q, rfl, j⟩, hv⟩)
      · exact hvC
      · exact base_subset_complex (C := C) hvD
      · rw [image_closedBall_bundleCellMap] at hv
        exact closedCell_subset_complex q j hv
    · intro hvC
      have hv_union : discBundleProj F E v ∈ D ∪ ⋃ (q : ℕ) (j : cell C q), closedCell q j := by
        rwa [RelCWComplex.union]
      rcases hv_union with hvD | hvcell
      · exact Or.inl (Or.inr hvD)
      · simp only [mem_iUnion] at hvcell
        obtain ⟨q, j, hq⟩ := hvcell
        right
        refine ⟨thomCellDimension r q, ⟨q, rfl, j⟩, ?_⟩
        rwa [image_closedBall_bundleCellMap]

/-- **Relative CW structure on `(D(E), S(E) ∪ D(E)|_A)` over a Hausdorff CW pair `(X, A)`.**
For a continuous Riemannian vector bundle `E → X` of rank `r` over a Hausdorff space `X` with a
classical relative CW structure `RelCWComplex univ A`, the unit disc bundle `D(E)` carries a
classical relative CW structure on `univ` relative to `Subtype.val ⁻¹' S(E) ∪ π_D ⁻¹' A`, with one
`(q + r)`-cell for each relative `q`-cell of `(X, A)`. -/
@[instance_reducible]
def bundleDiskSphereRelCW (A : Set X) [RelCWComplex (univ : Set X) A] {r : ℕ}
    (hr : Module.finrank ℝ F = r) :
    RelCWComplex (univ : Set (discBundle F E))
      (Subtype.val ⁻¹' sphereBundle F E ∪ discBundleProj F E ⁻¹' A) :=
  letI I := bundleDiskSphereRelCWOver F E (univ : Set X) (D := A) hr
  have hbase :
      (Subtype.val ⁻¹' sphereBundle F E ∩ discBundleProj F E ⁻¹' (univ : Set X)) ∪
          discBundleProj F E ⁻¹' A =
        Subtype.val ⁻¹' sphereBundle F E ∪ discBundleProj F E ⁻¹' A := by
    rw [preimage_univ, inter_univ]
  { cell := I.cell
    map := I.map
    source_eq := I.source_eq
    continuousOn := I.continuousOn
    continuousOn_symm := I.continuousOn_symm
    pairwiseDisjoint' := I.pairwiseDisjoint'
    disjointBase' n c := hbase ▸ I.disjointBase' n c
    mapsTo n c := hbase ▸ I.mapsTo n c
    closed' S hS := hbase ▸ I.closed' S hS
    isClosedBase := hbase ▸ I.isClosedBase
    union' := hbase ▸ I.union' }

end Cells

/-! ### Cell equivalences, explicit cell formulas, and finiteness -/

section API

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  (E : X → Type u) [TopologicalSpace (TotalSpace F E)]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E]

section Over

variable (C : Set X) {D : Set X} [RelCWComplex C D] {r : ℕ} (hr : Module.finrank ℝ F = r)

/-- The `(q + r)`-cells of `bundleDiskSphereRelCWOver` correspond bijectively to the `q`-cells of
the base complex `C`. -/
def bundleDiskSphereCellEquivOver (q : ℕ) :
    @RelCWComplex.cell _ _ _ _ (bundleDiskSphereRelCWOver F E C hr) (thomCellDimension r q) ≃
      cell C q where
  toFun c := thomCellDimension_injective r c.2.1 ▸ c.2.2
  invFun j := ⟨q, rfl, j⟩
  left_inv := by
    rintro ⟨q', hq', j⟩
    obtain rfl := thomCellDimension_injective r hq'
    rfl
  right_inv _ := rfl

/-- Below the fibre rank `r`, `bundleDiskSphereRelCWOver` has no cells. -/
theorem isEmpty_cell_bundleDiskSphereRelCWOver_of_lt {n : ℕ} (hn : n < r) :
    IsEmpty (@RelCWComplex.cell _ _ _ _ (bundleDiskSphereRelCWOver F E C hr) n) :=
  ⟨fun ⟨q, hqr, _⟩ ↦ Nat.not_le_of_lt hn (hqr ▸ le_thomCellDimension r q)⟩

theorem finiteDimensional_bundleDiskSphereRelCWOver [RelCWComplex.FiniteDimensional C] :
    @RelCWComplex.FiniteDimensional _ _ _ _ (bundleDiskSphereRelCWOver F E C hr) := by
  refine @RelCWComplex.FiniteDimensional.mk _ _ _ _ (bundleDiskSphereRelCWOver F E C hr) ?_
  obtain ⟨N, hN⟩ := eventually_atTop.1 (FiniteDimensional.eventually_isEmpty_cell (C := C) (D := D))
  refine eventually_atTop.2 ⟨thomCellDimension r N, fun n hn ↦ ⟨fun ⟨q, hqr, j⟩ ↦ ?_⟩⟩
  have hq : N ≤ q := by
    dsimp only [thomCellDimension] at hn hqr
    omega
  exact (hN q hq).false j

theorem finiteType_bundleDiskSphereRelCWOver [RelCWComplex.FiniteType C] :
    @RelCWComplex.FiniteType _ _ _ _ (bundleDiskSphereRelCWOver F E C hr) := by
  refine @RelCWComplex.FiniteType.mk _ _ _ _ (bundleDiskSphereRelCWOver F E C hr) fun n ↦ ?_
  by_cases hn : r ≤ n
  · obtain ⟨q, rfl⟩ : ∃ q, thomCellDimension r q = n := ⟨n - r, Nat.sub_add_cancel hn⟩
    have : _root_.Finite (cell C q) := FiniteType.finite_cell q
    exact _root_.Finite.of_equiv _ (bundleDiskSphereCellEquivOver F E C hr q).symm
  · have := isEmpty_cell_bundleDiskSphereRelCWOver_of_lt F E C hr (Nat.lt_of_not_ge hn)
    infer_instance

theorem finite_bundleDiskSphereRelCWOver [RelCWComplex.Finite C] :
    @RelCWComplex.Finite _ _ _ _ (bundleDiskSphereRelCWOver F E C hr) :=
  @RelCWComplex.Finite.mk _ _ _ _ (bundleDiskSphereRelCWOver F E C hr)
    (finiteDimensional_bundleDiskSphereRelCWOver F E C hr)
    (finiteType_bundleDiskSphereRelCWOver F E C hr)

end Over

section Univ

variable (A : Set X) [RelCWComplex (univ : Set X) A] {r : ℕ} (hr : Module.finrank ℝ F = r)

/-- **Cell correspondence for `(D(E), S(E) ∪ D(E)|_A)`.** The `(q + r)`-cells of
`TauCeti.bundleDiskSphereRelCW` are in canonical bijection with the relative `q`-cells of
`(X, A)`. -/
def bundleDiskSphereCellEquiv (q : ℕ) :
    @RelCWComplex.cell _ _ _ _ (bundleDiskSphereRelCW F E A hr) (thomCellDimension r q) ≃
      cell (univ : Set X) q :=
  bundleDiskSphereCellEquivOver F E (univ : Set X) hr q

/-- Below the fibre rank `r`, `(D(E), S(E) ∪ D(E)|_A)` has no `n`-cells. -/
theorem isEmpty_cell_bundleDiskSphereRelCW_of_lt {n : ℕ} (hn : n < r) :
    IsEmpty (@RelCWComplex.cell _ _ _ _ (bundleDiskSphereRelCW F E A hr) n) :=
  isEmpty_cell_bundleDiskSphereRelCWOver_of_lt F E (univ : Set X) hr hn

/-- On the closed `(q + r)`-cube, the bundle projection of the characteristic map of
`bundleDiskSphereRelCW` is the base characteristic map evaluated on the first `q` coordinates. -/
theorem discBundleProj_map_bundleDiskSphereRelCW (q : ℕ)
    (c : @RelCWComplex.cell _ _ _ _ (bundleDiskSphereRelCW F E A hr) (thomCellDimension r q))
    {x : Fin (thomCellDimension r q) → ℝ} (hx : x ∈ closedBall 0 1) :
    discBundleProj F E
        (@RelCWComplex.map _ _ _ _ (bundleDiskSphereRelCW F E A hr) (thomCellDimension r q) c x) =
      map q (bundleDiskSphereCellEquiv F E A hr q c)
        ((Fin.appendIsometryOfEq (rfl : q + r = thomCellDimension r q)).symm x).1 := by
  rcases c with ⟨q', hq', j⟩
  obtain rfl := thomCellDimension_injective r hq'
  rw [discBundleProj_apply]
  change (bundleCellMap F E hr ⟨q', rfl, j⟩ x : TotalSpace F E).proj = _
  rw [bundleCellMap_apply_of_mem_closedBall F E hr rfl j hx, cellProdMap_proj]
  rfl

/-- On the closed `(q + r)`-cube, the fibre norm of the characteristic map of
`bundleDiskSphereRelCW` is the norm of `fibreRadialHomeomorph` on the last `r` coordinates. -/
theorem norm_map_bundleDiskSphereRelCW (q : ℕ)
    (c : @RelCWComplex.cell _ _ _ _ (bundleDiskSphereRelCW F E A hr) (thomCellDimension r q))
    {x : Fin (thomCellDimension r q) → ℝ} (hx : x ∈ closedBall 0 1) :
    ‖(@RelCWComplex.map _ _ _ _ (bundleDiskSphereRelCW F E A hr)
        (thomCellDimension r q) c x : TotalSpace F E).2‖ =
      ‖fibreRadialHomeomorph F hr
        ((Fin.appendIsometryOfEq (rfl : q + r = thomCellDimension r q)).symm x).2‖ := by
  rcases c with ⟨q', hq', j⟩
  obtain rfl := thomCellDimension_injective r hq'
  change ‖(bundleCellMap F E hr ⟨q', rfl, j⟩ x : TotalSpace F E).2‖ = _
  rw [bundleCellMap_apply_of_mem_closedBall F E hr rfl j hx, norm_cellProdMap_snd]
  rfl

/-- The open `(q + r)`-cell of `bundleDiskSphereRelCW` over a base `q`-cell `j` consists of the
vectors of norm strictly less than `1` lying over `openCell q j`. -/
theorem openCell_bundleDiskSphereRelCW (q : ℕ)
    (c : @RelCWComplex.cell _ _ _ _ (bundleDiskSphereRelCW F E A hr) (thomCellDimension r q)) :
    @RelCWComplex.openCell _ _ _ _ (bundleDiskSphereRelCW F E A hr) (thomCellDimension r q) c =
      {v : discBundle F E |
        v.1.proj ∈ openCell q (bundleDiskSphereCellEquiv F E A hr q c) ∧ ‖v.1.2‖ < 1} := by
  rcases c with ⟨q', hq', j⟩
  obtain rfl := thomCellDimension_injective r hq'
  exact image_ball_bundleCellMap F E hr rfl j

/-- The closed `(q + r)`-cell of `bundleDiskSphereRelCW` over a base `q`-cell `j` is the preimage
`π_D ⁻¹' closedCell q j`. -/
theorem closedCell_bundleDiskSphereRelCW (q : ℕ)
    (c : @RelCWComplex.cell _ _ _ _ (bundleDiskSphereRelCW F E A hr) (thomCellDimension r q)) :
    @RelCWComplex.closedCell _ _ _ _ (bundleDiskSphereRelCW F E A hr) (thomCellDimension r q) c =
      discBundleProj F E ⁻¹' closedCell q (bundleDiskSphereCellEquiv F E A hr q c) := by
  rcases c with ⟨q', hq', j⟩
  obtain rfl := thomCellDimension_injective r hq'
  exact image_closedBall_bundleCellMap F E hr rfl j

/-- **Boundary formula `(∂D^q × D^r) ∪ (D^q × ∂D^r)` for bundle cells.** The cell frontier of the
`(q + r)`-cell of `bundleDiskSphereRelCW` over a base `q`-cell `j` is the union of `D(E)` over
`cellFrontier q j` and `S(E)` over `closedCell q j`. -/
theorem cellFrontier_bundleDiskSphereRelCW (q : ℕ)
    (c : @RelCWComplex.cell _ _ _ _ (bundleDiskSphereRelCW F E A hr) (thomCellDimension r q)) :
    @RelCWComplex.cellFrontier _ _ _ _ (bundleDiskSphereRelCW F E A hr) (thomCellDimension r q) c =
      discBundleProj F E ⁻¹' cellFrontier q (bundleDiskSphereCellEquiv F E A hr q c) ∪
        (Subtype.val ⁻¹' sphereBundle F E ∩
          discBundleProj F E ⁻¹' closedCell q (bundleDiskSphereCellEquiv F E A hr q c)) := by
  rcases c with ⟨q', hq', j⟩
  obtain rfl := thomCellDimension_injective r hq'
  exact image_sphere_bundleCellMap F E hr rfl j

theorem finiteDimensional_bundleDiskSphereRelCW
    [RelCWComplex.FiniteDimensional (univ : Set X)] :
    @RelCWComplex.FiniteDimensional _ _ _ _ (bundleDiskSphereRelCW F E A hr) :=
  @RelCWComplex.FiniteDimensional.mk _ _ _ _ (bundleDiskSphereRelCW F E A hr)
    (finiteDimensional_bundleDiskSphereRelCWOver F E (univ : Set X) hr).eventually_isEmpty_cell

theorem finiteType_bundleDiskSphereRelCW [RelCWComplex.FiniteType (univ : Set X)] :
    @RelCWComplex.FiniteType _ _ _ _ (bundleDiskSphereRelCW F E A hr) :=
  @RelCWComplex.FiniteType.mk _ _ _ _ (bundleDiskSphereRelCW F E A hr)
    (finiteType_bundleDiskSphereRelCWOver F E (univ : Set X) hr).finite_cell

theorem finite_bundleDiskSphereRelCW [RelCWComplex.Finite (univ : Set X)] :
    @RelCWComplex.Finite _ _ _ _ (bundleDiskSphereRelCW F E A hr) :=
  @RelCWComplex.Finite.mk _ _ _ _ (bundleDiskSphereRelCW F E A hr)
    (finiteDimensional_bundleDiskSphereRelCW F E A hr)
    (finiteType_bundleDiskSphereRelCW F E A hr)

end Univ

end API

end TauCeti
