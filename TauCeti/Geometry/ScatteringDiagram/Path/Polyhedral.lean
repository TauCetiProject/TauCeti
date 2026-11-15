/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity (Gemini 4 Carbon)
-/
module

public import TauCeti.Geometry.ScatteringDiagram.Path.Word
public import TauCeti.Geometry.Convex.PolyhedralComplex.Subdivision
public import TauCeti.Geometry.Convex.PolyhedralComplex.Map

/-!
# Crossing words across walls of a finite polyhedral complex

Distinct walls of a `FinitePolyhedralComplex` automatically have disjoint intrinsic interiors
(`FinitePolyhedralComplex.pairwise_disjoint_intrinsicInterior_walls`), so every admissible polygonal
path in the wall complement carries a crossing word `FinitePolyhedralComplex.crossingWord` in
`FreeGroup C.walls`.

For a wall coorientation (`FinitePolyhedralComplex.IsWallCoorientation`), rank-nullity identifies
each normal functional's kernel with the wall's affine direction and relates any two coorientations
on nested walls by a nonzero scalar. This yields functoriality of `crossingWord`:
* under passing to a subcomplex (`crossingWord_ofSubcomplex`), killing walls outside the subcomplex;
* under subdividing the polyhedral complex (`crossingWord_ofComplexSubdivision`), sending walls
  inside higher-dimensional coarse cells to `1` and subdivided pieces of a coarse wall `w` to
  `FreeGroup.of w` or `(FreeGroup.of w)⁻¹` according as coorientations agree or disagree;
* under `Toric.IntegralAffineEquiv` coordinate transport (`crossingWord_image`), mapping generators
  along `C.wallsEquiv e`.

Finally, `TauCeti.FourHalfAxesExample` evaluates `crossingWord` on the counterclockwise boundary of
`[-1, 1]²` in `ℝ × ℝ` across the four closed coordinate half-axes, verifies its restriction to the
positive `x`-half-axis `(of ())⁻¹ ≠ 1`, and checks that identifying opposite half-axes produces the
nontrivial commutator `(of false)⁻¹ * (of true)⁻¹ * of false * of true ≠ 1` in `FreeGroup Bool`.

## References

* M. Kontsevich and Y. Soibelman, *Affine structures and non-Archimedean analytic spaces*, §2.2.
* M. Gross, *Tropical Geometry and Mirror Symmetry*, §6.2.
-/

public section

noncomputable section

open Set

namespace TauCeti.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- An allowed endpoint for a finite polyhedral complex `C`: an ambient point lying on no wall of
`C`. -/
abbrev WallComplement (C : FinitePolyhedralComplex h) : Type _ :=
  _root_.TauCeti.WallComplement (Subtype.val : C.walls → Set V)

/-- Distinct walls of a finite polyhedral complex have disjoint intrinsic interiors. -/
theorem pairwise_disjoint_intrinsicInterior_walls (C : FinitePolyhedralComplex h) :
    Pairwise fun w₁ w₂ : C.walls =>
      Disjoint (intrinsicInterior ℝ (w₁ : Set V)) (intrinsicInterior ℝ (w₂ : Set V)) :=
  fun w₁ w₂ hne => C.disjoint_intrinsicInterior
    (mem_cellsOfCodimension.mp w₁.2).1 (mem_cellsOfCodimension.mp w₂.2).1
    (Subtype.coe_ne_coe.mpr hne)

/-- A family of wall coorientations on `C` assigns to each wall `w ∈ C.walls` a nonzero real linear
functional vanishing on the wall's affine direction. -/
def IsWallCoorientation (C : FinitePolyhedralComplex h)
    (ν : C.walls → V →ₗ[ℝ] ℝ) : Prop :=
  ∀ w : C.walls, ν w ≠ 0 ∧ (affineSpan ℝ (w : Set V)).direction ≤ LinearMap.ker (ν w)

/-- By rank-nullity, the kernel of a wall coorientation functional equals the wall's affine
direction. -/
theorem IsWallCoorientation.ker_eq {C : FinitePolyhedralComplex h} {ν : C.walls → V →ₗ[ℝ] ℝ}
    (hν : C.IsWallCoorientation ν) (w : C.walls) :
    LinearMap.ker (ν w) = (affineSpan ℝ (w : Set V)).direction := by
  have := h.finiteDimensional
  obtain ⟨hnez, hle⟩ := hν w
  obtain ⟨-, hdim⟩ := mem_cellsOfCodimension.mp w.2
  have hsurj : LinearMap.range (ν w) = ⊤ := by
    obtain ⟨v, hv⟩ : ∃ v, ν w v ≠ 0 := by
      by_contra! hall
      exact hnez (LinearMap.ext hall)
    refine top_unique fun r _ => ⟨(r / ν w v) • v, ?_⟩
    simp [div_mul_cancel₀ r hv]
  have hker_dim : Module.finrank ℝ (LinearMap.ker (ν w)) + 1 = Module.finrank ℝ V := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (ν w)
    rw [hsurj, finrank_top, Module.finrank_self, add_comm] at hrn
    exact hrn
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

/-- Two wall coorientations on nested walls of two complexes are nonzero scalar multiples of each
other. -/
theorem IsWallCoorientation.exists_ne_zero_smul_eq {C C' : FinitePolyhedralComplex h}
    {ν : C.walls → V →ₗ[ℝ] ℝ} {ν' : C'.walls → V →ₗ[ℝ] ℝ}
    (hν : C.IsWallCoorientation ν) (hν' : C'.IsWallCoorientation ν')
    {w : C.walls} {w' : C'.walls} (hsub : (w' : Set V) ⊆ (w : Set V)) :
    ∃ c : ℝ, c ≠ 0 ∧ ν' w' = c • ν w := by
  have := h.finiteDimensional
  obtain ⟨-, hdim⟩ := mem_cellsOfCodimension.mp w.2
  obtain ⟨-, hdim'⟩ := mem_cellsOfCodimension.mp w'.2
  have hdir : (affineSpan ℝ (w' : Set V)).direction = (affineSpan ℝ (w : Set V)).direction :=
    Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le (affineSpan_mono ℝ hsub))
      (by omega)
  have hker : LinearMap.ker (ν' w') = LinearMap.ker (ν w) := by
    rw [hν'.ker_eq w', hν.ker_eq w, hdir]
  obtain ⟨v, hv⟩ : ∃ v, ν w v ≠ 0 := by
    by_contra! hall
    exact (hν w).1 (LinearMap.ext hall)
  have hv' : ν' w' v ≠ 0 := fun hz => hv (LinearMap.mem_ker.mp (hker ▸ LinearMap.mem_ker.mpr hz))
  refine ⟨ν' w' v / ν w v, div_ne_zero hv' hv, LinearMap.ext fun u => ?_⟩
  have hu_ker : u - (ν w u / ν w v) • v ∈ LinearMap.ker (ν' w') := by
    rw [hker, LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hv, sub_self]
  rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, sub_eq_zero] at hu_ker
  rw [LinearMap.smul_apply, smul_eq_mul, hu_ker]
  ring

/-- The crossing word in `FreeGroup C.walls` of an admissible polygonal path for `C`. -/
def crossingWord (C : FinitePolyhedralComplex h) (ν : C.walls → V →ₗ[ℝ] ℝ)
    {x y : C.WallComplement} (p : AdmissiblePLPath x y) : FreeGroup C.walls :=
  p.crossingWord ν C.pairwise_disjoint_intrinsicInterior_walls

@[simp]
theorem crossingWord_nil (C : FinitePolyhedralComplex h) (ν : C.walls → V →ₗ[ℝ] ℝ)
    (x : C.WallComplement) :
    C.crossingWord ν (Quiver.Path.nil : AdmissiblePLPath x x) = 1 :=
  Quiver.Path.crossingWord_nil ν _

@[simp]
theorem crossingWord_cons (C : FinitePolyhedralComplex h) (ν : C.walls → V →ₗ[ℝ] ℝ)
    {x y z : C.WallComplement} (p : AdmissiblePLPath x y) (e : y ⟶ z) :
    C.crossingWord ν (p.cons e) =
      _root_.TauCeti.WallComplement.segmentCrossingWord ν
        C.pairwise_disjoint_intrinsicInterior_walls e * C.crossingWord ν p :=
  Quiver.Path.crossingWord_cons ν _ p e

@[simp]
theorem crossingWord_toPath (C : FinitePolyhedralComplex h) (ν : C.walls → V →ₗ[ℝ] ℝ)
    {x y : C.WallComplement} (e : x ⟶ y) :
    C.crossingWord ν e.toPath =
      _root_.TauCeti.WallComplement.segmentCrossingWord ν
        C.pairwise_disjoint_intrinsicInterior_walls e :=
  Quiver.Path.crossingWord_toPath ν _ e

@[simp]
theorem crossingWord_comp (C : FinitePolyhedralComplex h) (ν : C.walls → V →ₗ[ℝ] ℝ)
    {x y z : C.WallComplement} (p : AdmissiblePLPath x y) (q : AdmissiblePLPath y z) :
    C.crossingWord ν (p.comp q) = C.crossingWord ν q * C.crossingWord ν p :=
  Quiver.Path.crossingWord_comp ν _ p q

@[simp]
theorem crossingWord_smul (C : FinitePolyhedralComplex h) (ν : C.walls → V →ₗ[ℝ] ℝ)
    (r : C.walls → ℝ) (hr : ∀ w, 0 < r w) {x y : C.WallComplement} (p : AdmissiblePLPath x y) :
    C.crossingWord (fun w => r w • ν w) p = C.crossingWord ν p :=
  Quiver.Path.crossingWord_smul ν _ r hr p

@[simp]
theorem crossingWord_reverse {C : FinitePolyhedralComplex h} {ν : C.walls → V →ₗ[ℝ] ℝ}
    (hν : C.IsWallCoorientation ν) {x y : C.WallComplement} (p : AdmissiblePLPath x y) :
    C.crossingWord ν p.reverse = (C.crossingWord ν p)⁻¹ :=
  Quiver.Path.crossingWord_reverse ν _ hν.ker_eq p

theorem crossingWord_eq_of_isSubdivision (C : FinitePolyhedralComplex h) (ν : C.walls → V →ₗ[ℝ] ℝ)
    {x y : C.WallComplement} {p q : AdmissiblePLPath x y} (hpq : p.IsSubdivision q) :
    C.crossingWord ν p = C.crossingWord ν q :=
  hpq.crossingWord_eq ν _

@[simp]
theorem lift_crossingWord_eq_wallPathProduct {G : Type*} [Group G]
    (C : FinitePolyhedralComplex h) (ν : C.walls → V →ₗ[ℝ] ℝ) (label : C.walls → G)
    (hcomm : ∀ w₁ w₂ : C.walls,
      affineSpan ℝ (w₁ : Set V) = affineSpan ℝ (w₂ : Set V) → Commute (label w₁) (label w₂))
    {x y : C.WallComplement} (p : AdmissiblePLPath x y) :
    FreeGroup.lift label (C.crossingWord ν p) = p.wallPathProduct ν label hcomm :=
  Quiver.Path.lift_crossingWord_eq_wallPathProduct ν _ label hcomm p

/-! ### Subcomplex wall deletion -/

/-- Restrict an allowed vertex from `C` to a subcomplex `D` of `C`. -/
abbrev restrictEndpointOfSubcomplex {C D : FinitePolyhedralComplex h} (hDC : D.IsSubcomplex C)
    (x : C.WallComplement) : D.WallComplement :=
  x.comap (Set.inclusion (hDC.cellsOfCodimension_subset 1))

/-- Restrict an admissible polygonal path from `C` to a subcomplex `D` of `C`. -/
def restrictPathOfSubcomplex {C D : FinitePolyhedralComplex h} (hDC : D.IsSubcomplex C)
    {x y : C.WallComplement} (p : AdmissiblePLPath x y) :
    AdmissiblePLPath (restrictEndpointOfSubcomplex hDC x) (restrictEndpointOfSubcomplex hDC y) :=
  p.restrictWalls (Set.inclusion (hDC.cellsOfCodimension_subset 1))

/-- Generator map `C.walls → FreeGroup D.walls` sending walls of a subcomplex `D` to themselves
and killing walls outside `D.walls`. -/
def IsSubcomplex.wallWordMap {C D : FinitePolyhedralComplex h} (_ : D.IsSubcomplex C)
    (w : C.walls) : FreeGroup D.walls :=
  open scoped Classical in
  if hw : (w : Set V) ∈ D.walls then FreeGroup.of ⟨w, hw⟩ else 1

@[simp]
theorem IsSubcomplex.wallWordMap_of_mem {C D : FinitePolyhedralComplex h} (hDC : D.IsSubcomplex C)
    {w : C.walls} (hw : (w : Set V) ∈ D.walls) :
    hDC.wallWordMap w = FreeGroup.of ⟨w, hw⟩ := by
  simp [wallWordMap, hw]

@[simp]
theorem IsSubcomplex.wallWordMap_of_notMem {C D : FinitePolyhedralComplex h}
    (hDC : D.IsSubcomplex C) {w : C.walls} (hw : (w : Set V) ∉ D.walls) :
    hDC.wallWordMap w = 1 := by
  simp [wallWordMap, hw]

/-- Passing from `C` to a subcomplex `D` maps `crossingWord` by `FreeGroup.lift hDC.wallWordMap`,
killing all walls of `C` not belonging to `D`. -/
@[simp]
theorem crossingWord_ofSubcomplex {C D : FinitePolyhedralComplex h} (hDC : D.IsSubcomplex C)
    (ν : C.walls → V →ₗ[ℝ] ℝ) {x y : C.WallComplement} (p : AdmissiblePLPath x y) :
    D.crossingWord (fun w => ν ⟨w, hDC.cellsOfCodimension_subset 1 w.2⟩)
        (restrictPathOfSubcomplex hDC p) =
      FreeGroup.lift hDC.wallWordMap (C.crossingWord ν p) := by
  refine Quiver.Path.crossingWord_restrictWalls_eq_lift ν
    C.pairwise_disjoint_intrinsicInterior_walls
    (Set.inclusion_injective (hDC.cellsOfCodimension_subset 1)) (fun w => ?_) (fun w hw => ?_) p
  · exact hDC.wallWordMap_of_mem w.2
  · exact hDC.wallWordMap_of_notMem fun hwD => hw ⟨⟨w, hwD⟩, rfl⟩

/-! ### Functoriality under polyhedral complex subdivision -/

namespace IsSubdivision

/-- Subdividing a complex can only enlarge the singular support of its wall family. -/
theorem singularSupport_walls_subset {C C' : FinitePolyhedralComplex h}
    (hsub : C'.IsSubdivision C) :
    singularSupport (Subtype.val : C.walls → Set V) ⊆
      singularSupport (Subtype.val : C'.walls → Set V) := by
  intro z hz
  rcases mem_singularSupport.mp hz with ⟨w, hzw⟩ | ⟨w₁, w₂, hne, hz₁, hz₂⟩
  · have hcl : IsClosed (w : Set V) :=
      (C.isConvexPolyhedron (mem_cellsOfCodimension.mp w.2).1).isClosed
    obtain ⟨w', hw', hsubw, hspan, hzw'⟩ :=
      hsub.exists_mem_cellsOfCodimension_subset w.2 (intrinsicFrontier_subset hcl hzw)
    refine mem_singularSupport.mpr (.inl ⟨⟨w', hw'⟩, ?_⟩)
    rw [← intrinsicClosure_sdiff_intrinsicInterior] at hzw ⊢
    exact ⟨subset_intrinsicClosure hzw', fun hint =>
      hzw.2 (TauCeti.intrinsicInterior_mono_of_affineSpan_eq hsubw hspan hint)⟩
  · obtain ⟨w₁', hw₁', -, hspan₁, hz₁'⟩ := hsub.exists_mem_cellsOfCodimension_subset w₁.2 hz₁
    obtain ⟨w₂', hw₂', -, hspan₂, hz₂'⟩ := hsub.exists_mem_cellsOfCodimension_subset w₂.2 hz₂
    refine mem_singularSupport.mpr (.inr ⟨⟨w₁', hw₁'⟩, ⟨w₂', hw₂'⟩, ?_, hz₁', hz₂'⟩)
    rwa [hspan₁, hspan₂]

/-- An allowed endpoint for a subdivision `C'` of `C` is automatically an allowed endpoint for `C`.
-/
abbrev wallComplement {C C' : FinitePolyhedralComplex h} (hsub : C'.IsSubdivision C)
    (x : C'.WallComplement) : C.WallComplement where
  val := x.val
  notMem w hw := by
    obtain ⟨w', hw', -, -, hxw'⟩ := hsub.exists_mem_cellsOfCodimension_subset w.2 hw
    exact x.notMem ⟨w', hw'⟩ hxw'

/-- An admissible segment for a subdivision `C'` of `C` is automatically admissible for `C`. -/
theorem admissibleSegment {C C' : FinitePolyhedralComplex h} (hsub : C'.IsSubdivision C)
    {x y : C'.WallComplement} (a : _root_.TauCeti.WallComplement.AdmissibleSegment x y) :
    _root_.TauCeti.WallComplement.AdmissibleSegment (hsub.wallComplement x)
      (hsub.wallComplement y) where
  transverse w := by
    rintro ⟨t, ht, hzw⟩
    obtain ⟨w', hw', -, hspan, hzw'⟩ := hsub.exists_mem_cellsOfCodimension_subset w.2 hzw
    rw [← hspan]
    exact a.transverse ⟨w', hw'⟩ ⟨t, ht, hzw'⟩
  regular t ht hs := a.regular t ht (hsub.singularSupport_walls_subset hs)

/-- The quiver prefunctor viewing paths admissible for a subdivision `C'` as paths admissible for
`C`. -/
abbrev wallPrefunctor {C C' : FinitePolyhedralComplex h} (hsub : C'.IsSubdivision C) :
    C'.WallComplement ⥤q C.WallComplement where
  obj x := hsub.wallComplement x
  map a := ⟨hsub.admissibleSegment a.down⟩

/-- View an admissible polygonal path for `C'` as an admissible polygonal path for `C`. -/
def mapPath {C C' : FinitePolyhedralComplex h} (hsub : C'.IsSubdivision C)
    {x y : C'.WallComplement} (p : AdmissiblePLPath x y) :
    AdmissiblePLPath (hsub.wallComplement x) (hsub.wallComplement y) :=
  hsub.wallPrefunctor.mapPath p

/-- Generator map `C'.walls → FreeGroup C.walls` for a complex subdivision `C'.IsSubdivision C`:
sends `w' ∈ C'.walls` to `FreeGroup.of w` when `w' ⊆ w` and `ν' w'` is a positive multiple of
`ν w`, to `(FreeGroup.of w)⁻¹` when `w' ⊆ w` and their coorientations disagree, and to `1` when
no wall of `C` contains `w'`. -/
def wallWordMap {C C' : FinitePolyhedralComplex h} (_ : C'.IsSubdivision C)
    (ν' : C'.walls → V →ₗ[ℝ] ℝ) (ν : C.walls → V →ₗ[ℝ] ℝ) (w' : C'.walls) :
    FreeGroup C.walls :=
  open scoped Classical in
  if hex : ∃ w : C.walls, (w' : Set V) ⊆ (w : Set V) then
    if ∃ c : ℝ, 0 < c ∧ ν' w' = c • ν hex.choose then
      FreeGroup.of hex.choose
    else
      (FreeGroup.of hex.choose)⁻¹
  else 1

theorem eq_of_wall_subset {C C' : FinitePolyhedralComplex h}
    {w' : C'.walls} {w₁ w₂ : C.walls}
    (h₁ : (w' : Set V) ⊆ (w₁ : Set V)) (h₂ : (w' : Set V) ⊆ (w₂ : Set V)) : w₁ = w₂ :=
  Subtype.ext (C.eq_of_subset_of_mem_cellsOfCodimension
    (C'.nonempty w' (mem_cellsOfCodimension.mp w'.2).1)
    (mem_cellsOfCodimension.mp w'.2).2 w₁.2 w₂.2 h₁ h₂)

/-- When `w' ⊆ w` and `ν' w' = c • ν w` with `0 < c`, `wallWordMap` sends `w'` to `FreeGroup.of w`.
-/
theorem wallWordMap_of_subset_pos {C C' : FinitePolyhedralComplex h} (hsub : C'.IsSubdivision C)
    {ν' : C'.walls → V →ₗ[ℝ] ℝ} {ν : C.walls → V →ₗ[ℝ] ℝ}
    {w' : C'.walls} {w : C.walls} (hw : (w' : Set V) ⊆ (w : Set V))
    {c : ℝ} (hc : 0 < c) (hνc : ν' w' = c • ν w) :
    hsub.wallWordMap ν' ν w' = FreeGroup.of w := by
  unfold wallWordMap
  split_ifs with hex hpos
  · exact congrArg FreeGroup.of (eq_of_wall_subset hex.choose_spec hw)
  · exfalso
    exact hpos ⟨c, hc, eq_of_wall_subset hex.choose_spec hw ▸ hνc⟩
  · exact (hex ⟨w, hw⟩).elim

/-- When `w' ⊆ w`, `ν w ≠ 0`, and `ν' w' = c • ν w` with `c < 0`, `wallWordMap` sends `w'` to
`(FreeGroup.of w)⁻¹`. -/
theorem wallWordMap_of_subset_neg {C C' : FinitePolyhedralComplex h} (hsub : C'.IsSubdivision C)
    {ν' : C'.walls → V →ₗ[ℝ] ℝ} {ν : C.walls → V →ₗ[ℝ] ℝ}
    {w' : C'.walls} {w : C.walls} (hνw : ν w ≠ 0) (hw : (w' : Set V) ⊆ (w : Set V))
    {c : ℝ} (hc : c < 0) (hνc : ν' w' = c • ν w) :
    hsub.wallWordMap ν' ν w' = (FreeGroup.of w)⁻¹ := by
  unfold wallWordMap
  split_ifs with hex hpos
  · exfalso
    obtain ⟨c', hc', hνc'⟩ := eq_of_wall_subset hex.choose_spec hw ▸ hpos
    obtain ⟨v, hv⟩ : ∃ v, ν w v ≠ 0 := by
      by_contra! hall
      exact hνw (LinearMap.ext hall)
    have hmul : c * ν w v = c' * ν w v := by
      simpa [LinearMap.smul_apply, smul_eq_mul] using
        LinearMap.congr_fun (hνc.symm.trans hνc') v
    linarith [mul_right_cancel₀ hv hmul]
  · exact congrArg (fun u => (FreeGroup.of u)⁻¹) (eq_of_wall_subset hex.choose_spec hw)
  · exact (hex ⟨w, hw⟩).elim

/-- When no wall of `C` contains `w'`, `wallWordMap` sends `w'` to `1`. -/
@[simp]
theorem wallWordMap_of_forall_not_subset {C C' : FinitePolyhedralComplex h}
    (hsub : C'.IsSubdivision C) (ν' : C'.walls → V →ₗ[ℝ] ℝ) (ν : C.walls → V →ₗ[ℝ] ℝ)
    {w' : C'.walls} (hw : ∀ w : C.walls, ¬ (w' : Set V) ⊆ (w : Set V)) :
    hsub.wallWordMap ν' ν w' = 1 := by
  simp [wallWordMap, hw]

private theorem neg_ite_sign_of_neg {c v : ℝ} (hc : c < 0) (hv : v ≠ 0) :
    -(if 0 < c * v then -1 else 1 : ℤ) = if 0 < v then -1 else 1 := by
  split_ifs with h1 h2 h2
  · linarith [mul_neg_of_neg_of_pos hc h2]
  · rfl
  · rfl
  · exact (h1 (mul_pos_of_neg_of_neg hc (lt_of_le_of_ne (not_lt.mp h2) hv))).elim

/-- Lifting `crossingEventWord` on a subdivision `C'` by `wallWordMap` recovers the coarse
`crossingEventWord` on `C` at every parameter `t`. -/
theorem lift_crossingEventWord {C C' : FinitePolyhedralComplex h} (hsub : C'.IsSubdivision C)
    {ν' : C'.walls → V →ₗ[ℝ] ℝ} {ν : C.walls → V →ₗ[ℝ] ℝ}
    (hν' : C'.IsWallCoorientation ν') (hν : C.IsWallCoorientation ν)
    {x y : C'.WallComplement} (e : x ⟶ y)
    (e₀ : hsub.wallComplement x ⟶ hsub.wallComplement y) (t : ℝ) :
    FreeGroup.lift (hsub.wallWordMap ν' ν)
        (_root_.TauCeti.WallComplement.crossingEventWord ν'
          C'.pairwise_disjoint_intrinsicInterior_walls e t) =
      _root_.TauCeti.WallComplement.crossingEventWord ν
        C.pairwise_disjoint_intrinsicInterior_walls e₀ t := by
  by_cases hcr' : ∃ w' : C'.walls, (w', t) ∈ _root_.TauCeti.WallComplement.crossings x y
  · obtain ⟨w', hw't⟩ := hcr'
    obtain ⟨htI, hzw'⟩ := (_root_.TauCeti.WallComplement.mem_crossings x y w' t).mp hw't
    rw [_root_.TauCeti.WallComplement.crossingEventWord_of_mem_crossings ν' _ e hw't,
      map_zpow, FreeGroup.lift_apply_of]
    by_cases hex : ∃ w : C.walls, (w' : Set V) ⊆ (w : Set V)
    · obtain ⟨w, hww⟩ := hex
      have hwt : (w, t) ∈ _root_.TauCeti.WallComplement.crossings
          (hsub.wallComplement x) (hsub.wallComplement y) :=
        (_root_.TauCeti.WallComplement.mem_crossings _ _ w t).mpr ⟨htI, hww hzw'⟩
      rw [_root_.TauCeti.WallComplement.crossingEventWord_of_mem_crossings ν _ e₀ hwt]
      obtain ⟨c, hc0, hνc⟩ := hν.exists_ne_zero_smul_eq hν' hww
      have hv_ne : ν w (y.val - x.val) ≠ 0 := fun hz =>
        e₀.down.transverse w ⟨t, htI, hww hzw'⟩ ((hν.ker_eq w) ▸ LinearMap.mem_ker.mpr hz)
      rcases lt_or_gt_of_ne hc0 with hneg | hpos
      · rw [hsub.wallWordMap_of_subset_neg (hν w).1 hww hneg hνc, hνc, LinearMap.smul_apply,
          smul_eq_mul, inv_zpow, ← zpow_neg]
        exact congrArg (FreeGroup.of w ^ ·) (neg_ite_sign_of_neg hneg hv_ne)
      · rw [hsub.wallWordMap_of_subset_pos hww hpos hνc, hνc, LinearMap.smul_apply, smul_eq_mul]
        simp only [mul_pos_iff_of_pos_left hpos]
    · have hex' : ∀ w : C.walls, ¬ (w' : Set V) ⊆ (w : Set V) := fun w hw => hex ⟨w, hw⟩
      rw [hsub.wallWordMap_of_forall_not_subset ν' ν hex', one_zpow]
      refine (_root_.TauCeti.WallComplement.crossingEventWord_eq_one_of_forall_notMem ν _ e₀ t
        fun w hwt => ?_).symm
      obtain ⟨_, hzw⟩ := (_root_.TauCeti.WallComplement.mem_crossings _ _ w t).mp hwt
      obtain ⟨w'', hw'', hsub'', -, hzw''⟩ := hsub.exists_mem_cellsOfCodimension_subset w.2 hzw
      have hw''t : (⟨w'', hw''⟩, t) ∈ _root_.TauCeti.WallComplement.crossings x y :=
        (_root_.TauCeti.WallComplement.mem_crossings x y ⟨w'', hw''⟩ t).mpr ⟨htI, hzw''⟩
      exact hex' w (e.down.eq_of_mem_crossings C'.pairwise_disjoint_intrinsicInterior_walls
        hw't hw''t ▸ hsub'')
  · rw [_root_.TauCeti.WallComplement.crossingEventWord_eq_one_of_forall_notMem ν' _ e t
        fun w' hw' => hcr' ⟨w', hw'⟩, map_one]
    refine (_root_.TauCeti.WallComplement.crossingEventWord_eq_one_of_forall_notMem ν _ e₀ t
      fun w hwt => ?_).symm
    obtain ⟨htI, hzw⟩ := (_root_.TauCeti.WallComplement.mem_crossings _ _ w t).mp hwt
    obtain ⟨w', hw', -, -, hzw'⟩ := hsub.exists_mem_cellsOfCodimension_subset w.2 hzw
    exact hcr' ⟨⟨w', hw'⟩,
      (_root_.TauCeti.WallComplement.mem_crossings x y ⟨w', hw'⟩ t).mpr ⟨htI, hzw'⟩⟩

end IsSubdivision

/-- Subdividing a finite polyhedral complex `C` into `C'` maps the crossing word of any admissible
path for `C'` to its crossing word on `C` via `FreeGroup.lift (hsub.wallWordMap ν' ν)`. -/
theorem crossingWord_ofComplexSubdivision {C C' : FinitePolyhedralComplex h}
    (hsub : C'.IsSubdivision C) {ν' : C'.walls → V →ₗ[ℝ] ℝ} {ν : C.walls → V →ₗ[ℝ] ℝ}
    (hν' : C'.IsWallCoorientation ν') (hν : C.IsWallCoorientation ν)
    {x y : C'.WallComplement} (p : AdmissiblePLPath x y) :
    C.crossingWord ν (hsub.mapPath p) =
      FreeGroup.lift (hsub.wallWordMap ν' ν) (C'.crossingWord ν' p) := by
  induction p with
  | nil => simp [IsSubdivision.mapPath]
  | @cons u v p a ih =>
    rw [IsSubdivision.mapPath, Prefunctor.mapPath_cons, crossingWord_cons, crossingWord_cons,
      map_mul, ← IsSubdivision.mapPath, ih]
    refine congrArg (· * _) ?_
    let a₀ : hsub.wallComplement u ⟶ hsub.wallComplement v := hsub.wallPrefunctor.map a
    have hcover : ∀ t ∈ _root_.TauCeti.WallComplement.orderedCrossingTimes a₀,
        t ∈ _root_.TauCeti.WallComplement.orderedCrossingTimes a := by
      intro t ht
      obtain ⟨w, hwt⟩ := (_root_.TauCeti.WallComplement.mem_orderedCrossingTimes a₀ t).mp ht
      obtain ⟨htI, hzw⟩ := (_root_.TauCeti.WallComplement.mem_crossings _ _ w t).mp hwt
      obtain ⟨w', hw', -, -, hzw'⟩ := hsub.exists_mem_cellsOfCodimension_subset w.2 hzw
      exact (_root_.TauCeti.WallComplement.mem_orderedCrossingTimes a t).mpr
        ⟨⟨w', hw'⟩, (_root_.TauCeti.WallComplement.mem_crossings u v ⟨w', hw'⟩ t).mpr ⟨htI, hzw'⟩⟩
    rw [_root_.TauCeti.WallComplement.segmentCrossingWord_eq_prod_of_crossingTimes ν _ a₀
      (_root_.TauCeti.WallComplement.orderedCrossingTimes a)
      (_root_.TauCeti.WallComplement.pairwise_orderedCrossingTimes a) hcover,
      _root_.TauCeti.WallComplement.segmentCrossingWord_def, map_list_prod, List.map_map]
    exact congrArg List.prod
      (List.map_congr_left fun t _ => (hsub.lift_crossingEventWord hν' hν a a₀ t).symm)

/-! ### Integral affine transport -/

section IntegralAffineTransport

variable {N' U : Type*} [AddCommGroup N'] [NormedAddCommGroup U] [NormedSpace ℝ U]
  {i' : N' →+ U} {h' : TauCeti.Toric.IsIntegralLattice i'}

private theorem toContinuousAffineEquiv_toAffineEquiv (e : Toric.IntegralAffineEquiv h h') :
    e.toContinuousAffineEquiv.toAffineEquiv = e.toAffineEquiv := by
  ext x
  calc
    e.toContinuousAffineEquiv.toAffineEquiv x = e.toContinuousAffineEquiv x := rfl
    _ = e x := congrFun e.coe_toContinuousAffineEquiv x
    _ = e.toContinuousAffineMap x := (e.toContinuousAffineMap_apply x).symm
    _ = e.toContinuousAffineMap.toAffineMap x := rfl
    _ = e.toAffineEquiv.toAffineMap x := congrArg (· x) e.toContinuousAffineMap_toAffineMap
    _ = e.toAffineEquiv x := rfl

theorem coe_wallsEquiv_apply (C : FinitePolyhedralComplex h)
    (e : Toric.IntegralAffineEquiv h h') (w : C.walls) :
    (C.wallsEquiv e w : Set U) = e.toContinuousAffineEquiv '' (w : Set V) := by
  rw [e.coe_toContinuousAffineEquiv]
  exact C.coe_cellsOfCodimensionEquiv_apply e 1 w

/-- Transport an allowed vertex of `C` to `C.image e` along an integral affine equivalence `e`. -/
abbrev imageEndpoint (C : FinitePolyhedralComplex h) (e : Toric.IntegralAffineEquiv h h')
    (x : C.WallComplement) : (C.image e).WallComplement :=
  x.mapReindex e.toContinuousAffineEquiv (C.wallsEquiv e) (C.coe_wallsEquiv_apply e)

/-- Transport an admissible polygonal path of `C` to `C.image e` along an integral affine
equivalence `e`. -/
def imagePath (C : FinitePolyhedralComplex h) (e : Toric.IntegralAffineEquiv h h')
    {x y : C.WallComplement} (p : AdmissiblePLPath x y) :
    AdmissiblePLPath (C.imageEndpoint e x) (C.imageEndpoint e y) :=
  p.affineMapReindex e.toContinuousAffineEquiv (C.wallsEquiv e) (C.coe_wallsEquiv_apply e)

/-- Pushing wall coorientations forward along an integral affine equivalence `e` yields wall
coorientations on `C.image e`. -/
theorem IsWallCoorientation.image {C : FinitePolyhedralComplex h} {ν : C.walls → V →ₗ[ℝ] ℝ}
    (hν : C.IsWallCoorientation ν) (e : Toric.IntegralAffineEquiv h h') :
    (C.image e).IsWallCoorientation
      (fun w' => (ν ((C.wallsEquiv e).symm w')).comp e.toAffineEquiv.linear.symm.toLinearMap) := by
  intro w'
  set w := (C.wallsEquiv e).symm w'
  obtain ⟨hnez, hle⟩ := hν w
  refine ⟨fun hz => hnez ?_, ?_⟩
  · ext v
    simpa using LinearMap.congr_fun hz (e.toAffineEquiv.linear v)
  · have hcoe : (e.toContinuousAffineEquiv : V → U) = e.toAffineEquiv :=
      congrArg DFunLike.coe (toContinuousAffineEquiv_toAffineEquiv e)
    have hw' : (w' : Set U) = e.toAffineEquiv '' (w : Set V) := by
      have h1 := C.coe_wallsEquiv_apply e w
      rw [(C.wallsEquiv e).apply_symm_apply w', hcoe] at h1
      exact h1
    rw [hw', ← AffineEquiv.coe_toAffineMap, ← AffineSubspace.map_span,
      AffineSubspace.map_direction]
    rintro _ ⟨v, hv, rfl⟩
    simpa using hle hv

/-- Transporting an admissible polygonal path along an `IntegralAffineEquiv` `e` maps its
`crossingWord` by `FreeGroup.map (C.wallsEquiv e)` under the pushed-forward coorientations
`ν ∘ e.linear⁻¹`. -/
@[simp]
theorem crossingWord_image (C : FinitePolyhedralComplex h) (ν : C.walls → V →ₗ[ℝ] ℝ)
    (e : Toric.IntegralAffineEquiv h h') {x y : C.WallComplement} (p : AdmissiblePLPath x y) :
    (C.image e).crossingWord
        (fun w' => (ν ((C.wallsEquiv e).symm w')).comp e.toAffineEquiv.linear.symm.toLinearMap)
        (C.imagePath e p) =
      FreeGroup.map (C.wallsEquiv e) (C.crossingWord ν p) := by
  have hlin : e.toAffineEquiv.linear = e.toContinuousAffineEquiv.toAffineEquiv.linear :=
    congrArg AffineEquiv.linear (toContinuousAffineEquiv_toAffineEquiv e).symm
  simp_rw [hlin]
  exact Quiver.Path.crossingWord_affineMapReindex ν C.pairwise_disjoint_intrinsicInterior_walls
    e.toContinuousAffineEquiv (C.wallsEquiv e) (C.coe_wallsEquiv_apply e)
    (C.image e).pairwise_disjoint_intrinsicInterior_walls p

end IntegralAffineTransport

end TauCeti.FinitePolyhedralComplex

/-! ### Worked check: the counterclockwise square loop around the four half-axes in `ℝ × ℝ` -/

namespace TauCeti.FourHalfAxesExample

/-- The four closed coordinate half-axes in `ℝ × ℝ`:
`0` is `{(x, 0) | 0 ≤ x}`, `1` is `{(0, y) | 0 ≤ y}`,
`2` is `{(x, 0) | x ≤ 0}`, and `3` is `{(0, y) | y ≤ 0}`. -/
def halfAxis : Fin 4 → Set (ℝ × ℝ)
  | 0 => {p | 0 ≤ p.1 ∧ p.2 = 0}
  | 1 => {p | p.1 = 0 ∧ 0 ≤ p.2}
  | 2 => {p | p.1 ≤ 0 ∧ p.2 = 0}
  | 3 => {p | p.1 = 0 ∧ p.2 ≤ 0}

/-- Standard coorientations of the four half-axes: `dy` on horizontal half-axes (`0`, `2`) and
`dx` on vertical half-axes (`1`, `3`). -/
def halfAxisNormal : Fin 4 → (ℝ × ℝ) →ₗ[ℝ] ℝ
  | 0 => LinearMap.snd ℝ ℝ ℝ
  | 1 => LinearMap.fst ℝ ℝ ℝ
  | 2 => LinearMap.snd ℝ ℝ ℝ
  | 3 => LinearMap.fst ℝ ℝ ℝ

private theorem origin_notMem_intrinsicInterior (i : Fin 4) :
    ((0 : ℝ), (0 : ℝ)) ∉ intrinsicInterior ℝ (halfAxis i) := by
  intro h0
  fin_cases i
  · have h1 := TauCeti.eq_zero_of_nonneg_of_mem_intrinsicInterior
      (g := (LinearMap.fst ℝ ℝ ℝ).toAffineMap) (fun _ (hp : _ ∈ halfAxis 0) => hp.1) h0 rfl
      (show ((1 : ℝ), (0 : ℝ)) ∈ halfAxis 0 from ⟨zero_le_one, rfl⟩)
    exact one_ne_zero h1
  · have h1 := TauCeti.eq_zero_of_nonneg_of_mem_intrinsicInterior
      (g := (LinearMap.snd ℝ ℝ ℝ).toAffineMap) (fun _ (hp : _ ∈ halfAxis 1) => hp.2) h0 rfl
      (show ((0 : ℝ), (1 : ℝ)) ∈ halfAxis 1 from ⟨rfl, zero_le_one⟩)
    exact one_ne_zero h1
  · have h1 := TauCeti.eq_zero_of_nonneg_of_mem_intrinsicInterior
      (g := (-(LinearMap.fst ℝ ℝ ℝ)).toAffineMap)
      (fun _ (hp : _ ∈ halfAxis 2) => neg_nonneg.mpr hp.1) h0 (by simp)
      (show ((-1 : ℝ), (0 : ℝ)) ∈ halfAxis 2 from ⟨by norm_num, rfl⟩)
    norm_num at h1
  · have h1 := TauCeti.eq_zero_of_nonneg_of_mem_intrinsicInterior
      (g := (-(LinearMap.snd ℝ ℝ ℝ)).toAffineMap)
      (fun _ (hp : _ ∈ halfAxis 3) => neg_nonneg.mpr hp.2) h0 (by simp)
      (show ((0 : ℝ), (-1 : ℝ)) ∈ halfAxis 3 from ⟨rfl, by norm_num⟩)
    norm_num at h1

/-- Distinct coordinate half-axes meet only at `(0, 0)`, which lies in none of their intrinsic
interiors, so the four half-axes have pairwise disjoint intrinsic interiors. -/
theorem pairwise_disjoint_halfAxis :
    Pairwise fun i j =>
      Disjoint (intrinsicInterior ℝ (halfAxis i)) (intrinsicInterior ℝ (halfAxis j)) := by
  intro i j hij
  refine Set.disjoint_left.mpr fun p hpi hpj => origin_notMem_intrinsicInterior i ?_
  have hi := intrinsicInterior_subset hpi
  have hj := intrinsicInterior_subset hpj
  have hp0 : p = (0, 0) := by
    fin_cases i <;> fin_cases j <;> simp [halfAxis] at hi hj
    all_goals first | contradiction | (ext <;> linarith)
  exact hp0 ▸ hpi

private theorem direction_halfAxis_le (i : Fin 4) :
    (affineSpan ℝ (halfAxis i)).direction ≤ LinearMap.ker (halfAxisNormal i) := by
  rw [direction_affineSpan, vectorSpan_def, Submodule.span_le]
  rintro _ ⟨a, ha, b, hb, rfl⟩
  fin_cases i <;> simp_all [halfAxis, halfAxisNormal]

private theorem halfAxisNormal_eq_zero_of_mem_affineSpan (i : Fin 4) {q : ℝ × ℝ}
    (hq : q ∈ affineSpan ℝ (halfAxis i)) : halfAxisNormal i q = 0 := by
  have h0 : (0 : ℝ × ℝ) ∈ affineSpan ℝ (halfAxis i) :=
    subset_affineSpan ℝ _ (by fin_cases i <;> simp [halfAxis])
  have hv := direction_halfAxis_le i
    (direction_affineSpan ℝ (halfAxis i) ▸
      vsub_mem_vectorSpan_of_mem_affineSpan_of_mem_affineSpan hq h0)
  simpa using LinearMap.mem_ker.mp hv

private theorem mem_intrinsicInterior_halfAxis_of_ne_origin {i : Fin 4} {p : ℝ × ℝ}
    (hp : p ∈ halfAxis i) (hne : p ≠ (0, 0)) : p ∈ intrinsicInterior ℝ (halfAxis i) := by
  rw [TauCeti.mem_intrinsicInterior_iff_eventually]
  refine ⟨subset_affineSpan ℝ _ hp, ?_⟩
  fin_cases i
  · have hp1 : 0 < p.1 := lt_of_le_of_ne hp.1 fun h0 => hne (Prod.ext h0.symm hp.2)
    filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hp1] with q hq1 hqA
    exact ⟨hq1.le, halfAxisNormal_eq_zero_of_mem_affineSpan 0 hqA⟩
  · have hp2 : 0 < p.2 := lt_of_le_of_ne hp.2 fun h0 => hne (Prod.ext hp.1 h0.symm)
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hp2] with q hq2 hqA
    exact ⟨halfAxisNormal_eq_zero_of_mem_affineSpan 1 hqA, hq2.le⟩
  · have hp1 : p.1 < 0 := lt_of_le_of_ne hp.1 fun h0 => hne (Prod.ext h0 hp.2)
    filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hp1] with q hq1 hqA
    exact ⟨hq1.le, halfAxisNormal_eq_zero_of_mem_affineSpan 2 hqA⟩
  · have hp2 : p.2 < 0 := lt_of_le_of_ne hp.2 fun h0 => hne (Prod.ext hp.1 h0)
    filter_upwards [(isOpen_lt continuous_snd continuous_const).mem_nhds hp2] with q hq2 hqA
    exact ⟨halfAxisNormal_eq_zero_of_mem_affineSpan 3 hqA, hq2.le⟩

private theorem singularSupport_halfAxis_subset :
    singularSupport halfAxis ⊆ {(0, 0)} := by
  intro p hp
  simp only [Set.mem_singleton_iff]
  by_contra hne
  rcases mem_singularSupport.mp hp with ⟨i, hfr⟩ | ⟨i, j, hdir, hi, hj⟩
  · have hcl : IsClosed (halfAxis i) := by
      fin_cases i
      · exact (isClosed_le continuous_const continuous_fst).inter
          (isClosed_eq continuous_snd continuous_const)
      · exact (isClosed_eq continuous_fst continuous_const).inter
          (isClosed_le continuous_const continuous_snd)
      · exact (isClosed_le continuous_fst continuous_const).inter
          (isClosed_eq continuous_snd continuous_const)
      · exact (isClosed_eq continuous_fst continuous_const).inter
          (isClosed_le continuous_snd continuous_const)
    have hp_mem : p ∈ halfAxis i := intrinsicFrontier_subset hcl hfr
    rw [← intrinsicClosure_sdiff_intrinsicInterior (𝕜 := ℝ)] at hfr
    exact hfr.2 (mem_intrinsicInterior_halfAxis_of_ne_origin hp_mem hne)
  · have hij : i ≠ j := fun heq => hdir (heq ▸ rfl)
    exact Set.disjoint_left.mp (pairwise_disjoint_halfAxis hij)
      (mem_intrinsicInterior_halfAxis_of_ne_origin hi hne)
      (mem_intrinsicInterior_halfAxis_of_ne_origin hj hne)

/-- Top-right corner `(1, 1)` in the complement of the four half-axes. -/
def vPP : WallComplement halfAxis :=
  ⟨(1, 1), fun i h => by fin_cases i <;> simp [halfAxis] at h⟩

/-- Top-left corner `(-1, 1)`. -/
def vNP : WallComplement halfAxis :=
  ⟨(-1, 1), fun i h => by fin_cases i <;> simp [halfAxis] at h⟩

/-- Bottom-left corner `(-1, -1)`. -/
def vNN : WallComplement halfAxis :=
  ⟨(-1, -1), fun i h => by fin_cases i <;> simp [halfAxis] at h⟩

/-- Bottom-right corner `(1, -1)`. -/
def vPN : WallComplement halfAxis :=
  ⟨(1, -1), fun i h => by fin_cases i <;> simp [halfAxis] at h⟩

private theorem crossings_segTop : WallComplement.crossings vPP vNP = {(1, (1 / 2 : ℝ))} := by
  ext ⟨i, t⟩
  simp only [WallComplement.mem_crossings, Set.mem_singleton_iff, Prod.mk.injEq, vPP, vNP,
    AffineMap.lineMap_apply_module', mem_Icc]
  constructor
  · rintro ⟨-, hi⟩
    fin_cases i <;> simp [halfAxis] at hi <;> constructor <;> try rfl
    all_goals linarith
  · rintro ⟨rfl, rfl⟩
    norm_num [halfAxis]

private theorem crossings_segLeft : WallComplement.crossings vNP vNN = {(2, (1 / 2 : ℝ))} := by
  ext ⟨i, t⟩
  simp only [WallComplement.mem_crossings, Set.mem_singleton_iff, Prod.mk.injEq, vNP, vNN,
    AffineMap.lineMap_apply_module', mem_Icc]
  constructor
  · rintro ⟨-, hi⟩
    fin_cases i <;> simp [halfAxis] at hi <;> constructor <;> try rfl
    all_goals linarith
  · rintro ⟨rfl, rfl⟩
    norm_num [halfAxis]

private theorem crossings_segBot : WallComplement.crossings vNN vPN = {(3, (1 / 2 : ℝ))} := by
  ext ⟨i, t⟩
  simp only [WallComplement.mem_crossings, Set.mem_singleton_iff, Prod.mk.injEq, vNN, vPN,
    AffineMap.lineMap_apply_module', mem_Icc]
  constructor
  · rintro ⟨-, hi⟩
    fin_cases i <;> simp [halfAxis] at hi <;> constructor <;> try rfl
    all_goals linarith
  · rintro ⟨rfl, rfl⟩
    norm_num [halfAxis]

private theorem crossings_segRight : WallComplement.crossings vPN vPP = {(0, (1 / 2 : ℝ))} := by
  ext ⟨i, t⟩
  simp only [WallComplement.mem_crossings, Set.mem_singleton_iff, Prod.mk.injEq, vPN, vPP,
    AffineMap.lineMap_apply_module', mem_Icc]
  constructor
  · rintro ⟨-, hi⟩
    fin_cases i <;> simp [halfAxis] at hi <;> constructor <;> try rfl
    all_goals linarith
  · rintro ⟨rfl, rfl⟩
    norm_num [halfAxis]

/-- Top edge `(1, 1) → (-1, 1)` of the counterclockwise square loop. -/
def segTop : vPP ⟶ vNP := ⟨{
  transverse i := fun ⟨t, ht, hi⟩ hdir => by
    have hmem : (i, t) ∈ WallComplement.crossings vPP vNP :=
      (WallComplement.mem_crossings vPP vNP i t).mpr ⟨ht, hi⟩
    rw [crossings_segTop, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    have hker := direction_halfAxis_le _ (hmem.1 ▸ hdir)
    norm_num [halfAxisNormal, vPP, vNP] at hker
  regular t _ hs := by
    have h0 := Set.mem_singleton_iff.mp (singularSupport_halfAxis_subset hs)
    have h2 := congrArg Prod.snd h0
    norm_num [vPP, vNP, AffineMap.lineMap_apply_module'] at h2 }⟩

/-- Left edge `(-1, 1) → (-1, -1)` of the counterclockwise square loop. -/
def segLeft : vNP ⟶ vNN := ⟨{
  transverse i := fun ⟨t, ht, hi⟩ hdir => by
    have hmem : (i, t) ∈ WallComplement.crossings vNP vNN :=
      (WallComplement.mem_crossings vNP vNN i t).mpr ⟨ht, hi⟩
    rw [crossings_segLeft, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    have hker := direction_halfAxis_le _ (hmem.1 ▸ hdir)
    norm_num [halfAxisNormal, vNP, vNN] at hker
  regular t _ hs := by
    have h0 := Set.mem_singleton_iff.mp (singularSupport_halfAxis_subset hs)
    have h1 := congrArg Prod.fst h0
    norm_num [vNP, vNN, AffineMap.lineMap_apply_module'] at h1 }⟩

/-- Bottom edge `(-1, -1) → (1, -1)` of the counterclockwise square loop. -/
def segBot : vNN ⟶ vPN := ⟨{
  transverse i := fun ⟨t, ht, hi⟩ hdir => by
    have hmem : (i, t) ∈ WallComplement.crossings vNN vPN :=
      (WallComplement.mem_crossings vNN vPN i t).mpr ⟨ht, hi⟩
    rw [crossings_segBot, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    have hker := direction_halfAxis_le _ (hmem.1 ▸ hdir)
    norm_num [halfAxisNormal, vNN, vPN] at hker
  regular t _ hs := by
    have h0 := Set.mem_singleton_iff.mp (singularSupport_halfAxis_subset hs)
    have h2 := congrArg Prod.snd h0
    norm_num [vNN, vPN, AffineMap.lineMap_apply_module'] at h2 }⟩

/-- Right edge `(1, -1) → (1, 1)` of the counterclockwise square loop. -/
def segRight : vPN ⟶ vPP := ⟨{
  transverse i := fun ⟨t, ht, hi⟩ hdir => by
    have hmem : (i, t) ∈ WallComplement.crossings vPN vPP :=
      (WallComplement.mem_crossings vPN vPP i t).mpr ⟨ht, hi⟩
    rw [crossings_segRight, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
    have hker := direction_halfAxis_le _ (hmem.1 ▸ hdir)
    norm_num [halfAxisNormal, vPN, vPP] at hker
  regular t _ hs := by
    have h0 := Set.mem_singleton_iff.mp (singularSupport_halfAxis_subset hs)
    have h1 := congrArg Prod.fst h0
    norm_num [vPN, vPP, AffineMap.lineMap_apply_module'] at h1 }⟩

/-- The counterclockwise boundary of `[-1, 1]²` based at `(1, 1)`. -/
def squareLoop : AdmissiblePLPath vPP vPP :=
  (((segTop.toPath.cons segLeft).cons segBot).cons segRight)

/-- The counterclockwise square loop around `(0, 0)` crosses the positive `y`-, negative `x`-,
negative `y`-, and positive `x`-half-axes in order, producing the crossing word
`(of 0)⁻¹ * (of 3)⁻¹ * of 2 * of 1` in `FreeGroup (Fin 4)`. -/
theorem crossingWord_squareLoop :
    squareLoop.crossingWord halfAxisNormal pairwise_disjoint_halfAxis =
      (FreeGroup.of 0)⁻¹ * ((FreeGroup.of 3)⁻¹ * (FreeGroup.of 2 * FreeGroup.of 1)) := by
  simp only [squareLoop, Quiver.Path.crossingWord_cons, Quiver.Path.crossingWord_toPath,
    WallComplement.segmentCrossingWord_of_unique_crossing _ _ segTop crossings_segTop,
    WallComplement.segmentCrossingWord_of_unique_crossing _ _ segLeft crossings_segLeft,
    WallComplement.segmentCrossingWord_of_unique_crossing _ _ segBot crossings_segBot,
    WallComplement.segmentCrossingWord_of_unique_crossing _ _ segRight crossings_segRight]
  split_ifs <;> norm_num [halfAxisNormal, vPP, vNP, vNN, vPN] at *

/-- Restricting the four half-axes to the single positive `x`-half-axis `{(x, 0) | 0 ≤ x}`
cooriented by `dy` sends the counterclockwise square loop's crossing word to `(of ())⁻¹`,
distinct from the constant loop's word `1`. -/
theorem crossingWord_squareLoop_restrict_posX :
    (squareLoop.restrictWalls (fun _ : Unit => (0 : Fin 4))).crossingWord
        (halfAxisNormal ∘ fun _ : Unit => 0)
        (pairwise_disjoint_halfAxis.comp_of_injective fun _ _ _ => Subsingleton.elim _ _) =
      (FreeGroup.of ())⁻¹ ∧
      (FreeGroup.of () : FreeGroup Unit)⁻¹ ≠ 1 := by
  have hword :
      (squareLoop.restrictWalls (fun _ : Unit => (0 : Fin 4))).crossingWord
        (halfAxisNormal ∘ fun _ : Unit => 0)
        (pairwise_disjoint_halfAxis.comp_of_injective fun _ _ _ => Subsingleton.elim _ _) =
      (FreeGroup.of ())⁻¹ := by
    rw [Quiver.Path.crossingWord_restrictWalls_eq_lift halfAxisNormal pairwise_disjoint_halfAxis
        (f := fun _ : Unit => (0 : Fin 4)) (fun _ _ _ => Subsingleton.elim _ _)
        (g := fun i => if i = 0 then FreeGroup.of () else 1)
        (fun _ => rfl)
        (fun i hi => by
          split_ifs with h0
          · exact (hi ⟨(), h0.symm⟩).elim
          · rfl)
        squareLoop,
      crossingWord_squareLoop]
    simp
  refine ⟨hword, fun heq => ?_⟩
  have hhom := congrArg (FreeGroup.lift fun _ : Unit => Multiplicative.ofAdd (1 : ℤ)) heq
  simp only [map_inv, FreeGroup.lift_apply_of, map_one] at hhom
  have hadd := congrArg Multiplicative.toAdd hhom
  norm_num at hadd

/-- Identifying opposite half-axes into horizontal (`false`) and vertical (`true`) labels maps the
square loop's crossing word to the nontrivial commutator `(of false)⁻¹ * (of true)⁻¹ * of false *
of true ≠ 1` in `FreeGroup Bool`. -/
theorem lift_crossingWord_squareLoop_commutator_ne_one :
    let axisLabel : Fin 4 → FreeGroup Bool
      | 0 => FreeGroup.of false
      | 1 => FreeGroup.of true
      | 2 => FreeGroup.of false
      | 3 => FreeGroup.of true
    FreeGroup.lift axisLabel
        (squareLoop.crossingWord halfAxisNormal pairwise_disjoint_halfAxis) =
      (FreeGroup.of false)⁻¹ *
        ((FreeGroup.of true)⁻¹ * (FreeGroup.of false * FreeGroup.of true)) ∧
    FreeGroup.lift axisLabel
        (squareLoop.crossingWord halfAxisNormal pairwise_disjoint_halfAxis) ≠ 1 := by
  intro axisLabel
  have heval :
      FreeGroup.lift axisLabel
        (squareLoop.crossingWord halfAxisNormal pairwise_disjoint_halfAxis) =
      (FreeGroup.of false)⁻¹ *
        ((FreeGroup.of true)⁻¹ * (FreeGroup.of false * FreeGroup.of true)) := by
    rw [crossingWord_squareLoop]
    simp [axisLabel]
  refine ⟨heval, fun hone => ?_⟩
  let σ : Bool → Equiv.Perm (Fin 3)
    | false => Equiv.swap 0 1
    | true => Equiv.swap 1 2
  have hperm := congrArg (fun w => FreeGroup.lift σ w 0) (heval.symm.trans hone)
  simp only [map_mul, map_inv, map_one, FreeGroup.lift_apply_of, Equiv.Perm.mul_apply,
    Equiv.Perm.one_apply, σ, Equiv.swap_inv] at hperm
  exact absurd hperm (by decide)

end TauCeti.FourHalfAxesExample
