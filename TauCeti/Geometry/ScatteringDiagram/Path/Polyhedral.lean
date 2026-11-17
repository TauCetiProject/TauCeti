/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity (Gemini 4 Carbon)
-/
module

public import TauCeti.Geometry.ScatteringDiagram.Path.Word
public import TauCeti.Geometry.Convex.PolyhedralComplex.Subdivision
public import TauCeti.Geometry.Convex.PolyhedralComplex.Map
import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# Crossing words across walls of a finite polyhedral complex

Distinct walls of a `FinitePolyhedralComplex` automatically have disjoint intrinsic interiors
(`FinitePolyhedralComplex.pairwise_disjoint_intrinsicInterior_walls`), so every admissible polygonal
path in the wall complement carries a crossing word `FinitePolyhedralComplex.crossingWord` in
`FreeGroup C.walls`.

For a wall coorientation (`FinitePolyhedralComplex.IsWallCoorientation`), rank-nullity identifies
each normal functional's kernel with the wall's affine direction and relates any two coorientations
on walls with nested directions by a nonzero scalar. This yields functoriality of `crossingWord`:
* under passing to a subcomplex
  (`FinitePolyhedralComplex.IsSubcomplex.crossingWord_restrictPrefunctor`), killing walls outside
  the subcomplex via `Function.extend`;
* under subdividing the polyhedral complex
  (`FinitePolyhedralComplex.IsSubdivision.crossingWord_mapPath`), via
  `FinitePolyhedralComplex.wallWordMap`, sending walls inside higher-dimensional coarse cells to `1`
  and subdivided pieces of a coarse wall `w` to `FreeGroup.of w` or `(FreeGroup.of w)⁻¹` according
  as coorientations agree or disagree;
* under `Toric.IntegralAffineEquiv` coordinate transport
  (`FinitePolyhedralComplex.crossingWord_image`), mapping generators along `C.wallsEquiv e`.

## References

* M. Kontsevich and Y. Soibelman, *Wall-crossing structures in Donaldson–Thomas invariants,
  integrable systems and Mirror Symmetry*, §2.1.
* T. Bridgeland, *Scattering diagrams, Hall algebras and stability conditions*, §§2.2–2.5.
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
abbrev wallComplement (C : FinitePolyhedralComplex h) : Type _ :=
  WallComplement (Subtype.val : C.walls → Set V)

/-- A family of wall coorientations on `C` assigns to each wall `w ∈ C.walls` a nonzero real linear
functional vanishing on the wall's affine direction. -/
def IsWallCoorientation (C : FinitePolyhedralComplex h)
    (ν : C.walls → V →ₗ[ℝ] ℝ) : Prop :=
  ∀ w : C.walls, ν w ≠ 0 ∧ (affineSpan ℝ (w : Set V)).direction ≤ LinearMap.ker (ν w)

/-- Defining equivalence for `IsWallCoorientation`. -/
theorem isWallCoorientation_iff {C : FinitePolyhedralComplex h} {ν : C.walls → V →ₗ[ℝ] ℝ} :
    C.IsWallCoorientation ν ↔
      ∀ w : C.walls, ν w ≠ 0 ∧ (affineSpan ℝ (w : Set V)).direction ≤ LinearMap.ker (ν w) :=
  Iff.rfl

/-- Every functional in a wall coorientation is nonzero. -/
theorem IsWallCoorientation.ne_zero {C : FinitePolyhedralComplex h} {ν : C.walls → V →ₗ[ℝ] ℝ}
    (hν : C.IsWallCoorientation ν) (w : C.walls) : ν w ≠ 0 :=
  (hν w).1

/-- Every functional in a wall coorientation vanishes on its wall's affine direction. -/
theorem IsWallCoorientation.direction_le_ker {C : FinitePolyhedralComplex h}
    {ν : C.walls → V →ₗ[ℝ] ℝ} (hν : C.IsWallCoorientation ν) (w : C.walls) :
    (affineSpan ℝ (w : Set V)).direction ≤ LinearMap.ker (ν w) :=
  (hν w).2

/-- Scaling a wall coorientation by nonzero scalars on each wall preserves `IsWallCoorientation`. -/
theorem IsWallCoorientation.smul {C : FinitePolyhedralComplex h} {ν : C.walls → V →ₗ[ℝ] ℝ}
    (hν : C.IsWallCoorientation ν) {r : C.walls → ℝ} (hr : ∀ w, r w ≠ 0) :
    C.IsWallCoorientation (fun w => r w • ν w) :=
  fun w => ⟨smul_ne_zero (hr w) (hν.ne_zero w),
    (hν.direction_le_ker w).trans (LinearMap.ker_smul (ν w) (r w) (hr w)).symm.le⟩

/-- Restricting a wall coorientation of `C` to the walls of a subcomplex `D` yields a wall
coorientation on `D`. -/
theorem IsWallCoorientation.ofSubcomplex {C D : FinitePolyhedralComplex h}
    {ν : C.walls → V →ₗ[ℝ] ℝ} (hν : C.IsWallCoorientation ν) (hDC : D.IsSubcomplex C) :
    D.IsWallCoorientation (ν ∘ Set.inclusion (hDC.cellsOfCodimension_subset 1)) :=
  fun w => hν (Set.inclusion (hDC.cellsOfCodimension_subset 1) w)

/-- By rank-nullity, the kernel of a wall coorientation functional equals the wall's affine
direction. -/
theorem IsWallCoorientation.ker_eq {C : FinitePolyhedralComplex h} {ν : C.walls → V →ₗ[ℝ] ℝ}
    (hν : C.IsWallCoorientation ν) (w : C.walls) :
    LinearMap.ker (ν w) = (affineSpan ℝ (w : Set V)).direction :=
  Module.Dual.ker_eq_of_le_of_finrank_add_one (ν w) (hν.ne_zero w) (hν.direction_le_ker w)
    (mem_cellsOfCodimension.mp w.2).2

/-- Two wall coorientations on walls whose affine directions satisfy
`(affineSpan ℝ w').direction ≤ (affineSpan ℝ w).direction` are nonzero scalar multiples of each
other. -/
theorem IsWallCoorientation.exists_ne_zero_eq_smul {C C' : FinitePolyhedralComplex h}
    {ν : C.walls → V →ₗ[ℝ] ℝ} {ν' : C'.walls → V →ₗ[ℝ] ℝ}
    (hν : C.IsWallCoorientation ν) (hν' : C'.IsWallCoorientation ν')
    {w : C.walls} {w' : C'.walls}
    (hdir : (affineSpan ℝ (w' : Set V)).direction ≤ (affineSpan ℝ (w : Set V)).direction) :
    ∃ c : ℝ, c ≠ 0 ∧ ν' w' = c • ν w := by
  have := h.finiteDimensional
  obtain ⟨-, hdim⟩ := mem_cellsOfCodimension.mp w.2
  obtain ⟨-, hdim'⟩ := mem_cellsOfCodimension.mp w'.2
  have hdir_eq : (affineSpan ℝ (w' : Set V)).direction = (affineSpan ℝ (w : Set V)).direction :=
    Submodule.eq_of_le_of_finrank_eq hdir (by omega)
  have hker : LinearMap.ker (ν' w') = LinearMap.ker (ν w) := by
    rw [hν'.ker_eq w', hν.ker_eq w, hdir_eq]
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp (hν.ne_zero w)
  replace hv : ν w v ≠ 0 := by simpa using hv
  have hv' : ν' w' v ≠ 0 := fun hz => hv (LinearMap.mem_ker.mp (hker ▸ LinearMap.mem_ker.mpr hz))
  refine ⟨ν' w' v / ν w v, div_ne_zero hv' hv, ?_⟩
  exact Module.Dual.eq_of_ker_eq_of_apply_eq v
    (hker.trans (LinearMap.ker_smul (ν w) _ (div_ne_zero hv' hv)).symm)
    (by simp [div_mul_cancel₀ _ hv]) hv'

/-- The crossing word in `FreeGroup C.walls` of an admissible polygonal path for `C`. -/
def crossingWord (C : FinitePolyhedralComplex h) (ν : C.walls → V →ₗ[ℝ] ℝ)
    {x y : C.wallComplement} (p : AdmissiblePLPath x y) : FreeGroup C.walls :=
  p.crossingWord ν C.pairwise_disjoint_intrinsicInterior_walls

/-- `FinitePolyhedralComplex.crossingWord` is `Quiver.Path.crossingWord` applied to
`C.pairwise_disjoint_intrinsicInterior_walls`. -/
theorem crossingWord_def (C : FinitePolyhedralComplex h) (ν : C.walls → V →ₗ[ℝ] ℝ)
    {x y : C.wallComplement} (p : AdmissiblePLPath x y) :
    C.crossingWord ν p = p.crossingWord ν C.pairwise_disjoint_intrinsicInterior_walls :=
  (rfl)

/-- A constant path has trivial crossing word. -/
@[simp]
theorem crossingWord_nil (C : FinitePolyhedralComplex h) (ν : C.walls → V →ₗ[ℝ] ℝ)
    (x : C.wallComplement) :
    C.crossingWord ν (Quiver.Path.nil : AdmissiblePLPath x x) = 1 :=
  Quiver.Path.crossingWord_nil ν _

/-- Extending an admissible path by a segment multiplies by the segment's crossing word on the
left. -/
@[simp]
theorem crossingWord_cons (C : FinitePolyhedralComplex h) (ν : C.walls → V →ₗ[ℝ] ℝ)
    {x y z : C.wallComplement} (p : AdmissiblePLPath x y) (e : y ⟶ z) :
    C.crossingWord ν (p.cons e) =
      WallComplement.segmentCrossingWord ν
        C.pairwise_disjoint_intrinsicInterior_walls e * C.crossingWord ν p :=
  Quiver.Path.crossingWord_cons ν _ p e

/-- The crossing word of a single-segment path is the segment's crossing word. -/
@[simp]
theorem crossingWord_toPath (C : FinitePolyhedralComplex h) (ν : C.walls → V →ₗ[ℝ] ℝ)
    {x y : C.wallComplement} (e : x ⟶ y) :
    C.crossingWord ν e.toPath =
      WallComplement.segmentCrossingWord ν
        C.pairwise_disjoint_intrinsicInterior_walls e :=
  Quiver.Path.crossingWord_toPath ν _ e

/-- Concatenating two admissible paths multiplies their crossing words in reverse order. -/
@[simp]
theorem crossingWord_comp (C : FinitePolyhedralComplex h) (ν : C.walls → V →ₗ[ℝ] ℝ)
    {x y z : C.wallComplement} (p : AdmissiblePLPath x y) (q : AdmissiblePLPath y z) :
    C.crossingWord ν (p.comp q) = C.crossingWord ν q * C.crossingWord ν p :=
  Quiver.Path.crossingWord_comp ν _ p q

/-- Positive rescaling of wall coorientations leaves `C.crossingWord` unchanged. -/
@[simp]
theorem crossingWord_smul (C : FinitePolyhedralComplex h) (ν : C.walls → V →ₗ[ℝ] ℝ)
    (r : C.walls → ℝ) (hr : ∀ w, 0 < r w) {x y : C.wallComplement} (p : AdmissiblePLPath x y) :
    C.crossingWord (fun w => r w • ν w) p = C.crossingWord ν p :=
  Quiver.Path.crossingWord_smul ν _ r hr p

/-- Reversing an admissible path inverts its crossing word for a wall coorientation. -/
@[simp]
theorem crossingWord_reverse {C : FinitePolyhedralComplex h} {ν : C.walls → V →ₗ[ℝ] ℝ}
    (hν : C.IsWallCoorientation ν) {x y : C.wallComplement} (p : AdmissiblePLPath x y) :
    C.crossingWord ν p.reverse = (C.crossingWord ν p)⁻¹ :=
  Quiver.Path.crossingWord_reverse ν _ hν.ker_eq p

/-- Subdividing an admissible polygonal path by allowed interior vertices leaves `C.crossingWord`
unchanged. -/
theorem crossingWord_eq_of_path_isSubdivision (C : FinitePolyhedralComplex h)
    (ν : C.walls → V →ₗ[ℝ] ℝ) {x y : C.wallComplement} {p q : AdmissiblePLPath x y}
    (hpq : p.IsSubdivision q) :
    C.crossingWord ν p = C.crossingWord ν q :=
  hpq.crossingWord_eq ν _

/-- Lifting `C.crossingWord ν p` along `label` recovers `p.wallPathProduct`. -/
theorem lift_crossingWord_eq_wallPathProduct {G : Type*} [Group G]
    (C : FinitePolyhedralComplex h) (ν : C.walls → V →ₗ[ℝ] ℝ) (label : C.walls → G)
    (hcomm : ∀ w₁ w₂ : C.walls,
      affineSpan ℝ (w₁ : Set V) = affineSpan ℝ (w₂ : Set V) → Commute (label w₁) (label w₂))
    {x y : C.wallComplement} (p : AdmissiblePLPath x y) :
    FreeGroup.lift label (C.crossingWord ν p) = p.wallPathProduct ν label hcomm :=
  Quiver.Path.lift_crossingWord_eq_wallPathProduct ν _ label hcomm p

/-! ### Subcomplex wall deletion -/

/-- Passing from `C` to a subcomplex `D` along `WallComplement.restrictPrefunctor` maps
`crossingWord` by `FreeGroup.lift (Function.extend ... FreeGroup.of 1)`, killing all walls of `C`
outside `D`. -/
@[simp]
theorem IsSubcomplex.crossingWord_restrictPrefunctor {C D : FinitePolyhedralComplex h}
    (hDC : D.IsSubcomplex C) (ν : C.walls → V →ₗ[ℝ] ℝ)
    {x y : C.wallComplement} (p : AdmissiblePLPath x y) :
    D.crossingWord (ν ∘ Set.inclusion (hDC.cellsOfCodimension_subset 1))
        ((WallComplement.restrictPrefunctor (Subtype.val : C.walls → Set V)
          (Set.inclusion (hDC.cellsOfCodimension_subset 1))).mapPath p) =
      FreeGroup.lift (Function.extend (Set.inclusion (hDC.cellsOfCodimension_subset 1))
        FreeGroup.of 1) (C.crossingWord ν p) :=
  Quiver.Path.crossingWord_restrictPrefunctor ν C.pairwise_disjoint_intrinsicInterior_walls
    (Set.inclusion_injective (hDC.cellsOfCodimension_subset 1)) p

/-! ### Functoriality under polyhedral complex subdivision -/

/-- Generator map `C'.walls → FreeGroup C.walls` comparing the walls of `C'` against those of `C`:
for `w' ⊆ w`, sends `w' ∈ C'.walls` to `FreeGroup.of w` when `ν' w'` is a positive scalar multiple
of `ν w` and to `(FreeGroup.of w)⁻¹` otherwise (i.e. when coorientations disagree under
`IsWallCoorientation`), and sends `w'` to `1` when no wall of `C` contains `w'`. -/
def wallWordMap (C' C : FinitePolyhedralComplex h)
    (ν' : C'.walls → V →ₗ[ℝ] ℝ) (ν : C.walls → V →ₗ[ℝ] ℝ) (w' : C'.walls) :
    FreeGroup C.walls :=
  open scoped Classical in
  if hex : ∃ w : C.walls, (w' : Set V) ⊆ (w : Set V) then
    if ∃ c : ℝ, 0 < c ∧ ν' w' = c • ν hex.choose then
      FreeGroup.of hex.choose
    else
      (FreeGroup.of hex.choose)⁻¹
  else 1

/-- Defining equation for `FinitePolyhedralComplex.wallWordMap`. -/
theorem wallWordMap_def (C' C : FinitePolyhedralComplex h)
    (ν' : C'.walls → V →ₗ[ℝ] ℝ) (ν : C.walls → V →ₗ[ℝ] ℝ) (w' : C'.walls) :
    C'.wallWordMap C ν' ν w' =
      (open scoped Classical in
      if hex : ∃ w : C.walls, (w' : Set V) ⊆ (w : Set V) then
        if ∃ c : ℝ, 0 < c ∧ ν' w' = c • ν hex.choose then
          FreeGroup.of hex.choose
        else
          (FreeGroup.of hex.choose)⁻¹
      else 1) :=
  (rfl)

/-- When `w' ⊆ w` and `ν' w' = c • ν w` with `0 < c`, `wallWordMap` sends `w'` to `FreeGroup.of w`.
-/
theorem wallWordMap_of_subset_pos {C' C : FinitePolyhedralComplex h}
    {ν' : C'.walls → V →ₗ[ℝ] ℝ} {ν : C.walls → V →ₗ[ℝ] ℝ}
    {w' : C'.walls} {w : C.walls} (hw : (w' : Set V) ⊆ (w : Set V))
    {c : ℝ} (hc : 0 < c) (hνc : ν' w' = c • ν w) :
    C'.wallWordMap C ν' ν w' = FreeGroup.of w := by
  unfold wallWordMap
  split_ifs with hex hpos
  · exact congrArg FreeGroup.of (C.eq_of_wall_subset hex.choose_spec hw)
  · exfalso
    exact hpos ⟨c, hc, C.eq_of_wall_subset hex.choose_spec hw ▸ hνc⟩
  · exact (hex ⟨w, hw⟩).elim

/-- When `w' ⊆ w`, `ν w ≠ 0`, and `ν' w' = c • ν w` with `c < 0`, `wallWordMap` sends `w'` to
`(FreeGroup.of w)⁻¹`. -/
theorem wallWordMap_of_subset_neg {C' C : FinitePolyhedralComplex h}
    {ν' : C'.walls → V →ₗ[ℝ] ℝ} {ν : C.walls → V →ₗ[ℝ] ℝ}
    {w' : C'.walls} {w : C.walls} (hνw : ν w ≠ 0) (hw : (w' : Set V) ⊆ (w : Set V))
    {c : ℝ} (hc : c < 0) (hνc : ν' w' = c • ν w) :
    C'.wallWordMap C ν' ν w' = (FreeGroup.of w)⁻¹ := by
  unfold wallWordMap
  split_ifs with hex hpos
  · exfalso
    obtain ⟨c', hc', hνc'⟩ := C.eq_of_wall_subset hex.choose_spec hw ▸ hpos
    obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp hνw
    replace hv : ν w v ≠ 0 := by simpa using hv
    have hmul : c * ν w v = c' * ν w v := by
      simpa [LinearMap.smul_apply, smul_eq_mul] using
        LinearMap.congr_fun (hνc.symm.trans hνc') v
    linarith [mul_right_cancel₀ hv hmul]
  · exact congrArg (fun u => (FreeGroup.of u)⁻¹) (C.eq_of_wall_subset hex.choose_spec hw)
  · exact (hex ⟨w, hw⟩).elim

/-- When no wall of `C` contains `w'`, `wallWordMap` sends `w'` to `1`. -/
@[simp]
theorem wallWordMap_of_forall_not_subset {C' C : FinitePolyhedralComplex h}
    (ν' : C'.walls → V →ₗ[ℝ] ℝ) (ν : C.walls → V →ₗ[ℝ] ℝ)
    {w' : C'.walls} (hw : ∀ w : C.walls, ¬ (w' : Set V) ⊆ (w : Set V)) :
    C'.wallWordMap C ν' ν w' = 1 := by
  simp [wallWordMap, hw]

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
    (x : C'.wallComplement) : C.wallComplement where
  val := x.val
  notMem w hw := by
    obtain ⟨w', hw', -, -, hxw'⟩ := hsub.exists_mem_cellsOfCodimension_subset w.2 hw
    exact x.notMem ⟨w', hw'⟩ hxw'

/-- Viewing an allowed vertex of `C'` as an allowed vertex of `C` preserves its ambient point. -/
@[simp]
theorem wallComplement_val {C C' : FinitePolyhedralComplex h} (hsub : C'.IsSubdivision C)
    (x : C'.wallComplement) : (hsub.wallComplement x).val = x.val :=
  (rfl)

/-- An admissible segment for a subdivision `C'` of `C` is automatically admissible for `C`. -/
theorem admissibleSegment {C C' : FinitePolyhedralComplex h} (hsub : C'.IsSubdivision C)
    {x y : C'.wallComplement} (a : WallComplement.AdmissibleSegment x y) :
    WallComplement.AdmissibleSegment (hsub.wallComplement x)
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
    C'.wallComplement ⥤q C.wallComplement where
  obj x := hsub.wallComplement x
  map a := ⟨hsub.admissibleSegment a.down⟩

/-- `IsSubdivision.wallPrefunctor` commutes with segment reversal. -/
instance {C C' : FinitePolyhedralComplex h} (hsub : C'.IsSubdivision C) :
    hsub.wallPrefunctor.MapReverse where
  map_reverse' _ := PLift.ext (Subsingleton.elim _ _)

/-- View an admissible polygonal path for `C'` as an admissible polygonal path for `C`. -/
def mapPath {C C' : FinitePolyhedralComplex h} (hsub : C'.IsSubdivision C)
    {x y : C'.wallComplement} (p : AdmissiblePLPath x y) :
    AdmissiblePLPath (hsub.wallComplement x) (hsub.wallComplement y) :=
  hsub.wallPrefunctor.mapPath p

/-- `IsSubdivision.mapPath` is `Prefunctor.mapPath` along `hsub.wallPrefunctor`. -/
theorem mapPath_def {C C' : FinitePolyhedralComplex h} (hsub : C'.IsSubdivision C)
    {x y : C'.wallComplement} (p : AdmissiblePLPath x y) :
    hsub.mapPath p = hsub.wallPrefunctor.mapPath p :=
  (rfl)

@[simp]
theorem mapPath_nil {C C' : FinitePolyhedralComplex h} (hsub : C'.IsSubdivision C)
    (x : C'.wallComplement) :
    hsub.mapPath (Quiver.Path.nil : AdmissiblePLPath x x) = Quiver.Path.nil :=
  (rfl)

@[simp]
theorem mapPath_cons {C C' : FinitePolyhedralComplex h} (hsub : C'.IsSubdivision C)
    {x y z : C'.wallComplement} (p : AdmissiblePLPath x y) (a : y ⟶ z) :
    hsub.mapPath (p.cons a) = (hsub.mapPath p).cons (hsub.wallPrefunctor.map a) :=
  (rfl)

@[simp]
theorem mapPath_toPath {C C' : FinitePolyhedralComplex h} (hsub : C'.IsSubdivision C)
    {x y : C'.wallComplement} (a : x ⟶ y) :
    hsub.mapPath a.toPath = (hsub.wallPrefunctor.map a).toPath :=
  (rfl)

@[simp]
theorem mapPath_comp {C C' : FinitePolyhedralComplex h} (hsub : C'.IsSubdivision C)
    {x y z : C'.wallComplement} (p : AdmissiblePLPath x y) (q : AdmissiblePLPath y z) :
    hsub.mapPath (p.comp q) = (hsub.mapPath p).comp (hsub.mapPath q) :=
  Prefunctor.mapPath_comp _ _ _

@[simp]
theorem length_mapPath {C C' : FinitePolyhedralComplex h} (hsub : C'.IsSubdivision C)
    {x y : C'.wallComplement} (p : AdmissiblePLPath x y) :
    (hsub.mapPath p).length = p.length :=
  Prefunctor.length_mapPath _ _

@[simp]
theorem vertices_mapPath {C C' : FinitePolyhedralComplex h} (hsub : C'.IsSubdivision C)
    {x y : C'.wallComplement} (p : AdmissiblePLPath x y) :
    (hsub.mapPath p).vertices = p.vertices.map hsub.wallComplement :=
  Prefunctor.vertices_mapPath _ _

/-- Viewing a path of `C'` in `C` preserves its ambient vertex list. -/
theorem map_val_vertices_mapPath {C C' : FinitePolyhedralComplex h} (hsub : C'.IsSubdivision C)
    {x y : C'.wallComplement} (p : AdmissiblePLPath x y) :
    (hsub.mapPath p).vertices.map WallComplement.val =
      p.vertices.map WallComplement.val := by
  simp only [vertices_mapPath, List.map_map, Function.comp_def]

@[simp]
theorem mapPath_reverse {C C' : FinitePolyhedralComplex h} (hsub : C'.IsSubdivision C)
    {x y : C'.wallComplement} (p : AdmissiblePLPath x y) :
    hsub.mapPath p.reverse = (hsub.mapPath p).reverse :=
  Prefunctor.mapPath_reverse hsub.wallPrefunctor p

@[simp]
theorem toContinuousPath_mapPath {C C' : FinitePolyhedralComplex h} (hsub : C'.IsSubdivision C)
    {x y : C'.wallComplement} (p : AdmissiblePLPath x y) :
    (hsub.mapPath p).toContinuousPath = p.toContinuousPath := by
  induction p with
  | nil => simp
  | cons p a ih => simp only [mapPath_cons, Quiver.Path.toContinuousPath_cons, ih]

private theorem neg_ite_sign_of_neg {c v : ℝ} (hc : c < 0) (hv : v ≠ 0) :
    -(if 0 < c * v then -1 else 1 : ℤ) = if 0 < v then -1 else 1 := by
  split_ifs with h1 h2 h2
  · linarith [mul_neg_of_neg_of_pos hc h2]
  · rfl
  · rfl
  · exact (h1 (mul_pos_of_neg_of_neg hc (lt_of_le_of_ne (not_lt.mp h2) hv))).elim

/-- Lifting `crossingEventWord` on a subdivision `C'` by `FinitePolyhedralComplex.wallWordMap`
recovers the coarse `crossingEventWord` on `C` at every parameter `t`. -/
theorem lift_crossingEventWord {C C' : FinitePolyhedralComplex h} (hsub : C'.IsSubdivision C)
    {ν' : C'.walls → V →ₗ[ℝ] ℝ} {ν : C.walls → V →ₗ[ℝ] ℝ}
    (hν' : C'.IsWallCoorientation ν') (hν : C.IsWallCoorientation ν)
    {x y : C'.wallComplement} (e : x ⟶ y)
    (e₀ : hsub.wallComplement x ⟶ hsub.wallComplement y) (t : ℝ) :
    FreeGroup.lift (C'.wallWordMap C ν' ν)
        (WallComplement.crossingEventWord ν'
          C'.pairwise_disjoint_intrinsicInterior_walls e t) =
      WallComplement.crossingEventWord ν
        C.pairwise_disjoint_intrinsicInterior_walls e₀ t := by
  by_cases hcr' : ∃ w' : C'.walls, (w', t) ∈ WallComplement.crossings x y
  · obtain ⟨w', hw't⟩ := hcr'
    obtain ⟨htI, hzw'⟩ := (WallComplement.mem_crossings x y w' t).mp hw't
    rw [WallComplement.crossingEventWord_of_mem_crossings ν' _ e hw't,
      map_zpow, FreeGroup.lift_apply_of]
    by_cases hex : ∃ w : C.walls, (w' : Set V) ⊆ (w : Set V)
    · obtain ⟨w, hww⟩ := hex
      have hwt : (w, t) ∈ WallComplement.crossings
          (hsub.wallComplement x) (hsub.wallComplement y) :=
        (WallComplement.mem_crossings _ _ w t).mpr ⟨htI, hww hzw'⟩
      rw [WallComplement.crossingEventWord_of_mem_crossings ν _ e₀ hwt]
      obtain ⟨c, hc0, hνc⟩ :=
        hν.exists_ne_zero_eq_smul hν' (AffineSubspace.direction_le (affineSpan_mono ℝ hww))
      have hv_ne : ν w (y.val - x.val) ≠ 0 := fun hz =>
        e₀.down.transverse w ⟨t, htI, hww hzw'⟩ ((hν.ker_eq w) ▸ LinearMap.mem_ker.mpr hz)
      rcases lt_or_gt_of_ne hc0 with hneg | hpos
      · rw [wallWordMap_of_subset_neg (hν.ne_zero w) hww hneg hνc, hνc, LinearMap.smul_apply,
          smul_eq_mul, inv_zpow, ← zpow_neg]
        exact congrArg (FreeGroup.of w ^ ·) (neg_ite_sign_of_neg hneg hv_ne)
      · rw [wallWordMap_of_subset_pos hww hpos hνc, hνc, LinearMap.smul_apply, smul_eq_mul]
        simp only [mul_pos_iff_of_pos_left hpos]
    · have hex' : ∀ w : C.walls, ¬ (w' : Set V) ⊆ (w : Set V) := fun w hw => hex ⟨w, hw⟩
      rw [wallWordMap_of_forall_not_subset ν' ν hex', one_zpow]
      refine (WallComplement.crossingEventWord_eq_one_of_forall_notMem ν _ e₀ t
        fun w hwt => ?_).symm
      obtain ⟨_, hzw⟩ := (WallComplement.mem_crossings _ _ w t).mp hwt
      obtain ⟨w'', hw'', hsub'', -, hzw''⟩ := hsub.exists_mem_cellsOfCodimension_subset w.2 hzw
      have hw''t : (⟨w'', hw''⟩, t) ∈ WallComplement.crossings x y :=
        (WallComplement.mem_crossings x y ⟨w'', hw''⟩ t).mpr ⟨htI, hzw''⟩
      exact hex' w (e.down.eq_of_mem_crossings C'.pairwise_disjoint_intrinsicInterior_walls
        hw't hw''t ▸ hsub'')
  · rw [WallComplement.crossingEventWord_eq_one_of_forall_notMem ν' _ e t
        fun w' hw' => hcr' ⟨w', hw'⟩, map_one]
    refine (WallComplement.crossingEventWord_eq_one_of_forall_notMem ν _ e₀ t
      fun w hwt => ?_).symm
    obtain ⟨htI, hzw⟩ := (WallComplement.mem_crossings _ _ w t).mp hwt
    obtain ⟨w', hw', -, -, hzw'⟩ := hsub.exists_mem_cellsOfCodimension_subset w.2 hzw
    exact hcr' ⟨⟨w', hw'⟩,
      (WallComplement.mem_crossings x y ⟨w', hw'⟩ t).mpr ⟨htI, hzw'⟩⟩

/-- Subdividing a finite polyhedral complex `C` into `C'` maps the crossing word of any admissible
path for `C'` to its crossing word on `C` via `FreeGroup.lift (C'.wallWordMap C ν' ν)`. -/
theorem crossingWord_mapPath {C C' : FinitePolyhedralComplex h}
    (hsub : C'.IsSubdivision C) {ν' : C'.walls → V →ₗ[ℝ] ℝ} {ν : C.walls → V →ₗ[ℝ] ℝ}
    (hν' : C'.IsWallCoorientation ν') (hν : C.IsWallCoorientation ν)
    {x y : C'.wallComplement} (p : AdmissiblePLPath x y) :
    C.crossingWord ν (hsub.mapPath p) =
      FreeGroup.lift (C'.wallWordMap C ν' ν) (C'.crossingWord ν' p) := by
  induction p with
  | nil => simp
  | @cons u v p a ih =>
    rw [mapPath_cons, crossingWord_cons, crossingWord_cons, map_mul, ih]
    refine congrArg (· * _) ?_
    let a₀ : hsub.wallComplement u ⟶ hsub.wallComplement v := hsub.wallPrefunctor.map a
    have hcover : ∀ t ∈ WallComplement.orderedCrossingTimes a₀,
        t ∈ WallComplement.orderedCrossingTimes a := by
      intro t ht
      obtain ⟨w, hwt⟩ := (WallComplement.mem_orderedCrossingTimes a₀ t).mp ht
      obtain ⟨htI, hzw⟩ := (WallComplement.mem_crossings _ _ w t).mp hwt
      obtain ⟨w', hw', -, -, hzw'⟩ := hsub.exists_mem_cellsOfCodimension_subset w.2 hzw
      exact (WallComplement.mem_orderedCrossingTimes a t).mpr
        ⟨⟨w', hw'⟩, (WallComplement.mem_crossings u v ⟨w', hw'⟩ t).mpr ⟨htI, hzw'⟩⟩
    rw [WallComplement.segmentCrossingWord_eq_prod_of_crossingTimes ν _ a₀
      (WallComplement.orderedCrossingTimes a)
      (WallComplement.pairwise_orderedCrossingTimes a) hcover,
      WallComplement.segmentCrossingWord_def, map_list_prod, List.map_map]
    exact congrArg List.prod
      (List.map_congr_left fun t _ => (hsub.lift_crossingEventWord hν' hν a a₀ t).symm)

end IsSubdivision

/-! ### Integral affine transport -/

section IntegralAffineTransport

variable {N' U : Type*} [AddCommGroup N'] [NormedAddCommGroup U] [NormedSpace ℝ U]
  {i' : N' →+ U} {h' : TauCeti.Toric.IsIntegralLattice i'}

/-- `wallsEquiv` acts on underlying sets as the image under `e.toContinuousAffineEquiv`. -/
theorem coe_wallsEquiv_apply_eq_image_toContinuousAffineEquiv
    (C : FinitePolyhedralComplex h) (e : Toric.IntegralAffineEquiv h h') (w : C.walls) :
    (C.wallsEquiv e w : Set U) = e.toContinuousAffineEquiv '' (w : Set V) := by
  rw [e.coe_toContinuousAffineEquiv]
  exact C.coe_wallsEquiv_apply e w

/-- Transport an allowed vertex of `C` to `C.image e` along an integral affine equivalence `e`. -/
abbrev imageEndpoint (C : FinitePolyhedralComplex h) (e : Toric.IntegralAffineEquiv h h')
    (x : C.wallComplement) : (C.image e).wallComplement :=
  x.mapReindex e.toContinuousAffineEquiv (C.wallsEquiv e)
    (C.coe_wallsEquiv_apply_eq_image_toContinuousAffineEquiv e)

/-- `imageEndpoint` acts on ambient points as `e`. -/
theorem imageEndpoint_val (C : FinitePolyhedralComplex h) (e : Toric.IntegralAffineEquiv h h')
    (x : C.wallComplement) : (C.imageEndpoint e x).val = e x.val := by
  simp

/-- The quiver prefunctor transporting admissible segments of `C` to `C.image e` along `e`. -/
abbrev imagePrefunctor (C : FinitePolyhedralComplex h) (e : Toric.IntegralAffineEquiv h h') :
    C.wallComplement ⥤q (C.image e).wallComplement :=
  WallComplement.mapReindexPrefunctor e.toContinuousAffineEquiv (C.wallsEquiv e)
    (C.coe_wallsEquiv_apply_eq_image_toContinuousAffineEquiv e)

/-- Transport an admissible polygonal path of `C` to `C.image e` along an integral affine
equivalence `e`. -/
def imagePath (C : FinitePolyhedralComplex h) (e : Toric.IntegralAffineEquiv h h')
    {x y : C.wallComplement} (p : AdmissiblePLPath x y) :
    AdmissiblePLPath (C.imageEndpoint e x) (C.imageEndpoint e y) :=
  p.affineMapReindex e.toContinuousAffineEquiv (C.wallsEquiv e)
    (C.coe_wallsEquiv_apply_eq_image_toContinuousAffineEquiv e)

/-- `imagePath` unfolds to `Quiver.Path.affineMapReindex` along `e.toContinuousAffineEquiv` and
`C.wallsEquiv e`. -/
theorem imagePath_eq_affineMapReindex (C : FinitePolyhedralComplex h)
    (e : Toric.IntegralAffineEquiv h h') {x y : C.wallComplement} (p : AdmissiblePLPath x y) :
    C.imagePath e p = p.affineMapReindex e.toContinuousAffineEquiv (C.wallsEquiv e)
      (C.coe_wallsEquiv_apply_eq_image_toContinuousAffineEquiv e) :=
  (rfl)

/-- `imagePath` is `Prefunctor.mapPath` along `C.imagePrefunctor e`. -/
theorem imagePath_def (C : FinitePolyhedralComplex h) (e : Toric.IntegralAffineEquiv h h')
    {x y : C.wallComplement} (p : AdmissiblePLPath x y) :
    C.imagePath e p = (C.imagePrefunctor e).mapPath p :=
  Quiver.Path.affineMapReindex_def p _ _ _

@[simp]
theorem imagePath_nil (C : FinitePolyhedralComplex h) (e : Toric.IntegralAffineEquiv h h')
    (x : C.wallComplement) :
    C.imagePath e (Quiver.Path.nil : AdmissiblePLPath x x) = Quiver.Path.nil :=
  Quiver.Path.affineMapReindex_nil _ _ _

@[simp]
theorem imagePath_cons (C : FinitePolyhedralComplex h) (e : Toric.IntegralAffineEquiv h h')
    {x y z : C.wallComplement} (p : AdmissiblePLPath x y) (a : y ⟶ z) :
    C.imagePath e (p.cons a) = (C.imagePath e p).cons ((C.imagePrefunctor e).map a) :=
  Quiver.Path.affineMapReindex_cons p a _ _ _

@[simp]
theorem imagePath_toPath (C : FinitePolyhedralComplex h) (e : Toric.IntegralAffineEquiv h h')
    {x y : C.wallComplement} (a : x ⟶ y) :
    C.imagePath e a.toPath = ((C.imagePrefunctor e).map a).toPath :=
  Quiver.Path.affineMapReindex_toPath a _ _ _

@[simp]
theorem imagePath_comp (C : FinitePolyhedralComplex h) (e : Toric.IntegralAffineEquiv h h')
    {x y z : C.wallComplement} (p : AdmissiblePLPath x y) (q : AdmissiblePLPath y z) :
    C.imagePath e (p.comp q) = (C.imagePath e p).comp (C.imagePath e q) :=
  Quiver.Path.affineMapReindex_comp p q _ _ _

@[simp]
theorem length_imagePath (C : FinitePolyhedralComplex h) (e : Toric.IntegralAffineEquiv h h')
    {x y : C.wallComplement} (p : AdmissiblePLPath x y) :
    (C.imagePath e p).length = p.length :=
  Quiver.Path.length_affineMapReindex p _ _ _

@[simp]
theorem vertices_imagePath (C : FinitePolyhedralComplex h) (e : Toric.IntegralAffineEquiv h h')
    {x y : C.wallComplement} (p : AdmissiblePLPath x y) :
    (C.imagePath e p).vertices = p.vertices.map (C.imageEndpoint e) :=
  Quiver.Path.vertices_affineMapReindex p _ _ _

/-- Transporting a path along `e` maps its ambient vertex list by `e`. -/
theorem map_val_vertices_imagePath (C : FinitePolyhedralComplex h)
    (e : Toric.IntegralAffineEquiv h h') {x y : C.wallComplement} (p : AdmissiblePLPath x y) :
    (C.imagePath e p).vertices.map WallComplement.val =
      (p.vertices.map WallComplement.val).map e := by
  rw [imagePath_eq_affineMapReindex, Quiver.Path.map_val_vertices_affineMapReindex,
    e.coe_toContinuousAffineEquiv]

@[simp]
theorem imagePath_reverse (C : FinitePolyhedralComplex h) (e : Toric.IntegralAffineEquiv h h')
    {x y : C.wallComplement} (p : AdmissiblePLPath x y) :
    C.imagePath e p.reverse = (C.imagePath e p).reverse :=
  Quiver.Path.affineMapReindex_reverse p _ _ _

@[simp]
theorem toContinuousPath_imagePath (C : FinitePolyhedralComplex h)
    (e : Toric.IntegralAffineEquiv h h') {x y : C.wallComplement} (p : AdmissiblePLPath x y) :
    (C.imagePath e p).toContinuousPath =
      p.toContinuousPath.map e.toContinuousAffineEquiv.continuous :=
  Quiver.Path.toContinuousPath_affineMapReindex p _ _ _

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
  · have hcoe : (e : V → U) = e.toAffineEquiv.toAffineMap := by
      rw [← e.coe_toContinuousAffineEquiv, ← ContinuousAffineEquiv.coe_coe,
        e.toContinuousAffineEquiv_toAffineEquiv, AffineEquiv.coe_toAffineMap]
    have hw' : (w' : Set U) = e.toAffineEquiv.toAffineMap '' (w : Set V) := by
      have h1 := C.coe_wallsEquiv_apply e w
      rwa [(C.wallsEquiv e).apply_symm_apply w', hcoe] at h1
    rw [hw', ← AffineSubspace.map_span, AffineSubspace.map_direction]
    rintro _ ⟨v, hv, rfl⟩
    simpa using hle hv

/-- Transporting an admissible polygonal path along an `IntegralAffineEquiv` `e` maps its
`crossingWord` by `FreeGroup.map (C.wallsEquiv e)` under the pushed-forward coorientations
`ν ∘ e.linear⁻¹`. -/
@[simp]
theorem crossingWord_image (C : FinitePolyhedralComplex h) (ν : C.walls → V →ₗ[ℝ] ℝ)
    (e : Toric.IntegralAffineEquiv h h') {x y : C.wallComplement} (p : AdmissiblePLPath x y) :
    (C.image e).crossingWord
        (fun w' => (ν ((C.wallsEquiv e).symm w')).comp e.toAffineEquiv.linear.symm.toLinearMap)
        (C.imagePath e p) =
      FreeGroup.map (C.wallsEquiv e) (C.crossingWord ν p) := by
  have hlin : e.toAffineEquiv.linear = e.toContinuousAffineEquiv.toAffineEquiv.linear :=
    congrArg AffineEquiv.linear e.toContinuousAffineEquiv_toAffineEquiv.symm
  simp_rw [hlin]
  exact Quiver.Path.crossingWord_affineMapReindex ν C.pairwise_disjoint_intrinsicInterior_walls
    e.toContinuousAffineEquiv (C.wallsEquiv e)
    (C.coe_wallsEquiv_apply_eq_image_toContinuousAffineEquiv e) p

end IntegralAffineTransport

end TauCeti.FinitePolyhedralComplex
