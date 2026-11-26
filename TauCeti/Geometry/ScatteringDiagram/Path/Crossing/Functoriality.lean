/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity (Gemini 4 Carbon)
-/
module

public import TauCeti.Geometry.ScatteringDiagram.Path.Crossing.Word
public import TauCeti.Geometry.Convex.PolyhedralComplex.Subdivision
public import TauCeti.Geometry.Convex.PolyhedralComplex.Map
import TauCeti.LinearAlgebra.AffineSpace.AffineEquiv
import TauCeti.LinearAlgebra.Dual.Lemmas

/-!
# Functoriality of crossing words under complex subdivision and integral affine transport

Building on `Quiver.Path.crossingWord` from `TauCeti.Geometry.ScatteringDiagram.Path.Crossing.Word`,
this file formalizes wall coorientations on a `FinitePolyhedralComplex` and proves the remaining
functoriality laws of crossing words across polyhedral complexes:

* `FinitePolyhedralComplex.IsWallCoorientation`: assigns to each wall `w ∈ C.walls` a nonzero real
  linear functional vanishing on `(affineSpan ℝ w).direction`. By rank-nullity its kernel equals the
  wall's affine direction (`IsWallCoorientation.ker_eq`), and any two coorientations on walls with
  nested directions differ by a nonzero scalar (`IsWallCoorientation.exists_ne_zero_eq_smul`).
* **Complex subdivision** (`FinitePolyhedralComplex.IsSubdivision.crossingWord_mapPath`): for a
  subdivision `C'` of `C` with wall coorientations `ν'` and `ν`, viewing an admissible path `p` of
  `C'` as an admissible path `hsub.mapPath p` of `C` maps `p.crossingWord ν'` by
  `FreeGroup.lift (C'.wallWordMap C ν' ν)`, sending walls of `C'` inside higher-dimensional cells of
  `C` to `1` and sending each wall `w' ⊆ w` to `FreeGroup.of w` or `(FreeGroup.of w)⁻¹` according as
  `ν' w'` and `ν w` agree or disagree in sign.
* **Integral affine transport** (`FinitePolyhedralComplex.crossingWord_image`): transporting an
  admissible path `p` along `e : Toric.IntegralAffineEquiv h h'` to `C.image e` maps
  `p.crossingWord ν` by `FreeGroup.map (C.wallsEquiv e)` under the pushed-forward coorientations
  `w' ↦ ν ((C.wallsEquiv e).symm w') ∘ e.linear⁻¹`.

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

/-! ### Wall coorientations -/

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

/-- Restricting a wall coorientation of `C` to a complex `D` with `D.walls ⊆ C.walls` yields a wall
coorientation on `D`. -/
theorem IsWallCoorientation.ofWallsSubset {C D : FinitePolyhedralComplex h}
    {ν : C.walls → V →ₗ[ℝ] ℝ} (hν : C.IsWallCoorientation ν) (hW : D.walls ⊆ C.walls) :
    D.IsWallCoorientation (fun w => ν ⟨w.val, hW w.property⟩) :=
  fun w => hν ⟨w.val, hW w.property⟩

/-- Restricting a wall coorientation of `C` to a subcomplex `D` yields a wall coorientation on `D`.
-/
theorem IsWallCoorientation.ofSubcomplex {C D : FinitePolyhedralComplex h}
    {ν : C.walls → V →ₗ[ℝ] ℝ} (hν : C.IsWallCoorientation ν) (hDC : D.IsSubcomplex C) :
    D.IsWallCoorientation (fun w => ν ⟨w.val, hDC.cellsOfCodimension_subset 1 w.property⟩) :=
  hν.ofWallsSubset (hDC.cellsOfCodimension_subset 1)

/-- By rank-nullity, the kernel of a wall coorientation functional equals the wall's affine
direction. -/
theorem IsWallCoorientation.ker_eq {C : FinitePolyhedralComplex h} {ν : C.walls → V →ₗ[ℝ] ℝ}
    (hν : C.IsWallCoorientation ν) (w : C.walls) :
    LinearMap.ker (ν w) = (affineSpan ℝ (w : Set V)).direction :=
  Module.Dual.ker_eq_of_le_of_finrank_add_one (ν w) (hν.ne_zero w) (hν.direction_le_ker w)
    (mem_cellsOfCodimension.mp w.property).2

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
  obtain ⟨-, hdim⟩ := mem_cellsOfCodimension.mp w.property
  obtain ⟨-, hdim'⟩ := mem_cellsOfCodimension.mp w'.property
  have hdir_eq : (affineSpan ℝ (w' : Set V)).direction = (affineSpan ℝ (w : Set V)).direction :=
    Submodule.eq_of_le_of_finrank_eq hdir (by omega)
  have hker : LinearMap.ker (ν' w') = LinearMap.ker (ν w) := by
    rw [hν'.ker_eq w', hν.ker_eq w, hdir_eq]
  obtain ⟨v, hv⟩ := (LinearMap.surjective_iff_ne_zero.mpr (hν.ne_zero w)) 1
  have hv' : ν' w' v ≠ 0 := fun hz =>
    one_ne_zero (hv ▸ LinearMap.mem_ker.mp (hker ▸ LinearMap.mem_ker.mpr hz))
  exact ⟨ν' w' v, hv', Module.Dual.eq_of_ker_eq_of_apply_eq v
    (hker.trans (LinearMap.ker_smul (ν w) _ hv').symm) (by simp [hv]) hv'⟩

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
  rw [wallWordMap_def]
  split_ifs with hex hpos
  · exact congrArg FreeGroup.of (C.eq_of_cellsOfCodimension_subset hex.choose_spec hw)
  · exfalso
    exact hpos ⟨c, hc, C.eq_of_cellsOfCodimension_subset hex.choose_spec hw ▸ hνc⟩
  · exact (hex ⟨w, hw⟩).elim

/-- When `w' ⊆ w`, `ν w ≠ 0`, and `ν' w' = c • ν w` with `c < 0`, `wallWordMap` sends `w'` to
`(FreeGroup.of w)⁻¹`. -/
theorem wallWordMap_of_subset_neg {C' C : FinitePolyhedralComplex h}
    {ν' : C'.walls → V →ₗ[ℝ] ℝ} {ν : C.walls → V →ₗ[ℝ] ℝ}
    {w' : C'.walls} {w : C.walls} (hνw : ν w ≠ 0) (hw : (w' : Set V) ⊆ (w : Set V))
    {c : ℝ} (hc : c < 0) (hνc : ν' w' = c • ν w) :
    C'.wallWordMap C ν' ν w' = (FreeGroup.of w)⁻¹ := by
  rw [wallWordMap_def]
  split_ifs with hex hpos
  · exfalso
    obtain ⟨c', hc', hνc'⟩ := C.eq_of_cellsOfCodimension_subset hex.choose_spec hw ▸ hpos
    linarith [smul_left_injective ℝ hνw (hνc.symm.trans hνc')]
  · exact congrArg (fun u => (FreeGroup.of u)⁻¹)
      (C.eq_of_cellsOfCodimension_subset hex.choose_spec hw)
  · exact (hex ⟨w, hw⟩).elim

/-- When no wall of `C` contains `w'`, `wallWordMap` sends `w'` to `1`. -/
@[simp]
theorem wallWordMap_of_forall_not_subset {C' C : FinitePolyhedralComplex h}
    (ν' : C'.walls → V →ₗ[ℝ] ℝ) (ν : C.walls → V →ₗ[ℝ] ℝ)
    {w' : C'.walls} (hw : ∀ w : C.walls, ¬ (w' : Set V) ⊆ (w : Set V)) :
    C'.wallWordMap C ν' ν w' = 1 := by
  simp [wallWordMap_def, hw]

namespace IsSubdivision

/-- Subdividing a complex can only enlarge the singular support of its wall family. -/
theorem singularSupport_walls_subset {C C' : FinitePolyhedralComplex h}
    (hsub : C'.IsSubdivision C) :
    singularSupport (fun P : C.walls => (P : Set V)) ⊆
      singularSupport (fun P : C'.walls => (P : Set V)) := by
  intro z hz
  rcases mem_singularSupport.mp hz with ⟨w, hzw⟩ | ⟨w₁, w₂, hne, hz₁, hz₂⟩
  · have hcl : IsClosed (w : Set V) :=
      (C.isConvexPolyhedron (mem_cellsOfCodimension.mp w.property).1).isClosed
    obtain ⟨w', hw', hsubw, hspan, hzw'⟩ :=
      hsub.exists_mem_cellsOfCodimension_subset w.property (intrinsicFrontier_subset hcl hzw)
    refine mem_singularSupport.mpr (.inl ⟨⟨w', hw'⟩, ?_⟩)
    rw [← intrinsicClosure_sdiff_intrinsicInterior] at hzw ⊢
    exact ⟨subset_intrinsicClosure hzw', fun hint =>
      hzw.2 (TauCeti.intrinsicInterior_mono_of_affineSpan_eq hsubw hspan hint)⟩
  · obtain ⟨w₁', hw₁', -, hspan₁, hz₁'⟩ :=
      hsub.exists_mem_cellsOfCodimension_subset w₁.property hz₁
    obtain ⟨w₂', hw₂', -, hspan₂, hz₂'⟩ :=
      hsub.exists_mem_cellsOfCodimension_subset w₂.property hz₂
    refine mem_singularSupport.mpr (.inr ⟨⟨w₁', hw₁'⟩, ⟨w₂', hw₂'⟩, ?_, hz₁', hz₂'⟩)
    rwa [hspan₁, hspan₂]

/-- An allowed endpoint for a subdivision `C'` of `C` is automatically an allowed endpoint for `C`.
-/
abbrev wallComplement {C C' : FinitePolyhedralComplex h} (hsub : C'.IsSubdivision C)
    (x : C'.WallComplement) : C.WallComplement where
  val := x.val
  notMem w hw := by
    obtain ⟨w', hw', -, -, hxw'⟩ := hsub.exists_mem_cellsOfCodimension_subset w.property hw
    exact x.notMem ⟨w', hw'⟩ hxw'

/-- Viewing an allowed vertex of `C'` as an allowed vertex of `C` preserves its ambient point. -/
@[simp]
theorem wallComplement_val {C C' : FinitePolyhedralComplex h} (hsub : C'.IsSubdivision C)
    (x : C'.WallComplement) : (hsub.wallComplement x).val = x.val :=
  (rfl)

/-- An admissible segment for a subdivision `C'` of `C` is automatically admissible for `C`. -/
theorem admissibleSegment {C C' : FinitePolyhedralComplex h} (hsub : C'.IsSubdivision C)
    {x y : C'.WallComplement} (a : TauCeti.WallComplement.AdmissibleSegment x y) :
    TauCeti.WallComplement.AdmissibleSegment (hsub.wallComplement x)
      (hsub.wallComplement y) where
  transverse w := by
    rintro ⟨t, ht, hzw⟩
    obtain ⟨w', hw', -, hspan, hzw'⟩ := hsub.exists_mem_cellsOfCodimension_subset w.property hzw
    rw [← hspan]
    exact a.transverse ⟨w', hw'⟩ ⟨t, ht, hzw'⟩
  regular t ht hs := a.regular t ht (hsub.singularSupport_walls_subset hs)

/-- The quiver prefunctor viewing paths admissible for a subdivision `C'` as paths admissible for
`C`. -/
abbrev wallPrefunctor {C C' : FinitePolyhedralComplex h} (hsub : C'.IsSubdivision C) :
    C'.WallComplement ⥤q C.WallComplement where
  obj x := hsub.wallComplement x
  map a := ⟨hsub.admissibleSegment a.down⟩

/-- `IsSubdivision.wallPrefunctor` commutes with segment reversal. -/
instance {C C' : FinitePolyhedralComplex h} (hsub : C'.IsSubdivision C) :
    hsub.wallPrefunctor.MapReverse where
  map_reverse' _ := Subsingleton.elim _ _

/-- View an admissible polygonal path for `C'` as an admissible polygonal path for `C`. -/
abbrev mapPath {C C' : FinitePolyhedralComplex h} (hsub : C'.IsSubdivision C)
    {x y : C'.WallComplement} (p : AdmissiblePLPath x y) :
    AdmissiblePLPath (hsub.wallComplement x) (hsub.wallComplement y) :=
  hsub.wallPrefunctor.mapPath p

/-- Viewing a path of `C'` in `C` preserves its ambient vertex list. -/
theorem map_val_vertices_mapPath {C C' : FinitePolyhedralComplex h} (hsub : C'.IsSubdivision C)
    {x y : C'.WallComplement} (p : AdmissiblePLPath x y) :
    (hsub.mapPath p).vertices.map TauCeti.WallComplement.val =
      p.vertices.map TauCeti.WallComplement.val := by
  simp only [Prefunctor.vertices_mapPath, List.map_map, Function.comp_def]

@[simp]
theorem toContinuousPath_mapPath {C C' : FinitePolyhedralComplex h} (hsub : C'.IsSubdivision C)
    {x y : C'.WallComplement} (p : AdmissiblePLPath x y) :
    (hsub.mapPath p).toContinuousPath = p.toContinuousPath := by
  induction p with
  | nil => simp
  | cons p a ih => simp only [Prefunctor.mapPath_cons, Quiver.Path.toContinuousPath_cons, ih]

/-- Every crossing of a wall `w` of `C` along a segment between vertices of a subdivision `C'`
arises from a crossing at the same parameter of a wall `w'` of `C'` contained in `w`. -/
theorem exists_mem_crossings_subset {C C' : FinitePolyhedralComplex h}
    (hsub : C'.IsSubdivision C) {x y : C'.WallComplement} {w : C.walls} {t : ℝ}
    (hwt : (w, t) ∈ TauCeti.WallComplement.crossings
      (hsub.wallComplement x) (hsub.wallComplement y)) :
    ∃ w' : C'.walls,
      (w' : Set V) ⊆ (w : Set V) ∧ (w', t) ∈ TauCeti.WallComplement.crossings x y := by
  obtain ⟨htI, hzw⟩ := (TauCeti.WallComplement.mem_crossings _ _ w t).mp hwt
  obtain ⟨w', hw', hsubw, -, hzw'⟩ :=
    hsub.exists_mem_cellsOfCodimension_subset w.property hzw
  exact ⟨⟨w', hw'⟩, hsubw,
    (TauCeti.WallComplement.mem_crossings x y ⟨w', hw'⟩ t).mpr ⟨htI, hzw'⟩⟩

open Classical in
/-- Viewing an admissible segment for a subdivision `C'` in `C` filters its ordered crossing list
to those walls of `C'` contained in a wall of `C`, replacing each by its ambient wall. -/
theorem orderedCrossings_wallPrefunctor {C C' : FinitePolyhedralComplex h}
    (hsub : C'.IsSubdivision C) {x y : C'.WallComplement} (e : x ⟶ y) :
    C.orderedCrossings (hsub.wallPrefunctor.map e) =
      (C'.orderedCrossings e).filterMap fun a =>
        if hex : ∃ w : C.walls, (a.1 : Set V) ⊆ (w : Set V) then
          some (hex.choose, a.2)
        else none := by
  let f : C'.walls × ℝ → Option (C.walls × ℝ) := fun a =>
    if hex : ∃ w : C.walls, (a.1 : Set V) ⊆ (w : Set V) then some (hex.choose, a.2) else none
  have hsome (a : C'.walls × ℝ) (b : C.walls × ℝ) :
      f a = some b ↔ (a.1 : Set V) ⊆ (b.1 : Set V) ∧ a.2 = b.2 := by
    rcases b with ⟨w, t⟩
    by_cases hex : ∃ u : C.walls, (a.1 : Set V) ⊆ (u : Set V)
    · simp only [f, hex, ↓reduceDIte, Option.some.injEq, Prod.mk.injEq]
      exact ⟨fun ⟨hw, ht⟩ => ⟨hw ▸ hex.choose_spec, ht⟩,
        fun ⟨hsubw, ht⟩ => ⟨C.eq_of_cellsOfCodimension_subset hex.choose_spec hsubw, ht⟩⟩
    · simp only [f, hex, ↓reduceDIte, reduceCtorEq, false_iff, not_and]
      exact fun hsubw _ => hex ⟨w, hsubw⟩
  refine (C.orderedCrossings_eq_iff _ _).mpr ⟨?_, fun ⟨w, t⟩ => ?_⟩
  · refine (C'.pairwise_orderedCrossings e).filterMap f fun a a' haa b hb b' hb' => ?_
    rw [hsome] at hb hb'
    simpa only [← hb.2, ← hb'.2] using haa
  · simp only [List.mem_filterMap, mem_orderedCrossings, Prod.exists]
    constructor
    · rintro ⟨w', s, hw's, hf⟩
      obtain ⟨hsubw, rfl⟩ := (hsome (w', s) (w, t)).mp hf
      obtain ⟨hsI, hzw'⟩ := (TauCeti.WallComplement.mem_crossings x y w' s).mp hw's
      exact (TauCeti.WallComplement.mem_crossings _ _ w s).mpr ⟨hsI, hsubw hzw'⟩
    · intro hwt
      obtain ⟨w', hsubw, hw't⟩ := hsub.exists_mem_crossings_subset hwt
      exact ⟨w', t, hw't, (hsome (w', t) (w, t)).mpr ⟨hsubw, rfl⟩⟩

private theorem neg_ite_sign_of_neg {c v : ℝ} (hc : c < 0) (hv : v ≠ 0) :
    -(if 0 < c * v then -1 else 1 : ℤ) = if 0 < v then -1 else 1 := by
  split_ifs with h1 h2 h2
  · linarith [mul_neg_of_neg_of_pos hc h2]
  · rfl
  · rfl
  · exact (h1 (mul_pos_of_neg_of_neg hc (lt_of_le_of_ne (not_lt.mp h2) hv))).elim

open Classical in
/-- Lifting a crossing letter of `C'` at a crossed wall `w'` by `C'.wallWordMap C ν' ν` gives the
coarse crossing letter on `C` when `w'` lies in a wall of `C`, and `1` otherwise. -/
theorem lift_wallWordMap_crossingLetter {C C' : FinitePolyhedralComplex h}
    (hsub : C'.IsSubdivision C) {ν' : C'.walls → V →ₗ[ℝ] ℝ} {ν : C.walls → V →ₗ[ℝ] ℝ}
    (hν' : C'.IsWallCoorientation ν') (hν : C.IsWallCoorientation ν)
    {x y : C'.WallComplement} (e : x ⟶ y) {w' : C'.walls} {t : ℝ}
    (hw't : (w', t) ∈ TauCeti.WallComplement.crossings x y) :
    FreeGroup.lift (C'.wallWordMap C ν' ν) (C'.crossingLetter ν' x y w') =
      if hex : ∃ w : C.walls, (w' : Set V) ⊆ (w : Set V) then
        C.crossingLetter ν (hsub.wallComplement x) (hsub.wallComplement y) hex.choose
      else 1 := by
  rw [C'.crossingLetter_eq_zpow, map_zpow, FreeGroup.lift_apply_of]
  by_cases hex : ∃ w : C.walls, (w' : Set V) ⊆ (w : Set V)
  · simp only [dite_eq_left hex, C.crossingLetter_eq_zpow]
    set w := hex.choose
    have hww : (w' : Set V) ⊆ (w : Set V) := hex.choose_spec
    obtain ⟨htI, hzw'⟩ := (TauCeti.WallComplement.mem_crossings x y w' t).mp hw't
    obtain ⟨c, hc0, hνc⟩ :=
      hν.exists_ne_zero_eq_smul hν' (AffineSubspace.direction_le (affineSpan_mono ℝ hww))
    have hv_ne : ν w (y.val - x.val) ≠ 0 := fun hz =>
      (hsub.admissibleSegment e.down).transverse w ⟨t, htI, hww hzw'⟩
        ((hν.ker_eq w) ▸ LinearMap.mem_ker.mpr hz)
    rcases lt_or_gt_of_ne hc0 with hneg | hpos
    · rw [wallWordMap_of_subset_neg (hν.ne_zero w) hww hneg hνc, hνc, LinearMap.smul_apply,
        smul_eq_mul, inv_zpow, ← zpow_neg]
      exact congrArg (FreeGroup.of w ^ ·) (neg_ite_sign_of_neg hneg hv_ne)
    · rw [wallWordMap_of_subset_pos hww hpos hνc, hνc, LinearMap.smul_apply, smul_eq_mul]
      simp only [mul_pos_iff_of_pos_left hpos]
  · simp only [dite_eq_right hex,
      wallWordMap_of_forall_not_subset ν' ν (fun w hw => hex ⟨w, hw⟩), one_zpow]

/-- Viewing a segment of `C'` in `C` maps its segment crossing word by
`FreeGroup.lift (C'.wallWordMap C ν' ν)`. -/
theorem segmentCrossingWord_wallPrefunctor {C C' : FinitePolyhedralComplex h}
    (hsub : C'.IsSubdivision C) {ν' : C'.walls → V →ₗ[ℝ] ℝ} {ν : C.walls → V →ₗ[ℝ] ℝ}
    (hν' : C'.IsWallCoorientation ν') (hν : C.IsWallCoorientation ν)
    {x y : C'.WallComplement} (e : x ⟶ y) :
    C.segmentCrossingWord ν (hsub.wallPrefunctor.map e) =
      FreeGroup.lift (C'.wallWordMap C ν' ν) (C'.segmentCrossingWord ν' e) := by
  classical
  have hmem : ∀ a ∈ (C'.orderedCrossings e).reverse,
      a ∈ TauCeti.WallComplement.crossings x y := fun a ha =>
    (C'.mem_orderedCrossings e a).mp (List.mem_reverse.mp ha)
  rw [C.segmentCrossingWord_def, C'.segmentCrossingWord_def,
    hsub.orderedCrossings_wallPrefunctor e, ← List.filterMap_reverse]
  generalize (C'.orderedCrossings e).reverse = l at hmem
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha : (a.1, a.2) ∈ TauCeti.WallComplement.crossings x y :=
      hmem a List.mem_cons_self
    have hl := fun b hb => hmem b (List.mem_cons_of_mem a hb)
    by_cases hex : ∃ w : C.walls, (a.1 : Set V) ⊆ (w : Set V) <;>
      simp only [List.filterMap_cons, hex, ↓reduceDIte, List.map_cons, List.prod_cons, map_mul,
        ih hl, hsub.lift_wallWordMap_crossingLetter hν' hν e ha, one_mul]

/-- Subdividing a finite polyhedral complex `C` into `C'` maps the crossing word of any admissible
path for `C'` to its crossing word on `C` via `FreeGroup.lift (C'.wallWordMap C ν' ν)`. -/
theorem crossingWord_mapPath {C C' : FinitePolyhedralComplex h}
    (hsub : C'.IsSubdivision C) {ν' : C'.walls → V →ₗ[ℝ] ℝ} {ν : C.walls → V →ₗ[ℝ] ℝ}
    (hν' : C'.IsWallCoorientation ν') (hν : C.IsWallCoorientation ν)
    {x y : C'.WallComplement} (p : AdmissiblePLPath x y) :
    (hsub.mapPath p).crossingWord ν =
      FreeGroup.lift (C'.wallWordMap C ν' ν) (p.crossingWord ν') := by
  induction p with
  | nil => simp
  | cons p a ih =>
    simp only [Prefunctor.mapPath_cons, Quiver.Path.crossingWord_cons, map_mul, ih,
      hsub.segmentCrossingWord_wallPrefunctor hν' hν a]

end IsSubdivision

/-! ### Integral affine transport -/

section IntegralAffineTransport

variable {N' U : Type*} [AddCommGroup N'] [NormedAddCommGroup U] [NormedSpace ℝ U]
  {i' : N' →+ U} {h' : TauCeti.Toric.IsIntegralLattice i'}

/-- The quiver prefunctor transporting admissible segments of `C` to `C.image e` along `e`. -/
abbrev imagePrefunctor (C : FinitePolyhedralComplex h) (e : Toric.IntegralAffineEquiv h h') :
    C.WallComplement ⥤q (C.image e).WallComplement :=
  TauCeti.WallComplement.mapReindexPrefunctor e.toContinuousAffineEquiv (C.wallsEquiv e)
    (fun w => (C.coe_cellsOfCodimensionEquiv_apply e 1 w).trans
      (congrArg (· '' _) e.coe_toContinuousAffineEquiv.symm))

/-- Transport an allowed vertex of `C` to `C.image e` along an integral affine equivalence `e`. -/
abbrev imageEndpoint (C : FinitePolyhedralComplex h) (e : Toric.IntegralAffineEquiv h h')
    (x : C.WallComplement) : (C.image e).WallComplement :=
  (C.imagePrefunctor e).obj x

/-- Transport an admissible polygonal path of `C` to `C.image e` along an integral affine
equivalence `e`. -/
abbrev imagePath (C : FinitePolyhedralComplex h) (e : Toric.IntegralAffineEquiv h h')
    {x y : C.WallComplement} (p : AdmissiblePLPath x y) :
    AdmissiblePLPath (C.imageEndpoint e x) (C.imageEndpoint e y) :=
  (C.imagePrefunctor e).mapPath p

/-- Transporting a path along `e` maps its ambient vertex list by `e`. -/
theorem map_val_vertices_imagePath (C : FinitePolyhedralComplex h)
    (e : Toric.IntegralAffineEquiv h h') {x y : C.WallComplement} (p : AdmissiblePLPath x y) :
    (C.imagePath e p).vertices.map TauCeti.WallComplement.val =
      (p.vertices.map TauCeti.WallComplement.val).map e := by
  simp only [Prefunctor.vertices_mapPath, List.map_map, Function.comp_def,
    e.coe_toContinuousAffineEquiv]

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
  · have hw' : (w' : Set U) = e.toAffineEquiv.toAffineMap '' (w : Set V) := by
      simpa [w] using C.coe_cellsOfCodimensionEquiv_apply e 1 w
    rw [hw', ← AffineSubspace.map_span, AffineSubspace.map_direction]
    rintro _ ⟨v, hv, rfl⟩
    simpa using hle hv

/-- Transporting an admissible segment along `C.imagePrefunctor e` maps the walls of its ordered
crossings by `C.wallsEquiv e` while preserving crossing times. -/
theorem orderedCrossings_imagePrefunctor (C : FinitePolyhedralComplex h)
    (e : Toric.IntegralAffineEquiv h h') {x y : C.WallComplement} (a : x ⟶ y) :
    (C.image e).orderedCrossings ((C.imagePrefunctor e).map a) =
      (C.orderedCrossings a).map (Prod.map (C.wallsEquiv e) id) := by
  refine ((C.image e).orderedCrossings_eq_iff _ _).mpr ⟨?_, fun ⟨w', t⟩ => ?_⟩
  · exact List.pairwise_map.mpr (C.pairwise_orderedCrossings a)
  · obtain ⟨w, rfl⟩ := (C.wallsEquiv e).surjective w'
    have hmem := TauCeti.WallComplement.mem_crossings_mapReindex x y
      e.toContinuousAffineEquiv (C.wallsEquiv e)
      (fun u => (C.coe_cellsOfCodimensionEquiv_apply e 1 u).trans
        (congrArg (· '' _) e.coe_toContinuousAffineEquiv.symm)) w t
    simp only [List.mem_map, Prod.exists, Prod.map_apply, id_eq, Prod.mk.injEq,
      (C.wallsEquiv e).injective.eq_iff, mem_orderedCrossings, hmem]
    exact ⟨fun ⟨_, _, hwt, rfl, rfl⟩ => hwt, fun hwt => ⟨w, t, hwt, rfl, rfl⟩⟩

/-- Transporting endpoints and coorientations along `e` maps each crossing letter by
`FreeGroup.map (C.wallsEquiv e)`. -/
theorem crossingLetter_image (C : FinitePolyhedralComplex h) (ν : C.walls → V →ₗ[ℝ] ℝ)
    (e : Toric.IntegralAffineEquiv h h') (x y : C.WallComplement) (w : C.walls) :
    (C.image e).crossingLetter
        (fun w' => (ν ((C.wallsEquiv e).symm w')).comp e.toAffineEquiv.linear.symm.toLinearMap)
        (C.imageEndpoint e x) (C.imageEndpoint e y) (C.wallsEquiv e w) =
      FreeGroup.map (C.wallsEquiv e) (C.crossingLetter ν x y w) := by
  have hsub : e.toAffineEquiv.linear.symm (e y.val - e x.val) = y.val - x.val :=
    e.toAffineEquiv.linear_symm_apply_sub y.val x.val
  rw [(C.image e).crossingLetter_eq_zpow, C.crossingLetter_eq_zpow, map_zpow, FreeGroup.map.of]
  simp only [Equiv.symm_apply_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    e.coe_toContinuousAffineEquiv, hsub]

/-- Transporting an admissible segment along `C.imagePrefunctor e` maps its segment crossing word
by `FreeGroup.map (C.wallsEquiv e)` under pushed-forward coorientations. -/
@[simp]
theorem segmentCrossingWord_imagePrefunctor (C : FinitePolyhedralComplex h)
    (ν : C.walls → V →ₗ[ℝ] ℝ) (e : Toric.IntegralAffineEquiv h h')
    {x y : C.WallComplement} (a : x ⟶ y) :
    (C.image e).segmentCrossingWord
        (fun w' => (ν ((C.wallsEquiv e).symm w')).comp e.toAffineEquiv.linear.symm.toLinearMap)
        ((C.imagePrefunctor e).map a) =
      FreeGroup.map (C.wallsEquiv e) (C.segmentCrossingWord ν a) := by
  rw [(C.image e).segmentCrossingWord_def, C.segmentCrossingWord_def,
    C.orderedCrossings_imagePrefunctor e a, map_list_prod]
  simp only [List.map_reverse, List.map_map, Function.comp_def, Prod.map_fst,
    C.crossingLetter_image ν e x y]

/-- Transporting an admissible polygonal path along an `IntegralAffineEquiv` `e` maps its
`crossingWord` by `FreeGroup.map (C.wallsEquiv e)` under the pushed-forward coorientations
`ν ∘ e.linear⁻¹`. -/
@[simp]
theorem crossingWord_image (C : FinitePolyhedralComplex h) (ν : C.walls → V →ₗ[ℝ] ℝ)
    (e : Toric.IntegralAffineEquiv h h') {x y : C.WallComplement} (p : AdmissiblePLPath x y) :
    (C.imagePath e p).crossingWord
        (fun w' => (ν ((C.wallsEquiv e).symm w')).comp e.toAffineEquiv.linear.symm.toLinearMap) =
      FreeGroup.map (C.wallsEquiv e) (p.crossingWord ν) := by
  induction p with
  | nil => simp
  | cons p a ih =>
    simp only [Prefunctor.mapPath_cons, Quiver.Path.crossingWord_cons, map_mul, ih,
      C.segmentCrossingWord_imagePrefunctor ν e a]

end IntegralAffineTransport

end TauCeti.FinitePolyhedralComplex
