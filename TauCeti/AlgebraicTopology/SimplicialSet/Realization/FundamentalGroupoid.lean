/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import TauCeti.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.ULift
public import TauCeti.AlgebraicTopology.SimplicialSet.Realization.Basic
import TauCeti.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Edge paths and fundamental groupoid functor for geometric realization

An edge `e : X.Edge x₀ x₁` of `X : SSet` parametrizes a path `e.toTopPath` in `|X|` via
`StdSimplex.homeomorphI`. Degenerate edges give constant paths (`SSet.Edge.toTopPath_id`), and any
`2`-simplex `h : Edge.CompStruct e₀₁ e₁₂ e₀₂` witnesses
`(e₀₁.toTopPath.trans e₁₂.toTopPath).Homotopic e₀₂.toTopPath`
(`SSet.Edge.CompStruct.homotopic_toTopPath`). By `SSet.FundamentalGroupoid.desc`, these assemble
into `SSet.toTopFundamentalGroupoid X : SSet.FundamentalGroupoid X ⥤ _root_.FundamentalGroupoid |X|`
compatible up to natural isomorphism with simplicial maps (`SSet.mapFundamentalGroupoidToTopIso`)
and universe lifting (`SSet.uliftFundamentalGroupoidToTopIso`).

## References

* P. G. Goerss and J. F. Jardine, *Simplicial Homotopy Theory*, Progress in Mathematics 174,
  Birkhäuser, 1999, Section III.1.
-/

public section

open CategoryTheory Opposite Simplicial Convexity

universe v u

namespace SSet

section EdgePath

variable {X Y : SSet.{u}} {x₀ x₁ x₂ : X _⦋0⦌}

/-- The path in `|X|` from `toTopPoint x₀` to `toTopPoint x₁` traced by `e : X.Edge x₀ x₁`. -/
noncomputable def Edge.toTopPath (e : X.Edge x₀ x₁) :
    _root_.Path (toTopPoint x₀) (toTopPoint x₁) where
  toContinuousMap := (ContinuousMap.mk (toTopObjMk e.edge) (continuous_toTopObjMk e.edge)).comp
    (StdSimplex.homeomorphI.symm : C(unitInterval, StdSimplex ℝ (Fin 2)))
  source' := by simp [toTopObjMk_single, ← SimplexCategory.δ_one_eq_const,
    ← SimplicialObject.δ_def, e.src_eq]
  target' := by simp [toTopObjMk_single, ← SimplexCategory.δ_zero_eq_const,
    ← SimplicialObject.δ_def, e.tgt_eq]

@[simp]
lemma Edge.toTopPath_apply (e : X.Edge x₀ x₁) (t : unitInterval) :
    e.toTopPath t = toTopObjMk e.edge (StdSimplex.homeomorphI.symm t) := (rfl)

/-- A degenerate edge `Edge.id x` realizes to the constant path at `toTopPoint x`. -/
@[simp]
lemma Edge.toTopPath_id (x : X _⦋0⦌) : (Edge.id x).toTopPath = _root_.Path.refl (toTopPoint x) := by
  ext t; simp [Edge.id_edge, SimplicialObject.σ_def, toTopObjMk_map]

/-- Pushing an edge path forward along `toTop.map f` gives the path of the mapped edge. -/
lemma Edge.toTopPath_map (e : X.Edge x₀ x₁) (f : X ⟶ Y) :
    (e.map f).toTopPath = (e.toTopPath.map (toTop.map f).hom.continuous).cast
      (toTop_map_toTopPoint f x₀).symm (toTop_map_toTopPoint f x₁).symm := by
  ext t; simp [Edge.map_edge]

/-- Lifting an edge `e` along `uliftFunctor` pushes `e.toTopPath` forward along
`toTopUliftHomeomorph X`. -/
lemma Edge.toTopPath_ulift (e : X.Edge x₀ x₁) :
    e.ulift.{v}.toTopPath =
      (e.toTopPath.map (toTopUliftHomeomorph.{v, u} X).continuous).cast
        (toTopUliftHomeomorph_toTopPoint.{v, u} x₀).symm
        (toTopUliftHomeomorph_toTopPoint.{v, u} x₁).symm := by
  ext t; simp [Edge.ulift_edge]

/-- A `2`-simplex `h : Edge.CompStruct e₀₁ e₁₂ e₀₂` witnesses a path homotopy rel endpoints from
`e₀₁.toTopPath.trans e₁₂.toTopPath` to `e₀₂.toTopPath` in `|X|`. -/
theorem Edge.CompStruct.homotopic_toTopPath {e₀₁ : X.Edge x₀ x₁} {e₁₂ : X.Edge x₁ x₂}
    {e₀₂ : X.Edge x₀ x₂} (h : Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    (e₀₁.toTopPath.trans e₁₂.toTopPath).Homotopic e₀₂.toTopPath := by
  let facePath (k : Fin 3) : _root_.Path
      (StdSimplex.single (R := ℝ) (k.succAbove 0)) (StdSimplex.single (k.succAbove 1)) :=
    { toContinuousMap := (ContinuousMap.mk (StdSimplex.map (SimplexCategory.δ k))
        (StdSimplex.continuous_map ℝ _)).comp
        (StdSimplex.homeomorphI.symm : C(unitInterval, StdSimplex ℝ (Fin 2)))
      source' := by simp [SimplexCategory.δ_apply]
      target' := by simp [SimplexCategory.δ_apply] }
  let p₀₁ : _root_.Path (StdSimplex.single (R := ℝ) (0 : Fin 3)) (StdSimplex.single 1) := facePath 2
  let p₁₂ : _root_.Path (StdSimplex.single (R := ℝ) (1 : Fin 3)) (StdSimplex.single 2) := facePath 0
  let p₀₂ : _root_.Path (StdSimplex.single (R := ℝ) (0 : Fin 3)) (StdSimplex.single 2) := facePath 1
  obtain ⟨H⟩ := SimplyConnectedSpace.paths_homotopic (p₀₁.trans p₁₂) p₀₂
  let F : C(StdSimplex ℝ (Fin 3), |X|) := ⟨toTopObjMk h.simplex, continuous_toTopObjMk h.simplex⟩
  have hx₀ : toTopPoint x₀ = F (StdSimplex.single 0) := by
    have hc₀ : SimplexCategory.const ⦋0⦌ ⦋2⦌ 0 = SimplexCategory.δ 1 ≫ SimplexCategory.δ 2 := by
      rw [SimplexCategory.δ_one_eq_const, SimplexCategory.const_comp]; rfl
    simp [F, hc₀, ← SimplicialObject.δ_def, h.d₂, e₀₁.src_eq]
  have hx₁ : toTopPoint x₁ = F (StdSimplex.single 1) := by
    have hc₁ : SimplexCategory.const ⦋0⦌ ⦋2⦌ 1 = SimplexCategory.δ 0 ≫ SimplexCategory.δ 2 := by
      rw [SimplexCategory.δ_zero_eq_const, SimplexCategory.const_comp]; rfl
    simp [F, hc₁, ← SimplicialObject.δ_def, h.d₂, e₀₁.tgt_eq]
  have hx₂ : toTopPoint x₂ = F (StdSimplex.single 2) := by
    have hc₂ : SimplexCategory.const ⦋0⦌ ⦋2⦌ 2 = SimplexCategory.δ 0 ≫ SimplexCategory.δ 0 := by
      rw [SimplexCategory.δ_zero_eq_const, SimplexCategory.const_comp]; rfl
    simp [F, hc₂, ← SimplicialObject.δ_def, h.d₀, e₁₂.tgt_eq]
  have hface (k : Fin 3) (s : unitInterval) :
      F (facePath k s) = toTopObjMk (X.δ k h.simplex) (StdSimplex.homeomorphI.symm s) := by
    simp [F, facePath, SimplicialObject.δ_def, toTopObjMk_map]
  have htrans : ((p₀₁.trans p₁₂).map F.continuous).cast hx₀ hx₂ =
      e₀₁.toTopPath.trans e₁₂.toTopPath := by
    rw [_root_.Path.map_trans, _root_.Path.cast_trans _ _ hx₀ hx₁ hx₂]
    congr 1
    · ext t; exact (hface 2 t).trans (by rw [h.d₂, Edge.toTopPath_apply])
    · ext t; exact (hface 0 t).trans (by rw [h.d₀, Edge.toTopPath_apply])
  have hdiag : (p₀₂.map F.continuous).cast hx₀ hx₂ = e₀₂.toTopPath := by
    ext t; exact (hface 1 t).trans (by rw [h.d₁, Edge.toTopPath_apply])
  exact ⟨((H.map F).pathCast hx₀ hx₂).cast htrans hdiag⟩

end EdgePath

section FundamentalGroupoid

-- `@[expose]` is required by `module` so dependent morphism equalities over
-- `(toTopFundamentalGroupoid X).obj` typecheck in downstream public statements.
/-- The canonical functor `SSet.FundamentalGroupoid X ⥤ _root_.FundamentalGroupoid |X|` sending
`.mk x` to `.mk (toTopPoint x)` and `homMk e` to `FundamentalGroupoid.fromPath (.mk e.toTopPath)`.
-/
@[expose, implicit_reducible]
noncomputable def toTopFundamentalGroupoid (X : SSet.{u}) :
    SSet.FundamentalGroupoid X ⥤ _root_.FundamentalGroupoid |X| :=
  FundamentalGroupoid.desc (fun x ↦ .mk (toTopPoint x))
    (fun e ↦ _root_.FundamentalGroupoid.fromPath (.mk e.toTopPath))
    (fun h ↦ Quotient.sound h.homotopic_toTopPath)

@[simp]
lemma toTopFundamentalGroupoid_obj_mk (X : SSet.{u}) (x : X _⦋0⦌) :
    (toTopFundamentalGroupoid X).obj (.mk x) = .mk (toTopPoint x) := (rfl)

@[simp]
lemma toTopFundamentalGroupoid_map_homMk (X : SSet.{u}) {x y : X _⦋0⦌} (e : X.Edge x y) :
    (toTopFundamentalGroupoid X).map (FundamentalGroupoid.homMk e) =
      _root_.FundamentalGroupoid.fromPath (.mk e.toTopPath) :=
  FundamentalGroupoid.desc_map_homMk _ _ (fun h ↦ Quotient.sound h.homotopic_toTopPath) e

private lemma mapFundamentalGroupoid_toTop_obj {X Y : SSet.{u}} (f : X ⟶ Y) (x : X _⦋0⦌) :
    (mapFundamentalGroupoid f ⋙ toTopFundamentalGroupoid Y).obj (.mk x) =
      (toTopFundamentalGroupoid X ⋙ _root_.FundamentalGroupoid.map (toTop.map f).hom).obj (.mk x) :=
  _root_.FundamentalGroupoid.ext (toTop_map_toTopPoint f x).symm

/-- Naturality isomorphism comparing `toTopFundamentalGroupoid` along `f : X ⟶ Y` with the
topological fundamental groupoid functor induced by `toTop.map f`. -/
noncomputable def mapFundamentalGroupoidToTopIso {X Y : SSet.{u}} (f : X ⟶ Y) :
    mapFundamentalGroupoid f ⋙ toTopFundamentalGroupoid Y ≅
      toTopFundamentalGroupoid X ⋙ _root_.FundamentalGroupoid.map (toTop.map f).hom :=
  FundamentalGroupoid.natIsoMk (fun x ↦ eqToIso (mapFundamentalGroupoid_toTop_obj f x))
    fun e ↦ by
      dsimp only [Functor.comp_obj, Functor.comp_map]
      rw [mapFundamentalGroupoid_map_homMk, toTopFundamentalGroupoid_map_homMk,
        toTopFundamentalGroupoid_map_homMk]
      exact _root_.FundamentalGroupoid.fromPath_naturality_eqToHom (φ := (toTop.map f).hom)
        (toTop_map_toTopPoint f _) (toTop_map_toTopPoint f _)
        e.toTopPath (e.map f).toTopPath (e.toTopPath_map f)

@[simp] lemma mapFundamentalGroupoidToTopIso_hom_app {X Y : SSet.{u}} (f : X ⟶ Y)
    (x : SSet.FundamentalGroupoid X) :
    (mapFundamentalGroupoidToTopIso f).hom.app x = eqToHom (by cases x; ext; simp) := by
  cases x; rfl

@[simp] lemma mapFundamentalGroupoidToTopIso_inv_app {X Y : SSet.{u}} (f : X ⟶ Y)
    (x : SSet.FundamentalGroupoid X) :
    (mapFundamentalGroupoidToTopIso f).inv.app x = eqToHom (by cases x; ext; simp) := by
  cases x; rfl

private lemma uliftFundamentalGroupoid_toTop_obj (X : SSet.{u}) (x : X _⦋0⦌) :
    (uliftFundamentalGroupoid.{v} X ⋙ toTopFundamentalGroupoid (uliftFunctor.{v, u}.obj X)).obj
        (.mk x) =
      (toTopFundamentalGroupoid X ⋙
        _root_.FundamentalGroupoid.map (toTopUliftHomeomorph.{v, u} X : C(_, _))).obj (.mk x) :=
  _root_.FundamentalGroupoid.ext (toTopUliftHomeomorph_toTopPoint.{v, u} x).symm

/-- Compatibility isomorphism comparing `toTopFundamentalGroupoid` along `uliftFunctor` with the
topological fundamental groupoid functor induced by `toTopUliftHomeomorph X`. -/
noncomputable def uliftFundamentalGroupoidToTopIso (X : SSet.{u}) :
    uliftFundamentalGroupoid.{v} X ⋙ toTopFundamentalGroupoid (uliftFunctor.{v, u}.obj X) ≅
      toTopFundamentalGroupoid X ⋙
        _root_.FundamentalGroupoid.map (toTopUliftHomeomorph.{v, u} X : C(_, _)) :=
  FundamentalGroupoid.natIsoMk (fun x ↦ eqToIso (uliftFundamentalGroupoid_toTop_obj.{v} X x))
    fun e ↦ by
      dsimp only [Functor.comp_obj, Functor.comp_map]
      rw [uliftFundamentalGroupoid_map_homMk, toTopFundamentalGroupoid_map_homMk,
        toTopFundamentalGroupoid_map_homMk]
      exact _root_.FundamentalGroupoid.fromPath_naturality_eqToHom
        (φ := (toTopUliftHomeomorph.{v, u} X : C(_, _)))
        (toTopUliftHomeomorph_toTopPoint.{v, u} _) (toTopUliftHomeomorph_toTopPoint.{v, u} _)
        e.toTopPath e.ulift.{v}.toTopPath (e.toTopPath_ulift.{v})

@[simp] lemma uliftFundamentalGroupoidToTopIso_hom_app (X : SSet.{u})
    (x : SSet.FundamentalGroupoid X) :
    (uliftFundamentalGroupoidToTopIso.{v} X).hom.app x = eqToHom (by cases x; ext; simp) := by
  cases x; rfl

@[simp] lemma uliftFundamentalGroupoidToTopIso_inv_app (X : SSet.{u})
    (x : SSet.FundamentalGroupoid X) :
    (uliftFundamentalGroupoidToTopIso.{v} X).inv.app x = eqToHom (by cases x; ext; simp) := by
  cases x; rfl

end FundamentalGroupoid

end SSet
