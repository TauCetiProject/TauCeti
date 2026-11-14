/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Realization.Basic
public import TauCeti.Geometry.Convex.ConvexSpace.ContractibleSpaceStdSimplex

/-!
# Edge paths and fundamental groupoid functor for geometric realization

An edge `e : X.Edge x₀ x₁` of a simplicial set `X` parametrizes a continuous path
`e.toTopPath : Path (toTopPoint x₀) (toTopPoint x₁)` in the geometric realization `|X|` via the
standard homeomorphism `StdSimplex.homeomorphI : StdSimplex ℝ (Fin 2) ≃ₜ unitInterval`.

Degenerate edges `Edge.id x` realize to constant paths (`SSet.Edge.toTopPath_id`), and any
`2`-simplex `h : Edge.CompStruct e₀₁ e₁₂ e₀₂` witnesses a path homotopy
`(e₀₁.toTopPath.trans e₁₂.toTopPath).Homotopic e₀₂.toTopPath`
(`SSet.Edge.CompStruct.homotopic_toTopPath`): the concatenated path along the `[0, 1]` and `[1, 2]`
faces of `StdSimplex ℝ (Fin 3)` and the diagonal path along `[0, 2]` share endpoints inside the
contractible — hence simply connected — topological `2`-simplex, and pushing their homotopy forward
along `toTopObjMk h.simplex` gives the homotopy in `|X|`.

Using the universal property `SSet.FundamentalGroupoid.desc`, these paths assemble into a functor
`SSet.toTopFundamentalGroupoid X : SSet.FundamentalGroupoid X ⥤ _root_.FundamentalGroupoid |X|`
compatible up to natural isomorphism with simplicial maps (`SSet.mapFundamentalGroupoidToTopIso`).

## References

* P. G. Goerss and J. F. Jardine, *Simplicial Homotopy Theory*, Progress in Mathematics 174,
  Birkhäuser, 1999, Section III.1.
-/

public section

open CategoryTheory Opposite Simplicial Convexity

universe u

namespace SSet

section EdgePath

variable {X Y : SSet.{u}} {x₀ x₁ x₂ : X _⦋0⦌}

private lemma const_zero_one_zero : SimplexCategory.const ⦋0⦌ ⦋1⦌ 0 = SimplexCategory.δ 1 := by
  ext a : 3; fin_cases a; rfl

private lemma const_zero_one_one : SimplexCategory.const ⦋0⦌ ⦋1⦌ 1 = SimplexCategory.δ 0 := by
  ext a : 3; fin_cases a; rfl

private lemma const_zero_two_zero :
    SimplexCategory.const ⦋0⦌ ⦋2⦌ 0 = SimplexCategory.const ⦋0⦌ ⦋1⦌ 0 ≫ SimplexCategory.δ 2 := by
  ext a : 3; fin_cases a; rfl

private lemma const_zero_two_two :
    SimplexCategory.const ⦋0⦌ ⦋2⦌ 2 = SimplexCategory.const ⦋0⦌ ⦋1⦌ 1 ≫ SimplexCategory.δ 0 := by
  ext a : 3; fin_cases a; rfl

/-- The continuous path in `|X|` from `toTopPoint x₀` to `toTopPoint x₁` traced by an edge
`e : X.Edge x₀ x₁`. -/
noncomputable def Edge.toTopPath (e : X.Edge x₀ x₁) :
    _root_.Path (toTopPoint x₀) (toTopPoint x₁) where
  toContinuousMap := (ContinuousMap.mk (toTopObjMk e.edge) (continuous_toTopObjMk e.edge)).comp
    (StdSimplex.homeomorphI.symm : C(unitInterval, StdSimplex ℝ (Fin 2)))
  source' := by
    simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      StdSimplex.homeomorphI_symm_zero, toTopObjMk_single, const_zero_one_zero,
      ← SimplicialObject.δ_def, e.src_eq]
  target' := by
    simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
      StdSimplex.homeomorphI_symm_one, toTopObjMk_single, const_zero_one_one,
      ← SimplicialObject.δ_def, e.tgt_eq]

@[simp]
lemma Edge.toTopPath_apply (e : X.Edge x₀ x₁) (t : unitInterval) :
    e.toTopPath t = toTopObjMk e.edge (StdSimplex.homeomorphI.symm t) :=
  (rfl)

/-- A degenerate edge `Edge.id x` realizes to the constant path at `toTopPoint x`. -/
@[simp]
lemma Edge.toTopPath_id (x : X _⦋0⦌) :
    (Edge.id x).toTopPath = _root_.Path.refl (toTopPoint x) := by
  ext t
  simp only [toTopPath_apply, Edge.id_edge, SimplicialObject.σ_def, toTopObjMk_map, toTopObjMk_zero,
    _root_.Path.refl_apply]

/-- Pushing an edge path forward along `toTop.map f` gives the path of the mapped edge. -/
lemma Edge.toTopPath_map (e : X.Edge x₀ x₁) (f : X ⟶ Y) :
    (e.map f).toTopPath = (e.toTopPath.map (toTop.map f).hom.continuous).cast
      (toTop_map_toTopPoint f x₀).symm (toTop_map_toTopPoint f x₁).symm := by
  ext t
  simp only [toTopPath_apply, Edge.map_edge, _root_.Path.cast_coe, _root_.Path.map_coe,
    Function.comp_apply, toTop_map_toTopObjMk]

/-- A `2`-simplex `h : Edge.CompStruct e₀₁ e₁₂ e₀₂` witnesses a homotopy with fixed endpoints from
the concatenation `e₀₁.toTopPath.trans e₁₂.toTopPath` to `e₀₂.toTopPath` in `|X|`. -/
theorem Edge.CompStruct.homotopic_toTopPath {e₀₁ : X.Edge x₀ x₁} {e₁₂ : X.Edge x₁ x₂}
    {e₀₂ : X.Edge x₀ x₂} (h : Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    (e₀₁.toTopPath.trans e₁₂.toTopPath).Homotopic e₀₂.toTopPath := by
  -- Build each face path `δ k` inside the contractible `2`-simplex `StdSimplex ℝ (Fin 3)`.
  let facePath (k : Fin 3) :
      _root_.Path (StdSimplex.single (R := ℝ) (k.succAbove 0))
        (StdSimplex.single (k.succAbove 1)) :=
    { toContinuousMap :=
        (ContinuousMap.mk (StdSimplex.map (SimplexCategory.δ k))
          (StdSimplex.continuous_map ℝ _)).comp
          (StdSimplex.homeomorphI.symm : C(unitInterval, StdSimplex ℝ (Fin 2)))
      source' := by simp [SimplexCategory.δ]; rfl
      target' := by simp [SimplexCategory.δ]; rfl }
  let p₀₁ : _root_.Path (StdSimplex.single (R := ℝ) (0 : Fin 3)) (StdSimplex.single 1) := facePath 2
  let p₁₂ : _root_.Path (StdSimplex.single (R := ℝ) (1 : Fin 3)) (StdSimplex.single 2) := facePath 0
  let p₀₂ : _root_.Path (StdSimplex.single (R := ℝ) (0 : Fin 3)) (StdSimplex.single 2) := facePath 1
  obtain ⟨H⟩ := SimplyConnectedSpace.paths_homotopic (p₀₁.trans p₁₂) p₀₂
  let F : C(StdSimplex ℝ (Fin 3), |X|) := ⟨toTopObjMk h.simplex, continuous_toTopObjMk h.simplex⟩
  have hx₀ : toTopPoint x₀ = F (StdSimplex.single 0) := by
    simp only [F, ContinuousMap.coe_mk, toTopObjMk_single, const_zero_two_zero, op_comp,
      Functor.map_comp_apply, ← SimplicialObject.δ_def, h.d₂, const_zero_one_zero, e₀₁.src_eq]
  have hx₂ : toTopPoint x₂ = F (StdSimplex.single 2) := by
    simp only [F, ContinuousMap.coe_mk, toTopObjMk_single, const_zero_two_two, op_comp,
      Functor.map_comp_apply, ← SimplicialObject.δ_def, h.d₀, const_zero_one_one, e₁₂.tgt_eq]
  have htrans : ((p₀₁.trans p₁₂).map F.continuous).cast hx₀ hx₂ =
      e₀₁.toTopPath.trans e₁₂.toTopPath := by
    ext t
    rw [_root_.Path.cast_coe, _root_.Path.map_coe, Function.comp_apply, _root_.Path.trans_apply,
      _root_.Path.trans_apply]
    split_ifs
    · change toTopObjMk h.simplex (StdSimplex.map (SimplexCategory.δ 2)
        (StdSimplex.homeomorphI.symm _)) = _
      rw [← toTopObjMk_map, ← SimplicialObject.δ_def, h.d₂, Edge.toTopPath_apply]
    · change toTopObjMk h.simplex (StdSimplex.map (SimplexCategory.δ 0)
        (StdSimplex.homeomorphI.symm _)) = _
      rw [← toTopObjMk_map, ← SimplicialObject.δ_def, h.d₀, Edge.toTopPath_apply]
  have hdiag : (p₀₂.map F.continuous).cast hx₀ hx₂ = e₀₂.toTopPath := by
    ext t
    change toTopObjMk h.simplex (StdSimplex.map (SimplexCategory.δ 1)
      (StdSimplex.homeomorphI.symm t)) = _
    rw [← toTopObjMk_map, ← SimplicialObject.δ_def, h.d₁, Edge.toTopPath_apply]
  exact ⟨((H.map F).pathCast hx₀ hx₂).cast htrans hdiag⟩

end EdgePath

section FundamentalGroupoid

/-- The canonical functor from the simplicial fundamental groupoid of `X` to the topological
fundamental groupoid of its geometric realization `|X|`, sending a vertex `x` to `toTopPoint x`
and an edge `e` to the path homotopy class `Path.Homotopic.Quotient.mk e.toTopPath`. -/
@[expose, implicit_reducible]
noncomputable def toTopFundamentalGroupoid (X : SSet.{u}) :
    SSet.FundamentalGroupoid X ⥤ _root_.FundamentalGroupoid |X| :=
  FundamentalGroupoid.desc (fun x ↦ .mk (toTopPoint x))
    (fun e ↦ _root_.FundamentalGroupoid.fromPath (.mk e.toTopPath))
    (fun h ↦ Quotient.sound h.homotopic_toTopPath)

@[simp]
lemma toTopFundamentalGroupoid_obj_mk (X : SSet.{u}) (x : X _⦋0⦌) :
    (toTopFundamentalGroupoid X).obj (.mk x) = .mk (toTopPoint x) :=
  (rfl)

@[simp]
lemma toTopFundamentalGroupoid_map_homMk (X : SSet.{u}) {x y : X _⦋0⦌} (e : X.Edge x y) :
    (toTopFundamentalGroupoid X).map (FundamentalGroupoid.homMk e) =
      _root_.FundamentalGroupoid.fromPath (.mk e.toTopPath) :=
  FundamentalGroupoid.desc_map_homMk _ _ (fun h ↦ Quotient.sound h.homotopic_toTopPath) e

/-- Naturality isomorphism comparing `toTopFundamentalGroupoid` along a simplicial map `f : X ⟶ Y`
with the topological fundamental groupoid functor induced by `toTop.map f`. -/
noncomputable def mapFundamentalGroupoidToTopIso {X Y : SSet.{u}} (f : X ⟶ Y) :
    mapFundamentalGroupoid f ⋙ toTopFundamentalGroupoid Y ≅
      toTopFundamentalGroupoid X ⋙ _root_.FundamentalGroupoid.map (toTop.map f).hom := by
  have hobj (x : X _⦋0⦌) :
      (mapFundamentalGroupoid f ⋙ toTopFundamentalGroupoid Y).obj (.mk x) =
        (toTopFundamentalGroupoid X ⋙ _root_.FundamentalGroupoid.map (toTop.map f).hom).obj
          (.mk x) :=
    congrArg _root_.FundamentalGroupoid.mk (toTop_map_toTopPoint f x).symm
  refine FundamentalGroupoid.natIsoMk (fun x ↦ eqToIso (hobj x)) fun {x y} e ↦ ?_
  rw [← cancel_mono (eqToIso (hobj y)).inv, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  dsimp only [Functor.comp_map]
  rw [mapFundamentalGroupoid_map_homMk, toTopFundamentalGroupoid_map_homMk,
    toTopFundamentalGroupoid_map_homMk, Category.assoc]
  change _root_.FundamentalGroupoid.fromPath (.mk (e.map f).toTopPath) =
    eqToHom (congrArg _root_.FundamentalGroupoid.mk (toTop_map_toTopPoint f x).symm) ≫
      _root_.Path.Homotopic.Quotient.map (.mk e.toTopPath) (toTop.map f).hom ≫
      eqToHom (congrArg _root_.FundamentalGroupoid.mk (toTop_map_toTopPoint f y))
  rw [_root_.FundamentalGroupoid.conj_eqToHom (toTop_map_toTopPoint f x).symm
      (toTop_map_toTopPoint f y).symm,
    ← _root_.Path.Homotopic.Quotient.mk_map]
  exact Quotient.sound (by rw [e.toTopPath_map])

end FundamentalGroupoid

end SSet
