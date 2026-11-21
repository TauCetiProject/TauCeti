/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.AlgebraicTopology.SimplicialSet.Nonempty
public import Mathlib.Topology.Category.TopCat.ULift
public import Mathlib.Topology.Homotopy.Contractible
public import TauCeti.AlgebraicTopology.SimplicialSet.Op
public import TauCeti.AlgebraicTopology.SimplicialSet.PrismRealization
public import TauCeti.AlgebraicTopology.SimplicialSet.Realization.PiZero
public import TauCeti.Geometry.Convex.ConvexSpace.ContractibleSpaceStdSimplex
public import TauCeti.Geometry.Convex.ConvexSpace.Defs

/-!
# Basic properties and natural isomorphisms of geometric realization

The geometric realization `|X|` of a simplicial set `X : SSet.{u}` is built by gluing a standard
topological `n`-simplex for every `x : X _⦋n⦌` via `SSet.toTopObjMk x w` (which equals
`SSet.toTopPoint x` on `0`-simplices and is jointly surjective via `SSet.exists_toTopObjMk`).
Continuous maps out of `|X|` are constructed via `SSet.descToTop` and compared via
`SSet.toTop_hom_ext`.

To support classifying spaces of categories and their fundamental groupoids, this file establishes:
* emptiness, nonemptiness, subsingleton, path-connectedness, and contractibility criteria for `|X|`,
  together with constant-map realization (`toTop_map_const`);
* separation of `0`- and `1`-simplices via piecewise-linear test functions (`toTopPoint_injective`,
  `toTopObjMk_one_injective`);
* edge paths `Edge.toTopPath` and path homotopies from `2`-simplices
  (`Edge.CompStruct.toTopPath_homotopic`);
* natural isomorphisms commuting `SSet.toTop` with discrete sets (`constCompToTopIso`), universe
  lifts (`uliftFunctorCompToTopIso`, `toTopUliftHomeomorph`), and simplicial opposites
  (`opFunctorCompToTopIso`, `toTopOpHomeomorph`).

## References

* J. Milnor, *The geometric realization of a semi-simplicial complex*, Ann. of Math. 65 (1957).
* P. G. Goerss and J. F. Jardine, *Simplicial Homotopy Theory*, Birkhäuser, 1999, §§I.2, I.11.
-/

public section

open CategoryTheory Limits Opposite Simplicial Convexity
universe v u
namespace SSet
variable {X Y : SSet.{u}}

/-! ### Vertices, emptiness, connectedness, and constant maps -/

lemma toTop_map_yonedaEquiv_symm_toTopHomeo_symm {n : ℕ} (x : X _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    toTop.map (yonedaEquiv.symm x) ((⦋n⦌.toTopHomeo).symm w) = toTopObjMk x w := by
  rw [toTopObjMk_def]
  exact (ConcreteCategory.congr_hom (sSetTopAdj_unit_app_app_down X (op ⦋n⦌) x) (ULift.up w)).symm
lemma toTopObjMk_eq_toTopPoint (x : X _⦋0⦌) (w : StdSimplex ℝ (Fin 1)) :
    toTopObjMk x w = toTopPoint x := by
  rw [← toTop_map_yonedaEquiv_symm_toTopHomeo_symm,
    Subsingleton.elim ((⦋0⦌.toTopHomeo).symm w) (toTopPoint (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌))),
    toTop_map_toTopPoint, yonedaEquiv_symm_app_objEquiv_symm, op_id,
    CategoryTheory.Functor.map_id, types_id_apply]
lemma toTopObjMk_single {n : ℕ} (x : X _⦋n⦌) (i : Fin (n + 1)) :
    toTopObjMk x (StdSimplex.single i) = toTopPoint (X.map (⦋0⦌.const ⦋n⦌ i).op x) := by
  rw [← toTopObjMk_eq_toTopPoint _ (StdSimplex.single 0), toTopObjMk_map, StdSimplex.map_single]
  rfl
/-- Every point of `|X|` lies in the image of `SSet.toTopObjMk` for some simplex of `X`. -/
lemma exists_toTopObjMk (z : |X|) :
    ∃ (n : ℕ) (x : X _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))), toTopObjMk x w = z := by
  obtain ⟨⟨m, _, f⟩, y, hy⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (toTop ⋙ forget TopCat) (denseAtUliftYoneda X)) z
  dsimp at y hy; rw [Category.id_comp] at hy
  induction m using SimplexCategory.rec with | _ n =>
  let f' : Δ[n] ⟶ X := f; let y' : |Δ[n]| := y
  refine ⟨n, yonedaEquiv f', ⦋n⦌.toTopHomeo y', ?_⟩
  rwa [← toTop_map_yonedaEquiv_symm_toTopHomeo_symm, Equiv.symm_apply_apply,
    Homeomorph.symm_apply_apply]
@[simp] lemma toTop_map_const_apply (y : Y _⦋0⦌) (z : |X|) :
    toTop.map (SSet.const y) z = toTopPoint y := by
  obtain ⟨n, x, w, rfl⟩ := exists_toTopObjMk z
  rw [toTop_map_toTopObjMk, const_app, TypeCat.ofHom_apply, toTopObjMk_map,
    toTopObjMk_eq_toTopPoint]
lemma toTop_map_const (y : Y _⦋0⦌) :
    toTop.map (SSet.const y : X ⟶ Y) = TopCat.const (toTopPoint y) :=
  TopCat.ext (toTop_map_const_apply y)

/-- The geometric realization `|X|` is empty if and only if `X` has no `0`-simplices. -/
@[simp] theorem isEmpty_toTop_iff (X : SSet.{u}) : IsEmpty |X| ↔ IsEmpty (X _⦋0⦌) :=
  ⟨fun h ↦ ⟨fun x ↦ h.false (toTopPoint x)⟩, fun h ↦ ⟨fun z ↦
    let ⟨x, _⟩ := π₀.mk_surjective (X.π₀EquivZerothHomotopy.symm (.mk z)); h.false x⟩⟩
instance [IsEmpty (X _⦋0⦌)] : IsEmpty |X| := (isEmpty_toTop_iff X).2 inferInstance
/-- The geometric realization `|X|` is nonempty if and only if `X` is nonempty. -/
@[simp] theorem nonempty_toTop_iff (X : SSet.{u}) : Nonempty |X| ↔ X.Nonempty := by
  rw [← not_isEmpty_iff, isEmpty_toTop_iff, not_isEmpty_iff]
instance [X.Nonempty] : Nonempty |X| := (nonempty_toTop_iff X).2 inferInstance
instance [∀ n, Subsingleton (X.obj n)] : Subsingleton |X| where
  allEq z₁ z₂ := by
    obtain ⟨n₁, x₁, w₁, rfl⟩ := exists_toTopObjMk z₁
    obtain ⟨n₂, x₂, w₂, rfl⟩ := exists_toTopObjMk z₂
    have h {n : ℕ} (x : X _⦋n⦌) (w) : toTopObjMk x w = toTopPoint (X.map (⦋0⦌.const ⦋n⦌ 0).op x) :=
      (congrArg (toTopObjMk · w) (Subsingleton.elim x (X.map (⦋n⦌.const ⦋0⦌ 0).op _))).trans
        ((toTopObjMk_map _ _ w).trans (toTopObjMk_eq_toTopPoint _ _))
    rw [h x₁ w₁, h x₂ w₂]; exact congrArg toTopPoint (Subsingleton.elim _ _)
lemma exists_joined_toTopPoint (z : |X|) : ∃ x : X _⦋0⦌, Joined z (toTopPoint x) := by
  obtain ⟨x, hx⟩ := π₀.mk_surjective (X.π₀EquivZerothHomotopy.symm (.mk z))
  have hm := congrArg X.π₀EquivZerothHomotopy hx
  rw [π₀EquivZerothHomotopy_mk, Equiv.apply_symm_apply] at hm
  exact ⟨x, Quotient.exact hm.symm⟩
/-- The geometric realization `|X|` is path-connected if and only if `X` is connected. -/
@[simp] theorem pathConnectedSpace_toTop_iff (X : SSet.{u}) :
    PathConnectedSpace |X| ↔ X.IsConnected := by
  rw [pathConnectedSpace_iff_zerothHomotopy, and_comm, ← unique_iff_subsingleton_and_nonempty,
    SSet.isConnected_iff_nonempty_unique]
  exact ⟨fun ⟨_⟩ ↦ ⟨X.π₀EquivZerothHomotopy.unique⟩,
    fun ⟨_⟩ ↦ ⟨X.π₀EquivZerothHomotopy.symm.unique⟩⟩
instance [X.IsConnected] : PathConnectedSpace |X| :=
  (pathConnectedSpace_toTop_iff X).2 inferInstance

private lemma toTop_map_const_hom (x : X _⦋0⦌) :
    (toTop.map (SSet.const x : X ⟶ X)).hom = ContinuousMap.const |X| (toTopPoint x) :=
  ContinuousMap.ext (toTop_map_const_apply x)
private lemma contractibleSpace_toTop_of_topHomotopy (x : X _⦋0⦌)
    (H : ContinuousMap.Homotopy (toTop.map (𝟙 X)).hom
      (toTop.map (SSet.const x : X ⟶ X)).hom) : ContractibleSpace |X| := by
  rw [contractible_iff_id_nullhomotopic]
  rw [toTop_map_const_hom, CategoryTheory.Functor.map_id, TopCat.hom_id] at H
  exact ⟨toTopPoint x, ⟨H⟩⟩
/-- If `SSet.const x` is simplicially homotopic to `𝟙 X`, then `|X|` is contractible. -/
lemma contractibleSpace_toTop_of_homotopy {x : X _⦋0⦌}
    (H : SSet.Homotopy (SSet.const x) (𝟙 X)) : ContractibleSpace |X| :=
  contractibleSpace_toTop_of_topHomotopy x H.toTop.symm
/-- If `𝟙 X` is simplicially homotopic to `SSet.const x`, then `|X|` is contractible. -/
lemma contractibleSpace_toTop_of_homotopy_id_const {x : X _⦋0⦌}
    (H : SSet.Homotopy (𝟙 X) (SSet.const x)) : ContractibleSpace |X| :=
  contractibleSpace_toTop_of_topHomotopy x H.toTop

/-! ### Separation of vertices and `1`-simplices -/

/-- Distinct vertices of a simplicial set map to distinct points of its geometric realization. -/
theorem toTopPoint_injective (X : SSet.{u}) : Function.Injective (toTopPoint (X := X)) := by
  classical
  intro x₁ x₂ h
  let g : X _⦋0⦌ → ℝ := fun y ↦ if y = x₁ then 1 else 0
  let F : |X| ⟶ TopCat.of (ULift.{u} ℝ) := descToTop
    (fun n σ w ↦ ULift.up (∑ i, w.weights i * g (X.map (⦋0⦌.const ⦋n⦌ i).op σ)))
    (fun _ _ ↦ by fun_prop) fun _ _ θ σ w ↦ congrArg ULift.up <| by
      have hc (j) : ⦋0⦌.const _ j ≫ θ = ⦋0⦌.const _ (θ j) := by ext k; fin_cases k; rfl
      simp_rw [← Functor.map_comp_apply, ← op_comp, hc, StdSimplex.sum_weights_map_mul]
  have eval (x : X _⦋0⦌) : (F (toTopPoint x)).down = g x := by
    have hc₀ : ⦋0⦌.const ⦋0⦌ 0 = 𝟙 ⦋0⦌ := by ext k; fin_cases k; rfl
    rw [← toTopObjMk_eq_toTopPoint x (StdSimplex.single 0)]
    exact (congrArg ULift.down (descToTop_toTopObjMk _ _ _ x _)).trans (by simp [hc₀])
  have h12 : g x₁ = g x₂ := by rw [← eval x₁, ← eval x₂, h]
  by_contra hne; simp [g, Ne.symm hne] at h12
@[simp] lemma toTopPoint_inj {x₁ x₂ : X _⦋0⦌} : toTopPoint x₁ = toTopPoint x₂ ↔ x₁ = x₂ :=
  (toTopPoint_injective X).eq_iff

private lemma edgeExtension_diag {h : X _⦋1⦌ → ℝ} (hh : ∀ x : X _⦋0⦌, h (X.σ 0 x) = 0)
    {n : ℕ} (σ : X _⦋n⦌) (p : Fin (n + 1)) : h (X.map (⦋1⦌.const ⦋n⦌ p).op σ) = 0 := by
  rw [SimplexCategory.const_fac_thru_zero,
    ← SimplexCategory.eq_const_to_zero (SimplexCategory.σ 0), op_comp, Functor.map_comp_apply]
  exact hh _
private lemma mkOfLe_eq_const {n : ℕ} {i j : Fin (n + 1)} (h : i ≤ j) (hij : i = j) :
    SimplexCategory.mkOfLe i j h = ⦋1⦌.const ⦋n⦌ i := by
  subst hij; exact SimplexCategory.mkOfLe_refl i
private noncomputable def edgeExtension (h : X _⦋1⦌ → ℝ) (hh : ∀ x : X _⦋0⦌, h (X.σ 0 x) = 0) :
    |X| ⟶ TopCat.of (ULift.{u} ℝ) :=
  descToTop (fun n σ w ↦ ULift.up (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), w.weights i * w.weights j *
      if hij : i ≤ j then h (X.map (SimplexCategory.mkOfLe i j hij).op σ) else 0))
    (fun _ _ ↦ by fun_prop) fun m n θ σ w ↦ congrArg ULift.up <| by
      let c (p q : Fin (n + 1)) : ℝ :=
        if hpq : p ≤ q then h (X.map (SimplexCategory.mkOfLe p q hpq).op σ) else 0
      have hcoeff (a b : Fin (m + 1)) :
          (if hab : a ≤ b then h (X.map (SimplexCategory.mkOfLe a b hab).op (X.map θ.op σ))
            else 0) = c (θ a) (θ b) := by
        by_cases hab : a ≤ b
        · have hθ : θ a ≤ θ b := θ.toOrderHom.monotone hab
          have hcomp : SimplexCategory.mkOfLe a b hab ≫ θ =
              SimplexCategory.mkOfLe (θ a) (θ b) hθ := by ext k; fin_cases k <;> rfl
          simp only [c, hab, hθ, ↓reduceDIte, ← Functor.map_comp_apply, ← op_comp, hcomp]
        · simp only [c, hab, ↓reduceDIte]; split_ifs with hθ; swap; · rfl
          have heq : θ a = θ b := le_antisymm hθ (θ.toOrderHom.monotone (le_of_not_ge hab))
          rw [mkOfLe_eq_const hθ heq, edgeExtension_diag hh]
      simp_rw [hcoeff, mul_assoc, ← Finset.mul_sum]
      exact (Finset.sum_congr rfl fun a _ ↦
        congrArg (w.weights a * ·) (StdSimplex.sum_weights_map_mul _ _ _).symm).trans
        (StdSimplex.sum_weights_map_mul θ w fun p ↦ ∑ q, (w.map θ).weights q * c p q).symm

@[simp] lemma toTopObjMk_single_zero (e : X _⦋1⦌) :
    toTopObjMk e (StdSimplex.single 0) = toTopPoint (X.δ 1 e) := by
  rw [toTopObjMk_single, ← SimplexCategory.δ_one_eq_const]; rfl
@[simp] lemma toTopObjMk_single_one (e : X _⦋1⦌) :
    toTopObjMk e (StdSimplex.single 1) = toTopPoint (X.δ 0 e) := by
  rw [toTopObjMk_single, ← SimplexCategory.δ_zero_eq_const]; rfl

private lemma edgeExtension_midpoint {h : X _⦋1⦌ → ℝ} (hh : ∀ x : X _⦋0⦌, h (X.σ 0 x) = 0)
    (e : X _⦋1⦌) : (edgeExtension h hh (toTopObjMk e
      (StdSimplex.homeomorphI.symm ⟨1 / 2, by norm_num, by norm_num⟩))).down = h e / 4 := by
  have hid : SimplexCategory.mkOfLe (0 : Fin 2) 1 (by decide) = 𝟙 ⦋1⦌ := by
    ext k; fin_cases k <;> rfl
  refine (congrArg ULift.down (descToTop_toTopObjMk _ _ _ e _)).trans ?_
  simp [edgeExtension_diag hh, hid]; ring

/-- Distinct `1`-simplices of `X` determine distinct parametrized simplices in `|X|`. -/
theorem toTopObjMk_one_injective (X : SSet.{u}) :
    Function.Injective (fun e : X _⦋1⦌ ↦ toTopObjMk e) := by
  classical
  have sep {e₁ e₂ : X _⦋1⦌} (he₁ : e₁ ∉ Set.range (X.σ 0))
      (heq : toTopObjMk e₁ = toTopObjMk e₂) : e₁ = e₂ := by
    let h : X _⦋1⦌ → ℝ := fun e ↦ if e = e₁ then 1 else 0
    have hh (x : X _⦋0⦌) : h (X.σ 0 x) = 0 := ite_eq_right_iff.2 fun hx ↦ absurd ⟨x, hx⟩ he₁
    have hm := edgeExtension_midpoint hh e₁
    rw [heq, edgeExtension_midpoint hh e₂] at hm; by_contra hne; simp [h, Ne.symm hne] at hm
  intro e₁ e₂ heq
  by_cases h₁ : e₁ ∈ Set.range (X.σ 0)
  · by_cases h₂ : e₂ ∈ Set.range (X.σ 0); swap; · exact (sep h₂ heq.symm).symm
    obtain ⟨x₁, rfl⟩ := h₁; obtain ⟨x₂, rfl⟩ := h₂
    have hv : toTopObjMk (X.σ 0 x₁) (StdSimplex.single 1) =
        toTopObjMk (X.σ 0 x₂) (StdSimplex.single 1) := congrFun heq (StdSimplex.single 1)
    rw [toTopObjMk_single_one, toTopObjMk_single_one, toTopPoint_inj,
      ← Fin.castSucc_zero, δ_comp_σ_self_apply, δ_comp_σ_self_apply] at hv
    exact congrArg _ hv
  · exact sep h₁ heq

/-! ### Edge paths and `2`-simplices in geometric realization -/

namespace Edge
open unitInterval
variable {x₀ x₁ x₂ : X _⦋0⦌}
/-- The path in `|X|` from `toTopPoint x₀` to `toTopPoint x₁` traced by `e : X.Edge x₀ x₁`. -/
noncomputable def toTopPath (e : X.Edge x₀ x₁) : _root_.Path (toTopPoint x₀) (toTopPoint x₁) where
  toContinuousMap := (⟨toTopObjMk e.edge, continuous_toTopObjMk e.edge⟩ : C(_, |X|)).comp
    (StdSimplex.homeomorphI.symm : C(I, StdSimplex ℝ (Fin 2)))
  source' := by simp [e.src_eq]
  target' := by simp [e.tgt_eq]
lemma toTopPath_apply (e : X.Edge x₀ x₁) (t : I) :
    e.toTopPath t = toTopObjMk e.edge (StdSimplex.homeomorphI.symm t) := (rfl)
@[simp] lemma toTopPath_id (x : X _⦋0⦌) :
    (Edge.id x).toTopPath = _root_.Path.refl (toTopPoint x) := by
  ext t; rw [toTopPath_apply, Edge.id_edge, SimplicialObject.σ, toTopObjMk_map,
    toTopObjMk_eq_toTopPoint, _root_.Path.refl_apply]
@[simp] lemma toTop_map_toTopPath_apply (f : X ⟶ Y) (e : X.Edge x₀ x₁) (t : I) :
    toTop.map f (e.toTopPath t) = (e.map f).toTopPath t := by
  rw [toTopPath_apply, toTopPath_apply, toTop_map_toTopObjMk, Edge.map_edge]

private noncomputable def stdSimplex₂FacePath {a b : Fin 3} (j : Fin 3)
    (ha : j.succAbove 0 = a) (hb : j.succAbove 1 = b) :
    _root_.Path (StdSimplex.single (R := ℝ) a) (StdSimplex.single b) where
  toContinuousMap :=
    (⟨StdSimplex.map j.succAbove, StdSimplex.continuous_map ℝ j.succAbove⟩ : C(_, _)).comp
      (StdSimplex.homeomorphI.symm : C(I, StdSimplex ℝ (Fin 2)))
  source' := by simp [StdSimplex.map_single, ha]
  target' := by simp [StdSimplex.map_single, hb]
/-- A `2`-simplex `CompStruct e₀₁ e₁₂ e₀₂` in `X` witnesses a homotopy in `|X|` between the edge
path of `e₀₂` and the concatenation of the edge paths of `e₀₁` and `e₁₂`. -/
theorem CompStruct.toTopPath_homotopic {e₀₁ : X.Edge x₀ x₁} {e₁₂ : X.Edge x₁ x₂}
    {e₀₂ : X.Edge x₀ x₂} (h : CompStruct e₀₁ e₁₂ e₀₂) :
    e₀₂.toTopPath.Homotopic (e₀₁.toTopPath.trans e₁₂.toTopPath) := by
  let σMap : C(StdSimplex ℝ (Fin 3), |X|) := ⟨toTopObjMk h.simplex, continuous_toTopObjMk h.simplex⟩
  have hmap := (SimplyConnectedSpace.paths_homotopic
    (stdSimplex₂FacePath (a := 0) (b := 2) 1 (by decide) (by decide))
    ((stdSimplex₂FacePath (a := 0) (b := 1) 2 (by decide) (by decide)).trans
      (stdSimplex₂FacePath (a := 1) (b := 2) 0 (by decide) (by decide)))).map σMap
  rw [_root_.Path.map_trans] at hmap
  have hpt {y₀ y₁ : X _⦋0⦌} {a b : Fin 3} (j : Fin 3) (ha : j.succAbove 0 = a)
      (hb : j.succAbove 1 = b) (e : X.Edge y₀ y₁) (hd : X.δ j h.simplex = e.edge) (t : I) :
      ((stdSimplex₂FacePath j ha hb).map σMap.continuous) t = e.toTopPath t := by
    rw [_root_.Path.map_coe, Function.comp_apply]
    exact (congrArg (toTopObjMk h.simplex)
      (congrArg (StdSimplex.map · (StdSimplex.homeomorphI.symm t))
        (SimplexCategory.coe_δ j).symm)).trans <| by
      rw [← toTopObjMk_map, ← SimplicialObject.δ, hd, toTopPath_apply]
  have h02 := hpt (a := 0) (b := 2) 1 (by decide) (by decide) e₀₂ h.d₁
  convert hmap.pathCast
    ((e₀₂.toTopPath.source.symm.trans (h02 0).symm).trans (_root_.Path.source _))
    ((e₀₂.toTopPath.target.symm.trans (h02 1).symm).trans (_root_.Path.target _)) using 1
  · exact (_root_.Path.ext (funext h02)).symm
  · ext t; simp only [_root_.Path.cast_coe, _root_.Path.trans_apply]; split_ifs with ht'
    · exact (hpt 2 (by decide) (by decide) e₀₁ h.d₂ _).symm
    · exact (hpt 0 (by decide) (by decide) e₁₂ h.d₀ _).symm
end Edge

/-! ### Realization of discrete simplicial sets -/

/-- The natural isomorphism `|(Functor.const _).obj ι| ≅ TopCat.discrete.obj ι` identifying the
geometric realization of the discrete simplicial set on `ι` with the discrete space on `ι`. -/
noncomputable def constCompToTopIso :
    (Functor.const SimplexCategoryᵒᵖ : Type u ⥤ SSet.{u}) ⋙ SSet.toTop.{u} ≅ TopCat.discrete.{u} :=
  (NatIso.ofComponents (fun (ι : Type u) ↦
    { hom := ConcreteCategory.ofHom ⟨fun x ↦
        toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj ι)
          (x : ((Functor.const SimplexCategoryᵒᵖ).obj ι) _⦋0⦌), continuous_of_discreteTopology⟩
      inv := descToTop (fun _ i _ ↦ (i : TopCat.discrete.obj ι)) (fun _ _ ↦ continuous_const)
        fun _ _ _ _ _ ↦ rfl
      hom_inv_id := by
        ext x; let j : ((Functor.const SimplexCategoryᵒᵖ : Type u ⥤ SSet.{u}).obj ι) _⦋0⦌ := x
        exact (congrArg _ (toTopObjMk_eq_toTopPoint j (StdSimplex.single 0)).symm).trans
          (descToTop_toTopObjMk _ _ _ j _)
      inv_hom_id := toTop_hom_ext fun n i w ↦
        (congrArg _ (descToTop_toTopObjMk _ _ _ i w)).trans
          ((toTopObjMk_eq_toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj ι) i _).symm.trans
            (toTopObjMk_map (X := (Functor.const SimplexCategoryᵒᵖ).obj ι) (⦋n⦌.const ⦋0⦌ 0) i
              w).symm) })
    fun f ↦ by
      ext x; exact (toTop_map_toTopPoint ((Functor.const SimplexCategoryᵒᵖ).map f)
        (x : ((Functor.const SimplexCategoryᵒᵖ).obj _) _⦋0⦌)).symm).symm
@[simp] lemma constCompToTopIso_hom_app_toTopObjMk (ι : Type u) {n : ℕ}
    (i : ((Functor.const SimplexCategoryᵒᵖ : Type u ⥤ SSet.{u}).obj ι) _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    dsimp% (constCompToTopIso.hom.app ι) (toTopObjMk i w) = (i : TopCat.discrete.obj ι) :=
  descToTop_toTopObjMk _ _ _ i w
@[simp] lemma constCompToTopIso_inv_app_apply (ι : Type u) (i : ι) :
    dsimp% (constCompToTopIso.inv.app ι) (i : TopCat.discrete.obj ι) =
      toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj ι) i := (rfl)
@[simp] lemma constCompToTopIso_hom_app_toTopPoint (ι : Type u) (i : ι) :
    dsimp% (constCompToTopIso.hom.app ι)
        (toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj ι) i) =
      (i : TopCat.discrete.obj ι) := by
  simpa using Iso.inv_hom_id_app_apply constCompToTopIso ι (i : TopCat.discrete.obj ι)

/-! ### Realization of universe lifts -/

private noncomputable def uliftToTopCoconeApp (X : SSet.{u})
    (j : CostructuredArrow uliftYoneda.{u} X) :
    TopCat.uliftFunctor.{v, u}.obj |uliftYoneda.{u}.obj j.left| ⟶
      |SSet.uliftFunctor.{v, u}.obj X| :=
  ConcreteCategory.ofHom
    ⟨fun z ↦ toTopObjMk (X := SSet.uliftFunctor.{v, u}.obj X) (n := j.left.len)
        (ULift.up (CategoryTheory.uliftYonedaEquiv j.hom))
        (SimplexCategory.toTopHomeo.{u} j.left
          (|uliftYoneda.{u}.obj j.left|.uliftFunctorObjHomeo.{v, u}.symm z)),
      (continuous_toTopObjMk _).comp ((SimplexCategory.toTopHomeo.{u} j.left).continuous.comp
        |uliftYoneda.{u}.obj j.left|.uliftFunctorObjHomeo.{v, u}.symm.continuous)⟩
private lemma uliftToTopCoconeApp_apply (X : SSet.{u}) (j : CostructuredArrow uliftYoneda.{u} X)
    (y : |uliftYoneda.{u}.obj j.left|) :
    uliftToTopCoconeApp.{v, u} X j (|uliftYoneda.{u}.obj j.left|.uliftFunctorObjHomeo y) =
      toTopObjMk (X := SSet.uliftFunctor.{v, u}.obj X) (n := j.left.len)
        (ULift.up (CategoryTheory.uliftYonedaEquiv j.hom))
        (SimplexCategory.toTopHomeo.{u} j.left y) :=
  congrArg (toTopObjMk (X := SSet.uliftFunctor.{v, u}.obj X) (n := j.left.len) _)
    (congrArg (SimplexCategory.toTopHomeo.{u} j.left) (Homeomorph.symm_apply_apply _ y))
private noncomputable def uliftToTopCocone (X : SSet.{u}) :
    Cocone (CostructuredArrow.proj uliftYoneda.{u} X ⋙
      uliftYoneda.{u} ⋙ SSet.toTop.{u} ⋙ TopCat.uliftFunctor.{v, u}) where
  pt := |SSet.uliftFunctor.{v, u}.obj X|
  ι :=
    { app j := uliftToTopCoconeApp.{v, u} X j
      naturality j₁ j₂ g := by
        obtain ⟨l₁, ⟨⟩, h₁⟩ := j₁; obtain ⟨l₂, ⟨⟩, h₂⟩ := j₂
        induction l₁ using SimplexCategory.rec with | _ m
        induction l₂ using SimplexCategory.rec with | _ n
        ext z; obtain ⟨y, rfl⟩ := |uliftYoneda.{u}.obj ⦋m⦌|.uliftFunctorObjHomeo.surjective z
        have hyon := CategoryTheory.uliftYonedaEquiv_naturality h₂ g.left.op
        rw [Quiver.Hom.unop_op, CostructuredArrow.w g] at hyon
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Functor.comp_obj,
          Functor.comp_map, CostructuredArrow.proj_obj, CostructuredArrow.proj_map,
          ConcreteCategory.comp_apply, CategoryTheory.id_apply,
          TopCat.uliftFunctorObjHomeo_naturality_apply]
        rw [uliftToTopCoconeApp_apply, uliftToTopCoconeApp_apply]
        exact (congrArg (toTopObjMk (X := SSet.uliftFunctor.{v, u}.obj X) _)
            (SimplexCategory.toTopHomeo_naturality_apply.{u} g.left y)).trans <|
          (toTopObjMk_map (X := SSet.uliftFunctor.{v, u}.obj X) g.left _ _).symm.trans
            (congrArg (toTopObjMk · _) (congrArg ULift.up hyon)) }
private noncomputable def uliftToTopHom (X : SSet.{u}) :
    |SSet.uliftFunctor.{v, u}.obj X| ⟶ TopCat.uliftFunctor.{v, u}.obj |X| :=
  descToTop (fun _ x w ↦ |X|.uliftFunctorObjHomeo (toTopObjMk x.down w))
    (fun _ x ↦ |X|.uliftFunctorObjHomeo.continuous.comp (continuous_toTopObjMk x.down))
    fun _ _ θ x w ↦ congrArg |X|.uliftFunctorObjHomeo (toTopObjMk_map θ x.down w)
private lemma uliftToTopHom_toTopObjMk (X : SSet.{u}) {n : ℕ}
    (x : (SSet.uliftFunctor.{v, u}.obj X) _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
    uliftToTopHom.{v, u} X (toTopObjMk x w) = |X|.uliftFunctorObjHomeo (toTopObjMk x.down w) :=
  descToTop_toTopObjMk _ _ _ x w
private noncomputable def uliftToTopInv (X : SSet.{u}) :
    TopCat.uliftFunctor.{v, u}.obj |X| ⟶ |SSet.uliftFunctor.{v, u}.obj X| :=
  (isColimitOfPreserves (SSet.toTop.{u} ⋙ TopCat.uliftFunctor.{v, u})
    (denseAtUliftYoneda X)).desc (uliftToTopCocone.{v, u} X)
private lemma uliftToTopInv_apply (X : SSet.{u}) {n : ℕ} (x : X _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    uliftToTopInv.{v, u} X (|X|.uliftFunctorObjHomeo (toTopObjMk x w)) =
      toTopObjMk (X := SSet.uliftFunctor.{v, u}.obj X) (ULift.up x) w := by
  let f : uliftYoneda.{u}.obj ⦋n⦌ ⟶ X := CategoryTheory.uliftYonedaEquiv.symm x
  let j := CostructuredArrow.mk f
  let y : |uliftYoneda.{u}.obj j.left| := (SimplexCategory.toTopHomeo.{u} ⦋n⦌).symm w
  have hfac := ConcreteCategory.congr_hom ((isColimitOfPreserves
    (SSet.toTop.{u} ⋙ TopCat.uliftFunctor.{v, u}) (denseAtUliftYoneda X)).fac
    (uliftToTopCocone.{v, u} X) j) (|uliftYoneda.{u}.obj j.left|.uliftFunctorObjHomeo y)
  have hlhs : ((toTop.{u} ⋙ TopCat.uliftFunctor.{v, u}).mapCocone
      ((Functor.LeftExtension.mk _ uliftYoneda.{u}.rightUnitor.inv).coconeAt X)).ι.app j
      (|uliftYoneda.{u}.obj j.left|.uliftFunctorObjHomeo y) =
      |X|.uliftFunctorObjHomeo (toTopObjMk x w) :=
    congrArg |X|.uliftFunctorObjHomeo (toTop_map_yonedaEquiv_symm_toTopHomeo_symm x w)
  have hrhs : (uliftToTopCocone.{v, u} X).ι.app j
      (|uliftYoneda.{u}.obj j.left|.uliftFunctorObjHomeo y) =
      toTopObjMk (X := SSet.uliftFunctor.{v, u}.obj X) (ULift.up x) w :=
    (uliftToTopCoconeApp_apply.{v, u} X j y).trans (by simp [j, f, y])
  rw [← hlhs, ← hrhs]; exact hfac

/-- Geometric realization commutes up to natural isomorphism with universe lifting of simplicial
sets and topological spaces. -/
noncomputable def uliftFunctorCompToTopIso :
    SSet.uliftFunctor.{v, u} ⋙ SSet.toTop ≅ SSet.toTop ⋙ TopCat.uliftFunctor.{v, u} :=
  NatIso.ofComponents (fun X ↦
    { hom := uliftToTopHom.{v, u} X, inv := uliftToTopInv.{v, u} X
      hom_inv_id := toTop_hom_ext fun _ x w ↦ by
        rw [ConcreteCategory.comp_apply, uliftToTopHom_toTopObjMk, uliftToTopInv_apply]; rfl
      inv_hom_id := by
        ext z; obtain ⟨y, rfl⟩ := |X|.uliftFunctorObjHomeo.surjective z
        obtain ⟨n, x, w, rfl⟩ := exists_toTopObjMk y
        rw [ConcreteCategory.comp_apply, uliftToTopInv_apply]
        exact uliftToTopHom_toTopObjMk X (ULift.up x : (SSet.uliftFunctor.{v, u}.obj X) _⦋n⦌) w })
    fun f ↦ toTop_hom_ext fun _ _ _ ↦ by
      simp only [Functor.comp_obj, Functor.comp_map, ConcreteCategory.comp_apply,
        toTop_map_toTopObjMk, uliftToTopHom_toTopObjMk,
        TopCat.uliftFunctorObjHomeo_naturality_apply]; rfl

section ULiftLemmas
variable (X : SSet.{u})
@[simp] lemma uliftFunctorCompToTopIso_hom_app_toTopObjMk {n : ℕ}
    (x : (SSet.uliftFunctor.{v, u}.obj X) _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
    dsimp% (uliftFunctorCompToTopIso.{v, u}.hom.app X) (toTopObjMk x w) =
      |X|.uliftFunctorObjHomeo (toTopObjMk x.down w) := uliftToTopHom_toTopObjMk X x w
@[simp] lemma uliftFunctorCompToTopIso_inv_app_toTopObjMk {n : ℕ} (x : X _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    dsimp% (uliftFunctorCompToTopIso.{v, u}.inv.app X)
        (|X|.uliftFunctorObjHomeo (toTopObjMk x w)) =
      toTopObjMk (X := SSet.uliftFunctor.{v, u}.obj X) (ULift.up x) w := uliftToTopInv_apply X x w
/-- Homeomorphism `|uliftFunctor.obj X| ≃ₜ |X|` comparing the geometric realization of a universe
lift with the geometric realization of `X`. -/
noncomputable def toTopUliftHomeomorph : |SSet.uliftFunctor.{v, u}.obj X| ≃ₜ |X| :=
  (TopCat.homeoOfIso (uliftFunctorCompToTopIso.{v, u}.app X)).trans |X|.uliftFunctorObjHomeo.symm
@[simp] lemma toTopUliftHomeomorph_toTopObjMk {n : ℕ} (x : (SSet.uliftFunctor.{v, u}.obj X) _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    toTopUliftHomeomorph.{v, u} X (toTopObjMk x w) = toTopObjMk x.down w := by
  simp [toTopUliftHomeomorph]
@[simp] lemma toTopUliftHomeomorph_symm_toTopObjMk {n : ℕ} (x : X _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    (toTopUliftHomeomorph.{v, u} X).symm (toTopObjMk x w) =
      toTopObjMk (X := SSet.uliftFunctor.{v, u}.obj X) (ULift.up x) w := by
  simp [toTopUliftHomeomorph]
@[simp] lemma toTopUliftHomeomorph_toTopPoint (x : (SSet.uliftFunctor.{v, u}.obj X) _⦋0⦌) :
    toTopUliftHomeomorph.{v, u} X (toTopPoint x) = toTopPoint x.down := by
  rw [← toTopObjMk_eq_toTopPoint x (StdSimplex.single 0), toTopUliftHomeomorph_toTopObjMk,
    toTopObjMk_eq_toTopPoint]
@[simp] lemma toTopUliftHomeomorph_symm_toTopPoint (x : X _⦋0⦌) :
    (toTopUliftHomeomorph.{v, u} X).symm (toTopPoint x) =
      toTopPoint (X := SSet.uliftFunctor.{v, u}.obj X) (ULift.up x) :=
  let ux : (SSet.uliftFunctor.{v, u}.obj X) _⦋0⦌ := ULift.up x
  (toTopUliftHomeomorph.{v, u} X).injective
    ((Homeomorph.apply_symm_apply _ _).trans (toTopUliftHomeomorph_toTopPoint X ux).symm)
end ULiftLemmas

lemma toTopUliftHomeomorph_naturality_apply (f : X ⟶ Y) (z : |SSet.uliftFunctor.{v, u}.obj X|) :
    toTopUliftHomeomorph.{v, u} Y (toTop.map (SSet.uliftFunctor.map f) z) =
      toTop.map f (toTopUliftHomeomorph.{v, u} X z) := by
  obtain ⟨n, x, w, rfl⟩ := exists_toTopObjMk z
  simp only [toTop_map_toTopObjMk, toTopUliftHomeomorph_toTopObjMk]; rfl

/-! ### Realization of opposite simplicial sets -/

private noncomputable def toTopRevHom (e : ∀ n : ℕ, X _⦋n⦌ → Y _⦋n⦌)
    (he : ∀ (m n : ℕ) (θ : ⦋m⦌ ⟶ ⦋n⦌) (x : X _⦋n⦌),
      e m (X.map θ.op x) = Y.map (SimplexCategory.rev.map θ).op (e n x)) : |X| ⟶ |Y| :=
  descToTop (fun n x w ↦ toTopObjMk (e n x) (StdSimplex.map Fin.rev w))
    (fun n x ↦ (continuous_toTopObjMk (e n x)).comp (StdSimplex.continuous_map ℝ Fin.rev))
    fun m n θ x w ↦ by
      rw [he m n, toTopObjMk_map, StdSimplex.map_map, StdSimplex.map_map]
      exact congrArg (toTopObjMk (e n x)) (congrArg (StdSimplex.map · w) (funext fun i ↦
        (SimplexCategory.rev_map_apply θ i.rev).trans
          (congrArg Fin.rev (congrArg θ (Fin.rev_rev i)))))

/-- The geometric realization of the opposite of a simplicial set is naturally isomorphic to its
geometric realization, acting on each simplex by reversing barycentric coordinates. -/
noncomputable def opFunctorCompToTopIso : SSet.opFunctor.{u} ⋙ SSet.toTop ≅ SSet.toTop :=
  NatIso.ofComponents (fun X ↦
    { hom := toTopRevHom (fun _ y ↦ X.opObjEquiv y) fun _ _ _ _ ↦ by
        rw [X.op_map, Equiv.apply_symm_apply]; rfl
      inv := toTopRevHom (fun _ x ↦ X.opObjEquiv.symm x) fun _ _ _ _ ↦ by
        rw [X.op_map, Equiv.apply_symm_apply, Quiver.Hom.unop_op, SimplexCategory.rev_map_rev_map]
      hom_inv_id := toTop_hom_ext fun _ _ _ ↦ by simp [toTopRevHom]
      inv_hom_id := toTop_hom_ext fun _ _ _ ↦ by simp [toTopRevHom] })
    fun _ ↦ toTop_hom_ext fun _ _ _ ↦ by simp [toTopRevHom, toTop_map_toTopObjMk, opFunctor_map]

section OpLemmas
variable (X : SSet.{u})
@[simp] lemma opFunctorCompToTopIso_hom_app_toTopObjMk {n : ℕ} (y : X.op _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) : dsimp% (opFunctorCompToTopIso.hom.app X) (toTopObjMk y w) =
      toTopObjMk (X.opObjEquiv y) (StdSimplex.map Fin.rev w) := descToTop_toTopObjMk _ _ _ y w
@[simp] lemma opFunctorCompToTopIso_inv_app_toTopObjMk {n : ℕ} (x : X _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) : dsimp% (opFunctorCompToTopIso.inv.app X) (toTopObjMk x w) =
      toTopObjMk (X.opObjEquiv.symm x) (StdSimplex.map Fin.rev w) := descToTop_toTopObjMk _ _ _ x w
@[simp] lemma opFunctorCompToTopIso_hom_app_toTopPoint (y : X.op _⦋0⦌) :
    dsimp% (opFunctorCompToTopIso.hom.app X) (toTopPoint y) = toTopPoint (X.opObjEquiv y) := by
  rw [← toTopObjMk_eq_toTopPoint y (StdSimplex.single 0), opFunctorCompToTopIso_hom_app_toTopObjMk,
    toTopObjMk_eq_toTopPoint]
@[simp] lemma opFunctorCompToTopIso_inv_app_toTopPoint (x : X _⦋0⦌) :
    dsimp% (opFunctorCompToTopIso.inv.app X) (toTopPoint x) = toTopPoint (X.opObjEquiv.symm x) := by
  rw [← toTopObjMk_eq_toTopPoint x (StdSimplex.single 0), opFunctorCompToTopIso_inv_app_toTopObjMk,
    toTopObjMk_eq_toTopPoint]
/-- Homeomorphism `|X.op| ≃ₜ |X|` reversing barycentric coordinates on each simplex. -/
noncomputable def toTopOpHomeomorph : |X.op| ≃ₜ |X| :=
  TopCat.homeoOfIso (opFunctorCompToTopIso.app X)
@[simp] lemma toTopOpHomeomorph_toTopObjMk {n : ℕ} (y : X.op _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    toTopOpHomeomorph X (toTopObjMk y w) = toTopObjMk (X.opObjEquiv y) (StdSimplex.map Fin.rev w) :=
  opFunctorCompToTopIso_hom_app_toTopObjMk X y w
@[simp] lemma toTopOpHomeomorph_symm_toTopObjMk {n : ℕ} (x : X _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) : (toTopOpHomeomorph X).symm (toTopObjMk x w) =
      toTopObjMk (X.opObjEquiv.symm x) (StdSimplex.map Fin.rev w) :=
  opFunctorCompToTopIso_inv_app_toTopObjMk X x w
@[simp] lemma toTopOpHomeomorph_toTopPoint (y : X.op _⦋0⦌) :
    toTopOpHomeomorph X (toTopPoint y) = toTopPoint (X.opObjEquiv y) :=
  opFunctorCompToTopIso_hom_app_toTopPoint X y
@[simp] lemma toTopOpHomeomorph_symm_toTopPoint (x : X _⦋0⦌) :
    (toTopOpHomeomorph X).symm (toTopPoint x) = toTopPoint (X.opObjEquiv.symm x) :=
  opFunctorCompToTopIso_inv_app_toTopPoint X x
end OpLemmas

lemma toTopOpHomeomorph_naturality_apply (f : X ⟶ Y) (z : |X.op|) :
    toTopOpHomeomorph Y (toTop.map (SSet.opFunctor.map f) z) =
      toTop.map f (toTopOpHomeomorph X z) :=
  ConcreteCategory.congr_hom (opFunctorCompToTopIso.hom.naturality f) z
@[simp] lemma toTopOpHomeomorph_opEquiv_toTopPath_apply {x₀ x₁ : X _⦋0⦌} (e : X.Edge x₀ x₁)
    (t : unitInterval) :
    toTopOpHomeomorph X ((Edge.opEquiv e).toTopPath t) = e.toTopPath.symm t := by
  rw [Edge.toTopPath_apply, toTopOpHomeomorph_toTopObjMk, Edge.opEquiv_edge, Equiv.apply_symm_apply,
    StdSimplex.map_rev_homeomorphI_symm, _root_.Path.symm_apply, Function.comp_apply,
    Edge.toTopPath_apply]
end SSet
