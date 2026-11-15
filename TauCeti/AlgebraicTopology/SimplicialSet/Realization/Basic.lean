/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Category.TopCat.ULift
public import TauCeti.AlgebraicTopology.SimplicialSet.Op
public import TauCeti.AlgebraicTopology.SimplicialSet.Realization.PiZero
public import TauCeti.AlgebraicTopology.SimplicialSet.ULift
public import TauCeti.Geometry.Convex.ConvexSpace.ContractibleSpaceStdSimplex
public import TauCeti.Geometry.Convex.ConvexSpace.Defs

/-!
# Basic properties and natural isomorphisms of geometric realization

This file develops simplex-level and functorial properties of `SSet.toTop : SSet ⥤ TopCat`:
* vertices, constant maps, emptiness, and path components (`SSet.toTopObjMk_eq_toTopPoint`,
  `SSet.toTop_map_const`, `SSet.isEmpty_toTop_iff`, `SSet.exists_joined_toTopPoint`);
* separation of `0`- and `1`-simplices (`SSet.toTopPoint_injective`,
  `SSet.toTopObjMk_one_injective`);
* edge paths and `2`-simplex homotopies (`SSet.Edge.toTopPath`,
  `SSet.Edge.CompStruct.toTopPath_homotopic`);
* natural isomorphisms for discrete sets, universe lifts, and opposites (`SSet.constCompToTopIso`,
  `SSet.uliftFunctorCompToTopIso`, `SSet.toTopOpIso`).

## References

* J. Milnor, *The geometric realization of a semi-simplicial complex*, Ann. of Math. 65 (1957).
* P. G. Goerss and J. F. Jardine, *Simplicial Homotopy Theory*, Birkhäuser, 1999, §§I.2, I.11.
-/

public section

open CategoryTheory Limits Opposite Simplicial Convexity

universe v u

namespace SSet

variable {X Y : SSet.{u}}

/-! ### Vertices, emptiness, and constant maps -/

private structure SimplexCocone (X : SSet.{u}) (T : TopCat.{u}) where
  map (n : ℕ) (x : X _⦋n⦌) : C(StdSimplex ℝ (Fin (n + 1)), T)
  naturality {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (x : X _⦋n⦌) (w : StdSimplex ℝ (Fin (m + 1))) :
    map m (X.map θ.op x) w = map n x (StdSimplex.map θ w)

@[irreducible] private noncomputable def mkToTopHom {X : SSet.{u}} {T : TopCat.{u}}
    (S : SimplexCocone X T) : |X| ⟶ T :=
  (sSetTopAdj.homEquiv X T).symm
    { app n := ↾fun x ↦ (T.toSSetObjEquiv n).symm (S.map n.unop.len x)
      naturality := fun ⟨n⟩ ⟨m⟩ θ ↦ by
        ext x; induction n using SimplexCategory.rec with | _ n
        induction m using SimplexCategory.rec with | _ m
        obtain ⟨θ, rfl⟩ : ∃ φ : ⦋m⦌ ⟶ ⦋n⦌, φ.op = θ := ⟨θ.unop, rfl⟩
        apply (T.toSSetObjEquiv _).injective; ext w : 1
        simp only [TypeCat.Fun.toFun_apply, ConcreteCategory.comp_apply]
        rw [TopCat.toSSetObjEquiv_naturality_apply]; dsimp [SimplexCategory.len_mk]
        simp only [Equiv.apply_symm_apply]; exact S.naturality θ x w }

private lemma mkToTopHom_toTopObjMk {X : SSet.{u}} {T : TopCat.{u}} (S : SimplexCocone X T)
    {n : ℕ} (x : X _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
    mkToTopHom S (toTopObjMk x w) = S.map n x w := by
  unfold mkToTopHom; rw [apply_toTopObjMk, Equiv.apply_symm_apply]
  exact congrFun (congrArg DFunLike.coe (Equiv.apply_symm_apply _ (S.map n x))) w

/-- Evaluating the realization of a simplex morphism `Δ[n] ⟶ X` along `SimplexCategory.toTopHomeo`
produces `SSet.toTopObjMk`. -/
lemma toTop_map_yonedaEquiv_symm_toTopHomeo_symm {n : ℕ} (x : X _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    toTop.map (yonedaEquiv.symm x) ((⦋n⦌.toTopHomeo).symm w) = toTopObjMk x w := by
  rw [toTopObjMk_def]
  exact (ConcreteCategory.congr_hom (sSetTopAdj_unit_app_app_down X (op ⦋n⦌) x) (ULift.up w)).symm

/-- On the standard `0`-simplex, `SSet.toTopObjMk x w` equals `SSet.toTopPoint x`. -/
lemma toTopObjMk_eq_toTopPoint (x : X _⦋0⦌) (w : StdSimplex ℝ (Fin 1)) :
    toTopObjMk x w = toTopPoint x := by
  rw [← toTop_map_yonedaEquiv_symm_toTopHomeo_symm,
    Subsingleton.elim ((⦋0⦌.toTopHomeo).symm w) (toTopPoint (stdSimplex.objEquiv.symm (𝟙 ⦋0⦌))),
    toTop_map_toTopPoint, yonedaEquiv_symm_app_objEquiv_symm, op_id,
    CategoryTheory.Functor.map_id, types_id_apply]

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

/-- Geometric realization carries `SSet.const y` to the constant map at `toTopPoint y`. -/
@[simp]
lemma toTop_map_const (y : Y _⦋0⦌) (z : |X|) :
    toTop.map (SSet.const y) z = toTopPoint y := by
  obtain ⟨n, x, w, rfl⟩ := exists_toTopObjMk z
  rw [toTop_map_toTopObjMk, const_app, TypeCat.ofHom_apply, toTopObjMk_map,
    toTopObjMk_eq_toTopPoint]

/-- In `TopCat`, the geometric realization of `SSet.const y` is `TopCat.const (toTopPoint y)`. -/
lemma toTop_map_const_eq (y : Y _⦋0⦌) :
    toTop.map (SSet.const y : X ⟶ Y) = TopCat.const (toTopPoint y) := by
  ext z; exact toTop_map_const y z

/-- The geometric realization `|X|` is empty if and only if `X` has no `0`-simplices. -/
@[simp]
theorem isEmpty_toTop_iff (X : SSet.{u}) : IsEmpty |X| ↔ IsEmpty (X _⦋0⦌) := by
  refine ⟨fun h ↦ ⟨fun x ↦ h.false (toTopPoint x)⟩, fun h ↦ ⟨fun z ↦ ?_⟩⟩
  obtain ⟨x, -⟩ := π₀.mk_surjective (X.π₀EquivZerothHomotopy.symm (.mk z))
  exact h.false x

instance [IsEmpty (X _⦋0⦌)] : IsEmpty |X| :=
  (isEmpty_toTop_iff X).2 inferInstance

/-- Every point of `|X|` lies in the path component of `SSet.toTopPoint x` for some vertex `x`. -/
lemma exists_joined_toTopPoint (z : |X|) : ∃ x : X _⦋0⦌, Joined z (toTopPoint x) := by
  obtain ⟨x, hx⟩ := π₀.mk_surjective (X.π₀EquivZerothHomotopy.symm (.mk z))
  have hm := congrArg X.π₀EquivZerothHomotopy hx
  rw [π₀EquivZerothHomotopy_mk, Equiv.apply_symm_apply] at hm
  exact ⟨x, Quotient.exact hm.symm⟩

/-! ### Separation of vertices and `1`-simplices -/

private lemma sum_map_weights {m n : ℕ} (θ : Fin (m + 1) → Fin (n + 1))
    (w : StdSimplex ℝ (Fin (m + 1))) (f : Fin (n + 1) → ℝ) :
    ∑ p : Fin (n + 1), (w.map θ).weights p * f p = ∑ a : Fin (m + 1), w.weights a * f (θ a) := by
  rw [← Finset.sum_fiberwise Finset.univ θ (fun a ↦ w.weights a * f (θ a))]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [StdSimplex.weights_map_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a ha ↦ by rw [(Finset.mem_filter.1 ha).2]

/-- Distinct vertices of a simplicial set map to distinct points of its geometric realization. -/
theorem toTopPoint_injective (X : SSet.{u}) : Function.Injective (toTopPoint (X := X)) := by
  classical
  intro x₁ x₂ h
  let g : X _⦋0⦌ → ℝ := fun y ↦ if y = x₁ then 1 else 0
  let F : |X| ⟶ TopCat.of (ULift.{u} ℝ) := mkToTopHom
    ⟨fun n σ ↦ ⟨fun w ↦ ULift.up (∑ i, w.weights i * g (X.map (⦋0⦌.const ⦋n⦌ i).op σ)),
        by fun_prop⟩,
      fun θ σ w ↦ congrArg ULift.up <| by
        have hc (j) : ⦋0⦌.const _ j ≫ θ = ⦋0⦌.const _ (θ j) := by ext k; fin_cases k; rfl
        simp_rw [← Functor.map_comp_apply, ← op_comp, hc, sum_map_weights]⟩
  have eval (x : X _⦋0⦌) : (F (toTopPoint x)).down = g x := by
    have hc₀ : ⦋0⦌.const ⦋0⦌ 0 = 𝟙 ⦋0⦌ := by ext k; fin_cases k; rfl
    rw [← toTopObjMk_eq_toTopPoint x (StdSimplex.single 0)]
    have hF : F (toTopObjMk x (StdSimplex.single 0)) = _ := mkToTopHom_toTopObjMk _ x _
    exact (congrArg ULift.down hF).trans (by simp [hc₀])
  have h12 : g x₁ = g x₂ := by rw [← eval x₁, ← eval x₂, h]
  by_contra hne
  simp [g, Ne.symm hne] at h12

@[simp]
lemma toTopPoint_inj {x₁ x₂ : X _⦋0⦌} : toTopPoint x₁ = toTopPoint x₂ ↔ x₁ = x₂ :=
  (toTopPoint_injective X).eq_iff

private noncomputable def edgeExtension (h : X _⦋1⦌ → ℝ) (hh : ∀ x : X _⦋0⦌, h (X.σ 0 x) = 0) :
    |X| ⟶ TopCat.of (ULift.{u} ℝ) :=
  mkToTopHom
    ⟨fun n σ ↦ ⟨fun w ↦ ULift.up (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        w.weights i * w.weights j *
          if hij : i ≤ j then h (X.map (SimplexCategory.mkOfLe i j hij).op σ) else 0),
      by fun_prop⟩,
    fun {m n} θ σ w ↦ congrArg ULift.up <| by
      have hdiag (p : Fin (n + 1)) : h (X.map (SimplexCategory.mkOfLe p p le_rfl).op σ) = 0 := by
        have hmk : SimplexCategory.mkOfLe p p le_rfl = SimplexCategory.σ 0 ≫ ⦋0⦌.const ⦋n⦌ p := by
          ext k; fin_cases k <;> rfl
        rw [hmk, op_comp, Functor.map_comp_apply]; exact hh _
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
        · simp only [c, hab, ↓reduceDIte]
          split_ifs with hθ; swap; · rfl
          have heq : θ a = θ b := le_antisymm hθ (θ.toOrderHom.monotone (le_of_not_ge hab))
          have hmk : SimplexCategory.mkOfLe (θ a) (θ b) hθ =
              SimplexCategory.mkOfLe (θ a) (θ a) le_rfl := by
            ext k; fin_cases k <;> simp [SimplexCategory.mkOfLe, heq]
          rw [hmk, hdiag]
      simp_rw [hcoeff, mul_assoc, ← Finset.mul_sum]
      exact (Finset.sum_congr rfl fun a _ ↦
        congrArg (w.weights a * ·) (sum_map_weights _ _ _).symm).trans
        (sum_map_weights θ w fun p ↦ ∑ q, (w.map θ).weights q * c p q).symm⟩

/-- The vertex `0` of the standard `1`-simplex maps to the `1`-st face of a `1`-simplex. -/
@[simp]
lemma toTopObjMk_single_zero (e : X _⦋1⦌) :
    toTopObjMk e (StdSimplex.single 0) = toTopPoint (X.δ 1 e) := by
  rw [show (StdSimplex.single 0 : StdSimplex ℝ (Fin 2)) =
      StdSimplex.map (SimplexCategory.δ 1) (StdSimplex.single 0) by rw [StdSimplex.map_single]; rfl,
    ← toTopObjMk_map, toTopObjMk_eq_toTopPoint]; rfl

/-- The vertex `1` of the standard `1`-simplex maps to the `0`-th face of a `1`-simplex. -/
@[simp]
lemma toTopObjMk_single_one (e : X _⦋1⦌) :
    toTopObjMk e (StdSimplex.single 1) = toTopPoint (X.δ 0 e) := by
  rw [show (StdSimplex.single 1 : StdSimplex ℝ (Fin 2)) =
      StdSimplex.map (SimplexCategory.δ 0) (StdSimplex.single 0) by rw [StdSimplex.map_single]; rfl,
    ← toTopObjMk_map, toTopObjMk_eq_toTopPoint]; rfl

private lemma edgeExtension_midpoint {h : X _⦋1⦌ → ℝ} (hh : ∀ x : X _⦋0⦌, h (X.σ 0 x) = 0)
    (e : X _⦋1⦌) :
    (edgeExtension h hh
      (toTopObjMk e (StdSimplex.homeomorphI.symm ⟨1 / 2, by norm_num, by norm_num⟩))).down =
      h e / 4 := by
  let w : StdSimplex ℝ (Fin 2) := StdSimplex.homeomorphI.symm ⟨1 / 2, by norm_num, by norm_num⟩
  have hw₁ : w.weights 1 = 1 / 2 := by simpa [w] using (StdSimplex.homeomorphI_apply_coe w).symm
  have hw₀ : w.weights 0 = 1 / 2 := by
    linarith [StdSimplex.total_of_fintype w, Fin.sum_univ_two w.weights, hw₁]
  have hdiag (p : Fin 2) : h (X.map (SimplexCategory.mkOfLe p p le_rfl).op e) = 0 := by
    have hmk : SimplexCategory.mkOfLe p p le_rfl = SimplexCategory.σ 0 ≫ ⦋0⦌.const ⦋1⦌ p := by
      ext k; fin_cases k <;> rfl
    rw [hmk, op_comp, Functor.map_comp_apply]; exact hh _
  have hid : SimplexCategory.mkOfLe (0 : Fin 2) 1 (by decide) = 𝟙 ⦋1⦌ := by
    ext k; fin_cases k <;> rfl
  have hF : edgeExtension h hh (toTopObjMk e w) = _ := mkToTopHom_toTopObjMk _ e w
  refine (congrArg ULift.down hF).trans ?_
  dsimp
  have h01 : (0 : Fin 2) ≤ 1 := by decide
  have h10 : ¬ ((1 : Fin 2) ≤ 0) := by decide
  simp only [Fin.sum_univ_two, le_refl, ↓reduceDIte, hdiag, mul_zero, zero_add, add_zero,
    h01, h10, hid, op_id, CategoryTheory.Functor.map_id, CategoryTheory.id_apply]
  change w.weights 0 * w.weights 1 * h e = h e / 4
  rw [hw₀, hw₁]; ring

/-- Distinct `1`-simplices of `X` determine distinct parametrized simplices in `|X|`. -/
theorem toTopObjMk_one_injective (X : SSet.{u}) :
    Function.Injective (fun e : X _⦋1⦌ ↦ toTopObjMk e) := by
  classical
  have sep {e₁ e₂ : X _⦋1⦌} (he₁ : e₁ ∉ Set.range (X.σ 0))
      (heq : toTopObjMk e₁ = toTopObjMk e₂) : e₁ = e₂ := by
    let h : X _⦋1⦌ → ℝ := fun e ↦ if e = e₁ then 1 else 0
    have hh (x : X _⦋0⦌) : h (X.σ 0 x) = 0 :=
      ite_eq_right_iff.2 fun hx ↦ absurd ⟨x, hx⟩ he₁
    have hm := edgeExtension_midpoint hh e₁
    rw [heq, edgeExtension_midpoint hh e₂] at hm
    by_contra hne
    simp [h, Ne.symm hne] at hm
  intro e₁ e₂ heq
  by_cases h₁ : e₁ ∈ Set.range (X.σ 0)
  · by_cases h₂ : e₂ ∈ Set.range (X.σ 0); swap; · exact (sep h₂ heq.symm).symm
    obtain ⟨x₁, rfl⟩ := h₁; obtain ⟨x₂, rfl⟩ := h₂
    have hv : toTopObjMk (X.σ 0 x₁) (StdSimplex.single 1) =
        toTopObjMk (X.σ 0 x₂) (StdSimplex.single 1) := congrFun heq (StdSimplex.single 1)
    have h0 : (0 : Fin 2) = Fin.castSucc 0 := rfl
    rw [toTopObjMk_single_one, toTopObjMk_single_one, toTopPoint_inj, h0,
      δ_comp_σ_self_apply, δ_comp_σ_self_apply] at hv
    exact congrArg _ hv
  · exact sep h₁ heq

/-! ### Edge paths and `2`-simplices in geometric realization -/

namespace Edge

open unitInterval

variable {x₀ x₁ x₂ : X _⦋0⦌}

/-- The path in `|X|` from `toTopPoint x₀` to `toTopPoint x₁` traced by an edge `e : X.Edge x₀ x₁`
along `StdSimplex.homeomorphI.symm`. -/
noncomputable def toTopPath (e : X.Edge x₀ x₁) : _root_.Path (toTopPoint x₀) (toTopPoint x₁) where
  toContinuousMap :=
    (⟨toTopObjMk e.edge, continuous_toTopObjMk e.edge⟩ : C(_, |X|)).comp
      (StdSimplex.homeomorphI.symm : C(I, StdSimplex ℝ (Fin 2)))
  source' := by simp [e.src_eq]
  target' := by simp [e.tgt_eq]

@[simp]
lemma toTopPath_apply (e : X.Edge x₀ x₁) (t : I) :
    e.toTopPath t = toTopObjMk e.edge (StdSimplex.homeomorphI.symm t) := (rfl)

/-- A degenerate edge traces the constant path at its vertex. -/
@[simp]
lemma toTopPath_id (x : X _⦋0⦌) : (Edge.id x).toTopPath = _root_.Path.refl (toTopPoint x) := by
  ext t; change toTopObjMk (X.σ 0 x) _ = _
  rw [SimplicialObject.σ, toTopObjMk_map, toTopObjMk_eq_toTopPoint]; rfl

/-- Mapping an edge path along `|f|` gives the edge path of the mapped edge. -/
lemma toTop_map_toTopPath_apply (f : X ⟶ Y) (e : X.Edge x₀ x₁) (t : I) :
    toTop.map f (e.toTopPath t) = (e.map f).toTopPath t := by simp

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
    change toTopObjMk h.simplex (StdSimplex.map j.succAbove (StdSimplex.homeomorphI.symm t)) = _
    rw [← SimplexCategory.coe_δ, ← toTopObjMk_map, ← SimplicialObject.δ, hd, toTopPath_apply]
  have hs : toTopPoint x₀ = σMap (StdSimplex.single 0) :=
    (e₀₂.toTopPath.source.symm.trans
      (hpt (a := 0) (b := 2) 1 (by decide) (by decide) e₀₂ h.d₁ 0).symm).trans
      (_root_.Path.source _)
  have ht : toTopPoint x₂ = σMap (StdSimplex.single 2) :=
    (e₀₂.toTopPath.target.symm.trans
      (hpt (a := 0) (b := 2) 1 (by decide) (by decide) e₀₂ h.d₁ 1).symm).trans
      (_root_.Path.target _)
  convert hmap.pathCast hs ht using 1
  · exact (_root_.Path.ext (funext (hpt 1 (by decide) (by decide) e₀₂ h.d₁))).symm
  · ext t; simp only [_root_.Path.cast_coe, _root_.Path.trans_apply]; split_ifs with ht'
    · exact (hpt 2 (by decide) (by decide) e₀₁ h.d₂ ⟨2 * t,
        (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht'⟩⟩).symm
    · exact (hpt 0 (by decide) (by decide) e₁₂ h.d₀ ⟨2 * t - 1,
        unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht').le, t.2.2⟩⟩).symm

end Edge

/-! ### Realization of discrete simplicial sets -/

private noncomputable def constToTopHom (ι : Type u) :
    |((Functor.const SimplexCategoryᵒᵖ : Type u ⥤ SSet.{u}).obj ι)| ⟶ TopCat.discrete.obj ι :=
  mkToTopHom ⟨fun _ i ↦ ContinuousMap.const _ (show TopCat.discrete.obj ι from i), fun _ _ _ ↦ rfl⟩

private lemma constToTopHom_toTopObjMk (ι : Type u) {n : ℕ}
    (i : ((Functor.const SimplexCategoryᵒᵖ : Type u ⥤ SSet.{u}).obj ι) _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    constToTopHom ι (toTopObjMk i w) = (show TopCat.discrete.obj ι from i) :=
  mkToTopHom_toTopObjMk _ i w

private noncomputable def constToTopInv (ι : Type u) :
    TopCat.discrete.obj ι ⟶ |((Functor.const SimplexCategoryᵒᵖ : Type u ⥤ SSet.{u}).obj ι)| :=
  ConcreteCategory.ofHom ⟨fun x ↦ toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj ι)
    (show ((Functor.const SimplexCategoryᵒᵖ).obj ι) _⦋0⦌ from x), continuous_of_discreteTopology⟩

/-- The natural isomorphism `|(Functor.const _).obj ι| ≅ TopCat.discrete.obj ι` identifying the
geometric realization of the discrete simplicial set on `ι` with the discrete space on `ι`. -/
noncomputable def constCompToTopIso :
    (Functor.const SimplexCategoryᵒᵖ : Type u ⥤ SSet.{u}) ⋙ SSet.toTop.{u} ≅ TopCat.discrete.{u} :=
  (NatIso.ofComponents (fun (ι : Type u) ↦
    { hom := constToTopInv ι, inv := constToTopHom ι
      hom_inv_id := by
        ext x
        let j : ((Functor.const SimplexCategoryᵒᵖ : Type u ⥤ SSet.{u}).obj ι) _⦋0⦌ := x
        exact (congrArg (constToTopHom ι)
          (toTopObjMk_eq_toTopPoint j (StdSimplex.single 0)).symm).trans
          (constToTopHom_toTopObjMk ι j _)
      inv_hom_id := toTop_hom_ext fun n i w ↦ by
        let j : ((Functor.const SimplexCategoryᵒᵖ : Type u ⥤ SSet.{u}).obj ι) _⦋0⦌ := i
        have hi : toTopObjMk (X := (Functor.const SimplexCategoryᵒᵖ).obj ι) i w =
            toTopPoint j := by
          conv_lhs => rw [show i = ((Functor.const SimplexCategoryᵒᵖ).obj ι).map
            (⦋n⦌.const ⦋0⦌ 0).op j from rfl]
          rw [toTopObjMk_map, toTopObjMk_eq_toTopPoint]
        exact (congrArg (constToTopInv ι) (constToTopHom_toTopObjMk ι i w)).trans hi.symm })
    fun f ↦ by
      ext x; exact (toTop_map_toTopPoint ((Functor.const SimplexCategoryᵒᵖ).map f)
        (show ((Functor.const SimplexCategoryᵒᵖ).obj _) _⦋0⦌ from x)).symm).symm

@[simp]
lemma constCompToTopIso_inv_app_apply (ι : Type u) (i : ι) :
    dsimp% (constCompToTopIso.inv.app ι) (i : TopCat.discrete.obj ι) =
      toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj ι) i := by rfl

@[simp]
lemma constCompToTopIso_hom_app_toTopPoint (ι : Type u) (i : ι) :
    dsimp% (constCompToTopIso.hom.app ι)
        (toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj ι) i) =
      (i : TopCat.discrete.obj ι) := by
  simpa using Iso.inv_hom_id_app_apply constCompToTopIso ι (i : TopCat.discrete.obj ι)

/-! ### Realization of universe lifts -/

private noncomputable def uliftToTopHom (X : SSet.{u}) :
    |SSet.uliftFunctor.{v, u}.obj X| ⟶ TopCat.uliftFunctor.{v, u}.obj |X| :=
  mkToTopHom
    ⟨fun _ x ↦ (|X|.uliftFunctorObjHomeo : C(|X|, _)).comp
        ⟨toTopObjMk x.down, continuous_toTopObjMk x.down⟩,
      fun θ x w ↦ congrArg |X|.uliftFunctorObjHomeo (toTopObjMk_map θ x.down w)⟩

private lemma uliftToTopHom_toTopObjMk (X : SSet.{u}) {n : ℕ}
    (x : (SSet.uliftFunctor.{v, u}.obj X) _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
    uliftToTopHom.{v, u} X (toTopObjMk x w) = |X|.uliftFunctorObjHomeo (toTopObjMk x.down w) :=
  mkToTopHom_toTopObjMk _ x w

private noncomputable def uliftYonedaToTopHomeo (m : SimplexCategory) :
    |uliftYoneda.{u}.obj m| ≃ₜ StdSimplex ℝ (Fin (m.len + 1)) := m.toTopHomeo

private noncomputable def uliftToTopCoconeApp (X : SSet.{u})
    (j : CostructuredArrow uliftYoneda.{u} X) :
    TopCat.uliftFunctor.{v, u}.obj |uliftYoneda.{u}.obj j.left| ⟶
      |SSet.uliftFunctor.{v, u}.obj X| :=
  ConcreteCategory.ofHom ((⟨toTopObjMk (X := SSet.uliftFunctor.{v, u}.obj X)
      (ULift.up (yonedaEquiv (show Δ[j.left.len] ⟶ X from j.hom))), continuous_toTopObjMk _⟩ :
      C(StdSimplex ℝ (Fin (j.left.len + 1)), |SSet.uliftFunctor.{v, u}.obj X|)).comp
    ((uliftYonedaToTopHomeo.{u} j.left : C(|uliftYoneda.{u}.obj j.left|, _)).comp
      (|uliftYoneda.{u}.obj j.left|.uliftFunctorObjHomeo.{v, u}.symm : C(_, _))))

private lemma uliftToTopCoconeApp_apply (X : SSet.{u})
    (j : CostructuredArrow uliftYoneda.{u} X) (y : |uliftYoneda.{u}.obj j.left|) :
    uliftToTopCoconeApp.{v, u} X j (|uliftYoneda.{u}.obj j.left|.uliftFunctorObjHomeo.{v, u} y) =
      toTopObjMk (X := SSet.uliftFunctor.{v, u}.obj X)
        (ULift.up (yonedaEquiv (show Δ[j.left.len] ⟶ X from j.hom)))
        (uliftYonedaToTopHomeo.{u} j.left y) :=
  congrArg (fun z ↦ toTopObjMk (X := SSet.uliftFunctor.{v, u}.obj X)
    (ULift.up (yonedaEquiv (show Δ[j.left.len] ⟶ X from j.hom)))
    (uliftYonedaToTopHomeo.{u} j.left z))
    (Homeomorph.symm_apply_apply |uliftYoneda.{u}.obj j.left|.uliftFunctorObjHomeo.{v, u} y)

private noncomputable def uliftToTopCocone (X : SSet.{u}) :
    Cocone (CostructuredArrow.proj uliftYoneda.{u} X ⋙
      uliftYoneda.{u} ⋙ SSet.toTop.{u} ⋙ TopCat.uliftFunctor.{v, u}) where
  pt := |SSet.uliftFunctor.{v, u}.obj X|
  ι :=
    { app j := uliftToTopCoconeApp.{v, u} X j
      naturality j₁ j₂ g := by
        ext z; obtain ⟨y, rfl⟩ := |uliftYoneda.{u}.obj j₁.left|.uliftFunctorObjHomeo.surjective z
        dsimp only [Functor.const_obj_obj, Functor.const_obj_map, Functor.comp_obj,
          Functor.comp_map, CostructuredArrow.proj_obj, CostructuredArrow.proj_map]
        rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, CategoryTheory.id_apply,
          TopCat.uliftFunctorObjHomeo_naturality_apply, uliftToTopCoconeApp_apply,
          uliftToTopCoconeApp_apply,
          show uliftYonedaToTopHomeo.{u} j₂.left (toTop.map (uliftYoneda.{u}.map g.left) y) =
            StdSimplex.map g.left (uliftYonedaToTopHomeo.{u} j₁.left y) from
            SimplexCategory.toTopHomeo_naturality_apply g.left y]
        have hyon := SSet.yonedaEquiv_naturality
          (show ⦋j₁.left.len⦌ ⟶ ⦋j₂.left.len⦌ from g.left) (show Δ[j₂.left.len] ⟶ X from j₂.hom)
        rw [show SSet.stdSimplex.map (show ⦋j₁.left.len⦌ ⟶ ⦋j₂.left.len⦌ from g.left) ≫
          (show Δ[j₂.left.len] ⟶ X from j₂.hom) = show Δ[j₁.left.len] ⟶ X from j₁.hom from
          CostructuredArrow.w g] at hyon
        exact (toTopObjMk_map (X := SSet.uliftFunctor.{v, u}.obj X)
          (show ⦋j₁.left.len⦌ ⟶ ⦋j₂.left.len⦌ from g.left) _ _).symm.trans
          (congrArg (toTopObjMk · _) (congrArg ULift.up hyon)) }

private noncomputable def uliftToTopInv (X : SSet.{u}) :
    TopCat.uliftFunctor.{v, u}.obj |X| ⟶ |SSet.uliftFunctor.{v, u}.obj X| :=
  (isColimitOfPreserves (SSet.toTop.{u} ⋙ TopCat.uliftFunctor.{v, u})
    (denseAtUliftYoneda X)).desc (uliftToTopCocone.{v, u} X)

private lemma uliftToTopInv_apply (X : SSet.{u}) {n : ℕ} (x : X _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    uliftToTopInv.{v, u} X (|X|.uliftFunctorObjHomeo (toTopObjMk x w)) =
      toTopObjMk (X := SSet.uliftFunctor.{v, u}.obj X) (ULift.up x) w := by
  let f : uliftYoneda.{u}.obj ⦋n⦌ ⟶ X := yonedaEquiv.symm x
  let j : CostructuredArrow uliftYoneda.{u} X := CostructuredArrow.mk f
  let y : |uliftYoneda.{u}.obj j.left| := (uliftYonedaToTopHomeo.{u} ⦋n⦌).symm w
  have hfac := ConcreteCategory.congr_hom
    ((isColimitOfPreserves (SSet.toTop.{u} ⋙ TopCat.uliftFunctor.{v, u})
      (denseAtUliftYoneda X)).fac (uliftToTopCocone.{v, u} X) j)
    (|uliftYoneda.{u}.obj j.left|.uliftFunctorObjHomeo y)
  have hlhs : ((toTop.{u} ⋙ TopCat.uliftFunctor.{v, u}).mapCocone
      ((Functor.LeftExtension.mk _ uliftYoneda.{u}.rightUnitor.inv).coconeAt X)).ι.app j
      (|uliftYoneda.{u}.obj j.left|.uliftFunctorObjHomeo y) =
      |X|.uliftFunctorObjHomeo (toTopObjMk x w) := by
    dsimp [j]; exact congrArg |X|.uliftFunctorObjHomeo
      (toTop_map_yonedaEquiv_symm_toTopHomeo_symm x w)
  have hrhs : (uliftToTopCocone.{v, u} X).ι.app j
      (|uliftYoneda.{u}.obj j.left|.uliftFunctorObjHomeo y) =
      toTopObjMk (X := SSet.uliftFunctor.{v, u}.obj X) (ULift.up x) w := by
    refine (uliftToTopCoconeApp_apply X j y).trans ?_
    rw [show uliftYonedaToTopHomeo.{u} j.left y = w from Homeomorph.apply_symm_apply _ w]
    exact congrArg (fun z ↦ toTopObjMk (X := SSet.uliftFunctor.{v, u}.obj X) (ULift.up z) w)
      ((congrArg yonedaEquiv (rfl : (show Δ[n] ⟶ X from j.hom) = yonedaEquiv.symm x)).trans
        (Equiv.apply_symm_apply _ _))
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

@[simp]
lemma uliftFunctorCompToTopIso_hom_app_toTopObjMk (X : SSet.{u}) {n : ℕ}
    (x : (SSet.uliftFunctor.{v, u}.obj X) _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
    dsimp% (uliftFunctorCompToTopIso.{v, u}.hom.app X) (toTopObjMk x w) =
      |X|.uliftFunctorObjHomeo (toTopObjMk x.down w) :=
  uliftToTopHom_toTopObjMk X x w

@[simp]
lemma uliftFunctorCompToTopIso_inv_app_toTopObjMk (X : SSet.{u}) {n : ℕ}
    (x : X _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
    dsimp% (uliftFunctorCompToTopIso.{v, u}.inv.app X)
        (|X|.uliftFunctorObjHomeo (toTopObjMk x w)) =
      toTopObjMk (X := SSet.uliftFunctor.{v, u}.obj X) (ULift.up x) w :=
  uliftToTopInv_apply X x w

/-- Homeomorphism `|uliftFunctor.obj X| ≃ₜ |X|` comparing the geometric realization of a universe
lift with the geometric realization of `X`. -/
noncomputable def toTopUliftHomeomorph (X : SSet.{u}) :
    |SSet.uliftFunctor.{v, u}.obj X| ≃ₜ |X| :=
  (TopCat.homeoOfIso (uliftFunctorCompToTopIso.{v, u}.app X)).trans |X|.uliftFunctorObjHomeo.symm

@[simp]
lemma toTopUliftHomeomorph_toTopObjMk (X : SSet.{u}) {n : ℕ}
    (x : (SSet.uliftFunctor.{v, u}.obj X) _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
    toTopUliftHomeomorph.{v, u} X (toTopObjMk x w) = toTopObjMk x.down w := by
  simp only [toTopUliftHomeomorph, Homeomorph.trans_apply, TopCat.homeoOfIso_apply, Iso.app_hom]
  exact (congrArg |X|.uliftFunctorObjHomeo.symm
    (uliftToTopHom_toTopObjMk X x w)).trans (Homeomorph.symm_apply_apply _ _)

@[simp]
lemma toTopUliftHomeomorph_symm_toTopObjMk (X : SSet.{u}) {n : ℕ}
    (x : X _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
    (toTopUliftHomeomorph.{v, u} X).symm (toTopObjMk x w) =
      toTopObjMk (X := SSet.uliftFunctor.{v, u}.obj X) (ULift.up x) w := by
  simp only [toTopUliftHomeomorph, Homeomorph.symm_trans_apply, Homeomorph.symm_symm,
    TopCat.homeoOfIso_symm_apply, Iso.app_inv]
  exact uliftToTopInv_apply X x w

@[simp]
lemma toTopUliftHomeomorph_toTopPoint (X : SSet.{u})
    (x : (SSet.uliftFunctor.{v, u}.obj X) _⦋0⦌) :
    toTopUliftHomeomorph.{v, u} X (toTopPoint x) = toTopPoint x.down := by
  rw [← toTopObjMk_eq_toTopPoint x (StdSimplex.single 0), toTopUliftHomeomorph_toTopObjMk,
    toTopObjMk_eq_toTopPoint]

@[simp]
lemma toTopUliftHomeomorph_symm_toTopPoint (X : SSet.{u}) (x : X _⦋0⦌) :
    (toTopUliftHomeomorph.{v, u} X).symm (toTopPoint x) =
      toTopPoint (X := SSet.uliftFunctor.{v, u}.obj X) (ULift.up x) := by
  let ux : (SSet.uliftFunctor.{v, u}.obj X) _⦋0⦌ := ULift.up x
  rw [← toTopObjMk_eq_toTopPoint x (StdSimplex.single 0), toTopUliftHomeomorph_symm_toTopObjMk]
  exact toTopObjMk_eq_toTopPoint ux (StdSimplex.single 0)

/-- `toTopUliftHomeomorph` commutes with the geometric realizations of simplicial maps. -/
lemma toTopUliftHomeomorph_naturality {X Y : SSet.{u}} (f : X ⟶ Y)
    (z : |SSet.uliftFunctor.{v, u}.obj X|) :
    toTopUliftHomeomorph.{v, u} Y (toTop.map (SSet.uliftFunctor.map f) z) =
      toTop.map f (toTopUliftHomeomorph.{v, u} X z) := by
  obtain ⟨n, x, w, rfl⟩ := exists_toTopObjMk z
  simp only [toTop_map_toTopObjMk, toTopUliftHomeomorph_toTopObjMk]; rfl

/-! ### Realization of opposite simplicial sets -/

private noncomputable def toTopRevHom {X Y : SSet.{u}} (e : ∀ {n : ℕ}, X _⦋n⦌ → Y _⦋n⦌)
    (he : ∀ {m n : ℕ} (θ : ⦋m⦌ ⟶ ⦋n⦌) (x : X _⦋n⦌),
      e (X.map θ.op x) = Y.map (SimplexCategory.rev.map θ).op (e x)) : |X| ⟶ |Y| :=
  mkToTopHom
    ⟨fun _ x ↦ (⟨toTopObjMk (e x), continuous_toTopObjMk _⟩ : C(_, |Y|)).comp
        ⟨StdSimplex.map Fin.rev, StdSimplex.continuous_map ℝ Fin.rev⟩,
      fun θ x w ↦ by
        dsimp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk]
        rw [he, toTopObjMk_map, StdSimplex.map_map, StdSimplex.map_map]
        refine congrArg (toTopObjMk (e x)) (congrArg (StdSimplex.map · w) (funext fun i ↦ ?_))
        exact (SimplexCategory.rev_map_apply θ i.rev).trans
          (congrArg Fin.rev (congrArg θ (Fin.rev_rev i)))⟩

private noncomputable def toTopOpMap (X : SSet.{u}) : |X.op| ⟶ |X| :=
  toTopRevHom (fun y ↦ X.opObjEquiv y) fun _ _ ↦ by rw [X.op_map, Equiv.apply_symm_apply]; rfl

private noncomputable def toTopOpMapInv (X : SSet.{u}) : |X| ⟶ |X.op| :=
  toTopRevHom (fun x ↦ X.opObjEquiv.symm x) fun θ _ ↦ by
    rw [X.op_map, Equiv.apply_symm_apply,
      show SimplexCategory.rev.map (SimplexCategory.rev.map θ).op.unop = θ from
        SimplexCategory.rev_map_rev_map θ]

private lemma toTopOpMap_toTopObjMk (X : SSet.{u}) {n : ℕ} (y : X.op _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    toTopOpMap X (toTopObjMk y w) = toTopObjMk (X.opObjEquiv y) (StdSimplex.map Fin.rev w) :=
  mkToTopHom_toTopObjMk _ y w

private lemma toTopOpMapInv_toTopObjMk (X : SSet.{u}) {n : ℕ} (x : X _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    toTopOpMapInv X (toTopObjMk x w) =
      toTopObjMk (X.opObjEquiv.symm x) (StdSimplex.map Fin.rev w) :=
  mkToTopHom_toTopObjMk _ x w

private lemma map_rev_rev {n : ℕ} (w : StdSimplex ℝ (Fin (n + 1))) :
    StdSimplex.map (Fin.rev : Fin (n + 1) → Fin (n + 1)) (StdSimplex.map Fin.rev w) = w := by
  rw [← StdSimplex.map_comp, show (Fin.rev : Fin (n + 1) → _) ∘ Fin.rev = id from
    funext Fin.rev_rev, StdSimplex.map_id]

/-- The geometric realization of the opposite of a simplicial set is naturally isomorphic to its
geometric realization, acting on each simplex by reversing barycentric coordinates. -/
noncomputable def toTopOpIso : SSet.opFunctor.{u} ⋙ SSet.toTop ≅ SSet.toTop :=
  NatIso.ofComponents (fun X ↦
    { hom := toTopOpMap X, inv := toTopOpMapInv X
      hom_inv_id := toTop_hom_ext fun _ _ _ ↦ by
        dsimp only [Functor.comp_obj]
        rw [ConcreteCategory.comp_apply, toTopOpMap_toTopObjMk, toTopOpMapInv_toTopObjMk,
          Equiv.symm_apply_apply, map_rev_rev, CategoryTheory.id_apply]
      inv_hom_id := toTop_hom_ext fun _ _ _ ↦ by
        rw [ConcreteCategory.comp_apply, toTopOpMapInv_toTopObjMk, toTopOpMap_toTopObjMk,
          Equiv.apply_symm_apply, map_rev_rev, CategoryTheory.id_apply] })
    fun _ ↦ toTop_hom_ext fun _ _ _ ↦ by
      simp only [Functor.comp_obj, Functor.comp_map, ConcreteCategory.comp_apply,
        toTop_map_toTopObjMk, toTopOpMap_toTopObjMk, opFunctor_map, Equiv.apply_symm_apply]

@[simp]
lemma toTopOpIso_hom_app_toTopObjMk (X : SSet.{u}) {n : ℕ} (y : X.op _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    dsimp% (toTopOpIso.hom.app X) (toTopObjMk y w) =
      toTopObjMk (X.opObjEquiv y) (StdSimplex.map Fin.rev w) :=
  toTopOpMap_toTopObjMk X y w

@[simp]
lemma toTopOpIso_inv_app_toTopObjMk (X : SSet.{u}) {n : ℕ} (x : X _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    dsimp% (toTopOpIso.inv.app X) (toTopObjMk x w) =
      toTopObjMk (X.opObjEquiv.symm x) (StdSimplex.map Fin.rev w) :=
  toTopOpMapInv_toTopObjMk X x w

@[simp]
lemma toTopOpIso_hom_app_toTopPoint (X : SSet.{u}) (y : X.op _⦋0⦌) :
    dsimp% (toTopOpIso.hom.app X) (toTopPoint y) = toTopPoint (X.opObjEquiv y) := by
  rw [← toTopObjMk_eq_toTopPoint y (StdSimplex.single 0), toTopOpIso_hom_app_toTopObjMk,
    toTopObjMk_eq_toTopPoint]

@[simp]
lemma toTopOpIso_inv_app_toTopPoint (X : SSet.{u}) (x : X _⦋0⦌) :
    dsimp% (toTopOpIso.inv.app X) (toTopPoint x) = toTopPoint (X.opObjEquiv.symm x) := by
  rw [← toTopObjMk_eq_toTopPoint x (StdSimplex.single 0), toTopOpIso_inv_app_toTopObjMk,
    toTopObjMk_eq_toTopPoint]

/-- Homeomorphism `|X.op| ≃ₜ |X|` reversing barycentric coordinates on each simplex. -/
noncomputable def toTopOpHomeomorph (X : SSet.{u}) : |X.op| ≃ₜ |X| :=
  TopCat.homeoOfIso (toTopOpIso.app X)

@[simp]
lemma toTopOpHomeomorph_toTopPoint (X : SSet.{u}) (y : X.op _⦋0⦌) :
    toTopOpHomeomorph X (toTopPoint y) = toTopPoint (X.opObjEquiv y) :=
  toTopOpIso_hom_app_toTopPoint X y

@[simp]
lemma toTopOpHomeomorph_symm_toTopPoint (X : SSet.{u}) (x : X _⦋0⦌) :
    (toTopOpHomeomorph X).symm (toTopPoint x) = toTopPoint (X.opObjEquiv.symm x) :=
  toTopOpIso_inv_app_toTopPoint X x

/-- Reversing the two vertices of the standard `1`-simplex reflects the unit interval via
`unitInterval.symm`. -/
lemma stdSimplex_map_rev_homeomorphI_symm (t : unitInterval) :
    StdSimplex.map (Fin.rev : Fin 2 → Fin 2) (StdSimplex.homeomorphI.symm t) =
      StdSimplex.homeomorphI.symm (unitInterval.symm t) := by
  apply StdSimplex.homeomorphI.injective; ext
  rw [StdSimplex.homeomorphI_apply_coe, Homeomorph.apply_symm_apply, unitInterval.coe_symm_eq,
    show (1 : Fin 2) = Fin.rev 0 from rfl, StdSimplex.weights_map_apply_of_injective
      Fin.rev_injective]
  have hw₁ : (StdSimplex.homeomorphI.symm t).weights 1 = (t : ℝ) :=
    (StdSimplex.homeomorphI_apply_coe (StdSimplex.homeomorphI.symm t)).symm.trans (by simp)
  linarith [StdSimplex.total_of_fintype (StdSimplex.homeomorphI.symm t),
    Fin.sum_univ_two (StdSimplex.homeomorphI.symm t).weights, hw₁]

/-- On `|X.op|`, the opposite of an edge `e : X.Edge x₀ x₁` traces the reversed path
`e.toTopPath.symm` under `toTopOpHomeomorph`. -/
lemma toTopOpHomeomorph_opEquiv_toTopPath_apply {x₀ x₁ : X _⦋0⦌} (e : X.Edge x₀ x₁)
    (t : unitInterval) :
    toTopOpHomeomorph X ((Edge.opEquiv e).toTopPath t) = e.toTopPath.symm t := by
  rw [Edge.toTopPath_apply]
  change toTopOpMap X (toTopObjMk (Edge.opEquiv e).edge (StdSimplex.homeomorphI.symm t)) = _
  rw [toTopOpMap_toTopObjMk, Edge.opEquiv_edge, Equiv.apply_symm_apply,
    stdSimplex_map_rev_homeomorphI_symm]; rfl

end SSet
