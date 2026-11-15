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

This file develops the simplex-level and functorial properties of geometric realization
`SSet.toTop : SSet ⥤ TopCat` beyond the adjunction and connected-component results in
`TauCeti/AlgebraicTopology/SimplicialSet/TopAdj.lean` and
`TauCeti/AlgebraicTopology/SimplicialSet/Realization/PiZero.lean`.

## Vertices, edges, and separation of low-dimensional simplices

* `SSet.toTopObjMk_eq_toTopPoint`, `SSet.toTop_map_const`: points of `0`-simplices and realizations
  of constant maps.
* `SSet.isEmpty_toTop_iff`, `SSet.exists_joined_toTopPoint`: `|X|` is empty exactly when `X` has no
  vertices, and every point of `|X|` is joined by a path to the point of a vertex.
* `SSet.toTopPoint_injective`, `SSet.toTopObjMk_one_injective`: distinct vertices give distinct
  points of `|X|`, and distinct `1`-simplices give distinct parametrized `1`-simplices in `|X|`.
  Both are proved directly from `sSetTopAdj` without CW-complex machinery: any function on vertices
  extends barycentrically to a continuous real-valued function on `|X|`, and any function on
  `1`-simplices vanishing on degenerate edges extends quadratically via
  `∑_{i ≤ j} wᵢ wⱼ h(σ|_{[i, j]})`.
* `SSet.Edge.toTopPath`, `SSet.Edge.CompStruct.toTopPath_homotopic`: an edge of `X` traces a path
  in `|X|` between its endpoints, degenerate edges trace reflexivity paths, and any `2`-simplex
  witnesses a path homotopy between its `1`-st face and the concatenation of its `2`-nd and `0`-th
  faces because the standard `2`-simplex is contractible and hence simply connected.

## Natural isomorphisms of geometric realization

* `SSet.constCompToTopIso`: the geometric realization of the discrete simplicial set on `ι` is the
  discrete topological space on `ι`.
* `SSet.uliftFunctorCompToTopIso` and `SSet.toTopUliftHomeomorph`: geometric realization commutes
  with universe lifting `SSet.uliftFunctor` and `TopCat.uliftFunctor`.
* `SSet.toTopOpIso` and `SSet.toTopOpHomeomorph`: the geometric realization `|X.op|` of the
  opposite simplicial set is naturally isomorphic to `|X|` by reversing barycentric coordinates,
  fixing vertices and reversing edge paths.

## References

* J. Milnor, *The geometric realization of a semi-simplicial complex*, Ann. of Math. 65 (1957),
  357–362.
* P. G. Goerss and J. F. Jardine, *Simplicial Homotopy Theory*, Progress in Mathematics 174,
  Birkhäuser, 1999, Sections I.2 and I.11.
-/

public section

open CategoryTheory Limits Opposite Simplicial Convexity

universe v u

namespace SSet

variable {X Y : SSet.{u}}

/-! ### Vertices, emptiness, and constant maps -/

/-- Evaluating the realization of a simplex morphism `Δ[n] ⟶ X` along `SimplexCategory.toTopHomeo`
produces `SSet.toTopObjMk`. -/
lemma toTop_map_yonedaEquiv_symm_toTopHomeo_symm {n : ℕ} (x : X _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    toTop.map (yonedaEquiv.symm x) ((⦋n⦌.toTopHomeo).symm w) = toTopObjMk x w := by
  have hunit := ConcreteCategory.congr_hom (sSetTopAdj_unit_app_app_down X (op ⦋n⦌) x)
    (ULift.up w)
  rw [toTopObjMk_def]
  exact hunit.symm

/-- For any coordinates on the standard `0`-simplex, `SSet.toTopObjMk x w` is `SSet.toTopPoint x`.
-/
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
  dsimp at y hy
  rw [Category.id_comp] at hy
  induction m using SimplexCategory.rec with | _ n =>
  let f' : Δ[n] ⟶ X := f
  let y' : |Δ[n]| := y
  refine ⟨n, yonedaEquiv f', ⦋n⦌.toTopHomeo y', ?_⟩
  rw [← toTop_map_yonedaEquiv_symm_toTopHomeo_symm, Equiv.symm_apply_apply,
    Homeomorph.symm_apply_apply]
  exact hy

/-- The geometric realization of a constant simplicial map is the constant continuous map at the
corresponding point. -/
@[simp]
lemma toTop_map_const (y : Y _⦋0⦌) (z : |X|) :
    toTop.map (SSet.const y) z = toTopPoint y := by
  obtain ⟨n, x, w, rfl⟩ := exists_toTopObjMk z
  rw [toTop_map_toTopObjMk, const_app, TypeCat.ofHom_apply, toTopObjMk_map,
    toTopObjMk_eq_toTopPoint]

/-- In `TopCat`, the geometric realization of `SSet.const y` is `TopCat.const (toTopPoint y)`. -/
lemma toTop_map_const_eq (y : Y _⦋0⦌) :
    toTop.map (SSet.const y : X ⟶ Y) = TopCat.const (toTopPoint y) := by
  ext z
  exact toTop_map_const y z

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

/-- Barycentric extension of a real-valued function on the vertices of `X` to a morphism into the
singular simplicial set of `ULift ℝ`. -/
private noncomputable def vertexExtension (g : X _⦋0⦌ → ℝ) :
    X ⟶ TopCat.toSSet.obj (TopCat.of (ULift.{u} ℝ)) where
  app n := ↾fun σ ↦ ((TopCat.of (ULift.{u} ℝ)).toSSetObjEquiv n).symm
    ⟨fun w ↦ ULift.up (∑ i : Fin (n.unop.len + 1),
        w.weights i * g (X.map (⦋0⦌.const n.unop i).op σ)),
      by fun_prop⟩
  naturality n m θ := by
    ext σ
    induction n using Opposite.rec with | op n
    induction m using Opposite.rec with | op m
    induction n using SimplexCategory.rec with | _ n
    induction m using SimplexCategory.rec with | _ m
    obtain ⟨θ, rfl⟩ : ∃ φ : ⦋m⦌ ⟶ ⦋n⦌, φ.op = θ := ⟨θ.unop, rfl⟩
    apply ((TopCat.of (ULift.{u} ℝ)).toSSetObjEquiv _).injective
    ext w : 1
    simp only [TypeCat.Fun.toFun_apply, ConcreteCategory.comp_apply]
    rw [TopCat.toSSetObjEquiv_naturality_apply]
    dsimp [SimplexCategory.len_mk]
    simp only [Equiv.apply_symm_apply, ContinuousMap.coe_mk]
    refine congrArg ULift.up ?_
    have hconst (j : Fin (m + 1)) : ⦋0⦌.const ⦋m⦌ j ≫ θ = ⦋0⦌.const ⦋n⦌ (θ j) := by
      ext k
      obtain rfl := Fin.eq_zero k
      rfl
    simp_rw [← Functor.map_comp_apply, ← op_comp, hconst]
    rw [← Finset.sum_fiberwise Finset.univ (fun j : Fin (m + 1) ↦ θ j)
      (fun j ↦ w.weights j * g (X.map (⦋0⦌.const ⦋n⦌ (θ j)).op σ))]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rw [StdSimplex.weights_map_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [(Finset.mem_filter.1 hj).2]

/-- Distinct vertices of a simplicial set map to distinct points of its geometric realization. -/
theorem toTopPoint_injective (X : SSet.{u}) : Function.Injective (toTopPoint (X := X)) := by
  classical
  intro x₁ x₂ h
  let g : X _⦋0⦌ → ℝ := fun y ↦ if y = x₁ then 1 else 0
  let F : |X| ⟶ TopCat.of (ULift.{u} ℝ) := (sSetTopAdj.homEquiv X _).symm (vertexExtension g)
  have eval (x : X _⦋0⦌) : (F (toTopPoint x)).down = g x := by
    have hw₀ : (StdSimplex.single (R := ℝ) (0 : Fin 1)).weights 0 = 1 := by
      have htot := StdSimplex.total_of_fintype (StdSimplex.single (R := ℝ) (0 : Fin 1))
      simpa only [Fin.sum_univ_one] using htot
    have hconst0 : ⦋0⦌.const ⦋0⦌ 0 = 𝟙 ⦋0⦌ := by
      ext k
      obtain rfl := Fin.eq_zero k
      rfl
    rw [← toTopObjMk_eq_toTopPoint x (StdSimplex.single 0), apply_toTopObjMk]
    simp only [F, Equiv.apply_symm_apply, vertexExtension, TypeCat.ofHom_apply]
    dsimp [SimplexCategory.len_mk]
    simp only [Fin.sum_univ_one, hw₀, one_mul, hconst0, op_id, CategoryTheory.Functor.map_id,
      CategoryTheory.id_apply]
  have h12 : g x₁ = g x₂ := by rw [← eval x₁, ← eval x₂, h]
  by_contra hne
  simp [g, Ne.symm hne] at h12

@[simp]
lemma toTopPoint_inj {x₁ x₂ : X _⦋0⦌} : toTopPoint x₁ = toTopPoint x₂ ↔ x₁ = x₂ :=
  (toTopPoint_injective X).eq_iff

/-- Quadratic extension of a real-valued function on `1`-simplices that vanishes on degenerate
`1`-simplices to a morphism into the singular simplicial set of `ULift ℝ`. -/
private noncomputable def edgeExtension (h : X _⦋1⦌ → ℝ) (hh : ∀ x : X _⦋0⦌, h (X.σ 0 x) = 0) :
    X ⟶ TopCat.toSSet.obj (TopCat.of (ULift.{u} ℝ)) where
  app n := ↾fun σ ↦ ((TopCat.of (ULift.{u} ℝ)).toSSetObjEquiv n).symm
    ⟨fun w ↦ ULift.up (∑ i : Fin (n.unop.len + 1), ∑ j : Fin (n.unop.len + 1),
        w.weights i * w.weights j *
          if hij : i ≤ j then h (X.map (SimplexCategory.mkOfLe i j hij).op σ) else 0),
      by fun_prop⟩
  naturality n m θ := by
    ext σ
    induction n using Opposite.rec with | op n
    induction m using Opposite.rec with | op m
    induction n using SimplexCategory.rec with | _ n
    induction m using SimplexCategory.rec with | _ m
    obtain ⟨θ, rfl⟩ : ∃ φ : ⦋m⦌ ⟶ ⦋n⦌, φ.op = θ := ⟨θ.unop, rfl⟩
    apply ((TopCat.of (ULift.{u} ℝ)).toSSetObjEquiv _).injective
    ext w : 1
    simp only [TypeCat.Fun.toFun_apply, ConcreteCategory.comp_apply]
    rw [TopCat.toSSetObjEquiv_naturality_apply]
    dsimp [SimplexCategory.len_mk]
    simp only [Equiv.apply_symm_apply, ContinuousMap.coe_mk]
    refine congrArg ULift.up ?_
    have hdiag (p : Fin (n + 1)) : h (X.map (SimplexCategory.mkOfLe p p le_rfl).op σ) = 0 := by
      have hmk : SimplexCategory.mkOfLe p p le_rfl = SimplexCategory.σ 0 ≫ ⦋0⦌.const ⦋n⦌ p := by
        ext k
        fin_cases k <;> rfl
      rw [hmk, op_comp, Functor.map_comp_apply]
      exact hh _
    -- Compare the bilinear forms term by term after expanding mapped weights over fibres.
    let c (p q : Fin (n + 1)) : ℝ :=
      if hpq : p ≤ q then h (X.map (SimplexCategory.mkOfLe p q hpq).op σ) else 0
    have hcoeff (a b : Fin (m + 1)) :
        (if hab : a ≤ b then h (X.map (SimplexCategory.mkOfLe a b hab).op (X.map θ.op σ))
          else 0) = c (θ a) (θ b) := by
      by_cases hab : a ≤ b
      · have hθ : θ a ≤ θ b := θ.toOrderHom.monotone hab
        have hcomp : SimplexCategory.mkOfLe a b hab ≫ θ =
            SimplexCategory.mkOfLe (θ a) (θ b) hθ := by
          ext k
          fin_cases k <;> rfl
        simp only [c, hab, hθ, ↓reduceDIte, ← Functor.map_comp_apply, ← op_comp, hcomp]
      · simp only [c, hab, ↓reduceDIte]
        split_ifs with hθ
        · have heq : θ a = θ b := le_antisymm hθ (θ.toOrderHom.monotone (le_of_not_ge hab))
          have hmk : SimplexCategory.mkOfLe (θ a) (θ b) hθ =
              SimplexCategory.mkOfLe (θ a) (θ a) le_rfl := by
            ext k
            fin_cases k <;> simp [SimplexCategory.mkOfLe, heq]
          rw [hmk, hdiag]
        · rfl
    have sum_map_weights (f : Fin (n + 1) → ℝ) :
        ∑ p : Fin (n + 1), (w.map θ).weights p * f p =
          ∑ a : Fin (m + 1), w.weights a * f (θ a) := by
      rw [← Finset.sum_fiberwise Finset.univ (fun a : Fin (m + 1) ↦ θ a)
        (fun a ↦ w.weights a * f (θ a))]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      rw [StdSimplex.weights_map_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a ha ↦ ?_
      rw [(Finset.mem_filter.1 ha).2]
    simp_rw [hcoeff]
    -- Unwrap `ULift.up` on both double sums before applying `sum_map_weights`.
    change (∑ a : Fin (m + 1), ∑ b : Fin (m + 1), w.weights a * w.weights b * c (θ a) (θ b)) =
      ∑ p : Fin (n + 1), ∑ q : Fin (n + 1), (w.map θ).weights p * (w.map θ).weights q * c p q
    simp_rw [mul_assoc, ← Finset.mul_sum]
    symm
    rw [sum_map_weights]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [sum_map_weights]

/-- The vertex `0` of the standard `1`-simplex maps to the `1`-st face of a `1`-simplex. -/
@[simp]
lemma toTopObjMk_single_zero (e : X _⦋1⦌) :
    toTopObjMk e (StdSimplex.single 0) = toTopPoint (X.δ 1 e) := by
  have hs : (StdSimplex.single 0 : StdSimplex ℝ (Fin 2)) =
      StdSimplex.map (SimplexCategory.δ 1) (StdSimplex.single 0) := by
    rw [StdSimplex.map_single]
    rfl
  rw [hs, ← toTopObjMk_map, toTopObjMk_eq_toTopPoint]
  rfl

/-- The vertex `1` of the standard `1`-simplex maps to the `0`-th face of a `1`-simplex. -/
@[simp]
lemma toTopObjMk_single_one (e : X _⦋1⦌) :
    toTopObjMk e (StdSimplex.single 1) = toTopPoint (X.δ 0 e) := by
  have hs : (StdSimplex.single 1 : StdSimplex ℝ (Fin 2)) =
      StdSimplex.map (SimplexCategory.δ 0) (StdSimplex.single 0) := by
    rw [StdSimplex.map_single]
    rfl
  rw [hs, ← toTopObjMk_map, toTopObjMk_eq_toTopPoint]
  rfl

/-- Evaluating `edgeExtension` at the midpoint of a `1`-simplex recovers `h e / 4`. -/
private lemma edgeExtension_midpoint {h : X _⦋1⦌ → ℝ} (hh : ∀ x : X _⦋0⦌, h (X.σ 0 x) = 0)
    (e : X _⦋1⦌) :
    (((sSetTopAdj.homEquiv X _).symm (edgeExtension h hh))
      (toTopObjMk e (StdSimplex.homeomorphI.symm ⟨1 / 2, by norm_num, by norm_num⟩))).down =
      h e / 4 := by
  let t : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  let w : StdSimplex ℝ (Fin 2) := StdSimplex.homeomorphI.symm t
  have hw₁ : w.weights 1 = 1 / 2 := by
    simpa [w, t] using (StdSimplex.homeomorphI_apply_coe w).symm
  have hw₀ : w.weights 0 = 1 / 2 := by
    have := StdSimplex.total_of_fintype w
    rw [Fin.sum_univ_two, hw₁] at this
    linarith
  have hdiag (p : Fin 2) : h (X.map (SimplexCategory.mkOfLe p p le_rfl).op e) = 0 := by
    have hmk : SimplexCategory.mkOfLe p p le_rfl = SimplexCategory.σ 0 ≫ ⦋0⦌.const ⦋1⦌ p := by
      ext k
      fin_cases k <;> rfl
    rw [hmk, op_comp, Functor.map_comp_apply]
    exact hh _
  have hid : SimplexCategory.mkOfLe (0 : Fin 2) 1 (by decide) = 𝟙 ⦋1⦌ := by
    ext k
    fin_cases k <;> rfl
  rw [apply_toTopObjMk]
  simp only [Equiv.apply_symm_apply, edgeExtension, TypeCat.ofHom_apply]
  dsimp [SimplexCategory.len_mk]
  have h01 : (0 : Fin 2) ≤ 1 := by decide
  have h10 : ¬ ((1 : Fin 2) ≤ 0) := by decide
  simp only [Fin.sum_univ_two, le_refl, ↓reduceDIte, hdiag, mul_zero, zero_add, add_zero,
    h01, h10, hid, op_id, CategoryTheory.Functor.map_id, CategoryTheory.id_apply]
  -- Reduce `ULift.down (ULift.up _)` to the underlying real product.
  change w.weights 0 * w.weights 1 * h e = h e / 4
  rw [hw₀, hw₁]
  ring

/-- Distinct `1`-simplices of `X` determine distinct parametrized simplices in `|X|`. -/
theorem toTopObjMk_one_injective (X : SSet.{u}) :
    Function.Injective (fun e : X _⦋1⦌ ↦ toTopObjMk e) := by
  classical
  have sep {e₁ e₂ : X _⦋1⦌} (he₁ : e₁ ∉ Set.range (X.σ 0))
      (heq : toTopObjMk e₁ = toTopObjMk e₂) : e₁ = e₂ := by
    let h : X _⦋1⦌ → ℝ := fun e ↦ if e = e₁ then 1 else 0
    have hh (x : X _⦋0⦌) : h (X.σ 0 x) = 0 := by
      simp only [h, ite_eq_right_iff]
      exact fun hx ↦ absurd ⟨x, hx⟩ he₁
    have hm := edgeExtension_midpoint hh e₁
    rw [heq, edgeExtension_midpoint hh e₂] at hm
    by_contra hne
    simp [h, Ne.symm hne] at hm
  intro e₁ e₂ heq
  by_cases h₁ : e₁ ∈ Set.range (X.σ 0)
  · by_cases h₂ : e₂ ∈ Set.range (X.σ 0)
    · obtain ⟨x₁, rfl⟩ := h₁
      obtain ⟨x₂, rfl⟩ := h₂
      have hv : toTopObjMk (X.σ 0 x₁) (StdSimplex.single 1) =
          toTopObjMk (X.σ 0 x₂) (StdSimplex.single 1) := congrFun heq (StdSimplex.single 1)
      have h0 : (0 : Fin 2) = Fin.castSucc 0 := rfl
      rw [toTopObjMk_single_one, toTopObjMk_single_one, toTopPoint_inj, h0,
        δ_comp_σ_self_apply, δ_comp_σ_self_apply] at hv
      exact congrArg _ hv
    · exact (sep h₂ heq.symm).symm
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
    e.toTopPath t = toTopObjMk e.edge (StdSimplex.homeomorphI.symm t) :=
  (rfl)

/-- A degenerate edge traces the constant path at its vertex. -/
@[simp]
lemma toTopPath_id (x : X _⦋0⦌) : (Edge.id x).toTopPath = _root_.Path.refl (toTopPoint x) := by
  ext t
  -- Unfold `toTopPath` on `Edge.id x` to `toTopObjMk (X.σ 0 x) _` before factoring `σ 0`.
  change toTopObjMk (X.σ 0 x) _ = toTopPoint x
  rw [SimplicialObject.σ, toTopObjMk_map, toTopObjMk_eq_toTopPoint]

/-- Mapping an edge path along `|f|` gives the edge path of the mapped edge. -/
lemma toTop_map_toTopPath_apply (f : X ⟶ Y) (e : X.Edge x₀ x₁) (t : I) :
    toTop.map f (e.toTopPath t) = (e.map f).toTopPath t := by
  simp

/-- The `j`-th face of the standard `2`-simplex as a path between the specified vertices. -/
private noncomputable def stdSimplex₂FacePath {a b : Fin 3} (j : Fin 3)
    (ha : j.succAbove 0 = a) (hb : j.succAbove 1 = b) :
    _root_.Path (StdSimplex.single (R := ℝ) a) (StdSimplex.single b) where
  toContinuousMap :=
    (⟨StdSimplex.map j.succAbove, StdSimplex.continuous_map ℝ j.succAbove⟩ :
      C(StdSimplex ℝ (Fin 2), StdSimplex ℝ (Fin 3))).comp
      (StdSimplex.homeomorphI.symm : C(I, StdSimplex ℝ (Fin 2)))
  source' := by simp [StdSimplex.map_single, ha]
  target' := by simp [StdSimplex.map_single, hb]

/-- A `2`-simplex `CompStruct e₀₁ e₁₂ e₀₂` in `X` witnesses a homotopy in `|X|` between the edge
path of `e₀₂` and the concatenation of the edge paths of `e₀₁` and `e₁₂`. -/
theorem CompStruct.toTopPath_homotopic {e₀₁ : X.Edge x₀ x₁} {e₁₂ : X.Edge x₁ x₂}
    {e₀₂ : X.Edge x₀ x₂} (h : CompStruct e₀₁ e₁₂ e₀₂) :
    e₀₂.toTopPath.Homotopic (e₀₁.toTopPath.trans e₁₂.toTopPath) := by
  -- Inside the contractible (hence simply connected) standard `2`-simplex, the `1`-st face path is
  -- homotopic to the concatenation of the `2`-nd and `0`-th face paths.
  let p₀₂ := stdSimplex₂FacePath (a := 0) (b := 2) 1 (by decide) (by decide)
  let p₀₁ := stdSimplex₂FacePath (a := 0) (b := 1) 2 (by decide) (by decide)
  let p₁₂ := stdSimplex₂FacePath (a := 1) (b := 2) 0 (by decide) (by decide)
  have hstd : p₀₂.Homotopic (p₀₁.trans p₁₂) :=
    SimplyConnectedSpace.paths_homotopic (X := StdSimplex ℝ (Fin 3)) _ _
  let σMap : C(StdSimplex ℝ (Fin 3), |X|) := ⟨toTopObjMk h.simplex, continuous_toTopObjMk h.simplex⟩
  have hmap := hstd.map σMap
  rw [_root_.Path.map_trans] at hmap
  have hp {y₀ y₁ : X _⦋0⦌} {a b : Fin 3} (j : Fin 3) (ha : j.succAbove 0 = a)
      (hb : j.succAbove 1 = b) (e : X.Edge y₀ y₁) (hd : X.δ j h.simplex = e.edge) :
      ∃ hs ht, ((stdSimplex₂FacePath j ha hb).map σMap.continuous).cast hs ht = e.toTopPath := by
    have hpt (t : I) :
        ((stdSimplex₂FacePath j ha hb).map σMap.continuous) t = e.toTopPath t := by
      -- Unfold the mapped face path to `toTopObjMk h.simplex (StdSimplex.map j.succAbove _)`.
      change toTopObjMk h.simplex (StdSimplex.map j.succAbove (StdSimplex.homeomorphI.symm t)) = _
      rw [← SimplexCategory.coe_δ, ← toTopObjMk_map, ← SimplicialObject.δ, hd, toTopPath_apply]
    refine ⟨(e.toTopPath.source.symm.trans (hpt 0).symm).trans (_root_.Path.source _),
      (e.toTopPath.target.symm.trans (hpt 1).symm).trans (_root_.Path.target _), ?_⟩
    ext t
    exact hpt t
  obtain ⟨hs₁, ht₁, he₁⟩ := hp (a := 0) (b := 2) 1 (by decide) (by decide) e₀₂ h.d₁
  obtain ⟨hs₂, ht₂, he₂⟩ := hp (a := 0) (b := 1) 2 (by decide) (by decide) e₀₁ h.d₂
  obtain ⟨hs₀, ht₀, he₀⟩ := hp (a := 1) (b := 2) 0 (by decide) (by decide) e₁₂ h.d₀
  have hcast := hmap.pathCast hs₁ ht₁
  rw [he₁] at hcast
  have htrans :
      (((stdSimplex₂FacePath (a := 0) (b := 1) 2 (by decide) (by decide)).map
          σMap.continuous).trans
        ((stdSimplex₂FacePath (a := 1) (b := 2) 0 (by decide) (by decide)).map
          σMap.continuous)).cast hs₁ ht₁ =
      e₀₁.toTopPath.trans e₁₂.toTopPath := by
    ext t
    simp only [_root_.Path.cast_coe, _root_.Path.trans_apply]
    split_ifs with ht
    · exact congrFun (congrArg DFunLike.coe he₂) ⟨2 * t,
        (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, ht⟩⟩
    · exact congrFun (congrArg DFunLike.coe he₀) ⟨2 * t - 1,
        unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 ht).le, t.2.2⟩⟩
  rwa [htrans] at hcast

end Edge

/-! ### Realization of discrete simplicial sets -/

private noncomputable def constToTopHom (ι : Type u) :
    |((Functor.const SimplexCategoryᵒᵖ : Type u ⥤ SSet.{u}).obj ι)| ⟶ TopCat.discrete.obj ι :=
  (sSetTopAdj.homEquiv ((Functor.const SimplexCategoryᵒᵖ).obj ι) (TopCat.discrete.obj ι)).symm
    ((constHomEquiv ι).symm fun i ↦
      (TopCat.discrete.obj ι).toSSetObj₀Equiv.symm (show TopCat.discrete.obj ι from i))

private noncomputable def constToTopInv (ι : Type u) :
    TopCat.discrete.obj ι ⟶ |((Functor.const SimplexCategoryᵒᵖ : Type u ⥤ SSet.{u}).obj ι)| :=
  ConcreteCategory.ofHom
    ⟨fun x ↦ toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj ι)
        (show ((Functor.const SimplexCategoryᵒᵖ).obj ι) _⦋0⦌ from x),
      continuous_of_discreteTopology⟩

private lemma constToTopHom_toTopPoint (ι : Type u)
    (j : ((Functor.const SimplexCategoryᵒᵖ : Type u ⥤ SSet.{u}).obj ι) _⦋0⦌) :
    constToTopHom ι (toTopPoint j) = (show TopCat.discrete.obj ι from j) := by
  rw [constToTopHom, ← toTopObjMk_eq_toTopPoint j (StdSimplex.single 0), apply_toTopObjMk,
    Equiv.apply_symm_apply]
  have happ := constHomEquiv_symm_app_zero (X := TopCat.toSSet.obj (TopCat.discrete.obj ι)) ι
    (fun i ↦ (TopCat.discrete.obj ι).toSSetObj₀Equiv.symm (show TopCat.discrete.obj ι from i)) j
  rw [happ, TopCat.toSSetObj₀Equiv_symm_apply, Equiv.apply_symm_apply]
  rfl

private lemma constToTopInv_apply (ι : Type u) (x : TopCat.discrete.obj ι) :
    constToTopInv ι x =
      toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj ι)
        (show ((Functor.const SimplexCategoryᵒᵖ).obj ι) _⦋0⦌ from x) :=
  rfl

/-- The natural isomorphism `|(Functor.const _).obj ι| ≅ TopCat.discrete.obj ι` identifying the
geometric realization of the discrete simplicial set on `ι` with the discrete space on `ι`. -/
noncomputable def constCompToTopIso :
    (Functor.const SimplexCategoryᵒᵖ : Type u ⥤ SSet.{u}) ⋙ SSet.toTop.{u} ≅ TopCat.discrete.{u} :=
  (NatIso.ofComponents
    (fun (ι : Type u) ↦
      { hom := constToTopInv ι
        inv := constToTopHom ι
        hom_inv_id := by
          ext x
          rw [ConcreteCategory.comp_apply, CategoryTheory.id_apply, constToTopInv_apply,
            constToTopHom_toTopPoint]
        inv_hom_id := toTop_hom_ext fun n i w ↦ by
          let j : ((Functor.const SimplexCategoryᵒᵖ : Type u ⥤ SSet.{u}).obj ι) _⦋0⦌ := i
          have hi : toTopObjMk (X := (Functor.const SimplexCategoryᵒᵖ).obj ι) i w =
              toTopPoint j := by
            conv_lhs =>
              rw [show i = ((Functor.const SimplexCategoryᵒᵖ).obj ι).map (⦋n⦌.const ⦋0⦌ 0).op j
                from rfl]
            rw [toTopObjMk_map, toTopObjMk_eq_toTopPoint]
          dsimp only [Functor.comp_obj]
          rw [hi, ConcreteCategory.comp_apply, CategoryTheory.id_apply, constToTopHom_toTopPoint,
            constToTopInv_apply] })
    (fun {ι₁ ι₂} f ↦ by
      ext x
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
      dsimp only [Functor.comp_map]
      rw [constToTopInv_apply]
      exact (toTop_map_toTopPoint ((Functor.const SimplexCategoryᵒᵖ).map f)
        (show ((Functor.const SimplexCategoryᵒᵖ).obj ι₁) _⦋0⦌ from x)).symm)).symm

@[simp]
lemma constCompToTopIso_inv_app_apply (ι : Type u) (i : ι) :
    dsimp% (constCompToTopIso.inv.app ι) (i : TopCat.discrete.obj ι) =
      toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj ι) i :=
  constToTopInv_apply ι (i : TopCat.discrete.obj ι)

@[simp]
lemma constCompToTopIso_hom_app_toTopPoint (ι : Type u) (i : ι) :
    dsimp% (constCompToTopIso.hom.app ι)
        (toTopPoint (X := (Functor.const SimplexCategoryᵒᵖ).obj ι) i) =
      (i : TopCat.discrete.obj ι) := by
  have h := Iso.inv_hom_id_app_apply constCompToTopIso ι (i : TopCat.discrete.obj ι)
  rwa [constCompToTopIso_inv_app_apply] at h

/-! ### Realization of universe lifts -/

/-- The map `|uliftFunctor.obj X| ⟶ TopCat.uliftFunctor.obj |X|` adjoint to `toTopObjMk` on `X`. -/
private noncomputable def uliftToTopHom (X : SSet.{u}) :
    |SSet.uliftFunctor.{v, u}.obj X| ⟶ TopCat.uliftFunctor.{v, u}.obj |X| :=
  (sSetTopAdj.homEquiv _ _).symm
    { app n := ↾fun x ↦ ((TopCat.uliftFunctor.{v, u}.obj |X|).toSSetObjEquiv n).symm
        ((|X|.uliftFunctorObjHomeo : C(|X|, _)).comp
          ⟨toTopObjMk x.down, continuous_toTopObjMk x.down⟩)
      naturality n m θ := by
        ext x
        induction n using Opposite.rec with | op n
        induction m using Opposite.rec with | op m
        induction n using SimplexCategory.rec with | _ n
        induction m using SimplexCategory.rec with | _ m
        obtain ⟨θ, rfl⟩ : ∃ φ : ⦋m⦌ ⟶ ⦋n⦌, φ.op = θ := ⟨θ.unop, rfl⟩
        apply ((TopCat.uliftFunctor.{v, u}.obj |X|).toSSetObjEquiv _).injective
        ext w : 1
        simp only [TypeCat.Fun.toFun_apply, ConcreteCategory.comp_apply]
        rw [TopCat.toSSetObjEquiv_naturality_apply]
        dsimp [SimplexCategory.len_mk]
        simp only [Equiv.apply_symm_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
        exact congrArg |X|.uliftFunctorObjHomeo (toTopObjMk_map θ x.down w) }

private lemma uliftToTopHom_toTopObjMk (X : SSet.{u}) {n : ℕ}
    (x : (SSet.uliftFunctor.{v, u}.obj X) _⦋n⦌) (w : StdSimplex ℝ (Fin (n + 1))) :
    uliftToTopHom.{v, u} X (toTopObjMk x w) = |X|.uliftFunctorObjHomeo (toTopObjMk x.down w) := by
  rw [uliftToTopHom, apply_toTopObjMk, Equiv.apply_symm_apply]
  rfl

private noncomputable def uliftYonedaToTopHomeo (m : SimplexCategory) :
    |uliftYoneda.{u}.obj m| ≃ₜ StdSimplex ℝ (Fin (m.len + 1)) :=
  m.toTopHomeo

private lemma uliftYonedaToTopHomeo_naturality {m₁ m₂ : SimplexCategory} (g : m₁ ⟶ m₂)
    (y : |uliftYoneda.{u}.obj m₁|) :
    uliftYonedaToTopHomeo.{u} m₂ (toTop.map (uliftYoneda.{u}.map g) y) =
      StdSimplex.map g (uliftYonedaToTopHomeo.{u} m₁ y) :=
  SimplexCategory.toTopHomeo_naturality_apply g y

private lemma toTop_map_uliftYoneda_symm {X : SSet.{u}} {n : ℕ} (x : X _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    toTop.map (show uliftYoneda.{u}.obj ⦋n⦌ ⟶ X from yonedaEquiv.symm x)
        ((uliftYonedaToTopHomeo.{u} ⦋n⦌).symm w) = toTopObjMk x w :=
  toTop_map_yonedaEquiv_symm_toTopHomeo_symm x w

private def costructuredArrowHom {X : SSet.{u}} (j : CostructuredArrow uliftYoneda.{u} X) :
    Δ[j.left.len] ⟶ X :=
  j.hom

private def costructuredArrowSimplex {X : SSet.{u}} (j : CostructuredArrow uliftYoneda.{u} X) :
    (SSet.uliftFunctor.{v, u}.obj X) _⦋j.left.len⦌ :=
  ULift.up (yonedaEquiv (costructuredArrowHom j))

private lemma costructuredArrowHom_w {X : SSet.{u}}
    {j₁ j₂ : CostructuredArrow uliftYoneda.{u} X} (g : j₁ ⟶ j₂) :
    SSet.stdSimplex.map (show ⦋j₁.left.len⦌ ⟶ ⦋j₂.left.len⦌ from g.left) ≫
      costructuredArrowHom j₂ = costructuredArrowHom j₁ :=
  CostructuredArrow.w g

private lemma costructuredArrowSimplex_naturality {X : SSet.{u}}
    {j₁ j₂ : CostructuredArrow uliftYoneda.{u} X} (g : j₁ ⟶ j₂) :
    (SSet.uliftFunctor.{v, u}.obj X).map (show ⦋j₁.left.len⦌ ⟶ ⦋j₂.left.len⦌ from g.left).op
        (costructuredArrowSimplex.{v, u} j₂) =
      costructuredArrowSimplex.{v, u} j₁ := by
  have hyon := SSet.yonedaEquiv_naturality
    (show ⦋j₁.left.len⦌ ⟶ ⦋j₂.left.len⦌ from g.left) (costructuredArrowHom j₂)
  rw [costructuredArrowHom_w] at hyon
  exact congrArg ULift.up hyon

private lemma costructuredArrowSimplex_mk {X : SSet.{u}} {n : ℕ} (x : X _⦋n⦌) :
    costructuredArrowSimplex.{v, u}
        (CostructuredArrow.mk (show uliftYoneda.{u}.obj ⦋n⦌ ⟶ X from yonedaEquiv.symm x)) =
      ULift.up x := by
  have hhom : costructuredArrowHom
      (CostructuredArrow.mk (show uliftYoneda.{u}.obj ⦋n⦌ ⟶ X from yonedaEquiv.symm x)) =
      yonedaEquiv.symm x := rfl
  exact congrArg ULift.up ((congrArg yonedaEquiv hhom).trans (Equiv.apply_symm_apply _ _))

private noncomputable def uliftToTopCoconeApp (X : SSet.{u})
    (j : CostructuredArrow uliftYoneda.{u} X) :
    TopCat.uliftFunctor.{v, u}.obj |uliftYoneda.{u}.obj j.left| ⟶
      |SSet.uliftFunctor.{v, u}.obj X| :=
  ConcreteCategory.ofHom
    ((⟨toTopObjMk (costructuredArrowSimplex.{v, u} j), continuous_toTopObjMk _⟩ :
        C(StdSimplex ℝ (Fin (j.left.len + 1)), |SSet.uliftFunctor.{v, u}.obj X|)).comp
      ((uliftYonedaToTopHomeo.{u} j.left : C(|uliftYoneda.{u}.obj j.left|, _)).comp
        (|uliftYoneda.{u}.obj j.left|.uliftFunctorObjHomeo.symm :
          C(TopCat.uliftFunctor.{v, u}.obj |uliftYoneda.{u}.obj j.left|,
            |uliftYoneda.{u}.obj j.left|))))

private lemma uliftToTopCoconeApp_apply (X : SSet.{u})
    (j : CostructuredArrow uliftYoneda.{u} X) (y : |uliftYoneda.{u}.obj j.left|) :
    uliftToTopCoconeApp.{v, u} X j (|uliftYoneda.{u}.obj j.left|.uliftFunctorObjHomeo.{v, u} y) =
      toTopObjMk (costructuredArrowSimplex.{v, u} j) (uliftYonedaToTopHomeo.{u} j.left y) :=
  congrArg (fun z ↦ toTopObjMk (costructuredArrowSimplex.{v, u} j)
    (uliftYonedaToTopHomeo.{u} j.left z))
    (Homeomorph.symm_apply_apply |uliftYoneda.{u}.obj j.left|.uliftFunctorObjHomeo.{v, u} y)

/-- Cocone sending the lifted realization of each simplex of `X` into `|uliftFunctor.obj X|`. -/
private noncomputable def uliftToTopCocone (X : SSet.{u}) :
    Cocone (CostructuredArrow.proj uliftYoneda.{u} X ⋙
      uliftYoneda.{u} ⋙ SSet.toTop.{u} ⋙ TopCat.uliftFunctor.{v, u}) where
  pt := |SSet.uliftFunctor.{v, u}.obj X|
  ι :=
    { app j := uliftToTopCoconeApp.{v, u} X j
      naturality j₁ j₂ g := by
        ext z
        dsimp only [Functor.const_obj_obj, Functor.const_obj_map, Functor.comp_obj,
          Functor.comp_map, CostructuredArrow.proj_obj, CostructuredArrow.proj_map]
        rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, CategoryTheory.id_apply]
        obtain ⟨y, rfl⟩ := |uliftYoneda.{u}.obj j₁.left|.uliftFunctorObjHomeo.surjective z
        rw [TopCat.uliftFunctorObjHomeo_naturality_apply, uliftToTopCoconeApp_apply,
          uliftToTopCoconeApp_apply, uliftYonedaToTopHomeo_naturality]
        have hmap := toTopObjMk_map (X := SSet.uliftFunctor.{v, u}.obj X)
          (show ⦋j₁.left.len⦌ ⟶ ⦋j₂.left.len⦌ from g.left)
          (costructuredArrowSimplex.{v, u} j₂) (uliftYonedaToTopHomeo.{u} j₁.left y)
        exact hmap.symm.trans (by rw [costructuredArrowSimplex_naturality]) }

/-- The inverse map `TopCat.uliftFunctor.obj |X| ⟶ |uliftFunctor.obj X|` obtained from the
colimit presentation `denseAtUliftYoneda X` preserved by `toTop ⋙ TopCat.uliftFunctor`. -/
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
  have hlhs :
      ((toTop.{u} ⋙ TopCat.uliftFunctor.{v, u}).mapCocone
        ((Functor.LeftExtension.mk _ uliftYoneda.{u}.rightUnitor.inv).coconeAt X)).ι.app j
        (|uliftYoneda.{u}.obj j.left|.uliftFunctorObjHomeo y) =
      |X|.uliftFunctorObjHomeo (toTopObjMk x w) := by
    dsimp [j]
    exact congrArg |X|.uliftFunctorObjHomeo (toTop_map_uliftYoneda_symm x w)
  have hrhs : (uliftToTopCocone.{v, u} X).ι.app j
      (|uliftYoneda.{u}.obj j.left|.uliftFunctorObjHomeo y) =
      toTopObjMk (X := SSet.uliftFunctor.{v, u}.obj X) (ULift.up x) w := by
    refine (uliftToTopCoconeApp_apply X j y).trans ?_
    rw [show uliftYonedaToTopHomeo.{u} j.left y = w from Homeomorph.apply_symm_apply _ w,
      costructuredArrowSimplex_mk]
  rw [← hlhs, ← hrhs]
  exact hfac

/-- Geometric realization commutes up to natural isomorphism with universe lifting of simplicial
sets and topological spaces. -/
noncomputable def uliftFunctorCompToTopIso :
    SSet.uliftFunctor.{v, u} ⋙ SSet.toTop ≅ SSet.toTop ⋙ TopCat.uliftFunctor.{v, u} :=
  NatIso.ofComponents
    (fun X ↦
      { hom := uliftToTopHom.{v, u} X
        inv := uliftToTopInv.{v, u} X
        hom_inv_id := toTop_hom_ext fun n x w ↦ by
          rw [ConcreteCategory.comp_apply, uliftToTopHom_toTopObjMk, uliftToTopInv_apply]
          rfl
        inv_hom_id := by
          ext z
          obtain ⟨y, rfl⟩ := |X|.uliftFunctorObjHomeo.surjective z
          obtain ⟨n, x, w, rfl⟩ := exists_toTopObjMk y
          let ux : (SSet.uliftFunctor.{v, u}.obj X) _⦋n⦌ := ULift.up x
          rw [ConcreteCategory.comp_apply, uliftToTopInv_apply]
          exact uliftToTopHom_toTopObjMk X ux w })
    (fun {X Y} f ↦ toTop_hom_ext fun n x w ↦ by
      simp only [Functor.comp_obj, Functor.comp_map, ConcreteCategory.comp_apply,
        toTop_map_toTopObjMk, uliftToTopHom_toTopObjMk,
        TopCat.uliftFunctorObjHomeo_naturality_apply]
      rfl)

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
  simp only [toTop_map_toTopObjMk, toTopUliftHomeomorph_toTopObjMk]
  rfl

/-! ### Realization of opposite simplicial sets -/

/-- The map `|X.op| ⟶ |X|` reversing barycentric coordinates on each simplex. -/
private noncomputable def toTopOpMap (X : SSet.{u}) : |X.op| ⟶ |X| :=
  (sSetTopAdj.homEquiv X.op |X|).symm
    { app n := ↾fun y ↦ (|X|.toSSetObjEquiv n).symm
        ((⟨toTopObjMk (X.opObjEquiv y), continuous_toTopObjMk _⟩ : C(_, |X|)).comp
          ⟨StdSimplex.map Fin.rev, StdSimplex.continuous_map ℝ Fin.rev⟩)
      naturality n m θ := by
        ext y
        induction n using Opposite.rec with | op n
        induction m using Opposite.rec with | op m
        induction n using SimplexCategory.rec with | _ n
        induction m using SimplexCategory.rec with | _ m
        obtain ⟨θ, rfl⟩ : ∃ φ : ⦋m⦌ ⟶ ⦋n⦌, φ.op = θ := ⟨θ.unop, rfl⟩
        apply (|X|.toSSetObjEquiv _).injective
        ext w : 1
        simp only [TypeCat.Fun.toFun_apply, ConcreteCategory.comp_apply]
        rw [TopCat.toSSetObjEquiv_naturality_apply]
        dsimp [SimplexCategory.len_mk]
        simp only [Equiv.apply_symm_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
        rw [X.op_map, Equiv.apply_symm_apply, toTopObjMk_map, StdSimplex.map_map,
          StdSimplex.map_map]
        refine congrArg (toTopObjMk (X.opObjEquiv y)) (congrArg (StdSimplex.map · w) ?_)
        funext i
        exact (SimplexCategory.rev_map_apply θ i.rev).trans
          (congrArg Fin.rev (congrArg θ (Fin.rev_rev i))) }

/-- The inverse map `|X| ⟶ |X.op|` reversing barycentric coordinates on each simplex. -/
private noncomputable def toTopOpMapInv (X : SSet.{u}) : |X| ⟶ |X.op| :=
  (sSetTopAdj.homEquiv X |X.op|).symm
    { app n := ↾fun x ↦ (|X.op|.toSSetObjEquiv n).symm
        ((⟨toTopObjMk (X.opObjEquiv.symm x), continuous_toTopObjMk _⟩ : C(_, |X.op|)).comp
          ⟨StdSimplex.map Fin.rev, StdSimplex.continuous_map ℝ Fin.rev⟩)
      naturality n m θ := by
        ext x
        induction n using Opposite.rec with | op n
        induction m using Opposite.rec with | op m
        induction n using SimplexCategory.rec with | _ n
        induction m using SimplexCategory.rec with | _ m
        obtain ⟨θ, rfl⟩ : ∃ φ : ⦋m⦌ ⟶ ⦋n⦌, φ.op = θ := ⟨θ.unop, rfl⟩
        apply (|X.op|.toSSetObjEquiv _).injective
        ext w : 1
        simp only [TypeCat.Fun.toFun_apply, ConcreteCategory.comp_apply]
        rw [TopCat.toSSetObjEquiv_naturality_apply]
        dsimp [SimplexCategory.len_mk]
        simp only [Equiv.apply_symm_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
        have hop : X.opObjEquiv.symm (X.map θ.op x) =
            X.op.map (SimplexCategory.rev.map θ).op (X.opObjEquiv.symm x) := by
          rw [X.op_map, Equiv.apply_symm_apply,
            show SimplexCategory.rev.map (SimplexCategory.rev.map θ).op.unop = θ from
              SimplexCategory.rev_map_rev_map θ]
        rw [hop, toTopObjMk_map, StdSimplex.map_map, StdSimplex.map_map]
        refine congrArg (toTopObjMk (X.opObjEquiv.symm x)) (congrArg (StdSimplex.map · w) ?_)
        funext i
        exact (SimplexCategory.rev_map_apply θ i.rev).trans
          (congrArg Fin.rev (congrArg θ (Fin.rev_rev i))) }

private lemma toTopOpMap_toTopObjMk (X : SSet.{u}) {n : ℕ} (y : X.op _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    toTopOpMap X (toTopObjMk y w) = toTopObjMk (X.opObjEquiv y) (StdSimplex.map Fin.rev w) := by
  rw [toTopOpMap, apply_toTopObjMk, Equiv.apply_symm_apply]
  rfl

private lemma toTopOpMapInv_toTopObjMk (X : SSet.{u}) {n : ℕ} (x : X _⦋n⦌)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    toTopOpMapInv X (toTopObjMk x w) =
      toTopObjMk (X.opObjEquiv.symm x) (StdSimplex.map Fin.rev w) := by
  rw [toTopOpMapInv, apply_toTopObjMk, Equiv.apply_symm_apply]
  rfl

/-- The geometric realization of the opposite of a simplicial set is naturally isomorphic to its
geometric realization, acting on each simplex by reversing barycentric coordinates. -/
noncomputable def toTopOpIso : SSet.opFunctor.{u} ⋙ SSet.toTop ≅ SSet.toTop :=
  NatIso.ofComponents
    (fun X ↦
      { hom := toTopOpMap X
        inv := toTopOpMapInv X
        hom_inv_id := toTop_hom_ext fun n y w ↦ by
          have hrev : StdSimplex.map (Fin.rev : Fin (n + 1) → Fin (n + 1))
              (StdSimplex.map Fin.rev w) = w := by
            rw [← StdSimplex.map_comp, show (Fin.rev : Fin (n + 1) → _) ∘ Fin.rev = id from
              funext Fin.rev_rev, StdSimplex.map_id]
          dsimp only [Functor.comp_obj]
          rw [ConcreteCategory.comp_apply, toTopOpMap_toTopObjMk, toTopOpMapInv_toTopObjMk,
            Equiv.symm_apply_apply, hrev, CategoryTheory.id_apply]
        inv_hom_id := toTop_hom_ext fun n x w ↦ by
          have hrev : StdSimplex.map (Fin.rev : Fin (n + 1) → Fin (n + 1))
              (StdSimplex.map Fin.rev w) = w := by
            rw [← StdSimplex.map_comp, show (Fin.rev : Fin (n + 1) → _) ∘ Fin.rev = id from
              funext Fin.rev_rev, StdSimplex.map_id]
          rw [ConcreteCategory.comp_apply, toTopOpMapInv_toTopObjMk, toTopOpMap_toTopObjMk,
            Equiv.apply_symm_apply, hrev, CategoryTheory.id_apply] })
    (fun {X Y} f ↦ toTop_hom_ext fun n y w ↦ by
      simp only [Functor.comp_obj, Functor.comp_map, ConcreteCategory.comp_apply,
        toTop_map_toTopObjMk, toTopOpMap_toTopObjMk, opFunctor_map, Equiv.apply_symm_apply])

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
  apply StdSimplex.homeomorphI.injective
  ext
  rw [StdSimplex.homeomorphI_apply_coe, Homeomorph.apply_symm_apply, unitInterval.coe_symm_eq]
  have hrev : (1 : Fin 2) = Fin.rev 0 := rfl
  rw [hrev, StdSimplex.weights_map_apply_of_injective Fin.rev_injective]
  have htot := StdSimplex.total_of_fintype (StdSimplex.homeomorphI.symm t)
  have hw₁ : (StdSimplex.homeomorphI.symm t).weights 1 = (t : ℝ) :=
    (StdSimplex.homeomorphI_apply_coe (StdSimplex.homeomorphI.symm t)).symm.trans (by simp)
  rw [Fin.sum_univ_two, hw₁] at htot
  linarith

/-- On `|X.op|`, the opposite of an edge `e : X.Edge x₀ x₁` traces the reversed path
`e.toTopPath.symm` under `toTopOpHomeomorph`. -/
lemma toTopOpHomeomorph_opEquiv_toTopPath_apply {x₀ x₁ : X _⦋0⦌} (e : X.Edge x₀ x₁)
    (t : unitInterval) :
    toTopOpHomeomorph X ((Edge.opEquiv e).toTopPath t) = e.toTopPath.symm t := by
  rw [Edge.toTopPath_apply]
  -- Unfold `toTopOpHomeomorph` on `|X.op|` to its underlying map `toTopOpMap X`.
  change toTopOpMap X (toTopObjMk (Edge.opEquiv e).edge (StdSimplex.homeomorphI.symm t)) = _
  rw [toTopOpMap_toTopObjMk, Edge.opEquiv_edge, Equiv.apply_symm_apply,
    stdSimplex_map_rev_homeomorphI_symm]
  rfl

end SSet
