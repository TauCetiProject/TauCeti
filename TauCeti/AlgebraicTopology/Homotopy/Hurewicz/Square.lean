/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.Sphere
public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic
public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.Topology.Homotopy.GenLoop.Map
public import TauCeti.Geometry.Convex.ConvexSpace.Defs

/-!
# Hurewicz classes of squares as triangulated cycles

A generalized loop `p : I² → X` at `x` sends the boundary of the unit square to `x`. Cutting the
square along its diagonal into the two affine triangles with vertices `(0, 0), (1, 0), (1, 1)` and
`(0, 0), (1, 1), (0, 1)` gives two singular `2`-simplices of `X`. Their faces along the boundary of
the square are constant at `x`, and their diagonal faces cancel, so the boundary of their sum is
twice the constant `1`-simplex at `x`. Subtracting twice the constant `2`-simplex at `x`, whose
boundary is the constant `1`-simplex, gives an integral singular `2`-cycle
`GenLoop.squareChain p`, with homology class `GenLoop.squareClass p ∈ H₂(X; ℤ)`.

The square class is natural in based maps (`GenLoop.squareClass_map`). Every generalized
loop is the image of the tautological loop `TauCeti.sphereGenLoop 2` of the sphere `S²`
(`GenLoop.map_toSphere_sphereGenLoop`), whose Hurewicz class generates `H₂(S²; ℤ)`
(`TauCeti.exists_zsmul_hurewicz_sphereGenLoop`). So there is one integer `k`, the coordinate of
the square class of the tautological loop, with

`squareClass p = k • p_*[I²]`

for every generalized loop `p` in every space
(`GenLoop.exists_forall_squareClass_eq_zsmul_hurewicz`). The square class is thus an
explicit cycle representing, up to this universal factor, the Hurewicz class of `[p] ∈ π₂(X, x)`.
Its simplices are affine pieces of the square, so when `X` is a manifold and `p` is smooth they are
smooth simplices, over which differential forms can be integrated. The value of `k` is not computed
here: a universal factor is all that is needed to compare integrals over spheres with periods on
homology.

## Main definitions

* `TauCeti.squareLowerTriangle`, `TauCeti.squareUpperTriangle`: the two affine triangles of the
  unit square, as maps from the standard `2`-simplex.
* `GenLoop.squareChain p`: the triangulated singular `2`-cycle of a generalized loop.
* `GenLoop.squareClass p`: its class in `H₂(X; ℤ)`.

## Main results

* `GenLoop.d_squareChain`: the triangulated chain is a cycle.
* `GenLoop.squareClass_map`: naturality in based maps.
* `GenLoop.exists_forall_squareClass_eq_zsmul_hurewicz`: the square class is a universal
  integer multiple of the Hurewicz class.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.1 (singular chains of triangulated squares) and Section 4.2 (the Hurewicz map).
-/

public section

noncomputable section

open CategoryTheory Convexity Simplicial unitInterval HomologicalComplex
open scoped Topology Topology.Homotopy

namespace TauCeti

/-- The **lower triangle** of the unit square, with vertices `(0, 0)`, `(1, 0)`, `(1, 1)`: the
affine map `w ↦ (w₁ + w₂, w₂)` from the standard `2`-simplex. -/
def squareLowerTriangle : C(StdSimplex ℝ (Fin 3), I^(Fin 2)) where
  toFun w := ![StdSimplex.weightsOneAddTwoI w, StdSimplex.weightI 2 w]
  continuous_toFun := by
    refine continuous_pi fun i ↦ ?_
    fin_cases i
    exacts [StdSimplex.weightsOneAddTwoI.continuous, (StdSimplex.weightI 2).continuous]

/-- The **upper triangle** of the unit square, with vertices `(0, 0)`, `(1, 1)`, `(0, 1)`: the
affine map `w ↦ (w₁, w₁ + w₂)` from the standard `2`-simplex. -/
def squareUpperTriangle : C(StdSimplex ℝ (Fin 3), I^(Fin 2)) where
  toFun w := ![StdSimplex.weightI 1 w, StdSimplex.weightsOneAddTwoI w]
  continuous_toFun := by
    refine continuous_pi fun i ↦ ?_
    fin_cases i
    exacts [(StdSimplex.weightI 1).continuous, StdSimplex.weightsOneAddTwoI.continuous]

/-- The first coordinate of the lower triangle is `w₁ + w₂`. -/
@[simp]
theorem squareLowerTriangle_apply_zero (w : StdSimplex ℝ (Fin 3)) :
    (squareLowerTriangle w 0 : ℝ) = w.weights 1 + w.weights 2 :=
  StdSimplex.coe_weightsOneAddTwoI_apply w

/-- The second coordinate of the lower triangle is `w₂`. -/
@[simp]
theorem squareLowerTriangle_apply_one (w : StdSimplex ℝ (Fin 3)) :
    (squareLowerTriangle w 1 : ℝ) = w.weights 2 :=
  StdSimplex.coe_weightI_apply 2 w

/-- The first coordinate of the upper triangle is `w₁`. -/
@[simp]
theorem squareUpperTriangle_apply_zero (w : StdSimplex ℝ (Fin 3)) :
    (squareUpperTriangle w 0 : ℝ) = w.weights 1 :=
  StdSimplex.coe_weightI_apply 1 w

/-- The second coordinate of the upper triangle is `w₁ + w₂`. -/
@[simp]
theorem squareUpperTriangle_apply_one (w : StdSimplex ℝ (Fin 3)) :
    (squareUpperTriangle w 1 : ℝ) = w.weights 1 + w.weights 2 :=
  StdSimplex.coe_weightsOneAddTwoI_apply w

/-- On the face of the standard `2`-simplex opposite the vertex `0`, the coordinates `w₁` and `w₂`
sum to `1`. -/
private theorem weights_one_add_weights_two_map_succAbove_zero (z : StdSimplex ℝ (Fin 2)) :
    (StdSimplex.map (Fin.succAbove 0) z).weights 1 +
      (StdSimplex.map (Fin.succAbove 0) z).weights 2 = 1 := by
  rw [StdSimplex.weights_map_succAbove_of_eq (j := 0) (i := 0) (k := 1) rfl,
    StdSimplex.weights_map_succAbove_of_eq (j := 0) (i := 1) (k := 2) rfl,
    StdSimplex.total_fin_two]

/-- The diagonal faces of the two triangles of the square agree: both are `z ↦ (z₁, z₁)`. -/
private theorem squareLowerTriangle_map_succAbove_one (z : StdSimplex ℝ (Fin 2)) :
    squareLowerTriangle (StdSimplex.map (Fin.succAbove 1) z) =
      squareUpperTriangle (StdSimplex.map (Fin.succAbove 2) z) := by
  have h₁ : (StdSimplex.map (Fin.succAbove 1) z).weights 2 = z.weights 1 :=
    StdSimplex.weights_map_succAbove_of_eq (by decide) z
  have h₂ : (StdSimplex.map (Fin.succAbove 2) z).weights 1 = z.weights 1 :=
    StdSimplex.weights_map_succAbove_of_eq (by decide) z
  funext j
  apply Subtype.ext
  fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, squareLowerTriangle_apply_zero,
      squareUpperTriangle_apply_zero, squareLowerTriangle_apply_one, squareUpperTriangle_apply_one,
      StdSimplex.weights_map_succAbove_self, h₁, h₂, zero_add, add_zero]

/-- A face of the singular `2`-simplex of a map `f` out of the standard `2`-simplex is the singular
`1`-simplex of any map `g` agreeing with `f` on that face. -/
private theorem δ_toSSetObjEquiv_symm_eq {X : TopCat.{0}} (f : C(StdSimplex ℝ (Fin 3), X))
    (i : Fin 3) (g : C(StdSimplex ℝ (Fin 2), X))
    (h : ∀ z, f (StdSimplex.map i.succAbove z) = g z) :
    (TopCat.toSSet.obj X).δ i ((X.toSSetObjEquiv (.op ⦋2⦌)).symm f) =
      (X.toSSetObjEquiv (.op ⦋1⦌)).symm g := by
  apply (X.toSSetObjEquiv _).injective
  ext z
  rw [TopCat.toSSetObjEquiv_δ_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact h z

/-- A point of the square with a coordinate equal to `0` or `1` lies on its boundary. -/
private theorem mem_boundary_of_coord {y : I^(Fin 2)} (j : Fin 2)
    (h : (y j : ℝ) = 0 ∨ (y j : ℝ) = 1) : y ∈ Cube.boundary (Fin 2) :=
  ⟨j, h.imp (fun h ↦ Subtype.ext h) fun h ↦ Subtype.ext h⟩

end TauCeti

namespace GenLoop

open TauCeti

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}

/-- The **triangulated chain** of a generalized loop `p : I² → X` at `x`: the singular `2`-chain
`p ∘ T₁ + p ∘ T₂ - 2 [x]` of the lower and upper triangles `T₁`, `T₂` of the unit square
(`TauCeti.squareLowerTriangle`, `TauCeti.squareUpperTriangle`) and the constant `2`-simplex at `x`.
It is a cycle (`GenLoop.d_squareChain`). -/
def squareChain (p : Ω^ (Fin 2) X x) : ((singularChains ℤ).obj (TopCat.of X)).X 2 :=
  simplexChain (((TopCat.of X).toSSetObjEquiv (.op ⦋2⦌)).symm
      ((p : C(I^(Fin 2), X)).comp squareLowerTriangle)) 1 +
    simplexChain (((TopCat.of X).toSSetObjEquiv (.op ⦋2⦌)).symm
      ((p : C(I^(Fin 2), X)).comp squareUpperTriangle)) 1 -
    2 • simplexChain (((TopCat.of X).toSSetObjEquiv (.op ⦋2⦌)).symm (ContinuousMap.const _ x)) 1

/-- The triangulated chain of `p` is `p ∘ T₁ + p ∘ T₂ - 2 [x]`. -/
theorem squareChain_def (p : Ω^ (Fin 2) X x) :
    squareChain p =
      simplexChain (((TopCat.of X).toSSetObjEquiv (.op ⦋2⦌)).symm
          ((p : C(I^(Fin 2), X)).comp squareLowerTriangle)) 1 +
        simplexChain (((TopCat.of X).toSSetObjEquiv (.op ⦋2⦌)).symm
          ((p : C(I^(Fin 2), X)).comp squareUpperTriangle)) 1 -
        2 • simplexChain (((TopCat.of X).toSSetObjEquiv (.op ⦋2⦌)).symm
          (ContinuousMap.const _ x)) 1 :=
  (rfl)

/-- **The triangulated chain is a cycle.** The faces of the two triangles along the boundary of
the square are constant at `x`, their faces along the diagonal cancel, and the remaining twice the
constant `1`-simplex is the boundary of twice the constant `2`-simplex. -/
theorem d_squareChain (p : Ω^ (Fin 2) X x) :
    ((singularChains ℤ).obj (TopCat.of X)).d 2 1 (squareChain p) = 0 := by
  set c := ((TopCat.of X).toSSetObjEquiv (.op ⦋1⦌)).symm (ContinuousMap.const _ x)
  have hx {T : C(StdSimplex ℝ (Fin 3), I^(Fin 2))} {i : Fin 3}
      (h : ∀ z, T (StdSimplex.map i.succAbove z) ∈ Cube.boundary (Fin 2)) :
      (TopCat.toSSet.obj (TopCat.of X)).δ i (((TopCat.of X).toSSetObjEquiv (.op ⦋2⦌)).symm
        ((p : C(I^(Fin 2), X)).comp T)) = c :=
    δ_toSSetObjEquiv_symm_eq _ i _ fun z ↦ GenLoop.boundary p _ (h z)
  have hL₀ := hx (T := squareLowerTriangle) (i := 0) fun z ↦ mem_boundary_of_coord 0 <| Or.inr <| by
    rw [squareLowerTriangle_apply_zero, weights_one_add_weights_two_map_succAbove_zero]
  have hL₂ := hx (T := squareLowerTriangle) (i := 2) fun z ↦ mem_boundary_of_coord 1 <| Or.inl <| by
    rw [squareLowerTriangle_apply_one, StdSimplex.weights_map_succAbove_self]
  have hU₀ := hx (T := squareUpperTriangle) (i := 0) fun z ↦ mem_boundary_of_coord 1 <| Or.inr <| by
    rw [squareUpperTriangle_apply_one, weights_one_add_weights_two_map_succAbove_zero]
  have hU₁ := hx (T := squareUpperTriangle) (i := 1) fun z ↦ mem_boundary_of_coord 0 <| Or.inl <| by
    rw [squareUpperTriangle_apply_zero, StdSimplex.weights_map_succAbove_self]
  -- The diagonal faces of the two triangles are both `z ↦ (z₁, z₁)`.
  have hdiag : (TopCat.toSSet.obj (TopCat.of X)).δ 1 (((TopCat.of X).toSSetObjEquiv (.op ⦋2⦌)).symm
        ((p : C(I^(Fin 2), X)).comp squareLowerTriangle)) =
      (TopCat.toSSet.obj (TopCat.of X)).δ 2 (((TopCat.of X).toSSetObjEquiv (.op ⦋2⦌)).symm
        ((p : C(I^(Fin 2), X)).comp squareUpperTriangle)) :=
    (δ_toSSetObjEquiv_symm_eq _ 1 _ fun z ↦ congrArg p
        (squareLowerTriangle_map_succAbove_one z)).trans
      (δ_toSSetObjEquiv_symm_eq _ 2 ((p : C(I^(Fin 2), X)).comp squareUpperTriangle |>.comp
        ⟨StdSimplex.map (Fin.succAbove 2), StdSimplex.continuous_map ℝ _⟩) fun _ ↦ rfl).symm
  have hc (i : Fin 3) : (TopCat.toSSet.obj (TopCat.of X)).δ i
      (((TopCat.of X).toSSetObjEquiv (.op ⦋2⦌)).symm (ContinuousMap.const _ x)) = c :=
    δ_toSSetObjEquiv_symm_eq _ i _ fun _ ↦ rfl
  rw [squareChain, map_sub, map_add, map_nsmul, singularChains_d_simplexChain,
    singularChains_d_simplexChain, singularChains_d_simplexChain]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, hL₀, hL₂, hU₀, hU₁, hdiag, hc]
  simp
  abel

/-- The **square class** of a generalized loop `p : I² → X` at `x`: the class in `H₂(X; ℤ)` of its
triangulated cycle `GenLoop.squareChain p`. Up to a universal integer it is the Hurewicz
class of `[p] ∈ π₂(X, x)` (`GenLoop.exists_forall_squareClass_eq_zsmul_hurewicz`). -/
def squareClass (p : Ω^ (Fin 2) X x) : ((singularChains ℤ).obj (TopCat.of X)).homology 2 :=
  (((singularChains ℤ).obj (TopCat.of X)).homologyπ 2).hom
    (((singularChains ℤ).obj (TopCat.of X)).moduleCatCyclesMk (squareChain p) 1
      (ChainComplex.next_nat_succ 1) (d_squareChain p))

/-- The square class of `p` is the homology class of its triangulated cycle. -/
theorem squareClass_def (p : Ω^ (Fin 2) X x) :
    squareClass p = (((singularChains ℤ).obj (TopCat.of X)).homologyπ 2).hom
      (((singularChains ℤ).obj (TopCat.of X)).moduleCatCyclesMk (squareChain p) 1
        (ChainComplex.next_nat_succ 1) (d_squareChain p)) :=
  (rfl)

/-- Pushing the triangulated chain of a generalized loop forward along a based map gives the
triangulated chain of the image loop. -/
theorem singularChains_map_f_squareChain (f : C(X, Y)) (hf : f x = y) (p : Ω^ (Fin 2) X x) :
    ((singularChains ℤ).map (TopCat.ofHom f)).f 2 (squareChain p) =
      squareChain (GenLoop.map f hf p) := by
  rw [squareChain, squareChain, map_sub, map_add, map_nsmul, singularChains_map_f_simplexChain,
    singularChains_map_f_simplexChain, singularChains_map_f_simplexChain,
    TopCat.toSSet_map_app_toSSetObjEquiv_symm, TopCat.toSSet_map_app_toSSetObjEquiv_symm,
    TopCat.toSSet_map_app_toSSetObjEquiv_symm, GenLoop.coe_map]
  simp [hf, ContinuousMap.comp_assoc]

/-- **Naturality of the square class**: a based map `f : (X, x) → (Y, y)` sends the square class
of `p` to the square class of `f ∘ p`. -/
theorem squareClass_map (f : C(X, Y)) (hf : f x = y) (p : Ω^ (Fin 2) X x) :
    ContinuousMap.singularHomologyMap ℤ 2 f (squareClass p) = squareClass (GenLoop.map f hf p) := by
  rw [squareClass, squareClass, ContinuousMap.singularHomologyMap,
    homologyMap_homologyπ_moduleCatCyclesMk]
  simp only [singularChains_map_f_squareChain f hf p]

/-- **The square class is a universal multiple of the Hurewicz class.** There is one integer `k`
such that for every generalized loop `p : I² → X` at `x`, in every space `X`, the class of the
triangulated cycle of `p` is `k` times the Hurewicz class `p_*[I²]`. The integer is the coordinate
of the square class of the tautological loop of `S²` on the generator of `H₂(S²; ℤ)`; every
generalized loop is the image of the tautological loop, and both classes are natural. -/
theorem exists_forall_squareClass_eq_zsmul_hurewicz :
    ∃ k : ℤ, ∀ (X : Type) [TopologicalSpace X] (x : X) (p : Ω^ (Fin 2) X x),
      squareClass p = k • (hurewicz (ModuleCat.of ℤ ℤ) p).hom 1 := by
  obtain ⟨k, hk⟩ := exists_zsmul_hurewicz_sphereGenLoop 1 (squareClass (sphereGenLoop 2))
  refine ⟨k, fun X _ x p ↦ ?_⟩
  rw [hurewicz_eq_hurewicz_sphereGenLoop_comp, ModuleCat.hom_comp, LinearMap.comp_apply,
    ← map_zsmul, hk]
  -- The map of the singular homology functor is `ContinuousMap.singularHomologyMap`.
  refine Eq.trans ?_ (squareClass_map (toSphere p) (toSphere_sphereNorthPole p) _).symm
  rw [map_toSphere_sphereGenLoop]

end GenLoop
