/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic
public import TauCeti.Topology.Homotopy.Path
public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.Geometry.Convex.ConvexSpace.ContractibleSpaceStdSimplex
public import TauCeti.Geometry.Convex.ConvexSpace.Defs
public import TauCeti.GroupTheory.Abelianization.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# The Hurewicz theorem in degree one

For a path-connected space `X` with a base point `x`, the Hurewicz map sends a loop at `x` to the
homology class of the singular `1`-simplex it defines, and it identifies the abelianization of
the fundamental group `π₁(X, x)` with the first singular homology group `H₁(X; ℤ)`
(`TauCeti.HurewiczOne.hurewiczHomologyAddEquiv`).

The proof is the one of Hatcher, Theorem 2A.1, carried out on the singular chains with integer
coefficients through the element-level interface of
`TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic`.
Paths `γ : I → X` are read as singular `1`-simplices along the parameter of the standard
`1`-simplex, and three kinds of explicit singular `2`-simplices give the relations:

* a constant `2`-simplex shows that the chain of a constant path is a boundary;
* the composite of a concatenation `γ.trans δ` with the affine projection of `Δ²` onto `[0, 1]`
  sending the vertices to `0`, `1/2` and `1` shows that `γ + δ - γ.trans δ` is a boundary;
* a homotopy of paths, cut along the diagonal of its square into two `2`-simplices, shows that
  homotopic paths have homologous chains.

So the Hurewicz map is a well-defined homomorphism `π₁(X, x) → H₁(X; ℤ)`
(`TauCeti.HurewiczOne.hurewicz₁`). Its inverse sends a singular `1`-simplex `σ` to the class of the
loop that runs along a chosen path from `x` to the first vertex of `σ`, along `σ`, and back from
its last vertex. It vanishes on boundaries because the three edges of a singular `2`-simplex are
images of paths in the simply connected standard simplex, and it inverts the Hurewicz map because
conjugation is trivial in the abelianization. Conversely, the loop through `σ` differs from `σ` by
the chains of the chosen paths at its endpoints, which cancel on cycles.

The homology group is first described as the explicit homology
`ShortComplex.moduleCatLeftHomologyData` of the short complex `C₂ → C₁ → C₀`, that is `1`-cycles
modulo boundaries (`TauCeti.HurewiczOne.H₁`), and then identified with the homology of the
singular chain complex (`TauCeti.HurewiczOne.H₁AddEquivHomology`).

## Main definitions and results

* `TauCeti.HurewiczOne.hurewicz₁`: the Hurewicz homomorphism `π₁(X, x) → H₁(X; ℤ)`.
* `TauCeti.HurewiczOne.hurewiczAddEquiv`: for path-connected `X`, it induces an isomorphism from the
  abelianization of `π₁(X, x)` onto `H₁`, the `1`-cycles modulo boundaries.
* `TauCeti.HurewiczOne.hurewiczHomologyAddEquiv`: the same isomorphism onto the first homology group
  of the singular chain complex of `X` with integer coefficients.

## References

* A. Hatcher, *Algebraic Topology*, Theorem 2A.1.
-/

public section

noncomputable section

open CategoryTheory Convexity Simplicial unitInterval TauCeti.TopCat

namespace TauCeti.HurewiczOne

/-- The parametrization of the standard `1`-simplex by the unit interval, as a continuous map. -/
local notation "toI" => (StdSimplex.homeomorphI : C(StdSimplex ℝ (Fin 2), I))

/-- The point of the standard `1`-simplex with a given parameter, as a continuous map. -/
local notation "ofI" => (StdSimplex.homeomorphI.symm : C(I, StdSimplex ℝ (Fin 2)))

variable {X : TopCat.{0}}

/-- The inclusion of the `i`-th facet of the standard `2`-simplex. -/
private def face (i : Fin 3) : C(StdSimplex ℝ (Fin 2), StdSimplex ℝ (Fin 3)) :=
  ⟨StdSimplex.map i.succAbove, StdSimplex.continuous_map ℝ _⟩

section FaceWeights

variable (a : StdSimplex ℝ (Fin 2))

@[simp] private lemma face_zero_weights_zero : (face 0 a).weights 0 = 0 :=
  StdSimplex.weights_map_succAbove_self 0 a
@[simp] private lemma face_zero_weights_one : (face 0 a).weights 1 = a.weights 0 :=
  StdSimplex.weights_map_apply_of_injective (f := Fin.succAbove (0 : Fin 3))
    Fin.succAbove_right_injective a 0
@[simp] private lemma face_zero_weights_two : (face 0 a).weights 2 = a.weights 1 :=
  StdSimplex.weights_map_apply_of_injective (f := Fin.succAbove (0 : Fin 3))
    Fin.succAbove_right_injective a 1
@[simp] private lemma face_one_weights_zero : (face 1 a).weights 0 = a.weights 0 :=
  StdSimplex.weights_map_apply_of_injective (f := Fin.succAbove (1 : Fin 3))
    Fin.succAbove_right_injective a 0
@[simp] private lemma face_one_weights_one : (face 1 a).weights 1 = 0 :=
  StdSimplex.weights_map_succAbove_self 1 a
@[simp] private lemma face_one_weights_two : (face 1 a).weights 2 = a.weights 1 :=
  StdSimplex.weights_map_apply_of_injective (f := Fin.succAbove (1 : Fin 3))
    Fin.succAbove_right_injective a 1
@[simp] private lemma face_two_weights_zero : (face 2 a).weights 0 = a.weights 0 :=
  StdSimplex.weights_map_apply_of_injective (f := Fin.succAbove (2 : Fin 3))
    Fin.succAbove_right_injective a 0
@[simp] private lemma face_two_weights_one : (face 2 a).weights 1 = a.weights 1 :=
  StdSimplex.weights_map_apply_of_injective (f := Fin.succAbove (2 : Fin 3))
    Fin.succAbove_right_injective a 1
@[simp] private lemma face_two_weights_two : (face 2 a).weights 2 = 0 :=
  StdSimplex.weights_map_succAbove_self 2 a

end FaceWeights

/-- The chain of a singular `2`-simplex given as a continuous map from the standard simplex. -/
private abbrev chain₂ (f : C(StdSimplex ℝ (Fin 3), X)) : ((singularChains ℤ).obj X).X 2 :=
  simplexChain ((X.toSSetObjEquiv (.op ⦋2⦌)).symm f) 1

private lemma δ_toSSetObjEquiv_symm (f : C(StdSimplex ℝ (Fin 3), X)) (i : Fin 3)
    (g : C(I, X)) (h : f.comp (face i) = g.comp toI) :
    (TopCat.toSSet.obj X).δ i ((X.toSSetObjEquiv (.op ⦋2⦌)).symm f) = simplex₁ g := by
  apply (X.toSSetObjEquiv _).injective
  ext w
  rw [TopCat.toSSetObjEquiv_δ_apply, toSSetObjEquiv_simplex₁, Equiv.apply_symm_apply]
  exact congr($h w)

private lemma d_chain₂ (f : C(StdSimplex ℝ (Fin 3), X)) (g₀ g₁ g₂ : C(I, X))
    (h₀ : f.comp (face 0) = g₀.comp toI)
    (h₁ : f.comp (face 1) = g₁.comp toI)
    (h₂ : f.comp (face 2) = g₂.comp toI) :
    ((singularChains ℤ).obj X).d 2 1 (chain₂ f) =
      pathChain ℤ g₀ - pathChain ℤ g₁ + pathChain ℤ g₂ := by
  rw [singularChains_d_simplexChain (n := 1), Fin.sum_univ_three,
    δ_toSSetObjEquiv_symm f 0 g₀ h₀, δ_toSSetObjEquiv_symm f 1 g₁ h₁,
    δ_toSSetObjEquiv_symm f 2 g₂ h₂]
  simp [sub_eq_add_neg]

variable (X) in
/-- The short complex `C₂ → C₁ → C₀` of the singular chains of `X`. -/
abbrev sc₁ := ((singularChains ℤ).obj X).sc' 2 1 0

variable (X) in
/-- The boundaries among the singular `1`-chains of `X`. -/
abbrev boundaries₁ : Submodule ℤ (((singularChains ℤ).obj X).X 1) :=
  LinearMap.range (((singularChains ℤ).obj X).d 2 1).hom

lemma mem_boundaries₁ {c : ((singularChains ℤ).obj X).X 1} (y : ((singularChains ℤ).obj X).X 2)
    (h : ((singularChains ℤ).obj X).d 2 1 y = c) : c ∈ boundaries₁ X :=
  ⟨y, h⟩

/-- The chain of a constant map is a boundary. -/
lemma pathChain_const_mem_boundaries₁ (p : X) :
    pathChain ℤ (ContinuousMap.const I p) ∈ boundaries₁ X :=
  mem_boundaries₁ (chain₂ (ContinuousMap.const _ p)) (by
    rw [d_chain₂ _ (.const I p) (.const I p) (.const I p) rfl rfl rfl]
    abel)

/-- The affine projection of the standard `2`-simplex onto the unit interval sending the vertices
to `0`, `1/2` and `1`. -/
private def concatProj : C(StdSimplex ℝ (Fin 3), I) :=
  ⟨fun w ↦ ⟨w.weights 1 / 2 + w.weights 2,
    add_nonneg (div_nonneg (w.weights_nonneg 1) zero_le_two) (w.weights_nonneg 2),
    by linarith [w.weights_one_add_weights_two_le_one, w.weights_nonneg 1]⟩,
    (by fun_prop :
      Continuous fun w : StdSimplex ℝ (Fin 3) ↦ w.weights 1 / 2 + w.weights 2).subtype_mk _⟩

/-- The chain of a concatenation of paths differs from the sum of the chains of the two paths by
a boundary. -/
lemma pathChain_add_sub_trans_mem_boundaries₁ {a b c : X} (γ : Path a b) (δ : Path b c) :
    pathChain ℤ γ.toContinuousMap + pathChain ℤ δ.toContinuousMap -
      pathChain ℤ (γ.trans δ).toContinuousMap ∈
      boundaries₁ X := by
  refine mem_boundaries₁ (chain₂ ((γ.trans δ).toContinuousMap.comp concatProj)) ?_
  rw [d_chain₂ _ δ.toContinuousMap (γ.trans δ).toContinuousMap γ.toContinuousMap]
  · abel
  · ext a
    exact Path.trans_apply_of_ge γ δ
      (by simp [concatProj]; linarith [a.total_fin_two, a.weights_nonneg 1]) _
      (by simp [concatProj, StdSimplex.homeomorphI_apply_eq_mk]; linarith [a.total_fin_two])
  · ext a
    simp [concatProj, StdSimplex.homeomorphI_apply_eq_mk]
  · ext a
    exact Path.trans_apply_of_le γ δ
      (by simp [concatProj]; linarith [a.total_fin_two, a.weights_nonneg 0]) _
      (by simp [concatProj, StdSimplex.homeomorphI_apply_eq_mk]; ring)

/-- The weight of the last vertex of the standard `2`-simplex, as a point of the unit
interval. -/
private def lastWeight : C(StdSimplex ℝ (Fin 3), I) :=
  ⟨fun w ↦ ⟨w.weights 2, w.weights_nonneg 2, w.weights_apply_le_one 2⟩,
    (StdSimplex.continuous_weights_apply ℝ 2).subtype_mk _⟩

/-- The sum of the weights of the last two vertices of the standard `2`-simplex, as a point of
the unit interval. -/
private def lastTwoWeights : C(StdSimplex ℝ (Fin 3), I) :=
  ⟨fun w ↦ ⟨w.weights 1 + w.weights 2,
    add_nonneg (w.weights_nonneg 1) (w.weights_nonneg 2), w.weights_one_add_weights_two_le_one⟩,
    (by fun_prop :
      Continuous fun w : StdSimplex ℝ (Fin 3) ↦ w.weights 1 + w.weights 2).subtype_mk _⟩

/-- The chains of homotopic paths differ by a boundary. -/
lemma pathChain_sub_mem_boundaries₁_of_homotopy {a b : X} {γ γ' : Path a b}
    (F : Path.Homotopy γ γ') :
    pathChain ℤ γ.toContinuousMap - pathChain ℤ γ'.toContinuousMap ∈ boundaries₁ X := by
  let D : C(I, X) := F.toContinuousMap.comp ⟨fun t ↦ (t, t), by fun_prop⟩
  have h₁ : pathChain ℤ (.const I b) - pathChain ℤ D + pathChain ℤ γ.toContinuousMap ∈
      boundaries₁ X := by
    refine mem_boundaries₁ (chain₂ (F.toContinuousMap.comp (lastWeight.prodMk lastTwoWeights))) ?_
    rw [d_chain₂ _ (.const I b) D γ.toContinuousMap]
    · ext x
      simp [lastWeight, lastTwoWeights]
    · ext x
      simp [lastWeight, lastTwoWeights, StdSimplex.homeomorphI_apply_eq_mk, D]
    · ext x
      simp [lastWeight, lastTwoWeights, StdSimplex.homeomorphI_apply_eq_mk]
  have h₂ : pathChain ℤ γ'.toContinuousMap - pathChain ℤ D + pathChain ℤ (.const I a) ∈
      boundaries₁ X := by
    refine mem_boundaries₁ (chain₂ (F.toContinuousMap.comp (lastTwoWeights.prodMk lastWeight))) ?_
    rw [d_chain₂ _ γ'.toContinuousMap D (.const I a)]
    · ext x
      simp [lastWeight, lastTwoWeights, StdSimplex.homeomorphI_apply_eq_mk]
    · ext x
      simp [lastWeight, lastTwoWeights, StdSimplex.homeomorphI_apply_eq_mk, D]
    · ext x
      simp [lastWeight, lastTwoWeights]
  have := sub_mem (add_mem (sub_mem h₁ h₂) (pathChain_const_mem_boundaries₁ a))
    (pathChain_const_mem_boundaries₁ b)
  convert this using 1
  abel

/-! ### The Hurewicz map -/

variable (X) in
/-- The singular `1`-cycles of `X`, the kernel of the differential of `sc₁ X`. -/
abbrev cycles₁ : Submodule ℤ (((singularChains ℤ).obj X).X 1) :=
  LinearMap.ker (sc₁ X).g.hom

variable (X) in
/-- The first singular homology group of `X` with integer coefficients, as the explicit homology
`cycles₁ X ⧸ boundaries` of `sc₁ X` in `ModuleCat ℤ`. -/
abbrev H₁ : ModuleCat ℤ := (sc₁ X).moduleCatLeftHomologyData.H

/-- A `1`-chain is a cycle when its boundary vanishes. -/
lemma mem_cycles₁_iff {c : ((singularChains ℤ).obj X).X 1} :
    c ∈ cycles₁ X ↔ ((singularChains ℤ).obj X).d 1 0 c = 0 :=
  -- The differential `(sc₁ X).g` of the short complex is `d 1 0` by definition of `sc'`.
  LinearMap.mem_ker

lemma mem_cycles₁ {c : ((singularChains ℤ).obj X).X 1}
    (h : ((singularChains ℤ).obj X).d 1 0 c = 0) :
    c ∈ cycles₁ X :=
  mem_cycles₁_iff.2 h

/-- The class in `H₁ X` of a `1`-cycle, as an additive map. (It is not stated as a `ℤ`-linear
map: instance search on the cycles would find `AddCommGroup.toIntModule`, which is only
propositionally equal to their submodule structure.) -/
def H₁.mk : cycles₁ X →+ H₁ X :=
  (sc₁ X).moduleCatLeftHomologyData.π.hom.toAddMonoidHom

lemma H₁.mk_eq_mk_iff (c c' : cycles₁ X) :
    H₁.mk c = H₁.mk c' ↔ (c : ((singularChains ℤ).obj X).X 1) - c' ∈ boundaries₁ X := by
  rw [H₁.mk]
  exact (ShortComplex.moduleCatLeftHomologyData_π_hom_eq_iff (sc₁ X) c c').trans
    LinearMap.mem_range.symm

lemma H₁.mk_eq_zero_iff (c : cycles₁ X) :
    H₁.mk c = 0 ↔ (c : ((singularChains ℤ).obj X).X 1) ∈ boundaries₁ X := by
  rw [← map_zero H₁.mk, H₁.mk_eq_mk_iff, ZeroMemClass.coe_zero, sub_zero]

lemma H₁.mk_surjective : Function.Surjective (H₁.mk (X := X)) := by
  intro h
  obtain ⟨c, hc⟩ := ShortComplex.moduleCatLeftHomologyData_π_hom_surjective (sc₁ X) h
  exact ⟨c, by rw [H₁.mk]; exact hc⟩

lemma pathChain_mem_cycles₁ {x : X} (γ : Path x x) : pathChain ℤ γ.toContinuousMap ∈ cycles₁ X :=
  mem_cycles₁ (by rw [singularChains_d_pathChain]; simp)

/-- The homology class of the chain of a loop. -/
def loopClass {x : X} (γ : Path x x) : H₁ X :=
  H₁.mk ⟨_, pathChain_mem_cycles₁ γ⟩

lemma loopClass_def {x : X} (γ : Path x x) :
    loopClass γ = H₁.mk ⟨pathChain ℤ γ.toContinuousMap, pathChain_mem_cycles₁ γ⟩ :=
  (rfl)

lemma loopClass_eq_iff {x y : X} (γ : Path x x) (γ' : Path y y) :
    loopClass γ = loopClass γ' ↔
      pathChain ℤ γ.toContinuousMap - pathChain ℤ γ'.toContinuousMap ∈ boundaries₁ X := by
  rw [loopClass, loopClass, H₁.mk_eq_mk_iff]

@[simp]
lemma loopClass_refl (x : X) : loopClass (Path.refl x) = 0 := by
  rw [loopClass, H₁.mk_eq_zero_iff]
  exact pathChain_const_mem_boundaries₁ x

@[simp]
lemma loopClass_trans {x : X} (γ δ : Path x x) :
    loopClass (γ.trans δ) = loopClass γ + loopClass δ := by
  rw [loopClass, loopClass, loopClass, ← map_add, H₁.mk_eq_mk_iff]
  have := neg_mem (pathChain_add_sub_trans_mem_boundaries₁ γ δ)
  convert this using 1
  simp only [Submodule.coe_add]
  abel

variable (X) in
/-- **The Hurewicz map in degree one**: a loop is sent to the homology class of its chain. -/
def hurewicz₁ (x : X) : FundamentalGroup X x →* Multiplicative (H₁ X) where
  toFun g := Quotient.lift (s := Path.Homotopic.setoid x x)
    (fun γ ↦ Multiplicative.ofAdd (loopClass γ)) (fun γ γ' h ↦
      congrArg Multiplicative.ofAdd ((loopClass_eq_iff γ γ').2
        (pathChain_sub_mem_boundaries₁_of_homotopy h.some))) g.toPath
  map_one' := congrArg Multiplicative.ofAdd (loopClass_refl x)
  map_mul' := by
    rintro ⟨p⟩ ⟨q⟩
    induction p using Path.Homotopic.Quotient.ind with | mk p =>
    induction q using Path.Homotopic.Quotient.ind with | mk q =>
    -- `Quotient.lift` computes on the classes of `q.trans p`, `p` and `q`.
    change Multiplicative.ofAdd (loopClass (q.trans p)) = _
    rw [loopClass_trans, add_comm, ofAdd_add]
    -- `Quotient.lift` computes on the classes `⟦p⟧` and `⟦q⟧`.
    rfl

@[simp]
lemma hurewicz₁_mk {x : X} (γ : Path x x) :
    hurewicz₁ X x (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) =
      Multiplicative.ofAdd (loopClass γ) := by
  rw [hurewicz₁]
  -- `Quotient.lift` computes on the class of `γ`.
  rfl

/-! ### The inverse map -/

section Inverse

variable [PathConnectedSpace X] (x : X)

/-- A chosen path from the base point to a point. -/
private def pathTo (y : X) : Path x y := PathConnectedSpace.somePath x y

/-- The loop at the base point obtained from a path class `q` from `y` to `z` by going out to `y`
along the chosen path, along `q`, and back from `z` along the chosen path. -/
private def loopThrough {y z : X} (q : Path.Homotopic.Quotient y z) : FundamentalGroup X x :=
  FundamentalGroup.fromPath ((Path.Homotopic.Quotient.mk (pathTo x y)).trans
    (q.trans (Path.Homotopic.Quotient.mk (pathTo x z)).symm))

private lemma loopThrough_trans {y z w : X} (q : Path.Homotopic.Quotient y z)
    (q' : Path.Homotopic.Quotient z w) :
    loopThrough x q' * loopThrough x q = loopThrough x (q.trans q') := by
  simp only [loopThrough, FundamentalGroup.mul_def, FundamentalGroup.fromPath,
    FundamentalGroup.fromArrow, Path.Homotopic.Quotient.trans_assoc,
    ← Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.symm _),
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]

/-- The value of the inverse Hurewicz map on a singular `1`-simplex. -/
private def inverseValue (s : (TopCat.toSSet.obj X) _⦋1⦌) :
    Additive (Abelianization (FundamentalGroup X x)) :=
  Additive.ofMul (Abelianization.of (loopThrough x (Path.Homotopic.Quotient.mk (path₁ s))))

/-- The loop at the base point through the image under `g` of the (unique) path class from `u`
to `v` in a simply connected space. -/
private def imageClass {Y : Type} [TopologicalSpace Y] [SimplyConnectedSpace Y] (g : C(Y, X))
    (u v : Y) :
    FundamentalGroup X x :=
  loopThrough x ((Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath u v)).map g)

private lemma loopThrough_map_eq_imageClass {Y : Type} [TopologicalSpace Y] [SimplyConnectedSpace Y]
    (g : C(Y, X)) {u v : Y} (γ : Path u v) :
    loopThrough x ((Path.Homotopic.Quotient.mk γ).map g) = imageClass x g u v := by
  rw [imageClass, Subsingleton.elim (Path.Homotopic.Quotient.mk γ)]

/-- The loops through the images of two composable paths compose to the loop through the image
of their concatenation. -/
private lemma loopThrough_map_trans {Y : Type} [TopologicalSpace Y] (g : C(Y, X)) {u v w : Y}
    (p : Path u v) (q : Path v w) :
    loopThrough x ((Path.Homotopic.Quotient.mk q).map g) *
        loopThrough x ((Path.Homotopic.Quotient.mk p).map g) =
      loopThrough x ((Path.Homotopic.Quotient.mk (p.trans q)).map g) := by
  rw [loopThrough_trans, ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_trans, ← Path.map_trans, Path.Homotopic.Quotient.mk_map]

private lemma imageClass_trans {Y : Type} [TopologicalSpace Y] [SimplyConnectedSpace Y]
    (g : C(Y, X)) (u v w : Y) :
    imageClass x g v w * imageClass x g u v = imageClass x g u w := by
  rw [imageClass, imageClass, loopThrough_map_trans, loopThrough_map_eq_imageClass]

/-- An edge of the standard `2`-simplex, as a path. -/
private def edgePath (i : Fin 3) :
    Path (face i (StdSimplex.single 0)) (face i (StdSimplex.single 1)) where
  toContinuousMap := (face i).comp ofI
  source' := by simp
  target' := by simp

private lemma inverseValue_δ (τ : (TopCat.toSSet.obj X) _⦋2⦌) (i : Fin 3) :
    inverseValue x ((TopCat.toSSet.obj X).δ i τ) =
      Additive.ofMul (Abelianization.of (imageClass x (X.toSSetObjEquiv _ τ)
        (face i (StdSimplex.single 0)) (face i (StdSimplex.single 1)))) := by
  have : path₁ ((TopCat.toSSet.obj X).δ i τ) =
      (edgePath i).map (X.toSSetObjEquiv _ τ).continuous := by
    ext t
    rw [path₁_apply, TopCat.toSSetObjEquiv_δ_apply]
    -- By definition of `edgePath`, the right-hand side is `τ` at the image of
    -- `homeomorphI.symm t` under the inclusion `face i` of the facet.
    rfl
  rw [inverseValue]
  exact congrArg (fun q ↦ Additive.ofMul (Abelianization.of q))
    ((congrArg (fun γ ↦ loopThrough x (Path.Homotopic.Quotient.mk γ)) this).trans
      (loopThrough_map_eq_imageClass x _ (edgePath i)))

private lemma face_single (i : Fin 3) (j : Fin 2) :
    face i (StdSimplex.single j) = StdSimplex.single (i.succAbove j) :=
  StdSimplex.map_single _ _

/-- The values of the inverse map on the faces of a singular `2`-simplex satisfy the cocycle
relation. -/
private lemma inverseValue_cocycle (τ : (TopCat.toSSet.obj X) _⦋2⦌) :
    inverseValue x ((TopCat.toSSet.obj X).δ 0 τ) - inverseValue x ((TopCat.toSSet.obj X).δ 1 τ) +
      inverseValue x ((TopCat.toSSet.obj X).δ 2 τ) = 0 := by
  simp only [inverseValue_δ, face_single]
  rw [sub_add_eq_add_sub, add_comm, Abelianization.ofMul_of_add_ofMul_of, sub_eq_zero]
  exact congrArg (fun q ↦ Additive.ofMul (Abelianization.of q)) (imageClass_trans x _ _ _ _)

/-- The inverse Hurewicz map on singular `1`-chains. -/
private def inverseChains :
    ((singularChains ℤ).obj X).X 1 →ₗ[ℤ] Additive (Abelianization (FundamentalGroup X x)) :=
  chainsDesc (inverseValue x)

private lemma inverseChains_simplexChain (s : (TopCat.toSSet.obj X) _⦋1⦌) :
    inverseChains x (simplexChain s 1) = inverseValue x s := by
  rw [inverseChains, chainsDesc_simplexChain_one]

private lemma inverseChains_d (y : ((singularChains ℤ).obj X).X 2) :
    inverseChains x (((singularChains ℤ).obj X).d 2 1 y) = 0 := by
  have := singularChains_linearMap_ext
    (L := inverseChains x ∘ₗ (((singularChains ℤ).obj X).d 2 1).hom) (L' := 0) fun τ ↦ by
      rw [LinearMap.comp_apply, singularChains_d_simplexChain (n := 1), Fin.sum_univ_three]
      simp only [map_add, map_zsmul, inverseChains_simplexChain]
      simpa [sub_eq_add_neg] using inverseValue_cocycle x τ
  exact LinearMap.congr_fun this y

/-- The inverse Hurewicz map on the `1`-cycles, as a morphism of `ℤ`-modules. The module structure
on the cycles is passed explicitly: for `ℤ`, instance search on `LinearMap.ker (sc₁ X).g.hom` finds
`AddCommGroup.toIntModule`, which is only propositionally equal to the submodule structure. -/
private def inverseCycles :
    (sc₁ X).moduleCatLeftHomologyData.K ⟶ ModuleCat.of ℤ (Additive (Abelianization
      (FundamentalGroup X x))) :=
  @ModuleCat.ofHom ℤ _ _ _ _ (cycles₁ X).module _ _
    ((inverseChains x).comp (cycles₁ X).subtype)

private lemma f'_inverseCycles : (sc₁ X).moduleCatLeftHomologyData.f' ≫ inverseCycles x = 0 :=
  ModuleCat.hom_ext (LinearMap.ext fun y ↦ inverseChains_d x y)

/-- **The inverse of the Hurewicz map in degree one**, on the first homology group. -/
private def inverse₁ : H₁ X →ₗ[ℤ] Additive (Abelianization (FundamentalGroup X x)) :=
  ((sc₁ X).moduleCatLeftHomologyData.descH (inverseCycles x) (f'_inverseCycles x)).hom

private lemma inverse₁_mk (c : cycles₁ X) : inverse₁ x (H₁.mk c) = inverseChains x c := by
  rw [inverse₁]
  exact congr($((sc₁ X).moduleCatLeftHomologyData.π_descH (inverseCycles x)
    (f'_inverseCycles x)).hom c)

/-- The class of the chosen loop at the base point, as an element of the fundamental group. -/
private def basePathClass : FundamentalGroup X x :=
  FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (pathTo x x))

/-- The loop through a loop at the base point is its conjugate by the chosen loop at the base
point. -/
private lemma loopThrough_eq_inv_mul_mul (q : FundamentalGroup X x) :
    loopThrough x q.toPath = (basePathClass x)⁻¹ * q * basePathClass x := by
  rw [FundamentalGroup.mul_def, FundamentalGroup.mul_def, FundamentalGroup.inv_def, loopThrough,
    basePathClass]

private lemma ofMul_of_loopThrough_cast {y z : X} (hy : y = x) (hz : z = x)
    (q : Path.Homotopic.Quotient x x) :
    Additive.ofMul (Abelianization.of (loopThrough x (q.cast hy hz))) =
      Additive.ofMul ((Abelianization.of : FundamentalGroup X x →* _)
        (FundamentalGroup.fromPath q)) := by
  subst hy hz
  rw [Path.Homotopic.Quotient.cast_rfl_rfl]
  exact (congrArg (fun g ↦ Additive.ofMul (Abelianization.of g))
    (loopThrough_eq_inv_mul_mul _ (FundamentalGroup.fromPath q))).trans
      (by rw [Abelianization.of_inv_mul_mul])

/-- The inverse Hurewicz map sends the homology class of a loop back to the class of the loop. -/
private lemma inverse₁_loopClass (γ : Path x x) :
    inverse₁ x (loopClass γ) =
      Additive.ofMul ((Abelianization.of : FundamentalGroup X x →* _)
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))) := by
  have hs : source₁ (simplex₁ γ.toContinuousMap) = x := (source₁_simplex₁ _).trans γ.source
  have ht : target₁ (simplex₁ γ.toContinuousMap) = x := (target₁_simplex₁ _).trans γ.target
  have hγ : path₁ (simplex₁ γ.toContinuousMap) = γ.cast hs ht := by
    ext t
    simp
  rw [loopClass, inverse₁_mk, inverseChains_simplexChain, inverseValue, hγ,
    Path.Homotopic.Quotient.mk_cast, ofMul_of_loopThrough_cast]

/-- The `1`-chains of the chosen paths from the base point to the points of a `0`-chain. -/
private def pathChains : ((singularChains ℤ).obj X).X 0 →ₗ[ℤ] ((singularChains ℤ).obj X).X 1 :=
  chainsDesc fun v ↦ pathChain ℤ (pathTo x (TopCat.toSSetObj₀Equiv v)).toContinuousMap

private lemma pathChains_simplexChain (v : (TopCat.toSSet.obj X) _⦋0⦌) :
    pathChains x (simplexChain v 1) =
      pathChain ℤ (pathTo x (TopCat.toSSetObj₀Equiv v)).toContinuousMap := by
  rw [pathChains, chainsDesc_simplexChain_one]

/-- The loop at the base point through a singular `1`-simplex. -/
private def loopPath (s : (TopCat.toSSet.obj X) _⦋1⦌) : Path x x :=
  (pathTo x (source₁ s)).trans ((path₁ s).trans (pathTo x (target₁ s)).symm)

/-- The `1`-chains of the loops through the simplices of a `1`-chain. -/
private def loopChains : ((singularChains ℤ).obj X).X 1 →ₗ[ℤ] ((singularChains ℤ).obj X).X 1 :=
  chainsDesc fun s ↦ pathChain ℤ (loopPath x s).toContinuousMap

private lemma loopChains_simplexChain (s : (TopCat.toSSet.obj X) _⦋1⦌) :
    loopChains x (simplexChain s 1) = pathChain ℤ (loopPath x s).toContinuousMap := by
  rw [loopChains, chainsDesc_simplexChain_one]

omit [PathConnectedSpace X] in
lemma pathChain_add_symm_mem_boundaries₁ {a b : X} (γ : Path a b) :
    pathChain ℤ γ.toContinuousMap + pathChain ℤ γ.symm.toContinuousMap ∈ boundaries₁ X := by
  have h₁ := pathChain_add_sub_trans_mem_boundaries₁ γ γ.symm
  have h₂ := pathChain_sub_mem_boundaries₁_of_homotopy (Path.Homotopy.reflTransSymm γ)
  have h₃ : pathChain ℤ (Path.refl a).toContinuousMap ∈ boundaries₁ X :=
    pathChain_const_mem_boundaries₁ a
  have := add_mem (sub_mem h₁ h₂) h₃
  convert this using 1
  abel

private lemma pathChain_loopPath_sub_mem_boundaries₁ (s : (TopCat.toSSet.obj X) _⦋1⦌) :
    pathChain ℤ (loopPath x s).toContinuousMap - simplexChain s 1 +
      (pathChain ℤ (pathTo x (target₁ s)).toContinuousMap -
        pathChain ℤ (pathTo x (source₁ s)).toContinuousMap) ∈
        boundaries₁ X := by
  have h₁ := pathChain_add_sub_trans_mem_boundaries₁ (pathTo x (source₁ s))
    ((path₁ s).trans (pathTo x (target₁ s)).symm)
  have h₂ := pathChain_add_sub_trans_mem_boundaries₁ (path₁ s) (pathTo x (target₁ s)).symm
  have h₃ := pathChain_add_symm_mem_boundaries₁ (pathTo x (target₁ s))
  have hs : pathChain ℤ (path₁ s).toContinuousMap = simplexChain s 1 := by
    rw [pathChain, simplex₁_path₁]
  have := sub_mem (sub_mem h₃ h₂) h₁
  rw [hs] at this
  convert this using 1
  rw [loopPath]
  abel

private lemma loopChains_sub_mem_boundaries₁ (c : ((singularChains ℤ).obj X).X 1) :
    loopChains x c - c + pathChains x (((singularChains ℤ).obj X).d 1 0 c) ∈ boundaries₁ X := by
  let φ : ((singularChains ℤ).obj X).X 1 →+
      ((singularChains ℤ).obj X).X 1 ⧸ (boundaries₁ X).toAddSubgroup :=
    (QuotientAddGroup.mk' _).comp (loopChains x - LinearMap.id +
      pathChains x ∘ₗ (((singularChains ℤ).obj X).d 1 0).hom).toAddMonoidHom
  have : φ = 0 := singularChains_addMonoidHom_ext fun s ↦ by
    simp only [φ, AddMonoidHom.zero_apply, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_zero_iff, Submodule.mem_toAddSubgroup, LinearMap.toAddMonoidHom_coe,
      LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
    -- The boundary of `s` is `[target₁ s] - [source₁ s]`, so `pathChains` sends it to the
    -- difference of the chains of the chosen paths to the two vertices.
    rw [singularChains_d_simplexChain (n := 0), Fin.sum_univ_two, map_add, map_zsmul, map_zsmul,
      pathChains_simplexChain, pathChains_simplexChain, toSSetObj₀Equiv_δ_zero,
      toSSetObj₀Equiv_δ_one, loopChains_simplexChain]
    convert pathChain_loopPath_sub_mem_boundaries₁ x s using 1
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul]
    abel
  exact (Submodule.mem_toAddSubgroup _).1 ((QuotientAddGroup.eq_zero_iff _).1
    (DFunLike.congr_fun this c))

private lemma loopChains_mem_cycles₁ (c : ((singularChains ℤ).obj X).X 1) :
    loopChains x c ∈ cycles₁ X := by
  have : (((singularChains ℤ).obj X).d 1 0).hom ∘ₗ loopChains x = 0 :=
    singularChains_linearMap_ext fun s ↦ by
      rw [LinearMap.comp_apply, loopChains_simplexChain, LinearMap.zero_apply]
      exact pathChain_mem_cycles₁ (loopPath x s)
  exact mem_cycles₁ (LinearMap.congr_fun this c)

omit [PathConnectedSpace X] in
/-- The Hurewicz map on the abelianized fundamental group, written additively. -/
def hurewiczAb : Additive (Abelianization (FundamentalGroup X x)) →+ H₁ X :=
  MonoidHom.toAdditiveLeft (Abelianization.lift (hurewicz₁ X x))

omit [PathConnectedSpace X] in
/-- On the abelianization, the Hurewicz map is induced by `TauCeti.HurewiczOne.hurewicz₁`. -/
@[simp]
lemma hurewiczAb_ofMul_of (g : FundamentalGroup X x) :
    hurewiczAb x (Additive.ofMul (Abelianization.of g)) =
      Multiplicative.toAdd (hurewicz₁ X x g) := by
  simp [hurewiczAb]

omit [PathConnectedSpace X] in
lemma hurewiczAb_ofMul_of_mk (γ : Path x x) :
    hurewiczAb x (Additive.ofMul ((Abelianization.of : FundamentalGroup X x →* _)
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)))) = loopClass γ := by
  simp [hurewiczAb]

private lemma hurewiczAb_inverseChains (c : ((singularChains ℤ).obj X).X 1) :
    hurewiczAb x (inverseChains x c) = H₁.mk ⟨_, loopChains_mem_cycles₁ x c⟩ := by
  let ψ : ((singularChains ℤ).obj X).X 1 →+ H₁ X :=
    (hurewiczAb x).comp (inverseChains x).toAddMonoidHom
  let ρ : ((singularChains ℤ).obj X).X 1 →+ H₁ X := ((sc₁ X).moduleCatLeftHomologyData.π.hom ∘ₗ
    (loopChains x).codRestrict (cycles₁ X) (loopChains_mem_cycles₁ x)).toAddMonoidHom
  have : ψ = ρ := singularChains_addMonoidHom_ext fun s ↦ by
    simp only [ψ, ρ, AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
      inverseChains_simplexChain]
    refine (hurewiczAb_ofMul_of_mk x (loopPath x s)).trans
      (congrArg H₁.mk (Subtype.ext (loopChains_simplexChain x s).symm))
  exact DFunLike.congr_fun this c

private lemma hurewiczAb_inverse₁ (h : H₁ X) : hurewiczAb x (inverse₁ x h) = h := by
  obtain ⟨z, rfl⟩ := H₁.mk_surjective h
  rw [inverse₁_mk, hurewiczAb_inverseChains, H₁.mk_eq_mk_iff]
  have hz : ((singularChains ℤ).obj X).d 1 0 z = 0 := mem_cycles₁_iff.1 z.2
  have := loopChains_sub_mem_boundaries₁ x z
  rw [hz, map_zero, add_zero] at this
  exact this

private lemma inverse₁_hurewiczAb (a : Additive (Abelianization (FundamentalGroup X x))) :
    inverse₁ x (hurewiczAb x a) = a := by
  induction a using Additive.rec with | ofMul a =>
  induction a using Quot.ind with | mk p =>
  obtain ⟨p⟩ := p
  induction p using Path.Homotopic.Quotient.ind with | mk γ =>
  rw [Abelianization.mk_eq_of]
  exact (congrArg (inverse₁ x) (hurewiczAb_ofMul_of_mk x γ)).trans (inverse₁_loopClass x γ)

/-- **The Hurewicz theorem in degree one**: for a path-connected space, the Hurewicz map
identifies the abelianized fundamental group with the first homology group, written as the
explicit homology of the short complex `C₂ → C₁ → C₀`. -/
def hurewiczAddEquiv : Additive (Abelianization (FundamentalGroup X x)) ≃+ H₁ X where
  __ := hurewiczAb x
  invFun := inverse₁ x
  left_inv := inverse₁_hurewiczAb x
  right_inv := hurewiczAb_inverse₁ x

@[simp]
lemma hurewiczAddEquiv_ofMul_of_mk (γ : Path x x) :
    hurewiczAddEquiv x (Additive.ofMul ((Abelianization.of : FundamentalGroup X x →* _)
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)))) = loopClass γ :=
  hurewiczAb_ofMul_of_mk x γ

lemma hurewiczAddEquiv_apply (a : Additive (Abelianization (FundamentalGroup X x))) :
    hurewiczAddEquiv x a = hurewiczAb x a := by
  rw [hurewiczAddEquiv]
  -- The forward map of `hurewiczAddEquiv` is `hurewiczAb` by construction.
  rfl

/-- The inverse of the Hurewicz isomorphism sends the class of a loop to its class in the
abelianized fundamental group. -/
@[simp]
lemma hurewiczAddEquiv_symm_loopClass (γ : Path x x) :
    (hurewiczAddEquiv x).symm (loopClass γ) =
      Additive.ofMul ((Abelianization.of : FundamentalGroup X x →* _)
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))) := by
  rw [AddEquiv.symm_apply_eq, hurewiczAddEquiv_ofMul_of_mk]

end Inverse

/-! ### Comparison with the homology of the singular chain complex -/

variable (X) in
/-- The explicit homology `H₁ X` of `sc₁ X` is the first homology group of the singular chain
complex. -/
def H₁AddEquivHomology : H₁ X ≃+ ((singularChains ℤ).obj X).homology 1 :=
  ((sc₁ X).moduleCatHomologyIso.symm ≪≫
    (((singularChains ℤ).obj X).homologyIsoSc' 2 1 0 (by simp) (by simp)).symm).toLinearEquiv
      |>.toAddEquiv

/-- The identification of `H₁ X` with the homology of the singular chain complex sends the class
of a cycle `c` to the homology class of the cycle of the complex lying over `c`. -/
lemma H₁AddEquivHomology_mk (c : cycles₁ X) (z : ((singularChains ℤ).obj X).cycles 1)
    (hz : (((singularChains ℤ).obj X).iCycles 1).hom z = c) :
    H₁AddEquivHomology X (H₁.mk c) = (((singularChains ℤ).obj X).homologyπ 1).hom z := by
  have hi : (ComplexShape.down ℕ).prev 1 = 2 := by simp
  have hk : (ComplexShape.down ℕ).next 1 = 0 := by simp
  have h₁ := congr($(((singularChains ℤ).obj X).cyclesIsoSc'_inv_iCycles 2 1 0 hi hk).hom
    ((sc₁ X).moduleCatCyclesIso.inv.hom c))
  have h₂ := congr($((sc₁ X).moduleCatCyclesIso_inv_iCycles).hom c)
  have h₃ := congr($((sc₁ X).moduleCatCyclesIso_inv_π).hom c)
  have h₄ := congr($(((singularChains ℤ).obj X).π_homologyIsoSc'_inv 2 1 0 hi hk).hom
    ((sc₁ X).moduleCatCyclesIso.inv.hom c))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h₁ h₂ h₃ h₄
  have hz₀ : z = (((singularChains ℤ).obj X).cyclesIsoSc' 2 1 0 hi hk).inv.hom
      ((sc₁ X).moduleCatCyclesIso.inv.hom c) :=
    HomologicalComplex.moduleCat_iCycles_injective _ 1 (hz.trans (h₁.trans h₂).symm)
  rw [hz₀, ← h₄]
  exact (congrArg (((singularChains ℤ).obj X).homologyIsoSc' 2 1 0 hi hk).inv.hom h₃).symm

/-- The identification of `H₁ X` with the homology of the singular chain complex sends the class
of a loop to the homology class of a cycle of the complex lying over the chain of the loop. -/
lemma H₁AddEquivHomology_loopClass {x : X} (γ : Path x x)
    (z : ((singularChains ℤ).obj X).cycles 1)
    (hz : (((singularChains ℤ).obj X).iCycles 1).hom z = pathChain ℤ γ.toContinuousMap) :
    H₁AddEquivHomology X (loopClass γ) = (((singularChains ℤ).obj X).homologyπ 1).hom z := by
  rw [loopClass]
  exact H₁AddEquivHomology_mk _ z hz

/-! ### The Hurewicz isomorphism -/

/-- **The Hurewicz theorem in degree one**: for a path-connected space `X` with a base point `x`,
the Hurewicz map identifies the abelianization of `π₁(X, x)` with `H₁(X; ℤ)`, the first homology
group of the singular chain complex of `X` with integer coefficients. -/
def hurewiczHomologyAddEquiv [PathConnectedSpace X] (x : X) :
    Additive (Abelianization (FundamentalGroup X x)) ≃+ ((singularChains ℤ).obj X).homology 1 :=
  (hurewiczAddEquiv x).trans (H₁AddEquivHomology X)

lemma hurewiczHomologyAddEquiv_apply [PathConnectedSpace X] {x : X}
    (a : Additive (Abelianization (FundamentalGroup X x))) :
    hurewiczHomologyAddEquiv x a = H₁AddEquivHomology X (hurewiczAb x a) := by
  rw [hurewiczHomologyAddEquiv, AddEquiv.trans_apply, hurewiczAddEquiv_apply]

@[simp]
lemma hurewiczHomologyAddEquiv_ofMul_of_mk [PathConnectedSpace X] {x : X} (γ : Path x x) :
    hurewiczHomologyAddEquiv x (Additive.ofMul ((Abelianization.of : FundamentalGroup X x →* _)
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)))) =
        H₁AddEquivHomology X (loopClass γ) := by
  simp [hurewiczHomologyAddEquiv]

end TauCeti.HurewiczOne
