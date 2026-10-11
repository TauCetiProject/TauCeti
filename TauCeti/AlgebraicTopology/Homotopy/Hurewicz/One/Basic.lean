/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.TopAdj
public import TauCeti.Topology.Homotopy.Path
public import TauCeti.Algebra.Homology.ModuleCat
public import TauCeti.Geometry.Convex.ConvexSpace.ContractibleSpaceStdSimplex
public import TauCeti.Geometry.Convex.ConvexSpace.Defs
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.GroupTheory.Abelianization.Defs

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

open CategoryTheory Convexity Simplicial unitInterval

namespace TauCeti.HurewiczOne

/-- The parametrization of the standard `1`-simplex by the unit interval, as a continuous map. -/
local notation "toI" => (StdSimplex.homeomorphI : C(StdSimplex ℝ (Fin 2), I))

/-- The point of the standard `1`-simplex with a given parameter, as a continuous map. -/
local notation "ofI" => (StdSimplex.homeomorphI.symm : C(I, StdSimplex ℝ (Fin 2)))

private lemma homeomorphI_eq (w : StdSimplex ℝ (Fin 2)) :
    StdSimplex.homeomorphI w = ⟨w.weights 1, w.weights_nonneg 1, w.weights_apply_le_one 1⟩ :=
  Subtype.ext (StdSimplex.homeomorphI_apply_coe w)

variable {X : TopCat.{0}}

/-- The singular `1`-simplex of a map from the unit interval. -/
def simplex₁ (g : C(I, X)) : (TopCat.toSSet.obj X) _⦋1⦌ :=
  (X.toSSetObjEquiv _).symm (g.comp toI)

@[simp]
lemma toSSetObjEquiv_simplex₁ (g : C(I, X)) :
    X.toSSetObjEquiv _ (simplex₁ g) = g.comp toI :=
  Equiv.apply_symm_apply _ _

/-- The `0`-th face of the standard `1`-simplex is its last vertex, of parameter `1`. -/
lemma homeomorphI_map_succAbove_zero (w : StdSimplex ℝ (Fin 1)) :
    StdSimplex.homeomorphI (StdSimplex.map (Fin.succAbove (0 : Fin 2)) w) = 1 := by
  refine Subtype.ext ?_
  rw [StdSimplex.homeomorphI_apply_coe, show (1 : Fin 2) = (0 : Fin 2).succAbove 0 from rfl,
    StdSimplex.weights_map_apply_of_injective Fin.succAbove_right_injective]
  simp

/-- The `1`-st face of the standard `1`-simplex is its first vertex, of parameter `0`. -/
lemma homeomorphI_map_succAbove_one (w : StdSimplex ℝ (Fin 1)) :
    StdSimplex.homeomorphI (StdSimplex.map (Fin.succAbove (1 : Fin 2)) w) = 0 :=
  Subtype.ext ((StdSimplex.homeomorphI_apply_coe _).trans
    (StdSimplex.weights_map_succAbove_self 1 w))

lemma δ_zero_simplex₁ (g : C(I, X)) :
    (TopCat.toSSet.obj X).δ 0 (simplex₁ g) = TopCat.toSSetObj₀Equiv.symm (g 1) := by
  apply (X.toSSetObjEquiv _).injective
  ext w
  rw [TopCat.toSSetObjEquiv_δ_apply, toSSetObjEquiv_simplex₁, ContinuousMap.comp_apply,
    ContinuousMap.coe_coe, homeomorphI_map_succAbove_zero, TopCat.toSSetObj₀Equiv_symm_apply,
    Equiv.apply_symm_apply]
  rfl

lemma δ_one_simplex₁ (g : C(I, X)) :
    (TopCat.toSSet.obj X).δ 1 (simplex₁ g) = TopCat.toSSetObj₀Equiv.symm (g 0) := by
  apply (X.toSSetObjEquiv _).injective
  ext w
  rw [TopCat.toSSetObjEquiv_δ_apply, toSSetObjEquiv_simplex₁, ContinuousMap.comp_apply,
    ContinuousMap.coe_coe, homeomorphI_map_succAbove_one, TopCat.toSSetObj₀Equiv_symm_apply,
    Equiv.apply_symm_apply]
  rfl

/-- The inclusion of the `i`-th facet of the standard `2`-simplex. -/
def face (i : Fin 3) : C(StdSimplex ℝ (Fin 2), StdSimplex ℝ (Fin 3)) :=
  ⟨StdSimplex.map i.succAbove, StdSimplex.continuous_map ℝ _⟩

section FaceWeights

variable (a : StdSimplex ℝ (Fin 2))

@[simp] lemma face_zero_weights_zero : (face 0 a).weights 0 = 0 :=
  StdSimplex.weights_map_succAbove_self 0 a
@[simp] lemma face_zero_weights_one : (face 0 a).weights 1 = a.weights 0 :=
  StdSimplex.weights_map_apply_of_injective (f := Fin.succAbove (0 : Fin 3))
    Fin.succAbove_right_injective a 0
@[simp] lemma face_zero_weights_two : (face 0 a).weights 2 = a.weights 1 :=
  StdSimplex.weights_map_apply_of_injective (f := Fin.succAbove (0 : Fin 3))
    Fin.succAbove_right_injective a 1
@[simp] lemma face_one_weights_zero : (face 1 a).weights 0 = a.weights 0 :=
  StdSimplex.weights_map_apply_of_injective (f := Fin.succAbove (1 : Fin 3))
    Fin.succAbove_right_injective a 0
@[simp] lemma face_one_weights_one : (face 1 a).weights 1 = 0 :=
  StdSimplex.weights_map_succAbove_self 1 a
@[simp] lemma face_one_weights_two : (face 1 a).weights 2 = a.weights 1 :=
  StdSimplex.weights_map_apply_of_injective (f := Fin.succAbove (1 : Fin 3))
    Fin.succAbove_right_injective a 1
@[simp] lemma face_two_weights_zero : (face 2 a).weights 0 = a.weights 0 :=
  StdSimplex.weights_map_apply_of_injective (f := Fin.succAbove (2 : Fin 3))
    Fin.succAbove_right_injective a 0
@[simp] lemma face_two_weights_one : (face 2 a).weights 1 = a.weights 1 :=
  StdSimplex.weights_map_apply_of_injective (f := Fin.succAbove (2 : Fin 3))
    Fin.succAbove_right_injective a 1
@[simp] lemma face_two_weights_two : (face 2 a).weights 2 = 0 :=
  StdSimplex.weights_map_succAbove_self 2 a

end FaceWeights

variable (X) in
/-- The singular chains of `X` with integer coefficients, in degree `n`. -/
abbrev Chains (n : ℕ) := ((singularChains ℤ).obj X).X n

/-- The chain of the singular `0`-simplex at a point. -/
abbrev chain₀ (p : X) : Chains X 0 := simplexChain (TopCat.toSSetObj₀Equiv.symm p) 1

/-- The chain of the singular `1`-simplex of a map from the unit interval. -/
abbrev chain₁ (g : C(I, X)) : Chains X 1 := simplexChain (simplex₁ g) 1

lemma d_chain₁ (g : C(I, X)) :
    ((singularChains ℤ).obj X).d 1 0 (chain₁ g) = chain₀ (g 1) - chain₀ (g 0) := by
  rw [singularChains_d_simplexChain (n := 0), Fin.sum_univ_two, δ_zero_simplex₁, δ_one_simplex₁]
  simp [sub_eq_add_neg]

/-- The chain of a singular `2`-simplex given as a continuous map from the standard simplex. -/
abbrev chain₂ (f : C(StdSimplex ℝ (Fin 3), X)) : Chains X 2 :=
  simplexChain ((X.toSSetObjEquiv (.op ⦋2⦌)).symm f) 1

lemma δ_toSSetObjEquiv_symm (f : C(StdSimplex ℝ (Fin 3), X)) (i : Fin 3) (g : C(I, X))
    (h : f.comp (face i) = g.comp toI) :
    (TopCat.toSSet.obj X).δ i ((X.toSSetObjEquiv (.op ⦋2⦌)).symm f) = simplex₁ g := by
  rw [simplex₁, ← h]
  exact TopCat.toSSetObjEquiv_symm_naturality (SimplexCategory.δ i) f

lemma d_chain₂ (f : C(StdSimplex ℝ (Fin 3), X)) (g₀ g₁ g₂ : C(I, X))
    (h₀ : f.comp (face 0) = g₀.comp toI)
    (h₁ : f.comp (face 1) = g₁.comp toI)
    (h₂ : f.comp (face 2) = g₂.comp toI) :
    ((singularChains ℤ).obj X).d 2 1 (chain₂ f) = chain₁ g₀ - chain₁ g₁ + chain₁ g₂ := by
  rw [singularChains_d_simplexChain (n := 1), Fin.sum_univ_three,
    δ_toSSetObjEquiv_symm f 0 g₀ h₀, δ_toSSetObjEquiv_symm f 1 g₁ h₁,
    δ_toSSetObjEquiv_symm f 2 g₂ h₂]
  simp [sub_eq_add_neg]

variable (X) in
/-- The short complex `C₂ → C₁ → C₀` of the singular chains of `X`. -/
abbrev sc₁ := ((singularChains ℤ).obj X).sc' 2 1 0

variable (X) in
/-- The boundaries among the singular `1`-chains of `X`. -/
abbrev boundaries₁ : Submodule ℤ (Chains X 1) :=
  LinearMap.range (((singularChains ℤ).obj X).d 2 1).hom

lemma mem_boundaries₁ {c : Chains X 1} (y : Chains X 2)
    (h : ((singularChains ℤ).obj X).d 2 1 y = c) : c ∈ boundaries₁ X :=
  ⟨y, h⟩

/-- The chain of a constant map is a boundary. -/
lemma chain₁_const_mem_boundaries₁ (p : X) : chain₁ (ContinuousMap.const I p) ∈ boundaries₁ X :=
  mem_boundaries₁ (chain₂ (ContinuousMap.const _ p)) (by
    rw [d_chain₂ _ (.const I p) (.const I p) (.const I p) rfl rfl rfl]
    abel)

/-- The affine projection of the standard `2`-simplex onto the unit interval sending the vertices
to `0`, `1/2` and `1`. -/
def concatProj : C(StdSimplex ℝ (Fin 3), I) :=
  ⟨fun w ↦ ⟨w.weights 1 / 2 + w.weights 2,
    add_nonneg (div_nonneg (w.weights_nonneg 1) zero_le_two) (w.weights_nonneg 2),
    by linarith [w.weights_one_add_two_le, w.weights_nonneg 1]⟩,
    (by fun_prop :
      Continuous fun w : StdSimplex ℝ (Fin 3) ↦ w.weights 1 / 2 + w.weights 2).subtype_mk _⟩

/-- The chain of a concatenation of paths differs from the sum of the chains of the two paths by
a boundary. -/
lemma chain₁_add_sub_trans_mem_boundaries₁ {a b c : X} (γ : Path a b) (δ : Path b c) :
    chain₁ γ.toContinuousMap + chain₁ δ.toContinuousMap - chain₁ (γ.trans δ).toContinuousMap ∈
      boundaries₁ X := by
  refine mem_boundaries₁ (chain₂ ((γ.trans δ).toContinuousMap.comp concatProj)) ?_
  rw [d_chain₂ _ δ.toContinuousMap (γ.trans δ).toContinuousMap γ.toContinuousMap]
  · abel
  · ext a
    exact Path.trans_apply_of_ge γ δ
      (by simp [concatProj]; linarith [a.total_fin_two, a.weights_nonneg 1]) _
      (by simp [concatProj, homeomorphI_eq]; linarith [a.total_fin_two])
  · ext a
    simp [concatProj, homeomorphI_eq]
  · ext a
    exact Path.trans_apply_of_le γ δ
      (by simp [concatProj]; linarith [a.total_fin_two, a.weights_nonneg 0]) _
      (by simp [concatProj, homeomorphI_eq]; ring)

/-- The weight of the last vertex of the standard `2`-simplex, as a point of the unit
interval. -/
def lastWeight : C(StdSimplex ℝ (Fin 3), I) :=
  ⟨fun w ↦ ⟨w.weights 2, w.weights_nonneg 2, w.weights_apply_le_one 2⟩,
    (StdSimplex.continuous_weights_apply ℝ 2).subtype_mk _⟩

/-- The sum of the weights of the last two vertices of the standard `2`-simplex, as a point of
the unit interval. -/
def lastTwoWeights : C(StdSimplex ℝ (Fin 3), I) :=
  ⟨fun w ↦ ⟨w.weights 1 + w.weights 2,
    add_nonneg (w.weights_nonneg 1) (w.weights_nonneg 2), w.weights_one_add_two_le⟩,
    (by fun_prop :
      Continuous fun w : StdSimplex ℝ (Fin 3) ↦ w.weights 1 + w.weights 2).subtype_mk _⟩

/-- The chains of homotopic paths differ by a boundary. -/
lemma chain₁_sub_mem_boundaries₁_of_homotopy {a b : X} {γ γ' : Path a b} (F : Path.Homotopy γ γ') :
    chain₁ γ.toContinuousMap - chain₁ γ'.toContinuousMap ∈ boundaries₁ X := by
  let D : C(I, X) := F.toContinuousMap.comp ⟨fun t ↦ (t, t), by fun_prop⟩
  have h₁ : chain₁ (.const I b) - chain₁ D + chain₁ γ.toContinuousMap ∈ boundaries₁ X := by
    refine mem_boundaries₁ (chain₂ (F.toContinuousMap.comp (lastWeight.prodMk lastTwoWeights))) ?_
    rw [d_chain₂ _ (.const I b) D γ.toContinuousMap]
    · ext x
      simp [lastWeight, lastTwoWeights]
    · ext x
      simp [lastWeight, lastTwoWeights, homeomorphI_eq, D]
    · ext x
      simp [lastWeight, lastTwoWeights, homeomorphI_eq]
  have h₂ : chain₁ γ'.toContinuousMap - chain₁ D + chain₁ (.const I a) ∈ boundaries₁ X := by
    refine mem_boundaries₁ (chain₂ (F.toContinuousMap.comp (lastTwoWeights.prodMk lastWeight))) ?_
    rw [d_chain₂ _ γ'.toContinuousMap D (.const I a)]
    · ext x
      simp [lastWeight, lastTwoWeights, homeomorphI_eq]
    · ext x
      simp [lastWeight, lastTwoWeights, homeomorphI_eq, D]
    · ext x
      simp [lastWeight, lastTwoWeights]
  have := sub_mem (add_mem (sub_mem h₁ h₂) (chain₁_const_mem_boundaries₁ a))
    (chain₁_const_mem_boundaries₁ b)
  convert this using 1
  abel

/-! ### Paths of singular `1`-simplices -/

/-- The first vertex of a singular `1`-simplex. -/
def src (s : (TopCat.toSSet.obj X) _⦋1⦌) : X := X.toSSetObjEquiv _ s (StdSimplex.single 0)

/-- The last vertex of a singular `1`-simplex. -/
def tgt (s : (TopCat.toSSet.obj X) _⦋1⦌) : X := X.toSSetObjEquiv _ s (StdSimplex.single 1)

/-- A singular `1`-simplex as a path from its first to its last vertex. -/
def simplexPath (s : (TopCat.toSSet.obj X) _⦋1⦌) : Path (src s) (tgt s) where
  toContinuousMap := (X.toSSetObjEquiv _ s).comp ofI
  source' := by simp [src]
  target' := by simp [tgt]

@[simp]
lemma simplex₁_simplexPath (s : (TopCat.toSSet.obj X) _⦋1⦌) :
    simplex₁ (simplexPath s).toContinuousMap = s := by
  apply (X.toSSetObjEquiv _).injective
  ext w
  simp [simplex₁, simplexPath]

@[simp]
lemma simplexPath_simplex₁_apply (g : C(I, X)) (t : I) : simplexPath (simplex₁ g) t = g t := by
  have : (X.toSSetObjEquiv _ (simplex₁ g)).comp ofI =
      g := by
    ext t
    simp [simplex₁]
  exact congr($this t)


/-! ### The Hurewicz map -/

section ModuleCat

variable {R : Type*} [Ring R] (S : ShortComplex (ModuleCat R))

/- These two facts are stated for an arbitrary ring: for `ℤ`, instance search on the cycles
`LinearMap.ker S.g.hom` finds `AddCommGroup.toIntModule`, which is only propositionally equal to
the submodule structure that `ShortComplex.moduleCatLeftHomologyData` uses. -/

private lemma π_hom_eq_iff (c c' : LinearMap.ker S.g.hom) :
    S.moduleCatLeftHomologyData.π.hom c = S.moduleCatLeftHomologyData.π.hom c' ↔
      ∃ y, S.f.hom y = (c : S.X₂) - c' :=
  (Submodule.Quotient.eq _).trans
    ⟨fun ⟨y, hy⟩ ↦ ⟨y, congrArg Subtype.val hy⟩, fun ⟨y, hy⟩ ↦ ⟨y, Subtype.ext hy⟩⟩

private lemma π_hom_surjective : Function.Surjective S.moduleCatLeftHomologyData.π.hom :=
  (ModuleCat.epi_iff_surjective _).1 inferInstance

end ModuleCat

variable (X) in
/-- The singular `1`-cycles of `X`, the kernel of the differential of `sc₁ X`. -/
abbrev cycles₁ : Submodule ℤ (Chains X 1) :=
  LinearMap.ker (sc₁ X).g.hom

variable (X) in
/-- The first singular homology group of `X` with integer coefficients, as the explicit homology
`cycles₁ X ⧸ boundaries` of `sc₁ X` in `ModuleCat ℤ`. -/
abbrev H₁ : ModuleCat ℤ := (sc₁ X).moduleCatLeftHomologyData.H

lemma mem_cycles₁ {c : Chains X 1} (h : ((singularChains ℤ).obj X).d 1 0 c = 0) :
    c ∈ cycles₁ X :=
  h

/-- The class in `H₁ X` of a `1`-cycle. -/
def H₁.mk (c : cycles₁ X) : H₁ X :=
  (sc₁ X).moduleCatLeftHomologyData.π.hom c

lemma H₁.mk_add (c c' : cycles₁ X) : H₁.mk (c + c') = H₁.mk c + H₁.mk c' := by
  rw [H₁.mk, H₁.mk, H₁.mk]
  exact map_add _ _ _

lemma H₁.mk_zero : H₁.mk (0 : cycles₁ X) = 0 := by
  rw [H₁.mk]
  exact map_zero _

lemma H₁.mk_eq_mk_iff (c c' : cycles₁ X) :
    H₁.mk c = H₁.mk c' ↔ (c : Chains X 1) - c' ∈ boundaries₁ X := by
  rw [H₁.mk, H₁.mk]
  exact (π_hom_eq_iff (sc₁ X) c c').trans LinearMap.mem_range.symm

lemma H₁.mk_eq_zero_iff (c : cycles₁ X) : H₁.mk c = 0 ↔ (c : Chains X 1) ∈ boundaries₁ X := by
  rw [← H₁.mk_zero, H₁.mk_eq_mk_iff, ZeroMemClass.coe_zero, sub_zero]

lemma H₁.mk_surjective : Function.Surjective (H₁.mk (X := X)) := by
  intro h
  obtain ⟨c, hc⟩ := π_hom_surjective (sc₁ X) h
  exact ⟨c, hc⟩

lemma chain₁_mem_cycles₁ {x : X} (γ : Path x x) : chain₁ γ.toContinuousMap ∈ cycles₁ X :=
  mem_cycles₁ (by rw [d_chain₁]; simp)

/-- The homology class of the chain of a loop. -/
def loopClass {x : X} (γ : Path x x) : H₁ X :=
  H₁.mk ⟨_, chain₁_mem_cycles₁ γ⟩

lemma loopClass_def {x : X} (γ : Path x x) :
    loopClass γ = H₁.mk ⟨_, chain₁_mem_cycles₁ γ⟩ := by
  rw [loopClass]

lemma loopClass_eq_iff {x : X} (γ γ' : Path x x) :
    loopClass γ = loopClass γ' ↔
      chain₁ γ.toContinuousMap - chain₁ γ'.toContinuousMap ∈ boundaries₁ X := by
  rw [loopClass, loopClass, H₁.mk_eq_mk_iff]

lemma loopClass_refl (x : X) : loopClass (Path.refl x) = 0 := by
  rw [loopClass, H₁.mk_eq_zero_iff]
  exact chain₁_const_mem_boundaries₁ x

lemma loopClass_trans {x : X} (γ δ : Path x x) :
    loopClass (γ.trans δ) = loopClass γ + loopClass δ := by
  rw [loopClass, loopClass, loopClass, ← H₁.mk_add, H₁.mk_eq_mk_iff]
  have := neg_mem (chain₁_add_sub_trans_mem_boundaries₁ γ δ)
  convert this using 1
  simp only [Submodule.coe_add]
  abel

variable (X) in
/-- **The Hurewicz map in degree one**: a loop is sent to the homology class of its chain. -/
def hurewicz₁ (x : X) : FundamentalGroup X x →* Multiplicative (H₁ X) where
  toFun := Quotient.lift (s := Path.Homotopic.setoid x x)
    (fun γ ↦ Multiplicative.ofAdd (loopClass γ)) fun γ γ' h ↦
      congrArg Multiplicative.ofAdd ((loopClass_eq_iff γ γ').2
        (chain₁_sub_mem_boundaries₁_of_homotopy h.some))
  map_one' := congrArg Multiplicative.ofAdd (loopClass_refl x)
  map_mul' p q := by
    refine Quotient.inductionOn₂ (s₁ := Path.Homotopic.setoid x x)
      (s₂ := Path.Homotopic.setoid x x) p q fun p q ↦ ?_
    -- The product `⟦p⟧ * ⟦q⟧` in the fundamental group is, by definition of the composition in
    -- the fundamental groupoid, the class of `q.trans p`, on which `Quotient.lift` computes.
    change Multiplicative.ofAdd (loopClass (q.trans p)) = _
    rw [loopClass_trans, add_comm]
    rfl

@[simp]
lemma hurewicz₁_mk {x : X} (γ : Path x x) :
    hurewicz₁ X x (Path.Homotopic.Quotient.mk γ) = Multiplicative.ofAdd (loopClass γ) := by
  rw [hurewicz₁]
  rfl

/-! ### The inverse map -/

section Inverse

variable [PathConnectedSpace X] (x : X)

/-- A chosen path from the base point to a point. -/
def pathTo (y : X) : Path x y := PathConnectedSpace.somePath x y

/-- The loop at the base point obtained from a path class `q` from `y` to `z` by going out to `y`
along the chosen path, along `q`, and back from `z` along the chosen path. -/
def loopThrough {y z : X} (q : Path.Homotopic.Quotient y z) : FundamentalGroup X x :=
  (Path.Homotopic.Quotient.mk (pathTo x y)).trans
    (q.trans (Path.Homotopic.Quotient.mk (pathTo x z)).symm)

lemma loopThrough_trans {y z w : X} (q : Path.Homotopic.Quotient y z)
    (q' : Path.Homotopic.Quotient z w) :
    (loopThrough x q).trans (loopThrough x q') = loopThrough x (q.trans q') := by
  simp only [loopThrough, Path.Homotopic.Quotient.trans_assoc,
    ← Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.symm _),
    Path.Homotopic.Quotient.symm_trans, Path.Homotopic.Quotient.refl_trans]

/-- The value of the inverse Hurewicz map on a singular `1`-simplex. -/
def inverseValue (s : (TopCat.toSSet.obj X) _⦋1⦌) :
    Additive (Abelianization (FundamentalGroup X x)) :=
  Additive.ofMul (Abelianization.of (loopThrough x (Path.Homotopic.Quotient.mk (simplexPath s))))

omit [PathConnectedSpace X] in
lemma ofMul_of_add_ofMul_of (p q : FundamentalGroup X x) :
    Additive.ofMul (Abelianization.of p) + Additive.ofMul (Abelianization.of q) =
      Additive.ofMul (Abelianization.of (q * p)) := by
  rw [← ofMul_mul, ← map_mul, map_mul, mul_comm, ← map_mul]

/-- The class of the image of a path between two points of a simply connected space. -/
def imageClass {Y : Type} [TopologicalSpace Y] [SimplyConnectedSpace Y] (g : C(Y, X)) (u v : Y) :
    FundamentalGroup X x :=
  loopThrough x ((Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath u v)).map g)

lemma loopThrough_map_eq_imageClass {Y : Type} [TopologicalSpace Y] [SimplyConnectedSpace Y]
    (g : C(Y, X)) {u v : Y} (γ : Path u v) :
    loopThrough x ((Path.Homotopic.Quotient.mk γ).map g) = imageClass x g u v := by
  rw [imageClass, Subsingleton.elim (Path.Homotopic.Quotient.mk γ)]

lemma imageClass_trans {Y : Type} [TopologicalSpace Y] [SimplyConnectedSpace Y] (g : C(Y, X))
    (u v w : Y) :
    (imageClass x g u v).trans (imageClass x g v w) = imageClass x g u w := by
  rw [imageClass, imageClass, loopThrough_trans, ← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_trans, ← Path.map_trans,
    Path.Homotopic.Quotient.mk_map, loopThrough_map_eq_imageClass]

/-- An edge of the standard `2`-simplex, as a path. -/
def edgePath (i : Fin 3) :
    Path (face i (StdSimplex.single 0)) (face i (StdSimplex.single 1)) where
  toContinuousMap := (face i).comp ofI
  source' := by simp
  target' := by simp

lemma inverseValue_δ (τ : (TopCat.toSSet.obj X) _⦋2⦌) (i : Fin 3) :
    inverseValue x ((TopCat.toSSet.obj X).δ i τ) =
      Additive.ofMul (Abelianization.of (imageClass x (X.toSSetObjEquiv _ τ)
        (face i (StdSimplex.single 0)) (face i (StdSimplex.single 1)))) := by
  have : simplexPath ((TopCat.toSSet.obj X).δ i τ) =
      (edgePath i).map (X.toSSetObjEquiv _ τ).continuous := by
    ext t
    rfl
  rw [inverseValue]
  exact congrArg (fun q ↦ Additive.ofMul (Abelianization.of q))
    ((congrArg (fun γ ↦ loopThrough x (Path.Homotopic.Quotient.mk γ)) this).trans
      (loopThrough_map_eq_imageClass x _ (edgePath i)))

lemma face_single (i : Fin 3) (j : Fin 2) :
    face i (StdSimplex.single j) = StdSimplex.single (i.succAbove j) :=
  StdSimplex.map_single _ _

/-- The values of the inverse map on the faces of a singular `2`-simplex satisfy the cocycle
relation. -/
lemma inverseValue_cocycle (τ : (TopCat.toSSet.obj X) _⦋2⦌) :
    inverseValue x ((TopCat.toSSet.obj X).δ 0 τ) - inverseValue x ((TopCat.toSSet.obj X).δ 1 τ) +
      inverseValue x ((TopCat.toSSet.obj X).δ 2 τ) = 0 := by
  simp only [inverseValue_δ, face_single]
  rw [sub_add_eq_add_sub, add_comm, ofMul_of_add_ofMul_of, sub_eq_zero]
  congr 2
  exact imageClass_trans x _ _ _ _

/-- The inverse Hurewicz map on singular `1`-chains. -/
def inverseChains : Chains X 1 →ₗ[ℤ] Additive (Abelianization (FundamentalGroup X x)) :=
  chainsDesc (inverseValue x)

lemma inverseChains_simplexChain (s : (TopCat.toSSet.obj X) _⦋1⦌) :
    inverseChains x (simplexChain s 1) = inverseValue x s := by
  rw [inverseChains, chainsDesc_simplexChain_one]

lemma inverseChains_d (y : Chains X 2) :
    inverseChains x (((singularChains ℤ).obj X).d 2 1 y) = 0 := by
  have := singularChains_linearMap_ext
    (L := inverseChains x ∘ₗ (((singularChains ℤ).obj X).d 2 1).hom) (L' := 0) fun τ ↦ by
      rw [LinearMap.comp_apply, singularChains_d_simplexChain (n := 1), Fin.sum_univ_three]
      simp only [map_add, map_zsmul, inverseChains_simplexChain]
      simpa [sub_eq_add_neg] using inverseValue_cocycle x τ
  exact LinearMap.congr_fun this y

/-- The inverse Hurewicz map on the `1`-cycles, as a morphism of `ℤ`-modules. The module structure
on the cycles is passed explicitly, as in `TauCeti.HurewiczOne.H₁.mk_eq_mk_iff`. -/
def inverseCycles :
    (sc₁ X).moduleCatLeftHomologyData.K ⟶ ModuleCat.of ℤ (Additive (Abelianization
      (FundamentalGroup X x))) :=
  @ModuleCat.ofHom ℤ _ _ _ _ (cycles₁ X).module _ _
    ((inverseChains x).comp (cycles₁ X).subtype)

lemma f'_inverseCycles : (sc₁ X).moduleCatLeftHomologyData.f' ≫ inverseCycles x = 0 :=
  ModuleCat.hom_ext (LinearMap.ext fun y ↦ inverseChains_d x y)

/-- **The inverse of the Hurewicz map in degree one**, on the first homology group. -/
def inverse₁ : H₁ X →ₗ[ℤ] Additive (Abelianization (FundamentalGroup X x)) :=
  ((sc₁ X).moduleCatLeftHomologyData.descH (inverseCycles x) (f'_inverseCycles x)).hom

lemma inverse₁_mk (c : cycles₁ X) : inverse₁ x (H₁.mk c) = inverseChains x c := by
  rw [inverse₁]
  exact congr($((sc₁ X).moduleCatLeftHomologyData.π_descH (inverseCycles x)
    (f'_inverseCycles x)).hom c)

omit [PathConnectedSpace X] in
lemma of_conj (p q : FundamentalGroup X x) :
    Abelianization.of (p⁻¹ * q * p) = Abelianization.of q := by
  rw [map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]

lemma ofMul_of_loopThrough_cast {y z : X} (hy : y = x) (hz : z = x)
    (q : Path.Homotopic.Quotient x x) :
    Additive.ofMul (Abelianization.of (loopThrough x (q.cast hy hz))) =
      Additive.ofMul ((Abelianization.of : FundamentalGroup X x →* _) q) := by
  subst hy hz
  rw [Path.Homotopic.Quotient.cast_rfl_rfl]
  exact congrArg Additive.ofMul (of_conj _ _ q)

/-- The inverse Hurewicz map sends the homology class of a loop back to the class of the loop. -/
lemma inverse₁_loopClass (γ : Path x x) :
    inverse₁ x (loopClass γ) =
      Additive.ofMul ((Abelianization.of : FundamentalGroup X x →* _)
        (Path.Homotopic.Quotient.mk γ)) := by
  have hs : src (simplex₁ γ.toContinuousMap) = x := by
    simpa using simplexPath_simplex₁_apply γ.toContinuousMap 0
  have ht : tgt (simplex₁ γ.toContinuousMap) = x := by
    simpa using simplexPath_simplex₁_apply γ.toContinuousMap 1
  have hγ : simplexPath (simplex₁ γ.toContinuousMap) = γ.cast hs ht := by
    ext t
    simp
  rw [loopClass, inverse₁_mk, inverseChains_simplexChain, inverseValue, hγ,
    Path.Homotopic.Quotient.mk_cast, ofMul_of_loopThrough_cast]

omit [PathConnectedSpace X] in
lemma toSSetObj₀Equiv_δ_zero (s : (TopCat.toSSet.obj X) _⦋1⦌) :
    TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj X).δ 0 s) = tgt s := by
  rw [TopCat.toSSetObj₀Equiv_apply, TopCat.toSSetObjEquiv_δ_apply, tgt,
    Subsingleton.elim default (StdSimplex.single 0), StdSimplex.map_single]
  rfl

omit [PathConnectedSpace X] in
lemma toSSetObj₀Equiv_δ_one (s : (TopCat.toSSet.obj X) _⦋1⦌) :
    TopCat.toSSetObj₀Equiv ((TopCat.toSSet.obj X).δ 1 s) = src s := by
  rw [TopCat.toSSetObj₀Equiv_apply, TopCat.toSSetObjEquiv_δ_apply, src,
    Subsingleton.elim default (StdSimplex.single 0), StdSimplex.map_single]
  rfl

/-- The `1`-chains of the chosen paths from the base point to the points of a `0`-chain. -/
def pathChains : Chains X 0 →ₗ[ℤ] Chains X 1 :=
  chainsDesc fun v ↦ chain₁ (pathTo x (TopCat.toSSetObj₀Equiv v)).toContinuousMap

lemma pathChains_simplexChain (v : (TopCat.toSSet.obj X) _⦋0⦌) :
    pathChains x (simplexChain v 1) =
      chain₁ (pathTo x (TopCat.toSSetObj₀Equiv v)).toContinuousMap := by
  rw [pathChains, chainsDesc_simplexChain_one]

/-- The loop at the base point through a singular `1`-simplex. -/
def loopPath (s : (TopCat.toSSet.obj X) _⦋1⦌) : Path x x :=
  (pathTo x (src s)).trans ((simplexPath s).trans (pathTo x (tgt s)).symm)

/-- The `1`-chains of the loops through the simplices of a `1`-chain. -/
def loopChains : Chains X 1 →ₗ[ℤ] Chains X 1 :=
  chainsDesc fun s ↦ chain₁ (loopPath x s).toContinuousMap

lemma loopChains_simplexChain (s : (TopCat.toSSet.obj X) _⦋1⦌) :
    loopChains x (simplexChain s 1) = chain₁ (loopPath x s).toContinuousMap := by
  rw [loopChains, chainsDesc_simplexChain_one]

omit [PathConnectedSpace X] in
lemma chain₁_add_symm_mem_boundaries₁ {a b : X} (γ : Path a b) :
    chain₁ γ.toContinuousMap + chain₁ γ.symm.toContinuousMap ∈ boundaries₁ X := by
  have h₁ := chain₁_add_sub_trans_mem_boundaries₁ γ γ.symm
  have h₂ := chain₁_sub_mem_boundaries₁_of_homotopy (Path.Homotopy.reflTransSymm γ)
  have h₃ : chain₁ (Path.refl a).toContinuousMap ∈ boundaries₁ X := chain₁_const_mem_boundaries₁ a
  have := add_mem (sub_mem h₁ h₂) h₃
  convert this using 1
  abel

lemma chain₁_loopPath_sub_mem_boundaries₁ (s : (TopCat.toSSet.obj X) _⦋1⦌) :
    chain₁ (loopPath x s).toContinuousMap - simplexChain s 1 +
      (chain₁ (pathTo x (tgt s)).toContinuousMap - chain₁ (pathTo x (src s)).toContinuousMap) ∈
        boundaries₁ X := by
  have h₁ := chain₁_add_sub_trans_mem_boundaries₁ (pathTo x (src s))
    ((simplexPath s).trans (pathTo x (tgt s)).symm)
  have h₂ := chain₁_add_sub_trans_mem_boundaries₁ (simplexPath s) (pathTo x (tgt s)).symm
  have h₃ := chain₁_add_symm_mem_boundaries₁ (pathTo x (tgt s))
  have hs : chain₁ (simplexPath s).toContinuousMap = simplexChain s 1 := by
    rw [chain₁, simplex₁_simplexPath]
  have := sub_mem (sub_mem h₃ h₂) h₁
  rw [hs] at this
  convert this using 1
  rw [loopPath]
  abel

lemma loopChains_sub_mem_boundaries₁ (c : Chains X 1) :
    loopChains x c - c + pathChains x (((singularChains ℤ).obj X).d 1 0 c) ∈ boundaries₁ X := by
  let φ : Chains X 1 →+ Chains X 1 ⧸ (boundaries₁ X).toAddSubgroup :=
    (QuotientAddGroup.mk' _).comp (loopChains x - LinearMap.id +
      pathChains x ∘ₗ (((singularChains ℤ).obj X).d 1 0).hom).toAddMonoidHom
  have : φ = 0 := singularChains_addMonoidHom_ext fun s ↦ by
    rw [AddMonoidHom.zero_apply, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_zero_iff, Submodule.mem_toAddSubgroup, LinearMap.toAddMonoidHom_coe,
      LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      singularChains_d_simplexChain (n := 0), Fin.sum_univ_two, map_add, map_zsmul, map_zsmul,
      pathChains_simplexChain, pathChains_simplexChain, toSSetObj₀Equiv_δ_zero,
      toSSetObj₀Equiv_δ_one, loopChains_simplexChain]
    convert chain₁_loopPath_sub_mem_boundaries₁ x s using 1
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul]
    abel
  exact (Submodule.mem_toAddSubgroup _).1 ((QuotientAddGroup.eq_zero_iff _).1
    (DFunLike.congr_fun this c))

lemma loopChains_mem_cycles₁ (c : Chains X 1) : loopChains x c ∈ cycles₁ X := by
  have : (((singularChains ℤ).obj X).d 1 0).hom ∘ₗ loopChains x = 0 :=
    singularChains_linearMap_ext fun s ↦ by
      rw [LinearMap.comp_apply, loopChains_simplexChain, LinearMap.zero_apply]
      exact chain₁_mem_cycles₁ (loopPath x s)
  exact mem_cycles₁ (LinearMap.congr_fun this c)

omit [PathConnectedSpace X] in
/-- The Hurewicz map on the abelianized fundamental group, written additively. -/
def hurewiczAb : Additive (Abelianization (FundamentalGroup X x)) →+ H₁ X :=
  MonoidHom.toAdditiveLeft (Abelianization.lift (hurewicz₁ X x))

omit [PathConnectedSpace X] in
lemma hurewiczAb_ofMul_of (γ : Path x x) :
    hurewiczAb x (Additive.ofMul ((Abelianization.of : FundamentalGroup X x →* _)
      (Path.Homotopic.Quotient.mk γ))) = loopClass γ := by
  simp [hurewiczAb]

lemma hurewiczAb_inverseChains (c : Chains X 1) :
    hurewiczAb x (inverseChains x c) = H₁.mk ⟨_, loopChains_mem_cycles₁ x c⟩ := by
  let ψ : Chains X 1 →+ H₁ X := (hurewiczAb x).comp (inverseChains x).toAddMonoidHom
  let ρ : Chains X 1 →+ H₁ X := ((sc₁ X).moduleCatLeftHomologyData.π.hom ∘ₗ
    (loopChains x).codRestrict (cycles₁ X) (loopChains_mem_cycles₁ x)).toAddMonoidHom
  have : ψ = ρ := singularChains_addMonoidHom_ext fun s ↦ by
    simp only [ψ, ρ, AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
      inverseChains_simplexChain]
    refine (hurewiczAb_ofMul_of x (loopPath x s)).trans
      (congrArg H₁.mk (Subtype.ext (loopChains_simplexChain x s).symm))
  exact DFunLike.congr_fun this c

lemma hurewiczAb_inverse₁ (h : H₁ X) : hurewiczAb x (inverse₁ x h) = h := by
  obtain ⟨z, rfl⟩ := H₁.mk_surjective h
  rw [inverse₁_mk, hurewiczAb_inverseChains, H₁.mk_eq_mk_iff]
  have hz : ((singularChains ℤ).obj X).d 1 0 z = 0 := z.2
  have := loopChains_sub_mem_boundaries₁ x z
  rw [hz, map_zero, add_zero] at this
  exact this

lemma inverse₁_hurewiczAb (a : Additive (Abelianization (FundamentalGroup X x))) :
    inverse₁ x (hurewiczAb x a) = a := by
  induction a using Additive.rec with | ofMul a =>
  induction a using Quot.ind with | mk p =>
  induction p using Path.Homotopic.Quotient.ind with | mk γ =>
  rw [Abelianization.mk_eq_of]
  exact (congrArg (inverse₁ x) (hurewiczAb_ofMul_of x γ)).trans (inverse₁_loopClass x γ)

/-- **The Hurewicz theorem in degree one**: for a path-connected space, the Hurewicz map
identifies the abelianized fundamental group with the first homology group, written as the
explicit homology of the short complex `C₂ → C₁ → C₀`. -/
def hurewiczAddEquiv : Additive (Abelianization (FundamentalGroup X x)) ≃+ H₁ X where
  __ := hurewiczAb x
  invFun := inverse₁ x
  left_inv := inverse₁_hurewiczAb x
  right_inv := hurewiczAb_inverse₁ x

@[simp]
lemma hurewiczAddEquiv_ofMul_of (γ : Path x x) :
    hurewiczAddEquiv x (Additive.ofMul ((Abelianization.of : FundamentalGroup X x →* _)
      (Path.Homotopic.Quotient.mk γ))) = loopClass γ :=
  hurewiczAb_ofMul_of x γ

lemma hurewiczAddEquiv_apply (a : Additive (Abelianization (FundamentalGroup X x))) :
    hurewiczAddEquiv x a = hurewiczAb x a := by
  rw [hurewiczAddEquiv]
  rfl

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
  rw [hurewiczHomologyAddEquiv, AddEquiv.trans_apply]
  rfl

lemma hurewiczHomologyAddEquiv_ofMul_of [PathConnectedSpace X] {x : X} (γ : Path x x) :
    hurewiczHomologyAddEquiv x (Additive.ofMul ((Abelianization.of : FundamentalGroup X x →* _)
      (Path.Homotopic.Quotient.mk γ))) = H₁AddEquivHomology X (loopClass γ) := by
  simp [hurewiczHomologyAddEquiv]

end TauCeti.HurewiczOne
