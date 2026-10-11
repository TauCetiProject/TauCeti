/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.ModuleChains
public import TauCeti.AlgebraicTopology.SimplicialSet.TopAdj
public import TauCeti.Geometry.Convex.ConvexSpace.ContractibleSpaceStdSimplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# The Hurewicz theorem in degree one

For a path-connected space `X` with a base point `x`, the Hurewicz map sends a loop at `x` to the
homology class of the singular `1`-simplex it defines, and it identifies the abelianization of
the fundamental group `π₁(X, x)` with the first singular homology group `H₁(X; ℤ)`
(`TauCeti.HurewiczOne.hurewiczHomologyEquiv`).

The proof is the one of Hatcher, Theorem 2A.1, carried out on the singular chains with integer
coefficients through the element-level interface of
`TauCeti.AlgebraicTopology.Singular.ModuleChains`.
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

The homology group is first described as `1`-cycles modulo boundaries (`TauCeti.HurewiczOne.H₁`)
and then identified with the homology of the singular chain complex in `ModuleCat ℤ`
(`TauCeti.HurewiczOne.H₁AddEquivHomology`).

## Main definitions and results

* `TauCeti.HurewiczOne.hurewicz₁`: the Hurewicz homomorphism `π₁(X, x) → H₁(X; ℤ)`.
* `TauCeti.HurewiczOne.hurewiczEquiv`: for path-connected `X`, it induces an isomorphism from the
  abelianization of `π₁(X, x)` onto the `1`-cycles modulo boundaries.
* `TauCeti.HurewiczOne.hurewiczHomologyEquiv`: the same isomorphism onto the first homology group
  of the singular chain complex of `X` with integer coefficients.

## References

* A. Hatcher, *Algebraic Topology*, Theorem 2A.1.
-/

public section

noncomputable section

open CategoryTheory Convexity Simplicial unitInterval

namespace TauCeti.HurewiczOne

/-- The parameter of the standard `1`-simplex: the weight of its second vertex. -/
def param₁ : C(StdSimplex ℝ (Fin 2), I) :=
  ⟨fun w ↦ ⟨w.weights 1, w.weights_nonneg 1, w.weights_apply_le_one 1⟩,
    (StdSimplex.continuous_weights_apply ℝ 1).subtype_mk _⟩

lemma weights_map_succAbove_succAbove {n : ℕ} (i : Fin (n + 2)) (w : StdSimplex ℝ (Fin (n + 1)))
    (j : Fin (n + 1)) :
    (StdSimplex.map i.succAbove w).weights (i.succAbove j) = w.weights j :=
  Finsupp.mapDomain_apply_of_injective Fin.succAbove_right_injective _ _

lemma weights_map_succAbove_self {n : ℕ} (i : Fin (n + 2)) (w : StdSimplex ℝ (Fin (n + 1))) :
    (StdSimplex.map i.succAbove w).weights i = 0 :=
  Finsupp.mapDomain_of_notMem_range _ _ (by simp)

lemma weights_add_three (w : StdSimplex ℝ (Fin 3)) :
    w.weights 0 + w.weights 1 + w.weights 2 = 1 := by
  rw [← w.total_of_fintype, Fin.sum_univ_three]

variable {X : TopCat.{0}}

lemma toSSetObjEquiv_δ {n : ℕ} (s : (TopCat.toSSet.obj X) _⦋n + 1⦌) (i : Fin (n + 2)) :
    X.toSSetObjEquiv _ ((TopCat.toSSet.obj X).δ i s) =
      (X.toSSetObjEquiv _ s).comp ⟨StdSimplex.map i.succAbove, StdSimplex.continuous_map ℝ _⟩ :=
  rfl

/-- The singular `0`-simplex at a point. -/
def simplex₀ (p : X) : (TopCat.toSSet.obj X) _⦋0⦌ :=
  (X.toSSetObjEquiv _).symm (ContinuousMap.const _ p)

/-- The singular `1`-simplex of a map from the unit interval. -/
def simplex₁ (g : C(I, X)) : (TopCat.toSSet.obj X) _⦋1⦌ :=
  (X.toSSetObjEquiv _).symm (g.comp param₁)

lemma toSSetObjEquiv_simplex₁ (g : C(I, X)) :
    X.toSSetObjEquiv _ (simplex₁ g) = g.comp param₁ :=
  Equiv.apply_symm_apply _ _

lemma δ_zero_simplex₁ (g : C(I, X)) : (TopCat.toSSet.obj X).δ 0 (simplex₁ g) = simplex₀ (g 1) := by
  apply (X.toSSetObjEquiv _).injective
  ext w
  rw [toSSetObjEquiv_δ]
  simp only [simplex₁, simplex₀, Equiv.apply_symm_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, ContinuousMap.const_apply]
  congr 1
  ext
  change (StdSimplex.map (Fin.succAbove 0) w).weights ((0 : Fin 2).succAbove 0) = 1
  rw [weights_map_succAbove_succAbove]
  simp

lemma δ_one_simplex₁ (g : C(I, X)) : (TopCat.toSSet.obj X).δ 1 (simplex₁ g) = simplex₀ (g 0) := by
  apply (X.toSSetObjEquiv _).injective
  ext w
  rw [toSSetObjEquiv_δ]
  simp only [simplex₁, simplex₀, Equiv.apply_symm_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk, ContinuousMap.const_apply]
  congr 1
  ext
  change (StdSimplex.map (Fin.succAbove 1) w).weights 1 = 0
  exact weights_map_succAbove_self 1 w

/-- The inclusion of the `i`-th facet of the standard `2`-simplex. -/
def face (i : Fin 3) : C(StdSimplex ℝ (Fin 2), StdSimplex ℝ (Fin 3)) :=
  ⟨StdSimplex.map i.succAbove, StdSimplex.continuous_map ℝ _⟩

section FaceWeights

variable (a : StdSimplex ℝ (Fin 2))

@[simp] lemma face_zero_weights_zero : (face 0 a).weights 0 = 0 := weights_map_succAbove_self 0 a
@[simp] lemma face_zero_weights_one : (face 0 a).weights 1 = a.weights 0 :=
  weights_map_succAbove_succAbove (0 : Fin 3) a 0
@[simp] lemma face_zero_weights_two : (face 0 a).weights 2 = a.weights 1 :=
  weights_map_succAbove_succAbove (0 : Fin 3) a 1
@[simp] lemma face_one_weights_zero : (face 1 a).weights 0 = a.weights 0 :=
  weights_map_succAbove_succAbove (1 : Fin 3) a 0
@[simp] lemma face_one_weights_one : (face 1 a).weights 1 = 0 := weights_map_succAbove_self 1 a
@[simp] lemma face_one_weights_two : (face 1 a).weights 2 = a.weights 1 :=
  weights_map_succAbove_succAbove (1 : Fin 3) a 1
@[simp] lemma face_two_weights_zero : (face 2 a).weights 0 = a.weights 0 :=
  weights_map_succAbove_succAbove (2 : Fin 3) a 0
@[simp] lemma face_two_weights_one : (face 2 a).weights 1 = a.weights 1 :=
  weights_map_succAbove_succAbove (2 : Fin 3) a 1
@[simp] lemma face_two_weights_two : (face 2 a).weights 2 = 0 := weights_map_succAbove_self 2 a

end FaceWeights

variable (X) in
/-- The singular chains of `X` with integer coefficients, in degree `n`. -/
abbrev Chains (n : ℕ) := ((singularChains ℤ).obj X).X n

/-- The chain of the singular `0`-simplex at a point. -/
abbrev chain₀ (p : X) : Chains X 0 := simplexChain (simplex₀ p) 1

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
    (h : f.comp (face i) = g.comp param₁) :
    (TopCat.toSSet.obj X).δ i ((X.toSSetObjEquiv (.op ⦋2⦌)).symm f) = simplex₁ g := by
  apply (X.toSSetObjEquiv _).injective
  rw [toSSetObjEquiv_δ, Equiv.apply_symm_apply, simplex₁, Equiv.apply_symm_apply]
  exact h

lemma d_chain₂ (f : C(StdSimplex ℝ (Fin 3), X)) (g₀ g₁ g₂ : C(I, X))
    (h₀ : f.comp (face 0) = g₀.comp param₁) (h₁ : f.comp (face 1) = g₁.comp param₁)
    (h₂ : f.comp (face 2) = g₂.comp param₁) :
    ((singularChains ℤ).obj X).d 2 1 (chain₂ f) = chain₁ g₀ - chain₁ g₁ + chain₁ g₂ := by
  rw [singularChains_d_simplexChain (n := 1), Fin.sum_univ_three,
    δ_toSSetObjEquiv_symm f 0 g₀ h₀, δ_toSSetObjEquiv_symm f 1 g₁ h₁,
    δ_toSSetObjEquiv_symm f 2 g₂ h₂]
  simp [sub_eq_add_neg]

variable (X) in
/-- The boundaries among the singular `1`-chains of `X`. -/
abbrev boundaries₁ : AddSubgroup (Chains X 1) :=
  (((singularChains ℤ).obj X).d 2 1).hom.toAddMonoidHom.range

lemma mem_boundaries₁ {c : Chains X 1} (y : Chains X 2)
    (h : ((singularChains ℤ).obj X).d 2 1 y = c) : c ∈ boundaries₁ X :=
  ⟨y, h⟩

/-- The chain of a constant map is a boundary. -/
lemma chain₁_const_mem (p : X) : chain₁ (ContinuousMap.const I p) ∈ boundaries₁ X :=
  mem_boundaries₁ (chain₂ (ContinuousMap.const _ p)) (by
    rw [d_chain₂ _ (.const I p) (.const I p) (.const I p) rfl rfl rfl]
    abel)

lemma weights_one_add_two_le (w : StdSimplex ℝ (Fin 3)) : w.weights 1 + w.weights 2 ≤ 1 := by
  linarith [weights_add_three w, w.weights_nonneg 0]

/-- The affine projection of the standard `2`-simplex onto the unit interval sending the vertices
to `0`, `1/2` and `1`. -/
def concatProj : C(StdSimplex ℝ (Fin 3), I) :=
  ⟨fun w ↦ ⟨w.weights 1 / 2 + w.weights 2,
    add_nonneg (div_nonneg (w.weights_nonneg 1) zero_le_two) (w.weights_nonneg 2),
    by linarith [weights_one_add_two_le w, w.weights_nonneg 1]⟩,
    (by fun_prop :
      Continuous fun w : StdSimplex ℝ (Fin 3) ↦ w.weights 1 / 2 + w.weights 2).subtype_mk _⟩

lemma trans_apply_of_eq_left {a b c : X} (γ : Path a b) (δ : Path b c) {s t : I}
    (h : (s : ℝ) = t / 2) : γ.trans δ s = γ t := by
  rw [Path.trans_apply]
  split_ifs with hs
  · congr 1
    ext
    simp [h]; ring
  · exact absurd (by rw [h]; linarith [t.2.2]) hs

lemma trans_apply_of_eq_right {a b c : X} (γ : Path a b) (δ : Path b c) {s t : I}
    (h : (s : ℝ) = (1 + t) / 2) : γ.trans δ s = δ t := by
  rw [Path.trans_apply]
  split_ifs with hs
  · have ht : (t : ℝ) = 0 := by linarith [t.2.1]
    have : t = 0 := Subtype.ext ht
    subst this
    rw [show (⟨2 * s, _⟩ : I) = 1 from Subtype.ext (by simp [h]), γ.target, δ.source]
  · congr 1
    ext
    simp [h]; ring

/-- The chain of a concatenation of paths differs from the sum of the chains of the two paths by
a boundary. -/
lemma chain₁_add_sub_trans_mem {a b c : X} (γ : Path a b) (δ : Path b c) :
    chain₁ γ.toContinuousMap + chain₁ δ.toContinuousMap - chain₁ (γ.trans δ).toContinuousMap ∈
      boundaries₁ X := by
  refine mem_boundaries₁ (chain₂ ((γ.trans δ).toContinuousMap.comp concatProj)) ?_
  rw [d_chain₂ _ δ.toContinuousMap (γ.trans δ).toContinuousMap γ.toContinuousMap]
  · abel
  · ext a
    exact trans_apply_of_eq_right γ δ (by
      simp [concatProj, param₁]; linarith [a.total_fin_two])
  · ext a
    simp [concatProj, param₁]
  · ext a
    exact trans_apply_of_eq_left γ δ (by simp [concatProj, param₁])

/-- The weight of the last vertex of the standard `2`-simplex, as a point of the unit
interval. -/
def lastWeight : C(StdSimplex ℝ (Fin 3), I) :=
  ⟨fun w ↦ ⟨w.weights 2, w.weights_nonneg 2, w.weights_apply_le_one 2⟩,
    (StdSimplex.continuous_weights_apply ℝ 2).subtype_mk _⟩

/-- The sum of the weights of the last two vertices of the standard `2`-simplex, as a point of
the unit interval. -/
def lastTwoWeights : C(StdSimplex ℝ (Fin 3), I) :=
  ⟨fun w ↦ ⟨w.weights 1 + w.weights 2,
    add_nonneg (w.weights_nonneg 1) (w.weights_nonneg 2), weights_one_add_two_le w⟩,
    (by fun_prop :
      Continuous fun w : StdSimplex ℝ (Fin 3) ↦ w.weights 1 + w.weights 2).subtype_mk _⟩

/-- The chains of homotopic paths differ by a boundary: the square of the homotopy is cut along
its diagonal into two singular `2`-simplices. -/
lemma chain₁_sub_mem_of_homotopy {a b : X} {γ γ' : Path a b} (F : Path.Homotopy γ γ') :
    chain₁ γ.toContinuousMap - chain₁ γ'.toContinuousMap ∈ boundaries₁ X := by
  let D : C(I, X) := F.toContinuousMap.comp ⟨fun t ↦ (t, t), by fun_prop⟩
  have h₁ : chain₁ (.const I b) - chain₁ D + chain₁ γ.toContinuousMap ∈ boundaries₁ X := by
    refine mem_boundaries₁ (chain₂ (F.toContinuousMap.comp (lastWeight.prodMk lastTwoWeights))) ?_
    rw [d_chain₂ _ (.const I b) D γ.toContinuousMap]
    · ext x
      simp [lastWeight, lastTwoWeights, param₁]
    · ext x
      simp [lastWeight, lastTwoWeights, param₁, D]
    · ext x
      simp [lastWeight, lastTwoWeights, param₁]
  have h₂ : chain₁ γ'.toContinuousMap - chain₁ D + chain₁ (.const I a) ∈ boundaries₁ X := by
    refine mem_boundaries₁ (chain₂ (F.toContinuousMap.comp (lastTwoWeights.prodMk lastWeight))) ?_
    rw [d_chain₂ _ γ'.toContinuousMap D (.const I a)]
    · ext x
      simp [lastWeight, lastTwoWeights, param₁]
    · ext x
      simp [lastWeight, lastTwoWeights, param₁, D]
    · ext x
      simp [lastWeight, lastTwoWeights, param₁]
  have := sub_mem (add_mem (sub_mem h₁ h₂) (chain₁_const_mem a)) (chain₁_const_mem b)
  convert this using 1
  abel

/-! ### Paths of singular `1`-simplices -/

lemma equivIcc_symm_weights_zero (t : I) :
    (StdSimplex.equivIcc.symm t).weights 0 = 1 - t := by
  simp [StdSimplex.equivIcc_symm_apply]

lemma equivIcc_symm_weights_one (t : I) : (StdSimplex.equivIcc.symm t).weights 1 = t := by
  simp [StdSimplex.equivIcc_symm_apply]

/-- The inverse of `param₁`: the point of the standard `1`-simplex with parameter `t`. -/
def paramInv : C(I, StdSimplex ℝ (Fin 2)) :=
  ⟨StdSimplex.equivIcc.symm, by
    rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin 2)).continuous_iff, continuous_pi_iff]
    intro i
    fin_cases i
    · exact (continuous_const.sub continuous_subtype_val).congr
        fun t ↦ (equivIcc_symm_weights_zero t).symm
    · exact continuous_subtype_val.congr fun t ↦ (equivIcc_symm_weights_one t).symm⟩

@[simp]
lemma param₁_paramInv (t : I) : param₁ (paramInv t) = t :=
  StdSimplex.equivIcc.apply_symm_apply t

@[simp]
lemma paramInv_param₁ (w : StdSimplex ℝ (Fin 2)) : paramInv (param₁ w) = w :=
  StdSimplex.equivIcc.symm_apply_apply w

@[simp]
lemma paramInv_zero : paramInv 0 = StdSimplex.single 0 := StdSimplex.equivIcc_symm_zero

@[simp]
lemma paramInv_one : paramInv 1 = StdSimplex.single 1 := StdSimplex.equivIcc_symm_one

/-- The first vertex of a singular `1`-simplex. -/
def src (s : (TopCat.toSSet.obj X) _⦋1⦌) : X := X.toSSetObjEquiv _ s (StdSimplex.single 0)

/-- The last vertex of a singular `1`-simplex. -/
def tgt (s : (TopCat.toSSet.obj X) _⦋1⦌) : X := X.toSSetObjEquiv _ s (StdSimplex.single 1)

/-- A singular `1`-simplex as a path from its first to its last vertex. -/
def simplexPath (s : (TopCat.toSSet.obj X) _⦋1⦌) : Path (src s) (tgt s) where
  toContinuousMap := (X.toSSetObjEquiv _ s).comp paramInv
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
  have : (X.toSSetObjEquiv _ (simplex₁ g)).comp paramInv = g := by
    ext t
    simp [simplex₁]
  exact congr($this t)

/-! ### Linear maps out of singular chains -/

/-- The linear map out of the singular `n`-chains with the given values on singular simplices. -/
def chainsDesc {n : ℕ} {V : Type} [AddCommGroup V] (f : (TopCat.toSSet.obj X) _⦋n⦌ → V) :
    Chains X n →ₗ[ℤ] V :=
  (Limits.Cofan.IsColimit.desc
    ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
    (fun s ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ V (f s)))).hom

@[simp]
lemma chainsDesc_simplexChain {n : ℕ} {V : Type} [AddCommGroup V]
    (f : (TopCat.toSSet.obj X) _⦋n⦌ → V) (s : (TopCat.toSSet.obj X) _⦋n⦌) (a : ℤ) :
    chainsDesc f (simplexChain s a) = a • f s := by
  have h := Limits.Cofan.IsColimit.fac
    ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
    (fun s ↦ ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ V (f s))) s
  simp only [SSet.chainComplexXCofan, Limits.Cofan.inj, Limits.Cofan.mk_ι_app] at h
  exact congrArg (fun g ↦ g.hom a) h

/-! ### The Hurewicz map -/

variable (X) in
/-- The singular `1`-cycles of `X`. -/
abbrev cycles₁ : AddSubgroup (Chains X 1) :=
  (((singularChains ℤ).obj X).d 1 0).hom.toAddMonoidHom.ker

variable (X) in
/-- The first singular homology group of `X` with integer coefficients, as the quotient of the
`1`-cycles by the boundaries. -/
abbrev H₁ := cycles₁ X ⧸ (boundaries₁ X).addSubgroupOf (cycles₁ X)

lemma mem_cycles₁ {c : Chains X 1} (h : ((singularChains ℤ).obj X).d 1 0 c = 0) :
    c ∈ cycles₁ X :=
  h

lemma chain₁_mem_cycles₁ {x : X} (γ : Path x x) : chain₁ γ.toContinuousMap ∈ cycles₁ X :=
  mem_cycles₁ (by rw [d_chain₁]; simp)

/-- The homology class of the chain of a loop. -/
def loopClass {x : X} (γ : Path x x) : H₁ X :=
  QuotientAddGroup.mk ⟨_, chain₁_mem_cycles₁ γ⟩

lemma loopClass_def {x : X} (γ : Path x x) :
    loopClass γ = QuotientAddGroup.mk ⟨_, chain₁_mem_cycles₁ γ⟩ := by
  rw [loopClass]

lemma loopClass_eq_iff {x : X} (γ γ' : Path x x) :
    loopClass γ = loopClass γ' ↔
      chain₁ γ.toContinuousMap - chain₁ γ'.toContinuousMap ∈ boundaries₁ X := by
  rw [loopClass, loopClass, QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf]
  rfl

lemma loopClass_refl (x : X) : loopClass (Path.refl x) = 0 :=
  (QuotientAddGroup.eq_zero_iff _).2
    ((AddSubgroup.mem_addSubgroupOf).2 (chain₁_const_mem x))

lemma loopClass_trans {x : X} (γ δ : Path x x) :
    loopClass (γ.trans δ) = loopClass γ + loopClass δ := by
  rw [loopClass, loopClass, loopClass, ← QuotientAddGroup.mk_add,
    QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf]
  have := neg_mem (chain₁_add_sub_trans_mem γ δ)
  convert this using 1
  simp only [AddSubgroupClass.coe_sub, AddSubgroup.coe_add]
  abel

variable (X) in
/-- **The Hurewicz map in degree one**: a loop is sent to the homology class of its chain. -/
@[expose] def hurewicz₁ (x : X) : FundamentalGroup X x →* Multiplicative (H₁ X) where
  toFun := Quotient.lift (s := Path.Homotopic.setoid x x)
    (fun γ ↦ Multiplicative.ofAdd (loopClass γ)) fun γ γ' h ↦
      congrArg Multiplicative.ofAdd ((loopClass_eq_iff γ γ').2
        (chain₁_sub_mem_of_homotopy h.some))
  map_one' := congrArg Multiplicative.ofAdd (loopClass_refl x)
  map_mul' p q := by
    refine Quotient.inductionOn₂ (s₁ := Path.Homotopic.setoid x x)
      (s₂ := Path.Homotopic.setoid x x) p q fun p q ↦ ?_
    change Multiplicative.ofAdd (loopClass (q.trans p)) = _
    rw [loopClass_trans, add_comm]
    rfl

@[simp]
lemma hurewicz₁_mk {x : X} (γ : Path x x) :
    hurewicz₁ X x (Path.Homotopic.Quotient.mk γ) = Multiplicative.ofAdd (loopClass γ) :=
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
  toContinuousMap := (face i).comp paramInv
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

lemma inverseChains_d (y : Chains X 2) :
    inverseChains x (((singularChains ℤ).obj X).d 2 1 y) = 0 := by
  have := singularChains_linearMap_ext
    (L := inverseChains x ∘ₗ (((singularChains ℤ).obj X).d 2 1).hom) (L' := 0) fun τ ↦ by
      rw [LinearMap.comp_apply, singularChains_d_simplexChain (n := 1), Fin.sum_univ_three]
      simp only [map_add, map_zsmul, inverseChains, chainsDesc_simplexChain, one_smul]
      simpa [sub_eq_add_neg] using inverseValue_cocycle x τ
  exact LinearMap.congr_fun this y

/-- **The inverse of the Hurewicz map in degree one**, on the first homology group. -/
def inverse₁ : H₁ X →+ Additive (Abelianization (FundamentalGroup X x)) :=
  QuotientAddGroup.lift _ ((inverseChains x).toAddMonoidHom.comp (cycles₁ X).subtype)
    fun c hc ↦ by
      obtain ⟨y, hy⟩ := AddSubgroup.mem_addSubgroupOf.1 hc
      simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, Function.comp_apply,
        AddSubgroup.coe_subtype, LinearMap.toAddMonoidHom_coe]
      rw [← hy]
      exact inverseChains_d x y

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
  change inverseChains x (chain₁ γ.toContinuousMap) = _
  rw [inverseChains, chainsDesc_simplexChain, one_smul, inverseValue, hγ,
    Path.Homotopic.Quotient.mk_cast, ofMul_of_loopThrough_cast]

omit [PathConnectedSpace X] in
/-- Additive maps out of singular chains agree when they agree on simplices. -/
lemma chains_addMonoidHom_ext {n : ℕ} {V : Type} [AddCommGroup V] {f g : Chains X n →+ V}
    (h : ∀ s, f (simplexChain s 1) = g (simplexChain s 1)) : f = g := by
  let lin (φ : Chains X n →+ V) : Chains X n →ₗ[ℤ] V :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' a c := by
        rw [RingHom.id_apply]
        exact (congrArg φ (int_smul_eq_zsmul _ a c)).trans (map_zsmul φ a c) }
  have := singularChains_linearMap_ext (L := lin f) (L' := lin g) h
  exact AddMonoidHom.ext fun c ↦ LinearMap.congr_fun this c

/-- The point of a singular `0`-simplex. -/
def point (v : (TopCat.toSSet.obj X) _⦋0⦌) : X := X.toSSetObjEquiv _ v (StdSimplex.single 0)

omit [PathConnectedSpace X] in
lemma point_δ_zero (s : (TopCat.toSSet.obj X) _⦋1⦌) :
    point ((TopCat.toSSet.obj X).δ 0 s) = tgt s := by
  change X.toSSetObjEquiv _ s (StdSimplex.map (Fin.succAbove 0) (StdSimplex.single 0)) = _
  rw [StdSimplex.map_single]
  rfl

omit [PathConnectedSpace X] in
lemma point_δ_one (s : (TopCat.toSSet.obj X) _⦋1⦌) :
    point ((TopCat.toSSet.obj X).δ 1 s) = src s := by
  change X.toSSetObjEquiv _ s (StdSimplex.map (Fin.succAbove 1) (StdSimplex.single 0)) = _
  rw [StdSimplex.map_single]
  rfl

/-- The `1`-chains of the chosen paths from the base point to the points of a `0`-chain. -/
def pathChains : Chains X 0 →+ Chains X 1 :=
  (chainsDesc (V := Chains X 1) fun v ↦ chain₁ (pathTo x (point v)).toContinuousMap).toAddMonoidHom

/-- The loop at the base point through a singular `1`-simplex. -/
def loopPath (s : (TopCat.toSSet.obj X) _⦋1⦌) : Path x x :=
  (pathTo x (src s)).trans ((simplexPath s).trans (pathTo x (tgt s)).symm)

/-- The `1`-chains of the loops through the simplices of a `1`-chain. -/
def loopChains : Chains X 1 →+ Chains X 1 :=
  (chainsDesc (V := Chains X 1) fun s ↦ chain₁ (loopPath x s).toContinuousMap).toAddMonoidHom

omit [PathConnectedSpace X] in
lemma chain₁_add_symm_mem {a b : X} (γ : Path a b) :
    chain₁ γ.toContinuousMap + chain₁ γ.symm.toContinuousMap ∈ boundaries₁ X := by
  have h₁ := chain₁_add_sub_trans_mem γ γ.symm
  have h₂ := chain₁_sub_mem_of_homotopy (Path.Homotopy.reflTransSymm γ)
  have h₃ : chain₁ (Path.refl a).toContinuousMap ∈ boundaries₁ X := chain₁_const_mem a
  have := add_mem (sub_mem h₁ h₂) h₃
  convert this using 1
  abel

lemma loopChain_sub_mem (s : (TopCat.toSSet.obj X) _⦋1⦌) :
    chain₁ (loopPath x s).toContinuousMap - simplexChain s 1 +
      (chain₁ (pathTo x (tgt s)).toContinuousMap - chain₁ (pathTo x (src s)).toContinuousMap) ∈
        boundaries₁ X := by
  have h₁ := chain₁_add_sub_trans_mem (pathTo x (src s))
    ((simplexPath s).trans (pathTo x (tgt s)).symm)
  have h₂ := chain₁_add_sub_trans_mem (simplexPath s) (pathTo x (tgt s)).symm
  have h₃ := chain₁_add_symm_mem (pathTo x (tgt s))
  have hs : chain₁ (simplexPath s).toContinuousMap = simplexChain s 1 := by
    rw [chain₁, simplex₁_simplexPath]
  have := sub_mem (sub_mem h₃ h₂) h₁
  rw [hs] at this
  convert this using 1
  rw [loopPath]
  abel

lemma loopChains_sub_mem (c : Chains X 1) :
    loopChains x c - c + pathChains x (((singularChains ℤ).obj X).d 1 0 c) ∈ boundaries₁ X := by
  let φ : Chains X 1 →+ Chains X 1 ⧸ boundaries₁ X :=
    (QuotientAddGroup.mk' (boundaries₁ X)).comp (loopChains x -
      AddMonoidHom.id _ + (pathChains x).comp
        (((singularChains ℤ).obj X).d 1 0).hom.toAddMonoidHom)
  have : φ = 0 := chains_addMonoidHom_ext fun s ↦ by
    simp only [φ, AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.add_apply,
      AddMonoidHom.sub_apply, AddMonoidHom.id_apply,
      AddMonoidHom.zero_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    change loopChains x (simplexChain s 1) - simplexChain s 1 +
      pathChains x (((singularChains ℤ).obj X).d 1 0 (simplexChain s 1)) ∈ boundaries₁ X
    rw [singularChains_d_simplexChain (n := 0), Fin.sum_univ_two]
    simp only [loopChains, pathChains, LinearMap.toAddMonoidHom_coe, map_add, map_zsmul,
      chainsDesc_simplexChain, one_smul, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    erw [point_δ_zero, point_δ_one]
    convert loopChain_sub_mem x s using 1
    abel
  have h : φ c = 0 := DFunLike.congr_fun this c
  exact (QuotientAddGroup.eq_zero_iff _).1 h

lemma loopChains_mem_cycles₁ (c : Chains X 1) : loopChains x c ∈ cycles₁ X := by
  have : (((singularChains ℤ).obj X).d 1 0).hom.toAddMonoidHom.comp (loopChains x) = 0 :=
    chains_addMonoidHom_ext fun s ↦ by
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, loopChains,
        LinearMap.toAddMonoidHom_coe, chainsDesc_simplexChain, one_smul,
        AddMonoidHom.zero_apply]
      exact chain₁_mem_cycles₁ (loopPath x s)
  exact DFunLike.congr_fun this c

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
    hurewiczAb x (inverseChains x c) = QuotientAddGroup.mk ⟨_, loopChains_mem_cycles₁ x c⟩ := by
  let ψ : Chains X 1 →+ Additive (Abelianization (FundamentalGroup X x)) :=
    (inverseChains x).toAddMonoidHom
  let ρ : Chains X 1 →+ H₁ X :=
    (QuotientAddGroup.mk' _).comp ((loopChains x).codRestrict _ (loopChains_mem_cycles₁ x))
  have : (hurewiczAb x).comp ψ = ρ := chains_addMonoidHom_ext fun s ↦ by
    have e : loopChains x (simplexChain s 1) = chain₁ (loopPath x s).toContinuousMap := by
      simp [loopChains, chainsDesc_simplexChain]
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, ψ, ρ, LinearMap.toAddMonoidHom_coe,
      inverseChains, chainsDesc_simplexChain, one_smul, QuotientAddGroup.mk'_apply,
      AddMonoidHom.codRestrict_apply]
    exact (hurewiczAb_ofMul_of x (loopPath x s)).trans
      (congrArg QuotientAddGroup.mk (Subtype.ext e.symm))
  exact DFunLike.congr_fun this c

lemma hurewiczAb_inverse₁ (h : H₁ X) : hurewiczAb x (inverse₁ x h) = h := by
  induction h using QuotientAddGroup.induction_on with | H z =>
  change hurewiczAb x (inverseChains x z) = _
  rw [hurewiczAb_inverseChains, QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf]
  have hz : ((singularChains ℤ).obj X).d 1 0 z = 0 := z.2
  have := loopChains_sub_mem x z
  rw [hz, map_zero, add_zero] at this
  exact this

lemma inverse₁_hurewiczAb (a : Additive (Abelianization (FundamentalGroup X x))) :
    inverse₁ x (hurewiczAb x a) = a := by
  induction a using Additive.rec with | ofMul a =>
  induction a using QuotientGroup.induction_on with | H p =>
  rw [show (QuotientGroup.mk p : Abelianization (FundamentalGroup X x)) = Abelianization.of p
    from rfl]
  obtain ⟨γ, rfl⟩ : ∃ γ : Path x x, Path.Homotopic.Quotient.mk γ = p :=
    Quotient.exists_rep (s := Path.Homotopic.setoid x x) p
  exact (congrArg (inverse₁ x) (hurewiczAb_ofMul_of x γ)).trans (inverse₁_loopClass x γ)

/-- **The Hurewicz theorem in degree one**: for a path-connected space, the Hurewicz map
identifies the abelianized fundamental group with the first homology group, written as cycles
modulo boundaries. -/
def hurewiczEquiv : Additive (Abelianization (FundamentalGroup X x)) ≃+ H₁ X where
  __ := hurewiczAb x
  invFun := inverse₁ x
  left_inv := inverse₁_hurewiczAb x
  right_inv := hurewiczAb_inverse₁ x

@[simp]
lemma hurewiczEquiv_ofMul_of (γ : Path x x) :
    hurewiczEquiv x (Additive.ofMul ((Abelianization.of : FundamentalGroup X x →* _)
      (Path.Homotopic.Quotient.mk γ))) = loopClass γ :=
  hurewiczAb_ofMul_of x γ

end Inverse

/-! ### Comparison with the homology of the singular chain complex -/

variable (X) in
/-- The short complex `C₂ → C₁ → C₀` of the singular chains of `X`. -/
abbrev sc₁ := ((singularChains ℤ).obj X).sc' 2 1 0

/-- An additive map out of a `ℤ`-module, as a `ℤ`-linear map. The module structure is an
implicit argument so that it is unified with the given one rather than synthesized. -/
def intLinearMapOfAddMonoidHom {M V : Type} [AddCommGroup M] {_ : Module ℤ M} [AddCommGroup V]
    (f : M →+ V) : M →ₗ[ℤ] V where
  toFun := f
  map_add' := f.map_add
  map_smul' a c := by
    rw [RingHom.id_apply]
    exact (congrArg f (int_smul_eq_zsmul _ a c)).trans (map_zsmul f a c)

variable (X) in
/-- The inclusion of the cycles into the kernel of the differential of `sc₁ X`. -/
def cyclesToK : cycles₁ X →+ (sc₁ X).moduleCatLeftHomologyData.K where
  toFun c := ⟨c.1, c.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

variable (X) in
/-- The projection from the kernel of the differential of `sc₁ X` to the quotient of cycles by
boundaries. -/
def kToH₁ : (sc₁ X).moduleCatLeftHomologyData.K ⟶ ModuleCat.of ℤ (H₁ X) :=
  @ModuleCat.ofHom ℤ _ _ _ _ (LinearMap.ker (sc₁ X).g.hom).module _ _
    (intLinearMapOfAddMonoidHom ((QuotientAddGroup.mk' _).comp
      { toFun c := ⟨c.1, c.2⟩
        map_zero' := rfl
        map_add' _ _ := rfl }))

lemma f'_kToH₁ : (sc₁ X).moduleCatLeftHomologyData.f' ≫ kToH₁ X = 0 := by
  ext y
  exact (QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.mem_addSubgroupOf.2 ⟨y, rfl⟩)

variable (X) in
/-- The quotient of cycles by boundaries is the explicit homology of `sc₁ X` in `ModuleCat`. -/
def H₁AddEquivModuleCat : H₁ X ≃+ (sc₁ X).moduleCatLeftHomologyData.H where
  toFun := QuotientAddGroup.lift _
    ((sc₁ X).moduleCatLeftHomologyData.π.hom.toAddMonoidHom.comp (cyclesToK X))
    fun c hc ↦ by
      obtain ⟨y, hy⟩ := AddSubgroup.mem_addSubgroupOf.1 hc
      have hc' : cyclesToK X c = (sc₁ X).moduleCatLeftHomologyData.f'.hom y :=
        Subtype.ext hy.symm
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, hc']
      exact congr($((sc₁ X).moduleCatLeftHomologyData.f'_π).hom y)
  invFun := ((sc₁ X).moduleCatLeftHomologyData.descH (kToH₁ X) f'_kToH₁).hom
  left_inv h := by
    induction h using QuotientAddGroup.induction_on with | H c =>
    exact congr($((sc₁ X).moduleCatLeftHomologyData.π_descH (kToH₁ X) f'_kToH₁).hom
      (cyclesToK X c))
  right_inv h := by
    obtain ⟨k, rfl⟩ := Quot.exists_rep h
    have e := congr($((sc₁ X).moduleCatLeftHomologyData.π_descH (kToH₁ X) f'_kToH₁).hom k)
    rw [ModuleCat.hom_comp] at e
    refine (congrArg (QuotientAddGroup.lift _ _ _) e).trans ?_
    rfl
  map_add' := map_add _

variable (X) in
/-- The quotient of cycles by boundaries is the first homology group of the singular chain
complex. -/
def H₁AddEquivHomology : H₁ X ≃+ ((singularChains ℤ).obj X).homology 1 :=
  (H₁AddEquivModuleCat X).trans (((sc₁ X).moduleCatHomologyIso.symm ≪≫
    (((singularChains ℤ).obj X).homologyIsoSc' 2 1 0 (by simp) (by simp)).symm).toLinearEquiv
      |>.toAddEquiv)

/-- Every `1`-cycle lies under a cycle of the singular chain complex. -/
lemma exists_iCycles_eq (c : cycles₁ X) :
    ∃ z : ((singularChains ℤ).obj X).cycles 1,
      (((singularChains ℤ).obj X).iCycles 1).hom z = c := by
  have hi : (ComplexShape.down ℕ).prev 1 = 2 := by simp
  have hk : (ComplexShape.down ℕ).next 1 = 0 := by simp
  have h₁ := congr($(((singularChains ℤ).obj X).cyclesIsoSc'_inv_iCycles 2 1 0 hi hk).hom
    ((sc₁ X).moduleCatCyclesIso.inv.hom (cyclesToK X c)))
  have h₂ := congr($((sc₁ X).moduleCatCyclesIso_inv_iCycles).hom (cyclesToK X c))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h₁ h₂
  exact ⟨_, h₁.trans h₂⟩

/-- The identification of cycles modulo boundaries with the homology of the singular chain
complex sends the class of a cycle `c` to the homology class of the cycle of the complex lying
over `c`. -/
lemma H₁AddEquivHomology_mk (c : cycles₁ X) (z : ((singularChains ℤ).obj X).cycles 1)
    (hz : (((singularChains ℤ).obj X).iCycles 1).hom z = c) :
    H₁AddEquivHomology X (QuotientAddGroup.mk c) =
      (((singularChains ℤ).obj X).homologyπ 1).hom z := by
  have hi : (ComplexShape.down ℕ).prev 1 = 2 := by simp
  have hk : (ComplexShape.down ℕ).next 1 = 0 := by simp
  have h₁ := congr($(((singularChains ℤ).obj X).cyclesIsoSc'_inv_iCycles 2 1 0 hi hk).hom
    ((sc₁ X).moduleCatCyclesIso.inv.hom (cyclesToK X c)))
  have h₂ := congr($((sc₁ X).moduleCatCyclesIso_inv_iCycles).hom (cyclesToK X c))
  have h₃ := congr($((sc₁ X).moduleCatCyclesIso_inv_π).hom (cyclesToK X c))
  have h₄ := congr($(((singularChains ℤ).obj X).π_homologyIsoSc'_inv 2 1 0 hi hk).hom
    ((sc₁ X).moduleCatCyclesIso.inv.hom (cyclesToK X c)))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h₁ h₂ h₃ h₄
  have hz₀ : z = (((singularChains ℤ).obj X).cyclesIsoSc' 2 1 0 hi hk).inv.hom
      ((sc₁ X).moduleCatCyclesIso.inv.hom (cyclesToK X c)) := by
    apply (ModuleCat.mono_iff_injective (((singularChains ℤ).obj X).iCycles 1)).1 inferInstance
    refine hz.trans ?_
    exact (h₁.trans h₂).symm
  rw [hz₀, ← h₄, h₃]
  rfl

/-! ### The Hurewicz isomorphism -/

/-- **The Hurewicz theorem in degree one**: for a path-connected space `X` with a base point `x`,
the Hurewicz map identifies the abelianization of `π₁(X, x)` with `H₁(X; ℤ)`, the first homology
group of the singular chain complex of `X` with integer coefficients. -/
def hurewiczHomologyEquiv [PathConnectedSpace X] (x : X) :
    Additive (Abelianization (FundamentalGroup X x)) ≃+ ((singularChains ℤ).obj X).homology 1 :=
  (hurewiczEquiv x).trans (H₁AddEquivHomology X)

lemma hurewiczHomologyEquiv_apply [PathConnectedSpace X] {x : X}
    (a : Additive (Abelianization (FundamentalGroup X x))) :
    hurewiczHomologyEquiv x a = H₁AddEquivHomology X (hurewiczAb x a) := by
  rw [hurewiczHomologyEquiv, AddEquiv.trans_apply]
  rfl

lemma hurewiczHomologyEquiv_ofMul_of [PathConnectedSpace X] {x : X} (γ : Path x x) :
    hurewiczHomologyEquiv x (Additive.ofMul ((Abelianization.of : FundamentalGroup X x →* _)
      (Path.Homotopic.Quotient.mk γ))) = H₁AddEquivHomology X (loopClass γ) := by
  simp [hurewiczHomologyEquiv]

end TauCeti.HurewiczOne
