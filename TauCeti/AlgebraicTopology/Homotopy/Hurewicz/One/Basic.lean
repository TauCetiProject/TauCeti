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
public import TauCeti.Geometry.Convex.ConvexSpace.Defs
public import TauCeti.GroupTheory.Abelianization.Basic

/-!
# The Hurewicz theorem in degree one

For a path-connected space `X` with a base point `x`, the Hurewicz map sends a loop at `x` to the
homology class of the singular `1`-simplex it defines, and it identifies the abelianization of
the fundamental group `π₁(X, x)` with the first singular homology group `H₁(X; ℤ)`
(`TauCeti.HurewiczOne.hurewiczHomologyAddEquiv`).

The space `X` lives in an arbitrary universe `u`. Singular chains of `X : TopCat.{u}` take their
coefficients in a ring `R : Type u`, so integer coefficients are read through a ring `R` with a
ring isomorphism `e : R ≃+* ℤ`: the ring `ℤ` itself, with `RingEquiv.refl ℤ`, for spaces in
`Type`, and `ULift.{u} ℤ`, with `ULift.ringEquiv`, in general. The constructions of the Hurewicz
map and of the homomorphisms out of `H₁` work over every ring `R`; only the inverse uses `e`.

The proof is the one of Hatcher, Theorem 2A.1, carried out on the singular chains through the
element-level interface of `TauCeti.AlgebraicTopology.Singular.ModuleChains.Basic`.
Paths `γ : I → X` are read as singular `1`-simplices along the parameter of the standard
`1`-simplex, and three kinds of explicit singular `2`-simplices give the relations:

* a constant `2`-simplex shows that the chain of a constant path is a boundary;
* the composite of a concatenation `γ.trans δ` with the affine projection of `Δ²` onto `[0, 1]`
  sending the vertices to `0`, `1/2` and `1` shows that `γ + δ - γ.trans δ` is a boundary;
* a homotopy of paths, cut along the diagonal of its square into two `2`-simplices, shows that
  homotopic paths have homologous chains.

So the Hurewicz map is a well-defined homomorphism `π₁(X, x) → H₁(X; R)`
(`TauCeti.HurewiczOne.hurewicz₁`).

Conversely, a function `f` on path classes with values in an `R`-module that is additive under
concatenation induces a homomorphism out of `H₁(X; R)` sending the class of a cycle `Σ nᵢ σᵢ` to
`Σ nᵢ f [σᵢ]` (`TauCeti.HurewiczOne.H₁.liftPathClass`): it vanishes on boundaries because the
three edges of a singular `2`-simplex are images of paths in the simply connected standard
simplex. The inverse of the Hurewicz map is induced in this way by sending a path class from `y`
to `z` to the class of the loop that runs along a chosen path from `x` to `y`, along the class,
and back from `z`; the abelianized fundamental group is an `R`-module through `e`. It inverts the
Hurewicz map because conjugation is trivial in the abelianization. Conversely, the loop through a
singular `1`-simplex `σ` differs from `σ` by the chains of the chosen paths at its endpoints,
which cancel on cycles.

The homology group is first described as the explicit homology
`ShortComplex.moduleCatLeftHomologyData` of the short complex `C₂ → C₁ → C₀`, that is `1`-cycles
modulo boundaries (`TauCeti.HurewiczOne.H₁`), and then identified with the homology of the
singular chain complex (`TauCeti.HurewiczOne.H₁AddEquivHomology`).

## Main definitions and results

* `TauCeti.HurewiczOne.hurewicz₁`: the Hurewicz homomorphism `π₁(X, x) → H₁(X; R)`.
* `TauCeti.HurewiczOne.H₁.lift`, `TauCeti.HurewiczOne.H₁.liftPathClass`: the homomorphisms out of
  `H₁` induced by linear maps on `1`-chains vanishing on boundaries, and by functions on path
  classes additive under concatenation.
* `TauCeti.HurewiczOne.hurewiczAddEquiv`: for path-connected `X` and `e : R ≃+* ℤ`, it induces an
  isomorphism from the abelianization of `π₁(X, x)` onto `H₁`, the `1`-cycles modulo boundaries.
* `TauCeti.HurewiczOne.hurewiczHomologyAddEquiv`: the same isomorphism onto the first homology
  group of the singular chain complex of `X` with coefficients in `R`.

## References

* A. Hatcher, *Algebraic Topology*, Theorem 2A.1.
-/

public section

noncomputable section

open CategoryTheory Convexity Simplicial unitInterval TauCeti.TopCat

universe u

namespace TauCeti.HurewiczOne

/-- The parametrization of the standard `1`-simplex by the unit interval, as a continuous map. -/
local notation "toI" => (StdSimplex.homeomorphI : C(StdSimplex ℝ (Fin 2), I))

variable {R : Type u} [Ring R] {X : TopCat.{u}}

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

variable (R) in
/-- The chain of a singular `2`-simplex given as a continuous map from the standard simplex. -/
private abbrev chain₂ (f : C(StdSimplex ℝ (Fin 3), X)) : ((singularChains R).obj X).X 2 :=
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
    ((singularChains R).obj X).d 2 1 (chain₂ R f) =
      pathChain R g₀ - pathChain R g₁ + pathChain R g₂ := by
  rw [singularChains_d_simplexChain (n := 1), Fin.sum_univ_three,
    δ_toSSetObjEquiv_symm f 0 g₀ h₀, δ_toSSetObjEquiv_symm f 1 g₁ h₁,
    δ_toSSetObjEquiv_symm f 2 g₂ h₂]
  simp [sub_eq_add_neg]

variable (R X) in
/-- The short complex `C₂ → C₁ → C₀` of the singular chains of `X`. -/
abbrev sc₁ := ((singularChains R).obj X).sc' 2 1 0

variable (R X) in
/-- The boundaries among the singular `1`-chains of `X`. -/
abbrev boundaries₁ : Submodule R (((singularChains R).obj X).X 1) :=
  LinearMap.range (((singularChains R).obj X).d 2 1).hom

lemma mem_boundaries₁ {c : ((singularChains R).obj X).X 1} (y : ((singularChains R).obj X).X 2)
    (h : ((singularChains R).obj X).d 2 1 y = c) : c ∈ boundaries₁ R X :=
  ⟨y, h⟩

variable (R) in
/-- The chain of a constant map is a boundary. -/
lemma pathChain_const_mem_boundaries₁ (p : X) :
    pathChain R (ContinuousMap.const I p) ∈ boundaries₁ R X :=
  mem_boundaries₁ (chain₂ R (ContinuousMap.const _ p)) (by
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

variable (R) in
/-- The chain of a concatenation of paths differs from the sum of the chains of the two paths by
a boundary. -/
lemma pathChain_add_sub_trans_mem_boundaries₁ {a b c : X} (γ : Path a b) (δ : Path b c) :
    pathChain R γ.toContinuousMap + pathChain R δ.toContinuousMap -
      pathChain R (γ.trans δ).toContinuousMap ∈
      boundaries₁ R X := by
  refine mem_boundaries₁ (chain₂ R ((γ.trans δ).toContinuousMap.comp concatProj)) ?_
  rw [d_chain₂ _ δ.toContinuousMap (γ.trans δ).toContinuousMap γ.toContinuousMap]
  · abel
  · ext a
    exact Path.trans_apply_of_eq_two_mul_sub_one γ δ _
      (by simp [concatProj, StdSimplex.homeomorphI_apply_eq_mk]; linarith [a.total_fin_two])
  · ext a
    simp [concatProj, StdSimplex.homeomorphI_apply_eq_mk]
  · ext a
    exact Path.trans_apply_of_eq_two_mul γ δ _
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

variable (R) in
/-- The chains of homotopic paths differ by a boundary. -/
lemma pathChain_sub_mem_boundaries₁_of_homotopy {a b : X} {γ γ' : Path a b}
    (F : Path.Homotopy γ γ') :
    pathChain R γ.toContinuousMap - pathChain R γ'.toContinuousMap ∈ boundaries₁ R X := by
  let D : C(I, X) := F.toContinuousMap.comp ⟨fun t ↦ (t, t), by fun_prop⟩
  have h₁ : pathChain R (.const I b) - pathChain R D + pathChain R γ.toContinuousMap ∈
      boundaries₁ R X := by
    refine mem_boundaries₁
      (chain₂ R (F.toContinuousMap.comp (lastWeight.prodMk lastTwoWeights))) ?_
    rw [d_chain₂ _ (.const I b) D γ.toContinuousMap]
    · ext x
      simp [lastWeight, lastTwoWeights]
    · ext x
      simp [lastWeight, lastTwoWeights, StdSimplex.homeomorphI_apply_eq_mk, D]
    · ext x
      simp [lastWeight, lastTwoWeights, StdSimplex.homeomorphI_apply_eq_mk]
  have h₂ : pathChain R γ'.toContinuousMap - pathChain R D + pathChain R (.const I a) ∈
      boundaries₁ R X := by
    refine mem_boundaries₁
      (chain₂ R (F.toContinuousMap.comp (lastTwoWeights.prodMk lastWeight))) ?_
    rw [d_chain₂ _ γ'.toContinuousMap D (.const I a)]
    · ext x
      simp [lastWeight, lastTwoWeights, StdSimplex.homeomorphI_apply_eq_mk]
    · ext x
      simp [lastWeight, lastTwoWeights, StdSimplex.homeomorphI_apply_eq_mk, D]
    · ext x
      simp [lastWeight, lastTwoWeights]
  have := sub_mem (add_mem (sub_mem h₁ h₂) (pathChain_const_mem_boundaries₁ R a))
    (pathChain_const_mem_boundaries₁ R b)
  convert this using 1
  abel

/-! ### The Hurewicz map -/

variable (R X) in
/-- The singular `1`-cycles of `X`, the kernel of the differential of `sc₁ R X`. -/
abbrev cycles₁ : Submodule R (((singularChains R).obj X).X 1) :=
  LinearMap.ker (sc₁ R X).g.hom

variable (R X) in
/-- The first singular homology group of `X` with coefficients in `R`, as the explicit homology
`cycles₁ R X ⧸ boundaries` of `sc₁ R X` in `ModuleCat R`. -/
abbrev H₁ : ModuleCat R := (sc₁ R X).moduleCatLeftHomologyData.H

/-- A `1`-chain is a cycle when its boundary vanishes. -/
lemma mem_cycles₁_iff {c : ((singularChains R).obj X).X 1} :
    c ∈ cycles₁ R X ↔ ((singularChains R).obj X).d 1 0 c = 0 :=
  -- The differential `(sc₁ R X).g` of the short complex is `d 1 0` by definition of `sc'`.
  LinearMap.mem_ker

lemma mem_cycles₁ {c : ((singularChains R).obj X).X 1}
    (h : ((singularChains R).obj X).d 1 0 c = 0) :
    c ∈ cycles₁ R X :=
  mem_cycles₁_iff.2 h

/-- The class in `H₁ R X` of a `1`-cycle, as an additive map. (It is not stated as an `R`-linear
map: for `R = ℤ`, instance search on the cycles would find `AddCommGroup.toIntModule`, which is
only propositionally equal to their submodule structure.) -/
def H₁.mk : cycles₁ R X →+ H₁ R X :=
  (sc₁ R X).moduleCatLeftHomologyData.π.hom.toAddMonoidHom

lemma H₁.mk_eq_mk_iff (c c' : cycles₁ R X) :
    H₁.mk c = H₁.mk c' ↔ (c : ((singularChains R).obj X).X 1) - c' ∈ boundaries₁ R X := by
  rw [H₁.mk]
  exact (ShortComplex.moduleCatLeftHomologyData_π_hom_eq_iff (sc₁ R X) c c').trans
    LinearMap.mem_range.symm

lemma H₁.mk_eq_zero_iff (c : cycles₁ R X) :
    H₁.mk c = 0 ↔ (c : ((singularChains R).obj X).X 1) ∈ boundaries₁ R X := by
  rw [← map_zero H₁.mk, H₁.mk_eq_mk_iff, ZeroMemClass.coe_zero, sub_zero]

lemma H₁.mk_surjective : Function.Surjective (H₁.mk (R := R) (X := X)) := by
  intro h
  obtain ⟨c, hc⟩ := ShortComplex.moduleCatLeftHomologyData_π_hom_surjective (sc₁ R X) h
  exact ⟨c, by rw [H₁.mk]; exact hc⟩

/-- Two additive maps out of `H₁ R X` agree once they agree on the classes of `1`-cycles. -/
@[ext]
lemma H₁.addMonoidHom_ext {A : Type*} [AddZeroClass A] {f g : H₁ R X →+ A}
    (h : ∀ c : cycles₁ R X, f (H₁.mk c) = g (H₁.mk c)) : f = g := by
  ext a
  obtain ⟨c, rfl⟩ := H₁.mk_surjective a
  exact h c

variable (R) in
lemma pathChain_mem_cycles₁ {x : X} (γ : Path x x) :
    pathChain R γ.toContinuousMap ∈ cycles₁ R X :=
  mem_cycles₁ (by rw [singularChains_d_pathChain]; simp)

variable (R) in
/-- The homology class of the chain of a loop. -/
def loopClass {x : X} (γ : Path x x) : H₁ R X :=
  H₁.mk ⟨_, pathChain_mem_cycles₁ R γ⟩

lemma loopClass_def {x : X} (γ : Path x x) :
    loopClass R γ = H₁.mk ⟨pathChain R γ.toContinuousMap, pathChain_mem_cycles₁ R γ⟩ :=
  (rfl)

lemma loopClass_eq_iff {x y : X} (γ : Path x x) (γ' : Path y y) :
    loopClass R γ = loopClass R γ' ↔
      pathChain R γ.toContinuousMap - pathChain R γ'.toContinuousMap ∈ boundaries₁ R X := by
  rw [loopClass, loopClass, H₁.mk_eq_mk_iff]

/-- Loops with the same values have the same homology class, even when their base points are not
syntactically equal. -/
lemma loopClass_eq_of_apply_eq {x y : X} (γ : Path x x) (γ' : Path y y) (hγ : ∀ t, γ t = γ' t) :
    loopClass R γ = loopClass R γ' := by
  rw [loopClass_eq_iff, sub_eq_zero.2 (congrArg (pathChain R) (ContinuousMap.ext hγ))]
  exact zero_mem _

variable (R) in
@[simp]
lemma loopClass_refl (x : X) : loopClass R (Path.refl x) = 0 := by
  rw [loopClass, H₁.mk_eq_zero_iff]
  exact pathChain_const_mem_boundaries₁ R x

@[simp]
lemma loopClass_trans {x : X} (γ δ : Path x x) :
    loopClass R (γ.trans δ) = loopClass R γ + loopClass R δ := by
  rw [loopClass, loopClass, loopClass, ← map_add, H₁.mk_eq_mk_iff]
  have := neg_mem (pathChain_add_sub_trans_mem_boundaries₁ R γ δ)
  convert this using 1
  simp only [Submodule.coe_add]
  abel

variable (R X) in
/-- **The Hurewicz map in degree one**: a loop is sent to the homology class of its chain. -/
def hurewicz₁ (x : X) : FundamentalGroup X x →* Multiplicative (H₁ R X) where
  toFun g := Quotient.lift (s := Path.Homotopic.setoid x x)
    (fun γ ↦ Multiplicative.ofAdd (loopClass R γ)) (fun γ γ' h ↦
      congrArg Multiplicative.ofAdd ((loopClass_eq_iff γ γ').2
        (pathChain_sub_mem_boundaries₁_of_homotopy R h.some))) g.toPath
  map_one' := congrArg Multiplicative.ofAdd (loopClass_refl R x)
  map_mul' := by
    rintro ⟨p⟩ ⟨q⟩
    induction p using Path.Homotopic.Quotient.ind with | mk p =>
    induction q using Path.Homotopic.Quotient.ind with | mk q =>
    -- `Quotient.lift` computes on the classes of `q.trans p`, `p` and `q`.
    change Multiplicative.ofAdd (loopClass R (q.trans p)) = _
    rw [loopClass_trans, add_comm, ofAdd_add]
    -- `Quotient.lift` computes on the classes `⟦p⟧` and `⟦q⟧`.
    rfl

lemma hurewicz₁_mk {x : X} (γ : Path x x) :
    hurewicz₁ R X x (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) =
      Multiplicative.ofAdd (loopClass R γ) := by
  rw [hurewicz₁]
  -- `Quotient.lift` computes on the class of `γ`.
  rfl

/-! ### Homomorphisms out of the first homology group -/

section Lift

variable {A : Type u} [AddCommGroup A] [Module R A]

/-- The homomorphism out of `H₁ R X` induced by a linear map on the singular `1`-chains which
vanishes on boundaries. -/
def H₁.lift (f : ((singularChains R).obj X).X 1 →ₗ[R] A)
    (hf : ∀ y, f (((singularChains R).obj X).d 2 1 y) = 0) : H₁ R X →+ A :=
  -- The module structure on the cycles is passed explicitly: for `R = ℤ`, instance search on
  -- `LinearMap.ker (sc₁ R X).g.hom` finds `AddCommGroup.toIntModule`, which is only
  -- propositionally equal to the submodule structure.
  ((sc₁ R X).moduleCatLeftHomologyData.descH
    (@ModuleCat.ofHom R _ _ _ _ (cycles₁ R X).module _ _ (f.comp (cycles₁ R X).subtype))
    (ModuleCat.hom_ext (LinearMap.ext hf))).hom.toAddMonoidHom

lemma H₁.lift_mk (f : ((singularChains R).obj X).X 1 →ₗ[R] A)
    (hf : ∀ y, f (((singularChains R).obj X).d 2 1 y) = 0) (c : cycles₁ R X) :
    H₁.lift f hf (H₁.mk c) = f c := by
  rw [H₁.lift]
  exact congr($((sc₁ R X).moduleCatLeftHomologyData.π_descH
    (@ModuleCat.ofHom R _ _ _ _ (cycles₁ R X).module _ _ (f.comp (cycles₁ R X).subtype))
    (ModuleCat.hom_ext (LinearMap.ext hf))).hom c)

/-- The path of the `i`-th face of a singular `2`-simplex is the image of the path along the
`i`-th edge of the standard `2`-simplex. -/
private lemma path₁_δ_apply (τ : (TopCat.toSSet.obj X) _⦋2⦌) (i : Fin 3) (t : I) :
    path₁ ((TopCat.toSSet.obj X).δ i τ) t =
      (StdSimplex.edgePath i.succAbove).map (X.toSSetObjEquiv _ τ).continuous t := by
  rw [path₁_apply, TopCat.toSSetObjEquiv_δ_apply, Path.map_coe, Function.comp_apply,
    StdSimplex.edgePath_apply]

variable (f : ∀ {y z : X}, Path.Homotopic.Quotient y z → A)

/-- The value of `f` on the image under `g` of the (unique) path class from `u` to `v` in a
simply connected space. -/
private def imageValue {Y : Type} [TopologicalSpace Y] [SimplyConnectedSpace Y] (g : C(Y, X))
    (u v : Y) : A :=
  f ((Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath u v)).map g)

omit [AddCommGroup A] in
private lemma map_eq_imageValue {Y : Type} [TopologicalSpace Y] [SimplyConnectedSpace Y]
    (g : C(Y, X)) {u v : Y} (γ : Path u v) :
    f ((Path.Homotopic.Quotient.mk γ).map g) = imageValue f g u v := by
  rw [imageValue, Subsingleton.elim (Path.Homotopic.Quotient.mk γ)]

omit [AddCommGroup A] in
/-- The value of `f` on the class of a path depends only on the path as a function, its endpoints
being its values at `0` and `1`. -/
private lemma apply_mk_eq_of_coe_eq {y z y' z' : X} (γ : Path y z) (γ' : Path y' z')
    (h : ⇑γ = ⇑γ') : f (.mk γ) = f (.mk γ') := by
  obtain rfl : y = y' := γ.source.symm.trans ((congrFun h 0).trans γ'.source)
  obtain rfl : z = z' := γ.target.symm.trans ((congrFun h 1).trans γ'.target)
  rw [Path.ext h]

omit [AddCommGroup A] in
/-- The value of `f` on the path of the `i`-th face of a singular `2`-simplex `τ`. -/
private lemma apply_path₁_δ (τ : (TopCat.toSSet.obj X) _⦋2⦌) (i : Fin 3) :
    f (.mk (path₁ ((TopCat.toSSet.obj X).δ i τ))) = imageValue f (X.toSSetObjEquiv _ τ)
      (StdSimplex.single (i.succAbove 0)) (StdSimplex.single (i.succAbove 1)) := by
  rw [← map_eq_imageValue f _ (StdSimplex.edgePath i.succAbove), ← Path.Homotopic.Quotient.mk_map]
  exact apply_mk_eq_of_coe_eq f _ _ (funext (path₁_δ_apply τ i))

variable {f}
variable (hf : ∀ {y z w : X} (p : Path.Homotopic.Quotient y z) (q : Path.Homotopic.Quotient z w),
  f (p.trans q) = f p + f q)
include hf

private lemma imageValue_add {Y : Type} [TopologicalSpace Y] [SimplyConnectedSpace Y]
    (g : C(Y, X)) (u v w : Y) :
    imageValue f g u v + imageValue f g v w = imageValue f g u w := by
  -- Both sides are values of `f` on images of paths from `u` to `w`.
  rw [imageValue, imageValue, ← hf, ← map_eq_imageValue f g
    ((PathConnectedSpace.somePath u v).trans (PathConnectedSpace.somePath v w))]
  simp only [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_trans, Path.map_trans]

/-- An additive function on path classes kills the boundaries of singular `2`-simplices: the
three edges of a singular `2`-simplex are images of paths in the simply connected standard
simplex. -/
lemma chainsDesc_path₁_d (y : ((singularChains R).obj X).X 2) :
    chainsDesc (fun s ↦ f (.mk (path₁ s))) (((singularChains R).obj X).d 2 1 y) = 0 := by
  have := singularChains_linearMap_ext
    (L := chainsDesc (fun s ↦ f (.mk (path₁ s))) ∘ₗ (((singularChains R).obj X).d 2 1).hom)
    (L' := 0) fun τ ↦ by
      rw [LinearMap.comp_apply, singularChains_d_simplexChain (n := 1), Fin.sum_univ_three]
      simp only [map_add, map_zsmul, chainsDesc_simplexChain_one, apply_path₁_δ]
      have h₀₁ : (0 : Fin 3).succAbove 0 = 1 := rfl
      have h₀₂ : (0 : Fin 3).succAbove 1 = 2 := rfl
      have h₁₁ : (1 : Fin 3).succAbove 1 = 2 := rfl
      have h₂₁ : (2 : Fin 3).succAbove 1 = 1 := rfl
      rw [h₀₁, h₀₂, h₁₁, h₂₁, Fin.succAbove_ne_zero_zero one_ne_zero,
        Fin.succAbove_ne_zero_zero two_ne_zero,
        ← imageValue_add hf _ (StdSimplex.single 0) (StdSimplex.single 1) (StdSimplex.single 2)]
      simp
  exact LinearMap.congr_fun this y

variable (R) in
/-- The homomorphism out of `H₁ R X` induced by a function `f` on path classes that is additive
under concatenation: the class of a cycle `Σ nᵢ σᵢ` is sent to `Σ nᵢ f [σᵢ]`. -/
def H₁.liftPathClass : H₁ R X →+ A :=
  H₁.lift (chainsDesc fun s ↦ f (.mk (path₁ s))) (chainsDesc_path₁_d hf)

lemma H₁.liftPathClass_mk (c : cycles₁ R X) :
    H₁.liftPathClass R hf (H₁.mk c) =
      chainsDesc (fun s ↦ f (.mk (path₁ s))) (c : ((singularChains R).obj X).X 1) :=
  H₁.lift_mk _ _ c

omit [AddCommGroup A] hf in
private lemma apply_cast {y z y' z' : X} (hy : y' = y) (hz : z' = z)
    (q : Path.Homotopic.Quotient y z) : f (q.cast hy hz) = f q := by
  subst hy hz
  rw [Path.Homotopic.Quotient.cast_rfl_rfl]

/-- The homomorphism out of `H₁ R X` induced by an additive function `f` on path classes sends
the class of a loop to the value of `f` on its class. -/
lemma H₁.liftPathClass_loopClass {x : X} (γ : Path x x) :
    H₁.liftPathClass R hf (loopClass R γ) = f (.mk γ) := by
  have hs : source₁ (simplex₁ γ.toContinuousMap) = x := (source₁_simplex₁ _).trans γ.source
  have ht : target₁ (simplex₁ γ.toContinuousMap) = x := (target₁_simplex₁ _).trans γ.target
  have hγ : path₁ (simplex₁ γ.toContinuousMap) = γ.cast hs ht := by
    ext t
    simp
  rw [loopClass, H₁.liftPathClass_mk, chainsDesc_simplexChain_one, hγ,
    Path.Homotopic.Quotient.mk_cast]
  exact apply_cast hs ht _

end Lift

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

/-- The class in the abelianized fundamental group of the loop through a path class. -/
private def loopThroughAb {y z : X} (q : Path.Homotopic.Quotient y z) :
    Additive (Group.Abelianization (FundamentalGroup X x)) :=
  Additive.ofMul (Group.Abelianization.of (loopThrough x q))

private lemma loopThroughAb_trans {y z w : X} (q : Path.Homotopic.Quotient y z)
    (q' : Path.Homotopic.Quotient z w) :
    loopThroughAb x (q.trans q') = loopThroughAb x q + loopThroughAb x q' := by
  rw [loopThroughAb, loopThroughAb, loopThroughAb, Group.Abelianization.ofMul_of_add_ofMul_of,
    loopThrough_trans]

/-- The abelianized fundamental group, an `R`-module through a ring isomorphism `R ≃+* ℤ`. -/
private abbrev abModule (e : R ≃+* ℤ) :
    Module R (Additive (Group.Abelianization (FundamentalGroup X x))) :=
  Module.compHom _ e.toRingHom

/-- **The inverse of the Hurewicz map in degree one**, on the first homology group. -/
private def inverse₁ (e : R ≃+* ℤ) :
    H₁ R X →+ Additive (Group.Abelianization (FundamentalGroup X x)) :=
  letI := abModule x e
  H₁.liftPathClass R (loopThroughAb_trans x)

/-- The class of the chosen loop at the base point, as an element of the fundamental group. -/
private def basePathClass : FundamentalGroup X x :=
  FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (pathTo x x))

/-- The loop through a loop at the base point is its conjugate by the chosen loop at the base
point. -/
private lemma loopThrough_eq_inv_mul_mul (q : FundamentalGroup X x) :
    loopThrough x q.toPath = (basePathClass x)⁻¹ * q * basePathClass x := by
  rw [FundamentalGroup.mul_def, FundamentalGroup.mul_def, FundamentalGroup.inv_def, loopThrough,
    basePathClass]

/-- The inverse Hurewicz map sends the homology class of a loop back to the class of the loop. -/
private lemma inverse₁_loopClass (e : R ≃+* ℤ) (γ : Path x x) :
    inverse₁ x e (loopClass R γ) =
      Additive.ofMul ((Group.Abelianization.of : FundamentalGroup X x →* _)
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))) := by
  let _ := abModule x e
  rw [inverse₁, H₁.liftPathClass_loopClass, loopThroughAb]
  exact (congrArg (fun g ↦ Additive.ofMul (Group.Abelianization.of g))
    (loopThrough_eq_inv_mul_mul _ (FundamentalGroup.fromPath (.mk γ)))).trans
      (by rw [Group.Abelianization.of_inv_mul_mul])

variable (R) in
/-- The `1`-chains of the chosen paths from the base point to the points of a `0`-chain. -/
private def pathChains : ((singularChains R).obj X).X 0 →ₗ[R] ((singularChains R).obj X).X 1 :=
  chainsDesc fun v ↦ pathChain R (pathTo x (TopCat.toSSetObj₀Equiv v)).toContinuousMap

private lemma pathChains_simplexChain (v : (TopCat.toSSet.obj X) _⦋0⦌) :
    pathChains R x (simplexChain v 1) =
      pathChain R (pathTo x (TopCat.toSSetObj₀Equiv v)).toContinuousMap := by
  rw [pathChains, chainsDesc_simplexChain_one]

/-- The loop at the base point through a singular `1`-simplex. -/
private def loopPath (s : (TopCat.toSSet.obj X) _⦋1⦌) : Path x x :=
  (pathTo x (source₁ s)).trans ((path₁ s).trans (pathTo x (target₁ s)).symm)

variable (R) in
/-- The `1`-chains of the loops through the simplices of a `1`-chain. -/
private def loopChains : ((singularChains R).obj X).X 1 →ₗ[R] ((singularChains R).obj X).X 1 :=
  chainsDesc fun s ↦ pathChain R (loopPath x s).toContinuousMap

private lemma loopChains_simplexChain (s : (TopCat.toSSet.obj X) _⦋1⦌) :
    loopChains R x (simplexChain s 1) = pathChain R (loopPath x s).toContinuousMap := by
  rw [loopChains, chainsDesc_simplexChain_one]

omit [PathConnectedSpace X] in
variable (R) in
lemma pathChain_add_symm_mem_boundaries₁ {a b : X} (γ : Path a b) :
    pathChain R γ.toContinuousMap + pathChain R γ.symm.toContinuousMap ∈ boundaries₁ R X := by
  have h₁ := pathChain_add_sub_trans_mem_boundaries₁ R γ γ.symm
  have h₂ := pathChain_sub_mem_boundaries₁_of_homotopy R (Path.Homotopy.reflTransSymm γ)
  have h₃ : pathChain R (Path.refl a).toContinuousMap ∈ boundaries₁ R X :=
    pathChain_const_mem_boundaries₁ R a
  have := add_mem (sub_mem h₁ h₂) h₃
  convert this using 1
  abel

private lemma pathChain_loopPath_sub_mem_boundaries₁ (s : (TopCat.toSSet.obj X) _⦋1⦌) :
    pathChain R (loopPath x s).toContinuousMap - simplexChain s 1 +
      (pathChain R (pathTo x (target₁ s)).toContinuousMap -
        pathChain R (pathTo x (source₁ s)).toContinuousMap) ∈
        boundaries₁ R X := by
  have h₁ := pathChain_add_sub_trans_mem_boundaries₁ R (pathTo x (source₁ s))
    ((path₁ s).trans (pathTo x (target₁ s)).symm)
  have h₂ := pathChain_add_sub_trans_mem_boundaries₁ R (path₁ s) (pathTo x (target₁ s)).symm
  have h₃ := pathChain_add_symm_mem_boundaries₁ R (pathTo x (target₁ s))
  have hs : pathChain R (path₁ s).toContinuousMap = simplexChain s 1 := by
    rw [pathChain, simplex₁_path₁]
  have := sub_mem (sub_mem h₃ h₂) h₁
  rw [hs] at this
  convert this using 1
  rw [loopPath]
  abel

private lemma loopChains_sub_mem_boundaries₁ (c : ((singularChains R).obj X).X 1) :
    loopChains R x c - c + pathChains R x (((singularChains R).obj X).d 1 0 c) ∈
      boundaries₁ R X := by
  have : (boundaries₁ R X).mkQ ∘ₗ (loopChains R x - LinearMap.id +
      pathChains R x ∘ₗ (((singularChains R).obj X).d 1 0).hom) = 0 :=
    singularChains_linearMap_ext fun s ↦ by
      rw [LinearMap.zero_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, LinearMap.add_apply, LinearMap.sub_apply,
        LinearMap.id_apply, LinearMap.comp_apply]
      -- The boundary of `s` is `[target₁ s] - [source₁ s]`, so `pathChains` sends it to the
      -- difference of the chains of the chosen paths to the two vertices.
      rw [singularChains_d_simplexChain (n := 0), Fin.sum_univ_two, map_add, map_zsmul, map_zsmul,
        pathChains_simplexChain, pathChains_simplexChain, toSSetObj₀Equiv_δ_zero,
        toSSetObj₀Equiv_δ_one, loopChains_simplexChain]
      convert pathChain_loopPath_sub_mem_boundaries₁ x s using 1
      simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul]
      abel
  exact (Submodule.Quotient.mk_eq_zero _).1 (LinearMap.congr_fun this c)

private lemma loopChains_mem_cycles₁ (c : ((singularChains R).obj X).X 1) :
    loopChains R x c ∈ cycles₁ R X := by
  have : (((singularChains R).obj X).d 1 0).hom ∘ₗ loopChains R x = 0 :=
    singularChains_linearMap_ext fun s ↦ by
      rw [LinearMap.comp_apply, loopChains_simplexChain, LinearMap.zero_apply]
      exact pathChain_mem_cycles₁ R (loopPath x s)
  exact mem_cycles₁ (LinearMap.congr_fun this c)

omit [PathConnectedSpace X] in
variable (R) in
/-- The Hurewicz map on the abelianized fundamental group, written additively. -/
def hurewiczAb : Additive (Group.Abelianization (FundamentalGroup X x)) →+ H₁ R X :=
  MonoidHom.toAdditiveLeft (Group.Abelianization.lift (hurewicz₁ R X x))

omit [PathConnectedSpace X] in
/-- On the abelianization, the Hurewicz map is induced by `TauCeti.HurewiczOne.hurewicz₁`. -/
lemma hurewiczAb_ofMul_of (g : FundamentalGroup X x) :
    hurewiczAb R x (Additive.ofMul (Group.Abelianization.of g)) =
      Multiplicative.toAdd (hurewicz₁ R X x g) := by
  simp [hurewiczAb]

omit [PathConnectedSpace X] in
lemma hurewiczAb_ofMul_of_mk (γ : Path x x) :
    hurewiczAb R x (Additive.ofMul ((Group.Abelianization.of : FundamentalGroup X x →* _)
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)))) = loopClass R γ := by
  rw [hurewiczAb_ofMul_of, hurewicz₁_mk, toAdd_ofAdd]

private lemma hurewiczAb_chainsDesc_loopThroughAb (e : R ≃+* ℤ)
    (c : ((singularChains R).obj X).X 1) :
    letI := abModule x e
    hurewiczAb R x (chainsDesc (fun s ↦ loopThroughAb x (.mk (path₁ s))) c) =
      H₁.mk ⟨_, loopChains_mem_cycles₁ x c⟩ := by
  let _ := abModule x e
  let ψ : ((singularChains R).obj X).X 1 →+ H₁ R X :=
    (hurewiczAb R x).comp (chainsDesc fun s ↦ loopThroughAb x (.mk (path₁ s))).toAddMonoidHom
  let ρ : ((singularChains R).obj X).X 1 →+ H₁ R X := ((sc₁ R X).moduleCatLeftHomologyData.π.hom ∘ₗ
    (loopChains R x).codRestrict (cycles₁ R X) (loopChains_mem_cycles₁ x)).toAddMonoidHom
  have : ψ = ρ := singularChains_addMonoidHom_ext e fun s ↦ by
    simp only [ψ, ρ, AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe,
      chainsDesc_simplexChain_one]
    exact (hurewiczAb_ofMul_of_mk x (loopPath x s)).trans
      (congrArg H₁.mk (Subtype.ext (loopChains_simplexChain x s).symm))
  exact DFunLike.congr_fun this c

private lemma hurewiczAb_inverse₁ (e : R ≃+* ℤ) (h : H₁ R X) :
    hurewiczAb R x (inverse₁ x e h) = h := by
  let _ := abModule x e
  obtain ⟨z, rfl⟩ := H₁.mk_surjective h
  rw [inverse₁, H₁.liftPathClass_mk, hurewiczAb_chainsDesc_loopThroughAb x e, H₁.mk_eq_mk_iff]
  have hz : ((singularChains R).obj X).d 1 0 z = 0 := mem_cycles₁_iff.1 z.property
  have := loopChains_sub_mem_boundaries₁ (R := R) x z
  rw [hz, map_zero, add_zero] at this
  exact this

private lemma inverse₁_hurewiczAb (e : R ≃+* ℤ)
    (a : Additive (Group.Abelianization (FundamentalGroup X x))) :
    inverse₁ x e (hurewiczAb R x a) = a := by
  induction a using Additive.rec with | ofMul a =>
  induction a using Quot.ind with | mk p =>
  obtain ⟨p⟩ := p
  induction p using Path.Homotopic.Quotient.ind with | mk γ =>
  rw [Group.Abelianization.mk_eq_of]
  exact (congrArg (inverse₁ x e) (hurewiczAb_ofMul_of_mk x γ)).trans (inverse₁_loopClass x e γ)

/-- **The Hurewicz theorem in degree one**: for a path-connected space and a coefficient ring
`R` isomorphic to `ℤ`, the Hurewicz map identifies the abelianized fundamental group with the
first homology group, written as the explicit homology of the short complex `C₂ → C₁ → C₀`. -/
def hurewiczAddEquiv (e : R ≃+* ℤ) :
    Additive (Group.Abelianization (FundamentalGroup X x)) ≃+ H₁ R X where
  __ := hurewiczAb R x
  invFun := inverse₁ x e
  left_inv := inverse₁_hurewiczAb x e
  right_inv := hurewiczAb_inverse₁ x e

lemma hurewiczAddEquiv_ofMul_of_mk (e : R ≃+* ℤ) (γ : Path x x) :
    hurewiczAddEquiv x e (Additive.ofMul ((Group.Abelianization.of : FundamentalGroup X x →* _)
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)))) = loopClass R γ :=
  hurewiczAb_ofMul_of_mk x γ

lemma hurewiczAddEquiv_apply (e : R ≃+* ℤ)
    (a : Additive (Group.Abelianization (FundamentalGroup X x))) :
    hurewiczAddEquiv x e a = hurewiczAb R x a := by
  rw [hurewiczAddEquiv]
  -- The forward map of `hurewiczAddEquiv` is `hurewiczAb` by construction.
  rfl

/-- The inverse of the Hurewicz isomorphism sends the class of a loop to its class in the
abelianized fundamental group. -/
lemma hurewiczAddEquiv_symm_loopClass (e : R ≃+* ℤ) (γ : Path x x) :
    (hurewiczAddEquiv x e).symm (loopClass R γ) =
      Additive.ofMul ((Group.Abelianization.of : FundamentalGroup X x →* _)
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))) := by
  rw [AddEquiv.symm_apply_eq, hurewiczAddEquiv_ofMul_of_mk]

end Inverse

/-! ### Comparison with the homology of the singular chain complex -/

variable (R X) in
/-- The explicit homology `H₁ R X` of `sc₁ R X` is the first homology group of the singular chain
complex. -/
def H₁AddEquivHomology : H₁ R X ≃+ ((singularChains R).obj X).homology 1 :=
  ((sc₁ R X).moduleCatHomologyIso.symm ≪≫
    (((singularChains R).obj X).homologyIsoSc' 2 1 0 (by simp) (by simp)).symm).toLinearEquiv
      |>.toAddEquiv

/-- The identification of `H₁ R X` with the homology of the singular chain complex sends the
class of a cycle `c` to the homology class of the cycle of the complex lying over `c`. -/
lemma H₁AddEquivHomology_mk (c : cycles₁ R X) (z : ((singularChains R).obj X).cycles 1)
    (hz : (((singularChains R).obj X).iCycles 1).hom z = c) :
    H₁AddEquivHomology R X (H₁.mk c) = (((singularChains R).obj X).homologyπ 1).hom z := by
  have hi : (ComplexShape.down ℕ).prev 1 = 2 := by simp
  have hk : (ComplexShape.down ℕ).next 1 = 0 := by simp
  have h₁ := congr($(((singularChains R).obj X).cyclesIsoSc'_inv_iCycles 2 1 0 hi hk).hom
    ((sc₁ R X).moduleCatCyclesIso.inv.hom c))
  have h₂ := congr($((sc₁ R X).moduleCatCyclesIso_inv_iCycles).hom c)
  have h₃ := congr($((sc₁ R X).moduleCatCyclesIso_inv_π).hom c)
  have h₄ := congr($(((singularChains R).obj X).π_homologyIsoSc'_inv 2 1 0 hi hk).hom
    ((sc₁ R X).moduleCatCyclesIso.inv.hom c))
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h₁ h₂ h₃ h₄
  have hz₀ : z = (((singularChains R).obj X).cyclesIsoSc' 2 1 0 hi hk).inv.hom
      ((sc₁ R X).moduleCatCyclesIso.inv.hom c) :=
    HomologicalComplex.moduleCat_iCycles_injective _ 1 (hz.trans (h₁.trans h₂).symm)
  rw [hz₀, ← h₄]
  exact (congrArg (((singularChains R).obj X).homologyIsoSc' 2 1 0 hi hk).inv.hom h₃).symm

/-- The identification of `H₁ R X` with the homology of the singular chain complex sends the
class of a loop to the homology class of a cycle of the complex lying over the chain of the
loop. -/
lemma H₁AddEquivHomology_loopClass {x : X} (γ : Path x x)
    (z : ((singularChains R).obj X).cycles 1)
    (hz : (((singularChains R).obj X).iCycles 1).hom z = pathChain R γ.toContinuousMap) :
    H₁AddEquivHomology R X (loopClass R γ) = (((singularChains R).obj X).homologyπ 1).hom z := by
  rw [loopClass]
  exact H₁AddEquivHomology_mk _ z hz

/-- Two additive maps out of the first homology group of the singular chain complex agree once
they agree on the classes of `1`-cycles. -/
lemma homology_one_addMonoidHom_ext {A : Type*} [AddZeroClass A]
    {f g : ((singularChains R).obj X).homology 1 →+ A}
    (h : ∀ c : cycles₁ R X,
      f (H₁AddEquivHomology R X (H₁.mk c)) = g (H₁AddEquivHomology R X (H₁.mk c))) :
    f = g :=
  (AddMonoidHom.cancel_right (H₁AddEquivHomology R X).surjective).1 (H₁.addMonoidHom_ext h :
    f.comp (H₁AddEquivHomology R X).toAddMonoidHom = g.comp (H₁AddEquivHomology R X).toAddMonoidHom)

/-! ### The Hurewicz isomorphism -/

/-- **The Hurewicz theorem in degree one**: for a path-connected space `X` with a base point `x`
and a coefficient ring `R` isomorphic to `ℤ`, the Hurewicz map identifies the abelianization of
`π₁(X, x)` with `H₁(X; R)`, the first homology group of the singular chain complex of `X` with
coefficients in `R`. -/
def hurewiczHomologyAddEquiv [PathConnectedSpace X] (x : X) (e : R ≃+* ℤ) :
    Additive (Group.Abelianization (FundamentalGroup X x)) ≃+ ((singularChains R).obj
        X).homology 1 :=
  (hurewiczAddEquiv x e).trans (H₁AddEquivHomology R X)

lemma hurewiczHomologyAddEquiv_apply [PathConnectedSpace X] {x : X} (e : R ≃+* ℤ)
    (a : Additive (Group.Abelianization (FundamentalGroup X x))) :
    hurewiczHomologyAddEquiv x e a = H₁AddEquivHomology R X (hurewiczAb R x a) := by
  rw [hurewiczHomologyAddEquiv, AddEquiv.trans_apply, hurewiczAddEquiv_apply]

@[simp]
lemma hurewiczHomologyAddEquiv_ofMul_of_mk [PathConnectedSpace X] {x : X} (e : R ≃+* ℤ)
    (γ : Path x x) :
    hurewiczHomologyAddEquiv x e (Additive.ofMul
      ((Group.Abelianization.of : FundamentalGroup X x →* _)
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)))) =
        H₁AddEquivHomology R X (loopClass R γ) := by
  rw [hurewiczHomologyAddEquiv, AddEquiv.trans_apply, hurewiczAddEquiv_ofMul_of_mk]

/-- Two additive maps out of the first homology group of the singular chain complex of a
path-connected space agree once they agree on the Hurewicz classes of the loops at `x`. -/
lemma homology_one_addMonoidHom_ext_of_fundamentalGroup [PathConnectedSpace X] {A : Type*}
    [AddZeroClass A] (x : X) (e : R ≃+* ℤ) {f g : ((singularChains R).obj X).homology 1 →+ A}
    (h : ∀ γ : FundamentalGroup X x,
      f (hurewiczHomologyAddEquiv x e (Additive.ofMul (Group.Abelianization.of γ))) =
        g (hurewiczHomologyAddEquiv x e (Additive.ofMul (Group.Abelianization.of γ)))) :
    f = g := by
  refine AddMonoidHom.ext fun y ↦ ?_
  obtain ⟨a, rfl⟩ := (hurewiczHomologyAddEquiv x e).surjective y
  obtain ⟨γ, rfl⟩ := Group.Abelianization.exists_eq_ofMul_of a
  exact h γ

end TauCeti.HurewiczOne
