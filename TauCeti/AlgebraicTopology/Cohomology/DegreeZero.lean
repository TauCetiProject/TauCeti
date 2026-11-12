/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import TauCeti.AlgebraicTopology.Cohomology.Cup.Basic
public import TauCeti.AlgebraicTopology.Cohomology.Kronecker
public import TauCeti.AlgebraicTopology.Singular.Reduced

/-!
# Degree-zero singular cohomology as functions on path components

Let `k` be a commutative ring and `X` a space. A class `u ∈ H⁰(X; k)` has a value
`u(x) ∈ k` at every point `x : X` (`TopCat.singularCohomologyZeroEval`): the Kronecker pairing of
`u` with the class `[x] ∈ H₀(X; k)` of the point, equivalently the value at the unique point of the
pullback of `u` along `x : pt ⟶ X` (`TopCat.singularCohomologyZeroEval_naturality`). These values
identify `H⁰(X; k)` with the functions `X → k` that are constant on path components:

* a class is determined by its values (`TopCat.singularCohomologyZero_ext`), since the Kronecker
  map `H⁰(X; k) ⟶ Hom(H₀(X; k), k)` is bijective and the point classes generate `H₀(X; k)`;
* its values agree at points joined by a path (`TopCat.singularCohomologyZeroEval_eq_of_joined`);
* conversely every function constant on path components is the function of values of a class
  (`TopCat.exists_singularCohomologyZeroEval_eq`), through Mathlib's identification of `H₀(X; k)`
  with the coproduct of copies of `k` over the path components.

The values are multiplicative for the cup product (`TopCat.singularCohomologyZeroEval_singularCup`)
and the unit of the cup product, the class `TopCat.singularCohomologyZeroOne` of the constant
cocycle `1`, has the value `1` everywhere. Pulling back to a point reduces multiplicativity to the
unit law of the cup product on a point, where every degree-zero class is a multiple of the unit.

Consequently invertibility in `H⁰(X; k)` can be tested pointwise, one path component at a time: a
square matrix of degree-zero classes whose matrices of values are invertible at every point is
invertible for the cup product (`TopCat.exists_singularCup_matrix_eq_one`), and in particular a
class whose values are units is a unit (`TopCat.exists_singularCup_eq_one`). The inverse has, at
every point, the inverse matrix of values; it is a class because the matrix of values, and so its
inverse, is constant on path components.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.1 (`H⁰(X; G)` is the group of functions `X → G` constant on path components) and
  Section 3.2.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory

universe w

namespace TopCat

variable {k : Type w} [CommRing k]

section Eval

variable {X Y : TopCat.{w}}

/-- **The value of a degree-zero class at a point**: the value `u(x) ∈ k` of
`u ∈ H⁰(X; k)` at `x : X` is the Kronecker pairing of `u` with the class `[x] ∈ H₀(X; k)` of the
point. -/
def singularCohomologyZeroEval (x : X) :
    X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) 0 →ₗ[k] k where
  toFun u := (TauCeti.singularHomology₀Section (𝟙_ (ModuleCat.{w} k)) x ≫
    X.singularKronecker k 0 u).hom (1 : k)
  map_add' u v := by simp
  map_smul' a u := by simp

lemma singularCohomologyZeroEval_apply (x : X)
    (u : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) 0) :
    singularCohomologyZeroEval x u =
      (TauCeti.singularHomology₀Section (𝟙_ (ModuleCat.{w} k)) x ≫
        X.singularKronecker k 0 u).hom (1 : k) :=
  (rfl)

/-- **A degree-zero class is determined by its values at the points.** -/
theorem singularCohomologyZero_ext
    {u v : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) 0}
    (h : ∀ x : X, singularCohomologyZeroEval x u = singularCohomologyZeroEval x v) : u = v := by
  refine (X.singularKronecker_bijective_zero k).1
    (TauCeti.singularHomology₀_hom_ext _ fun x ↦ ?_)
  ext
  exact h x

/-- **Naturality of the values**: the value of a pulled-back class `f^* u` at `x` is the value of
`u` at `f x`. -/
@[simp]
lemma singularCohomologyZeroEval_naturality (f : X ⟶ Y) (x : X)
    (u : Y.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) 0) :
    singularCohomologyZeroEval x (TopCat.singularCohomologyMap f 0 u) =
      singularCohomologyZeroEval (f x) u := by
  simp only [singularCohomologyZeroEval_apply, singularKronecker_naturality,
    TauCeti.singularHomology₀Section_naturality_assoc]

/-- **The values of a degree-zero class are constant on path components.** -/
theorem singularCohomologyZeroEval_eq_of_joined {x y : X} (h : Joined x y)
    (u : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) 0) :
    singularCohomologyZeroEval x u = singularCohomologyZeroEval y u := by
  have hxy : TauCeti.singularHomology₀Section (𝟙_ (ModuleCat.{w} k)) x =
      TauCeti.singularHomology₀Section (𝟙_ (ModuleCat.{w} k)) y := by
    rw [← cancel_mono (X.singularHomology₀Iso _).hom,
      TauCeti.singularHomology₀Section_singularHomology₀Iso_hom,
      TauCeti.singularHomology₀Section_singularHomology₀Iso_hom]
    exact congrArg (Sigma.ι _) (Quotient.sound h)
  rw [singularCohomologyZeroEval_apply, singularCohomologyZeroEval_apply, hxy]

/-- **Every function constant on path components is the function of values of a degree-zero
class.** -/
theorem exists_singularCohomologyZeroEval_eq (f : X → k)
    (hf : ∀ x y : X, Joined x y → f x = f y) :
    ∃ u : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) 0,
      ∀ x : X, singularCohomologyZeroEval x u = f x := by
  let f' : ZerothHomotopy X → k := Quotient.lift f hf
  obtain ⟨u, hu⟩ := (X.singularKronecker_bijective_zero (R := 𝟙_ (ModuleCat.{w} k))
    (M := 𝟙_ (ModuleCat.{w} k)) k).2
    ((X.singularHomology₀Iso _).hom ≫ Sigma.desc fun c ↦ f' c • 𝟙 _)
  refine ⟨u, fun x ↦ ?_⟩
  rw [singularCohomologyZeroEval_apply, hu,
    TauCeti.singularHomology₀Section_singularHomology₀Iso_hom_assoc, Sigma.ι_comp_desc]
  simp [f', ZerothHomotopy.mk]

end Eval

section Unit

variable (X : TopCat.{w})

/-- **The unit of the cup product** in `H⁰(X; k)`: the class of the constant cocycle `1`. -/
def singularCohomologyZeroOne :
    X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) 0 :=
  (X.singularCochainComplex (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k))).homologyπ 0
    (X.constSingularCocycle k (𝟙 (𝟙_ (ModuleCat.{w} k))))

variable {X}

/-- The unit class pulls back to the unit class. -/
@[simp]
lemma singularCohomologyMap_singularCohomologyZeroOne {Y : TopCat.{w}} (f : X ⟶ Y) :
    TopCat.singularCohomologyMap f 0 (singularCohomologyZeroOne (k := k) Y) =
      singularCohomologyZeroOne X :=
  singularCohomologyMap_homologyπ_constSingularCocycle f k _

/-- The unit class has the value `1` at every point. -/
@[simp]
lemma singularCohomologyZeroEval_singularCohomologyZeroOne (x : X) :
    singularCohomologyZeroEval x (singularCohomologyZeroOne (k := k) X) = 1 := by
  have h : TauCeti.singularHomology₀Section (𝟙_ (ModuleCat.{w} k)) x ≫
      X.singularKronecker k 0 (singularCohomologyZeroOne X) = 𝟙 _ := by
    rw [TauCeti.singularHomology₀Section_def, SSet.ιHomology₀_def, singularCohomologyZeroOne]
    erw [Category.assoc, singularKronecker_homologyπ, HomologicalComplex.liftCycles_i_assoc]
    rw [iCycles_constSingularCocycle, SSet.ιChainComplex_constCochain]
  rw [singularCohomologyZeroEval_apply, h]
  rfl

/-- **The left unit law** for the cup product with the unit class. -/
@[simp]
lemma singularCup_singularCohomologyZeroOne_left {q : ℕ} (h : 0 + q = q)
    (b : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) q) :
    X.singularCup k (λ_ _).inv (λ_ _).hom 0 q q h (singularCohomologyZeroOne X) b = b :=
  X.singularCup_constSingularCocycle_left k (η := 𝟙 _) (by simp) (by simp) h b

/-- **The right unit law** for the cup product with the unit class. -/
@[simp]
lemma singularCup_singularCohomologyZeroOne_right {p : ℕ} (h : p + 0 = p)
    (a : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) p) :
    X.singularCup k (λ_ _).inv (λ_ _).hom p 0 p h a (singularCohomologyZeroOne X) = a :=
  X.singularCup_constSingularCocycle_right k (η := 𝟙 _) (by simp [unitors_inv_equal])
    (by simp [unitors_equal]) h a

/-- On a one-point space every degree-zero class is its value times the unit class. -/
lemma eq_singularCohomologyZeroEval_smul_singularCohomologyZeroOne [Unique X]
    (u : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) 0) :
    u = singularCohomologyZeroEval default u • singularCohomologyZeroOne X :=
  singularCohomologyZero_ext fun x ↦ by
    rw [Unique.eq_default x, map_smul, singularCohomologyZeroEval_singularCohomologyZeroOne,
      smul_eq_mul, mul_one]

/-- Pulling back a degree-zero class along the constant map at `x` gives its value at `x` times
the unit class. -/
@[simp]
lemma singularCohomologyMap_const_zero {Y : TopCat.{w}} (x : X)
    (u : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) 0) :
    TopCat.singularCohomologyMap (TopCat.ofHom (ContinuousMap.const Y x)) 0 u =
      singularCohomologyZeroEval x u • singularCohomologyZeroOne Y :=
  singularCohomologyZero_ext fun y ↦ by
    rw [singularCohomologyZeroEval_naturality, map_smul,
      singularCohomologyZeroEval_singularCohomologyZeroOne, smul_eq_mul, mul_one]
    rfl

/-- **The values are multiplicative for the cup product.** -/
@[simp]
theorem singularCohomologyZeroEval_singularCup (x : X)
    (u v : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) 0) :
    singularCohomologyZeroEval x (X.singularCup k (λ_ _).inv (λ_ _).hom 0 0 0 rfl u v) =
      singularCohomologyZeroEval x u * singularCohomologyZeroEval x v := by
  let s : TopCat.of PUnit.{w + 1} ⟶ X := TopCat.ofHom (ContinuousMap.const _ x)
  have hs (w' : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) 0) :
      singularCohomologyZeroEval x w' =
        singularCohomologyZeroEval PUnit.unit (TopCat.singularCohomologyMap s 0 w') :=
    (singularCohomologyZeroEval_naturality s PUnit.unit w').symm
  rw [hs, hs u, hs v, ← singularCup_naturality,
    eq_singularCohomologyZeroEval_smul_singularCohomologyZeroOne
      (TopCat.singularCohomologyMap s 0 u),
    eq_singularCohomologyZeroEval_smul_singularCohomologyZeroOne
      (TopCat.singularCohomologyMap s 0 v)]
  simp only [map_smul, LinearMap.smul_apply, singularCup_singularCohomologyZeroOne_left,
    singularCohomologyZeroEval_singularCohomologyZeroOne, smul_eq_mul, mul_one]
  exact mul_comm _ _

end Unit

section Invertibility

variable {X : TopCat.{w}} {ι : Type w} [Fintype ι] [DecidableEq ι]

/-- **Invertibility of a matrix of degree-zero classes is pointwise**: if `A` is a square matrix of
classes in `H⁰(X; k)` whose matrix of values `(A i j)(x)` is invertible at every point `x`, then
`A` has a two-sided inverse `B` for the matrix product built from the cup product. -/
theorem exists_singularCup_matrix_eq_one
    (A : ι → ι → X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) 0)
    (hA : ∀ x : X, IsUnit (Matrix.of fun i j ↦ singularCohomologyZeroEval x (A i j))) :
    ∃ B : ι → ι → X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) 0,
      (∀ i l, ∑ j, X.singularCup k (λ_ _).inv (λ_ _).hom 0 0 0 rfl (A i j) (B j l) =
        if i = l then singularCohomologyZeroOne X else 0) ∧
      (∀ i l, ∑ j, X.singularCup k (λ_ _).inv (λ_ _).hom 0 0 0 rfl (B i j) (A j l) =
        if i = l then singularCohomologyZeroOne X else 0) := by
  let Ax : X → Matrix ι ι k := fun x ↦ Matrix.of fun i j ↦ singularCohomologyZeroEval x (A i j)
  have hAx {x y : X} (h : Joined x y) : Ax x = Ax y := by
    ext i j
    exact singularCohomologyZeroEval_eq_of_joined h (A i j)
  have hB (i j : ι) : ∃ b : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) 0, ∀ x, singularCohomologyZeroEval x b = (Ax x)⁻¹ i j :=
    exists_singularCohomologyZeroEval_eq _ fun x y h ↦ by rw [hAx h]
  choose B hB using hB
  have key (P Q : ι → ι → X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k
      (𝟙_ (ModuleCat.{w} k)) 0)
      (hPQ : ∀ x, (Matrix.of fun i j ↦ singularCohomologyZeroEval x (P i j)) *
        (Matrix.of fun i j ↦ singularCohomologyZeroEval x (Q i j)) = 1) (i l : ι) :
      ∑ j, X.singularCup k (λ_ _).inv (λ_ _).hom 0 0 0 rfl (P i j) (Q j l) =
        if i = l then singularCohomologyZeroOne X else 0 :=
    singularCohomologyZero_ext fun x ↦ by
      have := congrFun (congrFun (hPQ x) i) l
      simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply] at this
      rw [map_sum]
      simp only [singularCohomologyZeroEval_singularCup, this]
      split_ifs <;> simp
  have hBx (x : X) : (Matrix.of fun i j ↦ singularCohomologyZeroEval x (B i j)) = (Ax x)⁻¹ := by
    ext i j
    exact hB i j x
  refine ⟨B, key A B fun x ↦ ?_, key B A fun x ↦ ?_⟩
  · rw [hBx]
    exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (hA x))
  · rw [hBx]
    exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (hA x))

omit [Fintype ι] [DecidableEq ι] in
/-- **A degree-zero class whose values are units is a unit** for the cup product. -/
theorem exists_singularCup_eq_one
    (u : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) 0)
    (hu : ∀ x : X, IsUnit (singularCohomologyZeroEval x u)) :
    ∃ v : X.singularCohomology (𝟙_ (ModuleCat.{w} k)) k (𝟙_ (ModuleCat.{w} k)) 0,
      X.singularCup k (λ_ _).inv (λ_ _).hom 0 0 0 rfl u v = singularCohomologyZeroOne X ∧
      X.singularCup k (λ_ _).inv (λ_ _).hom 0 0 0 rfl v u = singularCohomologyZeroOne X := by
  obtain ⟨B, h₁, h₂⟩ := exists_singularCup_matrix_eq_one (ι := PUnit.{w + 1}) (fun _ _ ↦ u)
    fun x ↦ (Matrix.isUnit_iff_isUnit_det _).2 (by simpa using hu x)
  exact ⟨B PUnit.unit PUnit.unit, by simpa using h₁ PUnit.unit PUnit.unit,
    by simpa using h₂ PUnit.unit PUnit.unit⟩

end Invertibility

end TopCat
