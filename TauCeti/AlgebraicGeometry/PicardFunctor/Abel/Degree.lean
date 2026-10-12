/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Degree.Sum
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Representable
public import TauCeti.AlgebraicGeometry.PicardFunctor.Abel.Jacobi
public import TauCeti.AlgebraicGeometry.PicardFunctor.MultiplicativeAbel

/-!
# The Abel–Jacobi maps of degree `d`

Let `f : X ⟶ S` be a smooth proper morphism of relative dimension one with a section `x₀`. For
every natural number `d`, the functor `Div^d_{X/S}` of relative effective Cartier divisors of
degree `d` maps to the relative Picard presheaf `T ↦ Pic(X_T) / Pic(T)` by the Abel map
`D ↦ 𝒪(D)`. Twisting by the `d`-th power of the class of the base-changed section `x₀_T`
normalizes it to the **Abel–Jacobi map of degree `d`**

  `abelJacobiMapOfDegree f hx₀ d : Div^d_{X/S} ⟶ (T ↦ Pic(X_T) / Pic(T))`,
  `D ↦ 𝒪(D - d • x₀_T)`,

which sends the divisor `d • x₀_T` to the identity. Once `Div^d_{X/S}` is represented by the
symmetric power `Symᵈ X` (here this is known only for `d ≤ 1`), these become the maps
`D ↦ 𝒪(D - d • x₀)` out of `Symᵈ X` used in the classical construction of the Jacobian from
symmetric powers of a curve.

Addition of divisors is written multiplicatively in the monoid of relative effective Cartier
divisors (the sum `D + E` is cut out by the product of the ideal sheaves), so below `D + E`
and `d • x₀_T` are `D * E` and `x₀_T ^ d` in Lean.

This file proves the compatibilities of these maps with the operations on divisors:

* addition of divisors goes to the group law: `AJ_{d+e}(D + E) = AJ_d(D) · AJ_e(E)`
  (`abelJacobiMapOfDegree_app_mul`);
* adding copies of `x₀_T` does not change the class: `AJ_{d+e}(D + e • x₀_T) = AJ_d(D)`
  (`abelJacobiMapOfDegree_app_mul_pow_basePoint`), so the maps are compatible with the
  stabilization maps `Div^d_{X/S} ⟶ Div^{d+e}_{X/S}`;
* in degree zero the map is trivial (`abelJacobiMapOfDegree_zero_app`);
* in degree one, under the isomorphism `Hom_S(-, X) ≅ Div¹_{X/S}` given by graphs, it is the
  Abel–Jacobi map `x ↦ 𝒪(Γₓ - x₀_T)` on points
  (`whiskerRight_graphDivisorDegreeOne_comp_abelJacobiMapOfDegree_one`);
* the divisor `Γ_{x₁} + ⋯ + Γ_{x_d}` of `d` points goes to the product of the Abel–Jacobi
  classes of the points (`abelJacobiMapOfDegree_app_prod_graphDivisor`): on `T`-points, the
  composite of `(x₁, …, x_d) ↦ Γ_{x₁} + ⋯ + Γ_{x_d}` with the Abel–Jacobi map of degree `d` is
  the product of `d` copies of the Abel–Jacobi map, hence symmetric in the points.

Representability of `Div^d_{X/S}` for `d ≥ 2`, and the identification of the image with the
degree-zero part of the Picard functor, are not treated here.

## References

* S. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry: Grothendieck's FGA
  Explained*, Section 9.3 (the Abel maps `Div^d_{X/S} ⟶ Pic_{X/S}`).
* J. S. Milne, *Jacobian varieties*, in *Arithmetic Geometry* (G. Cornell, J. H. Silverman,
  eds.), Springer, 1986, Sections 4 and 5 (the maps `D ↦ 𝒪(D - d P)` from `Symᵈ X` to the
  Jacobian).
-/

public section

open CategoryTheory Limits

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f] [RelativeDimensionLE 1 f]
  [SmoothOfRelativeDimension 1 f] {x₀ : S ⟶ X} (hx₀ : x₀ ≫ f = 𝟙 S)

/-- The class of `𝒪(D - d • x₀_T)` in `Pic(X_T) / Pic(T)` attached to a divisor `D` of degree
`d`. -/
private def abelJacobiClassOfDegree (d : ℕ) {T : (Over S)ᵒᵖ}
    (D : (relativeEffectiveCartierDegreeSubfunctor f d).toFunctor.obj T) :
    (relativePicardPresheaf f).obj T :=
  (abelMap f).app T (ULift.up D.1) /
    (abelMap f).app T (ULift.up ((graphDivisor f).app T (basePoint hx₀ T.unop))) ^ d

/-- The class of `𝒪(D - d • x₀_T)` is compatible with base change. -/
private lemma relativePicardPresheaf_map_abelJacobiClassOfDegree (d : ℕ) {T T' : (Over S)ᵒᵖ}
    (φ : T ⟶ T') (D : (relativeEffectiveCartierDegreeSubfunctor f d).toFunctor.obj T) :
    (relativePicardPresheaf f).map φ (abelJacobiClassOfDegree f hx₀ d D) =
      abelJacobiClassOfDegree f hx₀ d
        ((relativeEffectiveCartierDegreeSubfunctor f d).toFunctor.map φ D) := by
  -- Naturality of the Abel map, applied to `D` and to the divisor of the base point.
  have hD (E : (relativeEffectiveCartierSubfunctor f).toFunctor.obj T) :
      (relativePicardPresheaf f).map φ ((abelMap f).app T (ULift.up E)) =
        (abelMap f).app T' (ULift.up ((relativeEffectiveCartierSubfunctor f).toFunctor.map φ E)) :=
    (NatTrans.naturality_apply (abelMap f) φ
      (ULift.up E : ((relativeEffectiveCartierSubfunctor f).toFunctor ⋙
        uliftFunctor.{u + 1}).obj T)).symm
  rw [abelJacobiClassOfDegree, abelJacobiClassOfDegree, map_div, map_pow, hD, hD,
    ← graphDivisor_app_comp, comp_basePoint hx₀ φ.unop]
  -- The divisor underlying the pullback of `D` in `Div^d_{X/S}` is the pullback of the divisor
  -- underlying `D` in `Div_{X/S}`, by definition of `Subfunctor.toFunctor`.
  rfl

/-- The **Abel–Jacobi map of degree `d`** of a smooth proper morphism `f : X ⟶ S` of relative
dimension one with a section `x₀`: the natural transformation from the functor `Div^d_{X/S}` of
relative effective Cartier divisors of degree `d` on the base changes `X_T = T ×_S X` to the
relative Picard presheaf `T ↦ Pic(X_T) / Pic(T)`, sending a divisor `D` to the class of
`𝒪(D - d • x₀_T) = 𝒪(D) ⊗ 𝒪(x₀_T)^{⊗ -d}`, where `x₀_T` is the base change of `x₀`
(`abelJacobiMapOfDegree_app_apply`). -/
def abelJacobiMapOfDegree (d : ℕ) :
    (relativeEffectiveCartierDegreeSubfunctor f d).toFunctor ⋙ uliftFunctor.{u + 1} ⟶
      relativePicardPresheaf f ⋙ forget CommGrpCat where
  app T := TypeCat.ofHom fun D ↦ abelJacobiClassOfDegree f hx₀ d D.down
  naturality T T' φ := by
    ext ⟨D⟩
    exact (relativePicardPresheaf_map_abelJacobiClassOfDegree f hx₀ d φ D).symm

-- As for `abelJacobiMap_app_apply`, the source and target of
-- `(abelJacobiMapOfDegree f hx₀ d).app T` are spelled out in their simp-normal form, so that the
-- left-hand side passes the `simpNF` linter.
/-- The Abel–Jacobi map of degree `d` sends a divisor `D` to the quotient of the Abel map at `D`
by the `d`-th power of the Abel map at the graph of the base point, that is, to the class of
`𝒪(D - d • x₀_T)`. -/
lemma abelJacobiMapOfDegree_app_apply (d : ℕ) {T : (Over S)ᵒᵖ}
    (D : (relativeEffectiveCartierDegreeSubfunctor f d).toFunctor.obj T) :
    ConcreteCategory.hom (C := Type (u + 1))
      (X := uliftFunctor.{u + 1}.obj ((relativeEffectiveCartierDegreeSubfunctor f d).obj T))
      (Y := ToType ((relativePicardPresheaf f).obj T)) ((abelJacobiMapOfDegree f hx₀ d).app T)
      (ULift.up D) =
      (abelMap f).app T (ULift.up D.1) /
        (abelMap f).app T (ULift.up ((graphDivisor f).app T (basePoint hx₀ T.unop))) ^ d :=
  (rfl)

/-- **The Abel–Jacobi maps are additive**: the sum of divisors `D` and `E` of degrees `d` and
`e` goes to the product of their classes, `𝒪(D + E - (d + e) • x₀_T) =
𝒪(D - d • x₀_T) ⊗ 𝒪(E - e • x₀_T)`. -/
theorem abelJacobiMapOfDegree_app_mul {d e : ℕ} {T : (Over S)ᵒᵖ}
    (D : (relativeEffectiveCartierDegreeSubfunctor f d).toFunctor.obj T)
    (E : (relativeEffectiveCartierDegreeSubfunctor f e).toFunctor.obj T) :
    (abelJacobiMapOfDegree f hx₀ (d + e)).app T
        (ULift.up ⟨D.1 * E.1, mul_mem_relativeEffectiveCartierDegreeSubfunctor_obj f D.2 E.2⟩) =
      (abelJacobiMapOfDegree f hx₀ d).app T (ULift.up D) *
        (abelJacobiMapOfDegree f hx₀ e).app T (ULift.up E) := by
  rw [abelJacobiMapOfDegree_app_apply, abelJacobiMapOfDegree_app_apply,
    abelJacobiMapOfDegree_app_apply, abelMap_app_mul, pow_add, div_mul_div_comm]

/-- In degree zero the Abel–Jacobi map is trivial: the only divisor of degree zero is the empty
divisor, and `𝒪(∅) = 𝒪`. -/
@[simp]
lemma abelJacobiMapOfDegree_zero_app {T : (Over S)ᵒᵖ}
    (D : (relativeEffectiveCartierDegreeSubfunctor f 0).toFunctor.obj T) :
    ConcreteCategory.hom (C := Type (u + 1))
      (X := uliftFunctor.{u + 1}.obj ((relativeEffectiveCartierDegreeSubfunctor f 0).obj T))
      (Y := ToType ((relativePicardPresheaf f).obj T)) ((abelJacobiMapOfDegree f hx₀ 0).app T)
      (ULift.up D) = 1 := by
  rw [abelJacobiMapOfDegree_app_apply, pow_zero, div_one]
  have hD : D.1 = ⟨(⊤ : (pullback T.unop.hom f).IdealSheafData),
      top_mem_relativeEffectiveCartierSubfunctor_obj f T⟩ :=
    Subtype.ext ((mem_relativeEffectiveCartierDegreeSubfunctor_zero_obj_iff f).mp D.2)
  rw [hD]
  exact abelMap_app_top f T

/-- The divisor `n • x₀_T`, the `n`-th multiple of the graph of the base point, has degree `n`. -/
lemma graphDivisor_basePoint_pow_mem_relativeEffectiveCartierDegreeSubfunctor_obj (n : ℕ)
    (T : (Over S)ᵒᵖ) :
    (graphDivisor f).app T (basePoint hx₀ T.unop) ^ n ∈
      (relativeEffectiveCartierDegreeSubfunctor f n).obj T := by
  simpa using pow_mem_relativeEffectiveCartierDegreeSubfunctor_obj f
    ((range_graphDivisor f).le T ⟨basePoint hx₀ T.unop, rfl⟩) n

/-- **The Abel–Jacobi map of degree `d` sends `d • x₀_T` to the identity**:
`𝒪(d • x₀_T - d • x₀_T) = 𝒪`. -/
lemma abelJacobiMapOfDegree_app_pow_basePoint (d : ℕ) (T : (Over S)ᵒᵖ) :
    ConcreteCategory.hom (C := Type (u + 1))
      (X := uliftFunctor.{u + 1}.obj ((relativeEffectiveCartierDegreeSubfunctor f d).obj T))
      (Y := ToType ((relativePicardPresheaf f).obj T)) ((abelJacobiMapOfDegree f hx₀ d).app T)
        (ULift.up ⟨(graphDivisor f).app T (basePoint hx₀ T.unop) ^ d,
          graphDivisor_basePoint_pow_mem_relativeEffectiveCartierDegreeSubfunctor_obj
            f hx₀ d T⟩) = 1 := by
  rw [abelJacobiMapOfDegree_app_apply]
  simp only [← abelMapMonoidHom_apply, map_pow, div_self']

/-- **The Abel–Jacobi maps are compatible with stabilization**: adding `e` copies of the base
point to a divisor `D` of degree `d` does not change its class,
`𝒪(D + e • x₀_T - (d + e) • x₀_T) = 𝒪(D - d • x₀_T)`. -/
theorem abelJacobiMapOfDegree_app_mul_pow_basePoint {d : ℕ} (e : ℕ) {T : (Over S)ᵒᵖ}
    (D : (relativeEffectiveCartierDegreeSubfunctor f d).toFunctor.obj T) :
    (abelJacobiMapOfDegree f hx₀ (d + e)).app T
        (ULift.up ⟨D.1 * (graphDivisor f).app T (basePoint hx₀ T.unop) ^ e,
          mul_mem_relativeEffectiveCartierDegreeSubfunctor_obj f D.2
            (graphDivisor_basePoint_pow_mem_relativeEffectiveCartierDegreeSubfunctor_obj
              f hx₀ e T)⟩) =
      (abelJacobiMapOfDegree f hx₀ d).app T (ULift.up D) := by
  -- The divisor `e • x₀_T`, bundled with its degree, is the second summand.
  refine (abelJacobiMapOfDegree_app_mul f hx₀ D ⟨_,
    graphDivisor_basePoint_pow_mem_relativeEffectiveCartierDegreeSubfunctor_obj f hx₀ e T⟩).trans ?_
  rw [abelJacobiMapOfDegree_app_pow_basePoint, mul_one]

/-- **In degree one the Abel–Jacobi map is the Abel–Jacobi map on points**: composing the
isomorphism `Hom_S(-, X) ≅ Div¹_{X/S}`, `x ↦ Γₓ`, with the Abel–Jacobi map of degree one gives
the Abel–Jacobi map `x ↦ 𝒪(Γₓ - x₀_T)`. -/
theorem whiskerRight_graphDivisorDegreeOne_comp_abelJacobiMapOfDegree_one :
    Functor.whiskerRight (graphDivisorDegreeOne f) uliftFunctor.{u + 1} ≫
      abelJacobiMapOfDegree f hx₀ 1 = abelJacobiMap f hx₀ := by
  ext T ⟨x⟩
  have h := abelJacobiMapOfDegree_app_apply f hx₀ 1 ((graphDivisorDegreeOne f).app T x)
  rw [graphDivisorDegreeOne_app_apply_val, pow_one] at h
  exact h.trans (abelJacobiMap_app_apply f hx₀ x).symm

/-- The sum `Γ_{x_i}, i ∈ s` of the graphs of a finite family of `T`-points has degree the number
of points. -/
lemma prod_graphDivisor_mem_relativeEffectiveCartierDegreeSubfunctor_obj {ι : Type*}
    (s : Finset ι) {T : (Over S)ᵒᵖ} (x : ι → (T.unop ⟶ Over.mk f)) :
    ∏ i ∈ s, (graphDivisor f).app T (x i) ∈
      (relativeEffectiveCartierDegreeSubfunctor f s.card).obj T := by
  simpa using prod_mem_relativeEffectiveCartierDegreeSubfunctor_obj f s (d := fun _ ↦ 1)
    fun i _ ↦ (range_graphDivisor f).le T ⟨x i, rfl⟩

/-- **The Abel–Jacobi map of a sum of points is the product of their Abel–Jacobi classes**: for
a finite family of `T`-points `x_i, i ∈ s`, the divisor `∑ i ∈ s, Γ_{x_i}` goes to
`∏ i ∈ s, 𝒪(Γ_{x_i} - x₀_T)`. -/
theorem abelJacobiMapOfDegree_app_prod_graphDivisor {ι : Type*} (s : Finset ι)
    {T : (Over S)ᵒᵖ} (x : ι → (T.unop ⟶ Over.mk f)) :
    (abelJacobiMapOfDegree f hx₀ s.card).app T
        (ULift.up ⟨∏ i ∈ s, (graphDivisor f).app T (x i),
          prod_graphDivisor_mem_relativeEffectiveCartierDegreeSubfunctor_obj f s x⟩) =
      ∏ i ∈ s, (abelJacobiMap f hx₀).app T (ULift.up (x i)) := by
  have h := map_prod (abelMapMonoidHom f T) (fun i ↦ (graphDivisor f).app T (x i)) s
  simp only [abelMapMonoidHom_apply] at h
  rw [abelJacobiMapOfDegree_app_apply, Finset.prod_congr rfl fun i _ ↦
    abelJacobiMap_app_apply f hx₀ (x i), Finset.prod_div_distrib, Finset.prod_const, h]

end

end TauCeti.AlgebraicGeometry
