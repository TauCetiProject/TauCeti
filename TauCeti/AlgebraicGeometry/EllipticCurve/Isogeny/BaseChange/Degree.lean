/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Degree
-- Proof-only: `CoordinateRing.map` sends the monomial basis to the monomial basis.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.ScalarExtension
-- Proof-only: clearing the denominators of finitely many fractions.
import Mathlib.RingTheory.Localization.Integer

/-!
# The degree of an isogeny is invariant under base change

Let `φ : W₁ → W₂` be an isogeny over a field `F` and `f : F →+* K` a homomorphism of fields. This
file proves `deg (φ.map f) = deg φ`: base change along any field extension, algebraic or not,
preserves the degree, and so does transport along an automorphism of `F`.

Write `M = φ^* F(W₂) ⊆ F(W₁)` and `M' = φ_K^* K(W₂) ⊆ K(W₁)`, so that `deg φ = [F(W₁) : M]` and
`deg (φ.map f) = [K(W₁) : M']`. The embedding `F(W₁) → K(W₁)` carries `M` into `M'`, and the proof
shows that it carries a basis of `F(W₁)` over `M` to a basis of `K(W₁)` over `M'`.

* **Spanning.** The `M'`-span of the image of the basis contains the image of `F(W₁)`, and is
  closed under multiplication. It is therefore a subalgebra of `K(W₁)`, finite over the field `M'`
  and so itself a field. It contains `K` and the generic point, hence the coordinate ring of
  `W₁⁄K`, and hence every fraction.
* **Independence.** An `M'`-linear relation among the images becomes, once the coefficients are
  written over a common denominator and expanded in the monomial basis of `K[W₂]`, a `K`-linear
  relation among the images of the products `φ^*(xⁱyʲ) · bₖ`. These products are `F`-linearly
  independent in `F(W₁)`, and `F(W₁)` is linearly disjoint from `K` over `F`
  (`WeierstrassCurve.Affine.FunctionField.linearIndependent_map`), so the relation is trivial.

Linear disjointness of `F(W₁)` and `K` is where the curve enters. The coordinate ring `K[W₁⁄K]` is
the scalar extension `K ⊗_F F[W₁]`, the monomials `xⁱyʲ` forming a basis of both, so `F`-linearly
independent elements of `F[W₁]` stay `K`-linearly independent; clearing denominators passes this to
the function fields. For a separable algebraic extension of constants of an arbitrary field in
which the constants are relatively algebraically closed, this persistence of linear independence is
`TauCeti.linearIndependent_algebraMap_comp_of_isIntegrallyClosedIn_of_isSeparable`; the Weierstrass
argument needs no hypothesis on `K` at all, so it also covers inseparable and transcendental
extensions, such as an algebraic closure of an imperfect field.

## Main results

* `TauCeti.Isogeny.degree_map`: `deg (φ.map f) = deg φ`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.
* [H. Stichtenoth, *Algebraic Function Fields and Codes*][stichtenoth2009], III.6, the case of an
  algebraic extension of constants.
-/

public section

open WeierstrassCurve.Affine
open scoped nonZeroDivisors

namespace TauCeti.Isogeny

variable {F K : Type*} [Field F] [Field K] {W₁ W₂ : WeierstrassCurve.Affine F}

/-- The pullback along `φ.map f` of a function `z` of the coordinate ring of `W₂⁄K` is the
`K`-linear combination, with the coefficients of `z` in the monomial basis, of the images in
`K(W₁)` of the pullbacks along `φ` of the monomials of `F[W₂]`. -/
private theorem fieldPullback_map_algebraMap (φ : Isogeny W₁ W₂) (f : F →+* K)
    (z : (W₂.map f).CoordinateRing) :
    (φ.map f).fieldPullback (algebraMap _ _ z) =
      ((CoordinateRing.basisMonomials (W₂.map f)).repr z).sum fun j c ↦
        c • FunctionField.map W₁ f
          (φ.fieldPullback (algebraMap _ _ (CoordinateRing.basisMonomials W₂ j))) := by
  conv_lhs => rw [← (CoordinateRing.basisMonomials (W₂.map f)).linearCombination_repr z,
    Finsupp.linearCombination_apply]
  rw [Finsupp.sum, Finsupp.sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Algebra.smul_def, map_mul, map_mul, ← IsScalarTower.algebraMap_apply, AlgHom.commutes,
    Algebra.smul_def, ← CoordinateRing.map_basisMonomials,
    ← FunctionField.map_algebraMap_coordinateRing, map_fieldPullback_map]

/-- The monomials `xⁱyʲ` of `F[W₂]`, pulled back along `φ`, are linearly independent over `F` in
`φ^* F(W₂)`. -/
private theorem linearIndependent_pulledBackMonomials (φ : Isogeny W₁ W₂) :
    LinearIndependent F fun j : ℕ × Fin 2 ↦ (⟨φ.fieldPullback
      (algebraMap _ _ (CoordinateRing.basisMonomials W₂ j)), AlgHom.mem_fieldRange.2 ⟨_, rfl⟩⟩ :
        φ.fieldPullback.fieldRange) :=
  LinearIndependent.of_comp (φ.fieldPullback.fieldRange.val.toLinearMap) <|
    (CoordinateRing.basisMonomials W₂).linearIndependent.map' ((φ.fieldPullback.toLinearMap).comp
      (IsScalarTower.toAlgHom F W₂.CoordinateRing W₂.FunctionField).toLinearMap)
      (LinearMap.ker_eq_bot.2 (φ.fieldPullback.injective.comp
        (FaithfulSMul.algebraMap_injective _ _)))

/-- The image of a basis of `F(W₁)` over `φ^* F(W₂)` is linearly independent over
`φ_K^* K(W₂)`. -/
private theorem linearIndependent_functionFieldMap_basis (φ : Isogeny W₁ W₂) (f : F →+* K)
    {ι : Type*} [Finite ι] (b : Module.Basis ι φ.fieldPullback.fieldRange W₁.FunctionField) :
    LinearIndependent (φ.map f).fieldPullback.fieldRange (FunctionField.map W₁ f ∘ b) := by
  classical
  have := Fintype.ofFinite ι
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  -- each coefficient is a pulled-back function `φ_K^* (h i)`
  choose h hh using fun i ↦ AlgHom.mem_fieldRange.1 (g i).2
  -- with a common denominator `s`: `s • h i` is the function `r i` of the coordinate ring
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples (W₂.map f).CoordinateRing⁰
    Finset.univ h
  choose r hr using fun i ↦ hs i (Finset.mem_univ i)
  set B := CoordinateRing.basisMonomials W₂ with hB
  set B' := CoordinateRing.basisMonomials (W₂.map f) with hB'
  -- the products of the pulled-back monomials of `F[W₂]` with the basis, mapped to `K(W₁)`, are
  -- linearly independent over `K`
  let m : ℕ × Fin 2 → φ.fieldPullback.fieldRange := fun j ↦
    ⟨φ.fieldPullback (algebraMap _ _ (B j)), AlgHom.mem_fieldRange.2 ⟨_, rfl⟩⟩
  have hK := FunctionField.linearIndependent_map W₁ f
    (linearIndependent_smul (linearIndependent_pulledBackMonomials φ) b.linearIndependent)
  -- the monomials occurring in some `r i`
  set T := Finset.univ.biUnion fun i ↦ (B'.repr (r i)).support
  have hT (i) : (B'.repr (r i)).support ⊆ T :=
    Finset.subset_biUnion_of_mem (fun i ↦ (B'.repr (r i)).support) (Finset.mem_univ i)
  -- multiplying the relation `∑ g i • b i = 0` by `φ_K^* s` gives a `K`-linear relation
  have key : ∑ p ∈ T ×ˢ Finset.univ,
      B'.repr (r p.2) p.1 • FunctionField.map W₁ f (m p.1 • b p.2) = 0 := by
    have := congrArg
      ((φ.map f).fieldPullback (algebraMap _ _ (s : (W₂.map f).CoordinateRing)) * ·) hg
    simp only [mul_zero, Finset.mul_sum] at this
    rw [Finset.sum_product, Finset.sum_comm, ← this]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hgi : (φ.map f).fieldPullback (algebraMap _ _ (s : (W₂.map f).CoordinateRing)) *
        (g i : (W₁.map f).FunctionField) = (φ.map f).fieldPullback (algebraMap _ _ (r i)) := by
      rw [hr i, Algebra.smul_def, map_mul, hh]
    rw [Function.comp_apply, IntermediateField.smul_def, smul_eq_mul, ← mul_assoc, hgi,
      fieldPullback_map_algebraMap, ← hB, ← hB', Finsupp.sum_of_support_subset _ (hT i)
        (fun j c ↦ c • FunctionField.map W₁ f (m j)) (fun _ _ ↦ zero_smul _ _), Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [smul_mul_assoc, Algebra.smul_def (m j), map_mul, IntermediateField.algebraMap_apply]
  -- so every `r i` vanishes, and with it every `g i`
  have hc := linearIndependent_iff'.1 hK _ _ key
  have hr0 : r i = 0 := by
    refine B'.repr.injective (Finsupp.ext fun j ↦ ?_)
    by_cases hj : j ∈ T
    · simpa using hc (j, i) (Finset.mk_mem_product hj (Finset.mem_univ i))
    · simpa using Finsupp.notMem_support_iff.1 fun h ↦ hj (hT i h)
  have hs0 : algebraMap (W₂.map f).CoordinateRing (W₂.map f).FunctionField s ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  have hh0 : h i = 0 := by
    have := hr i
    rw [hr0, map_zero, Algebra.smul_def, eq_comm, mul_eq_zero] at this
    exact this.resolve_left hs0
  exact Subtype.ext (by rw [← hh, hh0, map_zero, ZeroMemClass.coe_zero])

/-- The image of a basis of `F(W₁)` over `φ^* F(W₂)` spans `K(W₁)` over `φ_K^* K(W₂)`. -/
private theorem span_functionFieldMap_basis (φ : Isogeny W₁ W₂) (f : F →+* K) {ι : Type*}
    [Finite ι] (b : Module.Basis ι φ.fieldPullback.fieldRange W₁.FunctionField) :
    Submodule.span (φ.map f).fieldPullback.fieldRange
      (Set.range (FunctionField.map W₁ f ∘ b)) = ⊤ := by
  classical
  have := Fintype.ofFinite ι
  set M' := (φ.map f).fieldPullback.fieldRange
  set V := Submodule.span M' (Set.range (FunctionField.map W₁ f ∘ b))
  -- `FunctionField.map W₁ f` carries `φ^* F(W₂)` into `φ_K^* K(W₂)`
  have hM (c : φ.fieldPullback.fieldRange) : FunctionField.map W₁ f c ∈ M' := by
    obtain ⟨z, hz⟩ := AlgHom.mem_fieldRange.1 c.2
    exact AlgHom.mem_fieldRange.2 ⟨FunctionField.map W₂ f z, by rw [map_fieldPullback_map, hz]⟩
  -- so the image of `F(W₁)` lies in `V`
  have hE (e : W₁.FunctionField) : FunctionField.map W₁ f e ∈ V := by
    rw [← b.sum_repr e, map_sum]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    have : FunctionField.map W₁ f (b.repr e i • b i) =
        (⟨_, hM (b.repr e i)⟩ : M') • FunctionField.map W₁ f (b i) := by
      rw [IntermediateField.smul_def, smul_eq_mul, IntermediateField.smul_def, smul_eq_mul,
        map_mul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  -- `V` is closed under multiplication, so it is a subalgebra, finite over `M'`
  have hmul (x y) (hx : x ∈ V) (hy : y ∈ V) : x * y ∈ V := by
    have hle : V * V ≤ V := by
      rw [Submodule.span_mul_span, Submodule.span_le]
      rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
      simp only [Function.comp_apply, ← map_mul]
      exact hE _
    exact hle (Submodule.mul_mem_mul hx hy)
  let S : Subalgebra M' (W₁.map f).FunctionField := V.toSubalgebra (by simpa using hE 1) hmul
  have hfg : (Subalgebra.toSubmodule S).FG :=
    ⟨Finset.univ.image (FunctionField.map W₁ f ∘ b), by simp [S, V, Function.comp_def]⟩
  -- it contains the coordinate ring of `W₁.map f`, generated over `K` by the generic point
  have hcoord (z : (W₁.map f).CoordinateRing) :
      algebraMap _ (W₁.map f).FunctionField z ∈ S := by
    refine (Algebra.adjoin_le ?_ : Algebra.adjoin K _ ≤ S.restrictScalars K)
      (algebraMap_mem_adjoin_genericX_genericY (W₁.map f) z)
    rintro _ (rfl | rfl)
    · rw [← FunctionField.map_genericX]
      exact hE _
    · rw [← FunctionField.map_genericY]
      exact hE _
  -- and, being finite over the field `M'`, it is a field, so it contains every fraction
  rw [eq_top_iff]
  intro ω _
  obtain ⟨a, c, -, rfl⟩ := IsFractionRing.div_surjective (A := (W₁.map f).CoordinateRing) ω
  have hinv : (algebraMap _ (W₁.map f).FunctionField c)⁻¹ ∈ S :=
    S.inv_mem_of_algebraic (x := ⟨_, hcoord c⟩)
      (IsIntegral.of_mem_of_fg S hfg _ (hcoord c)).isAlgebraic
  rw [div_eq_mul_inv]
  exact S.mul_mem (hcoord a) hinv

/-- **Base change preserves the degree of an isogeny**: `deg (φ.map f) = deg φ` for every
homomorphism of fields `f`, in particular along every field extension. -/
@[simp]
theorem degree_map (φ : Isogeny W₁ W₂) (f : F →+* K) : (φ.map f).degree = φ.degree := by
  -- a basis of `F(W₁)` over `φ^* F(W₂)` maps to a basis of `K(W₁)` over `φ_K^* K(W₂)`
  let b := Module.finBasis φ.fieldPullback.fieldRange W₁.FunctionField
  rw [degree_def, degree_def, Module.finrank_eq_card_basis
    (Module.Basis.mk (linearIndependent_functionFieldMap_basis φ f b)
      (span_functionFieldMap_basis φ f b).ge), Fintype.card_fin]

end TauCeti.Isogeny

end
