/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Ideal
public import TauCeti.Algebra.Category.GradedModuleCat.Concentrated
public import TauCeti.Algebra.Category.GradedModuleCat.HomLaurentSupport
import TauCeti.Algebra.Polynomial.Laurent.Coeff
import TauCeti.CategoryTheory.Linear.Biproduct
import TauCeti.CategoryTheory.Linear.FullyFaithful

/-!
# Graded Hom-dimension coordinates on `K₀^gr(proj A)`

Let `A` be a graded algebra over a field `k` (not assumed finite-dimensional) and let `M` be a
finite-dimensional graded `A`-module. Every short exact sequence of finitely generated graded
projectives splits (`TauCeti.gradedFiniteProjectiveModulesExactStructure_eq_split`), and shifting
the source by `1` shifts the graded Hom dimension `∑ⱼ dim_k Hom(P, M{j}) qʲ` by `q`. Hence the
graded Hom dimension descends via `TauCeti.LaurentK0.lift` to a `ℤ[q,q⁻¹]`-linear functional

```text
TauCeti.gradedHomShiftCoordinate M : K₀^gr(proj A) →ₗ[ℤ[q,q⁻¹]] ℤ[q,q⁻¹].
```

This construction is modelled directly on `TauCeti.gradedIdempotentCoordinate` in
`TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Idempotent.Coordinate`, using graded Hom
dimensions on `gradedFiniteProjectiveModulesExactStructure 𝒜` in place of idempotent graded
dimensions on `gradedFiniteModulesExactStructure 𝒜`. It needs neither finite-dimensionality of `A`
nor a `HasExt` instance.

On an idempotent projective `[A f]` with `f ∈ 𝒜 0`, the functional evaluates to
`bar(gdim(f • M))`. Consequently, when the classes `[A eᵢ]` form a Laurent basis `bP` of
`K₀^gr(proj A)` and `M` satisfies `gdim(eⱼ • M) = 0` for every `j ≠ i`, the functional equals
`bar(gdim(eᵢ • M))` times the `i`th coordinate in `bP`. Evaluating on `[P]` recovers the full
Laurent-polynomial identity `∑ⱼ dim_k Hom(P, M{j}) qʲ = bar(gdim(eᵢ • M)) · [P]ᵢ`. When `P` is
generated in a single degree `d` and `M` is concentrated in degree zero with `gdim(eⱼ • M) = 0`
for all `j ≠ i`, the weighted coordinate `gdim(eᵢ • M) · [P]ᵢ` is supported in degree `d` (and may
vanish).

## Main definitions

* `TauCeti.gradedHomShiftCoordinate`: the `ℤ[q,q⁻¹]`-linear functional on `K₀^gr(proj A)` sending
  `[P]` to `∑ⱼ dim_k Hom(P, M{j}) qʲ`.

## Main results

* `TauCeti.gradedHomShiftCoordinate_of`: on an object class `[P]`, the functional evaluates to
  `gradedDimension k (fun j => P ⟶ M{j})`.
* `TauCeti.gradedHomShiftCoordinate_gradedIdempotentProjective`: on `[A f]` for a degree-zero
  idempotent `f`, the functional evaluates to `bar(gdim(f • M))`.
* `TauCeti.gradedHomShiftCoordinate_eq_mul_repr`: for a finite-dimensional graded module `M` with
  `gdim(eⱼ • M) = 0` for every `j ≠ i`, `gradedHomShiftCoordinate M x = bar(gdim(eᵢ • M)) · xᵢ`.
* `TauCeti.gradedDimension_hom_shiftObj_eq_mul_repr`: for a finite graded projective `P` and a
  finite-dimensional graded module `M` with `gdim(eⱼ • M) = 0` for every `j ≠ i`,
  `∑ⱼ dim_k Hom(P, M{j}) qʲ = bar(gdim(eᵢ • M)) · [P]ᵢ`.
* `TauCeti.coeff_invert_smulGradedDimension_mul_repr`: for a finite graded projective `P` and a
  finite-dimensional graded module `M` with `gdim(eⱼ • M) = 0` for every `j ≠ i`, the coefficient
  of `qʲ` in `bar(gdim(eᵢ • M)) · [P]ᵢ` is `dim_k Hom(P, M{j})`.
* `TauCeti.smulGradedDimension_mul_repr_of_isGeneratedInDegree`: when `P` is generated in degree
  `d` and `M` is concentrated in degree zero with `gdim(eⱼ • M) = 0` for every `j ≠ i`, the
  weighted coordinate `gdim(eᵢ • M) · [P]ᵢ` equals `dim_k Hom(P, M{d}) · qᵈ` (and may vanish).

## References

* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  Sections 1.2 and 2.11, for generating degrees and projective multiplicities from shifted Hom
  spaces.
* Zsuzsanna Dancso and Anthony Licata, "Koszul algebras and flow lattices", Section 2.2, for the
  graded Grothendieck group convention `[M{1}] = q[M]`.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory LaurentPolynomial

universe uk uA uI

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]

/-- A conflation of finite graded projectives splits, so graded Hom dimensions into shifts of `M`
are additive on conflations. -/
private theorem homShiftGradedDimension_conflation (M : GradedModuleCat.{uA} 𝒜) [Module.Finite k M]
    {S : ShortComplex (gradedFiniteProjectiveModules 𝒜).FullSubcategory}
    (hS : (gradedFiniteProjectiveModulesExactStructure 𝒜).Conflation S) :
    gradedDimension k (fun j => S.X₂.obj ⟶ M.shiftObj j)
        (GradedModuleCat.hasFiniteLaurentSupport_hom_shiftObj S.X₂.obj M) =
      gradedDimension k (fun j => S.X₁.obj ⟶ M.shiftObj j)
          (GradedModuleCat.hasFiniteLaurentSupport_hom_shiftObj S.X₁.obj M) +
        gradedDimension k (fun j => S.X₃.obj ⟶ M.shiftObj j)
          (GradedModuleCat.hasFiniteLaurentSupport_hom_shiftObj S.X₃.obj M) := by
  rw [gradedFiniteProjectiveModulesExactStructure_eq_split] at hS
  obtain ⟨split⟩ := (ExactStructure.split_conflation S).mp hS
  have hsplit := split.map (gradedFiniteProjectiveModules 𝒜).ι
  let eHom (j : ℤ) : (S.X₂.obj ⟶ M.shiftObj j) ≃ₗ[k]
      (S.X₁.obj ⟶ M.shiftObj j) × (S.X₃.obj ⟶ M.shiftObj j) :=
    (Linear.homCongr k hsplit.isoBinaryBiproduct (Iso.refl _)).trans
      (homBiprodLinearEquiv k (M.shiftObj j) S.X₁.obj S.X₃.obj)
  exact (gradedDimension_equiv _ eHom).trans (gradedDimension_prod _ _)

/-- Shifting a finite graded projective by `1` multiplies its graded Hom dimension into shifts of
`M` by `q`. -/
private theorem homShiftGradedDimension_shift (M : GradedModuleCat.{uA} 𝒜) [Module.Finite k M]
    (Q : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) :
    gradedDimension k
        (fun j => ((gradedFiniteProjectiveModulesExactStructure 𝒜).shift.functor.obj Q).obj ⟶
          M.shiftObj j)
        (GradedModuleCat.hasFiniteLaurentSupport_hom_shiftObj _ M) =
      laurentTAut ℤ (LaurentPolynomial ℤ)
        (gradedDimension k (fun j => Q.obj ⟶ M.shiftObj j)
          (GradedModuleCat.hasFiniteLaurentSupport_hom_shiftObj Q.obj M)) := by
  let eShift (j : ℤ) :
      (((gradedFiniteProjectiveModulesExactStructure 𝒜).shift.functor.obj Q).obj ⟶
        M.shiftObj j) ≃ₗ[k] (Q.obj ⟶ M.shiftObj (j + (-1))) :=
    (Linear.homCongr k
        ((gradedFiniteProjectiveModulesExactStructureShiftFunctorCompιIso (𝒜 := 𝒜)).app Q)
        (eqToIso (congrArg M.shiftObj (by omega : j = (j + -1) + 1)) ≪≫
          ((GradedModuleCat.shiftFunctorAddIso 𝒜 (j + -1) 1).app M).symm)).trans
      ((GradedModuleCat.shift 𝒜).functor.homLinearEquiv k Q.obj (M.shiftObj (j + -1))).symm
  rw [laurentTAut_apply, smul_eq_mul, gradedDimension_equiv _ eShift,
    gradedDimension_congr _
      ((GradedModuleCat.hasFiniteLaurentSupport_hom_shiftObj Q.obj M).reindex_add (-1))
      (fun _ => rfl),
    gradedDimension_reindex_add (GradedModuleCat.hasFiniteLaurentSupport_hom_shiftObj Q.obj M)
      (-1),
    neg_neg]

/-- For a finite-dimensional graded module `M`, the graded Hom dimension `∑ⱼ dim_k Hom(P, M{j}) qʲ`
is a shift-equivariant additive invariant on finite graded projectives. Modelled on
`smulGradedDimensionInvariant` in `CartanMap/Idempotent/Coordinate.lean`. -/
private def homShiftGradedDimensionInvariant (M : GradedModuleCat.{uA} 𝒜) [Module.Finite k M] :
    (gradedFiniteProjectiveModulesExactStructure 𝒜).ShiftInvariant
      (laurentTAut ℤ (LaurentPolynomial ℤ)) where
  obj Q := gradedDimension k (fun j => Q.obj ⟶ M.shiftObj j)
    (GradedModuleCat.hasFiniteLaurentSupport_hom_shiftObj Q.obj M)
  map_conflation {_} hS := homShiftGradedDimension_conflation M hS
  map_shift Q := homShiftGradedDimension_shift M Q

/-- **The graded Hom-dimension coordinate** on `K₀^gr(proj A)` for a finite-dimensional graded
module `M`: the `ℤ[q,q⁻¹]`-linear map sending `[P]` to `∑ⱼ dim_k Hom(P, M{j}) qʲ`. Needs neither
finite-dimensionality of `A` nor `HasExt`. -/
def gradedHomShiftCoordinate (M : GradedModuleCat.{uA} 𝒜) [Module.Finite k M] :
    LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜) →ₗ[LaurentPolynomial ℤ]
      LaurentPolynomial ℤ :=
  LaurentK0.lift.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
    (homShiftGradedDimensionInvariant M)

/-- On the class of a finite graded projective `P`, `gradedHomShiftCoordinate M` is the graded
dimension of `j ↦ Hom(P, M{j})`. -/
@[simp]
theorem gradedHomShiftCoordinate_of (M : GradedModuleCat.{uA} 𝒜) [Module.Finite k M]
    (P : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) :
    gradedHomShiftCoordinate M (LaurentK0.of.{uA} _ P) =
      gradedDimension k (fun j => P.obj ⟶ M.shiftObj j)
        (GradedModuleCat.hasFiniteLaurentSupport_hom_shiftObj P.obj M) :=
  LaurentK0.lift_of.{uA} (homShiftGradedDimensionInvariant M) P

/-- On the class `[A f]` of a degree-zero idempotent `f`, `gradedHomShiftCoordinate M` evaluates
to the conjugate idempotent graded dimension `bar(gdim(f • M))`. -/
@[simp↓]
theorem gradedHomShiftCoordinate_gradedIdempotentProjective (M : GradedModuleCat.{uA} 𝒜)
    [Module.Finite k M] {f : A} (hf : IsIdempotentElem f) (hf₀ : f ∈ 𝒜 0) :
    gradedHomShiftCoordinate M
        (LaurentK0.of.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)
          (gradedIdempotentProjective hf hf₀)) =
      invert (M.smulGradedDimension f) := by
  have hI := Ideal.isHomogeneous_span_singleton 𝒜 ⟨0, hf₀⟩
  rw [gradedIdempotentProjective_eq _ _ hI, gradedHomShiftCoordinate_of]
  ext p
  rw [coeff_gradedDimension, invert_apply,
    GradedModuleCat.finrank_hom_ofIdeal_span_singleton_shiftObj hf hf₀ hI]

section Basis

variable {I : Type uI} {e : I → A} (he : ∀ i, IsIdempotentElem (e i)) (he₀ : ∀ i, e i ∈ 𝒜 0)
  (bP : Module.Basis I (LaurentPolynomial ℤ)
    (LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)))
  (hbP : ∀ i, bP i = LaurentK0.of.{uA} _
    (gradedIdempotentProjective (he i) (he₀ i)))

include hbP in
/-- **Evaluating `gradedHomShiftCoordinate M` in an idempotent projective basis.** For a
finite-dimensional graded module `M` with `gdim(eⱼ • M) = 0` for every `j ≠ i`, the functional
`gradedHomShiftCoordinate M` equals `bar(gdim(eᵢ • M))` times the `i`th coordinate in `bP`. -/
theorem gradedHomShiftCoordinate_eq_mul_repr
    (M : GradedModuleCat.{uA} 𝒜) [Module.Finite k M] (i : I)
    (hne : ∀ j, j ≠ i → M.smulGradedDimension (e j) = 0)
    (x : LaurentK0.{uA} (gradedFiniteProjectiveModulesExactStructure 𝒜)) :
    gradedHomShiftCoordinate M x = invert (M.smulGradedDimension (e i)) * bP.repr x i := by
  classical
  have hmap : gradedHomShiftCoordinate M =
      invert (M.smulGradedDimension (e i)) • bP.coord i := by
    refine bP.ext fun j => ?_
    rw [LinearMap.smul_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply, smul_eq_mul, hbP j,
      gradedHomShiftCoordinate_gradedIdempotentProjective M (he j) (he₀ j)]
    split_ifs with hij
    · subst hij
      rw [mul_one]
    · rw [hne j hij, map_zero, mul_zero]
  exact LinearMap.congr_fun hmap x

include hbP in
/-- **Graded Hom dimensions recover projective coordinates.** For a finite graded projective `P`
and a finite-dimensional graded module `M` with `gdim(eⱼ • M) = 0` for every `j ≠ i`, the graded
dimension `∑ⱼ dim_k Hom(P, M{j}) qʲ` equals `bar(gdim(eᵢ • M)) · [P]ᵢ`. -/
theorem gradedDimension_hom_shiftObj_eq_mul_repr
    (P : (gradedFiniteProjectiveModules 𝒜).FullSubcategory)
    (M : GradedModuleCat.{uA} 𝒜) [Module.Finite k M] (i : I)
    (hne : ∀ j, j ≠ i → M.smulGradedDimension (e j) = 0) :
    gradedDimension k (fun j => P.obj ⟶ M.shiftObj j)
        (GradedModuleCat.hasFiniteLaurentSupport_hom_shiftObj P.obj M) =
      invert (M.smulGradedDimension (e i)) * bP.repr (LaurentK0.of.{uA} _ P) i := by
  rw [← gradedHomShiftCoordinate_of,
    gradedHomShiftCoordinate_eq_mul_repr he he₀ bP hbP M i hne]

include hbP in
/-- **Projective coordinates count maps to shifted targets.** For a finite graded projective `P`
with `i`th projective coordinate `xᵢ`, and a finite-dimensional graded module `M` with
`gdim(eⱼ • M) = 0` for every `j ≠ i`, the coefficient of `qʲ` in `bar(gdim(eᵢ • M)) · xᵢ` is
`dim_k Hom(P, M{j})`. Neither finite-dimensionality of `A` nor a single generation degree on `P`
is assumed. -/
theorem coeff_invert_smulGradedDimension_mul_repr
    (P : (gradedFiniteProjectiveModules 𝒜).FullSubcategory)
    (M : GradedModuleCat.{uA} 𝒜) [Module.Finite k M] (i : I)
    (hne : ∀ j, j ≠ i → M.smulGradedDimension (e j) = 0) (j : ℤ) :
    (invert (M.smulGradedDimension (e i)) * bP.repr (LaurentK0.of.{uA} _ P) i).coeff j =
      Module.finrank k (P.obj ⟶ M.shiftObj j) := by
  rw [← gradedDimension_hom_shiftObj_eq_mul_repr he he₀ bP hbP P M i hne, coeff_gradedDimension]

include hbP in
/-- A degree-zero target detecting precisely `eᵢ` makes every coefficient of the `i`th
coordinate of a finite graded projective nonnegative. -/
theorem coeff_repr_projective_nonneg
    (P : (gradedFiniteProjectiveModules 𝒜).FullSubcategory)
    (N : GradedModuleCat.{uA} 𝒜) [Module.Finite k N]
    (hconc : ∀ p, p ≠ 0 → N.grading.piece p = ⊥) (i : I)
    (hne : ∀ j, j ≠ i → N.smulGradedDimension (e j) = 0)
    (hself : N.smulGradedDimension (e i) ≠ 0) (j : ℤ) :
    0 ≤ (bP.repr (LaurentK0.of.{uA} _ P) i).coeff j := by
  have hcoeff := coeff_invert_smulGradedDimension_mul_repr he he₀ bP hbP P N i hne j
  rw [GradedModuleCat.smulGradedDimension_eq_C_of_concentrated _ _ hconc, invert_C,
    coeff_C_mul] at hcoeff
  exact nonneg_of_mul_nonneg_right (hcoeff ▸ Int.natCast_nonneg _)
    (Int.natCast_pos.mpr (N.finrank_smul_piece_zero_pos_of_concentrated (e i) hconc hself))

include hbP in
/-- For a finite graded projective `P` generated in degree `d` and a finite-dimensional degree-zero
target `M` annihilated by every `eⱼ` with `j ≠ i`, the weighted projective coordinate
`gdim(eᵢ • M) · [P]ᵢ` is supported in degree `d` (and may vanish); the coordinate `[P]ᵢ` itself is
supported in degree `d` when `gdim(eᵢ • M) ≠ 0`. -/
theorem smulGradedDimension_mul_repr_of_isGeneratedInDegree
    (P : (gradedFiniteProjectiveModules 𝒜).FullSubcategory) {d : ℤ}
    (hP : P.obj.grading.IsGeneratedInDegree A d)
    (M : GradedModuleCat.{uA} 𝒜) [Module.Finite k M]
    (hconc : ∀ p, p ≠ 0 → M.grading.piece p = ⊥) (i : I)
    (hne : ∀ j, j ≠ i → M.smulGradedDimension (e j) = 0) :
    M.smulGradedDimension (e i) * bP.repr (LaurentK0.of.{uA} _ P) i =
      C (Module.finrank k (P.obj ⟶ M.shiftObj d) : ℤ) * T d := by
  rw [← GradedModuleCat.invert_smulGradedDimension_of_concentrated (e i) M hconc,
    ← gradedDimension_hom_shiftObj_eq_mul_repr he he₀ bP hbP P M i hne,
    gradedDimension_eq_sum _ {d}, Finset.sum_singleton]
  intro j hj
  exact GradedModuleCat.subsingleton_hom_shiftObj_of_isGeneratedInDegree hP hconc
    (Finset.mem_singleton.not.mp hj)

end Basis

end TauCeti
