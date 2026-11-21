/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Concentrated
public import TauCeti.Algebra.Category.GradedModuleCat.Free
public import TauCeti.Algebra.Category.GradedModuleCat.Idempotent.Head
public import TauCeti.Algebra.Category.GradedModuleCat.LinearResolution.Basic
public import TauCeti.Algebra.Category.GradedModuleCat.MinimalResolution
public import TauCeti.Algebra.Module.GradedModule.Polynomial

/-!
# Graded resolutions of truncated polynomial modules

Let `k` be a commutative ring and grade the polynomial ring `A = k[x]` with `x` in degree one
(`TauCeti.Polynomial.degreeGrade`). For `m : ℕ`, the truncated polynomial module
`M = k[x]/(x^m)` is the cokernel of the graded map `A{m} ⟶ A{0}` multiplying by `x^m`. Since
`x^m` is a nonzerodivisor,

```text
0 ⟶ A{m} --x^m--> A{0} ⟶ M ⟶ 0
```

is a graded projective resolution of `M`. For `m > 0` its differential takes values in
`A₊ = (x)`, so the resolution is minimal. Its first term is generated in internal degree `m`,
so it is linear exactly when `m = 1`, where it is the Koszul resolution of the residue field.

Against a graded module `N` annihilated by `A₊`, the minimal resolution computes Ext:
`Ext⁰(M, N) = N₀`, `Ext¹(M, N) = Nₘ`, and every higher Ext vanishes for every target. For the
residue field `S = A/A₊` over a field `k` this gives

```text
dim_k Extⁿ(M, S{j}) = 1 if (n, j) = (0, 0) or (n, j) = (1, m), and 0 otherwise.
```

For `m ≥ 2` the module `M` is cyclic, generated in degree zero, yet `Ext¹(M, S{m})` is nonzero
off the diagonal `j = n`, so `M` has no linear graded projective resolution at all. This is the
example separating minimal from linear resolutions: for every `m > 0` the Ext dimensions against
the shifts of `S` are nonzero in exactly two bidegrees, and only the internal degree `m` of the
class in `Ext¹` tells the linear case `m = 1` apart.

## Main definitions

* `TauCeti.polynomialGradedXPowMul`: multiplication by `x^m` as a graded map `A{m} ⟶ A{0}`.
* `TauCeti.gradedTruncatedPolynomial`: the graded module `k[x]/(x^m)`.
* `TauCeti.gradedTruncatedPolynomialResolution`: its two-term graded projective resolution.
* `TauCeti.polynomialGradedResidue`: the graded residue field `S = A/A₊`.
* `TauCeti.extGradedTruncatedPolynomialZeroEquiv` and
  `TauCeti.extGradedTruncatedPolynomialOneEquiv`: `Ext⁰(M, N) ≃ N₀` and `Ext¹(M, N) ≃ Nₘ` for
  targets annihilated by `A₊`.

## Main results

* `TauCeti.cokernelπ_polynomialGradedXPowMul_apply_eq_zero_iff`: the kernel of the projection
  `A ⟶ k[x]/(x^m)` is the ideal `(x^m)`.
* `TauCeti.isMinimal_gradedTruncatedPolynomialResolution`: for `m > 0` the resolution is
  minimal.
* `TauCeti.isLinear_gradedTruncatedPolynomialResolution_iff`: it is linear exactly when `m = 1`.
* `TauCeti.subsingleton_ext_gradedTruncatedPolynomial_add_two`: `M` has no Ext above degree one.
* `TauCeti.finrank_ext_gradedTruncatedPolynomial_polynomialGradedResidue_shiftObj`: the
  dimensions of `Extⁿ(M, S{j})` over a field.
* `TauCeti.not_exists_isLinear_gradedTruncatedPolynomial`: for `m ≥ 2`, `M` has no linear graded
  projective resolution.

## References

* A. Beilinson, V. Ginzburg and W. Soergel, "Koszul duality patterns in representation theory",
  *Journal of the AMS* 9 (1996), Section 1.2, for linear resolutions and for computing Ext from
  minimal graded resolutions.
* Charles A. Weibel, *An Introduction to Homological Algebra*, Cambridge Studies in Advanced
  Mathematics 38, Cambridge University Press (1994), Section 2.4, for computing Ext from
  projective resolutions.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian _root_.Polynomial

universe w u

section CommRing

variable (k : Type u) [CommRing k] (m : ℕ)

/-- **Multiplication by `x^m`** as the morphism of graded modules `A{m} ⟶ A{0}` over the
graded polynomial ring `A = k[x]`, sending `a` to `a x^m`. -/
def polynomialGradedXPowMul :
    (GradedModuleCat.regular (𝒜 := Polynomial.degreeGrade k)).shiftObj m ⟶
      (GradedModuleCat.regular (𝒜 := Polynomial.degreeGrade k)).shiftObj 0 :=
  GradedModuleCat.ofHom (LinearMap.toSpanSingleton k[X] k[X] (X ^ m)) <|
    LinearMap.isHomogeneous_def.2 fun p x hx ↦ by
      have hx' : x ∈ Polynomial.degreeGrade k (p - m) := by simpa [sub_eq_add_neg] using hx
      simpa using SetLike.GradedMul.mul_mem hx' (Polynomial.X_pow_mem_degreeGrade (k := k) m)

/-- Multiplication by `x^m` sends `a` to `a x^m`. -/
@[simp]
theorem polynomialGradedXPowMul_hom_apply (a : k[X]) :
    (polynomialGradedXPowMul k m).hom a = a * X ^ m := by
  rw [polynomialGradedXPowMul, GradedModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply,
    smul_eq_mul]

/-- Multiplication by `x^m` is injective, since `x^m` is a nonzerodivisor. -/
theorem polynomialGradedXPowMul_hom_injective :
    Function.Injective (polynomialGradedXPowMul k m).hom :=
  fun a b h ↦ (isRegular_X_pow m).right (by
    rwa [polynomialGradedXPowMul_hom_apply, polynomialGradedXPowMul_hom_apply] at h)

/-- **The graded truncated polynomial module** `k[x]/(x^m)`: the cokernel of multiplication by
`x^m` on the graded polynomial ring, with the grading induced from `k[x]`. -/
abbrev gradedTruncatedPolynomial : GradedModuleCat.{u} (Polynomial.degreeGrade k) :=
  GradedModuleCat.cokernelObj (polynomialGradedXPowMul k m)

/-- **The kernel of `k[x] ⟶ k[x]/(x^m)` is the ideal `(x^m)`.** -/
theorem cokernelπ_polynomialGradedXPowMul_apply_eq_zero_iff (a : k[X]) :
    (GradedModuleCat.cokernelπ (polynomialGradedXPowMul k m)).hom a = 0 ↔ X ^ m ∣ a := by
  rw [GradedModuleCat.cokernelπ, GradedModuleCat.hom_ofHom, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  refine ⟨fun ⟨b, hb⟩ ↦ ⟨b, ?_⟩, fun ⟨b, hb⟩ ↦ ⟨b, ?_⟩⟩
  · rw [← hb, polynomialGradedXPowMul_hom_apply, mul_comm]
  · rw [hb, polynomialGradedXPowMul_hom_apply, mul_comm]

/-- The terms `A{0}, A{m}, 0, 0, …` of the resolution of `k[x]/(x^m)`. -/
private abbrev resolutionTerm : ℕ → GradedModuleCat.{u} (Polynomial.degreeGrade k)
  | 0 => (GradedModuleCat.regular (𝒜 := Polynomial.degreeGrade k)).shiftObj 0
  | 1 => (GradedModuleCat.regular (𝒜 := Polynomial.degreeGrade k)).shiftObj m
  | _ + 2 => GradedModuleCat.directSumObj fun _ : Fin 0 =>
      GradedModuleCat.regular (𝒜 := Polynomial.degreeGrade k)

/-- The differentials of the resolution of `k[x]/(x^m)`: multiplication by `x^m`, then zero. -/
private def resolutionDifferential :
    ∀ n : ℕ, resolutionTerm k m (n + 1) ⟶ resolutionTerm k m n
  | 0 => polynomialGradedXPowMul k m
  | _ + 1 => 0

private theorem resolutionDifferential_zero :
    resolutionDifferential k m 0 = polynomialGradedXPowMul k m :=
  (rfl)

private theorem resolutionDifferential_succ (n : ℕ) : resolutionDifferential k m (n + 1) = 0 :=
  (rfl)

private instance (n : ℕ) : Subsingleton (resolutionTerm k m (n + 2)) :=
  inferInstanceAs (Subsingleton (DirectSum (Fin 0) fun _ ↦ k[X]))

/-- **The graded projective resolution `0 ⟶ A{m} ⟶ A{0} ⟶ k[x]/(x^m)`** of the truncated
polynomial module. Its first differential is multiplication by `x^m`
(`TauCeti.gradedTruncatedPolynomialResolution_differential_zero`), its augmentation is the
projection (`TauCeti.gradedTruncatedPolynomialResolution_augmentation`), and its terms vanish
from homological degree two on. -/
def gradedTruncatedPolynomialResolution :
    GradedProjectiveResolution.{u, u, u, u} (Polynomial.degreeGrade k)
      (gradedTruncatedPolynomial k m).grading where
  X n := resolutionTerm k m n
  grading n := (resolutionTerm k m n).grading
  projective n := by
    rcases n with _ | _ | n
    · exact inferInstanceAs (Module.Projective k[X] k[X])
    · exact inferInstanceAs (Module.Projective k[X] k[X])
    · exact inferInstanceAs (Module.Projective k[X] (DirectSum (Fin 0) fun _ ↦ k[X]))
  d n := (resolutionDifferential k m n).hom
  π := (GradedModuleCat.cokernelπ (polynomialGradedXPowMul k m)).hom
  isHomogeneous_d n := (resolutionDifferential k m n).isHomogeneous
  isHomogeneous_π := (GradedModuleCat.cokernelπ (polynomialGradedXPowMul k m)).isHomogeneous
  surjective_π := Submodule.mkQ_surjective _
  exact_d_π := LinearMap.exact_iff.2 (Submodule.ker_mkQ _)
  exact_d_d n := by
    rcases n with _ | n
    · -- `A{m} ⟶ A{0}` is injective and its source receives the zero map from the zero term
      refine LinearMap.exact_iff.2 ?_
      rw [resolutionDifferential_zero, resolutionDifferential_succ, GradedModuleCat.hom_zero,
        LinearMap.ker_eq_bot.2 (polynomialGradedXPowMul_hom_injective k m), LinearMap.range_zero]
    · -- both maps start at a zero term
      exact LinearMap.exact_iff.2 (Subsingleton.elim _ _)

/-- The term of the resolution in homological degree zero is `A{0}`. -/
theorem gradedTruncatedPolynomialResolution_termObj_zero :
    (gradedTruncatedPolynomialResolution k m).termObj 0 =
      (GradedModuleCat.regular (𝒜 := Polynomial.degreeGrade k)).shiftObj 0 :=
  (rfl)

/-- The term of the resolution in homological degree one is `A{m}`. -/
theorem gradedTruncatedPolynomialResolution_termObj_one :
    (gradedTruncatedPolynomialResolution k m).termObj 1 =
      (GradedModuleCat.regular (𝒜 := Polynomial.degreeGrade k)).shiftObj m :=
  (rfl)

/-- The terms of the resolution vanish from homological degree two on. -/
instance (n : ℕ) : Subsingleton ((gradedTruncatedPolynomialResolution k m).X (n + 2)) :=
  inferInstanceAs (Subsingleton (resolutionTerm k m (n + 2)))

/-- The first differential of the resolution, read through
`TauCeti.gradedTruncatedPolynomialResolution_termObj_one` and
`TauCeti.gradedTruncatedPolynomialResolution_termObj_zero`, is multiplication by `x^m`. -/
theorem gradedTruncatedPolynomialResolution_differential_zero :
    eqToHom (gradedTruncatedPolynomialResolution_termObj_one k m).symm ≫
        (gradedTruncatedPolynomialResolution k m).differential 0 ≫
          eqToHom (gradedTruncatedPolynomialResolution_termObj_zero k m) =
      polynomialGradedXPowMul k m := by
  -- both transports are identities, and the differential is multiplication by `x^m`
  exact GradedModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl)

/-- The augmentation of the resolution, read through
`TauCeti.gradedTruncatedPolynomialResolution_termObj_zero`, is the projection onto the
cokernel. -/
theorem gradedTruncatedPolynomialResolution_augmentation :
    eqToHom (gradedTruncatedPolynomialResolution_termObj_zero k m).symm ≫
        (gradedTruncatedPolynomialResolution k m).augmentation =
      GradedModuleCat.cokernelπ (polynomialGradedXPowMul k m) := by
  -- the transport is an identity, and the augmentation is the projection
  exact GradedModuleCat.hom_ext (LinearMap.ext fun _ ↦ rfl)

/-- **For `m > 0` the resolution of `k[x]/(x^m)` is minimal**: its only nonzero differential is
multiplication by `x^m`, which has positive degree. -/
theorem isMinimal_gradedTruncatedPolynomialResolution (hm : 0 < m) :
    (gradedTruncatedPolynomialResolution k m).IsMinimal := by
  refine GradedProjectiveResolution.isMinimal_iff.2 fun n x ↦ ?_
  rcases n with _ | n
  · have hd : (gradedTruncatedPolynomialResolution k m).d 0 x = (X ^ m : k[X]) • x :=
      (polynomialGradedXPowMul_hom_apply k m x).trans (mul_comm _ _)
    rw [hd]
    exact Submodule.smul_mem_smul
      (Submodule.mem_iSup_of_mem (m : ℤ) (Submodule.mem_iSup_of_mem (by exact_mod_cast hm)
        (Polynomial.X_pow_mem_degreeGrade m))) Submodule.mem_top
  · rw [Subsingleton.elim (α := (gradedTruncatedPolynomialResolution k m).X (n + 2)) x 0,
      map_zero]
    exact Submodule.zero_mem _

/-- **The resolution of `k[x]/(x^m)` is linear exactly when `m = 1`**, over a nontrivial ring.
For `m = 1` it is the Koszul resolution `0 ⟶ A{1} ⟶ A ⟶ k ⟶ 0` of the residue field; otherwise
its first term `A{m}` is not generated in degree one. -/
theorem isLinear_gradedTruncatedPolynomialResolution_iff [Nontrivial k] :
    (gradedTruncatedPolynomialResolution k m).IsLinear ↔ m = 1 := by
  rw [GradedProjectiveResolution.isLinear_iff]
  constructor
  · intro hr
    -- the first term is `A{m}`, generated in degree `1` only if `m = 1`
    have h1 : InternalGrading.IsGeneratedInDegree
        ((GradedModuleCat.regular (𝒜 := Polynomial.degreeGrade k)).shiftObj m).grading k[X]
        ((1 : ℕ) : ℤ) := hr 1
    have := (GradedModuleCat.isGeneratedInDegree_regular_shiftObj_iff
      (fun _ h ↦ Polynomial.degreeGrade_eq_bot_of_neg (k := k) h) _ _).1 h1
    exact_mod_cast this.symm
  · rintro rfl n
    rcases n with _ | _ | n
    · exact GradedModuleCat.isGeneratedInDegree_regular_shiftObj 0
    · exact GradedModuleCat.isGeneratedInDegree_regular_shiftObj 1
    · exact InternalGrading.isGeneratedInDegree_of_piece_eq_top _ _ (Subsingleton.elim _ _)

/-! ### The graded residue field -/

/-- **The graded residue field `S = k[x]/(x)`**, concentrated in degree zero: the graded head
`A / A₊` of the regular module `A`. -/
abbrev polynomialGradedResidue : GradedModuleCat.{u} (Polynomial.degreeGrade k) :=
  gradedPositiveMulQuotient (Polynomial.degreeGrade k)
    (SetLike.one_mem_graded (Polynomial.degreeGrade k))

/-- The graded residue field vanishes outside degree zero. -/
theorem polynomialGradedResidue_piece_eq_bot {p : ℤ} (hp : p ≠ 0) :
    (polynomialGradedResidue k).grading.piece p = ⊥ :=
  gradedPositiveMulQuotient_piece_eq_bot (fun _ ↦ Polynomial.degreeGrade_eq_bot_of_neg)
    IsIdempotentElem.one _ hp

/-- Positive-degree polynomials annihilate every internal shift of the graded residue field. -/
theorem positive_smul_top_shiftObj_polynomialGradedResidue_eq_bot (j : ℤ) :
    (⨆ (i : ℤ) (_ : 0 < i), Polynomial.degreeGrade k i) •
      (⊤ : Submodule k ((polynomialGradedResidue k).shiftObj j)) = ⊥ :=
  GradedModuleCat.positive_smul_top_eq_bot_of_concentrated _ j fun q hq ↦ by
    simpa [sub_eq_add_neg] using
      polynomialGradedResidue_piece_eq_bot k (p := q - j) (sub_ne_zero.2 hq)

/-- The graded residue field is nonzero over a nontrivial ring. -/
instance [Nontrivial k] : Nontrivial (polynomialGradedResidue k) :=
  (gradeZeroEquivGradedPositiveMulQuotientOne (𝒜 := Polynomial.degreeGrade k)
    (fun _ h ↦ Polynomial.degreeGrade_eq_bot_of_neg h)).symm.toEquiv.nontrivial

/-! ### Ext from the minimal resolution -/

section Ext

variable [HasExt.{w} (GradedModuleCat.{u} (Polynomial.degreeGrade k))]

/-- **`k[x]/(x^m)` has no Ext above degree one**, against every target: its resolution has
length one. -/
theorem subsingleton_ext_gradedTruncatedPolynomial_add_two
    (N : GradedModuleCat.{u} (Polynomial.degreeGrade k)) (n : ℕ) :
    Subsingleton (Ext.{w} (gradedTruncatedPolynomial k m) N (n + 2)) := by
  let r := gradedTruncatedPolynomialResolution k m
  have : Subsingleton (r.termObj (n + 2) ⟶ N) :=
    ⟨fun f g ↦ GradedModuleCat.hom_ext (LinearMap.ext fun x ↦ by
      rw [Subsingleton.elim x 0, map_zero, map_zero])⟩
  have : Subsingleton (r.toProjectiveResolution.complex.X (n + 2) ⟶ N) :=
    ((r.toProjectiveResolutionXIso (n + 2)).homCongr (Iso.refl N)).injective.subsingleton
  exact r.toProjectiveResolution.subsingleton_ext_of_subsingleton_hom (n + 2)

variable {k m} (hm : 0 < m) {N : GradedModuleCat.{u} (Polynomial.degreeGrade k)}
  (hN : (⨆ (i : ℤ) (_ : 0 < i), Polynomial.degreeGrade k i) • (⊤ : Submodule k N) = ⊥)

/-- **`Ext⁰(k[x]/(x^m), N)` is the degree-zero piece of `N`**, for `m > 0` and a target `N`
annihilated by positive-degree polynomials: graded maps out of `k[x]/(x^m)` into such a target
are determined by the image of `1`. -/
def extGradedTruncatedPolynomialZeroEquiv :
    Ext.{w} (gradedTruncatedPolynomial k m) N 0 ≃ₗ[k] N.grading.piece 0 :=
  ((isMinimal_gradedTruncatedPolynomialResolution k m hm).extLinearEquiv hN 0).symm ≪≫ₗ
    GradedModuleCat.regularShiftHomEquiv N 0

/-- The inverse of `TauCeti.extGradedTruncatedPolynomialZeroEquiv` sends `y ∈ N₀` to the class,
computed by the minimal resolution, of the graded map `A{0} ⟶ N` sending `1` to `y`. -/
theorem extGradedTruncatedPolynomialZeroEquiv_symm_apply (y : N.grading.piece 0) :
    (extGradedTruncatedPolynomialZeroEquiv hm hN).symm y =
      (isMinimal_gradedTruncatedPolynomialResolution k m hm).extLinearEquiv hN 0
        (eqToHom (gradedTruncatedPolynomialResolution_termObj_zero k m) ≫
          (GradedModuleCat.regularShiftHomEquiv N 0).symm y) :=
  (rfl)

/-- **`Ext¹(k[x]/(x^m), N)` is the degree-`m` piece of `N`**, for `m > 0` and a target `N`
annihilated by positive-degree polynomials: the minimal resolution identifies it with graded
maps `A{m} ⟶ N`. -/
def extGradedTruncatedPolynomialOneEquiv :
    Ext.{w} (gradedTruncatedPolynomial k m) N 1 ≃ₗ[k] N.grading.piece m :=
  ((isMinimal_gradedTruncatedPolynomialResolution k m hm).extLinearEquiv hN 1).symm ≪≫ₗ
    GradedModuleCat.regularShiftHomEquiv N m

/-- The inverse of `TauCeti.extGradedTruncatedPolynomialOneEquiv` sends `y ∈ Nₘ` to the class,
computed by the minimal resolution, of the graded map `A{m} ⟶ N` sending `1` to `y`. -/
theorem extGradedTruncatedPolynomialOneEquiv_symm_apply (y : N.grading.piece m) :
    (extGradedTruncatedPolynomialOneEquiv hm hN).symm y =
      (isMinimal_gradedTruncatedPolynomialResolution k m hm).extLinearEquiv hN 1
        (eqToHom (gradedTruncatedPolynomialResolution_termObj_one k m) ≫
          (GradedModuleCat.regularShiftHomEquiv N m).symm y) :=
  (rfl)

end Ext

end CommRing

/-! ### Over a field -/

section Field

variable (k : Type u) [Field k] (m : ℕ)

/-- **The graded residue field is one-dimensional, concentrated in degree zero.** -/
theorem finrank_polynomialGradedResidue_piece (p : ℤ) :
    Module.finrank k ((polynomialGradedResidue k).grading.piece p) = if p = 0 then 1 else 0 := by
  split_ifs with hp
  · subst hp
    rw [gradedPositiveMulQuotient_piece_zero_eq_top
        (fun _ ↦ Polynomial.degreeGrade_eq_bot_of_neg) IsIdempotentElem.one, finrank_top]
    exact finrank_gradedIdempotentHead (I := Unit) (e := fun _ ↦ (1 : k[X]))
      (fun _ ↦ Polynomial.degreeGrade_eq_bot_of_neg)
      (CompleteOrthogonalIdempotents.unique_iff.2 rfl).toOrthogonalIdempotents
      (fun _ ↦ SetLike.one_mem_graded (Polynomial.degreeGrade k))
      (by rw [Set.range_const, Polynomial.degreeGrade_zero_eq_span_one]) () one_ne_zero
  · rw [polynomialGradedResidue_piece_eq_bot k hp, finrank_bot]

variable [HasExt.{w} (GradedModuleCat.{u} (Polynomial.degreeGrade k))]

/-- **`dim_k Extⁿ(k[x]/(x^m), S{j})` is `1` for `(n, j) = (0, 0)` and `(n, j) = (1, m)`, and `0`
otherwise**, for `m > 0` and the graded residue field `S`. The class in degree one sits in internal
degree `m`, off the diagonal `j = n` unless `m = 1`. -/
theorem finrank_ext_gradedTruncatedPolynomial_polynomialGradedResidue_shiftObj (hm : 0 < m)
    (n : ℕ) (j : ℤ) :
    Module.finrank k
        (Ext.{w} (gradedTruncatedPolynomial k m) ((polynomialGradedResidue k).shiftObj j) n) =
      if (n = 0 ∧ j = 0) ∨ (n = 1 ∧ j = m) then 1 else 0 := by
  have hN := positive_smul_top_shiftObj_polynomialGradedResidue_eq_bot k j
  have hpiece (d : ℤ) : ((polynomialGradedResidue k).shiftObj j).grading.piece d =
      (polynomialGradedResidue k).grading.piece (d - j) :=
    Submodule.ext fun x ↦ GradedModuleCat.mem_shiftObj_piece_iff (polynomialGradedResidue k) j d x
  rcases n with _ | _ | n
  · rw [(extGradedTruncatedPolynomialZeroEquiv hm hN).finrank_eq, hpiece,
      finrank_polynomialGradedResidue_piece]
    exact if_congr (by omega) rfl rfl
  · rw [(extGradedTruncatedPolynomialOneEquiv hm hN).finrank_eq, hpiece,
      finrank_polynomialGradedResidue_piece]
    exact if_congr (by omega) rfl rfl
  · have := subsingleton_ext_gradedTruncatedPolynomial_add_two.{w} k m
      ((polynomialGradedResidue k).shiftObj j) n
    rw [Module.finrank_zero_of_subsingleton]
    simp

end Field

/-- **For `m ≥ 2`, the module `k[x]/(x^m)` has no linear graded projective resolution**, over a
nontrivial ring, although it is generated in degree zero: a linear resolution would force
`Ext¹(k[x]/(x^m), S{m})` to vanish, while it is the degree-zero piece of the residue field `S`. -/
theorem not_exists_isLinear_gradedTruncatedPolynomial (k : Type u) [CommRing k] [Nontrivial k]
    {m : ℕ} (hm : 2 ≤ m) :
    ¬ ∃ r : GradedProjectiveResolution.{u, u, u, u} (Polynomial.degreeGrade k)
      (gradedTruncatedPolynomial k m).grading, r.IsLinear := by
  rintro ⟨r, hr⟩
  let := HasExt.standard (GradedModuleCat.{u} (Polynomial.degreeGrade k))
  have hN := positive_smul_top_shiftObj_polynomialGradedResidue_eq_bot k m
  have hsub := hr.subsingleton_ext_shiftObj_of_ne
    (fun _ hp ↦ polynomialGradedResidue_piece_eq_bot k hp) 1 (m : ℤ) (by omega)
  have htop : ((polynomialGradedResidue k).shiftObj m).grading.piece m = ⊤ := by
    simpa using gradedPositiveMulQuotient_piece_zero_eq_top
      (fun _ ↦ Polynomial.degreeGrade_eq_bot_of_neg) IsIdempotentElem.one
      (SetLike.one_mem_graded (Polynomial.degreeGrade k))
  have : Nontrivial (((polynomialGradedResidue k).shiftObj m).grading.piece m) := by
    rw [htop]
    exact (Submodule.topEquiv).toEquiv.nontrivial
  exact not_subsingleton _
    ((extGradedTruncatedPolynomialOneEquiv (m := m) (by omega) hN).toEquiv.symm.subsingleton)

end TauCeti
