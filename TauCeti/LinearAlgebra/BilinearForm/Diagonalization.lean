/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.BilinearForm.Isometry
import TauCeti.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Diagonalization of symmetric bilinear forms in every characteristic

Over a field in which `2` is invertible, every symmetric bilinear form on a finite-dimensional
space has an orthogonal basis (`LinearMap.BilinForm.exists_orthogonal_basis`). In characteristic
two this fails: a nonzero alternating form is symmetric, and an orthogonal basis for it would make
every basis pairing vanish, hence the whole form. This file shows that the alternating forms are
the only obstruction, in every characteristic: a symmetric form has an orthogonal basis if and
only if it is zero or not alternating (`LinearMap.BilinForm.IsSymm.exists_orthogonal_basis_iff`).

For a nondegenerate form over a field in which every element is a square, for instance a finite
field of characteristic two (`isSquare_of_charTwo'`), the orthogonal basis can be rescaled: a
symmetric form that is not alternating has an **orthonormal basis**, one in which its matrix is
the identity (`LinearMap.BilinForm.IsSymm.exists_basis_toMatrix_eq_one`). Hence it is equivalent
to the standard form `Matrix.toBilin' 1`, which is itself such a form in every positive dimension
(`Matrix.isAlt_toBilin'_one_iff` in `TauCeti.LinearAlgebra.Matrix.BilinearForm`), and any two such
forms of the same dimension are equivalent. Together with the symplectic normal form of
`TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis` this gives the dichotomy for nondegenerate
forms that are alternating or symmetric: a symplectic basis when the form is alternating, an
orthonormal basis when it is not
(`LinearMap.BilinForm.Nondegenerate.exists_basis_toMatrix_eq_J_or_toMatrix_eq_one`). Over `𝔽₂`,
where every form that is alternating is symmetric, this classifies the nondegenerate symmetric
bilinear forms, which is the input to the normal forms of one-relator pro-`2` groups.

## Main results

* `LinearMap.BilinForm.IsSymm.exists_orthogonal_basis_of_isAlt_imp_eq_zero`: a symmetric form
  that is zero or not alternating has an orthogonal basis, in every characteristic.
* `LinearMap.BilinForm.IsSymm.exists_orthogonal_basis_iff`: this condition is also necessary.
* `LinearMap.BilinForm.IsSymm.exists_basis_toMatrix_eq_one`: over a field in which every element
  is a square, a nondegenerate symmetric form that is not alternating has an orthonormal basis.
* `LinearMap.BilinForm.IsSymm.equivalent_toBilin'_one`,
  `LinearMap.BilinForm.IsSymm.equivalent_of_finrank_eq`: such a form is equivalent to the standard
  form on `Fin n → K`, so any two of them of the same dimension are equivalent.
* `LinearMap.BilinForm.Nondegenerate.exists_basis_toMatrix_eq_J_or_toMatrix_eq_one`: the
  symplectic-or-orthonormal dichotomy.

## References

* A. A. Albert, *Symmetric and alternate matrices in an arbitrary field, I*, Trans. Amer. Math.
  Soc. 43 (1938), 386–436.
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)
open Module

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {B : BilinForm K V}

/-- If `x` is non-isotropic for a symmetric form `B` and the restriction of `B` to the orthogonal
complement of `x` is alternating and nonzero, then some non-isotropic vector has an orthogonal
complement on which `B` is not alternating: given `u, w` orthogonal to `x` with `B u w ≠ 0`, the
vector `x + u` works. -/
private theorem IsSymm.exists_apply_self_ne_zero_and_not_isAlt_restrict_orthogonal
    (hB : B.IsSymm) {x : V} (hx : B x x ≠ 0) (halt : (B.restrict (B.orthogonal (K ∙ x))).IsAlt)
    (hne : B.restrict (B.orthogonal (K ∙ x)) ≠ 0) :
    ∃ y, B y y ≠ 0 ∧ ¬ (B.restrict (B.orthogonal (K ∙ y))).IsAlt := by
  obtain ⟨u, w, huw⟩ : ∃ u w : B.orthogonal (K ∙ x), B u w ≠ 0 := by
    by_contra! h
    exact hne (LinearMap.ext fun u => LinearMap.ext fun w => by simpa using h u w)
  have hxu : B x u = 0 := (mem_orthogonal_span_singleton_iff B).1 u.2
  have hxw : B x w = 0 := (mem_orthogonal_span_singleton_iff B).1 w.2
  have huu : B u u = 0 := by simpa using halt u
  have hww : B w w = 0 := by simpa using halt w
  set z := x + u with hz
  have hzz : B z z = B x x := by simp [hz, hxu, hB.eq u x, huu]
  have hzw : B z w = B u w := by simp [hz, hxw]
  refine ⟨z, hzz ▸ hx, fun halt' => huw ?_⟩
  obtain ⟨c, hc⟩ : ∃ c, c * B z z = B z w := ⟨B z w / B z z, div_mul_cancel₀ _ (hzz ▸ hx)⟩
  have hw' : w - c • z ∈ B.orthogonal (K ∙ z) :=
    (mem_orthogonal_span_singleton_iff B).2 (by simp [hc])
  have h0 : B w w - c * B z w - c * (B z w - c * B z z) = 0 := by
    simpa [hB.eq w z] using halt' ⟨w - c • z, hw'⟩
  have hcb : c * B z w = 0 := by linear_combination -h0 + c * hc + hww
  rw [← hzw]
  rcases mul_eq_zero.1 hcb with hc0 | hb0
  · rw [← hc, hc0, zero_mul]
  · exact hb0

/-- A symmetric form that is not alternating has a non-isotropic vector `x` such that the
restriction of the form to the orthogonal complement of `x` is zero or not alternating. -/
private theorem IsSymm.exists_apply_self_ne_zero_and_restrict_orthogonal_isAlt_imp_eq_zero
    (hB : B.IsSymm) (h : ¬B.IsAlt) :
    ∃ x, B x x ≠ 0 ∧
      ((B.restrict (B.orthogonal (K ∙ x))).IsAlt → B.restrict (B.orthogonal (K ∙ x)) = 0) := by
  obtain ⟨x, hx⟩ : ∃ x, B x x ≠ 0 := by simpa [IsAlt, LinearMap.IsAlt] using h
  by_cases hW : (B.restrict (B.orthogonal (K ∙ x))).IsAlt ∧ B.restrict (B.orthogonal (K ∙ x)) ≠ 0
  · obtain ⟨y, hy, hy'⟩ :=
      hB.exists_apply_self_ne_zero_and_not_isAlt_restrict_orthogonal hx hW.1 hW.2
    exact ⟨y, hy, fun h' => (hy' h').elim⟩
  · exact ⟨x, hx, fun h' => not_not.1 (not_and.1 hW h')⟩

variable [FiniteDimensional K V]

/-- **A symmetric bilinear form that is zero or not alternating has an orthogonal basis**, in
every characteristic. Away from characteristic two the hypothesis is automatic for symmetric
forms (`TauCeti.BilinForm.eq_zero_of_isSymm_of_isAlt`), which recovers
`LinearMap.BilinForm.exists_orthogonal_basis`; in characteristic two it excludes exactly the
nonzero alternating forms. -/
theorem IsSymm.exists_orthogonal_basis_of_isAlt_imp_eq_zero (hB : B.IsSymm)
    (h : B.IsAlt → B = 0) : ∃ v : Basis (Fin (finrank K V)) K V, B.iIsOrtho v := by
  suffices ∀ d, finrank K V = d → ∃ v : Basis (Fin d) K V, B.iIsOrtho v from this _ rfl
  intro d hd
  induction d generalizing V with
  | zero => exact ⟨basisOfFinrankZero hd, fun i _ _ => i.elim0⟩
  | succ d ih =>
    obtain rfl | hB₀ := eq_or_ne B 0
    · exact ⟨finBasisOfFinrankEq K V hd, fun _ _ _ => rfl⟩
    obtain ⟨x, hx, hW⟩ :=
      hB.exists_apply_self_ne_zero_and_restrict_orthogonal_isAlt_imp_eq_zero
        fun halt => hB₀ (h halt)
    have hd' : finrank K (B.orthogonal (K ∙ x)) = d := by
      rw [← Submodule.finrank_add_eq_of_isCompl (isCompl_span_singleton_orthogonal hx).symm,
        finrank_span_singleton (ne_zero_of_not_isOrtho_self x hx)] at hd
      omega
    obtain ⟨v, hv⟩ := ih (hB.restrict _) hW hd'
    exact hB.isRefl.exists_orthogonal_basis_of_orthogonal_span_singleton hx hv

/-- **A symmetric bilinear form has an orthogonal basis if and only if it is zero or not
alternating.** The forward direction is the observation that an orthogonal basis of an alternating
form pairs every two basis vectors to zero. -/
theorem IsSymm.exists_orthogonal_basis_iff (hB : B.IsSymm) :
    (∃ v : Basis (Fin (finrank K V)) K V, B.iIsOrtho v) ↔ (B.IsAlt → B = 0) := by
  refine ⟨fun ⟨v, hv⟩ halt => ext_basis v fun i j => ?_,
    hB.exists_orthogonal_basis_of_isAlt_imp_eq_zero⟩
  obtain rfl | hij := eq_or_ne i j
  · simp [halt.self_eq_zero]
  · simp [iIsOrtho_def.1 hv i j hij]

/-- **A nondegenerate symmetric form that is not alternating has an orthonormal basis**, over a
field in which every element is a square: rescaling an orthogonal basis by inverse square roots of
the self-pairings makes the matrix of the form the identity. The hypothesis on squares holds in
every finite field of characteristic two (`isSquare_of_charTwo'`). -/
theorem IsSymm.exists_basis_toMatrix_eq_one (hsq : ∀ a : K, IsSquare a) (hB : B.IsSymm)
    (hnd : B.Nondegenerate) (h : B.IsAlt → B = 0) :
    ∃ v : Basis (Fin (finrank K V)) K V, BilinForm.toMatrix v B = 1 := by
  obtain ⟨v, hv⟩ := hB.exists_orthogonal_basis_of_isAlt_imp_eq_zero h
  have hvv : ∀ i, B (v i) (v i) ≠ 0 := hv.not_isOrtho_basis_self_of_nondegenerate hnd
  choose s hs using fun i => hsq (B (v i) (v i))
  have hs0 : ∀ i, s i ≠ 0 := fun i h0 => hvv i (by rw [hs i, h0, mul_zero])
  refine ⟨v.isUnitSMul (w := fun i => (s i)⁻¹) fun i => (inv_ne_zero (hs0 i)).isUnit, ?_⟩
  ext i j
  obtain rfl | hij := eq_or_ne i j
  · simp [toMatrix_apply, Basis.isUnitSMul_apply, hs i, hs0 i]
  · simp [toMatrix_apply, Basis.isUnitSMul_apply, iIsOrtho_def.1 hv i j hij, hij]

/-- Over a field in which every element is a square, a nondegenerate symmetric form that is not
alternating is equivalent to the standard form `∑ i, x i * y i` on `Fin n → K`, for `n` the
dimension. -/
theorem IsSymm.equivalent_toBilin'_one (hsq : ∀ a : K, IsSquare a) (hB : B.IsSymm)
    (hnd : B.Nondegenerate) (h : B.IsAlt → B = 0) :
    B.Equivalent (Matrix.toBilin' (1 : Matrix (Fin (finrank K V)) (Fin (finrank K V)) K)) := by
  obtain ⟨v, hv⟩ := hB.exists_basis_toMatrix_eq_one hsq hnd h
  exact ⟨v.isometryEquivOfToMatrixEq (Pi.basisFun K _)
    (by rw [hv, toMatrix_basisFun, toMatrix'_toBilin'])⟩

/-- Over a field in which every element is a square, two nondegenerate symmetric forms that are
not alternating, on spaces of the same dimension, are equivalent. -/
theorem IsSymm.equivalent_of_finrank_eq {V' : Type*} [AddCommGroup V'] [Module K V']
    [FiniteDimensional K V'] {B' : BilinForm K V'} (hsq : ∀ a : K, IsSquare a) (hB : B.IsSymm)
    (hnd : B.Nondegenerate) (h : B.IsAlt → B = 0) (hB' : B'.IsSymm) (hnd' : B'.Nondegenerate)
    (h' : B'.IsAlt → B' = 0) (hdim : finrank K V = finrank K V') : B.Equivalent B' := by
  have e := hB.equivalent_toBilin'_one hsq hnd h
  rw [hdim] at e
  exact e.trans (hB'.equivalent_toBilin'_one hsq hnd' h').symm

/-- **The normal-form dichotomy for a nondegenerate form that is alternating or symmetric**, over
a field in which every element is a square: an alternating form has a symplectic basis, and a
symmetric form that is not alternating has an orthonormal basis. In characteristic two every
alternating form is symmetric, so the hypothesis is just symmetry there. -/
theorem Nondegenerate.exists_basis_toMatrix_eq_J_or_toMatrix_eq_one (hsq : ∀ a : K, IsSquare a)
    (hnd : B.Nondegenerate) (h : B.IsAlt ∨ B.IsSymm) :
    (B.IsAlt ∧
        ∃ (m : ℕ) (v : Basis (Fin m ⊕ Fin m) K V), BilinForm.toMatrix v B = Matrix.J (Fin m) K) ∨
      (¬B.IsAlt ∧ ∃ v : Basis (Fin (finrank K V)) K V, BilinForm.toMatrix v B = 1) := by
  by_cases halt : B.IsAlt
  · exact Or.inl ⟨halt, halt.exists_basis_toMatrix_eq_J hnd⟩
  · exact Or.inr ⟨halt, (h.resolve_left halt).exists_basis_toMatrix_eq_one hsq hnd
      fun h' => (halt h').elim⟩

end Field

end LinearMap.BilinForm
