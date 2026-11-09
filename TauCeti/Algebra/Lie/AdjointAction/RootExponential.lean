/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Weights.Killing
public import TauCeti.Algebra.Lie.AdjointAction.InnerAutomorphismGroup
public import TauCeti.RingTheory.MvPolynomial.Dominant
public import TauCeti.Algebra.Lie.AdjointAction.Matrix
public import TauCeti.RingTheory.MvPolynomial.MatrixExponential
import Mathlib.Algebra.CharZero.Infinite
import TauCeti.Algebra.Lie.Weights.Basic
import TauCeti.LinearAlgebra.Matrix.ToLin

/-!
# Root exponentials and the density of the conjugates of a Cartan subalgebra

Let `L` be a finite-dimensional Lie algebra over a field `K` of characteristic zero whose Killing
form is nondegenerate, and let `H` be a splitting Cartan subalgebra. Choose a nonzero vector
`e_α` in each root space and list the roots in some order `α₁, …, α_m`. The **root-exponential
map**

`φ(t, h) = exp(t₁ ad e_{α₁}) ⋯ exp(t_m ad e_{α_m}) h`,  `t ∈ K^m`, `h ∈ H`,

takes values in the conjugates `Int(L) · H` of `H` under the group `Int(L)` of inner automorphisms
(`TauCeti.intLieAlgebra`). Each `ad e_α` is nilpotent, so each exponential is a finite sum and the
coordinates of `φ` in a basis of `L` are polynomials in `t` and in the coordinates of `h`.

At a point `(0, h₀)` the differential of `φ` sends `(τ, η)` to `η + ∑ τ_α ⁅e_α, h₀⁆`, and
`⁅e_α, h₀⁆ = -α(h₀) e_α`. If no root vanishes at `h₀` (such an `h₀` exists because `K` is
infinite) the image of the differential contains `H` and every root space, so by the root space
decomposition it is all of `L`. A polynomial map whose differential is surjective at one point is
dominant (`TauCeti.eq_zero_of_forall_eval_eq_zero_of_mulVec_surjective_jacobiMatrixAt`), so:

**a polynomial function on `L` that vanishes on `Int(L) · H` is zero.**

This is the density statement on which the injectivity half of Chevalley's restriction theorem
rests: an `Int(L)`-invariant polynomial function vanishing on `H` vanishes on `Int(L) · H`, hence
everywhere.

The differential is computed by evaluating the coordinate polynomials at a dual-number point
(`TauCeti.jacobiMatrixAt_mulVec_apply_eq_snd_aeval`): every exponential becomes `1 + ε τ_α ad e_α`,
and the product of these is `1 + ε ∑ τ_α ad e_α` because `ε² = 0`.

## Main results

* `LieSubalgebra.exists_rootExponentialPolynomialParametrization`: a polynomial family, in the
  coordinates of a basis of `L`, whose values all lie in `Int(L) · H` and whose Jacobian matrix
  is surjective at some point.
* `LieSubalgebra.polynomial_eq_zero_of_intCartan`: a polynomial in the coordinates of a basis
  of `L` that vanishes on `Int(L) · H` is zero.
* `LieSubalgebra.polynomial_eq_zero_of_invariant_of_cartan`: an `Int(L)`-invariant polynomial
  that vanishes on `H` is zero.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §23.1, where
  the injectivity of the Chevalley restriction map is proved by the density of `Int(L) · H`.
-/

public section

namespace TauCeti

open LieAlgebra LieAlgebra.IsKilling LieModule MvPolynomial Matrix List
  LinearMap.GeneralLinearGroup

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]

variable (H : LieSubalgebra K L)

variable [CharZero K] [LieAlgebra ℚ L] [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- **The root-exponential parametrization of the conjugates of a Cartan subalgebra.** Given a
basis `b` of `L` and a basis `bH` of the splitting Cartan subalgebra `H`, there is a family of
polynomials in one variable for each root and one for each basis vector of `H`, with these two
properties: its values, read in the coordinates of `b`, are all of the form `g h` with `g` in
`Int(L)` and `h ∈ H`, and its Jacobian matrix is surjective at some point. The polynomials are the
coordinates of `(t, h) ↦ ∏_α exp(t_α ad e_α) h` for chosen root vectors `e_α`. -/
theorem _root_.LieSubalgebra.exists_rootExponentialPolynomialParametrization {ι κ : Type*}
    [Finite ι] [Fintype κ] (b : Module.Basis ι K L) (bH : Module.Basis κ K H) :
    ∃ p : ι → MvPolynomial (H.root ⊕ κ) K,
      (∃ v, (jacobiMatrixAt p v).mulVec.Surjective) ∧
      ∀ x, ∃ g ∈ intLieAlgebra K L, ∃ h ∈ H, b.equivFun (g • h) = fun i ↦ eval x (p i) := by
  classical
  have := Fintype.ofFinite ι
  -- A nonzero root vector in each root space, and a nilpotency degree of its adjoint action.
  obtain ⟨e, he, he0, n, hn⟩ := H.exists_nonzero_rootVectors
  set d : H.root → ℕ := fun α ↦ n α + 2
  have hd (α) : ad K L (e α) ^ d α = 0 := by rw [pow_add, hn, zero_mul]
  have hnil' (α) (t : K) : IsNilpotent (ad K L (t • e α)) :=
    ⟨d α, by rw [map_smul, smul_pow, hd, smul_zero]⟩
  set l := (Finset.univ : Finset H.root).toList
  set A := fun α ↦ LinearMap.toMatrixAlgEquiv b (ad K L (e α))
  set c := fun j ↦ b.equivFun (bH j : L)
  refine ⟨expProdPoly l A d c, ?_, fun x ↦ ?_⟩
  · -- A point `h₀` of `H` at which no root vanishes.
    obtain ⟨h₀, hh₀⟩ := H.exists_forall_root_apply_ne_zero
    set s := bH.equivFun h₀
    have hs : ∑ j, s j • c j = b.equivFun (h₀ : L) := by
      conv_rhs => rw [← bH.sum_repr h₀]
      rw [AddSubmonoidClass.coe_finsetSum, map_sum]
      simp [s, c]
    refine ⟨Sum.elim 0 s, fun y ↦ ?_⟩
    -- The differential is `b.equivFun ∘ Λ` for the linear combination `Λ` of the vectors `v`.
    set v : H.root ⊕ κ → L :=
      Sum.elim (fun α ↦ ⁅e α, (h₀ : L)⁆) fun j ↦ (bH j : L)
    have hJ (w) : jacobiMatrixAt (expProdPoly l A d c) (Sum.elim 0 s) *ᵥ w =
        b.equivFun (Fintype.linearCombination K v w) := by
      rw [jacobiMatrixAt_expProdPoly_mulVec l A (fun _ ↦ le_add_self) c s w,
        Fintype.linearCombination_apply, Fintype.sum_sum_type, map_add, hs]
      congr 1
      · have hA : (l.map fun α ↦ w (Sum.inl α) • A α).sum =
            LinearMap.toMatrixAlgEquiv b (∑ α, w (Sum.inl α) • ad K L (e α)) := by
          simp [l, A, Finset.sum_map_toList, map_sum]
        rw [hA]
        refine (LinearMap.toMatrix_mulVec_repr b b _ _).trans ?_
        simp [v, map_sum]
      · simp [v, c, map_sum]
    obtain ⟨w, hw⟩ : b.equivFun.symm y ∈ LinearMap.range (Fintype.linearCombination K v) := by
      rw [Fintype.range_linearCombination, H.span_rootVectors_eq_top e he he0 h₀ hh₀ bH]
      trivial
    exact ⟨w, by rw [hJ, hw, LinearEquiv.apply_symm_apply]⟩
  · -- The value at `x` is `g h` for a product `g` of root exponentials and `h ∈ H`.
    refine ⟨(l.map fun α ↦ ofLinearEquiv (expAd (x (Sum.inl α) • e α)
        (hnil' α _).exists_pow_apply_eq_zero).toLinearEquiv).prod,
      list_prod_mem fun g hg ↦ ?_,
      ∑ j, x (Sum.inr j) • (bH j : L), H.sum_mem fun j _ ↦ H.smul_mem _ (bH j).2, ?_⟩
    · obtain ⟨α, -, rfl⟩ := List.mem_map.mp hg
      exact ofLinearEquiv_expAd_mem_intLieAlgebra _ (hnil' α _)
    · ext i
      rw [eval_expProdPoly, b.equivFun_list_prod_smul]
      congr 2
      · refine List.map_congr_left fun α _ ↦ ?_
        exact b.toMatrixAlgEquiv_expAd (hd α) _ (hnil' α _)
      · simp [c, map_sum]

/-- **A polynomial vanishing on the conjugates of a Cartan subalgebra is zero.** In the coordinates
of a basis `b` of `L`, a polynomial that vanishes at `g h` for every inner automorphism
`g ∈ Int(L)` and every `h` in the splitting Cartan subalgebra `H` is the zero polynomial. -/
theorem _root_.LieSubalgebra.polynomial_eq_zero_of_intCartan {ι : Type*} [Finite ι]
    (b : Module.Basis ι K L) {q : MvPolynomial ι K}
    (hq : ∀ g ∈ intLieAlgebra K L, ∀ h ∈ H, eval (b.equivFun (g • h)) q = 0) : q = 0 := by
  obtain ⟨p, ⟨v, hv⟩, hp⟩ :=
    H.exists_rootExponentialPolynomialParametrization b (Module.finBasis K H)
  refine eq_zero_of_forall_eval_eq_zero_of_mulVec_surjective_jacobiMatrixAt hv fun x ↦ ?_
  obtain ⟨g, hg, h, hh, hgh⟩ := hp x
  rw [← hgh]
  exact hq g hg h hh

/-- **Chevalley injectivity on polynomials.** In the coordinates of a basis `b` of `L`, a
polynomial invariant under the inner automorphisms `Int(L)` that vanishes on the splitting Cartan
subalgebra `H` is the zero polynomial. -/
theorem _root_.LieSubalgebra.polynomial_eq_zero_of_invariant_of_cartan {ι : Type*} [Finite ι]
    (b : Module.Basis ι K L) {q : MvPolynomial ι K}
    (hinv : ∀ g ∈ intLieAlgebra K L, ∀ x : L, eval (b.equivFun (g • x)) q = eval (b.equivFun x) q)
    (hH : ∀ h ∈ H, eval (b.equivFun h) q = 0) : q = 0 :=
  H.polynomial_eq_zero_of_intCartan b fun g hg h hh ↦ (hinv g hg h).trans (hH h hh)

end TauCeti
