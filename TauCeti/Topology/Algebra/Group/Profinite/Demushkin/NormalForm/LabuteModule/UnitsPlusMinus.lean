/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.LabuteModule.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.CharacterKernelTwoGenerators
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.RelationModule

/-!
# Labute's module of the even-rank dyadic normal form with image `{±1} × U^(f)`

Let `F` be the free pro-`2` group on `x₁, …, x_n`, `n ≥ 4`, and let `χ : F → ℤ_2ˣ` be the
standard orientation of the normal form `x₁^{2+α} (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯ (x_{n-1}, x_n)`,
read on `F`: `χ(x₂) = v = -(1 + α)⁻¹`, `χ(x₄) = u = (1 - 2^f)⁻¹` and `χ(x_i) = 1` otherwise. For
`4 ∣ α` and `f ≥ 2`, the marked value `v` has sign `-1` and `u ≠ 1` lies in `U^(2)`. In the branch
`2^f ∣ α` the image of `χ` is `{±1} × U^(f)`
(`TauCeti.range_orientationTwoEven_eq_unitsPlusMinus_of_dvd`), which is not procyclic, and `u`
topologically generates `U^(f)`. Labute's module for this normal form is `E = X ⧸ (X, X)` with
`X = ker χ`, a module over `Λ = ℤ_2[[F ⧸ X]]` through conjugation.

This file describes `X` by normal generators and hence `E` by module generators. Suppose
`v ^ 2 = u ^ m` for a `2`-adic exponent `m`; in the branch `2^f ∣ α` such an `m` exists, because
`v ^ 2 = (-v) ^ 2 ∈ U^(f)` (`TauCeti.exists_padicPow_eq_sq_of_neg_mem_unitsPrincipal`). Then the
kernel `X` is the closed normal closure of the unmarked generators `x_i`, `i ≠ 2, 4`, together
with `x₂² x₄^{-m}` and the commutator `(x₂, x₄)`
(`TauCeti.ker_orientationTwoEven_comp_mk_of_four_dvd`). In particular `E` is spanned over `Λ` by the
classes of these `n` elements
(`TauCeti.span_topologicalAbelianization_ker_orientationTwoEven_comp_mk_eq_top_of_four_dvd`). For
Labute's relator `x₁² (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯`, that is `α = 0`, the marked value is
`χ(x₂) = -1`, `m = 0`, and the extra generators are `x₂²` and `(x₂, x₄)`
(`TauCeti.ker_orientationTwoEven_comp_mk_of_eq_zero`).

Together with the expression `⟦r⟧ = (1 + α + [x₂]⁻¹) • [x₁] + (2^f - 1 + [x₄]⁻¹) • [x₃]` of the
relator class in `E` (`TauCeti.IsProP.ofMul_mk_demushkinWordTwoEven_ker`), this is the input to
Labute's argument on `E` in the branch `Im χ = {±1} × U^(f)`, where `Λ ≅ ℤ_2[C₂] ⊗ ℤ_2[[T]]`.

## Main results

* `TauCeti.ker_orientationTwoEven_comp_mk_of_four_dvd`: for `3 < n`, `2 ≤ f`, `4 ∣ α` and
  `u ^ m = v ^ 2`, the kernel of the standard orientation on `F` is the closed normal closure of
  the `x_i` with `i ≠ 2, 4`, of `x₂² x₄^{-m}` and of `(x₂, x₄)`.
* `TauCeti.ker_orientationTwoEven_comp_mk_of_eq_zero`: the case `α = 0`, with `x₂²` in place of
  `x₂² x₄^{-m}`.
* `TauCeti.span_topologicalAbelianization_ker_orientationTwoEven_comp_mk_eq_top_of_four_dvd`: the
  classes of these elements span Labute's module `E = X ⧸ (X, X)` over `ℤ_2[[F ⧸ X]]`.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), §4, Definition
  p. 121 and Theorem 6.
-/

public section

open scoped commutatorElement

namespace TauCeti

variable (a f n : ℕ) (v u : ℤ_[2]ˣ)

/-- **The kernel of the standard orientation of the even-rank dyadic normal form when
`4 ∣ α`.** For `3 < n` and `f ≥ 2`, let `χ` be the character of the free pro-`2` group on
`x₁, …, x_n` with `χ(x₂) = v`, `χ(x₄) = u` and `χ(x_i) = 1` otherwise, where `v (1 + α) = -1`,
`u (1 - 2^f) = 1` and `4 ∣ α`, so that `v` has sign `-1` and `u ≠ 1` lies in `U^(2)`. If
`u ^ m = v ^ 2` for a `2`-adic exponent `m`, then `ker χ` is the closed normal closure of the `x_i`
with `i ≠ 2, 4`, of `x₂² x₄^{-m}` and of the commutator `(x₂, x₄)`. In the branch `2^f ∣ α`, where
the image of `χ` is `{±1} × U^(f)`, such an `m` exists by
`TauCeti.exists_padicPow_eq_sq_of_neg_mem_unitsPrincipal`. -/
theorem ker_orientationTwoEven_comp_mk_of_four_dvd (hn : 3 < n) (hf : 2 ≤ f)
    (hv : (v : ℤ_[2]) * (1 + (a : ℤ_[2])) = -1) (hu : (u : ℤ_[2]) * (1 - (2 : ℤ_[2]) ^ f) = 1)
    (ha : 4 ∣ (a : ℤ_[2])) {m : ℤ_[2]}
    (hm : isProP_units_padicInt_two.padicPow u m = v ^ 2) :
    ((orientationTwoEven a f n v u).comp (presentedProP.mk 2 _)).toMonoidHom.ker =
      (Subgroup.normalClosure (insert (freeProPGen 2 n 1 ^ 2 *
          ((isProP_freeProP 2 (Fin n)).padicPow (freeProPGen 2 n 3) m)⁻¹)
        (insert ⁅freeProPGen 2 n 1, freeProPGen 2 n 3⁆
          (freeProPGen 2 n '' {i | i ≠ 1 ∧ i ≠ 3})))).topologicalClosure := by
  have hχ1 := orientationTwoEven_comp_mk_freeProPGen_one a f n v u (by omega)
  have hχ3 := orientationTwoEven_comp_mk_freeProPGen_three a f n v u hn
  have hu' : (u : ℤ_[2]) * (1 - ((2 : ℕ) : ℤ_[2]) ^ f) = 1 := by exact_mod_cast hu
  refine IsProP.ker_eq_topologicalClosure_normalClosure_of_neg_mem_unitsPrincipal
    (isProP_freeProP 2 (Fin n)) _
    (topologicalClosure_closure_insert_insert_image_freeProPGen_eq_top 2 1 3)
    (fun _ ⟨i, hi, hs⟩ ↦ hs ▸ orientationTwoEven_comp_mk_freeProPGen_of_ne a f n v u hi.1 hi.2)
    ?_ ?_ ?_ ?_
  · rw [hχ1, neg_mem_unitsPrincipal_iff_of_val_mul_one_add_eq_neg_one hv]
    norm_num
    exact ha
  · rw [hχ3]
    exact (mem_unitsPrincipal_iff_of_val_mul_one_sub_pow_eq_one hu').mpr hf
  · rw [hχ3]
    exact not_isOfFinOrder_of_val_mul_one_sub_pow_eq_one (fun _ ↦ hf) hu'
  · rw [hχ1, hχ3]
    exact hm

/-- **The kernel of the standard orientation of Labute's even-rank dyadic relator
`x₁² (x₁, x₂) x₃^{2^f} (x₃, x₄) ⋯`.** For `3 < n` and `f ≥ 2`, the character with `χ(x₂) = -1`,
`χ(x₄) = u = (1 - 2^f)⁻¹` and `χ(x_i) = 1` otherwise has kernel the closed normal closure of the
`x_i` with `i ≠ 2, 4`, of `x₂²` and of the commutator `(x₂, x₄)`. -/
theorem ker_orientationTwoEven_comp_mk_of_eq_zero (hn : 3 < n) (hf : 2 ≤ f) (ha : a = 0)
    (hv : (v : ℤ_[2]) * (1 + (a : ℤ_[2])) = -1)
    (hu : (u : ℤ_[2]) * (1 - (2 : ℤ_[2]) ^ f) = 1) :
    ((orientationTwoEven a f n v u).comp (presentedProP.mk 2 _)).toMonoidHom.ker =
      (Subgroup.normalClosure (insert (freeProPGen 2 n 1 ^ 2)
        (insert ⁅freeProPGen 2 n 1, freeProPGen 2 n 3⁆
          (freeProPGen 2 n '' {i | i ≠ 1 ∧ i ≠ 3})))).topologicalClosure := by
  have hv1 : v = -1 := by
    ext
    rw [Units.val_neg, Units.val_one, ← hv, ha]
    simp
  have hm : isProP_units_padicInt_two.padicPow u 0 = v ^ 2 := by
    rw [IsProP.padicPow_zero, hv1, neg_one_sq]
  rw [ker_orientationTwoEven_comp_mk_of_four_dvd a f n v u hn hf hv hu (by rw [ha]; simp) hm,
    IsProP.padicPow_zero, inv_one, mul_one]

/-- **Labute's module of the even-rank dyadic normal form with `4 ∣ α` is generated by the classes
of the unmarked generators, of `x₂² x₄^{-m}` and of `(x₂, x₄)`.** For `3 < n`, `f ≥ 2`, `4 ∣ α`
and `u ^ m = v ^ 2`, with `X = ker χ` the kernel of the standard orientation on the free pro-`2`
group `F`, the classes of the `x_i` with `i ≠ 2, 4`, of `x₂² x₄^{-m}` and of `(x₂, x₄)` span
`E = X ⧸ (X, X)` over `Λ = ℤ_2[[F ⧸ X]]`, for the module structure
`TauCeti.IsProP.completedGroupAlgebraModule` through conjugation. In the branch `2^f ∣ α`, where
the image of `χ` is `{±1} × U^(f)`, the exponent `m` exists by
`TauCeti.exists_padicPow_eq_sq_of_neg_mem_unitsPrincipal`. -/
theorem span_topologicalAbelianization_ker_orientationTwoEven_comp_mk_eq_top_of_four_dvd
    (hn : 3 < n) (hf : 2 ≤ f) (hv : (v : ℤ_[2]) * (1 + (a : ℤ_[2])) = -1)
    (hu : (u : ℤ_[2]) * (1 - (2 : ℤ_[2]) ^ f) = 1) (ha : 4 ∣ (a : ℤ_[2]))
    {m : ℤ_[2]} (hm : isProP_units_padicInt_two.padicPow u m = v ^ 2) :
    haveI := ((orientationTwoEven a f n v u).comp (presentedProP.mk 2 _)).isClosed_ker
    letI := ((isProP_freeProP 2 (Fin n)).topologicalAbelianization
      ((orientationTwoEven a f n v u).comp (presentedProP.mk 2 _)).toMonoidHom.ker
      ).completedGroupAlgebraModule (freeProP 2 (Fin n) ⧸
        ((orientationTwoEven a f n v u).comp (presentedProP.mk 2 _)).toMonoidHom.ker)
    Submodule.span (completedGroupAlgebra ℤ_[2] (freeProP 2 (Fin n) ⧸
        ((orientationTwoEven a f n v u).comp (presentedProP.mk 2 _)).toMonoidHom.ker))
      (Additive.ofMul '' ((QuotientGroup.mk :
        ((orientationTwoEven a f n v u).comp (presentedProP.mk 2 _)).toMonoidHom.ker →
          TopologicalAbelianization
            ((orientationTwoEven a f n v u).comp (presentedProP.mk 2 _)).toMonoidHom.ker) ''
        (Subtype.val ⁻¹' (insert (freeProPGen 2 n 1 ^ 2 *
            ((isProP_freeProP 2 (Fin n)).padicPow (freeProPGen 2 n 3) m)⁻¹)
          (insert ⁅freeProPGen 2 n 1, freeProPGen 2 n 3⁆
            (freeProPGen 2 n '' {i | i ≠ 1 ∧ i ≠ 3})))))) = ⊤ :=
  (isProP_freeProP 2 (Fin n)).span_completedGroupAlgebraModule_topologicalAbelianization_eq_top _
    ((((finite_range_freeProPGen 2 n).subset (Set.image_subset_range _ _)).insert _).insert _)
    (ker_orientationTwoEven_comp_mk_of_four_dvd a f n v u hn hf hv hu ha hm).symm

end TauCeti
