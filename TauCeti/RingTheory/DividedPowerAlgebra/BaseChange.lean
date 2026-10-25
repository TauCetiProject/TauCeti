/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DividedPowerAlgebra.Exp
public import TauCeti.RingTheory.DividedPowerAlgebra.Grading

/-!
# Base change of divided power algebras

For a commutative `R`-algebra `S` and an `R`-module `M`, the canonical map
`S ⊗[R] Γ_R(M) → Γ_S(S ⊗[R] M)`, `s ⊗ dp R n m ↦ s • dp S n (1 ⊗ m)`, is an isomorphism of
`S`-algebras. It preserves the grading, so it restricts to `S`-linear equivalences
`S ⊗[R] Γ^d_R(M) ≃ Γ^d_S(S ⊗[R] M)` of homogeneous pieces, taking `1 ⊗ dp R d m` to
`dp S d (1 ⊗ m)`. No flatness of `S` and no freeness or finiteness of `M` is assumed.

## Main declarations

* `DividedPowerAlgebra.baseChangeEquiv`: the `S`-algebra isomorphism
  `S ⊗[R] Γ_R(M) ≃ₐ[S] Γ_S(S ⊗[R] M)`.
* `DividedPowerAlgebra.baseChangeEquiv_tmul`, `DividedPowerAlgebra.baseChangeEquiv_pow_tmul_dp`
  and `DividedPowerAlgebra.baseChangeEquiv_symm_dp`: its values in both directions.
* `DividedPowerAlgebra.baseChangeHomogeneousEquiv`: the `S`-linear isomorphism
  `S ⊗[R] Γ^d_R(M) ≃ₗ[S] Γ^d_S(S ⊗[R] M)` on homogeneous pieces.

## Implementation notes

The inverse sends `dp S n x`, for any `x : S ⊗[R] M`, to the `X ^ n`-coefficient of the
divided-power exponential `DividedPowerAlgebra.exp x`, which takes values in `S ⊗[R] Γ_R(M)`.
This is well defined because the coefficients of the exponential satisfy the defining relations
of `Γ_S(S ⊗[R] M)`, and the universal property `DividedPowerAlgebra.lift'` applies. The layout
follows Mathlib's base change of exterior algebras, `ExteriorAlgebra.baseChangeEquiv`.

## References

* [N. Roby, *Lois polynômes et lois formelles en théorie des modules* (1963),
  Théorème III.3][Roby-1963]
* The ambient `DividedPowerAlgebra`, its functorial map and `lift'` are the Mathlib formalization
  by Antoine Chambert-Loir and María Inés de Frutos-Fernández.
-/

public section

noncomputable section

open TensorProduct PowerSeries

namespace DividedPowerAlgebra

variable (R : Type*) [CommSemiring R] (M : Type*) [AddCommMonoid M] [Module R M]
variable (S : Type*) [CommSemiring S] [Algebra R S]

/-- The forward map of `baseChangeEquiv`: `s ⊗ z ↦ s • map S (1 ⊗ ·) z`. -/
private def baseChangeForward :
    S ⊗[R] DividedPowerAlgebra R M →ₐ[S] DividedPowerAlgebra S (S ⊗[R] M) :=
  Algebra.TensorProduct.lift (Algebra.ofId S _) (map S (TensorProduct.mk R S M 1))
    fun _ _ ↦ Commute.all _ _

/-- The inverse map of `baseChangeEquiv`: `dp S n x` goes to the `X ^ n`-coefficient of the
divided-power exponential of `x`. -/
private def baseChangeInverse :
    DividedPowerAlgebra S (S ⊗[R] M) →ₐ[S] S ⊗[R] DividedPowerAlgebra R M :=
  lift' (f := fun nx ↦ coeff nx.1 (exp nx.2))
    (fun x ↦ by rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_exp])
    (fun n s x ↦ by
      rw [exp_smul, coeff_rescale (R := S ⊗[R] DividedPowerAlgebra R M)]
      simp [Algebra.smul_def])
    (fun m n x ↦ coeff_exp_mul_coeff_exp x m n)
    (fun n x y ↦ by rw [exp_add, coeff_mul])

private theorem baseChangeForward_tmul (s : S) (z : DividedPowerAlgebra R M) :
    baseChangeForward R M S (s ⊗ₜ[R] z) = s • map S (TensorProduct.mk R S M 1) z := by
  rw [baseChangeForward, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Algebra.smul_def]

private theorem baseChangeForward_pow_tmul_dp (s : S) (n : ℕ) (m : M) :
    baseChangeForward R M S ((s ^ n) ⊗ₜ[R] dp R n m) = dp S n (s ⊗ₜ[R] m) := by
  rw [baseChangeForward_tmul, map_apply_dp, mk_apply, ← dp_smul, smul_tmul', smul_eq_mul, mul_one]

private theorem baseChangeInverse_dp (n : ℕ) (x : S ⊗[R] M) :
    baseChangeInverse R M S (dp S n x) = coeff n (exp x) := by
  rw [baseChangeInverse, lift'_apply_dp]

/-- The forward map sends the coefficients of the exponential of `x` to the divided powers
of `x`. -/
private theorem baseChangeForward_coeff_exp (x : S ⊗[R] M) (n : ℕ) :
    baseChangeForward R M S (coeff n (exp x)) = dp S n x := by
  induction x using TensorProduct.inductionOn generalizing n with
  | tmul s m =>
      rw [coeff_exp_tmul, baseChangeForward_pow_tmul_dp]
  | add x y hx hy =>
      rw [exp_add, coeff_mul, map_sum, dp_add]
      exact Finset.sum_congr rfl fun k _ ↦ by rw [map_mul, hx, hy]

/-- **Base change of divided power algebras**: for a commutative `R`-algebra `S`, the canonical
map `S ⊗[R] Γ_R(M) → Γ_S(S ⊗[R] M)` is an isomorphism of `S`-algebras. No flatness is
assumed. -/
def baseChangeEquiv :
    S ⊗[R] DividedPowerAlgebra R M ≃ₐ[S] DividedPowerAlgebra S (S ⊗[R] M) :=
  AlgEquiv.ofAlgHom (baseChangeForward R M S) (baseChangeInverse R M S)
    (algHom_ext fun n x ↦ by
      rw [AlgHom.comp_apply, baseChangeInverse_dp, baseChangeForward_coeff_exp, AlgHom.id_apply])
    (by
      apply Algebra.TensorProduct.ext_ring
      refine algHom_ext (A := S ⊗[R] DividedPowerAlgebra R M) fun n m ↦ ?_
      simp [baseChangeForward_tmul, baseChangeInverse_dp])

private theorem baseChangeEquiv_apply (x : S ⊗[R] DividedPowerAlgebra R M) :
    baseChangeEquiv R M S x = baseChangeForward R M S x :=
  congr($(AlgEquiv.toAlgHom_ofAlgHom _ _ _ _) x)

private theorem baseChangeEquiv_symm_apply (y : DividedPowerAlgebra S (S ⊗[R] M)) :
    (baseChangeEquiv R M S).symm y = baseChangeInverse R M S y := by
  rw [baseChangeEquiv, AlgEquiv.ofAlgHom_symm]
  exact congr($(AlgEquiv.toAlgHom_ofAlgHom _ _ _ _) y)

/-- The base change isomorphism sends `s ⊗ z` to `s` times the image of `z` under the
functorial map `M → S ⊗[R] M`, `m ↦ 1 ⊗ m`. -/
@[simp]
theorem baseChangeEquiv_tmul (s : S) (z : DividedPowerAlgebra R M) :
    baseChangeEquiv R M S (s ⊗ₜ[R] z) = s • map S (TensorProduct.mk R S M 1) z :=
  (baseChangeEquiv_apply R M S _).trans (baseChangeForward_tmul R M S s z)

/-- The base change isomorphism sends `s ^ n ⊗ dp R n m` to `dp S n (s ⊗ m)`. -/
theorem baseChangeEquiv_pow_tmul_dp (s : S) (n : ℕ) (m : M) :
    baseChangeEquiv R M S ((s ^ n) ⊗ₜ[R] dp R n m) = dp S n (s ⊗ₜ[R] m) :=
  (baseChangeEquiv_apply R M S _).trans (baseChangeForward_pow_tmul_dp R M S s n m)

/-- The base change isomorphism sends `1 ⊗ dp R n m` to `dp S n (1 ⊗ m)`. -/
theorem baseChangeEquiv_one_tmul_dp (n : ℕ) (m : M) :
    baseChangeEquiv R M S (1 ⊗ₜ[R] dp R n m) = dp S n (1 ⊗ₜ[R] m) := by
  rw [← baseChangeEquiv_pow_tmul_dp, one_pow]

/-- The inverse of the base change isomorphism sends `dp S n x` to the `X ^ n`-coefficient of
the divided-power exponential of `x`. -/
theorem baseChangeEquiv_symm_dp (n : ℕ) (x : S ⊗[R] M) :
    (baseChangeEquiv R M S).symm (dp S n x) = coeff n (exp x) :=
  (baseChangeEquiv_symm_apply R M S _).trans (baseChangeInverse_dp R M S n x)

/-- The inverse of the base change isomorphism sends `dp S n (s ⊗ m)` to `s ^ n ⊗ dp R n m`. -/
@[simp]
theorem baseChangeEquiv_symm_dp_tmul (n : ℕ) (s : S) (m : M) :
    (baseChangeEquiv R M S).symm (dp S n (s ⊗ₜ[R] m)) = (s ^ n) ⊗ₜ[R] dp R n m := by
  rw [baseChangeEquiv_symm_dp, coeff_exp_tmul]

section Homogeneous

variable (d : ℕ)

/-- The base change isomorphism takes the base change of `Γ^d_R(M)` into `Γ^d_S(S ⊗[R] M)`. -/
private theorem baseChangeEquiv_baseChange_subtype_mem
    (z : S ⊗[R] homogeneousSubmodule (R := R) (M := M) d) :
    baseChangeEquiv R M S ((homogeneousSubmodule (R := R) (M := M) d).subtype.baseChange S z) ∈
      homogeneousSubmodule (R := S) (M := S ⊗[R] M) d := by
  induction z using TensorProduct.inductionOn with
  | tmul s w =>
      rw [LinearMap.baseChange_tmul, baseChangeEquiv_tmul]
      exact Submodule.smul_mem _ s (map_mem_homogeneousSubmodule _ w.2)
  | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy

/-- The base change isomorphism commutes with taking degree-`d` components. -/
private theorem coe_decompose_baseChangeEquiv (z : S ⊗[R] DividedPowerAlgebra R M) :
    (DirectSum.decompose (homogeneousSubmodule (R := S) (M := S ⊗[R] M))
        (baseChangeEquiv R M S z) d : DividedPowerAlgebra S (S ⊗[R] M)) =
      baseChangeEquiv R M S
        (((homogeneousSubmodule (R := R) (M := M) d).subtype ∘ₗ homogeneousProj R M d).baseChange
          S z) := by
  induction z using TensorProduct.inductionOn with
  | tmul s w =>
      rw [LinearMap.baseChange_tmul, baseChangeEquiv_tmul, baseChangeEquiv_tmul,
        DirectSum.decompose_smul, DirectSum.smul_apply, Submodule.coe_smul, coe_decompose_map,
        LinearMap.comp_apply, Submodule.subtype_apply, homogeneousProj_apply]
  | add x y hx hy => simp only [map_add, DirectSum.decompose_add, DirectSum.add_apply,
      Submodule.coe_add, hx, hy]

/-- The forward map of `baseChangeHomogeneousEquiv`. -/
private def baseChangeHomogeneousForward :
    S ⊗[R] homogeneousSubmodule (R := R) (M := M) d →ₗ[S]
      homogeneousSubmodule (R := S) (M := S ⊗[R] M) d :=
  LinearMap.codRestrict _
    ((baseChangeEquiv R M S).toLinearMap ∘ₗ
      (homogeneousSubmodule (R := R) (M := M) d).subtype.baseChange S)
    fun z ↦ by
      simpa only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply] using
        baseChangeEquiv_baseChange_subtype_mem R M S d z

/-- The inverse map of `baseChangeHomogeneousEquiv`. -/
private def baseChangeHomogeneousInverse :
    homogeneousSubmodule (R := S) (M := S ⊗[R] M) d →ₗ[S]
      S ⊗[R] homogeneousSubmodule (R := R) (M := M) d :=
  (homogeneousProj R M d).baseChange S ∘ₗ (baseChangeEquiv R M S).symm.toLinearMap ∘ₗ
    (homogeneousSubmodule (R := S) (M := S ⊗[R] M) d).subtype

/-- **Base change of homogeneous divided powers**: for a commutative `R`-algebra `S`, the base
change isomorphism restricts to an `S`-linear isomorphism
`S ⊗[R] Γ^d_R(M) ≃ₗ[S] Γ^d_S(S ⊗[R] M)` taking `1 ⊗ dp R d m` to `dp S d (1 ⊗ m)`
(`baseChangeHomogeneousEquiv_one_tmul_dp`). No flatness is assumed. -/
def baseChangeHomogeneousEquiv :
    S ⊗[R] homogeneousSubmodule (R := R) (M := M) d ≃ₗ[S]
      homogeneousSubmodule (R := S) (M := S ⊗[R] M) d :=
  LinearEquiv.ofLinearMap (baseChangeHomogeneousForward R M S d)
    (baseChangeHomogeneousInverse R M S d)
    (LinearMap.ext fun y ↦ Subtype.ext <| by
      simp only [baseChangeHomogeneousForward, baseChangeHomogeneousInverse, LinearMap.comp_apply,
        LinearMap.codRestrict_apply, AlgEquiv.toLinearMap_apply, Submodule.subtype_apply,
        LinearMap.id_apply]
      rw [← LinearMap.comp_apply (LinearMap.baseChange S _), ← LinearMap.baseChange_comp,
        ← coe_decompose_baseChangeEquiv, AlgEquiv.apply_symm_apply,
        DirectSum.decompose_of_mem_same _ y.2])
    (LinearMap.ext fun z ↦ by
      simp only [baseChangeHomogeneousForward, baseChangeHomogeneousInverse, LinearMap.comp_apply,
        LinearMap.codRestrict_apply, AlgEquiv.toLinearMap_apply, Submodule.subtype_apply,
        AlgEquiv.symm_apply_apply, LinearMap.id_apply]
      rw [← LinearMap.comp_apply (LinearMap.baseChange S _), ← LinearMap.baseChange_comp,
        homogeneousProj_comp_subtype, LinearMap.baseChange_id, LinearMap.id_apply])

/-- The base change isomorphism of homogeneous pieces is the restriction of `baseChangeEquiv`. -/
theorem coe_baseChangeHomogeneousEquiv_apply
    (z : S ⊗[R] homogeneousSubmodule (R := R) (M := M) d) :
    (baseChangeHomogeneousEquiv R M S d z : DividedPowerAlgebra S (S ⊗[R] M)) =
      baseChangeEquiv R M S ((homogeneousSubmodule (R := R) (M := M) d).subtype.baseChange S z) :=
  (rfl)

/-- The base change isomorphism of homogeneous pieces sends `1 ⊗ dp R d m` to
`dp S d (1 ⊗ m)`. -/
@[simp]
theorem baseChangeHomogeneousEquiv_one_tmul_dp (m : M) :
    baseChangeHomogeneousEquiv R M S d (1 ⊗ₜ[R] ⟨dp R d m, dp_mem_homogeneousSubmodule d m⟩) =
      ⟨dp S d (1 ⊗ₜ[R] m), dp_mem_homogeneousSubmodule d _⟩ := by
  ext
  rw [coe_baseChangeHomogeneousEquiv_apply, LinearMap.baseChange_tmul, Submodule.subtype_apply,
    baseChangeEquiv_one_tmul_dp]

/-- The inverse of the base change isomorphism of homogeneous pieces sends `dp S d (s ⊗ m)` to
`s ^ d ⊗ dp R d m`. -/
@[simp]
theorem baseChangeHomogeneousEquiv_symm_dp_tmul (s : S) (m : M) :
    (baseChangeHomogeneousEquiv R M S d).symm
        ⟨dp S d (s ⊗ₜ[R] m), dp_mem_homogeneousSubmodule d _⟩ =
      (s ^ d) ⊗ₜ[R] ⟨dp R d m, dp_mem_homogeneousSubmodule d m⟩ := by
  rw [LinearEquiv.symm_apply_eq]
  ext
  rw [coe_baseChangeHomogeneousEquiv_apply, LinearMap.baseChange_tmul, Submodule.subtype_apply,
    baseChangeEquiv_pow_tmul_dp]

end Homogeneous

end DividedPowerAlgebra
