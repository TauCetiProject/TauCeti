/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Weight
public import TauCeti.Algebra.Coalgebra.Comodule.BaseChange
import Mathlib.LinearAlgebra.TensorProduct.Decomposition

/-!
# Base change of weight spaces

Let `V` be a right comodule over an `R`-coalgebra `C`, corestricted along a coalgebra morphism
`π : C → R[X]` as in `TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Weight`, and let `S`
be a commutative `R`-algebra. Give `S ⊗[R] V` the base-changed comodule structure over
`S ⊗[R] C` (`TauCeti.Comodule.baseChange`) and corestrict it along a coalgebra morphism
`πS : S ⊗[R] C → S[X]` that agrees with `π` on `1 ⊗ c`, after mapping the coefficients along
`R → S`.

Then every weight space of `S ⊗[R] V` is the base change of the corresponding weight space
of `V`. No flatness is needed: base change carries the decomposition of `V` into weight spaces
to a decomposition of `S ⊗[R] V` into submodules contained in its weight spaces, and an
independent family is determined by any smaller family with the same supremum.

When `C` is the coordinate bialgebra of an affine group `G`, `π` exhibits a homomorphism
`D(X) → G`, and `πS` is its base change, this says that restricting a representation to
`D(X)` commutes with extension of the base ring.

## Main results

* `TauCeti.DiagonalizableGroup.weightSpace_baseChange`: **the weight spaces of the base-changed
  comodule are the base changes of the weight spaces.**
* `TauCeti.DiagonalizableGroup.injective_baseChange_subtype_weightSpace`: a weight space is a
  direct summand, so its inclusion stays injective after base change.

## References

* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §3.2.
* J. S. Milne, *Algebraic Groups* (2017), §12.c.
-/

public section

open scoped TensorProduct

namespace TauCeti.DiagonalizableGroup

section Injective

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
variable {C : Type*} [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {X : Type*}
variable {V : Type*} [AddCommMonoid V] [Module R V] [Comodule R C V]

variable (S V) in
/-- **A weight space is a direct summand**, so its inclusion stays injective after any base
change, flat or not. -/
theorem injective_baseChange_subtype_weightSpace (π : C →ₗc[R] MonoidAlgebra R X) (x : X) :
    Function.Injective ((weightSpace V π x).subtype.baseChange S) := by
  classical
  exact ((weightSpace V π x).subtype.baseChange S).injective_rangeRestrict_iff.mp
    (DirectSum.IsInternal.toBaseChange_injective (S := S) _ (isInternal_weightSpace V π) x)

end Injective

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable {C : Type*} [AddCommGroup C] [Module R C] [Coalgebra R C]
variable {X : Type*} [Monoid X]
variable {V : Type*} [AddCommGroup V] [Module R V] [Comodule R C V]

/-- Corestricting the base-changed coaction of `1 ⊗ v` along `πS` is the base change of the
corestriction of the coaction of `v` along `π`. -/
private theorem map_baseChangeCoact_one_tmul (π : C →ₗc[R] MonoidAlgebra R X)
    (πS : S ⊗[R] C →ₗc[S] MonoidAlgebra S X)
    (hπ : ∀ c, πS (1 ⊗ₜ c) = MonoidAlgebra.mapAlgHom X (Algebra.ofId R S) (π c)) (v : V) :
    TensorProduct.map LinearMap.id πS.toLinearMap
        (Comodule.baseChangeCoact (R := R) (H := C) S (1 ⊗ₜ[R] v)) =
      LinearMap.lTensor (S ⊗[R] V)
        ((MonoidAlgebra.mapAlgHom X (Algebra.ofId R S)).toLinearMap.liftBaseChange S)
        (TensorProduct.AlgebraTensorModule.distribBaseChange R S V (MonoidAlgebra R X)
          (1 ⊗ₜ[R] TensorProduct.map LinearMap.id π.toLinearMap
            (Comodule.coact (R := R) (C := C) (M := V) v))) := by
  rw [Comodule.baseChangeCoact_tmul]
  induction Comodule.coact (R := R) (C := C) (M := V) v using TensorProduct.inductionOn with
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul w c => simp [hπ]

variable (V) in
/-- **Weight spaces commute with base change.** If `πS : S ⊗[R] C → S[X]` agrees with
`π : C → R[X]` on `1 ⊗ c` after mapping coefficients along `R → S`, then the `x`-weight space
of the base-changed comodule `S ⊗[R] V` is the base change of the `x`-weight space of `V`.

No flatness of `S` over `R` is assumed. -/
theorem weightSpace_baseChange (π : C →ₗc[R] MonoidAlgebra R X)
    (πS : S ⊗[R] C →ₗc[S] MonoidAlgebra S X)
    (hπ : ∀ c, πS (1 ⊗ₜ c) = MonoidAlgebra.mapAlgHom X (Algebra.ofId R S) (π c)) (x : X) :
    letI := Comodule.baseChange (R := R) (H := C) (M := V) S
    weightSpace (S ⊗[R] V) πS x = (weightSpace V π x).baseChange S := by
  classical
  let _ := Comodule.baseChange (R := R) (H := C) (M := V) S
  -- The base change of each weight space lies in the corresponding weight space.
  have hle : (fun x ↦ (weightSpace V π x).baseChange S) ≤ weightSpace (S ⊗[R] V) πS := by
    intro x
    rw [Submodule.baseChange_le_iff_le_comap]
    intro v hv
    simp only [Submodule.mem_comap, Submodule.restrictScalars_mem, TensorProduct.mk_apply,
      mem_weightSpace, Comodule.baseChange_coact]
    rw [map_baseChangeCoact_one_tmul π πS hπ, mem_weightSpace.mp hv]
    simp
  -- These base changes still exhaust `S ⊗[R] V`, and the weight spaces are independent.
  have htop : ⨆ x, (weightSpace V π x).baseChange S = ⊤ := by
    rw [← Submodule.baseChange_iSup, (isInternal_weightSpace V π).submodule_iSup_eq_top,
      Submodule.baseChange_top]
  exact (congrFun (((isInternal_weightSpace (S ⊗[R] V) πS).submodule_iSupIndep
    |>.le_iff_eq_of_iSup_eq_top htop).mp hle) x).symm

end

end TauCeti.DiagonalizableGroup
