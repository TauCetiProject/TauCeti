/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Locally constant families of finitely supported functions as linear maps

Let `ι` be a finite discrete space and `X` a topological space. A locally constant function
`X → (ι →₀ R)` is the same as an `R`-linear map `LocallyConstant ι R →ₗ[R] LocallyConstant X R`:
a family `φ` sends `f` to `x ↦ ∑ i, φ x i * f i`, and a linear map `L` is recovered from its
values on the indicator functions of the points of `ι`
(`TauCeti.locallyConstantFinsuppLinearEquiv`). The index type of the finitely supported functions
is allowed to differ from `ι` by an equivalence, so that it can be a universe lift of `ι`.
The equivalence is natural in `X` (`TauCeti.locallyConstantFinsuppLinearEquiv_comap`) and in
`ι` (`TauCeti.locallyConstantFinsuppLinearEquiv_map_mapDomain`).

When `X` is compact Hausdorff and `T` is a finite set, the left-hand side is the module of
sections over `X` of the discrete condensed module `R[T]`. The equivalence thus identifies `R[T]`
with the dual of the locally constant functions on `T`, which is the finite case of the
description of free solid modules on profinite sets.
-/

public section

namespace LocallyConstant

/-- Zero and addition of locally constant functions are pointwise, so that the generic `FunLike`
lemmas such as `sum_apply` apply to `LocallyConstant X M`. -/
instance {X M : Type*} [TopologicalSpace X] [Zero M] : IsZeroApply (LocallyConstant X M) where

instance {X M : Type*} [TopologicalSpace X] [Add M] : IsAddApply (LocallyConstant X M) where

end LocallyConstant

namespace TauCeti

open LocallyConstant

variable (R : Type*) [CommSemiring R] (X : Type*) [TopologicalSpace X]
  {ι κ : Type*} [TopologicalSpace ι] [DiscreteTopology ι] [Finite κ] (e : κ ≃ ι)

/-- For a finite discrete space `ι` and an equivalence `e : κ ≃ ι`, locally constant maps
`X → (κ →₀ R)` are the same as `R`-linear maps `LocallyConstant ι R →ₗ[R] LocallyConstant X R`.
A family `φ` sends `f` to `x ↦ ∑ k, φ x k * f (e k)`; the inverse records the values of a linear
map on the indicator functions of the points of `ι`. -/
noncomputable def locallyConstantFinsuppLinearEquiv :
    LocallyConstant X (κ →₀ R) ≃ₗ[R] (LocallyConstant ι R →ₗ[R] LocallyConstant X R) where
  toFun φ :=
    { toFun f := φ.map (Finsupp.linearCombination R (f ∘ e))
      map_add' f g := by
        ext x
        simp [Finsupp.linearCombination_apply, mul_add, Finsupp.sum_add]
      map_smul' r f := by
        ext x
        simp [Finsupp.linearCombination_apply, Finsupp.mul_sum, mul_left_comm] }
  map_add' φ ψ := by ext f x; simp
  map_smul' r φ := by ext f x; simp
  invFun L :=
    letI := Fintype.ofFinite κ
    ∑ k, (L (charFn R (isClopen_discrete {e k}))).map (Finsupp.single k)
  left_inv φ := by
    classical
    let := Fintype.ofFinite κ
    ext x k
    simp only [LinearMap.coe_mk, AddHom.coe_mk, _root_.sum_apply, map_apply,
      Function.comp_apply]
    rw [Finset.sum_apply']
    simp [Finsupp.single_apply, Finsupp.linearCombination_apply, Finsupp.sum_fintype, coe_charFn,
      Pi.single_apply]
  right_inv L := by
    classical
    let := Fintype.ofFinite κ
    ext f x
    -- Expand `f` in the basis of indicator functions of the points of `ι`.
    have hf : f = ∑ k, f (e k) • charFn R (isClopen_discrete {e k}) := by
      ext i
      obtain ⟨j, rfl⟩ := e.surjective i
      simp [coe_charFn, Pi.single_apply]
    conv_rhs => rw [hf]
    simp [Finsupp.linearCombination_apply, Finsupp.sum_fintype, Finsupp.single_apply, mul_comm]

@[simp]
lemma locallyConstantFinsuppLinearEquiv_apply_apply (φ : LocallyConstant X (κ →₀ R))
    (f : LocallyConstant ι R) :
    locallyConstantFinsuppLinearEquiv R X e φ f = φ.map (Finsupp.linearCombination R (f ∘ e)) :=
  (rfl)

/-- The `k`-th coefficient at `x` of the family corresponding to a linear map `L` is the value at
`x` of `L` on the indicator function of the point `e k`. -/
@[simp]
lemma locallyConstantFinsuppLinearEquiv_symm_apply_apply_apply
    (L : LocallyConstant ι R →ₗ[R] LocallyConstant X R) (x : X) (k : κ) :
    (locallyConstantFinsuppLinearEquiv R X e).symm L x k =
      L (charFn R (isClopen_discrete {e k})) x := by
  classical
  simp [locallyConstantFinsuppLinearEquiv, Finset.sum_apply', Finsupp.single_apply]

/-- `locallyConstantFinsuppLinearEquiv` is natural in `X`: pulling a family back along
`g : X → Y` postcomposes the corresponding linear map with the pullback along `g`. -/
lemma locallyConstantFinsuppLinearEquiv_comap {Y : Type*} [TopologicalSpace Y] (g : C(X, Y))
    (φ : LocallyConstant Y (κ →₀ R)) (f : LocallyConstant ι R) :
    locallyConstantFinsuppLinearEquiv R X e (φ.comap g) f =
      (locallyConstantFinsuppLinearEquiv R Y e φ f).comap g := by
  ext x
  simp

/-- `locallyConstantFinsuppLinearEquiv` is natural in `ι`: if `h : κ → κ'` covers a continuous
map `g : ι → ι'`, pushing the coefficients of a family forward along `h` precomposes the
corresponding linear map with the pullback along `g`. -/
lemma locallyConstantFinsuppLinearEquiv_map_mapDomain {ι' κ' : Type*} [TopologicalSpace ι']
    [DiscreteTopology ι'] [Finite κ'] (e' : κ' ≃ ι') (h : κ → κ') (g : C(ι, ι'))
    (hg : ∀ k, e' (h k) = g (e k)) (φ : LocallyConstant X (κ →₀ R)) (f : LocallyConstant ι' R) :
    locallyConstantFinsuppLinearEquiv R X e' (φ.map (Finsupp.mapDomain h)) f =
      locallyConstantFinsuppLinearEquiv R X e φ (f.comap g) := by
  ext x
  simp only [locallyConstantFinsuppLinearEquiv_apply_apply, map_apply, Function.comp_apply]
  rw [Finsupp.linearCombination_mapDomain]
  congr 2
  ext k
  simp [hg]

end TauCeti
