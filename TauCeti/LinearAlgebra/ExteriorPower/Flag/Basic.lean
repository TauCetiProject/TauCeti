/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Finite
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Basis.VectorSpace
import TauCeti.LinearAlgebra.ExteriorPower.Basic
import TauCeti.LinearAlgebra.TensorProduct.Separation

/-!
# Exterior flag spaces

`TauCeti.exteriorPower.FlagSpace R M d` is `⨂[R] i : Fin (d + 1), ⋀[R]^(i : ℕ) M`, hosting the
Plücker--Segre embedding of `d`-step flags in `M`. Every `v : Fin d → M` defines
`exteriorFlagVector R d v`, and linear maps act factorwise via `exteriorFlagMap d f`.

## Main definitions

* `TauCeti.exteriorPower.FlagSpace`: `⨂[R] i : Fin (d + 1), ⋀[R]^(i : ℕ) M`.
* `TauCeti.exteriorPower.flagSpaceZeroEquiv`: `FlagSpace R M 0 ≃ₗ[R] ⋀[R]^0 M`.
* `TauCeti.exteriorPower.flagSpaceSuccEquiv`:
  `FlagSpace R M (r + 1) ≃ₗ[R] FlagSpace R M r ⊗[R] ⋀[R]^(r + 1) M`.
* `TauCeti.exteriorPower.exteriorFlagVector`: flag tensor of prefix exterior products.
* `TauCeti.exteriorPower.exteriorFlagMap`: functorial action on `FlagSpace`.

## Main results

* `TauCeti.exteriorPower.exteriorFlagMap_id`, `TauCeti.exteriorPower.exteriorFlagMap_comp`,
  `TauCeti.exteriorPower.exteriorFlagMap_exteriorFlagVector`: functoriality of `exteriorFlagMap`.
* `TauCeti.exteriorPower.exteriorFlagVector_ne_zero_iff`: `exteriorFlagVector k d v ≠ 0` iff
  `LinearIndependent k v`.
-/

public section

open scoped TensorProduct

namespace TauCeti.exteriorPower

universe u v w

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

/-- The indexed exterior-power tensor space `⨂[R] i : Fin (d + 1), ⋀[R]^(i : ℕ) M` hosting the
Plücker--Segre embedding of `d`-step flags in `M`. -/
abbrev FlagSpace (d : ℕ) : Type (max u v) :=
  ⨂[R] i : Fin (d + 1), ⋀[R]^(i : ℕ) M

/-- Canonical linear equivalence `FlagSpace R M 0 ≃ₗ[R] ⋀[R]^0 M`. -/
noncomputable def flagSpaceZeroEquiv : FlagSpace R M 0 ≃ₗ[R] ⋀[R]^0 M :=
  PiTensorProduct.subsingletonEquiv (0 : Fin 1)

/-- Canonical linear equivalence
`FlagSpace R M (r + 1) ≃ₗ[R] FlagSpace R M r ⊗[R] ⋀[R]^(r + 1) M`. -/
noncomputable def flagSpaceSuccEquiv (r : ℕ) :
    FlagSpace R M (r + 1) ≃ₗ[R] FlagSpace R M r ⊗[R] ⋀[R]^(r + 1) M :=
  (PiTensorProduct.reindex R (fun i : Fin (r + 1 + 1) ↦ ⋀[R]^(i : ℕ) M)
      finSumFinEquiv.symm).trans
    ((PiTensorProduct.tmulEquivDep R
        (fun j : Fin (r + 1) ⊕ Fin 1 ↦ ⋀[R]^(finSumFinEquiv j : ℕ) M)).symm.trans
      (TensorProduct.congr
        (PiTensorProduct.congr fun _ : Fin (r + 1) ↦ LinearEquiv.ofEq _ _ rfl)
        ((PiTensorProduct.subsingletonEquiv (0 : Fin 1)).trans (LinearEquiv.ofEq _ _ rfl))))

variable {M}

/-- The exterior flag vector `1 ⊗ v₀ ⊗ (v₀ ∧ v₁) ⊗ ⋯ ⊗ (v₀ ∧ ⋯ ∧ v_{d-1})`
associated to `v : Fin d → M`. -/
noncomputable def exteriorFlagVector (d : ℕ) (v : Fin d → M) : FlagSpace R M d :=
  PiTensorProduct.tprod R fun i : Fin (d + 1) ↦
    _root_.exteriorPower.ιMulti R i (v ∘ Fin.castLE (Nat.le_of_lt_succ i.isLt))

variable {R}

/-- Image of `exteriorFlagVector R 0 v` under `flagSpaceZeroEquiv`. -/
@[simp]
theorem flagSpaceZeroEquiv_exteriorFlagVector (v : Fin 0 → M) :
    flagSpaceZeroEquiv R M (exteriorFlagVector R 0 v) = _root_.exteriorPower.ιMulti R 0 v := by
  simp [flagSpaceZeroEquiv, exteriorFlagVector]

/-- Image of `exteriorFlagVector R (r + 1) v` under `flagSpaceSuccEquiv`. -/
@[simp]
theorem flagSpaceSuccEquiv_exteriorFlagVector (r : ℕ) (v : Fin (r + 1) → M) :
    flagSpaceSuccEquiv R M r (exteriorFlagVector R (r + 1) v) =
      exteriorFlagVector R r (v ∘ Fin.castSucc) ⊗ₜ[R]
        _root_.exteriorPower.ιMulti R (r + 1) v := by
  dsimp only [flagSpaceSuccEquiv, exteriorFlagVector, LinearEquiv.trans_apply]
  simp only [PiTensorProduct.reindex_tprod, Equiv.symm_symm,
    PiTensorProduct.tmulEquivDep_symm_apply, TensorProduct.congr_tmul, PiTensorProduct.congr_tprod,
    LinearEquiv.trans_apply, PiTensorProduct.subsingletonEquiv_apply_tprod]
  congr 1

/-- Base-case unfolding of `exteriorFlagVector` in degree `0`. -/
theorem exteriorFlagVector_zero (v : Fin 0 → M) :
    exteriorFlagVector R 0 v =
      (flagSpaceZeroEquiv R M).symm (_root_.exteriorPower.ιMulti R 0 v) :=
  (flagSpaceZeroEquiv R M).eq_symm_apply.mpr (flagSpaceZeroEquiv_exteriorFlagVector v)

/-- Recursive unfolding of `exteriorFlagVector` in degree `r + 1`. -/
theorem exteriorFlagVector_succ (r : ℕ) (v : Fin (r + 1) → M) :
    exteriorFlagVector R (r + 1) v =
      (flagSpaceSuccEquiv R M r).symm
        (exteriorFlagVector R r (v ∘ Fin.castSucc) ⊗ₜ[R]
          _root_.exteriorPower.ιMulti R (r + 1) v) :=
  (flagSpaceSuccEquiv R M r).eq_symm_apply.mpr (flagSpaceSuccEquiv_exteriorFlagVector r v)

variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Functorial action of an `R`-linear map `M →ₗ[R] N` on `FlagSpace`. -/
noncomputable def exteriorFlagMap (d : ℕ) (f : M →ₗ[R] N) :
    FlagSpace R M d →ₗ[R] FlagSpace R N d :=
  PiTensorProduct.map fun i : Fin (d + 1) ↦ _root_.exteriorPower.map i f

/-- Evaluation of `exteriorFlagMap 0 f` under `flagSpaceZeroEquiv`. -/
@[simp]
theorem flagSpaceZeroEquiv_exteriorFlagMap_apply (f : M →ₗ[R] N) (w : FlagSpace R M 0) :
    flagSpaceZeroEquiv R N (exteriorFlagMap 0 f w) =
      _root_.exteriorPower.map 0 f (flagSpaceZeroEquiv R M w) := by
  induction w using PiTensorProduct.induction_on with
  | smul_tprod r x => simp [flagSpaceZeroEquiv, exteriorFlagMap]
  | add x y hx hy => simp [hx, hy]

/-- Evaluation of `exteriorFlagMap (r + 1) f` under `flagSpaceSuccEquiv`. -/
@[simp]
theorem flagSpaceSuccEquiv_exteriorFlagMap_apply (r : ℕ) (f : M →ₗ[R] N)
    (w : FlagSpace R M (r + 1)) :
    flagSpaceSuccEquiv R N r (exteriorFlagMap (r + 1) f w) =
      TensorProduct.map (exteriorFlagMap r f) (_root_.exteriorPower.map (r + 1) f)
        (flagSpaceSuccEquiv R M r w) := by
  induction w using PiTensorProduct.induction_on with
  | smul_tprod r' x =>
    dsimp only [flagSpaceSuccEquiv, exteriorFlagMap, LinearEquiv.trans_apply]
    simp only [map_smul, PiTensorProduct.map_tprod, PiTensorProduct.reindex_tprod, Equiv.symm_symm,
      PiTensorProduct.tmulEquivDep_symm_apply, TensorProduct.congr_tmul,
      PiTensorProduct.congr_tprod, LinearEquiv.trans_apply,
      PiTensorProduct.subsingletonEquiv_apply_tprod, TensorProduct.map_tmul]
    congr 2
  | add x y hx hy => simp [hx, hy]

/-- Base-case unfolding of `exteriorFlagMap` in degree `0`. -/
theorem exteriorFlagMap_zero (f : M →ₗ[R] N) :
    exteriorFlagMap 0 f =
      (flagSpaceZeroEquiv R N).symm.toLinearMap ∘ₗ
        _root_.exteriorPower.map 0 f ∘ₗ (flagSpaceZeroEquiv R M).toLinearMap :=
  LinearMap.ext fun w ↦ (flagSpaceZeroEquiv R N).injective (by simp)

/-- Recursive unfolding of `exteriorFlagMap` in degree `r + 1`. -/
theorem exteriorFlagMap_succ (r : ℕ) (f : M →ₗ[R] N) :
    exteriorFlagMap (r + 1) f =
      (flagSpaceSuccEquiv R N r).symm.toLinearMap ∘ₗ
        TensorProduct.map (exteriorFlagMap r f) (_root_.exteriorPower.map (r + 1) f) ∘ₗ
          (flagSpaceSuccEquiv R M r).toLinearMap :=
  LinearMap.ext fun w ↦ (flagSpaceSuccEquiv R N r).injective (by simp)

/-- `exteriorFlagMap d` sends the identity linear map to the identity. -/
@[simp]
theorem exteriorFlagMap_id (d : ℕ) :
    exteriorFlagMap d (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  simp [exteriorFlagMap]

/-- `exteriorFlagMap d` preserves composition of linear maps. -/
theorem exteriorFlagMap_comp {P : Type*} [AddCommGroup P] [Module R P] (d : ℕ)
    (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    exteriorFlagMap d (g ∘ₗ f) = exteriorFlagMap d g ∘ₗ exteriorFlagMap d f := by
  refine PiTensorProduct.ext (MultilinearMap.ext fun m ↦ ?_)
  simp [exteriorFlagMap, _root_.exteriorPower.map_comp]

/-- `exteriorFlagMap` carries the flag vector of `v` to the flag vector of `f ∘ v`. -/
@[simp]
theorem exteriorFlagMap_exteriorFlagVector (d : ℕ) (f : M →ₗ[R] N) (v : Fin d → M) :
    exteriorFlagMap d f (exteriorFlagVector R d v) = exteriorFlagVector R d (f ∘ v) := by
  simp [exteriorFlagMap, exteriorFlagVector, Function.comp_assoc]

/-- Over a field, `exteriorFlagVector k d v` is nonzero if and only if `v` is linearly
independent. -/
@[simp]
theorem exteriorFlagVector_ne_zero_iff {k : Type u} {V : Type v} [Field k]
    [AddCommGroup V] [Module k V] {d : ℕ} {v : Fin d → V} :
    exteriorFlagVector k d v ≠ 0 ↔ LinearIndependent k v := by
  induction d with
  | zero =>
    rw [← (flagSpaceZeroEquiv k V).map_ne_zero_iff, flagSpaceZeroEquiv_exteriorFlagVector]
    exact _root_.exteriorPower.ιMulti_ne_zero_iff v
  | succ r ih =>
    rw [← (flagSpaceSuccEquiv k V r).map_ne_zero_iff, flagSpaceSuccEquiv_exteriorFlagVector]
    refine ⟨fun h ↦ ?_, fun hv ↦ ?_⟩
    · rw [← _root_.exteriorPower.ιMulti_ne_zero_iff v]
      exact fun h0 ↦ h (by rw [h0, TensorProduct.tmul_zero])
    · let _ := Module.addCommMonoidToAddCommGroup k (M := FlagSpace k V r)
      let _ := Module.addCommMonoidToAddCommGroup k (M := ⋀[k]^(r + 1) V)
      exact TauCeti.tmul_ne_zero (R := k)
        (ih.mpr (hv.comp Fin.castSucc (Fin.castSucc_injective r)))
        ((_root_.exteriorPower.ιMulti_ne_zero_iff v).mpr hv)

end TauCeti.exteriorPower
