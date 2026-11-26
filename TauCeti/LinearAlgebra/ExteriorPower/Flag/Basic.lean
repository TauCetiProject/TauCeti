/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.LinearAlgebra.PiTensorProduct.Finite
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

* `TauCeti.exteriorPower.flagSpaceZeroEquiv_tprod`,
  `TauCeti.exteriorPower.flagSpaceZeroEquiv_symm_apply`,
  `TauCeti.exteriorPower.flagSpaceSuccEquiv_tprod`,
  `TauCeti.exteriorPower.flagSpaceSuccEquiv_symm_tprod_tmul`: pure-tensor evaluation lemmas for
  the canonical flag-space equivalences.
* `TauCeti.exteriorPower.exteriorFlagVector_def`, `TauCeti.exteriorPower.exteriorFlagMap_tprod`:
  indexed-tensor characterization of `exteriorFlagVector` and `exteriorFlagMap`.
* `TauCeti.exteriorPower.exteriorFlagMap_id`, `TauCeti.exteriorPower.exteriorFlagMap_comp`,
  `TauCeti.exteriorPower.exteriorFlagMap_exteriorFlagVector`: functoriality of `exteriorFlagMap`.
* `TauCeti.exteriorPower.exteriorFlagVector_ne_zero_iff`: `exteriorFlagVector k d v ≠ 0` iff
  `LinearIndependent k v`.

## References

* W. Fulton, *Young Tableaux*, LMSST 35, Cambridge University Press (1997), §9.1.
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

/-- `flagSpaceZeroEquiv` evaluates on a pure tensor at its unique index `0`. -/
@[simp]
theorem flagSpaceZeroEquiv_tprod (x : ∀ i : Fin 1, ⋀[R]^(i : ℕ) M) :
    flagSpaceZeroEquiv R M (PiTensorProduct.tprod R x) = x 0 := by
  simp [flagSpaceZeroEquiv]

/-- `(flagSpaceZeroEquiv R M).symm` sends `x : ⋀[R]^0 M` to the corresponding pure tensor via
`Fin.lastCases`. -/
theorem flagSpaceZeroEquiv_symm_apply (x : ⋀[R]^0 M) :
    (flagSpaceZeroEquiv R M).symm x =
      PiTensorProduct.tprod R (Fin.lastCases x fun i : Fin 0 ↦ i.elim0) :=
  (flagSpaceZeroEquiv R M).injective (by simp; rfl)

/-- `flagSpaceSuccEquiv` splits a pure tensor into its prefix tensor and its last factor. -/
@[simp]
theorem flagSpaceSuccEquiv_tprod (r : ℕ) (x : ∀ i : Fin (r + 2), ⋀[R]^(i : ℕ) M) :
    flagSpaceSuccEquiv R M r (PiTensorProduct.tprod R x) =
      (PiTensorProduct.tprod R fun j : Fin (r + 1) ↦ x j.castSucc) ⊗ₜ[R] x (Fin.last (r + 1)) := by
  dsimp only [flagSpaceSuccEquiv, LinearEquiv.trans_apply]
  simp only [PiTensorProduct.reindex_tprod, Equiv.symm_symm,
    PiTensorProduct.tmulEquivDep_symm_apply, TensorProduct.congr_tmul, PiTensorProduct.congr_tprod,
    LinearEquiv.trans_apply, PiTensorProduct.subsingletonEquiv_apply_tprod]
  rfl

/-- `(flagSpaceSuccEquiv R M r).symm` recombines a pure prefix tensor and a top factor into a
single pure tensor via `Fin.lastCases`. -/
@[simp]
theorem flagSpaceSuccEquiv_symm_tprod_tmul (r : ℕ)
    (y : ∀ j : Fin (r + 1), ⋀[R]^(j : ℕ) M) (z : ⋀[R]^(r + 1) M) :
    (flagSpaceSuccEquiv R M r).symm ((PiTensorProduct.tprod R y) ⊗ₜ[R] z) =
      PiTensorProduct.tprod R (Fin.lastCases z y) :=
  (flagSpaceSuccEquiv R M r).injective (by simp)

/-- The exterior flag vector `1 ⊗ v₀ ⊗ (v₀ ∧ v₁) ⊗ ⋯ ⊗ (v₀ ∧ ⋯ ∧ v_{d-1})`
associated to `v : Fin d → M`. -/
noncomputable def exteriorFlagVector (d : ℕ) (v : Fin d → M) : FlagSpace R M d :=
  PiTensorProduct.tprod R fun i : Fin (d + 1) ↦
    _root_.exteriorPower.ιMulti R i (v ∘ Fin.castLE (Nat.le_of_lt_succ i.isLt))

variable {R}

/-- `exteriorFlagVector R d v` is the pure tensor of prefix exterior products
`ιMulti R i (v ∘ Fin.castLE _)`. -/
theorem exteriorFlagVector_def (d : ℕ) (v : Fin d → M) :
    exteriorFlagVector R d v =
      PiTensorProduct.tprod R fun i : Fin (d + 1) ↦
        _root_.exteriorPower.ιMulti R i (v ∘ Fin.castLE (Nat.le_of_lt_succ i.isLt)) := by
  rfl

/-- Image of `exteriorFlagVector R 0 v` under `flagSpaceZeroEquiv`. -/
@[simp]
theorem flagSpaceZeroEquiv_exteriorFlagVector (v : Fin 0 → M) :
    flagSpaceZeroEquiv R M (exteriorFlagVector R 0 v) = _root_.exteriorPower.ιMulti R 0 v := by
  simp [exteriorFlagVector]

/-- Image of `exteriorFlagVector R (r + 1) v` under `flagSpaceSuccEquiv`. -/
@[simp]
theorem flagSpaceSuccEquiv_exteriorFlagVector (r : ℕ) (v : Fin (r + 1) → M) :
    flagSpaceSuccEquiv R M r (exteriorFlagVector R (r + 1) v) =
      exteriorFlagVector R r (v ∘ Fin.castSucc) ⊗ₜ[R]
        _root_.exteriorPower.ιMulti R (r + 1) v := by
  rw [exteriorFlagVector, flagSpaceSuccEquiv_tprod]
  rfl

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

/-- `exteriorFlagMap d f` acts factorwise on pure tensors in `FlagSpace R M d`. -/
@[simp]
theorem exteriorFlagMap_tprod (d : ℕ) (f : M →ₗ[R] N)
    (x : ∀ i : Fin (d + 1), ⋀[R]^(i : ℕ) M) :
    exteriorFlagMap d f (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R fun i : Fin (d + 1) ↦ _root_.exteriorPower.map i f (x i) := by
  simp [exteriorFlagMap]

/-- Evaluation of `exteriorFlagMap 0 f` under `flagSpaceZeroEquiv`. -/
@[simp]
theorem flagSpaceZeroEquiv_exteriorFlagMap_apply (f : M →ₗ[R] N) (w : FlagSpace R M 0) :
    flagSpaceZeroEquiv R N (exteriorFlagMap 0 f w) =
      _root_.exteriorPower.map 0 f (flagSpaceZeroEquiv R M w) := by
  induction w using PiTensorProduct.induction_on with
  | smul_tprod r x => simp
  | add x y hx hy => simp [hx, hy]

/-- Evaluation of `exteriorFlagMap (r + 1) f` under `flagSpaceSuccEquiv`. -/
@[simp]
theorem flagSpaceSuccEquiv_exteriorFlagMap_apply (r : ℕ) (f : M →ₗ[R] N)
    (w : FlagSpace R M (r + 1)) :
    flagSpaceSuccEquiv R N r (exteriorFlagMap (r + 1) f w) =
      TensorProduct.map (exteriorFlagMap r f) (_root_.exteriorPower.map (r + 1) f)
        (flagSpaceSuccEquiv R M r w) := by
  induction w using PiTensorProduct.induction_on with
  | smul_tprod r' x => simp
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
  unfold exteriorFlagMap
  simp only [_root_.exteriorPower.map_comp, PiTensorProduct.map_comp]

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
