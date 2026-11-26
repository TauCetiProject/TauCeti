/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.LinearAlgebra.Matrix.Action
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.LinearAlgebra.Submodule.CardFinrank

import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# The action of `GL_n(k)` on the subspaces of `kⁿ`

The group `GL_n(k)` of a field `k` acts on the subspaces of `kⁿ` by the pointwise action,
`g • W = {g v : v ∈ W}`. This action preserves the dimension, and it is transitive on the
subspaces of each fixed dimension: an isomorphism `W ≃ W'` extends to an automorphism of `kⁿ`
(`Submodule.exists_linearEquiv_restrict_eq`). By the orbit-stabilizer theorem the index of the
stabilizer of `W` is the number of subspaces of the dimension of `W`, which over a finite field
with `q` elements is the Gaussian binomial coefficient `[n, dim W]_q`
(`TauCeti.card_submodule_finrank_eq_gaussianBinomial`).

## Main results

* `Matrix.GeneralLinearGroup.finrank_smul_submodule`: `dim (g • W) = dim W`.
* `Matrix.GeneralLinearGroup.exists_smul_eq_of_finrank_eq`: subspaces of the same dimension are
  carried to one another by some `g ∈ GL_n(k)`.
* `Matrix.GeneralLinearGroup.orbit_submodule_eq`: the orbit of `W` is the set of subspaces of the
  dimension of `W`.
* `Matrix.GeneralLinearGroup.index_stabilizer_submodule_eq_gaussianBinomial`: over a field with
  `q` elements the stabilizer of `W` has index `[n, dim W]_q`.
-/

public section

open Module
open scoped Pointwise

namespace Matrix.GeneralLinearGroup

variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n]

/-- The pointwise action of `g ∈ GL_n(k)` on vectors is multiplication by its matrix. -/
theorem smul_eq_mulVec (g : GL n k) (v : n → k) : g • v = (g : Matrix n n k) *ᵥ v :=
  (rfl)

/-- The action of `GL_n(k)` on the subspaces of `kⁿ` preserves the dimension. -/
theorem finrank_smul_submodule (g : GL n k) (W : Submodule k (n → k)) :
    finrank k ↥(g • W) = finrank k W := by
  have hinj : Function.Injective (DistribSMul.toLinearMap k (n → k) g) :=
    MulAction.injective g
  exact (Submodule.equivMapOfInjective _ hinj W).finrank_eq.symm

/-- **`GL_n(k)` acts transitively on the subspaces of `kⁿ` of each dimension.** Two subspaces of
the same dimension are carried to one another by some invertible matrix. -/
theorem exists_smul_eq_of_finrank_eq {W W' : Submodule k (n → k)}
    (h : finrank k W = finrank k W') : ∃ g : GL n k, g • W = W' := by
  obtain ⟨f, hf⟩ := W.exists_linearEquiv_restrict_eq (LinearEquiv.ofFinrankEq W W' h)
  set g : GL n k := toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv f)
  have hg (v : n → k) : g • v = f v := by
    rw [smul_eq_mulVec, ← mulVecLin_apply, ← coe_toLin, MulEquiv.apply_symm_apply,
      LinearMap.GeneralLinearGroup.coe_ofLinearEquiv]
  refine ⟨g, le_antisymm ?_ fun x hx ↦ ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    rw [DistribSMul.toLinearMap_apply, ← Units.smul_def, hg, ← hf ⟨v, hv⟩]
    exact Submodule.coe_mem _
  · set y : W := (LinearEquiv.ofFinrankEq W W' h).symm ⟨x, hx⟩
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr ⟨y, y.property, ?_⟩
    rw [hg, ← hf y, LinearEquiv.apply_symm_apply]

/-- The orbit of a subspace `W` of `kⁿ` under `GL_n(k)` consists of the subspaces of the dimension
of `W`. -/
theorem orbit_submodule_eq (W : Submodule k (n → k)) :
    MulAction.orbit (GL n k) W = {W' : Submodule k (n → k) | finrank k W' = finrank k W} := by
  ext W'
  refine ⟨?_, fun h ↦ exists_smul_eq_of_finrank_eq h.symm⟩
  rintro ⟨g, rfl⟩
  exact finrank_smul_submodule g W

/-- **The index of the stabilizer of a subspace** `W` of `kⁿ` in `GL_n(k)` is the number of
subspaces of the dimension of `W`. -/
theorem index_stabilizer_submodule_eq_natCard (W : Submodule k (n → k)) :
    (MulAction.stabilizer (GL n k) W).index =
      Nat.card {W' : Submodule k (n → k) // finrank k W' = finrank k W} := by
  rw [MulAction.index_stabilizer, orbit_submodule_eq, ← Nat.card_coe_set_eq, Set.coe_ofPred]

/-- **The index of the stabilizer of a subspace over a finite field.** If `k` has `q` elements,
the stabilizer of a subspace `W` of `kⁿ` has index the Gaussian binomial coefficient
`[n, dim W]_q`. -/
theorem index_stabilizer_submodule_eq_gaussianBinomial [Fintype k] (W : Submodule k (n → k)) :
    (MulAction.stabilizer (GL n k) W).index =
      TauCeti.gaussianBinomial (Fintype.card k) (Fintype.card n) (finrank k W) := by
  rw [index_stabilizer_submodule_eq_natCard, TauCeti.card_submodule_finrank_eq_gaussianBinomial,
    finrank_fintype_fun_eq_card]

end Matrix.GeneralLinearGroup
