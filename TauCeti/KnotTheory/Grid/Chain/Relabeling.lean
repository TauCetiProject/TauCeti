/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Chain.Basic

/-!
# Row and column relabelings of grid chains

Grid moves relabel the cyclic row or column labels of a grid diagram.  The diagram API already
has the corresponding operations on grid states, but the free chain module also needs the induced
linear equivalences on generators.  This file supplies those equivalences for arbitrary
permutations; cyclic relabelings are the special case used by `GridDiagram.IsMove`.

The equivalences are defined by transporting the domain of a finitely supported function.  Thus
they do not introduce a second chain representation, and their action on generators and
coefficients is exposed by simp lemmas.  No differential is used here: rectangle transport and
the resulting chain-map theorem belong to the next stage of the invariance construction.

## Main definitions

* `TauCeti.GridChain.relabelRowsEquiv`: the linear equivalence induced by relabeling rows.
* `TauCeti.GridChain.relabelColumnsEquiv`: the linear equivalence induced by relabeling columns.

## Main results

* `TauCeti.GridChain.relabelRowsEquiv_single` and
  `TauCeti.GridChain.relabelColumnsEquiv_single`: the action on a basis generator.
* `TauCeti.GridChain.relabelRowsEquiv_apply` and
  `TauCeti.GridChain.relabelColumnsEquiv_apply`: the coefficient formulas.
* `TauCeti.GridChain.relabelRowsEquiv_symm` and
  `TauCeti.GridChain.relabelColumnsEquiv_symm`: inverse relabelings use inverse permutations.

## References

This is a prerequisite for `TauCetiRoadmap/CombinatorialHeegaardFloer/README.md`, Lane G.5,
"Invariance over 𝔽₂. Grid moves = commutation + (de)stabilization".  The relabeling convention
follows Ozsváth--Stipsicz--Szabó, *Grid Homology for Knots and Links*, Chapter 3.
-/

public section

namespace TauCeti

namespace GridChain

variable {R : Type*} [Semiring R] {n : ℕ}

private def relabelRowsStateEquiv (ρ : Equiv.Perm (Fin n)) : GridState n ≃ GridState n where
  toFun := GridState.relabelRows ρ
  invFun := GridState.relabelRows ρ.symm
  left_inv := by
    intro x
    ext c
    simp
  right_inv := by
    intro x
    ext c
    simp

private def relabelColumnsStateEquiv (κ : Equiv.Perm (Fin n)) : GridState n ≃ GridState n where
  toFun := GridState.relabelColumns κ
  invFun := GridState.relabelColumns κ.symm
  left_inv := by
    intro x
    ext c
    simp
  right_inv := by
    intro x
    ext c
    simp

/-- The linear equivalence on grid chains induced by a permutation of the row labels. -/
noncomputable def relabelRowsEquiv (ρ : Equiv.Perm (Fin n)) :
    GridChain R n ≃ₗ[R] GridChain R n :=
  Finsupp.domLCongr (relabelRowsStateEquiv ρ)

/-- The linear equivalence on grid chains induced by a permutation of the column labels. -/
noncomputable def relabelColumnsEquiv (κ : Equiv.Perm (Fin n)) :
    GridChain R n ≃ₗ[R] GridChain R n :=
  Finsupp.domLCongr (relabelColumnsStateEquiv κ)

/-- Row relabeling sends a basis generator to the correspondingly relabeled generator. -/
@[simp]
theorem relabelRowsEquiv_single (ρ : Equiv.Perm (Fin n)) (x : GridState n) (a : R) :
    relabelRowsEquiv ρ (Finsupp.single x a) =
      Finsupp.single (x.relabelRows ρ) a := by
  rw [relabelRowsEquiv]
  exact Finsupp.domLCongr_single _ x a

/-- Column relabeling sends a basis generator to the correspondingly relabeled generator. -/
@[simp]
theorem relabelColumnsEquiv_single (κ : Equiv.Perm (Fin n)) (x : GridState n) (a : R) :
    relabelColumnsEquiv κ (Finsupp.single x a) =
      Finsupp.single (x.relabelColumns κ) a := by
  rw [relabelColumnsEquiv]
  exact Finsupp.domLCongr_single _ x a

/-- The coefficient at a state after row relabeling is read at the inverse-relabelled state. -/
@[simp]
theorem relabelRowsEquiv_apply (ρ : Equiv.Perm (Fin n)) (f : GridChain R n)
    (y : GridState n) :
    relabelRowsEquiv ρ f y = f (y.relabelRows ρ.symm) := by
  rw [relabelRowsEquiv, Finsupp.domLCongr_apply]
  exact Finsupp.equivMapDomain_apply _ _ _

/-- The coefficient at a state after column relabeling is read at the inverse-relabelled state. -/
@[simp]
theorem relabelColumnsEquiv_apply (κ : Equiv.Perm (Fin n)) (f : GridChain R n)
    (y : GridState n) :
    relabelColumnsEquiv κ f y = f (y.relabelColumns κ.symm) := by
  rw [relabelColumnsEquiv, Finsupp.domLCongr_apply]
  exact Finsupp.equivMapDomain_apply _ _ _

/-- The inverse of a row relabeling is induced by the inverse row permutation. -/
@[simp]
theorem relabelRowsEquiv_symm (ρ : Equiv.Perm (Fin n)) :
    (relabelRowsEquiv (R := R) ρ).symm = relabelRowsEquiv ρ.symm := by
  unfold relabelRowsEquiv
  rw [Finsupp.domLCongr_symm]
  rfl

/-- The inverse of a column relabeling is induced by the inverse column permutation. -/
@[simp]
theorem relabelColumnsEquiv_symm (κ : Equiv.Perm (Fin n)) :
    (relabelColumnsEquiv (R := R) κ).symm = relabelColumnsEquiv κ.symm := by
  unfold relabelColumnsEquiv
  rw [Finsupp.domLCongr_symm]
  rfl

/-- The inverse row relabeling has the expected coefficient formula. -/
@[simp]
theorem relabelRowsEquiv_symm_apply (ρ : Equiv.Perm (Fin n)) (f : GridChain R n)
    (y : GridState n) :
    (relabelRowsEquiv ρ).symm f y = f (y.relabelRows ρ) := by
  rw [relabelRowsEquiv_symm]
  simp

/-- The inverse column relabeling has the expected coefficient formula. -/
@[simp]
theorem relabelColumnsEquiv_symm_apply (κ : Equiv.Perm (Fin n)) (f : GridChain R n)
    (y : GridState n) :
    (relabelColumnsEquiv κ).symm f y = f (y.relabelColumns κ) := by
  rw [relabelColumnsEquiv_symm]
  simp

/-- Relabeling by the identity row permutation is the identity linear equivalence. -/
@[simp]
theorem relabelRowsEquiv_refl :
    relabelRowsEquiv (R := R) (Equiv.refl (Fin n)) = LinearEquiv.refl R _ := by
  apply LinearEquiv.ext
  intro f
  ext y
  simp

/-- Relabeling by the identity column permutation is the identity linear equivalence. -/
@[simp]
theorem relabelColumnsEquiv_refl :
    relabelColumnsEquiv (R := R) (Equiv.refl (Fin n)) = LinearEquiv.refl R _ := by
  apply LinearEquiv.ext
  intro f
  ext y
  simp

/-- Row relabeling equivalences compose in the same order as state relabelings. -/
theorem relabelRowsEquiv_trans_apply (ρ σ : Equiv.Perm (Fin n)) (f : GridChain R n) :
    relabelRowsEquiv σ (relabelRowsEquiv ρ f) =
      relabelRowsEquiv (ρ.trans σ) f := by
  ext y
  simp [GridState.relabelRows_relabelRows]

/-- Column relabeling equivalences compose in the same order as state relabelings. -/
theorem relabelColumnsEquiv_trans_apply (κ τ : Equiv.Perm (Fin n)) (f : GridChain R n) :
    relabelColumnsEquiv τ (relabelColumnsEquiv κ f) =
      relabelColumnsEquiv (κ.trans τ) f := by
  ext y
  simp [GridState.relabelColumns_relabelColumns]

end GridChain

end TauCeti
