/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.GroupTheory.Index

/-!
# Torsion order under surjective linear maps

Let `R` be a commutative semiring, `r : R`, and `f : M →ₗ[R] N` a surjective `R`-linear map from a
finite `R`-module `M`. Multiplication by `r` on `M` and on `N` have kernels `M[r]` and `N[r]`, and
their images satisfy `f (r • M) = r • N`. Comparing indices of ranges via
`AddSubgroup.index_map_dvd` and `AddSubgroup.index_range` shows that `#N[r]` divides `#M[r]`, and in
particular `#N[r] ≤ #M[r]`.

## Main results

* `TauCeti.natCard_torsionBy_dvd_of_surjective`: `#N[r] ∣ #M[r]` for a surjective `R`-linear map
  `f : M →ₗ[R] N` from a finite `R`-module `M`.
* `TauCeti.natCard_torsionBy_le_of_surjective`: `#N[r] ≤ #M[r]` under the same hypotheses.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
`72fead102f663d5c7a407964a13dc0cf9d977207`, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/Lib/ClassField/GreenbergWiles/RelationsModL.lean` (`New.card_torsionBy_le_of_surjective`),
generalized from `ℕ`-torsion of finite abelian groups to `r`-torsion of finite modules over any
commutative semiring and strengthened from inequality to divisibility.
-/

@[expose] public section

namespace TauCeti

/-- Under a surjective `R`-linear map `f : M →ₗ[R] N` from a finite `R`-module `M`, the order of
the `r`-torsion of `N` divides the order of the `r`-torsion of `M`. -/
theorem natCard_torsionBy_dvd_of_surjective {R M N : Type*} [CommSemiring R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] [Finite M] (r : R) {f : M →ₗ[R] N}
    (hf : Function.Surjective f) :
    Nat.card (Submodule.torsionBy R N r) ∣ Nat.card (Submodule.torsionBy R M r) := by
  have : Finite N := .of_surjective f hf
  let mulM : M →+ M := (DistribSMul.toLinearMap R M r).toAddMonoidHom
  let mulN : N →+ N := (DistribSMul.toLinearMap R N r).toAddMonoidHom
  have hmap : mulM.range.map f.toAddMonoidHom = mulN.range := by
    ext y
    constructor
    · rintro ⟨x, ⟨m, rfl⟩, rfl⟩
      exact ⟨f m, by simp [mulM, mulN]⟩
    · rintro ⟨n, rfl⟩
      obtain ⟨m, rfl⟩ := hf n
      exact ⟨mulM m, ⟨m, rfl⟩, by simp [mulM, mulN]⟩
  have hkerM : Nat.card (Submodule.torsionBy R M r) = Nat.card mulM.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦ by simp [Submodule.mem_torsionBy_iff, mulM])
  have hkerN : Nat.card (Submodule.torsionBy R N r) = Nat.card mulN.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦ by simp [Submodule.mem_torsionBy_iff, mulN])
  rw [hkerN, hkerM, ← AddSubgroup.index_range, ← AddSubgroup.index_range, ← hmap]
  exact mulM.range.index_map_dvd hf

/-- Under a surjective `R`-linear map `f : M →ₗ[R] N` from a finite `R`-module `M`, the `r`-torsion
of `N` has at most as many elements as the `r`-torsion of `M`. -/
theorem natCard_torsionBy_le_of_surjective {R M N : Type*} [CommSemiring R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] [Finite M] (r : R) {f : M →ₗ[R] N}
    (hf : Function.Surjective f) :
    Nat.card (Submodule.torsionBy R N r) ≤ Nat.card (Submodule.torsionBy R M r) :=
  Nat.le_of_dvd Nat.card_pos (natCard_torsionBy_dvd_of_surjective r hf)

end TauCeti
