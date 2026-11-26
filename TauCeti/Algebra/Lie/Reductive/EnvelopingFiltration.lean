/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Reductive.EnvelopingCenter
public import TauCeti.Algebra.Lie.UniversalEnveloping.ComplementaryIdeals.Filtration

/-!
# PBW filtrations and the enveloping algebra of a reductive Lie algebra

For a finite-dimensional reductive Lie algebra `L` over a field `K` of characteristic zero, the
algebra equivalence `TauCeti.UniversalEnvelopingAlgebra.reductiveEnveloping K L :
U(L) ≃ₐ[K] Sym(z(L)) ⊗[K] U([L, L])` carries the PBW filtration of `U(L)` exactly onto the total
tensor filtration of the degree filtration of `Sym(z(L))` and the PBW filtration of `U([L, L])`,
in both directions. This is the complementary-ideal compatibility
`TauCeti.UniversalEnvelopingAlgebra.map_pbwFiltration_envelopingEquivOfIsCompl` for the
central/derived splitting.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.map_pbwFiltration_reductiveEnveloping`: the image of PBW
  degree `n` is total tensor degree `n`.
* `TauCeti.UniversalEnvelopingAlgebra.reductiveEnveloping_mem_tensorFiltration_iff` and
  `TauCeti.UniversalEnvelopingAlgebra.reductiveEnveloping_symm_mem_pbwFiltration_iff`: the forward
  and inverse compatibilities, elementwise.
-/

public section

open scoped TensorProduct

open LieAlgebra

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v

variable (K : Type u) (L : Type v) [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [HasCentralRadical K L]

local notation "UL" => _root_.UniversalEnvelopingAlgebra K L
local notation "UD" => _root_.UniversalEnvelopingAlgebra K (derivedSeries K L 1)
local notation "SZ" => SymmetricAlgebra K (center K L)
local notation "T" => tensorFiltration
  (TauCeti.Algebra.wordFiltration (SymmetricAlgebra.ι K (center K L)))
  (pbwFiltration K (derivedSeries K L 1))

/-- `reductiveEnveloping` carries PBW degree `n` of `U(L)` exactly onto total degree `n` of
`Sym(z(L)) ⊗[K] U([L, L])`. -/
theorem map_pbwFiltration_reductiveEnveloping (n : ℕ) :
    (pbwFiltration K L n).map (reductiveEnveloping K L).toAlgHom.toLinearMap = T n := by
  rw [reductiveEnveloping_def]
  exact map_pbwFiltration_envelopingEquivOfIsCompl K _ _ _ n

/-- Forward compatibility: `reductiveEnveloping` sends PBW degree `n` into total tensor degree
`n`, and an element whose image has total tensor degree `n` has PBW degree `n`. -/
theorem reductiveEnveloping_mem_tensorFiltration_iff {n : ℕ} {x : UL} :
    reductiveEnveloping K L x ∈ T n ↔ x ∈ pbwFiltration K L n := by
  rw [reductiveEnveloping_def]
  exact envelopingEquivOfIsCompl_mem_tensorFiltration_iff K _ _ _

/-- Inverse compatibility: the inverse of `reductiveEnveloping` sends total tensor degree `n` into
PBW degree `n`, and conversely. -/
theorem reductiveEnveloping_symm_mem_pbwFiltration_iff {n : ℕ} {t : SZ ⊗[K] UD} :
    (reductiveEnveloping K L).symm t ∈ pbwFiltration K L n ↔ t ∈ T n := by
  rw [reductiveEnveloping_def]
  exact envelopingEquivOfIsCompl_symm_mem_pbwFiltration_iff K _ _ _

end TauCeti.UniversalEnvelopingAlgebra
