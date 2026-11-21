/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.Compact.Adic
public import TauCeti.Topology.Algebra.Ring.Compact

/-!
# Compact modules over compact Hausdorff noetherian local rings

Specializing `TauCeti/Topology/Algebra/Module/Compact/Adic.lean` via
`IsLocalRing.isAdic_maximalIdeal` to `I = maximalIdeal R` over a compact Hausdorff noetherian
local ring `R` gives `self_of_isLocalRing`, `quotient_maximalIdeal`,
`exists_maximalIdeal_pow_smul_top_le`, `isAdicComplete_maximalIdeal`, and
`quotient_maximalIdeal_smul_top`.
-/

public section

namespace TauCeti.IsCompactModule

open IsLocalRing

variable {R M : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]
  [T2Space R] [IsLocalRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
  [TopologicalSpace M]

variable (R) in
/-- A compact Hausdorff noetherian local ring is a compact module over itself. -/
theorem self_of_isLocalRing : IsCompactModule R R := self_of_isAdic (isAdic_maximalIdeal R)

variable (R) in
/-- Over a compact Hausdorff noetherian local ring `R`, the residue field `R ⧸ maximalIdeal R` with
its quotient topology is a compact `R`-module. -/
theorem quotient_maximalIdeal : IsCompactModule R (R ⧸ maximalIdeal R) :=
  quotient_of_isAdic (isAdic_maximalIdeal R)

variable (hM : IsCompactModule R M)
include hM

/-- **Every open submodule of a compact module over a compact Hausdorff noetherian local ring
contains `m ^ n • ⊤` for some `n`.** -/
theorem exists_maximalIdeal_pow_smul_top_le (N : Submodule R M) (hN : IsOpen (N : Set M)) :
    ∃ n : ℕ, (maximalIdeal R ^ n) • (⊤ : Submodule R M) ≤ N :=
  hM.exists_pow_smul_top_le (isAdic_maximalIdeal R) N hN

/-- **Every compact module over a compact Hausdorff noetherian local ring is `m`-adically complete
and separated.** -/
theorem isAdicComplete_maximalIdeal : IsAdicComplete (maximalIdeal R) M :=
  hM.isAdicComplete_of_isAdic (isAdic_maximalIdeal R) (IsNoetherian.noetherian (maximalIdeal R))

/-- Over a compact Hausdorff noetherian local ring `R`, the reduction
`M ⧸ (maximalIdeal R • ⊤)` of a compact `R`-module `M` is a compact module over the discrete
residue field `R ⧸ maximalIdeal R`. -/
theorem quotient_maximalIdeal_smul_top :
    IsCompactModule (R ⧸ maximalIdeal R) (M ⧸ ((maximalIdeal R) • (⊤ : Submodule R M))) :=
  hM.quotient_smul_top_of_isAdic (isAdic_maximalIdeal R) (IsNoetherian.noetherian (maximalIdeal R))

end TauCeti.IsCompactModule
