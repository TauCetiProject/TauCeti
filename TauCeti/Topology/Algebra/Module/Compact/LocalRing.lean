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
local ring `R` gives `TauCeti.IsCompactModule.quotient_maximalIdeal_smul_top`.
-/

public section

namespace TauCeti.IsCompactModule

open IsLocalRing

variable {R M : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [CompactSpace R]
  [T2Space R] [IsLocalRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
  [TopologicalSpace M]

variable (hM : IsCompactModule R M)
include hM

/-- Over a compact Hausdorff noetherian local ring `R`, the reduction
`M ⧸ (maximalIdeal R • ⊤)` of a compact `R`-module `M` is a compact module over the discrete
residue field `R ⧸ maximalIdeal R`. -/
theorem quotient_maximalIdeal_smul_top :
    IsCompactModule (R ⧸ maximalIdeal R) (M ⧸ ((maximalIdeal R) • (⊤ : Submodule R M))) :=
  hM.quotient_smul_top_of_isAdic (isAdic_maximalIdeal R) (IsNoetherian.noetherian (maximalIdeal R))

end TauCeti.IsCompactModule
