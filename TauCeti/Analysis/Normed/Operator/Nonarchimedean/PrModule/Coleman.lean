/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.PrModule.Basic
public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.Coleman
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Intertwining

/-!
# Polynomial spectral mapping on modules with property (Pr)

For a row-compact endomorphism `u` of a module with property (Pr), and a polynomial `B` with
zero constant coefficient, the Fredholm series of `B(u)` is Coleman's transform of that of `u`:

`(Polynomial.aeval u B).charPowerSeries = B.colemanDSeries u.charPowerSeries`.

This transports `ContinuousLinearMap.IsRowCompact.charPowerSeries_matrixCoeff_aeval` from model
spaces through an arbitrary continuous linear retract presentation. The zero constant
coefficient ensures that evaluating `B` commutes with extending the operator along the retract.
Presentation independence then gives the intrinsic identity, without choosing a complement or
an orthonormal basis of the module. The result applies over coefficient rings with nilpotents.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A3.
-/

public section

open ZeroAtInftyContinuousMap TauCeti
open scoped ZeroAtInfty

namespace ContinuousLinearMap

variable {R M : Type*} [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R]
  [CompleteSpace R] [TauCeti.NormedRing.IsTate R]
  [SeminormedAddCommGroup M] [Module R M] [ContinuousConstSMul R M]

/-- **Polynomial spectral mapping on (Pr) modules.** For a row-compact endomorphism `u` and a
polynomial `B` with `B(0) = 0`, the Fredholm series of `B(u)` is Coleman's transform of the
Fredholm series of `u`. -/
theorem IsPrCompact.charPowerSeries_aeval {u : M →L[R] M} (hu : u.IsPrCompact) {B : Polynomial R}
    (hB0 : B.coeff 0 = 0) :
    (Polynomial.aeval u B).charPowerSeries = B.colemanDSeries u.charPowerSeries := by
  classical
  obtain ⟨J, _, _, i, r, hri⟩ := (hasPr_def R M).1 hu.hasPr_source
  rw [(hu.aeval hB0).charPowerSeries_eq hri, hu.charPowerSeries_eq hri,
    ← aeval_comp_comp_of_retract hri u hB0]
  exact (hu.isRowCompact_comp i r).charPowerSeries_matrixCoeff_aeval hB0

end ContinuousLinearMap
