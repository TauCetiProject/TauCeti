/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Nonarchimedean.RieszProjection.Splitting
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Intertwining

/-!
# Functoriality of Riesz splittings

A linear map intertwining two operators also intertwines their Riesz projectors at the same
scalar, even when the nilpotence bounds differ. It therefore carries the nilpotent spectral
summand and its complementary summand into the corresponding summands of the target. The
complementary inverses are intertwined as well. Continuity of the intertwiner is unnecessary.

In particular every bounded operator commuting with an operator commutes with its Riesz
projector and complementary inverse. These results allow commuting actions to restrict to the
spectral splitting, without choosing bases or assuming that the coefficient ring is a field.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7.
* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127**
  (1997), 417–479, Appendix A4.
-/

public section

open scoped ZeroAtInfty TauCeti.RingOpNorm

namespace ContinuousLinearMap.IsRieszProjection

variable {I R : Type*} [TopologicalSpace I]
  [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  {u E : C₀(I, R) →L[R] C₀(I, R)} {a : R} {h : ℕ}

/-- A bounded operator commuting with `u` commutes with every Riesz projector of `u`. -/
theorem commute_of_commute (hE : IsRieszProjection u a h E)
    {w : C₀(I, R) →L[R] C₀(I, R)} (hw : Commute w u) : Commute w E :=
  (isRieszProjection_def.mp hE).commute_of_commute <| by
    rw [Commute, SemiconjBy]; ext x : 1
    have hwu : w (u x) = u (w x) := congr($(hw.eq) x)
    simp [mul_apply_eq_comp, hwu]

/-- A bounded operator commuting with `u` commutes with the complementary inverse of any
Riesz projector of `u`. -/
theorem commute_inverse_of_commute (hE : IsRieszProjection u a h E)
    {w : C₀(I, R) →L[R] C₀(I, R)} (hw : Commute w u) :
    Commute w (isRieszProjection_def.mp hE).inverse :=
  (isRieszProjection_def.mp hE).commute_inverse_of_commute <| by
    rw [Commute, SemiconjBy]; ext x : 1
    have hwu : w (u x) = u (w x) := congr($(hw.eq) x)
    simp [mul_apply_eq_comp, hwu]

end ContinuousLinearMap.IsRieszProjection
