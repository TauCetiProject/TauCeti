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

variable {I J R : Type*} [TopologicalSpace I] [TopologicalSpace J]
  [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  {u E : C₀(I, R) →L[R] C₀(I, R)} {v F : C₀(J, R) →L[R] C₀(J, R)}
  {a : R} {h k : ℕ}

/-- An intertwiner carries Riesz projectors at the same scalar to one another. The two
nilpotence bounds may differ, and the intertwiner need not be continuous. -/
theorem semiconj (hE : IsRieszProjection u a h E) (hF : IsRieszProjection v a k F)
    (f : C₀(I, R) →ₗ[R] C₀(J, R)) (hf : Function.Semiconj f u v) :
    Function.Semiconj f E F :=
  (isRieszProjection_def.mp hE).semiconj (isRieszProjection_def.mp hF) f (hf.one_sub_smul a)

/-- An intertwiner sends the nilpotent spectral summand into the corresponding summand. -/
theorem mapsTo_range_of_semiconj (hE : IsRieszProjection u a h E)
    (hF : IsRieszProjection v a k F) (f : C₀(I, R) →ₗ[R] C₀(J, R))
    (hf : Function.Semiconj f u v) : Set.MapsTo f E.range F.range :=
  (isRieszProjection_def.mp hE).mapsTo_range_of_semiconj (isRieszProjection_def.mp hF) f
    (hf.one_sub_smul a)

/-- An intertwiner sends the complementary spectral summand into the corresponding summand. -/
theorem mapsTo_ker_of_semiconj (hE : IsRieszProjection u a h E)
    (hF : IsRieszProjection v a k F) (f : C₀(I, R) →ₗ[R] C₀(J, R))
    (hf : Function.Semiconj f u v) : Set.MapsTo f E.ker F.ker :=
  (isRieszProjection_def.mp hE).mapsTo_ker_of_semiconj (isRieszProjection_def.mp hF) f
    (hf.one_sub_smul a)

/-- Intertwiners also carry the complementary inverses of the spectral operators to one
another. This includes order zero, when the complementary inverse is the full inverse. -/
theorem semiconj_inverse (hE : IsRieszProjection u a h E) (hF : IsRieszProjection v a k F)
    (f : C₀(I, R) →ₗ[R] C₀(J, R)) (hf : Function.Semiconj f u v) :
    Function.Semiconj f (isRieszProjection_def.mp hE).inverse
      (isRieszProjection_def.mp hF).inverse :=
  (isRieszProjection_def.mp hE).semiconj_inverse (isRieszProjection_def.mp hF) f (hf.one_sub_smul a)

/-- A bounded operator commuting with `u` commutes with every Riesz projector of `u`. -/
theorem commute_of_commute (hE : IsRieszProjection u a h E)
    {w : C₀(I, R) →L[R] C₀(I, R)} (hw : Commute w u) : Commute w E :=
  ext fun x ↦ hE.semiconj hE w.toLinearMap (fun y ↦ congr($(hw.eq) y)) x

/-- A bounded operator commuting with `u` commutes with the complementary inverse of any
Riesz projector of `u`. -/
theorem commute_inverse_of_commute (hE : IsRieszProjection u a h E)
    {w : C₀(I, R) →L[R] C₀(I, R)} (hw : Commute w u) :
    Commute w (isRieszProjection_def.mp hE).inverse :=
  ext fun x ↦ hE.semiconj_inverse hE w.toLinearMap (fun y ↦ congr($(hw.eq) y)) x

end ContinuousLinearMap.IsRieszProjection
