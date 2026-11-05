/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Logarithm.Rescale
public import TauCeti.RingTheory.FormalGroup.TopNilpotentPoint.Ideal

/-!
# The integral logarithm on adic points

Let `F` be a formal group law over a complete Hausdorff linearly topologized ring `R`
without additive torsion. If `n + 1` divides `sⁿ` for every `n`, the logarithm of the
rescaled law `F^s` is integral. Evaluating it gives the additive equivalence
`FormalGroup.rescaleLogPointEquiv` from the points of `F^s` in an adic ideal `I` to `I`
with its ordinary addition. Its inverse evaluates the inverse integral series.
The equivalence preserves and reflects membership in every power of `I`.

This is a logarithm comparison on a specified neighbourhood: the divisibility condition
ensures integrality of both series, and membership in the adic ideal ensures convergence.
For an integer ring over `ℚ_p`, one can choose `s` with `v(s) ≥ v(p)/(p - 1)`.
This supplies the logarithm comparison used when rescaling small neighbourhoods of `F`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.6.4.
-/

public section

namespace FormalGroup

variable {R : Type*} [CommRing R] [HasUniqueDiv R] [UniformSpace R]
  [IsUniformAddGroup R] [CompleteSpace R] [T2Space R] [IsTopologicalRing R]
  [IsLinearTopology R R]
  (F : FormalGroup R) {s : R} (hs : ∀ n : ℕ, (n + 1 : R) ∣ s ^ n)
  (I : Ideal R) [Fact (IsAdic I)]

/-- Evaluation of the integral logarithm identifies the rescaled formal group on `I` with
ordinary addition on `I`. Its inverse evaluates the inverse integral logarithm. -/
noncomputable def rescaleLogPointEquiv : (F.rescale s).idealPointSubgroup I ≃+ I :=
  ((F.rescaleLogIso hs).toIdealPointEquiv I).trans (Ideal.additiveFormalGroupPointEquiv I)

/-- The logarithm equivalence evaluates the integral logarithm at the coordinate of the point. -/
theorem coe_rescaleLogPointEquiv (x : (F.rescale s).idealPointSubgroup I) :
    (F.rescaleLogPointEquiv hs I x : R) = PowerSeries.aeval x.val.hasEval (F.rescaleLog hs) := by
  rw [rescaleLogPointEquiv, AddEquiv.trans_apply, Ideal.coe_additiveFormalGroupPointEquiv,
    TauCeti.FormalGroupIso.coe_toIdealPointEquiv, rescaleLogIso_toHom]
  have h := (F.rescaleLogIso hs).toHom.hasSum_val_toTopNilpotentPointHom x.val
  simp only [rescaleLogIso_toHom, rescaleLogHom_toPowerSeries, smul_eq_mul] at h
  exact h.unique (by
    simpa only [smul_eq_mul] using
      (PowerSeries.hasSum_aeval (R := R) x.val.hasEval (F.rescaleLog hs)))

/-- The inverse logarithm equivalence evaluates the inverse integral series at its argument. -/
theorem val_rescaleLogPointEquiv_symm (x : I) :
    ((F.rescaleLogPointEquiv hs I).symm x).val.val =
      PowerSeries.aeval ((Fact.out : IsAdic I).isTopologicallyNilpotent_of_mem x.property)
        (F.rescaleLogIso hs).invHom.toPowerSeries := by
  rw [rescaleLogPointEquiv, AddEquiv.symm_trans_apply,
    TauCeti.FormalGroupIso.coe_toIdealPointEquiv_symm]
  have h := (F.rescaleLogIso hs).invHom.hasSum_val_toTopNilpotentPointHom
    ((Ideal.additiveFormalGroupPointEquiv (R := R) I).symm x).val
  exact h.unique (by
    simpa only [smul_eq_mul, Ideal.val_additiveFormalGroupPointEquiv_symm] using
      (PowerSeries.hasSum_aeval (R := R)
        ((Fact.out : IsAdic I).isTopologicallyNilpotent_of_mem x.property)
        (F.rescaleLogIso hs).invHom.toPowerSeries))

/-- The logarithm equivalence preserves and reflects membership in every ideal, in particular
every power of `I`. -/
@[simp]
theorem rescaleLogPointEquiv_mem_iff (x : (F.rescale s).idealPointSubgroup I) (J : Ideal R) :
    (F.rescaleLogPointEquiv hs I x : R) ∈ J ↔ x.val.val ∈ J := by
  simpa only [rescaleLogPointEquiv, AddEquiv.trans_apply,
    Ideal.coe_additiveFormalGroupPointEquiv,
    TauCeti.FormalGroupIso.coe_toIdealPointEquiv] using
    (F.rescaleLogIso hs).val_toTopNilpotentPointHom_mem_iff J x.val

end FormalGroup
