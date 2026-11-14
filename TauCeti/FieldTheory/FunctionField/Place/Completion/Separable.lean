/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.Completion.LocalDegree

/-!
# Separability of completed extensions of function fields

Let `P'` be a place of `F' / k'` lying over the place `P` of `F / k`, with `F' / F` integral. Under
`TauCeti.Place.completionExtensionAlgebra`, every element of `F'` separable over `F` maps to an
element of `F̂'_{P'}` separable over `F̂_P` (`TauCeti.Place.isSeparable_completionEmbedding`), and
if `F' / F` is separable with `F'_{P'} / F_P` finite, then `F̂'_{P'} / F̂_P` is separable
(`TauCeti.Place.isSeparable_completion`), with no assumption on the characteristic or on the
separability or finiteness of the residue fields. Together with
`TauCeti.Place.isIntegralClosure_completionIntegers` in
`TauCeti/FieldTheory/FunctionField/Place/Completion/LocalDegree.lean`, this supplies the local
hypotheses for the completed trace-dual, different, and discriminant theory.

Unlike `IsDedekindDomain.HeightOneSpectrum.adicCompletion_isSeparable` in
`TauCeti/NumberTheory/NumberField/LocalGlobal/Separable.lean` (which uses `CharZero`),
`isSeparable_completion` covers arbitrary characteristic via `isSeparable_completionEmbedding` and
`adjoin_range_completionEmbedding_eq_top`.

## References

* J.-P. Serre, *Local Fields*, GTM 67, Springer, 1979, Chapter II, §§2–3.
-/

public section

open Polynomial

namespace TauCeti.Place

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
  [Algebra k F] [Algebra k k'] [Algebra k' F'] [Algebra k F'] [Algebra F F']
  [IsScalarTower k k' F'] [IsScalarTower k F F']
  [Algebra.IsIntegral F F'] (P : Place k F) (P' : Place k' F')
  (hP : P'.restrict k F = P)

/-- Any element of `F'` that is separable over `F` maps to an element of `F̂'_{P'}` separable over
`F̂_P`. -/
theorem isSeparable_completionEmbedding {x : F'} (hx : IsSeparable F x) :
    letI := P.completionExtensionAlgebra P' hP
    IsSeparable P.Completion (P'.completionEmbedding x) := by
  let := P.completionExtensionAlgebra P' hP
  -- Map `minpoly F x` along `F → F̂_P`; it stays separable and vanishes at `x` in `F̂'_{P'}`.
  have hsep : ((minpoly F x).map P.completionEmbedding.toRingHom).Separable :=
    Polynomial.Separable.map hx
  have hcomp : (P.completionExtension P' hP).comp P.completionEmbedding.toRingHom =
      P'.completionEmbedding.toRingHom.comp (algebraMap F F') :=
    RingHom.ext (P.completionExtension_completionEmbedding P' hP)
  have h0 := congrArg P'.completionEmbedding.toRingHom (minpoly.aeval F x)
  rw [map_zero, aeval_def,
    hom_eval₂ (minpoly F x) (algebraMap F F') P'.completionEmbedding.toRingHom x, ← hcomp] at h0
  have haeval : aeval (P'.completionEmbedding x)
      ((minpoly F x).map P.completionEmbedding.toRingHom) = 0 := by
    rwa [aeval_def, eval₂_map, P.algebraMap_completionExtensionAlgebra P' hP]
  exact hsep.of_dvd (minpoly.dvd P.Completion (P'.completionEmbedding x) haeval)

/-- **Completion preserves separability of field extensions**: if `F' / F` is separable and the
residue extension at `P'` is finite, then `F̂'_{P'} / F̂_P` is separable. No assumption is made on
the characteristic or on the separability of the residue extension. -/
theorem isSeparable_completion
    [FiniteDimensional (P'.restrict k F).ResidueField P'.ResidueField]
    [Algebra.IsSeparable F F'] :
    letI := P.completionExtensionAlgebra P' hP
    Algebra.IsSeparable P.Completion P'.Completion := by
  let := P.completionExtensionAlgebra P' hP
  have hadj : Algebra.IsSeparable P.Completion
      (IntermediateField.adjoin P.Completion (Set.range P'.completionEmbedding)) := by
    rw [IntermediateField.isSeparable_adjoin_iff_isSeparable]
    rintro _ ⟨x, rfl⟩
    exact P.isSeparable_completionEmbedding P' hP (Algebra.IsSeparable.isSeparable F x)
  have htop := P.adjoin_range_completionEmbedding_eq_top P' hP
  exact AlgEquiv.Algebra.isSeparable
    ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv)

end TauCeti.Place
