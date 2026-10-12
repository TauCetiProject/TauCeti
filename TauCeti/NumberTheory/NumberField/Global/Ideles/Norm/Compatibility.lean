/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Relative
public import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Norm

/-!
# Relative norms preserve the global idele norm

For an extension of number fields `L/K`, the normalized absolute value of a local norm is
that of its argument. Consequently, regrouping all the local factors by their place below
shows `‖N_{L/K}(x)‖_K = ‖x‖_L` for every idele, and hence for every idele class.

This is distinct from extension of scalars: extension raises the global norm to `[L : K]`,
whereas the relative norm preserves it. Neither identity needs a Galois hypothesis.

The proof uses the component formulas of `ideleNormMap`, the finite-completion norm identity
`IsDedekindDomain.HeightOneSpectrum.norm_norm_adicCompletion`, and the archimedean identity
`NumberField.InfinitePlace.completionNormalizedAbsValue_norm`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, §8 and Chapter VI, §1.
-/

public section
noncomputable section

open IsDedekindDomain NumberField NumberField.InfinitePlace
open scoped AdicCompletionExtension NumberField.LiesOver

namespace TauCeti.GlobalNumberFields

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The normalized absolute value of a finite coordinate of a relative idele norm is the
product of the normalized absolute values at all places above it. -/
theorem norm_ideleFiniteCoord_ideleNormMap (v : HeightOneSpectrum (𝓞 K))
    (x : IdeleGroup (𝓞 L) L) :
    ‖(v.ideleFiniteCoord (ideleNormMap K L x) : v.adicCompletion K)‖ =
      ∏ᶠ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
        ‖(w.1.ideleFiniteCoord x : w.1.adicCompletion L)‖ := by
  classical
  let _ : Fintype {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal} :=
    Fintype.ofFinite _
  rw [ideleFiniteCoord_ideleNormMap, finprod_eq_prod_of_fintype,
    Units.coe_prod, norm_prod, finprod_eq_prod_of_fintype]
  simp only [Algebra.coe_normUnits, HeightOneSpectrum.norm_norm_adicCompletion]

/-- The normalized absolute value of an infinite coordinate of a relative idele norm is the
product of the normalized absolute values at all places above it. -/
theorem completionNormalizedAbsValue_ideleInfiniteCoord_ideleNormMap (v : InfinitePlace K)
    (x : IdeleGroup (𝓞 L) L) :
    completionNormalizedAbsValue v (v.ideleInfiniteCoord (ideleNormMap K L x)) =
      ∏ᶠ w : {w : InfinitePlace L // w.LiesOver v},
        completionNormalizedAbsValue w.1 (w.1.ideleInfiniteCoord x) := by
  classical
  rw [ideleInfiniteCoord_ideleNormMap, finprod_eq_prod_of_fintype,
    Units.coe_prod, map_prod, finprod_eq_prod_of_fintype]
  simp only [Algebra.coe_normUnits, completionNormalizedAbsValue_norm]

private theorem prod_infiniteFactors_ideleNormMap (x : IdeleGroup (𝓞 L) L) :
    (∏ v, completionNormalizedAbsValue v (v.ideleInfiniteCoord (ideleNormMap K L x))) =
      ∏ w, completionNormalizedAbsValue w (w.ideleInfiniteCoord x) := by
  classical
  rw [← Fintype.prod_fiberwise (fun w : InfinitePlace L ↦ w.comap (algebraMap K L))]
  apply Finset.prod_congr rfl
  intro v _
  rw [completionNormalizedAbsValue_ideleInfiniteCoord_ideleNormMap]
  let e : {w : InfinitePlace L // w.comap (algebraMap K L) = v} ≃
      {w : InfinitePlace L // w.LiesOver v} := Equiv.subtypeEquivRight fun w ↦
    ⟨fun hw ↦ hw ▸ inferInstance, fun _ ↦ LiesOver.comap_eq w v⟩
  rw [finprod_eq_prod_of_fintype]
  exact (Fintype.prod_equiv e _ _ fun _ ↦ rfl).symm

private theorem prod_finiteFactors_ideleNormMap (x : IdeleGroup (𝓞 L) L) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 K),
      ‖(v.ideleFiniteCoord (ideleNormMap K L x) : v.adicCompletion K)‖) =
      ∏ᶠ w : HeightOneSpectrum (𝓞 L), ‖(w.ideleFiniteCoord x : w.adicCompletion L)‖ := by
  rw [← TauCeti.finprod_fiberwise (HeightOneSpectrum.under (𝓞 K)) _
    (hasFiniteMulSupport_norm_ideleFiniteCoord x)]
  apply finprod_congr
  intro v
  rw [norm_ideleFiniteCoord_ideleNormMap]
  let e : {w : HeightOneSpectrum (𝓞 L) // w.under (𝓞 K) = v} ≃
      {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal} :=
    Equiv.subtypeEquivRight fun w ↦
      ⟨fun hw ↦ hw ▸ inferInstance,
        fun hw ↦ HeightOneSpectrum.asIdeal_injective hw.over.symm⟩
  exact (finprod_comp_equiv e).symm

/-- The relative norm of ideles preserves their global norm, with residue-cardinality
normalization at finite places and squared absolute values at complex places. -/
@[simp]
theorem ideleNorm_ideleNormMap (x : IdeleGroup (𝓞 L) L) :
    ideleNorm (ideleNormMap K L x) = ideleNorm x := by
  apply Units.ext
  apply NNReal.eq
  simp only [coe_ideleNorm]
  rw [prod_infiniteFactors_ideleNormMap, prod_finiteFactors_ideleNormMap]

/-- The relative norm of idele classes preserves their global norm. In particular it sends
norm-one classes to norm-one classes. -/
@[simp]
theorem ideleClassNorm_ideleClassNormMap (x : IdeleClassGroup (𝓞 L) L) :
    ideleClassNorm (ideleClassNormMap K L x) = ideleClassNorm x := by
  induction x using QuotientGroup.induction_on with
  | H x => simp

end TauCeti.GlobalNumberFields
