/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.AdicValuation.LocalDegree
public import TauCeti.NumberTheory.LocalField.Norm.Basic

/-!
# Normalized absolute values under extension of adic completions

Let `R ⊆ B` be Dedekind domains with finite quotients and fraction fields `K ⊆ L`.
For height-one primes `w ∣ v`, the canonical map `K_v → L_w` raises the residue-cardinality
normalized absolute value to the local degree `[L_w : K_v]`. In particular, this map need
not preserve the norm.

The local degree is the product of the ramification index and inertia degree, as in
`IsDedekindDomain.HeightOneSpectrum.finrank_adicCompletion`; the residue cardinalities are
related by
`IsDedekindDomain.HeightOneSpectrum.natCard_residueField_adicCompletion_eq_pow_inertiaDeg`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.norm_adicCompletionExtension`: the normalized
  absolute value under the canonical extension of completions.
* `IsDedekindDomain.HeightOneSpectrum.adicCompletionExtensionEquiv`: when the local degree is
  `1`, the canonical map `K_v → L_w` is an isomorphism of topological `K_v`-algebras.
* `IsDedekindDomain.HeightOneSpectrum.norm_norm_adicCompletion`: the field norm preserves
  normalized absolute values. This uses `TauCeti.normalizedValuationWithZero_norm` together
  with the residue-cardinality formula.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II, §8.
-/

public section

open TauCeti IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped AdicCompletionExtension

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  [Ring.HasFiniteQuotients R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra R B]
  [Ring.HasFiniteQuotients B]
  {L : Type*} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]

/-- The normalized absolute value of the image in `L_w` is the normalized absolute value in
`K_v` raised to the local degree `[L_w : K_v]`. No Galois hypothesis is needed. -/
@[simp]
theorem norm_adicCompletionExtension
    (v : HeightOneSpectrum R) (w : HeightOneSpectrum B)
    [w.asIdeal.LiesOver v.asIdeal] (x : v.adicCompletion K) :
    ‖v.adicCompletionExtension K L w x‖ =
      ‖x‖ ^ Module.finrank (v.adicCompletion K) (w.adicCompletion L) := by
  have : Finite (R ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  have : Finite (B ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
  have : FaithfulSMul R B := FaithfulSMul.of_field_isFractionRing R B K L
  by_cases hx : x = 0
  · have := finite_of_valuativeExtension (v.adicCompletion K) (w.adicCompletion L)
    simp only [hx, map_zero, norm_zero,
      zero_pow (Module.finrank_pos (R := v.adicCompletion K) (M := w.adicCompletion L)).ne']
  have hcard : w.asIdeal.absNorm = v.asIdeal.absNorm ^ w.asIdeal.inertiaDeg R := by
    simpa only [natCard_residueField_adicCompletion_eq_absNorm] using
      natCard_residueField_adicCompletion_eq_pow_inertiaDeg (K := K) (L := L) v w
  rw [finrank_adicCompletion, FinitePlace.norm_def, FinitePlace.norm_def,
    valued_adicCompletionExtension, map_pow,
    Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot,
    WithZeroMulInt.toNNReal_neg_apply _ (by simpa using hx),
    WithZeroMulInt.toNNReal_neg_apply _ (by simpa using hx)]
  simp only [hcard, Nat.cast_pow, NNReal.coe_zpow,
    ← zpow_natCast, ← zpow_mul, Nat.cast_mul]
  congr 1
  ring

/-- The field norm between adic completions preserves the residue-cardinality normalized
absolute value. This differs from extension of scalars, which raises it to the local degree. -/
@[simp]
theorem norm_norm_adicCompletion
    (v : HeightOneSpectrum R) (w : HeightOneSpectrum B)
    [w.asIdeal.LiesOver v.asIdeal] (x : w.adicCompletion L) :
    ‖Algebra.norm (v.adicCompletion K) x‖ = ‖x‖ := by
  have : Finite (R ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  have : Finite (B ⧸ w.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient w.ne_bot
  have := finite_of_valuativeExtension (v.adicCompletion K) (w.adicCompletion L)
  have hval : Valued.v (Algebra.norm (v.adicCompletion K) x) =
      Valued.v x ^ w.asIdeal.inertiaDeg R := by
    simpa only [normalizedValuationWithZero_adicCompletion, inertiaDegree_def,
      finrank_residueField_adicCompletion, inv_pow, inv_inj] using
      normalizedValuationWithZero_norm (K := v.adicCompletion K) x
  by_cases hx : x = 0
  · simp [hx]
  have hcard : w.asIdeal.absNorm = v.asIdeal.absNorm ^ w.asIdeal.inertiaDeg R := by
    simpa only [natCard_residueField_adicCompletion_eq_absNorm] using
      natCard_residueField_adicCompletion_eq_pow_inertiaDeg (K := K) (L := L) v w
  rw [FinitePlace.norm_def, FinitePlace.norm_def, hval, map_pow,
    WithZeroMulInt.toNNReal_neg_apply _ (by simpa using hx),
    WithZeroMulInt.toNNReal_neg_apply _ (by simpa using hx)]
  simp only [hcard, Nat.cast_pow, NNReal.coe_zpow,
    ← zpow_natCast, ← zpow_mul, mul_comm]

/-- **Completions of local degree one.** When the local degree `[L_w : K_v]` is `1`, the canonical
map `K_v → L_w` is an isomorphism of topological `K_v`-algebras, for the algebra structure of the
`AdicCompletionExtension` scope. Its inverse is continuous because the map preserves the normalized
absolute value (`norm_adicCompletionExtension` with exponent `1`). -/
noncomputable def adicCompletionExtensionEquiv
    (v : HeightOneSpectrum R) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]
    (h : Module.finrank (v.adicCompletion K) (w.adicCompletion L) = 1) :
    v.adicCompletion K ≃A[v.adicCompletion K] w.adicCompletion L where
  toAlgEquiv := AlgEquiv.ofRingEquiv
    (f := .ofBijective _ (adicCompletionExtension_bijective_of_finrank_eq_one v w h))
    fun x ↦ by simp
  continuous_toFun := continuous_adicCompletionExtension K L v w
  continuous_invFun := by
    let f := RingEquiv.ofBijective _ (adicCompletionExtension_bijective_of_finrank_eq_one v w h)
    have hiso : Isometry f := AddMonoidHomClass.isometry_of_norm f fun x ↦ by
      rw [RingEquiv.ofBijective_apply, norm_adicCompletionExtension, h, pow_one]
    exact (hiso.right_inv f.right_inv).continuous

/-- `adicCompletionExtensionEquiv` is the canonical map `K_v → L_w`. -/
@[simp]
theorem coe_adicCompletionExtensionEquiv
    (v : HeightOneSpectrum R) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]
    (h : Module.finrank (v.adicCompletion K) (w.adicCompletion L) = 1) :
    ⇑(adicCompletionExtensionEquiv v w h) = v.adicCompletionExtension K L w := by
  funext x
  unfold adicCompletionExtensionEquiv
  exact (congr_fun (ContinuousAlgEquiv.coe_mk _ _ _) x).trans <|
    (AlgEquiv.ofRingEquiv_apply _ x).trans (RingEquiv.ofBijective_apply _ _ x)

/-- The inverse of `adicCompletionExtensionEquiv` sends the image of `x ∈ K_v` under the
canonical map `K_v → L_w` back to `x`. -/
@[simp]
theorem adicCompletionExtensionEquiv_symm_adicCompletionExtension
    (v : HeightOneSpectrum R) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]
    (h : Module.finrank (v.adicCompletion K) (w.adicCompletion L) = 1) (x : v.adicCompletion K) :
    (adicCompletionExtensionEquiv v w h).symm (v.adicCompletionExtension K L w x) = x := by
  rw [← coe_adicCompletionExtensionEquiv v w h, ContinuousAlgEquiv.symm_apply_apply]

end IsDedekindDomain.HeightOneSpectrum
