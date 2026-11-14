/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.CompletedDerivation
public import TauCeti.Algebra.Lie.Current.Sugawara.Virasoro

/-!
# Sugawara implementation of completed vector fields and the degree derivation

Let `Û = lim_N U / I_N` be the completed enveloping algebra of the residue central extension of an
invariant symmetric bilinear form `Φ` on `L` at central value `a`
(`TauCeti.CurrentAlgebra.CompletedEnveloping`). Every Laurent vector field `h d/dt` extends to a
continuous derivation of `Û`
(`TauCeti.CurrentAlgebra.vectorFieldCompletedEnvelopingDerivation`).

This file connects those completed vector fields with normal ordering and the Segal--Sugawara
construction.

* **Degree of normally ordered and Segal--Sugawara modes.** Over any commutative ring `R`, the
  completed degree derivation `t d/dt` acts on each normally ordered summand of `:x y:_n` by
  multiplying by `n`, so by continuity it sends `:x y:_n` to `n • :x y:_n`
  (`TauCeti.CurrentAlgebra.vectorFieldCompletedEnvelopingDerivation_single_one_normalOrderedMode`).
  Over a field with `[FiniteDimensional K L] [LieAlgebra.IsKilling K L]`, summing over Killing-dual
  bases shows that `t d/dt` sends `Sₙ` to `n • Sₙ` at every level, including the critical level
  (`TauCeti.CurrentAlgebra.vectorFieldCompletedEnvelopingDerivation_single_one_sugawaraMode`).
* **Innerness of the Witt derivations.** When `Φ = c • κ_L`, both `ad(Sₘ)` and
  `(1 - 2 a c) • (-t^{m+1} d/dt)` are continuous derivations of `Û` taking the same value
  `-(1 - 2 a c) k z_{m+k}` on every current mode `z_k`, so they agree on all of `Û`
  (`TauCeti.CurrentAlgebra.innerDerivation_sugawaraMode_of_eq_smul_killingForm`). Away from the
  critical level (`1 - 2 a c ≠ 0`), dividing by `1 - 2 a c` identifies `ad(Lₘ)` with the completed
  Witt vector field `-t^{m+1} d/dt` (`TauCeti.CurrentAlgebra.innerDerivation_sugawaraVirasoro`).
* **The Sugawara degree element.** Specialising to `m = 0` defines `D_κ = -L₀`
  (`TauCeti.CurrentAlgebra.sugawaraDegree`), which is homogeneous of degree `0` under `t d/dt` and
  implements the completed degree derivation `t d/dt` as an inner derivation of `Û`
  (`TauCeti.CurrentAlgebra.innerDerivation_sugawaraDegree`). Consequently, away from the critical
  level, every element of the completed center `Z(Û)` is annihilated by `t d/dt`
  (`CurrentAlgebra.vectorFieldCompletedEnvelopingDerivation_single_one_eq_zero_of_mem_center`),
  in contrast to the critical level where `Sₙ ∈ Z(Û)` has degree `n`.

## Main definitions

* `TauCeti.CurrentAlgebra.sugawaraDegree`: the Sugawara degree element `D_κ = -L₀` in `Û`.

## Main results

* `TauCeti.CurrentAlgebra.vectorFieldCompletedEnvelopingDerivation_single_one_normalOrderedMode`,
  `TauCeti.CurrentAlgebra.vectorFieldCompletedEnvelopingDerivation_single_one_sugawaraMode`:
  `t d/dt` acts by `n` on `:x y:_n` and `Sₙ` at every level.
* `TauCeti.CurrentAlgebra.innerDerivation_sugawaraMode_of_eq_smul_killingForm`,
  `TauCeti.CurrentAlgebra.innerDerivation_sugawaraVirasoro`: `Sₘ` and `Lₘ` implement the completed
  Witt vector field `-t^{m+1} d/dt` on `Û`.
* `TauCeti.CurrentAlgebra.innerDerivation_sugawaraDegree`: away from the critical level, `D_κ`
  implements the completed degree derivation `t d/dt` as an inner derivation of `Û`.
* `TauCeti.CurrentAlgebra.vectorFieldCompletedEnvelopingDerivation_single_one_eq_zero_of_mem_center`
  — away from the critical level, `t d/dt` annihilates the completed center `Z(Û)`.

## References

* V. G. Kac, *Infinite-Dimensional Lie Algebras*, 3rd ed., §12.8.
* E. Frenkel, *Langlands Correspondence for Loop Groups*, §3.1.1 and §4.3.9.
-/

public section

noncomputable section

open scoped TensorProduct LaurentSeries
open LieAlgebra TauCeti.UniversalEnvelopingAlgebra
open LieAlgebra.ofTwoCocycle (centralElement envelopingι)

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti.CurrentAlgebra

/-! ### Degree of normally ordered modes over a commutative ring -/

section NormalOrder

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  {Φ : LinearMap.BilinForm R L} {hΦ : Φ.lieInvariant L} {hΦs : Φ.IsSymm} {a : R}

local notation "UK" => CentralQuotient R (centralElement (twoCocycleOfBilinear R L Φ hΦ hΦs)) a
local notation "Û" => CompletedEnveloping Φ hΦ hΦs a

/-- On the uncompleted level algebra, the degree derivation `t d/dt` multiplies every summand of
`:x y:_n` at any cut `p` by `n`. -/
private theorem vectorFieldEnvelopingDerivation_single_one_normalOrderedSummand
    (p n m : ℤ) (x y : L) :
    (vectorFieldEnvelopingDerivation Φ hΦ hΦs a (HahnSeries.single 1 1) : Module.End R UK)
        (normalOrderedSummand Φ hΦ hΦs a p n m x y) =
      n • normalOrderedSummand Φ hΦ hΦs a p n m x y := by
  simp only [normalOrderedSummand_apply]
  split_ifs <;>
  · rw [derivationLieAlgebra.leibniz,
      vectorFieldEnvelopingDerivation_single_one_envelopingι_single_tmul,
      vectorFieldEnvelopingDerivation_single_one_envelopingι_single_tmul,
      smul_mul_assoc, mul_smul_comm, ← add_smul]
    congr 1
    ring

/-- **The completed degree derivation multiplies `:x y:_n` by `n`**, over any commutative ring and
at every central value `a`. -/
theorem vectorFieldCompletedEnvelopingDerivation_single_one_normalOrderedMode
    (n : ℤ) (x y : L) :
    (vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a (HahnSeries.single 1 1) : Module.End R Û)
        (normalOrderedMode Φ hΦ hΦs a n x y) =
      n • normalOrderedMode Φ hΦ hΦs a n x y := by
  let D := (vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a (HahnSeries.single 1 1) :
    Module.End R Û)
  have hterm (m : ℤ) :
      D (toCompletedEnveloping Φ hΦ hΦs a (normalOrderedSummand Φ hΦ hΦs a 0 n m x y)) =
        n • toCompletedEnveloping Φ hΦ hΦs a (normalOrderedSummand Φ hΦ hΦs a 0 n m x y) := by
    simp only [D, coe_toCompletedEnveloping,
      vectorFieldCompletedEnvelopingDerivation_toLimQuotients,
      vectorFieldEnvelopingDerivation_single_one_normalOrderedSummand, map_zsmul]
  have h₁ := (hasSum_normalOrderedMode (Φ := Φ) (hΦ := hΦ) (hΦs := hΦs) (a := a) n x y).map
    D.toAddMonoidHom
    (continuous_vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a (HahnSeries.single 1 1))
  simp only [Function.comp_def, LinearMap.toAddMonoidHom_coe, hterm] at h₁
  have h₂ : HasSum (fun m ↦ n • toCompletedEnveloping Φ hΦ hΦs a
      (normalOrderedSummand Φ hΦ hΦs a 0 n m x y))
      (n • normalOrderedMode Φ hΦ hΦs a n x y) := by
    simpa only [← Int.cast_smul_eq_zsmul R, Algebra.smul_def] using
      (hasSum_normalOrderedMode n x y).mul_left (algebraMap R Û n)
  exact h₁.unique h₂

end NormalOrder

/-! ### Innerness of the Witt derivations and the Sugawara degree element -/

section Sugawara

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]
  (Φ : LinearMap.BilinForm K L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (a : K)

local notation "Û" => CompletedEnveloping Φ hΦ hΦs a
local notation "ιK[" x ", " m "]" =>
  toCompletedEnveloping Φ hΦ hΦs a
    (envelopingι (twoCocycleOfBilinear K L Φ hΦ hΦs) a (HahnSeries.single m (1 : K) ⊗ₜ[K] x))

/-- **The Sugawara degree element** `D_κ = -L₀` in `Û`, attached to `Φ = c • κ_L` away from the
critical level `1 - 2 a c = 0`. It acts on current modes by `[D_κ, z_k] = k z_k` and implements the
completed degree derivation `t d/dt` as an inner derivation of `Û`. -/
def sugawaraDegree (c : K) : Û :=
  -sugawaraVirasoro Φ hΦ hΦs a c 0

variable {Φ hΦ hΦs a}

/-- The Sugawara degree element is `-L₀`. -/
theorem sugawaraDegree_def (c : K) :
    sugawaraDegree Φ hΦ hΦs a c = -sugawaraVirasoro Φ hΦ hΦs a c 0 :=
  (rfl)

omit [FiniteDimensional K L] [LieAlgebra.IsKilling K L] in
private theorem continuous_innerDerivation (z : Û) :
    Continuous (innerDerivation K z : Module.End K Û) := by
  have heq : ((innerDerivation K z : Module.End K Û) : Û → Û) = fun x ↦ z * x - x * z := by
    funext x
    simp only [coe_innerDerivation, LieAlgebra.ad_apply, Ring.lie_def]
  rw [heq]
  exact (continuous_const.mul continuous_id).sub (continuous_id.mul continuous_const)

/-- **The completed degree derivation `t d/dt` multiplies `Sₙ` by `n`**, at every level (including
the critical level and `a = 0`) and for every invariant symmetric form `Φ`. -/
theorem vectorFieldCompletedEnvelopingDerivation_single_one_sugawaraMode (n : ℤ) :
    (vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a (HahnSeries.single 1 1) : Module.End K Û)
        (sugawaraMode Φ hΦ hΦs a n) =
      n • sugawaraMode Φ hΦ hΦs a n := by
  rw [sugawaraMode_eq_sum (Module.finBasis K L), map_sum, Finset.smul_sum]
  simp only [vectorFieldCompletedEnvelopingDerivation_single_one_normalOrderedMode]

/-- **The completed degree derivation `t d/dt` multiplies `Lₙ` by `n`.** -/
theorem vectorFieldCompletedEnvelopingDerivation_single_one_sugawaraVirasoro (c : K) (n : ℤ) :
    (vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a (HahnSeries.single 1 1) : Module.End K Û)
        (sugawaraVirasoro Φ hΦ hΦs a c n) =
      n • sugawaraVirasoro Φ hΦ hΦs a c n := by
  rw [sugawaraVirasoro_def, map_smul,
    vectorFieldCompletedEnvelopingDerivation_single_one_sugawaraMode, smul_comm]

/-- **The Sugawara degree element `D_κ = -L₀` has degree `0` under `t d/dt`.** -/
@[simp]
theorem vectorFieldCompletedEnvelopingDerivation_single_one_sugawaraDegree (c : K) :
    (vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a (HahnSeries.single 1 1) : Module.End K Û)
        (sugawaraDegree Φ hΦ hΦs a c) = 0 := by
  rw [sugawaraDegree_def, map_neg,
    vectorFieldCompletedEnvelopingDerivation_single_one_sugawaraVirasoro, zero_smul, neg_zero]

/-- **The inner derivation of `Sₘ` is `(1 - 2 a c)` times the completed Witt vector field
`-t^{m+1} d/dt`**, for `Φ = c • κ_L` at every level, including the critical level. -/
theorem innerDerivation_sugawaraMode_of_eq_smul_killingForm {c : K}
    (h : Φ = c • killingForm K L) (m : ℤ) :
    innerDerivation K (sugawaraMode Φ hΦ hΦs a m) =
      (1 - 2 * a * c) •
        vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a (-HahnSeries.single (m + 1) 1) := by
  let D := vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a (-HahnSeries.single (m + 1) 1)
  have hcont : Continuous (((1 - 2 * a * c) • D : derivationLieAlgebra K Û) : Module.End K Û) := by
    have heq : (((1 - 2 * a * c) • D : derivationLieAlgebra K Û) : Û → Û) =
        fun x ↦ algebraMap K Û (1 - 2 * a * c) * (D : Module.End K Û) x := by
      funext x
      rw [SetLike.val_smul, LinearMap.smul_apply, Algebra.smul_def]
    rw [heq]
    exact continuous_const.mul (continuous_vectorFieldCompletedEnvelopingDerivation ..)
  refine derivationLieAlgebra_ext_single Φ hΦ hΦs a
    (continuous_innerDerivation (sugawaraMode Φ hΦ hΦs a m)) hcont fun k z ↦ ?_
  rw [coe_innerDerivation, LieAlgebra.ad_apply, Ring.lie_def,
    sugawaraMode_mul_toCompletedEnveloping_sub_mul_of_eq_smul_killingForm h,
    SetLike.val_smul, LinearMap.smul_apply,
    vectorFieldCompletedEnvelopingDerivation_neg, NegMemClass.coe_neg, LinearMap.neg_apply,
    vectorFieldCompletedEnvelopingDerivation_single_add_one_envelopingι_single_tmul,
    ← Int.cast_smul_eq_zsmul K, smul_neg, smul_smul, ← neg_smul]

/-- **Away from the critical level, `Lₘ` implements the completed Witt vector field `-t^{m+1} d/dt`
as an inner derivation of `Û`.** -/
theorem innerDerivation_sugawaraVirasoro {c : K}
    (h : Φ = c • killingForm K L) (hc : 1 - 2 * a * c ≠ 0) (m : ℤ) :
    innerDerivation K (sugawaraVirasoro Φ hΦ hΦs a c m) =
      vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a (-HahnSeries.single (m + 1) 1) := by
  rw [sugawaraVirasoro_def, map_smul, innerDerivation_sugawaraMode_of_eq_smul_killingForm h,
    smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- **Away from the critical level, the Sugawara degree element `D_κ = -L₀` implements the completed
degree derivation `t d/dt` as an inner derivation of `Û`.** -/
theorem innerDerivation_sugawaraDegree {c : K}
    (h : Φ = c • killingForm K L) (hc : 1 - 2 * a * c ≠ 0) :
    innerDerivation K (sugawaraDegree Φ hΦ hΦs a c) =
      vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a (HahnSeries.single 1 1) := by
  rw [sugawaraDegree, map_neg, innerDerivation_sugawaraVirasoro h hc, zero_add,
    vectorFieldCompletedEnvelopingDerivation_neg, neg_neg]

/-- **Commutator form of Sugawara degree implementation**: away from the critical level,
`[D_κ, x] = (t d/dt)(x)` for every element `x` of the completed enveloping algebra `Û`. -/
theorem sugawaraDegree_mul_sub_mul {c : K}
    (h : Φ = c • killingForm K L) (hc : 1 - 2 * a * c ≠ 0) (x : Û) :
    sugawaraDegree Φ hΦ hΦs a c * x - x * sugawaraDegree Φ hΦ hΦs a c =
      (vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a (HahnSeries.single 1 1) :
        Module.End K Û) x := by
  have hd := congrArg (fun D : derivationLieAlgebra K Û ↦ (D : Module.End K Û) x)
    (innerDerivation_sugawaraDegree (hΦ := hΦ) (hΦs := hΦs) (a := a) h hc)
  simpa only [coe_innerDerivation, LieAlgebra.ad_apply, Ring.lie_def] using hd

/-- **The Sugawara degree element acts on current modes by `[D_κ, z_k] = k z_k`.** -/
theorem sugawaraDegree_mul_toCompletedEnveloping_sub_mul {c : K}
    (h : Φ = c • killingForm K L) (hc : 1 - 2 * a * c ≠ 0) (z : L) (k : ℤ) :
    sugawaraDegree Φ hΦ hΦs a c * ιK[z, k] - ιK[z, k] * sugawaraDegree Φ hΦ hΦs a c =
      (k : K) • ιK[z, k] := by
  rw [sugawaraDegree_mul_sub_mul h hc,
    vectorFieldCompletedEnvelopingDerivation_single_one_envelopingι_single_tmul,
    Int.cast_smul_eq_zsmul]

/-- **The Sugawara degree element grades the Virasoro modes over any field**:
`[D_κ, Lₙ] = n Lₙ` whenever `Φ = c • κ_L` and `1 - 2 a c ≠ 0`. -/
theorem sugawaraDegree_mul_sugawaraVirasoro_sub_mul {c : K}
    (h : Φ = c • killingForm K L) (hc : 1 - 2 * a * c ≠ 0) (n : ℤ) :
    sugawaraDegree Φ hΦ hΦs a c * sugawaraVirasoro Φ hΦ hΦs a c n -
        sugawaraVirasoro Φ hΦ hΦs a c n * sugawaraDegree Φ hΦ hΦs a c =
      (n : K) • sugawaraVirasoro Φ hΦ hΦs a c n := by
  rw [sugawaraDegree_mul_sub_mul h hc,
    vectorFieldCompletedEnvelopingDerivation_single_one_sugawaraVirasoro, Int.cast_smul_eq_zsmul]

/-- **Away from the critical level, the completed center `Z(Û)` is killed by the degree derivation
`t d/dt`**, because `t d/dt` is the inner derivation `ad(D_κ)`. -/
theorem vectorFieldCompletedEnvelopingDerivation_single_one_eq_zero_of_mem_center {c : K}
    (h : Φ = c • killingForm K L) (hc : 1 - 2 * a * c ≠ 0) {z : Û}
    (hz : z ∈ Subalgebra.center K Û) :
    (vectorFieldCompletedEnvelopingDerivation Φ hΦ hΦs a (HahnSeries.single 1 1) :
      Module.End K Û) z = 0 := by
  rw [← sugawaraDegree_mul_sub_mul h hc, Subalgebra.mem_center_iff.1 hz, sub_self]

/-- **The completed level comparison preserves the Sugawara degree element.** -/
@[simp]
theorem levelCompletedEnvelopingEquiv_sugawaraDegree {Ψ : LinearMap.BilinForm K L}
    (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (hΨ : Ψ.lieInvariant L) (hΨs : Ψ.IsSymm)
    {k : K} (h : Ψ = k • Φ) (c : K) :
    levelCompletedEnvelopingEquiv hΦ hΦs hΨ hΨs h (sugawaraDegree Ψ hΨ hΨs 1 (k * c)) =
      sugawaraDegree Φ hΦ hΦs k c := by
  simp only [sugawaraDegree, map_neg, levelCompletedEnvelopingEquiv_sugawaraVirasoro]

end Sugawara

end TauCeti.CurrentAlgebra
