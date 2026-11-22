/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.Center
public import TauCeti.Algebra.Lie.Current.NormalOrder.Basic
public import TauCeti.Algebra.Lie.Killing.Duality

import TauCeti.LinearAlgebra.BilinearForm.Basic

/-!
# Segal--Sugawara modes in the completed enveloping algebra

Let `L` be a finite-dimensional Lie algebra over a field `K` whose Killing form `κ_L` is
nondegenerate, let `Φ` be an invariant symmetric form on `L`, and let `Û = lim_N U / I_N` be the
completed enveloping algebra of the residue central extension of `Φ` at the central value `a`
(`TauCeti.CurrentAlgebra.CompletedEnveloping`). Applying `normalOrderedMode` to the canonical
Killing Casimir tensor `TauCeti.killingCasimirTensor K L ∈ L ⊗[K] L` yields the **Segal--Sugawara
modes**

`Sₙ = ∑ᵢ :xᵢ yᵢ:_n ∈ Û`,

the modes of the normally ordered Casimir field `∑ᵢ :J^{xᵢ}(z) J^{yᵢ}(z):`
(`TauCeti.CurrentAlgebra.sugawaraMode`), for any basis `xᵢ` of `L` and the basis `yᵢ` dual to it
under `κ_L`. They do not depend on the basis (`TauCeti.CurrentAlgebra.sugawaraMode_eq_sum`), have
finite-window coordinates and smooth-module actions
(`TauCeti.CurrentAlgebra.limπ_sugawaraMode`, `TauCeti.CurrentAlgebra.limSmul_sugawaraMode`),
rescale inversely under rescaling the invariant form
(`TauCeti.CurrentAlgebra.sugawaraMode_eq_inv_smul_sum_dualBasis`), and are preserved by the
completed level comparison (`TauCeti.CurrentAlgebra.levelCompletedEnvelopingEquiv_sugawaraMode`).

The main result is the commutator of a current with these modes
(`TauCeti.CurrentAlgebra.toCompletedEnveloping_mul_sugawaraMode_sub_mul`): for the current
generator `z_k` of the mode `z ⊗ tᵏ`,

`[z_k, Sₙ] = k (z - 2 a w)_{n+k}`, where `κ_L(w, y) = Φ(z, y)` for all `y`.

It follows from the commutator of a current with a normally ordered mode
(`TauCeti.CurrentAlgebra.toCompletedEnveloping_mul_normalOrderedMode_sub_mul`): the Leibniz terms
cancel because `∑ᵢ xᵢ ⊗ yᵢ` is invariant, the reordering terms give the adjoint Casimir operator
`∑ᵢ ⁅⁅z, xᵢ⁆, yᵢ⁆ = z` (`TauCeti.sum_lie_lie_killingDualBasis`), the central contractions give
`2 a w`, and the central constant vanishes because `∑ᵢ ⁅xᵢ, yᵢ⁆ = 0`. If `Φ = c κ_L` then `w = c z`
and `[z_k, Sₙ] = k (1 - 2 a c) z_{n+k}`. Away from the critical level `1 - 2 a c = 0`, the
normalised modes `Lₘ = (1 - 2 a c)⁻¹ Sₘ` (`TauCeti.CurrentAlgebra.sugawaraVirasoro`) satisfy
`[Lₘ, z_k] = -k z_{m+k}`, with Sugawara central charge
`c_{Vir} = -(2 a c) / (1 - 2 a c) · dim L` (`TauCeti.CurrentAlgebra.sugawaraCentralCharge`).

**The critical level.** When `2 a Φ = κ_L`, every `Sₙ` commutes with all currents, so it lies in the
center of `Û` (`TauCeti.CurrentAlgebra.sugawaraMode_mem_center`). For the affine level form
`κ = -Φ` at `a = 1` this is `κ = -½ κ_L`, the critical level `κ_c`.

No characteristic or algebraic-closure hypothesis is needed. In the normalisation of Frenkel, with
the invariant form `κ₀ = κ_L / (2 h^∨)` and `S(z) = ½ ∑ :J^a J_a:` for `κ₀`-dual bases, the
Segal--Sugawara modes are `h^∨ Sₙ`, and at the level `κ = k κ₀` the formula above becomes
`[z_m, h^∨ Sₙ] = (k + h^∨) m z_{n+m}`.

The homothety `t ↦ u t` scales `Sₙ` by `u ^ n` at every central value
(`TauCeti.CurrentAlgebra.coordinateCompletedEnvelopingAut_homothety_sugawaraMode`). The finite
Killing-dual contraction uses finite-dimensionality of `L` and nondegeneracy of its Killing form.
The normal-order scaling law applies to every Lie algebra over the field. At the critical level
the coordinate action preserves the center, and the scaling law computes the transport of
central characters on the Sugawara modes.

## Main definitions

* `TauCeti.CurrentAlgebra.sugawaraMode`: the Segal--Sugawara modes `Sₙ = ∑ᵢ :xᵢ yᵢ:_n`.
* `TauCeti.CurrentAlgebra.sugawaraVirasoro`: the normalised Segal--Sugawara Virasoro modes
  `Lₘ = (1 - 2 a c)⁻¹ Sₘ`.
* `TauCeti.CurrentAlgebra.sugawaraCentralCharge`: the Sugawara central charge
  `-(2 a c) / (1 - 2 a c) · dim L`.

## Main results

* `TauCeti.CurrentAlgebra.sugawaraMode_eq_sum`: `Sₙ` may be computed in any basis.
* `TauCeti.CurrentAlgebra.coordinateCompletedEnvelopingAut_homothety_sugawaraMode`: a homothety
  scales `Sₙ` by `u ^ n` at every central value.
* `TauCeti.CurrentAlgebra.toCompletedEnveloping_mul_sugawaraMode_sub_mul`: the commutator
  `[z_k, Sₙ] = k (z - 2 a w)_{n+k}`.
* `TauCeti.CurrentAlgebra.toCompletedEnveloping_mul_sugawaraMode_sub_mul_of_eq_smul_killingForm`:
  for `Φ = c κ_L`, the commutator `[z_k, Sₙ] = k (1 - 2 a c) z_{n+k}`.
* `TauCeti.CurrentAlgebra.sugawaraVirasoro_mul_toCompletedEnveloping_sub_mul`:
  for `Φ = c κ_L` and `1 - 2 a c ≠ 0`, `[Lₘ, z_k] = -k z_{m+k}`.
* `TauCeti.CurrentAlgebra.sugawaraMode_mem_center`: at the critical level `2 a Φ = κ_L`, the
  Segal--Sugawara modes are central.
* `TauCeti.CurrentAlgebra.limπ_sugawaraMode`, `TauCeti.CurrentAlgebra.limSmul_sugawaraMode`:
  finite-window formulas for the coordinates and smooth-module action of `Sₙ`.
* `TauCeti.CurrentAlgebra.sugawaraMode_eq_inv_smul_sum_dualBasis`: expansion of `Sₙ` along the dual
  basis of a rescaled invariant form.
* `TauCeti.CurrentAlgebra.levelCompletedEnvelopingEquiv_sugawaraMode`,
  `TauCeti.CurrentAlgebra.levelCompletedEnvelopingEquiv_sugawaraVirasoro`: compatibility with the
  completed level comparison, including at level zero.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §3.1, for the Segal--Sugawara vector and
  its commutation relations with the currents, and Corollary 3.2.2, for the centrality of its
  Fourier coefficients at the critical level.
* E. Frenkel, D. Ben-Zvi, *Vertex Algebras and Algebraic Curves*, 2nd ed., §2.5.10.
-/

public section

noncomputable section

open scoped TensorProduct
open TauCeti.UniversalEnvelopingAlgebra
open LieAlgebra.ofTwoCocycle (centralElement envelopingι)

namespace TauCeti.CurrentAlgebra

section Sugawara

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  (Φ : LinearMap.BilinForm K L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (a : K)

local notation "ιK[" x ", " m "]" =>
  toCompletedEnveloping Φ hΦ hΦs a
    (envelopingι (twoCocycleOfBilinear K L Φ hΦ hΦs) a (HahnSeries.single m (1 : K) ⊗ₜ[K] x))

/-- The image of a mode is additive and homogeneous in the coefficient vector. -/
private theorem sum_smul_toCompletedEnveloping {ι : Type*} (s : Finset ι) (r : ι → K) (v : ι → L)
    (m : ℤ) : ∑ i ∈ s, r i • ιK[v i, m] = ιK[∑ i ∈ s, r i • v i, m] := by
  simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul, map_sum, map_smul]

variable [FiniteDimensional K L] [LieAlgebra.IsKilling K L]

/-- **The Segal--Sugawara modes** `Sₙ = ∑ᵢ :xᵢ yᵢ:_n` in `Û`, obtained by applying
`TauCeti.CurrentAlgebra.normalOrderedMode` to `TauCeti.killingCasimirTensor K L`: the modes of
the normally ordered Casimir field `∑ᵢ :J^{xᵢ}(z) J^{yᵢ}(z):`, without any normalising factor.
`TauCeti.CurrentAlgebra.sugawaraMode_eq_sum` evaluates `Sₙ` as `∑ᵢ :bᵢ b'ᵢ:_n` in any basis `b`
and its Killing-dual basis `b'`. -/
def sugawaraMode (n : ℤ) : CompletedEnveloping Φ hΦ hΦs a :=
  TensorProduct.lift (normalOrderedMode Φ hΦ hΦs a n) (killingCasimirTensor K L)

variable {Φ hΦ hΦs a}

/-- **The Segal--Sugawara modes may be computed in any basis**: `Sₙ = ∑ᵢ :xᵢ yᵢ:_n` for every basis
`xᵢ` of `L` and its Killing-dual basis `yᵢ`. -/
theorem sugawaraMode_eq_sum {ι : Type*} [DecidableEq ι] [Fintype ι] (b : Module.Basis ι K L)
    (n : ℤ) :
    sugawaraMode Φ hΦ hΦs a n =
      ∑ i, normalOrderedMode Φ hΦ hΦs a n (b i) (killingDualBasis b i) := by
  rw [sugawaraMode, killingCasimirTensor_eq_sum b, map_sum]
  simp only [TensorProduct.lift.tmul]

/-- Under the coordinate substitution `t ↦ u t`, the Segal--Sugawara mode `Sₙ` maps to
`u ^ n • Sₙ`. This holds at every central value, without a critical-level assumption. -/
@[simp]
theorem coordinateCompletedEnvelopingAut_homothety_sugawaraMode
    (Φ : LinearMap.BilinForm K L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (a : K)
    (u : Kˣ) (n : ℤ) :
    coordinateCompletedEnvelopingAut Φ hΦ hΦs a (FormalCoordinate.homothety u).substAlgEquiv
        (sugawaraMode Φ hΦ hΦs a n) =
      (u : K) ^ n • sugawaraMode Φ hΦ hΦs a n := by
  rw [sugawaraMode_eq_sum (Module.finBasis K L), map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ ↦
    coordinateCompletedEnvelopingAut_homothety_normalOrderedMode Φ hΦ hΦs a u n _ _

/-- **The commutator of a current with the Segal--Sugawara modes.** For the current generator `z_k`
of the mode `z ⊗ tᵏ` and the vector `w` dual to `Φ(z, ·)` under the Killing form,
`[z_k, Sₙ] = k (z - 2 a w)_{n+k}`. -/
theorem toCompletedEnveloping_mul_sugawaraMode_sub_mul {z w : L}
    (hw : ∀ y, killingForm K L w y = Φ z y) (k n : ℤ) :
    ιK[z, k] * sugawaraMode Φ hΦ hΦs a n - sugawaraMode Φ hΦ hΦs a n * ιK[z, k] =
      (k : K) • ιK[z - (2 * a) • w, n + k] := by
  classical
  set b := Module.finBasis K L
  have hnd := LieAlgebra.IsKilling.killingForm_nondegenerate K L
  rw [sugawaraMode_eq_sum b, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  simp only [toCompletedEnveloping_mul_normalOrderedMode_sub_mul, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, sum_apply_lie_killingDualBasis_add_eq_zero, zero_add]
  -- The double brackets sum to `z`: the adjoint Casimir operator is the identity.
  have h₁ : ∑ i, (k : K) • ιK[⁅⁅z, b i⁆, killingDualBasis b i⁆, n + k] =
      (k : K) • ιK[z, n + k] := by
    rw [sum_smul_toCompletedEnveloping, ← Finset.smul_sum, sum_lie_lie_killingDualBasis,
      TensorProduct.tmul_smul, map_smul, map_smul]
  -- The contractions with `Φ z` are both the Killing-dual vector `w`.
  have h₂ : ∑ i, (k * a * Φ z (b i)) • ιK[killingDualBasis b i, n + k] =
      (k * a) • ιK[w, n + k] := by
    simp only [sum_smul_toCompletedEnveloping, ← hw, mul_smul, ← Finset.smul_sum]
    rw [LinearMap.BilinForm.sum_apply_smul_dualBasis hnd b w]
  have h₃ : ∑ i, (k * a * Φ z (killingDualBasis b i)) • ιK[b i, n + k] =
      (k * a) • ιK[w, n + k] := by
    simp only [sum_smul_toCompletedEnveloping, ← hw, mul_smul, ← Finset.smul_sum,
      LieModule.traceForm_comm K L L w]
    rw [LinearMap.BilinForm.sum_apply_dualBasis_smul hnd b w]
  -- The central terms vanish, since `∑ᵢ Φ(⁅z, xᵢ⁆, yᵢ) = Φ(z, ∑ᵢ ⁅xᵢ, yᵢ⁆) = 0`.
  have hc : ∑ i, Φ ⁅z, b i⁆ (killingDualBasis b i) = 0 := by
    have hi (i) : Φ ⁅z, b i⁆ (killingDualBasis b i) = Φ z ⁅b i, killingDualBasis b i⁆ := by
      rw [← lie_skew, map_neg, LinearMap.neg_apply, hΦ, neg_neg]
    simp only [hi]
    rw [← map_sum, sum_lie_killingDualBasis_eq_zero, map_zero]
  have h₄ : ∑ i, algebraMap K (CompletedEnveloping Φ hΦ hΦs a) (if n + k = 0 then
      ((k * (k - 1) / 2 : ℤ) : K) * a * Φ ⁅z, b i⁆ (killingDualBasis b i) else 0) = 0 := by
    rw [← map_sum]
    split_ifs
    · rw [← Finset.mul_sum, hc, mul_zero, map_zero]
    · simp
  rw [h₁, h₂, h₃, h₄, TensorProduct.tmul_sub, TensorProduct.tmul_smul, map_sub, map_smul,
    map_sub, map_smul]
  module

/-- **The commutator of a current with the Segal--Sugawara modes, for a multiple of the Killing
form.** If `Φ = c κ_L`, then `[z_k, Sₙ] = k (1 - 2 a c) z_{n+k}`. -/
theorem toCompletedEnveloping_mul_sugawaraMode_sub_mul_of_eq_smul_killingForm {c : K}
    (h : Φ = c • killingForm K L) (z : L) (k n : ℤ) :
    ιK[z, k] * sugawaraMode Φ hΦ hΦs a n - sugawaraMode Φ hΦ hΦs a n * ιK[z, k] =
      ((k : K) * (1 - 2 * a * c)) • ιK[z, n + k] := by
  rw [toCompletedEnveloping_mul_sugawaraMode_sub_mul (w := c • z) (fun y ↦ by simp [h]),
    show z - (2 * a) • c • z = (1 - 2 * a * c) • z by module, TensorProduct.tmul_smul, map_smul,
    map_smul, smul_smul]

/-- **The Segal--Sugawara modes are central at the critical level.** If `2 a Φ = κ_L`, which for
the affine level form `κ = -Φ` at central value `1` is the critical level `κ = -½ κ_L`, then every
`Sₙ` lies in the center of `Û`. -/
theorem sugawaraMode_mem_center (h : (2 * a) • Φ = killingForm K L) (n : ℤ) :
    sugawaraMode Φ hΦ hΦs a n ∈ Subalgebra.center K (CompletedEnveloping Φ hΦ hΦs a) := by
  have hnd := LieAlgebra.IsKilling.killingForm_nondegenerate K L
  refine mem_center_iff_forall_commute_single.2 fun k z ↦ ?_
  set w := ((killingForm K L).toDual hnd).symm (Φ z)
  have hw (y : L) : killingForm K L w y = Φ z y := LinearMap.BilinForm.apply_toDual_symm_apply ..
  have hz : (2 * a) • w = z := by
    refine sub_eq_zero.1 (hnd.1 _ fun y ↦ ?_)
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, hw]
    simp [← h]
  rw [Commute, SemiconjBy, ← sub_eq_zero, toCompletedEnveloping_mul_sugawaraMode_sub_mul hw, hz,
    sub_self, TensorProduct.tmul_zero, map_zero, map_zero, smul_zero]

end Sugawara

/-! ### Coordinates, smooth action, rescaled forms and level comparison -/

section Basic

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [LieAlgebra.IsKilling K L]

section FixedForm

variable {Φ : LinearMap.BilinForm K L} {hΦ : Φ.lieInvariant L} {hΦs : Φ.IsSymm} {a : K}

local notation "UK" => CentralQuotient K (centralElement (twoCocycleOfBilinear K L Φ hΦ hΦs)) a

/-- **The coordinates of the Segal--Sugawara modes are finite sums.** Modulo `I_N`, `Sₙ` is
represented in any basis `b` by the summands of `:bᵢ b'ᵢ:_n` in the window
`min (n + 1 - N) 0 ≤ m < N`. -/
theorem limπ_sugawaraMode {ι : Type*} [DecidableEq ι] [Fintype ι] (b : Module.Basis ι K L)
    (n : ℤ) (N : ℕ) :
    (orderQuotientTower Φ hΦ hΦs a).limπ N (sugawaraMode Φ hΦ hΦs a n) =
      ModuleTower.quotientsπ _ (orderLeftIdeal_natCast_antitone Φ hΦ hΦs a) N
        (∑ i, ∑ m ∈ Finset.Ico (min (n + 1 - N) 0) N,
          normalOrderedSummand Φ hΦ hΦs a 0 n m (b i) (killingDualBasis b i)) := by
  rw [sugawaraMode_eq_sum b, map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ ↦ limπ_normalOrderedMode n (b i) (killingDualBasis b i) N

/-- **The action of a Segal--Sugawara mode on a smooth vector is a finite sum.** On a vector `v`
killed by `I_N`, `Sₙ` acts in any basis `b` by the summands with `min (n + 1 - N) 0 ≤ m < N`. -/
theorem limSmul_sugawaraMode {M : ModuleCat UK}
    (hM : smoothModules (fun n : ℕ ↦ orderLeftIdeal Φ hΦ hΦs a n) M)
    {ι : Type*} [DecidableEq ι] [Fintype ι] (b : Module.Basis ι K L) (n : ℤ) {v : M} {N : ℕ}
    (hv : ∀ c ∈ orderLeftIdeal Φ hΦ hΦs a N, c • v = 0) :
    ModuleTower.limSmul hM (sugawaraMode Φ hΦ hΦs a n) v =
      ∑ i, ∑ m ∈ Finset.Ico (min (n + 1 - N) 0) N,
        normalOrderedSummand Φ hΦ hΦs a 0 n m (b i) (killingDualBasis b i) • v := by
  rw [ModuleTower.limSmul_eq_smul hM _ hv (limπ_sugawaraMode b n N).symm]
  simp only [Finset.sum_smul]

/-- **Expansion of the Segal--Sugawara modes along a rescaled bilinear form.** If `κ_L = d • B` for
a nondegenerate form `B` and `d ≠ 0`, then `Sₙ = d⁻¹ • ∑ᵢ :bᵢ b^i:_n`, where `b^i` is the basis
dual to `b` under `B`. -/
theorem sugawaraMode_eq_inv_smul_sum_dualBasis {B : LinearMap.BilinForm K L}
    (hB : B.Nondegenerate) {d : K} (hd : d ≠ 0) (h : killingForm K L = d • B)
    {ι : Type*} [DecidableEq ι] [Fintype ι] (b : Module.Basis ι K L) (n : ℤ) :
    sugawaraMode Φ hΦ hΦs a n =
      d⁻¹ • ∑ i, normalOrderedMode Φ hΦ hΦs a n (b i) (B.dualBasis hB b i) := by
  have hcongr (B₁ B₂ : LinearMap.BilinForm K L) (h₁ : B₁.Nondegenerate) (h₂ : B₂.Nondegenerate)
      (heq : B₁ = B₂) (i : ι) : B₁.dualBasis h₁ b i = B₂.dualBasis h₂ b i := by
    subst heq
    rfl
  rw [sugawaraMode_eq_sum b, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [killingDualBasis, hcongr _ (d • B) _
    ((TauCeti.BilinForm.nondegenerate_smul_iff (IsRegular.of_ne_zero hd)).mpr hB) h,
    b.dualBasis_smul_apply B hB d hd i, map_smul]

/-- **The normalised Segal--Sugawara Virasoro modes** `Lₘ = (1 - 2 a c)⁻¹ Sₘ` in `Û`, attached to
`Φ = c • κ_L` away from the critical level `1 - 2 a c = 0`. -/
def sugawaraVirasoro (Φ : LinearMap.BilinForm K L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm)
    (a c : K) (m : ℤ) : CompletedEnveloping Φ hΦ hΦs a :=
  (1 - 2 * a * c)⁻¹ • sugawaraMode Φ hΦ hΦs a m

/-- The normalised Segal--Sugawara Virasoro mode `Lₘ` is `(1 - 2 a c)⁻¹ • Sₘ`. -/
theorem sugawaraVirasoro_def (c : K) (m : ℤ) :
    sugawaraVirasoro Φ hΦ hΦs a c m = (1 - 2 * a * c)⁻¹ • sugawaraMode Φ hΦ hΦs a m :=
  (rfl)

/-- **The commutator of a normalised Segal--Sugawara Virasoro mode with a current mode**:
`[Lₘ, z_k] = -k z_{m+k}` whenever `Φ = c • κ_L` and `1 - 2 a c ≠ 0`. -/
theorem sugawaraVirasoro_mul_toCompletedEnveloping_sub_mul {c : K}
    (h : Φ = c • killingForm K L) (hc : 1 - 2 * a * c ≠ 0) (z : L) (m k : ℤ) :
    sugawaraVirasoro Φ hΦ hΦs a c m *
        toCompletedEnveloping Φ hΦ hΦs a
          (envelopingι (twoCocycleOfBilinear K L Φ hΦ hΦs) a
            (HahnSeries.single k (1 : K) ⊗ₜ[K] z)) -
        toCompletedEnveloping Φ hΦ hΦs a
          (envelopingι (twoCocycleOfBilinear K L Φ hΦ hΦs) a
            (HahnSeries.single k (1 : K) ⊗ₜ[K] z)) *
          sugawaraVirasoro Φ hΦ hΦs a c m =
      (-(k : K)) • toCompletedEnveloping Φ hΦ hΦs a
        (envelopingι (twoCocycleOfBilinear K L Φ hΦ hΦs) a
          (HahnSeries.single (m + k) (1 : K) ⊗ₜ[K] z)) := by
  rw [sugawaraVirasoro_def, smul_mul_assoc, mul_smul_comm, ← smul_sub,
    ← neg_sub (toCompletedEnveloping Φ hΦ hΦs a _ * _),
    toCompletedEnveloping_mul_sugawaraMode_sub_mul_of_eq_smul_killingForm h,
    smul_neg, smul_smul, ← neg_smul]
  congr 1
  field_simp

end FixedForm

omit [FiniteDimensional K L] [LieAlgebra.IsKilling K L] in
variable (K L) in
/-- **The Sugawara central charge** `c_{Vir} = -(2 a c) / (1 - 2 a c) · dim L` of the Virasoro
algebra generated by `sugawaraVirasoro` for `Φ = c • κ_L` at central value `a`. For the affine
level form `κ = -Φ` with `κ = k κ₀` and `κ_L = 2 h^∨ κ₀` at `a = 1`, this is
`k · dim L / (k + h^∨)`. -/
def sugawaraCentralCharge (a c : K) : K :=
  -(2 * a * c) / (1 - 2 * a * c) * (Module.finrank K L : K)

omit [FiniteDimensional K L] [LieAlgebra.IsKilling K L] in
variable (K L) in
/-- The Sugawara central charge is `-(2 a c) / (1 - 2 a c) · dim L`. -/
theorem sugawaraCentralCharge_def (a c : K) :
    sugawaraCentralCharge K L a c = -(2 * a * c) / (1 - 2 * a * c) * (Module.finrank K L : K) :=
  (rfl)

/-- **The completed level comparison preserves the Segal--Sugawara modes.** If `Ψ = k • Φ`, the
completed level comparison from `Û(ĝ_Ψ)` at central value `1` to `Û(ĝ_Φ)` at central value `k`
sends `Sₙ` to `Sₙ`, for every `k : K`, including `k = 0`. -/
@[simp]
theorem levelCompletedEnvelopingEquiv_sugawaraMode {Φ Ψ : LinearMap.BilinForm K L}
    (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (hΨ : Ψ.lieInvariant L) (hΨs : Ψ.IsSymm)
    {k : K} (h : Ψ = k • Φ) (n : ℤ) :
    levelCompletedEnvelopingEquiv hΦ hΦs hΨ hΨs h (sugawaraMode Ψ hΨ hΨs 1 n) =
      sugawaraMode Φ hΦ hΦs k n := by
  rw [sugawaraMode_eq_sum (Module.finBasis K L), sugawaraMode_eq_sum (Module.finBasis K L), map_sum]
  simp only [levelCompletedEnvelopingEquiv_normalOrderedMode]

/-- **The completed level comparison preserves the normalised Segal--Sugawara Virasoro modes.** If
`Ψ = k • Φ`, then `Lₘ` at central value `1` for `Ψ = (k * c) • κ_L` maps to `Lₘ` at central value
`k` for `Φ = c • κ_L`. -/
@[simp]
theorem levelCompletedEnvelopingEquiv_sugawaraVirasoro {Φ Ψ : LinearMap.BilinForm K L}
    (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm) (hΨ : Ψ.lieInvariant L) (hΨs : Ψ.IsSymm)
    {k : K} (h : Ψ = k • Φ) (c : K) (m : ℤ) :
    levelCompletedEnvelopingEquiv hΦ hΦs hΨ hΨs h (sugawaraVirasoro Ψ hΨ hΨs 1 (k * c) m) =
      sugawaraVirasoro Φ hΦ hΦs k c m := by
  simp only [sugawaraVirasoro, map_smul, levelCompletedEnvelopingEquiv_sugawaraMode,
    one_mul, mul_assoc]

end Basic

end TauCeti.CurrentAlgebra
