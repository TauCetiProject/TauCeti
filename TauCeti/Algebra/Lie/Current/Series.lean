/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.Completion
public import TauCeti.Algebra.Category.ModuleCat.Tower.Summation

/-!
# High-order series in completed enveloping algebras

For currents `uₙ` of order at least `n`, and completely arbitrary elements `Pₙ` of the
level enveloping algebra, the series `∑ₙ Pₙ ι(uₙ)` converges in its left-ideal completion.
Its coordinate modulo `I_N` is represented by the first `N` terms. On a smooth module,
its action on a vector killed by `I_N` is the corresponding finite sum.

In particular this constructs the series `P₀ + ∑_{N ≥ 1} P_N ι((A_N)_N)` with no growth
conditions on `P_N` or `A_N`. The reason is left-ideal membership, not a norm estimate:
`P_N ι((A_N)_N)` belongs to `I_N` regardless of `P_N`.

## References

* E. Frenkel, *Langlands Correspondence for Loop Groups*, §2.1.2 and §3.2.1, for
  high-order series and their finite-cutoff action in the completed enveloping algebra.
-/

public section

noncomputable section

open scoped TensorProduct
open TauCeti.UniversalEnvelopingAlgebra
open LieAlgebra.ofTwoCocycle (centralElement envelopingι)

namespace TauCeti.CurrentAlgebra

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  {Φ : LinearMap.BilinForm R L} {hΦ : Φ.lieInvariant L} {hΦs : Φ.IsSymm} {a : R}

local notation "c" => twoCocycleOfBilinear R L Φ hΦ hΦs
local notation "UK" => CentralQuotient R (centralElement c) a

/-- Arbitrary left coefficients may multiply a series of currents whose orders tend to infinity
at least as fast as the index. The resulting series is unconditionally summable. -/
theorem summable_mul_envelopingι (P : ℕ → UK) {u : ℕ → currentAlgebra R L}
    (hu : ∀ n : ℕ, u n ∈ orderSubmodule R L n) :
    Summable fun n ↦ toCompletedEnveloping Φ hΦ hΦs a (P n * envelopingι c a (u n)) := by
  simp only [coe_toCompletedEnveloping]
  apply ModuleTower.summable_toLimQuotients_of_mem
  intro n
  exact (orderLeftIdeal Φ hΦ hΦs a n).smul_mem (P n) (envelopingι_mem_orderLeftIdeal (hu n))

/-- Each coordinate of a high-order current series is represented by a finite partial sum. -/
theorem limπ_tsum_mul_envelopingι (P : ℕ → UK) {u : ℕ → currentAlgebra R L}
    (hu : ∀ n : ℕ, u n ∈ orderSubmodule R L n) (N : ℕ) :
    (orderQuotientTower Φ hΦ hΦs a).limπ N
      (∑' n, toCompletedEnveloping Φ hΦ hΦs a (P n * envelopingι c a (u n))) =
      ModuleTower.quotientsπ _ (orderLeftIdeal_natCast_antitone Φ hΦ hΦs a) N
        (∑ n ∈ Finset.range N, P n * envelopingι c a (u n)) := by
  simp only [coe_toCompletedEnveloping]
  apply ModuleTower.limπ_tsum_toLimQuotients
  intro n
  exact (orderLeftIdeal Φ hΦ hΦs a n).smul_mem (P n) (envelopingι_mem_orderLeftIdeal (hu n))

/-- A constant plus a high-order series acts on a smooth vector by a finite sum at any
annihilating cutoff. No topology on the module or bounds on the left coefficients are required. -/
theorem limSmul_add_tsum_mul_envelopingι
    {M : ModuleCat UK} (hM : smoothModules (fun n : ℕ ↦ orderLeftIdeal Φ hΦ hΦs a n) M)
    (b : UK) (P : ℕ → UK) {u : ℕ → currentAlgebra R L}
    (hu : ∀ n : ℕ, u n ∈ orderSubmodule R L n) {m : M} {N : ℕ}
    (hm : ∀ x ∈ orderLeftIdeal Φ hΦ hΦs a N, x • m = 0) :
    ModuleTower.limSmul hM
      (toCompletedEnveloping Φ hΦ hΦs a b +
        ∑' n, toCompletedEnveloping Φ hΦ hΦs a (P n * envelopingι c a (u n))) m =
      b • m + ∑ n ∈ Finset.range N, P n • (envelopingι c a (u n) • m) := by
  have hf (n : ℕ) : P n * envelopingι c a (u n) ∈
      orderLeftIdeal Φ hΦ hΦs a n :=
    (orderLeftIdeal Φ hΦ hΦs a n).smul_mem (P n) (envelopingι_mem_orderLeftIdeal (hu n))
  rw [ModuleTower.add_limSmul, coe_toCompletedEnveloping,
    ModuleTower.limSmul_toLimQuotients, ModuleTower.limSmul_tsum_toLimQuotients hM hf hm]
  simp only [mul_smul]

/-- The positive-mode series with arbitrary left coefficients is summable. Adding any constant
term gives the usual high-order series in the completed enveloping algebra. -/
theorem summable_mul_envelopingι_single (P : ℕ → UK) (x : ℕ → L) :
    Summable fun n ↦ toCompletedEnveloping Φ hΦ hΦs a
      (P n * envelopingι c a ((HahnSeries.single (n + 1 : ℤ) 1) ⊗ₜ[R] x n)) := by
  apply summable_mul_envelopingι P
  intro n
  exact tmul_mem_orderSubmodule R L n
    ((WithTop.coe_le_coe.mpr (by omega : (n : ℤ) ≤ n + 1)).trans
      HahnSeries.orderTop_single_le) (x n)

end TauCeti.CurrentAlgebra
