/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.HeisenbergModel.LatticeVacuum
public import TauCeti.NumberTheory.NumberField.CMField.HeisenbergDatum
public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.WeilData
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.PiIntegralAdeles
import TauCeti.LinearAlgebra.Matrix.DotProduct

/-!
# The finite Heisenberg datum of Weil data and its lattice vacuum

Let `E` be a CM field with Weil data `(j, α, υ)`, finite adeles `𝔸_f` and integral finite adeles
`Ô`, let `ψ₀(z) = ψ_f(j α (conj α) z)` be the character of `𝔸_f` for which `Ô` is self-dual
(`TauCeti.WeilData.selfDualAddChar`), `c₀ = (1 − j⁻¹)/2` and `semi(z) = ψ₀(½ c₀ z* z)` the
semicharacter on `𝔸_fⁿ` (`TauCeti.WeilData.semichar`). This file defines the Heisenberg datum
and the vacuum of the reproducing model at the finite places:

* the **finite Heisenberg datum** `β_f(x, y) = ψ₀(½ y* x)` on `𝔸_fⁿ`
  (`TauCeti.WeilData.finiteDatum`). It is the finite part `ψ_f(½ j · y* x)` of the adelic
  Heisenberg datum read in the finite coordinates `x = α z`
  (`TauCeti.WeilData.finiteHeisenbergDatum_smul_smul_eq_finiteDatum`);
* the **finite vacuum** `e_f`, equal to `semi(z)` for `z ∈ Ôⁿ` and to `0` otherwise
  (`TauCeti.WeilData.finiteVacuum`).

The main result is that `e_f` is a vacuum for `β_f` and every translation-invariant measure giving
`Ôⁿ` mass one (`TauCeti.WeilData.isVacuum_finiteVacuum`), so that the reproducing model of `β_f`
and `e_f` is defined. It is an instance of the abstract lattice vacuum
`TauCeti.HeisenbergDatum.isVacuum_indicator`, with two arithmetic inputs:

* **self-duality of `Ôⁿ`** for `β_f²` (`TauCeti.WeilData.forall_finiteDatum_sq_eq_one_iff`),
  which reduces to the self-duality of `Ô` for `ψ₀`
  (`TauCeti.WeilData.forall_selfDualAddChar_mul_eq_one_iff`) on the vectors `u eᵢ`, `u ∈ Ô`;
* the **semicharacter law** `semi(a + b) = semi(a) semi(b) β_f(a, b)` on `Ôⁿ`
  (`TauCeti.WeilData.semichar_add_of_forall_mem`).

## Main definitions

* `TauCeti.WeilData.finiteDatum`: the Heisenberg datum `ψ₀(½ y* x)` on `𝔸_fⁿ`.
* `TauCeti.WeilData.finiteVacuum`: the extension by zero of the semicharacter on `Ôⁿ`.

## Main results

* `TauCeti.WeilData.finiteDatum_apply`: `β_f(x, y) = ψ₀(½ y* x)`.
* `TauCeti.WeilData.finiteHeisenbergDatum_smul_smul_eq_finiteDatum`: `β_f` is the finite part of
  the adelic Heisenberg datum in finite coordinates.
* `TauCeti.WeilData.forall_finiteDatum_sq_eq_one_iff`: self-duality of `Ôⁿ` for `β_f²`.
* `TauCeti.WeilData.isVacuum_finiteVacuum`: `e_f` is a vacuum for `β_f`.

## Attribution

The finite datum, the lattice vacuum and the statement that it is a vacuum follow
`New.stdLattice.finHeisenberg`, `New.stdLattice.finVac` and `New.stdLattice.isVacuum_finVac` in
`src/Lib/Weil/Construction/FiniteMultiplier.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC). The proof here
is written independently, as an instance of the abstract lattice vacuum.

## References

* A. Weil, *Sur certains groupes d'opérateurs unitaires*, Acta Math. 111 (1964), 143–211.
* S. S. Kudla, *Splitting metaplectic covers of dual reductive pairs*, Israel J. Math. 87 (1994).
-/

public section

noncomputable section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing MeasureTheory NumberField
  NumberField.IsCMField
open scoped NumberField.AdeleRing

namespace TauCeti.WeilData

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {Φ : CMType E} (W : WeilData Φ)
  (n : Type*) [Fintype n]

/-! ### The finite Heisenberg datum -/

section Datum

variable [DecidableEq n]

/-- The diagonal image of `j / 2` in the finite adeles is purely imaginary. -/
private theorem algebraMap_j_div_two_mem_skewAdjoint :
    algebraMap E 𝔸ᶠ[E] (W.j / 2) ∈ skewAdjoint 𝔸ᶠ[E] := by
  rw [skewAdjoint.mem_iff, ← algebraMap_star_comm, ← map_neg, star_div₀, star_ofNat, W.star_j,
    neg_div]

/-- The **finite Heisenberg datum** `β_f(x, y) = ψ₀(½ y* x)` on `𝔸_fⁿ` of Weil data
(`TauCeti.WeilData.finiteDatum_apply`): the datum `ψ_f(t · y* x)` of `t = α (j / 2) (conj α)`.
It is the finite part `ψ_f(½ j · y* x)` of the adelic Heisenberg datum, read in the finite
coordinates `x = α z` (`TauCeti.WeilData.finiteHeisenbergDatum_smul_smul_eq_finiteDatum`). -/
def finiteDatum : HeisenbergDatum (n → 𝔸ᶠ[E]) :=
  finiteHeisenbergDatum n ((W.α : 𝔸ᶠ[E]) * algebraMap E 𝔸ᶠ[E] (W.j / 2) * star (W.α : 𝔸ᶠ[E]))
    (skewAdjoint.conjugate W.algebraMap_j_div_two_mem_skewAdjoint _)

/-- In the finite coordinates `x = α z`, the finite Heisenberg datum `ψ_f(½ j · y* x)` of `j / 2`
(the finite part of the adelic Heisenberg datum) is `β_f`. -/
theorem finiteHeisenbergDatum_smul_smul_eq_finiteDatum
    (h : algebraMap E 𝔸ᶠ[E] (W.j / 2) ∈ skewAdjoint 𝔸ᶠ[E]) (x y : n → 𝔸ᶠ[E]) :
    finiteHeisenbergDatum n (algebraMap E 𝔸ᶠ[E] (W.j / 2)) h ((W.α : 𝔸ᶠ[E]) • x)
        ((W.α : 𝔸ᶠ[E]) • y) = W.finiteDatum n x y :=
  finiteHeisenbergDatum_smul_smul _ h _ x y

variable {n} in
/-- **`β_f(x, y) = ψ₀(½ y* x)`**. -/
@[simp]
theorem finiteDatum_apply (x y : n → 𝔸ᶠ[E]) :
    W.finiteDatum n x y = W.selfDualAddChar (algebraMap E 𝔸ᶠ[E] 2⁻¹ * (star y ⬝ᵥ x)) := by
  rw [finiteDatum, finiteHeisenbergDatum_apply, selfDualAddChar_apply, coe_scaleIdele]
  congr 2
  rw [div_eq_mul_inv, map_mul]
  ring

variable {n} in
/-- The square of `β_f` is `β_f(x, y)² = ψ₀(y* x)`. -/
theorem finiteDatum_sq (x y : n → 𝔸ᶠ[E]) :
    (W.finiteDatum n x y : ℂ) ^ 2 = W.selfDualAddChar (star y ⬝ᵥ x) := by
  rw [finiteDatum_apply, ← Circle.coe_pow, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul,
    Nat.cast_ofNat, ← mul_assoc, ← map_ofNat (algebraMap E 𝔸ᶠ[E]) 2, ← map_mul,
    mul_inv_cancel₀ two_ne_zero, map_one, one_mul]

/-- **`Ôⁿ` is self-dual for `β_f²`**: a vector `y` lies in `Ôⁿ` exactly when
`β_f(z, y)² = ψ₀(y* z) = 1` for every `z ∈ Ôⁿ`. -/
theorem forall_finiteDatum_sq_eq_one_iff (y : n → 𝔸ᶠ[E]) :
    (∀ z ∈ piIntegralAdeles (𝓞 E) E n, (W.finiteDatum n z y : ℂ) ^ 2 = 1) ↔
      y ∈ piIntegralAdeles (𝓞 E) E n := by
  simp_rw [finiteDatum_sq, mem_piIntegralAdeles]
  refine ⟨fun h i ↦ ?_, fun hy z hz ↦ ?_⟩
  · -- test on the vectors `u eᵢ`, `u ∈ Ô`
    rw [← star_mem_integralAdeles_iff, ← W.forall_selfDualAddChar_mul_eq_one_iff]
    intro u hu
    have hz : ∀ k, (Pi.single i u : n → 𝔸ᶠ[E]) k ∈ integralAdeles (𝓞 E) E := fun k ↦ by
      rcases eq_or_ne k i with rfl | hk
      · simpa using hu
      · simp [Pi.single_eq_of_ne hk]
    have h₁ := h _ hz
    rw [dotProduct_single, Pi.star_apply, Circle.coe_eq_one] at h₁
    exact h₁
  · rw [W.selfDualAddChar_eq_one_of_mem (dotProduct_mem (fun i ↦ by
      rw [Pi.star_apply]; exact star_mem_integralAdeles_iff.2 (hy i)) hz), Circle.coe_one]

end Datum

/-! ### The finite vacuum -/

/-- The **finite vacuum** on `𝔸_fⁿ`: the semicharacter `semi(z) = ψ₀(½ c₀ z* z)` on `Ôⁿ`,
extended by zero. -/
def finiteVacuum : (n → 𝔸ᶠ[E]) → ℂ :=
  (piIntegralAdeles (𝓞 E) E n : Set (n → 𝔸ᶠ[E])).indicator fun z ↦ (W.semichar z : ℂ)

/-- The finite vacuum is the extension by zero of the semicharacter on `Ôⁿ`. -/
theorem finiteVacuum_def :
    W.finiteVacuum n =
      (piIntegralAdeles (𝓞 E) E n : Set (n → 𝔸ᶠ[E])).indicator fun z ↦ (W.semichar z : ℂ) :=
  (rfl)

variable {n}

/-- On `Ôⁿ` the finite vacuum is the semicharacter. -/
theorem finiteVacuum_of_mem {z : n → 𝔸ᶠ[E]} (hz : z ∈ piIntegralAdeles (𝓞 E) E n) :
    W.finiteVacuum n z = W.semichar z :=
  Set.indicator_of_mem hz _

/-- Off `Ôⁿ` the finite vacuum vanishes. -/
theorem finiteVacuum_of_notMem {z : n → 𝔸ᶠ[E]} (hz : z ∉ piIntegralAdeles (𝓞 E) E n) :
    W.finiteVacuum n z = 0 :=
  Set.indicator_of_notMem hz _

variable [DecidableEq n] [MeasurableSpace (n → 𝔸ᶠ[E])] [OpensMeasurableSpace (n → 𝔸ᶠ[E])]
  [MeasurableAdd (n → 𝔸ᶠ[E])] {μ : Measure (n → 𝔸ᶠ[E])} [μ.IsAddLeftInvariant]

/-- **The finite vacuum is a vacuum** for the finite Heisenberg datum `β_f(x, y) = ψ₀(½ y* x)`
and every translation-invariant measure `μ` on `𝔸_fⁿ` giving `Ôⁿ` mass one. -/
theorem isVacuum_finiteVacuum (hμ : μ (piIntegralAdeles (𝓞 E) E n) = 1) :
    (W.finiteDatum n).IsVacuum μ (W.finiteVacuum n) := by
  rw [finiteVacuum_def]
  refine HeisenbergDatum.isVacuum_indicator _ (isOpen_piIntegralAdeles _ _ _) hμ
    (fun y hy ↦ (W.forall_finiteDatum_sq_eq_one_iff n y).1 hy)
    (by fun_prop) (fun a ha b hb ↦ ?_) (fun a ha ↦ ?_)
  · rw [mem_piIntegralAdeles] at ha hb
    rw [W.semichar_add_of_forall_mem ha hb, finiteDatum_apply, Circle.coe_mul, Circle.coe_mul]
  · rw [← Circle.coe_pow, W.semichar_sq_of_forall_mem (mem_piIntegralAdeles.1 ha),
      Circle.coe_one]

end TauCeti.WeilData
