/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.HeisenbergModel.LatticeVacuum
public import TauCeti.NumberTheory.NumberField.CMField.HeisenbergDatum
public import TauCeti.NumberTheory.NumberField.CMField.UnitaryGroup.WeilData
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Haar
import TauCeti.NumberTheory.NumberField.Countable

/-!
# The finite datum and the lattice vacuum of Weil data

Let `E` be a CM field with Weil data `(j, α, υ)`, finite adeles `𝔸_f`, integral finite adeles `Ô`,
`t = j α (conj α)` and `ψ₀(z) = ψ_f(t z)` (`TauCeti.WeilData.selfDualAddChar`), for which `Ô` is
self-dual. For a finite type `n`, the **finite datum** is the Heisenberg datum

`β_f(x, y) = ψ₀(½ y* x)`

on `𝔸_f^n`, where `y* x = Σ_i conj y_i x_i` (`TauCeti.WeilData.finiteDatum`). It is the finite
part `ψ_f(½ j · y* x)` of the adelic Heisenberg datum read in the finite coordinates `x = α z`
(`TauCeti.WeilData.finiteHeisenbergDatum_smul_smul_eq_finiteDatum`). The **lattice vacuum** is
the extension by zero of the semicharacter `semi(z) = ψ₀(½ c₀ z* z)` from `Ô^n`
(`TauCeti.WeilData.latticeVacuum`):

`e_f(z) = semi(z)` for `z ∈ Ô^n`, and `e_f(z) = 0` otherwise.

The main result is that `e_f` is a vacuum for `β_f` and every translation-invariant measure `λ`
on `𝔸_f^n` with `λ(Ô^n) = 1` (`TauCeti.WeilData.isVacuum_latticeVacuum`), in particular for the
product of the Haar measures of `𝔸_f` normalised by `Ô`, which is an instance
(`TauCeti.WeilData.isVacuum_latticeVacuum_pi`), so that the reproducing model of `(β_f, λ, e_f)`
is available. It is an instance of the abstract lattice vacuum
`TauCeti.HeisenbergDatum.isVacuum_indicator`, whose hypotheses hold here:

* `Ô^n` is self-dual for `β_f²` (`TauCeti.WeilData.forall_finiteDatum_sq_eq_one_iff`), by the
  self-duality of `Ô` for `ψ₀` (`TauCeti.WeilData.forall_selfDualAddChar_mul_eq_one_iff`) and the
  stability of `Ô` under conjugation;
* the semicharacter satisfies `semi(a + b) = semi(a) semi(b) β_f(a, b)` on `Ô^n`
  (`TauCeti.WeilData.semichar_add_of_mem`), as `c₀ + conj c₀ = 1`, `ψ₀(conj z) = ψ₀(z)⁻¹`
  (`TauCeti.WeilData.selfDualAddChar_star`) and `ψ₀` is trivial on `Ô`;
* `semi(a)² = ψ₀(c₀ a* a) = 1` on `Ô^n` (`TauCeti.WeilData.semichar_sq_of_mem`), as `c₀` is
  integral.

## Main definitions

* `TauCeti.WeilData.finiteDatum`: the finite datum `β_f(x, y) = ψ₀(½ y* x)` on `𝔸_f^n`.
* `TauCeti.WeilData.latticeVacuum`: the lattice vacuum `e_f`.

## Main results

* `NumberField.IsCMField.star_dotProduct_mem_integralAdeles`: `a* b` is integral for integral
  vectors `a` and `b`.
* `TauCeti.WeilData.finiteDatum_sq`, `TauCeti.WeilData.forall_finiteDatum_sq_eq_one_iff`:
  `β_f(x, y)² = ψ₀(y* x)`, and `Ô^n` is self-dual for `β_f²`.
* `TauCeti.WeilData.finiteHeisenbergDatum_smul_smul_eq_finiteDatum`: the finite datum is the finite
  part of the adelic Heisenberg datum in finite coordinates.
* `TauCeti.WeilData.semichar_add_of_mem`, `TauCeti.WeilData.semichar_sq_of_mem`: the laws of the
  semicharacter on `Ô^n`.
* `TauCeti.WeilData.isVacuum_latticeVacuum`, `TauCeti.WeilData.isVacuum_latticeVacuum_pi`: the
  lattice vacuum is a vacuum for the finite datum.

## Attribution

The finite datum and the lattice vacuum follow `New.stdLattice.finHeisenberg`,
`New.stdLattice.finVac` and `New.stdLattice.isVacuum_finVac` in
`src/Lib/Weil/Construction/FiniteMultiplier.lean` of grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC). The proof here
reduces to the abstract lattice vacuum `TauCeti.HeisenbergDatum.isVacuum_indicator` and was
written independently.

## References

* A. Weil, *Sur certains groupes d'opérateurs unitaires*, Acta Math. 111 (1964), 143–211.
-/

public section

noncomputable section

open IsDedekindDomain IsDedekindDomain.FiniteAdeleRing NumberField MeasureTheory Matrix
open TauCeti.GlobalNumberFields
open scoped NumberField.AdeleRing

namespace NumberField.IsCMField

/-- `a* b = Σ_i conj a_i b_i` is integral for integral vectors `a` and `b`. -/
theorem star_dotProduct_mem_integralAdeles {E n : Type*} [Field E] [NumberField E] [IsCMField E]
    [Fintype n] {a b : n → 𝔸ᶠ[E]}
    (ha : ∀ i, a i ∈ integralAdeles (𝓞 E) E) (hb : ∀ i, b i ∈ integralAdeles (𝓞 E) E) :
    star a ⬝ᵥ b ∈ integralAdeles (𝓞 E) E :=
  Subalgebra.sum_mem _ fun i _ ↦
    Subalgebra.mul_mem _ (star_mem_integralAdeles_iff.2 (ha i)) (hb i)

end NumberField.IsCMField

namespace TauCeti

namespace WeilData

variable {E : Type*} [Field E] [NumberField E] [IsCMField E] {Φ : CMType E} (W : WeilData Φ)
  {n : Type*} [Fintype n]

/-! ### The semicharacter on `Ô^n` -/

/-- The semicharacter squares to one on `Ô^n`: `semi(a)² = ψ₀(c₀ a* a) = 1`, as `c₀` is
integral. -/
theorem semichar_sq_of_mem {a : n → 𝔸ᶠ[E]} (ha : ∀ i, a i ∈ integralAdeles (𝓞 E) E) :
    W.semichar a ^ 2 = 1 := by
  rw [semichar_sq, W.selfDualAddChar_eq_one_of_mem (Subalgebra.mul_mem _
    W.algebraMap_traceOne_mem_integralAdeles (IsCMField.star_dotProduct_mem_integralAdeles ha ha))]

/-! ### The lattice vacuum -/

variable (n) in
/-- The **lattice vacuum** `e_f` on `𝔸_f^n`: the semicharacter `semi(z) = ψ₀(½ c₀ z* z)` on `Ô^n`,
extended by zero. -/
def latticeVacuum : (n → 𝔸ᶠ[E]) → ℂ :=
  (Set.univ.pi fun _ ↦ (integralAdeles (𝓞 E) E : Set 𝔸ᶠ[E])).indicator fun z ↦ (W.semichar z : ℂ)

/-- The lattice vacuum is the extension by zero of the semicharacter from `Ô^n`. -/
theorem latticeVacuum_def :
    W.latticeVacuum n = (Set.univ.pi fun _ ↦ (integralAdeles (𝓞 E) E : Set 𝔸ᶠ[E])).indicator
      fun z ↦ (W.semichar z : ℂ) :=
  (rfl)

/-- The lattice vacuum is the semicharacter on `Ô^n`. -/
theorem latticeVacuum_of_forall_mem {z : n → 𝔸ᶠ[E]} (hz : ∀ i, z i ∈ integralAdeles (𝓞 E) E) :
    W.latticeVacuum n z = W.semichar z := by
  rw [latticeVacuum_def]
  exact Set.indicator_of_mem (Set.mem_univ_pi.2 hz) _

/-- The lattice vacuum vanishes off `Ô^n`. -/
theorem latticeVacuum_of_not_forall_mem {z : n → 𝔸ᶠ[E]}
    (hz : ¬∀ i, z i ∈ integralAdeles (𝓞 E) E) : W.latticeVacuum n z = 0 := by
  rw [latticeVacuum_def]
  exact Set.indicator_of_notMem (fun h ↦ hz (Set.mem_univ_pi.1 h)) _

/-! ### The finite datum -/

/-- `½ t = ½ j α (conj α)` is purely imaginary. -/
theorem half_mul_scaleIdele_mem_skewAdjoint :
    algebraMap E 𝔸ᶠ[E] 2⁻¹ * W.scaleIdele ∈ skewAdjoint 𝔸ᶠ[E] := by
  rw [skewAdjoint.mem_iff, star_mul, skewAdjoint.mem_iff.1 W.scaleIdele_mem_skewAdjoint,
    ← algebraMap_star_comm, star_inv₀, star_ofNat]
  ring

variable [DecidableEq n]

variable (n) in
/-- The **finite datum** `β_f(x, y) = ψ₀(½ y* x)` on `𝔸_f^n`, where `y* x = Σ_i conj y_i x_i`:
the Heisenberg datum `ψ_f(½ t · y* x)` of the skew-adjoint finite adele `½ t`. -/
def finiteDatum : HeisenbergDatum (n → 𝔸ᶠ[E]) :=
  finiteHeisenbergDatum n _ W.half_mul_scaleIdele_mem_skewAdjoint

/-- The defining formula `β_f(x, y) = ψ₀(½ y* x)`. -/
@[simp]
theorem finiteDatum_apply (x y : n → 𝔸ᶠ[E]) :
    W.finiteDatum n x y = W.selfDualAddChar (algebraMap E 𝔸ᶠ[E] 2⁻¹ * (star y ⬝ᵥ x)) := by
  rw [finiteDatum, finiteHeisenbergDatum_apply, selfDualAddChar_apply, mul_left_comm, mul_assoc]

/-- `β_f(x, y)² = ψ₀(y* x)`. -/
theorem finiteDatum_sq (x y : n → 𝔸ᶠ[E]) :
    W.finiteDatum n x y ^ 2 = W.selfDualAddChar (star y ⬝ᵥ x) := by
  rw [finiteDatum_apply, ← Circle.coe_pow, selfDualAddChar_half_mul_sq]

/-- In the finite coordinates `x = α z`, the finite part `ψ_f(½ j · y* x)` of the adelic
Heisenberg datum (`TauCeti.adelicHeisenbergDatum`) is the finite datum:
`ψ_f(½ j · (α y)* (α x)) = β_f(x, y)`. -/
theorem finiteHeisenbergDatum_smul_smul_eq_finiteDatum
    (ht : algebraMap E 𝔸ᶠ[E] (2⁻¹ * W.j) ∈ skewAdjoint 𝔸ᶠ[E]) (x y : n → 𝔸ᶠ[E]) :
    finiteHeisenbergDatum n _ ht ((W.α : 𝔸ᶠ[E]) • x) ((W.α : 𝔸ᶠ[E]) • y) =
      W.finiteDatum n x y := by
  rw [finiteHeisenbergDatum_smul_smul, finiteHeisenbergDatum_apply, finiteDatum_apply,
    selfDualAddChar_apply, coe_scaleIdele, map_mul (algebraMap E 𝔸ᶠ[E])]
  congr 2
  ring

/-- **`Ô^n` is self-dual for `β_f²`**: `β_f(z, y)² = ψ₀(y* z) = 1` for every `z ∈ Ô^n` exactly when
`y ∈ Ô^n`. This is the self-duality of `Ô` for `ψ₀`, applied to `conj y_i`. -/
theorem forall_finiteDatum_sq_eq_one_iff {y : n → 𝔸ᶠ[E]} :
    (∀ z : n → 𝔸ᶠ[E], (∀ i, z i ∈ integralAdeles (𝓞 E) E) → W.finiteDatum n z y ^ 2 = 1) ↔
      ∀ i, y i ∈ integralAdeles (𝓞 E) E := by
  refine ⟨fun hy i ↦ ?_, fun hy z hz ↦ ?_⟩
  · rw [← IsCMField.star_mem_integralAdeles_iff, ← W.forall_selfDualAddChar_mul_eq_one_iff]
    intro u hu
    have hz : ∀ k, Pi.single (M := fun _ ↦ 𝔸ᶠ[E]) i u k ∈ integralAdeles (𝓞 E) E := fun k ↦ by
      rcases eq_or_ne k i with rfl | hk
      · rw [Pi.single_eq_same]
        exact hu
      · rw [Pi.single_eq_of_ne hk]
        exact zero_mem _
    have h := hy _ hz
    rw [finiteDatum_sq, dotProduct_single, Pi.star_apply] at h
    exact Circle.coe_eq_one.1 h
  · rw [finiteDatum_sq,
      W.selfDualAddChar_eq_one_of_mem (IsCMField.star_dotProduct_mem_integralAdeles hy hz),
      Circle.coe_one]

/-! ### The lattice vacuum is a vacuum -/

/-- **The law of the semicharacter**: `semi(a + b) = semi(a) semi(b) β_f(a, b)` for
`a, b ∈ Ô^n`. -/
theorem semichar_add_of_mem {a b : n → 𝔸ᶠ[E]} (ha : ∀ i, a i ∈ integralAdeles (𝓞 E) E)
    (hb : ∀ i, b i ∈ integralAdeles (𝓞 E) E) :
    (W.semichar (a + b) : ℂ) = W.semichar a * W.semichar b * W.finiteDatum n a b := by
  -- With `u = c₀ a* b`, the exponent of `semi(a + b)` exceeds those of `semi(a) semi(b) β_f(a, b)`
  -- by `½ u − conj(½ u)`, as `conj c₀ = 1 − c₀`; and `ψ₀(½ u − conj(½ u)) = ψ₀(½ u)² = ψ₀(u) = 1`.
  set u := algebraMap E 𝔸ᶠ[E] W.traceOne * (star a ⬝ᵥ b)
  have hu : W.selfDualAddChar u = 1 := W.selfDualAddChar_eq_one_of_mem
    (Subalgebra.mul_mem _ W.algebraMap_traceOne_mem_integralAdeles
      (IsCMField.star_dotProduct_mem_integralAdeles ha hb))
  have hc : star (algebraMap E 𝔸ᶠ[E] W.traceOne) = algebraMap E 𝔸ᶠ[E] (1 - W.traceOne) := by
    rw [← algebraMap_star_comm, ← W.traceOne_add_star, add_sub_cancel_left]
  have hstar : star (algebraMap E 𝔸ᶠ[E] 2⁻¹ * u) =
      algebraMap E 𝔸ᶠ[E] 2⁻¹ * (algebraMap E 𝔸ᶠ[E] (1 - W.traceOne) * (star b ⬝ᵥ a)) := by
    have hab : star (star a ⬝ᵥ b) = star b ⬝ᵥ a := (star_dotProduct b a).symm
    have h2 : star (algebraMap E 𝔸ᶠ[E] 2⁻¹) = algebraMap E 𝔸ᶠ[E] 2⁻¹ := by
      rw [← algebraMap_star_comm, star_inv₀, star_ofNat]
    rw [star_mul, star_mul, hc, hab, h2]
    ring
  have hdefect :
      W.selfDualAddChar (algebraMap E 𝔸ᶠ[E] 2⁻¹ * u - star (algebraMap E 𝔸ᶠ[E] 2⁻¹ * u)) = 1 := by
    rw [AddChar.map_sub_eq_div, selfDualAddChar_star, div_inv_eq_mul, ← sq,
      selfDualAddChar_half_mul_sq, hu]
  have hsplit : algebraMap E 𝔸ᶠ[E] (W.traceOne / 2) * (star (a + b) ⬝ᵥ (a + b)) =
      algebraMap E 𝔸ᶠ[E] (W.traceOne / 2) * (star a ⬝ᵥ a) +
        algebraMap E 𝔸ᶠ[E] (W.traceOne / 2) * (star b ⬝ᵥ b) +
        algebraMap E 𝔸ᶠ[E] 2⁻¹ * (star b ⬝ᵥ a) +
        (algebraMap E 𝔸ᶠ[E] 2⁻¹ * u - star (algebraMap E 𝔸ᶠ[E] 2⁻¹ * u)) := by
    simp only [hstar, star_add, add_dotProduct, dotProduct_add, map_sub, map_one, div_eq_mul_inv,
      map_mul, u]
    ring
  rw [semichar_eq_selfDualAddChar_dotProduct, hsplit]
  simp only [AddChar.map_add_eq_mul, hdefect, mul_one, finiteDatum_apply,
    ← semichar_eq_selfDualAddChar_dotProduct, Circle.coe_mul]

/-- **The lattice vacuum is a vacuum** for the finite datum `β_f` and every translation-invariant
measure `λ` on `𝔸_f^n` with `λ(Ô^n) = 1`. -/
theorem isVacuum_latticeVacuum (μ : Measure (n → 𝔸ᶠ[E])) [μ.IsAddLeftInvariant]
    (hμ : μ (Set.univ.pi fun _ ↦ (integralAdeles (𝓞 E) E : Set 𝔸ᶠ[E])) = 1) :
    (W.finiteDatum n).IsVacuum μ (W.latticeVacuum n) := by
  -- `Ô^n` as an additive subgroup, to apply the abstract lattice vacuum
  let L : AddSubgroup (n → 𝔸ᶠ[E]) :=
    AddSubgroup.pi Set.univ fun _ ↦ (integralAdeles (𝓞 E) E).toSubring.toAddSubgroup
  have hmem {z : n → 𝔸ᶠ[E]} : z ∈ L ↔ ∀ i, z i ∈ integralAdeles (𝓞 E) E := by
    simp [L, AddSubgroup.mem_pi]
  have hL : (L : Set (n → 𝔸ᶠ[E])) = Set.univ.pi fun _ ↦ (integralAdeles (𝓞 E) E : Set 𝔸ᶠ[E]) :=
    Set.ext fun z ↦ hmem.trans Set.mem_univ_pi.symm
  have h := (W.finiteDatum n).isVacuum_indicator (L := L) (σ := fun z ↦ (W.semichar z : ℂ))
    (μ := μ) (by rw [hL]; exact isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_integralAdeles _ _)
    (by rw [hL]; exact hμ)
    (fun y hy ↦ hmem.2 (W.forall_finiteDatum_sq_eq_one_iff.1 fun z hz ↦ hy z (hmem.2 hz)))
    (by fun_prop) (fun a ha b hb ↦ W.semichar_add_of_mem (hmem.1 ha) (hmem.1 hb))
    (fun a ha ↦ by rw [← Circle.coe_pow, W.semichar_sq_of_mem (hmem.1 ha), Circle.coe_one])
  rw [latticeVacuum_def, ← hL]
  exact h

/-- The lattice vacuum is a vacuum for the finite datum and the product `λ` of the Haar measures
of `𝔸_f` normalised by `Ô`, which is the Haar measure on `𝔸_f^n` with `λ(Ô^n) = 1`. -/
instance isVacuum_latticeVacuum_pi :
    (W.finiteDatum n).IsVacuum
      (Measure.pi fun _ : n ↦ Measure.addHaarMeasure (integralAdelesPositiveCompacts (𝓞 E) E))
      (W.latticeVacuum n) :=
  W.isVacuum_latticeVacuum _ <| by
    rw [Measure.pi_pi]
    simp [← coe_integralAdelesPositiveCompacts, Measure.addHaarMeasure_self]

end WeilData

end TauCeti
