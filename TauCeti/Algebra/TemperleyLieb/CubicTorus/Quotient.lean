/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.CubicTorus.Projection
public import TauCeti.Algebra.TemperleyLieb.CubicTorus.Trace
public import TauCeti.Algebra.TemperleyLieb.Trace.Radical
public import TauCeti.Algebra.TemperleyLieb.Trace.Star
public import Mathlib.Analysis.Complex.Order
-- Private: cosine quantum integer formulas and `cos (π / 6)` are proof-only.
import TauCeti.QuantumGroups.QuantumInteger.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The Jones quotient at `δ = √3` is the inversion-fixed cubic quantum torus

Building on `tr m x = (√3) ^ m * cubicScalarCoefficient (m - 1) (cubicHom m x)`
(`TauCeti.Algebra.TemperleyLieb.CubicTorus.Trace`) and the surjectivity, star-compatibility, and
dimension results (`TauCeti.Algebra.TemperleyLieb.CubicTorus.Projection`), this file establishes:

* Restriction of `cubicIncl N` to an injective tower inclusion
  `cubicFixedIncl N : cubicFixed N →ₐ[ℂ] cubicFixed (N + 1)` compatible with `cubicFixedAdjoint`
  and `strandIncl`.
* Positivity of every Markov trace at `δ = √3` (`IsMarkovTrace.map_star_mul_self_nonneg_sqrt_three`)
  and identification of its trace radical with `RingHom.ker (cubicHom m)`
  (`IsMarkovTrace.traceRadical_eq_ker_cubicHom`).
* The Jones quotient algebra equivalence
  `IsMarkovTrace.quotientCubicFixedEquiv : (TL_m(√3) ⧸ traceRadical) ≃ₐ[ℂ] cubicFixed (m - 1)` of
  complex dimension `(3 ^ (m - 1) + 1) / 2` (`finrank_quotient_traceRadical_sqrt_three`),
  packaged as `exists_cubicFixedModel`, and vanishing of `cubicHom 5 (jonesWenzl (√3 : ℂ) 5)`.

## Main definitions and results

* `TauCeti.TemperleyLieb.cubicFixedIncl`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.quotientCubicFixedEquiv`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.map_star_mul_self_nonneg_sqrt_three`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.traceRadical_eq_ker_cubicHom`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.finrank_quotient_traceRadical_sqrt_three`.
* `TauCeti.TemperleyLieb.exists_cubicFixedModel`, `TauCeti.TemperleyLieb.cubicHom_jonesWenzl_five`.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25; *A polynomial invariant
  for knots via von Neumann algebras*, Bull. Amer. Math. Soc. 12 (1985), 103–111.
* F. M. Goodman, P. de la Harpe, and V. F. R. Jones, *Coxeter Graphs and Towers of Algebras*,
  MSRI Publications 14, Springer (1989).
* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4.
-/

public section

open Multiplicative
open scoped ComplexOrder

namespace TauCeti.TemperleyLieb

/-! ### Adjoint compatibility and restricted tower inclusions -/

private def cubicExtendHom (N : ℕ) :
    Multiplicative (Fin N → ZMod 3) →* Multiplicative (Fin (N + 1) → ZMod 3) where
  toFun a := ofAdd (Fin.snoc a.toAdd 0)
  map_one' := toAdd.injective (funext fun i ↦ Fin.lastCases (by simp) (fun _ ↦ by simp) i)
  map_mul' _ _ := toAdd.injective (funext fun i ↦ Fin.lastCases (by simp) (fun _ ↦ by simp) i)

private theorem cubicExtendHom_injective (N : ℕ) : Function.Injective (cubicExtendHom N) :=
  fun _ _ h ↦ toAdd.injective (funext fun i ↦ by
    simpa [cubicExtendHom] using congrFun (congrArg toAdd h) i.castSucc)

private theorem cubicFactor_cubicExtendHom (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor (N + 1) (cubicExtendHom N a) (cubicExtendHom N b) = cubicFactor N a b := by
  rw [cubicFactor_apply, cubicFactor_apply]
  exact congrArg (fun z ↦ cubeRootPow (2 * z)) (chainForm_snoc_zero a.toAdd b.toAdd)

private theorem cubicIncl_eq_mapDomain (N : ℕ) :
    cubicIncl N =
      TwistedMonoidAlgebra.mapDomain (cubicExtendHom N) (cubicFactor_cubicExtendHom N) :=
  TwistedMonoidAlgebra.algHom_ext fun a ↦ by
    rw [of_eq_weyl, cubicIncl_weyl, ← of_eq_weyl (N := N) a, TwistedMonoidAlgebra.mapDomain_of,
      of_eq_weyl]
    rfl

theorem cubicIncl_injective (N : ℕ) : Function.Injective (cubicIncl N) := by
  rw [cubicIncl_eq_mapDomain]
  exact TwistedMonoidAlgebra.mapDomain_injective (cubicFactor_cubicExtendHom N)
    (cubicExtendHom_injective N)

@[simp] theorem cubicAdjoint_cubicIncl (N : ℕ) (x : CubicTorus N) :
    cubicAdjoint (N + 1) (cubicIncl N x) = cubicIncl N (cubicAdjoint N x) := by
  rw [cubicIncl_eq_mapDomain]
  exact TwistedMonoidAlgebra.conjReverse_mapDomain (cubicExtendHom N)
    (cubicFactor_cubicExtendHom N) x

theorem cubicIncl_mem_cubicFixed {N : ℕ} {x : CubicTorus N} (hx : x ∈ cubicFixed N) :
    cubicIncl N x ∈ cubicFixed (N + 1) := by
  rw [mem_cubicFixed, cubicInversion_cubicIncl, mem_cubicFixed.mp hx]

/-- **The restricted tower inclusion** `cubicFixed N →ₐ[ℂ] cubicFixed (N + 1)`. -/
noncomputable def cubicFixedIncl (N : ℕ) : cubicFixed N →ₐ[ℂ] cubicFixed (N + 1) :=
  ((cubicIncl N).comp (cubicFixed N).val).codRestrict (cubicFixed (N + 1))
    fun x ↦ cubicIncl_mem_cubicFixed x.property

@[simp] theorem coe_cubicFixedIncl (N : ℕ) (x : cubicFixed N) :
    (cubicFixedIncl N x : CubicTorus (N + 1)) = cubicIncl N x := (rfl)

theorem cubicFixedIncl_injective (N : ℕ) : Function.Injective (cubicFixedIncl N) := fun _ _ h ↦
  Subtype.ext (cubicIncl_injective N (congrArg Subtype.val h))

@[simp] theorem cubicFixedAdjoint_cubicFixedIncl (N : ℕ) (x : cubicFixed N) :
    cubicFixedAdjoint (N + 1) (cubicFixedIncl N x) = cubicFixedIncl N (cubicFixedAdjoint N x) :=
  Subtype.ext (by
    rw [coe_cubicFixedAdjoint, coe_cubicFixedIncl, coe_cubicFixedIncl, coe_cubicFixedAdjoint,
      cubicAdjoint_cubicIncl])

/-- `cubicHom` intertwines `TemperleyLieb.strandIncl` with `cubicFixedIncl`. -/
theorem cubicHom_strandIncl_eq_cubicFixedIncl (n : ℕ)
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) (n + 1)) :
    cubicHom (n + 2) (strandIncl x) = cubicFixedIncl n (cubicHom (n + 1) x) :=
  Subtype.ext (cubicHom_strandIncl n x)

/-! ### Positivity, kernel = trace radical, and the Jones quotient equivalence -/

namespace IsMarkovTrace

variable {tr : ∀ n : ℕ, TemperleyLieb ℂ (Real.sqrt 3 : ℂ) n →ₗ[ℂ] ℂ}

private theorem cubicScalarCoefficient_eq_scalarTrace (N : ℕ) :
    cubicScalarCoefficient N =
      TwistedMonoidAlgebra.scalarTrace ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N) :=
  (TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)).ext fun g ↦ by
    classical
    rw [TwistedMonoidAlgebra.basis_apply, of_eq_weyl, cubicScalarCoefficient_weyl, ← of_eq_weyl,
      TwistedMonoidAlgebra.scalarTrace_of]
    have hg : g.toAdd = 0 ↔ g = 1 := ⟨fun h ↦ toAdd.injective (by simp [h]), fun h ↦ by simp [h]⟩
    simp [hg]

/-- **Positivity of the Markov trace at `δ = √3`**: `0 ≤ tr m (star x * x)` on every `m`. -/
theorem map_star_mul_self_nonneg_sqrt_three
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) {m : ℕ}
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    0 ≤ tr m (star x * x) := by
  have hz := TwistedMonoidAlgebra.scalarTrace_conjReverse_mul_self_nonneg
    (cubicFactor_inv_self (m - 1)) (cubicHom m x)
  rw [← cubicScalarCoefficient_eq_scalarTrace] at hz
  have hz0 : ((0 : ℝ) : ℂ) ≤
      cubicScalarCoefficient (m - 1) (cubicAdjoint (m - 1) (cubicHom m x) * cubicHom m x) := by
    simpa using hz
  rw [htr.apply_eq_mul_cubicScalarCoefficient_cubicHom, map_mul,
    Subalgebra.coe_mul, coe_cubicHom_star, Complex.eq_re_of_ofReal_le hz0,
    ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.zero_le_real]
  exact mul_nonneg (by positivity) (Complex.nonneg_iff.mp hz).left

/-- At `δ = √3`, `tr m (star x * x) = 0` if and only if `cubicHom m x = 0`. -/
theorem map_star_mul_self_eq_zero_iff_cubicHom_eq_zero
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) {m : ℕ}
    {x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m} :
    tr m (star x * x) = 0 ↔ cubicHom m x = 0 := by
  have hne : (Real.sqrt 3 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  rw [htr.apply_eq_mul_cubicScalarCoefficient_cubicHom, map_mul,
    Subalgebra.coe_mul, coe_cubicHom_star, mul_eq_zero, or_iff_right (pow_ne_zero m hne),
    cubicScalarCoefficient_eq_scalarTrace,
    TwistedMonoidAlgebra.scalarTrace_conjReverse_mul_self_eq_zero_iff
      (cubicFactor_inv_self (m - 1)), ZeroMemClass.coe_eq_zero]

/-- **The trace radical at `δ = √3` is the kernel of `cubicHom`.** -/
theorem traceRadical_eq_ker_cubicHom
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) :
    (tr m).traceRadical (htr.map_mul_comm m) = RingHom.ker (cubicHom m) := by
  ext x
  rw [LinearMap.mem_traceRadical, RingHom.mem_ker]
  refine ⟨fun hx ↦ ?_, fun hx y ↦ ?_⟩
  · rw [← htr.map_star_mul_self_eq_zero_iff_cubicHom_eq_zero, htr.map_mul_comm]
    exact hx (star x)
  · rw [htr.apply_eq_mul_cubicScalarCoefficient_cubicHom, map_mul, hx, zero_mul,
      Subalgebra.coe_zero, map_zero, mul_zero]

/-- At `δ = √3`, the null vectors of `x ↦ tr m (star x * x)` are precisely the trace radical. -/
theorem map_star_mul_self_eq_zero_iff_mem_traceRadical_sqrt_three
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) {m : ℕ}
    {x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m} :
    tr m (star x * x) = 0 ↔ x ∈ (tr m).traceRadical (htr.map_mul_comm m) := by
  rw [htr.map_star_mul_self_eq_zero_iff_cubicHom_eq_zero,
    htr.traceRadical_eq_ker_cubicHom, RingHom.mem_ker]

/-- **The Jones quotient at `δ = √3` is isomorphic to `cubicFixed (m - 1)`.** -/
noncomputable def quotientCubicFixedEquiv
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) :
    (TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m ⧸ (tr m).traceRadical (htr.map_mul_comm m)) ≃ₐ[ℂ]
      cubicFixed (m - 1) :=
  (Ideal.quotientEquivAlgOfEq ℂ (htr.traceRadical_eq_ker_cubicHom m)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (cubicHom_surjective m))

@[simp] theorem quotientCubicFixedEquiv_mk
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ)
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    htr.quotientCubicFixedEquiv m
        (Ideal.Quotient.mk ((tr m).traceRadical (htr.map_mul_comm m)) x) =
      cubicHom m x := by
  simp [quotientCubicFixedEquiv, Ideal.quotientEquivAlgOfEq_mk]

/-- `quotientCubicFixedEquiv` intertwines `quotientStrandIncl` with `cubicFixedIncl`. -/
theorem quotientCubicFixedEquiv_quotientStrandIncl
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (n : ℕ)
    (q : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) (n + 1) ⧸
      (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) :
    htr.quotientCubicFixedEquiv (n + 2) (htr.quotientStrandIncl n q) =
      cubicFixedIncl n (htr.quotientCubicFixedEquiv (n + 1) q) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [htr.quotientStrandIncl_mk, htr.quotientCubicFixedEquiv_mk, htr.quotientCubicFixedEquiv_mk,
    cubicHom_strandIncl_eq_cubicFixedIncl]

@[simp] theorem quotientCubicFixedEquiv_symm_cubicHom
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ)
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    (htr.quotientCubicFixedEquiv m).symm (cubicHom m x) =
      Ideal.Quotient.mk ((tr m).traceRadical (htr.map_mul_comm m)) x :=
  (htr.quotientCubicFixedEquiv m).injective (by simp)

/-- `(quotientCubicFixedEquiv _).symm` intertwines `cubicFixedIncl` with `quotientStrandIncl`. -/
theorem quotientCubicFixedEquiv_symm_cubicFixedIncl
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (n : ℕ) (y : cubicFixed n) :
    (htr.quotientCubicFixedEquiv (n + 2)).symm (cubicFixedIncl n y) =
      htr.quotientStrandIncl n ((htr.quotientCubicFixedEquiv (n + 1)).symm y) :=
  (htr.quotientCubicFixedEquiv (n + 2)).injective <| by
    rw [AlgEquiv.apply_symm_apply, htr.quotientCubicFixedEquiv_quotientStrandIncl,
      AlgEquiv.apply_symm_apply]

/-- The induced trace on the `m`-strand quotient at `δ = √3` is `(√3 : ℂ) ^ m` times
`cubicScalarCoefficient (m - 1)` under `quotientCubicFixedEquiv`. -/
theorem quotientTrace_eq_mul_cubicScalarCoefficient_quotientCubicFixedEquiv
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ)
    (q : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m ⧸
      (tr m).traceRadical (htr.map_mul_comm m)) :
    (tr m).quotientTrace (htr.map_mul_comm m) q =
      (Real.sqrt 3 : ℂ) ^ m *
        cubicScalarCoefficient (m - 1) (htr.quotientCubicFixedEquiv m q) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp [htr.apply_eq_mul_cubicScalarCoefficient_cubicHom]

@[simp] theorem quotientTrace_quotientCubicFixedEquiv_symm
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) (x : cubicFixed (m - 1)) :
    (tr m).quotientTrace (htr.map_mul_comm m) ((htr.quotientCubicFixedEquiv m).symm x) =
      (Real.sqrt 3 : ℂ) ^ m * cubicScalarCoefficient (m - 1) x := by
  simp [htr.quotientTrace_eq_mul_cubicScalarCoefficient_quotientCubicFixedEquiv]

/-- The `m`-strand trace quotient at `δ = √3` has complex dimension `(3 ^ (m - 1) + 1) / 2`. -/
@[simp] theorem finrank_quotient_traceRadical_sqrt_three
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) :
    Module.finrank ℂ
        (TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m ⧸ (tr m).traceRadical (htr.map_mul_comm m)) =
      (3 ^ (m - 1) + 1) / 2 := by
  rw [(htr.quotientCubicFixedEquiv m).toLinearEquiv.finrank_eq, finrank_cubicFixed]

end IsMarkovTrace

/-! ### Packaged cubic fixed-point model and vanishing of the five-strand Jones–Wenzl projection -/

/-- **The cubic quantum torus model of `TemperleyLieb ℂ (√3 : ℂ) m`.** For every Markov trace `tr`
at loop value `√3` and every `m : ℕ`, there is a surjective `ℂ`-algebra homomorphism
`F : TemperleyLieb ℂ (√3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1)` sending `e j` to
`(√3 : ℂ) • cubicProjection (m - 1) j`, intertwining `star` with `cubicAdjoint (m - 1)`, expressing
`tr m` via `cubicScalarCoefficient (m - 1)`, and having kernel `(tr m).traceRadical`. -/
theorem exists_cubicFixedModel
    {tr : ∀ n : ℕ, TemperleyLieb ℂ (Real.sqrt 3 : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) :
    ∃ F : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1),
      Function.Surjective F ∧
      (∀ j : Fin (m - 1),
        (F (e (Real.sqrt 3 : ℂ) j) : CubicTorus (m - 1)) =
          (Real.sqrt 3 : ℂ) • cubicProjection (m - 1) j) ∧
      (∀ x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m,
        (F (star x) : CubicTorus (m - 1)) = cubicAdjoint (m - 1) (F x)) ∧
      (∀ x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m,
        tr m x = (Real.sqrt 3 : ℂ) ^ m * cubicScalarCoefficient (m - 1) (F x)) ∧
      RingHom.ker F = (tr m).traceRadical (htr.map_mul_comm m) :=
  ⟨cubicHom m, cubicHom_surjective m, coe_cubicHom_e m, coe_cubicHom_star,
    htr.apply_eq_mul_cubicScalarCoefficient_cubicHom m,
    (htr.traceRadical_eq_ker_cubicHom m).symm⟩

/-- At `δ = √3`, `cubicHom 5` maps the five-strand Jones–Wenzl projection to `0`. -/
@[simp] theorem cubicHom_jonesWenzl_five :
    cubicHom 5 (jonesWenzl (Real.sqrt 3 : ℂ) 5) = 0 := by
  have hsqrt : (Real.sqrt 3 : ℝ) = 2 * Real.cos (Real.pi / (6 : ℕ)) := by
    rw [Nat.cast_ofNat, Real.cos_pi_div_six]; ring
  have hcoe : (Real.sqrt 3 : ℂ) = Complex.ofRealHom (2 * Real.cos (Real.pi / (6 : ℕ))) := by
    rw [← hsqrt]; rfl
  have hunits : ∀ k ∈ Finset.Icc 1 5, IsUnit (qInt ℂ (Real.sqrt 3 : ℂ) k) := by
    intro k hk
    obtain ⟨hk1, hk5⟩ := Finset.mem_Icc.mp hk
    rw [hcoe, ← Complex.ofRealHom.map_qInt, isUnit_iff_ne_zero]
    exact Complex.ofReal_ne_zero.mpr (qInt_two_mul_cos_pi_div_pos (by omega) (by omega)).ne'
  rw [← RingHom.mem_ker, ← isMarkovTrace_cubicTrace.traceRadical_eq_ker_cubicHom 5,
    isMarkovTrace_cubicTrace.jonesWenzl_mem_traceRadical_iff hunits, hcoe,
    ← Complex.ofRealHom.map_qInt, qInt_two_mul_cos_pi_div_eq_zero (by decide), map_zero]

end TauCeti.TemperleyLieb
