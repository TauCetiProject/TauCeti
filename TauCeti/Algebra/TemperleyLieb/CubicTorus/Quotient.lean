/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.CubicTorus.Projection
public import TauCeti.Algebra.TemperleyLieb.CubicTorus.Trace
public import TauCeti.Algebra.TemperleyLieb.Positivity
public import TauCeti.Algebra.TemperleyLieb.Trace.Radical

/-!
# The Jones quotient at `δ = √3` is the inversion-fixed cubic quantum torus

Building on `tr m x = (√3) ^ m * cubicScalarCoefficient (m - 1) (cubicHom m x)`
(`TauCeti.Algebra.TemperleyLieb.CubicTorus.Trace`) and the surjectivity, star-compatibility, and
dimension results (`TauCeti.Algebra.TemperleyLieb.CubicTorus.Projection`), this file establishes:

* Identification of the trace radical of every Markov trace at `δ = √3` with
  `RingHom.ker (cubicHom m)` (`IsMarkovTrace.traceRadical_eq_ker_cubicHom`).
* The Jones quotient algebra equivalence `IsMarkovTrace.quotientCubicFixedEquiv` between
  `TL_m(√3) ⧸ traceRadical` and `cubicFixed (m - 1)` of complex dimension
  `(3 ^ (m - 1) + 1) / 2` (`finrank_quotient_traceRadical_sqrt_three`), compatibility with `star`
  (`quotientCubicFixedEquiv_star`), packaged as `exists_cubicFixedModel`, and vanishing of
  `cubicHom 5 (jonesWenzl (√3 : ℂ) 5)`.

## Main definitions and results

* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientCubicFixedEquiv`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.traceRadical_eq_ker_cubicHom`,
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

open scoped ComplexOrder

namespace TauCeti.TemperleyLieb

/-! ### Kernel = trace radical and the Jones quotient equivalence -/

namespace IsMarkovTrace

variable {tr : ∀ n : ℕ, TemperleyLieb ℂ (Real.sqrt 3 : ℂ) n →ₗ[ℂ] ℂ}

/-- At `δ = √3`, `tr m (star x * x) = 0` if and only if `cubicHom m x = 0`. -/
theorem map_star_mul_self_eq_zero_iff_cubicHom_eq_zero
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) {m : ℕ}
    {x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m} :
    tr m (star x * x) = 0 ↔ cubicHom m x = 0 := by
  rw [htr.apply_eq_mul_cubicScalarCoefficient_cubicHom, map_mul,
    Subalgebra.coe_mul, coe_cubicHom_star, mul_eq_zero,
    or_iff_right (pow_ne_zero m sqrt_three_ne_zero),
    cubicScalarCoefficient_cubicAdjoint_mul_self_eq_zero_iff, ZeroMemClass.coe_eq_zero]

/-- **The trace radical at `δ = √3` is the kernel of `cubicHom`.** -/
theorem traceRadical_eq_ker_cubicHom
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) :
    (tr m).traceRadical (htr.map_mul_comm m) = RingHom.ker (cubicHom m) := by
  ext x
  rw [htr.mem_traceRadical_iff_map_star_mul_self_eq_zero sqrt_three_mem_jonesLoopParameters,
    htr.map_star_mul_self_eq_zero_iff_cubicHom_eq_zero, RingHom.mem_ker]

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

/-- `quotientCubicFixedEquiv` intertwines the quotient `star` with `cubicFixedAdjoint`. -/
@[simp] theorem quotientCubicFixedEquiv_star
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ)
    [((tr m).traceRadical (htr.map_mul_comm m)).IsStar]
    (q : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m ⧸ (tr m).traceRadical (htr.map_mul_comm m)) :
    htr.quotientCubicFixedEquiv m (star q) =
      cubicFixedAdjoint (m - 1) (htr.quotientCubicFixedEquiv m q) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [Ideal.Quotient.star_mk, htr.quotientCubicFixedEquiv_mk, htr.quotientCubicFixedEquiv_mk,
    cubicHom_star]

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

/-- `(quotientCubicFixedEquiv _).symm` intertwines `cubicFixedAdjoint` with the quotient `star`. -/
@[simp] theorem quotientCubicFixedEquiv_symm_cubicFixedAdjoint
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ)
    [((tr m).traceRadical (htr.map_mul_comm m)).IsStar]
    (y : cubicFixed (m - 1)) :
    (htr.quotientCubicFixedEquiv m).symm (cubicFixedAdjoint (m - 1) y) =
      star ((htr.quotientCubicFixedEquiv m).symm y) :=
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
  have hcoe : (Real.sqrt 3 : ℂ) = Complex.ofRealHom (2 * Real.cos (Real.pi / (6 : ℕ))) := by
    rw [Complex.ofRealHom_eq_coe]
    exact_mod_cast (by rw [Nat.cast_ofNat, Real.cos_pi_div_six]; ring :
      Real.sqrt 3 = 2 * Real.cos (Real.pi / (6 : ℕ)))
  have hunits : ∀ k ∈ Finset.Icc 1 5, IsUnit (qInt ℂ (Real.sqrt 3 : ℂ) k) := by
    intro k hk
    obtain ⟨hk1, hk5⟩ := Finset.mem_Icc.mp hk
    rw [hcoe, ← Complex.ofRealHom.map_qInt, isUnit_iff_ne_zero]
    exact Complex.ofReal_ne_zero.mpr (qInt_two_mul_cos_pi_div_pos (by omega) (by omega)).ne'
  rw [← RingHom.mem_ker, ← isMarkovTrace_cubicTrace.traceRadical_eq_ker_cubicHom 5,
    isMarkovTrace_cubicTrace.jonesWenzl_mem_traceRadical_iff hunits, hcoe,
    ← Complex.ofRealHom.map_qInt, qInt_two_mul_cos_pi_div_eq_zero (by decide), map_zero]

end TauCeti.TemperleyLieb
