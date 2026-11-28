/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.CubicTorus.Projection
public import TauCeti.Algebra.TemperleyLieb.CubicTorus.Star
public import TauCeti.Algebra.TemperleyLieb.CubicTorus.Trace
public import TauCeti.Algebra.TemperleyLieb.Star
public import TauCeti.Algebra.TemperleyLieb.Trace.Radical
public import TauCeti.Algebra.TemperleyLieb.Trace.Star
-- Private: positive trace quotients and `√3` arithmetic are used only inside proofs.
import TauCeti.Analysis.Complex.Sqrt
import TauCeti.RingTheory.TraceFunctional.Positive

/-!
# The Jones quotient at `δ = √3` is the inversion-fixed cubic quantum torus

Let `F_m = cubicHom m : TemperleyLieb ℂ (√3 : ℂ) m →ₐ[ℂ] C_(m-1)` be the comparison map of
`TauCeti.Algebra.TemperleyLieb.CubicTorus.Basic` into the inversion-fixed cubic quantum torus,
`e j ↦ √3 p_j`. By `TauCeti.Algebra.TemperleyLieb.CubicTorus.Trace`, every Markov trace at
`δ = √3` is `tr m = (√3) ^ m s_(m-1) ∘ F_m`, where `s_N` is the scalar coefficient.

The cubic projections are self-adjoint, so `F_m` intertwines the analytic adjoint of the
Temperley–Lieb algebra with the adjoint of the cubic quantum torus (`coe_cubicHom_star`). Since
`s_N` is a faithful positive functional (`nullSubmodule_cubicStarPositiveFunctional`), an element
`x` of the trace radical `R_m = {x | ∀ y, tr m (x * y) = 0}` satisfies
`s(F_m(x)⋆ F_m(x)) = 0`, hence `F_m x = 0`; conversely `F_m x = 0` kills every `tr m (x * y)`. So
the kernel of `F_m` is exactly the trace radical (`IsMarkovTrace.traceRadical_eq_ker_cubicHom`).
Together with surjectivity and the dimension formula `dim C_N = (3 ^ N + 1) / 2` from
`TauCeti.Algebra.TemperleyLieb.CubicTorus.Projection`, `F_m` induces a `ℂ`-algebra isomorphism
`IsMarkovTrace.quotientCubicFixedEquiv` between `TL_m(√3) ⧸ R_m` and `C_(m-1)` of complex
dimension `(3 ^ (m - 1) + 1) / 2` (`finrank_quotient_traceRadical_sqrt_three`), intertwining `star`,
the tower inclusions, and the trace
(`quotientTrace_eq_mul_cubicScalarCoefficient_quotientCubicFixedEquiv`).
Since the quantum integers at `√3 = 2 cos (π / 6)` are `1, √3, 2, √3, 1, 0`, the Jones–Wenzl
projection on five strands is negligible, and `F_5` annihilates it (`cubicHom_jonesWenzl_five`).

## Main definitions

* `TauCeti.TemperleyLieb.cubicStarAlgHom`: `F_m` as a star-algebra map into `CubicTorus (m - 1)`,
  with values in the star subalgebra `cubicFixedStarSubalgebra (m - 1)`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientCubicHom`: the injective algebra map from the
  trace-radical quotient of `TemperleyLieb ℂ (√3 : ℂ) m` into `cubicFixed (m - 1)`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientCubicFixedEquiv`: the `ℂ`-algebra equivalence
  between the trace-radical quotient of `TemperleyLieb ℂ (√3 : ℂ) m` and `cubicFixed (m - 1)`.

## Main results

* `TauCeti.TemperleyLieb.coe_cubicHom_star`: `F_m` preserves the adjoints.
* `TauCeti.TemperleyLieb.IsMarkovTrace.traceRadical_eq_ker_cubicHom` and
  `TauCeti.TemperleyLieb.IsMarkovTrace.cubicHom_eq_zero_iff`: the kernel of `F_m` is the trace
  radical.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientCubicHom_injective` and
  `TauCeti.TemperleyLieb.IsMarkovTrace.finrank_quotient_traceRadical_sqrt_three`: injectivity of
  `quotientCubicHom` and dimension `(3 ^ (m - 1) + 1) / 2` of the Jones quotient.
* `IsMarkovTrace.quotientTrace_eq_mul_cubicScalarCoefficient_quotientCubicHom` and
  `IsMarkovTrace.quotientTrace_eq_mul_cubicScalarCoefficient_quotientCubicFixedEquiv`:
  carrying the quotient trace to `(√3) ^ m` times the scalar coefficient.
* `TauCeti.TemperleyLieb.exists_cubicFixedModel` and
  `TauCeti.TemperleyLieb.cubicHom_jonesWenzl_five`: packaged cubic fixed-point model and
  annihilation of the five-strand Jones–Wenzl projection.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25; *A polynomial invariant
  for knots via von Neumann algebras*, Bull. Amer. Math. Soc. 12 (1985), 103–111, p. 107.
* F. M. Goodman, P. de la Harpe, and V. F. R. Jones, *Coxeter Graphs and Towers of Algebras*,
  MSRI Publications 14, Springer (1989).
* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4, Sections 4.3–4.5, for trace radicals
  and the Jones quotients.
-/

public section

open scoped ComplexOrder

namespace TauCeti.TemperleyLieb

/-- The cubic comparison map intertwines the analytic adjoint of the Temperley–Lieb algebra with
the adjoint of the cubic quantum torus. -/
@[simp]
theorem coe_cubicHom_star {m : ℕ} (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    (cubicHom m (star x) : CubicTorus (m - 1)) = star (cubicHom m x : CubicTorus (m - 1)) :=
  (map_star_iff (F := (cubicFixed (m - 1)).val.comp (cubicHom m))).2
    (fun j ↦ by simp [IsSelfAdjoint, star_smul]) x

/-- The cubic comparison map `F_m`, as a star-algebra map into the cubic quantum torus. Its values
lie in the star subalgebra `cubicFixedStarSubalgebra (m - 1)` (`cubicStarAlgHom_mem`). -/
noncomputable def cubicStarAlgHom (m : ℕ) :
    TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →⋆ₐ[ℂ] CubicTorus (m - 1) :=
  { (cubicFixed (m - 1)).val.comp (cubicHom m) with map_star' := coe_cubicHom_star }

@[simp]
theorem cubicStarAlgHom_apply {m : ℕ} (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    cubicStarAlgHom m x = cubicHom m x :=
  (rfl)

/-- The star-algebra form of `F_m` takes values in the inversion-fixed star subalgebra. -/
theorem cubicStarAlgHom_mem {m : ℕ} (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    cubicStarAlgHom m x ∈ cubicFixedStarSubalgebra (m - 1) :=
  mem_cubicFixedStarSubalgebra.2 (cubicHom m x).property

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
    cubicScalarCoefficient_star_mul_self_eq_zero_iff, ZeroMemClass.coe_eq_zero]

/-- **The kernel of the cubic comparison map is the trace radical**: for every Markov trace `tr`
at `δ = √3`, `RingHom.ker (cubicHom m)` is the radical of the trace form of `tr m`. -/
theorem traceRadical_eq_ker_cubicHom (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) :
    (tr m).traceRadical (htr.map_mul_comm m) = RingHom.ker (cubicHom m) := by
  have hne : (Real.sqrt 3 : ℂ) ^ m ≠ 0 := pow_ne_zero m (by simp)
  -- `tr m` is `(√3) ^ m` times the pullback `τ` of the faithful positive trace `s_(m-1)`, so both
  -- have the same radical, which is the kernel of the pullback map.
  let τ : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →ₗ[ℂ] ℂ :=
    cubicScalarCoefficient (m - 1) ∘ₗ (cubicStarAlgHom m).toAlgHom.toLinearMap
  have hτ : ∀ x y, τ (x * y) = τ (y * x) := fun x y ↦ by
    simp only [τ, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul,
      cubicScalarCoefficient_mul_comm]
  have hrad : (tr m).traceRadical (htr.map_mul_comm m) = τ.traceRadical hτ := by
    ext x
    simp [τ, htr.apply_eq_mul_cubicScalarCoefficient_cubicHom, hne]
  rw [hrad, LinearMap.traceRadical_eq_ker_of_nullSubmodule_eq_bot τ hτ
    (cubicStarPositiveFunctional (m - 1)) nullSubmodule_cubicStarPositiveFunctional
    (cubicStarAlgHom m) fun a ↦ by simp [τ]]
  ext x
  simp [RingHom.mem_ker]

/-- The cubic comparison map kills `x` exactly when `x` lies in the trace radical, that is,
`tr m (x * y) = 0` for every `y`. -/
theorem cubicHom_eq_zero_iff (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) {m : ℕ}
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    cubicHom m x = 0 ↔ ∀ y, tr m (x * y) = 0 := by
  rw [← RingHom.mem_ker, ← htr.traceRadical_eq_ker_cubicHom m, LinearMap.mem_traceRadical]

/-- The **Jones quotient at `δ = √3` embeds in the inversion-fixed cubic quantum torus**: the
injective algebra map `TL_m ⧸ R_m →ₐ[ℂ] C_(m-1)` induced by the cubic comparison map. -/
noncomputable def quotientCubicHom (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) :
    (TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m ⧸ (tr m).traceRadical (htr.map_mul_comm m)) →ₐ[ℂ]
      cubicFixed (m - 1) :=
  (Ideal.kerLiftAlg (cubicHom m)).comp
    (Ideal.quotientEquivAlgOfEq ℂ (htr.traceRadical_eq_ker_cubicHom m)).toAlgHom

/-- `quotientCubicHom` evaluates on a quotient representative via `cubicHom`. -/
@[simp]
theorem quotientCubicHom_mk (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ)
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    htr.quotientCubicHom m (Ideal.Quotient.mk ((tr m).traceRadical (htr.map_mul_comm m)) x) =
      cubicHom m x := by
  simp [quotientCubicHom]

/-- The induced map on the Jones quotient at `δ = √3` is injective. -/
theorem quotientCubicHom_injective (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) :
    Function.Injective (htr.quotientCubicHom m) :=
  (Ideal.kerLiftAlg_injective (cubicHom m)).comp
    (Ideal.quotientEquivAlgOfEq ℂ (htr.traceRadical_eq_ker_cubicHom m)).injective

/-- The induced trace on the Jones quotient at `δ = √3` is `(√3) ^ m` times the scalar coefficient
under `quotientCubicHom`. -/
theorem quotientTrace_eq_mul_cubicScalarCoefficient_quotientCubicHom
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ)
    (q : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m ⧸ (tr m).traceRadical (htr.map_mul_comm m)) :
    (tr m).quotientTrace (htr.map_mul_comm m) q =
      (Real.sqrt 3 : ℂ) ^ m * cubicScalarCoefficient (m - 1) (htr.quotientCubicHom m q) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp [htr.apply_eq_mul_cubicScalarCoefficient_cubicHom]

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

/-- `quotientCubicFixedEquiv` intertwines the quotient `star` with `star` on `CubicTorus`. -/
@[simp] theorem coe_quotientCubicFixedEquiv_star
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ)
    [((tr m).traceRadical (htr.map_mul_comm m)).IsStar]
    (q : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m ⧸ (tr m).traceRadical (htr.map_mul_comm m)) :
    (htr.quotientCubicFixedEquiv m (star q) : CubicTorus (m - 1)) =
      star (htr.quotientCubicFixedEquiv m q : CubicTorus (m - 1)) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp

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

/-- `(quotientCubicFixedEquiv _).symm` intertwines `star` with the quotient `star`. -/
@[simp] theorem quotientCubicFixedEquiv_symm_star
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ)
    [((tr m).traceRadical (htr.map_mul_comm m)).IsStar]
    (y : cubicFixed (m - 1)) :
    (htr.quotientCubicFixedEquiv m).symm
        ⟨star (y : CubicTorus (m - 1)), star_mem_cubicFixed y.property⟩ =
      star ((htr.quotientCubicFixedEquiv m).symm y) :=
  (htr.quotientCubicFixedEquiv m).injective (Subtype.ext (by simp))

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

/-- **The cubic quantum torus model of `TemperleyLieb ℂ (√3 : ℂ) m`.** For every Markov trace `tr`
at loop value `√3` and every `m : ℕ`, there is a surjective `ℂ`-algebra homomorphism
`F : TemperleyLieb ℂ (√3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1)` sending `e j` to
`(√3 : ℂ) • cubicProjection (m - 1) j`, intertwining `star`, expressing `tr m` via
`cubicScalarCoefficient (m - 1)`, and having kernel `(tr m).traceRadical`. -/
theorem exists_cubicFixedModel
    {tr : ∀ n : ℕ, TemperleyLieb ℂ (Real.sqrt 3 : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) :
    ∃ F : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1),
      Function.Surjective F ∧
      (∀ j : Fin (m - 1),
        (F (e (Real.sqrt 3 : ℂ) j) : CubicTorus (m - 1)) =
          (Real.sqrt 3 : ℂ) • cubicProjection (m - 1) j) ∧
      (∀ x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m,
        (F (star x) : CubicTorus (m - 1)) = star (F x : CubicTorus (m - 1))) ∧
      (∀ x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m,
        tr m x = (Real.sqrt 3 : ℂ) ^ m * cubicScalarCoefficient (m - 1) (F x)) ∧
      RingHom.ker F = (tr m).traceRadical (htr.map_mul_comm m) :=
  ⟨cubicHom m, cubicHom_surjective m, coe_cubicHom_e m, coe_cubicHom_star,
    htr.apply_eq_mul_cubicScalarCoefficient_cubicHom m,
    (htr.traceRadical_eq_ker_cubicHom m).symm⟩

/-- At `δ = √3`, the cubic comparison map annihilates the five-strand Jones–Wenzl projection: the
quantum integers `[1], …, [5]` are `1, √3, 2, √3, 1`, and `[6] = 0`. -/
@[simp]
theorem cubicHom_jonesWenzl_five : cubicHom 5 (jonesWenzl (Real.sqrt 3 : ℂ) 5) = 0 := by
  have hsqrt : (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 :=
    Complex.mul_self_ofReal_sqrt zero_le_three
  have hunits : ∀ k ∈ Finset.Icc 1 5, IsUnit (qInt ℂ (Real.sqrt 3 : ℂ) k) := by
    intro k hk
    obtain ⟨hk1, hk5⟩ := Finset.mem_Icc.mp hk
    interval_cases k
    · simp
    · simp [qInt_two]
    · simp [qInt_three_of_mul_self_eq_three hsqrt]
    · simp [qInt_four_of_mul_self_eq_three hsqrt]
    · simp [qInt_five_of_mul_self_eq_three hsqrt]
  rw [← RingHom.mem_ker, ← isMarkovTrace_cubicTrace.traceRadical_eq_ker_cubicHom 5,
    isMarkovTrace_cubicTrace.jonesWenzl_mem_traceRadical_iff hunits]
  exact qInt_six_of_mul_self_eq_three hsqrt

end TauCeti.TemperleyLieb
