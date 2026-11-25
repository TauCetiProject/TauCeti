/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.CubicTorus.Star
public import TauCeti.Algebra.TemperleyLieb.CubicTorus.Trace
public import TauCeti.Algebra.TemperleyLieb.Star
public import TauCeti.Algebra.TemperleyLieb.Trace.Radical
-- Private: positive trace quotients and `√3` arithmetic are used only inside proofs.
import TauCeti.Analysis.Complex.Sqrt
import TauCeti.RingTheory.TraceFunctional.Positive

/-!
# The kernel of the cubic comparison map at `δ = √3`

Let `F_m = cubicHom m : TemperleyLieb ℂ (√3 : ℂ) m →ₐ[ℂ] C_(m-1)` be the comparison map of
`TauCeti.Algebra.TemperleyLieb.CubicTorus.Basic` into the inversion-fixed cubic quantum torus,
`e j ↦ √3 p_j`. By `TauCeti.Algebra.TemperleyLieb.CubicTorus.Trace`, every Markov trace at
`δ = √3` is `tr m = (√3) ^ m s_(m-1) ∘ F_m`, where `s_N` is the scalar coefficient.

The cubic projections are self-adjoint, so `F_m` intertwines the analytic adjoint of the
Temperley–Lieb algebra with the adjoint of the cubic quantum torus (`coe_cubicHom_star`). Since
`s_N` is a faithful positive functional (`nullSubmodule_cubicStarPositiveFunctional`), an element
`x` of the trace radical `R_m = {x | ∀ y, tr m (x * y) = 0}` satisfies
`s(F_m(x)⋆ F_m(x)) = 0`, hence `F_m x = 0`; conversely `F_m x = 0` kills every `tr m (x * y)`. So
the kernel of `F_m` is exactly the trace radical (`IsMarkovTrace.traceRadical_eq_ker_cubicHom`),
without any use of surjectivity, and `F_m` induces an injective algebra map from the Jones quotient
`TL_m ⧸ R_m` into `C_(m-1)` carrying the quotient trace to `(√3) ^ m s_(m-1)`
(`IsMarkovTrace.quotientCubicHom`). Since the quantum integers at `√3 = 2 cos (π / 6)` are
`1, √3, 2, √3, 1, 0`, the Jones–Wenzl projection on five strands is negligible, and `F_5`
annihilates it (`cubicHom_jonesWenzl_five`).

## Main definitions

* `TauCeti.TemperleyLieb.cubicStarAlgHom`: `F_m` as a star-algebra map into `CubicTorus (m - 1)`,
  with values in the star subalgebra `cubicFixedStarSubalgebra (m - 1)`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientCubicHom`: the injective algebra map from the
  trace-radical quotient of `TemperleyLieb ℂ (√3 : ℂ) m` into `cubicFixed (m - 1)`.

## Main results

* `TauCeti.TemperleyLieb.coe_cubicHom_star`: `F_m` preserves the adjoints.
* `TauCeti.TemperleyLieb.IsMarkovTrace.traceRadical_eq_ker_cubicHom` and
  `TauCeti.TemperleyLieb.IsMarkovTrace.cubicHom_eq_zero_iff`: the kernel of `F_m` is the trace
  radical.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientCubicHom_injective`: the induced map on the Jones
  quotient is injective.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientTrace_eq_mul_cubicScalarCoefficient_quotientCubicHom`
  : it carries the quotient trace to `(√3) ^ m` times the scalar coefficient.
* `TauCeti.TemperleyLieb.cubicHom_jonesWenzl_five`: `F_5` annihilates the five-strand Jones–Wenzl
  projection.

## References

* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), 103–111, p. 107.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4, Sections 4.3–4.5, for trace radicals
  and the Jones quotients.
-/

public section

open scoped ComplexOrder

namespace TauCeti.TemperleyLieb

/-- Registers `IsSelfAdjoint (Real.sqrt 3 : ℂ)` as a `Fact`, so that
`TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m` carries the analytic adjoint `TemperleyLieb.instStarRing`. -/
instance : Fact (IsSelfAdjoint (Real.sqrt 3 : ℂ)) :=
  ⟨Complex.conj_ofReal _⟩

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

end IsMarkovTrace

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
