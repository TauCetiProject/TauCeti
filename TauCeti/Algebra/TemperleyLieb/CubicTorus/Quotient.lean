/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.CubicTorus.Basic
public import TauCeti.Algebra.TemperleyLieb.Trace.Radical
public import TauCeti.RingTheory.Ideal.Quotient.Star
-- Private: positive trace radical characterization is used only inside proofs.
import TauCeti.RingTheory.TraceFunctional.Positive

/-!
# The Jones quotient at `δ = √3` as the inversion-fixed cubic quantum torus

Building on the surjective `⋆`-algebra homomorphism
`F_m = cubicFixedHom m : TemperleyLieb ℂ (√3 : ℂ) m →⋆ₐ[ℂ] cubicFixed (m - 1)` from
`TauCeti.Algebra.TemperleyLieb.CubicTorus.Basic`, this file equips the cubic quantum torus tower
with coordinate inclusions, identifies the Markov trace at `δ = √3` with `(√3) ^ m` times the
canonical trace `TwistedMonoidAlgebra.trace`, establishes positivity of the Markov Hermitian form
at `δ = √3`, identifies the `m`-strand Temperley–Lieb trace-radical quotient (the Jones
quotient at index `δ² = 3`) with `cubicFixed (m - 1)`, and proves that `cubicFixedHom 5`
annihilates the negligible five-strand Jones–Wenzl projection `jonesWenzl (√3 : ℂ) 5`.

* **Coordinate inclusions and Markov trace identity**: extending `Fin N → ZMod 3` by `0` in the
  last coordinate induces injective `⋆`-algebra homomorphisms `cubicTorusIncl N` and
  `cubicFixedIncl N` that intertwine `strandIncl` and `cubicInversion`, preserve
  `TwistedMonoidAlgebra.trace`, and satisfy
  `trace (cubicTorusIncl N x * cubicProjection (N + 1) (Fin.last N)) = 3⁻¹ * trace x` because the
  non-identity summands `U_N` and `U_N ^ 2` lie outside the embedded subgroup. Hence
  `cubicFixedTrace m x = (√3) ^ m * trace (cubicFixedHom m x)` satisfies `IsMarkovTrace`, and
  Markov uniqueness identifies every Markov trace at `√3` with it.
* **Positivity and the trace radical**: Parseval positivity and faithfulness of
  `TwistedMonoidAlgebra.trace` show that at `δ = √3` the Markov Hermitian form
  `tr m (star x * x)` is positive semidefinite (the `m = 6` discrete-series point `2 cos (π / 6)`
  of Jones's positivity theorem), and `LinearMap.traceRadical_eq_ker_of_nullSubmodule_eq_bot`
  identifies both the Hermitian null space and `(tr m).traceRadical` with
  `RingHom.ker (cubicFixedHom m)`.
* **Jones quotient equivalence and five-strand Jones–Wenzl vanishing**: passing to the quotient
  yields `IsMarkovTrace.quotientCubicFixedEquiv` of complex dimension `(3 ^ (m - 1) + 1) / 2`
  intertwining `quotientStrandIncl`, `quotientTrace`, and `star`. In particular, at five strands
  (`dim TL_5 = 42`, `dim C_4 = 41`), `cubicFixedHom 5` kills `jonesWenzl (√3 : ℂ) 5`.

## Main definitions

* `TauCeti.TemperleyLieb.cubicExtendHom`, `TauCeti.TemperleyLieb.cubicTorusIncl`, and
  `TauCeti.TemperleyLieb.cubicFixedIncl`: the coordinate inclusions extending `Fin N → ZMod 3` by
  zero.
* `TauCeti.TemperleyLieb.cubicFixedTrace`: the unnormalized Markov trace at `√3` induced by
  `TwistedMonoidAlgebra.trace`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientCubicFixedEquiv`: the algebra isomorphism between
  the `m`-strand Temperley–Lieb trace quotient at `√3` and `cubicFixed (m - 1)`.

## Main results

* `TauCeti.TemperleyLieb.cubicTorusIncl_injective`,
  `TauCeti.TemperleyLieb.cubicFixedIncl_injective`, and
  `TauCeti.TemperleyLieb.cubicFixedHom_strandIncl`: injectivity and tower compatibility of the
  coordinate inclusions.
* `TauCeti.TemperleyLieb.isMarkovTrace_cubicFixedTrace`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.apply_eq_mul_trace_cubicFixedHom`, and
  `TauCeti.TemperleyLieb.markovTrace_eq_mul_trace_cubicFixedHom`: the Markov-trace formula
  `tr m x = (√3) ^ m * TwistedMonoidAlgebra.trace (cubicFixedHom m x)`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.map_star_mul_self_nonneg_sqrt_three` and
  `TauCeti.TemperleyLieb.IsMarkovTrace.traceRadical_eq_ker_cubicFixedHom`: positivity of the
  Markov Hermitian form at `δ = √3` and identification of the trace radical with
  `RingHom.ker (cubicFixedHom m)`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientCubicFixedEquiv_quotientStrandIncl`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.quotientCubicFixedEquiv_star`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.quotientTrace_eq_mul_trace_quotientCubicFixedEquiv`, and
  `TauCeti.TemperleyLieb.IsMarkovTrace.finrank_quotient_traceRadical_sqrt_three`: tower, adjoint,
  trace, and dimension (`(3 ^ (m - 1) + 1) / 2`) properties of the Jones quotient equivalence.
* `TauCeti.TemperleyLieb.exists_cubicFixedModel` and
  `TauCeti.TemperleyLieb.cubicFixedHom_jonesWenzl_five`: packaged existence theorem for the cubic
  quantum torus model at `δ = √3` and vanishing of the five-strand Jones–Wenzl projection.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), 103–111 (p. 107, cubic quantum torus model at `t = exp (πi / 3)`).
* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989.
* C. Galindo and E. C. Rowell, *Braid representations from unitary braided vector spaces*,
  J. Math. Phys. 55 (2014), 061702, Section 3.
-/

public section

open scoped ComplexOrder

namespace TauCeti.TemperleyLieb

private theorem sqrt_three_mul_self :
    (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 := by
  exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)

/-! ### Coordinate inclusions and the Markov trace identity -/

/-- Extending a coordinate vector `v : Fin N → ZMod 3` by `0` in the last coordinate gives a group
homomorphism `Multiplicative (Fin N → ZMod 3) →* Multiplicative (Fin (N + 1) → ZMod 3)`. -/
def cubicExtendHom (N : ℕ) :
    Multiplicative (Fin N → ZMod 3) →* Multiplicative (Fin (N + 1) → ZMod 3) where
  toFun a := Multiplicative.ofAdd (Fin.snoc a.toAdd 0)
  map_one' := by
    apply Multiplicative.toAdd.injective
    ext k
    refine Fin.lastCases ?_ (fun k ↦ ?_) k <;> simp
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    ext k
    refine Fin.lastCases ?_ (fun k ↦ ?_) k <;> simp

/-- Explicit formula for `cubicExtendHom`. -/
@[simp]
theorem cubicExtendHom_apply (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicExtendHom N a = Multiplicative.ofAdd (Fin.snoc a.toAdd 0) :=
  (rfl)

/-- `cubicExtendHom N` is injective. -/
theorem cubicExtendHom_injective (N : ℕ) : Function.Injective (cubicExtendHom N) := by
  intro a b h
  apply Multiplicative.toAdd.injective
  ext i
  have hi := congrFun (congrArg Multiplicative.toAdd h) i.castSucc
  simpa [cubicExtendHom_apply] using hi

/-- Extending by zero in the last coordinate preserves `chainForm`. -/
theorem chainForm_snoc_zero (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm (N + 1) (Fin.snoc a 0) (Fin.snoc b 0) = chainForm N a b := by
  simp only [chainForm_apply, Fin.sum_univ_castSucc, Fin.snoc_last, Fin.snoc_castSucc,
    Fin.val_castSucc, zero_mul, mul_zero, sub_self, ite_self, Finset.sum_const_zero, add_zero]

/-- `cubicExtendHom N` pulls back `cubicFactor (N + 1)` to `cubicFactor N`. -/
theorem cubicFactor_cubicExtendHom (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor (N + 1) (cubicExtendHom N a) (cubicExtendHom N b) = cubicFactor N a b := by
  simp [cubicFactor_apply, cubicExtendHom_apply, chainForm_snoc_zero]

/-- The `⋆`-algebra inclusion `CubicTorus N →⋆ₐ[ℂ] CubicTorus (N + 1)` extending a coordinate
vector `Fin N → ZMod 3` by zero in the last coordinate. -/
noncomputable def cubicTorusIncl (N : ℕ) : CubicTorus N →⋆ₐ[ℂ] CubicTorus (N + 1) :=
  TwistedMonoidAlgebra.starMap (cubicExtendHom N)
    (fun a b ↦ (cubicFactor_cubicExtendHom N a b).symm)

/-- `cubicTorusIncl N` sends `weyl N a` to `weyl (N + 1) (cubicExtendHom N a)`. -/
@[simp]
theorem cubicTorusIncl_weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicTorusIncl N (weyl N a) = weyl (N + 1) (cubicExtendHom N a) := by
  rw [weyl_def, weyl_def, cubicTorusIncl, TwistedMonoidAlgebra.starMap_of]

/-- `cubicTorusIncl N` is injective. -/
theorem cubicTorusIncl_injective (N : ℕ) : Function.Injective (cubicTorusIncl N) :=
  TwistedMonoidAlgebra.starMap_injective _ _ (cubicExtendHom_injective N)

/-- `cubicTorusIncl` commutes with `cubicInversion`. -/
@[simp]
theorem cubicTorusIncl_cubicInversion (N : ℕ) (x : CubicTorus N) :
    cubicTorusIncl N (cubicInversion N x) = cubicInversion (N + 1) (cubicTorusIncl N x) := by
  have h : (cubicTorusIncl N).toAlgHom.comp (cubicInversion N).toAlgHom =
      (cubicInversion (N + 1)).toAlgHom.comp (cubicTorusIncl N).toAlgHom := by
    refine TwistedMonoidAlgebra.algHom_ext fun a ↦ ?_
    simp only [AlgHom.comp_apply, StarAlgHom.coe_toAlgHom, ← weyl_def, cubicInversion_weyl,
      cubicTorusIncl_weyl, map_inv]
  exact AlgHom.congr_fun h x

/-- `cubicTorusIncl N` maps `cubicFixed N` into `cubicFixed (N + 1)`. -/
theorem cubicTorusIncl_mem_cubicFixed (N : ℕ) {x : CubicTorus N} (hx : x ∈ cubicFixed N) :
    cubicTorusIncl N x ∈ cubicFixed (N + 1) := by
  rw [mem_cubicFixed_iff, ← cubicTorusIncl_cubicInversion, mem_cubicFixed_iff.mp hx]

/-- `cubicTorusIncl N x` lies in `cubicFixed (N + 1)` if and only if `x` lies in `cubicFixed N`. -/
theorem cubicTorusIncl_mem_cubicFixed_iff (N : ℕ) {x : CubicTorus N} :
    cubicTorusIncl N x ∈ cubicFixed (N + 1) ↔ x ∈ cubicFixed N := by
  refine ⟨fun hx ↦ ?_, cubicTorusIncl_mem_cubicFixed N⟩
  rw [mem_cubicFixed_iff] at hx ⊢
  rw [← cubicTorusIncl_cubicInversion] at hx
  exact cubicTorusIncl_injective N hx

/-- The restricted `⋆`-algebra inclusion `cubicFixed N →⋆ₐ[ℂ] cubicFixed (N + 1)`. -/
noncomputable def cubicFixedIncl (N : ℕ) : cubicFixed N →⋆ₐ[ℂ] cubicFixed (N + 1) :=
  ((cubicTorusIncl N).comp (cubicFixed N).subtype).codRestrict (cubicFixed (N + 1)) fun x ↦
    cubicTorusIncl_mem_cubicFixed N x.2

/-- Coercing `cubicFixedIncl N` to the ambient cubic quantum torus recovers `cubicTorusIncl N`. -/
@[simp]
theorem coe_cubicFixedIncl (N : ℕ) (x : cubicFixed N) :
    (cubicFixedIncl N x : CubicTorus (N + 1)) = cubicTorusIncl N x :=
  (rfl)

/-- `cubicFixedIncl N` is injective. -/
theorem cubicFixedIncl_injective (N : ℕ) : Function.Injective (cubicFixedIncl N) := by
  intro x y hxy
  apply Subtype.ext
  exact cubicTorusIncl_injective N (congrArg Subtype.val hxy)

/-- `cubicTorusIncl N` maps `cubicSite N j` to `cubicSite (N + 1) j.castSucc`. -/
@[simp]
theorem cubicTorusIncl_cubicSite (N : ℕ) (j : Fin N) :
    cubicTorusIncl N (cubicSite N j) = cubicSite (N + 1) j.castSucc := by
  have hsnoc : Fin.snoc (Pi.single j (1 : ZMod 3)) 0 =
      (Pi.single j.castSucc 1 : Fin (N + 1) → ZMod 3) := by
    ext k
    refine Fin.lastCases ?_ (fun k ↦ ?_) k
    · simp [(Fin.castSucc_lt_last j).ne']
    · simp [Pi.single_apply]
  simp [cubicSite_def, hsnoc]

/-- `cubicTorusIncl N` maps `cubicProjection N j` to `cubicProjection (N + 1) j.castSucc`. -/
@[simp]
theorem cubicTorusIncl_cubicProjection (N : ℕ) (j : Fin N) :
    cubicTorusIncl N (cubicProjection N j) = cubicProjection (N + 1) j.castSucc := by
  simp [cubicProjection_def]

/-- Coordinate inclusion preserves the canonical trace `TwistedMonoidAlgebra.trace`. -/
@[simp]
theorem trace_cubicTorusIncl (N : ℕ) (x : CubicTorus N) :
    TwistedMonoidAlgebra.trace (cubicTorusIncl N x) = TwistedMonoidAlgebra.trace x :=
  TwistedMonoidAlgebra.trace_starMap (cubicExtendHom N) _ (cubicExtendHom_injective N) x

/-- `cubicFixedHom` intertwines Temperley–Lieb `strandIncl` with `cubicFixedIncl`. -/
theorem cubicFixedHom_strandIncl (n : ℕ)
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) (n + 1)) :
    cubicFixedHom (n + 2) (strandIncl x) =
      cubicFixedIncl n (cubicFixedHom (n + 1) x) := by
  have hhom : (cubicFixedHom (n + 2)).toAlgHom.comp strandIncl =
      (cubicFixedIncl n).toAlgHom.comp (cubicFixedHom (n + 1)).toAlgHom := by
    apply TemperleyLieb.hom_ext
    intro i
    apply Subtype.ext
    simp only [AlgHom.comp_apply, StarAlgHom.coe_toAlgHom, strandIncl_e, coe_cubicFixedHom_e,
      coe_cubicFixedIncl, map_smul]
    exact congrArg ((Real.sqrt 3 : ℂ) • ·) (cubicTorusIncl_cubicProjection n i).symm
  exact AlgHom.congr_fun hhom x

/-- Multiplying an included element by the last projection scales its canonical trace by `3⁻¹`:
the non-identity summands `U_N` and `U_N ^ 2` lie outside the embedded subgroup. -/
theorem trace_cubicTorusIncl_mul_cubicProjection_last (N : ℕ) (x : CubicTorus N) :
    TwistedMonoidAlgebra.trace
        (cubicTorusIncl N x * cubicProjection (N + 1) (Fin.last N)) =
      (3 : ℂ)⁻¹ * TwistedMonoidAlgebra.trace x := by
  let e1 : Fin (N + 1) → ZMod 3 := Pi.single (Fin.last N) 1
  let e2 : Fin (N + 1) → ZMod 3 := Pi.single (Fin.last N) 2
  have h1 : Multiplicative.ofAdd e1 ∉ Set.range (cubicExtendHom N) := by
    rintro ⟨a, ha⟩
    have hlast := congrFun (congrArg Multiplicative.toAdd ha) (Fin.last N)
    simp only [cubicExtendHom_apply, toAdd_ofAdd, Fin.snoc_last, e1, Pi.single_eq_same] at hlast
    exact absurd hlast (by decide)
  have h2 : Multiplicative.ofAdd e2 ∉ Set.range (cubicExtendHom N) := by
    rintro ⟨a, ha⟩
    have hlast := congrFun (congrArg Multiplicative.toAdd ha) (Fin.last N)
    simp only [cubicExtendHom_apply, toAdd_ofAdd, Fin.snoc_last, e2, Pi.single_eq_same] at hlast
    exact absurd hlast (by decide)
  have ht1 :
      TwistedMonoidAlgebra.trace (cubicTorusIncl N x * cubicSite (N + 1) (Fin.last N)) = 0 := by
    rw [cubicSite_def, weyl_def, cubicTorusIncl]
    exact TwistedMonoidAlgebra.trace_starMap_mul_of_eq_zero (cubicExtendHom N) _ x h1
  have ht2 :
      TwistedMonoidAlgebra.trace (cubicTorusIncl N x * cubicSite (N + 1) (Fin.last N) ^ 2) = 0 := by
    rw [cubicSite_sq, weyl_def, cubicTorusIncl]
    exact TwistedMonoidAlgebra.trace_starMap_mul_of_eq_zero (cubicExtendHom N) _ x h2
  rw [cubicProjection_def, mul_smul_comm, mul_add, mul_add, mul_one, map_smul, map_add, map_add,
    trace_cubicTorusIncl, ht1, ht2, add_zero, add_zero, smul_eq_mul]

/-- The unnormalized Markov trace on `TemperleyLieb ℂ (√3 : ℂ) m` obtained by pulling back
`(√3) ^ m` times `TwistedMonoidAlgebra.trace` along `cubicFixedHom m`. -/
noncomputable def cubicFixedTrace (m : ℕ) :
    TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →ₗ[ℂ] ℂ :=
  ((Real.sqrt 3 : ℂ) ^ m) •
    (TwistedMonoidAlgebra.trace ∘ₗ
      (cubicFixed (m - 1)).toSubalgebra.val.toLinearMap ∘ₗ
        (cubicFixedHom m).toAlgHom.toLinearMap)

/-- Evaluation formula for `cubicFixedTrace`. -/
theorem cubicFixedTrace_apply (m : ℕ) (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    cubicFixedTrace m x =
      (Real.sqrt 3 : ℂ) ^ m *
        TwistedMonoidAlgebra.trace (cubicFixedHom m x : CubicTorus (m - 1)) := by
  simp only [cubicFixedTrace, LinearMap.smul_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    Subalgebra.coe_val, StarAlgHom.coe_toAlgHom, smul_eq_mul]

/-- **The canonical twisted-group trace defines a Markov trace at `δ = √3`.** -/
theorem isMarkovTrace_cubicFixedTrace :
    IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) cubicFixedTrace where
  map_one m := by simp [cubicFixedTrace_apply]
  map_mul_comm m x y := by
    rw [cubicFixedTrace_apply, cubicFixedTrace_apply, map_mul, map_mul, MulMemClass.coe_mul,
      MulMemClass.coe_mul, TwistedMonoidAlgebra.trace_mul_comm]
  map_strandIncl n x := by
    simp only [cubicFixedTrace_apply, cubicFixedHom_strandIncl, coe_cubicFixedIncl,
      trace_cubicTorusIncl, pow_succ']
    ring
  map_strandIncl_mul_e_last n x := by
    simp only [cubicFixedTrace_apply, map_mul, MulMemClass.coe_mul, cubicFixedHom_strandIncl,
      coe_cubicFixedIncl, coe_cubicFixedHom_e, mul_smul_comm, map_smul, smul_eq_mul]
    change (Real.sqrt 3 : ℂ) ^ (n + 2) *
        ((Real.sqrt 3 : ℂ) *
          TwistedMonoidAlgebra.trace
            (cubicTorusIncl n (cubicFixedHom (n + 1) x).1 *
              cubicProjection (n + 1) (Fin.last n))) =
      (Real.sqrt 3 : ℂ) ^ (n + 1) *
        TwistedMonoidAlgebra.trace (cubicFixedHom (n + 1) x).1
    rw [trace_cubicTorusIncl_mul_cubicProjection_last, pow_succ]
    calc
      (Real.sqrt 3 : ℂ) ^ (n + 1) * (Real.sqrt 3 : ℂ) *
          ((Real.sqrt 3 : ℂ) *
            ((3 : ℂ)⁻¹ * TwistedMonoidAlgebra.trace (cubicFixedHom (n + 1) x).1))
          = (Real.sqrt 3 : ℂ) ^ (n + 1) *
              (((Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ)) * (3 : ℂ)⁻¹) *
                TwistedMonoidAlgebra.trace (cubicFixedHom (n + 1) x).1 := by
            ring
      _ = (Real.sqrt 3 : ℂ) ^ (n + 1) *
            TwistedMonoidAlgebra.trace (cubicFixedHom (n + 1) x).1 := by
            rw [sqrt_three_mul_self]
            norm_num

/-- Scaled positive trace functional `(√3) ^ m * trace` restricted to `cubicFixed (m - 1)`. -/
private noncomputable def scaledCubicFixedPositiveFunctional (m : ℕ) :
    StarPositiveFunctional (cubicFixed (m - 1)) where
  toLinearMap :=
    ((Real.sqrt 3 : ℂ) ^ m) •
      (TwistedMonoidAlgebra.trace ∘ₗ (cubicFixed (m - 1)).toSubalgebra.val.toLinearMap)
  square_nonneg y := by
    change 0 ≤ (Real.sqrt 3 : ℂ) ^ m *
      TwistedMonoidAlgebra.trace (star (y : CubicTorus (m - 1)) * (y : CubicTorus (m - 1)))
    have hz := TwistedMonoidAlgebra.trace_star_mul_self_nonneg (y : CubicTorus (m - 1))
    have hz0 : ((0 : ℝ) : ℂ) ≤
        TwistedMonoidAlgebra.trace (star (y : CubicTorus (m - 1)) * (y : CubicTorus (m - 1))) := by
      simpa using hz
    rw [Complex.eq_re_of_ofReal_le hz0, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      Complex.zero_le_real]
    exact mul_nonneg (by positivity) (Complex.nonneg_iff.mp hz).1

private theorem nullSubmodule_scaledCubicFixedPositiveFunctional (m : ℕ) :
    (scaledCubicFixedPositiveFunctional m).nullSubmodule = ⊥ := by
  have hne : (Real.sqrt 3 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
  ext y
  rw [StarPositiveFunctional.mem_nullSubmodule_iff_apply_star_mul_self_eq_zero, Submodule.mem_bot]
  change (Real.sqrt 3 : ℂ) ^ m *
      TwistedMonoidAlgebra.trace (star (y : CubicTorus (m - 1)) * (y : CubicTorus (m - 1))) = 0 ↔
    y = 0
  simp only [mul_eq_zero, pow_ne_zero m hne, false_or,
    TwistedMonoidAlgebra.trace_star_mul_self_eq_zero_iff, ZeroMemClass.coe_eq_zero]

namespace IsMarkovTrace

variable {tr : ∀ n : ℕ, TemperleyLieb ℂ (Real.sqrt 3 : ℂ) n →ₗ[ℂ] ℂ}

/-- Every Markov trace on `TemperleyLieb ℂ (√3 : ℂ)` coincides with `cubicFixedTrace`. -/
theorem eq_cubicFixedTrace (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) :
    tr = cubicFixedTrace :=
  htr.unique isMarkovTrace_cubicFixedTrace

/-- **The Markov trace at `δ = √3` as the canonical cubic-torus trace**: for every Markov trace
`tr`, `tr m x = (√3 : ℂ) ^ m * TwistedMonoidAlgebra.trace (cubicFixedHom m x)`. -/
theorem apply_eq_mul_trace_cubicFixedHom
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ)
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    tr m x =
      (Real.sqrt 3 : ℂ) ^ m *
        TwistedMonoidAlgebra.trace (cubicFixedHom m x : CubicTorus (m - 1)) := by
  rw [htr.eq_cubicFixedTrace, cubicFixedTrace_apply]

/-- **Positivity of the Markov trace at `δ = √3`** (the `m = 6` discrete-series point
`2 cos (π / 6)` of Jones's positivity theorem): `0 ≤ tr m (star x * x)` on every number of
strands. -/
theorem map_star_mul_self_nonneg_sqrt_three
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) {m : ℕ}
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    0 ≤ tr m (star x * x) := by
  have h := (scaledCubicFixedPositiveFunctional m).square_nonneg (cubicFixedHom m x)
  change 0 ≤ (Real.sqrt 3 : ℂ) ^ m *
      TwistedMonoidAlgebra.trace
        ((star (cubicFixedHom m x) * cubicFixedHom m x : cubicFixed (m - 1)) :
          CubicTorus (m - 1)) at h
  rwa [htr.apply_eq_mul_trace_cubicFixedHom, map_mul, map_star]

/-- At `δ = √3`, `tr m (star x * x) = 0` if and only if `cubicFixedHom m x = 0`. -/
theorem map_star_mul_self_eq_zero_iff_cubicFixedHom_eq_zero
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) {m : ℕ}
    {x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m} :
    tr m (star x * x) = 0 ↔ cubicFixedHom m x = 0 := by
  have hne : (Real.sqrt 3 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
  rw [htr.apply_eq_mul_trace_cubicFixedHom, map_mul, map_star, MulMemClass.coe_mul,
    StarMemClass.coe_star]
  simp only [mul_eq_zero, pow_ne_zero m hne, false_or,
    TwistedMonoidAlgebra.trace_star_mul_self_eq_zero_iff, ZeroMemClass.coe_eq_zero]

/-! ### Kernel = trace radical and the Jones quotient equivalence -/

/-- **The trace radical at `δ = √3` is the kernel of `cubicFixedHom`.** -/
theorem traceRadical_eq_ker_cubicFixedHom
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) :
    (tr m).traceRadical (htr.map_mul_comm m) = RingHom.ker (cubicFixedHom m) := by
  exact LinearMap.traceRadical_eq_ker_of_nullSubmodule_eq_bot (tr m) (htr.map_mul_comm m)
    (scaledCubicFixedPositiveFunctional m)
    (nullSubmodule_scaledCubicFixedPositiveFunctional m)
    (cubicFixedHom m)
    (fun a ↦ (htr.apply_eq_mul_trace_cubicFixedHom m a).symm)

/-- At `δ = √3`, the trace radical is star-stable. -/
theorem isStar_traceRadical_sqrt_three
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) :
    ((tr m).traceRadical (htr.map_mul_comm m)).IsStar where
  star_mem {a} ha := by
    rw [htr.traceRadical_eq_ker_cubicFixedHom, RingHom.mem_ker] at ha ⊢
    rw [map_star, ha, star_zero]

/-- At `δ = √3`, the null vectors of `x ↦ tr m (star x * x)` are precisely the trace radical.
-/
theorem map_star_mul_self_eq_zero_iff_mem_traceRadical_sqrt_three
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) {m : ℕ}
    {x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m} :
    tr m (star x * x) = 0 ↔ x ∈ (tr m).traceRadical (htr.map_mul_comm m) := by
  rw [htr.map_star_mul_self_eq_zero_iff_cubicFixedHom_eq_zero,
    htr.traceRadical_eq_ker_cubicFixedHom, RingHom.mem_ker]

/-- **The Jones quotient at `δ = √3` is isomorphic to the inversion-fixed cubic quantum torus**
`cubicFixed (m - 1)`. -/
noncomputable def quotientCubicFixedEquiv
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) :
    (TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m ⧸
        (tr m).traceRadical (htr.map_mul_comm m)) ≃ₐ[ℂ]
      cubicFixed (m - 1) :=
  (Ideal.quotientEquivAlgOfEq ℂ
      ((htr.traceRadical_eq_ker_cubicFixedHom m).trans
        (show RingHom.ker (cubicFixedHom m) = RingHom.ker (cubicFixedHom m).toAlgHom from
          rfl))).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := (cubicFixedHom m).toAlgHom)
      (cubicFixedHom_surjective m))

/-- `quotientCubicFixedEquiv` evaluates on a quotient representative via `cubicFixedHom`. -/
@[simp]
theorem quotientCubicFixedEquiv_mk
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ)
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    htr.quotientCubicFixedEquiv m
        (Ideal.Quotient.mk ((tr m).traceRadical (htr.map_mul_comm m)) x) =
      cubicFixedHom m x := by
  rw [quotientCubicFixedEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk]
  exact Ideal.quotientKerAlgEquivOfSurjective_mk (f := (cubicFixedHom m).toAlgHom)
    (cubicFixedHom_surjective m) x

/-- `quotientCubicFixedEquiv` is `⋆`-compatible whenever the quotient carries the induced star
structure. -/
@[simp]
theorem quotientCubicFixedEquiv_star
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ)
    [((tr m).traceRadical (htr.map_mul_comm m)).IsStar]
    (q : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m ⧸
      (tr m).traceRadical (htr.map_mul_comm m)) :
    htr.quotientCubicFixedEquiv m (star q) = star (htr.quotientCubicFixedEquiv m q) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp [Ideal.Quotient.star_mk, map_star]

/-- `quotientCubicFixedEquiv` intertwines the Temperley–Lieb quotient strand map
`quotientStrandIncl` with the coordinate inclusion `cubicFixedIncl`. -/
theorem quotientCubicFixedEquiv_quotientStrandIncl
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (n : ℕ)
    (q : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) (n + 1) ⧸
      (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) :
    htr.quotientCubicFixedEquiv (n + 2) (htr.quotientStrandIncl n q) =
      cubicFixedIncl n (htr.quotientCubicFixedEquiv (n + 1) q) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [htr.quotientStrandIncl_mk, htr.quotientCubicFixedEquiv_mk (n + 2),
    htr.quotientCubicFixedEquiv_mk (n + 1), cubicFixedHom_strandIncl]

/-- `(quotientCubicFixedEquiv m).symm` maps `cubicFixedHom m x` back to the quotient class of
`x`. -/
@[simp]
theorem quotientCubicFixedEquiv_symm_cubicFixedHom
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ)
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    (htr.quotientCubicFixedEquiv m).symm (cubicFixedHom m x) =
      Ideal.Quotient.mk ((tr m).traceRadical (htr.map_mul_comm m)) x :=
  (htr.quotientCubicFixedEquiv m).injective (by simp)

/-- `(quotientCubicFixedEquiv _).symm` intertwines `cubicFixedIncl` with `quotientStrandIncl`. -/
theorem quotientCubicFixedEquiv_symm_cubicFixedIncl
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (n : ℕ)
    (y : cubicFixed n) :
    (htr.quotientCubicFixedEquiv (n + 2)).symm (cubicFixedIncl n y) =
      htr.quotientStrandIncl n ((htr.quotientCubicFixedEquiv (n + 1)).symm y) := by
  apply (htr.quotientCubicFixedEquiv (n + 2)).injective
  rw [AlgEquiv.apply_symm_apply, htr.quotientCubicFixedEquiv_quotientStrandIncl,
    AlgEquiv.apply_symm_apply]

/-- The induced trace on the `m`-strand Temperley–Lieb quotient at `δ = √3` is
`(√3 : ℂ) ^ m` times `TwistedMonoidAlgebra.trace` under `quotientCubicFixedEquiv`. -/
theorem quotientTrace_eq_mul_trace_quotientCubicFixedEquiv
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ)
    (q : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m ⧸
      (tr m).traceRadical (htr.map_mul_comm m)) :
    (tr m).quotientTrace (htr.map_mul_comm m) q =
      (Real.sqrt 3 : ℂ) ^ m *
        TwistedMonoidAlgebra.trace (htr.quotientCubicFixedEquiv m q : CubicTorus (m - 1)) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp [htr.apply_eq_mul_trace_cubicFixedHom]

/-- Transporting `quotientTrace` across `(quotientCubicFixedEquiv m).symm` gives `(√3 : ℂ) ^ m`
times `TwistedMonoidAlgebra.trace`. -/
@[simp]
theorem quotientTrace_quotientCubicFixedEquiv_symm
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) (x : cubicFixed (m - 1)) :
    (tr m).quotientTrace (htr.map_mul_comm m) ((htr.quotientCubicFixedEquiv m).symm x) =
      (Real.sqrt 3 : ℂ) ^ m * TwistedMonoidAlgebra.trace (x : CubicTorus (m - 1)) := by
  simp [htr.quotientTrace_eq_mul_trace_quotientCubicFixedEquiv]

/-- The `m`-strand Temperley–Lieb trace quotient at `δ = √3` has complex dimension
`(3 ^ (m - 1) + 1) / 2`. -/
@[simp]
theorem finrank_quotient_traceRadical_sqrt_three
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) :
    Module.finrank ℂ
        (TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m ⧸ (tr m).traceRadical (htr.map_mul_comm m)) =
      (3 ^ (m - 1) + 1) / 2 := by
  rw [(htr.quotientCubicFixedEquiv m).toLinearEquiv.finrank_eq, finrank_cubicFixed]

end IsMarkovTrace

/-- Specialization of `IsMarkovTrace.apply_eq_mul_trace_cubicFixedHom` to the spin-model
`markovTrace` at any unit `q : ℂˣ` satisfying `(√3 : ℂ) = -(q + q⁻¹)`. -/
theorem markovTrace_eq_mul_trace_cubicFixedHom (q : ℂˣ)
    (hq : (Real.sqrt 3 : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ))) {m : ℕ}
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    markovTrace q hq x =
      (Real.sqrt 3 : ℂ) ^ m *
        TwistedMonoidAlgebra.trace (cubicFixedHom m x : CubicTorus (m - 1)) :=
  (isMarkovTrace_markovTrace q hq).apply_eq_mul_trace_cubicFixedHom m x

/-! ### Packaged cubic model and vanishing of the five-strand Jones–Wenzl projection -/

/-- **The cubic quantum torus model of `TemperleyLieb ℂ (√3 : ℂ) m`.** For every Markov trace
`tr` at loop value `√3` and every `m : ℕ`, there is a surjective `⋆`-algebra homomorphism
`F : TemperleyLieb ℂ (√3 : ℂ) m →⋆ₐ[ℂ] cubicFixed (m - 1)` sending each `e j` to
`(√3 : ℂ) • cubicProjection (m - 1) j`, expressing `tr m` as `(√3 : ℂ) ^ m` times
`TwistedMonoidAlgebra.trace`, and having kernel equal to `(tr m).traceRadical`. -/
theorem exists_cubicFixedModel
    {tr : ∀ n : ℕ, TemperleyLieb ℂ (Real.sqrt 3 : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) :
    ∃ F : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →⋆ₐ[ℂ] cubicFixed (m - 1),
      Function.Surjective F ∧
      (∀ j : Fin (m - 1),
        (F (e (Real.sqrt 3 : ℂ) j) : CubicTorus (m - 1)) =
          (Real.sqrt 3 : ℂ) • cubicProjection (m - 1) j) ∧
      (∀ x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m,
        tr m x =
          (Real.sqrt 3 : ℂ) ^ m * TwistedMonoidAlgebra.trace (F x : CubicTorus (m - 1))) ∧
      RingHom.ker F = (tr m).traceRadical (htr.map_mul_comm m) :=
  ⟨cubicFixedHom m,
    cubicFixedHom_surjective m,
    coe_cubicFixedHom_e m,
    htr.apply_eq_mul_trace_cubicFixedHom m,
    (htr.traceRadical_eq_ker_cubicFixedHom m).symm⟩

/-- At `δ = √3`, `cubicFixedHom 5` maps the five-strand Jones–Wenzl projection
`jonesWenzl (√3 : ℂ) 5` to `0`. -/
@[simp]
theorem cubicFixedHom_jonesWenzl_five :
    cubicFixedHom 5 (jonesWenzl (Real.sqrt 3 : ℂ) 5) = 0 := by
  have hq3 : qInt ℂ (Real.sqrt 3 : ℂ) 3 = 2 := by
    rw [qInt_add_two (Real.sqrt 3 : ℂ) 1, qInt_two, qInt_one, sqrt_three_mul_self]
    norm_num
  have hq4 : qInt ℂ (Real.sqrt 3 : ℂ) 4 = (Real.sqrt 3 : ℂ) := by
    rw [qInt_add_two (Real.sqrt 3 : ℂ) 2, hq3, qInt_two]
    ring
  have hq5 : qInt ℂ (Real.sqrt 3 : ℂ) 5 = 1 := by
    rw [qInt_add_two (Real.sqrt 3 : ℂ) 3, hq4, hq3, sqrt_three_mul_self]
    norm_num
  have hq6 : qInt ℂ (Real.sqrt 3 : ℂ) 6 = 0 := by
    rw [qInt_add_two (Real.sqrt 3 : ℂ) 4, hq5, hq4]
    ring
  have hunits : ∀ k ∈ Finset.Icc 1 5, IsUnit (qInt ℂ (Real.sqrt 3 : ℂ) k) := by
    intro k hk
    obtain ⟨hk1, hk5⟩ := Finset.mem_Icc.mp hk
    interval_cases k
    · simp
    · simp [qInt_two]
    · simp [hq3]
    · simp [hq4]
    · simp [hq5]
  rw [← RingHom.mem_ker, ← isMarkovTrace_cubicFixedTrace.traceRadical_eq_ker_cubicFixedHom 5,
    isMarkovTrace_cubicFixedTrace.jonesWenzl_mem_traceRadical_iff hunits]
  exact hq6

end TauCeti.TemperleyLieb
