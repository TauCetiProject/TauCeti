/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.CubicTorus.Basic
public import TauCeti.Algebra.TemperleyLieb.Trace.Radical
public import TauCeti.Algebra.TemperleyLieb.Trace.Star
public import Mathlib.Analysis.Complex.Order
-- Private: bounded interval case analysis is proof-only.
import Mathlib.Tactic.IntervalCases

/-!
# The Jones quotient at `δ = √3` is the inversion-fixed cubic quantum torus

In `TauCeti.Algebra.TemperleyLieb.CubicTorus.Basic` we constructed the cubic quantum torus
`CubicTorus N`, its inversion-fixed subalgebra `cubicFixed N` of complex dimension
`(3 ^ N + 1) / 2`, and the surjective star-compatible comparison homomorphism
`cubicFixedHom m : TemperleyLieb ℂ (√3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1)` sending each generator
`e (√3 : ℂ) j` to `(√3 : ℂ) • cubicProjection (m - 1) j`.

Extending `(ZMod 3)^N` by `0` in the last coordinate preserves `cubicFactor`, inducing injective
tower inclusions `cubicIncl N : CubicTorus N →ₐ[ℂ] CubicTorus (N + 1)` and
`cubicFixedIncl N : cubicFixed N →ₐ[ℂ] cubicFixed (N + 1)` that intertwine `strandIncl`,
`cubicAdjoint`, `cubicInversion`, and `cubicScalarCoefficient`. Multiplying an included element on
the right by the last spectral projection `cubicProjection (N + 1) (Fin.last N)` scales
`cubicScalarCoefficient` by `3⁻¹`, because the `W(e_N)` and `W(2 e_N)` terms shift coordinates
outside the image of `cubicExtendHom N`.

Rescaling by `(√3 : ℂ) ^ m` therefore defines an unnormalized Markov trace `cubicTrace` on
`TemperleyLieb ℂ (√3 : ℂ)`. By `IsMarkovTrace.unique`, *every* Markov trace `tr` at loop value
`√3` equals `(√3 : ℂ) ^ m` times `cubicScalarCoefficient (m - 1) ∘ cubicFixedHom m`. Faithfulness
and positivity of `cubicScalarCoefficient (x† * x)` on `CubicTorus (m - 1)` yield positivity of the
Markov trace at the `A_5` discrete-series point `2 cos (π / 6) = √3`, identify the trace radical
`(tr m).traceRadical` with `RingHom.ker (cubicFixedHom m)`, and establish the quotient isomorphism
`(TemperleyLieb ℂ (√3 : ℂ) m ⧸ (tr m).traceRadical) ≃ₐ[ℂ] cubicFixed (m - 1)` of complex dimension
`(3 ^ (m - 1) + 1) / 2`, where the five-strand Jones–Wenzl projection vanishes.

## Main definitions

* `TauCeti.TemperleyLieb.cubicExtendHom`: extension of `Multiplicative (Fin N → ZMod 3)` by `0` in
  the last coordinate.
* `TauCeti.TemperleyLieb.cubicIncl` and `TauCeti.TemperleyLieb.cubicFixedIncl`: injective tower
  inclusions `CubicTorus N →ₐ[ℂ] CubicTorus (N + 1)` and `cubicFixed N →ₐ[ℂ] cubicFixed (N + 1)`.
* `TauCeti.TemperleyLieb.cubicTrace`: the unnormalized Markov trace on
  `TemperleyLieb ℂ (√3 : ℂ)` induced by `cubicScalarCoefficient` and `cubicFixedHom`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientCubicFixedEquiv`: the `ℂ`-algebra isomorphism
  `(TemperleyLieb ℂ (√3 : ℂ) m ⧸ (tr m).traceRadical) ≃ₐ[ℂ] cubicFixed (m - 1)`.

## Main results

* `TauCeti.TemperleyLieb.isMarkovTrace_cubicTrace` and
  `TauCeti.TemperleyLieb.IsMarkovTrace.apply_eq_mul_cubicScalarCoefficient_cubicFixedHom`:
  every Markov trace at `δ = √3` is `(√3 : ℂ) ^ m` times `cubicScalarCoefficient ∘ cubicFixedHom`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.map_star_mul_self_nonneg_sqrt_three` and
  `TauCeti.TemperleyLieb.IsMarkovTrace.traceRadical_eq_ker_cubicFixedHom`: positivity of
  `tr m (star x * x)` and identification of the trace radical with `RingHom.ker (cubicFixedHom m)`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.finrank_quotient_traceRadical_sqrt_three`: the `m`-strand
  trace quotient at `δ = √3` has complex dimension `(3 ^ (m - 1) + 1) / 2`.
* `TauCeti.TemperleyLieb.exists_cubicFixedModel` and
  `TauCeti.TemperleyLieb.cubicFixedHom_jonesWenzl_five`: packaged cubic fixed-point model and
  vanishing of the five-strand Jones–Wenzl projection.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. (N.S.) 12 (1985), 103–111.
* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*, MSRI
  Publications 14, Springer, 1989.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4.
-/

public section

open Multiplicative
open scoped ComplexOrder

namespace TauCeti.TemperleyLieb

/-! ### Coordinate extension and tower inclusions -/

/-- Multiplicative group homomorphism extending `a : Multiplicative (Fin N → ZMod 3)` by `0` in the
last coordinate. -/
def cubicExtendHom (N : ℕ) :
    Multiplicative (Fin N → ZMod 3) →* Multiplicative (Fin (N + 1) → ZMod 3) where
  toFun a := ofAdd (Fin.snoc a.toAdd 0)
  map_one' := by
    apply toAdd.injective
    ext i
    refine Fin.lastCases ?_ (fun i ↦ ?_) i <;> simp
  map_mul' a b := by
    apply toAdd.injective
    ext i
    refine Fin.lastCases ?_ (fun i ↦ ?_) i <;> simp

@[simp]
theorem toAdd_cubicExtendHom (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    (cubicExtendHom N a).toAdd = Fin.snoc (α := fun _ ↦ ZMod 3) a.toAdd 0 :=
  (rfl)

/-- `cubicExtendHom N` is injective. -/
theorem cubicExtendHom_injective (N : ℕ) : Function.Injective (cubicExtendHom N) := by
  intro a b h
  apply toAdd.injective
  ext i
  simpa using congrFun (congrArg toAdd h) i.castSucc

@[simp]
theorem cubicExtendHom_ofAdd_single (N : ℕ) (j : Fin N) (c : ZMod 3) :
    cubicExtendHom N (ofAdd (Pi.single j c)) = ofAdd (Pi.single j.castSucc c) := by
  apply toAdd.injective
  ext i
  refine Fin.lastCases ?_ (fun i ↦ ?_) i
  · simp [(Fin.castSucc_lt_last j).ne.symm]
  · simp [Pi.single_apply, Fin.castSucc_inj]

/-- `cubicExtendHom N` pulls `cubicFactor (N + 1)` back to `cubicFactor N`. -/
@[simp]
theorem cubicFactor_cubicExtendHom (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor (N + 1) (cubicExtendHom N a) (cubicExtendHom N b) = cubicFactor N a b := by
  rw [cubicFactor_def, cubicFactor_def, toAdd_cubicExtendHom, toAdd_cubicExtendHom,
    chainForm_snoc_zero]

private theorem ofAdd_single_last_notMem_range_cubicExtendHom (N : ℕ) {r : ZMod 3} (hr : r ≠ 0) :
    ofAdd (Pi.single (Fin.last N) r) ∉ Set.range (cubicExtendHom N) := by
  rintro ⟨a, ha⟩
  have h := congrFun (congrArg toAdd ha) (Fin.last N)
  simp at h
  exact hr h.symm

/-- **The tower inclusion** `I_N : CubicTorus N →ₐ[ℂ] CubicTorus (N + 1)` sending `W(a)` to
`W(a, 0)`. -/
noncomputable def cubicIncl (N : ℕ) : CubicTorus N →ₐ[ℂ] CubicTorus (N + 1) :=
  TwistedMonoidAlgebra.mapDomain (cubicExtendHom N) (cubicFactor_cubicExtendHom N)

/-- Unfolds `cubicIncl N`. -/
theorem cubicIncl_def (N : ℕ) :
    cubicIncl N =
      TwistedMonoidAlgebra.mapDomain (cubicExtendHom N) (cubicFactor_cubicExtendHom N) :=
  (rfl)

/-- `cubicIncl N` is injective. -/
theorem cubicIncl_injective (N : ℕ) : Function.Injective (cubicIncl N) :=
  TwistedMonoidAlgebra.mapDomain_injective (cubicFactor_cubicExtendHom N)
    (cubicExtendHom_injective N)

@[simp]
theorem cubicIncl_weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicIncl N (weyl N a) = weyl (N + 1) (cubicExtendHom N a) := by
  rw [weyl_def, weyl_def, cubicIncl_def, TwistedMonoidAlgebra.mapDomain_of]

@[simp]
theorem cubicIncl_cubicSite (N : ℕ) (j : Fin N) :
    cubicIncl N (cubicSite N j) = cubicSite (N + 1) j.castSucc := by
  rw [cubicSite_def, cubicIncl_weyl, cubicExtendHom_ofAdd_single, ← cubicSite_def]

@[simp]
theorem cubicIncl_cubicProjection (N : ℕ) (j : Fin N) :
    cubicIncl N (cubicProjection N j) = cubicProjection (N + 1) j.castSucc := by
  have hadd (a b) : cubicIncl N (a + b) = cubicIncl N a + cubicIncl N b :=
    (cubicIncl N).map_add' a b
  rw [cubicProjection_def, cubicProjection_def, AlgHom.map_smul_of_tower, hadd, hadd, map_one,
    map_pow, cubicIncl_cubicSite]

/-- `cubicIncl N` intertwines `cubicAdjoint`. -/
@[simp]
theorem cubicAdjoint_cubicIncl (N : ℕ) (x : CubicTorus N) :
    cubicAdjoint (N + 1) (cubicIncl N x) = cubicIncl N (cubicAdjoint N x) :=
  TwistedMonoidAlgebra.conjReverse_mapDomain (cubicExtendHom N) (cubicFactor_cubicExtendHom N) x

/-- `cubicIncl N` preserves `cubicScalarCoefficient`. -/
@[simp]
theorem cubicScalarCoefficient_cubicIncl (N : ℕ) (x : CubicTorus N) :
    cubicScalarCoefficient (N + 1) (cubicIncl N x) = cubicScalarCoefficient N x :=
  TwistedMonoidAlgebra.scalarTrace_mapDomain_of_injective (cubicFactor_cubicExtendHom N)
    (cubicExtendHom_injective N) x

/-- `cubicIncl N` intertwines `cubicInversion`. -/
@[simp]
theorem cubicInversion_cubicIncl (N : ℕ) (x : CubicTorus N) :
    cubicInversion (N + 1) (cubicIncl N x) = cubicIncl N (cubicInversion N x) := by
  have hcomp : (cubicInversion (N + 1)).comp (cubicIncl N) =
      (cubicIncl N).comp (cubicInversion N) :=
    TwistedMonoidAlgebra.algHom_ext fun a ↦ by
      rw [AlgHom.comp_apply, AlgHom.comp_apply, ← weyl_def, cubicIncl_weyl, cubicInversion_weyl,
        cubicInversion_weyl, cubicIncl_weyl, map_inv]
  exact AlgHom.congr_fun hcomp x

/-- `cubicIncl N` maps `cubicFixed N` into `cubicFixed (N + 1)`. -/
theorem cubicIncl_mem_cubicFixed {N : ℕ} {x : CubicTorus N} (hx : x ∈ cubicFixed N) :
    cubicIncl N x ∈ cubicFixed (N + 1) := by
  rw [mem_cubicFixed_iff, cubicInversion_cubicIncl, mem_cubicFixed_iff.mp hx]

/-- **The restricted tower inclusion** `cubicFixed N →ₐ[ℂ] cubicFixed (N + 1)`. -/
noncomputable def cubicFixedIncl (N : ℕ) : cubicFixed N →ₐ[ℂ] cubicFixed (N + 1) :=
  ((cubicIncl N).comp (cubicFixed N).val).codRestrict (cubicFixed (N + 1))
    fun x ↦ cubicIncl_mem_cubicFixed x.2

@[simp]
theorem coe_cubicFixedIncl (N : ℕ) (x : cubicFixed N) :
    (cubicFixedIncl N x : CubicTorus (N + 1)) = cubicIncl N x :=
  (rfl)

/-- `cubicFixedIncl N` is injective. -/
theorem cubicFixedIncl_injective (N : ℕ) : Function.Injective (cubicFixedIncl N) := by
  intro x y h
  exact Subtype.ext (cubicIncl_injective N (congrArg Subtype.val h))

/-- `cubicFixedIncl N` intertwines `cubicFixedAdjoint`. -/
@[simp]
theorem cubicFixedAdjoint_cubicFixedIncl (N : ℕ) (x : cubicFixed N) :
    cubicFixedAdjoint (N + 1) (cubicFixedIncl N x) = cubicFixedIncl N (cubicFixedAdjoint N x) := by
  apply Subtype.ext
  rw [coe_cubicFixedAdjoint, coe_cubicFixedIncl, coe_cubicFixedIncl, coe_cubicFixedAdjoint,
    cubicAdjoint_cubicIncl]

/-- `cubicFixedHom` intertwines `TemperleyLieb.strandIncl` with `cubicFixedIncl`. -/
theorem cubicFixedHom_strandIncl (n : ℕ) (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) (n + 1)) :
    cubicFixedHom (n + 2) (strandIncl x) = cubicFixedIncl n (cubicFixedHom (n + 1) x) := by
  have hhom : (cubicFixedHom (n + 2)).comp strandIncl =
      (cubicFixedIncl n).comp (cubicFixedHom (n + 1)) := by
    apply TemperleyLieb.hom_ext
    intro i
    apply Subtype.ext
    rw [AlgHom.comp_apply, AlgHom.comp_apply, strandIncl_e, coe_cubicFixedHom_e,
      coe_cubicFixedIncl, coe_cubicFixedHom_e, AlgHom.map_smul_of_tower]
    exact congrArg ((Real.sqrt 3 : ℂ) • ·) (cubicIncl_cubicProjection n i).symm
  exact AlgHom.congr_fun hhom x

/-! ### Markov partial-trace identity and uniqueness of the cubic Markov trace -/

/-- Multiplying an included element `cubicIncl N x` on the right by the last spectral projection
`cubicProjection (N + 1) (Fin.last N)` scales `cubicScalarCoefficient` by `3⁻¹`: the `W(e_N)` and
`W(2 e_N)` terms vanish because their inverse group elements lie outside
`Set.range (cubicExtendHom N)`. -/
theorem cubicScalarCoefficient_cubicIncl_mul_cubicProjection_last (N : ℕ) (x : CubicTorus N) :
    cubicScalarCoefficient (N + 1) (cubicIncl N x * cubicProjection (N + 1) (Fin.last N)) =
      (3 : ℂ)⁻¹ * cubicScalarCoefficient N x := by
  have hzero : ∀ {r : ZMod 3}, r ≠ 0 →
      cubicScalarCoefficient (N + 1)
        (cubicIncl N x * weyl (N + 1) (ofAdd (Pi.single (Fin.last N) r))) = 0 := by
    intro r hr
    have hinv : (ofAdd (Pi.single (Fin.last N) r))⁻¹ =
        ofAdd (Pi.single (M := fun _ ↦ ZMod 3) (Fin.last N) (-r)) := by
      rw [← ofAdd_neg, ← Pi.single_neg]
    have hnotMem : (ofAdd (Pi.single (Fin.last N) r))⁻¹ ∉ Set.range (cubicExtendHom N) := by
      rw [hinv]
      exact ofAdd_single_last_notMem_range_cubicExtendHom N (neg_ne_zero.mpr hr)
    rw [weyl_def, TwistedMonoidAlgebra.scalarTrace_mul_of, cubicIncl_def,
      TwistedMonoidAlgebra.basis_repr_mapDomain_of_notMem_range (cubicExtendHom N)
        (cubicFactor_cubicExtendHom N) x hnotMem,
      zero_mul]
  rw [cubicProjection_def, cubicSite_sq, cubicSite_def, mul_smul_comm, map_smul, smul_eq_mul,
    mul_add, mul_add, mul_one, map_add, map_add, cubicScalarCoefficient_cubicIncl,
    hzero (by decide), hzero (by decide), add_zero, add_zero]

/-- The unnormalized Markov trace on `TemperleyLieb ℂ (√3 : ℂ)` obtained by pulling back
`(√3 : ℂ) ^ m` times `cubicScalarCoefficient (m - 1)` along `cubicFixedHom m`. -/
noncomputable def cubicTrace (m : ℕ) : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →ₗ[ℂ] ℂ :=
  ((Real.sqrt 3 : ℂ) ^ m) •
    (cubicScalarCoefficient (m - 1) ∘ₗ
      (cubicFixed (m - 1)).val.toLinearMap ∘ₗ (cubicFixedHom m).toLinearMap)

/-- Evaluation formula for `cubicTrace`. -/
theorem cubicTrace_apply (m : ℕ) (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    cubicTrace m x =
      (Real.sqrt 3 : ℂ) ^ m * cubicScalarCoefficient (m - 1) (cubicFixedHom m x) := by
  simp [cubicTrace]

/-- **The cubic scalar trace defines an unnormalized Markov trace at `δ = √3`.** -/
theorem isMarkovTrace_cubicTrace : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) cubicTrace where
  map_one m := by
    rw [cubicTrace_apply, map_one, Subalgebra.coe_one,
      TwistedMonoidAlgebra.scalarTrace_one, mul_one]
  map_mul_comm m x y := by
    rw [cubicTrace_apply, cubicTrace_apply, map_mul, map_mul,
      Subalgebra.coe_mul, Subalgebra.coe_mul, TwistedMonoidAlgebra.scalarTrace_mul_comm]
  map_strandIncl n x := by
    rw [cubicTrace_apply, cubicTrace_apply, cubicFixedHom_strandIncl, coe_cubicFixedIncl]
    change (Real.sqrt 3 : ℂ) ^ (n + 2) *
        cubicScalarCoefficient (n + 1) (cubicIncl n (cubicFixedHom (n + 1) x).1) =
      (Real.sqrt 3 : ℂ) *
        ((Real.sqrt 3 : ℂ) ^ (n + 1) * cubicScalarCoefficient n (cubicFixedHom (n + 1) x).1)
    rw [cubicScalarCoefficient_cubicIncl, pow_succ']
    ring
  map_strandIncl_mul_e_last n x := by
    have hsqrt : (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 := by
      exact_mod_cast Real.mul_self_sqrt (by positivity)
    rw [cubicTrace_apply, cubicTrace_apply, map_mul, Subalgebra.coe_mul,
      cubicFixedHom_strandIncl, coe_cubicFixedIncl, coe_cubicFixedHom_e, mul_smul_comm, map_smul,
      smul_eq_mul]
    change (Real.sqrt 3 : ℂ) ^ (n + 2) *
        ((Real.sqrt 3 : ℂ) *
          cubicScalarCoefficient (n + 1)
            (cubicIncl n (cubicFixedHom (n + 1) x).1 * cubicProjection (n + 1) (Fin.last n))) =
      (Real.sqrt 3 : ℂ) ^ (n + 1) * cubicScalarCoefficient n (cubicFixedHom (n + 1) x).1
    rw [cubicScalarCoefficient_cubicIncl_mul_cubicProjection_last, pow_succ]
    calc
      (Real.sqrt 3 : ℂ) ^ (n + 1) * (Real.sqrt 3 : ℂ) *
          ((Real.sqrt 3 : ℂ) *
            ((3 : ℂ)⁻¹ * cubicScalarCoefficient n (cubicFixedHom (n + 1) x).1))
          = (Real.sqrt 3 : ℂ) ^ (n + 1) *
              (((Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ)) * (3 : ℂ)⁻¹) *
                cubicScalarCoefficient n (cubicFixedHom (n + 1) x).1 := by
            ring
      _ = (Real.sqrt 3 : ℂ) ^ (n + 1) *
            cubicScalarCoefficient n (cubicFixedHom (n + 1) x).1 := by
            rw [hsqrt]
            norm_num

namespace IsMarkovTrace

variable {tr : ∀ n : ℕ, TemperleyLieb ℂ (Real.sqrt 3 : ℂ) n →ₗ[ℂ] ℂ}

/-- Every Markov trace on `TemperleyLieb ℂ (√3 : ℂ)` coincides with `cubicTrace`. -/
theorem eq_cubicTrace (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) : tr = cubicTrace :=
  htr.unique isMarkovTrace_cubicTrace

/-- **The Markov trace at `δ = √3` as the cubic quantum torus trace**: for every Markov trace `tr`,
`tr m x = (√3 : ℂ) ^ m * cubicScalarCoefficient (m - 1) (cubicFixedHom m x)`. -/
theorem apply_eq_mul_cubicScalarCoefficient_cubicFixedHom
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ)
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    tr m x =
      (Real.sqrt 3 : ℂ) ^ m * cubicScalarCoefficient (m - 1) (cubicFixedHom m x) := by
  rw [htr.eq_cubicTrace, cubicTrace_apply]

/-- **Positivity of the Markov trace at `δ = √3`** (the `m = 6` discrete-series point
`2 cos (π / 6)` of Jones's positivity theorem): `0 ≤ tr m (star x * x)` on every number of
strands. -/
theorem map_star_mul_self_nonneg_sqrt_three
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) {m : ℕ}
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    0 ≤ tr m (star x * x) := by
  have hz := TwistedMonoidAlgebra.scalarTrace_conjReverse_mul_self_nonneg
    (cubicFactor_inv_self (m - 1)) (cubicFixedHom m x)
  have hz0 : ((0 : ℝ) : ℂ) ≤
      cubicScalarCoefficient (m - 1)
        (cubicAdjoint (m - 1) (cubicFixedHom m x) * cubicFixedHom m x) := by
    simpa using hz
  rw [htr.apply_eq_mul_cubicScalarCoefficient_cubicFixedHom, map_mul,
    Subalgebra.coe_mul, coe_cubicFixedHom_star, Complex.eq_re_of_ofReal_le hz0,
    ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.zero_le_real]
  exact mul_nonneg (by positivity) (Complex.nonneg_iff.mp hz).1

/-- At `δ = √3`, `tr m (star x * x) = 0` if and only if `cubicFixedHom m x = 0`. -/
theorem map_star_mul_self_eq_zero_iff_cubicFixedHom_eq_zero
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) {m : ℕ}
    {x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m} :
    tr m (star x * x) = 0 ↔ cubicFixedHom m x = 0 := by
  have hne : (Real.sqrt 3 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  rw [htr.apply_eq_mul_cubicScalarCoefficient_cubicFixedHom, map_mul,
    Subalgebra.coe_mul, coe_cubicFixedHom_star, mul_eq_zero, or_iff_right (pow_ne_zero m hne),
    TwistedMonoidAlgebra.scalarTrace_conjReverse_mul_self_eq_zero_iff
      (cubicFactor_inv_self (m - 1)),
    ZeroMemClass.coe_eq_zero]

/-! ### Kernel = trace radical and the Jones quotient equivalence -/

/-- **The trace radical at `δ = √3` is the kernel of `cubicFixedHom`.** -/
theorem traceRadical_eq_ker_cubicFixedHom
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) :
    (tr m).traceRadical (htr.map_mul_comm m) = RingHom.ker (cubicFixedHom m) := by
  ext x
  rw [LinearMap.mem_traceRadical, RingHom.mem_ker]
  refine ⟨fun hx ↦ ?_, fun hx y ↦ ?_⟩
  · rw [← htr.map_star_mul_self_eq_zero_iff_cubicFixedHom_eq_zero, htr.map_mul_comm]
    exact hx (star x)
  · rw [htr.apply_eq_mul_cubicScalarCoefficient_cubicFixedHom, map_mul, hx,
      zero_mul, Subalgebra.coe_zero, map_zero, mul_zero]

/-- At `δ = √3`, the null vectors of `x ↦ tr m (star x * x)` are precisely the trace radical. -/
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
    (TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m ⧸ (tr m).traceRadical (htr.map_mul_comm m)) ≃ₐ[ℂ]
      cubicFixed (m - 1) :=
  (Ideal.quotientEquivAlgOfEq ℂ (htr.traceRadical_eq_ker_cubicFixedHom m)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (cubicFixedHom_surjective m))

/-- `quotientCubicFixedEquiv` evaluates on a quotient representative via `cubicFixedHom`. -/
@[simp]
theorem quotientCubicFixedEquiv_mk
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ)
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    htr.quotientCubicFixedEquiv m
        (Ideal.Quotient.mk ((tr m).traceRadical (htr.map_mul_comm m)) x) =
      cubicFixedHom m x := by
  simp [quotientCubicFixedEquiv, Ideal.quotientEquivAlgOfEq_mk]

/-- `quotientCubicFixedEquiv` intertwines the Temperley–Lieb quotient strand map
`quotientStrandIncl` with `cubicFixedIncl`. -/
theorem quotientCubicFixedEquiv_quotientStrandIncl
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (n : ℕ)
    (q : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) (n + 1) ⧸
      (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) :
    htr.quotientCubicFixedEquiv (n + 2) (htr.quotientStrandIncl n q) =
      cubicFixedIncl n (htr.quotientCubicFixedEquiv (n + 1) q) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [htr.quotientStrandIncl_mk, htr.quotientCubicFixedEquiv_mk, htr.quotientCubicFixedEquiv_mk,
    cubicFixedHom_strandIncl]

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
      htr.quotientStrandIncl n ((htr.quotientCubicFixedEquiv (n + 1)).symm y) :=
  (htr.quotientCubicFixedEquiv (n + 2)).injective <| by
    rw [AlgEquiv.apply_symm_apply, htr.quotientCubicFixedEquiv_quotientStrandIncl,
      AlgEquiv.apply_symm_apply]

/-- The induced trace on the `m`-strand Temperley–Lieb quotient at `δ = √3` is `(√3 : ℂ) ^ m` times
`cubicScalarCoefficient (m - 1)` under `quotientCubicFixedEquiv`. -/
theorem quotientTrace_eq_mul_cubicScalarCoefficient_quotientCubicFixedEquiv
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ)
    (q : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m ⧸
      (tr m).traceRadical (htr.map_mul_comm m)) :
    (tr m).quotientTrace (htr.map_mul_comm m) q =
      (Real.sqrt 3 : ℂ) ^ m *
        cubicScalarCoefficient (m - 1) (htr.quotientCubicFixedEquiv m q) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp [htr.apply_eq_mul_cubicScalarCoefficient_cubicFixedHom]

/-- Transporting `quotientTrace` across `(quotientCubicFixedEquiv m).symm` gives `(√3 : ℂ) ^ m`
times `cubicScalarCoefficient (m - 1)`. -/
@[simp]
theorem quotientTrace_quotientCubicFixedEquiv_symm
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) (x : cubicFixed (m - 1)) :
    (tr m).quotientTrace (htr.map_mul_comm m) ((htr.quotientCubicFixedEquiv m).symm x) =
      (Real.sqrt 3 : ℂ) ^ m * cubicScalarCoefficient (m - 1) x := by
  simp [htr.quotientTrace_eq_mul_cubicScalarCoefficient_quotientCubicFixedEquiv]

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

/-- Specialization of `IsMarkovTrace.apply_eq_mul_cubicScalarCoefficient_cubicFixedHom` to the
spin-model `markovTrace` at any unit `q : ℂˣ` satisfying `(√3 : ℂ) = -(q + q⁻¹)`. -/
theorem markovTrace_eq_mul_cubicScalarCoefficient_cubicFixedHom (q : ℂˣ)
    (hq : (Real.sqrt 3 : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ))) {m : ℕ}
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    markovTrace q hq x =
      (Real.sqrt 3 : ℂ) ^ m * cubicScalarCoefficient (m - 1) (cubicFixedHom m x) :=
  (isMarkovTrace_markovTrace q hq).apply_eq_mul_cubicScalarCoefficient_cubicFixedHom m x

/-! ### Packaged cubic fixed-point model and vanishing of the five-strand Jones–Wenzl projection -/

/-- **The cubic quantum torus model of `TemperleyLieb ℂ (√3 : ℂ) m`.** For every Markov trace `tr`
at loop value `√3` and every `m : ℕ`, there is a surjective `ℂ`-algebra homomorphism
`F : TemperleyLieb ℂ (√3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1)` sending each generator `e j` to
`(√3 : ℂ) • cubicProjection (m - 1) j`, intertwining `star` with `cubicAdjoint (m - 1)`, expressing
`tr m` as `(√3 : ℂ) ^ m` times `cubicScalarCoefficient (m - 1)`, and having kernel equal to the
trace radical `(tr m).traceRadical`. -/
theorem exists_cubicFixedModel
    {tr : ∀ n : ℕ, TemperleyLieb ℂ (Real.sqrt 3 : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) :
    ∃ F : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1),
      Function.Surjective F ∧
      (∀ j : Fin (m - 1),
        (F (e (Real.sqrt 3 : ℂ) j) : CubicTorus (m - 1)) =
          (Real.sqrt 3 : ℂ) • cubicProjection (m - 1) j) ∧
      (∀ x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m,
        (F (star x) : CubicTorus (m - 1)) =
          cubicAdjoint (m - 1) (F x)) ∧
      (∀ x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m,
        tr m x =
          (Real.sqrt 3 : ℂ) ^ m *
            cubicScalarCoefficient (m - 1) (F x)) ∧
      RingHom.ker F = (tr m).traceRadical (htr.map_mul_comm m) :=
  ⟨cubicFixedHom m,
    cubicFixedHom_surjective m,
    coe_cubicFixedHom_e m,
    coe_cubicFixedHom_star,
    htr.apply_eq_mul_cubicScalarCoefficient_cubicFixedHom m,
    (htr.traceRadical_eq_ker_cubicFixedHom m).symm⟩

/-- At `δ = √3`, `cubicFixedHom 5` maps the five-strand Jones–Wenzl projection
`jonesWenzl (√3 : ℂ) 5` to `0`. -/
@[simp]
theorem cubicFixedHom_jonesWenzl_five :
    cubicFixedHom 5 (jonesWenzl (Real.sqrt 3 : ℂ) 5) = 0 := by
  have hsqrt : (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 := by
    exact_mod_cast Real.mul_self_sqrt (by positivity)
  have hne : (Real.sqrt 3 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  have hq3 : qInt ℂ (Real.sqrt 3 : ℂ) 3 = 2 := by
    rw [qInt_add_two (Real.sqrt 3 : ℂ) 1, qInt_two, qInt_one, hsqrt]
    norm_num
  have hq4 : qInt ℂ (Real.sqrt 3 : ℂ) 4 = (Real.sqrt 3 : ℂ) := by
    rw [qInt_add_two (Real.sqrt 3 : ℂ) 2, hq3, qInt_two]
    ring
  have hq5 : qInt ℂ (Real.sqrt 3 : ℂ) 5 = 1 := by
    rw [qInt_add_two (Real.sqrt 3 : ℂ) 3, hq4, hq3, hsqrt]
    norm_num
  have hq6 : qInt ℂ (Real.sqrt 3 : ℂ) 6 = 0 := by
    rw [qInt_add_two (Real.sqrt 3 : ℂ) 4, hq5, hq4]
    ring
  have hunits : ∀ k ∈ Finset.Icc 1 5, IsUnit (qInt ℂ (Real.sqrt 3 : ℂ) k) := by
    intro k hk
    obtain ⟨hk1, hk5⟩ := Finset.mem_Icc.mp hk
    interval_cases k
    · simp
    · simp [qInt_two, hne]
    · simp [hq3]
    · simp [hq4, hne]
    · simp [hq5]
  rw [← RingHom.mem_ker, ← isMarkovTrace_cubicTrace.traceRadical_eq_ker_cubicFixedHom 5,
    isMarkovTrace_cubicTrace.jonesWenzl_mem_traceRadical_iff hunits]
  exact hq6

end TauCeti.TemperleyLieb
