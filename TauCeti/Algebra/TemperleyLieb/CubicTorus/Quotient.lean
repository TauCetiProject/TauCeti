/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.CubicTorus.Basic
public import TauCeti.Algebra.TemperleyLieb.Trace.Radical
public import TauCeti.RingTheory.Ideal.Quotient.Star
import TauCeti.RingTheory.TraceFunctional.Positive

/-!
# The Jones quotient at `δ = √3` as the inversion-fixed cubic quantum torus

Building on the surjective `⋆`-algebra comparison homomorphism
`F_m = cubicFixedHom m : TemperleyLieb ℂ (√3 : ℂ) m →⋆ₐ[ℂ] cubicFixed (m - 1)` from
`TauCeti.Algebra.TemperleyLieb.CubicTorus.Basic`, this file equips the cubic quantum torus tower
`G_N` and its inversion-fixed tower `C_N = cubicFixed N` with coordinate inclusions, identifies
the Markov trace at `δ = √3` with `(√3) ^ m` times
`TwistedMonoidAlgebra.scalarTrace (cubicFactor (m - 1))`, establishes positivity of the Markov
Hermitian form at `δ = √3`, and identifies the `m`-strand Temperley–Lieb trace-radical quotient
(the Jones quotient at index `δ² = 3`) with `cubicFixed (m - 1)`.

* **Coordinate inclusions and Markov trace identity**: extending `Fin N → ZMod 3` by `0` in the
  last coordinate preserves `chainForm` and `cubicFactor`, inducing injective `⋆`-algebra maps
  `cubicIncl N` and `cubicFixedIncl N` that intertwine `strandIncl` and `cubicInversion`,
  preserve `TwistedMonoidAlgebra.scalarTrace`, and satisfy
  `scalarTrace (cubicIncl N x * cubicProjection (N + 1) (Fin.last N)) = 3⁻¹ * scalarTrace x`
  because every non-identity term in `cubicProjection (N + 1) (Fin.last N)` shifts the last
  coordinate away from `0`. Hence `cubicFixedTrace m x = (√3) ^ m * s_{m - 1} (F_m x)` satisfies
  `IsMarkovTrace`, and Markov uniqueness identifies every Markov trace at `√3` with it.
* **Positivity and the trace radical**: Parseval positivity and faithfulness of
  `TwistedMonoidAlgebra.scalarTracePositiveFunctional (cubicFactor (m - 1))` show that at
  `δ = √3` the Markov Hermitian form `tr m (star x * x)` is positive semidefinite (the `m = 6`
  discrete-series point `2 cos (π / 6)` of Jones's positivity theorem), and
  `LinearMap.traceRadical_eq_ker_of_nullSubmodule_eq_bot` identifies `(tr m).traceRadical` with
  `RingHom.ker (cubicFixedHom m)`.
* **Jones quotient equivalence and five-strand Jones–Wenzl vanishing**: passing to the quotient
  yields `IsMarkovTrace.quotientCubicFixedEquiv` of complex dimension `(3 ^ (m - 1) + 1) / 2`,
  intertwining `quotientStrandIncl` and `quotientTrace`. In particular, at five strands
  (`dim TL_5 = 42`, `dim C_4 = 41`), `cubicFixedHom 5` annihilates the negligible Jones–Wenzl
  projection `jonesWenzl (√3 : ℂ) 5`.

## Main definitions

* `TauCeti.TemperleyLieb.cubicIncl` and `TauCeti.TemperleyLieb.cubicFixedIncl`: the coordinate
  `⋆`-algebra inclusions extending `Fin N → ZMod 3` by zero.
* `TauCeti.TemperleyLieb.cubicFixedTrace`: the unnormalized Markov trace at `√3` induced by
  `TwistedMonoidAlgebra.scalarTrace`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientCubicFixedEquiv`: the algebra isomorphism between
  the `m`-strand Temperley–Lieb trace quotient at `√3` and `cubicFixed (m - 1)`.

## Main results

* `TauCeti.TemperleyLieb.cubicIncl_injective`,
  `TauCeti.TemperleyLieb.cubicFixedIncl_injective`, and
  `TauCeti.TemperleyLieb.cubicFixedHom_strandIncl`: injectivity and tower compatibility of the
  coordinate inclusions.
* `TauCeti.TemperleyLieb.isMarkovTrace_cubicFixedTrace`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.apply_eq_mul_scalarTrace_cubicFixedHom`, and
  `TauCeti.TemperleyLieb.markovTrace_eq_mul_scalarTrace_cubicFixedHom`: the Markov-trace formula
  `tr m x = (√3) ^ m * scalarTrace (cubicFactor (m - 1)) (cubicFixedHom m x)`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.map_star_mul_self_nonneg_sqrt_three`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.traceRadical_eq_ker_cubicFixedHom`, and
  `TauCeti.TemperleyLieb.IsMarkovTrace.isStar_traceRadical_sqrt_three`: positivity of the Markov
  Hermitian form at `δ = √3`, identification of the trace radical with
  `RingHom.ker (cubicFixedHom m)`, and star-stability of the trace radical.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientCubicFixedEquiv_quotientStrandIncl`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.quotientTrace_eq_mul_scalarTrace_quotientCubicFixedEquiv`,
  and `TauCeti.TemperleyLieb.IsMarkovTrace.finrank_quotient_traceRadical_sqrt_three`: tower,
  trace, and dimension (`(3 ^ (m - 1) + 1) / 2`) properties of the Jones quotient equivalence.
* `TauCeti.TemperleyLieb.exists_cubicFixedModel` and
  `TauCeti.TemperleyLieb.cubicFixedHom_jonesWenzl_five`: packaged existence theorem for the
  inversion-fixed cubic quantum torus model at `δ = √3` and vanishing of the five-strand
  Jones–Wenzl projection.

## References

* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), 103–111, p. 107.
* C. Galindo and E. C. Rowell, *Braid representations from unitary braided vector spaces*,
  J. Math. Phys. 55 (2014), 061702.
* E. C. Rowell and H. Wenzl, *SO(N)_2 braid group representations are Gaussian*, Quantum Topol. 8
  (2017), no. 1, 1–33.
-/

public section

open scoped ComplexOrder

namespace TauCeti.TemperleyLieb

/-! ### Coordinate inclusions and the Markov trace identity -/

/-- Extending `Fin N → ZMod 3` by `0` in the last coordinate as a multiplicative group
homomorphism. -/
private def cubicSnocHom (N : ℕ) :
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

private theorem cubicSnocHom_injective (N : ℕ) : Function.Injective (cubicSnocHom N) := by
  intro a b hab
  apply Multiplicative.toAdd.injective
  ext i
  have h := congrFun (congrArg Multiplicative.toAdd hab) i.castSucc
  simpa [cubicSnocHom] using h

/-- Extending two coordinate vectors by `0` in the last coordinate preserves `chainForm`. -/
theorem chainForm_snoc_zero (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm (N + 1) (Fin.snoc a 0) (Fin.snoc b 0) = chainForm N a b := by
  simp only [chainForm_def, Fin.sum_univ_castSucc, Fin.snoc_last, Fin.snoc_castSucc,
    Fin.val_last, Fin.val_castSucc, mul_zero, zero_mul, sub_self, ite_self,
    Finset.sum_const_zero, add_zero]

private theorem cubicFactor_cubicSnocHom (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor (N + 1) (cubicSnocHom N a) (cubicSnocHom N b) = cubicFactor N a b := by
  simp [cubicFactor_def, cubicSnocHom, chainForm_snoc_zero]

/-- The coordinate `⋆`-algebra inclusion `CubicTorus N →⋆ₐ[ℂ] CubicTorus (N + 1)` extending
`Fin N → ZMod 3` by zero in the last coordinate. -/
noncomputable def cubicIncl (N : ℕ) : CubicTorus N →⋆ₐ[ℂ] CubicTorus (N + 1) :=
  TwistedMonoidAlgebra.mapStarAlgHom (cubicSnocHom N) (cubicFactor_cubicSnocHom N)

/-- `cubicIncl N` acts on Weyl basis elements by extending the index vector by `0`. -/
@[simp]
theorem cubicIncl_weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicIncl N (weyl N a) = weyl (N + 1) (Multiplicative.ofAdd (Fin.snoc a.toAdd 0)) := by
  rw [cubicIncl, weyl_def, weyl_def]
  exact TwistedMonoidAlgebra.mapStarAlgHom_of (cubicSnocHom N) (cubicFactor_cubicSnocHom N) a

/-- `cubicIncl N` maps the `j`-th site unitary to `cubicSite (N + 1) j.castSucc`. -/
@[simp]
theorem cubicIncl_cubicSite (N : ℕ) (j : Fin N) :
    cubicIncl N (cubicSite N j) = cubicSite (N + 1) j.castSucc := by
  have hsnoc : Fin.snoc (Pi.single j (1 : ZMod 3) : Fin N → ZMod 3) 0 =
      (Pi.single j.castSucc (1 : ZMod 3) : Fin (N + 1) → ZMod 3) := by
    ext k
    refine Fin.lastCases ?_ (fun k ↦ ?_) k
    · simp [(Fin.castSucc_lt_last j).ne']
    · simp [Pi.single_apply]
  simp [cubicSite_def, hsnoc]

/-- `cubicIncl N` maps the `j`-th Jones projection to `cubicProjection (N + 1) j.castSucc`. -/
@[simp]
theorem cubicIncl_cubicProjection (N : ℕ) (j : Fin N) :
    cubicIncl N (cubicProjection N j) = cubicProjection (N + 1) j.castSucc := by
  simp [cubicProjection_def]

/-- `cubicIncl N` intertwines `cubicInversion` across adjacent dimensions. -/
@[simp]
theorem cubicIncl_cubicInversion (N : ℕ) (x : CubicTorus N) :
    cubicIncl N (cubicInversion N x) = cubicInversion (N + 1) (cubicIncl N x) := by
  have h : (cubicIncl N).toAlgHom.comp (cubicInversion N).toAlgHom =
      (cubicInversion (N + 1)).toAlgHom.comp (cubicIncl N).toAlgHom := by
    apply TwistedMonoidAlgebra.algHom_ext
    intro a
    simp only [AlgHom.comp_apply, StarAlgHom.coe_toAlgHom, ← weyl_def, cubicInversion_weyl,
      cubicIncl_weyl]
    congr 1
    apply Multiplicative.toAdd.injective
    ext k
    refine Fin.lastCases ?_ (fun k ↦ ?_) k <;> simp
  exact AlgHom.congr_fun h x

/-- Coordinate inclusion preserves the scalar trace. -/
@[simp]
theorem scalarTrace_cubicIncl (N : ℕ) (x : CubicTorus N) :
    TwistedMonoidAlgebra.scalarTrace (cubicFactor (N + 1)) (cubicIncl N x) =
      TwistedMonoidAlgebra.scalarTrace (cubicFactor N) x :=
  TwistedMonoidAlgebra.scalarTrace_mapStarAlgHom
    (cubicFactor_cubicSnocHom N) (cubicSnocHom_injective N) x

/-- The coordinate inclusion `cubicIncl N` is injective. -/
theorem cubicIncl_injective (N : ℕ) : Function.Injective (cubicIncl N) :=
  TwistedMonoidAlgebra.mapStarAlgHom_injective
    (cubicFactor_cubicSnocHom N) (cubicSnocHom_injective N)

/-- The coordinate inclusion maps `cubicFixed N` into `cubicFixed (N + 1)`. -/
theorem cubicIncl_mem_cubicFixed (N : ℕ) {x : CubicTorus N} (hx : x ∈ cubicFixed N) :
    cubicIncl N x ∈ cubicFixed (N + 1) := by
  rw [mem_cubicFixed, ← cubicIncl_cubicInversion, mem_cubicFixed.mp hx]

/-- `cubicIncl N x` lies in `cubicFixed (N + 1)` if and only if `x` lies in `cubicFixed N`. -/
theorem cubicIncl_mem_cubicFixed_iff (N : ℕ) {x : CubicTorus N} :
    cubicIncl N x ∈ cubicFixed (N + 1) ↔ x ∈ cubicFixed N := by
  refine ⟨fun h ↦ ?_, cubicIncl_mem_cubicFixed N⟩
  rw [mem_cubicFixed] at h ⊢
  rw [← cubicIncl_cubicInversion] at h
  exact cubicIncl_injective N h

/-- The restricted coordinate `⋆`-algebra inclusion `cubicFixed N →⋆ₐ[ℂ] cubicFixed (N + 1)`. -/
noncomputable def cubicFixedIncl (N : ℕ) : cubicFixed N →⋆ₐ[ℂ] cubicFixed (N + 1) :=
  ((cubicIncl N).comp (cubicFixed N).subtype).codRestrict (cubicFixed (N + 1)) fun x ↦
    cubicIncl_mem_cubicFixed N x.2

/-- Coercing `cubicFixedIncl` to `CubicTorus (N + 1)` recovers `cubicIncl`. -/
@[simp]
theorem coe_cubicFixedIncl (N : ℕ) (x : cubicFixed N) :
    (cubicFixedIncl N x : CubicTorus (N + 1)) = cubicIncl N x := (rfl)

/-- The restricted coordinate inclusion `cubicFixedIncl N` is injective. -/
theorem cubicFixedIncl_injective (N : ℕ) : Function.Injective (cubicFixedIncl N) := by
  intro x y hxy
  apply Subtype.ext
  exact cubicIncl_injective N (congrArg Subtype.val hxy)

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
    exact congrArg ((Real.sqrt 3 : ℂ) • ·) (cubicIncl_cubicProjection n i).symm
  exact AlgHom.congr_fun hhom x

/-- Multiplying an included element on the right by the last Jones projection scales its scalar
trace by `3⁻¹`: both `U_last` and `U_last ^ 2` shift the last coordinate away from `0`. -/
theorem scalarTrace_cubicIncl_mul_cubicProjection_last (N : ℕ) (x : CubicTorus N) :
    TwistedMonoidAlgebra.scalarTrace (cubicFactor (N + 1))
        (cubicIncl N x * cubicProjection (N + 1) (Fin.last N)) =
      (3 : ℂ)⁻¹ * TwistedMonoidAlgebra.scalarTrace (cubicFactor N) x := by
  have hlin :
      (TwistedMonoidAlgebra.scalarTrace (cubicFactor (N + 1))).comp
          ((LinearMap.mulRight ℂ (cubicProjection (N + 1) (Fin.last N))).comp
            (cubicIncl N).toAlgHom.toLinearMap) =
        (3 : ℂ)⁻¹ • TwistedMonoidAlgebra.scalarTrace (cubicFactor N) := by
    refine (TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)).ext
      fun a ↦ ?_
    have hne1 :
        Multiplicative.ofAdd (Fin.snoc a.toAdd 0) *
          Multiplicative.ofAdd (Pi.single (Fin.last N) (1 : ZMod 3) : Fin (N + 1) → ZMod 3) ≠
            1 := by
      intro h
      have h0 := congrFun (congrArg Multiplicative.toAdd h) (Fin.last N)
      simp at h0
    have hne2 :
        Multiplicative.ofAdd (Fin.snoc a.toAdd 0) *
          (Multiplicative.ofAdd
            (Pi.single (Fin.last N) (1 : ZMod 3) : Fin (N + 1) → ZMod 3))⁻¹ ≠ 1 := by
      intro h
      have h0 := congrFun (congrArg Multiplicative.toAdd h) (Fin.last N)
      simp at h0
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, AlgHom.toLinearMap_apply,
      StarAlgHom.coe_toAlgHom, LinearMap.smul_apply, smul_eq_mul,
      TwistedMonoidAlgebra.basis_apply, ← weyl_def, cubicIncl_weyl, cubicProjection_def,
      cubicSite_def, weyl_sq, mul_smul_comm, mul_add, mul_one, weyl_mul, map_smul, map_add]
    rw [weyl_def, weyl_def, weyl_def,
      TwistedMonoidAlgebra.scalarTrace_of_ne_one _ hne1,
      TwistedMonoidAlgebra.scalarTrace_of_ne_one _ hne2,
      ← weyl_def, ← cubicIncl_weyl, scalarTrace_cubicIncl]
    simp
  exact LinearMap.congr_fun hlin x

/-- The unnormalized Markov trace on `TemperleyLieb ℂ (√3 : ℂ) m` obtained by pulling back
`(√3) ^ m` times `TwistedMonoidAlgebra.scalarTrace (cubicFactor (m - 1))` along
`cubicFixedHom m`. -/
noncomputable def cubicFixedTrace (m : ℕ) :
    TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →ₗ[ℂ] ℂ :=
  ((Real.sqrt 3 : ℂ) ^ m) •
    (TwistedMonoidAlgebra.scalarTrace (cubicFactor (m - 1)) ∘ₗ
      (cubicFixed (m - 1)).subtype.toAlgHom.toLinearMap ∘ₗ
      (cubicFixedHom m).toAlgHom.toLinearMap)

/-- Evaluation formula for `cubicFixedTrace`. -/
theorem cubicFixedTrace_apply (m : ℕ) (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    cubicFixedTrace m x =
      (Real.sqrt 3 : ℂ) ^ m *
        TwistedMonoidAlgebra.scalarTrace (cubicFactor (m - 1)) (cubicFixedHom m x) := by
  simp [cubicFixedTrace]

/-- **The cubic quantum torus scalar trace defines a Markov trace at `δ = √3`.** -/
theorem isMarkovTrace_cubicFixedTrace :
    IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) cubicFixedTrace where
  map_one m := by simp [cubicFixedTrace_apply]
  map_mul_comm m x y := by
    rw [cubicFixedTrace_apply, cubicFixedTrace_apply, map_mul, map_mul, MulMemClass.coe_mul,
      MulMemClass.coe_mul, TwistedMonoidAlgebra.scalarTrace_mul_comm]
  map_strandIncl n x := by
    calc
      cubicFixedTrace (n + 2) (strandIncl x)
        = (Real.sqrt 3 : ℂ) ^ (n + 2) *
            TwistedMonoidAlgebra.scalarTrace (cubicFactor (n + 1))
              (cubicIncl n ((cubicFixedHom (n + 1) x).1 : CubicTorus n)) := by
            rw [cubicFixedTrace_apply, cubicFixedHom_strandIncl, coe_cubicFixedIncl]
            rfl
      _ = (Real.sqrt 3 : ℂ) ^ (n + 2) *
            TwistedMonoidAlgebra.scalarTrace (cubicFactor n)
              ((cubicFixedHom (n + 1) x).1 : CubicTorus n) := by
            rw [scalarTrace_cubicIncl]
      _ = (Real.sqrt 3 : ℂ) * cubicFixedTrace (n + 1) x := by
            rw [cubicFixedTrace_apply, pow_succ', mul_assoc]
            rfl
  map_strandIncl_mul_e_last n x := by
    have hsqrt : (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 := by
      exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    calc
      cubicFixedTrace (n + 2) (strandIncl x * e (Real.sqrt 3 : ℂ) (Fin.last n))
        = (Real.sqrt 3 : ℂ) ^ (n + 2) * ((Real.sqrt 3 : ℂ) *
            TwistedMonoidAlgebra.scalarTrace (cubicFactor (n + 1))
              (cubicIncl n ((cubicFixedHom (n + 1) x).1 : CubicTorus n) *
                cubicProjection (n + 1) (Fin.last n))) := by
            rw [cubicFixedTrace_apply, map_mul, MulMemClass.coe_mul, cubicFixedHom_strandIncl,
              coe_cubicFixedIncl, coe_cubicFixedHom_e, mul_smul_comm, map_smul, smul_eq_mul]
            rfl
      _ = (Real.sqrt 3 : ℂ) ^ (n + 2) * ((Real.sqrt 3 : ℂ) * ((3 : ℂ)⁻¹ *
            TwistedMonoidAlgebra.scalarTrace (cubicFactor n)
              ((cubicFixedHom (n + 1) x).1 : CubicTorus n))) := by
            rw [scalarTrace_cubicIncl_mul_cubicProjection_last]
      _ = (Real.sqrt 3 : ℂ) ^ (n + 1) *
            (((Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ)) * (3 : ℂ)⁻¹) *
              TwistedMonoidAlgebra.scalarTrace (cubicFactor n)
                ((cubicFixedHom (n + 1) x).1 : CubicTorus n) := by
            rw [pow_succ]
            ring
      _ = cubicFixedTrace (n + 1) x := by
            rw [hsqrt, cubicFixedTrace_apply]
            have h3 : (3 : ℂ) * (3 : ℂ)⁻¹ = 1 := by norm_num
            rw [h3, mul_one]
            rfl

namespace IsMarkovTrace

variable {tr : ∀ n : ℕ, TemperleyLieb ℂ (Real.sqrt 3 : ℂ) n →ₗ[ℂ] ℂ}

/-- Every Markov trace on `TemperleyLieb ℂ (√3 : ℂ)` coincides with `cubicFixedTrace`. -/
theorem eq_cubicFixedTrace (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) :
    tr = cubicFixedTrace :=
  htr.unique isMarkovTrace_cubicFixedTrace

/-- **The Markov trace at `δ = √3` as the cubic quantum torus scalar trace**: for every Markov
trace `tr`, `tr m x = (√3 : ℂ) ^ m * scalarTrace (cubicFactor (m - 1)) (cubicFixedHom m x)`. -/
theorem apply_eq_mul_scalarTrace_cubicFixedHom
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ)
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    tr m x =
      (Real.sqrt 3 : ℂ) ^ m *
        TwistedMonoidAlgebra.scalarTrace (cubicFactor (m - 1)) (cubicFixedHom m x) := by
  rw [htr.eq_cubicFixedTrace, cubicFixedTrace_apply]

/-- **Positivity of the Markov trace at `δ = √3`** (the `m = 6` discrete-series point
`2 cos (π / 6)` of Jones's positivity theorem): `0 ≤ tr m (star x * x)` on every number of
strands. -/
theorem map_star_mul_self_nonneg_sqrt_three
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) {m : ℕ}
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    0 ≤ tr m (star x * x) := by
  have hz := TwistedMonoidAlgebra.scalarTrace_star_mul_self_nonneg (cubicFactor (m - 1))
    (cubicFixedHom m x : CubicTorus (m - 1))
  have hz0 : ((0 : ℝ) : ℂ) ≤
      TwistedMonoidAlgebra.scalarTrace (cubicFactor (m - 1))
        (star (cubicFixedHom m x : CubicTorus (m - 1)) * cubicFixedHom m x) := by
    simpa using hz
  rw [htr.apply_eq_mul_scalarTrace_cubicFixedHom, map_mul, MulMemClass.coe_mul,
    cubicFixedHom_star, StarMemClass.coe_star, Complex.eq_re_of_ofReal_le hz0,
    ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.zero_le_real]
  exact mul_nonneg (by positivity) (Complex.nonneg_iff.mp hz).1

/-- At `δ = √3`, `tr m (star x * x) = 0` if and only if `cubicFixedHom m x = 0`. -/
theorem map_star_mul_self_eq_zero_iff_cubicFixedHom_eq_zero
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) {m : ℕ}
    {x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m} :
    tr m (star x * x) = 0 ↔ cubicFixedHom m x = 0 := by
  have hne : (Real.sqrt 3 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
  rw [htr.apply_eq_mul_scalarTrace_cubicFixedHom, map_mul, MulMemClass.coe_mul,
    cubicFixedHom_star, StarMemClass.coe_star, mul_eq_zero]
  simp [pow_ne_zero m hne]

/-! ### Kernel = trace radical and the Jones quotient equivalence -/

/-- **The trace radical at `δ = √3` is the kernel of `cubicFixedHom`.** -/
theorem traceRadical_eq_ker_cubicFixedHom
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) :
    (tr m).traceRadical (htr.map_mul_comm m) = RingHom.ker (cubicFixedHom m) := by
  have hne : (Real.sqrt 3 : ℂ) ^ m ≠ 0 :=
    pow_ne_zero m (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num)))
  let τ : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →ₗ[ℂ] ℂ := ((Real.sqrt 3 : ℂ) ^ m)⁻¹ • tr m
  have hτ : ∀ x y, τ (x * y) = τ (y * x) := fun x y ↦ by
    simp [τ, htr.map_mul_comm m x y]
  have hrad_eq : (tr m).traceRadical (htr.map_mul_comm m) = τ.traceRadical hτ := by
    ext x
    simp [LinearMap.mem_traceRadical, τ, hne]
  let f : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →⋆ₐ[ℂ] CubicTorus (m - 1) :=
    (cubicFixed (m - 1)).subtype.comp (cubicFixedHom m)
  have hf : ∀ a, TwistedMonoidAlgebra.scalarTracePositiveFunctional (cubicFactor (m - 1)) (f a) =
      τ a := fun a ↦ by
    simp only [TwistedMonoidAlgebra.scalarTracePositiveFunctional_apply, f, StarAlgHom.comp_apply,
      StarSubalgebra.coe_subtype, τ, LinearMap.smul_apply, smul_eq_mul,
      htr.apply_eq_mul_scalarTrace_cubicFixedHom]
    rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  have hker_eq : RingHom.ker f = RingHom.ker (cubicFixedHom m) := by
    ext x
    simp [RingHom.mem_ker, f]
  rw [hrad_eq, ← hker_eq]
  exact LinearMap.traceRadical_eq_ker_of_nullSubmodule_eq_bot τ hτ
    (TwistedMonoidAlgebra.scalarTracePositiveFunctional (cubicFactor (m - 1)))
    (TwistedMonoidAlgebra.nullSubmodule_scalarTracePositiveFunctional (cubicFactor (m - 1)))
    f hf

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
  (Ideal.quotientEquivAlgOfEq ℂ
    ((htr.traceRadical_eq_ker_cubicFixedHom m).trans
      (Ideal.ext (I := RingHom.ker (cubicFixedHom m))
        (J := RingHom.ker (cubicFixedHom m).toAlgHom) fun _ ↦ Iff.rfl))).trans
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
  simp [quotientCubicFixedEquiv, Ideal.quotientEquivAlgOfEq_mk]

/-- At `δ = √3`, the trace radical is a star-closed ideal. -/
theorem isStar_traceRadical_sqrt_three
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) :
    Ideal.IsStar ((tr m).traceRadical (htr.map_mul_comm m)) where
  star_mem {x} hx := by
    rw [htr.traceRadical_eq_ker_cubicFixedHom] at hx ⊢
    simpa [RingHom.mem_ker] using congrArg star (RingHom.mem_ker.mp hx)

/-- `quotientCubicFixedEquiv` intertwines the quotient star structure with the star structure on
`cubicFixed (m - 1)`. -/
@[simp]
theorem quotientCubicFixedEquiv_star
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ)
    [Ideal.IsStar ((tr m).traceRadical (htr.map_mul_comm m))]
    (q : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m ⧸ (tr m).traceRadical (htr.map_mul_comm m)) :
    htr.quotientCubicFixedEquiv m (star q) = star (htr.quotientCubicFixedEquiv m q) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp

/-- `quotientCubicFixedEquiv` intertwines the Temperley–Lieb quotient strand map
`quotientStrandIncl` with `cubicFixedIncl`. -/
theorem quotientCubicFixedEquiv_quotientStrandIncl
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (n : ℕ)
    (q : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) (n + 1) ⧸
      (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) :
    htr.quotientCubicFixedEquiv (n + 2) (htr.quotientStrandIncl n q) =
      cubicFixedIncl n (htr.quotientCubicFixedEquiv (n + 1) q) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [htr.quotientStrandIncl_mk, htr.quotientCubicFixedEquiv_mk,
    htr.quotientCubicFixedEquiv_mk, cubicFixedHom_strandIncl]

/-- `(quotientCubicFixedEquiv m).symm` maps `cubicFixedHom m x` back to the quotient class
of `x`. -/
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

/-- The induced trace on the `m`-strand Temperley–Lieb quotient at `δ = √3` is `(√3 : ℂ) ^ m`
times `TwistedMonoidAlgebra.scalarTrace` under `quotientCubicFixedEquiv`. -/
theorem quotientTrace_eq_mul_scalarTrace_quotientCubicFixedEquiv
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ)
    (q : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m ⧸
      (tr m).traceRadical (htr.map_mul_comm m)) :
    (tr m).quotientTrace (htr.map_mul_comm m) q =
      (Real.sqrt 3 : ℂ) ^ m *
        TwistedMonoidAlgebra.scalarTrace (cubicFactor (m - 1))
          (htr.quotientCubicFixedEquiv m q) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp [htr.apply_eq_mul_scalarTrace_cubicFixedHom]

/-- Transporting `quotientTrace` across `(quotientCubicFixedEquiv m).symm` gives `(√3 : ℂ) ^ m`
times `TwistedMonoidAlgebra.scalarTrace`. -/
@[simp]
theorem quotientTrace_quotientCubicFixedEquiv_symm
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) (x : cubicFixed (m - 1)) :
    (tr m).quotientTrace (htr.map_mul_comm m) ((htr.quotientCubicFixedEquiv m).symm x) =
      (Real.sqrt 3 : ℂ) ^ m * TwistedMonoidAlgebra.scalarTrace (cubicFactor (m - 1)) x := by
  simp [htr.quotientTrace_eq_mul_scalarTrace_quotientCubicFixedEquiv]

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

/-- Specialization of `IsMarkovTrace.apply_eq_mul_scalarTrace_cubicFixedHom` to the spin-model
`markovTrace` at any unit `q : ℂˣ` satisfying `(√3 : ℂ) = -(q + q⁻¹)`. -/
theorem markovTrace_eq_mul_scalarTrace_cubicFixedHom (q : ℂˣ)
    (hq : (Real.sqrt 3 : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ))) {m : ℕ}
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    markovTrace q hq x =
      (Real.sqrt 3 : ℂ) ^ m *
        TwistedMonoidAlgebra.scalarTrace (cubicFactor (m - 1)) (cubicFixedHom m x) :=
  (isMarkovTrace_markovTrace q hq).apply_eq_mul_scalarTrace_cubicFixedHom m x

/-! ### Packaged cubic quantum torus model and five-strand Jones–Wenzl vanishing -/

/-- **The inversion-fixed cubic quantum torus model of `TemperleyLieb ℂ (√3 : ℂ) m`.** For every
Markov trace `tr` at loop value `√3` and every `m : ℕ`, there is a surjective `⋆`-algebra
homomorphism `F : TemperleyLieb ℂ (√3 : ℂ) m →⋆ₐ[ℂ] cubicFixed (m - 1)` sending each generator
`e j` to `(√3 : ℂ) • cubicProjection (m - 1) j`, expressing `tr m` as `(√3 : ℂ) ^ m` times
`TwistedMonoidAlgebra.scalarTrace (cubicFactor (m - 1))`, and having kernel equal to the trace
radical `(tr m).traceRadical`. -/
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
          (Real.sqrt 3 : ℂ) ^ m *
            TwistedMonoidAlgebra.scalarTrace (cubicFactor (m - 1)) (F x)) ∧
      RingHom.ker F = (tr m).traceRadical (htr.map_mul_comm m) :=
  ⟨cubicFixedHom m,
    cubicFixedHom_surjective m,
    coe_cubicFixedHom_e m,
    htr.apply_eq_mul_scalarTrace_cubicFixedHom m,
    (htr.traceRadical_eq_ker_cubicFixedHom m).symm⟩

/-- At `δ = √3`, `cubicFixedHom 5` maps the five-strand Jones–Wenzl projection
`jonesWenzl (√3 : ℂ) 5` to `0`. -/
@[simp]
theorem cubicFixedHom_jonesWenzl_five :
    cubicFixedHom 5 (jonesWenzl (Real.sqrt 3 : ℂ) 5) = 0 := by
  have hsqrt : (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
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
    · simp [qInt_two]
    · simp [hq3]
    · simp [hq4]
    · simp [hq5]
  rw [← RingHom.mem_ker, ← isMarkovTrace_cubicFixedTrace.traceRadical_eq_ker_cubicFixedHom 5,
    isMarkovTrace_cubicFixedTrace.jonesWenzl_mem_traceRadical_iff hunits]
  exact hq6

end TauCeti.TemperleyLieb
