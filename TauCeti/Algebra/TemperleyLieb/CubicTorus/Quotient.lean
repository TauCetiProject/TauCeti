/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.CubicTorus.Hom
public import TauCeti.Algebra.TemperleyLieb.Trace.Radical

/-!
# The Jones quotient at `δ = √3` as the inversion-fixed cubic quantum torus

Building on `cubicFixedHom m : TemperleyLieb ℂ (√3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1)` from
`TauCeti.Algebra.TemperleyLieb.CubicTorus.Hom`, this file constructs coordinate inclusions for the
cubic quantum torus tower, identifies the Markov trace at `δ = √3` with `(√3) ^ m` times
`cubicScalarCoefficient (m - 1)`, proves positivity of the Markov Hermitian form at `δ = √3` (the
`m = 6` discrete-series point `2 cos (π / 6)` of Jones's positivity theorem), and identifies the
`m`-strand Temperley–Lieb trace-radical quotient with `cubicFixed (m - 1)` of complex dimension
`(3 ^ (m - 1) + 1) / 2`. As an immediate consequence, `cubicFixedHom 5` annihilates the five-strand
Jones–Wenzl projection `jonesWenzl (√3 : ℂ) 5`.

## Main definitions

* `TauCeti.TemperleyLieb.cubicTorusIncl`, `TauCeti.TemperleyLieb.cubicFixedIncl`: coordinate
  inclusions extending `Fin N → ZMod 3` by zero.
* `TauCeti.TemperleyLieb.cubicFixedTrace`: the unnormalized Markov trace at `√3` induced by
  `cubicScalarCoefficient`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientCubicFixedEquiv`: the `ℂ`-algebra isomorphism from
  the `m`-strand Temperley–Lieb trace quotient at `√3` to `cubicFixed (m - 1)`.

## Main results

* `TauCeti.TemperleyLieb.cubicTorusIncl_injective`,
  `TauCeti.TemperleyLieb.cubicFixedIncl_injective`, and
  `TauCeti.TemperleyLieb.cubicFixedHom_strandIncl`: injectivity and tower compatibility.
* `TauCeti.TemperleyLieb.isMarkovTrace_cubicFixedTrace`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.apply_eq_mul_cubicScalarCoefficient_cubicFixedHom`, and
  `TauCeti.TemperleyLieb.markovTrace_eq_mul_cubicScalarCoefficient_cubicFixedHom`: the
  Markov-trace formula at `δ = √3`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.map_star_mul_self_nonneg_sqrt_three` and
  `TauCeti.TemperleyLieb.IsMarkovTrace.traceRadical_eq_ker_cubicFixedHom`: positivity and
  identification of the trace radical with `RingHom.ker (cubicFixedHom m)`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientCubicFixedEquiv_quotientStrandIncl`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.quotientTrace_eq_mul_cubicScalarCoefficient`, and
  `TauCeti.TemperleyLieb.IsMarkovTrace.finrank_quotient_traceRadical_sqrt_three`: tower, trace,
  and dimension properties of the Jones quotient equivalence.
* `TauCeti.TemperleyLieb.exists_cubicFixedModel` and
  `TauCeti.TemperleyLieb.cubicFixedHom_jonesWenzl_five`: packaged existence theorem and vanishing
  of the five-strand Jones–Wenzl projection.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), 103–111, p. 107.
* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989.
* C. Galindo and E. C. Rowell, *Braid representations from unitary braided vector spaces*,
  J. Math. Phys. 55 (2014), 061702.
* E. C. Rowell and H. Wenzl, *SO(N)_2 braid group representations are Gaussian*, Quantum Topology
  8 (2017), 1–33.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4.
-/

public section

open scoped ComplexOrder

namespace TauCeti.TemperleyLieb

/-! ### Coordinate inclusions and the Markov trace identity -/

/-- Extending exponent vectors by `0` in the last coordinate preserves `chainForm`. -/
@[simp]
theorem chainForm_snoc_zero (N : ℕ) (a b : Fin N → ZMod 3) :
    chainForm (N + 1) (Fin.snoc a 0) (Fin.snoc b 0) = chainForm N a b := by
  rw [chainForm_def, chainForm_def, Fin.sum_univ_castSucc]
  have hlast : ∑ j : Fin (N + 1),
      (if ((Fin.last N : Fin (N + 1)) : ℕ) + 1 = j then
        Fin.snoc (α := fun _ ↦ ZMod 3) a 0 (Fin.last N) *
          Fin.snoc (α := fun _ ↦ ZMod 3) b 0 j -
        Fin.snoc (α := fun _ ↦ ZMod 3) b 0 (Fin.last N) *
          Fin.snoc (α := fun _ ↦ ZMod 3) a 0 j else 0) = 0 :=
    Finset.sum_eq_zero fun _ _ ↦ by simp [Fin.snoc_last]
  rw [hlast, add_zero]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_last, mul_zero, sub_self, ite_self, add_zero]
  exact Finset.sum_congr rfl fun j _ ↦ by simp [Fin.snoc_castSucc]

/-- Extending exponent vectors by `0` in the last coordinate preserves `cubicFactor`. -/
@[simp]
theorem cubicFactor_snoc_zero (N : ℕ) (a b : Multiplicative (Fin N → ZMod 3)) :
    cubicFactor (N + 1) (Multiplicative.ofAdd (Fin.snoc a.toAdd 0))
        (Multiplicative.ofAdd (Fin.snoc b.toAdd 0)) =
      cubicFactor N a b := by
  simp [cubicFactor_def, chainForm_snoc_zero]

/-- The coordinate inclusion `CubicTorus N →ₐ[ℂ] CubicTorus (N + 1)` induced by extending
`Fin N → ZMod 3` by `0` in the last coordinate. -/
noncomputable def cubicTorusIncl (N : ℕ) : CubicTorus N →ₐ[ℂ] CubicTorus (N + 1) :=
  TwistedMonoidAlgebra.lift
    (fun a ↦ weyl (N + 1) (Multiplicative.ofAdd (Fin.snoc a.toAdd 0)))
    (by
      have h0 : Fin.snoc (α := fun _ ↦ ZMod 3) (0 : Fin N → ZMod 3) 0 = 0 := by
        ext k; refine Fin.lastCases (by simp) (fun k ↦ by simp) k
      simp [h0])
    (fun g h ↦ by
      rw [weyl_mul, cubicFactor_snoc_zero]
      congr 2
      apply Multiplicative.toAdd.injective
      ext k
      refine Fin.lastCases (by simp) (fun k ↦ by simp) k)

/-- `cubicTorusIncl` acts on Weyl basis elements by extending the exponent by `0`. -/
@[simp]
theorem cubicTorusIncl_weyl (N : ℕ) (a : Multiplicative (Fin N → ZMod 3)) :
    cubicTorusIncl N (weyl N a) =
      weyl (N + 1) (Multiplicative.ofAdd (Fin.snoc a.toAdd 0)) := by
  rw [cubicTorusIncl, weyl_def]
  exact TwistedMonoidAlgebra.lift_of _ _ _ a

/-- `cubicTorusIncl` sends the `j`-th site unitary to `cubicSite (N + 1) j.castSucc`. -/
@[simp]
theorem cubicTorusIncl_cubicSite (N : ℕ) (j : Fin N) :
    cubicTorusIncl N (cubicSite N j) = cubicSite (N + 1) j.castSucc := by
  have hsingle : Fin.snoc (α := fun _ ↦ ZMod 3) (Pi.single j 1) 0 = Pi.single j.castSucc 1 := by
    ext k
    refine Fin.lastCases ?_ (fun k ↦ ?_) k
    · simp [(Fin.castSucc_lt_last j).ne']
    · simp [Pi.single_apply]
  simp [cubicSite_def, hsingle]

/-- `cubicTorusIncl` sends the `j`-th cubic projection to `cubicProjection (N + 1) j.castSucc`. -/
@[simp]
theorem cubicTorusIncl_cubicProjection (N : ℕ) (j : Fin N) :
    cubicTorusIncl N (cubicProjection N j) = cubicProjection (N + 1) j.castSucc := by
  simp [cubicProjection_def]

/-- `cubicTorusIncl` commutes with `cubicInversion`. -/
@[simp]
theorem cubicTorusIncl_cubicInversion (N : ℕ) (x : CubicTorus N) :
    cubicTorusIncl N (cubicInversion N x) = cubicInversion (N + 1) (cubicTorusIncl N x) := by
  have hhom : (cubicTorusIncl N).comp (cubicInversion N) =
      (cubicInversion (N + 1)).comp (cubicTorusIncl N) := by
    apply TwistedMonoidAlgebra.algHom_ext
    intro a
    simp only [AlgHom.comp_apply, ← weyl_def, cubicInversion_weyl, cubicTorusIncl_weyl]
    congr 1
    apply Multiplicative.toAdd.injective
    ext k
    refine Fin.lastCases (by simp) (fun k ↦ by simp) k
  exact AlgHom.congr_fun hhom x

/-- `cubicTorusIncl` intertwines `cubicAdjoint` across adjacent dimensions. -/
@[simp]
theorem cubicTorusIncl_cubicAdjoint (N : ℕ) (x : CubicTorus N) :
    cubicTorusIncl N (cubicAdjoint N x) = cubicAdjoint (N + 1) (cubicTorusIncl N x) := by
  let b := TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)
  have hx := (b.sum_repr x).symm
  conv_lhs => rw [hx]
  conv_rhs => rw [hx]
  rw [map_sum, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  simp only [b, TwistedMonoidAlgebra.basis_apply, ← weyl_def, map_smul, map_smulₛₗ,
    cubicAdjoint_weyl, cubicTorusIncl_weyl]
  congr 2
  apply Multiplicative.toAdd.injective
  ext k
  refine Fin.lastCases (by simp) (fun k ↦ by simp) k

/-- Coordinate inclusion preserves the scalar-part trace `cubicScalarCoefficient`. -/
@[simp]
theorem cubicScalarCoefficient_cubicTorusIncl (N : ℕ) (x : CubicTorus N) :
    cubicScalarCoefficient (N + 1) (cubicTorusIncl N x) = cubicScalarCoefficient N x := by
  let b := TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)
  have hx := (b.sum_repr x).symm
  conv_lhs => rw [hx]
  conv_rhs => rw [hx]
  rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun g _ ↦ ?_
  simp only [b, TwistedMonoidAlgebra.basis_apply, ← weyl_def, map_smul, cubicTorusIncl_weyl,
    cubicScalarCoefficient_weyl]
  have hiff : Multiplicative.ofAdd (Fin.snoc (α := fun _ ↦ ZMod 3) g.toAdd 0) = 1 ↔ g = 1 := by
    constructor
    · intro h
      apply Multiplicative.toAdd.injective
      ext k
      have hk := congrFun (congrArg Multiplicative.toAdd h) k.castSucc
      simpa [Fin.snoc_castSucc] using hk
    · rintro rfl
      apply Multiplicative.toAdd.injective
      ext k
      refine Fin.lastCases (by simp) (fun k ↦ by simp) k
  simp [hiff]

/-- The coordinate inclusion `cubicTorusIncl N` is injective. -/
theorem cubicTorusIncl_injective (N : ℕ) : Function.Injective (cubicTorusIncl N) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  apply (cubicScalarCoefficient_cubicAdjoint_mul_self_eq_zero_iff N).mp
  rw [← cubicScalarCoefficient_cubicTorusIncl N, map_mul, cubicTorusIncl_cubicAdjoint, ha,
    mul_zero, map_zero]

/-- The coordinate inclusion maps `cubicFixed N` into `cubicFixed (N + 1)`. -/
theorem cubicTorusIncl_mem_cubicFixed (N : ℕ) {x : CubicTorus N} (hx : x ∈ cubicFixed N) :
    cubicTorusIncl N x ∈ cubicFixed (N + 1) := by
  rw [mem_cubicFixed_iff, ← cubicTorusIncl_cubicInversion, mem_cubicFixed_iff.mp hx]

/-- `cubicTorusIncl N x` lies in `cubicFixed (N + 1)` if and only if `x` lies in
`cubicFixed N`. -/
theorem cubicTorusIncl_mem_cubicFixed_iff (N : ℕ) {x : CubicTorus N} :
    cubicTorusIncl N x ∈ cubicFixed (N + 1) ↔ x ∈ cubicFixed N := by
  refine ⟨fun h ↦ ?_, cubicTorusIncl_mem_cubicFixed N⟩
  rw [mem_cubicFixed_iff] at h ⊢
  rw [← cubicTorusIncl_cubicInversion] at h
  exact cubicTorusIncl_injective N h

/-- The restricted coordinate inclusion `cubicFixed N →ₐ[ℂ] cubicFixed (N + 1)`. -/
noncomputable def cubicFixedIncl (N : ℕ) : cubicFixed N →ₐ[ℂ] cubicFixed (N + 1) :=
  ((cubicTorusIncl N).comp (cubicFixed N).val).codRestrict (cubicFixed (N + 1)) fun x ↦
    cubicTorusIncl_mem_cubicFixed N x.2

/-- Coercing `cubicFixedIncl` to the ambient cubic quantum torus recovers `cubicTorusIncl`. -/
@[simp]
theorem coe_cubicFixedIncl (N : ℕ) (x : cubicFixed N) :
    (cubicFixedIncl N x : CubicTorus (N + 1)) = cubicTorusIncl N x :=
  (rfl)

/-- `cubicFixedIncl` intertwines `cubicFixedAdjoint` across adjacent dimensions. -/
@[simp]
theorem cubicFixedIncl_cubicFixedAdjoint (N : ℕ) (x : cubicFixed N) :
    cubicFixedIncl N (cubicFixedAdjoint N x) =
      cubicFixedAdjoint (N + 1) (cubicFixedIncl N x) :=
  Subtype.ext (by simp)

/-- The restricted coordinate inclusion `cubicFixedIncl N` is injective. -/
theorem cubicFixedIncl_injective (N : ℕ) : Function.Injective (cubicFixedIncl N) := by
  intro x y hxy
  apply Subtype.ext
  exact cubicTorusIncl_injective N (congrArg Subtype.val hxy)

/-- `cubicFixedHom` intertwines Temperley–Lieb `strandIncl` with `cubicFixedIncl`. -/
theorem cubicFixedHom_strandIncl (n : ℕ)
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) (n + 1)) :
    cubicFixedHom (n + 2) (strandIncl x) =
      cubicFixedIncl n (cubicFixedHom (n + 1) x) := by
  have hhom : (cubicFixedHom (n + 2)).comp strandIncl =
      (cubicFixedIncl n).comp (cubicFixedHom (n + 1)) := by
    apply TemperleyLieb.hom_ext
    intro i
    apply Subtype.ext
    simp only [AlgHom.comp_apply, strandIncl_e, coe_cubicFixedIncl]
    rw [coe_cubicFixedHom_e (n + 2) i.castSucc, coe_cubicFixedHom_e (n + 1) i, map_smul]
    congr 1
    exact (cubicTorusIncl_cubicProjection n i).symm
  exact AlgHom.congr_fun hhom x

/-- Helper: multiplying an included element by a Weyl element supported on a nonzero multiple of
the last coordinate has zero scalar part. -/
private theorem cubicScalarCoefficient_cubicTorusIncl_mul_weyl_last_eq_zero (N : ℕ)
    (a : CubicTorus N) {c : ZMod 3} (hc : c ≠ 0) :
    cubicScalarCoefficient (N + 1)
        (cubicTorusIncl N a * weyl (N + 1) (Multiplicative.ofAdd (Pi.single (Fin.last N) c))) =
      0 := by
  let b := TwistedMonoidAlgebra.basis ℂ (Multiplicative (Fin N → ZMod 3)) (cubicFactor N)
  have ha := (b.sum_repr a).symm
  conv_lhs => rw [ha]
  rw [map_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_eq_zero fun g _ ↦ ?_
  simp only [b, TwistedMonoidAlgebra.basis_apply, ← weyl_def, map_smul, cubicTorusIncl_weyl,
    smul_mul_assoc, weyl_mul, smul_smul, cubicScalarCoefficient_weyl]
  have hne : Multiplicative.ofAdd (Fin.snoc (α := fun _ ↦ ZMod 3) g.toAdd 0) *
      Multiplicative.ofAdd (Pi.single (M := fun _ ↦ ZMod 3) (Fin.last N) c) ≠ 1 := by
    intro h
    have hlast := congrFun (congrArg Multiplicative.toAdd h) (Fin.last N)
    exact hc (by simpa using hlast)
  simp [hne]

/-- Multiplying an included cubic quantum torus element on the right by the last cubic projection
scales its scalar part by `3⁻¹`: the `U_N` and `U_N²` terms have nonzero last coordinate and
therefore zero scalar part. -/
theorem cubicScalarCoefficient_cubicTorusIncl_mul_cubicProjection_last (N : ℕ)
    (a : CubicTorus N) :
    cubicScalarCoefficient (N + 1)
        (cubicTorusIncl N a * cubicProjection (N + 1) (Fin.last N)) =
      (3 : ℂ)⁻¹ * cubicScalarCoefficient N a := by
  have h1 : cubicScalarCoefficient (N + 1)
      (cubicTorusIncl N a * cubicSite (N + 1) (Fin.last N)) = 0 := by
    rw [cubicSite_def]
    exact cubicScalarCoefficient_cubicTorusIncl_mul_weyl_last_eq_zero N a (by decide)
  have h2 : cubicScalarCoefficient (N + 1)
      (cubicTorusIncl N a * cubicSite (N + 1) (Fin.last N) ^ 2) = 0 := by
    have hneg : -(Pi.single (M := fun _ ↦ ZMod 3) (Fin.last N) 1) =
        Pi.single (M := fun _ ↦ ZMod 3) (Fin.last N) (-1) := by
      ext k
      by_cases hk : k = Fin.last N <;> simp [hk]
    rw [cubicSite_sq, hneg]
    exact cubicScalarCoefficient_cubicTorusIncl_mul_weyl_last_eq_zero N a (by decide)
  rw [cubicProjection_def, mul_smul_comm, map_smul, mul_add, mul_add, mul_one, map_add, map_add,
    cubicScalarCoefficient_cubicTorusIncl, h1, h2]
  simp

/-- The unnormalized Markov trace on `TemperleyLieb ℂ (√3 : ℂ) m` obtained by pulling back
`(√3) ^ m` times `cubicScalarCoefficient (m - 1)` along `cubicFixedHom m`. -/
noncomputable def cubicFixedTrace (m : ℕ) :
    TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →ₗ[ℂ] ℂ :=
  ((Real.sqrt 3 : ℂ) ^ m) •
    (cubicScalarCoefficient (m - 1) ∘ₗ
      (cubicFixed (m - 1)).val.toLinearMap ∘ₗ (cubicFixedHom m).toLinearMap)

/-- Evaluation formula for `cubicFixedTrace`. -/
theorem cubicFixedTrace_apply (m : ℕ) (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    cubicFixedTrace m x =
      (Real.sqrt 3 : ℂ) ^ m * cubicScalarCoefficient (m - 1) (cubicFixedHom m x) := by
  simp [cubicFixedTrace]

/-- **The cubic quantum torus scalar trace defines a Markov trace at `δ = √3`.** -/
theorem isMarkovTrace_cubicFixedTrace :
    IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) cubicFixedTrace where
  map_one m := by simp [cubicFixedTrace_apply]
  map_mul_comm m x y := by
    simp only [cubicFixedTrace_apply, map_mul, Subalgebra.coe_mul,
      cubicScalarCoefficient_mul_comm]
  map_strandIncl n x := by
    let y : CubicTorus n := (cubicFixedHom (n + 1) x).val
    calc
      cubicFixedTrace (n + 2) (strandIncl x)
          = (Real.sqrt 3 : ℂ) ^ (n + 2) *
              cubicScalarCoefficient (n + 1) (cubicTorusIncl n y) := by
            rw [cubicFixedTrace_apply, cubicFixedHom_strandIncl, coe_cubicFixedIncl]
            rfl
      _ = (Real.sqrt 3 : ℂ) ^ (n + 2) * cubicScalarCoefficient n y := by
            rw [cubicScalarCoefficient_cubicTorusIncl]
      _ = (Real.sqrt 3 : ℂ) * ((Real.sqrt 3 : ℂ) ^ (n + 1) * cubicScalarCoefficient n y) := by
            rw [pow_succ']
            ring
      _ = (Real.sqrt 3 : ℂ) * cubicFixedTrace (n + 1) x := by
            rw [cubicFixedTrace_apply]
            rfl
  map_strandIncl_mul_e_last n x := by
    let y : CubicTorus n := (cubicFixedHom (n + 1) x).val
    have hsqrt : (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ) = 3 := by
      exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    calc
      cubicFixedTrace (n + 2) (strandIncl x * e (Real.sqrt 3 : ℂ) (Fin.last n))
          = (Real.sqrt 3 : ℂ) ^ (n + 2) *
              cubicScalarCoefficient (n + 1)
                (cubicTorusIncl n y *
                  ((Real.sqrt 3 : ℂ) • cubicProjection (n + 1) (Fin.last n))) := by
            rw [cubicFixedTrace_apply, map_mul, Subalgebra.coe_mul,
              cubicFixedHom_strandIncl, coe_cubicFixedIncl, coe_cubicFixedHom_e]
            rfl
      _ = (Real.sqrt 3 : ℂ) ^ (n + 2) *
            ((Real.sqrt 3 : ℂ) * ((3 : ℂ)⁻¹ * cubicScalarCoefficient n y)) := by
            rw [mul_smul_comm, map_smul, smul_eq_mul,
              cubicScalarCoefficient_cubicTorusIncl_mul_cubicProjection_last]
      _ = (Real.sqrt 3 : ℂ) ^ (n + 1) *
            (((Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ)) * (3 : ℂ)⁻¹) *
            cubicScalarCoefficient n y := by
            rw [pow_succ]
            ring
      _ = (Real.sqrt 3 : ℂ) ^ (n + 1) * cubicScalarCoefficient n y := by
            rw [hsqrt]
            norm_num
      _ = cubicFixedTrace (n + 1) x := by
            rw [cubicFixedTrace_apply]
            rfl

namespace IsMarkovTrace

variable {tr : ∀ n : ℕ, TemperleyLieb ℂ (Real.sqrt 3 : ℂ) n →ₗ[ℂ] ℂ}

/-- Every Markov trace on `TemperleyLieb ℂ (√3 : ℂ)` coincides with `cubicFixedTrace`. -/
theorem eq_cubicFixedTrace (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) :
    tr = cubicFixedTrace :=
  htr.unique isMarkovTrace_cubicFixedTrace

/-- **The Markov trace at `δ = √3` as the cubic quantum torus scalar trace**: for every Markov
trace `tr`, `tr m x = (√3 : ℂ) ^ m * cubicScalarCoefficient (m - 1) (cubicFixedHom m x)`. -/
theorem apply_eq_mul_cubicScalarCoefficient_cubicFixedHom
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ)
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    tr m x =
      (Real.sqrt 3 : ℂ) ^ m * cubicScalarCoefficient (m - 1) (cubicFixedHom m x) := by
  rw [htr.eq_cubicFixedTrace, cubicFixedTrace_apply]

/-- **Positivity of the Markov trace at `δ = √3`** (the `m = 6` discrete-series point
`2 cos (π / 6)` of Jones's positivity theorem): `0 ≤ tr m (star x * x)` on every number of
strands. -/
theorem map_star_mul_self_nonneg_sqrt_three
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) {m : ℕ}
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    0 ≤ tr m (star x * x) := by
  have hz := cubicScalarCoefficient_cubicAdjoint_mul_self_nonneg (m - 1) (cubicFixedHom m x)
  have hz0 : ((0 : ℝ) : ℂ) ≤
      cubicScalarCoefficient (m - 1)
        (cubicAdjoint (m - 1) (cubicFixedHom m x) * cubicFixedHom m x) := by
    simpa using hz
  rw [htr.apply_eq_mul_cubicScalarCoefficient_cubicFixedHom, map_mul, Subalgebra.coe_mul,
    coe_cubicFixedHom_star, Complex.eq_re_of_ofReal_le hz0,
    ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.zero_le_real]
  exact mul_nonneg (by positivity) (Complex.nonneg_iff.mp hz).1

/-- At `δ = √3`, `tr m (star x * x) = 0` if and only if `cubicFixedHom m x = 0`. -/
theorem map_star_mul_self_eq_zero_iff_cubicFixedHom_eq_zero
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) {m : ℕ}
    {x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m} :
    tr m (star x * x) = 0 ↔ cubicFixedHom m x = 0 := by
  have hne : (Real.sqrt 3 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
  rw [htr.apply_eq_mul_cubicScalarCoefficient_cubicFixedHom, map_mul, Subalgebra.coe_mul,
    coe_cubicFixedHom_star, mul_eq_zero, or_iff_right (pow_ne_zero m hne),
    cubicScalarCoefficient_cubicAdjoint_mul_self_eq_zero_iff, ZeroMemClass.coe_eq_zero]

/-! ### Kernel = trace radical and the Jones quotient equivalence -/

/-- **The trace radical at `δ = √3` is the kernel of `cubicFixedHom`.** -/
theorem traceRadical_eq_ker_cubicFixedHom
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ) :
    (tr m).traceRadical (htr.map_mul_comm m) = RingHom.ker (cubicFixedHom m) := by
  have hne : (Real.sqrt 3 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
  ext x
  rw [LinearMap.mem_traceRadical, RingHom.mem_ker]
  simp only [htr.apply_eq_mul_cubicScalarCoefficient_cubicFixedHom, map_mul, Subalgebra.coe_mul,
    mul_eq_zero, pow_ne_zero m hne, false_or]
  exact (cubicFixedHom_surjective m).forall.symm.trans
    forall_cubicFixed_scalarCoefficient_mul_eq_zero_iff

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
`quotientStrandIncl` with the inversion-fixed coordinate inclusion `cubicFixedIncl`. -/
theorem quotientCubicFixedEquiv_quotientStrandIncl
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (n : ℕ)
    (q : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) (n + 1) ⧸
      (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) :
    htr.quotientCubicFixedEquiv (n + 2) (htr.quotientStrandIncl n q) =
      cubicFixedIncl n (htr.quotientCubicFixedEquiv (n + 1) q) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [htr.quotientStrandIncl_mk, htr.quotientCubicFixedEquiv_mk (n + 2),
    htr.quotientCubicFixedEquiv_mk (n + 1), cubicFixedHom_strandIncl]

/-- `(quotientCubicFixedEquiv m).symm` maps `cubicFixedHom m x` back to the quotient class
of `x`. -/
@[simp]
theorem quotientCubicFixedEquiv_symm_cubicFixedHom
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ)
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    (htr.quotientCubicFixedEquiv m).symm (cubicFixedHom m x) =
      Ideal.Quotient.mk ((tr m).traceRadical (htr.map_mul_comm m)) x :=
  (htr.quotientCubicFixedEquiv m).injective (by simp)

/-- `(quotientCubicFixedEquiv _).symm` intertwines `cubicFixedIncl` with
`quotientStrandIncl`. -/
theorem quotientCubicFixedEquiv_symm_cubicFixedIncl
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (n : ℕ)
    (y : cubicFixed n) :
    (htr.quotientCubicFixedEquiv (n + 2)).symm (cubicFixedIncl n y) =
      htr.quotientStrandIncl n ((htr.quotientCubicFixedEquiv (n + 1)).symm y) :=
  (htr.quotientCubicFixedEquiv (n + 2)).injective (by
    rw [AlgEquiv.apply_symm_apply, htr.quotientCubicFixedEquiv_quotientStrandIncl,
      AlgEquiv.apply_symm_apply])

/-- The induced trace on the `m`-strand Temperley–Lieb quotient at `δ = √3` is `(√3 : ℂ) ^ m` times
`cubicScalarCoefficient (m - 1)` under `quotientCubicFixedEquiv`. -/
theorem quotientTrace_eq_mul_cubicScalarCoefficient
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
  simp [htr.quotientTrace_eq_mul_cubicScalarCoefficient]

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

/-! ### Packaged cubic quantum torus model and five-strand Jones–Wenzl vanishing -/

/-- **The cubic quantum torus model of `TemperleyLieb ℂ (√3 : ℂ) m`.** For every Markov trace `tr`
at loop value `√3` and every `m : ℕ`, there is a surjective `ℂ`-algebra homomorphism
`F : TemperleyLieb ℂ (√3 : ℂ) m →ₐ[ℂ] cubicFixed (m - 1)` sending each generator `e j` to
`(√3 : ℂ) • cubicProjection (m - 1) j`, intertwining `star` with `cubicAdjoint (m - 1)`,
expressing `tr m` as `(√3 : ℂ) ^ m` times `cubicScalarCoefficient (m - 1)`, and having kernel equal
to the trace radical `(tr m).traceRadical`. -/
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
          (Real.sqrt 3 : ℂ) ^ m * cubicScalarCoefficient (m - 1) (F x)) ∧
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
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hsqrt_ne : (Real.sqrt 3 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
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
    · simp [qInt_two, hsqrt_ne]
    · simp [hq3]
    · simp [hq4, hsqrt_ne]
    · simp [hq5]
  rw [← RingHom.mem_ker, ← isMarkovTrace_cubicFixedTrace.traceRadical_eq_ker_cubicFixedHom 5,
    isMarkovTrace_cubicFixedTrace.jonesWenzl_mem_traceRadical_iff hunits]
  exact hq6

end TauCeti.TemperleyLieb
