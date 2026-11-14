/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.EvenClifford.Basic
public import TauCeti.Algebra.TemperleyLieb.Trace.Radical
-- Private: functoriality of Clifford involutions and even subalgebras, grade-involution parity
-- criteria, and `Fin.snoc` linear equivalences are used only inside proofs and internal
-- constructions.
import TauCeti.LinearAlgebra.CliffordAlgebra.Functoriality
import TauCeti.LinearAlgebra.CliffordAlgebra.Grading
import TauCeti.LinearAlgebra.Pi

/-!
# The Jones quotient at `δ = √2` as an even Clifford algebra

Building on the surjective star-compatible comparison homomorphism
`F_m = evenCliffordHom m : TemperleyLieb ℂ (√2 : ℂ) m →ₐ[ℂ] EvenClifford m` from
`TauCeti.Algebra.TemperleyLieb.EvenClifford.Basic`, this file equips the even complex Clifford
tower `Cl_m⁰` with coordinate inclusions, identifies the Markov trace at `δ = √2` with `(√2) ^ m`
times `s_m = CliffordAlgebra.scalarTrace (cliffordForm m)`, establishes positivity of the Markov
Hermitian form at `δ = √2`, and identifies the `m`-strand Temperley–Lieb trace-radical quotient
(the Jones quotient at index `δ² = 2`) with `EvenClifford m`.

* **Coordinate inclusions and Markov trace identity**: extending `ℂ^m → ℂ^(m + 1)` by zero induces
  injective algebra maps `cliffordIncl m` and `evenCliffordIncl m` that intertwine `strandIncl` and
  `cliffordAdjoint`, preserve `CliffordAlgebra.scalarTrace`, and send
  `cliffordIncl (n + 1) a * cliffordProjection (n + 2) (Fin.last n)` to
  `2⁻¹ • cliffordIncl (n + 1) a` plus a term ending in the orthogonal generator `c_{n + 1}`, whose
  scalar part vanishes by `CliffordAlgebra.scalarTrace_map_mul_ι_eq_zero`. Hence
  `evenCliffordTrace m x = (√2) ^ m * s_m (F_m x)` satisfies `IsMarkovTrace`, and Markov uniqueness
  identifies every Markov trace at `√2` with it.
* **Positivity and the trace radical**: Parseval positivity and faithfulness of `s_m (a† * a)` show
  that at `δ = √2` the Markov Hermitian form `tr m (star x * x)` is positive semidefinite (the
  `m = 4` discrete-series point `2 cos (π / 4)` of Jones's positivity theorem), and nondegeneracy of
  the scalar-trace pairing on `EvenClifford m` identifies both the Hermitian null space and
  `(tr m).traceRadical` with `RingHom.ker (evenCliffordHom m)`.
* **Jones quotient equivalence and three-strand Jones–Wenzl vanishing**: passing to the quotient
  yields `IsMarkovTrace.quotientEvenCliffordEquiv` of complex dimension `2 ^ (m - 1)` intertwining
  `quotientStrandIncl` and `quotientTrace`. In particular, at three strands (`dim TL_3 = 5`,
  `dim Cl_3⁰ = 4`), `evenCliffordHom 3` annihilates the negligible Jones–Wenzl projection
  `jonesWenzl (√2 : ℂ) 3`.

## Main definitions

* `TauCeti.TemperleyLieb.cliffordExtendIsometry`, `TauCeti.TemperleyLieb.cliffordIncl`, and
  `TauCeti.TemperleyLieb.evenCliffordIncl`: the coordinate inclusions extending `Fin m → ℂ` by zero.
* `TauCeti.TemperleyLieb.evenCliffordTrace`: the unnormalized Markov trace at `√2` induced by
  `CliffordAlgebra.scalarTrace`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientEvenCliffordEquiv`: the algebra isomorphism between
  the `m`-strand Temperley–Lieb trace quotient at `√2` and `EvenClifford m`.

## Main results

* `TauCeti.TemperleyLieb.cliffordIncl_injective`,
  `TauCeti.TemperleyLieb.evenCliffordIncl_injective`, and
  `TauCeti.TemperleyLieb.evenCliffordHom_strandIncl`: injectivity and tower compatibility of the
  coordinate inclusions.
* `TauCeti.TemperleyLieb.isMarkovTrace_evenCliffordTrace`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.apply_eq_mul_scalarTrace_evenCliffordHom`, and
  `TauCeti.TemperleyLieb.markovTrace_eq_mul_scalarTrace_evenCliffordHom`: the Markov-trace formula
  `tr m x = (√2) ^ m * scalarTrace (cliffordForm m) (evenCliffordHom m x)`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.map_star_mul_self_nonneg_sqrt_two` and
  `TauCeti.TemperleyLieb.IsMarkovTrace.traceRadical_eq_ker_evenCliffordHom`: positivity of the
  Markov Hermitian form at `δ = √2` and identification of the trace radical with
  `RingHom.ker (evenCliffordHom m)`.
* `TauCeti.TemperleyLieb.IsMarkovTrace.quotientEvenCliffordEquiv_quotientStrandIncl`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.quotientTrace_eq_mul_scalarTrace_quotientEvenCliffordEquiv`,
  and `TauCeti.TemperleyLieb.IsMarkovTrace.finrank_quotient_traceRadical_sqrt_two`: tower, trace,
  and dimension (`2 ^ (m - 1)`) properties of the Jones quotient equivalence.
* `TauCeti.TemperleyLieb.exists_evenCliffordModel` and
  `TauCeti.TemperleyLieb.evenCliffordHom_jonesWenzl_three`: packaged existence theorem for the even
  Clifford model at `δ = √2` and vanishing of the three-strand Jones–Wenzl projection.

## References

* V. F. R. Jones, *Index for subfactors*, Invent. Math. 72 (1983), 1–25.
* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), 103–111.
* F. M. Goodman, P. de la Harpe and V. F. R. Jones, *Coxeter graphs and towers of algebras*,
  MSRI Publications 14, Springer, 1989.
* K. Iohara, G. I. Lehrer and R. B. Zhang, *The Jones quotients of the Temperley–Lieb algebras*,
  arXiv:1702.08128, §5.3, Theorem 5.4 and §5.4, Proposition 5.5.
* K. Iohara, G. I. Lehrer and R. B. Zhang, *Temperley–Lieb at roots of unity, a fusion category and
  the Jones quotient*, Math. Res. Lett. 26 (2019), no. 1, 121–158.
* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4.
-/

public section

open scoped ComplexOrder

namespace TauCeti.TemperleyLieb

/-! ### Coordinate inclusions and the Markov trace identity -/

/-- Extending a coordinate vector `v : Fin m → ℂ` by `0` in the last coordinate gives a quadratic
isometry `cliffordForm m →qᵢ cliffordForm (m + 1)`. -/
noncomputable def cliffordExtendIsometry (m : ℕ) :
    cliffordForm m →qᵢ cliffordForm (m + 1) where
  toLinearMap :=
    (LinearEquiv.piFinSnoc ℂ fun _ : Fin (m + 1) ↦ ℂ).symm.toLinearMap.comp
      (LinearMap.inl ℂ (Fin m → ℂ) ℂ)
  map_app' v := by
    simp [cliffordForm_apply, Fin.sum_univ_castSucc]

/-- Evaluation of `cliffordExtendIsometry` as `Fin.snoc · 0`. -/
@[simp]
theorem cliffordExtendIsometry_apply (m : ℕ) (v : Fin m → ℂ) :
    cliffordExtendIsometry m v = Fin.snoc v 0 := by
  rw [← QuadraticMap.Isometry.coe_toLinearMap]
  simp [cliffordExtendIsometry]

/-- The algebra inclusion
`CliffordAlgebra (cliffordForm m) →ₐ[ℂ] CliffordAlgebra (cliffordForm (m + 1))` induced by
extending `Fin m → ℂ` by zero. -/
noncomputable def cliffordIncl (m : ℕ) :
    CliffordAlgebra (cliffordForm m) →ₐ[ℂ] CliffordAlgebra (cliffordForm (m + 1)) :=
  CliffordAlgebra.map (cliffordExtendIsometry m)

/-- Unfolding `cliffordIncl` as `CliffordAlgebra.map (cliffordExtendIsometry m)`. -/
theorem cliffordIncl_def (m : ℕ) :
    cliffordIncl m = CliffordAlgebra.map (cliffordExtendIsometry m) :=
  (rfl)

/-- `cliffordIncl` acts on vectors by extending `Fin m → ℂ` by `0` in the last coordinate. -/
@[simp]
theorem cliffordIncl_ι (m : ℕ) (v : Fin m → ℂ) :
    cliffordIncl m (CliffordAlgebra.ι (cliffordForm m) v) =
      CliffordAlgebra.ι (cliffordForm (m + 1)) (Fin.snoc v 0) := by
  simp [cliffordIncl_def]

/-- `cliffordIncl` commutes with the Clifford grade involution. -/
@[simp]
theorem cliffordIncl_involute (m : ℕ) (a : CliffordAlgebra (cliffordForm m)) :
    cliffordIncl m (CliffordAlgebra.involute a) =
      CliffordAlgebra.involute (cliffordIncl m a) :=
  CliffordAlgebra.map_involute (cliffordExtendIsometry m) a

/-- `cliffordIncl` commutes with Clifford reversal. -/
@[simp]
theorem cliffordIncl_reverse (m : ℕ) (a : CliffordAlgebra (cliffordForm m)) :
    cliffordIncl m (CliffordAlgebra.reverse a) =
      CliffordAlgebra.reverse (cliffordIncl m a) :=
  CliffordAlgebra.map_reverse (cliffordExtendIsometry m) a

/-- `cliffordIncl` commutes with complex-linear Clifford conjugation `star`. -/
@[simp]
theorem cliffordIncl_star (m : ℕ) (a : CliffordAlgebra (cliffordForm m)) :
    cliffordIncl m (star a) = star (cliffordIncl m a) :=
  CliffordAlgebra.map_star (cliffordExtendIsometry m) a

/-- The coordinate inclusion maps `EvenClifford m` into `EvenClifford (m + 1)`. -/
theorem cliffordIncl_mem_even (m : ℕ) {a : CliffordAlgebra (cliffordForm m)}
    (ha : a ∈ EvenClifford m) :
    cliffordIncl m a ∈ EvenClifford (m + 1) :=
  CliffordAlgebra.map_mem_even (cliffordExtendIsometry m) ha

/-- The restricted coordinate inclusion `EvenClifford m →ₐ[ℂ] EvenClifford (m + 1)`. -/
noncomputable def evenCliffordIncl (m : ℕ) :
    EvenClifford m →ₐ[ℂ] EvenClifford (m + 1) :=
  ((cliffordIncl m).comp (EvenClifford m).val).codRestrict (EvenClifford (m + 1)) fun x ↦
    cliffordIncl_mem_even m x.2

/-- Coercing `evenCliffordIncl` to the ambient Clifford algebra recovers `cliffordIncl`. -/
@[simp]
theorem coe_evenCliffordIncl (m : ℕ) (x : EvenClifford m) :
    (evenCliffordIncl m x : CliffordAlgebra (cliffordForm (m + 1))) = cliffordIncl m x := by
  rfl

/-- `cliffordIncl` maps the `j`-th Majorana generator to `majorana (m + 1) j.castSucc`. -/
@[simp]
theorem cliffordIncl_majorana (m : ℕ) (j : Fin m) :
    cliffordIncl m (majorana m j) = majorana (m + 1) j.castSucc := by
  have hsnoc :
      Fin.snoc (Pi.single j (1 : ℂ)) 0 = (Pi.single j.castSucc 1 : Fin (m + 1) → ℂ) := by
    ext k
    refine Fin.lastCases ?_ (fun k ↦ ?_) k
    · simp [(Fin.castSucc_lt_last j).ne']
    · simp [Pi.single_apply]
  simp [majorana_def, hsnoc]

/-- `cliffordIncl` maps the `j`-th Clifford projection to the `j`-th projection on `m + 1`
coordinates. -/
@[simp]
theorem cliffordIncl_cliffordProjection (m : ℕ) (j : Fin (m - 1)) :
    cliffordIncl m (cliffordProjection m j) =
      cliffordProjection (m + 1) ⟨j.1, by omega⟩ := by
  have h0 : (⟨j.1, by omega⟩ : Fin m).castSucc = ⟨j.1, by omega⟩ := Fin.ext (by simp)
  have h1 : (⟨j.1 + 1, by omega⟩ : Fin m).castSucc = ⟨j.1 + 1, by omega⟩ := Fin.ext (by simp)
  simp [cliffordProjection_def, h0, h1]

/-- `cliffordIncl` intertwines `cliffordAdjoint` across adjacent dimensions. -/
@[simp]
theorem cliffordIncl_cliffordAdjoint (m : ℕ) (a : CliffordAlgebra (cliffordForm m)) :
    cliffordIncl m (cliffordAdjoint m a) = cliffordAdjoint (m + 1) (cliffordIncl m a) := by
  induction a using CliffordAlgebra.induction with
  | algebraMap z =>
    simp [Algebra.algebraMap_eq_smul_one]
  | ι v =>
    rw [ι_cliffordForm_eq_sum_majorana]
    simp
  | mul a b ha hb =>
    simp [ha, hb]
  | add a b ha hb =>
    simp [ha, hb]

/-- `evenCliffordIncl` intertwines `evenCliffordAdjoint` across adjacent dimensions. -/
@[simp]
theorem evenCliffordIncl_evenCliffordAdjoint (m : ℕ) (x : EvenClifford m) :
    evenCliffordIncl m (evenCliffordAdjoint m x) =
      evenCliffordAdjoint (m + 1) (evenCliffordIncl m x) :=
  Subtype.ext (by simp)

/-- Coordinate inclusion preserves the Clifford scalar trace. -/
@[simp]
theorem scalarTrace_cliffordIncl (m : ℕ) (a : CliffordAlgebra (cliffordForm m)) :
    CliffordAlgebra.scalarTrace (cliffordForm (m + 1)) (cliffordIncl m a) =
      CliffordAlgebra.scalarTrace (cliffordForm m) a :=
  CliffordAlgebra.scalarTrace_map (cliffordExtendIsometry m) a

/-- The coordinate inclusion `cliffordIncl m` is injective. -/
theorem cliffordIncl_injective (m : ℕ) : Function.Injective (cliffordIncl m) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  apply (scalarTrace_cliffordAdjoint_mul_self_eq_zero_iff m).mp
  rw [← scalarTrace_cliffordIncl m, map_mul, cliffordIncl_cliffordAdjoint, ha, mul_zero, map_zero]

/-- `cliffordIncl m a` lies in `EvenClifford (m + 1)` if and only if `a` lies in
`EvenClifford m`. -/
@[simp]
theorem cliffordIncl_mem_even_iff (m : ℕ) {a : CliffordAlgebra (cliffordForm m)} :
    cliffordIncl m a ∈ EvenClifford (m + 1) ↔ a ∈ EvenClifford m := by
  refine ⟨fun h ↦ ?_, cliffordIncl_mem_even m⟩
  have hinv : CliffordAlgebra.involute (cliffordIncl m a) = cliffordIncl m a :=
    CliffordAlgebra.involute_eq_self_iff.mpr
      (by simpa [← CliffordAlgebra.even_toSubmodule] using h)
  rw [← cliffordIncl_involute] at hinv
  simpa [← CliffordAlgebra.even_toSubmodule] using
    CliffordAlgebra.involute_eq_self_iff.mp (cliffordIncl_injective m hinv)

/-- The even coordinate inclusion `evenCliffordIncl m` is injective. -/
theorem evenCliffordIncl_injective (m : ℕ) : Function.Injective (evenCliffordIncl m) := by
  intro x y hxy
  apply Subtype.ext
  exact cliffordIncl_injective m (congrArg Subtype.val hxy)

/-- `evenCliffordHom` intertwines Temperley–Lieb `strandIncl` with `evenCliffordIncl`. -/
@[simp]
theorem evenCliffordHom_strandIncl (n : ℕ)
    (x : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) (n + 1)) :
    evenCliffordHom (n + 2) (strandIncl x) =
      evenCliffordIncl (n + 1) (evenCliffordHom (n + 1) x) := by
  have hhom : (evenCliffordHom (n + 2)).comp strandIncl =
      (evenCliffordIncl (n + 1)).comp (evenCliffordHom (n + 1)) := by
    apply TemperleyLieb.hom_ext
    intro i
    apply Subtype.ext
    have hi : (⟨i.1, by omega⟩ : Fin (n + 1)) = i.castSucc := Fin.ext (by simp)
    simp only [AlgHom.comp_apply, strandIncl_e, coe_evenCliffordHom_e, coe_evenCliffordIncl,
      map_smul, cliffordIncl_cliffordProjection, hi]
  exact AlgHom.congr_fun hhom x

/-- Multiplying an included Clifford element on the right by the last Clifford projection scales its
scalar trace by `2⁻¹`: the term containing `c_{n + 1}` vanishes by orthogonality. -/
theorem scalarTrace_cliffordIncl_mul_cliffordProjection_last (n : ℕ)
    (a : CliffordAlgebra (cliffordForm (n + 1))) :
    CliffordAlgebra.scalarTrace (cliffordForm (n + 2))
        (cliffordIncl (n + 1) a * cliffordProjection (n + 2) (Fin.last n)) =
      (2 : ℂ)⁻¹ * CliffordAlgebra.scalarTrace (cliffordForm (n + 1)) a := by
  have hortho : ∀ v : Fin (n + 1) → ℂ,
      (cliffordForm (n + 2)).IsOrtho (Pi.single (Fin.last (n + 1)) 1)
        (cliffordExtendIsometry (n + 1) v) := by
    intro v
    rw [← QuadraticMap.associated_isOrtho, associated_cliffordForm]
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    refine Fin.lastCases ?_ (fun k ↦ ?_) k
    · simp
    · simp [(Fin.castSucc_lt_last k).ne]
  have hcast : (⟨(Fin.last n).1, by omega⟩ : Fin (n + 2)) = (Fin.last n).castSucc :=
    Fin.ext (by simp)
  have hlast : (⟨(Fin.last n).1 + 1, by omega⟩ : Fin (n + 2)) = Fin.last (n + 1) :=
    Fin.ext (by simp)
  have hterm : CliffordAlgebra.scalarTrace (cliffordForm (n + 2))
      (cliffordIncl (n + 1) a *
        (majorana (n + 2) (Fin.last n).castSucc * majorana (n + 2) (Fin.last (n + 1)))) = 0 := by
    rw [← cliffordIncl_majorana (n + 1) (Fin.last n), ← mul_assoc, ← map_mul, majorana_def,
      majorana_def, cliffordIncl_def]
    exact CliffordAlgebra.scalarTrace_map_mul_ι_eq_zero (cliffordExtendIsometry (n + 1)) hortho _
  rw [cliffordProjection_def, hcast, hlast]
  simp [mul_add, hterm]

/-- The unnormalized Markov trace on `TemperleyLieb ℂ (√2 : ℂ) m` obtained by pulling back
`(√2) ^ m` times `CliffordAlgebra.scalarTrace (cliffordForm m)` along `evenCliffordHom m`. -/
noncomputable def evenCliffordTrace (m : ℕ) :
    TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m →ₗ[ℂ] ℂ :=
  ((Real.sqrt 2 : ℂ) ^ m) •
    (CliffordAlgebra.scalarTrace (cliffordForm m) ∘ₗ
      (EvenClifford m).val.toLinearMap ∘ₗ (evenCliffordHom m).toLinearMap)

/-- Evaluation formula for `evenCliffordTrace`. -/
theorem evenCliffordTrace_apply (m : ℕ) (x : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m) :
    evenCliffordTrace m x =
      (Real.sqrt 2 : ℂ) ^ m *
        CliffordAlgebra.scalarTrace (cliffordForm m) (evenCliffordHom m x) := by
  simp [evenCliffordTrace]

/-- **The Clifford scalar trace defines a Markov trace at `δ = √2`.** -/
theorem isMarkovTrace_evenCliffordTrace :
    IsMarkovTrace ℂ (Real.sqrt 2 : ℂ) evenCliffordTrace where
  map_one m := by simp [evenCliffordTrace_apply]
  map_mul_comm m x y := by
    simp only [evenCliffordTrace_apply, map_mul, Subalgebra.coe_mul,
      CliffordAlgebra.scalarTrace_mul_comm]
  map_strandIncl n x := by
    simp only [evenCliffordTrace_apply, evenCliffordHom_strandIncl, coe_evenCliffordIncl,
      scalarTrace_cliffordIncl, pow_succ']
    ring
  map_strandIncl_mul_e_last n x := by
    have hsqrt : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
      exact_mod_cast Real.mul_self_sqrt zero_le_two
    simp only [evenCliffordTrace_apply, map_mul, Subalgebra.coe_mul, evenCliffordHom_strandIncl,
      coe_evenCliffordIncl, coe_evenCliffordHom_e, mul_smul_comm, map_smul,
      scalarTrace_cliffordIncl_mul_cliffordProjection_last, smul_eq_mul]
    rw [pow_succ]
    calc
      (Real.sqrt 2 : ℂ) ^ (n + 1) * (Real.sqrt 2 : ℂ) *
          ((Real.sqrt 2 : ℂ) *
            ((2 : ℂ)⁻¹ *
              CliffordAlgebra.scalarTrace (cliffordForm (n + 1)) (evenCliffordHom (n + 1) x)))
          = (Real.sqrt 2 : ℂ) ^ (n + 1) *
              (((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)) * (2 : ℂ)⁻¹) *
                CliffordAlgebra.scalarTrace (cliffordForm (n + 1)) (evenCliffordHom (n + 1) x) := by
            ring
      _ = (Real.sqrt 2 : ℂ) ^ (n + 1) *
            CliffordAlgebra.scalarTrace (cliffordForm (n + 1)) (evenCliffordHom (n + 1) x) := by
            rw [hsqrt]
            norm_num

namespace IsMarkovTrace

variable {tr : ∀ n : ℕ, TemperleyLieb ℂ (Real.sqrt 2 : ℂ) n →ₗ[ℂ] ℂ}

/-- Every Markov trace on `TemperleyLieb ℂ (√2 : ℂ)` coincides with `evenCliffordTrace`. -/
theorem eq_evenCliffordTrace (htr : IsMarkovTrace ℂ (Real.sqrt 2 : ℂ) tr) :
    tr = evenCliffordTrace :=
  htr.unique isMarkovTrace_evenCliffordTrace

/-- **The Markov trace at `δ = √2` as the Clifford scalar trace**: for every Markov trace `tr`,
`tr m x = (√2 : ℂ) ^ m * scalarTrace (cliffordForm m) (evenCliffordHom m x)`. -/
theorem apply_eq_mul_scalarTrace_evenCliffordHom
    (htr : IsMarkovTrace ℂ (Real.sqrt 2 : ℂ) tr) (m : ℕ)
    (x : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m) :
    tr m x =
      (Real.sqrt 2 : ℂ) ^ m *
        CliffordAlgebra.scalarTrace (cliffordForm m) (evenCliffordHom m x) := by
  rw [htr.eq_evenCliffordTrace, evenCliffordTrace_apply]

/-- **Positivity of the Markov trace at `δ = √2`** (the `m = 4` discrete-series point
`2 cos (π / 4)` of Jones's positivity theorem): `0 ≤ tr m (star x * x)` on every number of
strands. -/
theorem map_star_mul_self_nonneg_sqrt_two
    (htr : IsMarkovTrace ℂ (Real.sqrt 2 : ℂ) tr) {m : ℕ}
    (x : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m) :
    0 ≤ tr m (star x * x) := by
  have hz := scalarTrace_cliffordAdjoint_mul_self_nonneg m (evenCliffordHom m x)
  have hz0 : ((0 : ℝ) : ℂ) ≤
      CliffordAlgebra.scalarTrace (cliffordForm m)
        (cliffordAdjoint m (evenCliffordHom m x) * evenCliffordHom m x) := by
    simpa using hz
  rw [htr.apply_eq_mul_scalarTrace_evenCliffordHom, map_mul, Subalgebra.coe_mul,
    coe_evenCliffordHom_star, Complex.eq_re_of_ofReal_le hz0,
    ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.zero_le_real]
  exact mul_nonneg (by positivity) (Complex.nonneg_iff.mp hz).1

/-- At `δ = √2`, `tr m (star x * x) = 0` if and only if `evenCliffordHom m x = 0`. -/
theorem map_star_mul_self_eq_zero_iff_evenCliffordHom_eq_zero
    (htr : IsMarkovTrace ℂ (Real.sqrt 2 : ℂ) tr) {m : ℕ}
    {x : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m} :
    tr m (star x * x) = 0 ↔ evenCliffordHom m x = 0 := by
  simp [htr.apply_eq_mul_scalarTrace_evenCliffordHom]

/-! ### Kernel = trace radical and the Jones quotient equivalence -/

/-- **The trace radical at `δ = √2` is the kernel of `evenCliffordHom`.** -/
theorem traceRadical_eq_ker_evenCliffordHom
    (htr : IsMarkovTrace ℂ (Real.sqrt 2 : ℂ) tr) (m : ℕ) :
    (tr m).traceRadical (htr.map_mul_comm m) = RingHom.ker (evenCliffordHom m) := by
  have hne : (Real.sqrt 2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr zero_lt_two)
  ext x
  rw [LinearMap.mem_traceRadical, RingHom.mem_ker]
  simp only [htr.apply_eq_mul_scalarTrace_evenCliffordHom, map_mul, Subalgebra.coe_mul,
    mul_eq_zero, pow_ne_zero m hne, false_or]
  exact (evenCliffordHom_surjective m).forall.symm.trans
    (CliffordAlgebra.forall_even_scalarTrace_mul_eq_zero_iff (nondegenerate_cliffordForm m))

/-- At `δ = √2`, the null vectors of `x ↦ tr m (star x * x)` are precisely the trace radical. -/
theorem map_star_mul_self_eq_zero_iff_mem_traceRadical_sqrt_two
    (htr : IsMarkovTrace ℂ (Real.sqrt 2 : ℂ) tr) {m : ℕ}
    {x : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m} :
    tr m (star x * x) = 0 ↔ x ∈ (tr m).traceRadical (htr.map_mul_comm m) := by
  rw [htr.map_star_mul_self_eq_zero_iff_evenCliffordHom_eq_zero,
    htr.traceRadical_eq_ker_evenCliffordHom, RingHom.mem_ker]

/-- **The Jones quotient at `δ = √2` is isomorphic to the even Clifford algebra**
`EvenClifford m`. -/
noncomputable def quotientEvenCliffordEquiv
    (htr : IsMarkovTrace ℂ (Real.sqrt 2 : ℂ) tr) (m : ℕ) :
    (TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m ⧸ (tr m).traceRadical (htr.map_mul_comm m)) ≃ₐ[ℂ]
      EvenClifford m :=
  (Ideal.quotientEquivAlgOfEq ℂ (htr.traceRadical_eq_ker_evenCliffordHom m)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (evenCliffordHom_surjective m))

/-- `quotientEvenCliffordEquiv` evaluates on a quotient representative via `evenCliffordHom`. -/
@[simp]
theorem quotientEvenCliffordEquiv_mk
    (htr : IsMarkovTrace ℂ (Real.sqrt 2 : ℂ) tr) (m : ℕ)
    (x : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m) :
    htr.quotientEvenCliffordEquiv m
        (Ideal.Quotient.mk ((tr m).traceRadical (htr.map_mul_comm m)) x) =
      evenCliffordHom m x := by
  simp [quotientEvenCliffordEquiv, Ideal.quotientEquivAlgOfEq_mk]

/-- `quotientEvenCliffordEquiv` intertwines the Temperley–Lieb quotient strand map
`quotientStrandIncl` with the even Clifford coordinate inclusion `evenCliffordIncl`. -/
@[simp]
theorem quotientEvenCliffordEquiv_quotientStrandIncl
    (htr : IsMarkovTrace ℂ (Real.sqrt 2 : ℂ) tr) (n : ℕ)
    (q : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) (n + 1) ⧸
      (tr (n + 1)).traceRadical (htr.map_mul_comm (n + 1))) :
    htr.quotientEvenCliffordEquiv (n + 2) (htr.quotientStrandIncl n q) =
      evenCliffordIncl (n + 1) (htr.quotientEvenCliffordEquiv (n + 1) q) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp

/-- `(quotientEvenCliffordEquiv m).symm` maps `evenCliffordHom m x` back to the quotient class
of `x`. -/
@[simp]
theorem quotientEvenCliffordEquiv_symm_evenCliffordHom
    (htr : IsMarkovTrace ℂ (Real.sqrt 2 : ℂ) tr) (m : ℕ)
    (x : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m) :
    (htr.quotientEvenCliffordEquiv m).symm (evenCliffordHom m x) =
      Ideal.Quotient.mk ((tr m).traceRadical (htr.map_mul_comm m)) x :=
  (htr.quotientEvenCliffordEquiv m).injective (by simp)

/-- `(quotientEvenCliffordEquiv _).symm` intertwines `evenCliffordIncl` with
`quotientStrandIncl`. -/
@[simp]
theorem quotientEvenCliffordEquiv_symm_evenCliffordIncl
    (htr : IsMarkovTrace ℂ (Real.sqrt 2 : ℂ) tr) (n : ℕ)
    (y : EvenClifford (n + 1)) :
    (htr.quotientEvenCliffordEquiv (n + 2)).symm (evenCliffordIncl (n + 1) y) =
      htr.quotientStrandIncl n ((htr.quotientEvenCliffordEquiv (n + 1)).symm y) :=
  (htr.quotientEvenCliffordEquiv (n + 2)).injective (by simp)

/-- The induced trace on the `m`-strand Temperley–Lieb quotient at `δ = √2` is `(√2 : ℂ) ^ m` times
`CliffordAlgebra.scalarTrace` under `quotientEvenCliffordEquiv`. -/
theorem quotientTrace_eq_mul_scalarTrace_quotientEvenCliffordEquiv
    (htr : IsMarkovTrace ℂ (Real.sqrt 2 : ℂ) tr) (m : ℕ)
    (q : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m ⧸
      (tr m).traceRadical (htr.map_mul_comm m)) :
    (tr m).quotientTrace (htr.map_mul_comm m) q =
      (Real.sqrt 2 : ℂ) ^ m *
        CliffordAlgebra.scalarTrace (cliffordForm m) (htr.quotientEvenCliffordEquiv m q) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  simp [htr.apply_eq_mul_scalarTrace_evenCliffordHom]

/-- Transporting `quotientTrace` across `(quotientEvenCliffordEquiv m).symm` gives `(√2 : ℂ) ^ m`
times `CliffordAlgebra.scalarTrace`. -/
@[simp]
theorem quotientTrace_quotientEvenCliffordEquiv_symm
    (htr : IsMarkovTrace ℂ (Real.sqrt 2 : ℂ) tr) (m : ℕ) (x : EvenClifford m) :
    (tr m).quotientTrace (htr.map_mul_comm m) ((htr.quotientEvenCliffordEquiv m).symm x) =
      (Real.sqrt 2 : ℂ) ^ m * CliffordAlgebra.scalarTrace (cliffordForm m) x := by
  simp [htr.quotientTrace_eq_mul_scalarTrace_quotientEvenCliffordEquiv]

/-- The `m`-strand Temperley–Lieb trace quotient at `δ = √2` has complex dimension `2 ^ (m - 1)`. -/
@[simp]
theorem finrank_quotient_traceRadical_sqrt_two
    (htr : IsMarkovTrace ℂ (Real.sqrt 2 : ℂ) tr) (m : ℕ) :
    Module.finrank ℂ
        (TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m ⧸ (tr m).traceRadical (htr.map_mul_comm m)) =
      2 ^ (m - 1) := by
  rw [(htr.quotientEvenCliffordEquiv m).toLinearEquiv.finrank_eq, finrank_evenClifford]

end IsMarkovTrace

/-- Specialization of `IsMarkovTrace.apply_eq_mul_scalarTrace_evenCliffordHom` to the spin-model
`markovTrace` at any unit `q : ℂˣ` satisfying `(√2 : ℂ) = -(q + q⁻¹)`. -/
theorem markovTrace_eq_mul_scalarTrace_evenCliffordHom (q : ℂˣ)
    (hq : (Real.sqrt 2 : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ))) {m : ℕ}
    (x : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m) :
    markovTrace q hq x =
      (Real.sqrt 2 : ℂ) ^ m *
        CliffordAlgebra.scalarTrace (cliffordForm m) (evenCliffordHom m x) :=
  (isMarkovTrace_markovTrace q hq).apply_eq_mul_scalarTrace_evenCliffordHom m x

/-! ### Packaged even Clifford model and vanishing of the three-strand Jones–Wenzl projection -/

/-- **The even Clifford model of `TemperleyLieb ℂ (√2 : ℂ) m`.** For every Markov trace `tr` at
loop value `√2` and every `m : ℕ`, there is a surjective `ℂ`-algebra homomorphism
`F : TemperleyLieb ℂ (√2 : ℂ) m →ₐ[ℂ] EvenClifford m` sending each generator `e j` to
`(√2 : ℂ) • cliffordProjection m j`, intertwining `star` with `cliffordAdjoint m`, expressing
`tr m` as `(√2 : ℂ) ^ m` times `CliffordAlgebra.scalarTrace (cliffordForm m)`, and having kernel
equal to the trace radical `(tr m).traceRadical`. -/
theorem exists_evenCliffordModel
    {tr : ∀ n : ℕ, TemperleyLieb ℂ (Real.sqrt 2 : ℂ) n →ₗ[ℂ] ℂ}
    (htr : IsMarkovTrace ℂ (Real.sqrt 2 : ℂ) tr) (m : ℕ) :
    ∃ F : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m →ₐ[ℂ] EvenClifford m,
      Function.Surjective F ∧
      (∀ j : Fin (m - 1),
        (F (e (Real.sqrt 2 : ℂ) j) : CliffordAlgebra (cliffordForm m)) =
          (Real.sqrt 2 : ℂ) • cliffordProjection m j) ∧
      (∀ x : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m,
        (F (star x) : CliffordAlgebra (cliffordForm m)) =
          cliffordAdjoint m (F x)) ∧
      (∀ x : TemperleyLieb ℂ (Real.sqrt 2 : ℂ) m,
        tr m x =
          (Real.sqrt 2 : ℂ) ^ m *
            CliffordAlgebra.scalarTrace (cliffordForm m) (F x)) ∧
      RingHom.ker F = (tr m).traceRadical (htr.map_mul_comm m) :=
  ⟨evenCliffordHom m,
    evenCliffordHom_surjective m,
    coe_evenCliffordHom_e m,
    coe_evenCliffordHom_star,
    htr.apply_eq_mul_scalarTrace_evenCliffordHom m,
    (htr.traceRadical_eq_ker_evenCliffordHom m).symm⟩

/-- At `δ = √2`, `evenCliffordHom 3` maps the three-strand Jones–Wenzl projection
`jonesWenzl (√2 : ℂ) 3` to `0`. -/
@[simp]
theorem evenCliffordHom_jonesWenzl_three :
    evenCliffordHom 3 (jonesWenzl (Real.sqrt 2 : ℂ) 3) = 0 := by
  have hsqrt : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    exact_mod_cast Real.mul_self_sqrt zero_le_two
  have hq3 : qInt ℂ (Real.sqrt 2 : ℂ) 3 = 1 := by
    rw [qInt_add_two (Real.sqrt 2 : ℂ) 1, qInt_two, qInt_one, hsqrt]
    norm_num
  have hq4 : qInt ℂ (Real.sqrt 2 : ℂ) 4 = 0 := by
    rw [qInt_add_two (Real.sqrt 2 : ℂ) 2, hq3, qInt_two]
    ring
  have hunits : ∀ k ∈ Finset.Icc 1 3, IsUnit (qInt ℂ (Real.sqrt 2 : ℂ) k) := by
    intro k hk
    obtain ⟨hk1, hk3⟩ := Finset.mem_Icc.mp hk
    interval_cases k
    · simp
    · simp [qInt_two]
    · simp [hq3]
  rw [← RingHom.mem_ker, ← isMarkovTrace_evenCliffordTrace.traceRadical_eq_ker_evenCliffordHom 3,
    isMarkovTrace_evenCliffordTrace.jonesWenzl_mem_traceRadical_iff hunits]
  exact hq4

end TauCeti.TemperleyLieb
