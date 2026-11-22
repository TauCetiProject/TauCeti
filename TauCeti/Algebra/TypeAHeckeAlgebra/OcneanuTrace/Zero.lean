/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TypeAHeckeAlgebra.OcneanuTrace.Basic
public import TauCeti.Algebra.TypeAHeckeAlgebra.Regular.Form
public import TauCeti.RingTheory.TraceFunctional.Radical

/-!
# Positivity and faithfulness of the zero-parameter Ocneanu trace

At `z = 0`, the Ocneanu trace agrees on every finite stage with the canonical symmetrizing trace
(`TauCeti.TypeAHeckeAlgebra.canonicalTrace_eq_ocneanuTrace_zero`, proved via
`TauCeti.TypeAHeckeAlgebra.canonicalTrace_eq_regularRep_toInfinite`). Consequently it is
`⋆`-positive over any commutative `StarOrderedRing` with star-fixed parameter
(`TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_zero_star_mul_self_nonneg`), and over `ℝ` or `ℂ`
its trace form is anisotropic
(`TauCeti.InfiniteTypeAHeckeAlgebra.ocneanuTrace_zero_star_mul_self_eq_zero_iff`) and its trace
radical is trivial (`TauCeti.InfiniteTypeAHeckeAlgebra.traceRadical_ocneanuTrace_zero`).
-/

public section

namespace TauCeti

namespace TypeAHeckeAlgebra

variable {R : Type*} [CommRing R] {q : Rˣ}

/-- **The canonical trace is the `z = 0` Ocneanu trace** along `toInfinite`. -/
theorem canonicalTrace_eq_ocneanuTrace_zero {n : ℕ} {W : Type*} [Group W]
    (cs : CoxeterSystem (CoxeterMatrix.A (n - 1)) W) (x : TypeAHeckeAlgebra R q n) :
    canonicalTrace cs x = InfiniteTypeAHeckeAlgebra.ocneanuTrace R q 0 (toInfinite R q n x) := by
  classical
  let cs₀ (m : ℕ) := (CoxeterMatrix.A (m - 1)).toCoxeterSystem
  let cs' := coxeterMatrixAInfty.toCoxeterSystem
  rw [canonicalTrace_eq_regularRep_toInfinite cs cs',
    ← canonicalTrace_eq_regularRep_toInfinite (cs₀ n) cs']
  refine eq_ocneanuTrace_toInfinite (fun m ↦ canonicalTrace (cs₀ m))
    (canonicalTrace_one (cs₀ 0)) (fun m y ↦ by
      rw [canonicalTrace_eq_regularRep_toInfinite (cs₀ (m + 1)) cs',
        canonicalTrace_eq_regularRep_toInfinite (cs₀ m) cs', toInfinite_strandIncl])
    (fun m ↦ canonicalTrace_mul_comm (cs₀ m)) (fun m y ↦ ?_) n x
  rw [zero_mul, canonicalTrace_mul_comm]
  refine LinearMap.congr_fun ((basisTw q (cs₀ (m + 1))).ext
    (f₁ := (canonicalTrace (R := R) (q := q) (cs₀ (m + 2))).comp
      ((LinearMap.mulLeft R (T q (Fin.last m))).comp (strandIncl R q (m + 1)).toLinearMap))
    (f₂ := 0) fun w ↦ ?_) y
  simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
    LinearMap.mulLeft_apply, LinearMap.zero_apply, coe_basisTw,
    canonicalTrace_eq_regularRep_toInfinite (cs₀ (m + 2)) cs', map_mul, toInfinite_T,
    Fin.val_last, toInfinite_strandIncl, mul_apply_eq_comp,
    InfiniteTypeAHeckeAlgebra.regularRep_T, regularRep_toInfinite_Tw_apply_single_one]
  set u := (cs₀ (m + 1)).parabolicHom cs' coxeterMatrixA_eq_coxeterMatrixAInfty w
  have hsu : cs'.simple m * u ≠ 1 := fun hmul ↦ by
    have hmem : cs'.simple m ∈
        ((cs₀ (m + 1)).parabolicHom cs' coxeterMatrixA_eq_coxeterMatrixAInfty).range :=
      ⟨w⁻¹, by rw [map_inv]; exact (eq_inv_of_mul_eq_one_left hmul).symm⟩
    rw [(cs₀ (m + 1)).range_parabolicHom coxeterMatrixA_eq_coxeterMatrixAInfty,
      cs'.simple_mem_parabolic_iff] at hmem
    obtain ⟨j, hj⟩ := hmem
    exact j.isLt.ne hj
  by_cases hd : cs'.IsLeftDescent u m
  · have hu1 : u ≠ 1 := fun h1 ↦ cs'.not_isLeftDescent_one m (h1 ▸ hd)
    rw [cs'.heckeLeftMul_single_of_isLeftDescent hd]
    simp [hu1.symm, hsu.symm]
  · rw [cs'.heckeLeftMul_single_of_not_isLeftDescent hd]
    simp [hsu.symm]

end TypeAHeckeAlgebra

namespace InfiniteTypeAHeckeAlgebra

/-- **Positivity of the `z = 0` Ocneanu trace** over any commutative `StarOrderedRing`. -/
theorem ocneanuTrace_zero_star_mul_self_nonneg {R : Type*} [CommRing R] [PartialOrder R]
    [StarRing R] [StarOrderedRing R] {q : Rˣ} [Fact (IsSelfAdjoint (q : R))]
    (x : InfiniteTypeAHeckeAlgebra R q) :
    0 ≤ ocneanuTrace R q 0 (star x * x) := by
  obtain ⟨n, hx⟩ := exists_mem_stage x
  rw [← TypeAHeckeAlgebra.range_toInfinite, AlgHom.mem_range] at hx; obtain ⟨y, rfl⟩ := hx
  rw [← TypeAHeckeAlgebra.toInfinite_star, ← map_mul,
    ← TypeAHeckeAlgebra.canonicalTrace_eq_ocneanuTrace_zero (permCoxeterSystem n),
    TypeAHeckeAlgebra.canonicalTrace_star_mul]
  exact Finset.sum_nonneg fun _ _ ↦ star_mul_self_nonneg _

/-- Over `ℝ` or `ℂ` (`RCLike 𝕜`), the `z = 0` Ocneanu trace form is anisotropic. -/
@[simp]
theorem ocneanuTrace_zero_star_mul_self_eq_zero_iff {𝕜 : Type*} [RCLike 𝕜] {q : 𝕜ˣ}
    [Fact (IsSelfAdjoint (q : 𝕜))] (x : InfiniteTypeAHeckeAlgebra 𝕜 q) :
    ocneanuTrace 𝕜 q 0 (star x * x) = 0 ↔ x = 0 := by
  obtain ⟨n, hx⟩ := exists_mem_stage x
  rw [← TypeAHeckeAlgebra.range_toInfinite, AlgHom.mem_range] at hx; obtain ⟨y, rfl⟩ := hx
  rw [← TypeAHeckeAlgebra.toInfinite_star, ← map_mul,
    ← TypeAHeckeAlgebra.canonicalTrace_eq_ocneanuTrace_zero (permCoxeterSystem n),
    TypeAHeckeAlgebra.canonicalTrace_star_mul_self_eq_zero_iff,
    map_eq_zero_iff _ (TypeAHeckeAlgebra.toInfinite_injective 𝕜 q n)]

/-- **Faithfulness of the `z = 0` Ocneanu trace** over `ℝ` or `ℂ`. -/
theorem traceRadical_ocneanuTrace_zero {𝕜 : Type*} [RCLike 𝕜] {q : 𝕜ˣ}
    [Fact (IsSelfAdjoint (q : 𝕜))] :
    (ocneanuTrace 𝕜 q 0).traceRadical (isMarkovTrace_ocneanuTrace 0).map_mul_comm = ⊥ := by
  refine eq_bot_iff.mpr fun x hx ↦ (ocneanuTrace_zero_star_mul_self_eq_zero_iff x).mp ?_
  rw [LinearMap.mem_traceRadical] at hx
  rw [(isMarkovTrace_ocneanuTrace 0).map_mul_comm]
  exact hx (star x)

end InfiniteTypeAHeckeAlgebra

end TauCeti
