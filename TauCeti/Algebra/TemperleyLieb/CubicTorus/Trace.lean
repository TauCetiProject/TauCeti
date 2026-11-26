/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.CubicTorus.Basic
public import TauCeti.Algebra.TemperleyLieb.MarkovTrace
import TauCeti.Algebra.Group.Fin.Tuple
import TauCeti.Analysis.Complex.Sqrt

/-!
# The Markov trace at `δ = √3` through the cubic quantum torus

Building on the cubic comparison map `F_m = cubicHom m : TemperleyLieb ℂ (√3 : ℂ) m →ₐ[ℂ] C_(m-1)`
of `TauCeti.Algebra.TemperleyLieb.CubicTorus.Basic`, this file equips the cubic quantum tori with
their tower inclusions and identifies every Markov trace at `δ = √3` with `(√3) ^ m s_(m-1) ∘ F_m`,
where `s_N = cubicScalarCoefficient N` is the coefficient of `1`.

Extending `a : Fin N → ZMod 3` by a zero last coordinate preserves the chain form, so
`W(a) ↦ W(a, 0)` defines an algebra map `I_N = cubicIncl N : G_N →ₐ[ℂ] G_(N+1)`. It sends `U_j` to
`U_j`, commutes with the inversions, preserves `s`, and intertwines the strand inclusion of the
Temperley–Lieb tower with `F`. For `x ∈ G_N` the products `I_N(x) U_N` and `I_N(x) U_N ^ 2` involve
only basis elements with nonzero last coordinate, so `s_(N+1)(I_N(x) p_N) = s_N(x) / 3`. With
`(√3) ^ 2 = 3` this is the Markov property, and `x ↦ (√3) ^ m s_(m-1)(F_m x)` is a Markov trace
(`isMarkovTrace_cubicTrace`). By uniqueness of Markov traces, every Markov trace at `δ = √3`, in
particular the spin-model `markovTrace`, is this one.

## Main definitions

* `TauCeti.TemperleyLieb.cubicIncl`: the inclusion `G_N →ₐ[ℂ] G_(N+1)`, `W(a) ↦ W(a, 0)`.
* `TauCeti.TemperleyLieb.cubicTrace`: the Markov trace `x ↦ (√3) ^ m s_(m-1)(F_m x)`.

## Main results

* `TauCeti.TemperleyLieb.cubicHom_strandIncl`: `F_(n+2) ∘ strandIncl = I_n ∘ F_(n+1)`.
* `TauCeti.TemperleyLieb.cubicScalarCoefficient_cubicIncl_mul_cubicProjection_last`:
  `s_(N+1)(I_N(x) p_N) = 3⁻¹ s_N(x)`.
* `TauCeti.TemperleyLieb.isMarkovTrace_cubicTrace`,
  `TauCeti.TemperleyLieb.IsMarkovTrace.apply_eq_mul_cubicScalarCoefficient_cubicHom` and
  `TauCeti.TemperleyLieb.markovTrace_eq_mul_cubicScalarCoefficient_cubicHom`: the Markov trace at
  `δ = √3` is `(√3) ^ m s_(m-1) ∘ F_m`.

## Implementation notes

`F_m` takes values in `C_(m-1)`, so at `m = n + 1` and `m = n + 2` its codomain is indexed by
`n + 1 - 1` and `n + 2 - 1`, which are `n` and `n + 1` only after unfolding `Nat.sub`. The tower
statements are therefore phrased through `Subtype.val` at the indices `n` and `n + 1`.

## References

* V. F. R. Jones, *A polynomial invariant for knots via von Neumann algebras*, Bull. Amer. Math.
  Soc. 12 (1985), 103–111, p. 107.
* E. C. Rowell and H. Wenzl, *SO(N)_2 braid group representations are Gaussian*, Quantum Topol. 8
  (2017), §4.
-/

public section

namespace TauCeti.TemperleyLieb

open TwistedMonoidAlgebra

/-! ### The tower inclusions -/

section Inclusion

variable (N : ℕ)

/-- The **inclusion** `I_N : G_N →ₐ[ℂ] G_(N+1)` of cubic quantum tori, `W(a) ↦ W(a, 0)`: extending
by a zero last coordinate preserves the chain form (`chainForm_snoc_zero`). -/
noncomputable def cubicIncl : CubicTorus N →ₐ[ℂ] CubicTorus (N + 1) :=
  TwistedMonoidAlgebra.lift (fun g ↦ weyl (N + 1) (Fin.snoc g.toAdd 0))
    (by
      have h : (Fin.snoc (0 : Fin N → ZMod 3) 0 : Fin (N + 1) → ZMod 3) = 0 := by
        funext i
        refine Fin.lastCases ?_ (fun i ↦ ?_) i <;> simp
      simp [h])
    fun g h ↦ by
      have hadd : (Fin.snoc g.toAdd 0 + Fin.snoc h.toAdd 0 : Fin (N + 1) → ZMod 3) =
          Fin.snoc (g * h).toAdd 0 := by
        funext i
        refine Fin.lastCases ?_ (fun i ↦ ?_) i <;> simp
      rw [weyl_mul_weyl, chainForm_snoc_zero, hadd, cubicFactor_apply]

variable {N}

@[simp]
theorem cubicIncl_weyl (a : Fin N → ZMod 3) :
    cubicIncl N (weyl N a) = weyl (N + 1) (Fin.snoc a 0) := by
  rw [weyl_def, cubicIncl, TwistedMonoidAlgebra.lift_of, toAdd_ofAdd]

@[simp]
theorem cubicIncl_cubicSite (j : Fin N) :
    cubicIncl N (cubicSite N j) = cubicSite (N + 1) j.castSucc := by
  have h : (Fin.snoc (Pi.single j 1 : Fin N → ZMod 3) 0 : Fin (N + 1) → ZMod 3) =
      Pi.single j.castSucc 1 := by
    funext i
    refine Fin.lastCases ?_ (fun i ↦ ?_) i
    · simp [(Fin.castSucc_lt_last j).ne']
    · simp [Pi.single_apply, Fin.castSucc_inj]
  rw [cubicSite_def, cubicIncl_weyl, h, cubicSite_def]

@[simp]
theorem cubicIncl_cubicProjection (j : Fin N) :
    cubicIncl N (cubicProjection N j) = cubicProjection (N + 1) j.castSucc := by
  simp [cubicProjection_def]

/-- The inclusion commutes with the inversions. -/
theorem cubicInversion_cubicIncl (x : CubicTorus N) :
    cubicInversion (N + 1) (cubicIncl N x) = cubicIncl N (cubicInversion N x) := by
  have h : (cubicInversion (N + 1)).comp (cubicIncl N) = (cubicIncl N).comp (cubicInversion N) :=
    algHom_ext fun g ↦ by simp [of_eq_weyl, Fin.neg_snoc]
  exact AlgHom.congr_fun h x

/-- The inclusion preserves the scalar coefficient. -/
@[simp]
theorem cubicScalarCoefficient_cubicIncl (x : CubicTorus N) :
    cubicScalarCoefficient (N + 1) (cubicIncl N x) = cubicScalarCoefficient N x := by
  have h : cubicScalarCoefficient (N + 1) ∘ₗ (cubicIncl N).toLinearMap =
      cubicScalarCoefficient N :=
    (basis ℂ _ (cubicFactor N)).ext fun g ↦ by
      have hzero : (Fin.snoc g.toAdd 0 : Fin (N + 1) → ZMod 3) = 0 ↔ g.toAdd = 0 := by
        refine ⟨fun h ↦ funext fun i ↦ by simpa using congrFun h i.castSucc, fun h ↦ ?_⟩
        rw [h]
        funext i
        refine Fin.lastCases ?_ (fun i ↦ ?_) i <;> simp
      rw [LinearMap.comp_apply, basis_apply, of_eq_weyl]
      simp [hzero]
  exact LinearMap.congr_fun h x

/-- Multiplying an included element by a nontrivial power of the new site unitary `U_N` kills its
scalar coefficient: every basis element in the product has last coordinate `n ≠ 0`. -/
theorem cubicScalarCoefficient_cubicIncl_mul_cubicSite_last_pow (x : CubicTorus N) {n : ℕ}
    (hn : (n : ZMod 3) ≠ 0) :
    cubicScalarCoefficient (N + 1) (cubicIncl N x * cubicSite (N + 1) (Fin.last N) ^ n) = 0 := by
  have h : cubicScalarCoefficient (N + 1) ∘ₗ
      LinearMap.mulRight ℂ (cubicSite (N + 1) (Fin.last N) ^ n) ∘ₗ (cubicIncl N).toLinearMap = 0 :=
    (basis ℂ _ (cubicFactor N)).ext fun g ↦ by
      have hne : (Fin.snoc g.toAdd 0 + Pi.single (Fin.last N) (n : ZMod 3) :
          Fin (N + 1) → ZMod 3) ≠ 0 := fun h ↦ hn (by simpa using congrFun h (Fin.last N))
      simp [of_eq_weyl, cubicSite_pow, hne]
  exact LinearMap.congr_fun h x

/-- **The Markov property of the scalar coefficient**: multiplying an included element by the last
cubic projection divides its scalar coefficient by `3`. -/
theorem cubicScalarCoefficient_cubicIncl_mul_cubicProjection_last (x : CubicTorus N) :
    cubicScalarCoefficient (N + 1) (cubicIncl N x * cubicProjection (N + 1) (Fin.last N)) =
      (3 : ℂ)⁻¹ * cubicScalarCoefficient N x := by
  have h1 := cubicScalarCoefficient_cubicIncl_mul_cubicSite_last_pow x (n := 1) (by decide)
  have h2 := cubicScalarCoefficient_cubicIncl_mul_cubicSite_last_pow x (n := 2) (by decide)
  rw [pow_one] at h1
  simp [cubicProjection_def, mul_add, h1, h2]

end Inclusion

/-! ### The Markov trace -/

section MarkovTrace

/-- The cubic comparison maps intertwine the strand inclusion with `cubicIncl`. -/
theorem cubicHom_strandIncl (n : ℕ) (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) (n + 1)) :
    ((cubicHom (n + 2) (strandIncl x)).val : CubicTorus (n + 1)) =
      cubicIncl n (cubicHom (n + 1) x).val := by
  have hhom : ((cubicFixed (n + 1)).val.comp (cubicHom (n + 2))).comp strandIncl =
      (cubicIncl n).comp ((cubicFixed n).val.comp (cubicHom (n + 1))) := by
    apply TemperleyLieb.hom_ext
    intro i
    simp only [AlgHom.comp_apply, strandIncl_e, Subalgebra.coe_val]
    rw [coe_cubicHom_e, coe_cubicHom_e]
    -- The index `n + 1 - 1` is `n` only up to unfolding `Nat.sub`, so state the step at `n`.
    exact (by rw [AlgHom.map_smul_of_tower, cubicIncl_cubicProjection] :
      (Real.sqrt 3 : ℂ) • cubicProjection (n + 1) i.castSucc =
        cubicIncl n ((Real.sqrt 3 : ℂ) • cubicProjection n i))
  exact AlgHom.congr_fun hhom x

/-- The unnormalized Markov trace on `TemperleyLieb ℂ (√3 : ℂ) m` obtained by pulling back
`(√3) ^ m` times the scalar coefficient along the cubic comparison map. -/
noncomputable def cubicTrace (m : ℕ) : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m →ₗ[ℂ] ℂ :=
  ((Real.sqrt 3 : ℂ) ^ m) •
    (cubicScalarCoefficient (m - 1) ∘ₗ (cubicFixed (m - 1)).val.toLinearMap ∘ₗ
      (cubicHom m).toLinearMap)

theorem cubicTrace_apply (m : ℕ) (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    cubicTrace m x = (Real.sqrt 3 : ℂ) ^ m * cubicScalarCoefficient (m - 1) (cubicHom m x) := by
  simp [cubicTrace]

/-- **The scalar coefficient of the cubic quantum torus defines a Markov trace at `δ = √3`.** -/
theorem isMarkovTrace_cubicTrace : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) cubicTrace where
  map_one m := by simp [cubicTrace_apply]
  map_mul_comm m x y := by
    simp only [cubicTrace_apply, map_mul, Subalgebra.coe_mul, cubicScalarCoefficient_mul_comm]
  map_strandIncl n x := by
    have h : cubicScalarCoefficient (n + 1) (cubicHom (n + 2) (strandIncl x)).val =
        cubicScalarCoefficient n (cubicHom (n + 1) x).val := by
      rw [cubicHom_strandIncl, cubicScalarCoefficient_cubicIncl]
    rw [cubicTrace_apply, cubicTrace_apply]
    -- Restate the indices `n + 2 - 1` and `n + 1 - 1` as `n + 1` and `n`.
    change _ * cubicScalarCoefficient (n + 1) _ = _ * (_ * cubicScalarCoefficient n _)
    rw [h]
    ring
  map_strandIncl_mul_e_last n x := by
    have h : cubicScalarCoefficient (n + 1)
        ((cubicHom (n + 2) (strandIncl x * e (Real.sqrt 3 : ℂ) (Fin.last n))).val) =
          (Real.sqrt 3 : ℂ) * ((3 : ℂ)⁻¹ * cubicScalarCoefficient n (cubicHom (n + 1) x).val) := by
      rw [map_mul, Subalgebra.coe_mul, cubicHom_strandIncl, coe_cubicHom_e, mul_smul_comm,
        map_smul, smul_eq_mul]
      -- The last projection is indexed by `Fin (n + 2 - 1)`, which is `Fin (n + 1)`.
      exact congrArg _ (cubicScalarCoefficient_cubicIncl_mul_cubicProjection_last _)
    rw [cubicTrace_apply, cubicTrace_apply]
    -- Restate the indices `n + 2 - 1` and `n + 1 - 1` as `n + 1` and `n`.
    change _ * cubicScalarCoefficient (n + 1) _ = _ * cubicScalarCoefficient n _
    rw [h, pow_succ]
    linear_combination (norm := skip) (Real.sqrt 3 : ℂ) ^ (n + 1) * (3 : ℂ)⁻¹ *
      cubicScalarCoefficient n (cubicHom (n + 1) x).val * Complex.mul_self_ofReal_sqrt zero_le_three
    push_cast
    ring

namespace IsMarkovTrace

variable {tr : ∀ n : ℕ, TemperleyLieb ℂ (Real.sqrt 3 : ℂ) n →ₗ[ℂ] ℂ}

/-- Every Markov trace on `TemperleyLieb ℂ (√3 : ℂ)` coincides with `cubicTrace`. -/
theorem eq_cubicTrace (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) : tr = cubicTrace :=
  htr.unique isMarkovTrace_cubicTrace

/-- **The Markov trace at `δ = √3` through the cubic quantum torus**: for every Markov trace `tr`,
`tr m x = (√3) ^ m * s_(m-1)(cubicHom m x)`. -/
theorem apply_eq_mul_cubicScalarCoefficient_cubicHom
    (htr : IsMarkovTrace ℂ (Real.sqrt 3 : ℂ) tr) (m : ℕ)
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    tr m x = (Real.sqrt 3 : ℂ) ^ m * cubicScalarCoefficient (m - 1) (cubicHom m x) := by
  rw [htr.eq_cubicTrace, cubicTrace_apply]

end IsMarkovTrace

/-- Specialization of `IsMarkovTrace.apply_eq_mul_cubicScalarCoefficient_cubicHom` to the
spin-model `markovTrace` at any unit `q : ℂˣ` with `(√3 : ℂ) = -(q + q⁻¹)`. -/
theorem markovTrace_eq_mul_cubicScalarCoefficient_cubicHom (q : ℂˣ)
    (hq : (Real.sqrt 3 : ℂ) = -((q : ℂ) + ((q⁻¹ : ℂˣ) : ℂ))) {m : ℕ}
    (x : TemperleyLieb ℂ (Real.sqrt 3 : ℂ) m) :
    markovTrace q hq x =
      (Real.sqrt 3 : ℂ) ^ m * cubicScalarCoefficient (m - 1) (cubicHom m x) :=
  (isMarkovTrace_markovTrace q hq).apply_eq_mul_cubicScalarCoefficient_cubicHom m x

end MarkovTrace

end TauCeti.TemperleyLieb
