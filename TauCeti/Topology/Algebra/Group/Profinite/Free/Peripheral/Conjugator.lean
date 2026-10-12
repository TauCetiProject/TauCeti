/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.Peripheral.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Heisenberg

/-!
# The peripheral conjugators cannot all coincide

Let `F` be a free pro-`p` group of rank `r ≥ 2` with basis `x_0, …, x_{r-1}` and cusp
`z = (x_0 ⋯ x_{r-1})⁻¹`. The peripheral-power theorem
(`TauCeti.Peripheral.exists_peripheralAut`) produces, for every unit `u ∈ ℤ_pˣ`, an automorphism
`φ` with `φ (x i) = (c i)⁻¹ * x i ^ u * c i` and `φ z = d⁻¹ * z ^ u * d`, where `^ u` is the
`p`-adic power. This file shows that for every `u ∈ ℤ_p` other than `0` and `1`, in particular
for every unit `u ≠ 1`, no endomorphism `φ` of `F` satisfies these equations with the `r + 1`
conjugators `c 0, …, c (r-1), d` all equal.

A common conjugator `g` would make `ψ := g * φ (·) * g⁻¹` carry every `x_i` to `x_i ^ u` and the
cusp to `z ^ u` on the nose, so `x_0 ^ u ⋯ x_{r-1} ^ u = (x_0 ⋯ x_{r-1}) ^ u`. That identity
fails: map `F` to the Heisenberg group over `ℤ_p` by `x_0 ↦ a = (1, 0, 0)`, `x_1 ↦ b = (0, 1, 0)`
and `x_i ↦ 1` for `i ≥ 2`. By the power formula `TauCeti.HeisenbergGroup.padicPow_eq` the
central coordinates of `a ^ u * b ^ u` and `(a * b) ^ u` are `u ^ 2` and `u + (u choose 2)`, which
differ by `u choose 2 = u (u - 1) / 2 ≠ 0`. The same Heisenberg detection argument shows, in
rank at least three, that the diagonal power map is not peripheral
(`TauCeti.Peripheral.not_isConj_diagonalPow`).

In rank at least two the conjugators of a peripheral automorphism are therefore genuinely
independent data, and the existence theorem cannot be strengthened to a single conjugator.

## Main results

* `TauCeti.Peripheral.padicPow_prod_basis_ne`: for `r ≥ 2` and `u ≠ 0, 1`,
  `(x_0 ⋯ x_{r-1}) ^ u ≠ x_0 ^ u ⋯ x_{r-1} ^ u`.
* `TauCeti.Peripheral.apply_cusp_ne_padicPow_of_apply_basis_eq_padicPow`: an endomorphism
  sending every `x_i` to `x_i ^ u` does not send the cusp to `z ^ u`.
* `TauCeti.Peripheral.exists_ne_of_apply_eq_conj`: the conjugators of an endomorphism carrying
  each element of the peripheral tuple to a conjugate of its `u`-th power are not all equal.

## References

* Y. Ihara, "Braids, Galois groups, and some arithmetic functions", Proc. ICM Kyoto 1990,
  99–120, for the normalization `x ↦ x ^ λ`, `y ↦ f⁻¹ y ^ λ f` of a peripheral automorphism of a
  free pro-`p` group of rank two, in which the conjugator `f` cannot be removed.
-/

public section

namespace TauCeti

namespace Peripheral

variable {p : ℕ} [Fact p.Prime] {F : Type*} [Group F] [TopologicalSpace F]
  [IsTopologicalGroup F] [CompactSpace F] [TotallyDisconnectedSpace F]

/-- **The power of the product is not the product of the powers.** For a free pro-`p` group of
rank at least two and `u ∈ ℤ_p` other than `0` and `1`, the `p`-adic power
`(x_0 ⋯ x_{r-1}) ^ u` of the ordered product of the basis differs from the ordered product
`x_0 ^ u ⋯ x_{r-1} ^ u` of the powers. -/
theorem padicPow_prod_basis_ne {n : ℕ} (hF : IsProP p F) (e : F ≃ₜ* freeProP p (Fin (n + 2)))
    {u : ℤ_[p]} (hu₀ : u ≠ 0) (hu₁ : u ≠ 1) :
    hF.padicPow (List.ofFn (basis e)).prod u ≠
      (List.ofFn fun i ↦ hF.padicPow (basis e i) u).prod := by
  intro heq
  -- Map `F` to the Heisenberg group over `ℤ_p`, sending `x_0, x_1` to the non-commuting
  -- elements `a`, `b` and the remaining basis elements to `1`.
  have hH := HeisenbergGroup.isProP_padicInt p
  let a : HeisenbergGroup ℤ_[p] := ⟨1, 0, 0⟩
  let b : HeisenbergGroup ℤ_[p] := ⟨0, 1, 0⟩
  let w : Fin (n + 2) → HeisenbergGroup ℤ_[p] := Fin.cons a (Fin.cons b 1)
  let f : F →ₜ* HeisenbergGroup ℤ_[p] :=
    (freeProP.lift hH w).comp (e : F →ₜ* freeProP p (Fin (n + 2)))
  have hf : ∀ i, f (basis e i) = w i := fun i ↦ by
    simp [f, ContinuousMonoidHom.comp_toFun]
  have hfpow : ∀ y, f (hF.padicPow y u) = hH.padicPow (f y) u := fun y ↦
    hF.map_padicPow hH (f : F →* HeisenbergGroup ℤ_[p]) f.continuous _ _
  have hmap := congrArg f heq
  rw [hfpow, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn, Function.comp_def,
    Function.comp_def] at hmap
  simp only [hfpow, hf, w, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, Pi.one_apply,
    hH.one_padicPow, List.ofFn_const, List.prod_cons, List.prod_replicate, one_pow,
    mul_one] at hmap
  -- The central coordinates of `(a b) ^ u` and `a ^ u * b ^ u` are `u + (u choose 2)` and `u * u`.
  have hz : u + Ring.choose u 2 = u * u := by
    simpa [a, b, HeisenbergGroup.padicPow_eq] using congrArg HeisenbergGroup.z hmap
  -- `2 * (u choose 2) = u * (u - 1)`, so `u choose 2 = u * u - u` would force `u (u - 1) = 0`.
  have hchoose : u * (u - 1) = 2 * Ring.choose u 2 := by
    simpa [descPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_X,
      Polynomial.smeval_sub, Polynomial.smeval_one] using
      Ring.descPochhammer_eq_factorial_smul_choose u 2
  have : u * (u - 1) = 0 := by linear_combination -hchoose - 2 * hz
  simp [sub_eq_zero, hu₀, hu₁] at this

variable {M : Type*} [FunLike M F F] [MonoidHomClass M F F]

/-- **No endomorphism is the `u`-th power on the whole peripheral tuple.** For a free pro-`p`
group of rank at least two and `u ∈ ℤ_p` other than `0` and `1`, an endomorphism `φ` sending every
basis element `x_i` to `x_i ^ u` does not send the cusp `z` to `z ^ u`. -/
theorem apply_cusp_ne_padicPow_of_apply_basis_eq_padicPow {n : ℕ} (hF : IsProP p F)
    (e : F ≃ₜ* freeProP p (Fin (n + 2))) {u : ℤ_[p]} (hu₀ : u ≠ 0) (hu₁ : u ≠ 1) (φ : M)
    (hφ : ∀ i, φ (basis e i) = hF.padicPow (basis e i) u) :
    φ (cusp (basis e)) ≠ hF.padicPow (cusp (basis e)) u := by
  intro hcusp
  rw [map_cusp, cusp_def, cusp_def, hF.inv_padicPow, inv_inj] at hcusp
  simp only [Function.comp_def, hφ] at hcusp
  exact padicPow_prod_basis_ne hF e hu₀ hu₁ hcusp.symm

/-- **The peripheral conjugators are not all equal.** For a free pro-`p` group of rank at least
two and `u ∈ ℤ_p` other than `0` and `1`, if an endomorphism `φ` satisfies
`φ (x i) = (c i)⁻¹ * x i ^ u * c i` for every basis element and `φ z = d⁻¹ * z ^ u * d` on the
cusp, then some `c i` differs from `d`. -/
theorem exists_ne_of_apply_eq_conj {n : ℕ} (hF : IsProP p F)
    (e : F ≃ₜ* freeProP p (Fin (n + 2))) {u : ℤ_[p]} (hu₀ : u ≠ 0) (hu₁ : u ≠ 1) (φ : M)
    {c : Fin (n + 2) → F} {d : F}
    (hc : ∀ i, φ (basis e i) = (c i)⁻¹ * hF.padicPow (basis e i) u * c i)
    (hd : φ (cusp (basis e)) = d⁻¹ * hF.padicPow (cusp (basis e)) u * d) :
    ∃ i, c i ≠ d := by
  by_contra! h
  -- Conjugating `φ` by the common conjugator `d` gives the `u`-th power on the peripheral tuple.
  let ψ : F →* F := (MulAut.conj d : F →* F).comp (φ : F →* F)
  refine apply_cusp_ne_padicPow_of_apply_basis_eq_padicPow hF e hu₀ hu₁ ψ (fun i ↦ ?_) ?_
  · simp [ψ, hc, h]
    group
  · simp [ψ, hd, -map_cusp]
    group

end Peripheral

end TauCeti
