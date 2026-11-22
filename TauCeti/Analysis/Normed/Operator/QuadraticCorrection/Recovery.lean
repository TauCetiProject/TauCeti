/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The recovery estimate of a fast–slow reduction

A gluing construction produces a solution of an equation `S(x) = 0` near an approximate
solution, and the quadratic correction of
`TauCeti.Analysis.Normed.Operator.QuadraticCorrection.Basic` shows that it is the only one in a
ball of some radius `γ`. To know that *every* actual solution is the constructed one, a separate
**recovery estimate** places each actual solution within `K_rec ε` of the approximate solution,
where `ε` is the residual of the approximate solution; then `K_rec ε < γ` finishes the argument
(`TauCeti.eventually_exists_continuous_forall_add_add_eq_zero_of_norm_le_mul`,
`TauCeti.IsNewtonWitness`). This file proves the recovery estimate in the form used for a
Lyapunov–Schmidt reduction, where the linearization of `S` is invertible only on a fast block and
the remaining slow directions are controlled by a reduced equation.

The unknown `x = (σ, f)` has a slow component `σ : E_C` and a fast component `f : E_F`, and the
equation is split by two maps `P_F : Y → Y_F` and `P_C : Y → Y_C` into its fast and slow parts.
On a comparison neighbourhood `U ⊆ E_C × E_F` assume:

* **a fast graph** `g : E_C → E_F` with **fast stability**
  `‖f - g σ‖ ≤ K_F ‖P_F S(σ, f)‖`, so that the fast part of the equation, solved exactly on the
  graph, controls the distance to it;
* **slow sensitivity to the fast variable**:
  `‖P_C S(σ, f) - P_C S(σ, g σ)‖ ≤ K_CF ‖f - g σ‖`;
* **a Lipschitz graph**: `‖g σ - g σ'‖ ≤ K_graph ‖σ - σ'‖`;
* **slow stability** of the reduced map `G(σ) = h⁻¹ P_C S(σ, g σ)`, for a scale `h > 0`:
  `‖σ - σ'‖ ≤ C_S ‖G σ - G σ'‖`.

If `y ∈ U` solves both projected equations, `P_F S(y) = 0 = P_C S(y)`, and `x ∈ U` has
projected residuals `‖P_F S(x)‖ ≤ K_PF ε` and `‖P_C S(x)‖ ≤ K_PC ε`, then
(`TauCeti.norm_fst_sub_le_mul_of_fastSlow`, `TauCeti.norm_fst_sub_add_norm_snd_sub_le_of_fastSlow`)

`‖σ_x - σ_y‖ ≤ C_S K_G ε`,  `‖σ_x - σ_y‖ + ‖f_x - f_y‖ ≤ ((1 + K_graph) C_S K_G + K_F K_PF) ε`,

with `K_G = h⁻¹ (K_PC + K_CF K_F K_PF)`, the bound on the reduced map at `σ_x`. Measured in a
norm on the product with `‖(σ, f)‖_E ≤ T_E (‖σ‖ + ‖f‖)`, this is the recovery estimate

`‖x - y‖_E ≤ K_rec ε`,  `K_rec = T_E ((1 + K_graph) C_S K_G + K_F K_PF)`

(`TauCeti.norm_sub_le_mul_of_fastSlow`). Typically `P_F` and `P_C` are additive projections of
norms `K_PF` and `K_PC` that both vanish on an obstruction term `o`, and the residual is
`‖S(x) - o‖ ≤ ε` (`TauCeti.norm_sub_le_mul_of_fastSlow_of_norm_sub_le`). No linearity, no
completeness and no differentiability enter: the estimate is a chain of triangle inequalities,
and the constants are the coarse stability constants of the reduction, not the norm of a fine
inverse.

The fast constants usually come from the quadratic correction: when the fast part of the equation
at `σ` reads `e σ + D σ f + N σ f = 0`, with right inverse of norm `C` and quadratic constant `L`
on a ball of radius `r` with `C L r ≤ 1 / 2`, fast stability holds with `K_F = 2 C`
(`TauCeti.norm_sub_le_two_mul_mul_norm_add_add`), and the graph is Lipschitz with twice the
Lipschitz constant of `σ ↦ Q σ (e σ + N σ z)` (`TauCeti.norm_sub_le_two_mul_norm_apply_sub_apply`).

In gluing constructions every constant depends on the small scale `h` with a polynomial rate.
If `T_E`, `K_graph`, `C_S`, `K_PC`, `K_CF`, `K_F` and `K_PF` are `O(h^(-t))`, `O(h^(-g))`,
`O(h^(-c))`, `O(h^(-p))`, `O(h^(-k))`, `O(h^(-f))` and `O(h^(-q))` as `h → 0⁺`, then
`K_rec = O(h^(-b))` for every `b` with

`t + max g 0 + c + 1 + p ≤ b`,  `t + max g 0 + c + 1 + k + f + q ≤ b`,  `t + f + q ≤ b`

(`TauCeti.isBigO_recoveryConstant`), which is the form in which the recovery loss `b` enters the
exponent conditions of `TauCeti.eventually_forall_isNewtonWitness`.

## Main results

* `TauCeti.norm_fst_sub_le_mul_of_fastSlow`: the slow distance is at most `C_S K_G ε`.
* `TauCeti.norm_fst_sub_add_norm_snd_sub_le_of_fastSlow`: the slow and fast distances together.
* `TauCeti.norm_sub_le_mul_of_fastSlow`: the recovery estimate `‖x - y‖_E ≤ K_rec ε`.
* `TauCeti.norm_sub_le_mul_of_fastSlow_of_norm_sub_le`: the same for a residual measured up to an
  obstruction term killed by both projections.
* `TauCeti.isBigO_recoveryConstant`: the power law of `K_rec`.

## References

* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

open Asymptotics Filter Set
open scoped Topology

namespace TauCeti

section Estimate

variable {EC EF Y YF YC : Type*} [SeminormedAddCommGroup EC] [SeminormedAddCommGroup EF]
  [SeminormedAddCommGroup YF] [SeminormedAddCommGroup YC]
  {S : EC × EF → Y} {PF : Y → YF} {PC : Y → YC} {g : EC → EF} {U : Set (EC × EF)}
  {KF KCF Kgraph CS h KPF KPC ε : ℝ}
  (hfast : ∀ x ∈ U, ‖x.2 - g x.1‖ ≤ KF * ‖PF (S x)‖)
  (hCF : ∀ x ∈ U, ‖PC (S x) - PC (S (x.1, g x.1))‖ ≤ KCF * ‖x.2 - g x.1‖)
  (hslow : ∀ x ∈ U, ∀ y ∈ U,
    ‖x.1 - y.1‖ ≤ CS * (h⁻¹ * ‖PC (S (x.1, g x.1)) - PC (S (y.1, g y.1))‖))
  {x y : EC × EF} (hx : x ∈ U) (hy : y ∈ U) (hxF : ‖PF (S x)‖ ≤ KPF * ε)
  (hxC : ‖PC (S x)‖ ≤ KPC * ε) (hyF : PF (S y) = 0) (hyC : PC (S y) = 0)
include hfast hCF hslow hx hy hxF hxC hyF hyC

omit [SeminormedAddCommGroup EC] hCF hslow hx hxF hxC hyC in
/-- At a solution `y` of both projected equations, fast stability puts `y` on the fast graph:
`‖f_y - g σ_y‖ = 0`. -/
private lemma norm_snd_sub_eq_zero_of_fastSlow : ‖y.2 - g y.1‖ = 0 :=
  le_antisymm ((hfast y hy).trans (by rw [hyF, norm_zero, mul_zero])) (norm_nonneg _)

omit [SeminormedAddCommGroup EC] hslow hx hxF hxC in
/-- At a solution `y` of both projected equations, the slow part of the equation also vanishes at
the graph point `(σ_y, g σ_y)`. -/
private lemma norm_apply_graph_eq_zero_of_fastSlow :
    ‖PC (S (y.1, g y.1))‖ = 0 := by
  have h0 := norm_snd_sub_eq_zero_of_fastSlow hfast hy hyF
  have h := hCF y hy
  rw [h0, mul_zero, hyC, zero_sub, norm_neg] at h
  exact le_antisymm h (norm_nonneg _)

omit [SeminormedAddCommGroup EC] hslow hy hyF hyC in
/-- At a point `x` with small projected residuals, the reduced map `G = h⁻¹ P_C S(·, g ·)` is
bounded by `K_G ε`, `K_G = h⁻¹ (K_PC + K_CF K_F K_PF)`. -/
private lemma inv_mul_norm_apply_graph_le_of_fastSlow (hKF : 0 ≤ KF) (hKCF : 0 ≤ KCF)
    (hh : 0 ≤ h) : h⁻¹ * ‖PC (S (x.1, g x.1))‖ ≤ h⁻¹ * (KPC + KCF * KF * KPF) * ε := by
  have hfx : KCF * ‖x.2 - g x.1‖ ≤ KCF * KF * KPF * ε := by
    calc KCF * ‖x.2 - g x.1‖ ≤ KCF * (KF * ‖PF (S x)‖) := by gcongr; exact hfast x hx
      _ ≤ KCF * (KF * (KPF * ε)) := by gcongr
      _ = KCF * KF * KPF * ε := by ring
  have hG : ‖PC (S (x.1, g x.1))‖ ≤ (KPC + KCF * KF * KPF) * ε := by
    calc ‖PC (S (x.1, g x.1))‖ ≤ ‖PC (S x)‖ + ‖PC (S x) - PC (S (x.1, g x.1))‖ :=
          norm_le_norm_add_norm_sub _ _
      _ ≤ KPC * ε + KCF * KF * KPF * ε := add_le_add hxC ((hCF x hx).trans hfx)
      _ = (KPC + KCF * KF * KPF) * ε := by ring
  calc h⁻¹ * ‖PC (S (x.1, g x.1))‖ ≤ h⁻¹ * ((KPC + KCF * KF * KPF) * ε) := by gcongr
    _ = h⁻¹ * (KPC + KCF * KF * KPF) * ε := by ring

/-- **Slow recovery.** In a fast–slow reduction with fast stability constant `K_F`, slow
sensitivity `K_CF` to the fast variable and slow stability constant `C_S` for the reduced map
`G(σ) = h⁻¹ P_C S(σ, g σ)` on a neighbourhood `U`, let `y ∈ U` solve both projected equations and
let `x ∈ U` have projected residuals `‖P_F S(x)‖ ≤ K_PF ε` and `‖P_C S(x)‖ ≤ K_PC ε`. Then the slow
components satisfy `‖σ_x - σ_y‖ ≤ C_S K_G ε` with `K_G = h⁻¹ (K_PC + K_CF K_F K_PF)`. -/
theorem norm_fst_sub_le_mul_of_fastSlow (hKF : 0 ≤ KF) (hKCF : 0 ≤ KCF) (hCS : 0 ≤ CS)
    (hh : 0 ≤ h) : ‖x.1 - y.1‖ ≤ CS * (h⁻¹ * (KPC + KCF * KF * KPF)) * ε := by
  have hy0 := norm_apply_graph_eq_zero_of_fastSlow hfast hCF hy hyF hyC
  have hG := inv_mul_norm_apply_graph_le_of_fastSlow hfast hCF hx hxF hxC hKF hKCF hh
  calc ‖x.1 - y.1‖
      ≤ CS * (h⁻¹ * ‖PC (S (x.1, g x.1)) - PC (S (y.1, g y.1))‖) := hslow x hx y hy
    _ ≤ CS * (h⁻¹ * (‖PC (S (x.1, g x.1))‖ + ‖PC (S (y.1, g y.1))‖)) := by
        gcongr; exact norm_sub_le _ _
    _ = CS * (h⁻¹ * ‖PC (S (x.1, g x.1))‖) := by rw [hy0, add_zero]
    _ ≤ CS * (h⁻¹ * (KPC + KCF * KF * KPF) * ε) := by gcongr
    _ = CS * (h⁻¹ * (KPC + KCF * KF * KPF)) * ε := by ring

variable (hgraph : ∀ x ∈ U, ∀ y ∈ U, ‖g x.1 - g y.1‖ ≤ Kgraph * ‖x.1 - y.1‖)
include hgraph

/-- **Slow and fast recovery.** In the situation of `TauCeti.norm_fst_sub_le_mul_of_fastSlow`, if
moreover the fast graph is `K_graph`-Lipschitz on `U`, then
`‖σ_x - σ_y‖ + ‖f_x - f_y‖ ≤ ((1 + K_graph) C_S K_G + K_F K_PF) ε`, with
`K_G = h⁻¹ (K_PC + K_CF K_F K_PF)`. -/
theorem norm_fst_sub_add_norm_snd_sub_le_of_fastSlow (hKF : 0 ≤ KF) (hKCF : 0 ≤ KCF)
    (hKgraph : 0 ≤ Kgraph) (hCS : 0 ≤ CS) (hh : 0 ≤ h) :
    ‖x.1 - y.1‖ + ‖x.2 - y.2‖ ≤
      ((1 + Kgraph) * CS * (h⁻¹ * (KPC + KCF * KF * KPF)) + KF * KPF) * ε := by
  have hσ := norm_fst_sub_le_mul_of_fastSlow hfast hCF hslow hx hy hxF hxC hyF hyC hKF hKCF hCS hh
  have hy0 := norm_snd_sub_eq_zero_of_fastSlow hfast hy hyF
  -- The fast distance splits along the graph: from `f_x` to `g σ_x`, to `g σ_y`, to `f_y`.
  have hf : ‖x.2 - y.2‖ ≤ KF * KPF * ε + Kgraph * ‖x.1 - y.1‖ := by
    calc ‖x.2 - y.2‖ ≤ ‖x.2 - g x.1‖ + ‖g x.1 - g y.1‖ + ‖g y.1 - y.2‖ := by
          linarith [norm_sub_le_norm_sub_add_norm_sub x.2 (g y.1) y.2,
            norm_sub_le_norm_sub_add_norm_sub x.2 (g x.1) (g y.1)]
      _ ≤ KF * (KPF * ε) + Kgraph * ‖x.1 - y.1‖ + 0 := by
          gcongr
          · exact (hfast x hx).trans (by gcongr)
          · exact hgraph x hx y hy
          · rw [norm_sub_rev]; exact hy0.le
      _ = KF * KPF * ε + Kgraph * ‖x.1 - y.1‖ := by ring
  calc ‖x.1 - y.1‖ + ‖x.2 - y.2‖ ≤ (1 + Kgraph) * ‖x.1 - y.1‖ + KF * KPF * ε := by linarith
    _ ≤ (1 + Kgraph) * (CS * (h⁻¹ * (KPC + KCF * KF * KPF)) * ε) + KF * KPF * ε := by gcongr
    _ = ((1 + Kgraph) * CS * (h⁻¹ * (KPC + KCF * KF * KPF)) + KF * KPF) * ε := by ring

/-- **The recovery estimate.** In the situation of
`TauCeti.norm_fst_sub_add_norm_snd_sub_le_of_fastSlow`, let `ι : E_C × E_F →+ E` identify the
product with a space whose norm satisfies `‖ι (σ, f)‖ ≤ T_E (‖σ‖ + ‖f‖)`. Then
`‖ι x - ι y‖ ≤ K_rec ε` with `K_rec = T_E ((1 + K_graph) C_S K_G + K_F K_PF)` and
`K_G = h⁻¹ (K_PC + K_CF K_F K_PF)`. -/
theorem norm_sub_le_mul_of_fastSlow {E : Type*} [SeminormedAddCommGroup E] {ι : EC × EF →+ E}
    {TE : ℝ} (hι : ∀ z, ‖ι z‖ ≤ TE * (‖z.1‖ + ‖z.2‖)) (hTE : 0 ≤ TE) (hKF : 0 ≤ KF)
    (hKCF : 0 ≤ KCF) (hKgraph : 0 ≤ Kgraph) (hCS : 0 ≤ CS) (hh : 0 ≤ h) :
    ‖ι x - ι y‖ ≤
      TE * ((1 + Kgraph) * CS * (h⁻¹ * (KPC + KCF * KF * KPF)) + KF * KPF) * ε := by
  have hd := norm_fst_sub_add_norm_snd_sub_le_of_fastSlow hfast hCF hslow hx hy hxF hxC hyF hyC
    hgraph hKF hKCF hKgraph hCS hh
  calc ‖ι x - ι y‖ = ‖ι (x - y)‖ := by rw [map_sub]
    _ ≤ TE * (‖x.1 - y.1‖ + ‖x.2 - y.2‖) := hι (x - y)
    _ ≤ TE * (((1 + Kgraph) * CS * (h⁻¹ * (KPC + KCF * KF * KPF)) + KF * KPF) * ε) := by gcongr
    _ = _ := by ring

end Estimate

/-- **The recovery estimate up to an obstruction.** Let `P_F : Y →+ Y_F` and `P_C : Y →+ Y_C` be
additive projections of norms at most `K_PF` and `K_PC` that both vanish on an obstruction term
`o`, and let `x` have residual `‖S(x) - o‖ ≤ ε`. In the situation of
`TauCeti.norm_sub_le_mul_of_fastSlow`, `‖ι x - ι y‖ ≤ K_rec ε` with
`K_rec = T_E ((1 + K_graph) C_S K_G + K_F K_PF)` and `K_G = h⁻¹ (K_PC + K_CF K_F K_PF)`. -/
theorem norm_sub_le_mul_of_fastSlow_of_norm_sub_le {EC EF Y YF YC E : Type*}
    [SeminormedAddCommGroup EC] [SeminormedAddCommGroup EF] [SeminormedAddCommGroup Y]
    [SeminormedAddCommGroup YF] [SeminormedAddCommGroup YC] [SeminormedAddCommGroup E]
    {S : EC × EF → Y} {PF : Y →+ YF} {PC : Y →+ YC} {g : EC → EF} {U : Set (EC × EF)}
    {ι : EC × EF →+ E} {KF KCF Kgraph CS h KPF KPC TE ε : ℝ} {o : Y}
    (hPF : ∀ z, ‖PF z‖ ≤ KPF * ‖z‖) (hPC : ∀ z, ‖PC z‖ ≤ KPC * ‖z‖) (hPFo : PF o = 0)
    (hPCo : PC o = 0) (hfast : ∀ x ∈ U, ‖x.2 - g x.1‖ ≤ KF * ‖PF (S x)‖)
    (hCF : ∀ x ∈ U, ‖PC (S x) - PC (S (x.1, g x.1))‖ ≤ KCF * ‖x.2 - g x.1‖)
    (hslow : ∀ x ∈ U, ∀ y ∈ U,
      ‖x.1 - y.1‖ ≤ CS * (h⁻¹ * ‖PC (S (x.1, g x.1)) - PC (S (y.1, g y.1))‖))
    (hgraph : ∀ x ∈ U, ∀ y ∈ U, ‖g x.1 - g y.1‖ ≤ Kgraph * ‖x.1 - y.1‖)
    (hι : ∀ z, ‖ι z‖ ≤ TE * (‖z.1‖ + ‖z.2‖)) {x y : EC × EF} (hx : x ∈ U) (hy : y ∈ U)
    (hxε : ‖S x - o‖ ≤ ε) (hyF : PF (S y) = 0) (hyC : PC (S y) = 0) (hKPF : 0 ≤ KPF)
    (hKPC : 0 ≤ KPC) (hTE : 0 ≤ TE) (hKF : 0 ≤ KF) (hKCF : 0 ≤ KCF) (hKgraph : 0 ≤ Kgraph)
    (hCS : 0 ≤ CS) (hh : 0 ≤ h) :
    ‖ι x - ι y‖ ≤
      TE * ((1 + Kgraph) * CS * (h⁻¹ * (KPC + KCF * KF * KPF)) + KF * KPF) * ε := by
  have hxF : ‖PF (S x)‖ ≤ KPF * ε := by
    rw [← sub_zero (PF (S x)), ← hPFo, ← map_sub]
    exact (hPF _).trans (by gcongr)
  have hxC : ‖PC (S x)‖ ≤ KPC * ε := by
    rw [← sub_zero (PC (S x)), ← hPCo, ← map_sub]
    exact (hPC _).trans (by gcongr)
  exact norm_sub_le_mul_of_fastSlow hfast hCF hslow hx hy hxF hxC hyF hyC hgraph hι hTE hKF hKCF
    hKgraph hCS hh

/-- **The power law of the recovery constant.** If, as `h → 0⁺`, the constants of a fast–slow
reduction satisfy `T_E = O(h^(-t))`, `K_graph = O(h^(-g))`, `C_S = O(h^(-c))`, `K_PC = O(h^(-p))`,
`K_CF = O(h^(-k))`, `K_F = O(h^(-f))` and `K_PF = O(h^(-q))`, then the recovery constant
`K_rec = T_E ((1 + K_graph) C_S h⁻¹ (K_PC + K_CF K_F K_PF) + K_F K_PF)` is `O(h^(-b))` for every
`b` with `t + max g 0 + c + 1 + p ≤ b`, `t + max g 0 + c + 1 + k + f + q ≤ b` and
`t + f + q ≤ b`. -/
theorem isBigO_recoveryConstant {TE Kgraph CS KPC KCF KF KPF : ℝ → ℝ} {t g c p k f q b : ℝ}
    (hTE : TE =O[𝓝[>] 0] fun h ↦ h ^ (-t)) (hKgraph : Kgraph =O[𝓝[>] 0] fun h ↦ h ^ (-g))
    (hCS : CS =O[𝓝[>] 0] fun h ↦ h ^ (-c)) (hKPC : KPC =O[𝓝[>] 0] fun h ↦ h ^ (-p))
    (hKCF : KCF =O[𝓝[>] 0] fun h ↦ h ^ (-k)) (hKF : KF =O[𝓝[>] 0] fun h ↦ h ^ (-f))
    (hKPF : KPF =O[𝓝[>] 0] fun h ↦ h ^ (-q)) (hb₁ : t + max g 0 + c + 1 + p ≤ b)
    (hb₂ : t + max g 0 + c + 1 + (k + f + q) ≤ b) (hb₃ : t + (f + q) ≤ b) :
    (fun h ↦ TE h * ((1 + Kgraph h) * CS h * (h⁻¹ * (KPC h + KCF h * KF h * KPF h)) +
      KF h * KPF h)) =O[𝓝[>] 0] fun h ↦ h ^ (-b) := by
  -- The exponent left for the bracket `K_PC + K_CF K_F K_PF` of `K_G`.
  set e := b - t - max g 0 - c - 1
  have hone : (fun _ : ℝ ↦ (1 : ℝ)) =O[𝓝[>] 0] fun h ↦ h ^ (-max g 0) :=
    ((isBigO_refl (fun h : ℝ ↦ h ^ (0 : ℝ)) _).congr_left fun h ↦ Real.rpow_zero h)
      |>.nhdsGT_zero_rpow_of_le (neg_nonpos.2 (le_max_right _ _))
  have h1g : (fun h ↦ 1 + Kgraph h) =O[𝓝[>] 0] fun h ↦ h ^ (-max g 0) :=
    hone.add (hKgraph.nhdsGT_zero_rpow_of_le (neg_le_neg (le_max_left _ _)))
  have hinv : (fun h : ℝ ↦ h⁻¹) =O[𝓝[>] 0] fun h ↦ h ^ (-1 : ℝ) :=
    (isBigO_refl (fun h : ℝ ↦ h ^ (-1 : ℝ)) _).congr_left fun h ↦ Real.rpow_neg_one h
  have hbr : (fun h ↦ KPC h + KCF h * KF h * KPF h) =O[𝓝[>] 0] fun h ↦ h ^ (-e) :=
    (hKPC.nhdsGT_zero_rpow_of_le (by linarith)).add
      ((hKCF.mul_nhdsGT_zero_rpow_of_isBigO_rpow hKF le_rfl).mul_nhdsGT_zero_rpow_of_isBigO_rpow
        hKPF (by linarith))
  have hslow : (fun h ↦ (1 + Kgraph h) * CS h * (h⁻¹ * (KPC h + KCF h * KF h * KPF h)))
      =O[𝓝[>] 0] fun h ↦ h ^ (-(b - t)) :=
    (h1g.mul_nhdsGT_zero_rpow_of_isBigO_rpow hCS le_rfl).mul_nhdsGT_zero_rpow_of_isBigO_rpow
      (hinv.mul_nhdsGT_zero_rpow_of_isBigO_rpow hbr le_rfl) (by linarith)
  have hfast : (fun h ↦ KF h * KPF h) =O[𝓝[>] 0] fun h ↦ h ^ (-(b - t)) :=
    hKF.mul_nhdsGT_zero_rpow_of_isBigO_rpow hKPF (by linarith)
  exact hTE.mul_nhdsGT_zero_rpow_of_isBigO_rpow (hslow.add hfast) (by linarith)

end TauCeti
