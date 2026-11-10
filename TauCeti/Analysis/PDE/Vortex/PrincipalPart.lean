/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Divisor
public import Mathlib.LinearAlgebra.Dimension.Finrank
import TauCeti.Analysis.Complex.Wirtinger.DolbeaultLemma
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Data.Multiset.Fintype
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Principal parts of holomorphic deformations of a plane vortex

In the coordinates of `TauCeti.Vortex.equation`, a field `x = (b₁, b₂, p, q)` has section
`α = 2 (p + i q)`, and the two holomorphicity rows of the vortex equation say `∂bar α = c α` with
`c = (b₂ - i b₁) / 2`. By the Dolbeault lemma on the plane there is a global solution `ν` of
`∂bar ν = c`, and every such `ν` is an integrating factor: `exp (-ν) α` is entire
(`TauCeti.Vortex.differentiable_exp_neg_mul_sectionValue`). This is the global similarity
principle `α = e^ν f`, `f` entire.

A variation `y = (δb, δα)` satisfying the holomorphicity rows of the linearized equation has
`∂bar δα = c δα + c(δb) α`, where `c(δb) = (δb₂ - i δb₁) / 2`
(`TauCeti.Vortex.conjWirtingerDeriv_apply_one_sectionValue_of_linearizedEquation_eq_zero`).
Solving `∂bar G = c(δb)` on the plane, the difference `δα - α G` satisfies the homogeneous
equation, so (`TauCeti.Vortex.exists_sectionValue_eq_mul_add_exp_mul`)

`δα = α G + e^ν H`,  `G` of class `Cᵏ`,  `H` entire.

Hence `δα / α = G + H / f` is a `Cᵏ` function plus a meromorphic function whose poles lie at the
zeros of `α`, of order at most their multiplicities. At a zero `a` of multiplicity `n(a)` the
principal part of `δα / α` is recorded by the derivatives `H⁽ʲ⁾(a)`, `j < n(a)`:

* they do not depend on the decomposition
  (`TauCeti.Vortex.iteratedDeriv_eq_of_sectionValue_mul_add_exp_mul_eq`);
* they all vanish exactly when `δα = α η` for a function `η` of class `Cᵏ`, and already when
  `δα = α η` for a continuous `η` (`TauCeti.Vortex.tfae_exists_sectionValue_eq_mul`).

For a framed vortex of degree `m` the zeros of `α` have total multiplicity `m`, so these
derivatives form `m` complex numbers. Consequently a real vector space of such variations in which
every variation with `δα = α η`, `η` of class `Cᵏ`, is zero has real dimension at most `2 m`
(`TauCeti.Vortex.finiteDimensional_of_forall_sectionValue_eq_mul_eq_zero`,
`TauCeti.Vortex.finrank_le_two_mul_of_forall_sectionValue_eq_mul_eq_zero`). For the kernel of the
gauge-fixed operator `L_x` at a framed vortex, `2 m` is the real dimension of the tangent space of
the divisor space `Sym^m ℂ`; this is the upper bound in the identification of that kernel with the
tangent space, once kernel elements with divisible section variation are known to vanish.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* I. N. Vekua, *Generalized Analytic Functions*, Pergamon Press, 1962 (the similarity principle).
* T. M. Samols, *Vortex scattering*, Comm. Math. Phys. 145 (1992), 149–179 (the zero modes of a
  vortex through `δα / α`).
-/

public noncomputable section

open Complex Filter Topology
open scoped ContDiff

namespace TauCeti.Vortex

variable {x y : ℂ → EuclideanSpace ℝ (Fin 4)}

/-! ### The linearized Cauchy–Riemann equation and the integrating factor -/

/-- **The linearized holomorphicity rows as a Cauchy–Riemann equation.** If the variation `y`
satisfies the two holomorphicity rows of the linearized vortex equation at `x`, then
`∂bar δα = c δα + c(δb) α` with `c = (b₂ - i b₁) / 2` and `c(δb) = (δb₂ - i δb₁) / 2`. -/
theorem conjWirtingerDeriv_apply_one_sectionValue_of_linearizedEquation_eq_zero {z : ℂ}
    (hp : DifferentiableAt ℝ (fun w ↦ y w 2) z) (hq : DifferentiableAt ℝ (fun w ↦ y w 3) z)
    (h₁ : linearizedEquation x y z 1 = 0) (h₂ : linearizedEquation x y z 2 = 0) :
    conjWirtingerDeriv (sectionValue y) z 1 =
      ((x z 1 : ℂ) - I * x z 0) / 2 * sectionValue y z +
        ((y z 1 : ℂ) - I * y z 0) / 2 * sectionValue x z := by
  have hP := Complex.ofRealCLM.hasFDerivAt.comp z hp.hasFDerivAt
  have hQ := Complex.ofRealCLM.hasFDerivAt.comp z hq.hasFDerivAt
  have hA := (hP.fun_add (hQ.mul_const I)).const_mul (2 : ℂ)
  simp only [Function.comp_def, Complex.ofRealCLM_apply] at hA
  have hsec : sectionValue y = fun w ↦ 2 * ((y w 2 : ℂ) + (y w 3 : ℂ) * I) :=
    funext (sectionValue_apply y)
  rw [conjWirtingerDeriv_apply, hsec, hA.fderiv]
  rw [linearizedEquation_apply_one] at h₁
  rw [linearizedEquation_apply_two] at h₂
  simp only [sectionValue_apply]
  apply Complex.ext <;>
    simp [smul_eq_mul, Complex.ofRealCLM_apply] <;> linarith

/-- The coefficient `(b₂ - i b₁) / 2` is as regular as the connection. -/
private theorem contDiff_connectionCoeff {k : ℕ∞} (hb₁ : ContDiff ℝ k (fun w ↦ x w 0))
    (hb₂ : ContDiff ℝ k (fun w ↦ x w 1)) :
    ContDiff ℝ k fun w ↦ ((x w 1 : ℂ) - I * x w 0) / 2 :=
  ((ofRealCLM.contDiff.comp hb₂).sub (contDiff_const.mul (ofRealCLM.contDiff.comp hb₁))).div_const 2

/-- The holomorphicity rows say `∂bar α = c α` with `c = (b₂ - i b₁) / 2`. -/
private theorem conjWirtingerDeriv_apply_one_sectionValue {z : ℂ}
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z) (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (h₁ : equation x z 1 = 0) (h₂ : equation x z 2 = 0) :
    conjWirtingerDeriv (sectionValue x) z 1 =
      ((x z 1 : ℂ) - I * x z 0) / 2 * sectionValue x z := by
  have hsec : sectionValue x = fun w ↦ 2 * ((x w 2 : ℂ) + I * x w 3) :=
    funext fun w ↦ by rw [sectionValue_apply, mul_comm (x w 3 : ℂ) I]
  rw [hsec]
  exact conjWirtingerDeriv_apply_one_section_eq_mul hp hq h₁ h₂

/-- **The global similarity principle for a vortex section.** If `∂bar ν = (b₂ - i b₁) / 2` on the
plane, then `exp (-ν) α` is entire, so `α = e^ν f` with `f` entire. Such a `ν` exists, of class
`Cᵏ` when the connection is, by the Dolbeault lemma
`TauCeti.exists_contDiff_conjWirtingerDeriv_apply_one_eq`. -/
theorem differentiable_exp_neg_mul_sectionValue {ν : ℂ → ℂ}
    (hp : Differentiable ℝ (fun w ↦ x w 2)) (hq : Differentiable ℝ (fun w ↦ x w 3))
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2) :
    Differentiable ℂ fun w ↦ exp (-ν w) * sectionValue x w := fun w ↦
  differentiableAt_exp_neg_mul_of_conjWirtingerDeriv_apply_one_eq_mul
    (a := fun w ↦ ((x w 1 : ℂ) - I * x w 0) / 2) (hν w)
    (differentiableAt_sectionValue (hp w) (hq w)) (hνeq w)
    (conjWirtingerDeriv_apply_one_sectionValue (hp w) (hq w) (hhol w).1 (hhol w).2)

/-! ### The decomposition `δα = α G + e^ν H` -/

/-- **Decomposition of a holomorphic deformation.** Let `x` satisfy the holomorphicity rows, let
`∂bar ν = (b₂ - i b₁) / 2` on the plane, and let the variation `y`, with `Cᵏ` connection
coefficients (`k ≥ 1`) and differentiable section, satisfy the holomorphicity rows of the
linearized equation at `x`. Then `δα = α G + e^ν H` with `G` of class `Cᵏ` and `H` entire.
So `δα / α` is a `Cᵏ` function plus `H / f`, where `α = e^ν f`. -/
theorem exists_sectionValue_eq_mul_add_exp_mul {k : ℕ∞} (hk : 1 ≤ k) {ν : ℂ → ℂ}
    (hp : Differentiable ℝ (fun w ↦ x w 2)) (hq : Differentiable ℝ (fun w ↦ x w 3))
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    (hyb₁ : ContDiff ℝ k (fun w ↦ y w 0)) (hyb₂ : ContDiff ℝ k (fun w ↦ y w 1))
    (hyp : Differentiable ℝ (fun w ↦ y w 2)) (hyq : Differentiable ℝ (fun w ↦ y w 3))
    (hylin : ∀ w, linearizedEquation x y w 1 = 0 ∧ linearizedEquation x y w 2 = 0) :
    ∃ G : ℂ → ℂ, ContDiff ℝ k G ∧ ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
      ∀ z, sectionValue y z = sectionValue x z * G z + exp (ν z) * H z := by
  have hk0 : (k : WithTop ℕ∞) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hk))
  -- Solve `∂bar G = c(δb)` on the plane.
  obtain ⟨G, hG, hGeq⟩ :=
    exists_contDiff_conjWirtingerDeriv_apply_one_eq hk (contDiff_connectionCoeff hyb₁ hyb₂)
  have hGd := hG.differentiable hk0
  have hαd : Differentiable ℝ (sectionValue x) := fun w ↦
    differentiableAt_sectionValue (hp w) (hq w)
  have hδd : Differentiable ℝ (sectionValue y) := fun w ↦
    differentiableAt_sectionValue (hyp w) (hyq w)
  -- `F = δα - α G` solves the homogeneous equation `∂bar F = c F`.
  set F : ℂ → ℂ := sectionValue y - fun w ↦ sectionValue x w * G w with hF
  have hFd : Differentiable ℝ F := hδd.sub (hαd.mul hGd)
  have hFeq (w : ℂ) : conjWirtingerDeriv F w 1 = ((x w 1 : ℂ) - I * x w 0) / 2 * F w := by
    rw [hF, conjWirtingerDeriv_sub (g₂ := fun w ↦ sectionValue x w * G w) (hδd w)
        ((hαd w).mul (hGd w)),
      conjWirtingerDeriv_fun_mul (hαd w) (hGd w)]
    simp only [sub_apply, add_apply, smul_apply, smul_eq_mul, hGeq w,
      conjWirtingerDeriv_apply_one_sectionValue_of_linearizedEquation_eq_zero (hyp w) (hyq w)
        (hylin w).1 (hylin w).2,
      conjWirtingerDeriv_apply_one_sectionValue (hp w) (hq w) (hhol w).1 (hhol w).2]
    simp only [Pi.sub_apply]
    ring
  refine ⟨G, hG, fun w ↦ exp (-ν w) * F w, fun w ↦
    differentiableAt_exp_neg_mul_of_conjWirtingerDeriv_apply_one_eq_mul
      (a := fun w ↦ ((x w 1 : ℂ) - I * x w 0) / 2) (hν w) (hFd w) (hνeq w) (hFeq w), fun z ↦ ?_⟩
  rw [← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul, hF, Pi.sub_apply]
  ring

/-! ### The principal-part data -/

/-- **The principal-part data do not depend on the decomposition.** If
`α G₁ + e^ν H₁ = α G₂ + e^ν H₂` with `G₁`, `G₂`, `ν` continuous and `H₁`, `H₂` entire, then at
every `z` the derivatives of `H₁` and `H₂` of order below the zero multiplicity `n z` of `α`
agree. -/
theorem iteratedDeriv_eq_of_sectionValue_mul_add_exp_mul_eq {n : ℂ → ℕ}
    (hα : IsZeroMultiplicity (sectionValue x) n) {ν G₁ G₂ H₁ H₂ : ℂ → ℂ} (hν : Continuous ν)
    (hG₁ : Continuous G₁) (hG₂ : Continuous G₂) (hH₁ : Differentiable ℂ H₁)
    (hH₂ : Differentiable ℂ H₂)
    (h : ∀ z, sectionValue x z * G₁ z + exp (ν z) * H₁ z =
      sectionValue x z * G₂ z + exp (ν z) * H₂ z)
    (z : ℂ) {j : ℕ} (hj : j < n z) : iteratedDeriv j H₁ z = iteratedDeriv j H₂ z := by
  -- `H₁ - H₂ = α u` with `u = e^(-ν) (G₂ - G₁)` continuous, so it vanishes to order `n z`.
  have hord : (n z : ℕ∞) ≤ analyticOrderAt (H₁ - H₂) z :=
    hα.natCast_le_analyticOrderAt_of_eventually_eq_mul (u := fun w ↦ exp (-ν w) * (G₂ w - G₁ w))
      ((hH₁.sub hH₂).analyticAt z) (by fun_prop) (Eventually.of_forall fun w ↦ by
        have hexp : exp (-ν w) * exp (ν w) = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
        simp only [Pi.sub_apply]
        linear_combination exp (-ν w) * sub_eq_zero.2 (h w) - (H₁ w - H₂ w) * hexp)
  have hzero := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    ((hH₁.sub hH₂).analyticAt z)).1 hord j hj
  rwa [iteratedDeriv_sub ((hH₁.contDiff (n := j)).contDiffAt)
    ((hH₂.contDiff (n := j)).contDiffAt), sub_eq_zero] at hzero

/-- If `α G + e^ν H = 0` with `G`, `ν` continuous and `H` entire, then the derivatives of `H` of
order below the zero multiplicities of `α` vanish. -/
private theorem iteratedDeriv_eq_zero_of_sectionValue_mul_add_exp_mul_eq_zero {n : ℂ → ℕ}
    (hα : IsZeroMultiplicity (sectionValue x) n) {ν G H : ℂ → ℂ} (hν : Continuous ν)
    (hG : Continuous G) (hH : Differentiable ℂ H)
    (h : ∀ z, sectionValue x z * G z + exp (ν z) * H z = 0) (z : ℂ) {j : ℕ} (hj : j < n z) :
    iteratedDeriv j H z = 0 := by
  have := iteratedDeriv_eq_of_sectionValue_mul_add_exp_mul_eq (G₂ := fun _ ↦ 0) (H₂ := fun _ ↦ 0)
    hα hν hG continuous_const hH (differentiable_const 0) (fun w ↦ by rw [h w]; simp) z hj
  simpa using this

/-- **Divisibility of a holomorphic deformation by the section.** Let `x` have `Cᵏ` connection
coefficients (`k ≥ 1`) and differentiable section, satisfy the holomorphicity rows, and have
zero multiplicities `n`. For a decomposition
`δα = α G + e^ν H` with `G` and `ν` of class `Cᵏ` and `H` entire, the following are equivalent:
`δα = α η` for a function `η` of class `Cᵏ`; `δα = α η` for a continuous `η`; and the derivatives
`H⁽ʲ⁾(z)`, `j < n z`, vanish at every `z`. -/
theorem tfae_exists_sectionValue_eq_mul {k : ℕ∞} (hk : 1 ≤ k)
    (hb₁ : ContDiff ℝ k (fun w ↦ x w 0)) (hb₂ : ContDiff ℝ k (fun w ↦ x w 1))
    (hp : Differentiable ℝ (fun w ↦ x w 2)) (hq : Differentiable ℝ (fun w ↦ x w 3))
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    {n : ℂ → ℕ} (hα : IsZeroMultiplicity (sectionValue x) n) {ν G H : ℂ → ℂ}
    (hν : ContDiff ℝ k ν) (hG : ContDiff ℝ k G) (hH : Differentiable ℂ H)
    (hy : ∀ z, sectionValue y z = sectionValue x z * G z + exp (ν z) * H z) :
    [∃ η : ℂ → ℂ, ContDiff ℝ k η ∧ ∀ z, sectionValue y z = sectionValue x z * η z,
      ∃ η : ℂ → ℂ, Continuous η ∧ ∀ z, sectionValue y z = sectionValue x z * η z,
      ∀ z, ∀ j < n z, iteratedDeriv j H z = 0].TFAE := by
  tfae_have 1 → 2 := fun ⟨η, hη, hyη⟩ ↦ ⟨η, hη.continuous, hyη⟩
  tfae_have 2 → 3 := fun ⟨η, hη, hyη⟩ z j hj ↦
    iteratedDeriv_eq_zero_of_sectionValue_mul_add_exp_mul_eq_zero hα hν.continuous
      (hG.continuous.sub hη) hH (fun w ↦ by rw [Pi.sub_apply, mul_sub, ← hyη w, hy w]; ring) z hj
  tfae_have 3 → 1 := by
    intro hjet
    -- Local `Cᵏ` factorizations `α = (w - z) ^ n z * v_z` of the section.
    choose N v hv hv₀ hvf using fun z ↦
      exists_contDiffAt_sectionValue_eq_pow_mul hk hb₁ hb₂ hp hq hhol hα.exists_ne_zero z
    have hN : N = n := (isZeroMultiplicity_iff.2 fun z ↦
      ⟨v z, (hv z).continuousAt, hv₀ z, hvf z⟩).unique hα
    subst hN
    -- Near each `z`, `H = e^(-ν) α K_z` with `K_z` of class `Cᵏ` at `z`.
    have hloc (z : ℂ) : ∃ K : ℂ → ℂ, ContDiffAt ℝ k K z ∧
        ∀ᶠ w in 𝓝 z, H w = exp (-ν w) * sectionValue x w * K w :=
      exists_contDiffAt_eventually_eq_mul_of_natCast_le_analyticOrderAt (v := fun w ↦
          exp (-ν w) * v z w) (hH.analyticAt z)
        ((natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hH.analyticAt z)).2 (hjet z))
        (hν.contDiffAt.neg.cexp.mul (hv z)) (mul_ne_zero (exp_ne_zero _) (hv₀ z))
        (by filter_upwards [hvf z] with w hw; rw [hw]; ring)
    choose K hK hKH using hloc
    -- Near `z`, the only zero of `α` is `z`, and away from the zeros `K_z = e^ν H / α`.
    have hKeq (z : ℂ) : (fun w ↦ K w w) =ᶠ[𝓝 z] K z := by
      filter_upwards [hvf z, (hv z).continuousAt.eventually_ne (hv₀ z), hKH z] with w hw hw₀ hwK
      by_cases hwz : w = z
      · rw [hwz]
      have hαw : sectionValue x w ≠ 0 := by
        rw [hw]
        exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.2 hwz)) hw₀
      have hself := (hKH w).self_of_nhds
      rw [hwK] at hself
      exact (mul_left_cancel₀ (mul_ne_zero (exp_ne_zero _) hαw) hself).symm
    refine ⟨fun w ↦ G w + K w w, hG.add (contDiff_iff_contDiffAt.2 fun z ↦
      (hK z).congr_of_eventuallyEq (hKeq z)), fun z ↦ ?_⟩
    rw [hy z, (hKH z).self_of_nhds, ← mul_assoc, ← mul_assoc, ← exp_add, add_neg_cancel,
      exp_zero, one_mul]
    ring
  tfae_finish

/-! ### The real dimension bound -/

/-- The principal-part data give an injective real-linear map into `ι → ℂ` with `ι` of
cardinality `m`. -/
private theorem exists_injective_linearMap {k : ℕ∞} (hk : 1 ≤ k) {m : ℕ}
    (hb₁ : ContDiff ℝ k (fun w ↦ x w 0)) (hb₂ : ContDiff ℝ k (fun w ↦ x w 1))
    (hp : Differentiable ℝ (fun w ↦ x w 2)) (hq : Differentiable ℝ (fun w ↦ x w 3))
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    {V : Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4))}
    (hV : ∀ y ∈ V, ContDiff ℝ k (fun w ↦ y w 0) ∧ ContDiff ℝ k (fun w ↦ y w 1) ∧
      Differentiable ℝ (fun w ↦ y w 2) ∧ Differentiable ℝ (fun w ↦ y w 3) ∧
      ∀ w, linearizedEquation x y w 1 = 0 ∧ linearizedEquation x y w 2 = 0)
    (hdiv : ∀ y ∈ V, ∀ η : ℂ → ℂ, ContDiff ℝ k η →
      (∀ z, sectionValue y z = sectionValue x z * η z) → y = 0) :
    ∃ (ι : Type) (_ : Fintype ι) (Φ : V →ₗ[ℝ] ι → ℂ), Function.Injective Φ ∧
      Fintype.card ι = m := by
  classical
  have hk0 : (k : WithTop ℕ∞) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hk))
  -- The zero divisor `D` of `α` and an integrating factor `ν`.
  obtain ⟨D, hD⟩ := exists_sym_sectionValue_eq_pow_count_mul hk hb₁ hb₂ hp hq hhol hframe
  have hα : IsZeroMultiplicity (sectionValue x) fun z ↦ Multiset.count z (D : Multiset ℂ) :=
    isZeroMultiplicity_iff.2 fun z ↦ by
      obtain ⟨v, hv, hv₀, hvf⟩ := hD z
      exact ⟨v, hv.continuousAt, hv₀, hvf⟩
  obtain ⟨ν, hν, hνeq⟩ :=
    exists_contDiff_conjWirtingerDeriv_apply_one_eq hk (contDiff_connectionCoeff hb₁ hb₂)
  -- A decomposition `δα = α G + e^ν H` of every element of `V`.
  have hdec (y : V) : ∃ G : ℂ → ℂ, ContDiff ℝ k G ∧ ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
      ∀ z, sectionValue y z = sectionValue x z * G z + exp (ν z) * H z := by
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hV y y.2
    exact exists_sectionValue_eq_mul_add_exp_mul hk hp hq hhol (hν.differentiable hk0) hνeq
      h₁ h₂ h₃ h₄ h₅
  choose G hG H hH hGH using hdec
  -- Comparison of the principal-part data of two decompositions of the same section.
  have huniq (y : V) {G' H' : ℂ → ℂ} (hG' : Continuous G') (hH' : Differentiable ℂ H')
      (h : ∀ z, sectionValue y z = sectionValue x z * G' z + exp (ν z) * H' z) (z : ℂ) {j : ℕ}
      (hj : j < Multiset.count z (D : Multiset ℂ)) :
      iteratedDeriv j (H y) z = iteratedDeriv j H' z :=
    iteratedDeriv_eq_of_sectionValue_mul_add_exp_mul_eq hα hν.continuous (hG y).continuous hG'
      (hH y) hH' (fun w ↦ by rw [← hGH y w, h w]) z hj
  -- The principal-part data are indexed by the points `⟨a, j⟩`, `j < count a D`, of `D`.
  let Φ : V →ₗ[ℝ] Multiset.ToType (D : Multiset ℂ) → ℂ :=
    { toFun := fun y i ↦ iteratedDeriv i.2 (H y) i.1
      map_add' := fun y y' ↦ funext fun i ↦ by
        rw [huniq (y + y') ((hG y).continuous.add (hG y').continuous) ((hH y).add (hH y'))
          (fun w ↦ by
            rw [Submodule.coe_add, sectionValue_add, hGH y w, hGH y' w]
            simp only [Pi.add_apply]
            ring) i.1 i.2.2,
          iteratedDeriv_add ((hH y).contDiff.contDiffAt) ((hH y').contDiff.contDiffAt),
          Pi.add_apply]
      map_smul' := fun t y ↦ funext fun i ↦ by
        rw [huniq (t • y) (G' := fun w ↦ (t : ℂ) * G y w) (H' := fun w ↦ (t : ℂ) * H y w)
          (continuous_const.mul (hG y).continuous) ((differentiable_const _).mul (hH y))
          (fun w ↦ by
            rw [Submodule.coe_smul, sectionValue_smul, hGH y w]
            ring) i.1 i.2.2,
          iteratedDeriv_const_mul_field, RingHom.id_apply, Pi.smul_apply, Complex.real_smul] }
  refine ⟨Multiset.ToType (D : Multiset ℂ), inferInstance, Φ,
    (injective_iff_map_eq_zero Φ).2 fun y hy ↦ ?_, ?_⟩
  · -- If all principal-part data vanish, then `δα = α η` with `η` of class `Cᵏ`.
    have hjet (z : ℂ) (j : ℕ) (hj : j < Multiset.count z (D : Multiset ℂ)) :
        iteratedDeriv j (H y) z = 0 :=
      congrFun hy (⟨z, ⟨j, hj⟩⟩ : Multiset.ToType (D : Multiset ℂ))
    obtain ⟨η, hη, hyη⟩ := ((tfae_exists_sectionValue_eq_mul (y := y) hk hb₁ hb₂ hp hq hhol hα
      hν (hG y) (hH y) (hGH y)).out 3 1).1 hjet
    exact Subtype.ext (hdiv y y.2 η hη hyη)
  · rw [Multiset.card_coe, Sym.card_coe]

/-- **Finite dimensionality from the principal-part data.** Let `x` be a field with `Cᵏ`
connection coefficients (`k ≥ 1`) and differentiable section, satisfying the holomorphicity rows
and the degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1`. Let `V` be a real vector space of variations
with `Cᵏ` connection coefficients and differentiable sections satisfying the holomorphicity rows of
the linearized equation at `x`. If every `y ∈ V` with `δα = α η`, `η` of class `Cᵏ`, is zero, then
`V` is finite dimensional. -/
theorem finiteDimensional_of_forall_sectionValue_eq_mul_eq_zero {k : ℕ∞} (hk : 1 ≤ k) {m : ℕ}
    (hb₁ : ContDiff ℝ k (fun w ↦ x w 0)) (hb₂ : ContDiff ℝ k (fun w ↦ x w 1))
    (hp : Differentiable ℝ (fun w ↦ x w 2)) (hq : Differentiable ℝ (fun w ↦ x w 3))
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    {V : Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4))}
    (hV : ∀ y ∈ V, ContDiff ℝ k (fun w ↦ y w 0) ∧ ContDiff ℝ k (fun w ↦ y w 1) ∧
      Differentiable ℝ (fun w ↦ y w 2) ∧ Differentiable ℝ (fun w ↦ y w 3) ∧
      ∀ w, linearizedEquation x y w 1 = 0 ∧ linearizedEquation x y w 2 = 0)
    (hdiv : ∀ y ∈ V, ∀ η : ℂ → ℂ, ContDiff ℝ k η →
      (∀ z, sectionValue y z = sectionValue x z * η z) → y = 0) :
    FiniteDimensional ℝ V := by
  obtain ⟨ι, _, Φ, hΦ, -⟩ := exists_injective_linearMap hk hb₁ hb₂ hp hq hhol hframe hV hdiv
  exact Module.Finite.of_injective Φ hΦ

/-- **The real dimension bound `2 m`.** Under the hypotheses of
`TauCeti.Vortex.finiteDimensional_of_forall_sectionValue_eq_mul_eq_zero`, the real dimension of
`V` is at most `2 m`, the real dimension of the tangent space of `Sym^m ℂ`. -/
theorem finrank_le_two_mul_of_forall_sectionValue_eq_mul_eq_zero {k : ℕ∞} (hk : 1 ≤ k) {m : ℕ}
    (hb₁ : ContDiff ℝ k (fun w ↦ x w 0)) (hb₂ : ContDiff ℝ k (fun w ↦ x w 1))
    (hp : Differentiable ℝ (fun w ↦ x w 2)) (hq : Differentiable ℝ (fun w ↦ x w 3))
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    {V : Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4))}
    (hV : ∀ y ∈ V, ContDiff ℝ k (fun w ↦ y w 0) ∧ ContDiff ℝ k (fun w ↦ y w 1) ∧
      Differentiable ℝ (fun w ↦ y w 2) ∧ Differentiable ℝ (fun w ↦ y w 3) ∧
      ∀ w, linearizedEquation x y w 1 = 0 ∧ linearizedEquation x y w 2 = 0)
    (hdiv : ∀ y ∈ V, ∀ η : ℂ → ℂ, ContDiff ℝ k η →
      (∀ z, sectionValue y z = sectionValue x z * η z) → y = 0) :
    Module.finrank ℝ V ≤ 2 * m := by
  obtain ⟨ι, _, Φ, hΦ, hcard⟩ := exists_injective_linearMap hk hb₁ hb₂ hp hq hhol hframe hV hdiv
  calc Module.finrank ℝ V ≤ Module.finrank ℝ (ι → ℂ) :=
        LinearMap.finrank_le_finrank_of_injective hΦ
    _ = 2 * m := by
      rw [Module.finrank_pi_fintype, Finset.sum_const, Complex.finrank_real_complex, smul_eq_mul,
        Finset.card_univ, hcard, mul_comm]

end TauCeti.Vortex
