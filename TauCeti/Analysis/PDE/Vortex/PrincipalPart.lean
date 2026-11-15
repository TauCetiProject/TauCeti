/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Divisor
public import TauCeti.Analysis.PDE.Vortex.Gauge.Fixed
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Data.Multiset.Fintype
import TauCeti.Analysis.Complex.Wirtinger.DolbeaultLemma
import TauCeti.Analysis.PDE.Vortex.LogVariation
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
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
  (`TauCeti.Vortex.principalPart_eq_iteratedDeriv`, from
  `TauCeti.IsZeroMultiplicity.iteratedDeriv_eq_of_eventually_mul_add_mul_eq`);
* they all vanish exactly when `δα = α η` for a function `η` of class `Cᵏ`, and already when
  `δα = α η` for a continuous `η` (`TauCeti.Vortex.tfae_exists_sectionValue_eq_mul`).

For a framed vortex of degree `m` the zeros of `α` have total multiplicity `m`, so these
derivatives form `m` complex numbers: the values of the real-linear principal-part map
(`TauCeti.Vortex.principalPartMap`). On a real vector space of such variations in which every
variation with `δα = α η`, `η` of class `Cᵏ`, is zero, this map is injective
(`TauCeti.Vortex.principalPartMap_injective`), so the space has real dimension at most `2 m`
(`TauCeti.Vortex.finiteDimensional_of_forall_sectionValue_eq_mul_eq_zero`,
`TauCeti.Vortex.finrank_le_two_mul_of_forall_sectionValue_eq_mul_eq_zero`).

The `C²` square-integrable kernel of the gauge-fixed operator `L_x = d₀* ⊕ d₁`
(`TauCeti.Vortex.gaugeFixedKernel x`) is such a space: rows `2` and `3` of `L_x y = 0` are the
holomorphicity rows of the linearized equation, and a kernel element with `δα = α η`, `η` of class
`C²`, vanishes when `|α| → 1` at infinity
(`TauCeti.Vortex.eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto`). So at a
`C²` field satisfying `∂bar_a α = 0` with the degree-`m` end framing, the kernel of `L_x` is finite
dimensional, of real dimension at most `2 m`
(`TauCeti.Vortex.finiteDimensional_gaugeFixedKernel`, `TauCeti.Vortex.finrank_gaugeFixedKernel_le`).
At a framed vortex, `2 m` is the real dimension of the tangent space of the divisor space
`Sym^m ℂ`; this is the upper bound in the identification of the kernel with that tangent space.
Surjectivity of the principal-part map, which needs the existence theory of vortices, and the
comparison of this classical kernel with the kernel of the Sobolev realization of `L_x`, which
needs elliptic regularity, are not treated here.

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
  rw [conjWirtingerDeriv_apply_one_sectionValue hp hq, sectionValue_apply, sectionValue_apply]
  rw [linearizedEquation_apply_one] at h₁
  rw [linearizedEquation_apply_two] at h₂
  apply Complex.ext <;> simp <;> linarith

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
    (conjWirtingerDeriv_apply_one_section_eq_mul (hp w) (hq w) (hhol w).1 (hhol w).2)

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
      conjWirtingerDeriv_apply_one_section_eq_mul (hp w) (hq w) (hhol w).1 (hhol w).2]
    simp only [Pi.sub_apply]
    ring
  refine ⟨G, hG, fun w ↦ exp (-ν w) * F w, fun w ↦
    differentiableAt_exp_neg_mul_of_conjWirtingerDeriv_apply_one_eq_mul
      (a := fun w ↦ ((x w 1 : ℂ) - I * x w 0) / 2) (hν w) (hFd w) (hνeq w) (hFeq w), fun z ↦ ?_⟩
  rw [← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul, hF, Pi.sub_apply]
  ring

/-! ### The principal-part data -/

/-- **The principal-part data of a variation.** For an integrating factor `ν`, if the section
variation of `y` decomposes as `δα = α G + e^ν H` with `G` continuous and `H` entire, then
`principalPart x ν y z j` is the derivative `H⁽ʲ⁾(z)` for one such decomposition (and `0` if there
is none). For `j` below the zero multiplicity of `α` at `z` it does not depend on the decomposition
(`TauCeti.Vortex.principalPart_eq_iteratedDeriv`); these values record the principal part of
`δα / α` at `z`. -/
def principalPart (x : ℂ → EuclideanSpace ℝ (Fin 4)) (ν : ℂ → ℂ)
    (y : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) (j : ℕ) : ℂ :=
  iteratedDeriv j (Classical.epsilon fun H : ℂ → ℂ ↦ Differentiable ℂ H ∧
    ∃ G : ℂ → ℂ, Continuous G ∧ ∀ w, sectionValue y w = sectionValue x w * G w + exp (ν w) * H w) z

/-- **The principal-part data do not depend on the decomposition.** If `δα = α G + e^ν H` with
`G`, `ν` continuous and `H` entire, then below the zero multiplicity `n z` of `α` at `z` the
principal-part data of `y` at `z` are the derivatives of `H`. -/
theorem principalPart_eq_iteratedDeriv {n : ℂ → ℕ} (hα : IsZeroMultiplicity (sectionValue x) n)
    {ν G H : ℂ → ℂ} (hν : Continuous ν) (hG : Continuous G) (hH : Differentiable ℂ H)
    (hy : ∀ w, sectionValue y w = sectionValue x w * G w + exp (ν w) * H w) {z : ℂ} {j : ℕ}
    (hj : j < n z) : principalPart x ν y z j = iteratedDeriv j H z := by
  obtain ⟨hH', G', hG', hy'⟩ := Classical.epsilon_spec (p := fun H : ℂ → ℂ ↦
    Differentiable ℂ H ∧ ∃ G : ℂ → ℂ, Continuous G ∧
      ∀ w, sectionValue y w = sectionValue x w * G w + exp (ν w) * H w) ⟨H, hH, G, hG, hy⟩
  exact hα.iteratedDeriv_eq_of_eventually_mul_add_mul_eq hν.cexp.continuousAt (exp_ne_zero _)
    hG'.continuousAt hG.continuousAt (hH'.analyticAt z) (hH.analyticAt z)
    (Eventually.of_forall fun w ↦ by rw [← hy' w, hy w]) hj

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
  tfae_have 2 → 3 := fun ⟨η, hη, hyη⟩ z j hj ↦ by
    simpa using hα.iteratedDeriv_eq_of_eventually_mul_add_mul_eq (H₂ := fun _ ↦ 0)
      hν.continuous.cexp.continuousAt (exp_ne_zero _) hG.continuous.continuousAt hη.continuousAt
      (hH.analyticAt z) analyticAt_const
      (Eventually.of_forall fun w ↦ by rw [← hy w, hyη w, mul_zero, add_zero]) hj
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

/-- **The principal-part map.** Let `D` be the divisor of zeros of `α`, so that `count z D` is the
zero multiplicity of `α` at `z`, let `ν` be continuous, and let `V` be a real vector space of
variations whose section variations decompose as `δα = α G + e^ν H` with `G` continuous and `H`
entire. The principal-part data `H⁽ʲ⁾(a)` at the points `⟨a, j⟩`, `j < count a D`, of `D` form a
real-linear map from `V` to `D → ℂ`. -/
def principalPartMap {D : Multiset ℂ}
    (hα : IsZeroMultiplicity (sectionValue x) fun z ↦ Multiset.count z D) {ν : ℂ → ℂ}
    (hν : Continuous ν) {V : Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4))}
    (hV : ∀ y ∈ V, ∃ G : ℂ → ℂ, Continuous G ∧ ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
      ∀ w, sectionValue y w = sectionValue x w * G w + exp (ν w) * H w) :
    V →ₗ[ℝ] Multiset.ToType D → ℂ where
  toFun y i := principalPart x ν y i.1 i.2
  map_add' y y' := funext fun i ↦ by
    obtain ⟨G, hG, H, hH, hy⟩ := hV y y.2
    obtain ⟨G', hG', H', hH', hy'⟩ := hV y' y'.2
    rw [Pi.add_apply, principalPart_eq_iteratedDeriv hα hν hG hH hy i.2.2,
      principalPart_eq_iteratedDeriv hα hν hG' hH' hy' i.2.2,
      principalPart_eq_iteratedDeriv hα hν (hG.add hG') (hH.add hH')
        (fun w ↦ by
          simp only [Submodule.coe_add, sectionValue_add, hy w, hy' w, Pi.add_apply]
          ring) i.2.2,
      iteratedDeriv_add hH.contDiff.contDiffAt hH'.contDiff.contDiffAt]
  map_smul' t y := funext fun i ↦ by
    obtain ⟨G, hG, H, hH, hy⟩ := hV y y.2
    rw [Pi.smul_apply, RingHom.id_apply, principalPart_eq_iteratedDeriv hα hν hG hH hy i.2.2,
      principalPart_eq_iteratedDeriv hα hν (G := fun w ↦ (t : ℂ) * G w)
        (H := fun w ↦ (t : ℂ) * H w) (continuous_const.mul hG) ((differentiable_const _).mul hH)
        (fun w ↦ by simp only [Submodule.coe_smul, sectionValue_smul, hy w]; ring) i.2.2,
      iteratedDeriv_const_mul_field, Complex.real_smul]

/-- The principal-part map evaluated at the point `⟨a, j⟩` of `D` is `principalPart x ν y a j`. -/
@[simp]
theorem principalPartMap_apply {D : Multiset ℂ}
    (hα : IsZeroMultiplicity (sectionValue x) fun z ↦ Multiset.count z D) {ν : ℂ → ℂ}
    (hν : Continuous ν) {V : Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4))}
    (hV : ∀ y ∈ V, ∃ G : ℂ → ℂ, Continuous G ∧ ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
      ∀ w, sectionValue y w = sectionValue x w * G w + exp (ν w) * H w)
    (y : V) (i : Multiset.ToType D) :
    principalPartMap hα hν hV y i = principalPart x ν y i.1 i.2 := (rfl)

/-- **Injectivity of the principal-part map.** Let `x` have `Cᵏ` connection coefficients
(`k ≥ 1`) and differentiable section, satisfy the holomorphicity rows and have zero divisor `D`,
and let `∂bar ν = (b₂ - i b₁) / 2` with `ν` of class `Cᵏ`. Let `V` be a real vector space of
variations with `Cᵏ` connection coefficients and differentiable sections satisfying the
holomorphicity rows of the linearized equation at `x`. If every `y ∈ V` with `δα = α η`, `η` of
class `Cᵏ`, is zero, then the principal-part map on `V` is injective. -/
theorem principalPartMap_injective {k : ℕ∞} (hk : 1 ≤ k)
    (hb₁ : ContDiff ℝ k (fun w ↦ x w 0)) (hb₂ : ContDiff ℝ k (fun w ↦ x w 1))
    (hp : Differentiable ℝ (fun w ↦ x w 2)) (hq : Differentiable ℝ (fun w ↦ x w 3))
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) {D : Multiset ℂ}
    (hα : IsZeroMultiplicity (sectionValue x) fun z ↦ Multiset.count z D) {ν : ℂ → ℂ}
    (hν : ContDiff ℝ k ν) (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    {V : Submodule ℝ (ℂ → EuclideanSpace ℝ (Fin 4))}
    (hV : ∀ y ∈ V, ContDiff ℝ k (fun w ↦ y w 0) ∧ ContDiff ℝ k (fun w ↦ y w 1) ∧
      Differentiable ℝ (fun w ↦ y w 2) ∧ Differentiable ℝ (fun w ↦ y w 3) ∧
      ∀ w, linearizedEquation x y w 1 = 0 ∧ linearizedEquation x y w 2 = 0)
    (hdec : ∀ y ∈ V, ∃ G : ℂ → ℂ, Continuous G ∧ ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
      ∀ w, sectionValue y w = sectionValue x w * G w + exp (ν w) * H w)
    (hdiv : ∀ y ∈ V, ∀ η : ℂ → ℂ, ContDiff ℝ k η →
      (∀ z, sectionValue y z = sectionValue x z * η z) → y = 0) :
    Function.Injective (principalPartMap hα hν.continuous hdec) := by
  have hk0 : (k : WithTop ℕ∞) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hk))
  refine (injective_iff_map_eq_zero _).2 fun y hy ↦ ?_
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hV y y.2
  obtain ⟨G, hG, H, hH, hGH⟩ := exists_sectionValue_eq_mul_add_exp_mul hk hp hq hhol
    (hν.differentiable hk0) hνeq h₁ h₂ h₃ h₄ h₅
  -- If all principal-part data vanish, then `δα = α η` with `η` of class `Cᵏ`.
  have hjet (z : ℂ) (j : ℕ) (hj : j < Multiset.count z D) : iteratedDeriv j H z = 0 := by
    rw [← principalPart_eq_iteratedDeriv hα hν.continuous hG.continuous hH hGH hj]
    exact congrFun hy ⟨z, ⟨j, hj⟩⟩
  obtain ⟨η, hη, hyη⟩ := ((tfae_exists_sectionValue_eq_mul (y := y) hk hb₁ hb₂ hp hq hhol hα
    hν hG hH hGH).out 3 1).1 hjet
  exact Subtype.ext (hdiv y y.2 η hη hyη)

/-- The principal-part map on `V`, for the zero divisor `D` of `α`, which has `m` points. -/
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
  have hdec (y) (hy : y ∈ V) : ∃ G : ℂ → ℂ, Continuous G ∧ ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
      ∀ w, sectionValue y w = sectionValue x w * G w + exp (ν w) * H w := by
    obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := hV y hy
    obtain ⟨G, hG, H, hH, hGH⟩ := exists_sectionValue_eq_mul_add_exp_mul hk hp hq hhol
      (hν.differentiable hk0) hνeq h₁ h₂ h₃ h₄ h₅
    exact ⟨G, hG.continuous, H, hH, hGH⟩
  exact ⟨Multiset.ToType (D : Multiset ℂ), inferInstance, principalPartMap hα hν.continuous hdec,
    principalPartMap_injective hk hb₁ hb₂ hp hq hhol hα hν hνeq hV hdec hdiv,
    by rw [Multiset.card_coe, Sym.card_coe]⟩

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

/-! ### The kernel of the gauge-fixed operator -/

section Kernel

variable (hx : ContDiff ℝ 2 x) (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) {m : ℕ}
  (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))

/-- A kernel element of `L_x` has `C²` connection variation and differentiable section variation,
and satisfies the holomorphicity rows of the linearized equation, which are rows `2` and `3` of
`L_x y = 0`. -/
private theorem gaugeFixedKernel_linearizedEquation (y) (hy : y ∈ gaugeFixedKernel x) :
    ContDiff ℝ 2 (fun w ↦ y w 0) ∧ ContDiff ℝ 2 (fun w ↦ y w 1) ∧
      Differentiable ℝ (fun w ↦ y w 2) ∧ Differentiable ℝ (fun w ↦ y w 3) ∧
      ∀ w, linearizedEquation x y w 1 = 0 ∧ linearizedEquation x y w 2 = 0 := by
  obtain ⟨hyc, -, hker⟩ := mem_gaugeFixedKernel.1 hy
  have hyi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ y w i := contDiff_euclidean.1 hyc i
  refine ⟨hyi 0, hyi 1, (hyi 2).differentiable (by simp), (hyi 3).differentiable (by simp),
    fun w ↦ ?_⟩
  have h₂ := congrArg (fun v ↦ v 2) (hker w)
  have h₃ := congrArg (fun v ↦ v 3) (hker w)
  simp only [gaugeFixedOperator_apply_two, gaugeFixedOperator_apply_three,
    PiLp.zero_apply] at h₂ h₃
  exact ⟨h₂, h₃⟩

include hx hhol hframe in
/-- A kernel element of `L_x` at a framed field whose section variation is `δα = α η`, with `η`
of class `C²`, vanishes. -/
private theorem gaugeFixedKernel_eq_zero_of_sectionValue_eq_mul (y) (hy : y ∈ gaugeFixedKernel x)
    (η : ℂ → ℂ) (hη : ContDiff ℝ 2 η) (hyη : ∀ z, sectionValue y z = sectionValue x z * η z) :
    y = 0 := by
  obtain ⟨hyc, hy₂, hker⟩ := mem_gaugeFixedKernel.1 hy
  exact eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto
    (hx.of_le one_le_two) hhol (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe)
    hyc.continuous hy₂ hker hη hyη

include hx hhol hframe

/-- **The kernel of `L_x` at a framed field is finite dimensional.** -/
theorem finiteDimensional_gaugeFixedKernel : FiniteDimensional ℝ (gaugeFixedKernel x) := by
  have hxi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i := contDiff_euclidean.1 hx i
  exact finiteDimensional_of_forall_sectionValue_eq_mul_eq_zero (k := 2) (by norm_num) (hxi 0)
    (hxi 1) ((hxi 2).differentiable (by simp)) ((hxi 3).differentiable (by simp)) hhol hframe
    gaugeFixedKernel_linearizedEquation
    (gaugeFixedKernel_eq_zero_of_sectionValue_eq_mul hx hhol hframe)

/-- **The kernel of `L_x` at a framed degree-`m` field has real dimension at most `2 m`.** Let
`x` be a `C²` field satisfying the holomorphicity rows `∂bar_a α = 0` of the vortex equation,
whose section has the degree-`m` end framing `α(z) (z / |z|)⁻ᵐ → 1`. Then the `C²`
square-integrable kernel of the gauge-fixed operator `L_x` has real dimension at most `2 m`. -/
theorem finrank_gaugeFixedKernel_le : Module.finrank ℝ (gaugeFixedKernel x) ≤ 2 * m := by
  have hxi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i := contDiff_euclidean.1 hx i
  exact finrank_le_two_mul_of_forall_sectionValue_eq_mul_eq_zero (k := 2) (by norm_num) (hxi 0)
    (hxi 1) ((hxi 2).differentiable (by simp)) ((hxi 3).differentiable (by simp)) hhol hframe
    gaugeFixedKernel_linearizedEquation
    (gaugeFixedKernel_eq_zero_of_sectionValue_eq_mul hx hhol hframe)

end Kernel

end TauCeti.Vortex
