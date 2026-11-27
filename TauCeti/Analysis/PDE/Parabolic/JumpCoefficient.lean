/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Parabolic.InteriorRegularity
public import TauCeti.Analysis.PDE.Regularity.JumpCoefficient
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Sobolev.W1p.CompactSupport
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian

/-!
# Interior `H²` regularity of parabolic equations fails for a coefficient with a jump

For a time-independent operator `L u = -∂ᵢ(aⁱʲ ∂ⱼu) + bⁱ ∂ᵢu + c u` with `a` uniformly elliptic,
symmetric and **locally Lipschitz** on `Ω`, every weak solution of the parabolic Dirichlet problem

`∂ₜu + L u = F` in `(t₀, t₁) × Ω`, `u = 0` on `(t₀, t₁) × ∂Ω`, `u(t₀) = u₀`,

with `F ∈ L²(t₀, t₁; L²(Ω))` and `u₀ ∈ H¹₀(Ω)`, lies in `L²(t₀, t₁; H²_loc(Ω))`
(`TauCeti.PDE.exists_memLp_lowerOrder_eq_restrictL_of_isSymm`). This file shows that the Lipschitz
hypothesis cannot be dropped, even though the coefficient stays uniformly elliptic, symmetric and
measurable and the data keep their regularity.

The coefficient is the jump coefficient `κ(x) I = TauCeti.PDE.jumpCoefficient n` on `ℝⁿ⁺¹`, with
`κ = 1` on `{x₀ > 0}` and `κ = 2` on its complement, and `b = 0`, `c = 0`. It is uniformly
elliptic (`TauCeti.PDE.uniformlyEllipticOn_jumpCoefficient`) and symmetric
(`TauCeti.PDE.isSymm_jumpCoefficient`), but not locally Lipschitz on any open set meeting the
hyperplane `{x₀ = 0}` (`TauCeti.PDE.not_locallyLipschitzOn_jumpCoefficient`).

* On a bounded open `Ω` and for a compact `K ⊆ Ω`, some `u₀ ∈ H¹₀(Ω)` is a weak solution of
  `-div(κ ∇u₀) = f` with `f ∈ L²(Ω)` and equals the explicit solution
  `TauCeti.PDE.jumpSolution`, `x₀ / κ(x)`, on `K`
  (in the `TauCeti.PDE` namespace,
  `exists_w1p0_forall_energyFormH1_jumpCoefficient_eq_inner_and_value_eq_jumpSolution`).
  One may take `u₀ = χ x₀ / κ` for a smooth cutoff `χ` equal to `1` near `K` and compactly
  supported in `Ω`: its flux is `κ ∇u₀ = ∇(x₀ χ)`, so `f = -Δ(x₀ χ)`.
* The stationary curve `u(t) = u₀`, with time derivative `0` and the constant forcing
  `F(t) = f`, is then a weak solution of the parabolic problem with initial value `u₀`. If `K`
  is the closure of an open `V` meeting the hyperplane, `u` does not lie in
  `L²(t₀, t₁; H²(V))`, since the jump solution is not in `W^{2,2}` of any open set meeting the
  hyperplane (`TauCeti.PDE.not_exists_wkp_two_value_ae_eq_jumpSolution`). So the conclusion of
  the interior regularity theorem fails for this coefficient
  (`TauCeti.PDE.not_forall_exists_memLp_lowerOrder_eq_restrictL_jumpCoefficient`).

For `n = 0` this is a statement on an interval around `0`: a stationary solution of the heat
equation with the piecewise constant conductivity `κ`, whose derivative jumps at `0`, so that it
is not in `H²` there.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §7.1.3, Theorem 5 (improved regularity
  for smooth coefficients).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Filter InnerProductSpace Laplacian
open scoped ContDiff InnerProductSpace Topology Gradient Distributions

namespace TauCeti

namespace PDE

attribute [local instance] W1p0.instNormedAddCommGroup W1p0.instInnerProductSpace

variable {n : ℕ}

/-- The gradient of `x ↦ x₀ χ(x)` for a differentiable `χ` is `χ e₀ + x₀ ∇χ`. -/
private theorem gradient_coord_mul {χ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    {x : EuclideanSpace ℝ (Fin (n + 1))} (hχ : DifferentiableAt ℝ χ x) :
    ∇ (fun y : EuclideanSpace ℝ (Fin (n + 1)) => y 0 * χ y) x =
      χ x • EuclideanSpace.single 0 1 + x 0 • ∇ χ x := by
  have hcoord : (fun y : EuclideanSpace ℝ (Fin (n + 1)) => y 0) =
      fun y => ⟪(EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin (n + 1))), y⟫_ℝ := by
    funext y
    simp [EuclideanSpace.inner_single_left]
  have hd : DifferentiableAt ℝ (fun y : EuclideanSpace ℝ (Fin (n + 1)) => y 0) x := by
    rw [hcoord]
    exact (innerSL ℝ _).differentiableAt
  rw [gradient_fun_mul hd hχ, hcoord, gradient_inner_const_left]
  simp only [conj_trivial]
  exact add_comm _ _

/-- The cutoff `χ u` of the jump solution `u = x₀ / κ` is a weak solution of
`-div(κ ∇(χ u)) = -Δ(x₀ χ)`: its flux `κ (χ ∇u + u ∇χ) = χ e₀ + x₀ ∇χ` is the gradient of the test
function `x₀ χ`. -/
private theorem energyFormH1_jumpCoefficient_contDiffSMul_eq
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {χ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) {N : ℝ} (hN : 0 ≤ N)
    (hχN : ∀ x ∈ Omega, |χ x| ≤ N) (hgradN : ∀ x ∈ Omega, ‖∇ χ x‖ ≤ N)
    {u : W1p volume Omega 2}
    (huv : W1p.value u =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))]
      jumpSolution n)
    (hug : W1p.gradient u =ᵐ[volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))]
      fun x => (if 0 < x 0 then 1 else 2 : ℝ)⁻¹ • EuclideanSpace.single 0 1)
    (v : W1p0 volume Omega 2) :
    energyFormH1 (jumpCoefficient n) 0 0 (W1p.contDiffSMul χ hχ hN hχN hgradN u)
      (v : W1p volume Omega 2) =
      ∫ x in Omega, -Δ (fun y : EuclideanSpace ℝ (Fin (n + 1)) => y 0 * χ y) x *
        W1p.value (v : W1p volume Omega 2) x := by
  -- The test function `φ = x₀ χ`.
  let φ : 𝓓(Omega, ℝ) := ⟨fun y => y 0 * χ y,
    (EuclideanSpace.proj (0 : Fin (n + 1)) : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ).contDiff.mul
      hχ, hχc.mul_left (f := fun y => y 0),
    (tsupport_mul_subset_right (f := fun y => y 0)).trans hχΩ⟩
  have hφ : (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) = fun y => y 0 * χ y := TestFunction.coe_mk
  -- The flux of `χ u` is `∇φ`.
  have hflux : ∀ᵐ x ∂volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      matrixBilinearForm (jumpCoefficient n x) (W1p.gradient (v : W1p volume Omega 2) x)
        (W1p.gradient (W1p.contDiffSMul χ hχ hN hχN hgradN u) x) =
      ⟪∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x,
        W1p.gradient (v : W1p volume Omega 2) x⟫_ℝ := by
    filter_upwards [W1p.gradient_contDiffSMul_ae hχ hN hχN hgradN u, huv, hug] with x h1 h2 h3
    have hκ : (if 0 < x 0 then 1 else 2 : ℝ) ≠ 0 := by split_ifs <;> norm_num
    rw [matrixBilinearForm_jumpCoefficient_apply, h1, h2, h3, hφ,
      gradient_coord_mul ((hχ.differentiable (by simp)) x), real_inner_comm, jumpSolution_apply,
      ← real_inner_smul_left]
    generalize (if 0 < x 0 then 1 else 2 : ℝ) = κ at hκ ⊢
    rw [smul_add, smul_smul, smul_smul, smul_smul, mul_comm κ (χ x), mul_assoc, ← mul_assoc κ,
      mul_inv_cancel₀ hκ, mul_one, one_mul]
  -- Off `Ω`, both `Δφ` and `∇φ` vanish, so the whole-space integrals are integrals over `Ω`.
  have hout : ∀ x ∉ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
      x ∉ tsupport (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) :=
    fun x hx hxφ => hx (φ.tsupport_subset hxφ)
  rw [energyFormH1_zero_zero_eq_setIntegral, integral_congr_ae hflux,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [gradient_of_notMem_tsupport (hout x hx), inner_zero_left],
    ← neg_neg (∫ x, ⟪_, _⟫_ℝ),
    ← (W1p.hasWeakFDerivOn
      (v : W1p volume Omega 2)).integral_laplacian_smul_eq_neg_integral_inner φ,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [laplacian_of_notMem_tsupport (hout x hx), zero_smul], ← integral_neg, hφ]
  simp only [smul_eq_mul, neg_mul]

/-- **A zero-boundary weak solution that agrees with the jump solution on a compact set.** Let
`Ω ⊆ ℝⁿ⁺¹` be bounded and open, and let `K ⊆ Ω` be compact. Some `u₀ ∈ H¹₀(Ω)` is a weak solution
of `-div(κ ∇u₀) = f` in `Ω` for the jump coefficient `κ I = TauCeti.PDE.jumpCoefficient n` and some
`f ∈ L²(Ω)`, that is `∫_Ω κ ∇u₀ · ∇v = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`, and `u₀` equals the
explicit solution `TauCeti.PDE.jumpSolution` almost everywhere on `K`.

One may take `u₀ = χ x₀ / κ` for a smooth cutoff `χ` equal to `1` near `K` and compactly supported
in `Ω`, and `f = -Δ(x₀ χ)`. -/
theorem exists_w1p0_forall_energyFormH1_jumpCoefficient_eq_inner_and_value_eq_jumpSolution
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    {K : Set (EuclideanSpace ℝ (Fin (n + 1)))} (hK : IsCompact K)
    (hKΩ : K ⊆ (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) :
    ∃ u₀ : W1p0 volume Omega 2,
      ∃ f : Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))),
        (∀ v : W1p0 volume Omega 2,
          energyFormH1 (jumpCoefficient n) 0 0 (u₀ : W1p volume Omega 2)
            (v : W1p volume Omega 2) = ⟪f, W1p0.valueL v⟫_ℝ) ∧
        ∀ᵐ x ∂volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))),
          x ∈ K → W1p.value (u₀ : W1p volume Omega 2) x = jumpSolution n x := by
  -- A smooth cutoff `χ`, equal to one near `K` and compactly supported in `Ω`.
  obtain ⟨χ, hχ, -, hχ1, hχc, hχΩ⟩ := hK.exists_contDiff_cutoff_eventuallyEq_one Omega.isOpen hKΩ
  obtain ⟨N, hN, hχN, hgradN⟩ := (hχ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hχc
  -- The jump solution `u = x₀ / κ` and its cutoff `u₀ = χ u ∈ H¹₀(Ω)`.
  obtain ⟨u, huv, hug⟩ := exists_w1p_value_gradient_ae_eq_jumpSolution (n := n) (p := 2)
    ENNReal.ofNat_ne_top hb
  have hmem := W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport (p := 2) (by norm_num) hχ
    hN (fun x _ => hχN x) (fun x _ => hgradN x) hχc hχΩ u
  -- The forcing `f = -Δ(x₀ χ) ∈ L²(Ω)`.
  have hφ : ContDiff ℝ 2 fun y : EuclideanSpace ℝ (Fin (n + 1)) => y 0 * χ y :=
    (EuclideanSpace.proj (0 : Fin (n + 1)) : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ).contDiff.mul
      (hχ.of_le (by simp))
  have hc : HasCompactSupport fun y : EuclideanSpace ℝ (Fin (n + 1)) => y 0 * χ y :=
    hχc.mul_left
  have hf : MemLp (fun x => -Δ (fun y : EuclideanSpace ℝ (Fin (n + 1)) => y 0 * χ y) x) 2
      (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))) :=
    (hφ.continuous_laplacian.neg.memLp_of_hasCompactSupport hc.laplacian.neg).restrict _
  refine ⟨⟨_, hmem⟩, hf.toLp _, fun v => ?_, ?_⟩
  · rw [W1p0.valueL_apply, ← dirichletForcing_apply, dirichletForcing_apply_eq_setIntegral]
    refine (energyFormH1_jumpCoefficient_contDiffSMul_eq hχ hχc hχΩ hN (fun x _ => hχN x)
      (fun x _ => hgradN x) huv hug v).trans (setIntegral_congr_ae Omega.isOpen.measurableSet ?_)
    filter_upwards [(ae_restrict_iff' Omega.isOpen.measurableSet).1 hf.coeFn_toLp] with x hx hxΩ
    rw [hx hxΩ]
  · -- On `K`, the cutoff is one.
    filter_upwards [W1p.value_contDiffSMul_ae hχ hN (fun x _ => hχN x) (fun x _ => hgradN x) u,
      huv] with x h1 h2 hxK
    rw [h1, h2, (hχ1 x hxK).self_of_nhds, one_smul]

/-- **Interior `H²` regularity in space fails for a parabolic equation with a jump coefficient.**
Let `Ω ⊆ ℝⁿ⁺¹` be bounded and open, let `V` be open with closure in `Ω` and containing a point of
the hyperplane `{x₀ = 0}`, and let `t₀ < t₁`. For the jump coefficient
`κ I = TauCeti.PDE.jumpCoefficient n`, with `b = 0` and `c = 0`, the conclusion of
`TauCeti.PDE.exists_memLp_lowerOrder_eq_restrictL_of_isSymm` fails on `V`: not every weak solution
of `∂ₜu - div(κ ∇u) = F` in `(t₀, t₁) × Ω`, `u = 0` on `(t₀, t₁) × ∂Ω`, with
`F ∈ L²(t₀, t₁; L²(Ω))` and continuous `L²(Ω)`-valued representative starting at `u₀ ∈ H¹₀(Ω)`,
lies in `L²(t₀, t₁; H²(V))`.

The coefficient satisfies every other hypothesis of that theorem: it is uniformly elliptic
(`TauCeti.PDE.uniformlyEllipticOn_jumpCoefficient`) and symmetric
(`TauCeti.PDE.isSymm_jumpCoefficient`). It is not locally Lipschitz on `Ω`
(`TauCeti.PDE.not_locallyLipschitzOn_jumpCoefficient`). A counterexample is a stationary solution
`u(t) = u₀` with `u₀` equal to the explicit solution `TauCeti.PDE.jumpSolution` on `V`. -/
theorem not_forall_exists_memLp_lowerOrder_eq_restrictL_jumpCoefficient
    {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (hb : Bornology.IsBounded (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))
    {V : Opens (EuclideanSpace ℝ (Fin (n + 1)))}
    (hVΩ : closure (V : Set (EuclideanSpace ℝ (Fin (n + 1)))) ⊆ Omega)
    {z : EuclideanSpace ℝ (Fin (n + 1))} (hzV : z ∈ V) (hz : z 0 = 0) {t₀ t₁ : ℝ}
    (ht : t₀ < t₁) :
    ¬ ∀ (F : ℝ → Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1))))))
        (u₀ : W1p0 volume Omega 2) (u : ℝ → W1p0 volume Omega 2)
        (u' : ℝ → StrongDual ℝ (W1p0 volume Omega 2))
        (w : ℝ → Lp ℝ 2 (volume.restrict (Omega : Set (EuclideanSpace ℝ (Fin (n + 1)))))),
        MemLp F 2 (volume.restrict (Ioo t₀ t₁)) →
        HasWeakLineDerivOn volume ⟨Ioo t₀ t₁, isOpen_Ioo⟩
          (fun t => (W1p0.valueL (mu := volume) (Omega := Omega) (p := 2)).gelfandDual
            (W1p0.valueL (u t))) u' 1 →
        MemLp u 2 (volume.restrict (Ioo t₀ t₁)) →
        MemLp u' 2 (volume.restrict (Ioo t₀ t₁)) →
        (∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), ∀ v : W1p0 volume Omega 2,
          u' t v + energyFormH1 (jumpCoefficient n) 0 0 (u t : W1p volume Omega 2)
            (v : W1p volume Omega 2) = ⟪F t, W1p0.valueL v⟫_ℝ) →
        ContinuousOn w (Icc t₀ t₁) →
        (fun t => W1p0.valueL (u t)) =ᵐ[volume.restrict (Ioo t₀ t₁)] w →
        w t₀ = W1p0.valueL u₀ →
        ∃ U : ℝ → Wkp volume V 2 2, MemLp U 2 (volume.restrict (Ioo t₀ t₁)) ∧
          ∀ᵐ t ∂volume.restrict (Ioo t₀ t₁), Wkp.lowerOrder 1 (U t) =
            W1p.restrictL (SetLike.coe_subset_coe.mp (subset_closure.trans hVΩ))
              (u t : W1p volume Omega 2) := by
  intro H
  obtain ⟨u₀, f, hf, hval⟩ :=
    exists_w1p0_forall_energyFormH1_jumpCoefficient_eq_inner_and_value_eq_jumpSolution hb
      (Metric.isCompact_of_isClosed_isBounded isClosed_closure (hb.subset hVΩ)) hVΩ
  -- The stationary curve `u(t) = u₀` solves the parabolic problem with forcing `F(t) = f`.
  obtain ⟨U, -, hU⟩ := H (fun _ => f) u₀ (fun _ => u₀) (fun _ => 0) (fun _ => W1p0.valueL u₀)
    (memLp_const f) (hasWeakLineDerivOn_const _) (memLp_const u₀)
    (memLp_const (0 : StrongDual ℝ (W1p0 volume Omega 2)))
    (.of_forall fun _ v => by simpa using hf v) continuousOn_const .rfl rfl
  -- At some time `t`, `U t ∈ W^{2,2}(V)` has first-order part `u₀`, which is the jump solution.
  have : (ae (volume.restrict (Ioo t₀ t₁))).NeBot := ae_restrict_neBot.2 (by simp [ht])
  obtain ⟨t, hUt⟩ := hU.exists
  refine not_exists_wkp_two_value_ae_eq_jumpSolution (p := 2) ENNReal.ofNat_ne_top hzV hz
    ⟨U t, ?_⟩
  have hVΩ' : V ≤ Omega := SetLike.coe_subset_coe.mp (subset_closure.trans hVΩ)
  rw [Wkp.value_succ, hUt, Wkp.value_one (W1p.restrictL hVΩ' (u₀ : W1p volume Omega 2))]
  filter_upwards [W1p.value_restrictL_ae hVΩ' (u₀ : W1p volume Omega 2),
    ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hVΩ) hval,
    ae_restrict_mem V.isOpen.measurableSet] with x h1 h2 hx
  rw [h1, h2 (subset_closure hx)]

end PDE

end TauCeti
