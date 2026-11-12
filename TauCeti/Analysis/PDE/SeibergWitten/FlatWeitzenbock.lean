/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.CanonicalTensor
public import TauCeti.Analysis.PDE.SeibergWitten.CutoffCurrent
public import TauCeti.Analysis.PDE.SeibergWitten.SelfDualSplitting
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import TauCeti.Analysis.Calculus.DifferentialForm.Basic
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Trace

/-!
# The Weitzenböck formula for the twisted Dirac operator on a flat space

Let `V` be a finite-dimensional real inner product space and `W` a complex Clifford module of `V`,
`ρ : Cl(V, Q) → End_ℂ W` with `Q v = -‖v‖²`, so that `c(v)² = -‖v‖²` for `c(v) = ρ (ι v)`. A
spinor field `ψ : V → W` twisted by a Hermitian line with imaginary connection form `a = i b` has
the covariant derivative `∇ψ = dψ + i b ψ` (`TauCeti.SeibergWitten.covariantDeriv`) and the
**twisted Dirac operator**

`D_b ψ = ∑ₖ c(eₖ) ∇_{eₖ} ψ`     (`TauCeti.SeibergWitten.twistedDirac`),

for any orthonormal basis `e` of `V` (`TauCeti.SeibergWitten.twistedDirac_eq_sum`). This file
proves the **Weitzenböck formula** for `D_b` on the flat space `V`:

`D_b D_b ψ = -∑ₖ ∇²_{eₖ, eₖ} ψ - i c₂(F) ψ`     (`TauCeti.SeibergWitten.twistedDirac_twistedDirac`),

where `∇²_{v, w} ψ = ∇_v (∇ψ)(w)` is the second covariant derivative, so that the first term is
the connection Laplacian `∇*∇ψ`, and `F ∈ ⋀² V` is the two-vector of the real curvature form
`i F_a = -db` of the line, `⟪F, u ∧ w⟫ = -db(u, w)`. It acts through the Clifford map `c₂` of
two-vectors (`CliffordAlgebra.bivectorExterior`). On the positive half-spinors of a four-space
`i c₂(F)` is the Clifford map `C(iF)` (`TauCeti.SeibergWitten.cliffordRestriction`), which only
sees the self-dual part of `F`, and the formula reads `D_b⁻ D_b⁺ = ∇*∇ - C(iF)`. Since `F` indexes
the imaginary curvature `F_a = -iF`, the last term is the Clifford action of `F_a⁺`, that is
`C(F_A⁺) / 2` for the determinant connection `A = 2a` in the usual form
`D_A⁻ D_A⁺ = ∇*∇ + s / 4 + C(F_A⁺) / 2` of the Weitzenböck formula; the scalar curvature `s`
vanishes on flat space.

The proof is the classical one. The Clifford relations `c(eⱼ) c(eₖ) + c(eₖ) c(eⱼ) = -2 δⱼₖ` split
`D_b D_b ψ = ∑ⱼ ∑ₖ c(eⱼ) c(eₖ) ∇²_{eⱼ, eₖ} ψ` into the trace `-∑ₖ ∇²_{eₖ, eₖ} ψ` and the
antisymmetric part `½ ∑ⱼ ∑ₖ c(eⱼ) c(eₖ) (∇²_{eⱼ, eₖ} - ∇²_{eₖ, eⱼ}) ψ`, and the Ricci
identity `∇²_{v, w} ψ - ∇²_{w, v} ψ = i db(v, w) ψ`
(`TauCeti.SeibergWitten.covariantDeriv_covariantDeriv_sub`) identifies the latter with the
curvature term.

## Large-parameter Seiberg–Witten equations

In Taubes's analysis of the Seiberg–Witten equations on a symplectic four-manifold with a large
parameter `r`, a solution is a connection `a = i b` on the line `E` and a positive spinor
`Ψ = √r ψ`, `ψ = φ + β` with `φ` in the `2`-eigenspace of `C(iω)` (the canonical line `α u₀`) and
`β` in the `-2`-eigenspace, solving

`D_b ψ = 0`,    `F + ⋆F = (r / 4) ω - q(√r ψ) - η`,

where `F = i F_a` is indexed by a real two-form, as in
`TauCeti.SeibergWitten.inner_div_two_eq_of_add_hodgeStar_eq`, and `η` is the self-dual forcing.
On flat space, with the constant canonical spinor and the trivial canonical connection, the
Weitzenböck formula turns these equations into Taubes's projected second-order system
(`TauCeti.SeibergWitten.neg_sum_covariantDeriv_covariantDeriv_eq_of_add_hodgeStar_eq`):

`∇*∇ψ + (r / 4) (|ψ|² - 1) ψ + (r / 2) β + C(iη) ψ / 2 = 0`.

Its inner product with `ψ` is the Ginzburg–Landau identity behind the maximum-principle bound
`|ψ|² ≤ 1 + C / r`, and its components along `φ` and `β` are the equations for `α` and `β`.
On a curved almost-Kähler manifold the same computation acquires the scalar curvature, the
curvature of the canonical connection and the torsion terms of `∇u₀`, which this flat statement
does not contain.

## Main definitions

* `TauCeti.SeibergWitten.twistedDirac ρ b ψ`: the twisted Dirac operator `∑ₖ c(eₖ) ∇_{eₖ} ψ`.

## Main results

* `TauCeti.SeibergWitten.covariantDeriv_fun_sum`,
  `TauCeti.SeibergWitten.covariantDeriv_apply_apply`,
  `TauCeti.SeibergWitten.differentiableAt_covariantDeriv`: sums, evaluation and differentiability
  of covariant derivatives.
* `TauCeti.SeibergWitten.twistedDirac_eq_sum`: `D_b ψ` may be computed in any orthonormal basis.
* `TauCeti.SeibergWitten.covariantDeriv_covariantDeriv_sub`: the Ricci identity
  `∇²_{v, w} ψ - ∇²_{w, v} ψ = i db(v, w) ψ`.
* `TauCeti.SeibergWitten.twistedDirac_twistedDirac`: the Weitzenböck formula
  `D_b D_b ψ = -∑ₖ ∇²_{eₖ, eₖ} ψ - i c₂(F) ψ`.
* `TauCeti.SeibergWitten.cliffordRestriction_apply_of_add_hodgeStar_eq`: the action of the
  curvature on the spinor of a solution of the large-parameter curvature equation.
* `TauCeti.SeibergWitten.neg_sum_covariantDeriv_covariantDeriv_eq_of_add_hodgeStar_eq`: the
  projected second-order system of a solution of the large-parameter equations.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press (1989),
  Chapter II, Theorem 8.17 (the general Bochner identity for Dirac bundles).
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §5.1.
* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918, Section 2.
-/

public section

noncomputable section

open CliffordAlgebra Complex Filter Module TensorProduct
open scoped RealInnerProductSpace InnerProductSpace Topology

namespace TauCeti.SeibergWitten

/-! ### Covariant derivatives -/

section CovariantDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {b : E → E [⋀^Fin 1]→L[ℝ] ℝ} {ψ : E → W} {x : E} {κ : Type*} [Fintype κ]

/-- The covariant derivative of a finite sum of differentiable sections is the sum of their
covariant derivatives. -/
theorem covariantDeriv_fun_sum {f : κ → E → W} (hf : ∀ k, DifferentiableAt ℝ (f k) x) :
    covariantDeriv b (fun y ↦ ∑ k, f k y) x = ∑ k, covariantDeriv b (f k) x := by
  ext v
  simp only [sum_apply, covariantDeriv_apply_eq_add_smul,
    Finset.sum_add_distrib, Finset.smul_sum]
  rw [fderiv_fun_sum fun k _ ↦ hf k]
  simp

/-- The covariant derivative of a section of `Hom(E, W)` evaluated at a fixed vector `w` is the
covariant derivative of the section `y ↦ G y w` of `W`. -/
theorem covariantDeriv_apply_apply {G : E → E →L[ℝ] W} (hG : DifferentiableAt ℝ G x)
    (v w : E) : covariantDeriv b G x v w = covariantDeriv b (fun y ↦ G y w) x v := by
  have hd : fderiv ℝ (fun y ↦ G y w) x = (ContinuousLinearMap.apply ℝ W w).comp (fderiv ℝ G x) :=
    ((ContinuousLinearMap.apply ℝ W w).hasFDerivAt.comp x hG.hasFDerivAt).fderiv
  simp [covariantDeriv_apply_eq_add_smul, hd]

/-- The covariant derivative of a section differentiable at `x`, for a connection form
differentiable at `x`, is differentiable at `x`. -/
theorem differentiableAt_covariantDeriv (hψ : DifferentiableAt ℝ (fderiv ℝ ψ) x)
    (hψ' : DifferentiableAt ℝ ψ x) (hb : DifferentiableAt ℝ b x) :
    DifferentiableAt ℝ (covariantDeriv b ψ) x := by
  -- `∇ψ(y) = dψ(y) + (b y) ⊗ i ψ(y)`, a sum of differentiable maps.
  have heq : covariantDeriv b ψ = fun y ↦ fderiv ℝ ψ y +
      ContinuousLinearMap.smulRightL ℝ E W
        ((ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).symm (b y)) (I • ψ y) := by
    ext y v
    simp [covariantDeriv_apply_eq_add_smul, ContinuousAlternatingMap.ofSubsingletonLIE_symm_apply]
  rw [heq]
  refine hψ.add ?_
  have h₁ : DifferentiableAt ℝ
      (fun y ↦ (ContinuousAlternatingMap.ofSubsingletonLIE (0 : Fin 1)).symm (b y)) x := by
    fun_prop
  have h₂ : DifferentiableAt ℝ (fun y ↦ I • ψ y) x := hψ'.const_smul I
  exact ((ContinuousLinearMap.smulRightL ℝ E W).differentiableAt.comp x h₁).clm_apply h₂

/-- The covariant derivative `y ↦ ∇_w ψ(y)` in a fixed direction `w` is
`y ↦ dψ(y) w + b(y)(w) i ψ(y)`. -/
private theorem covariantDeriv_apply_fun (w : E) :
    (fun y ↦ covariantDeriv b ψ y w) =
      fun y ↦ fderiv ℝ ψ y w + b y (fun _ ↦ w) • I • ψ y := by
  ext y
  exact covariantDeriv_apply_eq_add_smul b ψ y w

/-- The second covariant derivative `∇²_{v, w} ψ = ∇_v (∇ψ)(w)`, expanded. -/
private theorem covariantDeriv_covariantDeriv_apply (hψ : DifferentiableAt ℝ (fderiv ℝ ψ) x)
    (hψ' : DifferentiableAt ℝ ψ x) (hb : DifferentiableAt ℝ b x) (v w : E) :
    covariantDeriv b (covariantDeriv b ψ) x v w =
      fderiv ℝ (fderiv ℝ ψ) x v w + b x (fun _ ↦ w) • I • fderiv ℝ ψ x v +
        fderiv ℝ (fun y ↦ b y (fun _ ↦ w)) x v • I • ψ x +
        b x (fun _ ↦ v) • I • (fderiv ℝ ψ x w + b x (fun _ ↦ w) • I • ψ x) := by
  rw [covariantDeriv_apply_apply (differentiableAt_covariantDeriv hψ hψ' hb),
    covariantDeriv_apply_eq_add_smul, covariantDeriv_apply_fun, covariantDeriv_apply_eq_add_smul]
  have hbw : DifferentiableAt ℝ (fun y ↦ b y (fun _ ↦ w)) x :=
    hb.continuousAlternatingMap_apply_const _
  have hfw : DifferentiableAt ℝ (fun y ↦ fderiv ℝ ψ y w) x :=
    (ContinuousLinearMap.apply ℝ W w).differentiableAt.comp x hψ
  have h₁ : fderiv ℝ (fun y ↦ fderiv ℝ ψ y w) x v = fderiv ℝ (fderiv ℝ ψ) x v w := by
    rw [fderiv_clm_apply hψ (differentiableAt_const w)]
    simp
  have hd : HasFDerivAt (fun y ↦ fderiv ℝ ψ y w + b y (fun _ ↦ w) • I • ψ y) _ x :=
    hfw.hasFDerivAt.add (hbw.hasFDerivAt.smul (hψ'.hasFDerivAt.const_smul I))
  rw [hd.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, h₁]
  abel

/-- **The Ricci identity** for the twisted connection on flat space: the curvature of
`∇ = d + i b` is `i db`, so `∇²_{v, w} ψ - ∇²_{w, v} ψ = db(v, w) i ψ`. -/
theorem covariantDeriv_covariantDeriv_sub (hψ : ContDiffAt ℝ 2 ψ x)
    (hb : DifferentiableAt ℝ b x) (v w : E) :
    covariantDeriv b (covariantDeriv b ψ) x v w - covariantDeriv b (covariantDeriv b ψ) x w v =
      extDeriv b x ![v, w] • I • ψ x := by
  have hψ₁ : DifferentiableAt ℝ (fderiv ℝ ψ) x :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hψ' : DifferentiableAt ℝ ψ x := hψ.differentiableAt two_ne_zero
  have hsymm : fderiv ℝ (fderiv ℝ ψ) x v w = fderiv ℝ (fderiv ℝ ψ) x w v :=
    hψ.isSymmSndFDerivAt (by simp) v w
  rw [covariantDeriv_covariantDeriv_apply hψ₁ hψ' hb,
    covariantDeriv_covariantDeriv_apply hψ₁ hψ' hb, extDeriv_apply_pair_of_differentiableAt hb,
    hsymm, sub_smul]
  simp only [smul_add, smul_comm (b x (fun _ ↦ v)) I, smul_comm (b x (fun _ ↦ w)) I,
    smul_smul (b x (fun _ ↦ v)), smul_smul (b x (fun _ ↦ w)), mul_comm (b x (fun _ ↦ w))]
  abel

section FiniteDimensional

variable [FiniteDimensional ℂ W]

/-- The covariant derivative commutes with a complex-linear endomorphism of the fibre:
`∇ (T ψ) = T (∇ ψ)`. -/
private theorem covariantDeriv_comp_apply (T : Module.End ℂ W) (hψ : DifferentiableAt ℝ ψ x)
    (v : E) : covariantDeriv b (fun y ↦ T (ψ y)) x v = T (covariantDeriv b ψ x v) := by
  set L := (LinearMap.toContinuousLinearMap T).restrictScalars ℝ
  have hd : fderiv ℝ (fun y ↦ T (ψ y)) x = L.comp (fderiv ℝ ψ x) :=
    (L.hasFDerivAt.comp x hψ.hasFDerivAt).fderiv
  simp [covariantDeriv_apply_eq_add_smul, hd, L, LinearMap.map_smul_of_tower]

/-- A complex-linear endomorphism of the fibre preserves differentiability of sections. -/
private theorem differentiableAt_end_comp (T : Module.End ℂ W) {f : E → W}
    (hf : DifferentiableAt ℝ f x) : DifferentiableAt ℝ (fun y ↦ T (f y)) x :=
  (((LinearMap.toContinuousLinearMap T).restrictScalars ℝ).hasFDerivAt.comp x
    hf.hasFDerivAt).differentiableAt

end FiniteDimensional

end CovariantDeriv

section Dirac

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {Q : QuadraticForm ℝ V}
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)
  {b : V → V [⋀^Fin 1]→L[ℝ] ℝ} {ψ : V → W} {x : V}
  {κ : Type*} [Fintype κ]

/-! ### Clifford relations in an orthonormal basis -/

/-- The polarization of `Q v = -‖v‖²` on an orthonormal basis: `polar Q eⱼ eₖ = -2 δⱼₖ`. -/
private theorem polar_apply_apply [DecidableEq κ] (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (e : OrthonormalBasis κ ℝ V) (j k : κ) :
    QuadraticMap.polar Q (e j) (e k) = if j = k then -2 else 0 := by
  have hpolar : QuadraticMap.polar Q (e j) (e k) = -2 * ⟪e j, e k⟫ := by
    rw [QuadraticMap.polar, hQ, hQ, hQ, norm_add_sq_real]
    ring
  rw [hpolar, e.inner_eq_ite]
  split_ifs <;> simp

/-- The Clifford relation `c(eⱼ) c(eₖ) + c(eₖ) c(eⱼ) = -2 δⱼₖ` of an orthonormal basis. -/
private theorem map_ι_mul_ι_add_swap [DecidableEq κ] (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (e : OrthonormalBasis κ ℝ V) (j k : κ) :
    ρ (ι Q (e j)) * ρ (ι Q (e k)) + ρ (ι Q (e k)) * ρ (ι Q (e j)) =
      if j = k then -2 else 0 := by
  rw [← map_mul ρ, ← map_mul ρ, ← map_add ρ, ι_mul_ι_add_swap, AlgHom.commutes,
    polar_apply_apply hQ e j k]
  split_ifs <;> simp [map_ofNat]

/-- The algebra of the Weitzenböck formula: if `cⱼ cₖ + cₖ cⱼ = -2 δⱼₖ`, then
`∑ⱼ ∑ₖ cⱼ cₖ Xⱼₖ = -∑ₖ Xₖₖ + ½ ∑ⱼ ∑ₖ cⱼ cₖ (Xⱼₖ - Xₖⱼ)`. -/
private theorem sum_sum_mul_apply_eq [DecidableEq κ] (c : κ → Module.End ℂ W) (X : κ → κ → W)
    (hc : ∀ j k, c j * c k + c k * c j = if j = k then -2 else 0) :
    ∑ j, ∑ k, c j (c k (X j k)) =
      -∑ k, X k k + (2⁻¹ : ℂ) • ∑ j, ∑ k, c j (c k (X j k - X k j)) := by
  -- The Clifford relation applied to `Xⱼₖ`.
  have hrel (j k : κ) : c k (c j (X j k)) =
      -c j (c k (X j k)) + if j = k then (-2 : ℂ) • X j k else 0 := by
    have h := congrArg (fun T : Module.End ℂ W ↦ T (X j k)) (hc j k)
    simp only [LinearMap.add_apply, mul_apply_eq_comp] at h
    rw [eq_neg_add_iff_add_eq, h]
    split_ifs <;> simp [two_smul]
  -- Swap the indices in the second half of the antisymmetrized sum.
  have hswap : ∑ j, ∑ k, c j (c k (X k j)) = ∑ j, ∑ k, c k (c j (X j k)) := Finset.sum_comm
  simp only [map_sub, Finset.sum_sub_distrib]
  rw [hswap]
  simp only [hrel, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, ← Finset.smul_sum]
  module

/-! ### The Dirac operator -/

/-- The real bilinear map `(v, w) ↦ c(v) (L w)` of a real-linear map `L : V → W`. Its trace over
an orthonormal basis is the Clifford contraction `∑ₖ c(eₖ) (L eₖ)`. -/
private def cliffordBilin (L : V →L[ℝ] W) : V →ₗ[ℝ] V →ₗ[ℝ] W :=
  LinearMap.mk₂ ℝ (fun v w ↦ ρ (ι Q v) (L w))
    (fun v₁ v₂ w ↦ by simp)
    (fun c v w ↦ by simp [LinearMap.smul_apply])
    (fun v w₁ w₂ ↦ by simp)
    (fun c v w ↦ by simp [LinearMap.map_smul_of_tower])

variable [FiniteDimensional ℝ V]

/-- The trace of a real bilinear map over an orthonormal basis does not depend on the basis. -/
private theorem sum_apply_apply_eq_of_orthonormalBasis {κ' : Type*} [Fintype κ']
    (B : V →ₗ[ℝ] V →ₗ[ℝ] W) (e : OrthonormalBasis κ ℝ V) (e' : OrthonormalBasis κ' ℝ V) :
    ∑ k, B (e k) (e k) = ∑ k, B (e' k) (e' k) := by
  have h (f : OrthonormalBasis κ ℝ V) :
      ∑ k, B (f k) (f k) = TensorProduct.lift B (InnerProductSpace.canonicalCovariantTensor V) := by
    simp [InnerProductSpace.canonicalCovariantTensor_eq_sum V f]
  have h' (f : OrthonormalBasis κ' ℝ V) :
      ∑ k, B (f k) (f k) = TensorProduct.lift B (InnerProductSpace.canonicalCovariantTensor V) := by
    simp [InnerProductSpace.canonicalCovariantTensor_eq_sum V f]
  rw [h e, h' e']

/-- The **twisted Dirac operator** `D_b ψ = ∑ₖ c(eₖ) ∇_{eₖ} ψ` of a spinor field `ψ : V → W` for
the imaginary connection form `a = i b`, where `c(v) = ρ (ι v)` is Clifford multiplication and
`∇ψ = dψ + i b ψ` (`TauCeti.SeibergWitten.covariantDeriv`). It is computed in the standard
orthonormal basis of `V`, and any other orthonormal basis gives the same value
(`TauCeti.SeibergWitten.twistedDirac_eq_sum`). -/
def twistedDirac (b : V → V [⋀^Fin 1]→L[ℝ] ℝ) (ψ : V → W) (x : V) : W :=
  ∑ k, ρ (ι Q (stdOrthonormalBasis ℝ V k)) (covariantDeriv b ψ x (stdOrthonormalBasis ℝ V k))

/-- The twisted Dirac operator in an arbitrary orthonormal basis `e`:
`D_b ψ = ∑ₖ c(eₖ) ∇_{eₖ} ψ`. -/
theorem twistedDirac_eq_sum (e : OrthonormalBasis κ ℝ V) (b : V → V [⋀^Fin 1]→L[ℝ] ℝ)
    (ψ : V → W) (x : V) :
    twistedDirac ρ b ψ x = ∑ k, ρ (ι Q (e k)) (covariantDeriv b ψ x (e k)) :=
  sum_apply_apply_eq_of_orthonormalBasis (cliffordBilin ρ (covariantDeriv b ψ x))
    (stdOrthonormalBasis ℝ V) e

/-- The twisted Dirac operator vanishes at a point near which the spinor field vanishes. -/
theorem twistedDirac_eq_zero_of_eventuallyEq_zero (hψ : ψ =ᶠ[𝓝 x] 0) :
    twistedDirac ρ b ψ x = 0 := by
  have hd : fderiv ℝ ψ x = 0 := by simp [hψ.fderiv_eq]
  have h0 : ψ x = 0 := hψ.eq_of_nhds
  simp [twistedDirac, covariantDeriv_apply_eq_add_smul, hd, h0]

/-! ### The Weitzenböck formula -/

/-- The Clifford image of a two-vector `F` in an orthonormal basis:
`∑ⱼ ∑ₖ ⟪F, eⱼ ∧ eₖ⟫ c(eⱼ) c(eₖ) = 2 c₂(F)`. -/
private theorem sum_sum_inner_smul_ι_mul_ι (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (e : OrthonormalBasis κ ℝ V) (F : ⋀[ℝ]^2 V) :
    ∑ j, ∑ k, ⟪F, exteriorPower.ιMulti ℝ 2 ![e j, e k]⟫ • (ι Q (e j) * ι Q (e k)) =
      (2 : ℝ) • bivectorExterior Q F := by
  classical
  -- Expand `F = ½ ∑ⱼ ∑ₖ ⟪F, eⱼ ∧ eₖ⟫ eⱼ ∧ eₖ`, so `2 c₂(F) = ∑ⱼ ∑ₖ ⟪F, eⱼ ∧ eₖ⟫ c₂(eⱼ ∧ eₖ)`.
  have hF := congrArg (fun T : Module.End ℝ (⋀[ℝ]^2 V) ↦ bivectorExterior Q (T F))
    (e.sum_rankOne_ιMulti_two)
  simp only [LinearMap.sum_apply, ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply,
    map_sum, map_smul, LinearMap.smul_apply, LinearMap.id_apply,
    bivectorExterior_apply_ιMulti] at hF
  rw [← hF]
  -- The symmetric part `½ polar Q eⱼ eₖ = -δⱼₖ` of `c(eⱼ) c(eₖ)` meets only the diagonal
  -- coefficients `⟪F, eⱼ ∧ eⱼ⟫ = 0`.
  have hdiag (j k : κ) : ⟪F, exteriorPower.ιMulti ℝ 2 ![e j, e k]⟫ •
      ((⅟ (2 : ℝ)) • algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q (e j) (e k))) = 0 := by
    rcases eq_or_ne j k with rfl | hjk
    · rw [(exteriorPower.ιMulti ℝ 2).map_eq_zero_of_eq ![e j, e j] (i := 0) (j := 1) (by simp)
        (by decide), inner_zero_right, zero_smul]
    · simp [polar_apply_apply hQ e j k, hjk]
  simp only [ι_mul_ι_eq_bivector_add, smul_add, hdiag, add_zero, real_inner_comm F]

variable [FiniteDimensional ℂ W]

/-- **The Weitzenböck formula for the twisted Dirac operator** on a flat space: for a `C²` spinor
field `ψ`, a connection form `b` differentiable at `x`, and the two-vector `F` of the curvature
`i F_a = -db`, `⟪F, u ∧ w⟫ = -db(u, w)`,

`D_b D_b ψ = -∑ₖ ∇²_{eₖ, eₖ} ψ - i c₂(F) ψ`

in any orthonormal basis `e`. The first term is the connection Laplacian `∇*∇ψ`. -/
theorem twistedDirac_twistedDirac (hQ : ∀ v, Q v = -‖v‖ ^ 2) (e : OrthonormalBasis κ ℝ V)
    (hψ : ContDiffAt ℝ 2 ψ x) (hb : DifferentiableAt ℝ b x) {F : ⋀[ℝ]^2 V}
    (hF : ∀ u w, ⟪F, exteriorPower.ιMulti ℝ 2 ![u, w]⟫ = -extDeriv b x ![u, w]) :
    twistedDirac ρ b (twistedDirac ρ b ψ) x =
      -∑ k, covariantDeriv b (covariantDeriv b ψ) x (e k) (e k) -
        I • ρ (bivectorExterior Q F) (ψ x) := by
  classical
  have hψ₁ : DifferentiableAt ℝ (fderiv ℝ ψ) x :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hψ' : DifferentiableAt ℝ ψ x := hψ.differentiableAt two_ne_zero
  have hcov : DifferentiableAt ℝ (covariantDeriv b ψ) x :=
    differentiableAt_covariantDeriv hψ₁ hψ' hb
  have hcovk (k : κ) : DifferentiableAt ℝ (fun y ↦ covariantDeriv b ψ y (e k)) x :=
    hcov.clm_apply (differentiableAt_const _)
  set X : κ → κ → W := fun j k ↦ covariantDeriv b (covariantDeriv b ψ) x (e j) (e k) with hXdef
  -- `D_b D_b ψ = ∑ⱼ ∑ₖ c(eⱼ) c(eₖ) ∇²_{eⱼ, eₖ} ψ`.
  have hDD : twistedDirac ρ b (twistedDirac ρ b ψ) x =
      ∑ j, ∑ k, ρ (ι Q (e j)) (ρ (ι Q (e k)) (X j k)) := by
    have hfun : twistedDirac ρ b ψ =
        fun y ↦ ∑ k, ρ (ι Q (e k)) (covariantDeriv b ψ y (e k)) := by
      ext y
      exact twistedDirac_eq_sum ρ e b ψ y
    rw [twistedDirac_eq_sum ρ e, hfun]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [covariantDeriv_fun_sum (f := fun k y ↦ ρ (ι Q (e k)) (covariantDeriv b ψ y (e k)))
      fun k ↦ differentiableAt_end_comp _ (hcovk k), sum_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [covariantDeriv_comp_apply _ (hcovk k), ← covariantDeriv_apply_apply hcov]
  -- The antisymmetric part is the curvature term, by the Ricci identity.
  have hcurv : ∑ j, ∑ k, ρ (ι Q (e j)) (ρ (ι Q (e k)) (X j k - X k j)) =
      (-(2 : ℂ) * I) • ρ (bivectorExterior Q F) (ψ x) := by
    have hX (j k : κ) :
        X j k - X k j = (-⟪F, exteriorPower.ιMulti ℝ 2 ![e j, e k]⟫) • I • ψ x := by
      rw [hXdef, covariantDeriv_covariantDeriv_sub hψ hb, hF, neg_neg]
    have h := congrArg (fun T : CliffordAlgebra Q ↦ ρ T (ψ x)) (sum_sum_inner_smul_ι_mul_ι hQ e F)
    simp only [map_sum, map_smul, map_mul, LinearMap.sum_apply, LinearMap.smul_apply,
      mul_apply_eq_comp] at h
    calc ∑ j, ∑ k, ρ (ι Q (e j)) (ρ (ι Q (e k)) (X j k - X k j))
        = (-I) • ∑ j, ∑ k, ⟪F, exteriorPower.ιMulti ℝ 2 ![e j, e k]⟫ •
            ρ (ι Q (e j)) (ρ (ι Q (e k)) (ψ x)) := by
          simp only [hX, map_neg, map_smul, LinearMap.map_smul_of_tower, Finset.smul_sum,
            neg_smul, smul_comm I (⟪F, _⟫ : ℝ)]
      _ = (-(2 : ℂ) * I) • ρ (bivectorExterior Q F) (ψ x) := by
          rw [h, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
          congr 1
          push_cast
          ring
  rw [hDD, sum_sum_mul_apply_eq _ X fun j k ↦ map_ι_mul_ι_add_swap ρ hQ e j k, hcurv, smul_smul]
  rw [sub_eq_add_neg, ← neg_smul]
  congr 2
  ring

end Dirac

/-! ### The large-parameter Seiberg–Witten equations -/

section LargeParameter

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} {o : Orientation ℝ V (Fin 4)}
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
  {ω : ⋀[ℝ]^2 V} (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V)
  (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
  (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2) {φ β : positiveHalfSpinors o ρ}
  (hφ : cliffordProjection o ρ ω φ = φ) (hβ : cliffordProjection o ρ ω β = 0) {r : ℝ}
  {F η : ⋀[ℝ]^2 V}

attribute [local instance] finiteDimensional_of_finrank_four

include hQ hkl hρ h₂ hφ hβ in
/-- **The curvature term on a solution of the large-parameter equations.** If
`F + ⋆F = (r / 4) ω - q(√r (φ + β)) - η`, with `φ` and `β` in the `2`- and `-2`-eigenspaces of
`C(iω)`, then the Clifford map of `F` acts on `ψ = φ + β` by

`C(iF) ψ = (r / 4) (1 - |ψ|²) ψ - (r / 2) β - C(iη) ψ / 2`.

Only the self-dual part `(F + ⋆F) / 2` of `F` acts on positive spinors; `ω` acts by `±2` on the two
eigenspaces and `C(i q(ψ)) ψ = (|ψ|² / 2) ψ`. -/
theorem cliffordRestriction_apply_of_add_hodgeStar_eq (hr : 0 ≤ r)
    (hF : F + o.hodgeStar hkl F =
      (r / 4) • ω - (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ + β)) : ⋀[ℝ]^2 V) - η) :
    cliffordRestriction o ρ F (φ + β) =
      (r / 4 * (1 - ‖φ + β‖ ^ 2)) • (φ + β) - (r / 2) • β -
        (2⁻¹ : ℝ) • cliffordRestriction o ρ η (φ + β) := by
  -- Only the self-dual part of `F` acts on positive spinors.
  have hasd : cliffordRestriction o ρ (F - o.hodgeStar hkl F) = 0 := by
    refine cliffordRestriction_eq_zero_of_hodgeStar_eq_neg o ρ hQ hkl ?_
    rw [map_sub, o.hodgeStar_hodgeStar_of_even even_two hkl, neg_sub]
  have hsd : cliffordRestriction o ρ F =
      (2⁻¹ : ℝ) • cliffordRestriction o ρ (F + o.hodgeStar hkl F) := by
    have h : F = (2⁻¹ : ℝ) • (F + o.hodgeStar hkl F) + (2⁻¹ : ℝ) • (F - o.hodgeStar hkl F) := by
      module
    conv_lhs => rw [h]
    rw [map_add, map_smul, map_smul, hasd]
    -- `simp` does not find the zero-smul instance of this real action on the endomorphisms of
    -- `W⁺` by itself, so the module is named.
    simp only [add_eq_left]
    exact smul_zero (A := positiveHalfSpinors o ρ →L[ℂ] positiveHalfSpinors o ρ) (2⁻¹ : ℝ)
  have hω₁ : cliffordRestriction o ρ ω φ = (2 : ℂ) • φ :=
    (cliffordProjection_apply_eq_self_iff o ρ).1 hφ
  have hω₂ : cliffordRestriction o ρ ω β = (-2 : ℂ) • β :=
    (cliffordProjection_apply_eq_zero_iff o ρ).1 hβ
  have hq : cliffordRestriction o ρ
      (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ + β)) : ⋀[ℝ]^2 V) (φ + β) =
        (r * ‖φ + β‖ ^ 2 / 2 : ℝ) • (φ + β) := by
    rw [quadraticTwoForm_sqrt_smul o ρ hkl hr, Submodule.coe_smul, map_smul,
      smul_apply, cliffordRestriction_quadraticTwoForm_apply_self o hQ hkl hρ h₂,
      RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
    congr 1
    push_cast
    ring_nf
    rfl
  rw [hsd, hF, map_sub, map_sub, map_smul, smul_apply, sub_apply, sub_apply, smul_apply,
    map_add, hω₁, hω₂, hq]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  push_cast
  module

include hQ hkl hρ h₂ hφ hβ in
/-- **Taubes's projected second-order system on flat space.** Let `ψ` be a `C²` spinor field and
`a = i b` a connection form differentiable at `x`, with `D_b ψ = 0` near `x`. Suppose that at `x`
the two-vector `F` of the curvature `i F_a = -db` satisfies the large-parameter curvature equation
`F + ⋆F = (r / 4) ω - q(√r ψ) - η`, where `ψ(x) = φ + β` with `φ` and `β` in the `2`- and
`-2`-eigenspaces of `C(iω)`. Then, in any orthonormal basis `e`,

`∇*∇ψ = -∑ₖ ∇²_{eₖ, eₖ} ψ = (r / 4) (1 - |ψ|²) ψ - (r / 2) β - C(iη) ψ / 2`

at `x`. -/
theorem neg_sum_covariantDeriv_covariantDeriv_eq_of_add_hodgeStar_eq {κ : Type*} [Fintype κ]
    (e : OrthonormalBasis κ ℝ V) {b : V → V [⋀^Fin 1]→L[ℝ] ℝ} {ψ : V → W}
    {x : V} (hψ : ContDiffAt ℝ 2 ψ x) (hb : DifferentiableAt ℝ b x)
    (hD : twistedDirac ρ b ψ =ᶠ[𝓝 x] 0)
    (hFb : ∀ u w, ⟪F, exteriorPower.ιMulti ℝ 2 ![u, w]⟫ = -extDeriv b x ![u, w])
    (hψx : ψ x = (φ : W) + β) (hr : 0 ≤ r)
    (hF : F + o.hodgeStar hkl F =
      (r / 4) • ω - (quadraticTwoForm o ρ hkl (((√r : ℝ) : ℂ) • (φ + β)) : ⋀[ℝ]^2 V) - η) :
    -∑ k, covariantDeriv b (covariantDeriv b ψ) x (e k) (e k) =
      (r / 4 * (1 - ‖ψ x‖ ^ 2)) • ψ x - (r / 2) • (β : W) -
        (2⁻¹ : ℝ) • (cliffordRestriction o ρ η (φ + β) : W) := by
  have h := twistedDirac_twistedDirac ρ hQ e hψ hb hFb
  rw [twistedDirac_eq_zero_of_eventuallyEq_zero ρ hD, eq_comm, sub_eq_zero] at h
  have hC := congrArg Subtype.val
    (cliffordRestriction_apply_of_add_hodgeStar_eq hQ hkl hρ h₂ hφ hβ hr hF)
  rw [coe_cliffordRestriction_apply, Submodule.coe_add, ← hψx] at hC
  rw [h, hC, hψx]
  simp [Submodule.coe_add]

end LargeParameter

end TauCeti.SeibergWitten
