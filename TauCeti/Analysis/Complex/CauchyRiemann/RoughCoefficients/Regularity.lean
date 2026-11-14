/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Differentiated
public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.OrderZero
public import TauCeti.Analysis.Normed.Lp.ProdLp
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Sobolev.Local.Coordinates
import TauCeti.Analysis.Sobolev.Local.Morrey.Higher
import TauCeti.Analysis.Sobolev.Local.Multiplication.Higher
import TauCeti.Analysis.Sobolev.Local.SobolevEmbedding
import TauCeti.Analysis.Sobolev.WeakDeriv.Symmetry
import TauCeti.Analysis.Sobolev.WeakDeriv.WithLp
import TauCeti.Data.ENNReal.Inv
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Higher-order interior regularity for Cauchy–Riemann equations with Sobolev coefficients

Let `Ω ⊆ ℂ` be open, write `z = s + i t`, and let `V` be a finite-dimensional real inner product
space. For `2 < p < ∞`, `1 ≤ ℓ`, an almost complex structure `J ∈ W^{ℓ,p}_loc(Ω; V →L[ℝ] V)`
satisfying `J² = -1` almost everywhere on `Ω` with weak derivative `DJ`, and a zeroth-order
coefficient `S ∈ W^{m,p}_loc(Ω; V →L[ℝ] V)`, consider a weak solution `ξ` of

`∂_s ξ + J ∂_t ξ + S ξ = η`

in the sense of `TauCeti.IsWeakCRSolution q Ω J DJ S ξ η` with `1/p + 1/q < 1`. For every order `k`
with `k ≤ ℓ` and `k ≤ m` and every target exponent `1 < s ≤ p`, this file proves that
`η ∈ W^{k,s}_loc(Ω)` implies `ξ ∈ W^{k+1,s}_loc(Ω)` (McDuff–Salamon, Proposition B.4.9).

## Proof structure

1. *Mixed-derivative commutator with a rough coefficient*
   (`TauCeti.integral_inner_fderiv_add_integral_inner_eq_of_hasWeakFDerivOn`). For
   `J ∈ W^{1,p}_loc(Ω)` and `ξ ∈ W^{1,q}_loc(Ω)` (`1/p + 1/q ≤ 1`) and directions `u, v ∈ ℂ`,
   mollifying `J` near the support of a scalar test function and expanding a vector test function
   `φ` in an orthonormal basis proves
   `∫ ⟪∂_u φ, J (∂_v ξ)⟫ + ∫ ⟪φ, (∂_u J) (∂_v ξ)⟫ = ∫ ⟪∂_v φ, J (∂_u ξ)⟫ + ∫ ⟪φ, (∂_v J) (∂_u ξ)⟫`
   without assuming second weak derivatives of `ξ`.
2. *Weak differentiated system* (`TauCeti.IsWeakCRSolution.differentiated`). When `1/p + 1/q ≤ 1`,
   `J, S ∈ W^{1,p}_loc(Ω)`, `ξ ∈ W^{1,q}_loc(Ω)` and `η` has weak derivative `Dη` on `Ω`, the pair
   `Ξ = (∂_s ξ, ∂_t ξ)` valued in `WithLp 2 (V × V)` solves the differentiated system
   `∂_s Ξ + (J ⊕ J) ∂_t Ξ + S₂ Ξ = (∂_s η - (∂_s S) ξ, ∂_t η - (∂_t S) ξ)` weakly in `L^q_loc(Ω)`,
   where `S₂ = [[S, ∂_s J], [0, S + ∂_t J]]` is conjugated to `WithLp 2 (V × V)`.
3. *Induction on `k`* (`TauCeti.IsWeakCRSolution.memWkpLoc_of_memWkpLoc`). The base `k = 0` is
   `TauCeti.IsWeakCRSolution.memWkpLoc_one_of_memLpLoc`. For `k = k' + 1`, the induction hypothesis
   at `k'` puts `ξ` in `W^{k'+1,s}_loc(Ω)`; simultaneously, two-dimensional Sobolev embedding
   (`TauCeti.MemWkpLoc.exists_two_lt_le_memLpLoc_of_one_lt`) upgrades `η ∈ W^{1,s}_loc(Ω)` to
   `L^{q₁}_loc(Ω)` for an exponent `2 < q₁ ≤ p`, so order-zero regularity puts `ξ` in
   `W^{1,q₁}_loc(Ω)` where `1/p + 1/q₁ < 1`. Applying the induction hypothesis at `k'` to the
   differentiated system on `WithLp 2 (V × V)` puts `Ξ` in `W^{k'+1,s}_loc(Ω)`, hence `ξ` in
   `W^{k'+2,s}_loc(Ω)`.

Transferring across `toEuclidean` removes the inner-product hypothesis for the almost-everywhere
equation on an arbitrary finite-dimensional real normed space
(`TauCeti.memWkpLoc_of_ae_cauchyRiemann`) and for homogeneous linear solutions
(`TauCeti.IsWeakLinearCauchyRiemannOn.memWkpLoc`,
`TauCeti.IsWeakLinearCauchyRiemannOn.memWkpLoc_of_le`,
`TauCeti.IsWeakLinearCauchyRiemannOn.contDiffOn`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (Proposition B.4.9).
-/

public noncomputable section

open Complex Filter LineDeriv MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal InnerProductSpace NNReal Topology

namespace TauCeti

/-! ### Mixed-derivative commutator for a rough endomorphism field -/

section InnerProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Ω : Opens ℂ} {p q s : ℝ≥0∞}
  {J S : ℂ → V →L[ℝ] V} {DJ DS : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}

/-- Scalar test-function form of the commutator identity for `J ∈ W^{1,p}_loc(Ω)` and
`ξ ∈ W^{1,q}_loc(Ω)` (`2 < p < ∞`, `1/p + 1/q ≤ 1`) in directions `u, v ∈ ℂ`. -/
private theorem integral_mul_inner_clm_apply_comm_scalar (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hpq : p⁻¹ + q⁻¹ ≤ 1) (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    {Dξ : ℂ → ℂ →L[ℝ] V} (hDξ : HasWeakFDerivOn volume Ω ξ Dξ) (hDξq : MemLpLoc q Ω Dξ)
    (u v : ℂ) (α : 𝓓(Ω, ℝ)) (x : V) :
    (∫ z, (∂_{u} α : 𝓓(Ω, ℝ)) z * ⟪x, J z (Dξ z v)⟫_ℝ) +
        (∫ z, (α : ℂ → ℝ) z * ⟪x, DJ z u (Dξ z v)⟫_ℝ) =
      (∫ z, (∂_{v} α : 𝓓(Ω, ℝ)) z * ⟪x, J z (Dξ z u)⟫_ℝ) +
        ∫ z, (α : ℂ → ℝ) z * ⟪x, DJ z v (Dξ z u)⟫_ℝ := by
  obtain ⟨Ψ, hderiv, -⟩ :=
    exists_testFunction_tendsto_integral_inner_of_hasWeakFDerivOn hp hp_top hpq hJ hDJ α x
  have hw (w : ℂ) : MemLpLoc q Ω (fun z => Dξ z w) :=
    hDξq.clm_comp (ContinuousLinearMap.apply ℝ V w)
  exact tendsto_nhds_unique (hderiv u (hw v))
    ((hderiv v (hw u)).congr fun n => (hDξ.integral_inner_fderiv_comm u v (Ψ n)).symm)

/-- **Mixed-derivative commutator with a Sobolev coefficient.** If `2 < p < ∞`, `1/p + 1/q ≤ 1`,
`J ∈ W^{1,p}_loc(Ω)` has weak derivative `DJ` and `ξ ∈ W^{1,q}_loc(Ω)` has weak derivative `Dξ`,
then for any directions `u, v ∈ ℂ` and every test function `φ ∈ 𝓓(Ω, V)`,
`∫ ⟪∂_u φ, J (∂_v ξ)⟫ + ∫ ⟪φ, (∂_u J) (∂_v ξ)⟫ = ∫ ⟪∂_v φ, J (∂_u ξ)⟫ + ∫ ⟪φ, (∂_v J) (∂_u ξ)⟫`. -/
theorem integral_inner_fderiv_add_integral_inner_eq_of_hasWeakFDerivOn (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hpq : p⁻¹ + q⁻¹ ≤ 1) (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    {Dξ : ℂ → ℂ →L[ℝ] V} (hDξ : HasWeakFDerivOn volume Ω ξ Dξ) (hDξq : MemLpLoc q Ω Dξ)
    (u v : ℂ) (φ : 𝓓(Ω, V)) :
    (∫ z, ⟪fderiv ℝ (φ : ℂ → V) z u, J z (Dξ z v)⟫_ℝ) +
        (∫ z, ⟪(φ : ℂ → V) z, DJ z u (Dξ z v)⟫_ℝ) =
      (∫ z, ⟪fderiv ℝ (φ : ℂ → V) z v, J z (Dξ z u)⟫_ℝ) +
        ∫ z, ⟪(φ : ℂ → V) z, DJ z v (Dξ z u)⟫_ℝ := by
  let b := stdOrthonormalBasis ℝ V
  let α : Fin (Module.finrank ℝ V) → 𝓓(Ω, ℝ) :=
    fun i => TestFunction.postcompCLM (innerSL ℝ (b i)) φ
  have hloc := Ω.isOpen.isLocallyClosed
  have hDJp : MemLpLoc p Ω DJ := hJ.memLpLoc_of_hasWeakFDerivOn hDJ
  have hα_deriv (i : Fin (Module.finrank ℝ V)) (w : ℂ) (z : ℂ) :
      (∂_{w} (α i) : 𝓓(Ω, ℝ)) z = ⟪b i, fderiv ℝ (φ : ℂ → V) z w⟫_ℝ := by
    simp [α, TestFunction.lineDeriv_eq_fderiv]
  have hparseval (x y : V) : ⟪x, y⟫_ℝ = ∑ i, ⟪b i, x⟫_ℝ * ⟪b i, y⟫_ℝ := by
    conv_lhs => rw [← b.sum_repr' x]
    simp only [sum_inner, real_inner_smul_left]
  have hsum_val {w : ℂ → V} (hw : LocallyIntegrableOn w Ω) :
      ∫ z, ⟪(φ : ℂ → V) z, w z⟫_ℝ = ∑ i, ∫ z, (α i : ℂ → ℝ) z * ⟪b i, w z⟫_ℝ := by
    rw [← integral_finsetSum _ fun i _ => (α i).integrable_mul_inner hw (b i)]
    exact integral_congr_ae (.of_forall fun z => hparseval ((φ : ℂ → V) z) (w z))
  have hsum_deriv (d : ℂ) {w : ℂ → V} (hw : LocallyIntegrableOn w Ω) :
      ∫ z, ⟪fderiv ℝ (φ : ℂ → V) z d, w z⟫_ℝ =
        ∑ i, ∫ z, (∂_{d} (α i) : 𝓓(Ω, ℝ)) z * ⟪b i, w z⟫_ℝ := by
    rw [← integral_finsetSum _ fun i _ => (∂_{d} (α i)).integrable_mul_inner hw (b i)]
    exact integral_congr_ae (.of_forall fun z => by
      dsimp only; simpa only [hα_deriv] using hparseval (fderiv ℝ (φ : ℂ → V) z d) (w z))
  have hADξ {A : ℂ → V →L[ℝ] V} (hA : MemLpLoc p Ω A) (d : ℂ) :
      LocallyIntegrableOn (fun z => A z (Dξ z d)) Ω :=
    hA.locallyIntegrableOn_clm_apply (hDξq.clm_comp (ContinuousLinearMap.apply ℝ V d)) hpq hloc
  have hDJu (d : ℂ) : MemLpLoc p Ω (fun z => DJ z d) :=
    hDJp.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) d)
  rw [hsum_deriv u (hADξ hJ.memLpLoc v), hsum_val (hADξ (hDJu u) v),
    hsum_deriv v (hADξ hJ.memLpLoc u), hsum_val (hADξ (hDJu v) u),
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ =>
    integral_mul_inner_clm_apply_comm_scalar hp hp_top hpq hJ hDJ hDξ hDξq u v (α i) (b i)

/-! ### The weak differentiated Cauchy–Riemann system -/

private noncomputable def fstTestProdL2 (Φ : 𝓓(Ω, WithLp 2 (V × V))) : 𝓓(Ω, V) :=
  TestFunction.postcompCLM (WithLp.fstL 2 ℝ V V) Φ

private noncomputable def sndTestProdL2 (Φ : 𝓓(Ω, WithLp 2 (V × V))) : 𝓓(Ω, V) :=
  TestFunction.postcompCLM (WithLp.sndL 2 ℝ V V) Φ

omit [FiniteDimensional ℝ V] in
private theorem integral_inner_postcomp_prodL2 {f g : ℂ → V}
    (hf : LocallyIntegrableOn f Ω) (hg : LocallyIntegrableOn g Ω)
    (Φ : 𝓓(Ω, WithLp 2 (V × V))) :
    ∫ z, ⟪(Φ : ℂ → WithLp 2 (V × V)) z, WithLp.toLp 2 (f z, g z)⟫_ℝ =
      (∫ z, ⟪(fstTestProdL2 Φ : ℂ → V) z, f z⟫_ℝ) +
        ∫ z, ⟪(sndTestProdL2 Φ : ℂ → V) z, g z⟫_ℝ := by
  rw [← integral_add ((fstTestProdL2 Φ).integrable_inner hf)
    ((sndTestProdL2 Φ).integrable_inner hg)]
  exact integral_congr_ae (.of_forall fun z => by
    dsimp only; rw [WithLp.prod_inner_apply]; simp [fstTestProdL2, sndTestProdL2])

omit [FiniteDimensional ℝ V] in
private theorem integral_inner_postcomp_prodL2_add {f₁ f₂ g₁ g₂ : ℂ → V}
    (hf₁ : LocallyIntegrableOn f₁ Ω) (hf₂ : LocallyIntegrableOn f₂ Ω)
    (hg₁ : LocallyIntegrableOn g₁ Ω) (hg₂ : LocallyIntegrableOn g₂ Ω)
    (Φ : 𝓓(Ω, WithLp 2 (V × V))) :
    ∫ z, ⟪(Φ : ℂ → WithLp 2 (V × V)) z, WithLp.toLp 2 (f₁ z + f₂ z, g₁ z + g₂ z)⟫_ℝ =
      ((∫ z, ⟪(fstTestProdL2 Φ : ℂ → V) z, f₁ z⟫_ℝ) +
          ∫ z, ⟪(fstTestProdL2 Φ : ℂ → V) z, f₂ z⟫_ℝ) +
        ((∫ z, ⟪(sndTestProdL2 Φ : ℂ → V) z, g₁ z⟫_ℝ) +
          ∫ z, ⟪(sndTestProdL2 Φ : ℂ → V) z, g₂ z⟫_ℝ) := by
  rw [integral_inner_postcomp_prodL2 (f := fun z => f₁ z + f₂ z) (g := fun z => g₁ z + g₂ z)
    (hf₁.add hf₂) (hg₁.add hg₂) Φ]
  simp only [inner_add_right]
  rw [integral_add ((fstTestProdL2 Φ).integrable_inner hf₁)
      ((fstTestProdL2 Φ).integrable_inner hf₂),
    integral_add ((sndTestProdL2 Φ).integrable_inner hg₁)
      ((sndTestProdL2 Φ).integrable_inner hg₂)]

omit [FiniteDimensional ℝ V] in
private theorem integral_inner_postcomp_prodL2_sub {f₁ f₂ g₁ g₂ : ℂ → V}
    (hf₁ : LocallyIntegrableOn f₁ Ω) (hf₂ : LocallyIntegrableOn f₂ Ω)
    (hg₁ : LocallyIntegrableOn g₁ Ω) (hg₂ : LocallyIntegrableOn g₂ Ω)
    (Φ : 𝓓(Ω, WithLp 2 (V × V))) :
    ∫ z, ⟪(Φ : ℂ → WithLp 2 (V × V)) z, WithLp.toLp 2 (f₁ z - f₂ z, g₁ z - g₂ z)⟫_ℝ =
      ((∫ z, ⟪(fstTestProdL2 Φ : ℂ → V) z, f₁ z⟫_ℝ) -
          ∫ z, ⟪(fstTestProdL2 Φ : ℂ → V) z, f₂ z⟫_ℝ) +
        ((∫ z, ⟪(sndTestProdL2 Φ : ℂ → V) z, g₁ z⟫_ℝ) -
          ∫ z, ⟪(sndTestProdL2 Φ : ℂ → V) z, g₂ z⟫_ℝ) := by
  simpa only [← sub_eq_add_neg, inner_neg_right, integral_neg] using
    integral_inner_postcomp_prodL2_add (f₂ := fun z => -f₂ z) (g₂ := fun z => -g₂ z)
      hf₁ hf₂.neg hg₁ hg₂.neg Φ

omit [FiniteDimensional ℝ V] in
private theorem integral_inner_fderiv_postcomp_prodL2 {f g : ℂ → V}
    (hf : LocallyIntegrableOn f Ω) (hg : LocallyIntegrableOn g Ω)
    (u : ℂ) (Φ : 𝓓(Ω, WithLp 2 (V × V))) :
    ∫ z, ⟪fderiv ℝ (Φ : ℂ → WithLp 2 (V × V)) z u, WithLp.toLp 2 (f z, g z)⟫_ℝ =
      (∫ z, ⟪fderiv ℝ (fstTestProdL2 Φ : ℂ → V) z u, f z⟫_ℝ) +
        ∫ z, ⟪fderiv ℝ (sndTestProdL2 Φ : ℂ → V) z u, g z⟫_ℝ := by
  rw [← integral_add ((fstTestProdL2 Φ).integrable_inner_fderiv hf u)
    ((sndTestProdL2 Φ).integrable_inner_fderiv hg u)]
  refine integral_congr_ae (.of_forall fun z => ?_)
  dsimp only [fstTestProdL2, sndTestProdL2]
  rw [WithLp.prod_inner_apply, TestFunction.fderiv_postcompCLM, TestFunction.fderiv_postcompCLM]
  simp

private theorem isSobolevCRCoefficients_prodL2 (hJ : MemWkpLoc p Ω 1 J)
    (hDJ : HasWeakFDerivOn volume Ω J DJ) (hSp : MemLpLoc p Ω S) :
    IsSobolevCRCoefficients p Ω (fun z => (J z).withLpProdMap 2 (J z))
      (fun z => (ContinuousLinearMap.withLpProdMapL 2 ℝ V V V V).comp ((DJ z).prod (DJ z)))
      (fun z => ((WithLp.prodContinuousLinearEquiv 2 ℝ V V).arrowCongr
        (WithLp.prodContinuousLinearEquiv 2 ℝ V V)).symm
        (differentiatedCRCoefficient (S z) (DJ z))) := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  have hJ₂_one := hJ.withLpProdMap 2 hJ
  have hDJ₂ := hDJ.withLpProdMap 2 hDJ
  exact ⟨hDJ₂, hJ₂_one.memLpLoc, hJ₂_one.memLpLoc_of_hasWeakFDerivOn hDJ₂,
    ((memWkpLoc_zero_iff.2 hSp).differentiatedCRCoefficient hJ hDJ).memLpLoc.clm_comp
      (G := WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V))
      ((WithLp.prodContinuousLinearEquiv 2 ℝ V V).arrowCongr
        (WithLp.prodContinuousLinearEquiv 2 ℝ V V)).symm.toContinuousLinearMap⟩

/-- Weak integration by parts of `S ξ` in direction `u` for `S ∈ W^{1,p}_loc(Ω)` and
`ξ ∈ W^{1,q}_loc(Ω)` (`2 < p < ∞`, `q ≤ p`, `1/p + 1/q ≤ 1`). -/
private theorem integral_inner_fderiv_clm_apply_eq_neg {Dξ : ℂ → ℂ →L[ℝ] V}
    (hp : 2 < p) (hp_top : p ≠ ⊤) (hqp : q ≤ p) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    (hS : MemWkpLoc p Ω 1 S) (hDS : HasWeakFDerivOn volume Ω S DS)
    (hξ : MemWkpLoc q Ω 1 ξ) (hDξ : HasWeakFDerivOn volume Ω ξ Dξ) (u : ℂ) (ψ : 𝓓(Ω, V)) :
    ∫ z, ⟪fderiv ℝ (ψ : ℂ → V) z u, S z (ξ z)⟫_ℝ =
      -((∫ z, ⟪(ψ : ℂ → V) z, DS z u (ξ z)⟫_ℝ) + ∫ z, ⟪(ψ : ℂ → V) z, S z (Dξ z u)⟫_ℝ) := by
  have hq_top : q ≠ ⊤ := ne_top_of_le_ne_top hp_top hqp
  have hq1 : 1 < q := ENNReal.one_lt_of_ne_top_of_inv_add_inv_le_one hp_top hpq
  have hloc := Ω.isOpen.isLocallyClosed
  have hDSp : MemLpLoc p Ω DS := hS.memLpLoc_of_hasWeakFDerivOn hDS
  have hDξq : MemLpLoc q Ω Dξ := hξ.memLpLoc_of_hasWeakFDerivOn hDξ
  have hSξ : HasWeakFDerivOn volume Ω (fun z => S z (ξ z))
      (fun z => (ContinuousLinearMap.id ℝ (V →L[ℝ] V)).precompL ℂ (DS z) (ξ z) +
        (ContinuousLinearMap.id ℝ (V →L[ℝ] V)).precompR ℂ (S z) (Dξ z)) := by
    have hSi : MemLpLoc ∞ Ω S := hS.memLpLoc_top hp
    lift p to ℝ≥0 using hp_top
    lift q to ℝ≥0 using hq_top
    exact hDS.bilin_of_memLpLoc (ContinuousLinearMap.id ℝ (V →L[ℝ] V)) (by exact_mod_cast hp)
      (by exact_mod_cast hq1) (by exact_mod_cast hqp) (hSi.mono_exponent le_top) hDSp hDξ
      hξ.memLpLoc hDξq
  have h := (hSξ.hasWeakLineDerivOn u).integral_inner_lineDeriv_eq_neg ψ
  simp only [TestFunction.lineDeriv_eq_fderiv, add_apply,
    ContinuousLinearMap.precompL_apply, ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply, inner_add_right] at h
  have hi1 : Integrable (fun z => ⟪(ψ : ℂ → V) z, DS z u (ξ z)⟫_ℝ) :=
    ψ.integrable_inner
      ((hDSp.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) u)).locallyIntegrableOn_clm_apply
        hξ.memLpLoc hpq hloc)
  have hi2 : Integrable (fun z => ⟪(ψ : ℂ → V) z, S z (Dξ z u)⟫_ℝ) :=
    ψ.integrable_inner (hS.memLpLoc.locallyIntegrableOn_clm_apply
      (hDξq.clm_comp (ContinuousLinearMap.apply ℝ V u)) hpq hloc)
  rwa [integral_add hi1 hi2] at h

/-- Testing the almost-everywhere equation `∂_s ξ + J ∂_t ξ + S ξ = η` against `∂_{u} ψ` and
integrating the `S ξ` and `η` terms by parts. -/
private theorem integral_fderiv_test_eq {Dξ Dη : ℂ → ℂ →L[ℝ] V}
    (hp : 2 < p) (hp_top : p ≠ ⊤) (hqp : q ≤ p) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hS : MemWkpLoc p Ω 1 S) (hDS : HasWeakFDerivOn volume Ω S DS)
    (hξ : MemWkpLoc q Ω 1 ξ) (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hDη : HasWeakFDerivOn volume Ω η Dη)
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η) (u : ℂ) (ψ : 𝓓(Ω, V)) :
    (∫ z, ⟪fderiv ℝ (ψ : ℂ → V) z u, Dξ z 1⟫_ℝ) +
        (∫ z, ⟪fderiv ℝ (ψ : ℂ → V) z u, J z (Dξ z I)⟫_ℝ) -
        (∫ z, ⟪(ψ : ℂ → V) z, DS z u (ξ z)⟫_ℝ) -
        (∫ z, ⟪(ψ : ℂ → V) z, S z (Dξ z u)⟫_ℝ) =
      -∫ z, ⟪(ψ : ℂ → V) z, Dη z u⟫_ℝ := by
  have hq_top : q ≠ ⊤ := ne_top_of_le_ne_top hp_top hqp
  have hq1 : 1 < q := ENNReal.one_lt_of_ne_top_of_inv_add_inv_le_one hp_top hpq
  have hloc := Ω.isOpen.isLocallyClosed
  have hJp : MemLpLoc p Ω J := hJ.memLpLoc
  have hSp : MemLpLoc p Ω S := hS.memLpLoc
  have hDξq : MemLpLoc q Ω Dξ := hξ.memLpLoc_of_hasWeakFDerivOn hDξ
  have hc : IsSobolevCRCoefficients p Ω J DJ S :=
    ⟨hDJ, hJp, hJ.memLpLoc_of_hasWeakFDerivOn hDJ, hSp⟩
  have hae := (hc.isWeakCRSolution_iff_ae hpq hp_top hq_top hDξ hξ.memLpLoc hDξq
    hsol.locallyIntegrableOn).1 hsol
  let ψu : 𝓓(Ω, V) := ∂_{u} ψ
  have hψu (z : ℂ) : (ψu : ℂ → V) z = fderiv ℝ (ψ : ℂ → V) z u :=
    TestFunction.lineDerivOp_apply_eq_fderiv ψ u z
  have hiA : Integrable (fun z => ⟪(ψu : ℂ → V) z, Dξ z 1⟫_ℝ) := ψu.integrable_inner
    ((hDξq.clm_comp (ContinuousLinearMap.apply ℝ V 1)).locallyIntegrableOn hq1.le hloc)
  have hiB : Integrable (fun z => ⟪(ψu : ℂ → V) z, J z (Dξ z I)⟫_ℝ) :=
    ψu.integrable_inner (hJp.locallyIntegrableOn_clm_apply
      (hDξq.clm_comp (ContinuousLinearMap.apply ℝ V I)) hpq hloc)
  have hiAB : Integrable (fun z =>
      ⟪(ψu : ℂ → V) z, Dξ z 1⟫_ℝ + ⟪(ψu : ℂ → V) z, J z (Dξ z I)⟫_ℝ) := hiA.add hiB
  have hiC := ψu.integrable_inner (hSp.locallyIntegrableOn_clm_apply hξ.memLpLoc hpq hloc)
  have hae_int : ∫ z, ⟪(ψu : ℂ → V) z, Dξ z 1 + J z (Dξ z I) + S z (ξ z)⟫_ℝ =
      ∫ z, ⟪(ψu : ℂ → V) z, η z⟫_ℝ := by
    refine integral_congr_ae ?_
    filter_upwards [ae_imp_of_ae_restrict hae] with z hz
    by_cases hzΩ : z ∈ (Ω : Set ℂ)
    · rw [hz hzΩ]
    · simp [image_eq_zero_of_notMem_tsupport fun h' => hzΩ (ψu.tsupport_subset h')]
  have hlhs_split : ∫ z, ⟪(ψu : ℂ → V) z, Dξ z 1 + J z (Dξ z I) + S z (ξ z)⟫_ℝ =
      (∫ z, ⟪fderiv ℝ (ψ : ℂ → V) z u, Dξ z 1⟫_ℝ) +
        (∫ z, ⟪fderiv ℝ (ψ : ℂ → V) z u, J z (Dξ z I)⟫_ℝ) +
        ∫ z, ⟪fderiv ℝ (ψ : ℂ → V) z u, S z (ξ z)⟫_ℝ := by
    simp only [inner_add_right]
    rw [integral_add hiAB hiC, integral_add hiA hiB]
    simp only [hψu]
  have hη_ibp : ∫ z, ⟪(ψu : ℂ → V) z, η z⟫_ℝ = -∫ z, ⟪(ψ : ℂ → V) z, Dη z u⟫_ℝ := by
    simpa only [TestFunction.lineDeriv_eq_fderiv, hψu] using
      (hDη.hasWeakLineDerivOn u).integral_inner_lineDeriv_eq_neg ψ
  rw [hlhs_split, integral_inner_fderiv_clm_apply_eq_neg hp hp_top hqp hpq hS hDS hξ hDξ u ψ,
    hη_ibp] at hae_int
  linarith

/-- **The weak differentiated Cauchy–Riemann system.** Let `2 < p < ∞` and `1/p + 1/q ≤ 1`. If
`J, S ∈ W^{1,p}_loc(Ω)` have weak derivatives `DJ, DS`, `ξ ∈ W^{1,q}_loc(Ω)` has weak derivative
`Dξ`, `η` has weak derivative `Dη` on `Ω`, and `ξ` solves `∂_s ξ + J ∂_t ξ + S ξ = η` weakly in
`L^q_loc(Ω)`, then the pair `Ξ = (∂_s ξ, ∂_t ξ)` in `WithLp 2 (V × V)` solves the differentiated
system `∂_s Ξ + (J ⊕ J) ∂_t Ξ + S₂ Ξ = (∂_s η - (∂_s S) ξ, ∂_t η - (∂_t S) ξ)` weakly in
`L^q_loc(Ω)` (McDuff–Salamon, Proposition B.4.9, Step 2). -/
theorem IsWeakCRSolution.differentiated {Dξ Dη : ℂ → ℂ →L[ℝ] V}
    (hp : 2 < p) (hp_top : p ≠ ⊤) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hS : MemWkpLoc p Ω 1 S) (hDS : HasWeakFDerivOn volume Ω S DS)
    (hξ : MemWkpLoc q Ω 1 ξ) (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hDη : HasWeakFDerivOn volume Ω η Dη)
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η) :
    IsWeakCRSolution q Ω (fun z => (J z).withLpProdMap 2 (J z))
      (fun z => (ContinuousLinearMap.withLpProdMapL 2 ℝ V V V V).comp ((DJ z).prod (DJ z)))
      (fun z => ((WithLp.prodContinuousLinearEquiv 2 ℝ V V).arrowCongr
        (WithLp.prodContinuousLinearEquiv 2 ℝ V V)).symm
        (differentiatedCRCoefficient (S z) (DJ z)))
      (fun z => WithLp.toLp 2 (Dξ z 1, Dξ z I))
      (fun z => WithLp.toLp 2 (Dη z 1 - DS z 1 (ξ z), Dη z I - DS z I (ξ z))) := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  have hq1 : 1 < q := ENNReal.one_lt_of_ne_top_of_inv_add_inv_le_one hp_top hpq
  have hloc := Ω.isOpen.isLocallyClosed
  have hDJu (v : ℂ) : MemLpLoc p Ω (fun z => DJ z v) :=
    (hJ.memLpLoc_of_hasWeakFDerivOn hDJ).clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) v)
  have hDξq : MemLpLoc q Ω Dξ := hξ.memLpLoc_of_hasWeakFDerivOn hDξ
  have hDη_loc (u : ℂ) : LocallyIntegrableOn (fun z => Dη z u) Ω :=
    (hDη.hasWeakLineDerivOn u).locallyIntegrableOn_deriv
  have hDSξ_loc (u : ℂ) : LocallyIntegrableOn (fun z => DS z u (ξ z)) Ω :=
    ((hS.memLpLoc_of_hasWeakFDerivOn hDS).clm_comp
      (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) u)).locallyIntegrableOn_clm_apply
      hξ.memLpLoc hpq hloc
  have hc₂ := isSobolevCRCoefficients_prodL2 hJ hDJ hS.memLpLoc
  have hΞq : MemLpLoc q Ω (fun z => WithLp.toLp 2 (Dξ z 1, Dξ z I)) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm.comp_memLpLoc_iff.2
      (hξ.memWkpLoc_partials_of_hasWeakFDerivOn hDξ).memLpLoc
  refine isWeakCRSolution_iff.2
    ⟨hΞq, LocallyIntegrableOn.of_fst_of_snd_prodLp
      ⟨(hDη_loc 1).sub (hDSξ_loc 1), (hDη_loc I).sub (hDSξ_loc I)⟩,
      fun Φ => ⟨hc₂.integrable_inner_crFormalAdjoint hpq hΞq Φ, ?_⟩⟩
  have hpq₀ : p⁻¹ + (min q p)⁻¹ ≤ 1 := ENNReal.inv_add_inv_min_le_one hp.le hpq
  have hrow (u : ℂ) (ψ : 𝓓(Ω, V)) := integral_fderiv_test_eq hp hp_top (min_le_right q p) hpq₀ hJ
    hDJ hS hDS (hξ.mono_exponent (min_le_left q p)) hDξ hDη (hsol.mono_exponent (min_le_left q p))
    u ψ
  have hrow1 := hrow 1 (fstTestProdL2 Φ)
  have hrow2 := hrow I (sndTestProdL2 Φ)
  have hcomm := integral_inner_fderiv_add_integral_inner_eq_of_hasWeakFDerivOn hp hp_top hpq hJ
    hDJ hDξ hDξq 1 I (fstTestProdL2 Φ)
  have hsymm := (hDξ.integral_inner_fderiv_comm 1 I (sndTestProdL2 Φ)).symm
  have hDξ_loc (u : ℂ) : LocallyIntegrableOn (fun z => Dξ z u) Ω :=
    (hDξq.clm_comp (ContinuousLinearMap.apply ℝ V u)).locallyIntegrableOn hq1.le hloc
  have hADξ_loc {A : ℂ → V →L[ℝ] V} (hA : MemLpLoc p Ω A) (u : ℂ) :
      LocallyIntegrableOn (fun z => A z (Dξ z u)) Ω :=
    hA.locallyIntegrableOn_clm_apply (hDξq.clm_comp (ContinuousLinearMap.apply ℝ V u)) hpq hloc
  rw [hc₂.integral_inner_crFormalAdjoint_eq_terms hpq hΞq Φ]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.withLpProdMapL_apply, ContinuousLinearMap.withLpProdMap_apply,
    WithLp.toLp_fst, WithLp.toLp_snd, ContinuousLinearEquiv.arrowCongr_symm,
    ContinuousLinearEquiv.arrowCongr_apply, ContinuousLinearEquiv.symm_symm,
    WithLp.prodContinuousLinearEquiv_apply, WithLp.prodContinuousLinearEquiv_symm_apply,
    differentiatedCRCoefficient_apply]
  rw [integral_inner_fderiv_postcomp_prodL2 (hDξ_loc 1) (hDξ_loc I) 1 Φ,
    integral_inner_fderiv_postcomp_prodL2 (hADξ_loc hJ.memLpLoc 1) (hADξ_loc hJ.memLpLoc I) I Φ,
    integral_inner_postcomp_prodL2 (hADξ_loc (hDJu I) 1) (hADξ_loc (hDJu I) I) Φ,
    integral_inner_postcomp_prodL2_add (hADξ_loc hS.memLpLoc 1) (hADξ_loc (hDJu 1) I)
      (hADξ_loc hS.memLpLoc I) (hADξ_loc (hDJu I) I) Φ,
    integral_inner_postcomp_prodL2_sub (hDη_loc 1) (hDSξ_loc 1) (hDη_loc I) (hDSξ_loc I) Φ]
  linarith

/-! ### Interior regularity at all orders (McDuff–Salamon Proposition B.4.9) -/

/-- **Higher-order interior regularity for Sobolev Cauchy–Riemann equations** (McDuff–Salamon,
Proposition B.4.9). Let `2 < p < ∞`, `1/p + 1/q < 1`, `1 < s ≤ p`, `1 ≤ ℓ`, `k ≤ ℓ` and `k ≤ m`.
If `J ∈ W^{ℓ,p}_loc(Ω)` satisfies `J² = -1` almost everywhere on `Ω` with weak derivative `DJ`,
`S ∈ W^{m,p}_loc(Ω)`, and `ξ` solves `∂_s ξ + J ∂_t ξ + S ξ = η` weakly in `L^q_loc(Ω)` with
`η ∈ W^{k,s}_loc(Ω)`, then `ξ ∈ W^{k+1,s}_loc(Ω)`. -/
theorem IsWeakCRSolution.memWkpLoc_of_memWkpLoc {k ℓ m : ℕ} (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hpq : p⁻¹ + q⁻¹ < 1) (hs1 : 1 < s) (hsp : s ≤ p) (hℓ : 1 ≤ ℓ) (hkℓ : k ≤ ℓ) (hkm : k ≤ m)
    (hJ : MemWkpLoc p Ω ℓ J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V)
    (hS : MemWkpLoc p Ω m S) (hsol : IsWeakCRSolution q Ω J DJ S ξ η)
    (hη : MemWkpLoc s Ω k η) :
    MemWkpLoc s Ω (k + 1) ξ := by
  induction k generalizing V q ℓ m with
  | zero =>
    exact hsol.memWkpLoc_one_of_memLpLoc hp hp_top hpq hs1 hsp (hJ.of_le hℓ) hDJ hJsq
      hS.memLpLoc hη.memLpLoc
  | succ k' ih =>
    have hξ_s : MemWkpLoc s Ω (k' + 1) ξ :=
      ih hpq hℓ (by omega) (by omega) hJ hDJ hJsq hS hsol hη.of_succ
    obtain ⟨Dξ, hDξ, -⟩ := hξ_s.exists_weakFDeriv_of_isOpen
    obtain ⟨q₁, hq₁, hq₁_le_p, hη_q₁⟩ :=
      (hη.of_le (by omega)).exists_two_lt_le_memLpLoc_of_one_lt hp hs1
    have hpq₁ : p⁻¹ + (q₁ : ℝ≥0∞)⁻¹ < 1 :=
      ENNReal.inv_add_inv_lt_one_of_two_lt hp (by exact_mod_cast hq₁.le)
    have hξ_q₁ : MemWkpLoc q₁ Ω 1 ξ :=
      hsol.memWkpLoc_one_of_memLpLoc hp hp_top hpq (by exact_mod_cast one_lt_two.trans hq₁)
        hq₁_le_p (hJ.of_le hℓ) hDJ hJsq hS.memLpLoc hη_q₁
    have hSm' : MemWkpLoc p Ω (k' + 1) S := hS.of_le hkm
    obtain ⟨DS, hDS, hDS_k'⟩ := hSm'.exists_weakFDeriv_of_isOpen
    obtain ⟨Dη, hDη, hDη_k'⟩ := hη.exists_weakFDeriv_of_isOpen
    have hsol₂ := (hsol.of_memLpLoc hξ_q₁.memLpLoc).differentiated hp hp_top hpq₁.le
      (hJ.of_le hℓ) hDJ (hSm'.of_le (by omega)) hDS hξ_q₁ hDξ hDη
    have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
    have hJ_m := hJ.of_le (max_le hℓ (Nat.le_of_succ_le hkℓ))
    have hJ₂sq : ∀ᵐ z ∂volume.restrict Ω,
        ((J z).withLpProdMap 2 (J z)).comp ((J z).withLpProdMap 2 (J z)) =
          -ContinuousLinearMap.id ℝ (WithLp 2 (V × V)) :=
      hJsq.mono fun z hz => by
        rw [ContinuousLinearMap.withLpProdMap_comp, hz, ContinuousLinearMap.withLpProdMap_neg,
          ContinuousLinearMap.withLpProdMap_id]
    have hS₂ := ((hS.of_le (by omega)).differentiatedCRCoefficient (hJ.of_le hkℓ) hDJ).clm_comp
      (G := WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V))
      ((WithLp.prodContinuousLinearEquiv 2 ℝ V V).arrowCongr
        (WithLp.prodContinuousLinearEquiv 2 ℝ V V)).symm.toContinuousLinearMap
    have hs_top : s ≠ ⊤ := ne_top_of_le_ne_top hp_top hsp
    lift p to ℝ≥0 using hp_top
    lift s to ℝ≥0 using hs_top
    have hΗ := (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm.comp_memWkpLoc_iff.2
      (memWkpLoc_differentiatedCR_rightSide (by exact_mod_cast hp) (by exact_mod_cast hs1)
        (by exact_mod_cast hsp) hDS_k' hDη_k' hξ_s)
    have hΞ_s := ih hpq₁ (le_max_left 1 k') (le_max_right 1 k') le_rfl
      (hJ_m.withLpProdMap 2 hJ_m) (hDJ.withLpProdMap 2 hDJ) hJ₂sq hS₂ hsol₂ hΗ
    exact hξ_s.memLpLoc.memWkpLoc_succ_of_hasWeakFDerivOn (by rwa [Opens.interior_coe])
      (by simpa using hΞ_s.clm_comp (WithLp.fstL 2 ℝ V V))
      (by simpa using hΞ_s.clm_comp (WithLp.sndL 2 ℝ V V))

/-- **Higher-order interior regularity at the solution's exponent.** If `2 < p < ∞`,
`1/p + 1/q < 1`, `q ≤ p`, `1 ≤ ℓ`, `k ≤ ℓ`, `k ≤ m`, `J ∈ W^{ℓ,p}_loc(Ω)` with `J² = -1` almost
everywhere on `Ω`, `S ∈ W^{m,p}_loc(Ω)`, and `ξ` solves `∂_s ξ + J ∂_t ξ + S ξ = η` weakly in
`L^q_loc(Ω)` with `η ∈ W^{k,q}_loc(Ω)`, then `ξ ∈ W^{k+1,q}_loc(Ω)`. -/
theorem IsWeakCRSolution.memWkpLoc_of_le {k ℓ m : ℕ} (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hpq : p⁻¹ + q⁻¹ < 1) (hqp : q ≤ p) (hℓ : 1 ≤ ℓ) (hkℓ : k ≤ ℓ) (hkm : k ≤ m)
    (hJ : MemWkpLoc p Ω ℓ J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V)
    (hS : MemWkpLoc p Ω m S) (hsol : IsWeakCRSolution q Ω J DJ S ξ η)
    (hη : MemWkpLoc q Ω k η) :
    MemWkpLoc q Ω (k + 1) ξ :=
  have hq1 : 1 < q :=
    ENNReal.inv_lt_one.1 (lt_of_le_of_lt (le_add_self : q⁻¹ ≤ p⁻¹ + q⁻¹) hpq)
  hsol.memWkpLoc_of_memWkpLoc hp hp_top hpq hq1 hqp hℓ hkℓ hkm hJ hDJ hJsq hS hη

/-- **Higher-order interior regularity at the coefficient exponent.** If `2 < p < ∞`,
`1/p + 1/q < 1`, `1 ≤ ℓ`, `k ≤ ℓ`, `k ≤ m`, `J ∈ W^{ℓ,p}_loc(Ω)` with `J² = -1` almost everywhere
on `Ω`, `S ∈ W^{m,p}_loc(Ω)`, and `ξ` solves `∂_s ξ + J ∂_t ξ + S ξ = η` weakly in `L^q_loc(Ω)`
with `η ∈ W^{k,p}_loc(Ω)`, then `ξ ∈ W^{k+1,p}_loc(Ω)`. -/
theorem IsWeakCRSolution.memWkpLoc {k ℓ m : ℕ} (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hpq : p⁻¹ + q⁻¹ < 1) (hℓ : 1 ≤ ℓ) (hkℓ : k ≤ ℓ) (hkm : k ≤ m)
    (hJ : MemWkpLoc p Ω ℓ J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V)
    (hS : MemWkpLoc p Ω m S) (hsol : IsWeakCRSolution q Ω J DJ S ξ η)
    (hη : MemWkpLoc p Ω k η) :
    MemWkpLoc p Ω (k + 1) ξ :=
  hsol.memWkpLoc_of_memWkpLoc hp hp_top hpq (ENNReal.one_lt_two.trans hp) le_rfl hℓ
    hkℓ hkm hJ hDJ hJsq hS hη

end InnerProduct

/-! ### Transfer to finite-dimensional real normed spaces -/

section NormedSpace

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {Ω : Opens ℂ} {p q s : ℝ≥0∞}

/-- **Interior regularity for the almost-everywhere linear Cauchy–Riemann equation on any
finite-dimensional real normed space.** Let `2 < p < ∞`, `1/p + 1/q < 1`, `1 < s ≤ p`, `1 ≤ ℓ`,
`k ≤ ℓ` and `k ≤ m` (`q = ⊤` is included). If `J ∈ W^{ℓ,p}_loc(Ω; W →L[ℝ] W)` satisfies `J² = -1`
almost everywhere on `Ω`, `S ∈ W^{m,p}_loc(Ω; W →L[ℝ] W)`, `ξ ∈ W^{1,q}_loc(Ω; W)` has a weak
derivative `Dξ` satisfying `Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z` almost everywhere on `Ω`, and
`η ∈ W^{k,s}_loc(Ω; W)`, then `ξ ∈ W^{k+1,s}_loc(Ω; W)`. -/
theorem memWkpLoc_of_ae_cauchyRiemann {k ℓ m : ℕ} {J S : ℂ → W →L[ℝ] W} {ξ η : ℂ → W}
    {Dξ : ℂ → ℂ →L[ℝ] W} (hp : 2 < p) (hp_top : p ≠ ⊤) (hpq : p⁻¹ + q⁻¹ < 1)
    (hs1 : 1 < s) (hsp : s ≤ p) (hℓ : 1 ≤ ℓ) (hkℓ : k ≤ ℓ) (hkm : k ≤ m)
    (hJ : MemWkpLoc p Ω ℓ J)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ W)
    (hS : MemWkpLoc p Ω m S) (hξ : MemWkpLoc q Ω 1 ξ) (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hae : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z)
    (hη : MemWkpLoc s Ω k η) :
    MemWkpLoc s Ω (k + 1) ξ := by
  let q₀ : ℝ≥0∞ := min q p
  have hq₀_top : q₀ ≠ ⊤ := ne_top_of_le_ne_top hp_top (min_le_right q p)
  have hpq₀ : p⁻¹ + q₀⁻¹ < 1 := ENNReal.inv_add_inv_min_lt_one hp hpq
  have hξ₀ : MemWkpLoc q₀ Ω 1 ξ := hξ.mono_exponent (min_le_left q p)
  let e : W ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ W)) := toEuclidean
  let eEnd := e.arrowCongr e
  obtain ⟨DJ, hDJ, -⟩ := (hJ.of_le hℓ).exists_weakFDeriv_of_isOpen
  let J' := fun z => eEnd (J z)
  let DJ' := fun z => eEnd.toContinuousLinearMap.comp (DJ z)
  let S' := fun z => eEnd (S z)
  let ξ' := fun z => e (ξ z)
  let Dξ' := fun z => e.toContinuousLinearMap.comp (Dξ z)
  let η' := fun z => e (η z)
  have hJ' : MemWkpLoc p Ω ℓ J' := eEnd.comp_memWkpLoc_iff.2 hJ
  have hDJ' : HasWeakFDerivOn volume Ω J' DJ' := hDJ.clm_comp eEnd.toContinuousLinearMap
  have hJ'sq : ∀ᵐ z ∂volume.restrict Ω, (J' z).comp (J' z) =
      -ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ W))) := by
    filter_upwards [hJsq] with z hz
    ext x
    have hx : J z (J z (e.symm x)) = -e.symm x := by simpa using congr($hz (e.symm x))
    simp [J', eEnd, hx]
  have hS' : MemWkpLoc p Ω m S' := eEnd.comp_memWkpLoc_iff.2 hS
  have hξ' : MemWkpLoc q₀ Ω 1 ξ' := e.comp_memWkpLoc_iff.2 hξ₀
  have hDξ' : HasWeakFDerivOn volume Ω ξ' Dξ' := hDξ.clm_comp e.toContinuousLinearMap
  have hDξ'q₀ : MemLpLoc q₀ Ω Dξ' := hξ'.memLpLoc_of_hasWeakFDerivOn hDξ'
  have hη' : MemWkpLoc s Ω k η' := e.comp_memWkpLoc_iff.2 hη
  have hη'_loc : LocallyIntegrableOn η' Ω :=
    hη'.memLpLoc.locallyIntegrableOn hs1.le Ω.isOpen.isLocallyClosed
  have hc' : IsSobolevCRCoefficients p Ω J' DJ' S' :=
    ⟨hDJ', hJ'.memLpLoc, (hJ'.of_le hℓ).memLpLoc_of_hasWeakFDerivOn hDJ', hS'.memLpLoc⟩
  have hsol' : IsWeakCRSolution q₀ Ω J' DJ' S' ξ' η' := by
    refine (hc'.isWeakCRSolution_iff_ae hpq₀.le hp_top hq₀_top hDξ' hξ'.memLpLoc hDξ'q₀
      hη'_loc).2 ?_
    filter_upwards [hae] with z hz
    have he := congrArg e hz
    simpa [J', S', ξ', Dξ', η', eEnd, map_add] using he
  exact e.comp_memWkpLoc_iff.1
    (hsol'.memWkpLoc_of_memWkpLoc hp hp_top hpq₀ hs1 hsp hℓ hkℓ hkm hJ' hDJ' hJ'sq hS' hη')

/-- **Interior Sobolev regularity for homogeneous linear Cauchy–Riemann solutions.** If `2 < p < ∞`,
`1/p + 1/q < 1` (`q = ⊤` is included), `1 ≤ ℓ`, `k ≤ ℓ`, `k ≤ m`, `J ∈ W^{ℓ,p}_loc(Ω)` with
`J² = -1` almost everywhere on `Ω`, `S ∈ W^{m,p}_loc(Ω)`, and `ξ` satisfies
`IsWeakLinearCauchyRiemannOn q Ω J S ξ`, then `ξ ∈ W^{k+1,p}_loc(Ω)` (and when `q ≤ p`,
`IsWeakLinearCauchyRiemannOn.memWkpLoc_of_le` gives `ξ ∈ W^{k+1,q}_loc(Ω)`). -/
theorem IsWeakLinearCauchyRiemannOn.memWkpLoc {k ℓ m : ℕ} {J S : ℂ → W →L[ℝ] W} {ξ : ℂ → W}
    (h : IsWeakLinearCauchyRiemannOn q Ω J S ξ) (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hpq : p⁻¹ + q⁻¹ < 1) (hℓ : 1 ≤ ℓ) (hkℓ : k ≤ ℓ) (hkm : k ≤ m)
    (hJ : MemWkpLoc p Ω ℓ J)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ W)
    (hS : MemWkpLoc p Ω m S) :
    MemWkpLoc p Ω (k + 1) ξ := by
  obtain ⟨-, hξq, D, hD, hDq, hae⟩ := isWeakLinearCauchyRiemannOn_iff_of_isOpen.1 h
  have hξ1 : MemWkpLoc q Ω 1 ξ :=
    memWkpLoc_succ_iff_of_isOpen.2 ⟨hξq, D, hD, memWkpLoc_zero_iff.2 hDq⟩
  exact memWkpLoc_of_ae_cauchyRiemann hp hp_top hpq (ENNReal.one_lt_two.trans hp)
    le_rfl hℓ hkℓ hkm hJ hJsq hS hξ1 hD hae memWkpLoc_zero_fun

/-- **Interior Sobolev regularity at the solution's exponent for homogeneous linear solutions.** -/
theorem IsWeakLinearCauchyRiemannOn.memWkpLoc_of_le {k ℓ m : ℕ} {J S : ℂ → W →L[ℝ] W} {ξ : ℂ → W}
    (h : IsWeakLinearCauchyRiemannOn q Ω J S ξ) (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hpq : p⁻¹ + q⁻¹ < 1) (hqp : q ≤ p) (hℓ : 1 ≤ ℓ) (hkℓ : k ≤ ℓ) (hkm : k ≤ m)
    (hJ : MemWkpLoc p Ω ℓ J)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ W)
    (hS : MemWkpLoc p Ω m S) :
    MemWkpLoc q Ω (k + 1) ξ :=
  (h.memWkpLoc hp hp_top hpq hℓ hkℓ hkm hJ hJsq hS).mono_exponent hqp

/-- **`C^n` interior regularity of homogeneous linear Cauchy–Riemann solutions.** For every
`1 < q ≤ ∞` and `n : ℕ∞`, if `J` and `S` are `C^n` on `Ω` with `J² = -1` on `Ω` and `ξ` satisfies
`IsWeakLinearCauchyRiemannOn q Ω J S ξ`, then `ξ` is `C^n` on `Ω`. -/
theorem IsWeakLinearCauchyRiemannOn.contDiffOn {n : ℕ∞} {J S : ℂ → W →L[ℝ] W} {ξ : ℂ → W}
    (h : IsWeakLinearCauchyRiemannOn q Ω J S ξ) (hq : 1 < q)
    (hJ : ContDiffOn ℝ n J Ω)
    (hJsq : ∀ z ∈ (Ω : Set ℂ), (J z).comp (J z) = -ContinuousLinearMap.id ℝ W)
    (hS : ContDiffOn ℝ n S Ω) :
    ContDiffOn ℝ n ξ Ω := by
  obtain ⟨p, hp, hp_top, hpq⟩ := ENNReal.exists_two_lt_ne_top_and_inv_add_inv_lt_one hq
  lift p to ℝ≥0 using hp_top
  have hJsq_ae : ∀ᵐ z ∂volume.restrict Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ W :=
    (ae_restrict_iff' Ω.isOpen.measurableSet).2 (.of_forall hJsq)
  refine contDiffOn_iff_forall_nat_le.2 fun k hk => ?_
  rcases eq_or_ne k 0 with rfl | hk0
  · exact contDiffOn_zero.2 h.continuousOn
  · have hmax_le : ((max 1 k : ℕ) : ℕ∞) ≤ n := by
      simpa only [Nat.max_eq_right (Nat.one_le_iff_ne_zero.2 hk0)] using hk
    have hJp : MemWkpLoc p Ω (max 1 k) J := (hJ.of_le (mod_cast hmax_le)).memWkpLoc subset_rfl
    have hSp : MemWkpLoc p Ω (max 1 k) S := (hS.of_le (mod_cast hmax_le)).memWkpLoc subset_rfl
    have hξ_sob : MemWkpLoc p Ω (k + 1) ξ :=
      h.memWkpLoc hp ENNReal.coe_ne_top hpq (le_max_left 1 k) (le_max_right 1 k)
        (le_max_right 1 k) hJp hJsq_ae hSp
    obtain ⟨g, hg, hξg⟩ := hξ_sob.exists_contDiffOn_ae_eq hp
    exact hg.congr (Measure.eqOn_open_of_ae_eq hξg Ω.isOpen h.continuousOn hg.continuousOn)

end NormedSpace

end TauCeti
