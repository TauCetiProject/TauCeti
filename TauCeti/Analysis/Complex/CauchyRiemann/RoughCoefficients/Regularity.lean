/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Differentiated
public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.OrderZero
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.Postcomp
import TauCeti.Analysis.Sobolev.Local.Coordinates
import TauCeti.Analysis.Sobolev.Local.Morrey.Higher
import TauCeti.Analysis.Sobolev.Local.Multiplication.Higher
import TauCeti.Analysis.Sobolev.Local.SobolevEmbedding

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
   (`integral_inner_fderiv_one_clm_apply_eq`). For `J ∈ W^{1,p}_loc(Ω)` and `ξ ∈ W^{1,q}_loc(Ω)`
   (`1/p + 1/q < 1`), mollifying `J` near the support of a scalar test function and expanding a
   vector test function `φ` in an orthonormal basis proves
   `∫ ⟪∂_s φ, J (∂_t ξ)⟫ + ∫ ⟪φ, (∂_s J) (∂_t ξ)⟫ = ∫ ⟪∂_t φ, J (∂_s ξ)⟫ + ∫ ⟪φ, (∂_t J) (∂_s ξ)⟫`
   without assuming second weak derivatives of `ξ`.
2. *Weak differentiated system* (`TauCeti.IsWeakCRSolution.differentiated`). When `1 < q ≤ p`,
   `p⁻¹ + q⁻¹ < 1`, `J, S ∈ W^{1,p}_loc(Ω)`, `ξ ∈ W^{1,q}_loc(Ω)` and `η ∈ W^{1,s}_loc(Ω)`
   (`1 ≤ s`), the pair `Ξ = (∂_s ξ, ∂_t ξ)` valued in `WithLp 2 (V × V)` solves the differentiated
   system `∂_s Ξ + diag(J, J) ∂_t Ξ + S₂ Ξ = (∂_s η - (∂_s S) ξ, ∂_t η - (∂_t S) ξ)` weakly in
   `L^q_loc(Ω)`, where `S₂ = [[S, ∂_s J], [0, S + ∂_t J]]` is conjugated to `WithLp 2 (V × V)`.
3. *Induction on `k`* (`TauCeti.IsWeakCRSolution.memWkpLoc_of_memWkpLoc`). The base `k = 0` is
   `TauCeti.IsWeakCRSolution.memWkpLoc_one_of_memLpLoc`. For `k = k' + 1`, the induction hypothesis
   at `k'` puts `ξ` in `W^{k'+1,s}_loc(Ω)`; simultaneously, two-dimensional Sobolev embedding
   upgrades `η ∈ W^{1,s}_loc(Ω)` to `L^{q₁}_loc(Ω)` for an exponent `2 < q₁ ≤ p`, so order-zero
   regularity puts `ξ` in `W^{1,q₁}_loc(Ω)` where `1/p + 1/q₁ < 1`. Applying the induction
   hypothesis at `k'` to the differentiated system on `WithLp 2 (V × V)` puts `Ξ` in
   `W^{k'+1,s}_loc(Ω)`, hence `ξ` in `W^{k'+2,s}_loc(Ω)`.

Transferring across `toEuclidean` removes the inner-product hypothesis for the almost-everywhere
equation on an arbitrary finite-dimensional real normed space
(`TauCeti.memWkpLoc_of_ae_linearCR`) and for homogeneous linear solutions
(`TauCeti.IsWeakLinearCauchyRiemannOn.memWkpLoc`,
`TauCeti.IsWeakLinearCauchyRiemannOn.contDiffOn`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (Proposition B.4.9).
-/

public noncomputable section

open Complex Filter LineDeriv MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal InnerProductSpace NNReal Topology

namespace TauCeti

/-! ### Operators on the `L²` product `WithLp 2 (V × V)` -/

section ProdL2

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Conjugation of continuous linear endomorphisms of `V × V` to `WithLp 2 (V × V)`, packaged as a
continuous linear map so local Sobolev regularity transfers via `MemWkpLoc.clm_comp`. -/
def conjProdL2L (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    (V × V →L[ℝ] V × V) →L[ℝ] (WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) :=
  let e := (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm
  (e.arrowCongr e).toContinuousLinearMap

/-- `conjProdL2L` conjugates `A` by `WithLp.prodContinuousLinearEquiv 2 ℝ V V`. -/
@[simp]
theorem conjProdL2L_apply (A : V × V →L[ℝ] V × V) (x : WithLp 2 (V × V)) :
    conjProdL2L V A x =
      (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm
        (A (WithLp.prodContinuousLinearEquiv 2 ℝ V V x)) := by
  simp [conjProdL2L]

/-- Evaluation of `conjProdL2L V A` on `(WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm p`. -/
theorem conjProdL2L_apply_symm (A : V × V →L[ℝ] V × V) (p : V × V) :
    conjProdL2L V A ((WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm p) =
      (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm (A p) := by
  simp [conjProdL2L]

/-- Diagonal action `diag(A, A)` on `WithLp 2 (V × V)`, packaged as a continuous linear map in
`A : V →L[ℝ] V`. -/
def prodMapL2L (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    (V →L[ℝ] V) →L[ℝ] (WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) :=
  (conjProdL2L V).comp
    ((ContinuousLinearMap.prodMapL ℝ V V V V).comp
      ((ContinuousLinearMap.id ℝ (V →L[ℝ] V)).prod (ContinuousLinearMap.id ℝ (V →L[ℝ] V))))

/-- `prodMapL2L` conjugates `A.prodMap A` by `WithLp.prodContinuousLinearEquiv 2 ℝ V V`. -/
@[simp]
theorem prodMapL2L_apply (A : V →L[ℝ] V) (x : WithLp 2 (V × V)) :
    prodMapL2L V A x =
      (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm
        ((A.prodMap A) (WithLp.prodContinuousLinearEquiv 2 ℝ V V x)) := by
  simp [prodMapL2L]

/-- Action of `prodMapL2L V A` on `(WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm (x, y)`. -/
theorem prodMapL2L_apply_symm (A : V →L[ℝ] V) (x y : V) :
    prodMapL2L V A ((WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm (x, y)) =
      (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm (A x, A y) := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ V V).injective
  ext <;> simp [prodMapL2L]

/-- If `A² = -1` on `V`, then `prodMapL2L V A` squares to `-1` on `WithLp 2 (V × V)`. -/
theorem prodMapL2L_comp_self_eq_neg_id {A : V →L[ℝ] V}
    (hA : A.comp A = -ContinuousLinearMap.id ℝ V) :
    (prodMapL2L V A).comp (prodMapL2L V A) = -ContinuousLinearMap.id ℝ (WithLp 2 (V × V)) := by
  ext x
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ V V).injective
  have hx (y : V) : A (A y) = -y := by simpa using congr($hA y)
  ext <;> simp [hx]

end ProdL2

/-! ### Mixed-derivative commutator for a rough endomorphism field -/

section InnerProduct

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Ω : Opens ℂ} {p q s : ℝ≥0∞}
  {J S : ℂ → V →L[ℝ] V} {DJ DS : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}

/-- Symmetry of mixed second derivatives of a test function transfers across a single weak
derivative: `∫ ⟪∂_s Ψ, ∂_t ξ⟫ = ∫ ⟪∂_t Ψ, ∂_s ξ⟫` for every `Ψ ∈ 𝓓(Ω, V)`. -/
private theorem HasWeakFDerivOn.integral_inner_fderiv_one_eq {Dξ : ℂ → ℂ →L[ℝ] V}
    (hDξ : HasWeakFDerivOn volume Ω ξ Dξ) (Ψ : 𝓓(Ω, V)) :
    ∫ z, ⟪fderiv ℝ (Ψ : ℂ → V) z 1, Dξ z I⟫_ℝ =
      ∫ z, ⟪fderiv ℝ (Ψ : ℂ → V) z I, Dξ z 1⟫_ℝ := by
  have h1 := (hDξ.hasWeakLineDerivOn 1).integral_inner_lineDeriv_eq_neg (∂_{(I : ℂ)} Ψ)
  have h2 := (hDξ.hasWeakLineDerivOn I).integral_inner_lineDeriv_eq_neg (∂_{(1 : ℂ)} Ψ)
  have hlhs : ∫ z, ⟪(∂_{(1 : ℂ)} (∂_{(I : ℂ)} Ψ) : 𝓓(Ω, V)) z, ξ z⟫_ℝ =
      ∫ z, ⟪(∂_{(I : ℂ)} (∂_{(1 : ℂ)} Ψ) : 𝓓(Ω, V)) z, ξ z⟫_ℝ := by
    rw [TestFunction.lineDerivOp_comm Ψ 1 I]
  simp only [TestFunction.lineDeriv_eq_fderiv,
    ← TestFunction.lineDerivOp_apply_eq_fderiv] at h1 h2 ⊢
  linarith

/-- Scalar test-function form of the commutator identity for `J ∈ W^{1,p}_loc(Ω)` and
`ξ ∈ W^{1,q}_loc(Ω)` (`2 < p < ∞`, `1/p + 1/q < 1`). -/
private theorem integral_mul_inner_clm_apply_comm_scalar (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hpq : p⁻¹ + q⁻¹ < 1) (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    {Dξ : ℂ → ℂ →L[ℝ] V} (hDξ : HasWeakFDerivOn volume Ω ξ Dξ) (hDξq : MemLpLoc q Ω Dξ)
    (α : 𝓓(Ω, ℝ)) (v : V) :
    (∫ z, (∂_{(1 : ℂ)} α : 𝓓(Ω, ℝ)) z * ⟪v, J z (Dξ z I)⟫_ℝ) +
        (∫ z, (α : ℂ → ℝ) z * ⟪v, DJ z 1 (Dξ z I)⟫_ℝ) =
      (∫ z, (∂_{(I : ℂ)} α : 𝓓(Ω, ℝ)) z * ⟪v, J z (Dξ z 1)⟫_ℝ) +
        ∫ z, (α : ℂ → ℝ) z * ⟪v, DJ z I (Dξ z 1)⟫_ℝ := by
  obtain ⟨Ψ, hderiv, -⟩ :=
    exists_adjoint_testFunction_tendsto_of_hasWeakFDerivOn hp hp_top hpq hJ hDJ α v
  have hw (u : ℂ) : MemLpLoc q Ω (fun z => Dξ z u) :=
    hDξq.clm_comp (ContinuousLinearMap.apply ℝ V u)
  exact tendsto_nhds_unique (hderiv 1 (hw I))
    ((hderiv I (hw 1)).congr fun n => (hDξ.integral_inner_fderiv_one_eq (Ψ n)).symm)

/-- **Mixed-derivative commutator with a Sobolev coefficient.** If `2 < p < ∞`, `1/p + 1/q < 1`,
`J ∈ W^{1,p}_loc(Ω)` has weak derivative `DJ` and `ξ ∈ W^{1,q}_loc(Ω)` has weak derivative `Dξ`,
then for every test function `φ ∈ 𝓓(Ω, V)`,
`∫ ⟪∂_s φ, J (∂_t ξ)⟫ + ∫ ⟪φ, (∂_s J) (∂_t ξ)⟫ = ∫ ⟪∂_t φ, J (∂_s ξ)⟫ + ∫ ⟪φ, (∂_t J) (∂_s ξ)⟫`. -/
theorem integral_inner_fderiv_one_clm_apply_eq (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hpq : p⁻¹ + q⁻¹ < 1) (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    {Dξ : ℂ → ℂ →L[ℝ] V} (hDξ : HasWeakFDerivOn volume Ω ξ Dξ) (hDξq : MemLpLoc q Ω Dξ)
    (φ : 𝓓(Ω, V)) :
    (∫ z, ⟪fderiv ℝ (φ : ℂ → V) z 1, J z (Dξ z I)⟫_ℝ) +
        (∫ z, ⟪(φ : ℂ → V) z, DJ z 1 (Dξ z I)⟫_ℝ) =
      (∫ z, ⟪fderiv ℝ (φ : ℂ → V) z I, J z (Dξ z 1)⟫_ℝ) +
        ∫ z, ⟪(φ : ℂ → V) z, DJ z I (Dξ z 1)⟫_ℝ := by
  let b := stdOrthonormalBasis ℝ V
  let α : Fin (Module.finrank ℝ V) → 𝓓(Ω, ℝ) :=
    fun i => TestFunction.postcompCLM (innerSL ℝ (b i)) φ
  have hloc := Ω.isOpen.isLocallyClosed
  have hDJp : MemLpLoc p Ω DJ := hJ.memLpLoc_of_hasWeakFDerivOn hDJ
  have hα_deriv (i : Fin (Module.finrank ℝ V)) (u : ℂ) (z : ℂ) :
      (∂_{u} (α i) : 𝓓(Ω, ℝ)) z = ⟪b i, fderiv ℝ (φ : ℂ → V) z u⟫_ℝ := by
    rw [TestFunction.lineDerivOp_apply_eq_fderiv]
    have hd := ((innerSL ℝ (b i)).hasFDerivAt.comp z
      ((φ.contDiff.differentiable (by simp) z).hasFDerivAt)).fderiv
    exact congr($hd u)
  have hparseval (x y : V) : ⟪x, y⟫_ℝ = ∑ i, ⟪b i, x⟫_ℝ * ⟪b i, y⟫_ℝ := by
    conv_lhs => rw [← b.sum_repr' x]
    simp only [sum_inner, real_inner_smul_left]
  have hsum_val {w : ℂ → V} (hw : LocallyIntegrableOn w Ω) :
      ∫ z, ⟪(φ : ℂ → V) z, w z⟫_ℝ = ∑ i, ∫ z, (α i : ℂ → ℝ) z * ⟪b i, w z⟫_ℝ := by
    rw [← integral_finsetSum _ fun i _ => (α i).integrable_mul_inner hw (b i)]
    exact integral_congr_ae (.of_forall fun z => hparseval ((φ : ℂ → V) z) (w z))
  have hsum_deriv (u : ℂ) {w : ℂ → V} (hw : LocallyIntegrableOn w Ω) :
      ∫ z, ⟪fderiv ℝ (φ : ℂ → V) z u, w z⟫_ℝ =
        ∑ i, ∫ z, (∂_{u} (α i) : 𝓓(Ω, ℝ)) z * ⟪b i, w z⟫_ℝ := by
    rw [← integral_finsetSum _ fun i _ => (∂_{u} (α i)).integrable_mul_inner hw (b i)]
    exact integral_congr_ae (.of_forall fun z => by
      dsimp only; simpa only [hα_deriv] using hparseval (fderiv ℝ (φ : ℂ → V) z u) (w z))
  have hADξ {A : ℂ → V →L[ℝ] V} (hA : MemLpLoc p Ω A) (u : ℂ) :
      LocallyIntegrableOn (fun z => A z (Dξ z u)) Ω :=
    hA.locallyIntegrableOn_clm_apply (hDξq.clm_comp (ContinuousLinearMap.apply ℝ V u)) hpq.le hloc
  have hDJu (v : ℂ) : MemLpLoc p Ω (fun z => DJ z v) :=
    hDJp.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) v)
  rw [hsum_deriv 1 (hADξ hJ.memLpLoc I), hsum_val (hADξ (hDJu 1) I),
    hsum_deriv I (hADξ hJ.memLpLoc 1), hsum_val (hADξ (hDJu I) 1),
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ =>
    integral_mul_inner_clm_apply_comm_scalar hp hp_top hpq hJ hDJ hDξ hDξq (α i) (b i)

/-! ### The weak differentiated Cauchy–Riemann system -/

private noncomputable def fstTestProdL2 (Φ : 𝓓(Ω, WithLp 2 (V × V))) : 𝓓(Ω, V) :=
  TestFunction.postcompCLM
    ((ContinuousLinearMap.fst ℝ V V).comp
      (WithLp.prodContinuousLinearEquiv 2 ℝ V V).toContinuousLinearMap) Φ

private noncomputable def sndTestProdL2 (Φ : 𝓓(Ω, WithLp 2 (V × V))) : 𝓓(Ω, V) :=
  TestFunction.postcompCLM
    ((ContinuousLinearMap.snd ℝ V V).comp
      (WithLp.prodContinuousLinearEquiv 2 ℝ V V).toContinuousLinearMap) Φ

omit [FiniteDimensional ℝ V] in
private theorem integral_inner_postcomp_prodL2 {f g : ℂ → V}
    (hf : LocallyIntegrableOn f Ω) (hg : LocallyIntegrableOn g Ω)
    (Φ : 𝓓(Ω, WithLp 2 (V × V))) :
    ∫ z, ⟪(Φ : ℂ → WithLp 2 (V × V)) z,
        (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm (f z, g z)⟫_ℝ =
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
    ∫ z, ⟪(Φ : ℂ → WithLp 2 (V × V)) z,
        (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm (f₁ z + f₂ z, g₁ z + g₂ z)⟫_ℝ =
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
    ∫ z, ⟪(Φ : ℂ → WithLp 2 (V × V)) z,
        (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm (f₁ z - f₂ z, g₁ z - g₂ z)⟫_ℝ =
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
    ∫ z, ⟪fderiv ℝ (Φ : ℂ → WithLp 2 (V × V)) z u,
        (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm (f z, g z)⟫_ℝ =
      (∫ z, ⟪fderiv ℝ (fstTestProdL2 Φ : ℂ → V) z u, f z⟫_ℝ) +
        ∫ z, ⟪fderiv ℝ (sndTestProdL2 Φ : ℂ → V) z u, g z⟫_ℝ := by
  rw [← integral_add ((fstTestProdL2 Φ).integrable_inner_fderiv hf u)
    ((sndTestProdL2 Φ).integrable_inner_fderiv hg u)]
  refine integral_congr_ae (.of_forall fun z => ?_)
  have hfderiv (L : WithLp 2 (V × V) →L[ℝ] V) :
      fderiv ℝ (TestFunction.postcompCLM L Φ : ℂ → V) z u =
        L (fderiv ℝ (Φ : ℂ → WithLp 2 (V × V)) z u) :=
    congr($((L.hasFDerivAt.comp z ((Φ.contDiff.differentiable (by simp) z).hasFDerivAt)).fderiv) u)
  dsimp only [fstTestProdL2, sndTestProdL2]
  rw [WithLp.prod_inner_apply, hfderiv, hfderiv]
  simp

omit [FiniteDimensional ℝ V] in
private theorem locallyIntegrableOn_symm_prodL2 {f g : ℂ → V}
    (hf : LocallyIntegrableOn f Ω) (hg : LocallyIntegrableOn g Ω) :
    LocallyIntegrableOn
      (fun z => (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm (f z, g z)) Ω := by
  let e := WithLp.prodContinuousLinearEquiv 2 ℝ V V
  refine (((e.symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl ℝ V V)).locallyIntegrableOn_comp hf).add
    ((e.symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inr ℝ V V)).locallyIntegrableOn_comp hg)).congr (.of_forall fun z => ?_)
  simp only [Pi.add_apply, Function.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, ContinuousLinearEquiv.coe_coe,
    ← map_add, Prod.mk_add_mk, add_zero, zero_add]
  rfl

private theorem memLpLoc_symm_prodL2 {Dξ : ℂ → ℂ →L[ℝ] V} (hDξq : MemLpLoc q Ω Dξ) :
    MemLpLoc q Ω
      (fun z => (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm (Dξ z 1, Dξ z I)) := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  exact ((memWkpLoc_zero_iff.2 (hDξq.clm_comp (ContinuousLinearMap.apply ℝ V 1))).prodMk
    (memWkpLoc_zero_iff.2 (hDξq.clm_comp (ContinuousLinearMap.apply ℝ V I)))).memLpLoc.clm_comp
      (G := WithLp 2 (V × V))
      (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm.toContinuousLinearMap

private theorem isSobolevCRCoefficients_prodL2 (hJ : MemWkpLoc p Ω 1 J)
    (hDJ : HasWeakFDerivOn volume Ω J DJ) (hSp : MemLpLoc p Ω S) :
    IsSobolevCRCoefficients p Ω (fun z => prodMapL2L V (J z))
      (fun z => (prodMapL2L V).comp (DJ z))
      (fun z => conjProdL2L V (differentiatedCRCoefficient (S z) (DJ z))) := by
  have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
  have hJ₂_one := hJ.clm_comp (G := WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) (prodMapL2L V)
  have hDJ₂ := hDJ.clm_comp (G := WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) (prodMapL2L V)
  exact ⟨hDJ₂, hJ₂_one.memLpLoc, hJ₂_one.memLpLoc_of_hasWeakFDerivOn hDJ₂,
    ((memWkpLoc_zero_iff.2 hSp).differentiatedCRCoefficient hJ hDJ).memLpLoc.clm_comp
      (G := WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) (conjProdL2L V)⟩

/-- Testing the almost-everywhere equation `∂_s ξ + J ∂_t ξ + S ξ = η` against `∂_{u} ψ` and
integrating the `S ξ` and `η` terms by parts. -/
private theorem integral_fderiv_test_eq {Dξ Dη : ℂ → ℂ →L[ℝ] V}
    (hp : 2 < p) (hp_top : p ≠ ⊤) (hqp : q ≤ p) (hpq : p⁻¹ + q⁻¹ < 1)
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
  have hq1 : 1 < q := ENNReal.inv_lt_one.1 (lt_of_le_of_lt le_add_self hpq)
  have hloc := Ω.isOpen.isLocallyClosed
  have hJp : MemLpLoc p Ω J := hJ.memLpLoc
  have hDJp : MemLpLoc p Ω DJ := hJ.memLpLoc_of_hasWeakFDerivOn hDJ
  have hSp : MemLpLoc p Ω S := hS.memLpLoc
  have hDSp : MemLpLoc p Ω DS := hS.memLpLoc_of_hasWeakFDerivOn hDS
  have hDξq : MemLpLoc q Ω Dξ := hξ.memLpLoc_of_hasWeakFDerivOn hDξ
  have hc : IsSobolevCRCoefficients p Ω J DJ S := ⟨hDJ, hJp, hDJp, hSp⟩
  have hae := (hc.isWeakCRSolution_iff_ae hpq.le hp_top hq_top hDξ hξ.memLpLoc hDξq
    hsol.locallyIntegrableOn).1 hsol
  have hSξ : HasWeakFDerivOn volume Ω (fun z => S z (ξ z))
      (fun z => (ContinuousLinearMap.id ℝ (V →L[ℝ] V)).precompL ℂ (DS z) (ξ z) +
        (ContinuousLinearMap.id ℝ (V →L[ℝ] V)).precompR ℂ (S z) (Dξ z)) := by
    lift p to ℝ≥0 using hp_top
    lift q to ℝ≥0 using hq_top
    have hpR : 2 < p := by exact_mod_cast hp
    have : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast (one_lt_two.trans hpR).le⟩
    exact hDS.bilin_of_memLpLoc (ContinuousLinearMap.id ℝ (V →L[ℝ] V)) hpR (by exact_mod_cast hq1)
      (by exact_mod_cast hqp) ((hS.memLpLoc_of_holderTriple hpR le_rfl).mono_exponent le_top)
      hDSp hDξ hξ.memLpLoc hDξq
  let ψu : 𝓓(Ω, V) := ∂_{u} ψ
  have hψu (z : ℂ) : (ψu : ℂ → V) z = fderiv ℝ (ψ : ℂ → V) z u :=
    TestFunction.lineDerivOp_apply_eq_fderiv ψ u z
  have hiA : Integrable (fun z => ⟪(ψu : ℂ → V) z, Dξ z 1⟫_ℝ) := ψu.integrable_inner
    ((hDξq.clm_comp (ContinuousLinearMap.apply ℝ V 1)).locallyIntegrableOn hq1.le hloc)
  have hiB : Integrable (fun z => ⟪(ψu : ℂ → V) z, J z (Dξ z I)⟫_ℝ) :=
    ψu.integrable_inner (hJp.locallyIntegrableOn_clm_apply
      (hDξq.clm_comp (ContinuousLinearMap.apply ℝ V I)) hpq.le hloc)
  have hiAB : Integrable (fun z =>
      ⟪(ψu : ℂ → V) z, Dξ z 1⟫_ℝ + ⟪(ψu : ℂ → V) z, J z (Dξ z I)⟫_ℝ) := hiA.add hiB
  have hiC := ψu.integrable_inner (hSp.locallyIntegrableOn_clm_apply hξ.memLpLoc hpq.le hloc)
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
  have hSξ_ibp : ∫ z, ⟪fderiv ℝ (ψ : ℂ → V) z u, S z (ξ z)⟫_ℝ =
      -((∫ z, ⟪(ψ : ℂ → V) z, DS z u (ξ z)⟫_ℝ) + ∫ z, ⟪(ψ : ℂ → V) z, S z (Dξ z u)⟫_ℝ) := by
    have h := (hSξ.hasWeakLineDerivOn u).integral_inner_lineDeriv_eq_neg ψ
    simp only [TestFunction.lineDeriv_eq_fderiv, add_apply,
      ContinuousLinearMap.precompL_apply, ContinuousLinearMap.precompR_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.comp_apply, inner_add_right] at h
    have hi1 : Integrable (fun z => ⟪(ψ : ℂ → V) z, DS z u (ξ z)⟫_ℝ) :=
      ψ.integrable_inner
        ((hDSp.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) u)).locallyIntegrableOn_clm_apply
          hξ.memLpLoc hpq.le hloc)
    have hi2 : Integrable (fun z => ⟪(ψ : ℂ → V) z, S z (Dξ z u)⟫_ℝ) :=
      ψ.integrable_inner (hSp.locallyIntegrableOn_clm_apply
        (hDξq.clm_comp (ContinuousLinearMap.apply ℝ V u)) hpq.le hloc)
    rwa [integral_add hi1 hi2] at h
  have hη_ibp : ∫ z, ⟪(ψu : ℂ → V) z, η z⟫_ℝ = -∫ z, ⟪(ψ : ℂ → V) z, Dη z u⟫_ℝ := by
    simpa only [TestFunction.lineDeriv_eq_fderiv, hψu] using
      (hDη.hasWeakLineDerivOn u).integral_inner_lineDeriv_eq_neg ψ
  rw [hlhs_split, hSξ_ibp, hη_ibp] at hae_int
  linarith

/-- **The weak differentiated Cauchy–Riemann system.** Let `2 < p < ∞`, `q ≤ p` with
`1/p + 1/q < 1`, and `1 ≤ s`. If `J, S ∈ W^{1,p}_loc(Ω)` have weak derivatives `DJ, DS`,
`ξ ∈ W^{1,q}_loc(Ω)` has weak derivative `Dξ`, `η ∈ W^{1,s}_loc(Ω)` has weak derivative `Dη`, and
`ξ` solves `∂_s ξ + J ∂_t ξ + S ξ = η` weakly in `L^q_loc(Ω)`, then the pair
`Ξ = (∂_s ξ, ∂_t ξ)` in `WithLp 2 (V × V)` solves the differentiated system
`∂_s Ξ + diag(J, J) ∂_t Ξ + S₂ Ξ = (∂_s η - (∂_s S) ξ, ∂_t η - (∂_t S) ξ)` weakly in
`L^q_loc(Ω)` (McDuff–Salamon, Proposition B.4.9, Step 2). -/
theorem IsWeakCRSolution.differentiated {Dξ Dη : ℂ → ℂ →L[ℝ] V}
    (hp : 2 < p) (hp_top : p ≠ ⊤) (hqp : q ≤ p)
    (hpq : p⁻¹ + q⁻¹ < 1) (hs1 : 1 ≤ s)
    (hJ : MemWkpLoc p Ω 1 J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hS : MemWkpLoc p Ω 1 S) (hDS : HasWeakFDerivOn volume Ω S DS)
    (hξ : MemWkpLoc q Ω 1 ξ) (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hη : MemWkpLoc s Ω 1 η) (hDη : HasWeakFDerivOn volume Ω η Dη)
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η) :
    let e := WithLp.prodContinuousLinearEquiv 2 ℝ V V
    IsWeakCRSolution q Ω (fun z => prodMapL2L V (J z))
      (fun z => (prodMapL2L V).comp (DJ z))
      (fun z => conjProdL2L V (differentiatedCRCoefficient (S z) (DJ z)))
      (fun z => e.symm (Dξ z 1, Dξ z I))
      (fun z => e.symm (Dη z 1 - DS z 1 (ξ z), Dη z I - DS z I (ξ z))) := by
  intro e
  have hq1 : 1 < q := ENNReal.inv_lt_one.1 (lt_of_le_of_lt le_add_self hpq)
  have hloc := Ω.isOpen.isLocallyClosed
  have hDJp : MemLpLoc p Ω DJ := hJ.memLpLoc_of_hasWeakFDerivOn hDJ
  have hDSp : MemLpLoc p Ω DS := hS.memLpLoc_of_hasWeakFDerivOn hDS
  have hDξq : MemLpLoc q Ω Dξ := hξ.memLpLoc_of_hasWeakFDerivOn hDξ
  have hDηs : MemLpLoc s Ω Dη := hη.memLpLoc_of_hasWeakFDerivOn hDη
  have hDη_loc (u : ℂ) : LocallyIntegrableOn (fun z => Dη z u) Ω :=
    (hDηs.clm_comp (ContinuousLinearMap.apply ℝ V u)).locallyIntegrableOn hs1 hloc
  have hDSξ_loc (u : ℂ) : LocallyIntegrableOn (fun z => DS z u (ξ z)) Ω :=
    (hDSp.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) u)).locallyIntegrableOn_clm_apply
      hξ.memLpLoc hpq.le hloc
  have hc₂ := isSobolevCRCoefficients_prodL2 hJ hDJ hS.memLpLoc
  have hΞq := memLpLoc_symm_prodL2 hDξq
  refine isWeakCRSolution_iff.2
    ⟨hΞq, locallyIntegrableOn_symm_prodL2
      ((hDη_loc 1).sub (hDSξ_loc 1)) ((hDη_loc I).sub (hDSξ_loc I)),
      fun Φ => ⟨hc₂.integrable_inner_crFormalAdjoint hpq.le hΞq Φ, ?_⟩⟩
  have hrow1 :=
    integral_fderiv_test_eq hp hp_top hqp hpq hJ hDJ hS hDS hξ hDξ hDη hsol 1 (fstTestProdL2 Φ)
  have hcomm :=
    integral_inner_fderiv_one_clm_apply_eq hp hp_top hpq hJ hDJ hDξ hDξq (fstTestProdL2 Φ)
  have hrow2 :=
    integral_fderiv_test_eq hp hp_top hqp hpq hJ hDJ hS hDS hξ hDξ hDη hsol I (sndTestProdL2 Φ)
  have hsymm := (hDξ.integral_inner_fderiv_one_eq (sndTestProdL2 Φ)).symm
  have hDξ_loc (u : ℂ) : LocallyIntegrableOn (fun z => Dξ z u) Ω :=
    (hDξq.clm_comp (ContinuousLinearMap.apply ℝ V u)).locallyIntegrableOn hq1.le hloc
  have hDJu (v : ℂ) : MemLpLoc p Ω (fun z => DJ z v) :=
    hDJp.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) v)
  have hADξ_loc {A : ℂ → V →L[ℝ] V} (hA : MemLpLoc p Ω A) (u : ℂ) :
      LocallyIntegrableOn (fun z => A z (Dξ z u)) Ω :=
    hA.locallyIntegrableOn_clm_apply (hDξq.clm_comp (ContinuousLinearMap.apply ℝ V u)) hpq.le hloc
  rw [hc₂.integral_inner_crFormalAdjoint_eq_terms hpq.le hΞq Φ]
  dsimp only [e]
  simp only [ContinuousLinearMap.comp_apply, prodMapL2L_apply_symm, conjProdL2L_apply_symm,
    differentiatedCRCoefficient_apply]
  rw [integral_inner_fderiv_postcomp_prodL2 (hDξ_loc 1) (hDξ_loc I) 1 Φ,
    integral_inner_fderiv_postcomp_prodL2 (hADξ_loc hJ.memLpLoc 1) (hADξ_loc hJ.memLpLoc I) I Φ,
    integral_inner_postcomp_prodL2 (hADξ_loc (hDJu I) 1) (hADξ_loc (hDJu I) I) Φ,
    integral_inner_postcomp_prodL2_add (hADξ_loc hS.memLpLoc 1) (hADξ_loc (hDJu 1) I)
      (hADξ_loc hS.memLpLoc I) (hADξ_loc (hDJu I) I) Φ,
    integral_inner_postcomp_prodL2_sub (hDη_loc 1) (hDSξ_loc 1) (hDη_loc I) (hDSξ_loc I) Φ]
  linarith

/-! ### Interior regularity at all orders (McDuff–Salamon Proposition B.4.9) -/

/-- Two-dimensional Sobolev embedding upgrade: if `2 < p < ∞`, `1 < s ≤ p` and `η ∈ W^{1,s}_loc(Ω)`,
then `η ∈ L^{q₁}_loc(Ω)` for an exponent `q₁ : ℝ≥0` satisfying `2 < q₁ ≤ p`. -/
private theorem exists_two_lt_le_memLpLoc_of_memWkpLoc_one {p s : ℝ≥0} (hp : 2 < (p : ℝ))
    (hs1 : 1 < (s : ℝ)) (hsp : (s : ℝ) ≤ p) {η : ℂ → V} (hη : MemWkpLoc s Ω 1 η) :
    ∃ q₁ : ℝ≥0, 2 < (q₁ : ℝ) ∧ q₁ ≤ p ∧ MemLpLoc q₁ Ω η := by
  have hs0 : (0 : ℝ) < s := zero_lt_one.trans hs1
  have hp0 : (0 : ℝ) < p := by linarith
  rcases le_or_gt ((s : ℝ)⁻¹ - (p : ℝ)⁻¹) 2⁻¹ with hgap | hgap
  · exact ⟨p, hp, le_rfl,
      hη.memLpLoc_of_inv_sub_inv_le (by exact_mod_cast hs1.le) (by exact_mod_cast hsp) hgap⟩
  · -- When `1/s - 1/p > 1/2`, the critical Sobolev exponent `q₁ = (1/s - 1/2)⁻¹` satisfies
    -- `2 < q₁ < p` because `s > 1` forces `1/s - 1/2 < 1/2`.
    set b : ℝ := (s : ℝ)⁻¹ - 2⁻¹
    have hp_inv_pos : 0 < (p : ℝ)⁻¹ := inv_pos.2 hp0
    have hb_gt_p : (p : ℝ)⁻¹ < b := by dsimp only [b]; linarith
    have hb_pos : 0 < b := hp_inv_pos.trans hb_gt_p
    have hs_inv_lt : (s : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hs1
    have hb_lt_half : b < 2⁻¹ := by dsimp only [b]; linarith
    let q₁ : ℝ≥0 := ⟨b⁻¹, by positivity⟩
    have hq₁_coe : (q₁ : ℝ) = b⁻¹ := rfl
    have hq₁_inv : (q₁ : ℝ)⁻¹ = b := inv_inv b
    have hq₁_gt2 : 2 < (q₁ : ℝ) := by
      rw [hq₁_coe]
      have h := (inv_lt_inv₀ (by positivity : (0 : ℝ) < 2⁻¹) hb_pos).2 hb_lt_half
      norm_num at h
      exact h
    have hq₁_le_p : q₁ ≤ p := by
      apply NNReal.coe_le_coe.1
      rw [hq₁_coe]
      have h := (inv_lt_inv₀ hb_pos hp_inv_pos).2 hb_gt_p
      rw [inv_inv] at h
      exact h.le
    have hs_le_q₁ : s ≤ q₁ := by
      apply NNReal.coe_le_coe.1
      rw [hq₁_coe]
      have hb_lt_s : b < (s : ℝ)⁻¹ := by dsimp only [b]; linarith
      have h := (inv_lt_inv₀ (inv_pos.2 hs0) hb_pos).2 hb_lt_s
      rw [inv_inv] at h
      exact h.le
    exact ⟨q₁, hq₁_gt2, hq₁_le_p,
      hη.memLpLoc_of_inv_sub_inv_le (by exact_mod_cast hs1.le) hs_le_q₁
        (by rw [hq₁_inv]; dsimp only [b]; linarith)⟩

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
    -- Induction at `k'` puts `ξ` in `W^{k'+1, s}_loc(Ω)`.
    have hξ_s : MemWkpLoc s Ω (k' + 1) ξ :=
      ih hpq hℓ (by omega) (by omega) hJ hDJ hJsq hS hsol hη.of_succ
    obtain ⟨Dξ, hDξ, -⟩ := hξ_s.exists_weakFDeriv_of_isOpen
    -- Lift `p` and `s` to `ℝ≥0` to apply 2D Sobolev embedding and mixed-exponent products.
    have hs_top : s ≠ ⊤ := ne_top_of_le_ne_top hp_top hsp
    lift p to ℝ≥0 using hp_top
    lift s to ℝ≥0 using hs_top
    have hpR : 2 < (p : ℝ) := by exact_mod_cast hp
    have hs1R : 1 < (s : ℝ) := by exact_mod_cast hs1
    have hspR : (s : ℝ) ≤ p := by exact_mod_cast hsp
    -- `η ∈ W^{1,s}_loc(Ω)` embeds into `L^{q₁}_loc(Ω)` for some `2 < q₁ ≤ p`.
    obtain ⟨q₁, hq₁R, hq₁_le_p, hη_q₁⟩ :=
      exists_two_lt_le_memLpLoc_of_memWkpLoc_one hpR hs1R hspR (hη.of_le (by omega))
    have hq₁_gt1 : (1 : ℝ≥0∞) < q₁ := by exact_mod_cast one_lt_two.trans hq₁R
    have hpq₁ : (p : ℝ≥0∞)⁻¹ + (q₁ : ℝ≥0∞)⁻¹ < 1 := by
      have hp0 : (0 : ℝ) < p := by linarith
      have hq₁0 : (0 : ℝ) < q₁ := by linarith
      have hp_inv : (p : ℝ)⁻¹ < 2⁻¹ := (inv_lt_inv₀ hp0 zero_lt_two).2 hpR
      have hq₁_inv : (q₁ : ℝ)⁻¹ < 2⁻¹ := (inv_lt_inv₀ hq₁0 zero_lt_two).2 hq₁R
      have hsum : (p : ℝ)⁻¹ + (q₁ : ℝ)⁻¹ < 1 := by linarith
      rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal (p := q₁),
        ← ENNReal.ofReal_inv_of_pos hp0, ← ENNReal.ofReal_inv_of_pos hq₁0,
        ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_lt_ofReal_iff zero_lt_one |>.2 hsum
    -- Order-zero regularity puts `ξ` in `W^{1, q₁}_loc(Ω)` and upgrades `hsol` to exponent `q₁`.
    have hξ_q₁ : MemWkpLoc q₁ Ω 1 ξ :=
      hsol.memWkpLoc_one_of_memLpLoc hp ENNReal.coe_ne_top hpq hq₁_gt1
        (by exact_mod_cast hq₁_le_p) (hJ.of_le hℓ) hDJ hJsq hS.memLpLoc hη_q₁
    have hDξ_q₁ : MemLpLoc q₁ Ω Dξ := hξ_q₁.memLpLoc_of_hasWeakFDerivOn hDξ
    have hc : IsSobolevCRCoefficients p Ω J DJ S :=
      ⟨hDJ, hJ.memLpLoc, (hJ.of_le hℓ).memLpLoc_of_hasWeakFDerivOn hDJ, hS.memLpLoc⟩
    have hsol₁ : IsWeakCRSolution q₁ Ω J DJ S ξ η := by
      rcases le_or_gt (q₁ : ℝ≥0∞) q with hle | hlt
      · exact hsol.mono_exponent hle
      · have hq_top : q ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hlt.le
        have hae := (hc.isWeakCRSolution_iff_ae hpq.le ENNReal.coe_ne_top hq_top hDξ
          hsol.memLpLoc (hDξ_q₁.mono_exponent hlt.le) hsol.locallyIntegrableOn).1 hsol
        exact (hc.isWeakCRSolution_iff_ae hpq₁.le ENNReal.coe_ne_top ENNReal.coe_ne_top hDξ
          hξ_q₁.memLpLoc hDξ_q₁ hsol.locallyIntegrableOn).2 hae
    -- Differentiate the equation weakly on `V₂ = WithLp 2 (V × V)`.
    have hSm' : MemWkpLoc p Ω (k' + 1) S := hS.of_le hkm
    obtain ⟨DS, hDS, hDS_k'⟩ := hSm'.exists_weakFDeriv_of_isOpen
    obtain ⟨Dη, hDη, hDη_k'⟩ := hη.exists_weakFDeriv_of_isOpen
    have hsol₂ := hsol₁.differentiated hp ENNReal.coe_ne_top (by exact_mod_cast hq₁_le_p) hpq₁
      hs1.le (hJ.of_le hℓ) hDJ (hSm'.of_le (by omega)) hDS hξ_q₁ hDξ (hη.of_le (by omega)) hDη
    -- Regularity of `J₂`, `S₂` and the right-hand side `Η` on `WithLp 2 (V × V)`.
    let e := WithLp.prodContinuousLinearEquiv 2 ℝ V V
    have : CompleteSpace V := FiniteDimensional.completeSpace ℝ V
    have hmax : max 1 k' ≤ ℓ := max_le hℓ (Nat.le_of_succ_le hkℓ)
    have hJ₂ : MemWkpLoc p Ω (max 1 k') (fun z => prodMapL2L V (J z)) :=
      (hJ.of_le hmax).clm_comp (G := WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) (prodMapL2L V)
    have hDJ₂ : HasWeakFDerivOn volume Ω (fun z => prodMapL2L V (J z))
        (fun z => (prodMapL2L V).comp (DJ z)) :=
      hDJ.clm_comp (G := WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) (prodMapL2L V)
    have hJ₂sq : ∀ᵐ z ∂volume.restrict Ω,
        (prodMapL2L V (J z)).comp (prodMapL2L V (J z)) =
          -ContinuousLinearMap.id ℝ (WithLp 2 (V × V)) :=
      hJsq.mono fun z hz => prodMapL2L_comp_self_eq_neg_id hz
    have hS₂ : MemWkpLoc p Ω k'
        (fun z => conjProdL2L V (differentiatedCRCoefficient (S z) (DJ z))) :=
      ((hS.of_le (by omega)).differentiatedCRCoefficient (hJ.of_le hkℓ) hDJ).clm_comp
        (G := WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) (conjProdL2L V)
    have hΗ_comp (v : ℂ) : MemWkpLoc s Ω k' (fun z => Dη z v - DS z v (ξ z)) := by
      have h1 : MemWkpLoc s Ω k' (fun z => Dη z v) :=
        hDη_k'.clm_comp (G := V) (ContinuousLinearMap.apply ℝ V v)
      have hDSv : MemWkpLoc p Ω k' (fun z => DS z v) :=
        hDS_k'.clm_comp (G := V →L[ℝ] V) (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) v)
      have h2 : MemWkpLoc s Ω k' (fun z => DS z v (ξ z)) := by
        cases k' with
        | zero =>
          have : Fact (1 ≤ (s : ℝ≥0∞)) := ⟨by exact_mod_cast hs1.le⟩
          exact memWkpLoc_zero_iff.2
            (MemLpLoc.bilin_of_memWkpLoc (ContinuousLinearMap.id ℝ (V →L[ℝ] V))
              (by exact_mod_cast hp) (by exact_mod_cast hsp) hDSv.memLpLoc hξ_s)
        | succ k'' =>
          exact hDSv.clm_apply_succ (by exact_mod_cast hp) (by exact_mod_cast hs1)
            (by exact_mod_cast hsp) hξ_s.of_succ
      exact h1.sub h2
    have hΗ : MemWkpLoc s Ω k'
        (fun z => e.symm (Dη z 1 - DS z 1 (ξ z), Dη z I - DS z I (ξ z))) :=
      ((hΗ_comp 1).prodMk (hΗ_comp I)).clm_comp (G := WithLp 2 (V × V))
        e.symm.toContinuousLinearMap
    -- Induction hypothesis on `WithLp 2 (V × V)` puts `Ξ` in `W^{k'+1, s}_loc(Ω)`.
    have hΞ_s : MemWkpLoc s Ω (k' + 1) (fun z => e.symm (Dξ z 1, Dξ z I)) :=
      ih hpq₁ (le_max_left 1 k') (le_max_right 1 k') le_rfl hJ₂ hDJ₂ hJ₂sq hS₂ hsol₂ hΗ
    have hDξ1 : MemWkpLoc s Ω (k' + 1) (fun z => Dξ z 1) := by
      simpa [e] using hΞ_s.clm_comp (G := V)
        ((ContinuousLinearMap.fst ℝ V V).comp e.toContinuousLinearMap)
    have hDξI : MemWkpLoc s Ω (k' + 1) (fun z => Dξ z I) := by
      simpa [e] using hΞ_s.clm_comp (G := V)
        ((ContinuousLinearMap.snd ℝ V V).comp e.toContinuousLinearMap)
    exact hξ_s.memLpLoc.memWkpLoc_succ_of_hasWeakFDerivOn
      (by rwa [Opens.interior_coe]) hDξ1 hDξI

/-- **Higher-order interior regularity at the solution's exponent.** If `2 < p < ∞`,
`1/p + 1/q < 1`, `q ≤ p`, `1 ≤ ℓ`, `k ≤ ℓ`, `k ≤ m`, `J ∈ W^{ℓ,p}_loc(Ω)` with `J² = -1` almost
everywhere on `Ω`, `S ∈ W^{m,p}_loc(Ω)`, and `ξ` solves `∂_s ξ + J ∂_t ξ + S ξ = η` weakly in
`L^q_loc(Ω)` with `η ∈ W^{k,q}_loc(Ω)`, then `ξ ∈ W^{k+1,q}_loc(Ω)`. -/
theorem IsWeakCRSolution.memWkpLoc {k ℓ m : ℕ} (hp : 2 < p) (hp_top : p ≠ ⊤)
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
theorem IsWeakCRSolution.memWkpLoc_coeff {k ℓ m : ℕ} (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hpq : p⁻¹ + q⁻¹ < 1) (hℓ : 1 ≤ ℓ) (hkℓ : k ≤ ℓ) (hkm : k ≤ m)
    (hJ : MemWkpLoc p Ω ℓ J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ V)
    (hS : MemWkpLoc p Ω m S) (hsol : IsWeakCRSolution q Ω J DJ S ξ η)
    (hη : MemWkpLoc p Ω k η) :
    MemWkpLoc p Ω (k + 1) ξ :=
  hsol.memWkpLoc_of_memWkpLoc hp hp_top hpq ((by norm_num : (1 : ℝ≥0∞) < 2).trans hp) le_rfl hℓ
    hkℓ hkm hJ hDJ hJsq hS hη

end InnerProduct

/-! ### Transfer to finite-dimensional real normed spaces -/

section NormedSpace

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {Ω : Opens ℂ} {p q s : ℝ≥0∞}

/-- **Interior regularity for the almost-everywhere linear Cauchy–Riemann equation on any
finite-dimensional real normed space.** Let `2 < p < ∞`, `1/p + 1/q < 1`, `q ≠ ⊤`, `1 < s ≤ p`,
`1 ≤ ℓ`, `k ≤ ℓ` and `k ≤ m`. If `J ∈ W^{ℓ,p}_loc(Ω; W →L[ℝ] W)` satisfies `J² = -1` almost
everywhere on `Ω`, `S ∈ W^{m,p}_loc(Ω; W →L[ℝ] W)`, `ξ ∈ W^{1,q}_loc(Ω; W)` has a weak derivative
`Dξ` satisfying `Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z` almost everywhere on `Ω`, and
`η ∈ W^{k,s}_loc(Ω; W)`, then `ξ ∈ W^{k+1,s}_loc(Ω; W)`. -/
theorem memWkpLoc_of_ae_linearCR {k ℓ m : ℕ} {J S : ℂ → W →L[ℝ] W} {ξ η : ℂ → W}
    {Dξ : ℂ → ℂ →L[ℝ] W} (hp : 2 < p) (hp_top : p ≠ ⊤) (hpq : p⁻¹ + q⁻¹ < 1) (hq_top : q ≠ ⊤)
    (hs1 : 1 < s) (hsp : s ≤ p) (hℓ : 1 ≤ ℓ) (hkℓ : k ≤ ℓ) (hkm : k ≤ m)
    (hJ : MemWkpLoc p Ω ℓ J)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ W)
    (hS : MemWkpLoc p Ω m S) (hξ : MemWkpLoc q Ω 1 ξ) (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (hae : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z)
    (hη : MemWkpLoc s Ω k η) :
    MemWkpLoc s Ω (k + 1) ξ := by
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
  have hξ' : MemWkpLoc q Ω 1 ξ' := e.comp_memWkpLoc_iff.2 hξ
  have hDξ' : HasWeakFDerivOn volume Ω ξ' Dξ' := hDξ.clm_comp e.toContinuousLinearMap
  have hDξ'q : MemLpLoc q Ω Dξ' := hξ'.memLpLoc_of_hasWeakFDerivOn hDξ'
  have hη' : MemWkpLoc s Ω k η' := e.comp_memWkpLoc_iff.2 hη
  have hη'_loc : LocallyIntegrableOn η' Ω :=
    hη'.memLpLoc.locallyIntegrableOn hs1.le Ω.isOpen.isLocallyClosed
  have hc' : IsSobolevCRCoefficients p Ω J' DJ' S' :=
    ⟨hDJ', hJ'.memLpLoc, (hJ'.of_le hℓ).memLpLoc_of_hasWeakFDerivOn hDJ', hS'.memLpLoc⟩
  have hsol' : IsWeakCRSolution q Ω J' DJ' S' ξ' η' := by
    refine (hc'.isWeakCRSolution_iff_ae hpq.le hp_top hq_top hDξ' hξ'.memLpLoc hDξ'q hη'_loc).2 ?_
    filter_upwards [hae] with z hz
    have he := congrArg e hz
    simpa [J', S', ξ', Dξ', η', eEnd, map_add] using he
  exact e.comp_memWkpLoc_iff.1
    (hsol'.memWkpLoc_of_memWkpLoc hp hp_top hpq hs1 hsp hℓ hkℓ hkm hJ' hDJ' hJ'sq hS' hη')

/-- **Interior Sobolev regularity for homogeneous linear Cauchy–Riemann solutions.** If `2 < p < ∞`,
`1 < q ≤ p`, `1 ≤ ℓ`, `k ≤ ℓ`, `k ≤ m`, `J ∈ W^{ℓ,p}_loc(Ω)` with `J² = -1` almost everywhere on
`Ω`, `S ∈ W^{m,p}_loc(Ω)`, and `ξ` satisfies `IsWeakLinearCauchyRiemannOn q Ω J S ξ`, then
`ξ ∈ W^{k+1,p}_loc(Ω)` (and in particular `ξ ∈ W^{k+1,q}_loc(Ω)`). -/
theorem IsWeakLinearCauchyRiemannOn.memWkpLoc_coeff {k ℓ m : ℕ} {J S : ℂ → W →L[ℝ] W} {ξ : ℂ → W}
    (h : IsWeakLinearCauchyRiemannOn q Ω J S ξ) (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hpq : p⁻¹ + q⁻¹ < 1) (hq_top : q ≠ ⊤) (hℓ : 1 ≤ ℓ) (hkℓ : k ≤ ℓ) (hkm : k ≤ m)
    (hJ : MemWkpLoc p Ω ℓ J)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ W)
    (hS : MemWkpLoc p Ω m S) :
    MemWkpLoc p Ω (k + 1) ξ := by
  obtain ⟨-, hξq, D, hD, hDq, hae⟩ := isWeakLinearCauchyRiemannOn_iff_of_isOpen.1 h
  have hξ1 : MemWkpLoc q Ω 1 ξ :=
    memWkpLoc_succ_iff_of_isOpen.2 ⟨hξq, D, hD, memWkpLoc_zero_iff.2 hDq⟩
  exact memWkpLoc_of_ae_linearCR hp hp_top hpq hq_top ((by norm_num : (1 : ℝ≥0∞) < 2).trans hp)
    le_rfl hℓ hkℓ hkm hJ hJsq hS hξ1 hD hae memWkpLoc_zero_fun

/-- **Interior Sobolev regularity at the solution's exponent for homogeneous linear solutions.** -/
theorem IsWeakLinearCauchyRiemannOn.memWkpLoc {k ℓ m : ℕ} {J S : ℂ → W →L[ℝ] W} {ξ : ℂ → W}
    (h : IsWeakLinearCauchyRiemannOn q Ω J S ξ) (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hpq : p⁻¹ + q⁻¹ < 1) (hqp : q ≤ p) (hℓ : 1 ≤ ℓ) (hkℓ : k ≤ ℓ) (hkm : k ≤ m)
    (hJ : MemWkpLoc p Ω ℓ J)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ W)
    (hS : MemWkpLoc p Ω m S) :
    MemWkpLoc q Ω (k + 1) ξ :=
  (h.memWkpLoc_coeff hp hp_top hpq (ne_top_of_le_ne_top hp_top hqp) hℓ hkℓ hkm hJ hJsq
    hS).mono_exponent hqp

/-- **Smoothness of homogeneous linear Cauchy–Riemann solutions for smooth coefficients.** For
every `1 < q ≤ ∞`, if `J` and `S` are smooth on `Ω` with `J² = -1` on `Ω` and `ξ` satisfies
`IsWeakLinearCauchyRiemannOn q Ω J S ξ`, then `ξ` is smooth on `Ω`. -/
theorem IsWeakLinearCauchyRiemannOn.contDiffOn {J S : ℂ → W →L[ℝ] W} {ξ : ℂ → W}
    (h : IsWeakLinearCauchyRiemannOn q Ω J S ξ) (hq : 1 < q)
    (hJ : ContDiffOn ℝ ∞ J Ω)
    (hJsq : ∀ z ∈ (Ω : Set ℂ), (J z).comp (J z) = -ContinuousLinearMap.id ℝ W)
    (hS : ContDiffOn ℝ ∞ S Ω) :
    ContDiffOn ℝ ∞ ξ Ω := by
  -- Choose a finite exponent `p > 2` large enough that `1/p + 1/min(q, 3) < 1`.
  have hq₀_top : min q 3 ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) (min_le_right q 3)
  let q₀ : ℝ≥0 := (min q 3).toNNReal
  have hq₀_eq : (q₀ : ℝ≥0∞) = min q 3 := ENNReal.coe_toNNReal hq₀_top
  have hq₀_gt1 : (1 : ℝ≥0∞) < q₀ := hq₀_eq.symm ▸ lt_min hq (by norm_num)
  have hq₀R : 1 < (q₀ : ℝ) := by exact_mod_cast hq₀_gt1
  have hq₀_inv_lt : (q₀ : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq₀R
  let p : ℝ≥0 := max 3 ⟨2 * (1 - (q₀ : ℝ)⁻¹)⁻¹, by positivity⟩
  have hp_gt2 : (2 : ℝ≥0∞) < p := by
    have : (3 : ℝ) ≤ p := le_max_left _ _
    exact_mod_cast (by linarith : (2 : ℝ) < p)
  have hpq₀ : (p : ℝ≥0∞)⁻¹ + (q₀ : ℝ≥0∞)⁻¹ < 1 := by
    have hp0 : (0 : ℝ) < p := by
      have : (3 : ℝ) ≤ p := le_max_left _ _
      linarith
    have hq₀0 : (0 : ℝ) < q₀ := zero_lt_one.trans hq₀R
    have hp_ge : 2 * (1 - (q₀ : ℝ)⁻¹)⁻¹ ≤ (p : ℝ) := le_max_right _ _
    have hp_inv : (p : ℝ)⁻¹ ≤ (2 * (1 - (q₀ : ℝ)⁻¹)⁻¹)⁻¹ :=
      (inv_le_inv₀ hp0 (by positivity)).2 hp_ge
    have hrhs_eq : (2 * (1 - (q₀ : ℝ)⁻¹)⁻¹)⁻¹ = (1 - (q₀ : ℝ)⁻¹) / 2 := by
      rw [mul_inv, inv_inv]
      ring
    have hsum : (p : ℝ)⁻¹ + (q₀ : ℝ)⁻¹ < 1 := by linarith
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal (p := q₀),
      ← ENNReal.ofReal_inv_of_pos hp0, ← ENNReal.ofReal_inv_of_pos hq₀0,
      ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).2 hsum
  have h₀ : IsWeakLinearCauchyRiemannOn q₀ Ω J S ξ :=
    h.mono_exponent (hq₀_eq.trans_le (min_le_left q 3))
  have hJsq_ae : ∀ᵐ z ∂volume.restrict Ω, (J z).comp (J z) = -ContinuousLinearMap.id ℝ W :=
    (ae_restrict_iff' Ω.isOpen.measurableSet).2 (.of_forall hJsq)
  refine contDiffOn_infty.2 fun k => ?_
  have hℓ : 1 ≤ max 1 k := le_max_left 1 k
  have hkℓ : k ≤ max 1 k := le_max_right 1 k
  have hJp : MemWkpLoc p Ω (max 1 k) J :=
    (hJ.of_le (WithTop.coe_le_coe.2 le_top)).memWkpLoc subset_rfl
  have hSp : MemWkpLoc p Ω (max 1 k) S :=
    (hS.of_le (WithTop.coe_le_coe.2 le_top)).memWkpLoc subset_rfl
  have hξ_sob : MemWkpLoc p Ω (k + 1) ξ :=
    h₀.memWkpLoc_coeff hp_gt2 ENNReal.coe_ne_top hpq₀ ENNReal.coe_ne_top hℓ hkℓ hkℓ hJp hJsq_ae hSp
  obtain ⟨g, hg, hξg⟩ := hξ_sob.exists_contDiffOn_ae_eq hp_gt2
  exact hg.congr (Measure.eqOn_open_of_ae_eq hξg Ω.isOpen h.continuousOn hg.continuousOn)

end NormedSpace

end TauCeti
