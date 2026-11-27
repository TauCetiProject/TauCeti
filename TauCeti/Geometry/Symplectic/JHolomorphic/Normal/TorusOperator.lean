/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Algebra.Quotient
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Trivial.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Fredholm
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.CauchyRiemann.Regularity
public import TauCeti.Geometry.Symplectic.JHolomorphic.Normal.PhaseFrame
import TauCeti.Geometry.Manifold.Algebra.Quotient.Tangent
import TauCeti.Geometry.Manifold.VectorBundle.Trivial

/-!
# The normal operator of a torus on the trivial line and its Fredholm realization

Let `C = ℂ ⧸ Λ` be a torus, for a discrete subgroup `Λ` of `ℂ`, with its complex structure as a
quotient manifold. In Taubes's count of pseudoholomorphic curves, an embedded square-zero torus is
labelled by its normal Cauchy–Riemann operator twisted by each of its four real flat sign lines
(`TauCeti.signTwisted`, `TauCeti.cauchyRiemannKernel`). In the phase frame of a sign character
each twisted operator becomes an operator `∂bar + ν + μ conj` on `Λ`-periodic maps
(`TauCeti.phaseKernelEquiv`), that is on sections of the trivial line over `C`. This file builds
that operator on `C` and its Fredholm realization.

**The operator.** For coefficients `ν μ : C → ℂ`,
`TauCeti.torusCauchyRiemannOperator Λ ν μ` sends a function `σ : C → ℂ`, a section of the trivial
line `C × ℂ`, to the `(0,1)`-form

`D σ = ∂bar σ + (ν σ + μ conj σ) dzbar`,

where `∂bar` is `TauCeti.SmoothAlmostComplexStructure.dbarFunction` for the complex structure of
`C`, and `dzbar = TauCeti.torusConjForm Λ x : v ↦ conj v` on every tangent space `ℂ`. It is a real
Cauchy–Riemann operator in the sense of McDuff–Salamon, Definition C.1.5
(`TauCeti.isRealCauchyRiemannOperator_torusCauchyRiemannOperator`), and for smooth coefficients it
is smooth (`TauCeti.contMDiffCovariantDerivativeOn_torusCauchyRiemannOperator`): the tangent bundle
of `C` is trivial, with `dzbar` a smooth one-form (`AddSubgroup.contMDiffAt_oneForm_quotient_iff`).

**On the plane.** At the class of `z ∈ ℂ`, `D σ` is `(∂bar v + ν v + μ conj v)(z) dzbar` for the
lift `v = σ ∘ (↑)` (`TauCeti.torusCauchyRiemannOperator_quotientMk_apply`), so `σ` is a
differentiable solution of `D σ = 0` exactly when `v` lies in the kernel
`TauCeti.cauchyRiemannKernel` for the lifted coefficients
(`TauCeti.comp_quotientMk_mem_cauchyRiemannKernel_iff`); lifts are `Λ`-periodic
(`TauCeti.comp_quotientMk_mem_signTwisted_zero`).

**The realization.** Given a finite bundle atlas of the trivial line, which exists when `C` is
compact (`TauCeti.FiniteBundleAtlas.nonempty`), for instance when `Λ` is a full lattice
(`QuotientAddGroup.instCompactSpaceOfIsZLattice`), and smooth coefficients,
`TauCeti.torusCauchyRiemannSobolevL` is the realization
`W^{1,p}(C, ℂ) → Lᵖ(C, Λ^{0,1})` of `D`. For `1 < p < ∞`:

* it is Fredholm (`TauCeti.isFredholm_torusCauchyRiemannSobolevL`), and its index does not depend
  on the coefficients (`TauCeti.index_torusCauchyRiemannSobolevL_eq`);
* its kernel embeds into the `Λ`-periodic solutions of `∂bar v + ν v + μ conj v = 0` on `ℂ` by
  lifting (`TauCeti.kerTorusCauchyRiemannSobolevLLift`,
  `TauCeti.kerTorusCauchyRiemannSobolevLLift_injective`), with image exactly the `C¹` periodic
  solutions (`TauCeti.mem_range_kerTorusCauchyRiemannSobolevLLift_iff`);
* hence it is injective when there is no nonzero periodic solution
  (`TauCeti.ker_torusCauchyRiemannSobolevL_eq_bot`), and, in the phase frame of a sign character
  `χ`, when the normal operator has no nonzero solution twisted by `χ`
  (`TauCeti.ker_torusCauchyRiemannSobolevL_eq_bot_of_signTwisted`).

The index itself, which is `0` by the Riemann–Roch theorem for the trivial line over a torus, and
the determinant lines of these realizations are not computed here. For the square torus, modelled
as the product of two circles, the kernel and cokernel of `∂bar` on smooth sections are computed by
Fourier series in `TauCeti.UnitAddTorus.finrank_ker_sub_finrank_cokernel_cauchyRiemannOperatorₗ`.

## Main definitions

* `TauCeti.torusCauchyRiemannOperator`: the operator `∂bar + ν + μ conj` on functions on `ℂ ⧸ Λ`.
* `TauCeti.torusCauchyRiemannSobolevL`: its realization `W^{1,p} → Lᵖ`.
* `TauCeti.kerTorusCauchyRiemannSobolevLLift`: the kernel of the realization, lifted to periodic
  solutions on `ℂ`.

## Main results

* `TauCeti.isRealCauchyRiemannOperator_torusCauchyRiemannOperator`,
  `TauCeti.contMDiffCovariantDerivativeOn_torusCauchyRiemannOperator`: it is a smooth real
  Cauchy–Riemann operator.
* `TauCeti.isFredholm_torusCauchyRiemannSobolevL`: the realization is Fredholm.
* `TauCeti.mem_range_kerTorusCauchyRiemannSobolevLLift_iff`: its kernel is the space of `C¹`
  periodic solutions.
* `TauCeti.ker_torusCauchyRiemannSobolevL_eq_bot_of_signTwisted`: nondegeneracy of a twisted
  normal operator makes the realization of its periodic operator injective.

## References

* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  **44** (1996), 818–893.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix C.1 (real Cauchy–Riemann operators) and Theorem C.1.10.
-/

public section

noncomputable section

open Bundle Set MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace TauCeti

variable {Λ : AddSubgroup ℂ} [DiscreteTopology Λ]

open SmoothAlmostComplexStructure ComplexConjugate

variable (Λ) in
/-- The one-form `dzbar : v ↦ conj v` on the tangent space `ℂ` of `ℂ ⧸ Λ` at `x`. -/
def torusConjForm (x : ℂ ⧸ Λ) : TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℂ :=
  (Complex.conjCLE : ℂ →L[ℝ] ℂ)

@[simp]
theorem torusConjForm_apply (x : ℂ ⧸ Λ) (v : ℂ) : torusConjForm Λ x v = conj v :=
  (rfl)

variable (Λ) in
/-- The **normal Cauchy–Riemann operator of a torus on the trivial line**: for coefficients
`ν μ : ℂ ⧸ Λ → ℂ`, the operator

`D σ = ∂bar σ + (ν σ + μ conj σ) dzbar`

on functions `σ : ℂ ⧸ Λ → ℂ`, the sections of the trivial line `(ℂ ⧸ Λ) × ℂ`. Here `∂bar` is
`TauCeti.SmoothAlmostComplexStructure.dbarFunction` for the complex structure of `ℂ ⧸ Λ`, and
`dzbar` is the one-form `v ↦ conj v` on every tangent space `ℂ`. -/
def torusCauchyRiemannOperator (ν μ : ℂ ⧸ Λ → ℂ) (σ : ℂ ⧸ Λ → ℂ) (x : ℂ ⧸ Λ) :
    TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℂ :=
  (ofComplexManifold ℂ (ℂ ⧸ Λ)).dbarFunction σ x +
    (ν x * σ x + μ x * conj (σ x)) • torusConjForm Λ x

variable {ν μ : ℂ ⧸ Λ → ℂ}

theorem torusCauchyRiemannOperator_apply (σ : ℂ ⧸ Λ → ℂ) (x : ℂ ⧸ Λ) (v : ℂ) :
    torusCauchyRiemannOperator Λ ν μ σ x v =
      (ofComplexManifold ℂ (ℂ ⧸ Λ)).dbarFunction σ x v +
        (ν x * σ x + μ x * conj (σ x)) * conj v :=
  (rfl)

variable (Λ ν μ) in
/-- The zeroth-order term `ξ ↦ (ν ξ + μ conj ξ) dzbar` of `torusCauchyRiemannOperator`. -/
private def zeroOrder (x : ℂ ⧸ Λ) : ℂ →L[ℝ] ℂ →L[ℝ] ℂ :=
  ((ContinuousLinearMap.lsmul ℝ ℂ).flip (Complex.conjCLE : ℂ →L[ℝ] ℂ)).comp
    (ν x • ContinuousLinearMap.id ℝ ℂ + μ x • (Complex.conjCLE : ℂ →L[ℝ] ℂ))

omit [DiscreteTopology Λ] in
private theorem zeroOrder_apply (x : ℂ ⧸ Λ) (ξ v : ℂ) :
    zeroOrder Λ ν μ x ξ v = (ν x * ξ + μ x * conj ξ) * conj v := by
  simp [zeroOrder]
  ring

omit [DiscreteTopology Λ] in
/-- `zeroOrder Λ ν μ x ξ` is `(ν x ξ + μ x conj ξ) • dzbar`, with `dzbar = conj`. -/
private theorem zeroOrder_eq_smul (x : ℂ ⧸ Λ) (ξ : ℂ) :
    zeroOrder Λ ν μ x ξ = (ν x * ξ + μ x * conj ξ) • (Complex.conjCLE : ℂ →L[ℝ] ℂ) := by
  ext v
  rw [zeroOrder_apply, smul_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
    smul_eq_mul]

variable (ν μ) in
/-- `torusCauchyRiemannOperator` is a **real Cauchy–Riemann operator** on the trivial line over
`ℂ ⧸ Λ`: `∂bar` is one, and `(ν σ + μ conj σ) dzbar` is a real-linear zeroth-order term with values
in `(0,1)`-forms. -/
theorem isRealCauchyRiemannOperator_torusCauchyRiemannOperator :
    IsRealCauchyRiemannOperator ℂ (ofComplexManifold ℂ (ℂ ⧸ Λ)) (V := Trivial (ℂ ⧸ Λ) ℂ)
      (torusCauchyRiemannOperator Λ ν μ) := by
  have h := (ofComplexManifold ℂ (ℂ ⧸ Λ)).isRealCauchyRiemannOperator_dbarFunction.add_zeroOrder
    (V := Trivial (ℂ ⧸ Λ) ℂ) (fun x ↦ zeroOrder Λ ν μ x) fun x ξ ↦ isZeroOneForm_iff.2 fun v ↦ ?_
  · -- `h` is the claim: its zeroth-order term is `(ν σ + μ conj σ) • dzbar`, with `dzbar` the
    -- form `torusConjForm Λ x = Complex.conjCLE` on the tangent space `ℂ`.
    convert h using 3
    exact congrArg (_ + ·) (zeroOrder_eq_smul _ _).symm
  · -- The tangent space `TangentSpace 𝓘(ℝ, ℂ) x` is `ℂ` by definition; restate `v` as a complex
    -- number to evaluate `zeroOrder`, whose type uses the instances of `ℂ`.
    obtain ⟨w, rfl⟩ : ∃ w : ℂ, w = v := ⟨v, rfl⟩
    have hJ : (ofComplexManifold ℂ (ℂ ⧸ Λ)).toEndomorphism x w = Complex.I * w :=
      ofComplexManifold_apply x w
    beta_reduce
    rw [hJ]
    -- Read the goal with the instances of `ℂ`, so that `zeroOrder_apply` rewrites it.
    change zeroOrder Λ ν μ x ξ (Complex.I * w) = -(Complex.I * zeroOrder Λ ν μ x ξ w)
    rw [zeroOrder_apply, zeroOrder_apply]
    simp only [map_mul, Complex.conj_I]
    ring

/-- For `C^n` coefficients, `n ≤ ∞`, `torusCauchyRiemannOperator` is **`C^n`**: it sends
`C^(n + 1)` functions to `C^n` sections of `Hom(T(ℂ ⧸ Λ), ℂ)`. -/
theorem contMDiffCovariantDerivativeOn_torusCauchyRiemannOperator {n : ℕ∞ω} (hn : n ≤ (∞ : ℕ∞ω))
    (hν : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n ν) (hμ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n μ) :
    ContMDiffCovariantDerivativeOn ℂ n (V := Trivial (ℂ ⧸ Λ) ℂ)
      (torusCauchyRiemannOperator Λ ν μ) univ where
  contMDiff {σ} hσ := by
    have hd := ((ofComplexManifold ℂ (ℂ ⧸ Λ)).contMDiffCovariantDerivativeOn_dbarFunction
      (F := ℂ) hn).contMDiff hσ
    rw [contMDiffOn_univ] at hσ hd ⊢
    have hσ' : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n σ :=
      (Trivial.contMDiff_mk_iff.1 hσ).2.of_le le_self_add
    have hf : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) n fun x ↦ ν x * σ x + μ x * conj (σ x) :=
      (contDiff_mul.comp_contMDiff (hν.prodMk_space hσ')).add (contDiff_mul.comp_contMDiff
        (hμ.prodMk_space ((Complex.conjCLE : ℂ →L[ℝ] ℂ).contDiff.comp_contMDiff hσ')))
    have hz : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] ℂ)) n fun x ↦
        TotalSpace.mk' (ℂ →L[ℝ] ℂ)
          (E := fun y ↦ TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] Trivial (ℂ ⧸ Λ) ℂ y) x
          ((ν x * σ x + μ x * conj (σ x)) • torusConjForm Λ x) := fun x ↦
      AddSubgroup.contMDiffAt_oneForm_quotient_iff.2
        ((((ContinuousLinearMap.lsmul ℝ ℂ).flip
          (Complex.conjCLE : ℂ →L[ℝ] ℂ)).contDiff.comp_contMDiff hf) x)
    exact hd.add_section hz

/-- `∂bar` of a function on `ℂ ⧸ Λ`, at the class of `z`, is the conjugate Wirtinger derivative
of its lift to `ℂ` at `z`. -/
theorem SmoothAlmostComplexStructure.dbarFunction_ofComplexManifold_quotientMk_apply
    (σ : ℂ ⧸ Λ → ℂ) (z v : ℂ) :
    (ofComplexManifold ℂ (ℂ ⧸ Λ)).dbarFunction σ z v =
      conjWirtingerDeriv (fun w : ℂ ↦ σ w) z v := by
  have hJ : (ofComplexManifold ℂ (ℂ ⧸ Λ)) (z : ℂ ⧸ Λ) v = Complex.I * v :=
    ofComplexManifold_apply _ v
  refine ((ofComplexManifold ℂ (ℂ ⧸ Λ)).dbarFunction_apply σ (z : ℂ ⧸ Λ) v).trans ?_
  rw [hJ, AddSubgroup.mvfderiv_quotientMk_apply, AddSubgroup.mvfderiv_quotientMk_apply,
    conjWirtingerDeriv_apply]
  simp [Complex.real_smul]
  ring

/-- **The operator read on the cover.** At the class of `z`, the value of
`torusCauchyRiemannOperator` on `σ` is that of `∂bar + ν + μ conj` on the lift `σ ∘ (↑)` at `z`,
times `dzbar`. -/
theorem torusCauchyRiemannOperator_quotientMk_apply (σ : ℂ ⧸ Λ → ℂ) (z v : ℂ) :
    torusCauchyRiemannOperator Λ ν μ σ z v =
      (conjWirtingerDeriv (fun w : ℂ ↦ σ w) z 1 + ν z * σ z + μ z * conj (σ z)) * conj v := by
  rw [torusCauchyRiemannOperator_apply, dbarFunction_ofComplexManifold_quotientMk_apply,
    conjWirtingerDeriv_apply_eq_conj_smul_apply_one, smul_eq_mul]
  ring

/-- **Solutions on the torus are periodic solutions on the plane.** A function `σ` on `ℂ ⧸ Λ` is
real differentiable with `torusCauchyRiemannOperator Λ ν μ σ = 0` exactly when its lift
`σ ∘ (↑)` solves `∂bar v + ν v + μ conj v = 0` on `ℂ` for the lifted coefficients. -/
theorem comp_quotientMk_mem_cauchyRiemannKernel_iff {σ : ℂ ⧸ Λ → ℂ} :
    (fun z : ℂ ↦ σ z) ∈ cauchyRiemannKernel (fun z : ℂ ↦ ν z) (fun z : ℂ ↦ μ z) ↔
      MDifferentiable 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) σ ∧ ∀ x, torusCauchyRiemannOperator Λ ν μ σ x = 0 := by
  have hdiff : Differentiable ℝ (fun z : ℂ ↦ σ z) ↔ MDifferentiable 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) σ := by
    rw [← mdifferentiable_iff_differentiable]
    refine ⟨fun h x ↦ ?_, fun h z ↦ ?_⟩
    · obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
      exact ((Λ.isLocalDiffeomorph_quotientMk (I := 𝓘(ℝ, ℂ)) (n := ∞) z).mdifferentiableAt_comp_iff
        (by simp)).1 (h z)
    · exact ((Λ.isLocalDiffeomorph_quotientMk (I := 𝓘(ℝ, ℂ)) (n := ∞) z).mdifferentiableAt_comp_iff
        (by simp)).2 (h z)
  rw [mem_cauchyRiemannKernel, hdiff]
  refine and_congr_right fun _ ↦ ⟨fun h x ↦ ?_, fun h z ↦ ?_⟩
  · obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
    refine ContinuousLinearMap.ext fun v ↦
      (torusCauchyRiemannOperator_quotientMk_apply σ z v).trans ?_
    rw [h z, zero_mul, zero_apply]
  · have h1 : (conjWirtingerDeriv (fun z : ℂ ↦ σ z) z 1 + ν z * σ z + μ z * conj (σ z)) *
        conj 1 = 0 :=
      (torusCauchyRiemannOperator_quotientMk_apply (ν := ν) (μ := μ) σ z 1).symm.trans
        (by rw [h z]; exact zero_apply _)
    simpa using h1

/-! ### The Sobolev realization -/

section Sobolev

variable (A : FiniteBundleAtlas ℂ (ℂ ⧸ Λ) ℂ (Trivial (ℂ ⧸ Λ) ℂ))
  (hν : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ν) (hμ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ μ)
  (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The **realization** `W^{1,p}(ℂ ⧸ Λ, ℂ) → Lᵖ(ℂ ⧸ Λ, Λ^{0,1})` of the normal operator
`∂bar + ν + μ conj` of a torus on the trivial line, for smooth coefficients, through a finite
bundle atlas `A` of the trivial line
(`TauCeti.IsRealCauchyRiemannOperator.sobolevL`). Such an atlas exists when `ℂ ⧸ Λ` is compact
(`TauCeti.FiniteBundleAtlas.nonempty`), for instance when `Λ` is a full lattice
(`QuotientAddGroup.instCompactSpaceOfIsZLattice`). -/
abbrev torusCauchyRiemannSobolevL :
    SobolevSection A volume p 1 →L[ℝ] zeroOneSobolevSections A volume p 0 :=
  (isRealCauchyRiemannOperator_torusCauchyRiemannOperator ν μ).sobolevL A
    (contMDiffCovariantDerivativeOn_torusCauchyRiemannOperator le_rfl hν hμ) volume p

/-- **The normal operator of a torus is Fredholm** on `W^{1,p}`, `1 < p < ∞`
(`TauCeti.IsRealCauchyRiemannOperator.isFredholm_sobolevL`). -/
theorem isFredholm_torusCauchyRiemannSobolevL (hp : 1 < p) (hp_top : p ≠ ⊤) :
    (torusCauchyRiemannSobolevL A hν hμ p).IsFredholm :=
  IsRealCauchyRiemannOperator.isFredholm_sobolevL A _ _ hp hp_top

/-- **The index does not depend on the coefficients**: any two pairs of smooth coefficients give
realizations of the same index (`TauCeti.IsRealCauchyRiemannOperator.index_sobolevL_eq`). -/
theorem index_torusCauchyRiemannSobolevL_eq {ν' μ' : ℂ ⧸ Λ → ℂ}
    (hν' : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ ν') (hμ' : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ μ')
    (hp : 1 < p) (hp_top : p ≠ ⊤) :
    (torusCauchyRiemannSobolevL A hν' hμ' p).index =
      (torusCauchyRiemannSobolevL A hν hμ p).index :=
  IsRealCauchyRiemannOperator.index_sobolevL_eq A _ _ _ _ hp hp_top

variable {p}

/-- The lift to `ℂ` of a `C¹` section whose Sobolev section lies in the kernel of the
realization: a periodic solution of `∂bar v + ν v + μ conj v = 0`. -/
private def liftKer (hp : 1 < p) :
    ((torusCauchyRiemannSobolevL A hν hμ p).ker.comap
        (SobolevSection.ofContMDiffSection A volume p 1)) →ₗ[ℝ]
      ↥(signTwisted ℝ Λ.subtype 0 ⊓
        cauchyRiemannKernel (fun z : ℂ ↦ ν z) (fun z : ℂ ↦ μ z)) where
  toFun t := ⟨fun z : ℂ ↦ t.val z,
    comp_quotientMk_mem_signTwisted_zero _, comp_quotientMk_mem_cauchyRiemannKernel_iff.2
      ⟨fun x ↦ ((Trivial.contMDiff_mk_iff.1 t.val.contMDiff).2 x).mdifferentiableAt one_ne_zero,
        (IsRealCauchyRiemannOperator.ofContMDiffSection_mem_ker_sobolevL_iff A _ _ hp _).1
          t.property⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
private theorem coe_liftKer_apply (hp : 1 < p)
    (t : (torusCauchyRiemannSobolevL A hν hμ p).ker.comap
      (SobolevSection.ofContMDiffSection A volume p 1)) :
    (liftKer A hν hμ hp t : ℂ → ℂ) = fun z : ℂ ↦ t.val z :=
  rfl

/-- **The kernel of the realization on the plane.** Every element of the kernel of the
realization, `p > 1`, is the Sobolev section of a smooth function `σ` on `ℂ ⧸ Λ`
(`TauCeti.IsRealCauchyRiemannOperator.exists_contMDiff_of_sobolevL_eq_zero`); this linear map sends
it to the lift `σ ∘ (↑)`, a `Λ`-periodic solution of `∂bar v + ν v + μ conj v = 0` on `ℂ`. -/
def kerTorusCauchyRiemannSobolevLLift (hp : 1 < p) :
    (torusCauchyRiemannSobolevL A hν hμ p).ker →ₗ[ℝ]
      ↥(signTwisted ℝ Λ.subtype 0 ⊓
        cauchyRiemannKernel (fun z : ℂ ↦ ν z) (fun z : ℂ ↦ μ z)) :=
  (liftKer A hν hμ hp).comp
    (IsRealCauchyRiemannOperator.kerSobolevLEquivComap A _ _ hp).symm.toLinearMap

/-- The lift of the Sobolev section of a `C¹` function `σ` in the kernel is `σ ∘ (↑)`. -/
@[simp]
theorem coe_kerTorusCauchyRiemannSobolevLLift_ofContMDiffSection (hp : 1 < p)
    {σ : Cₛ^((1 : ℕ) : WithTop ℕ∞)⟮𝓘(ℝ, ℂ); ℂ, Trivial (ℂ ⧸ Λ) ℂ⟯}
    (hσ : SobolevSection.ofContMDiffSection A volume p 1 σ ∈
      (torusCauchyRiemannSobolevL A hν hμ p).ker) :
    (kerTorusCauchyRiemannSobolevLLift A hν hμ hp ⟨_, hσ⟩ : ℂ → ℂ) = fun z : ℂ ↦ σ z := by
  -- Unfold the composite `kerTorusCauchyRiemannSobolevLLift = liftKer ∘ kerSobolevLEquivComap.symm`
  -- (its `simp` unfolding times out on the kernel types).
  change (liftKer A hν hμ hp ((IsRealCauchyRiemannOperator.kerSobolevLEquivComap A _ _ hp).symm
    ⟨_, hσ⟩) : ℂ → ℂ) = _
  rw [IsRealCauchyRiemannOperator.kerSobolevLEquivComap_symm_ofContMDiffSection, coe_liftKer_apply]

private theorem liftKer_injective (hp : 1 < p) : Function.Injective (liftKer A hν hμ hp) := by
  refine (injective_iff_map_eq_zero _).2 fun t ht ↦ Subtype.ext (ContMDiffSection.ext fun x ↦ ?_)
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
  exact congrFun (congrArg Subtype.val ht) z

/-- Distinct elements of the kernel of the realization have distinct lifts. -/
theorem kerTorusCauchyRiemannSobolevLLift_injective (hp : 1 < p) :
    Function.Injective (kerTorusCauchyRiemannSobolevLLift A hν hμ hp) :=
  (liftKer_injective A hν hμ hp).comp
    (IsRealCauchyRiemannOperator.kerSobolevLEquivComap A _ _ hp).symm.injective

/-- **The kernel of the realization is the space of `C¹` periodic solutions.** A `Λ`-periodic
solution `v` of `∂bar v + ν v + μ conj v = 0` on `ℂ` is the lift of an element of the kernel of the
realization exactly when it is `C¹`: it then descends to a `C¹` function on `ℂ ⧸ Λ`. -/
theorem mem_range_kerTorusCauchyRiemannSobolevLLift_iff (hp : 1 < p)
    {v : ↥(signTwisted ℝ Λ.subtype 0 ⊓
      cauchyRiemannKernel (fun z : ℂ ↦ ν z) (fun z : ℂ ↦ μ z))} :
    v ∈ LinearMap.range (kerTorusCauchyRiemannSobolevLLift A hν hμ hp) ↔
      ContDiff ℝ 1 (v : ℂ → ℂ) := by
  refine ⟨?_, fun hv ↦ ?_⟩
  · rintro ⟨w, rfl⟩
    set t := (IsRealCauchyRiemannOperator.kerSobolevLEquivComap A _ _ hp).symm w
    have ht := (Trivial.contMDiff_mk_iff.1 t.val.contMDiff).2.comp
      ((Λ.isLocalDiffeomorph_quotientMk (I := 𝓘(ℝ, ℂ)) (n := ∞)).contMDiff.of_le (by simp))
    exact contMDiff_iff_contDiff.1 ht
  -- Descend the periodic map `v` to `ℂ ⧸ Λ`.
  set σ : ℂ ⧸ Λ → ℂ :=
    signTwistedZeroEquivQuotientFun ℝ Λ ⟨(v : ℂ → ℂ), (Submodule.mem_inf.1 v.property).1⟩
  have hσv : (fun z : ℂ ↦ σ z) = (v : ℂ → ℂ) :=
    funext fun z ↦ signTwistedZeroEquivQuotientFun_apply_mk _ z
  have hσs : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((1 : ℕ) : WithTop ℕ∞) σ := by
    refine (Λ.contMDiff_quotient_iff (I := 𝓘(ℝ, ℂ)) (n := ∞) (by simp) σ).2 ?_
    rw [show σ ∘ QuotientAddGroup.mk = fun z : ℂ ↦ σ z from rfl, hσv]
    exact contMDiff_iff_contDiff.2 (by simpa using hv)
  let s : Cₛ^((1 : ℕ) : WithTop ℕ∞)⟮𝓘(ℝ, ℂ); ℂ, Trivial (ℂ ⧸ Λ) ℂ⟯ :=
    ⟨σ, Trivial.contMDiff_mk_iff.2 ⟨contMDiff_id, hσs⟩⟩
  have hker : (fun z : ℂ ↦ s z) ∈ cauchyRiemannKernel (fun z : ℂ ↦ ν z) (fun z : ℂ ↦ μ z) := by
    -- The section `s` is the function `σ`.
    change (fun z : ℂ ↦ σ z) ∈ _
    rw [hσv]
    exact (Submodule.mem_inf.1 v.property).2
  have hs : SobolevSection.ofContMDiffSection A volume p 1 s ∈
      (torusCauchyRiemannSobolevL A hν hμ p).ker :=
    (IsRealCauchyRiemannOperator.ofContMDiffSection_mem_ker_sobolevL_iff A _ _ hp s).2
      (comp_quotientMk_mem_cauchyRiemannKernel_iff.1 hker).2
  exact ⟨⟨_, hs⟩, Subtype.ext ((coe_kerTorusCauchyRiemannSobolevLLift_ofContMDiffSection
    A hν hμ hp hs).trans hσv)⟩

/-- **Nondegeneracy from the periodic kernel.** If `∂bar v + ν v + μ conj v = 0` has no nonzero
`Λ`-periodic solution on `ℂ`, then the realization of the normal operator on `ℂ ⧸ Λ` is
injective. -/
theorem ker_torusCauchyRiemannSobolevL_eq_bot (hp : 1 < p)
    (h : signTwisted ℝ Λ.subtype 0 ⊓
      cauchyRiemannKernel (fun z : ℂ ↦ ν z) (fun z : ℂ ↦ μ z) = ⊥) :
    (torusCauchyRiemannSobolevL A hν hμ p).ker = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun w hw ↦ ?_
  have h0 : kerTorusCauchyRiemannSobolevLLift A hν hμ hp ⟨w, hw⟩ = 0 :=
    Subtype.ext ((Submodule.eq_bot_iff _).1 h _ (kerTorusCauchyRiemannSobolevLLift A hν hμ hp
      ⟨w, hw⟩).property)
  exact congrArg Subtype.val
    ((injective_iff_map_eq_zero _).1 (kerTorusCauchyRiemannSobolevLLift_injective A hν hμ hp) _ h0)

open Complex in
open scoped Real in
/-- **Nondegeneracy from a twisted kernel.** Let `c` be a real linear form lifting the sign
character `χ`, `exp (2π i c ω) = (-1) ^ χ ω` on `Λ`, and let the coefficients on `ℂ ⧸ Λ` be those
of `∂bar + ν₀ + μ₀ conj` in the phase frame `e_c` (`TauCeti.phaseKernelEquiv`):
`ν = ν₀ + π i (c 1 + i c i)` and `μ = μ₀ e_(-2c)` on `ℂ`. If `∂bar v + ν₀ v + μ₀ conj v = 0` has no
nonzero solution twisted by `χ`, then the realization on `ℂ ⧸ Λ` of the periodic operator with
coefficients `ν` and `μ` is injective. -/
theorem ker_torusCauchyRiemannSobolevL_eq_bot_of_signTwisted (c : ℂ →L[ℝ] ℝ)
    {χ : Λ →+ ZMod 2}
    (hc : ∀ g, cexp (2 * π * I * c (Λ.subtype g)) = ((hilbertSign (χ g) : ℤ) : ℂ))
    {ν₀ μ₀ : ℂ → ℂ} (hν₀ : ∀ z : ℂ, ν z = ν₀ z + π * I * (c 1 + I * c I))
    (hμ₀ : ∀ z : ℂ, μ z = μ₀ z * linearPhase (-2 • c) z) (hp : 1 < p)
    (h : signTwisted ℝ Λ.subtype χ ⊓ cauchyRiemannKernel ν₀ μ₀ = ⊥) :
    (torusCauchyRiemannSobolevL A hν hμ p).ker = ⊥ := by
  refine ker_torusCauchyRiemannSobolevL_eq_bot A hν hμ hp ?_
  rw [funext hν₀, funext hμ₀]
  exact (signTwisted_inf_cauchyRiemannKernel_eq_bot_iff c hc ν₀ μ₀).1 h

end Sobolev

end TauCeti
