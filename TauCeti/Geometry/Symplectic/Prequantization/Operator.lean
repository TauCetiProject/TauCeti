/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Bracket
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import TauCeti.Geometry.Symplectic.Prequantization.Exact
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Trivial

/-!
# Prequantum operators

Let `σ` be a two-form on `M`, `ℏ` a real number and `∇` a connection on the trivial complex line
`M × ℂ`, encoded as a Mathlib `CovariantDerivative` on the real smooth bundle with fibre `ℂ`. The
**prequantum operator** of a real function `f` acts on sections by

`Q_f s = iℏ ∇_{X_f} s + f s`,

where `X_f` is the Hamiltonian vector field of `f`, normalized by `ι_{X_f} σ = df`
(`TauCeti.SmoothTwoForm.prequantumOperator`). It has the following properties.

* Constants act by their scalar value, `Q_c s = c s`, and in particular `Q_0 = 0`
  (`TauCeti.SmoothTwoForm.prequantumOperator_const`,
  `TauCeti.SmoothTwoForm.prequantumOperator_zero`).
* `Q_f` is real-linear in `f` on differentiable functions and additive in `s` on differentiable
  sections (`TauCeti.SmoothTwoForm.prequantumOperator_add_left`,
  `TauCeti.SmoothTwoForm.prequantumOperator_const_smul_left`,
  `TauCeti.SmoothTwoForm.prequantumOperator_add_right`); it is complex-linear in `s` when `∇`
  commutes with complex scalars (`TauCeti.SmoothTwoForm.prequantumOperator_const_smul_right`).
* **Leibniz rule.** For a real function `g`, `Q_f (g s) = g Q_f s - iℏ {f, g} s`
  (`TauCeti.SmoothTwoForm.prequantumOperator_smul_right`), where `{f, g} = σ(X_f, X_g)` is the
  Poisson bracket.
* **The commutator.** If `σ` is symplectic, `∇` commutes with complex scalars and has curvature
  `R(X, Y) = -(i/ℏ) σ(X, Y)` at `x`, then for `C²` functions `f`, `g` and a `C²` section `s`,

  `Q_f Q_g s - Q_g Q_f s = -iℏ Q_{{f, g}} s`

  at `x` (`TauCeti.SmoothTwoForm.prequantumOperator_commutator`). The proof combines the
  Leibniz rule with the curvature along Hamiltonian vector fields,
  `∇_{X_f} ∇_{X_g} s - ∇_{X_g} ∇_{X_f} s + ∇_{X_{{f, g}}} s = -({f, g}/ℏ) i s`
  (`TauCeti.SmoothTwoForm.covariantDerivative_hamiltonianVectorField_curvature`), which follows
  from `[X_f, X_g] = -X_{{f, g}}`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.hamiltonianVectorField_poissonBracket`).

For an exact form `σ = -dθ`, the connection `d + iθ/ℏ` (`TauCeti.exactPrequantumConnection`) has
these properties, giving the commutator on the exact prequantum line
(`TauCeti.SmoothTwoForm.prequantumOperator_exactPrequantumConnection_commutator`). Complex
conjugation `s ↦ conj s` intertwines its prequantum operator with the operator
`-iℏ ∇'_{X_f} + f` of the conjugate line, whose connection is `d - iθ/ℏ`
(`TauCeti.SmoothTwoForm.conj_prequantumOperator_exactPrequantumConnection`), and the conjugate
operators satisfy `[Q'_f, Q'_g] = iℏ Q'_{{f, g}}`
(`TauCeti.SmoothTwoForm.prequantumOperator_exactPrequantumConnection_neg_commutator`).

## References

* B. Kostant, *Quantization and unitary representations*, in Lectures in Modern Analysis and
  Applications III, Lecture Notes in Mathematics 170, Springer, 1970, 87–208.
* M. Schottenloher, *Lecture Notes on Geometric Quantization*, version 15.6, Theorem 7.8, p. 99,
  and Proposition 7.10, p. 101, with the conjugate line convention and curvature scale `1/ℏ`.
* N. M. J. Woodhouse, *Geometric Quantization*, second edition, Oxford, 1992, Section 8.3.
-/

public noncomputable section

open Bundle VectorField
open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  (σ : SmoothTwoForm I M) (cov : CovariantDerivative I ℂ (Trivial M ℂ)) (ℏ : ℝ)
  {f g : M → ℝ} {s t : M → ℂ} {x : M}

/-- The **prequantum operator** `Q_f s = iℏ ∇_{X_f} s + f s` of a real function `f`, acting on
sections `s` of the trivial complex line with connection `∇`. Here `X_f` is the Hamiltonian vector
field of `f` for the two-form `σ`. -/
def prequantumOperator (f : M → ℝ) (s : M → ℂ) (x : M) : ℂ :=
  Complex.I * ℏ * cov s x (σ.hamiltonianVectorField f x) + f x * s x

/-- The prequantum operator unfolds as `iℏ ∇_{X_f} s + f s`. -/
theorem prequantumOperator_def (f : M → ℝ) (s : M → ℂ) (x : M) :
    σ.prequantumOperator cov ℏ f s x =
      Complex.I * ℏ * cov s x (σ.hamiltonianVectorField f x) + f x * s x :=
  (rfl)

/-- A constant function acts by its scalar value: `Q_c s = c s`. -/
@[simp]
theorem prequantumOperator_const (c : ℝ) (s : M → ℂ) (x : M) :
    σ.prequantumOperator cov ℏ (fun _ ↦ c) s x = c * s x := by
  simp [prequantumOperator_def, hamiltonianVectorField_const]

/-- The zero function acts by zero. -/
@[simp]
theorem prequantumOperator_zero (s : M → ℂ) (x : M) :
    σ.prequantumOperator cov ℏ 0 s x = 0 := by
  rw [Pi.zero_def, prequantumOperator_const]
  simp

/-- The prequantum operator is additive in the function, at a point where both functions are
differentiable. -/
theorem prequantumOperator_add_left (hf : MDifferentiableAt I 𝓘(ℝ) f x)
    (hg : MDifferentiableAt I 𝓘(ℝ) g x) (s : M → ℂ) :
    σ.prequantumOperator cov ℏ (f + g) s x =
      σ.prequantumOperator cov ℏ f s x + σ.prequantumOperator cov ℏ g s x := by
  simp only [prequantumOperator_def, hamiltonianVectorField_add hf hg, map_add, Pi.add_apply,
    Complex.ofReal_add]
  ring

/-- The prequantum operator is homogeneous in the function for real scalars. -/
theorem prequantumOperator_const_smul_left (c : ℝ) (f : M → ℝ) (s : M → ℂ) (x : M) :
    σ.prequantumOperator cov ℏ (c • f) s x = c * σ.prequantumOperator cov ℏ f s x := by
  simp only [prequantumOperator_def, hamiltonianVectorField_const_smul, map_smul, Pi.smul_apply,
    smul_eq_mul, Complex.real_smul, Complex.ofReal_mul]
  ring

/-- The prequantum operator is additive on sections differentiable at the point. -/
theorem prequantumOperator_add_right (f : M → ℝ) (hs : MDifferentiableAt I 𝓘(ℝ, ℂ) s x)
    (ht : MDifferentiableAt I 𝓘(ℝ, ℂ) t x) :
    σ.prequantumOperator cov ℏ f (s + t) x =
      σ.prequantumOperator cov ℏ f s x + σ.prequantumOperator cov ℏ f t x := by
  have hadd := cov.isCovariantDerivativeOnUniv.add (σ := s) (σ' := t)
    (Trivial.mdifferentiableAt_section_iff.2 hs) (Trivial.mdifferentiableAt_section_iff.2 ht)
  simp only [prequantumOperator_def, hadd, add_apply, Pi.add_apply]
  ring

/-- If the connection commutes with complex scalars, so does the prequantum operator. -/
theorem prequantumOperator_const_smul_right (hc : ∀ (c : ℂ) (t : M → ℂ), cov (c • t) = c • cov t)
    (f : M → ℝ) (c : ℂ) (s : M → ℂ) (x : M) :
    σ.prequantumOperator cov ℏ f (c • s) x = c * σ.prequantumOperator cov ℏ f s x := by
  simp only [prequantumOperator_def, hc, Pi.smul_apply, smul_apply,
    smul_eq_mul]
  ring

/-- **The Leibniz rule for the prequantum operator**: for a real function `g`,
`Q_f (g s) = g Q_f s - iℏ {f, g} s`. -/
theorem prequantumOperator_smul_right (f : M → ℝ) (hg : MDifferentiableAt I 𝓘(ℝ) g x)
    (hs : MDifferentiableAt I 𝓘(ℝ, ℂ) s x) :
    σ.prequantumOperator cov ℏ f (g • s) x =
      g x * σ.prequantumOperator cov ℏ f s x -
        Complex.I * ℏ * σ.poissonBracket f g x * s x := by
  have hl := cov.isCovariantDerivativeOnUniv.leibniz (σ := s)
    (Trivial.mdifferentiableAt_section_iff.2 hs) hg
  simp only [prequantumOperator_def, hl, add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply, Pi.smul_apply',
    poissonBracket_eq_neg_mvfderiv, Complex.real_smul, Complex.ofReal_neg]
  ring

/-- The covariant derivative of `Q_g s`, expanded by additivity, complex linearity and the
Leibniz rule. -/
private theorem prequantumOperator_covariantDerivative
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (hc : ∀ (c : ℂ) (t : M → ℂ), cov (c • t) = c • cov t)
    (hX : ContMDiff I I.tangent 1 (T% (σ.hamiltonianVectorField g)))
    (hg : ContMDiff I 𝓘(ℝ) 2 g) (hs : ContMDiff I 𝓘(ℝ, ℂ) 2 s) (v : TangentSpace I x) :
    cov (σ.prequantumOperator cov ℏ g s) x v =
      Complex.I * ℏ * cov (fun y ↦ cov s y (σ.hamiltonianVectorField g y)) x v +
        g x * cov s x v + mvfderiv I g x v * s x := by
  have hs' : MDifferentiableAt I 𝓘(ℝ, ℂ) s x := hs.mdifferentiableAt (by simp)
  have hg' : MDifferentiableAt I 𝓘(ℝ) g x := hg.mdifferentiableAt (by simp)
  have hA : MDifferentiableAt I 𝓘(ℝ, ℂ)
      (fun y ↦ (cov s y (σ.hamiltonianVectorField g y) : ℂ)) x :=
    Trivial.mdifferentiableAt_section_iff.1 ((cov.contMDiffAt_apply (hX x)
      (Trivial.contMDiff_mk_iff.2 ⟨contMDiff_id, hs⟩)).mdifferentiableAt one_ne_zero)
  have hQ : σ.prequantumOperator cov ℏ g s =
      (Complex.I * ℏ) • (fun y ↦ (cov s y (σ.hamiltonianVectorField g y) : ℂ)) + g • s := by
    funext y
    simp [prequantumOperator_def, Complex.real_smul]
  have hadd := cov.isCovariantDerivativeOnUniv.add
    (σ := ((Complex.I * ℏ) • fun y ↦ (cov s y (σ.hamiltonianVectorField g y) : ℂ) : M → ℂ))
    (σ' := (g • s : M → ℂ))
    (Trivial.mdifferentiableAt_section_iff.2 (mdifferentiableAt_const.mul hA))
    (Trivial.mdifferentiableAt_section_iff.2 (hg'.smul hs'))
  rw [hQ, hadd, hc,
    cov.isCovariantDerivativeOnUniv.leibniz (Trivial.mdifferentiableAt_section_iff.2 hs') hg']
  simp only [add_apply, smul_apply, Pi.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, Complex.real_smul]
  ring

/-- **Curvature along Hamiltonian vector fields.** Let `σ` be symplectic and let `∇` have curvature
`R(X, Y) s = -(i/ℏ) σ(X, Y) s` at `x`. Since `[X_f, X_g] = -X_{{f, g}}` for `C²` functions `f`, `g`,

`∇_{X_f} ∇_{X_g} s - ∇_{X_g} ∇_{X_f} s + ∇_{X_{{f, g}}} s = -({f, g}/ℏ) i s`

at `x`. -/
theorem covariantDerivative_hamiltonianVectorField_curvature [FiniteDimensional ℝ E]
    (hσ : σ.IsSymplectic)
    (hR : ∀ X Y : Π y : M, TangentSpace I y, MDiffAt (T% X) x → MDiffAt (T% Y) x →
      cov.curvatureOperator X Y s x = -(σ.val x ![X x, Y x] / ℏ) • (Complex.I * s x))
    (hf : ContMDiff I 𝓘(ℝ) 2 f) (hg : ContMDiff I 𝓘(ℝ) 2 g) :
    cov (fun y ↦ cov s y (σ.hamiltonianVectorField g y)) x (σ.hamiltonianVectorField f x) -
        cov (fun y ↦ cov s y (σ.hamiltonianVectorField f y)) x (σ.hamiltonianVectorField g x) +
        cov s x (σ.hamiltonianVectorField (σ.poissonBracket f g) x) =
      -(σ.poissonBracket f g x / ℏ) • (Complex.I * s x) := by
  have hXf := hσ.isNondegenerate.contMDiff_hamiltonianVectorField (n := 1) (f := f) (by simp)
    (by norm_num [hf])
  have hXg := hσ.isNondegenerate.contMDiff_hamiltonianVectorField (n := 1) (f := g) (by simp)
    (by norm_num [hg])
  have h := hR _ _ ((hXf x).mdifferentiableAt one_ne_zero) ((hXg x).mdifferentiableAt one_ne_zero)
  rw [CovariantDerivative.curvatureOperator_apply] at h
  rw [hσ.isNondegenerate.hamiltonianVectorField_poissonBracket hσ.isClosed hf hg, Pi.neg_apply,
    map_neg, poissonBracket_def, SmoothBundleForm.eval₂_apply]
  linear_combination h

/-- **The commutator of prequantum operators.** Let `σ` be symplectic and let `∇` be a `C¹`
connection on the trivial complex line which commutes with complex scalars and has curvature
`R(X, Y) s = -(i/ℏ) σ(X, Y) s` at `x`. For `C²` functions `f`, `g` and a `C²` section `s`,

`Q_f Q_g s - Q_g Q_f s = -iℏ Q_{{f, g}} s`

at `x`. -/
theorem prequantumOperator_commutator [FiniteDimensional ℝ E] (hσ : σ.IsSymplectic)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (hc : ∀ (c : ℂ) (t : M → ℂ), cov (c • t) = c • cov t)
    (hR : ∀ X Y : Π y : M, TangentSpace I y, MDiffAt (T% X) x → MDiffAt (T% Y) x →
      cov.curvatureOperator X Y s x = -(σ.val x ![X x, Y x] / ℏ) • (Complex.I * s x))
    (hf : ContMDiff I 𝓘(ℝ) 2 f) (hg : ContMDiff I 𝓘(ℝ) 2 g) (hs : ContMDiff I 𝓘(ℝ, ℂ) 2 s) :
    σ.prequantumOperator cov ℏ f (σ.prequantumOperator cov ℏ g s) x -
        σ.prequantumOperator cov ℏ g (σ.prequantumOperator cov ℏ f s) x =
      -(Complex.I * ℏ) * σ.prequantumOperator cov ℏ (σ.poissonBracket f g) s x := by
  have hXf := hσ.isNondegenerate.contMDiff_hamiltonianVectorField (n := 1) (f := f) (by simp)
    (by norm_num [hf])
  have hXg := hσ.isNondegenerate.contMDiff_hamiltonianVectorField (n := 1) (f := g) (by simp)
    (by norm_num [hg])
  have hcurv := σ.covariantDerivative_hamiltonianVectorField_curvature cov ℏ hσ hR hf hg
  rw [Complex.real_smul] at hcurv
  -- The first-order terms of the commutator are `dg(X_f) = -{f, g}` and `df(X_g) = {f, g}`.
  have hgf : (mvfderiv I g x (σ.hamiltonianVectorField f x) : ℂ) = -σ.poissonBracket f g x := by
    rw [poissonBracket_eq_neg_mvfderiv, Complex.ofReal_neg, neg_neg]
  have hfg : (mvfderiv I f x (σ.hamiltonianVectorField g x) : ℂ) = σ.poissonBracket f g x := by
    rw [poissonBracket_eq_mvfderiv]
  have hℏ : (ℏ : ℂ) ^ 2 * (σ.poissonBracket f g x / ℏ) = ℏ * σ.poissonBracket f g x := by
    rcases eq_or_ne (ℏ : ℂ) 0 with h | h
    · simp [h]
    · field_simp
  simp only [prequantumOperator_def, σ.prequantumOperator_covariantDerivative cov ℏ hc hXg hg hs,
    σ.prequantumOperator_covariantDerivative cov ℏ hc hXf hf hs]
  push_cast at hcurv ⊢
  -- Both sides differ by `(iℏ)²` times the curvature identity `hcurv` and `iℏ s` times the
  -- first-order terms; `i² = -1` and `ℏ² ({f, g}/ℏ) = ℏ {f, g}` (also when `ℏ = 0`) then close it.
  linear_combination (Complex.I * ℏ) ^ 2 * hcurv + Complex.I * ℏ * s x * (hgf - hfg) +
    Complex.I * s x * hℏ - Complex.I * ℏ ^ 2 * (σ.poissonBracket f g x / ℏ) * s x * Complex.I_sq

/-! ### The exact prequantum line -/

/-- **The commutator on the exact prequantum line.** If `σ` is symplectic and `σ = -dθ` at `x`,
then for `C²` functions `f`, `g` and a `C²` section `s` the prequantum operators of the connection
`d + iθ/ℏ` satisfy `Q_f Q_g s - Q_g Q_f s = -iℏ Q_{{f, g}} s` at `x`. -/
theorem prequantumOperator_exactPrequantumConnection_commutator [FiniteDimensional ℝ E]
    (hσ : σ.IsSymplectic) (θ : SmoothForm I M ℝ 1) (hθ : mextDeriv θ.val x = -σ.val x)
    (hf : ContMDiff I 𝓘(ℝ) 2 f) (hg : ContMDiff I 𝓘(ℝ) 2 g) (hs : ContMDiff I 𝓘(ℝ, ℂ) 2 s) :
    σ.prequantumOperator (exactPrequantumConnection θ ℏ) ℏ f
        (σ.prequantumOperator (exactPrequantumConnection θ ℏ) ℏ g s) x -
        σ.prequantumOperator (exactPrequantumConnection θ ℏ) ℏ g
          (σ.prequantumOperator (exactPrequantumConnection θ ℏ) ℏ f s) x =
      -(Complex.I * ℏ) *
        σ.prequantumOperator (exactPrequantumConnection θ ℏ) ℏ (σ.poissonBracket f g) s x :=
  σ.prequantumOperator_commutator _ ℏ hσ (fun c t ↦ exactPrequantumConnection_const_smul θ ℏ t c)
    (fun _ _ hX hY ↦ curvatureOperator_exactPrequantumConnection_of_mextDeriv_eq_neg θ σ ℏ hθ hX hY
      (hs x)) hf hg hs

/-- **Complex conjugation intertwines the prequantum operators of conjugate lines.** Conjugation
sends the operator `iℏ ∇_{X_f} + f` of the connection `d + iθ/ℏ` to the operator
`-iℏ ∇'_{X_f} + f` of the conjugate connection `∇' = d - iθ/ℏ`. -/
theorem conj_prequantumOperator_exactPrequantumConnection (θ : SmoothForm I M ℝ 1) (f : M → ℝ)
    (s : M → ℂ) (x : M) :
    starRingEnd ℂ (σ.prequantumOperator (exactPrequantumConnection θ ℏ) ℏ f s x) =
      σ.prequantumOperator (exactPrequantumConnection (-θ) ℏ) (-ℏ) f (starRingEnd ℂ ∘ s) x := by
  simp only [prequantumOperator_def, exactPrequantumConnection_neg_conj_apply, map_add, map_mul,
    Complex.conj_I, Complex.conj_ofReal, Function.comp_apply, Complex.ofReal_neg]
  ring

/-- **The commutator on the conjugate exact line.** If `σ` is symplectic and `σ = -dθ` at `x`, the
operators `Q'_f = -iℏ ∇'_{X_f} + f` of the conjugate connection `∇' = d - iθ/ℏ` satisfy
`Q'_f Q'_g s - Q'_g Q'_f s = iℏ Q'_{{f, g}} s` at `x`, for `C²` functions `f`, `g` and a `C²`
section `s`. -/
theorem prequantumOperator_exactPrequantumConnection_neg_commutator [FiniteDimensional ℝ E]
    (hσ : σ.IsSymplectic) (θ : SmoothForm I M ℝ 1) (hθ : mextDeriv θ.val x = -σ.val x)
    (hf : ContMDiff I 𝓘(ℝ) 2 f) (hg : ContMDiff I 𝓘(ℝ) 2 g) (hs : ContMDiff I 𝓘(ℝ, ℂ) 2 s) :
    σ.prequantumOperator (exactPrequantumConnection (-θ) ℏ) (-ℏ) f
        (σ.prequantumOperator (exactPrequantumConnection (-θ) ℏ) (-ℏ) g s) x -
        σ.prequantumOperator (exactPrequantumConnection (-θ) ℏ) (-ℏ) g
          (σ.prequantumOperator (exactPrequantumConnection (-θ) ℏ) (-ℏ) f s) x =
      Complex.I * ℏ * σ.prequantumOperator (exactPrequantumConnection (-θ) ℏ) (-ℏ)
        (σ.poissonBracket f g) s x := by
  -- The conjugate primitive `-θ` is a primitive of `-σ`: `d(-θ) = σ = -(-σ)` at `x`.
  have hθ' : mextDeriv (-θ).val x = -(-σ).val x := by
    rw [NegMemClass.coe_neg, NegMemClass.coe_neg, mextDeriv_neg, Pi.neg_apply, Pi.neg_apply, hθ]
  have h := σ.prequantumOperator_commutator _ (-ℏ) hσ
    (fun c t ↦ exactPrequantumConnection_const_smul (-θ) ℏ t c) (fun X Y hX hY ↦ by
      rw [curvatureOperator_exactPrequantumConnection_of_mextDeriv_eq_neg (-θ) (-σ) ℏ hθ' hX hY
        (hs x), NegMemClass.coe_neg, Pi.neg_apply, ContinuousAlternatingMap.neg_apply, neg_div,
        div_neg])
    hf hg hs
  rw [h, Complex.ofReal_neg, mul_neg, neg_neg]

end SmoothTwoForm

end TauCeti
