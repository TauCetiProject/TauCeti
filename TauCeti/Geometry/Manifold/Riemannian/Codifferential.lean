/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.HodgeStar
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.TopForm
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import TauCeti.Geometry.Manifold.DeRham.CompactSupport
public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.BoundarylessStokes
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Positivity
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
import TauCeti.Geometry.Manifold.DifferentialForm.Squared
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Divergence

/-!
# The codifferential and the Hodge Laplacian of an oriented Riemannian manifold

On an oriented Riemannian manifold `M` of dimension `m`, the codifferential of smooth real forms
of degree `j = k + 1` is

`d* = (-1) ^ (m (j + 1) + 1) ⋆ d ⋆ : Ω^(k+1)(M) → Ω^k(M)`,

built from the Hodge star `TauCeti.SmoothForm.hodgeStar` and the exterior derivative. With this
sign it is the formal adjoint of `d` for the pointwise inner product of forms integrated against
the Riemannian volume form: on a boundaryless manifold, for smooth forms `α` of degree `k` and
`β` of degree `k + 1`, one of them compactly supported,

`∫_M ⟨dα, β⟩ vol = ∫_M ⟨α, d*β⟩ vol`.

The proof is Stokes' theorem for `α ∧ ⋆β`, whose exterior derivative is
`⟨dα, β⟩ vol - ⟨α, d*β⟩ vol` by the Leibniz rule, `α ∧ ⋆γ = ⟨α, γ⟩ vol` and the identity
`⋆d*β = (-1) ^ (k + 1) d⋆β`.

The codifferential does not depend on the orientation, since reversing it negates both stars,
it squares to zero, and it does not enlarge supports.

The Hodge Laplacian `Δ = d*d + dd*` of smooth `k`-forms (only `d*d` in degree `0` and only
`dd*` in the top degree) is the second-order operator of Hodge theory. By Green's formulas
`∫_M ⟨d*dα, β⟩ vol = ∫_M ⟨dα, dβ⟩ vol` and
`∫_M ⟨dd*α, β⟩ vol = ∫_M ⟨d*α, d*β⟩ vol` it is formally self-adjoint and nonnegative, and a
compactly supported form is harmonic exactly when it is closed and coclosed. These Green's-formula
arguments use only that `d*` is a formal adjoint of `d` and that both preserve compact support, so
they are proved once for the Laplacian `δD + Dδ` of any such pair `(D, δ)`; the Hodge Laplacian is
the case `(d, d*)`. The sign identities
`⋆d*β = (-1) ^ (k + 1) d⋆β` and `⋆dα = (-1) ^ (k + 1) d*⋆α` show that `Δ` commutes with the Hodge
star.

Multiplication by a smooth function `f` commutes with `d` and `d*` up to zeroth-order terms:
`d (f α) = f dα + df ∧ α` and `d*(f β) = f d*β - ι_(grad f) β`. Hence the double commutator of the
Hodge Laplacian with `f` is `[[Δ, f], f] = -2 (ι_(grad f) ε_(df) + ε_(df) ι_(grad f)) = -2 |df|²`,
and more generally `[[Δ, f], g] = -2 ⟪df, dg⟫` for smooth functions `f` and `g`.
With the normalization `σ(P)(df) = ½ [[P, f], f]` of the principal symbol of a second-order
operator, this says that the principal symbol of `Δ` at `df_x` is `-|df_x|² Id`, that is
`|ξ|² Id` at `ξ = df_x` in the Fourier convention `σ(∂ⱼ) = i ξⱼ`.

## Main definitions

* `TauCeti.SmoothForm.codifferential`: the codifferential `d* = (-1) ^ (m (k + 2) + 1) ⋆ d ⋆` of
  smooth `(k + 1)`-forms.
* `TauCeti.SmoothForm.laplacian`: the Laplacian `δD + Dδ` of a family of differentials `D` and
  codifferentials `δ`.
* `TauCeti.SmoothForm.hodgeLaplacian`: the Hodge Laplacian `Δ = d*d + dd*` of smooth `k`-forms.

## Main results

* `TauCeti.SmoothForm.hodgeStar_codifferential`: `⋆d*β = (-1) ^ (k + 1) d⋆β`.
* `TauCeti.SmoothForm.codifferential_neg_orientation`: `d*` does not depend on the orientation.
* `TauCeti.SmoothForm.codifferential_codifferential`: `d* d* = 0`.
* `TauCeti.SmoothForm.mextDeriv_wedge_hodgeStar`: Green's formula
  `d (α ∧ ⋆β) = ⟨dα, β⟩ vol - ⟨α, d*β⟩ vol`.
* `TauCeti.SmoothForm.integralTopForm_inner_mextDeriv_eq_inner_codifferential`: `d*` is the
  formal adjoint of `d`,
  `∫_M ⟨dα, β⟩ vol = ∫_M ⟨α, d*β⟩ vol`.
* `TauCeti.RoughForm.integralTopForm_inner_self_smul_riemannianVolumeForm_nonneg`,
  `TauCeti.SmoothForm.integralTopForm_inner_self_smul_riemannianVolumeForm_eq_zero_iff`: the
  pairing is positive definite, `∫_M |α|² vol ≥ 0` with equality only for `α = 0` when `α` is
  smooth and compactly supported.
* `TauCeti.SmoothForm.hodgeStar_mextDeriv`: `⋆dα = (-1) ^ (k + 1) d*⋆α`.
* `TauCeti.SmoothForm.hodgeStar_hodgeLaplacian`: `⋆Δ = Δ⋆`.
* `TauCeti.SmoothForm.hodgeLaplacian_eq_ofFunction_neg_laplaceBeltrami`: on functions,
  `Δf = -div grad f`.
* `TauCeti.SmoothForm.coe_codifferential_funSMulₗ`: the Leibniz rule
  `d*(f β) = f d*β - ι_(grad f) β`.
* `TauCeti.SmoothForm.coe_lie_lie_hodgeLaplacian_funSMulₗ`,
  `TauCeti.SmoothForm.coe_lie_lie_hodgeLaplacian_funSMulₗ_self`: the principal symbol of the Hodge
  Laplacian, `[[Δ, f], g] = -2 ⟪df, dg⟫` and `[[Δ, f], f] = -2 |df|²`.
* `TauCeti.SmoothForm.integralTopForm_inner_codifferential_mextDeriv`,
  `TauCeti.SmoothForm.integralTopForm_inner_mextDeriv_codifferential`: Green's formulas for `d*d`
  and `dd*`.
* `TauCeti.SmoothForm.integralTopForm_inner_codiff_diff`,
  `TauCeti.SmoothForm.integralTopForm_inner_diff_codiff`: Green's formulas for `δD` and `Dδ` when
  `δ` is a formal adjoint of `D`.
* `TauCeti.SmoothForm.integralTopForm_inner_laplacian_eq_inner_laplacian`,
  `TauCeti.SmoothForm.integralTopForm_inner_laplacian_self_nonneg`,
  `TauCeti.SmoothForm.laplacian_eq_zero_iff`,
  `TauCeti.SmoothForm.laplacian_eq_zero_iff_apply_eq_zero`:
  if `δ` is a formal adjoint of `D` and both preserve compact support, then `δD + Dδ` is formally
  self-adjoint and nonnegative, and a compactly supported form lies in its kernel exactly when `D`
  and, in positive degree, `δ` annihilate it.
* `TauCeti.SmoothForm.integralTopForm_inner_hodgeLaplacian_eq_inner_hodgeLaplacian`: `Δ` is
  formally self-adjoint, `∫_M ⟨Δα, β⟩ vol = ∫_M ⟨α, Δβ⟩ vol`.
* `TauCeti.SmoothForm.integralTopForm_inner_hodgeLaplacian_self_nonneg`: `0 ≤ ∫_M ⟨Δα, α⟩ vol`.
* `TauCeti.SmoothForm.hodgeLaplacian_eq_zero_iff`,
  `TauCeti.SmoothForm.hodgeLaplacian_eq_zero_iff_mextDeriv_eq_zero`: a compactly supported form
  is harmonic exactly when it is closed and coclosed.

## References

* F. W. Warner, *Foundations of Differentiable Manifolds and Lie Groups*, Graduate Texts in
  Mathematics 94, Springer (1983), §6.1–6.2.
-/

public section

noncomputable section

open Bundle Set
open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {m k l : ℕ}

namespace SmoothForm

/-- The codifferential `d* = (-1) ^ (m (k + 2) + 1) ⋆ d ⋆` of smooth `(k + 1)`-forms on an
oriented Riemannian manifold of dimension `m = k + 1 + l`. For forms of degree `j = k + 1` the
sign is `(-1) ^ (m (j + 1) + 1)`, which makes `d*` the formal adjoint of the exterior derivative
(`TauCeti.SmoothForm.integralTopForm_inner_mextDeriv_eq_inner_codifferential`). -/
def codifferential (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + l = m) :
    SmoothForm I M ℝ (k + 1) →ₗ[ℝ] SmoothForm I M ℝ k :=
  (-1 : ℝ) ^ (m * (k + 2) + 1) •
    hodgeStar o (show l + 1 + k = m by omega) ∘ₗ mextDerivₗ I l ∘ₗ hodgeStar o hkl

/-- The codifferential is `(-1) ^ (m (k + 2) + 1) ⋆ d ⋆`. -/
theorem codifferential_apply (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + l = m)
    (hlk : l + 1 + k = m) (β : SmoothForm I M ℝ (k + 1)) :
    codifferential o hkl β =
      (-1 : ℝ) ^ (m * (k + 2) + 1) • hodgeStar o hlk (mextDerivₗ I l (hodgeStar o hkl β)) :=
  (rfl)

/-- The sign relating `⋆d*` to `d⋆`. -/
private theorem neg_one_pow_mul_neg_one_pow (hkl : k + 1 + l = m) :
    (-1 : ℝ) ^ (m * (k + 2) + 1) * (-1) ^ ((l + 1) * k) = (-1) ^ (k + 1) := by
  subst hkl
  rw [← pow_add]
  refine neg_one_pow_congr ?_
  simp only [Nat.even_add, Nat.even_mul, Nat.even_add_one]
  tauto

/-- **The Hodge star of the codifferential**: `⋆d*β = (-1) ^ (k + 1) d⋆β` for a
`(k + 1)`-form `β`. -/
theorem hodgeStar_codifferential (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + l = m)
    (hkl' : k + (l + 1) = m) (β : SmoothForm I M ℝ (k + 1)) :
    hodgeStar o hkl' (codifferential o hkl β) =
      (-1 : ℝ) ^ (k + 1) • mextDerivₗ I l (hodgeStar o hkl β) := by
  rw [codifferential_apply o hkl (by omega : l + 1 + k = m), map_smul, hodgeStar_hodgeStar,
    smul_smul, neg_one_pow_mul_neg_one_pow hkl]

/-- The codifferential does not depend on the orientation: reversing it negates both Hodge
stars. -/
@[simp]
theorem codifferential_neg_orientation (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + l = m) : codifferential (-o) hkl = codifferential o hkl := by
  have hlk : l + 1 + k = m := by omega
  ext β : 1
  simp only [codifferential_apply _ hkl hlk, hodgeStar_neg_orientation, map_neg, neg_neg]

/-- **The codifferential squares to zero**: `d* d* β = 0`, since `⋆⋆` is a sign and
`d d = 0`. -/
@[simp]
theorem codifferential_codifferential {l' : ℕ} (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + l = m) (hkl' : k + 1 + 1 + l' = m) (β : SmoothForm I M ℝ (k + 1 + 1)) :
    codifferential o hkl (codifferential o hkl' β) = 0 := by
  obtain rfl : l = l' + 1 := by omega
  rw [codifferential_apply o hkl (by omega), codifferential_apply o hkl' (by omega), map_smul,
    map_smul, hodgeStar_hodgeStar, map_smul, map_smul,
    ← LinearMap.comp_apply (mextDerivₗ I (l' + 1)) (mextDerivₗ I l'), mextDerivₗ_comp_mextDerivₗ]
  simp

/-- The codifferential squares to zero as a linear map: `d* ∘ d* = 0`. -/
@[simp]
theorem codifferential_comp_codifferential {l' : ℕ} (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + l = m) (hkl' : k + 1 + 1 + l' = m) :
    codifferential o hkl ∘ₗ codifferential o hkl' = 0 :=
  LinearMap.ext (codifferential_codifferential o hkl hkl')

/-- The codifferential does not enlarge supports. -/
theorem tsupport_codifferential_subset (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + l = m) (β : SmoothForm I M ℝ (k + 1)) :
    _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) (codifferential o hkl β).1 ⊆
      _root_.tsupport (α := E [⋀^Fin (k + 1)]→L[ℝ] ℝ) β.1 := by
  rw [codifferential_apply o hkl (by omega : l + 1 + k = m), Submodule.coe_smul, coe_hodgeStar,
    mextDerivₗ_apply, coe_hodgeStar]
  refine (RoughForm.tsupport_smul_subset _ _).trans ?_
  refine (RoughForm.tsupport_hodgeStar_subset o _ _).trans ?_
  refine (RoughForm.tsupport_mextDeriv_subset _).trans ?_
  exact RoughForm.tsupport_hodgeStar_subset o hkl β.1

/-- The codifferential of a compactly supported form is compactly supported. -/
theorem codifferential_mem_compactlySupportedForms (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + l = m) {β : SmoothForm I M ℝ (k + 1)}
    (hβ : β ∈ compactlySupportedForms I M (k + 1)) :
    codifferential o hkl β ∈ compactlySupportedForms I M k :=
  (mem_compactlySupportedForms I).2 (((mem_compactlySupportedForms I).1 hβ).of_isClosed_subset
    (_root_.isClosed_tsupport _) (tsupport_codifferential_subset o hkl β))

/-- **Green's formula for the codifferential**: for smooth forms `α` of degree `k` and `β` of
degree `k + 1` on an oriented Riemannian manifold of dimension `k + l + 1`,
`d (α ∧ ⋆β) = ⟨dα, β⟩ vol - ⟨α, d*β⟩ vol`, where `⟨·, ·⟩` is the pointwise inner product of forms
and `vol` the Riemannian volume form. -/
theorem mextDeriv_wedge_hodgeStar (o : Manifold.Orientation I M (Fin (k + l + 1)))
    (α : SmoothForm I M ℝ k) (β : SmoothForm I M ℝ (k + 1)) :
    mextDeriv (RoughForm.wedge α.1 (hodgeStar o (add_right_comm k 1 l) β).1) =
      (fun x ↦ alternatingFormInner (TangentSpace I x) (k + 1) ((mextDerivₗ I k α).1 x) (β.1 x) •
        riemannianVolumeForm o x) -
      fun x ↦ alternatingFormInner (TangentSpace I x) k (α.1 x)
        ((codifferential o (add_right_comm k 1 l) β).1 x) • riemannianVolumeForm o x := by
  have hkl' : k + (l + 1) = k + l + 1 := (add_assoc k l 1).symm
  -- `d⋆β = (-1) ^ (k + 1) ⋆d*β`, and the Leibniz sign is `(-1) ^ k`.
  have hdβ : mextDerivₗ I l (hodgeStar o (add_right_comm k 1 l) β) =
      (-1 : ℝ) ^ (k + 1) • hodgeStar o hkl' (codifferential o (add_right_comm k 1 l) β) := by
    rw [hodgeStar_codifferential o _ hkl', smul_smul, ← pow_add, ← two_mul, pow_mul,
      neg_one_sq, one_pow, one_smul]
  have hsign : (-1 : ℝ) ^ k * (-1) ^ (k + 1) = -1 := by
    rw [← pow_add]
    exact Odd.neg_one_pow ⟨k, by ring⟩
  rw [inner_smul_riemannianVolumeForm_eq_wedge_hodgeStar o hkl']
  funext x
  ext v
  rw [Pi.sub_apply, ContinuousAlternatingMap.sub_apply, cast_apply, coe_wedge,
    SmoothForm.mextDeriv_wedge_apply,
    ← mextDerivₗ_apply I l (hodgeStar o _ β), hdβ, Submodule.coe_smul,
    RoughForm.wedge_smul_right, ← mextDerivₗ_apply I k α]
  simp only [coe_hodgeStar, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
    RoughForm.wedge_def, RoughForm.wedgeWith_apply', ← ContinuousAlternatingMap.wedge_def,
    RoughForm.wedge_hodgeStar_apply, smul_eq_mul, Function.comp_def,
    finCongr_apply, Fin.cast_cast, Fin.cast_eq_self]
  linear_combination (alternatingFormInner (TangentSpace I x) k (α.1 x)
    ((codifferential o _ β).1 x) * riemannianVolumeForm o x v) * hsign

/-- `⋆dα = (-1) ^ (k + 1) d*⋆α` for a `k`-form `α`: the Hodge star of the exterior derivative is,
up to sign, the codifferential of the Hodge star. -/
theorem hodgeStar_mextDeriv (o : Manifold.Orientation I M (Fin m)) (hkl : k + (l + 1) = m)
    (hlk : l + 1 + k = m) (hkl' : k + 1 + l = m) (α : SmoothForm I M ℝ k) :
    hodgeStar o hkl' (mextDerivₗ I k α) =
      (-1 : ℝ) ^ (k + 1) • codifferential o hlk (hodgeStar o hkl α) := by
  have hsign : (-1 : ℝ) ^ (k + 1) * (-1) ^ (m * (l + 2) + 1) * (-1) ^ (k * (l + 1)) = 1 := by
    subst hkl
    rw [← pow_add, ← pow_add]
    refine Even.neg_one_pow ?_
    simp only [Nat.even_add, Nat.even_mul, Nat.even_add_one]
    tauto
  rw [codifferential_apply o hlk hkl', hodgeStar_hodgeStar, map_smul, map_smul, smul_smul,
    smul_smul, hsign, one_smul]

/-! ### The Laplacian of a differential and a codifferential -/

section Laplacian

omit [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

variable (D : ∀ k, SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ (k + 1))
  (δ : ∀ {k l : ℕ}, k + 1 + l = m → SmoothForm I M ℝ (k + 1) →ₗ[ℝ] SmoothForm I M ℝ k)

/-- The Laplacian `δD + Dδ` of smooth `k`-forms on a manifold of dimension `m = k + l`, built from
a family of differentials `D : Ω^k → Ω^(k+1)` and a family of codifferentials
`δ : Ω^(k+1) → Ω^k`. In degree `0` only `δD` is present, and in the top degree `k = m` only `Dδ`
is present; on a zero-dimensional manifold it is zero. The Hodge Laplacian
(`TauCeti.SmoothForm.hodgeLaplacian`) is the case `D = d`, `δ = d*`. When `δ` is the formal
adjoint of `D`, this Laplacian is formally self-adjoint and nonnegative
(`TauCeti.SmoothForm.integralTopForm_inner_laplacian_eq_inner_laplacian`,
`TauCeti.SmoothForm.integralTopForm_inner_laplacian_self_nonneg`). -/
def laplacian : ∀ {k l : ℕ}, k + l = m → SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ k
  | 0, 0, _ => 0
  | 0, l + 1, hkl => δ (show 0 + 1 + l = m by omega) ∘ₗ D 0
  | k + 1, 0, hkl => D k ∘ₗ δ hkl
  | k + 1, l + 1, hkl => δ (show k + 1 + 1 + l = m by omega) ∘ₗ D (k + 1) + D k ∘ₗ δ hkl

/-- On a zero-dimensional manifold the Laplacian of functions is zero. -/
@[simp]
theorem laplacian_zero_zero (hkl : 0 + 0 = m) (f : SmoothForm I M ℝ 0) :
    laplacian D δ hkl f = 0 :=
  (rfl)

/-- In positive dimension the Laplacian of functions is `δDf`. -/
theorem laplacian_zero_add_one (hkl : 0 + (l + 1) = m) (hkl' : 0 + 1 + l = m)
    (f : SmoothForm I M ℝ 0) : laplacian D δ hkl f = δ hkl' (D 0 f) :=
  (rfl)

/-- In the top degree the Laplacian is `Dδα`. -/
theorem laplacian_add_one_zero (hkl : k + 1 + 0 = m) (α : SmoothForm I M ℝ (k + 1)) :
    laplacian D δ hkl α = D k (δ hkl α) :=
  (rfl)

/-- Strictly between degree `0` and the top degree the Laplacian is `δDα + Dδα`. -/
theorem laplacian_add_one_add_one (hkl : k + 1 + (l + 1) = m) (hkl' : k + 1 + 1 + l = m)
    (α : SmoothForm I M ℝ (k + 1)) :
    laplacian D δ hkl α = δ hkl' (D (k + 1) α) + D k (δ hkl α) :=
  (rfl)

variable {D δ}

/-- If `D` and `δ` preserve compact support, then so does their Laplacian. -/
theorem laplacian_mem_compactlySupportedForms
    (hD : ∀ {k : ℕ} {α : SmoothForm I M ℝ k},
      α ∈ compactlySupportedForms I M k → D k α ∈ compactlySupportedForms I M (k + 1))
    (hδ : ∀ {k l : ℕ} (hkl : k + 1 + l = m) {β : SmoothForm I M ℝ (k + 1)},
      β ∈ compactlySupportedForms I M (k + 1) → δ hkl β ∈ compactlySupportedForms I M k)
    (hkl : k + l = m) {α : SmoothForm I M ℝ k} (hα : α ∈ compactlySupportedForms I M k) :
    laplacian D δ hkl α ∈ compactlySupportedForms I M k := by
  rcases k with _ | k <;> rcases l with _ | l
  · simp
  · exact hδ _ (hD hα)
  · exact hD (hδ hkl hα)
  · exact add_mem (hδ _ (hD hα)) (hD (hδ hkl hα))

/-- If `D` and `δ` do not enlarge supports, then neither does their Laplacian. -/
theorem tsupport_laplacian_subset
    (hD : ∀ {k : ℕ} (α : SmoothForm I M ℝ k),
      _root_.tsupport (α := E [⋀^Fin (k + 1)]→L[ℝ] ℝ) (D k α).1 ⊆
        _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) α.1)
    (hδ : ∀ {k l : ℕ} (hkl : k + 1 + l = m) (β : SmoothForm I M ℝ (k + 1)),
      _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) (δ hkl β).1 ⊆
        _root_.tsupport (α := E [⋀^Fin (k + 1)]→L[ℝ] ℝ) β.1)
    (hkl : k + l = m) (α : SmoothForm I M ℝ k) :
    _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) (laplacian D δ hkl α).1 ⊆
      _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) α.1 := by
  -- Both `δD` and `Dδ` do not enlarge supports.
  rcases k with _ | k <;> rcases l with _ | l
  · rw [laplacian_zero_zero, ← zero_smul ℝ α, Submodule.coe_smul]
    exact RoughForm.tsupport_smul_subset _ _
  · exact (hδ _ _).trans (hD α)
  · exact (hD _).trans (hδ hkl α)
  · rw [laplacian_add_one_add_one D δ hkl (by omega), Submodule.coe_add]
    exact (tsupport_add _ _).trans
      (union_subset ((hδ _ _).trans (hD α)) ((hD _).trans (hδ hkl α)))

end Laplacian

/-! ### The Hodge Laplacian -/

/-- The Hodge Laplacian `Δ = d*d + dd*` of smooth `k`-forms on an oriented Riemannian manifold of
dimension `m = k + l`. In degree `0` only `d*d` is present, and in the top degree `k = m` only
`dd*` is present, since there are no forms of negative degree and the `(m + 1)`-forms vanish; on
a zero-dimensional manifold it is zero. This is the nonnegative sign convention:
`0 ≤ ∫_M ⟨Δα, α⟩ vol` (`TauCeti.SmoothForm.integralTopForm_inner_hodgeLaplacian_self_nonneg`).
It is the Laplacian `TauCeti.SmoothForm.laplacian` of `D = d` and `δ = d*`. -/
def hodgeLaplacian (o : Manifold.Orientation I M (Fin m)) :
    ∀ {k l : ℕ}, k + l = m → SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ k :=
  laplacian (mextDerivₗ I) fun hkl ↦ codifferential o hkl

/-- The Hodge Laplacian is the Laplacian of the pair `(d, d*)`. -/
theorem hodgeLaplacian_def (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) :
    hodgeLaplacian o hkl = laplacian (mextDerivₗ I) (fun hkl ↦ codifferential o hkl) hkl :=
  (rfl)

/-- On a zero-dimensional manifold the Hodge Laplacian of functions is zero. -/
@[simp]
theorem hodgeLaplacian_zero_zero (o : Manifold.Orientation I M (Fin m)) (hkl : 0 + 0 = m)
    (f : SmoothForm I M ℝ 0) : hodgeLaplacian o hkl f = 0 :=
  (rfl)

/-- In positive dimension the Hodge Laplacian of functions is `Δf = d*df`. -/
theorem hodgeLaplacian_zero_add_one (o : Manifold.Orientation I M (Fin m))
    (hkl : 0 + (l + 1) = m) (hkl' : 0 + 1 + l = m) (f : SmoothForm I M ℝ 0) :
    hodgeLaplacian o hkl f = codifferential o hkl' (mextDerivₗ I 0 f) :=
  (rfl)

/-- In the top degree the Hodge Laplacian is `Δα = dd*α`. -/
theorem hodgeLaplacian_add_one_zero (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + 0 = m) (α : SmoothForm I M ℝ (k + 1)) :
    hodgeLaplacian o hkl α = mextDerivₗ I k (codifferential o hkl α) :=
  (rfl)

/-- Strictly between degree `0` and the top degree the Hodge Laplacian is `Δα = d*dα + dd*α`. -/
theorem hodgeLaplacian_add_one_add_one (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + (l + 1) = m) (hkl' : k + 1 + 1 + l = m) (α : SmoothForm I M ℝ (k + 1)) :
    hodgeLaplacian o hkl α =
      codifferential o hkl' (mextDerivₗ I (k + 1) α) + mextDerivₗ I k (codifferential o hkl α) :=
  (rfl)

/-- In positive dimension the Hodge Laplacian of functions is `Δ = d* ∘ d`. -/
theorem hodgeLaplacian_zero_add_one_eq_comp (o : Manifold.Orientation I M (Fin m))
    (hkl : 0 + (l + 1) = m) (hkl' : 0 + 1 + l = m) :
    hodgeLaplacian o hkl = codifferential o hkl' ∘ₗ mextDerivₗ I 0 :=
  (rfl)

/-- In the top degree the Hodge Laplacian is `Δ = d ∘ d*`. -/
theorem hodgeLaplacian_add_one_zero_eq_comp (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + 0 = m) : hodgeLaplacian o hkl = mextDerivₗ I k ∘ₗ codifferential o hkl :=
  (rfl)

/-- Strictly between degree `0` and the top degree the Hodge Laplacian is
`Δ = d* ∘ d + d ∘ d*`. -/
theorem hodgeLaplacian_add_one_add_one_eq_comp_add_comp (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + (l + 1) = m) (hkl' : k + 1 + 1 + l = m) :
    hodgeLaplacian o hkl =
      codifferential o hkl' ∘ₗ mextDerivₗ I (k + 1) + mextDerivₗ I k ∘ₗ codifferential o hkl :=
  (rfl)

/-- The Hodge Laplacian does not depend on the orientation. -/
@[simp]
theorem hodgeLaplacian_neg_orientation (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) :
    hodgeLaplacian (-o) hkl = hodgeLaplacian o hkl := by
  ext α : 1
  rcases k with _ | k <;> rcases l with _ | l
  · simp
  · simp [hodgeLaplacian_zero_add_one _ hkl (by omega)]
  · simp [hodgeLaplacian_add_one_zero]
  · simp [hodgeLaplacian_add_one_add_one _ hkl (by omega)]

/-- The Hodge Laplacian does not enlarge supports. -/
theorem tsupport_hodgeLaplacian_subset (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m)
    (α : SmoothForm I M ℝ k) :
    _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) (hodgeLaplacian o hkl α).1 ⊆
      _root_.tsupport (α := E [⋀^Fin k]→L[ℝ] ℝ) α.1 :=
  tsupport_laplacian_subset
    (fun α ↦ by rw [mextDerivₗ_apply]; exact RoughForm.tsupport_mextDeriv_subset _)
    (tsupport_codifferential_subset o) hkl α

/-- **The Hodge star commutes with the Hodge Laplacian**: `⋆Δα = Δ⋆α`. -/
theorem hodgeStar_hodgeLaplacian (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m)
    (hlk : l + k = m) (α : SmoothForm I M ℝ k) :
    hodgeStar o hkl (hodgeLaplacian o hkl α) = hodgeLaplacian o hlk (hodgeStar o hkl α) := by
  -- `⋆d*d = dd*⋆` and `⋆dd* = d*d⋆`, by the sign identities for `⋆d` and `⋆d*`.
  have hsq (k : ℕ) : ((-1 : ℝ) ^ (k + 1)) * (-1) ^ (k + 1) = 1 := by
    rw [← mul_pow]
    norm_num
  have hup {k l : ℕ} (hkl : k + 1 + l = m) (hkl' : k + (l + 1) = m) (hlk : l + 1 + k = m)
      (α : SmoothForm I M ℝ k) :
      hodgeStar o hkl' (codifferential o hkl (mextDerivₗ I k α)) =
        mextDerivₗ I l (codifferential o hlk (hodgeStar o hkl' α)) := by
    rw [hodgeStar_codifferential o hkl hkl', hodgeStar_mextDeriv o hkl' hlk hkl, map_smul,
      smul_smul, hsq, one_smul]
  have hdown {k l : ℕ} (hkl : k + 1 + l = m) (hkl' : k + (l + 1) = m) (hlk : l + 1 + k = m)
      (α : SmoothForm I M ℝ (k + 1)) :
      hodgeStar o hkl (mextDerivₗ I k (codifferential o hkl α)) =
        codifferential o hlk (mextDerivₗ I l (hodgeStar o hkl α)) := by
    rw [hodgeStar_mextDeriv o hkl' hlk hkl, hodgeStar_codifferential o hkl hkl', map_smul,
      smul_smul, hsq, one_smul]
  rcases k with _ | k <;> rcases l with _ | l
  · simp
  · rw [hodgeLaplacian_zero_add_one o hkl (by omega), hodgeLaplacian_add_one_zero,
      hup (by omega) hkl hlk]
  · rw [hodgeLaplacian_add_one_zero, hodgeLaplacian_zero_add_one o hlk (by omega),
      hdown (l := 0) hkl (by omega) (by omega)]
  · rw [hodgeLaplacian_add_one_add_one o hkl (by omega),
      hodgeLaplacian_add_one_add_one o hlk (by omega), map_add,
      hup (k := k + 1) (l := l) (by omega) (by omega) (by omega),
      hdown (k := k) (l := l + 1) (by omega) (by omega) (by omega)]
    exact add_comm _ _

/-! ### Functions -/

/-- **The Hodge Laplacian of a function is minus its Laplace–Beltrami operator**: for a smooth
`0`-form `f`, with underlying function `x ↦ f x 0`, `Δf = d*df = -div grad f`. -/
theorem hodgeLaplacian_eq_ofFunction_neg_laplaceBeltrami (o : Manifold.Orientation I M (Fin m))
    (hl : 0 + l = m) (f : SmoothForm I M ℝ 0) :
    (hodgeLaplacian o hl f : RoughForm I M ℝ 0) =
      RoughForm.ofFunction I (-Manifold.laplaceBeltrami I fun x ↦ f.1 x 0) := by
  set g : M → ℝ := fun x ↦ f.1 x 0
  have hf : f.1 = RoughForm.ofFunction I g := RoughForm.eq_ofFunction _
  rcases l with _ | l
  · -- In dimension zero both sides vanish: the divergence is the trace of an endomorphism of the
    -- zero space.
    obtain rfl : m = 0 := by omega
    have : Subsingleton E := Module.finrank_zero_iff.1 (by simpa using o.card_eq.symm)
    funext x
    ext v
    have hA (A : Module.End ℝ (TangentSpace I x)) : A = 0 :=
      LinearMap.ext fun _ ↦ Subsingleton.elim (α := E) _ _
    rw [hodgeLaplacian_zero_zero, RoughForm.ofFunction_apply, Pi.neg_apply,
      Manifold.laplaceBeltrami_def, Manifold.divergence_def, hA (_ : _ →L[ℝ] _).toLinearMap,
      map_zero, neg_zero]
    simp
  · -- `Δf = -⋆d⋆df = -⋆d(ι_(grad f) vol) = -⋆((div grad f) vol) = -div grad f`.
    obtain rfl : m = l + 1 := by omega
    have hsmooth : ContMDiff I 𝓘(ℝ) ∞ g :=
      isSmoothForm_ofFunction_iff.1 (hf ▸ f.isSmoothForm)
    rw [hodgeLaplacian_zero_add_one o hl (by omega), codifferential_apply o _ (by omega),
      Odd.neg_one_pow ⟨l + 1, by ring⟩]
    simp only [SetLike.val_smul, coe_hodgeStar, mextDerivₗ_apply, hf]
    rw [RoughForm.hodgeStar_mextDeriv_ofFunction, mextDeriv_interior_riemannianVolumeForm o
        (Manifold.mdifferentiable_mgradient (hsmooth.of_le (by simp))),
      RoughForm.hodgeStar_smul_riemannianVolumeForm]
    funext x
    ext v
    simp [Manifold.laplaceBeltrami_def]

/-! ### Commutators with functions and the principal symbol of the Hodge Laplacian -/

/-- Exterior multiplication `ε_u` by the gradient `u = grad f x` of `f` at `x` on alternating
forms of the tangent space, read through the identification of forms with the exterior algebra. -/
private def gradWedge (f : M → ℝ) (j : ℕ) (x : M) :
    (TangentSpace I x [⋀^Fin j]→L[ℝ] ℝ) →ₗ[ℝ] TangentSpace I x [⋀^Fin (j + 1)]→L[ℝ] ℝ :=
  (alternatingFormEquiv _ (j + 1)).toLinearMap ∘ₗ
    ExteriorAlgebra.wedgeLeft (Manifold.mgradient I f x) j ∘ₗ
      (alternatingFormEquiv _ j).symm.toLinearMap

/-- The contraction `ι_u` by the gradient `u = grad f x` of `f` at `x` on alternating forms of the
tangent space, read through the identification of forms with the exterior algebra. -/
private def gradContr (f : M → ℝ) (j : ℕ) (x : M) :
    (TangentSpace I x [⋀^Fin (j + 1)]→L[ℝ] ℝ) →ₗ[ℝ] TangentSpace I x [⋀^Fin j]→L[ℝ] ℝ :=
  (alternatingFormEquiv _ j).toLinearMap ∘ₗ
    koszulDifferential (innerₗ _ (Manifold.mgradient I f x)) j ∘ₗ
      (alternatingFormEquiv _ (j + 1)).symm.toLinearMap

omit [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The contraction by the gradient is the interior product with it. -/
private theorem gradContr_apply (f : M → ℝ) (j : ℕ) (β : RoughForm I M ℝ (j + 1)) (x : M) :
    gradContr f j x (β x) = RoughForm.interior (Manifold.mgradient I f) β x := by
  ext v
  simp [gradContr, alternatingFormEquiv_koszulDifferential]

omit [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- `ι_v ε_u = ⟪v, u⟫` on functions, for the gradients `u` of `f` and `v` of `g`. -/
private theorem gradContr_gradWedge_zero (f g : M → ℝ) (x : M)
    (w : TangentSpace I x [⋀^Fin 0]→L[ℝ] ℝ) :
    gradContr g 0 x (gradWedge f 0 x w) =
      ⟪Manifold.mgradient I g x, Manifold.mgradient I f x⟫ • w := by
  have h := LinearMap.congr_fun (koszulDifferential_comp_wedgeLeft_zero
    (innerₗ _ (Manifold.mgradient I g x)) (Manifold.mgradient I f x))
    ((alternatingFormEquiv _ 0).symm w)
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    innerₗ_apply_apply] at h
  simp only [gradContr, gradWedge, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, h, map_smul, LinearEquiv.apply_symm_apply]

omit [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The Koszul homotopy identity `ε_u ι_v + ι_v ε_u = ⟪v, u⟫` in positive degrees, for the
gradients `u` of `f` and `v` of `g`. -/
private theorem gradWedge_gradContr_add (f g : M → ℝ) (j : ℕ) (x : M)
    (w : TangentSpace I x [⋀^Fin (j + 1)]→L[ℝ] ℝ) :
    gradWedge f j x (gradContr g j x w) + gradContr g (j + 1) x (gradWedge f (j + 1) x w) =
      ⟪Manifold.mgradient I g x, Manifold.mgradient I f x⟫ • w := by
  have h := LinearMap.congr_fun (wedgeLeft_comp_koszulDifferential_add
    (innerₗ _ (Manifold.mgradient I g x)) (Manifold.mgradient I f x) j)
    ((alternatingFormEquiv _ (j + 1)).symm w)
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    innerₗ_apply_apply] at h
  simp only [gradContr, gradWedge, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, ← map_add, h, map_smul, LinearEquiv.apply_symm_apply]

omit [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The Leibniz rule `d (f α) = f dα + df ∧ α` for smooth forms, with `df ∧ ·` written as exterior
multiplication by the gradient. -/
private theorem mextDerivₗ_funSMulₗ_eq_gradWedge (f : C^∞⟮I, M; ℝ⟯) (α : SmoothForm I M ℝ k)
    (x : M) :
    (mextDerivₗ I k (funSMulₗ f α)).1 x =
      f x • (mextDerivₗ I k α).1 x + gradWedge f k x (α.1 x) := by
  have hdf : mvfderiv I f x = innerSL ℝ (Manifold.mgradient I f x) := by
    ext w
    rw [innerSL_apply_apply, Manifold.inner_mgradient]
  ext v
  rw [mextDerivₗ_funSMulₗ_apply, RoughForm.wedge_def, RoughForm.wedgeWith_apply',
    ← ContinuousAlternatingMap.wedge_def, mextDeriv_ofFunction, hdf, add_comm]
  simp only [gradWedge, LinearMap.comp_apply, LinearEquiv.coe_coe,
    alternatingFormEquiv_wedgeLeft_apply, LinearEquiv.apply_symm_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]

/-- **The Leibniz rule for the codifferential**: `d*(f β) = f d*β - ι_(grad f) β` for a smooth
function `f` and a smooth `(k + 1)`-form `β`. The commutator `[d*, f] = -ι_(grad f)` is a
zeroth-order operator, the principal symbol of `d*` at `df` up to the factor `i`. -/
theorem coe_codifferential_funSMulₗ (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + l = m) (f : C^∞⟮I, M; ℝ⟯) (β : SmoothForm I M ℝ (k + 1)) :
    (codifferential o hkl (funSMulₗ f β) : RoughForm I M ℝ k) =
      (fun x ↦ f x • (codifferential o hkl β).1 x) -
        RoughForm.interior (Manifold.mgradient I f) β.1 := by
  have hlk : l + 1 + k = m := by omega
  funext x
  have hfin := o.fact_finrank_tangentSpace x
  obtain ⟨b, hb⟩ := (alternatingFormEquiv (TangentSpace I x) (k + 1)).surjective (β.1 x)
  rw [codifferential_apply o hkl hlk, hodgeStar_funSMulₗ, codifferential_apply o hkl hlk]
  simp only [SetLike.val_smul, coe_hodgeStar, Pi.smul_apply, RoughForm.hodgeStar_apply,
    mextDerivₗ_funSMulₗ_eq_gradWedge, map_add, map_smul, smul_add, Pi.sub_apply]
  rw [smul_comm, sub_eq_add_neg, ← gradContr_apply, ← hb]
  congr 1
  simp only [gradWedge, gradContr, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Orientation.formHodgeStar_alternatingFormEquiv, LinearEquiv.symm_apply_apply]
  -- `ι_u = (-1) ^ (m k) ⋆ ε_u ⋆` on `(k + 1)`-forms, and `(-1) ^ (m (k + 2) + 1 + m k) = -1`.
  have key := (o.orientationAt x).koszulDifferential_eq_smul_hodgeStar_wedgeLeft_hodgeStar
    (Manifold.mgradient I f x) (hkl.trans hfin.out.symm) (hlk.trans hfin.out.symm) b
  replace key := congrArg ((-1 : ℝ) ^ (Module.finrank ℝ (TangentSpace I x) * k) • ·) key
  rw [smul_smul, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, one_smul] at key
  have hsign :
      (-1 : ℝ) ^ (m * (k + 2) + 1) * (-1) ^ (Module.finrank ℝ (TangentSpace I x) * k) = -1 := by
    rw [hfin.out, ← pow_add]
    exact Odd.neg_one_pow ⟨m * (k + 1), by ring⟩
  rw [← key, map_smul, smul_smul, hsign]
  exact neg_one_smul ℝ (M := TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) _

/-- `[d*, f] = -ι_(grad f)`, in the form consumed by the double commutator computation. -/
private theorem codifferential_funSMulₗ_apply (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + l = m) (f : C^∞⟮I, M; ℝ⟯) (β : SmoothForm I M ℝ (k + 1)) (x : M) :
    (codifferential o hkl (funSMulₗ f β)).1 x =
      f x • (codifferential o hkl β).1 x + (-gradContr f k x) (β.1 x) := by
  rw [congrFun (coe_codifferential_funSMulₗ o hkl f β) x, Pi.sub_apply, sub_eq_add_neg,
    LinearMap.neg_apply, gradContr_apply]

omit [FiniteDimensional ℝ E] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The double commutator `[[Q P, f], g]` of a composite of two operators whose commutators
`[P, h] = A h` and `[Q, h] = B h` with every smooth function `h` are fibrewise is
`(B g) (A f) + (B f) (A g)`. -/
private theorem lie_lie_comp_funSMulₗ_apply {j : ℕ}
    (P : SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ j)
    (Q : SmoothForm I M ℝ j →ₗ[ℝ] SmoothForm I M ℝ k)
    (A : C^∞⟮I, M; ℝ⟯ → ∀ x : M,
      (TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ) →ₗ[ℝ] TangentSpace I x [⋀^Fin j]→L[ℝ] ℝ)
    (B : C^∞⟮I, M; ℝ⟯ → ∀ x : M,
      (TangentSpace I x [⋀^Fin j]→L[ℝ] ℝ) →ₗ[ℝ] TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)
    (hP : ∀ h α x, (P (funSMulₗ h α)).1 x = h x • (P α).1 x + A h x (α.1 x))
    (hQ : ∀ h β x, (Q (funSMulₗ h β)).1 x = h x • (Q β).1 x + B h x (β.1 x))
    (f g : C^∞⟮I, M; ℝ⟯) (α : SmoothForm I M ℝ k) (x : M) :
    (⁅⁅Q ∘ₗ P, funSMulₗ (F := ℝ) (k := k) f⁆, funSMulₗ g⁆ α).1 x =
      B g x (A f x (α.1 x)) + B f x (A g x (α.1 x)) := by
  -- `P (f g α) = f P (g α) + g P (f α) - f g P α` as smooth forms.
  have hγ : P (funSMulₗ f (funSMulₗ g α)) =
      funSMulₗ f (P (funSMulₗ g α)) + funSMulₗ g (P (funSMulₗ f α)) -
        funSMulₗ f (funSMulₗ g (P α)) := by
    refine Subtype.ext (funext fun y ↦ ?_)
    simp only [hP, coe_funSMulₗ, map_smul, Submodule.coe_add, Submodule.coe_sub, Pi.add_apply,
      Pi.sub_apply]
    module
  simp only [Ring.lie_def, mul_apply_eq_comp, LinearMap.sub_apply, LinearMap.comp_apply,
    map_sub, map_add, hγ, hQ, hP, map_smul, Submodule.coe_add, Submodule.coe_sub, coe_funSMulₗ,
    Pi.add_apply, Pi.sub_apply]
  module

/-- **The principal symbol of the Hodge Laplacian**, polarized: for smooth functions `f` and `g`,
the double commutator of `Δ = d*d + dd*` with multiplication by `f` and `g` is multiplication by
`-2 ⟪grad f, grad g⟫`, `[[Δ, f], g] α = -2 ⟪df, dg⟫ α`. -/
theorem coe_lie_lie_hodgeLaplacian_funSMulₗ (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) (f g : C^∞⟮I, M; ℝ⟯) (α : SmoothForm I M ℝ k) :
    (⁅⁅hodgeLaplacian o hkl, funSMulₗ (F := ℝ) (k := k) f⁆, funSMulₗ g⁆ α : RoughForm I M ℝ k) =
      fun x ↦ (-2 * ⟪Manifold.mgradient I f x, Manifold.mgradient I g x⟫) • α.1 x := by
  funext x
  have hm := (o.fact_finrank_tangentSpace x).out
  have hgf := real_inner_comm (Manifold.mgradient I f x) (Manifold.mgradient I g x)
  rcases k with _ | k <;> rcases l with _ | l
  · -- On a zero-dimensional manifold both sides vanish.
    have : Subsingleton (TangentSpace I x) := Module.finrank_zero_iff.1 (hm.trans (by omega))
    have hL : hodgeLaplacian o hkl = 0 := LinearMap.ext (hodgeLaplacian_zero_zero o hkl)
    rw [hL, Subsingleton.elim (Manifold.mgradient I f x) 0]
    simp [Ring.lie_def]
  · -- On functions `Δ = d*d`, and `[[d*d, f], g] = -ι_v ε_u - ι_u ε_v = -2 ⟪u, v⟫`.
    have h : 0 + 1 + l = m := by omega
    rw [hodgeLaplacian_zero_add_one_eq_comp o hkl h,
      lie_lie_comp_funSMulₗ_apply _ _ (fun f ↦ gradWedge f 0) (fun f ↦ -gradContr f 0)
        (mextDerivₗ_funSMulₗ_eq_gradWedge ·) (codifferential_funSMulₗ_apply o h ·)]
    simp only [Pi.neg_apply, LinearMap.neg_apply, gradContr_gradWedge_zero, hgf]
    module
  · -- In the top degree `Δ = dd*`, and `[[dd*, f], g] = -ε_v ι_u - ε_u ι_v = -2 ⟪u, v⟫`, since
    -- exterior multiplication into degree `k + 2` vanishes.
    have hε (f g : C^∞⟮I, M; ℝ⟯) :
        gradWedge f k x (gradContr g k x (α.1 x)) =
          ⟪Manifold.mgradient I g x, Manifold.mgradient I f x⟫ • α.1 x := by
      rw [← gradWedge_gradContr_add f g k x (α.1 x),
        (gradWedge f (k + 1) x (α.1 x)).eq_zero_of_finrank_lt (by rw [Fintype.card_fin]; omega),
        map_zero, add_zero]
    rw [hodgeLaplacian_add_one_zero_eq_comp o hkl,
      lie_lie_comp_funSMulₗ_apply _ _ (fun f ↦ -gradContr f k) (fun f ↦ gradWedge f k)
        (codifferential_funSMulₗ_apply o hkl ·) (mextDerivₗ_funSMulₗ_eq_gradWedge ·)]
    simp only [Pi.neg_apply, LinearMap.neg_apply, map_neg, hε, hgf]
    module
  · -- In between, `[[Δ, f], g] = -(ι_v ε_u + ε_u ι_v) - (ι_u ε_v + ε_v ι_u) = -2 ⟪u, v⟫`.
    have h : k + 1 + 1 + l = m := by omega
    -- The ring commutator is additive in its first argument; `add_lie` would need the Lie ring
    -- structure of `Mathlib.Algebra.Lie.OfAssociative`, which is not imported here.
    have hadd (a b c d : Module.End ℝ (SmoothForm I M ℝ (k + 1))) :
        ⁅⁅a + b, c⁆, d⁆ = ⁅⁅a, c⁆, d⁆ + ⁅⁅b, c⁆, d⁆ := by
      simp only [Ring.lie_def, add_mul, mul_add, sub_mul, mul_sub]
      abel
    rw [hodgeLaplacian_add_one_add_one_eq_comp_add_comp o hkl h, hadd]
    simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply,
      lie_lie_comp_funSMulₗ_apply _ _ (fun f ↦ gradWedge f (k + 1)) (fun f ↦ -gradContr f (k + 1))
        (mextDerivₗ_funSMulₗ_eq_gradWedge ·) (codifferential_funSMulₗ_apply o h ·),
      lie_lie_comp_funSMulₗ_apply _ _ (fun f ↦ -gradContr f k) (fun f ↦ gradWedge f k)
        (codifferential_funSMulₗ_apply o hkl ·) (mextDerivₗ_funSMulₗ_eq_gradWedge ·),
      Pi.neg_apply, LinearMap.neg_apply, map_neg]
    linear_combination (norm := module) -gradWedge_gradContr_add f g k x (α.1 x) -
      gradWedge_gradContr_add g f k x (α.1 x) - hgf • α.1 x

/-- **The principal symbol of the Hodge Laplacian**: for a smooth function `f`, the double
commutator of `Δ = d*d + dd*` with multiplication by `f` is multiplication by `-2 |grad f|²`,
`[[Δ, f], f] α = -2 |df|² α`. With the normalization `σ(P)(df) = ½ [[P, f], f]` of second-order
principal symbols, the symbol of `Δ` at `df_x` is `-|df_x|² Id`, or `|ξ|² Id` at `ξ = df_x` in the
Fourier convention `σ(∂ⱼ) = i ξⱼ`. -/
theorem coe_lie_lie_hodgeLaplacian_funSMulₗ_self (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) (f : C^∞⟮I, M; ℝ⟯) (α : SmoothForm I M ℝ k) :
    (⁅⁅hodgeLaplacian o hkl, funSMulₗ (F := ℝ) (k := k) f⁆, funSMulₗ f⁆ α : RoughForm I M ℝ k) =
      fun x ↦ (-2 * ⟪Manifold.mgradient I f x, Manifold.mgradient I f x⟫) • α.1 x :=
  coe_lie_lie_hodgeLaplacian_funSMulₗ o hkl f f α

/-! ### The `L²` pairing -/

omit [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- On a positively oriented tangent basis, the top form `|α|² vol` takes a nonnegative value. -/
private theorem inner_self_smul_riemannianVolumeForm_apply_nonneg
    (o : Manifold.Orientation I M (Fin m)) (α : RoughForm I M ℝ k) (x : M)
    (c : Module.Basis (Fin m) ℝ (TangentSpace I x))
    (hc : c.orientation = o.orientationAt x) :
    0 ≤ (alternatingFormInner (TangentSpace I x) k (α x) (α x) • riemannianVolumeForm o x) c := by
  let := o.fact_finrank_tangentSpace x
  rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, riemannianVolumeForm_apply]
  exact mul_nonneg (alternatingFormInner_self_nonneg _)
    (Orientation.volumeForm_apply_pos_iff.2 hc).le

omit [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- **The `L²` pairing of forms is nonnegative**: on an oriented Riemannian manifold of positive
dimension, `0 ≤ ∫_M |α|² vol` for every form `α`, where `|α|²` is the pointwise inner product of
`α` with itself and `vol` the Riemannian volume form. -/
theorem _root_.TauCeti.RoughForm.integralTopForm_inner_self_smul_riemannianVolumeForm_nonneg
    [NeZero m] (o : Manifold.Orientation I M (Fin m)) (α : RoughForm I M ℝ k) :
    0 ≤ integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k (α x) (α x) •
      riemannianVolumeForm o x) :=
  integralTopForm_nonneg o (inner_self_smul_riemannianVolumeForm_apply_nonneg o α)

omit [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The `L²` pairing vanishes when its first argument is zero: `∫_M ⟨0, β⟩ vol = 0`. -/
theorem integralTopForm_inner_zero_left (o : Manifold.Orientation I M (Fin m))
    (β : SmoothForm I M ℝ k) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
      ((0 : SmoothForm I M ℝ k).1 x) (β.1 x) • riemannianVolumeForm o x) = 0 := by
  simp only [ZeroMemClass.coe_zero, Pi.zero_apply, LinearMap.map_zero₂, zero_smul]
  exact integralTopForm_zero o

/-- **The `L²` pairing of forms is definite**: on an oriented Riemannian manifold of positive
dimension `m = k + l`, a compactly supported smooth `k`-form `α` satisfies `∫_M |α|² vol = 0`
exactly when `α = 0`. -/
theorem integralTopForm_inner_self_smul_riemannianVolumeForm_eq_zero_iff [NeZero m]
    (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) {α : SmoothForm I M ℝ k}
    (hα : α ∈ compactlySupportedForms I M k) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k (α.1 x) (α.1 x) •
      riemannianVolumeForm o x) = 0 ↔ α = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_contra hne
    obtain ⟨x, hx⟩ : ∃ x, α.1 x ≠ 0 := by
      by_contra! h'
      exact hne (Subtype.ext (funext h'))
    -- A positively oriented orthonormal basis at `x`, on which `|α|² vol` is `|α x|² > 0`.
    let := o.fact_finrank_tangentSpace x
    let b := (o.orientationAt x).finOrthonormalBasis (NeZero.pos m) Fact.out
    have hb : b.toBasis.orientation = o.orientationAt x := by simp [b]
    refine (integralTopForm_pos o
      ((isSmoothForm_inner_smul_riemannianVolumeForm o hkl α α).of_le bot_le)
      (RoughForm.isCompact_tsupport_inner_smul_riemannianVolumeForm o α.1 α.1
        ((mem_compactlySupportedForms I).mp hα))
      (inner_self_smul_riemannianVolumeForm_apply_nonneg o α.1) ⟨x, b.toBasis, hb, ?_⟩).ne' h
    rw [ContinuousAlternatingMap.smul_apply, smul_eq_mul, OrthonormalBasis.coe_toBasis,
      riemannianVolumeForm_apply_orthonormal o x b hb, mul_one]
    exact (alternatingFormInner_self_nonneg _).lt_of_ne
      (Ne.symm (mt alternatingFormInner_self_eq_zero.1 hx))
  · subst h
    exact integralTopForm_inner_zero_left o 0

omit [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- The `L²` pairing of forms is symmetric: `∫_M ⟨α, β⟩ vol = ∫_M ⟨β, α⟩ vol`. -/
theorem _root_.TauCeti.RoughForm.integralTopForm_inner_smul_riemannianVolumeForm_comm
    (o : Manifold.Orientation I M (Fin m)) (α β : RoughForm I M ℝ k) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k (α x) (β x) •
      riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k (β x) (α x) •
        riemannianVolumeForm o x) := by
  congr 1
  funext x
  rw [alternatingFormInner_comm]

/-- The `L²` pairing of forms is additive in its first argument,
`∫_M ⟨α + β, γ⟩ vol = ∫_M ⟨α, γ⟩ vol + ∫_M ⟨β, γ⟩ vol`, when `α` and `β` or `γ` are compactly
supported. -/
theorem integralTopForm_inner_add_left (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m)
    (α β γ : SmoothForm I M ℝ k)
    (h : (α ∈ compactlySupportedForms I M k ∧ β ∈ compactlySupportedForms I M k) ∨
      γ ∈ compactlySupportedForms I M k) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k ((α + β).1 x) (γ.1 x) •
      riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k (α.1 x) (γ.1 x) •
        riemannianVolumeForm o x) +
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k (β.1 x) (γ.1 x) •
        riemannianVolumeForm o x) := by
  -- Each top form `⟨φ, γ⟩ vol` is compactly supported, read through the symmetric pairing.
  have hc (φ : SmoothForm I M ℝ k) (hφ : φ ∈ compactlySupportedForms I M k ∨
      γ ∈ compactlySupportedForms I M k) :
      IsCompact (_root_.tsupport (α := E [⋀^Fin m]→L[ℝ] ℝ)
        (fun x ↦ alternatingFormInner (TangentSpace I x) k (φ.1 x) (γ.1 x) •
          riemannianVolumeForm o x)) := by
    rcases hφ with hφ | hγ
    · exact RoughForm.isCompact_tsupport_inner_smul_riemannianVolumeForm o φ.1 γ.1
        ((mem_compactlySupportedForms I).1 hφ)
    · have := RoughForm.isCompact_tsupport_inner_smul_riemannianVolumeForm o γ.1 φ.1
        ((mem_compactlySupportedForms I).1 hγ)
      simp_rw [alternatingFormInner_comm (γ.1 _)] at this
      exact this
  rw [← integralTopForm_add o ((isSmoothForm_inner_smul_riemannianVolumeForm o hkl α γ).of_le
      bot_le) ((isSmoothForm_inner_smul_riemannianVolumeForm o hkl β γ).of_le bot_le)
      (hc α (h.imp_left And.left)) (hc β (h.imp_left And.right))]
  congr 1
  funext x
  rw [Submodule.coe_add, Pi.add_apply, LinearMap.map_add₂, add_smul, Pi.add_apply]

/-! ### Green's formulas and positivity of a Laplacian -/

section Laplacian

variable (o : Manifold.Orientation I M (Fin m))
  {D : ∀ k, SmoothForm I M ℝ k →ₗ[ℝ] SmoothForm I M ℝ (k + 1)}
  {δ : ∀ {k l : ℕ}, k + 1 + l = m → SmoothForm I M ℝ (k + 1) →ₗ[ℝ] SmoothForm I M ℝ k}
  (hD : ∀ {k : ℕ} {α : SmoothForm I M ℝ k},
    α ∈ compactlySupportedForms I M k → D k α ∈ compactlySupportedForms I M (k + 1))
  (hδ : ∀ {k l : ℕ} (hkl : k + 1 + l = m) {β : SmoothForm I M ℝ (k + 1)},
    β ∈ compactlySupportedForms I M (k + 1) → δ hkl β ∈ compactlySupportedForms I M k)
  (hadj : ∀ {k l : ℕ} (hkl : k + 1 + l = m) (α : SmoothForm I M ℝ k)
    (β : SmoothForm I M ℝ (k + 1)),
    α ∈ compactlySupportedForms I M k ∨ β ∈ compactlySupportedForms I M (k + 1) →
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) (k + 1)
          ((D k α).1 x) (β.1 x) • riemannianVolumeForm o x) =
        integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
          (α.1 x) ((δ hkl β).1 x) • riemannianVolumeForm o x))
include hadj

include hD in
omit [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- Green's formula `∫_M ⟨δDα, β⟩ vol = ∫_M ⟨Dα, Dβ⟩ vol` for a formal adjoint `δ` of `D`. -/
theorem integralTopForm_inner_codiff_diff (hkl : k + 1 + l = m)
    (α β : SmoothForm I M ℝ k)
    (h : α ∈ compactlySupportedForms I M k ∨ β ∈ compactlySupportedForms I M k) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((δ hkl (D k α)).1 x) (β.1 x) • riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) (k + 1)
        ((D k α).1 x) ((D k β).1 x) • riemannianVolumeForm o x) := by
  rw [RoughForm.integralTopForm_inner_smul_riemannianVolumeForm_comm,
    ← hadj hkl β _ (h.symm.imp_right fun hα ↦ hD hα),
    RoughForm.integralTopForm_inner_smul_riemannianVolumeForm_comm]

include hδ in
omit [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
/-- Green's formula `∫_M ⟨Dδα, β⟩ vol = ∫_M ⟨δα, δβ⟩ vol` for a formal adjoint `δ` of `D`. -/
theorem integralTopForm_inner_diff_codiff (hkl : k + 1 + l = m)
    (α β : SmoothForm I M ℝ (k + 1))
    (h : α ∈ compactlySupportedForms I M (k + 1) ∨ β ∈ compactlySupportedForms I M (k + 1)) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) (k + 1)
        ((D k (δ hkl α)).1 x) (β.1 x) • riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((δ hkl α).1 x) ((δ hkl β).1 x) • riemannianVolumeForm o x) :=
  hadj hkl _ β (h.imp_left (hδ hkl))

include hD hδ

/-- **The Dirichlet pairing of a Laplacian**: if `δ` is a formal adjoint of `D` and both preserve
compact support, then strictly between degree `0` and the top degree
`∫_M ⟨Δα, β⟩ vol = ∫_M ⟨Dα, Dβ⟩ vol + ∫_M ⟨δα, δβ⟩ vol` for `Δ = δD + Dδ` and smooth forms `α`
and `β`, one of them compactly supported. -/
theorem integralTopForm_inner_laplacian_add_one_add_one (hkl : k + 1 + (l + 1) = m)
    (α β : SmoothForm I M ℝ (k + 1))
    (h : α ∈ compactlySupportedForms I M (k + 1) ∨ β ∈ compactlySupportedForms I M (k + 1)) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) (k + 1)
        ((laplacian D δ hkl α).1 x) (β.1 x) • riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) (k + 1 + 1)
        ((D (k + 1) α).1 x) ((D (k + 1) β).1 x) • riemannianVolumeForm o x) +
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((δ hkl α).1 x) ((δ hkl β).1 x) • riemannianVolumeForm o x) := by
  have hkl' : k + 1 + 1 + l = m := by omega
  rw [laplacian_add_one_add_one D δ hkl hkl', integralTopForm_inner_add_left o hkl _ _ _
      (h.imp_left fun hα ↦ ⟨hδ hkl' (hD hα), hD (hδ hkl hα)⟩),
    integralTopForm_inner_codiff_diff o hD hadj hkl' α β h,
    integralTopForm_inner_diff_codiff o hδ hadj hkl α β h]

/-- **A Laplacian is formally self-adjoint**: if `δ` is a formal adjoint of `D` and both preserve
compact support, then `∫_M ⟨Δα, β⟩ vol = ∫_M ⟨α, Δβ⟩ vol` for `Δ = δD + Dδ` and smooth `k`-forms
`α` and `β`, one of them compactly supported. -/
theorem integralTopForm_inner_laplacian_eq_inner_laplacian (hkl : k + l = m)
    (α β : SmoothForm I M ℝ k)
    (h : α ∈ compactlySupportedForms I M k ∨ β ∈ compactlySupportedForms I M k) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((laplacian D δ hkl α).1 x) (β.1 x) • riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        (α.1 x) ((laplacian D δ hkl β).1 x) • riemannianVolumeForm o x) := by
  -- Both sides are the symmetric Dirichlet pairing `∫ ⟨Dα, Dβ⟩ vol + ∫ ⟨δα, δβ⟩ vol`.
  rw [RoughForm.integralTopForm_inner_smul_riemannianVolumeForm_comm
    (β := (laplacian D δ hkl β).1)]
  rcases k with _ | k <;> rcases l with _ | l
  · simp
  · rw [laplacian_zero_add_one D δ hkl (by omega), laplacian_zero_add_one D δ hkl (by omega),
      integralTopForm_inner_codiff_diff o hD hadj _ α β h,
      integralTopForm_inner_codiff_diff o hD hadj _ β α h.symm,
      RoughForm.integralTopForm_inner_smul_riemannianVolumeForm_comm]
  · rw [laplacian_add_one_zero, laplacian_add_one_zero,
      integralTopForm_inner_diff_codiff o hδ hadj hkl α β h,
      integralTopForm_inner_diff_codiff o hδ hadj hkl β α h.symm,
      RoughForm.integralTopForm_inner_smul_riemannianVolumeForm_comm]
  · rw [integralTopForm_inner_laplacian_add_one_add_one o hD hδ hadj hkl α β h,
      integralTopForm_inner_laplacian_add_one_add_one o hD hδ hadj hkl β α h.symm,
      RoughForm.integralTopForm_inner_smul_riemannianVolumeForm_comm (β := (D _ α).1),
      RoughForm.integralTopForm_inner_smul_riemannianVolumeForm_comm (β := (δ hkl α).1)]

omit hD hδ in
/-- **A Laplacian is nonnegative**: if `δ` is a formal adjoint of `D`, then `0 ≤ ∫_M ⟨Δα, α⟩ vol`
for `Δ = δD + Dδ` and every compactly supported smooth form `α`. -/
theorem integralTopForm_inner_laplacian_self_nonneg (hkl : k + l = m) {α : SmoothForm I M ℝ k}
    (hα : α ∈ compactlySupportedForms I M k) :
    0 ≤ integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
      ((laplacian D δ hkl α).1 x) (α.1 x) • riemannianVolumeForm o x) := by
  -- Since `α` is compactly supported, `∫ ⟨δDα, α⟩ vol = ∫ |Dα|² vol` and
  -- `∫ ⟨Dδα, α⟩ vol = ∫ |δα|² vol`.
  have hup {l : ℕ} (hkl : k + 1 + l = m) : integralTopForm o (fun x ↦
      alternatingFormInner (TangentSpace I x) k ((δ hkl (D k α)).1 x) (α.1 x) •
        riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) (k + 1)
        ((D k α).1 x) ((D k α).1 x) • riemannianVolumeForm o x) := by
    rw [RoughForm.integralTopForm_inner_smul_riemannianVolumeForm_comm, hadj hkl α _ (.inl hα)]
  rcases k with _ | k <;> rcases l with _ | l
  · rw [laplacian_zero_zero, integralTopForm_inner_zero_left]
  · have : NeZero m := ⟨by omega⟩
    rw [laplacian_zero_add_one D δ hkl (by omega), hup]
    exact RoughForm.integralTopForm_inner_self_smul_riemannianVolumeForm_nonneg o _
  · have : NeZero m := ⟨by omega⟩
    rw [laplacian_add_one_zero, hadj hkl _ α (.inr hα)]
    exact RoughForm.integralTopForm_inner_self_smul_riemannianVolumeForm_nonneg o _
  · have : NeZero m := ⟨by omega⟩
    rw [laplacian_add_one_add_one D δ hkl (by omega),
      integralTopForm_inner_add_left o hkl _ _ α (.inr hα), hup, hadj hkl _ α (.inr hα)]
    exact add_nonneg (RoughForm.integralTopForm_inner_self_smul_riemannianVolumeForm_nonneg o _)
      (RoughForm.integralTopForm_inner_self_smul_riemannianVolumeForm_nonneg o _)

omit hδ in
/-- **The kernel of a Laplacian on functions**: if `δ` is a formal adjoint of `D` and `D`
preserves compact support, then a compactly supported smooth function `f` satisfies `Δf = 0`
for `Δ = δD` exactly when `Df = 0`. -/
theorem laplacian_eq_zero_iff_apply_eq_zero (hl : 0 + l = m) {f : SmoothForm I M ℝ 0}
    (hf : f ∈ compactlySupportedForms I M 0) : laplacian D δ hl f = 0 ↔ D 0 f = 0 := by
  rcases l with _ | l
  · simpa using (D 0 f).eq_zero_of_finrank_lt (by rw [← o.card_eq, Fintype.card_fin]; omega)
  have : NeZero m := ⟨by omega⟩
  have hl' : 0 + 1 + l = m := by omega
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [laplacian_zero_add_one D δ hl hl', h, map_zero]⟩
  -- `0 = ∫ ⟨Δf, f⟩ vol = ∫ |Df|² vol`, and the pairing is definite.
  have hint := integralTopForm_inner_codiff_diff o hD hadj hl' f f (.inl hf)
  rw [← laplacian_zero_add_one D δ hl hl', h, integralTopForm_inner_zero_left] at hint
  exact (integralTopForm_inner_self_smul_riemannianVolumeForm_eq_zero_iff o hl' (hD hf)).1
    hint.symm

/-- **The kernel of a Laplacian in positive degree**: if `δ` is a formal adjoint of `D` and both
preserve compact support, then a compactly supported smooth `(k + 1)`-form `α` satisfies `Δα = 0`
for `Δ = δD + Dδ` exactly when `Dα = 0` and `δα = 0`. -/
theorem laplacian_eq_zero_iff (hkl : k + 1 + l = m) {α : SmoothForm I M ℝ (k + 1)}
    (hα : α ∈ compactlySupportedForms I M (k + 1)) :
    laplacian D δ hkl α = 0 ↔ D (k + 1) α = 0 ∧ δ hkl α = 0 := by
  have : NeZero m := ⟨by omega⟩
  -- The pairing `∫ |δα|² vol` is definite.
  have hdown : integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
      ((δ hkl α).1 x) ((δ hkl α).1 x) • riemannianVolumeForm o x) = 0 ↔ δ hkl α = 0 :=
    integralTopForm_inner_self_smul_riemannianVolumeForm_eq_zero_iff o
      (show k + (l + 1) = m by omega) (hδ hkl hα)
  rcases l with _ | l
  · have hd : D (k + 1) α = 0 :=
      SmoothForm.eq_zero_of_finrank_lt (by rw [← o.card_eq, Fintype.card_fin]; omega) _
    refine ⟨fun h ↦ ⟨hd, hdown.1 ?_⟩, fun h ↦ ?_⟩
    · rw [← integralTopForm_inner_diff_codiff o hδ hadj hkl α α (.inl hα),
        ← laplacian_add_one_zero, h, integralTopForm_inner_zero_left]
    · rw [laplacian_add_one_zero, h.2, map_zero]
  · have hkl' : k + 1 + 1 + l = m := by omega
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · -- `0 = ∫ ⟨Δα, α⟩ vol = ∫ |Dα|² vol + ∫ |δα|² vol`, a sum of nonnegative terms.
      have hint := integralTopForm_inner_laplacian_add_one_add_one o hD hδ hadj hkl α α (.inl hα)
      rw [h, integralTopForm_inner_zero_left, eq_comm, add_eq_zero_iff_of_nonneg
        (RoughForm.integralTopForm_inner_self_smul_riemannianVolumeForm_nonneg o _)
        (RoughForm.integralTopForm_inner_self_smul_riemannianVolumeForm_nonneg o _)] at hint
      exact ⟨(integralTopForm_inner_self_smul_riemannianVolumeForm_eq_zero_iff o hkl'
        (hD hα)).1 hint.1, hdown.1 hint.2⟩
    · rw [laplacian_add_one_add_one D δ hkl hkl', h.1, h.2, map_zero, map_zero, add_zero]

end Laplacian

variable [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

/-- **The codifferential is the formal adjoint of the exterior derivative**: on an oriented
boundaryless Riemannian manifold, for smooth forms `α` of degree `k` and `β` of degree `k + 1`,
one of them compactly supported, `∫_M ⟨dα, β⟩ vol = ∫_M ⟨α, d*β⟩ vol`, where `⟨·, ·⟩` is the
pointwise inner product of forms and `vol` the Riemannian volume form. -/
theorem integralTopForm_inner_mextDeriv_eq_inner_codifferential
    (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + l = m) (α : SmoothForm I M ℝ k)
    (β : SmoothForm I M ℝ (k + 1))
    (h : α ∈ compactlySupportedForms I M k ∨ β ∈ compactlySupportedForms I M (k + 1)) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) (k + 1)
        ((mextDerivₗ I k α).1 x) (β.1 x) • riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        (α.1 x) ((codifferential o hkl β).1 x) • riemannianVolumeForm o x) := by
  obtain rfl : m = k + l + 1 := by omega
  rw [mem_compactlySupportedForms, mem_compactlySupportedForms] at h
  have hkl' : k + (l + 1) = k + l + 1 := (add_assoc k l 1).symm
  -- Both `α ∧ ⋆β` and `α ∧ ⋆d*β` are compactly supported.
  have hγ := RoughForm.isCompact_tsupport_wedge_hodgeStar o hkl α.1 β.1 h
  have hδ : wedge α (hodgeStar o hkl' (codifferential o hkl β)) ∈
      compactlySupportedForms I M (k + (l + 1)) := by
    rw [mem_compactlySupportedForms, coe_wedge, coe_hodgeStar]
    exact RoughForm.isCompact_tsupport_wedge_hodgeStar o hkl' α.1 _
      (h.imp_right fun hβ ↦ hβ.of_isClosed_subset (_root_.isClosed_tsupport _)
        (tsupport_codifferential_subset o hkl β))
  -- By Green's formula `⟨dα, β⟩ vol = ⟨α, d*β⟩ vol + d (α ∧ ⋆β)`, and Stokes kills the last term.
  have hdγ : IsSmoothForm I 0 (mextDeriv (RoughForm.wedge α.1 (hodgeStar o hkl β).1)) := by
    simpa only [mextDerivₗ_apply, coe_wedge] using
      (mextDerivₗ I (k + l) (wedge α (hodgeStar o hkl β))).isSmoothForm.of_le (by simp)
  rw [sub_eq_iff_eq_add.mp (mextDeriv_wedge_hodgeStar o α β).symm,
    integralTopForm_add o hdγ _ (RoughForm.isCompact_tsupport_mextDeriv (by rwa [coe_hodgeStar])),
    integralTopForm_mextDeriv_eq_zero o
      (by simpa only [coe_wedge] using (wedge α (hodgeStar o hkl β)).isSmoothForm.of_le (by simp))
      (by rwa [coe_hodgeStar]), zero_add]
  all_goals rw [inner_smul_riemannianVolumeForm_eq_wedge_hodgeStar o hkl']
  · exact (mem_compactlySupportedForms I).mp ((cast_mem_compactlySupportedForms_iff I hkl').mpr hδ)
  · exact (isSmoothForm _).of_le bot_le

/-! ### Green's formulas and positivity of the Hodge Laplacian -/

/-- **Green's formula for `d*d`**: on an oriented boundaryless Riemannian manifold,
`∫_M ⟨d*dα, β⟩ vol = ∫_M ⟨dα, dβ⟩ vol` for smooth `k`-forms `α` and `β`, one of them compactly
supported. -/
theorem integralTopForm_inner_codifferential_mextDeriv (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + l = m) (α β : SmoothForm I M ℝ k)
    (h : α ∈ compactlySupportedForms I M k ∨ β ∈ compactlySupportedForms I M k) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((codifferential o hkl (mextDerivₗ I k α)).1 x) (β.1 x) • riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) (k + 1)
        ((mextDerivₗ I k α).1 x) ((mextDerivₗ I k β).1 x) • riemannianVolumeForm o x) :=
  integralTopForm_inner_codiff_diff o (mextDerivₗ_mem_compactlySupportedForms I)
    (integralTopForm_inner_mextDeriv_eq_inner_codifferential o) hkl α β h

/-- **Green's formula for `dd*`**: on an oriented boundaryless Riemannian manifold,
`∫_M ⟨dd*α, β⟩ vol = ∫_M ⟨d*α, d*β⟩ vol` for smooth `(k + 1)`-forms `α` and `β`, one of them
compactly supported. -/
theorem integralTopForm_inner_mextDeriv_codifferential (o : Manifold.Orientation I M (Fin m))
    (hkl : k + 1 + l = m) (α β : SmoothForm I M ℝ (k + 1))
    (h : α ∈ compactlySupportedForms I M (k + 1) ∨ β ∈ compactlySupportedForms I M (k + 1)) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) (k + 1)
        ((mextDerivₗ I k (codifferential o hkl α)).1 x) (β.1 x) • riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((codifferential o hkl α).1 x) ((codifferential o hkl β).1 x) •
          riemannianVolumeForm o x) :=
  integralTopForm_inner_diff_codiff o (codifferential_mem_compactlySupportedForms o)
    (integralTopForm_inner_mextDeriv_eq_inner_codifferential o) hkl α β h

/-- **The Dirichlet pairing of the Hodge Laplacian**: on an oriented boundaryless Riemannian
manifold, strictly between degree `0` and the top degree,
`∫_M ⟨Δα, β⟩ vol = ∫_M ⟨dα, dβ⟩ vol + ∫_M ⟨d*α, d*β⟩ vol` for smooth forms `α` and `β`, one of
them compactly supported. -/
theorem integralTopForm_inner_hodgeLaplacian_add_one_add_one
    (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + (l + 1) = m)
    (α β : SmoothForm I M ℝ (k + 1))
    (h : α ∈ compactlySupportedForms I M (k + 1) ∨ β ∈ compactlySupportedForms I M (k + 1)) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) (k + 1)
        ((hodgeLaplacian o hkl α).1 x) (β.1 x) • riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) (k + 1 + 1)
        ((mextDerivₗ I (k + 1) α).1 x) ((mextDerivₗ I (k + 1) β).1 x) •
          riemannianVolumeForm o x) +
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((codifferential o hkl α).1 x) ((codifferential o hkl β).1 x) •
          riemannianVolumeForm o x) :=
  integralTopForm_inner_laplacian_add_one_add_one o
    (mextDerivₗ_mem_compactlySupportedForms I)
    (codifferential_mem_compactlySupportedForms o)
    (integralTopForm_inner_mextDeriv_eq_inner_codifferential o) hkl α β h

/-- **The Hodge Laplacian is formally self-adjoint**: on an oriented boundaryless Riemannian
manifold, `∫_M ⟨Δα, β⟩ vol = ∫_M ⟨α, Δβ⟩ vol` for smooth `k`-forms `α` and `β`, one of them
compactly supported. -/
theorem integralTopForm_inner_hodgeLaplacian_eq_inner_hodgeLaplacian
    (o : Manifold.Orientation I M (Fin m)) (hkl : k + l = m) (α β : SmoothForm I M ℝ k)
    (h : α ∈ compactlySupportedForms I M k ∨ β ∈ compactlySupportedForms I M k) :
    integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        ((hodgeLaplacian o hkl α).1 x) (β.1 x) • riemannianVolumeForm o x) =
      integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
        (α.1 x) ((hodgeLaplacian o hkl β).1 x) • riemannianVolumeForm o x) :=
  integralTopForm_inner_laplacian_eq_inner_laplacian o
    (mextDerivₗ_mem_compactlySupportedForms I)
    (codifferential_mem_compactlySupportedForms o)
    (integralTopForm_inner_mextDeriv_eq_inner_codifferential o) hkl α β h

/-- **The Hodge Laplacian is nonnegative**: on an oriented boundaryless Riemannian manifold,
`0 ≤ ∫_M ⟨Δα, α⟩ vol` for every compactly supported smooth form `α`. -/
theorem integralTopForm_inner_hodgeLaplacian_self_nonneg (o : Manifold.Orientation I M (Fin m))
    (hkl : k + l = m) {α : SmoothForm I M ℝ k} (hα : α ∈ compactlySupportedForms I M k) :
    0 ≤ integralTopForm o (fun x ↦ alternatingFormInner (TangentSpace I x) k
      ((hodgeLaplacian o hkl α).1 x) (α.1 x) • riemannianVolumeForm o x) :=
  integralTopForm_inner_laplacian_self_nonneg o
    (integralTopForm_inner_mextDeriv_eq_inner_codifferential o) hkl hα

/-- **Harmonic functions are locally constant**: on an oriented boundaryless Riemannian manifold, a
compactly supported smooth function `f` satisfies `Δf = 0` exactly when `df = 0`. -/
theorem hodgeLaplacian_eq_zero_iff_mextDeriv_eq_zero (o : Manifold.Orientation I M (Fin m))
    (hl : 0 + l = m) {f : SmoothForm I M ℝ 0} (hf : f ∈ compactlySupportedForms I M 0) :
    hodgeLaplacian o hl f = 0 ↔ mextDerivₗ I 0 f = 0 :=
  laplacian_eq_zero_iff_apply_eq_zero o (mextDerivₗ_mem_compactlySupportedForms I)
    (integralTopForm_inner_mextDeriv_eq_inner_codifferential o) hl hf

/-- **Harmonic forms are closed and coclosed**: on an oriented boundaryless Riemannian manifold,
a compactly supported smooth `(k + 1)`-form `α` satisfies `Δα = 0` exactly when `dα = 0` and
`d*α = 0`. -/
theorem hodgeLaplacian_eq_zero_iff (o : Manifold.Orientation I M (Fin m)) (hkl : k + 1 + l = m)
    {α : SmoothForm I M ℝ (k + 1)} (hα : α ∈ compactlySupportedForms I M (k + 1)) :
    hodgeLaplacian o hkl α = 0 ↔ mextDerivₗ I (k + 1) α = 0 ∧ codifferential o hkl α = 0 :=
  laplacian_eq_zero_iff o (mextDerivₗ_mem_compactlySupportedForms I)
    (codifferential_mem_compactlySupportedForms o)
    (integralTopForm_inner_mextDeriv_eq_inner_codifferential o) hkl hα

end SmoothForm

end TauCeti
