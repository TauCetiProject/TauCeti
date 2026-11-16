/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.CalibratedFrame
public import TauCeti.Analysis.InnerProductSpace.HodgeStar.Kahler.Basic
public import TauCeti.LinearAlgebra.Complex.Orientation
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Algebra.BigOperators.Ring.SquareZero
import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Basic
import TauCeti.Analysis.InnerProductSpace.SkewSymmetric.NormalForm
import TauCeti.Geometry.Symplectic.Complex.OrthonormalBasis
import TauCeti.Geometry.Symplectic.Finrank
import TauCeti.Geometry.Symplectic.Wirtinger
import TauCeti.LinearAlgebra.ExteriorPower.Basic
import TauCeti.LinearAlgebra.ExteriorPower.Basis

/-!
# The Wirtinger inequality and Kähler calibrations in every degree

On a finite-dimensional real inner product space `V` equipped with an orthogonal almost complex
structure `J`, the Kähler bivector `J.kahlerForm ∈ ⋀[ℝ]^2 V` represents the fundamental two-form
`ω(u, w) = ⟪J u, w⟫`. Its normalized `r`-th exterior power is the `2r`-form
`ωʳ / r!`, defined via the Riesz identification `TauCeti.alternatingFormEquiv` as
`J.kahlerPowerForm r := (r!)⁻¹ • alternatingFormEquiv V (2 * r) ⟨(J.kahlerForm) ^ r, _⟩`.

The **Wirtinger inequality** states that `ωʳ / r!` has comass at most one in every degree, and
comass equal to one whenever `2 * r ≤ finrank ℝ V` (`AlmostComplexStructure.norm_kahlerPowerForm`).
Its calibrated frames are precisely the real-orthonormal `2r`-frames sharing the same oriented
exterior product as a `J`-adapted orthonormal frame `(u₀, J u₀, …, u_{r-1}, J u_{r-1})`
(`AlmostComplexStructure.isCalibratedFrame_kahlerPowerForm_iff`). The proof restricts `ω` to the
span `P` of an orthonormal `2r`-frame, applies the real normal form and Pfaffian divided-power
identity (`TauCeti.exists_orthonormalBasis_twoVector_normalForm`) to the skew-adjoint contraction
`x ↦ P.starProjection (J x)`, and reads off `ωʳ / r! (v) = ± ∏ⱼ μⱼ` with `0 ≤ μⱼ ≤ 1`, where
equality `μⱼ = 1` forces `J` to preserve `P`.

In contrast to comass one, the Hilbert norm `√⟨ωʳ / r!, ωʳ / r!⟩` equals `√(n choose r)` where
`n = finrank ℝ V / 2` (`AlmostComplexStructure.sqrt_alternatingFormInner_kahlerPowerForm`).

Specializing `J` to multiplication by `i` (`AlmostComplexStructure.ofComplexModule E`) yields the
full Hermitian vector space API for `TauCeti.kahlerForm E` (`(v, w) ↦ Im ⟪v, w⟫_ℂ`) and
`TauCeti.kahlerPowerForm E r`, including degree-two Wirtinger without finite-dimensionality,
naturality under all complex linear isometries (and in particular unitary invariance), the
non-orthonormal plane equality characterization, and the all-degree calibrated frame
classification in terms of `TauCeti.complexToRealFamily`.

## Main definitions

* `TauCeti.AlmostComplexStructure.kahlerPowerForm`: the normalized Kähler power `ωʳ / r!` of an
  almost complex structure `J`.
* `TauCeti.kahlerForm`: the Kähler two-form `ω(v, w) = Im ⟪v, w⟫_ℂ` on a complex inner product
  space.
* `TauCeti.kahlerPowerForm`: the normalized Kähler power `ωʳ / r!` on a finite-dimensional
  Hermitian vector space.

## Main results

* `TauCeti.alternatingFormEquiv_pow_compContinuousLinearMap`: pulling back the form of `Bʳ` along
  any continuous linear map equals the form of the `r`-th power of the pulled-back bivector.
* `TauCeti.AlmostComplexStructure.norm_kahlerPowerForm` and
  `TauCeti.AlmostComplexStructure.isCalibratedFrame_kahlerPowerForm_iff`: the Wirtinger inequality
  and equality classification for an orthogonal almost complex structure in every degree.
* `TauCeti.AlmostComplexStructure.sqrt_alternatingFormInner_kahlerPowerForm`: the Hilbert norm of
  `ωʳ / r!` is `√((finrank ℝ V / 2).choose r)`.
* `TauCeti.norm_kahlerForm`, `TauCeti.isCalibratedFrame_kahlerForm_iff`, and
  `TauCeti.kahlerForm_apply_eq_norm_ιMulti_iff`: degree-two Wirtinger inequality and equality
  characterizations on complex inner product spaces.
* `TauCeti.norm_kahlerPowerForm`, `TauCeti.isCalibratedFrame_kahlerPowerForm_iff`,
  `TauCeti.kahlerPowerForm_comp_linearIsometry`, and
  `TauCeti.sqrt_alternatingFormInner_kahlerPowerForm`: all-degree Wirtinger inequality, calibrated
  frame classification, naturality under complex linear isometries, and Hilbert norm on any
  finite-dimensional Hermitian vector space.

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. **148** (1982), Theorem II.6.11
  and Lemma II.6.13.
* H. Federer, *Geometric Measure Theory*, Springer (1969), §1.8.2.
* R. C. McLean, *Deformations of calibrated submanifolds*, Comm. Anal. Geom. **6** (1998),
  705–747.
-/

public section

noncomputable section

open Module exteriorPower
open scoped InnerProductSpace RealInnerProductSpace

namespace TauCeti

/-! ### General real-vs-complex inner product and pullback of bivector powers -/

/-- Any real inner product sharing the norm of an `RCLike` inner product agrees with its real part,
by the polarization identity. -/
theorem inner_real_eq_re_inner {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] [InnerProductSpace 𝕜 E] (x y : E) :
    ⟪x, y⟫_ℝ = RCLike.re ⟪x, y⟫_𝕜 := by
  have h1 := norm_add_sq_real x y
  have h2 := norm_add_sq (𝕜 := 𝕜) x y
  linarith

/-- The `r`-th exterior power of a bivector `B ∈ ⋀² W`, viewed in `⋀^(2r) W`. -/
private def bivectorPow {W : Type*} [AddCommGroup W] [Module ℝ W]
    (B : ⋀[ℝ]^2 W) (r : ℕ) : ⋀[ℝ]^(2 * r) W :=
  ⟨(B : _root_.ExteriorAlgebra ℝ W) ^ r, by
    simpa [pow_mul] using Submodule.pow_mem_pow _ B.2 r⟩

private theorem bivectorPow_zero {W : Type*} [AddCommGroup W] [Module ℝ W]
    (B : ⋀[ℝ]^2 W) :
    bivectorPow B 0 = ιMulti ℝ 0 ![] :=
  Subtype.ext (by simp [bivectorPow, _root_.ExteriorAlgebra.ιMulti_zero_apply])

private theorem bivectorPow_succ {W : Type*} [AddCommGroup W] [Module ℝ W]
    (B : ⋀[ℝ]^2 W) (r : ℕ) :
    bivectorPow B (r + 1) = exteriorPower.wedge ℝ W (2 * r) 2 (bivectorPow B r) B :=
  Subtype.ext (by simp [bivectorPow, pow_succ])

/-- Pulling back the `2r`-form of the `r`-th exterior power of a bivector `B ∈ ⋀² E` along any
continuous linear map `L : W →L[ℝ] E` yields the `2r`-form of the `r`-th exterior power of the
pulled-back bivector in `⋀² W`. -/
theorem alternatingFormEquiv_pow_compContinuousLinearMap
    {W E : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : W →L[ℝ] E) (B : ⋀[ℝ]^2 E) (r : ℕ) :
    (alternatingFormEquiv E (2 * r)
        ⟨(B : _root_.ExteriorAlgebra ℝ E) ^ r, by
          simpa [pow_mul] using Submodule.pow_mem_pow _ B.2 r⟩
      ).compContinuousLinearMap L =
      alternatingFormEquiv W (2 * r)
        ⟨(((alternatingFormEquiv W 2).symm
              ((alternatingFormEquiv E 2 B).compContinuousLinearMap L) : ⋀[ℝ]^2 W) :
            _root_.ExteriorAlgebra ℝ W) ^ r,
          by simpa [pow_mul] using Submodule.pow_mem_pow _ ((alternatingFormEquiv W 2).symm _).2 r⟩
    := by
  set B_W : ⋀[ℝ]^2 W :=
    (alternatingFormEquiv W 2).symm ((alternatingFormEquiv E 2 B).compContinuousLinearMap L)
  change (alternatingFormEquiv E (2 * r) (bivectorPow B r)).compContinuousLinearMap L =
    alternatingFormEquiv W (2 * r) (bivectorPow B_W r)
  induction r with
  | zero =>
    ext v
    have : IsEmpty (Fin (2 * 0)) := ⟨fun i ↦ Fin.elim0 i⟩
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, bivectorPow_zero,
      alternatingFormEquiv_ιMulti_apply]
    rw [Matrix.det_isEmpty, Matrix.det_isEmpty]
  | succ r ih =>
    change (alternatingFormEquiv E (2 * r + 2) (bivectorPow B (r + 1))).compContinuousLinearMap L =
      alternatingFormEquiv W (2 * r + 2) (bivectorPow B_W (r + 1))
    rw [bivectorPow_succ, bivectorPow_succ, alternatingFormEquiv_wedge, alternatingFormEquiv_wedge,
      ← ContinuousAlternatingMap.wedge_compContinuousLinearMap, ih]
    simp [B_W]

/-! ### Wirtinger inequality for orthogonal almost complex structures -/

namespace AlmostComplexStructure

section KahlerPower

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The normalized `r`-th Kähler power `ωʳ / r!` of an almost complex structure `J` on a
finite-dimensional real inner product space, as a continuous alternating `2r`-form. -/
def kahlerPowerForm (J : AlmostComplexStructure V) (r : ℕ) : V [⋀^Fin (2 * r)]→L[ℝ] ℝ :=
  (r.factorial : ℝ)⁻¹ • alternatingFormEquiv V (2 * r) (bivectorPow J.kahlerForm r)

/-- In degree zero, `ω⁰ / 0!` is the constant form `1`. -/
@[simp]
theorem kahlerPowerForm_zero (J : AlmostComplexStructure V) :
    J.kahlerPowerForm 0 = ContinuousAlternatingMap.constOfIsEmpty ℝ V (Fin 0) 1 := by
  ext v
  have : IsEmpty (Fin (2 * 0)) := ⟨fun i ↦ Fin.elim0 i⟩
  simp only [kahlerPowerForm, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    bivectorPow_zero, alternatingFormEquiv_ιMulti_apply,
    ContinuousAlternatingMap.constOfIsEmpty_apply]
  rw [Matrix.det_isEmpty]

/-- In degree two (`r = 1`), `ω¹ / 1!` is the alternating two-form of `J.kahlerForm`. -/
@[simp]
theorem kahlerPowerForm_one (J : AlmostComplexStructure V) :
    J.kahlerPowerForm 1 = alternatingFormEquiv V 2 J.kahlerForm := by
  simp [kahlerPowerForm, bivectorPow]

/-- Wedge recurrence for normalized Kähler powers:
`ω^(r+1) / (r+1)! = (r + 1)⁻¹ • (ωʳ / r!) ∧ ω`. -/
theorem kahlerPowerForm_succ (J : AlmostComplexStructure V) (r : ℕ) :
    J.kahlerPowerForm (r + 1) =
      ((r + 1 : ℕ) : ℝ)⁻¹ •
        (J.kahlerPowerForm r).wedge (alternatingFormEquiv V 2 J.kahlerForm) := by
  rw [kahlerPowerForm]
  change ((r + 1).factorial : ℝ)⁻¹ •
      alternatingFormEquiv V (2 * r + 2) (bivectorPow J.kahlerForm (r + 1)) = _
  rw [bivectorPow_succ, alternatingFormEquiv_wedge, kahlerPowerForm,
    ContinuousAlternatingMap.wedge_smul_left, smul_smul, Nat.factorial_succ, Nat.cast_mul,
    mul_inv]

/-- Normalized Kähler powers vanish above the real dimension of `V`. -/
theorem kahlerPowerForm_eq_zero_of_finrank_lt (J : AlmostComplexStructure V) {r : ℕ}
    (hr : finrank ℝ V < 2 * r) : J.kahlerPowerForm r = 0 := by
  rw [kahlerPowerForm, exteriorPower.eq_zero_of_finrank_lt (2 * r) hr (bivectorPow J.kahlerForm r),
    map_zero, smul_zero]

/-- For any almost complex structure `J` (not necessarily orthogonal), pairing `J.kahlerForm` with
`u ∧ w` evaluates the skew-symmetrization `(⟪J u, w⟫ - ⟪J w, u⟫) / 2`. -/
theorem inner_kahlerForm_ιMulti_eq (J : AlmostComplexStructure V) (u w : V) :
    ⟪J.kahlerForm, ιMulti ℝ 2 ![u, w]⟫ = (2⁻¹ : ℝ) * (⟪J u, w⟫ - ⟪J w, u⟫) := by
  have hsum (x y : V) :
      ∑ i, ⟪stdOrthonormalBasis ℝ V i, x⟫ * ⟪J (stdOrthonormalBasis ℝ V i), y⟫ = ⟪J x, y⟫ := by
    calc ∑ i, ⟪stdOrthonormalBasis ℝ V i, x⟫ * ⟪J (stdOrthonormalBasis ℝ V i), y⟫
        = ⟪J (∑ i, ⟪stdOrthonormalBasis ℝ V i, x⟫ • stdOrthonormalBasis ℝ V i), y⟫ := by
          simp only [map_sum, map_smul, sum_inner, real_inner_smul_left]
      _ = ⟪J x, y⟫ := by rw [(stdOrthonormalBasis ℝ V).sum_repr' x]
  simp only [kahlerForm_def, real_inner_smul_left, sum_inner, inner_ιMulti_two,
    Finset.sum_sub_distrib, hsum]

/-- Naturality of `kahlerPowerForm` under complex-linear isometric embeddings into a real inner
product space with an orthogonal almost complex structure. -/
theorem kahlerPowerForm_comp_linearIsometry {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} (hJ' : ∀ u w, ⟪J' u, J' w⟫ = ⟪u, w⟫)
    (f : V →ₗᵢ[ℝ] W) (hf : ∀ v, f (J v) = J' (f v)) (r : ℕ) :
    (J'.kahlerPowerForm r).compContinuousLinearMap f.toContinuousLinearMap =
      J.kahlerPowerForm r := by
  have hJ (u w : V) : ⟪J u, J w⟫ = ⟪u, w⟫ := by
    rw [← f.inner_map_map (J u) (J w), hf u, hf w, hJ', f.inner_map_map]
  have h2 : (alternatingFormEquiv W 2 J'.kahlerForm).compContinuousLinearMap
      f.toContinuousLinearMap = alternatingFormEquiv V 2 J.kahlerForm := by
    ext v
    have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
    have hfv : (f.toContinuousLinearMap ∘ v) = ![f (v 0), f (v 1)] := by
      ext i; fin_cases i <;> rfl
    rw [ContinuousAlternatingMap.compContinuousLinearMap_apply, hfv, alternatingFormEquiv_apply,
      inner_kahlerForm_ιMulti hJ', ← hf, f.inner_map_map, ← inner_kahlerForm_ιMulti hJ,
      ← alternatingFormEquiv_apply, ← hv]
  have hsymm : (alternatingFormEquiv V 2).symm
      ((alternatingFormEquiv W 2 J'.kahlerForm).compContinuousLinearMap
        f.toContinuousLinearMap) = J.kahlerForm := by
    rw [h2, LinearEquiv.symm_apply_apply]
  have hsmul (c : ℝ) (φ : W [⋀^Fin (2 * r)]→L[ℝ] ℝ) :
      (c • φ).compContinuousLinearMap f.toContinuousLinearMap =
        c • φ.compContinuousLinearMap f.toContinuousLinearMap := by
    ext v; simp
  rw [kahlerPowerForm, hsmul, bivectorPow, alternatingFormEquiv_pow_compContinuousLinearMap,
    kahlerPowerForm]
  congr 2
  exact Subtype.ext (by dsimp only [bivectorPow]; rw [hsymm])

/-- The skew-adjoint contraction of the Kähler bivector of an orthogonal almost complex structure
`J` is `J` itself. -/
theorem twoVectorContraction_kahlerForm {J : AlmostComplexStructure V}
    (hJ : ∀ u w, ⟪J u, J w⟫ = ⟪u, w⟫) :
    twoVectorContraction J.kahlerForm = J.toLinearMap :=
  (toLinearMap_eq_twoVectorContraction fun u w ↦ by
    rw [inner_kahlerForm_ιMulti hJ, hJ]).symm

omit [FiniteDimensional ℝ V] in
/-- An almost complex structure admitting an adapted orthonormal basis
`(b₀, J b₀, …, b_{2n-2}, J b_{2n-2})` is automatically orthogonal. -/
theorem inner_apply_apply_of_adapted {J : AlmostComplexStructure V} {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ V)
    (hb : ∀ j : Fin n, b ⟨2 * (j : ℕ) + 1, by omega⟩ = J (b ⟨2 * (j : ℕ), by omega⟩))
    (u w : V) : ⟪J u, J w⟫ = ⟪u, w⟫ := by
  have hJb (i k : Fin (2 * n)) : ⟪J (b i), J (b k)⟫ = ⟪b i, b k⟫ := by
    obtain ⟨⟨a, p⟩, rfl⟩ := (complexRealIndexEquiv n).surjective i
    obtain ⟨⟨c, q⟩, rfl⟩ := (complexRealIndexEquiv n).surjective k
    have h0 (j : Fin n) : complexRealIndexEquiv n (j, 0) = ⟨2 * (j : ℕ), by omega⟩ :=
      Fin.ext (by simp)
    have h1 (j : Fin n) : complexRealIndexEquiv n (j, 1) = ⟨2 * (j : ℕ) + 1, by omega⟩ :=
      Fin.ext (by simp)
    have hJ0 (j : Fin n) : J (b ⟨2 * (j : ℕ), by omega⟩) = b ⟨2 * (j : ℕ) + 1, by omega⟩ :=
      (hb j).symm
    have hJ1 (j : Fin n) : J (b ⟨2 * (j : ℕ) + 1, by omega⟩) = -b ⟨2 * (j : ℕ), by omega⟩ := by
      rw [hb j, J.apply_apply]
    have hb_ite := orthonormal_iff_ite.mp b.orthonormal
    rcases (by fin_cases p <;> simp : p = 0 ∨ p = 1) with rfl | rfl <;>
      rcases (by fin_cases q <;> simp : q = 0 ∨ q = 1) with rfl | rfl
    · rw [h0, h0, hJ0, hJ0, hb_ite, hb_ite]
      by_cases h : a = c <;> simp [h, Fin.ext_iff]
    · rw [h0, h1, hJ0, hJ1, inner_neg_right, hb_ite, hb_ite]
      have hne1 : (⟨2 * (a : ℕ) + 1, by omega⟩ : Fin (2 * n)) ≠ ⟨2 * (c : ℕ), by omega⟩ :=
        fun h ↦ by have := congrArg Fin.val h; dsimp only at this; omega
      have hne2 : (⟨2 * (a : ℕ), by omega⟩ : Fin (2 * n)) ≠ ⟨2 * (c : ℕ) + 1, by omega⟩ :=
        fun h ↦ by have := congrArg Fin.val h; dsimp only at this; omega
      simp [hne1, hne2]
    · rw [h1, h0, hJ1, hJ0, inner_neg_left, hb_ite, hb_ite]
      have hne1 : (⟨2 * (a : ℕ), by omega⟩ : Fin (2 * n)) ≠ ⟨2 * (c : ℕ) + 1, by omega⟩ :=
        fun h ↦ by have := congrArg Fin.val h; dsimp only at this; omega
      have hne2 : (⟨2 * (a : ℕ) + 1, by omega⟩ : Fin (2 * n)) ≠ ⟨2 * (c : ℕ), by omega⟩ :=
        fun h ↦ by have := congrArg Fin.val h; dsimp only at this; omega
      simp [hne1, hne2]
    · rw [h1, h1, hJ1, hJ1, inner_neg_left, inner_neg_right, neg_neg, hb_ite, hb_ite]
      by_cases h : a = c <;> simp [h, Fin.ext_iff]
  conv_lhs => rw [← b.sum_repr' u, ← b.sum_repr' w]
  conv_rhs => rw [← b.sum_repr' u, ← b.sum_repr' w]
  simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    hJb]

/-- In any adapted orthonormal basis `(b₀, J b₀, …, b_{2n-2}, J b_{2n-2})`, the Kähler bivector
decomposes as `∑ j, b_{2j} ∧ b_{2j+1}`. -/
theorem kahlerForm_eq_sum_of_adapted {J : AlmostComplexStructure V} {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ V)
    (hb : ∀ j : Fin n, b ⟨2 * (j : ℕ) + 1, by omega⟩ = J (b ⟨2 * (j : ℕ), by omega⟩)) :
    J.kahlerForm = ∑ j : Fin n,
      ιMulti ℝ 2 ![b ⟨2 * (j : ℕ), by omega⟩, b ⟨2 * (j : ℕ) + 1, by omega⟩] := by
  have hJ := inner_apply_apply_of_adapted b hb
  let b₀ : OrthonormalBasis (Fin n × Fin 2) ℝ V := b.reindex (complexRealIndexEquiv n).symm
  have hb0 (j : Fin n) : b₀ (j, 0) = b ⟨2 * (j : ℕ), by omega⟩ := by
    simp only [b₀, OrthonormalBasis.coe_reindex, Equiv.symm_symm, Function.comp_apply]
    congr 1; exact Fin.ext (by simp)
  have hb1 (j : Fin n) : b₀ (j, 1) = b ⟨2 * (j : ℕ) + 1, by omega⟩ := by
    simp only [b₀, OrthonormalBasis.coe_reindex, Equiv.symm_symm, Function.comp_apply]
    congr 1; exact Fin.ext (by simp)
  have hsum := twoVector_eq_sum_of_skew_normalForm J.kahlerForm b₀ (fun _ ↦ (1 : ℝ))
    (fun j ↦ by
      rw [twoVectorContraction_kahlerForm hJ, one_smul, hb0, hb1, ← hb])
    (fun j ↦ by
      rw [twoVectorContraction_kahlerForm hJ, one_smul, hb0, hb1, hb]
      exact J.apply_apply _)
  simpa only [one_smul, hb0, hb1] using hsum

/-- Pullback of the Kähler bivector `J.kahlerForm` to a subspace `P ≤ V` via the Riesz
identification `alternatingFormEquiv`. -/
private def kahlerSubspacePullback (J : AlmostComplexStructure V) (P : Submodule ℝ V) :
    ⋀[ℝ]^2 P :=
  (alternatingFormEquiv P 2).symm
    ((alternatingFormEquiv V 2 J.kahlerForm).compContinuousLinearMap P.subtypeL)

private theorem inner_twoVectorContraction_kahlerSubspacePullback_eq
    (J : AlmostComplexStructure V) (P : Submodule ℝ V) (x y : P) :
    ⟪twoVectorContraction (kahlerSubspacePullback J P) x, y⟫ =
      (2⁻¹ : ℝ) * (⟪J x.1, y.1⟫ - ⟪J y.1, x.1⟫) := by
  rw [inner_twoVectorContraction_apply, kahlerSubspacePullback,
    inner_alternatingFormEquiv_symm_ιMulti,
    ContinuousAlternatingMap.compContinuousLinearMap_apply, alternatingFormEquiv_apply]
  have hcomp : (P.subtypeL ∘ ![x, y]) = ![x.1, y.1] := by ext i; fin_cases i <;> rfl
  rw [hcomp, inner_kahlerForm_ιMulti_eq]

private theorem inner_twoVectorContraction_kahlerSubspacePullback
    {J : AlmostComplexStructure V} (hJ : ∀ u w, ⟪J u, J w⟫ = ⟪u, w⟫)
    (P : Submodule ℝ V) (x y : P) :
    ⟪twoVectorContraction (kahlerSubspacePullback J P) x, y⟫ = ⟪J x.1, y.1⟫ := by
  rw [inner_twoVectorContraction_kahlerSubspacePullback_eq, inner_apply_left hJ y.1 x.1,
    real_inner_comm y.1 (J x.1)]
  ring

private theorem coe_twoVectorContraction_kahlerSubspacePullback
    {J : AlmostComplexStructure V} (hJ : ∀ u w, ⟪J u, J w⟫ = ⟪u, w⟫)
    (P : Submodule ℝ V) (x : P) :
    (twoVectorContraction (kahlerSubspacePullback J P) x : V) = P.starProjection (J x.1) := by
  refine (Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (twoVectorContraction (kahlerSubspacePullback J P) x).2 fun y hy ↦ ?_).symm
  have hxy := inner_twoVectorContraction_kahlerSubspacePullback hJ P x ⟨y, hy⟩
  rw [inner_sub_left, sub_eq_zero]
  exact hxy.symm

private theorem kahlerPowerForm_comp_subtype (J : AlmostComplexStructure V)
    (P : Submodule ℝ V) {r : ℕ} (vP : Fin (2 * r) → P) :
    J.kahlerPowerForm r (fun i ↦ (vP i : V)) =
      ⟪(r.factorial : ℝ)⁻¹ • bivectorPow (kahlerSubspacePullback J P) r,
        ιMulti ℝ (2 * r) vP⟫ := by
  have hcomp : (P.subtypeL ∘ vP) = fun i ↦ (vP i : V) := rfl
  have heval := DFunLike.congr_fun
    (alternatingFormEquiv_pow_compContinuousLinearMap P.subtypeL J.kahlerForm r) vP
  rw [kahlerPowerForm, ContinuousAlternatingMap.smul_apply, ← hcomp]
  change (r.factorial : ℝ)⁻¹ •
    ((alternatingFormEquiv V (2 * r) (bivectorPow J.kahlerForm r)).compContinuousLinearMap
      P.subtypeL) vP = _
  dsimp only [bivectorPow]
  rw [heval, ← ContinuousAlternatingMap.smul_apply, ← map_smul, alternatingFormEquiv_apply]
  rfl

private theorem bivectorPow_sum_adapted {W : Type*} [AddCommGroup W] [Module ℝ W] {r : ℕ}
    (b : Fin (2 * r) → W) (F : ⋀[ℝ]^2 W)
    (hF : F = ∑ j : Fin r,
      ιMulti ℝ 2 ![b ⟨2 * (j : ℕ), by omega⟩, b ⟨2 * (j : ℕ) + 1, by omega⟩]) :
    (r.factorial : ℝ)⁻¹ • bivectorPow F r = ιMulti ℝ (2 * r) b := by
  apply Subtype.ext
  have hcoe : (F : _root_.ExteriorAlgebra ℝ W) =
      ∑ j : Fin r, (1 : ℝ) • _root_.ExteriorAlgebra.ιMulti ℝ 2
        ![b ⟨2 * (j : ℕ), by omega⟩, b ⟨2 * (j : ℕ) + 1, by omega⟩] := by
    conv_lhs => rw [hF]
    simp
  rw [SetLike.val_smul]
  dsimp only [bivectorPow]
  rw [hcoe, TauCeti.ExteriorAlgebra.pow_sum_smul_ιMulti_two]
  simp only [Finset.prod_const_one, one_smul, ιMulti_apply_coe, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero (R := ℝ).mpr (Nat.factorial_ne_zero r))]

/-- The normalized Kähler power `ωʳ / r!` evaluates to `1` on every `J`-adapted orthonormal
`2r`-frame `(w₀, J w₀, …, w_{2r-2}, J w_{2r-2})`, without requiring `J` to be orthogonal outside
the span of `w`. -/
theorem kahlerPowerForm_apply_of_adapted {J : AlmostComplexStructure V}
    {r : ℕ} {w : Fin (2 * r) → V} (hw : Orthonormal ℝ w)
    (hadapt : ∀ j : Fin r, w ⟨2 * (j : ℕ) + 1, by omega⟩ = J (w ⟨2 * (j : ℕ), by omega⟩)) :
    J.kahlerPowerForm r w = 1 := by
  let P : Submodule ℝ V := Submodule.span ℝ (Set.range w)
  have hP_dim : finrank ℝ P = 2 * r := by simpa using finrank_span_eq_card hw.linearIndependent
  let wP : Fin (2 * r) → P := fun i ↦ ⟨w i, Submodule.subset_span ⟨i, rfl⟩⟩
  have hwP : Orthonormal ℝ wP := hw
  let bP : OrthonormalBasis (Fin (2 * r)) ℝ P :=
    (basisOfLinearIndependentOfCardEqFinrank' wP hwP.linearIndependent
      (by simp [hP_dim])).toOrthonormalBasis
      (by simpa only [coe_basisOfLinearIndependentOfCardEqFinrank'] using hwP)
  have hbP_coe (i : Fin (2 * r)) : (bP i : V) = w i := by simp [bP, wP]
  have hJP : ∀ x ∈ P, J x ∈ P := fun x hx ↦ by
    rw [show x = (⟨x, hx⟩ : P).1 from rfl, ← bP.sum_repr' ⟨x, hx⟩, Submodule.coe_sum, map_sum]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    obtain ⟨⟨j, k⟩, rfl⟩ := (complexRealIndexEquiv r).surjective i
    rw [Submodule.coe_smul, map_smul, hbP_coe]
    refine Submodule.smul_mem _ _ ?_
    rcases (by fin_cases k <;> simp : k = 0 ∨ k = 1) with rfl | rfl
    · have h0 : complexRealIndexEquiv r (j, 0) = ⟨2 * (j : ℕ), by omega⟩ := Fin.ext (by simp)
      rw [h0, ← hadapt j]; exact Submodule.subset_span ⟨_, rfl⟩
    · have h1 : complexRealIndexEquiv r (j, 1) = ⟨2 * (j : ℕ) + 1, by omega⟩ := Fin.ext (by simp)
      rw [h1, hadapt j, J.apply_apply]; exact Submodule.neg_mem _ (Submodule.subset_span ⟨_, rfl⟩)
  let JP : AlmostComplexStructure P :=
    { toLinearMap := J.toLinearMap.restrict hJP
      square_neg := by ext x; exact J.apply_apply x.1 }
  have hJP_orth := inner_apply_apply_of_adapted (J := JP) bP
    (fun j ↦ Subtype.ext (by simpa [JP, hbP_coe] using hadapt j))
  have hFP_eq : kahlerSubspacePullback J P = JP.kahlerForm := by
    refine exteriorPower.ext_inner_ιMulti_two fun x y ↦ ?_
    rw [← inner_twoVectorContraction_apply, inner_twoVectorContraction_kahlerSubspacePullback_eq,
      inner_kahlerForm_ιMulti hJP_orth]
    have hskew : ⟪J y.1, x.1⟫ = -⟪J x.1, y.1⟫ := by
      have := inner_apply_left hJP_orth y x
      simpa [JP, real_inner_comm] using this
    rw [hskew]; change _ = ⟪J x.1, y.1⟫; ring
  have hpow := bivectorPow_sum_adapted bP (kahlerSubspacePullback J P)
    (hFP_eq.trans (kahlerForm_eq_sum_of_adapted bP
      (fun j ↦ Subtype.ext (by simpa [JP, hbP_coe] using hadapt j))))
  have hw_eq : w = fun i ↦ (bP i : V) := funext fun i ↦ (hbP_coe i).symm
  rw [hw_eq, kahlerPowerForm_comp_subtype, hpow, real_inner_self_eq_norm_sq,
    bP.orthonormal.norm_ιMulti, one_pow]

private theorem inner_smul_smul_exteriorPower {W : Type*} [NormedAddCommGroup W]
    [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] {k : ℕ} (a c : ℝ) (x : ⋀[ℝ]^k W) :
    ⟪a • x, c • x⟫ = a * c * ‖x‖ ^ 2 := by
  rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
  ring

private theorem apply_eq_of_norm_starProjection_eq_one {J : AlmostComplexStructure V}
    (hJ : ∀ u w, ⟪J u, J w⟫ = ⟪u, w⟫) {P : Submodule ℝ V} {u w : P}
    (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (hproj : P.starProjection (J u.1) = w.1) :
    w.1 = J u.1 := by
  have hnorm : ‖P.starProjection (J u.1)‖ = ‖J u.1‖ := by
    rw [hproj, Submodule.norm_coe, hw, J.norm_apply hJ, Submodule.norm_coe, hu]
  rw [← hproj]
  exact P.starProjection_eq_self_iff.2 ((P.mem_iff_norm_starProjection _).2 hnorm)

/-- Core normal-form decomposition of `J.kahlerPowerForm r` restricted to the span of an
orthonormal `2r`-frame `v`: yields a companion orthonormal frame `w` of the same span, weights
`0 ≤ μ j ≤ 1`, and a sign `ε ∈ {1, -1}` with `v₁ ∧ ⋯ ∧ v_{2r} = ε • (w₁ ∧ ⋯ ∧ w_{2r})`,
`ωʳ / r! (v) = ε * ∏ j, μ j`, and `μ j = 1 → w_{2j+1} = J w_{2j}`. -/
private theorem exists_normalForm_eval_of_orthonormal {J : AlmostComplexStructure V}
    (hJ : ∀ u w, ⟪J u, J w⟫ = ⟪u, w⟫) {r : ℕ} {v : Fin (2 * r) → V} (hv : Orthonormal ℝ v) :
    ∃ (w : Fin (2 * r) → V) (μ : Fin r → ℝ) (ε : ℝ),
      Orthonormal ℝ w ∧
      (∀ j, 0 ≤ μ j ∧ μ j ≤ 1) ∧
      |ε| = 1 ∧
      ιMulti ℝ (2 * r) v = ε • ιMulti ℝ (2 * r) w ∧
      J.kahlerPowerForm r v = ε * ∏ j, μ j ∧
      (∀ j : Fin r, μ j = 1 →
        w ⟨2 * (j : ℕ) + 1, by omega⟩ = J (w ⟨2 * (j : ℕ), by omega⟩)) := by
  let P : Submodule ℝ V := Submodule.span ℝ (Set.range v)
  have hP_dim : finrank ℝ P = 2 * r := by simpa using finrank_span_eq_card hv.linearIndependent
  let vP : Fin (2 * r) → P := fun i ↦ ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩
  obtain ⟨b, μ, hμ0, hcontr0, _, _, hpow⟩ :=
    exists_orthonormalBasis_twoVector_normalForm hP_dim (kahlerSubspacePullback J P)
  have hproj (x : P) := coe_twoVectorContraction_kahlerSubspacePullback hJ P x
  have hμ1 (j : Fin r) : μ j ≤ 1 := by
    have hnorm := congrArg norm (hcontr0 j)
    rw [norm_smul, Real.norm_of_nonneg (hμ0 j), b.orthonormal.1, mul_one, ← Submodule.norm_coe,
      hproj] at hnorm
    calc μ j = ‖P.starProjection (J (b ⟨2 * (j : ℕ), by omega⟩ : V))‖ := hnorm.symm
      _ ≤ ‖J (b ⟨2 * (j : ℕ), by omega⟩ : V)‖ := P.norm_starProjection_apply_le _
      _ = 1 := by rw [J.norm_apply hJ, Submodule.norm_coe, b.orthonormal.1]
  set ε : ℝ := b.toBasis.det vP
  have hdetP : ιMulti ℝ (2 * r) vP = ε • ιMulti ℝ (2 * r) b :=
    b.toBasis.exteriorPower_ιMulti_eq_det_smul vP
  have hw : Orthonormal ℝ (fun i ↦ (b i : V)) := b.orthonormal.comp_linearIsometry P.subtypeₗᵢ
  have hι : ιMulti ℝ (2 * r) v = ε • ιMulti ℝ (2 * r) (fun i ↦ (b i : V)) := by
    simpa only [map_smul, exteriorPower.map_apply_ιMulti, Function.comp_def,
      Submodule.coe_subtype] using congrArg (exteriorPower.map (2 * r) P.subtype) hdetP
  have hε : |ε| = 1 := by
    have hn := congrArg norm hι
    rw [hv.norm_ιMulti, norm_smul, Real.norm_eq_abs, hw.norm_ιMulti, mul_one] at hn
    exact hn.symm
  refine ⟨fun i ↦ (b i : V), μ, ε, hw, fun j ↦ ⟨hμ0 j, hμ1 j⟩, hε, hι, ?_, fun j hμj ↦ ?_⟩
  · change J.kahlerPowerForm r (fun i ↦ (vP i : V)) = _
    rw [kahlerPowerForm_comp_subtype, bivectorPow, hpow, hdetP, inner_smul_smul_exteriorPower,
      b.orthonormal.norm_ιMulti]
    ring
  · exact apply_eq_of_norm_starProjection_eq_one hJ (b.orthonormal.1 _) (b.orthonormal.1 _)
      (by simpa [hproj, hμj] using congrArg Subtype.val (hcontr0 j))

/-- **The Wirtinger comass bound** for an orthogonal almost complex structure: `‖ωʳ / r!‖ ≤ 1` in
every degree `r` (including degrees exceeding `finrank ℝ V`). -/
theorem norm_kahlerPowerForm_le {J : AlmostComplexStructure V}
    (hJ : ∀ u w, ⟪J u, J w⟫ = ⟪u, w⟫) (r : ℕ) :
    ‖J.kahlerPowerForm r‖ ≤ 1 := by
  refine (ContinuousAlternatingMap.opNorm_le_iff_le_orthonormal zero_le_one).2 fun v hv ↦ ?_
  obtain ⟨_, μ, ε, _, hμ, hε, _, heval, _⟩ := exists_normalForm_eval_of_orthonormal hJ hv
  rw [heval, Real.norm_eq_abs, abs_mul, hε, one_mul,
    abs_of_nonneg (Finset.prod_nonneg fun j _ ↦ (hμ j).1)]
  exact Finset.prod_le_one₀ (fun j _ ↦ (hμ j).1) (fun j _ ↦ (hμ j).2)

/-- **The Wirtinger inequality in every degree** for an orthogonal almost complex structure: when
`2 * r ≤ finrank ℝ V`, the normalized Kähler power `ωʳ / r!` has comass equal to one. -/
theorem norm_kahlerPowerForm {J : AlmostComplexStructure V}
    (hJ : ∀ u w, ⟪J u, J w⟫ = ⟪u, w⟫) {r : ℕ} (hr : 2 * r ≤ finrank ℝ V) :
    ‖J.kahlerPowerForm r‖ = 1 := by
  obtain ⟨n, hn⟩ := J.even_finrank_real
  have hdim : finrank ℝ V = 2 * n := by omega
  obtain ⟨b, hb⟩ := J.exists_adapted_orthonormalBasis (J.norm_apply hJ) n hdim
  let ι : Fin (2 * r) → Fin (2 * n) := fun i ↦ ⟨(i : ℕ), by have := i.isLt; omega⟩
  let w : Fin (2 * r) → V := b ∘ ι
  have hw : Orthonormal ℝ w :=
    b.orthonormal.comp ι (fun i j hij ↦ Fin.ext (by simpa [ι] using congrArg Fin.val hij))
  have hadapt (j : Fin r) : w ⟨2 * (j : ℕ) + 1, by omega⟩ = J (w ⟨2 * (j : ℕ), by omega⟩) := by
    simpa [w, ι] using hb ⟨(j : ℕ), by omega⟩
  have hcal : IsCalibratedFrame (J.kahlerPowerForm r) w :=
    isCalibratedFrame_iff.2 ⟨hw, kahlerPowerForm_apply_of_adapted hw hadapt⟩
  exact hcal.norm_eq_one (norm_kahlerPowerForm_le hJ r)

/-- **Equality case of the Wirtinger inequality** for an orthogonal almost complex structure: a
`2r`-frame `v` is calibrated by `ωʳ / r!` precisely when `v` is real-orthonormal and shares its
exterior product with a `J`-adapted orthonormal frame `(w₀, J w₀, …, w_{2r-2}, J w_{2r-2})`. -/
theorem isCalibratedFrame_kahlerPowerForm_iff {J : AlmostComplexStructure V}
    (hJ : ∀ u w, ⟪J u, J w⟫ = ⟪u, w⟫) {r : ℕ} (v : Fin (2 * r) → V) :
    IsCalibratedFrame (J.kahlerPowerForm r) v ↔
      Orthonormal ℝ v ∧ ∃ w : Fin (2 * r) → V, Orthonormal ℝ w ∧
        (∀ j : Fin r, w ⟨2 * (j : ℕ) + 1, by omega⟩ = J (w ⟨2 * (j : ℕ), by omega⟩)) ∧
        ιMulti ℝ (2 * r) v = ιMulti ℝ (2 * r) w := by
  constructor
  · rw [isCalibratedFrame_iff]
    rintro ⟨hv, hval⟩
    obtain ⟨w, μ, ε, hw, hμ, hε, hι, heval, hμ_eq⟩ := exists_normalForm_eval_of_orthonormal hJ hv
    have hprod_nonneg : 0 ≤ ∏ j, μ j := Finset.prod_nonneg fun j _ ↦ (hμ j).1
    have hε1 : ε = 1 := by
      rcases (abs_eq zero_le_one).mp hε with h1 | hneg
      · exact h1
      · rw [heval, hneg, neg_one_mul] at hval
        linarith
    have hprod1 : ∏ j, μ j = 1 := by rw [hε1, one_mul] at heval; linarith
    have hall1 : ∀ j, μ j = 1 := fun j ↦ by
      by_contra hne
      have hlt : μ j < 1 := lt_of_le_of_ne (hμ j).2 hne
      have hrest : ∏ k ∈ Finset.univ.erase j, μ k ≤ 1 :=
        Finset.prod_le_one₀ (fun k _ ↦ (hμ k).1) (fun k _ ↦ (hμ k).2)
      have hrest0 : 0 ≤ ∏ k ∈ Finset.univ.erase j, μ k :=
        Finset.prod_nonneg fun k _ ↦ (hμ k).1
      rw [← Finset.mul_prod_erase Finset.univ μ (Finset.mem_univ j)] at hprod1
      nlinarith [(hμ j).1]
    exact ⟨hv, w, hw, fun j ↦ hμ_eq j (hall1 j), by simpa [hε1] using hι⟩
  · rintro ⟨hv, w, hw, hadapt, hι⟩
    exact (isCalibratedFrame_iff_of_ιMulti_eq (J.kahlerPowerForm r) hv hw hι).2
      (isCalibratedFrame_iff.2 ⟨hw, kahlerPowerForm_apply_of_adapted hw hadapt⟩)

/-- Lifting an order embedding `Fin r ↪o Fin n` to consecutive pairs `Fin (2 * r) ↪o Fin (2 * n)`
by `i ↦ 2 * e (i / 2) + i % 2`. -/
private def doubleOrderEmb {n r : ℕ} (e : Fin r ↪o Fin n) : Fin (2 * r) ↪o Fin (2 * n) :=
  OrderEmbedding.ofStrictMono
    (fun i ↦ ⟨2 * (e ⟨(i : ℕ) / 2, by omega⟩ : ℕ) + (i : ℕ) % 2, by omega⟩)
    (fun i j hij ↦ by
      change 2 * (e ⟨(i : ℕ) / 2, by omega⟩ : ℕ) + (i : ℕ) % 2 <
        2 * (e ⟨(j : ℕ) / 2, by omega⟩ : ℕ) + (j : ℕ) % 2
      have hdiv : (i : ℕ) / 2 ≤ (j : ℕ) / 2 := Nat.div_le_div_right (le_of_lt hij)
      rcases hdiv.eq_or_lt with heq | hlt
      · have hfin : (⟨(i : ℕ) / 2, by omega⟩ : Fin r) = ⟨(j : ℕ) / 2, by omega⟩ := Fin.ext heq
        rw [hfin]
        omega
      · have hlt' : (e ⟨(i : ℕ) / 2, by omega⟩ : ℕ) < (e ⟨(j : ℕ) / 2, by omega⟩ : ℕ) :=
          e.strictMono (by exact hlt)
        omega)

private theorem doubleOrderEmb_even {n r : ℕ} (e : Fin r ↪o Fin n) (j : Fin r) :
    doubleOrderEmb e ⟨2 * (j : ℕ), by omega⟩ = ⟨2 * (e j : ℕ), by omega⟩ := by
  apply Fin.ext
  change 2 * (e ⟨(2 * (j : ℕ)) / 2, by omega⟩ : ℕ) + (2 * (j : ℕ)) % 2 = 2 * (e j : ℕ)
  have h1 : (⟨(2 * (j : ℕ)) / 2, by omega⟩ : Fin r) = j :=
    Fin.ext (show (2 * (j : ℕ)) / 2 = (j : ℕ) by omega)
  rw [h1]
  omega

private theorem doubleOrderEmb_odd {n r : ℕ} (e : Fin r ↪o Fin n) (j : Fin r) :
    doubleOrderEmb e ⟨2 * (j : ℕ) + 1, by omega⟩ = ⟨2 * (e j : ℕ) + 1, by omega⟩ := by
  apply Fin.ext
  change 2 * (e ⟨(2 * (j : ℕ) + 1) / 2, by omega⟩ : ℕ) + (2 * (j : ℕ) + 1) % 2 =
    2 * (e j : ℕ) + 1
  have h1 : (⟨(2 * (j : ℕ) + 1) / 2, by omega⟩ : Fin r) = j :=
    Fin.ext (show (2 * (j : ℕ) + 1) / 2 = (j : ℕ) by omega)
  rw [h1]
  omega

private theorem doubleOrderEmb_injective {n r : ℕ} :
    Function.Injective (doubleOrderEmb (n := n) (r := r)) := by
  intro e₁ e₂ h
  ext j
  have hj := congrArg (fun f : Fin (2 * r) ↪o Fin (2 * n) ↦ (f ⟨2 * (j : ℕ), by omega⟩ : ℕ)) h
  simp only [doubleOrderEmb_even] at hj
  omega

private theorem noncommProd_adapted_eq_exteriorPowerBasis {n r : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ V) (s : Set.powersetCard (Fin n) r)
    (hcs : (s.1 : Set (Fin n)).Pairwise (Function.onFun Commute fun k : Fin n ↦
      _root_.ExteriorAlgebra.ιMulti ℝ 2
        ![b ⟨2 * (k : ℕ), by omega⟩, b ⟨2 * (k : ℕ) + 1, by omega⟩])) :
    s.1.noncommProd (fun k : Fin n ↦
      _root_.ExteriorAlgebra.ιMulti ℝ 2
        ![b ⟨2 * (k : ℕ), by omega⟩, b ⟨2 * (k : ℕ) + 1, by omega⟩]) hcs =
      (b.exteriorPower (2 * r)
        (Set.powersetCard.ofFinEmbEquiv (doubleOrderEmb (Set.powersetCard.ofFinEmbEquiv.symm s))) :
        _root_.ExteriorAlgebra ℝ V) := by
  let x : Fin n → _root_.ExteriorAlgebra ℝ V := fun k ↦
    _root_.ExteriorAlgebra.ιMulti ℝ 2 ![b ⟨2 * (k : ℕ), by omega⟩, b ⟨2 * (k : ℕ) + 1, by omega⟩]
  let e : Fin r ↪o Fin n := Set.powersetCard.ofFinEmbEquiv.symm s
  have hB_coe : (b.exteriorPower (2 * r) (Set.powersetCard.ofFinEmbEquiv (doubleOrderEmb e)) :
      _root_.ExteriorAlgebra ℝ V) =
      _root_.ExteriorAlgebra.ιMulti ℝ (2 * r) (b ∘ doubleOrderEmb e) := by
    have hBs : b.exteriorPower (2 * r) (Set.powersetCard.ofFinEmbEquiv (doubleOrderEmb e)) =
        ιMulti ℝ (2 * r) (b ∘ Set.powersetCard.ofFinEmbEquiv.symm
          (Set.powersetCard.ofFinEmbEquiv (doubleOrderEmb e))) := by
      rw [← OrthonormalBasis.coe_toBasis, OrthonormalBasis.toBasis_exteriorPower, basis_apply,
        ιMulti_family, OrthonormalBasis.coe_toBasis]
    rw [hBs, ιMulti_apply_coe, Equiv.symm_apply_apply]
  have hs_eq : s.1 = ((List.finRange r).map e).toFinset := by
    ext k
    simp only [List.mem_toFinset, List.mem_map, List.mem_finRange, true_and]
    exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s k).symm
  have hnodup : ((List.finRange r).map e).Nodup := (List.nodup_finRange r).map e.injective
  have hprod := (Finset.noncommProd_congr hs_eq (fun _ _ ↦ rfl) hcs).trans
    (Finset.noncommProd_toFinset _ _ _ hnodup)
  rw [hprod, List.map_map, hB_coe]
  have hcomm_e : ((Finset.univ : Finset (Fin r)) : Set (Fin r)).Pairwise
      (Function.onFun Commute fun j : Fin r ↦ (1 : ℝ) • _root_.ExteriorAlgebra.ιMulti ℝ 2
        ![(b ∘ doubleOrderEmb e) ⟨2 * (j : ℕ), by omega⟩,
          (b ∘ doubleOrderEmb e) ⟨2 * (j : ℕ) + 1, by omega⟩]) := fun _ _ _ _ _ ↦
    TauCeti.ExteriorAlgebra.commute_smul_ιMulti_two _ _ _ _ _ _
  have hnat := TauCeti.ExteriorAlgebra.noncommProd_univ_smul_ιMulti_two (fun _ : Fin r ↦ (1 : ℝ))
    (b ∘ doubleOrderEmb e) hcomm_e
  have huniv : (Finset.univ : Finset (Fin r)) = (List.finRange r).toFinset := by ext j; simp
  have hnat' := ((Finset.noncommProd_congr huniv (fun _ _ ↦ rfl) hcomm_e).trans
    (Finset.noncommProd_toFinset _ _ _ (List.nodup_finRange r))).symm.trans hnat
  simpa only [x, Function.comp_def, doubleOrderEmb_even, doubleOrderEmb_odd, one_smul,
    Finset.prod_const_one] using hnat'

private theorem kahlerPowerForm_symm_eq_sum_adapted {J : AlmostComplexStructure V} {n : ℕ}
    (b : OrthonormalBasis (Fin (2 * n)) ℝ V)
    (hb : ∀ j : Fin n, b ⟨2 * (j : ℕ) + 1, by omega⟩ = J (b ⟨2 * (j : ℕ), by omega⟩)) (r : ℕ) :
    (alternatingFormEquiv V (2 * r)).symm (J.kahlerPowerForm r) =
      ∑ s : Set.powersetCard (Fin n) r, b.exteriorPower (2 * r)
        (Set.powersetCard.ofFinEmbEquiv
          (doubleOrderEmb (Set.powersetCard.ofFinEmbEquiv.symm s))) := by
  let x : Fin n → _root_.ExteriorAlgebra ℝ V := fun k ↦
    _root_.ExteriorAlgebra.ιMulti ℝ 2 ![b ⟨2 * (k : ℕ), by omega⟩, b ⟨2 * (k : ℕ) + 1, by omega⟩]
  have hcoe : (J.kahlerForm : _root_.ExteriorAlgebra ℝ V) = ∑ k : Fin n, x k := by
    rw [kahlerForm_eq_sum_of_adapted b hb]; simp [x]
  have hcomm : Pairwise (Function.onFun Commute x) := fun _ _ _ ↦ by
    simpa [x] using TauCeti.ExteriorAlgebra.commute_smul_ιMulti_two (1 : ℝ) 1
      (b ⟨2 * _, _⟩) (b ⟨2 * _ + 1, _⟩) (b ⟨2 * _, _⟩) (b ⟨2 * _ + 1, _⟩)
  have hsq : ∀ k ∈ (Finset.univ : Finset (Fin n)), x k * x k = 0 := fun k _ ↦ by
    simpa [x] using TauCeti.ExteriorAlgebra.smul_ιMulti_two_mul_self (1 : ℝ)
      (b ⟨2 * (k : ℕ), by omega⟩) (b ⟨2 * (k : ℕ) + 1, by omega⟩)
  rw [kahlerPowerForm, map_smul, LinearEquiv.symm_apply_apply]
  apply Subtype.ext
  rw [SetLike.val_smul, Submodule.coe_sum]
  dsimp only [bivectorPow]
  rw [hcoe, Finset.sum_pow_of_pairwise_commute_of_mul_self_eq_zero Finset.univ x hcomm hsq r,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ (Nat.cast_ne_zero (R := ℝ).mpr (Nat.factorial_ne_zero r)), one_smul,
    ← Finset.sum_coe_sort ((Finset.univ : Finset (Fin n)).powersetCard r)]
  refine Finset.sum_bij
    (fun (s : ((Finset.univ : Finset (Fin n)).powersetCard r)) _ ↦
      Set.powersetCard.ofCard (Finset.mem_powersetCard.mp s.2).2)
    (fun _ _ ↦ Finset.mem_univ _)
    (fun s₁ _ s₂ _ h ↦ Subtype.ext (by
      simpa [Set.powersetCard.ofCard] using congrArg Subtype.val h))
    (fun s _ ↦
      ⟨⟨s.1, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, Set.powersetCard.card_eq s⟩⟩,
        Finset.mem_univ _, rfl⟩)
    (fun s _ ↦ noncommProd_adapted_eq_exteriorPowerBasis b
      (Set.powersetCard.ofCard (Finset.mem_powersetCard.mp s.2).2) _)

/-- **Hilbert norm of the normalized Kähler power**: for an orthogonal almost complex structure `J`
on a `2n`-dimensional real inner product space, the Hilbert norm `√⟨ωʳ / r!, ωʳ / r!⟩` equals
`√(n choose r)`. -/
theorem sqrt_alternatingFormInner_kahlerPowerForm {J : AlmostComplexStructure V}
    (hJ : ∀ u w, ⟪J u, J w⟫ = ⟪u, w⟫) (r : ℕ) :
    √(alternatingFormInner V (2 * r) (J.kahlerPowerForm r) (J.kahlerPowerForm r)) =
      √((finrank ℝ V / 2).choose r) := by
  obtain ⟨n, hn⟩ := J.even_finrank_real
  have hdim : finrank ℝ V = 2 * n := by omega
  have hn_eq : finrank ℝ V / 2 = n := by omega
  obtain ⟨b, hb⟩ := J.exists_adapted_orthonormalBasis (J.norm_apply hJ) n hdim
  have hB_ite := orthonormal_iff_ite.mp (b.exteriorPower (2 * r)).orthonormal
  have hinj (s t : Set.powersetCard (Fin n) r) :
      Set.powersetCard.ofFinEmbEquiv (doubleOrderEmb (Set.powersetCard.ofFinEmbEquiv.symm s)) =
        Set.powersetCard.ofFinEmbEquiv (doubleOrderEmb (Set.powersetCard.ofFinEmbEquiv.symm t)) ↔
        s = t := by
    simp [doubleOrderEmb_injective.eq_iff]
  rw [ContinuousAlternatingMap.sqrt_alternatingFormInner_self,
    kahlerPowerForm_symm_eq_sum_adapted b hb r, hn_eq, norm_eq_sqrt_real_inner]
  congr 1
  rw [sum_inner]
  simp_rw [inner_sum, hB_ite, hinj]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]
  rw [← Nat.card_eq_fintype_card, Set.powersetCard.card, Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-- **Non-orthonormal degree-two Wirtinger equality** for an orthogonal almost complex structure:
for linearly independent `v` and `w`, `⟪J v, w⟫ = ‖v ∧ w‖` exactly when `w = a • v + b • J v`
with `0 < b`. -/
theorem inner_apply_eq_norm_ιMulti_iff {J : AlmostComplexStructure V}
    (hJ : ∀ u w, ⟪J u, J w⟫ = ⟪u, w⟫) {v w : V} (h : LinearIndependent ℝ ![v, w]) :
    ⟪J v, w⟫ = ‖ιMulti ℝ 2 ![v, w]‖ ↔ ∃ a b : ℝ, 0 < b ∧ w = a • v + b • J v := by
  let ω := J.symplecticForm hJ
  have hinv : ω.Invariant J := (ω.invariant_iff J).2 fun u z ↦ by
    simp only [ω, symplecticForm_apply, J.apply_apply, inner_neg_left, inner_apply_left hJ]
  have htame : ω.Tames J := fun u hu ↦ by
    simpa [ω, symplecticForm_apply, hJ] using real_inner_self_pos.mpr hu
  have hcompat : ω.Compatible J := SymplecticForm.Compatible.of_tames hinv htame
  have hbil (u z : V) : ω.associatedBilinForm J u z = ⟪u, z⟫ := by
    simp [ω, SymplecticForm.associatedBilinForm_apply, symplecticForm_apply, hJ]
  have hwedge : ω.wedgeNorm J v w = ‖ιMulti ℝ 2 ![v, w]‖ := by
    rw [SymplecticForm.wedgeNorm_def, hbil, hbil, hbil, ← Real.sqrt_sq (norm_nonneg _),
      norm_ιMulti_sq]
    congr 1
    simp [Matrix.gram, Matrix.det_fin_two, sq, real_inner_comm]
  rw [← J.symplecticForm_apply hJ, ← hwedge]
  exact hcompat.apply_eq_wedgeNorm_iff_of_linearIndependent h

end KahlerPower

end AlmostComplexStructure

/-! ### Hermitian vector spaces: Kähler form and Wirtinger inequality -/

section DegreeTwo

variable (E : Type*) [SeminormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℂ E]
  [IsScalarTower ℝ ℂ E]

/-- The **Kähler two-form** `ω(v, w) = Im ⟪v, w⟫_ℂ` on a complex inner product space, as a real
continuous alternating two-form. For `E = ℂ` with the standard Hermitian product conjugate-linear
in the first slot, `ω(1, i) = 1`. -/
def kahlerForm : E [⋀^Fin 2]→L[ℝ] ℝ where
  toFun v := (inner ℂ (v 0) (v 1)).im
  map_update_add' m i x y := by fin_cases i <;> simp [inner_add_left, inner_add_right]
  map_update_smul' m i c x := by
    have hsmul : c • x = (c : ℂ) • x := by rw [← Complex.coe_algebraMap, algebraMap_smul]
    fin_cases i
    · simp only [Fin.isValue, Fin.zero_eta, Function.update_self, ne_eq, one_ne_zero,
        not_false_eq_true, Function.update_of_ne, smul_eq_mul]
      rw [hsmul, inner_smul_left]
      simp
    · simp only [Fin.isValue, Fin.mk_one, Function.update_self, ne_eq, zero_ne_one,
        not_false_eq_true, Function.update_of_ne, smul_eq_mul]
      rw [hsmul, inner_smul_right]
      simp
  cont := Complex.continuous_im.comp ((continuous_apply 0).inner (continuous_apply 1))
  map_eq_zero_of_eq' v i j hv hij := by
    fin_cases i <;> fin_cases j <;> simp_all [← Complex.ofReal_pow]

variable {E}

/-- Evaluation formula for `TauCeti.kahlerForm`. -/
@[simp]
theorem kahlerForm_apply (v : Fin 2 → E) :
    kahlerForm E v = (inner ℂ (v 0) (v 1)).im :=
  (rfl)

/-- The Kähler form has comass at most one on every complex inner product space. -/
theorem norm_kahlerForm_le : ‖kahlerForm E‖ ≤ 1 := by
  refine (kahlerForm E).opNorm_le_bound zero_le_one fun v ↦ ?_
  rw [kahlerForm_apply, Real.norm_eq_abs, one_mul, Fin.prod_univ_two]
  exact (Complex.abs_im_le_norm _).trans (norm_inner_le_norm (v 0) (v 1))

/-- Naturality of `TauCeti.kahlerForm` under any complex linear isometry `f : E →ₗᵢ[ℂ] F`. -/
theorem kahlerForm_comp_linearIsometry {F : Type*} [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    [InnerProductSpace ℂ F] [IsScalarTower ℝ ℂ F] (f : E →ₗᵢ[ℂ] F) :
    (kahlerForm F).compContinuousLinearMap (f.toContinuousLinearMap.restrictScalars ℝ) =
      kahlerForm E := by
  ext v
  simp [kahlerForm_apply, f.inner_map_map]

end DegreeTwo

section DegreeTwoNormed

/-- **Wirtinger inequality in degree two**: on every nontrivial complex inner product space (no
finite-dimensionality required), the Kähler form has comass one. -/
theorem norm_kahlerForm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [InnerProductSpace ℂ E] [IsScalarTower ℝ ℂ E] [Nontrivial E] :
    ‖kahlerForm E‖ = 1 := by
  refine le_antisymm norm_kahlerForm_le ?_
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  set u : E := ‖x‖⁻¹ • x
  have hu : ‖u‖ = 1 := norm_smul_inv_norm hx
  have hval : kahlerForm E ![u, Complex.I • u] = 1 := by
    simp [kahlerForm_apply, inner_smul_right, hu]
  simpa [hval, Fin.prod_univ_two, norm_smul, hu] using (kahlerForm E).le_opNorm ![u, Complex.I • u]

end DegreeTwoNormed

section DegreeTwoInner

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E] [InnerProductSpace ℂ E]
  [IsScalarTower ℝ ℂ E]

/-- In terms of the compatible real inner product, `ω(v, w) = ⟪i • v, w⟫_ℝ`. -/
theorem kahlerForm_apply_eq_inner (v w : E) :
    kahlerForm E ![v, w] = ⟪Complex.I • v, w⟫_ℝ := by
  rw [kahlerForm_apply, inner_real_eq_re_inner (𝕜 := ℂ), inner_smul_left]
  simp

/-- Multiplication by `i` is orthogonal for the compatible real inner product. -/
theorem ofComplexModule_orthogonal (v w : E) :
    ⟪AlmostComplexStructure.ofComplexModule E v, AlmostComplexStructure.ofComplexModule E w⟫_ℝ =
      ⟪v, w⟫_ℝ := by
  simp [inner_real_eq_re_inner (𝕜 := ℂ), inner_smul_left, inner_smul_right]

omit [IsScalarTower ℝ ℂ E] in
/-- The underlying real family `(u₀, i • u₀, …)` of a complex-orthonormal family is
real-orthonormal. -/
theorem orthonormal_complexToRealFamily {r : ℕ} {u : Fin r → E} (hu : Orthonormal ℂ u) :
    Orthonormal ℝ (complexToRealFamily u) := by
  rw [orthonormal_iff_ite]
  intro i j
  obtain ⟨⟨a, p⟩, rfl⟩ := (complexRealIndexEquiv r).surjective i
  obtain ⟨⟨b, q⟩, rfl⟩ := (complexRealIndexEquiv r).surjective j
  simp only [complexToRealFamily_complexRealIndexEquiv, inner_real_eq_re_inner (𝕜 := ℂ),
    inner_smul_left, inner_smul_right, (complexRealIndexEquiv r).injective.eq_iff, Prod.mk.injEq]
  rcases eq_or_ne a b with rfl | hab
  · fin_cases p <;> fin_cases q <;> simp [hu.1 a]
  · simp [hab, hu.2 hab]

end DegreeTwoInner

section DegreeTwoEquality

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [InnerProductSpace ℂ E]
  [IsScalarTower ℝ ℂ E]

/-- **Equality case of degree-two Wirtinger** on any Hermitian inner product space (no
finite-dimensionality required): an ordered pair `(v₀, v₁)` is calibrated by `kahlerForm E`
precisely when `‖v₀‖ = 1` and `v₁ = i • v₀`. -/
theorem isCalibratedFrame_kahlerForm_iff (v : Fin 2 → E) :
    IsCalibratedFrame (kahlerForm E) v ↔ ‖v 0‖ = 1 ∧ v 1 = Complex.I • v 0 := by
  rw [isCalibratedFrame_iff]
  constructor
  · rintro ⟨hv, hval⟩
    refine ⟨hv.1 0, ?_⟩
    have hre : (inner ℂ (v 0) (v 1)).re = 0 := by
      rw [← RCLike.re_to_complex, ← inner_real_eq_re_inner (𝕜 := ℂ)]
      exact hv.2 (by decide : (0 : Fin 2) ≠ 1)
    have hinner : inner ℂ (v 0) (v 1) = Complex.I :=
      Complex.ext hre (by simpa [kahlerForm_apply] using hval)
    have hsq : ‖v 1 - Complex.I • v 0‖ ^ 2 = 0 := by
      rw [norm_sub_sq (𝕜 := ℂ), norm_smul, Complex.norm_I, one_mul, hv.1 0, hv.1 1,
        inner_smul_right, ← inner_conj_symm (v 1) (v 0), hinner]
      simp
      norm_num
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))
  · rintro ⟨hv0, hv1⟩
    refine ⟨?_, ?_⟩
    · rw [orthonormal_iff_ite]
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [inner_real_eq_re_inner (𝕜 := ℂ), hv1, inner_smul_left, inner_smul_right,
          inner_self_eq_norm_sq_to_K, norm_smul, hv0]
    · simp [kahlerForm_apply, hv1, inner_smul_right, hv0]

/-- **Non-orthonormal degree-two Wirtinger equality**: for linearly independent `v` and `w` in a
finite-dimensional Hermitian vector space, `ω(v, w) = ‖v ∧ w‖` exactly when
`w = a • v + b • (i • v)` with `0 < b`. -/
theorem kahlerForm_apply_eq_norm_ιMulti_iff [FiniteDimensional ℝ E] {v w : E}
    (h : LinearIndependent ℝ ![v, w]) :
    kahlerForm E ![v, w] = ‖ιMulti ℝ 2 ![v, w]‖ ↔
      ∃ a b : ℝ, 0 < b ∧ w = a • v + b • (Complex.I • v) := by
  rw [kahlerForm_apply_eq_inner]
  simpa only [AlmostComplexStructure.ofComplexModule_apply] using
    AlmostComplexStructure.inner_apply_eq_norm_ιMulti_iff
      (J := AlmostComplexStructure.ofComplexModule E) ofComplexModule_orthogonal h

end DegreeTwoEquality

/-! ### All-degree Kähler powers and Wirtinger inequality on Hermitian spaces -/

section EveryDegree

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [InnerProductSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [InnerProductSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [FiniteDimensional ℝ F]

/-- The Riesz dual of `(AlmostComplexStructure.ofComplexModule E).kahlerForm` is `kahlerForm E`. -/
@[simp]
theorem alternatingFormEquiv_ofComplexModule_kahlerForm :
    alternatingFormEquiv E 2 (AlmostComplexStructure.ofComplexModule E).kahlerForm =
      kahlerForm E := by
  ext v
  have hv : v = ![v 0, v 1] := by ext i; fin_cases i <;> rfl
  rw [hv, alternatingFormEquiv_apply,
    AlmostComplexStructure.inner_kahlerForm_ιMulti ofComplexModule_orthogonal,
    AlmostComplexStructure.ofComplexModule_apply, kahlerForm_apply_eq_inner]

/-- In any complex orthonormal basis `b` of `E`, the Kähler bivector is
`∑ j, b j ∧ (i • b j)`. -/
theorem ofComplexModule_kahlerForm_eq_sum {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ E) :
    (AlmostComplexStructure.ofComplexModule E).kahlerForm =
      ∑ j : ι, ιMulti ℝ 2 ![b j, Complex.I • b j] := by
  refine exteriorPower.ext_inner_ιMulti_two fun u w ↦ ?_
  rw [AlmostComplexStructure.inner_kahlerForm_ιMulti ofComplexModule_orthogonal,
    AlmostComplexStructure.ofComplexModule_apply, ← kahlerForm_apply_eq_inner, kahlerForm_apply]
  dsimp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [← b.sum_inner_mul_inner u w, Complex.im_sum, sum_inner]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [exteriorPower.inner_ιMulti_two, inner_real_eq_re_inner (𝕜 := ℂ),
    inner_real_eq_re_inner (𝕜 := ℂ), inner_real_eq_re_inner (𝕜 := ℂ),
    inner_real_eq_re_inner (𝕜 := ℂ), inner_smul_left, inner_smul_left,
    ← inner_conj_symm (b j) u]
  simp only [RCLike.re_to_complex, Complex.conj_I, neg_mul, Complex.I_mul, Complex.neg_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

variable (E) in
/-- The normalized `r`-th Kähler power `ωʳ / r!` on a finite-dimensional Hermitian vector space
`E`, as a real continuous alternating `2r`-form. -/
def kahlerPowerForm (r : ℕ) : E [⋀^Fin (2 * r)]→L[ℝ] ℝ :=
  (AlmostComplexStructure.ofComplexModule E).kahlerPowerForm r

/-- In degree zero, `ω⁰ / 0!` is the constant form `1`. -/
@[simp]
theorem kahlerPowerForm_zero :
    kahlerPowerForm E 0 = ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) 1 :=
  AlmostComplexStructure.kahlerPowerForm_zero _

/-- In degree two (`r = 1`), `ω¹ / 1!` is `TauCeti.kahlerForm E`. -/
@[simp]
theorem kahlerPowerForm_one : kahlerPowerForm E 1 = kahlerForm E := by
  rw [kahlerPowerForm, AlmostComplexStructure.kahlerPowerForm_one,
    alternatingFormEquiv_ofComplexModule_kahlerForm]

/-- Wedge recurrence for normalized Kähler powers on a Hermitian vector space:
`ω^(r+1) / (r+1)! = (r + 1)⁻¹ • (ωʳ / r!) ∧ ω`. -/
theorem kahlerPowerForm_succ (r : ℕ) :
    kahlerPowerForm E (r + 1) =
      ((r + 1 : ℕ) : ℝ)⁻¹ • (kahlerPowerForm E r).wedge (kahlerForm E) := by
  rw [kahlerPowerForm, AlmostComplexStructure.kahlerPowerForm_succ,
    alternatingFormEquiv_ofComplexModule_kahlerForm, kahlerPowerForm]

/-- Normalized Kähler powers vanish above the complex dimension of `E`. -/
theorem kahlerPowerForm_eq_zero_of_finrank_lt {r : ℕ} (hr : finrank ℂ E < r) :
    kahlerPowerForm E r = 0 := by
  have : FiniteDimensional ℂ E := Module.Finite.of_restrictScalars_finite ℝ ℂ E
  refine AlmostComplexStructure.kahlerPowerForm_eq_zero_of_finrank_lt _ ?_
  rw [finrank_real_eq_two_mul_finrank_complex]
  omega

/-- Naturality of `TauCeti.kahlerPowerForm` under every complex linear isometry `f : E →ₗᵢ[ℂ] F`
(in particular, unitary invariance when `f : E ≃ₗᵢ[ℂ] E`). -/
theorem kahlerPowerForm_comp_linearIsometry (f : E →ₗᵢ[ℂ] F) (r : ℕ) :
    (kahlerPowerForm F r).compContinuousLinearMap (f.toContinuousLinearMap.restrictScalars ℝ) =
      kahlerPowerForm E r := by
  let fR : E →ₗᵢ[ℝ] F :=
    { toLinearMap := f.toLinearMap.restrictScalars ℝ
      norm_map' := f.norm_map }
  exact AlmostComplexStructure.kahlerPowerForm_comp_linearIsometry
    ofComplexModule_orthogonal fR
    (fun v ↦ by
      rw [AlmostComplexStructure.ofComplexModule_apply,
        AlmostComplexStructure.ofComplexModule_apply]
      exact f.map_smul Complex.I v) r

/-- The normalized Kähler power `ωʳ / r!` evaluates to `1` on the real frame
`TauCeti.complexToRealFamily u` of every complex-orthonormal family `u : Fin r → E`. -/
theorem kahlerPowerForm_complexToRealFamily {r : ℕ} {u : Fin r → E} (hu : Orthonormal ℂ u) :
    kahlerPowerForm E r (complexToRealFamily u) = 1 := by
  refine AlmostComplexStructure.kahlerPowerForm_apply_of_adapted
    (orthonormal_complexToRealFamily hu) fun j ↦ ?_
  have h0 : (⟨2 * (j : ℕ), by omega⟩ : Fin (2 * r)) = complexRealIndexEquiv r (j, 0) :=
    Fin.ext (by simp)
  have h1 : (⟨2 * (j : ℕ) + 1, by omega⟩ : Fin (2 * r)) = complexRealIndexEquiv r (j, 1) :=
    Fin.ext (by simp)
  rw [h0, h1, complexToRealFamily_complexRealIndexEquiv,
    complexToRealFamily_complexRealIndexEquiv]
  simp

/-- **Hilbert norm of the normalized Kähler power**:
`√⟨ωʳ / r!, ωʳ / r!⟩ = √((finrank ℂ E).choose r)`. -/
theorem sqrt_alternatingFormInner_kahlerPowerForm (r : ℕ) :
    √(alternatingFormInner E (2 * r) (kahlerPowerForm E r) (kahlerPowerForm E r)) =
      √((finrank ℂ E).choose r) := by
  have : FiniteDimensional ℂ E := Module.Finite.of_restrictScalars_finite ℝ ℂ E
  rw [kahlerPowerForm, AlmostComplexStructure.sqrt_alternatingFormInner_kahlerPowerForm
    ofComplexModule_orthogonal r, finrank_real_eq_two_mul_finrank_complex,
    Nat.mul_div_right _ (by decide : 0 < 2)]

/-- The normalized Kähler power has comass at most one in every degree. -/
theorem norm_kahlerPowerForm_le (r : ℕ) : ‖kahlerPowerForm E r‖ ≤ 1 :=
  AlmostComplexStructure.norm_kahlerPowerForm_le ofComplexModule_orthogonal r

/-- **The Wirtinger inequality in every degree**: on a finite-dimensional Hermitian vector space
`E`, for every `r ≤ finrank ℂ E`, the normalized Kähler power `ωʳ / r!` has comass one. -/
theorem norm_kahlerPowerForm {r : ℕ} (hr : r ≤ finrank ℂ E) : ‖kahlerPowerForm E r‖ = 1 := by
  have : FiniteDimensional ℂ E := Module.Finite.of_restrictScalars_finite ℝ ℂ E
  refine AlmostComplexStructure.norm_kahlerPowerForm ofComplexModule_orthogonal ?_
  rw [finrank_real_eq_two_mul_finrank_complex]
  omega

/-- **Equality case of the Wirtinger inequality in every degree**: a `2r`-frame `v` in a
finite-dimensional Hermitian vector space `E` is calibrated by `ωʳ / r!` precisely when `v` is
real-orthonormal and shares its exterior product with `TauCeti.complexToRealFamily u` for some
complex-orthonormal family `u : Fin r → E`. -/
theorem isCalibratedFrame_kahlerPowerForm_iff {r : ℕ} (v : Fin (2 * r) → E) :
    IsCalibratedFrame (kahlerPowerForm E r) v ↔
      Orthonormal ℝ v ∧ ∃ u : Fin r → E, Orthonormal ℂ u ∧
        ιMulti ℝ (2 * r) v = ιMulti ℝ (2 * r) (complexToRealFamily u) := by
  rw [kahlerPowerForm,
    AlmostComplexStructure.isCalibratedFrame_kahlerPowerForm_iff ofComplexModule_orthogonal v]
  refine and_congr_right fun _ ↦ ⟨?_, ?_⟩
  · rintro ⟨w, hw, hadapt, hι⟩
    let u : Fin r → E := fun j ↦ w ⟨2 * (j : ℕ), by omega⟩
    have hu : Orthonormal ℂ u := by
      refine ⟨fun j ↦ hw.1 _, fun j k hjk ↦ ?_⟩
      have hre : (inner ℂ (u j) (u k)).re = 0 := by
        rw [← RCLike.re_to_complex, ← inner_real_eq_re_inner (𝕜 := ℂ)]
        exact hw.2 (by
          intro h; have hv := congrArg Fin.val h; dsimp only at hv
          exact hjk (Fin.ext (by omega)))
      have him : (inner ℂ (u j) (u k)).im = 0 := by
        rw [show (inner ℂ (u j) (u k)).im = kahlerForm E ![u j, u k] from
            (kahlerForm_apply ![u j, u k]).symm, kahlerForm_apply_eq_inner]
        have hI : Complex.I • u j = w ⟨2 * (j : ℕ) + 1, by omega⟩ := by
          simpa only [AlmostComplexStructure.ofComplexModule_apply] using (hadapt j).symm
        rw [hI]
        exact hw.2 (by intro h; have hv := congrArg Fin.val h; dsimp only at hv; omega)
      exact Complex.ext hre him
    have hw_eq : complexToRealFamily u = w := by
      ext i
      obtain ⟨⟨j, k⟩, rfl⟩ := (complexRealIndexEquiv r).surjective i
      rw [complexToRealFamily_complexRealIndexEquiv]
      fin_cases k
      · have h0 : complexRealIndexEquiv r (j, 0) = ⟨2 * (j : ℕ), by omega⟩ :=
          Fin.ext (by simp)
        simp [h0, u]
      · have h1 : complexRealIndexEquiv r (j, 1) = ⟨2 * (j : ℕ) + 1, by omega⟩ :=
          Fin.ext (by simp)
        simpa [h1, u] using (hadapt j).symm
    exact ⟨u, hu, by rwa [hw_eq]⟩
  · rintro ⟨u, hu, hι⟩
    refine ⟨complexToRealFamily u, orthonormal_complexToRealFamily hu, fun j ↦ ?_, hι⟩
    have h0 : (⟨2 * (j : ℕ), by omega⟩ : Fin (2 * r)) = complexRealIndexEquiv r (j, 0) :=
      Fin.ext (by simp)
    have h1 : (⟨2 * (j : ℕ) + 1, by omega⟩ : Fin (2 * r)) = complexRealIndexEquiv r (j, 1) :=
      Fin.ext (by simp)
    rw [h0, h1, complexToRealFamily_complexRealIndexEquiv,
      complexToRealFamily_complexRealIndexEquiv]
    simp

end EveryDegree

end TauCeti
