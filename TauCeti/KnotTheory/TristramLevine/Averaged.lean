/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Algebra.Group.Order
public import Mathlib.Topology.Order.LeftRightLim
public import TauCeti.Algebra.Polynomial.Laurent.Detection
public import TauCeti.KnotTheory.TristramLevine.Continuity
public import TauCeti.KnotTheory.TristramLevine.Metabolic
public import TauCeti.KnotTheory.TristramLevine.SEquivalence

/-!
# The averaged Tristram--Levine signature

The Tristram--Levine signature `σ_ω(V)` of a Seifert matrix `V` is the signature of the Hermitian
form `(1 - ω) V + (1 - conj ω) Vᵀ` (`TauCeti.KnotTheory.tristramLevineSignature`). Away from the
singular parameters of this form it is a knot-concordance invariant and vanishes on metabolic
Seifert matrices (`Matrix.tristramLevineSignature_eq_zero_of_congr_zero_block`), but at a singular
parameter, a root of the Alexander polynomial on the unit circle, it can fail to be one. The
standard repair (Livingston) replaces `σ_ω` by the mean of its two one-sided limits along the
circle, the **averaged Tristram--Levine signature**
(`TauCeti.KnotTheory.averagedTristramLevineSignature`):

`σ̄_ω(V) = (lim_{t → 0⁻} σ_{ω e^{it}}(V) + lim_{t → 0⁺} σ_{ω e^{it}}(V)) / 2`,

with the one-sided limits taken by Mathlib's `Function.leftLim` and `Function.rightLim`. It takes
values in `ℚ`, in fact in `½ ℤ`.

The one-sided limits exist as soon as the singular parameters do not accumulate at `ω`, that is,
the form is nonsingular at every point of a punctured neighbourhood of `ω` on the circle. Since the
singular parameters other than `1` are the roots of the Alexander polynomial, this holds at every
`ω` when the Alexander polynomial is nonzero
(`TauCeti.KnotTheory.eventually_det_tristramLevineForm_ne_zero`), for instance for the Seifert
matrix of a knot, where `Δ(1) = det (V - Vᵀ) = ±1`. Under that hypothesis the signature is
constant on each side of `ω` close to `ω`
(`TauCeti.KnotTheory.eventually_tristramLevineSignature_mul_exp_eq_rightLim` and its left version),
and:

* at a nonsingular parameter the averaged signature is the signature itself
  (`TauCeti.KnotTheory.averagedTristramLevineSignature_eq_of_det_ne_zero`);
* it is invariant under congruence, transposition and S-equivalence, like the signature, and it is
  additive along block diagonals, the Seifert matrices of connected sums;
* it is negated by passing to `-V` and to `-Vᵀ`, the Seifert matrices of the reverse mirror image
  and of the mirror image, and is unchanged by `ω ↦ ω⁻¹ = conj ω`;
* it vanishes for a metabolic Seifert matrix at **every** parameter of the circle, including the
  roots of the Alexander polynomial
  (`TauCeti.KnotTheory.averagedTristramLevineSignature_eq_zero_of_congr_zero_block`).

Combining the last three: if `V ⊕ (-W)` is metabolic, that is `V` and `W` are algebraically
concordant, then `σ̄_ω(V) = σ̄_ω(W)` for every `ω` on the circle
(`TauCeti.KnotTheory.averagedTristramLevineSignature_eq_of_congr_zero_block`). This is the
algebraic half of the statement that the averaged signature function is a homomorphism on the knot
concordance group at every point of the circle, connected sum going to the block sum of Seifert
matrices; the geometric half, that the Seifert matrices of concordant knots are algebraically
concordant, is not proved here.

## Main definitions

* `TauCeti.KnotTheory.averagedTristramLevineSignature`: the mean of the two one-sided limits of the
  Tristram--Levine signature at a point of the unit circle.

## Main results

* `TauCeti.KnotTheory.eventually_det_tristramLevineForm_ne_zero`: if the Alexander polynomial is
  nonzero, the singular parameters on the circle are isolated.
* `TauCeti.KnotTheory.averagedTristramLevineSignature_eq_of_eventually`: the averaged signature
  from the values of the signature on the two sides of `ω`.
* `TauCeti.KnotTheory.averagedTristramLevineSignature_eq_of_det_ne_zero`: at a nonsingular
  parameter the averaged signature is the signature.
* `TauCeti.KnotTheory.averagedTristramLevineSignature_fromBlocks_zero`: additivity along block
  diagonals.
* `TauCeti.KnotTheory.averagedTristramLevineSignature_eq_zero_of_congr_zero_block`: vanishing for
  metabolic matrices at every parameter.
* `TauCeti.KnotTheory.averagedTristramLevineSignature_eq_of_congr_zero_block`: algebraically
  concordant Seifert matrices have the same averaged signature function.

## References

* C. Livingston, [*A survey of classical knot concordance*](https://arxiv.org/abs/math/0307077),
  in *Handbook of Knot Theory* (2005), Section 3.1 (the signature function and its averaging at
  the jumps).
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 8.
* J. Levine, *Knot cobordism groups in codimension two*, Comment. Math. Helv. 44 (1969),
  229--244 (algebraic concordance and its signature invariants).
-/

public section

open Filter Topology Function Matrix LaurentPolynomial
open scoped ComplexConjugate

namespace TauCeti.KnotTheory

variable {ι : Type*} [Fintype ι]

/-- The **averaged Tristram--Levine signature** of a Seifert matrix `V` at a point `ω` of the unit
circle: the mean of the limits of `σ_z(V)` as `z = ω e^{it}` approaches `ω` clockwise (`t → 0⁻`)
and counterclockwise (`t → 0⁺`).

Both limits exist when the singular parameters of the form do not accumulate at `ω`, in
particular at every `ω` when the Alexander polynomial of `V` is nonzero. Otherwise Mathlib's
`Function.leftLim` and `Function.rightLim` fall back to the value `σ_ω(V)`, and no result below
applies. -/
noncomputable def averagedTristramLevineSignature (V : Matrix ι ι ℝ) (ω : Circle) : ℚ :=
  (((leftLim (fun t : ℝ => tristramLevineSignature V ↑(ω * Circle.exp t)) 0 : ℤ) : ℚ) +
    ((rightLim (fun t : ℝ => tristramLevineSignature V ↑(ω * Circle.exp t)) 0 : ℤ) : ℚ)) / 2

/-- The averaged signature is the mean of the left and right limits of `t ↦ σ_{ω e^{it}}(V)` at
`t = 0`. -/
theorem averagedTristramLevineSignature_def (V : Matrix ι ι ℝ) (ω : Circle) :
    averagedTristramLevineSignature V ω =
      (((leftLim (fun t : ℝ => tristramLevineSignature V ↑(ω * Circle.exp t)) 0 : ℤ) : ℚ) +
        ((rightLim (fun t : ℝ => tristramLevineSignature V ↑(ω * Circle.exp t)) 0 : ℤ) : ℚ)) /
          2 := by
  rw [averagedTristramLevineSignature]

/-! ### Moving along the circle -/

/-- Moving away from `ω` along the circle leaves `ω`. -/
private theorem tendsto_mul_circleExp_nhdsNE (ω : Circle) :
    Tendsto (fun t : ℝ => ω * Circle.exp t) (𝓝[≠] 0) (𝓝[≠] ω) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · exact tendsto_nhdsWithin_of_tendsto_nhds
      ((continuous_const.mul Circle.exp.continuous).tendsto' 0 ω (by simp))
  · have hpi := Real.pi_pos
    filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds (neg_neg_of_pos hpi) hpi),
      self_mem_nhdsWithin] with t ht ht0
    rw [Set.mem_compl_singleton_iff, Ne, mul_eq_left, ← Circle.exp_zero]
    exact fun h => ht0 (Circle.exp_injOn_Ioc (a := -Real.pi) (b := Real.pi) (by linarith)
      (Set.Ioo_subset_Ioc_self ht) ⟨neg_neg_of_pos hpi, hpi.le⟩ h)

/-- The coordinate `t ↦ ω e^{it}` around `ω` is continuous into `ℂ`. -/
private theorem continuous_coe_mul_circleExp (ω : Circle) :
    Continuous fun t : ℝ => ((ω * Circle.exp t : Circle) : ℂ) :=
  continuous_subtype_val.comp (continuous_const.mul Circle.exp.continuous)

/-! ### Computing the averaged signature -/

/-- **The averaged signature from the two sides.** If `σ_{ω e^{it}}(V)` is eventually `a` for
`t < 0` and eventually `b` for `t > 0`, the averaged signature at `ω` is `(a + b) / 2`. -/
theorem averagedTristramLevineSignature_eq_of_eventually {V : Matrix ι ι ℝ} {ω : Circle} {a b : ℤ}
    (ha : ∀ᶠ t in 𝓝[<] (0 : ℝ), tristramLevineSignature V ↑(ω * Circle.exp t) = a)
    (hb : ∀ᶠ t in 𝓝[>] (0 : ℝ), tristramLevineSignature V ↑(ω * Circle.exp t) = b) :
    averagedTristramLevineSignature V ω = ((a : ℚ) + b) / 2 := by
  rw [averagedTristramLevineSignature_def,
    leftLim_eq_of_tendsto (tendsto_const_nhds.congr' (ha.mono fun _ h => h.symm)),
    rightLim_eq_of_tendsto (tendsto_const_nhds.congr' (hb.mono fun _ h => h.symm))]

/-- The zero matrix, the Seifert matrix of a disc, has averaged signature zero. -/
@[simp]
theorem averagedTristramLevineSignature_zero_matrix (ω : Circle) :
    averagedTristramLevineSignature (0 : Matrix ι ι ℝ) ω = 0 := by
  rw [averagedTristramLevineSignature_eq_of_eventually (a := 0) (b := 0)
    (Eventually.of_forall fun _ => tristramLevineSignature_zero_matrix _)
    (Eventually.of_forall fun _ => tristramLevineSignature_zero_matrix _)]
  simp

/-! ### Invariance -/

/-- Transposing a Seifert matrix preserves its averaged signature. -/
@[simp]
theorem averagedTristramLevineSignature_transpose (V : Matrix ι ι ℝ) (ω : Circle) :
    averagedTristramLevineSignature Vᵀ ω = averagedTristramLevineSignature V ω := by
  simp only [averagedTristramLevineSignature_def, tristramLevineSignature_transpose]

/-- Reindexing a Seifert matrix along an equivalence does not change its averaged signature. -/
@[simp]
theorem averagedTristramLevineSignature_submatrix_equiv_self {κ : Type*} [Fintype κ] (e : ι ≃ κ)
    (V : Matrix ι ι ℝ) (ω : Circle) :
    averagedTristramLevineSignature (V.submatrix e.symm e.symm) ω =
      averagedTristramLevineSignature V ω := by
  simp only [averagedTristramLevineSignature_def, tristramLevineSignature_submatrix_equiv_self]

/-- **The averaged signature is invariant under S-equivalence** of integral Seifert matrices. -/
theorem IntegralSquareMatrix.SEquivalent.averagedTristramLevineSignature_eq
    {V W : IntegralSquareMatrix} (h : IntegralSquareMatrix.SEquivalent V W) (ω : Circle) :
    averagedTristramLevineSignature (V.2.map ((↑) : ℤ → ℝ)) ω =
      averagedTristramLevineSignature (W.2.map ((↑) : ℤ → ℝ)) ω := by
  simp only [averagedTristramLevineSignature_def, h.tristramLevineSignature_eq]

variable [DecidableEq ι]

/-- **Congruence invariance of the averaged signature.** -/
theorem averagedTristramLevineSignature_congr {P : Matrix ι ι ℝ} (hP : IsUnit P.det)
    (V : Matrix ι ι ℝ) (ω : Circle) :
    averagedTristramLevineSignature (P * V * Pᵀ) ω = averagedTristramLevineSignature V ω := by
  simp only [averagedTristramLevineSignature_def, tristramLevineSignature_congr hP]

/-! ### Isolated singular parameters and one-sided limits -/

/-- **The singular parameters of the Tristram--Levine form on the unit circle are isolated** when
the Alexander polynomial is nonzero: they are `1` and the finitely many roots of the Alexander
polynomial on the circle. -/
theorem eventually_det_tristramLevineForm_ne_zero {V : Matrix ι ι ℝ} (hΔ : alexander V ≠ 0)
    (ω : Circle) : ∀ᶠ z : Circle in 𝓝[≠] ω, (tristramLevineForm V z).det ≠ 0 := by
  have hroots : {u : ℂˣ | eval₂ Complex.ofRealHom u (alexander V) = 0}.Finite :=
    Set.not_infinite.mp fun h =>
      hΔ ((alexander V).eq_zero_of_infinite_eval₂_eq_zero _ Complex.ofRealHom.injective h)
  have hinj : Injective Circle.toUnits := fun a b h =>
    Circle.ext (by simpa using congrArg Units.val h)
  have hS : (insert 1 (Circle.toUnits ⁻¹'
      {u : ℂˣ | eval₂ Complex.ofRealHom u (alexander V) = 0})).Finite :=
    (hroots.preimage hinj.injOn).insert 1
  filter_upwards [hS.eventually_cofinite_notMem.filter_mono (nhdsNE_le_cofinite ω)] with z hz
  rw [Set.mem_insert_iff, not_or] at hz
  exact (det_tristramLevineForm_ne_zero_iff V z hz.1).mpr hz.2

/-- The signature is constant along a preconnected set of parameters on which the form is
nonsingular. -/
private theorem tristramLevineSignature_comp_eq_of_isPreconnected (V : Matrix ι ι ℝ)
    {γ : ℝ → ℂ} (hγ : Continuous γ) {s : Set ℝ} (hs : IsPreconnected s)
    (hdet : ∀ t ∈ s, (tristramLevineForm V (γ t)).det ≠ 0) {t₀ t : ℝ} (ht₀ : t₀ ∈ s)
    (ht : t ∈ s) :
    tristramLevineSignature V (γ t) = tristramLevineSignature V (γ t₀) := by
  have hloc : IsLocallyConstant fun x : s => tristramLevineSignature V (γ x) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    exact (hγ.comp continuous_subtype_val).continuousAt.eventually
      (eventually_tristramLevineSignature_eq V (hdet x x.2))
  have : PreconnectedSpace s := isPreconnected_iff_preconnectedSpace.mp hs
  exact hloc.apply_eq_of_preconnectedSpace ⟨t, ht⟩ ⟨t₀, ht₀⟩

variable {V : Matrix ι ι ℝ} {ω : Circle}

/-- Near a parameter at which the singular parameters do not accumulate, the form is nonsingular
at `ω e^{it}` for all small `t ≠ 0`. -/
private theorem eventually_det_tristramLevineForm_mul_circleExp_ne_zero
    (hdet : ∀ᶠ z : Circle in 𝓝[≠] ω, (tristramLevineForm V z).det ≠ 0) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ), (tristramLevineForm V ↑(ω * Circle.exp t)).det ≠ 0 :=
  (tendsto_mul_circleExp_nhdsNE ω).eventually hdet

/-- **The signature is eventually constant counterclockwise of `ω`**, where it equals its right
limit, provided the singular parameters do not accumulate at `ω`. -/
theorem eventually_tristramLevineSignature_mul_exp_eq_rightLim
    (hdet : ∀ᶠ z : Circle in 𝓝[≠] ω, (tristramLevineForm V z).det ≠ 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), tristramLevineSignature V ↑(ω * Circle.exp t) =
      rightLim (fun t : ℝ => tristramLevineSignature V ↑(ω * Circle.exp t)) 0 := by
  obtain ⟨ε, hε, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp
    ((eventually_det_tristramLevineForm_mul_circleExp_ne_zero hdet).filter_mono
      (nhdsGT_le_nhdsNE 0))
  have hε' : (0 : ℝ) < ε := hε
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), tristramLevineSignature V ↑(ω * Circle.exp t) =
      tristramLevineSignature V ↑(ω * Circle.exp (ε / 2)) :=
    Filter.mem_of_superset (Ioo_mem_nhdsGT hε') fun t ht =>
      tristramLevineSignature_comp_eq_of_isPreconnected V (continuous_coe_mul_circleExp ω)
        isPreconnected_Ioo hsub ⟨by positivity, by linarith⟩ ht
  rwa [rightLim_eq_of_tendsto (tendsto_const_nhds.congr' (hev.mono fun _ h => h.symm))]

/-- **The signature is eventually constant clockwise of `ω`**, where it equals its left limit,
provided the singular parameters do not accumulate at `ω`. -/
theorem eventually_tristramLevineSignature_mul_exp_eq_leftLim
    (hdet : ∀ᶠ z : Circle in 𝓝[≠] ω, (tristramLevineForm V z).det ≠ 0) :
    ∀ᶠ t in 𝓝[<] (0 : ℝ), tristramLevineSignature V ↑(ω * Circle.exp t) =
      leftLim (fun t : ℝ => tristramLevineSignature V ↑(ω * Circle.exp t)) 0 := by
  obtain ⟨ε, hε, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp
    ((eventually_det_tristramLevineForm_mul_circleExp_ne_zero hdet).filter_mono
      (nhdsLT_le_nhdsNE 0))
  have hε' : ε < (0 : ℝ) := hε
  have hev : ∀ᶠ t in 𝓝[<] (0 : ℝ), tristramLevineSignature V ↑(ω * Circle.exp t) =
      tristramLevineSignature V ↑(ω * Circle.exp (ε / 2)) :=
    Filter.mem_of_superset (Ioo_mem_nhdsLT hε') fun t ht =>
      tristramLevineSignature_comp_eq_of_isPreconnected V (continuous_coe_mul_circleExp ω)
        isPreconnected_Ioo hsub ⟨by linarith, by linarith⟩ ht
  rwa [leftLim_eq_of_tendsto (tendsto_const_nhds.congr' (hev.mono fun _ h => h.symm))]

/-! ### Nonsingular and conjugate parameters -/

/-- **At a nonsingular parameter the averaged signature is the Tristram--Levine signature.** -/
theorem averagedTristramLevineSignature_eq_of_det_ne_zero
    (hdet : (tristramLevineForm V ω).det ≠ 0) :
    averagedTristramLevineSignature V ω = tristramLevineSignature V ω := by
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ),
      tristramLevineSignature V ↑(ω * Circle.exp t) = tristramLevineSignature V ω :=
    ((continuous_coe_mul_circleExp ω).tendsto' 0 ω (by simp)).eventually
      (eventually_tristramLevineSignature_eq V hdet)
  rw [averagedTristramLevineSignature_eq_of_eventually (hev.filter_mono nhdsWithin_le_nhds)
    (hev.filter_mono nhdsWithin_le_nhds)]
  ring

/-- Away from `1` and the roots of the Alexander polynomial on the circle, the averaged signature
is the Tristram--Levine signature. -/
theorem averagedTristramLevineSignature_eq_of_alexander_ne_zero (hω : ω ≠ 1)
    (hΔ : eval₂ Complex.ofRealHom (Circle.toUnits ω) (alexander V) ≠ 0) :
    averagedTristramLevineSignature V ω = tristramLevineSignature V ω :=
  averagedTristramLevineSignature_eq_of_det_ne_zero
    ((det_tristramLevineForm_ne_zero_iff V ω hω).mpr hΔ)

/-- **Conjugate parameters give the same averaged signature**: passing from `ω` to
`ω⁻¹ = conj ω` exchanges the two one-sided limits. -/
theorem averagedTristramLevineSignature_inv
    (hdet : ∀ᶠ z : Circle in 𝓝[≠] ω, (tristramLevineForm V z).det ≠ 0) :
    averagedTristramLevineSignature V ω⁻¹ = averagedTristramLevineSignature V ω := by
  have hconj (t : ℝ) : tristramLevineSignature V ↑(ω⁻¹ * Circle.exp t) =
      tristramLevineSignature V ↑(ω * Circle.exp (-t)) := by
    rw [← tristramLevineSignature_conj V ↑(ω * Circle.exp (-t)), ← Circle.coe_inv_eq_conj,
      Circle.exp_neg, _root_.mul_inv_rev, inv_inv, mul_comm]
  have hL := eventually_tristramLevineSignature_mul_exp_eq_leftLim hdet
  have hR := eventually_tristramLevineSignature_mul_exp_eq_rightLim hdet
  have hneg₁ : Tendsto Neg.neg (𝓝[<] (0 : ℝ)) (𝓝[>] 0) := by
    simpa using tendsto_neg_nhdsLT_neg (a := (0 : ℝ))
  have hneg₂ : Tendsto Neg.neg (𝓝[>] (0 : ℝ)) (𝓝[<] 0) := by
    simpa using tendsto_neg_nhdsGT_neg (a := (0 : ℝ))
  rw [averagedTristramLevineSignature_eq_of_eventually hL hR,
    averagedTristramLevineSignature_eq_of_eventually
      ((hneg₁.eventually hR).mono fun t ht => (hconj t).trans ht)
      ((hneg₂.eventually hL).mono fun t ht => (hconj t).trans ht)]
  ring

/-! ### Negation and block sums -/

/-- The singular parameters of `-V` are those of `V`. -/
private theorem det_tristramLevineForm_neg_ne_zero_iff (V : Matrix ι ι ℝ) (z : ℂ) :
    (tristramLevineForm (-V) z).det ≠ 0 ↔ (tristramLevineForm V z).det ≠ 0 := by
  rw [tristramLevineForm_neg, det_neg]
  simp

/-- The singular parameters of `Vᵀ` are those of `V`. -/
private theorem det_tristramLevineForm_transpose_ne_zero_iff (V : Matrix ι ι ℝ) (z : ℂ) :
    (tristramLevineForm Vᵀ z).det ≠ 0 ↔ (tristramLevineForm V z).det ≠ 0 := by
  rw [tristramLevineForm_transpose, tristramLevineForm_conj, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det]
  simp

/-- **Negating a Seifert matrix negates its averaged signature.** The reverse mirror image of a
knot, its inverse in the concordance group, has Seifert matrix `-V`. -/
theorem averagedTristramLevineSignature_neg
    (hdet : ∀ᶠ z : Circle in 𝓝[≠] ω, (tristramLevineForm V z).det ≠ 0) :
    averagedTristramLevineSignature (-V) ω = -averagedTristramLevineSignature V ω := by
  have hL := eventually_tristramLevineSignature_mul_exp_eq_leftLim hdet
  have hR := eventually_tristramLevineSignature_mul_exp_eq_rightLim hdet
  rw [averagedTristramLevineSignature_eq_of_eventually
      (hL.mono fun t ht => by rw [tristramLevineSignature_neg, ht])
      (hR.mono fun t ht => by rw [tristramLevineSignature_neg, ht]),
    averagedTristramLevineSignature_eq_of_eventually hL hR, Int.cast_neg, Int.cast_neg]
  ring

/-- **The mirror image negates the averaged signature.** The mirror image of a knot has Seifert
matrix `-Vᵀ`. -/
theorem averagedTristramLevineSignature_neg_transpose
    (hdet : ∀ᶠ z : Circle in 𝓝[≠] ω, (tristramLevineForm V z).det ≠ 0) :
    averagedTristramLevineSignature (-Vᵀ) ω = -averagedTristramLevineSignature V ω := by
  have hdet' : ∀ᶠ z : Circle in 𝓝[≠] ω, (tristramLevineForm Vᵀ z).det ≠ 0 :=
    hdet.mono fun z hz => (det_tristramLevineForm_transpose_ne_zero_iff V z).mpr hz
  rw [averagedTristramLevineSignature_neg hdet', averagedTristramLevineSignature_transpose]

/-- **Additivity of the averaged signature along a block diagonal**, the Seifert matrix of a
connected sum. -/
theorem averagedTristramLevineSignature_fromBlocks_zero {κ : Type*} [Fintype κ] [DecidableEq κ]
    {W : Matrix κ κ ℝ}
    (hV : ∀ᶠ z : Circle in 𝓝[≠] ω, (tristramLevineForm V z).det ≠ 0)
    (hW : ∀ᶠ z : Circle in 𝓝[≠] ω, (tristramLevineForm W z).det ≠ 0) :
    averagedTristramLevineSignature (fromBlocks V 0 0 W) ω =
      averagedTristramLevineSignature V ω + averagedTristramLevineSignature W ω := by
  have hLV := eventually_tristramLevineSignature_mul_exp_eq_leftLim hV
  have hRV := eventually_tristramLevineSignature_mul_exp_eq_rightLim hV
  have hLW := eventually_tristramLevineSignature_mul_exp_eq_leftLim hW
  have hRW := eventually_tristramLevineSignature_mul_exp_eq_rightLim hW
  rw [averagedTristramLevineSignature_eq_of_eventually
      ((hLV.and hLW).mono fun t ht => by rw [tristramLevineSignature_fromBlocks_zero, ht.1, ht.2])
      ((hRV.and hRW).mono fun t ht => by rw [tristramLevineSignature_fromBlocks_zero, ht.1, ht.2]),
    averagedTristramLevineSignature_eq_of_eventually hLV hRV,
    averagedTristramLevineSignature_eq_of_eventually hLW hRW, Int.cast_add, Int.cast_add]
  ring

/-! ### Metabolic Seifert matrices -/

/-- **The averaged signature of a metabolic Seifert matrix vanishes at every parameter** of the
circle at which the singular parameters do not accumulate, including the singular ones: if a
change of basis puts `B` in block form with a half-size zero block, then `σ̄_ω(B) = 0`. -/
theorem averagedTristramLevineSignature_eq_zero_of_congr_zero_block
    {B P : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ} (hP : IsUnit P.det) (hzero : (P * B * Pᵀ).toBlocks₁₁ = 0)
    (hdet : ∀ᶠ z : Circle in 𝓝[≠] ω, (tristramLevineForm B z).det ≠ 0) :
    averagedTristramLevineSignature B ω = 0 := by
  have h₀ : ∀ᶠ t in 𝓝[≠] (0 : ℝ), tristramLevineSignature B ↑(ω * Circle.exp t) = 0 :=
    (eventually_det_tristramLevineForm_mul_circleExp_ne_zero hdet).mono fun t ht =>
      tristramLevineSignature_eq_zero_of_congr_zero_block_of_det_ne_zero B P hP hzero _ ht
  rw [averagedTristramLevineSignature_eq_of_eventually (h₀.filter_mono (nhdsLT_le_nhdsNE 0))
    (h₀.filter_mono (nhdsGT_le_nhdsNE 0))]
  simp

/-- **Algebraically concordant Seifert matrices have the same averaged signature function.** If
the block sum `V ⊕ (-W)`, reindexed along `e`, becomes metabolic after a change of basis, then
`σ̄_ω(V) = σ̄_ω(W)` at every parameter `ω` at which the singular parameters of neither `V` nor `W`
accumulate; by `TauCeti.KnotTheory.eventually_det_tristramLevineForm_ne_zero` this is every `ω`
when both Alexander polynomials are nonzero. -/
theorem averagedTristramLevineSignature_eq_of_congr_zero_block {κ κ' : Type*} [Fintype κ]
    [DecidableEq κ] [Fintype κ'] [DecidableEq κ'] {V : Matrix κ κ ℝ} {W : Matrix κ' κ' ℝ}
    (e : κ ⊕ κ' ≃ ι ⊕ ι) {P : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ} (hP : IsUnit P.det)
    (hzero : (P * (fromBlocks V 0 0 (-W)).submatrix e.symm e.symm * Pᵀ).toBlocks₁₁ = 0)
    (hV : ∀ᶠ z : Circle in 𝓝[≠] ω, (tristramLevineForm V z).det ≠ 0)
    (hW : ∀ᶠ z : Circle in 𝓝[≠] ω, (tristramLevineForm W z).det ≠ 0) :
    averagedTristramLevineSignature V ω = averagedTristramLevineSignature W ω := by
  have hW' : ∀ᶠ z : Circle in 𝓝[≠] ω, (tristramLevineForm (-W) z).det ≠ 0 :=
    hW.mono fun z hz => (det_tristramLevineForm_neg_ne_zero_iff W z).mpr hz
  have hB : ∀ᶠ z : Circle in 𝓝[≠] ω,
      (tristramLevineForm ((fromBlocks V 0 0 (-W)).submatrix e.symm e.symm) z).det ≠ 0 :=
    (hV.and hW').mono fun z hz => by
      rw [tristramLevineForm_submatrix, det_submatrix_equiv_self,
        tristramLevineForm_fromBlocks_zero, det_fromBlocks_zero₂₁]
      exact mul_ne_zero hz.1 hz.2
  have h := averagedTristramLevineSignature_eq_zero_of_congr_zero_block hP hzero hB
  rw [averagedTristramLevineSignature_submatrix_equiv_self,
    averagedTristramLevineSignature_fromBlocks_zero hV hW',
    averagedTristramLevineSignature_neg hW] at h
  linarith

end TauCeti.KnotTheory
