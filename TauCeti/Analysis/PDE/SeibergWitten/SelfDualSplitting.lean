/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.SeibergWitten.QuadraticTwoForm
public import TauCeti.RingTheory.Idempotents.SquareRootOne

/-!
# The splitting of `W⁺` by a self-dual two-form of norm `√2`

Let `W⁺` be the positive half-spinors of a Hermitian Clifford module over an oriented real inner
product space `V` of dimension four, and let `C(iα) = i c₂(α)` be the Clifford map
(`TauCeti.SeibergWitten.cliffordRestriction`). A self-dual two-form `ω` with `‖ω‖² = 2`, such as
the Kähler form of an orthogonal complex structure inducing the orientation, satisfies
`C(iω)² = 4`. The two operators

`P_α = (1 + i c₂(ω) / 2) / 2 = (1 + C(iω) / 2) / 2`,  `P_β = (1 - C(iω) / 2) / 2`

are therefore complementary orthogonal projections, onto the `2`- and `-2`-eigenspaces of the
self-adjoint `C(iω)`; equivalently onto the `-2i`- and `2i`-eigenspaces of `c₂(ω)`. When `W⁺` has
complex dimension two both eigenspaces are lines. Here `P_α` is
`TauCeti.SeibergWitten.cliffordProjection o ρ ω`, the idempotent `TauCeti.halfOneAdd` cut out by
the square root of one `C(iω) / 2`, and `P_β` is the same construction for `-ω`.

This is the pointwise algebra behind Taubes's decomposition of a positive spinor on a symplectic
four-manifold as `ψ = α u₀ + β`, with `u₀` a unit spinor in the `-2i`-eigenline of `c₂(ω)` and `β`
in the complementary line. The quadratic two-form `q` (`TauCeti.SeibergWitten.quadraticTwoForm`)
of the curvature equation `F_A⁺ = q(ψ) + η` is computed on this decomposition: `q(u₀) = ω / 4`,
`q(β) = -(‖β‖² / 4) ω`, the cross term `q'(α u₀, β)` is orthogonal to `ω`, and in general
`⟪q(ψ), ω⟫ = (‖P_α ψ‖² - ‖P_β ψ‖²) / 2`. As elsewhere, `q(ψ)` is a real self-dual form indexing the
imaginary form `i q(ψ)`, so `q(u₀) = ω / 4` is the identity `q(u₀) = i ω / 4` of imaginary forms.

## Main definitions

* `TauCeti.SeibergWitten.cliffordProjection o ρ ω`: the operator `(1 + C(iω) / 2) / 2` on `W⁺`.

## Main results

* `cliffordProjection_neg`: `P_β = 1 - P_α`.
* `isStarProjection_cliffordProjection`: for self-dual `ω` with `‖ω‖² = 2`, `P_α` is an orthogonal
  projection.
* `cliffordProjection_apply_eq_self_iff`,
  `bivectorExterior_apply_of_cliffordProjection_apply_eq_self`: the fixed vectors of `P_α` are
  the `2`-eigenvectors of `C(iω)`, on which `c₂(ω)` acts by `-2i`.
* `finrank_range_cliffordProjection`: in complex dimension two, the range of `P_α` is a line.
* `rankOne_eq_smul_cliffordProjection`: `ψψ* = ‖ψ‖² P_α` for `ψ` in that line.
* `coe_quadraticTwoForm_of_cliffordProjection_apply_eq_self`,
  `coe_quadraticTwoForm_of_cliffordProjection_apply_eq_zero`: `q(ψ) = (‖ψ‖² / 4) ω` on the range
  of `P_α` and `q(ψ) = -(‖ψ‖² / 4) ω` on its kernel.
* `inner_quadraticTwoForm`: `⟪q(ψ), ω⟫ = (‖P_α ψ‖² - ‖P_β ψ‖²) / 2`.
* `coe_quadraticTwoForm_add_of_cliffordProjection`: for `P_α φ = φ` and `P_α β = 0`,
  `q(φ + β) = ((‖φ‖² - ‖β‖²) / 4) ω + q'(φ, β)`, with `⟪q'(φ, β), ω⟫ = 0`
  (`inner_quadraticTwoFormPolar_of_cliffordProjection`).

## References

* C. H. Taubes, *The Seiberg–Witten invariants and symplectic forms*, Math. Res. Lett. 1 (1994),
  809–822.
* C. H. Taubes, *SW ⇒ Gr: From the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

noncomputable section

namespace TauCeti.SeibergWitten

open CliffordAlgebra Module
open scoped RealInnerProductSpace InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin 4))
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W) (ω : ⋀[ℝ]^2 V)

/-- The dimension `Fact` makes the oriented four-space finite-dimensional. -/
local instance finiteDimensional_of_finrank_four : FiniteDimensional ℝ V :=
  .of_fact_finrank_eq_succ 3

/-- Instance search does not find the complex scalar-tower instances for the endomorphisms of the
submodule `W⁺`, so they are supplied from the generic ones. -/
local instance isScalarTower_end {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    IsScalarTower ℂ (E →L[ℂ] E) (E →L[ℂ] E) :=
  inferInstance

/-- See `isScalarTower_end`. -/
local instance smulCommClass_end {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] :
    SMulCommClass ℂ (E →L[ℂ] E) (E →L[ℂ] E) :=
  inferInstance

/-! ### The projection and its algebra -/

/-- **The Clifford projection** `P_α = (1 + C(iω) / 2) / 2 = (1 + i c₂(ω) / 2) / 2` of the positive
half-spinors determined by a two-form `ω`, the element `TauCeti.halfOneAdd` of `C(iω) / 2`. For
self-dual `ω` with `‖ω‖² = 2`, `C(iω) / 2` squares to one and `P_α` is the orthogonal projection
onto the `2`-eigenspace of `C(iω)` (`isStarProjection_cliffordProjection`,
`cliffordProjection_apply_eq_self_iff`); the complementary projection `P_β` is
`cliffordProjection o ρ (-ω)` (`cliffordProjection_neg`). -/
def cliffordProjection : positiveHalfSpinors o ρ →L[ℂ] positiveHalfSpinors o ρ :=
  halfOneAdd ℂ ((2⁻¹ : ℂ) • cliffordRestriction o ρ ω)

/-- Unfolding lemma for `cliffordProjection`. -/
theorem cliffordProjection_def :
    cliffordProjection o ρ ω = halfOneAdd ℂ ((2⁻¹ : ℂ) • cliffordRestriction o ρ ω) :=
  (rfl)

/-- The explicit formula `P_α = (1 + C(iω) / 2) / 2`. -/
theorem cliffordProjection_eq_smul :
    cliffordProjection o ρ ω = (2⁻¹ : ℂ) • (1 + (2⁻¹ : ℂ) • cliffordRestriction o ρ ω) := by
  rw [cliffordProjection_def, halfOneAdd_def, invOf_eq_inv]

/-- `C(iω) = 4 P_α - 2`. -/
theorem cliffordRestriction_eq_cliffordProjection :
    cliffordRestriction o ρ ω = (4 : ℂ) • cliffordProjection o ρ ω - (2 : ℂ) • 1 := by
  rw [cliffordProjection_eq_smul]
  module

/-- The complementary projection: `P_β = P(-ω) = 1 - P_α`. -/
theorem cliffordProjection_neg : cliffordProjection o ρ (-ω) = 1 - cliffordProjection o ρ ω := by
  rw [cliffordProjection_def, cliffordProjection_def, map_neg, smul_neg, halfOneAdd_neg_eq_one_sub]

/-- `P_β ψ = ψ - P_α ψ`. -/
theorem cliffordProjection_neg_apply (ψ : positiveHalfSpinors o ρ) :
    cliffordProjection o ρ (-ω) ψ = ψ - cliffordProjection o ρ ω ψ := by
  rw [cliffordProjection_neg, sub_apply, one_apply_eq_self]

variable {ω} in
/-- The fixed vectors of `P_α` are the `2`-eigenvectors of `C(iω)`: `P_α ψ = ψ` exactly when
`C(iω) ψ = 2 ψ`. -/
theorem cliffordProjection_apply_eq_self_iff {ψ : positiveHalfSpinors o ρ} :
    cliffordProjection o ρ ω ψ = ψ ↔ cliffordRestriction o ρ ω ψ = (2 : ℂ) • ψ := by
  rw [cliffordRestriction_eq_cliffordProjection, sub_apply, smul_apply, smul_apply,
    one_apply_eq_self]
  constructor <;> intro h
  · linear_combination (norm := module) (4 : ℂ) • h
  · linear_combination (norm := module) (4⁻¹ : ℂ) • h

variable {ω} in
/-- On the fixed vectors of `P_α`, the Clifford action of `ω` is multiplication by `-2i`: they are
`-2i`-eigenvectors of `c₂(ω)`. -/
theorem bivectorExterior_apply_of_cliffordProjection_apply_eq_self {ψ : positiveHalfSpinors o ρ}
    (hψ : cliffordProjection o ρ ω ψ = ψ) :
    ρ (bivectorExterior Q ω) ψ = (-2 * Complex.I) • (ψ : W) := by
  have h := congrArg Subtype.val ((cliffordProjection_apply_eq_self_iff o ρ).1 hψ)
  rw [coe_cliffordRestriction_apply, Submodule.coe_smul] at h
  -- Multiply `i c₂(ω) ψ = 2 ψ` by `-i`.
  calc ρ (bivectorExterior Q ω) ψ = (-Complex.I) • (Complex.I • ρ (bivectorExterior Q ω) ψ) := by
        rw [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul]
    _ = (-2 * Complex.I) • (ψ : W) := by rw [h, smul_smul]; ring_nf

variable {ω} in
/-- The kernel of `P_α` is the `-2`-eigenspace of `C(iω)`: `P_α ψ = 0` exactly when
`C(iω) ψ = -2 ψ`. -/
theorem cliffordProjection_apply_eq_zero_iff {ψ : positiveHalfSpinors o ρ} :
    cliffordProjection o ρ ω ψ = 0 ↔ cliffordRestriction o ρ ω ψ = (-2 : ℂ) • ψ := by
  rw [cliffordRestriction_eq_cliffordProjection, sub_apply, smul_apply, smul_apply,
    one_apply_eq_self]
  constructor <;> intro h
  · linear_combination (norm := module) (4 : ℂ) • h
  · linear_combination (norm := module) (4⁻¹ : ℂ) • h

variable {ρ} in
/-- If the generators act skew-adjointly, `P_α` is self-adjoint. -/
theorem isSelfAdjoint_cliffordProjection
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) :
    IsSelfAdjoint (cliffordProjection o ρ ω) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro ψ φ
  have h := (isSelfAdjoint_cliffordRestriction o hρ ω).isSymmetric ψ φ
  simp only [ContinuousLinearMap.coe_coe] at h
  simp [cliffordProjection_eq_smul, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, h, map_ofNat]

/-- The trace of `P_α` is half the dimension of `W⁺`. -/
theorem trace_cliffordProjection (hQ : ∀ v, Q v = -‖v‖ ^ 2) :
    LinearMap.trace ℂ (positiveHalfSpinors o ρ) (cliffordProjection o ρ ω) =
      finrank ℂ (positiveHalfSpinors o ρ) / 2 := by
  simp [cliffordProjection_eq_smul, map_add, trace_cliffordRestriction o ρ hQ, div_eq_inv_mul]

section Normalized

variable {ω} (hQ : ∀ v, Q v = -‖v‖ ^ 2) (hkl : 2 + 2 = finrank ℝ V)
  (hω : o.hodgeStar hkl ω = ω) (hω₂ : ‖ω‖ ^ 2 = 2)

include hQ hω hω₂

/-- A self-dual form of norm `√2` squares to `4` under the Clifford map: `C(iω)² = 4`. -/
private theorem cliffordRestriction_mul_self_of_norm_sq_eq_two :
    cliffordRestriction o ρ ω * cliffordRestriction o ρ ω = (4 : ℂ) • 1 := by
  rw [cliffordRestriction_mul_self_of_hodgeStar_eq_self o ρ hQ hkl hω, hω₂]
  norm_num

/-- `C(iω) / 2` is a square root of one. -/
private theorem inv_two_smul_cliffordRestriction_mul_self :
    (2⁻¹ : ℂ) • cliffordRestriction o ρ ω * (2⁻¹ : ℂ) • cliffordRestriction o ρ ω = 1 := by
  rw [smul_mul_smul, cliffordRestriction_mul_self_of_norm_sq_eq_two o ρ hQ hkl hω hω₂, smul_smul]
  norm_num

/-- `C(iω) P_α = 2 P_α`: the range of `P_α` lies in the `2`-eigenspace of `C(iω)`. -/
theorem cliffordRestriction_mul_cliffordProjection :
    cliffordRestriction o ρ ω * cliffordProjection o ρ ω = (2 : ℂ) • cliffordProjection o ρ ω := by
  have h := mul_halfOneAdd ℂ (inv_two_smul_cliffordRestriction_mul_self o ρ hQ hkl hω hω₂)
  rw [← cliffordProjection_def, smul_mul_assoc] at h
  calc cliffordRestriction o ρ ω * cliffordProjection o ρ ω =
        (2 : ℂ) • (2⁻¹ : ℂ) • (cliffordRestriction o ρ ω * cliffordProjection o ρ ω) := by
        rw [smul_smul]
        norm_num
    _ = (2 : ℂ) • cliffordProjection o ρ ω := by rw [h]

/-- `P_α` is idempotent. -/
theorem isIdempotentElem_cliffordProjection : IsIdempotentElem (cliffordProjection o ρ ω) :=
  isIdempotentElem_halfOneAdd ℂ (inv_two_smul_cliffordRestriction_mul_self o ρ hQ hkl hω hω₂)

variable {ρ} in
/-- **`P_α` is an orthogonal projection** when `ω` is self-dual of norm `√2`. -/
theorem isStarProjection_cliffordProjection
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) :
    IsStarProjection (cliffordProjection o ρ ω) :=
  ⟨isIdempotentElem_cliffordProjection o ρ hQ hkl hω hω₂,
    isSelfAdjoint_cliffordProjection o ω hρ⟩

section TwoDimensional

variable (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2)
include h₂

omit hkl hω hω₂ in
/-- In complex dimension two, `tr P_α = 1`. -/
private theorem trace_cliffordProjection_of_finrank_eq_two :
    LinearMap.trace ℂ (positiveHalfSpinors o ρ) (cliffordProjection o ρ ω) = 1 := by
  rw [trace_cliffordProjection o ρ ω hQ, h₂]
  norm_num

/-- **The range of `P_α` is a line** when `W⁺` has complex dimension two. -/
theorem finrank_range_cliffordProjection :
    finrank ℂ (LinearMap.range (cliffordProjection o ρ ω).toLinearMap) = 1 := by
  have hP : IsIdempotentElem (cliffordProjection o ρ ω).toLinearMap := by
    unfold IsIdempotentElem
    rw [← ContinuousLinearMap.toLinearMap_mul,
      (isIdempotentElem_cliffordProjection o ρ hQ hkl hω hω₂).eq]
  have h := (LinearMap.IsIdempotentElem.isProj_range _ hP).trace
  rw [trace_cliffordProjection_of_finrank_eq_two o ρ hQ h₂] at h
  exact_mod_cast h.symm

variable {ρ} (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
include hρ

/-- On the line `P_α W⁺`, the rank-one operator of a spinor is a multiple of `P_α`:
`ψψ* = ‖ψ‖² P_α` when `P_α ψ = ψ`. In particular `P_α = u₀u₀*` for a unit spinor `u₀` of
that line. -/
theorem rankOne_eq_smul_cliffordProjection {ψ : positiveHalfSpinors o ρ}
    (hψ : cliffordProjection o ρ ω ψ = ψ) :
    InnerProductSpace.rankOne ℂ ψ ψ = ((‖ψ‖ : ℂ) ^ 2) • cliffordProjection o ρ ω := by
  rcases eq_or_ne ψ 0 with rfl | hψ₀
  · ext v
    simp
  set P := cliffordProjection o ρ ω
  have hsa := isSelfAdjoint_cliffordProjection o ω hρ
  -- The range of `P` is the line spanned by `ψ`.
  have hline : ∀ w : LinearMap.range (P : Module.End ℂ (positiveHalfSpinors o ρ)),
      ∃ c : ℂ, c • (⟨ψ, ψ, hψ⟩ : LinearMap.range (P : Module.End ℂ _)) = w :=
    (finrank_eq_one_iff_of_nonzero' _ fun h ↦ hψ₀ (by simpa using congrArg Subtype.val h)).1
      (finrank_range_cliffordProjection o ρ hQ hkl hω hω₂ h₂)
  ext v
  obtain ⟨c, hc⟩ := hline ⟨P v, v, rfl⟩
  have hc' : c • ψ = P v := congrArg Subtype.val hc
  -- Pairing `P v = c ψ` with `ψ` identifies `c ‖ψ‖² = ⟪ψ, v⟫`.
  have hinner : ⟪ψ, v⟫_ℂ = c * (‖ψ‖ : ℂ) ^ 2 := by
    calc ⟪ψ, v⟫_ℂ = ⟪P ψ, v⟫_ℂ := by rw [hψ]
      _ = ⟪ψ, P v⟫_ℂ := hsa.isSymmetric ψ v
      _ = c * (‖ψ‖ : ℂ) ^ 2 := by
        rw [← hc', inner_smul_right, inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal]
  simp only [InnerProductSpace.rankOne_apply, smul_apply, ← hc', smul_smul,
    hinner]
  ring_nf

/-- **`q` on the line `P_α W⁺`**: `q(ψ) = (‖ψ‖² / 4) ω` when `P_α ψ = ψ`. In particular
`q(u₀) = ω / 4` for a unit spinor `u₀` of that line. -/
theorem coe_quadraticTwoForm_of_cliffordProjection_apply_eq_self {ψ : positiveHalfSpinors o ρ}
    (hψ : cliffordProjection o ρ ω ψ = ψ) :
    (quadraticTwoForm o ρ hkl ψ : ⋀[ℝ]^2 V) = (‖ψ‖ ^ 2 / 4) • ω := by
  have : Nontrivial (positiveHalfSpinors o ρ) := Module.nontrivial_of_finrank_eq_succ h₂
  have hsd : o.hodgeStar hkl ((quadraticTwoForm o ρ hkl ψ : ⋀[ℝ]^2 V) - (‖ψ‖ ^ 2 / 4) • ω) =
      (quadraticTwoForm o ρ hkl ψ : ⋀[ℝ]^2 V) - (‖ψ‖ ^ 2 / 4) • ω := by
    rw [map_sub, map_smul, hω, o.hodgeStar_coe_of_mem_eigenspace_one]
  -- Both sides have Clifford image `Q₀(ψ) = ψψ* - (‖ψ‖² / 2) = ‖ψ‖² (C(iω) / 4)`.
  rw [← sub_eq_zero, ← cliffordRestriction_eq_zero_iff_of_hodgeStar_eq_self o ρ hQ hkl hsd,
    map_sub, cliffordRestriction_quadraticTwoForm o hQ hkl hρ h₂, quadraticEnd_def,
    rankOne_eq_smul_cliffordProjection o hQ hkl hω hω₂ h₂ hρ hψ, map_smul,
    cliffordRestriction_eq_cliffordProjection, ← ContinuousLinearMap.one_def]
  module

/-- **`q` on the kernel of `P_α`**: `q(β) = -(‖β‖² / 4) ω` when `P_α β = 0`, that is when `β` lies
in the line `P_β W⁺`. -/
theorem coe_quadraticTwoForm_of_cliffordProjection_apply_eq_zero {β : positiveHalfSpinors o ρ}
    (hβ : cliffordProjection o ρ ω β = 0) :
    (quadraticTwoForm o ρ hkl β : ⋀[ℝ]^2 V) = -((‖β‖ ^ 2 / 4) • ω) := by
  have hneg : o.hodgeStar hkl (-ω) = -ω := by rw [map_neg, hω]
  have hβ' : cliffordProjection o ρ (-ω) β = β := by
    rw [cliffordProjection_neg, sub_apply, hβ, sub_zero,
      one_apply_eq_self]
  rw [coe_quadraticTwoForm_of_cliffordProjection_apply_eq_self o hQ hkl hneg (by rwa [norm_neg])
    h₂ hρ hβ', smul_neg]

end TwoDimensional

section Pairing

variable {ρ} (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v))
include hρ

omit hω₂ hρ in
/-- **The `ω`-component of `q`**: `⟪q(ψ), ω⟫ = (‖P_α ψ‖² - ‖P_β ψ‖²) / 2` for every self-dual `ω`.
With `ψ = α u₀ + β` and `‖ω‖² = 2` this is `(|α|² - ‖β‖²) / 2`, the term of the curvature equation
along `ω`. -/
theorem inner_quadraticTwoForm (ψ : positiveHalfSpinors o ρ) :
    ⟪(quadraticTwoForm o ρ hkl ψ : ⋀[ℝ]^2 V), ω⟫ =
      (‖cliffordProjection o ρ ω ψ‖ ^ 2 - ‖cliffordProjection o ρ (-ω) ψ‖ ^ 2) / 2 := by
  -- `P(±ω) ψ = ψ / 2 ± C(iω) ψ / 4`, and `‖a + b‖² - ‖a - b‖² = 4 Re⟪a, b⟫`.
  have hP : cliffordProjection o ρ ω ψ =
      (2⁻¹ : ℂ) • ψ + (4⁻¹ : ℂ) • cliffordRestriction o ρ ω ψ := by
    rw [cliffordProjection_eq_smul]
    simp only [smul_apply, add_apply, one_apply_eq_self, smul_add, smul_smul]
    norm_num
  have hP' : cliffordProjection o ρ (-ω) ψ =
      (2⁻¹ : ℂ) • ψ - (4⁻¹ : ℂ) • cliffordRestriction o ρ ω ψ := by
    rw [cliffordProjection_neg_apply, hP]
    module
  rw [inner_quadraticTwoForm_eq_re_inner o ρ hQ hkl hω, hP, hP', @norm_add_sq ℂ,
    @norm_sub_sq ℂ, inner_smul_left, inner_smul_right]
  simp only [RCLike.re_to_complex, map_inv₀, map_ofNat, ← mul_assoc]
  norm_num [Complex.mul_re]
  ring

omit hω₂ in
/-- **The cross term of `q` is orthogonal to `ω`**: `⟪q'(φ, β), ω⟫ = 0` when `P_α φ = φ` and
`P_α β = 0`. -/
theorem inner_quadraticTwoFormPolar_of_cliffordProjection {φ β : positiveHalfSpinors o ρ}
    (hφ : cliffordProjection o ρ ω φ = φ) (hβ : cliffordProjection o ρ ω β = 0) :
    ⟪(quadraticTwoFormPolar o ρ hkl φ β : ⋀[ℝ]^2 V), ω⟫ = 0 := by
  have hmem : ω ∈ Module.End.eigenspace (o.hodgeStar hkl : Module.End ℝ (⋀[ℝ]^2 V)) 1 :=
    Module.End.mem_eigenspace_iff.2 (by simpa using hω)
  have h := inner_cliffordRestrictionAdjoint_left o ρ hkl (quadraticEndPolar φ β) ⟨ω, hmem⟩
  rw [trace_quadraticEndPolar_mul_of_mem_traceFreeSelfAdjoint
    (cliffordRestriction_mem_traceFreeSelfAdjoint o hQ hρ ω)] at h
  simp only [Submodule.coe_inner] at h
  -- `φ` is orthogonal to `β`, as `P_α` is self-adjoint.
  have hφβ : ⟪φ, β⟫_ℂ = 0 :=
    calc ⟪φ, β⟫_ℂ = ⟪cliffordProjection o ρ ω φ, β⟫_ℂ := by rw [hφ]
      _ = ⟪φ, cliffordProjection o ρ ω β⟫_ℂ :=
        (isSelfAdjoint_cliffordProjection o ω hρ).isSymmetric φ β
      _ = 0 := by rw [hβ, inner_zero_right]
  -- Hence so is `C(iω) φ = 2 φ`.
  have horth : ⟪cliffordRestriction o ρ ω φ, β⟫_ℂ = 0 := by
    rw [(cliffordProjection_apply_eq_self_iff o ρ).1 hφ, inner_smul_left, hφβ, mul_zero]
  rw [quadraticTwoFormPolar_apply, Submodule.coe_smul, real_inner_smul_left, h,
    ← Submodule.coe_inner, horth]
  simp

/-- **`q` on the decomposition `ψ = φ + β`** with `P_α φ = φ` and `P_α β = 0`:
`q(φ + β) = ((‖φ‖² - ‖β‖²) / 4) ω + q'(φ, β)`, where the cross term `q'(φ, β)` is orthogonal to
`ω` (`inner_quadraticTwoFormPolar_of_cliffordProjection`). -/
theorem coe_quadraticTwoForm_add_of_cliffordProjection
    (h₂ : finrank ℂ (positiveHalfSpinors o ρ) = 2) {φ β : positiveHalfSpinors o ρ}
    (hφ : cliffordProjection o ρ ω φ = φ) (hβ : cliffordProjection o ρ ω β = 0) :
    (quadraticTwoForm o ρ hkl (φ + β) : ⋀[ℝ]^2 V) =
      ((‖φ‖ ^ 2 - ‖β‖ ^ 2) / 4) • ω + quadraticTwoFormPolar o ρ hkl φ β := by
  rw [quadraticTwoForm_add, Submodule.coe_add, Submodule.coe_add,
    coe_quadraticTwoForm_of_cliffordProjection_apply_eq_self o hQ hkl hω hω₂ h₂ hρ hφ,
    coe_quadraticTwoForm_of_cliffordProjection_apply_eq_zero o hQ hkl hω hω₂ h₂ hρ hβ]
  module

end Pairing

end Normalized

end TauCeti.SeibergWitten
