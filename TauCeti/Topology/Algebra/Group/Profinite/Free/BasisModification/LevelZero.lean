/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.BasisModification

/-!
# The basis-modification map at level zero

Let `F = freeProP p X` be the free pro-`p` group on a finite linearly ordered type `X`, with
canonical generators `x_i = freeProP.of i` and lower `p`-series `λ_k = λ_k(F)`. A family
`w : X → λ_0(F) = F` defines the basis modification `θ_w : x_i ↦ x_i * w_i`
(`TauCeti.freeProP.basisModification`), which at this level is an arbitrary continuous endomorphism
of `F` (`TauCeti.freeProP.eq_basisModification`). For a relator `r ∈ λ_1(F)` with class
`ρ ∈ gr_1(F)` it moves `r` inside its coset by the element `r⁻¹ * θ_w r ∈ λ_1(F)`, whose class in
`gr_1(F)` depends only on the classes `ω_i ∈ gr_0(F)` of the `w_i`.

That class is the **level-zero basis-modification map** `δ⁰_ρ(ω)`
(`TauCeti.freeProP.basisModificationDeltaZero`), the map `δ_1` into `gr_1(F)` in the indexing of
the maps by their target degree: writing
`ρ = Σ_i c_i π ξ_i + Σ_{i<k} a_{ik} [ξ_i, ξ_k]` in the standard basis
`TauCeti.freeProP.degreeOneBasis`, with `ξ_i ∈ gr_0(F)` the class of `x_i`,

  `δ⁰_ρ(ω) = Σ_i c_i (π ω_i + (p choose 2) • [ω_i, ξ_i])
             + Σ_{i<k} a_{ik} ([ω_i, ξ_k] - [ω_k, ξ_i] + [ω_i, ω_k])`.

It is `𝔽_p`-linear in `ρ`, and it is the level-zero instance of the maps `δ` of
`TauCeti.freeProP.basisModificationDelta`, which are stated there for modifications by elements of
`λ_m(F)` with `m ≥ 1` and are `𝔽_p`-linear in the classes `ω_i` as well. At level zero the map is
**not** linear in `ω`, for two reasons that are both visible in the formula: the `p`-power operator
`π` is not additive on `gr_0(F)` when `p = 2` (`TauCeti.gradedPow_add_zero`), and the bracket part
of `ρ` contributes the quadratic terms `a_{ik} [ω_i, ω_k]`, because `[ξ_i + ω_i, ξ_k + ω_k]`
expands bilinearly. The **polarization identity**
(`TauCeti.freeProP.basisModificationDeltaZero_add`) records the exact defect:

  `δ⁰_ρ(v + w) - δ⁰_ρ(v) - δ⁰_ρ(w)
     = (p choose 2) • Σ_i c_i [w_i, v_i] + Σ_{i<k} a_{ik} ([v_i, w_k] + [w_i, v_k])`,

so for odd `p` only the bracket part of `ρ` obstructs additivity, and for `p = 2` the `p`-power
part contributes `Σ_i c_i [v_i, w_i]` in addition. The second sum is not an artifact of the
presentation: for the bracket class `ρ = [ξ_0, ξ_1]` in rank two, the modification
`x_0 ↦ x_0 * x_1`, `x_1 ↦ x_1 * x_0` has deviation `δ⁰_ρ(ω) = -ρ`
(`TauCeti.freeProP.basisModificationDeltaZero_gradedBracket_gradedMkZero_fin_two`), whereas the
terms linear in `ω` vanish there. Equivalently, the induced map `θ_*` sends `ρ` to
`ρ + δ⁰_ρ(ω) = 0`: with `r = [x_0, x_1]` one has `θ_w r = [x_0 * x_1, x_1 * x_0] ∈ λ_2(F)`, so
`θ_w r ≡ 1` modulo `λ_2(F)` and `r⁻¹ * θ_w r ≡ r⁻¹`.

Through the deviation `θ_* - id` of an arbitrary endomorphism, the same formula computes the
induced map of any continuous endomorphism `φ` of `F` on `gr_1(F)` from its effect on the generator
classes (`TauCeti.freeProP.gradedMap_one_eq_add_basisModificationDeltaZero`).

## Main definitions

* `TauCeti.freeProP.basisModificationDeltaZero`: the level-zero basis-modification map
  `δ⁰ : gr_0(F)^X → (gr_1(F) →ₗ[𝔽_p] gr_1(F))`, `(ω, ρ) ↦ δ⁰_ρ(ω)`.

## Main results

* `TauCeti.freeProP.gradedDeviation_basisModification_zero`,
  `TauCeti.freeProP.gradedMk_inv_mul_basisModification_zero`: the class of `r⁻¹ * θ_w r` in
  `gr_1(F)` is `δ⁰_ρ(ω)`; in particular it depends only on the classes `ω_i`.
* `TauCeti.freeProP.basisModificationDeltaZero_apply`,
  `TauCeti.freeProP.basisModificationDeltaZero_eq_sum_gradedPow_add_sum_add_sum`: the formula for
  `δ⁰_ρ(ω)`, in the standard basis and through the partial derivatives
  `δ⁰_ρ(ω) = Σ_i c_i • π ω_i + Σ_i [ω_i, ∂_i ρ] + Σ_{i<k} a_{ik} [ω_i, ω_k]`.
* `TauCeti.freeProP.basisModificationDeltaZero_add`,
  `TauCeti.freeProP.basisModificationDeltaZero_add_of_odd`,
  `TauCeti.freeProP.basisModificationDeltaZero_add_of_two`: the polarization identity.
* `TauCeti.freeProP.gradedMap_one_eq_add_basisModificationDeltaZero`: the induced map of a
  continuous endomorphism of `F` on `gr_1(F)` is `ρ ↦ ρ + δ⁰_ρ(φ_* ξ - ξ)`.

## References

* J. Labute, *Classification of Demushkin groups*, Canadian J. Math. 19 (1967), §2,
  Proposition 5 and the formula on p. 124.
-/

public section

namespace TauCeti.freeProP

open Subgroup Submodule
open scoped commutatorElement

universe u

variable {p : ℕ} {X : Type u} [Fact p.Prime] [Finite X] [LinearOrder X]

/-! ### The map `δ⁰` -/

variable (p X) in
/-- **The level-zero basis-modification map `δ⁰`**: for a family `ω : X → gr_0(F)` of degree-zero
classes, the `𝔽_p`-linear map `gr_1(F) → gr_1(F)` sending a class `ρ ∈ gr_1(F)` to

  `δ⁰_ρ(ω) = Σ_i c_i (π ω_i + (p choose 2) • [ω_i, ξ_i])
             + Σ_{i<k} a_{ik} ([ω_i, ξ_k] - [ω_k, ξ_i] + [ω_i, ω_k])`

where `c_i` and `a_{ik}` are the coordinates of `ρ` in the standard basis
`TauCeti.freeProP.degreeOneBasis` of `gr_1(F)`, that is
`ρ = Σ_i c_i π ξ_i + Σ_{i<k} a_{ik} [ξ_i, ξ_k]` with `ξ_i ∈ gr_0(F)` the class of `x_i`. It is
defined by its values on that basis
(`TauCeti.freeProP.basisModificationDeltaZero_degreeOneBasis_inl`,
`TauCeti.freeProP.basisModificationDeltaZero_degreeOneBasis_inr`), and its value at a general `ρ`
is `TauCeti.freeProP.basisModificationDeltaZero_apply`. For a relator `r ∈ λ_1(F)` with class `ρ`
and a family `w : X → F` with classes `ω_i ∈ gr_0(F)`, `δ⁰_ρ(ω)` is the class in `gr_1(F)` of
`r⁻¹ * θ_w r`, the amount by which the basis modification `θ_w : x_i ↦ x_i * w_i` moves `r`
(`TauCeti.freeProP.gradedMk_inv_mul_basisModification_zero`). Unlike the maps
`TauCeti.freeProP.basisModificationDelta` at the levels `m ≥ 1`, it is quadratic and not linear in
`ω`, with polarization `TauCeti.freeProP.basisModificationDeltaZero_add`. -/
noncomputable def basisModificationDeltaZero (ω : X → gradedPiece p (freeProP p X) 0) :
    gradedPiece p (freeProP p X) 1 →ₗ[ZMod p] gradedPiece p (freeProP p X) 1 :=
  (degreeOneBasis p X).constr (ZMod p) <| Sum.elim
    (fun i ↦ gradedPow p (freeProP p X) 0 (ω i) +
      p.choose 2 • gradedBracket p (freeProP p X) 0 0 (ω i) (gradedMkZero p (freeProP p X) (of i)))
    fun ij ↦
      gradedBracket p (freeProP p X) 0 0 (ω ij.1.1) (gradedMkZero p (freeProP p X) (of ij.1.2)) -
        gradedBracket p (freeProP p X) 0 0 (ω ij.1.2) (gradedMkZero p (freeProP p X) (of ij.1.1)) +
        gradedBracket p (freeProP p X) 0 0 (ω ij.1.1) (ω ij.1.2)

/-- **The value of `δ⁰` on a `p`-power basis vector**:
`δ⁰_{π ξ_i}(ω) = π ω_i + (p choose 2) • [ω_i, ξ_i]`. -/
theorem basisModificationDeltaZero_degreeOneBasis_inl (ω : X → gradedPiece p (freeProP p X) 0)
    (i : X) :
    basisModificationDeltaZero p X ω (degreeOneBasis p X (Sum.inl i)) =
      gradedPow p (freeProP p X) 0 (ω i) +
        p.choose 2 • gradedBracket p (freeProP p X) 0 0 (ω i)
          (gradedMkZero p (freeProP p X) (of i)) := by
  rw [basisModificationDeltaZero, Module.Basis.constr_basis, Sum.elim_inl]

/-- **The value of `δ⁰` on a bracket basis vector**:
`δ⁰_{[ξ_i, ξ_k]}(ω) = [ω_i, ξ_k] - [ω_k, ξ_i] + [ω_i, ω_k]`. -/
theorem basisModificationDeltaZero_degreeOneBasis_inr (ω : X → gradedPiece p (freeProP p X) 0)
    (ij : {ij : X × X // ij.1 < ij.2}) :
    basisModificationDeltaZero p X ω (degreeOneBasis p X (Sum.inr ij)) =
      gradedBracket p (freeProP p X) 0 0 (ω ij.1.1) (gradedMkZero p (freeProP p X) (of ij.1.2)) -
        gradedBracket p (freeProP p X) 0 0 (ω ij.1.2) (gradedMkZero p (freeProP p X) (of ij.1.1)) +
        gradedBracket p (freeProP p X) 0 0 (ω ij.1.1) (ω ij.1.2) := by
  rw [basisModificationDeltaZero, Module.Basis.constr_basis, Sum.elim_inr]

/-- **The value of `δ⁰`**: with `ρ = Σ_i c_i π ξ_i + Σ_{i<k} a_{ik} [ξ_i, ξ_k]`,
`δ⁰_ρ(ω) = Σ_i c_i (π ω_i + (p choose 2) • [ω_i, ξ_i])
  + Σ_{i<k} a_{ik} ([ω_i, ξ_k] - [ω_k, ξ_i] + [ω_i, ω_k])`. -/
theorem basisModificationDeltaZero_apply [Fintype X] (ω : X → gradedPiece p (freeProP p X) 0)
    (ρ : gradedPiece p (freeProP p X) 1) :
    basisModificationDeltaZero p X ω ρ =
      ∑ i, (degreeOneBasis p X).repr ρ (Sum.inl i) •
          (gradedPow p (freeProP p X) 0 (ω i) +
            p.choose 2 • gradedBracket p (freeProP p X) 0 0 (ω i)
              (gradedMkZero p (freeProP p X) (of i))) +
        ∑ ij : {ij : X × X // ij.1 < ij.2}, (degreeOneBasis p X).repr ρ (Sum.inr ij) •
          (gradedBracket p (freeProP p X) 0 0 (ω ij.1.1)
              (gradedMkZero p (freeProP p X) (of ij.1.2)) -
            gradedBracket p (freeProP p X) 0 0 (ω ij.1.2)
              (gradedMkZero p (freeProP p X) (of ij.1.1)) +
            gradedBracket p (freeProP p X) 0 0 (ω ij.1.1) (ω ij.1.2)) := by
  conv_lhs => rw [← (degreeOneBasis p X).sum_repr ρ]
  simp only [Fintype.sum_sum_type, map_add, map_sum, map_smul,
    basisModificationDeltaZero_degreeOneBasis_inl, basisModificationDeltaZero_degreeOneBasis_inr]

/-! ### The class of the moved relator -/

/-- **The class of the moved relator is `δ⁰_ρ(ω)`.** For `w : X → λ_0(F) = F` and `ρ ∈ gr_1(F)`,
the graded deviation of the basis modification `θ_w` on `ρ` is `δ⁰_ρ(ω)`, where `ω_i ∈ gr_0(F)` is
the class of `w_i`. -/
theorem gradedDeviation_basisModification_zero (w : X → pLowerCentralSeries p (freeProP p X) 0)
    (ρ : gradedPiece p (freeProP p X) 1) :
    gradedDeviation (basisModification w).toMonoidHom (basisModification w).continuous
        (inv_mul_basisModification_mem_pLowerCentralSeries w) 1 ρ =
      basisModificationDeltaZero p X (fun i ↦ gradedMkZero p (freeProP p X) (w i)) ρ := by
  -- Both sides are linear in `ρ`, and they agree on the standard basis of `gr_1(F)` by the
  -- degree-zero rules for the deviation against `π` and against the bracket.
  have key : (gradedDeviation (basisModification w).toMonoidHom (basisModification w).continuous
      (inv_mul_basisModification_mem_pLowerCentralSeries w) 1).toZModLinearMap p =
        basisModificationDeltaZero p X fun i ↦ gradedMkZero p (freeProP p X) (w i) := by
    refine (degreeOneBasis p X).ext fun b ↦ ?_
    rw [AddMonoidHom.coe_toZModLinearMap]
    rcases b with i | ij
    · rw [basisModificationDeltaZero_degreeOneBasis_inl, degreeOneBasis_apply, degreeOneFamily_inl,
        gradedDeviation_gradedPow_zero, gradedDeviation_basisModification_gradedMkZero_of,
        gradedMk_zero]
    · rw [basisModificationDeltaZero_degreeOneBasis_inr, degreeOneBasis_apply, degreeOneFamily_inr,
        gradedDeviation_gradedBracket_zero_zero, gradedDeviation_basisModification_gradedMkZero_of,
        gradedDeviation_basisModification_gradedMkZero_of, gradedMk_zero, gradedMk_zero]
  exact LinearMap.congr_fun key ρ

/-- **The basis modification `θ_w` by an arbitrary family `w : X → F` moves a relator
`r ∈ λ_1(F)` by `δ⁰_ρ(ω)`**: the class in `gr_1(F)` of `r⁻¹ * θ_w r` is `δ⁰_ρ(ω)`, where
`ρ ∈ gr_1(F)` is the class of `r` and `ω_i ∈ gr_0(F)` the class of `w_i`. In particular that class
depends only on the classes `ω_i` of the modifications. -/
@[simp]
theorem gradedMk_inv_mul_basisModification_zero (w : X → pLowerCentralSeries p (freeProP p X) 0)
    (r : pLowerCentralSeries p (freeProP p X) 1) :
    gradedMk p (freeProP p X) 1 ⟨(r : freeProP p X)⁻¹ * basisModification w r,
        inv_mul_apply_mem_pLowerCentralSeries (basisModification w).toMonoidHom
          (basisModification w).continuous
          (inv_mul_basisModification_mem_pLowerCentralSeries w) r.2⟩ =
      basisModificationDeltaZero p X (fun i ↦ gradedMkZero p (freeProP p X) (w i))
        (gradedMk p (freeProP p X) 1 r) := by
  have h := gradedDeviation_basisModification_zero w (gradedMk p (freeProP p X) 1 r)
  rwa [gradedDeviation_gradedMk] at h

/-- **The induced map of a continuous endomorphism on `gr_1(F)`**, from its effect on the generator
classes: `φ_* ρ = ρ + δ⁰_ρ(ω)` with `ω_i = φ_* ξ_i - ξ_i`, since `φ` is the basis modification by
`x_i⁻¹ * φ x_i`. -/
theorem gradedMap_one_eq_add_basisModificationDeltaZero (φ : freeProP p X →ₜ* freeProP p X)
    (ρ : gradedPiece p (freeProP p X) 1) :
    gradedMap p φ.toMonoidHom φ.continuous 1 ρ =
      ρ + basisModificationDeltaZero p X
        (fun i ↦ gradedMkZero p (freeProP p X) (φ (of i)) - gradedMkZero p (freeProP p X) (of i))
        ρ := by
  -- `φ` is the basis modification by `w_i = x_i⁻¹ * φ x_i`, whose deviation on `ρ` is `δ⁰_ρ(ω)`.
  have h := gradedDeviation_basisModification_zero (fun i ↦ (⟨(of i)⁻¹ * φ (of i),
    mem_pLowerCentralSeries_zero p _⟩ : pLowerCentralSeries p (freeProP p X) 0)) ρ
  rw [gradedDeviation_one_eq_gradedMap_sub, sub_eq_iff_eq_add'] at h
  simp only [gradedMkZero_mul, gradedMkZero_inv, neg_add_eq_sub] at h
  exact (congrArg (fun ψ : freeProP p X →ₜ* freeProP p X ↦
    gradedMap p ψ.toMonoidHom ψ.continuous 1 ρ) (eq_basisModification φ)).trans h

/-! ### The formula through the partial derivatives -/

/-- **`δ⁰` through the partial derivatives**:
`δ⁰_ρ(ω) = Σ_i c_i • π ω_i + Σ_i [ω_i, ∂_i ρ] + Σ_{i<k} a_{ik} [ω_i, ω_k]`, where `c_i` and
`a_{ik}` are the coordinates of `ρ`. The terms linear in `ω` are those of the higher-degree maps
`TauCeti.freeProP.basisModificationDelta_eq_gradedPow_add_sum`, except that the `p`-powers are not
collected into a single `π (Σ_i c_i ω_i)`, since `π` is not additive in degree zero; the quadratic
terms are the bracket part of `ρ` evaluated on `ω`. -/
theorem basisModificationDeltaZero_eq_sum_gradedPow_add_sum_add_sum [Fintype X]
    (ω : X → gradedPiece p (freeProP p X) 0) (ρ : gradedPiece p (freeProP p X) 1) :
    basisModificationDeltaZero p X ω ρ =
      ∑ i, (degreeOneBasis p X).repr ρ (Sum.inl i) • gradedPow p (freeProP p X) 0 (ω i) +
        ∑ i, gradedBracket p (freeProP p X) 0 0 (ω i) (degreeOneDeriv p X i ρ) +
        ∑ ij : {ij : X × X // ij.1 < ij.2}, (degreeOneBasis p X).repr ρ (Sum.inr ij) •
          gradedBracket p (freeProP p X) 0 0 (ω ij.1.1) (ω ij.1.2) := by
  -- Both sides are linear in `ρ`; compare them on the standard basis of `gr_1(F)`.
  have key : basisModificationDeltaZero p X ω =
      ∑ i, (Finsupp.lapply (Sum.inl i) ∘ₗ (degreeOneBasis p X).repr.toLinearMap).smulRight
          (gradedPow p (freeProP p X) 0 (ω i)) +
        ∑ i, gradedBracketLinear p (freeProP p X) 0 0 (ω i) ∘ₗ degreeOneDeriv p X i +
        ∑ ij : {ij : X × X // ij.1 < ij.2},
          (Finsupp.lapply (Sum.inr ij) ∘ₗ (degreeOneBasis p X).repr.toLinearMap).smulRight
            (gradedBracket p (freeProP p X) 0 0 (ω ij.1.1) (ω ij.1.2)) := by
    refine (degreeOneBasis p X).ext fun b ↦ ?_
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sum_apply,
      LinearMap.smulRight_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply,
      gradedBracketLinear_apply, Finsupp.single_apply]
    rcases b with j | jk
    · rw [basisModificationDeltaZero_degreeOneBasis_inl]
      simp only [Sum.inl.injEq, reduceCtorEq, ↓reduceIte, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq, Finset.mem_univ, Finset.sum_const_zero, add_zero,
        degreeOneDeriv_degreeOneBasis_inl]
      congr 1
      rw [Finset.sum_eq_single j (fun i _ hij ↦ by rw [ite_eq_right (Ne.symm hij), map_zero])
        (fun h ↦ (h (Finset.mem_univ j)).elim), ite_eq_left rfl, map_nsmul]
    · rw [basisModificationDeltaZero_degreeOneBasis_inr]
      simp only [reduceCtorEq, Sum.inr.injEq, ↓reduceIte, zero_smul, Finset.sum_const_zero,
        zero_add, ite_smul, one_smul, Finset.sum_ite_eq, Finset.mem_univ,
        degreeOneDeriv_degreeOneBasis_inr, map_sub, Finset.sum_sub_distrib]
      congr 2
      · rw [Finset.sum_eq_single jk.1.1 (fun i _ hij ↦ by rw [ite_eq_right (Ne.symm hij), map_zero])
          (fun h ↦ (h (Finset.mem_univ _)).elim), ite_eq_left rfl]
      · rw [Finset.sum_eq_single jk.1.2 (fun i _ hij ↦ by rw [ite_eq_right (Ne.symm hij), map_zero])
          (fun h ↦ (h (Finset.mem_univ _)).elim), ite_eq_left rfl]
  have h := LinearMap.congr_fun key ρ
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.smulRight_apply, LinearEquiv.coe_coe, Finsupp.lapply_apply,
    gradedBracketLinear_apply] using h

/-! ### The polarization identity -/

/-- **The polarization identity for `δ⁰`.** The level-zero basis-modification map is quadratic in
the family of classes: for `v, w : X → gr_0(F)`,
`δ⁰_ρ(v + w) = δ⁰_ρ(v) + δ⁰_ρ(w) + (p choose 2) • Σ_i c_i [w_i, v_i]
  + Σ_{i<k} a_{ik} ([v_i, w_k] + [w_i, v_k])`,
where `c_i` and `a_{ik}` are the coordinates of `ρ`. The first correction is the defect of
additivity of `π` in degree zero (`TauCeti.gradedPow_add_zero`), the second the bilinear expansion
of the quadratic brackets `a_{ik} [ω_i, ω_k]`. -/
theorem basisModificationDeltaZero_add [Fintype X] (v w : X → gradedPiece p (freeProP p X) 0)
    (ρ : gradedPiece p (freeProP p X) 1) :
    basisModificationDeltaZero p X (v + w) ρ =
      basisModificationDeltaZero p X v ρ + basisModificationDeltaZero p X w ρ +
        p.choose 2 • ∑ i, (degreeOneBasis p X).repr ρ (Sum.inl i) •
          gradedBracket p (freeProP p X) 0 0 (w i) (v i) +
        ∑ ij : {ij : X × X // ij.1 < ij.2}, (degreeOneBasis p X).repr ρ (Sum.inr ij) •
          (gradedBracket p (freeProP p X) 0 0 (v ij.1.1) (w ij.1.2) +
            gradedBracket p (freeProP p X) 0 0 (w ij.1.1) (v ij.1.2)) := by
  simp only [basisModificationDeltaZero_apply, Pi.add_apply, gradedPow_add_zero, map_add,
    AddMonoidHom.add_apply, smul_add, smul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.smul_sum, smul_comm (p.choose 2)]
  abel

/-- **The polarization identity for odd `p`**: `π` is additive in degree zero, so only the bracket
part of `ρ` obstructs the additivity of `δ⁰`:
`δ⁰_ρ(v + w) = δ⁰_ρ(v) + δ⁰_ρ(w) + Σ_{i<k} a_{ik} ([v_i, w_k] + [w_i, v_k])`. -/
theorem basisModificationDeltaZero_add_of_odd [Fintype X] (hp : Odd p)
    (v w : X → gradedPiece p (freeProP p X) 0) (ρ : gradedPiece p (freeProP p X) 1) :
    basisModificationDeltaZero p X (v + w) ρ =
      basisModificationDeltaZero p X v ρ + basisModificationDeltaZero p X w ρ +
        ∑ ij : {ij : X × X // ij.1 < ij.2}, (degreeOneBasis p X).repr ρ (Sum.inr ij) •
          (gradedBracket p (freeProP p X) 0 0 (v ij.1.1) (w ij.1.2) +
            gradedBracket p (freeProP p X) 0 0 (w ij.1.1) (v ij.1.2)) := by
  rw [basisModificationDeltaZero_add, choose_two_nsmul_gradedPiece_eq_zero_of_odd hp]
  abel

/-- **The polarization identity for `p = 2`**: the `2`-power part of `ρ` contributes the brackets
`Σ_i c_i [v_i, w_i]` of the two families, and the bracket part its bilinear expansion:
`δ⁰_ρ(v + w) = δ⁰_ρ(v) + δ⁰_ρ(w) + Σ_i c_i [v_i, w_i]
  + Σ_{i<k} a_{ik} ([v_i, w_k] + [w_i, v_k])`. -/
theorem basisModificationDeltaZero_add_of_two [Fintype X] (hp : p = 2)
    (v w : X → gradedPiece p (freeProP p X) 0) (ρ : gradedPiece p (freeProP p X) 1) :
    basisModificationDeltaZero p X (v + w) ρ =
      basisModificationDeltaZero p X v ρ + basisModificationDeltaZero p X w ρ +
        ∑ i, (degreeOneBasis p X).repr ρ (Sum.inl i) •
          gradedBracket p (freeProP p X) 0 0 (v i) (w i) +
        ∑ ij : {ij : X × X // ij.1 < ij.2}, (degreeOneBasis p X).repr ρ (Sum.inr ij) •
          (gradedBracket p (freeProP p X) 0 0 (v ij.1.1) (w ij.1.2) +
            gradedBracket p (freeProP p X) 0 0 (w ij.1.1) (v ij.1.2)) := by
  subst hp
  -- Since `gr_1(F)` is killed by `2`, `[w_i, v_i] = -[v_i, w_i] = [v_i, w_i]`.
  have hswap (i : X) : gradedBracket 2 (freeProP 2 X) 0 0 (w i) (v i) =
      gradedBracket 2 (freeProP 2 X) 0 0 (v i) (w i) := by
    have h := gradedCast_gradedBracket_swap (v i) (w i)
    rw [gradedCast_rfl] at h
    rw [h, neg_eq_iff_add_eq_zero]
    exact (two_nsmul _).symm.trans (nsmul_gradedPiece_eq_zero _)
  simp only [basisModificationDeltaZero_add, Nat.choose_self, one_nsmul, hswap]

/-! ### The quadratic term is not an artifact -/

/-- **A basis modification moving a bracket class by a quadratic term.** In `F = freeProP p (Fin 2)`
the modification `x_0 ↦ x_0 * x_1`, `x_1 ↦ x_1 * x_0`, with classes `ω = (ξ_1, ξ_0)`, has
deviation `δ⁰_ρ(ω) = -ρ` at the bracket class `ρ = [ξ_0, ξ_1]`: the terms of `δ⁰_ρ(ω)` linear in
`ω` are `[ξ_1, ξ_1] - [ξ_0, ξ_0] = 0`, and the quadratic term is `[ξ_1, ξ_0] = -[ξ_0, ξ_1]`. The
induced map `θ_*` therefore sends `ρ` to `ρ + δ⁰_ρ(ω) = 0`, as `[ξ_0 + ξ_1, ξ_1 + ξ_0] = 0`
confirms. For `p = 2` the class `-ρ` is nonzero (`TauCeti.gradedBracket_freeProP_two_ne_zero`),
so the quadratic term of `δ⁰` cannot be dropped. -/
theorem basisModificationDeltaZero_gradedBracket_gradedMkZero_fin_two :
    basisModificationDeltaZero p (Fin 2)
        ![gradedMkZero p (freeProP p (Fin 2)) (of 1), gradedMkZero p (freeProP p (Fin 2)) (of 0)]
        (gradedBracket p (freeProP p (Fin 2)) 0 0 (gradedMkZero p (freeProP p (Fin 2)) (of 0))
          (gradedMkZero p (freeProP p (Fin 2)) (of 1))) =
      -gradedBracket p (freeProP p (Fin 2)) 0 0 (gradedMkZero p (freeProP p (Fin 2)) (of 0))
        (gradedMkZero p (freeProP p (Fin 2)) (of 1)) := by
  have h := basisModificationDeltaZero_degreeOneBasis_inr (p := p)
    ![gradedMkZero p (freeProP p (Fin 2)) (of 1), gradedMkZero p (freeProP p (Fin 2)) (of 0)]
    ⟨(0, 1), by decide⟩
  rw [degreeOneBasis_apply, degreeOneFamily_inr] at h
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, gradedBracket_self, sub_self,
    zero_add] at h
  rw [h]
  have hs := gradedCast_gradedBracket_swap (gradedMkZero p (freeProP p (Fin 2)) (of 0))
    (gradedMkZero p (freeProP p (Fin 2)) (of 1))
  rwa [gradedCast_rfl] at hs

end TauCeti.freeProP
