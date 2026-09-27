/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.Deviation
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Graded

/-!
# Basis modifications of a free pro-`p` group and the maps `δ`

Let `F = freeProP p X` be the free pro-`p` group on a finite linearly ordered type `X`, with
canonical generators `x_i = freeProP.of i`, and let `λ_k = λ_k(F)` be its lower `p`-series. A
family `w : X → λ_m(F)` defines the **basis modification** `θ_w : F → F`, `x_i ↦ x_i * w_i`
(`TauCeti.freeProP.basisModification`). It is congruent to the identity modulo `λ_m`, so for a
relator `r ∈ λ_1(F)` it moves `r` inside its coset by the element `r⁻¹ * θ_w r ∈ λ_{m+1}(F)`,
whose class in `gr_{m+1}(F)` is the graded deviation `D_1 ρ` of `θ_w` (`TauCeti.gradedDeviation`)
on the class `ρ ∈ gr_1(F)` of `r`.

For `m ≥ 1` that class is given by the **basis-modification map**
`δ = TauCeti.freeProP.basisModificationDelta`: writing `ρ` in the standard basis
`TauCeti.freeProP.degreeOneBasis` as `ρ = Σ_i c_i π ξ_i + Σ_{i<k} a_{ik} [ξ_i, ξ_k]`, where
`ξ_i ∈ gr_0(F)` is the class of `x_i`, and writing `ω_i ∈ gr_m(F)` for the class of `w_i`, the
class of `r⁻¹ * θ_w r` in `gr_{m+1}(F)` is

  `δ(ω) = Σ_i c_i (π ω_i + (p choose 2) • [ω_i, ξ_i])
          + Σ_{i<k} a_{ik} ([ω_i, ξ_k] - [ω_k, ξ_i])`,

an `𝔽_p`-linear function of the classes `ω_i` alone, and `𝔽_p`-linear in `ρ` as well. The bracket
part is the derivative of the commutator part of `ρ` in the direction `ω`, and for odd `p` the
`p`-power part contributes `Σ_i c_i π ω_i`. For `p = 2` the `p`-power part contributes in addition
the brackets `Σ_i c_i [ω_i, ξ_i]`: the square of `x_i * w_i` is `x_i ^ 2 * w_i ^ 2 * ⁅w_i, x_i⁆`
up to `λ_{m+2}(F)`, and the commutator `⁅w_i, x_i⁆` lies in `λ_{m+1}(F)` and may have a nonzero
class in `gr_{m+1}(F)`. That term is the trace, in every degree, of the failure of additivity of
`π` on `gr_0(F)` at `p = 2`.

The image of `δ` is the subspace of `gr_{m+1}(F)` that the successive-approximation arguments of
the classification of Demushkin groups compare with `gr_{m+1}(F)`; there `m + 1` is the modulus of
the normal-form congruence, and the classes `ω_i` are the level-`m` basis corrections.

## Main definitions

* `TauCeti.freeProP.basisModification`: the endomorphism `θ_w : F → F`, `x_i ↦ x_i * w_i`.
* `TauCeti.freeProP.basisModificationDelta`: for `m ≥ 1`, the `𝔽_p`-bilinear map
  `δ : gr_1(F) → gr_m(F)^X → gr_{m+1}(F)`, `(ρ, ω) ↦ δ_ρ(ω)`.

## Main results

* `TauCeti.freeProP.inv_mul_basisModification_mem_pLowerCentralSeries`: `θ_w` is congruent to the
  identity modulo `λ_m(F)`.
* `TauCeti.freeProP.gradedDeviation_basisModification`,
  `TauCeti.freeProP.gradedMk_inv_mul_basisModification`: the class of `r⁻¹ * θ_w r` in
  `gr_{m+1}(F)` is `δ(ω)`; in particular it depends only on the classes `ω_i`.

## References

* J. Labute, *Classification of Demushkin groups*, Canadian J. Math. 19 (1967), §3,
  Proposition 5.
-/

public section

namespace TauCeti.freeProP

open Subgroup
open scoped commutatorElement

universe u

variable {p : ℕ} {X : Type u} {m : ℕ}

/-! ### The basis modification `x_i ↦ x_i * w_i` -/

/-- **The basis modification** `θ_w : F → F`, `x_i ↦ x_i * w_i`, of the free pro-`p` group
`F = freeProP p X` by a family `w : X → λ_m(F)`. It is congruent to the identity modulo `λ_m(F)`
(`TauCeti.freeProP.inv_mul_basisModification_mem_pLowerCentralSeries`). -/
noncomputable def basisModification (w : X → pLowerCentralSeries p (freeProP p X) m) :
    freeProP p X →ₜ* freeProP p X :=
  lift (isProP_freeProP p X) fun i ↦ of i * (w i : freeProP p X)

@[simp]
theorem basisModification_of (w : X → pLowerCentralSeries p (freeProP p X) m) (i : X) :
    basisModification w (of i) = of i * (w i : freeProP p X) :=
  lift_of _ _ i

/-- **The basis modification is congruent to the identity modulo `λ_m(F)`.** -/
theorem inv_mul_basisModification_mem_pLowerCentralSeries
    (w : X → pLowerCentralSeries p (freeProP p X) m) (g : freeProP p X) :
    g⁻¹ * basisModification w g ∈ pLowerCentralSeries p (freeProP p X) m := by
  -- The quotient by the closed subgroup `λ_m(F)` is Hausdorff, so two continuous homomorphisms
  -- into it agreeing on the generators are equal.
  have : IsClosed ((pLowerCentralSeries p (freeProP p X) m : Subgroup (freeProP p X)) :
      Set (freeProP p X)) :=
    isClosed_pLowerCentralSeries m
  have h : (⟨QuotientGroup.mk' (pLowerCentralSeries p (freeProP p X) m),
        QuotientGroup.continuous_mk⟩ : freeProP p X →ₜ* _).comp (basisModification w) =
      ⟨QuotientGroup.mk' _, QuotientGroup.continuous_mk⟩ :=
    hom_ext fun i ↦ by
      rw [ContinuousMonoidHom.coe_comp, Function.comp_apply, basisModification_of]
      exact QuotientGroup.mk_mul_of_mem _ (w i).2
  have hg : ((basisModification w g : freeProP p X) :
      freeProP p X ⧸ pLowerCentralSeries p (freeProP p X) m) = g :=
    DFunLike.congr_fun h g
  exact QuotientGroup.eq.mp hg.symm

/-- **The deviation of the basis modification on a generator class** is the class of the
modification: `D_0 ξ_i = ω_i` in `gr_m(F)`, where `ξ_i` and `ω_i` are the classes of `x_i` and
`w_i`. -/
theorem gradedDeviation_basisModification_gradedMkZero_of
    (w : X → pLowerCentralSeries p (freeProP p X) m) (i : X) :
    gradedDeviation (basisModification w).toMonoidHom (basisModification w).continuous
        (inv_mul_basisModification_mem_pLowerCentralSeries w) 0
        (gradedMkZero p (freeProP p X) (of i)) =
      gradedMk p (freeProP p X) m (w i) := by
  rw [gradedDeviation_gradedMkZero]
  congr 1
  exact Subtype.ext (by simp)

/-! ### The maps `δ` -/

section Delta

variable [Fact p.Prime] [Finite X] [LinearOrder X]

variable (p X) in
/-- **The basis-modification map `δ`**, for `m ≥ 1`: the `𝔽_p`-bilinear map
`gr_1(F) → gr_m(F)^X → gr_{m+1}(F)` sending a class `ρ ∈ gr_1(F)` and a family `v` to

  `δ_ρ(v) = Σ_i c_i (π v_i + (p choose 2) • [v_i, ξ_i]) + Σ_{i<k} a_{ik} ([v_i, ξ_k] - [v_k, ξ_i])`

where `c_i` and `a_{ik}` are the coordinates of `ρ` in the standard basis
`TauCeti.freeProP.degreeOneBasis` of `gr_1(F)`, that is
`ρ = Σ_i c_i π ξ_i + Σ_{i<k} a_{ik} [ξ_i, ξ_k]` with `ξ_i ∈ gr_0(F)` the class of `x_i`. It is
defined by its values on that basis
(`TauCeti.freeProP.basisModificationDelta_degreeOneBasis_inl`,
`TauCeti.freeProP.basisModificationDelta_degreeOneBasis_inr`), and its value at a general `ρ` is
`TauCeti.freeProP.basisModificationDelta_apply`. For a relator `r ∈ λ_1(F)` with class `ρ`, and
`w : X → λ_m(F)` with classes `v_i = ω_i`, `δ_ρ(v)` is the class in `gr_{m+1}(F)` of
`r⁻¹ * θ_w r`, the amount by which the basis modification `θ_w` moves `r`
(`TauCeti.freeProP.gradedMk_inv_mul_basisModification`). -/
noncomputable def basisModificationDelta (hm : 1 ≤ m) :
    gradedPiece p (freeProP p X) 1 →ₗ[ZMod p]
      (X → gradedPiece p (freeProP p X) m) →ₗ[ZMod p] gradedPiece p (freeProP p X) (m + 1) :=
  (degreeOneBasis p X).constr (ZMod p) <| Sum.elim
    (fun i ↦ ((gradedPowAddMonoidHom p (freeProP p X) hm).toZModLinearMap p +
        p.choose 2 • (gradedBracketLinear p (freeProP p X) m 0).flip
          (gradedMkZero p (freeProP p X) (of i))) ∘ₗ
      LinearMap.proj i)
    fun ij ↦ (gradedBracketLinear p (freeProP p X) m 0).flip
        (gradedMkZero p (freeProP p X) (of ij.1.2)) ∘ₗ LinearMap.proj ij.1.1 -
      (gradedBracketLinear p (freeProP p X) m 0).flip
        (gradedMkZero p (freeProP p X) (of ij.1.1)) ∘ₗ LinearMap.proj ij.1.2

/-- **The value of `δ` on a `p`-power basis vector**:
`δ_{π ξ_i}(v) = π v_i + (p choose 2) • [v_i, ξ_i]`. -/
theorem basisModificationDelta_degreeOneBasis_inl (hm : 1 ≤ m) (i : X)
    (v : X → gradedPiece p (freeProP p X) m) :
    basisModificationDelta p X hm (degreeOneBasis p X (Sum.inl i)) v =
      gradedPow p (freeProP p X) m (v i) +
        p.choose 2 • gradedBracket p (freeProP p X) m 0 (v i)
          (gradedMkZero p (freeProP p X) (of i)) := by
  rw [basisModificationDelta, Module.Basis.constr_basis]
  simp

/-- **The value of `δ` on a bracket basis vector**:
`δ_{[ξ_i, ξ_k]}(v) = [v_i, ξ_k] - [v_k, ξ_i]`. -/
theorem basisModificationDelta_degreeOneBasis_inr (hm : 1 ≤ m)
    (ij : {ij : X × X // ij.1 < ij.2}) (v : X → gradedPiece p (freeProP p X) m) :
    basisModificationDelta p X hm (degreeOneBasis p X (Sum.inr ij)) v =
      gradedBracket p (freeProP p X) m 0 (v ij.1.1) (gradedMkZero p (freeProP p X) (of ij.1.2)) -
        gradedBracket p (freeProP p X) m 0 (v ij.1.2)
          (gradedMkZero p (freeProP p X) (of ij.1.1)) := by
  rw [basisModificationDelta, Module.Basis.constr_basis]
  simp

/-- **The value of `δ`**: with `ρ = Σ_i c_i π ξ_i + Σ_{i<k} a_{ik} [ξ_i, ξ_k]`,
`δ_ρ(v) = Σ_i c_i (π v_i + (p choose 2) • [v_i, ξ_i]) + Σ_{i<k} a_{ik} ([v_i, ξ_k] - [v_k, ξ_i])`.
-/
theorem basisModificationDelta_apply [Fintype X] (hm : 1 ≤ m) (ρ : gradedPiece p (freeProP p X) 1)
    (v : X → gradedPiece p (freeProP p X) m) :
    basisModificationDelta p X hm ρ v =
      ∑ i, (degreeOneBasis p X).repr ρ (Sum.inl i) •
          (gradedPow p (freeProP p X) m (v i) +
            p.choose 2 • gradedBracket p (freeProP p X) m 0 (v i)
              (gradedMkZero p (freeProP p X) (of i))) +
        ∑ ij : {ij : X × X // ij.1 < ij.2}, (degreeOneBasis p X).repr ρ (Sum.inr ij) •
          (gradedBracket p (freeProP p X) m 0 (v ij.1.1)
              (gradedMkZero p (freeProP p X) (of ij.1.2)) -
            gradedBracket p (freeProP p X) m 0 (v ij.1.2)
              (gradedMkZero p (freeProP p X) (of ij.1.1))) := by
  conv_lhs => rw [← (degreeOneBasis p X).sum_repr ρ]
  simp only [Fintype.sum_sum_type, map_add, LinearMap.add_apply, map_sum, LinearMap.sum_apply,
    map_smul, LinearMap.smul_apply, basisModificationDelta_degreeOneBasis_inl,
    basisModificationDelta_degreeOneBasis_inr]

/-- **The class of the moved relator is `δ_ρ(ω)`.** For `m ≥ 1`, `w : X → λ_m(F)` and
`ρ ∈ gr_1(F)`, the graded deviation of the basis modification `θ_w` on `ρ` is `δ_ρ(ω)`, where
`ω_i ∈ gr_m(F)` is the class of `w_i`. -/
theorem gradedDeviation_basisModification (hm : 1 ≤ m)
    (w : X → pLowerCentralSeries p (freeProP p X) m) (ρ : gradedPiece p (freeProP p X) 1) :
    gradedDeviation (basisModification w).toMonoidHom (basisModification w).continuous
        (inv_mul_basisModification_mem_pLowerCentralSeries w) 1 ρ =
      basisModificationDelta p X hm ρ fun i ↦ gradedMk p (freeProP p X) m (w i) := by
  -- Both sides are linear in `ρ`, and they agree on the standard basis of `gr_1(F)` by the
  -- Leibniz rule and the `π`-compatibility of the deviation.
  have key : (gradedDeviation (basisModification w).toMonoidHom (basisModification w).continuous
      (inv_mul_basisModification_mem_pLowerCentralSeries w) 1).toZModLinearMap p =
        (basisModificationDelta p X hm).flip fun i ↦ gradedMk p (freeProP p X) m (w i) := by
    refine (degreeOneBasis p X).ext fun b ↦ ?_
    rw [LinearMap.flip_apply, AddMonoidHom.coe_toZModLinearMap]
    rcases b with i | ij
    · rw [basisModificationDelta_degreeOneBasis_inl, degreeOneBasis_apply, degreeOneFamily_inl,
        gradedDeviation_gradedPow_zero, gradedDeviation_basisModification_gradedMkZero_of]
    · rw [basisModificationDelta_degreeOneBasis_inr, degreeOneBasis_apply, degreeOneFamily_inr,
        gradedDeviation_gradedBracket_zero _ _ _ hm,
        gradedDeviation_basisModification_gradedMkZero_of,
        gradedDeviation_basisModification_gradedMkZero_of]
  exact LinearMap.congr_fun key ρ

/-- **The basis modification `θ_w` moves a relator `r ∈ λ_1(F)` by `δ_ρ(ω)`**: the class in
`gr_{m+1}(F)` of `r⁻¹ * θ_w r` is `δ_ρ(ω)`, for `m ≥ 1`, where `ρ ∈ gr_1(F)` is the class of `r`
and `ω_i ∈ gr_m(F)` the class of `w_i`. In particular that class depends only on the classes
`ω_i` of the modifications. -/
@[simp]
theorem gradedMk_inv_mul_basisModification (hm : 1 ≤ m)
    (w : X → pLowerCentralSeries p (freeProP p X) m)
    (r : pLowerCentralSeries p (freeProP p X) 1) :
    gradedMk p (freeProP p X) (m + 1) ⟨(r : freeProP p X)⁻¹ * basisModification w r,
        inv_mul_apply_mem_pLowerCentralSeries (basisModification w).toMonoidHom
          (basisModification w).continuous
          (inv_mul_basisModification_mem_pLowerCentralSeries w) r.2⟩ =
      basisModificationDelta p X hm (gradedMk p (freeProP p X) 1 r)
        fun i ↦ gradedMk p (freeProP p X) m (w i) := by
  have h := gradedDeviation_basisModification hm w (gradedMk p (freeProP p X) 1 r)
  rwa [gradedDeviation_gradedMk] at h

end Delta

end TauCeti.freeProP
