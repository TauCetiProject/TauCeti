/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.Deviation
public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.Pow
public import TauCeti.Topology.Algebra.Group.Profinite.Free.DegreeOneForm
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Graded
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.OrzechProperty

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

For `p = 2` those arguments compare `gr_j(F)` with the image of `δ` enlarged by one further
subspace, the **tail** `T_j(ρ)` (`TauCeti.freeProP.basisModificationTail`): the span in `gr_j(F)`
of the iterated `p`-powers `π^j ξ_i` over the generators whose coefficient `c_i` in `ρ` vanishes,
which are the generators contributing no `π`-term to `δ`. For the dyadic relator
`x₁² x₂^{2^f} ⁅x₂, x₃⁆ ⋯` with `f ≥ 2` these are `x₂, …, x_n`.

Collecting the brackets of `δ` by their degree-`m` entry gives the **partial derivatives**
`∂_i ρ ∈ gr_0(F)` (`TauCeti.freeProP.degreeOneDeriv`), the `i`-th row of the matrix
`(a_{ik})` completed skew-symmetrically with diagonal `(p choose 2) c_i`, and the formula
`δ_ρ(ω) = π (Σ_i c_i ω_i) + Σ_i [ω_i, ∂_i ρ]`. The image of `δ_ρ` is then computed under the
hypothesis that the derivatives `∂_i ρ` span `gr_0(F)`, which is the nondegeneracy of the form
`(a_{ik})` completed with that diagonal, and holds for every Demushkin relator in normal form: the
coordinates of `∂_i ρ` in the basis of generator classes form the `i`-th row of the matrix of the
degree-one form `TauCeti.freeProP.degreeOneForm ρ` in the dual basis of the generators, so the
derivatives span exactly when that form is nondegenerate.
The **span statements** are: if all `c_i = 0`, then `Im δ_ρ` is the span of the brackets
`[gr_m(F), gr_0(F)]` and `gr_{m+1}(F) = Im δ_ρ + T_{m+1}(ρ)` for every `m ≥ 1`, the tail being
spanned by all the `π^{m+1} ξ_i`, so that `Im δ_ρ` consists exactly of the classes of the
elements of `λ_{m+1}(F)` all of whose exponent sums are divisible by `p ^ (m + 2)`; and if `p` is
odd and some `c_i ≠ 0`, then `gr_{m+1}(F) = Im δ_ρ` for every `m ≥ 1`. The first case is that of
the relators `x₁^q (x₁, x₂) (x₃, x₄) ⋯` with `q ≠ p`, whose `p`-power part lies in `λ_2(F)`, and
the second that of `x₁^p (x₁, x₂) (x₃, x₄) ⋯` at odd `p`. Both rest on the spanning of
`gr_{m+1}(F)` by `π gr_m(F)` and `[gr_m(F), gr_0(F)]` and on the naturality `π ∘ δ_ρ = δ_ρ ∘ π`,
which carries the image of `δ_ρ` in degree `m` into its image in degree `m + 1`. For `p = 2` and a
class with a `p`-power part the odd-`p` argument breaks down at the degree-zero defect of `π`. It
survives when a single generator `x_{i₀}` carries the `2`-power part and `ξ_{i₀}` occurs in no
bracket of `ρ`: then again `gr_{m+1}(F) = Im δ_ρ + T_{m+1}(ρ)`, the tail being spanned by the
`π^{m+1} ξ_i` with `i ≠ i₀`. That is the case of the dyadic relators `x₁² x₂^{2^f} (x₂, x₃) ⋯` of
odd rank, whose level `f` is the free parameter the tail accounts for. The even-rank dyadic
relators `x₁^{2+α} (x₁, x₂) x₃^{2^f} ⋯`, where `ξ₁` occurs in a bracket, are not treated here.

## Main definitions

* `TauCeti.freeProP.basisModification`: the endomorphism `θ_w : F → F`, `x_i ↦ x_i * w_i`.
* `TauCeti.freeProP.basisModificationDelta`: for `m ≥ 1`, the `𝔽_p`-bilinear map
  `δ : gr_1(F) → gr_m(F)^X → gr_{m+1}(F)`, `(ρ, ω) ↦ δ_ρ(ω)`.
* `TauCeti.freeProP.basisModificationTail`: the tail `T_j(ρ) ≤ gr_j(F)`, spanned by the `π^j ξ_i`
  with `c_i = 0`.
* `TauCeti.freeProP.degreeOneDeriv`: the partial derivative `∂_i : gr_1(F) →ₗ[𝔽_p] gr_0(F)`.

## Main results

* `TauCeti.freeProP.inv_mul_basisModification_mem_pLowerCentralSeries`: `θ_w` is congruent to the
  identity modulo `λ_m(F)`.
* `TauCeti.freeProP.gradedDeviation_basisModification`,
  `TauCeti.freeProP.gradedMk_inv_mul_basisModification`: the class of `r⁻¹ * θ_w r` in
  `gr_{m+1}(F)` is `δ(ω)`; in particular it depends only on the classes `ω_i`.
* `TauCeti.freeProP.finrank_basisModificationTail`: `dim T_j(ρ)` is the number of indices `i`
  with `c_i = 0`.
* `TauCeti.freeProP.basisModificationTail_succ`: `T_{j+1}(ρ) = π(T_j(ρ))` for `j ≥ 1`.
* `TauCeti.freeProP.basisModificationDelta_eq_gradedPow_add_sum`,
  `TauCeti.freeProP.gradedPow_basisModificationDelta`:
  `δ_ρ(ω) = π (Σ_i c_i ω_i) + Σ_i [ω_i, ∂_i ρ]`, and `π (δ_ρ(ω)) = δ_ρ(π ω)`.
* `TauCeti.freeProP.degreeZeroBasis_repr_degreeOneDeriv`,
  `TauCeti.freeProP.span_range_degreeOneDeriv_eq_top_iff_nondegenerate_degreeOneForm`: the
  coordinates of `∂_i ρ` are the `i`-th row of the matrix of the degree-one form of `ρ`, so the
  derivatives span `gr_0(F)` exactly when that form is nondegenerate.
* `TauCeti.freeProP.range_basisModificationDelta_eq_span_of_repr_inl_eq_zero`,
  `TauCeti.freeProP.range_basisModificationDelta_sup_basisModificationTail_eq_top`: for a class
  without `p`-power part whose derivatives span `gr_0(F)`, `Im δ_ρ = [gr_m(F), gr_0(F)]` and
  `gr_{m+1}(F) = Im δ_ρ + T_{m+1}(ρ)`.
* `TauCeti.freeProP.gradedMk_mem_range_basisModificationDelta_iff`: for a class without `p`-power
  part whose derivatives span `gr_0(F)`, the class of `z ∈ λ_{m+1}(F)` lies in `Im δ_ρ` if and only
  if `p ^ (m + 2)` divides every exponent sum of `z`; so `Im δ_ρ` is the kernel of the map to
  `gr_{m+1}(F^{ab})`.
* `TauCeti.freeProP.range_basisModificationDelta_eq_top_of_odd`: for odd `p` and a class with a
  `p`-power part whose derivatives span `gr_0(F)`, `gr_{m+1}(F) = Im δ_ρ`.
* `TauCeti.freeProP.range_basisModificationDelta_sup_basisModificationTail_eq_top_two`: for
  `p = 2` and a class whose derivatives span `gr_0(F)` and whose `2`-power part sits on a single
  generator `x_{i₀}` not occurring in its brackets,
  `gr_{m+1}(F) = Im δ_ρ + T_{m+1}(ρ)`.

## References

* J. Labute, *Classification of Demushkin groups*, Canadian J. Math. 19 (1967), §3,
  Proposition 5 and the proof of Theorem 3.
-/

public section

namespace TauCeti.freeProP

open Subgroup Submodule
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

/-! ### The partial derivatives `∂_i` -/

section Deriv

variable [Fact p.Prime] [Finite X] [LinearOrder X]

variable (p X) in
/-- **The partial derivative `∂_i`** of a class in `gr_1(F)`: the `𝔽_p`-linear map
`gr_1(F) → gr_0(F)` given on the standard basis `TauCeti.freeProP.degreeOneBasis` by
`∂_i (π ξ_i) = (p choose 2) • ξ_i`, `∂_i (π ξ_j) = 0` for `j ≠ i`, `∂_i [ξ_i, ξ_k] = ξ_k`,
`∂_i [ξ_j, ξ_i] = -ξ_j` and `∂_i [ξ_j, ξ_k] = 0` when `i ∉ {j, k}`. For
`ρ = Σ_i c_i π ξ_i + Σ_{j<k} a_{jk} [ξ_j, ξ_k]` this is
`∂_i ρ = (p choose 2) c_i • ξ_i + Σ_{k>i} a_{ik} ξ_k - Σ_{j<i} a_{ji} ξ_j`, the `i`-th row of the
matrix of the form `(a_{jk})` completed skew-symmetrically, with diagonal `(p choose 2) c_i`,
read as a vector of `gr_0(F)`. The bracket terms of the basis-modification map are
`Σ_i [v_i, ∂_i ρ]` (`TauCeti.freeProP.basisModificationDelta_eq_gradedPow_add_sum`). -/
noncomputable def degreeOneDeriv (i : X) :
    gradedPiece p (freeProP p X) 1 →ₗ[ZMod p] gradedPiece p (freeProP p X) 0 :=
  (degreeOneBasis p X).constr (ZMod p) <| Sum.elim
    (fun j ↦ if j = i then p.choose 2 • gradedMkZero p (freeProP p X) (of i) else 0)
    fun jk ↦ (if jk.1.1 = i then gradedMkZero p (freeProP p X) (of jk.1.2) else 0) -
      if jk.1.2 = i then gradedMkZero p (freeProP p X) (of jk.1.1) else 0

/-- `∂_i` on the `p`-power basis vectors: `∂_i (π ξ_i) = (p choose 2) • ξ_i` and `∂_i (π ξ_j) = 0`
for `j ≠ i`. -/
theorem degreeOneDeriv_degreeOneBasis_inl (i j : X) :
    degreeOneDeriv p X i (degreeOneBasis p X (Sum.inl j)) =
      if j = i then p.choose 2 • gradedMkZero p (freeProP p X) (of i) else 0 := by
  rw [degreeOneDeriv, Module.Basis.constr_basis, Sum.elim_inl]

/-- `∂_i` on the bracket basis vectors: `∂_i [ξ_j, ξ_k] = ξ_k` if `j = i`, `-ξ_j` if `k = i`, and
`0` otherwise, for `j < k`. -/
theorem degreeOneDeriv_degreeOneBasis_inr (i : X) (jk : {ij : X × X // ij.1 < ij.2}) :
    degreeOneDeriv p X i (degreeOneBasis p X (Sum.inr jk)) =
      (if jk.1.1 = i then gradedMkZero p (freeProP p X) (of jk.1.2) else 0) -
        if jk.1.2 = i then gradedMkZero p (freeProP p X) (of jk.1.1) else 0 := by
  rw [degreeOneDeriv, Module.Basis.constr_basis, Sum.elim_inr]

/-- `∂_i (π ξ_i) = (p choose 2) • ξ_i`. -/
theorem degreeOneDeriv_gradedPow_gradedMkZero_of_self (i : X) :
    degreeOneDeriv p X i (gradedPow p (freeProP p X) 0 (gradedMkZero p (freeProP p X) (of i))) =
      p.choose 2 • gradedMkZero p (freeProP p X) (of i) := by
  have h := degreeOneDeriv_degreeOneBasis_inl (p := p) i i
  rwa [degreeOneBasis_apply, degreeOneFamily_inl, ite_eq_left rfl] at h

/-- `∂_i (π ξ_j) = 0` for `j ≠ i`. -/
theorem degreeOneDeriv_gradedPow_gradedMkZero_of_of_ne {i j : X} (hji : j ≠ i) :
    degreeOneDeriv p X i (gradedPow p (freeProP p X) 0 (gradedMkZero p (freeProP p X) (of j))) =
      0 := by
  have h := degreeOneDeriv_degreeOneBasis_inl (p := p) i j
  rwa [degreeOneBasis_apply, degreeOneFamily_inl, ite_eq_right hji] at h

/-- `∂_i [ξ_i, ξ_k] = ξ_k` for `i < k`. -/
theorem degreeOneDeriv_gradedBracket_gradedMkZero_of_left {i k : X} (hik : i < k) :
    degreeOneDeriv p X i (gradedBracket p (freeProP p X) 0 0
        (gradedMkZero p (freeProP p X) (of i)) (gradedMkZero p (freeProP p X) (of k))) =
      gradedMkZero p (freeProP p X) (of k) := by
  have h := degreeOneDeriv_degreeOneBasis_inr (p := p) i ⟨(i, k), hik⟩
  rwa [degreeOneBasis_apply, degreeOneFamily_inr, ite_eq_left rfl, ite_eq_right hik.ne',
    sub_zero] at h

/-- `∂_i [ξ_j, ξ_i] = -ξ_j` for `j < i`. -/
theorem degreeOneDeriv_gradedBracket_gradedMkZero_of_right {i j : X} (hji : j < i) :
    degreeOneDeriv p X i (gradedBracket p (freeProP p X) 0 0
        (gradedMkZero p (freeProP p X) (of j)) (gradedMkZero p (freeProP p X) (of i))) =
      -gradedMkZero p (freeProP p X) (of j) := by
  have h := degreeOneDeriv_degreeOneBasis_inr (p := p) i ⟨(j, i), hji⟩
  rwa [degreeOneBasis_apply, degreeOneFamily_inr, ite_eq_right hji.ne, ite_eq_left rfl,
    zero_sub] at h

/-- `∂_i [ξ_j, ξ_k] = 0` for `j < k` with `i ∉ {j, k}`. -/
theorem degreeOneDeriv_gradedBracket_gradedMkZero_of_of_ne {i j k : X} (hjk : j < k) (hj : j ≠ i)
    (hk : k ≠ i) :
    degreeOneDeriv p X i (gradedBracket p (freeProP p X) 0 0
        (gradedMkZero p (freeProP p X) (of j)) (gradedMkZero p (freeProP p X) (of k))) = 0 := by
  have h := degreeOneDeriv_degreeOneBasis_inr (p := p) i ⟨(j, k), hjk⟩
  rwa [degreeOneBasis_apply, degreeOneFamily_inr, ite_eq_right hj, ite_eq_right hk, sub_zero] at h

/-- **A class with spanning derivatives, in rank two.** In `F = freeProP p (Fin 2)` the
derivatives of the bracket class `[ξ_0, ξ_1]` are `∂_0 = ξ_1` and `∂_1 = -ξ_0`, which span
`gr_0(F)`. This is the class of the surface relation `(x₁, x₂)` of `ℤ_p × ℤ_p`. -/
theorem span_range_degreeOneDeriv_gradedBracket_gradedMkZero_fin_two :
    span (ZMod p) (Set.range fun i ↦ degreeOneDeriv p (Fin 2) i
      (gradedBracket p (freeProP p (Fin 2)) 0 0 (gradedMkZero p (freeProP p (Fin 2)) (of 0))
        (gradedMkZero p (freeProP p (Fin 2)) (of 1)))) = ⊤ := by
  have h0 := Submodule.subset_span (R := ZMod p) (Set.mem_range_self
    (f := fun i ↦ degreeOneDeriv p (Fin 2) i (gradedBracket p (freeProP p (Fin 2)) 0 0
      (gradedMkZero p (freeProP p (Fin 2)) (of 0)) (gradedMkZero p (freeProP p (Fin 2)) (of 1))))
    (1 : Fin 2))
  have h1 := Submodule.subset_span (R := ZMod p) (Set.mem_range_self
    (f := fun i ↦ degreeOneDeriv p (Fin 2) i (gradedBracket p (freeProP p (Fin 2)) 0 0
      (gradedMkZero p (freeProP p (Fin 2)) (of 0)) (gradedMkZero p (freeProP p (Fin 2)) (of 1))))
    (0 : Fin 2))
  rw [degreeOneDeriv_gradedBracket_gradedMkZero_of_right (show (0 : Fin 2) < 1 by decide)] at h0
  rw [degreeOneDeriv_gradedBracket_gradedMkZero_of_left (show (0 : Fin 2) < 1 by decide)] at h1
  rw [eq_top_iff, ← span_gradedMkZero_image_eq_top
    ((isTopologicallyFinitelyGenerated_freeProP p (Fin 2)).isOpen_pLowerCentralSeries Fact.out 1)
    (topologicalClosure_closure_range_of_eq_top p (Fin 2)), Submodule.span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  revert i
  exact Fin.forall_fin_two.mpr ⟨neg_mem_iff.mp h0, h1⟩

/-- **The basis-modification map through the partial derivatives**: for `m ≥ 1`,
`δ_ρ(v) = π (Σ_i c_i • v_i) + Σ_i [v_i, ∂_i ρ]`, where `c_i` is the coefficient of `π ξ_i` in
`ρ`. The `p`-power part of `ρ` contributes the single `p`-power `π (Σ_i c_i v_i)`, and all
brackets are collected in the derivatives. -/
theorem basisModificationDelta_eq_gradedPow_add_sum [Fintype X] (hm : 1 ≤ m)
    (ρ : gradedPiece p (freeProP p X) 1) (v : X → gradedPiece p (freeProP p X) m) :
    basisModificationDelta p X hm ρ v =
      gradedPow p (freeProP p X) m (∑ i, (degreeOneBasis p X).repr ρ (Sum.inl i) • v i) +
        ∑ i, gradedBracket p (freeProP p X) m 0 (v i) (degreeOneDeriv p X i ρ) := by
  -- Both sides are linear in `ρ`; compare them on the standard basis of `gr_1(F)`.
  have key : (basisModificationDelta p X hm).flip v =
      (gradedPowAddMonoidHom p (freeProP p X) hm).toZModLinearMap p ∘ₗ
          (∑ i, (Finsupp.lapply (Sum.inl i) ∘ₗ (degreeOneBasis p X).repr.toLinearMap).smulRight
            (v i)) +
        ∑ i, gradedBracketLinear p (freeProP p X) m 0 (v i) ∘ₗ degreeOneDeriv p X i := by
    refine (degreeOneBasis p X).ext fun b ↦ ?_
    simp only [LinearMap.flip_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sum_apply,
      LinearMap.smulRight_apply, LinearEquiv.coe_coe, Module.Basis.repr_self, Finsupp.lapply_apply,
      AddMonoidHom.coe_toZModLinearMap, gradedPowAddMonoidHom_apply, gradedBracketLinear_apply,
      Finsupp.single_apply]
    rcases b with j | jk
    · rw [basisModificationDelta_degreeOneBasis_inl]
      simp only [Sum.inl.injEq, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true, degreeOneDeriv_degreeOneBasis_inl]
      congr 1
      rw [Finset.sum_eq_single j (fun i _ hij ↦ by rw [ite_eq_right (Ne.symm hij), map_zero])
        (fun h ↦ (h (Finset.mem_univ j)).elim), ite_eq_left rfl, map_nsmul]
    · rw [basisModificationDelta_degreeOneBasis_inr]
      simp only [reduceCtorEq, ite_false, zero_smul, Finset.sum_const_zero, gradedPow_zero,
        zero_add, degreeOneDeriv_degreeOneBasis_inr, map_sub, Finset.sum_sub_distrib]
      congr 1
      · rw [Finset.sum_eq_single jk.1.1 (fun i _ hij ↦ by rw [ite_eq_right (Ne.symm hij), map_zero])
          (fun h ↦ (h (Finset.mem_univ _)).elim), ite_eq_left rfl]
      · rw [Finset.sum_eq_single jk.1.2 (fun i _ hij ↦ by rw [ite_eq_right (Ne.symm hij), map_zero])
          (fun h ↦ (h (Finset.mem_univ _)).elim), ite_eq_left rfl]
  have h := LinearMap.congr_fun key ρ
  simpa only [LinearMap.flip_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.smulRight_apply, LinearEquiv.coe_coe, Finsupp.lapply_apply,
    AddMonoidHom.coe_toZModLinearMap, gradedPowAddMonoidHom_apply, gradedBracketLinear_apply]
    using h

/-- **`δ` on a family proportional to a single class**: for `b : X → 𝔽_p` and `v ∈ gr_m(F)`,
`δ_ρ(b • v) = (Σ_i b_i c_i) • π v + [v, Σ_i b_i • ∂_i ρ]`. -/
theorem basisModificationDelta_smul [Fintype X] (hm : 1 ≤ m) (ρ : gradedPiece p (freeProP p X) 1)
    (b : X → ZMod p) (v : gradedPiece p (freeProP p X) m) :
    basisModificationDelta p X hm ρ (fun i ↦ b i • v) =
      (∑ i, b i * (degreeOneBasis p X).repr ρ (Sum.inl i)) • gradedPow p (freeProP p X) m v +
        gradedBracket p (freeProP p X) m 0 v (∑ i, b i • degreeOneDeriv p X i ρ) := by
  rw [basisModificationDelta_eq_gradedPow_add_sum]
  congr 1
  · have h : ∑ i, (degreeOneBasis p X).repr ρ (Sum.inl i) • b i • v =
        (∑ i, b i * (degreeOneBasis p X).repr ρ (Sum.inl i)) • v := by
      simp only [smul_smul, Finset.sum_smul, mul_comm]
    rw [h, ← gradedPowAddMonoidHom_apply hm, ← AddMonoidHom.coe_toZModLinearMap p,
      map_smul, AddMonoidHom.coe_toZModLinearMap, gradedPowAddMonoidHom_apply]
  · simp only [← gradedBracketLinear_apply, map_sum, map_smul, LinearMap.smul_apply]

/-- **`δ` on a family supported at one generator**: for `v ∈ gr_m(F)`,
`δ_ρ(single i v) = c_i • π v + [v, ∂_i ρ]`, where `c_i` is the coefficient of `π ξ_i` in `ρ`. -/
@[simp]
theorem basisModificationDelta_single [DecidableEq X] (hm : 1 ≤ m)
    (ρ : gradedPiece p (freeProP p X) 1) (i : X) (v : gradedPiece p (freeProP p X) m) :
    basisModificationDelta p X hm ρ (Pi.single i v) =
      (degreeOneBasis p X).repr ρ (Sum.inl i) • gradedPow p (freeProP p X) m v +
        gradedBracket p (freeProP p X) m 0 v (degreeOneDeriv p X i ρ) := by
  cases nonempty_fintype X
  -- `single i v` is the proportional family with indicator coefficients `single i 1`.
  have h : (Pi.single i v : X → gradedPiece p (freeProP p X) m) =
      fun j ↦ Pi.single (M := fun _ ↦ ZMod p) i 1 j • v := by
    funext j
    simp only [Pi.single_apply, ite_smul, one_smul, zero_smul]
  rw [h, basisModificationDelta_smul]
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- **Naturality of `δ` under `π`**: for `m ≥ 1`, `π (δ_ρ(v)) = δ_ρ(π v)`, where `δ_ρ` on the left
is the map in degree `m` and on the right the map in degree `m + 1`. -/
theorem gradedPow_basisModificationDelta (hm : 1 ≤ m)
    (ρ : gradedPiece p (freeProP p X) 1) (v : X → gradedPiece p (freeProP p X) m) :
    gradedPow p (freeProP p X) (m + 1) (basisModificationDelta p X hm ρ v) =
      basisModificationDelta p X (m := m + 1) (by omega) ρ
        fun i ↦ gradedPow p (freeProP p X) m (v i) := by
  cases nonempty_fintype X
  rw [basisModificationDelta_eq_gradedPow_add_sum, basisModificationDelta_eq_gradedPow_add_sum,
    gradedPow_add_of_one_le (by omega)]
  congr 1
  · congr 1
    rw [← gradedPowAddMonoidHom_apply hm, ← AddMonoidHom.coe_toZModLinearMap p, map_sum]
    simp only [map_smul, AddMonoidHom.coe_toZModLinearMap, gradedPowAddMonoidHom_apply]
  · rw [← gradedPowAddMonoidHom_apply (by omega : 1 ≤ m + 1), map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [gradedPowAddMonoidHom_apply, gradedPow_gradedBracket_left_zero hm]

end Deriv

/-! ### The derivatives and the degree-one form -/

section DerivForm

variable [Fact p.Prime] [Finite X] [LinearOrder X]

-- Preferring the ring path keeps a single additive structure on `ZMod p`, so that the continuous
-- dual is an additive group over the module structure of `ZMod p` on itself.
attribute [local instance 2000] Ring.toAddCommGroup

/-- **The coordinates of the partial derivatives are the matrix of the degree-one form**: the
`k`-th coordinate of `∂_i ρ` in the basis of generator classes of `gr_0(F)` is `B_ρ(χ_i, χ_k)`, the
`(i, k)` entry of the matrix of the degree-one form of `ρ` in the dual basis of the generators. -/
@[simp]
theorem degreeZeroBasis_repr_degreeOneDeriv (ρ : gradedPiece p (freeProP p X) 1) (i k : X) :
    (degreeZeroBasis p X).repr (degreeOneDeriv p X i ρ) k =
      degreeOneForm ρ (dualBasis p X i) (dualBasis p X k) := by
  -- Both sides are linear in `ρ`; compare them on the standard basis of `gr_1(F)`, where both are
  -- read off the coordinates of the basis vector.
  have key : (degreeZeroBasis p X).coord k ∘ₗ degreeOneDeriv p X i =
      ((degreeOneForm (p := p) (X := X)).flip (dualBasis p X i)).flip (dualBasis p X k) := by
    refine (degreeOneBasis p X).ext fun b ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.flip_apply]
    rcases b with j | ⟨⟨a, b⟩, hab⟩
    · rw [degreeOneDeriv_degreeOneBasis_inl]
      rcases lt_trichotomy i k with hik | rfl | hki
      · rw [degreeOneForm_dualBasis_of_lt _ hik, Module.Basis.repr_self]
        split_ifs <;> subst_vars <;>
          simp_all [← degreeZeroBasis_apply, Module.Basis.repr_self, hik.ne]
      · rw [degreeOneForm_dualBasis_self, Module.Basis.repr_self]
        split_ifs <;> subst_vars <;> simp_all [← degreeZeroBasis_apply, Module.Basis.repr_self]
      · rw [degreeOneForm_dualBasis_of_gt _ hki, Module.Basis.repr_self]
        split_ifs <;> subst_vars <;>
          simp_all [← degreeZeroBasis_apply, Module.Basis.repr_self, hki.ne']
    · dsimp only at hab
      rw [degreeOneDeriv_degreeOneBasis_inr, map_sub]
      simp only [Module.Basis.coord_apply]
      rcases lt_trichotomy i k with hik | rfl | hki
      · rw [degreeOneForm_dualBasis_of_lt _ hik, Module.Basis.repr_self]
        -- If `b = i` then `a < b = i < k`, so the coordinate of `ξ_a` at `k` vanishes.
        have hak : b = i → a ≠ k := fun hb ha ↦ ((hab.trans_eq hb).trans hik).ne ha
        split_ifs <;> subst_vars <;>
          simp_all [← degreeZeroBasis_apply, Module.Basis.repr_self, Finsupp.single_apply, hik.ne]
      · rw [degreeOneForm_dualBasis_self, Module.Basis.repr_self]
        split_ifs <;> subst_vars <;> simp_all [← degreeZeroBasis_apply, Module.Basis.repr_self]
      · rw [degreeOneForm_dualBasis_of_gt _ hki, Module.Basis.repr_self]
        -- If `a = i` then `k < i = a < b`, so the coordinate of `ξ_b` at `k` vanishes.
        have hbk : a = i → b ≠ k := fun ha hb ↦ ((hki.trans_eq ha.symm).trans hab).ne hb.symm
        split_ifs <;> subst_vars <;>
          simp_all [← degreeZeroBasis_apply, Module.Basis.repr_self, Finsupp.single_apply, hki.ne']
  have := LinearMap.congr_fun key ρ
  simpa only [LinearMap.comp_apply, LinearMap.flip_apply, Module.Basis.coord_apply] using this

/-- **The partial derivatives span `gr_0(F)` exactly when the degree-one form is nondegenerate.**
The coordinates of `∂_i ρ` form the `i`-th row of the matrix of `B_ρ` in the dual basis of the
generators, so the derivatives span exactly when that matrix is invertible. This is the spanning
hypothesis of the span statements below, and it holds for every Demushkin relator. -/
theorem span_range_degreeOneDeriv_eq_top_iff_nondegenerate_degreeOneForm
    (ρ : gradedPiece p (freeProP p X) 1) :
    span (ZMod p) (Set.range fun i ↦ degreeOneDeriv p X i ρ) = ⊤ ↔
      (degreeOneForm ρ).Nondegenerate := by
  cases nonempty_fintype X
  set M := LinearMap.BilinForm.toMatrix (dualBasis p X) (degreeOneForm ρ) with hM
  -- The derivatives span exactly when `b ↦ Σ_i b_i ∂_i ρ` is onto, and in the coordinates of the
  -- generator classes that map is `b ↦ b ᵥ* M`.
  have hD : ⇑(Fintype.linearCombination (ZMod p) fun i ↦ degreeOneDeriv p X i ρ) =
      (degreeZeroBasis p X).equivFun.symm ∘ M.vecMul := by
    funext b
    apply (degreeZeroBasis p X).equivFun.injective
    rw [Function.comp_apply, LinearEquiv.apply_symm_apply]
    ext k
    rw [Module.Basis.equivFun_apply, Fintype.linearCombination_apply, map_sum,
      Finsupp.finsetSum_apply, Matrix.vecMul, dotProduct]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, degreeZeroBasis_repr_degreeOneDeriv, hM,
      LinearMap.BilinForm.toMatrix_apply]
  rw [← Fintype.range_linearCombination, LinearMap.range_eq_top, hD,
    Function.Surjective.of_comp_iff' (degreeZeroBasis p X).equivFun.symm.bijective,
    Matrix.vecMul_surjective_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero,
    LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (dualBasis p X)]

end DerivForm

/-! ### The tails `T_j` -/

section Tail

variable [Fact p.Prime] [Finite X] [LinearOrder X]

variable (p X) in
/-- **The tail `T_j(ρ)`** of a class `ρ ∈ gr_1(F)`: the subspace of `gr_j(F)` spanned by the
iterated `p`-powers `π^j ξ_i` of the generator classes `ξ_i ∈ gr_0(F)`, over the indices `i` whose
coefficient `c_i` of `π ξ_i` in `ρ`, in the standard basis `TauCeti.freeProP.degreeOneBasis`,
vanishes. For the class `ρ` of a relator these are the generators contributing no `π`-term to the
basis-modification map `TauCeti.freeProP.basisModificationDelta`. The vectors `π^j ξ_i` are
linearly independent, so `T_j(ρ)` has dimension the number of such indices
(`TauCeti.freeProP.finrank_basisModificationTail`), and above degree zero `π` carries `T_j(ρ)`
onto `T_{j+1}(ρ)` (`TauCeti.freeProP.basisModificationTail_succ`). -/
noncomputable def basisModificationTail (ρ : gradedPiece p (freeProP p X) 1) (j : ℕ) :
    Submodule (ZMod p) (gradedPiece p (freeProP p X) j) :=
  span (ZMod p) (Set.range fun i : {i : X // (degreeOneBasis p X).repr ρ (Sum.inl i) = 0} ↦
    gradedPowIter p (freeProP p X) j (gradedMkZero p (freeProP p X) (of (i : X))))

/-- An iterated power `π^j ξ_i` belongs to `T_j(ρ)` when its coefficient `c_i` in `ρ`
vanishes. -/
theorem gradedPowIter_mem_basisModificationTail {ρ : gradedPiece p (freeProP p X) 1} {i : X}
    (hi : (degreeOneBasis p X).repr ρ (Sum.inl i) = 0) (j : ℕ) :
    gradedPowIter p (freeProP p X) j (gradedMkZero p (freeProP p X) (of i)) ∈
      basisModificationTail p X ρ j :=
  subset_span ⟨⟨i, hi⟩, rfl⟩

/-- The double power `π² ξ_i` belongs to `T₂(ρ)` when the coefficient `c_i` in `ρ`
vanishes. -/
theorem gradedPow_gradedPow_gradedMkZero_mem_basisModificationTail
    {ρ : gradedPiece p (freeProP p X) 1} {i : X}
    (hi : (degreeOneBasis p X).repr ρ (Sum.inl i) = 0) :
    gradedPow p (freeProP p X) 1
        (gradedPow p (freeProP p X) 0 (gradedMkZero p (freeProP p X) (of i))) ∈
      basisModificationTail p X ρ 2 := by
  have h := gradedPowIter_mem_basisModificationTail hi 2
  rwa [gradedPowIter_succ, gradedPowIter_succ, gradedPowIter_zero] at h

/-- A submodule contains `T_j(ρ)` if and only if it contains every generator `π^j ξ_i`
whose coefficient `c_i` in `ρ` vanishes. -/
@[simp]
theorem basisModificationTail_le_iff {ρ : gradedPiece p (freeProP p X) 1} {j : ℕ}
    {W : Submodule (ZMod p) (gradedPiece p (freeProP p X) j)} :
    basisModificationTail p X ρ j ≤ W ↔ ∀ i, (degreeOneBasis p X).repr ρ (Sum.inl i) = 0 →
      gradedPowIter p (freeProP p X) j (gradedMkZero p (freeProP p X) (of i)) ∈ W := by
  simp only [basisModificationTail, span_le, Set.range_subset_iff, Subtype.forall,
    SetLike.mem_coe]

section

attribute [local instance] Fintype.ofFinite

/-- **Membership in the tail**: the elements of `T_j(ρ)` are the linear combinations of the
`π^j ξ_i` over the indices `i` with `c_i = 0`. -/
theorem mem_basisModificationTail_iff {ρ : gradedPiece p (freeProP p X) 1} {j : ℕ}
    {v : gradedPiece p (freeProP p X) j} :
    v ∈ basisModificationTail p X ρ j ↔
      ∃ c : {i : X // (degreeOneBasis p X).repr ρ (Sum.inl i) = 0} → ZMod p,
        ∑ i, c i • gradedPowIter p (freeProP p X) j (gradedMkZero p (freeProP p X) (of (i : X))) =
          v :=
  mem_span_range_iff_exists_fun _

end

/-- **`π` carries the tail onto the next tail above degree zero**: for `j ≥ 1`,
`T_{j+1}(ρ) = π(T_j(ρ))`, since `π` is additive on `gr_j(F)` and `π (π^j ξ_i) = π^{j+1} ξ_i`. -/
theorem basisModificationTail_succ (ρ : gradedPiece p (freeProP p X) 1) {j : ℕ} (hj : 1 ≤ j) :
    basisModificationTail p X ρ (j + 1) =
      (basisModificationTail p X ρ j).map
        ((gradedPowAddMonoidHom p (freeProP p X) hj).toZModLinearMap p) := by
  rw [basisModificationTail, basisModificationTail, map_span, ← Set.range_comp]
  simp only [Function.comp_def, AddMonoidHom.coe_toZModLinearMap, gradedPowAddMonoidHom_apply,
    gradedPowIter_succ]

/-- **The dimension of the tail**: `dim T_j(ρ)` is the number of indices `i` whose coefficient
`c_i` of `π ξ_i` in `ρ` vanishes, because the `π^j ξ_i` are linearly independent
(`TauCeti.freeProP.linearIndependent_gradedPowIter_gradedMkZero_of`). -/
theorem finrank_basisModificationTail (ρ : gradedPiece p (freeProP p X) 1) (j : ℕ) :
    Module.finrank (ZMod p) (basisModificationTail p X ρ j) =
      Nat.card {i : X // (degreeOneBasis p X).repr ρ (Sum.inl i) = 0} := by
  classical
  have := Fintype.ofFinite X
  exact (finrank_span_eq_card ((linearIndependent_gradedPowIter_gradedMkZero_of p X j).comp
    (Subtype.val : {i : X // (degreeOneBasis p X).repr ρ (Sum.inl i) = 0} → X)
    Subtype.val_injective)).trans Nat.card_eq_fintype_card.symm

end Tail

/-! ### The image of `δ` -/

section Span

variable [Fact p.Prime] [Finite X] [LinearOrder X]

/-- **`π` carries the image-plus-tail sum to the next level**: above degree zero it preserves
the image of `δ_ρ` and maps `T_{m+1}(ρ)` onto `T_{m+2}(ρ)`. -/
theorem gradedPow_mem_range_basisModificationDelta_sup_basisModificationTail (hm : 1 ≤ m)
    {ρ : gradedPiece p (freeProP p X) 1} {v : gradedPiece p (freeProP p X) (m + 1)}
    (hv : v ∈ LinearMap.range (basisModificationDelta p X hm ρ) ⊔
      basisModificationTail p X ρ (m + 1)) :
    gradedPow p (freeProP p X) (m + 1) v ∈
      LinearMap.range (basisModificationDelta p X (by omega) ρ) ⊔
        basisModificationTail p X ρ (m + 1 + 1) := by
  obtain ⟨_, ⟨w, rfl⟩, t, ht, rfl⟩ := Submodule.mem_sup.mp hv
  rw [gradedPow_add_of_one_le (by omega), gradedPow_basisModificationDelta]
  refine add_mem (Submodule.mem_sup_left ⟨_, rfl⟩) (Submodule.mem_sup_right ?_)
  rw [basisModificationTail_succ ρ (by omega : 1 ≤ m + 1)]
  have h := Submodule.mem_map_of_mem
    (f := (gradedPowAddMonoidHom p (freeProP p X) (by omega : 1 ≤ m + 1)).toZModLinearMap p) ht
  rwa [AddMonoidHom.coe_toZModLinearMap, gradedPowAddMonoidHom_apply] at h

/-- **Brackets lie in the image of `δ_ρ`** when `ρ` has no `p`-power part and its partial
derivatives span `gr_0(F)`: for `v ∈ gr_m(F)` and `y ∈ gr_0(F)`, writing `y = Σ_i b_i ∂_i ρ`, the
family `b • v` has `δ_ρ(b • v) = [v, y]`. -/
theorem gradedBracket_mem_range_basisModificationDelta (hm : 1 ≤ m)
    {ρ : gradedPiece p (freeProP p X) 1}
    (hρ : span (ZMod p) (Set.range fun i ↦ degreeOneDeriv p X i ρ) = ⊤)
    (hc : ∀ i, (degreeOneBasis p X).repr ρ (Sum.inl i) = 0) (v : gradedPiece p (freeProP p X) m)
    (y : gradedPiece p (freeProP p X) 0) :
    gradedBracket p (freeProP p X) m 0 v y ∈ LinearMap.range (basisModificationDelta p X hm ρ) := by
  cases nonempty_fintype X
  obtain ⟨b, hb⟩ := (mem_span_range_iff_exists_fun (ZMod p)).mp (hρ ▸ Submodule.mem_top :
    y ∈ span (ZMod p) (Set.range fun i ↦ degreeOneDeriv p X i ρ))
  refine ⟨fun i ↦ b i • v, ?_⟩
  rw [basisModificationDelta_smul, hb]
  simp only [hc, mul_zero, Finset.sum_const_zero, zero_smul, zero_add]

/-- **The image of `δ_ρ` for a relator without `p`-power part** is the span of the brackets
`[v, y]` with `v ∈ gr_m(F)` and `y ∈ gr_0(F)`, provided the partial derivatives `∂_i ρ` span
`gr_0(F)`. -/
theorem range_basisModificationDelta_eq_span_of_repr_inl_eq_zero (hm : 1 ≤ m)
    {ρ : gradedPiece p (freeProP p X) 1}
    (hρ : span (ZMod p) (Set.range fun i ↦ degreeOneDeriv p X i ρ) = ⊤)
    (hc : ∀ i, (degreeOneBasis p X).repr ρ (Sum.inl i) = 0) :
    LinearMap.range (basisModificationDelta p X hm ρ) =
      span (ZMod p) (Set.range
        fun vy : gradedPiece p (freeProP p X) m × gradedPiece p (freeProP p X) 0 ↦
          gradedBracket p (freeProP p X) m 0 vy.1 vy.2) := by
  cases nonempty_fintype X
  refine le_antisymm ?_ ?_
  · rintro _ ⟨v, rfl⟩
    rw [basisModificationDelta_eq_gradedPow_add_sum]
    simp only [hc, zero_smul, Finset.sum_const_zero, gradedPow_zero, zero_add]
    refine Submodule.sum_mem _ fun i _ ↦ Submodule.subset_span ?_
    exact ⟨(v i, degreeOneDeriv p X i ρ), rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨⟨v, y⟩, rfl⟩
    exact gradedBracket_mem_range_basisModificationDelta hm hρ hc v y

/-- **The span statement for a relator without `p`-power part**: if `ρ ∈ gr_1(F)` has all
coefficients `c_i` of `π ξ_i` equal to zero and its partial derivatives `∂_i ρ` span `gr_0(F)`, then
for every `m ≥ 1`
  `gr_{m+1}(F) = Im δ_ρ + T_{m+1}(ρ)`,
where the tail `T_{m+1}(ρ)` is spanned by the `p`-powers `π^{m+1} ξ_i` of all the generator
classes. The image of `δ_ρ` is the span of the brackets `[gr_m(F), gr_0(F)]`, and the tail
accounts for the `p`-powers: `π` carries `Im δ_ρ` in degree `m` into `Im δ_ρ` in degree `m + 1` and
`T_{m+1}(ρ)` onto `T_{m+2}(ρ)`. This is the case of the Demushkin relators
`x₁^q (x₁, x₂) (x₃, x₄) ⋯` with `q ≠ p`, where the `p`-power part of the relator lies in `λ_2(F)`
and is not seen by `gr_1(F)`. -/
theorem range_basisModificationDelta_sup_basisModificationTail_eq_top (hm : 1 ≤ m)
    {ρ : gradedPiece p (freeProP p X) 1}
    (hρ : span (ZMod p) (Set.range fun i ↦ degreeOneDeriv p X i ρ) = ⊤)
    (hc : ∀ i, (degreeOneBasis p X).repr ρ (Sum.inl i) = 0) :
    LinearMap.range (basisModificationDelta p X hm ρ) ⊔ basisModificationTail p X ρ (m + 1) =
      ⊤ := by
  cases nonempty_fintype X
  have hopen (k : ℕ) :
      IsOpen (pLowerCentralSeries p (freeProP p X) k : Set (freeProP p X)) :=
    (isTopologicallyFinitelyGenerated_freeProP p X).isOpen_pLowerCentralSeries Fact.out k
  induction m, hm using Nat.le_induction with
  | base =>
    refine eq_top_of_forall_gradedPow_mem_of_forall_gradedBracket_mem (hopen 3) (fun v ↦ ?_)
      fun v y ↦
        Submodule.mem_sup_left (gradedBracket_mem_range_basisModificationDelta le_rfl hρ hc v y)
    -- `gr_1(F)` is spanned by the `π ξ_i` and the `[ξ_j, ξ_k]`, and `π` is linear on it.
    refine forall_gradedPow_mem_of_span_eq_top le_rfl
      (span_range_degreeOneFamily_of_eq_top p X) ?_ v
    rintro _ ⟨k, rfl⟩
    rcases k with i | jk
    · -- `π (π ξ_i) = π² ξ_i` lies in the tail, since `c_i = 0`.
      rw [degreeOneFamily_inl]
      exact Submodule.mem_sup_right
        (gradedPow_gradedPow_gradedMkZero_mem_basisModificationTail (hc i))
    · -- `π [ξ_j, ξ_k] = [π ξ_j, ξ_k] + (p choose 2) • [[ξ_j, ξ_k], ξ_j]` is a sum of brackets.
      rw [degreeOneFamily_inr, gradedPow_gradedBracket_zero_zero]
      exact Submodule.mem_sup_left
        (add_mem (gradedBracket_mem_range_basisModificationDelta le_rfl hρ hc _ _)
          (nsmul_mem (gradedBracket_mem_range_basisModificationDelta le_rfl hρ hc _ _) _))
  | succ m hm ih =>
    refine eq_top_of_forall_gradedPow_mem_of_forall_gradedBracket_mem (hopen (m + 1 + 1 + 1))
      (fun v ↦ ?_) fun v y ↦
        Submodule.mem_sup_left (gradedBracket_mem_range_basisModificationDelta (by omega) hρ hc v y)
    exact gradedPow_mem_range_basisModificationDelta_sup_basisModificationTail hm
      (ih ▸ Submodule.mem_top)

/-! ### The image of `δ` and the exponent sums

For a class `ρ` without `p`-power part the image of `δ_ρ` is spanned by brackets, so every
continuous homomorphism to a commutative group kills it, while the tail `T_{m+1}(ρ)` is spanned by
the `p`-powers `π^{m+1} ξ_i`, which the exponent sums modulo `p ^ (m + 2)` separate
(`TauCeti.freeProP.exponentSumZModPow`). The decomposition `gr_{m+1}(F) = Im δ_ρ + T_{m+1}(ρ)`
therefore identifies `Im δ_ρ` with the classes killed by every exponent sum modulo `p ^ (m + 2)`. -/

/-- **A continuous homomorphism to a commutative group kills the image of `δ_ρ`** when `ρ` has no
`p`-power part: `δ_ρ(v)` is then a sum of brackets, and brackets vanish in a commutative group. -/
theorem gradedMap_basisModificationDelta_eq_zero {H : Type u} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [IsMulCommutative H] (f : freeProP p X →* H) (hf : Continuous f)
    (hm : 1 ≤ m) {ρ : gradedPiece p (freeProP p X) 1}
    (hc : ∀ i, (degreeOneBasis p X).repr ρ (Sum.inl i) = 0)
    (v : X → gradedPiece p (freeProP p X) m) :
    gradedMap p f hf (m + 1) (basisModificationDelta p X hm ρ v) = 0 := by
  cases nonempty_fintype X
  rw [basisModificationDelta_eq_gradedPow_add_sum]
  simp only [hc, zero_smul, Finset.sum_const_zero, gradedPow_zero, zero_add, map_sum]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have h := gradedMap_gradedBracket f hf (v i) (degreeOneDeriv p X i ρ)
  rw [gradedBracket_eq_zero_of_isMulCommutative (G := H)] at h
  exact h

/-- **The image of `δ_ρ` through the exponent sums**: if `ρ ∈ gr_1(F)` has no `p`-power part and
its partial derivatives `∂_i ρ` span `gr_0(F)`, then for `m ≥ 1` the class in `gr_{m+1}(F)` of
`z ∈ λ_{m+1}(F)` lies in `Im δ_ρ` if and only if `p ^ (m + 2)` divides every exponent sum of `z`.
So `Im δ_ρ` is the kernel of the map `gr_{m+1}(F) → gr_{m+1}(F^{ab})` induced by the
abelianization, the complement of the tail `T_{m+1}(ρ)` in
`TauCeti.freeProP.range_basisModificationDelta_sup_basisModificationTail_eq_top`. This is the span
statement for the relators `x₁^q (x₁, x₂) (x₃, x₄) ⋯` with `q ≠ p`: a discrepancy between two
such relators whose exponent sums agree modulo `p ^ (m + 2)` is absorbed by a level-`m` basis
modification. -/
theorem gradedMk_mem_range_basisModificationDelta_iff (hm : 1 ≤ m)
    {ρ : gradedPiece p (freeProP p X) 1}
    (hρ : span (ZMod p) (Set.range fun i ↦ degreeOneDeriv p X i ρ) = ⊤)
    (hc : ∀ i, (degreeOneBasis p X).repr ρ (Sum.inl i) = 0)
    (z : pLowerCentralSeries p (freeProP p X) (m + 1)) :
    gradedMk p (freeProP p X) (m + 1) z ∈ LinearMap.range (basisModificationDelta p X hm ρ) ↔
      ∀ i, (p : ℤ_[p]) ^ (m + 2) ∣ (exponentSum p X (z : freeProP p X)).toAdd i := by
  classical
  cases nonempty_fintype X
  constructor
  · rintro ⟨v, hv⟩ i
    have h := gradedMap_exponentSumZModPow_gradedMk_eq_zero_iff i z
    rw [← hv, gradedMap_basisModificationDelta_eq_zero _ _ hm hc] at h
    exact h.mp rfl
  · intro hz
    have hmem : gradedMk p (freeProP p X) (m + 1) z ∈
        LinearMap.range (basisModificationDelta p X hm ρ) ⊔
          basisModificationTail p X ρ (m + 1) := by
      rw [range_basisModificationDelta_sup_basisModificationTail_eq_top hm hρ hc]
      exact Submodule.mem_top
    obtain ⟨_, ⟨v, rfl⟩, t, ht, hdt⟩ := Submodule.mem_sup.mp hmem
    obtain ⟨c, rfl⟩ := mem_basisModificationTail_iff.mp ht
    -- Every coefficient of the tail vanishes: the character of the `i`-th exponent sum modulo
    -- `p ^ (m + 2)` kills the class of `z` and the image of `δ_ρ`, and it reads off the
    -- coefficient of `π^{m+1} ξ_i`.
    suffices hc0 : ∀ i, c i = 0 by
      rw [← hdt]
      simp [hc0]
    intro i
    have h := congrArg ((gradedMap p (exponentSumZModPow p X (m + 1 + 1) (i : X)).toMonoidHom
      (exponentSumZModPow p X (m + 1 + 1) (i : X)).continuous (m + 1)).toZModLinearMap p) hdt
    rw [map_add, map_sum] at h
    simp only [map_smul] at h
    simp only [AddMonoidHom.coe_toZModLinearMap] at h
    rw [(gradedMap_exponentSumZModPow_gradedMk_eq_zero_iff (i : X) z).mpr (hz i),
      gradedMap_basisModificationDelta_eq_zero _ _ hm hc, zero_add,
      Finset.sum_eq_single i (fun j _ hj ↦ by
        rw [gradedMap_exponentSumZModPow_gradedPowIter_gradedMkZero_of_of_ne _
          fun h' ↦ hj (Subtype.ext h'), smul_zero]) (by simp)] at h
    exact (smul_eq_zero_iff_left
      (gradedMap_exponentSumZModPow_gradedPowIter_gradedMkZero_of_self_ne_zero _ _)).mp h

/-- **A class of the closed commutator subgroup lies in the image of `δ_ρ`**: for `ρ` without
`p`-power part and with spanning partial derivatives, the class in `gr_{m+1}(F)` of an element of
`λ_{m+1}(F)` lying in the closure of the commutator subgroup is in `Im δ_ρ`. This is the form used
for the relators `(x₁, x₂) (x₃, x₄) ⋯` with `q = 0`, whose discrepancies have trivial exponent
sums. -/
theorem gradedMk_mem_range_basisModificationDelta_of_mem_topologicalClosure_commutator
    (hm : 1 ≤ m) {ρ : gradedPiece p (freeProP p X) 1}
    (hρ : span (ZMod p) (Set.range fun i ↦ degreeOneDeriv p X i ρ) = ⊤)
    (hc : ∀ i, (degreeOneBasis p X).repr ρ (Sum.inl i) = 0)
    (z : pLowerCentralSeries p (freeProP p X) (m + 1))
    (hz : (z : freeProP p X) ∈ (commutator (freeProP p X)).topologicalClosure) :
    gradedMk p (freeProP p X) (m + 1) z ∈ LinearMap.range (basisModificationDelta p X hm ρ) := by
  rw [← exponentSum_eq_one_iff] at hz
  rw [gradedMk_mem_range_basisModificationDelta_iff hm hρ hc]
  intro i
  rw [hz, toAdd_one, Pi.zero_apply]
  exact dvd_zero _

/-- The odd-`p` span statement, in the form in which it is proved: a linear functional `φ` on
`gr_0(F)` with a value `1` at `y₀` such that `φ(y) • π v + [v, y] ∈ Im δ_ρ` for every `v` and `y`
forces `Im δ_ρ = gr_{m+1}(F)` for every `m ≥ 1`. -/
private theorem range_basisModificationDelta_eq_top_of_forall_smul_gradedPow_add_mem (hp : Odd p)
    {ρ : gradedPiece p (freeProP p X) 1}
    (φ : gradedPiece p (freeProP p X) 0 →ₗ[ZMod p] ZMod p) {y₀ : gradedPiece p (freeProP p X) 0}
    (hy₀ : φ y₀ = 1)
    (hkey : ∀ (m : ℕ) (hm : 1 ≤ m) (v : gradedPiece p (freeProP p X) m)
      (y : gradedPiece p (freeProP p X) 0),
      φ y • gradedPow p (freeProP p X) m v + gradedBracket p (freeProP p X) m 0 v y ∈
        LinearMap.range (basisModificationDelta p X hm ρ))
    (hm : 1 ≤ m) : LinearMap.range (basisModificationDelta p X hm ρ) = ⊤ := by
  cases nonempty_fintype X
  have hopen (k : ℕ) :
      IsOpen (pLowerCentralSeries p (freeProP p X) k : Set (freeProP p X)) :=
    (isTopologicallyFinitelyGenerated_freeProP p X).isOpen_pLowerCentralSeries Fact.out k
  -- Brackets with an element of the kernel of `φ` lie in the image.
  have hker (m : ℕ) (hm : 1 ≤ m) (v : gradedPiece p (freeProP p X) m)
      {z : gradedPiece p (freeProP p X) 0} (hz : φ z = 0) :
      gradedBracket p (freeProP p X) m 0 v z ∈
        LinearMap.range (basisModificationDelta p X hm ρ) := by
    have h := hkey m hm v z
    rwa [hz, zero_smul, zero_add] at h
  have hsplit (y : gradedPiece p (freeProP p X) 0) : φ (y - φ y • y₀) = 0 := by
    rw [map_sub, map_smul, hy₀, smul_eq_mul, mul_one]
    exact sub_self _
  -- Once `π v` lies in the image, so does every bracket `[v, y]`.
  have hbr (m : ℕ) (hm : 1 ≤ m) (v : gradedPiece p (freeProP p X) m)
      (hv : gradedPow p (freeProP p X) m v ∈ LinearMap.range (basisModificationDelta p X hm ρ))
      (y : gradedPiece p (freeProP p X) 0) :
      gradedBracket p (freeProP p X) m 0 v y ∈
        LinearMap.range (basisModificationDelta p X hm ρ) := by
    have h₁ := hker m hm v (hsplit y)
    have h₂ := hkey m hm v y₀
    rw [hy₀, one_smul] at h₂
    have e : gradedBracket p (freeProP p X) m 0 v y =
        gradedBracket p (freeProP p X) m 0 v (y - φ y • y₀) +
          φ y • ((gradedPow p (freeProP p X) m v + gradedBracket p (freeProP p X) m 0 v y₀) -
            gradedPow p (freeProP p X) m v) := by
      rw [add_sub_cancel_left]
      simp only [← gradedBracketLinear_apply, map_sub, map_smul, sub_add_cancel]
    rw [e]
    exact add_mem h₁ (Submodule.smul_mem _ _ (sub_mem h₂ hv))
  -- `π v` lies in the image for every `v ∈ gr_m(F)`, by induction on `m`.
  have hpow : ∀ (m : ℕ) (hm : 1 ≤ m) (v : gradedPiece p (freeProP p X) m),
      gradedPow p (freeProP p X) m v ∈ LinearMap.range (basisModificationDelta p X hm ρ) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      -- `[π u, y₀] = π [u, y₀] = -π [y₀, u - φ(u) y₀] = -[π y₀, u - φ(u) y₀]` for `u ∈ gr_0(F)`.
      have hy₀u (u : gradedPiece p (freeProP p X) 0) :
          gradedBracket p (freeProP p X) 1 0 (gradedPow p (freeProP p X) 0 u) y₀ ∈
            LinearMap.range (basisModificationDelta p X le_rfl ρ) := by
        have hswap := gradedCast_gradedBracket_swap y₀ u
        rw [gradedCast_rfl] at hswap
        have e : gradedBracket p (freeProP p X) 0 0 y₀ (u - φ u • y₀) =
            gradedBracket p (freeProP p X) 0 0 y₀ u := by
          rw [map_sub, ← gradedBracketLinear_apply y₀ (φ u • y₀), map_smul,
            gradedBracketLinear_apply, gradedBracket_self, smul_zero, sub_zero]
        rw [← gradedPow_gradedBracket_left_zero_of_odd hp, hswap, ← e,
          gradedPow_neg_of_one_le le_rfl, gradedPow_gradedBracket_left_zero_of_odd hp]
        exact neg_mem (hker 1 le_rfl _ (hsplit u))
      have hππ (u : gradedPiece p (freeProP p X) 0) :
          gradedPow p (freeProP p X) 1 (gradedPow p (freeProP p X) 0 u) ∈
            LinearMap.range (basisModificationDelta p X le_rfl ρ) := by
        have h := hkey 1 le_rfl (gradedPow p (freeProP p X) 0 u) y₀
        rw [hy₀, one_smul] at h
        simpa only [add_sub_cancel_right] using sub_mem h (hy₀u u)
      intro v
      refine forall_gradedPow_mem_of_span_eq_top le_rfl
        (span_range_gradedPow_union_range_gradedBracket_eq_top (hopen 2)) ?_ v
      rintro _ (⟨u, rfl⟩ | ⟨⟨u, y⟩, rfl⟩)
      · exact hππ u
      · rw [gradedPow_gradedBracket_left_zero_of_odd hp]
        exact hbr 1 le_rfl _ (hππ u) y
    | succ m hm ih =>
      have hππ (u : gradedPiece p (freeProP p X) m) :
          gradedPow p (freeProP p X) (m + 1) (gradedPow p (freeProP p X) m u) ∈
            LinearMap.range (basisModificationDelta p X (by omega) ρ) := by
        obtain ⟨w, hw⟩ := ih u
        rw [← hw, gradedPow_basisModificationDelta]
        exact ⟨_, rfl⟩
      intro v
      refine forall_gradedPow_mem_of_span_eq_top (by omega)
        (span_range_gradedPow_union_range_gradedBracket_eq_top (hopen (m + 1 + 1))) ?_ v
      rintro _ (⟨u, rfl⟩ | ⟨⟨u, y⟩, rfl⟩)
      · exact hππ u
      · rw [gradedPow_gradedBracket_left_zero hm]
        exact hbr (m + 1) (by omega) _ (hππ u) y
  exact eq_top_of_forall_gradedPow_mem_of_forall_gradedBracket_mem (hopen (m + 1 + 1))
    (hpow m hm) fun v y ↦ hbr m hm v (hpow m hm v) y

/-- **The span statement for odd `p` and a relator with a `p`-power part**: if `p` is odd,
`ρ ∈ gr_1(F)` has some coefficient `c_i` of `π ξ_i` nonzero and its partial derivatives `∂_i ρ`
span `gr_0(F)`, then `δ_ρ` is onto `gr_{m+1}(F)` for every `m ≥ 1`:
  `gr_{m+1}(F) = Im δ_ρ`.
This is the case of the Demushkin relators `x₁^p (x₁, x₂) (x₃, x₄) ⋯` at odd `p`. -/
theorem range_basisModificationDelta_eq_top_of_odd (hp : Odd p) (hm : 1 ≤ m)
    {ρ : gradedPiece p (freeProP p X) 1}
    (hρ : span (ZMod p) (Set.range fun i ↦ degreeOneDeriv p X i ρ) = ⊤)
    (hc : ∃ i, (degreeOneBasis p X).repr ρ (Sum.inl i) ≠ 0) :
    LinearMap.range (basisModificationDelta p X hm ρ) = ⊤ := by
  cases nonempty_fintype X
  -- The derivatives and the `p`-power coefficients as linear maps on `𝔽_p^X`.
  set D : (X → ZMod p) →ₗ[ZMod p] gradedPiece p (freeProP p X) 0 :=
    Fintype.linearCombination (ZMod p) fun i ↦ degreeOneDeriv p X i ρ with hD
  set c : (X → ZMod p) →ₗ[ZMod p] ZMod p :=
    Fintype.linearCombination (ZMod p) fun i ↦ (degreeOneBasis p X).repr ρ (Sum.inl i) with hcdef
  have hDtop : LinearMap.range D = ⊤ := by rw [hD, Fintype.range_linearCombination, hρ]
  have hδ (m : ℕ) (hm : 1 ≤ m) (b : X → ZMod p) (v : gradedPiece p (freeProP p X) m) :
      basisModificationDelta p X hm ρ (fun i ↦ b i • v) =
        c b • gradedPow p (freeProP p X) m v + gradedBracket p (freeProP p X) m 0 v (D b) := by
    rw [basisModificationDelta_smul, hcdef, hD, Fintype.linearCombination_apply,
      Fintype.linearCombination_apply]
    simp only [smul_eq_mul]
  -- `gr_0(F)` has dimension `#X`: the `#X` derivatives span it and the `#X` generator classes are
  -- linearly independent in it. So the spanning derivatives are a basis and `D` is injective.
  have hfin : Module.finrank (ZMod p) (gradedPiece p (freeProP p X) 0) = Fintype.card X := by
    have : Module.Finite (ZMod p) (gradedPiece p (freeProP p X) 0) :=
      Module.Finite.of_surjective D (LinearMap.range_eq_top.mp hDtop)
    refine le_antisymm ?_ (LinearIndependent.fintype_card_le_finrank
      (linearIndependent_gradedPowIter_gradedMkZero_of p X 0))
    rw [← finrank_top (R := ZMod p), ← hρ]
    exact finrank_range_le_card _
  have hB (b : X → ZMod p) (hb : D b = 0) : c b = 0 := by
    have hli : LinearIndependent (ZMod p) fun i ↦ degreeOneDeriv p X i ρ :=
      linearIndependent_of_top_le_span_of_card_eq_finrank hρ.ge hfin.symm
    rw [hD, Fintype.linearCombination_apply] at hb
    rw [show b = 0 from funext (Fintype.linearIndependent_iff.mp hli b hb), map_zero]
  -- `c` factors through `D`: `c = φ ∘ D` for `φ := c ∘ s`, with `s` a linear section of `D`.
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective D hDtop
  have hφ (b : X → ZMod p) : c b = (c ∘ₗ s) (D b) := by
    have h0 : D (b - s (D b)) = 0 := by
      rw [map_sub, ← LinearMap.comp_apply, hs, LinearMap.id_apply, sub_self]
    have h := hB _ h0
    rw [map_sub] at h
    have h' : c b = c (s (D b)) := sub_eq_zero.mp h
    rw [LinearMap.comp_apply]
    exact h'
  obtain ⟨i, hi⟩ := hc
  have hne : (c ∘ₗ s) (D (Pi.single i 1)) ≠ 0 := by
    rw [← hφ, hcdef, Fintype.linearCombination_apply_single, one_smul]
    exact hi
  refine range_basisModificationDelta_eq_top_of_forall_smul_gradedPow_add_mem hp (c ∘ₗ s)
    (y₀ := ((c ∘ₗ s) (D (Pi.single i 1)))⁻¹ • D (Pi.single i 1)) ?_ (fun m hm v y ↦ ?_) hm
  · rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hne]
  · refine ⟨fun j ↦ s y j • v, ?_⟩
    rw [hδ, hφ, ← LinearMap.comp_apply D s, hs, LinearMap.id_apply]

end Span

/-! ### The dyadic span statement -/

section DyadicSpan

variable [Finite X] [LinearOrder X]

-- Preferring the ring path keeps a single additive structure on `ZMod 2`, so that the continuous
-- dual is an additive group over the module structure of `ZMod 2` on itself.
attribute [local instance 2000] Ring.toAddCommGroup

/-- The dyadic form of the membership behind the span statements: if `x_{i₀}` is the only
generator with a `2`-power coefficient in `ρ` and the coordinate character `χ_{i₀}` is orthogonal
to the other coordinate characters under the degree-one form, then
`ψ(y) • π v + [v, y] ∈ Im δ_ρ`, where `ψ(y)` is the coordinate of `y ∈ gr_0(F)` at `ξ_{i₀}`. -/
private theorem repr_smul_gradedPow_add_gradedBracket_mem_range_two (hm : 1 ≤ m)
    {ρ : gradedPiece 2 (freeProP 2 X) 1}
    (hρ : span (ZMod 2) (Set.range fun i ↦ degreeOneDeriv 2 X i ρ) = ⊤) {i₀ : X}
    (hc : ∀ i, i ≠ i₀ → (degreeOneBasis 2 X).repr ρ (Sum.inl i) = 0)
    (hd : ∀ i, i ≠ i₀ → degreeOneForm ρ (dualBasis 2 X i) (dualBasis 2 X i₀) = 0)
    (v : gradedPiece 2 (freeProP 2 X) m) (y : gradedPiece 2 (freeProP 2 X) 0) :
    (degreeZeroBasis 2 X).repr y i₀ • gradedPow 2 (freeProP 2 X) m v +
        gradedBracket 2 (freeProP 2 X) m 0 v y ∈
      LinearMap.range (basisModificationDelta 2 X hm ρ) := by
  cases nonempty_fintype X
  obtain ⟨b, hb⟩ := (mem_span_range_iff_exists_fun (ZMod 2)).mp (hρ ▸ Submodule.mem_top :
    y ∈ span (ZMod 2) (Set.range fun i ↦ degreeOneDeriv 2 X i ρ))
  refine ⟨fun i ↦ b i • v, ?_⟩
  rw [basisModificationDelta_smul, hb]
  congr 2
  -- `Σ_i b_i c_i = Σ_i b_i ψ(∂_i ρ)`, termwise: both factors vanish away from `i₀`, and at `i₀`
  -- the diagonal entry of the degree-one form is `(2 choose 2) c_{i₀} = c_{i₀}`.
  rw [← hb, map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, degreeZeroBasis_repr_degreeOneDeriv]
  by_cases hi : i = i₀
  · rw [hi, degreeOneForm_dualBasis_self, Nat.choose_self, one_smul]
  · rw [hc i hi, hd i hi]

/-- **The dyadic span statement for the odd-rank normal form**: let `ρ ∈ gr_1(F)`, for `F` free
pro-`2`, have its partial derivatives `∂_i ρ` spanning `gr_0(F)`, let `x_{i₀}` be the only
generator whose coefficient `c_i` of `π ξ_i` in `ρ` may be nonzero, and let the coordinate
character `χ_{i₀}` be orthogonal to every other coordinate character under the degree-one form of
`ρ`, that is, `ξ_{i₀}` occurs in no bracket of `ρ`. Then for every `m ≥ 1`
  `gr_{m+1}(F) = Im δ_ρ + T_{m+1}(ρ)`,
where the tail `T_{m+1}(ρ)` is spanned by the `2`-powers `π^{m+1} ξ_i` with `i ≠ i₀`. This is the
case of the dyadic relators `x₁² x₂^{2^f} (x₂, x₃) ⋯ (x_{n-1}, x_n)` of odd rank `n`, with
`f ≥ 2`, whose class is `π ξ₁ + [ξ₂, ξ₃] + ⋯ + [ξ_{n-1}, ξ_n]`. -/
theorem range_basisModificationDelta_sup_basisModificationTail_eq_top_two (hm : 1 ≤ m)
    {ρ : gradedPiece 2 (freeProP 2 X) 1}
    (hρ : span (ZMod 2) (Set.range fun i ↦ degreeOneDeriv 2 X i ρ) = ⊤) {i₀ : X}
    (hc : ∀ i, i ≠ i₀ → (degreeOneBasis 2 X).repr ρ (Sum.inl i) = 0)
    (hd : ∀ i, i ≠ i₀ → degreeOneForm ρ (dualBasis 2 X i) (dualBasis 2 X i₀) = 0) :
    LinearMap.range (basisModificationDelta 2 X hm ρ) ⊔ basisModificationTail 2 X ρ (m + 1) =
      ⊤ := by
  have hopen (k : ℕ) :
      IsOpen (pLowerCentralSeries 2 (freeProP 2 X) k : Set (freeProP 2 X)) :=
    (isTopologicallyFinitelyGenerated_freeProP 2 X).isOpen_pLowerCentralSeries Nat.prime_two k
  have hkey := fun (m : ℕ) (hm : 1 ≤ m) ↦
    repr_smul_gradedPow_add_gradedBracket_mem_range_two hm hρ hc hd
  -- The coordinate of a generator class at `ξ_{i₀}`.
  have hψ (a : X) : (degreeZeroBasis 2 X).repr (gradedMkZero 2 (freeProP 2 X) (of a)) i₀ =
      if a = i₀ then 1 else 0 := by
    rw [← degreeZeroBasis_apply, Module.Basis.repr_self, Finsupp.single_apply]
  -- Although `π` is not additive on `gr_0(F)`, its defect does not obstruct the argument: modulo
  -- `Im δ_ρ`, a bracket `[v, y]` is `-ψ(y) • π v`, where `ψ(y)` is the coordinate of `y` at
  -- `ξ_{i₀}`; so once `π v` lies in the sum, so does every bracket `[v, y]`.
  have hbr (m : ℕ) (hm : 1 ≤ m) (v : gradedPiece 2 (freeProP 2 X) m)
      (hv : gradedPow 2 (freeProP 2 X) m v ∈
        LinearMap.range (basisModificationDelta 2 X hm ρ) ⊔ basisModificationTail 2 X ρ (m + 1))
      (y : gradedPiece 2 (freeProP 2 X) 0) :
      gradedBracket 2 (freeProP 2 X) m 0 v y ∈
        LinearMap.range (basisModificationDelta 2 X hm ρ) ⊔
          basisModificationTail 2 X ρ (m + 1) := by
    rw [← add_sub_cancel_left ((degreeZeroBasis 2 X).repr y i₀ • gradedPow 2 (freeProP 2 X) m v)
      (gradedBracket 2 (freeProP 2 X) m 0 v y)]
    exact sub_mem (Submodule.mem_sup_left (hkey m hm v y)) (Submodule.smul_mem _ _ hv)
  -- `π v` lies in the sum for every `v ∈ gr_m(F)`, by induction on `m`.
  have hpow : ∀ (m : ℕ) (hm : 1 ≤ m) (v : gradedPiece 2 (freeProP 2 X) m),
      gradedPow 2 (freeProP 2 X) m v ∈
        LinearMap.range (basisModificationDelta 2 X hm ρ) ⊔
          basisModificationTail 2 X ρ (m + 1) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      -- `π [ξ_a, y]` lies in the sum for `a ≠ i₀`: it is `[π ξ_a, y] + [[ξ_a, y], ξ_a]`, where the
      -- second bracket lies in `Im δ_ρ` since `ψ(ξ_a) = 0`, and the first is `-ψ(y) • π² ξ_a`
      -- modulo `Im δ_ρ`, with `π² ξ_a` in the tail since `c_a = 0`.
      have hgen (a : X) (ha : a ≠ i₀) (y : gradedPiece 2 (freeProP 2 X) 0) :
          gradedPow 2 (freeProP 2 X) 1 (gradedBracket 2 (freeProP 2 X) 0 0
              (gradedMkZero 2 (freeProP 2 X) (of a)) y) ∈
            LinearMap.range (basisModificationDelta 2 X le_rfl ρ) ⊔
              basisModificationTail 2 X ρ (1 + 1) := by
        have htail := gradedPow_gradedPow_gradedMkZero_mem_basisModificationTail (hc a ha)
        have h₂ := hkey 1 le_rfl (gradedBracket 2 (freeProP 2 X) 0 0
          (gradedMkZero 2 (freeProP 2 X) (of a)) y) (gradedMkZero 2 (freeProP 2 X) (of a))
        rw [hψ, ite_eq_right ha, zero_smul, zero_add] at h₂
        rw [gradedPow_gradedBracket_zero_zero]
        refine add_mem (hbr 1 le_rfl _ (Submodule.mem_sup_right htail) y)
          (nsmul_mem (Submodule.mem_sup_left h₂) _)
      intro v
      -- `gr_1(F)` is spanned by the `π ξ_i` and the `[ξ_j, ξ_k]`, and `π` is linear on it.
      refine forall_gradedPow_mem_of_span_eq_top le_rfl
        (span_range_degreeOneFamily_of_eq_top 2 X) ?_ v
      rintro _ ⟨k, rfl⟩
      rcases k with i | ⟨⟨j, k⟩, hjk⟩
      · rw [degreeOneFamily_inl]
        by_cases hi : i = i₀
        · -- `π² ξ_{i₀} = π² ξ_{i₀} + [π ξ_{i₀}, ξ_{i₀}]` lies in `Im δ_ρ`, since `ψ(ξ_{i₀}) = 1`.
          have h := hkey 1 le_rfl (gradedPow 2 (freeProP 2 X) 0
            (gradedMkZero 2 (freeProP 2 X) (of i))) (gradedMkZero 2 (freeProP 2 X) (of i))
          rw [hψ, ite_eq_left hi, one_smul, gradedBracket_gradedPow_self, add_zero] at h
          exact Submodule.mem_sup_left h
        · -- `π² ξ_i` lies in the tail, since `c_i = 0`.
          exact Submodule.mem_sup_right
            (gradedPow_gradedPow_gradedMkZero_mem_basisModificationTail (hc i hi))
      · rw [degreeOneFamily_inr]
        dsimp only
        by_cases hj : j = i₀
        · -- `[ξ_{i₀}, ξ_k] = -[ξ_k, ξ_{i₀}]` with `k ≠ i₀`.
          have hk : k ≠ i₀ := hj ▸ hjk.ne'
          have hswap := gradedCast_gradedBracket_swap (gradedMkZero 2 (freeProP 2 X) (of j))
            (gradedMkZero 2 (freeProP 2 X) (of k))
          rw [gradedCast_rfl] at hswap
          rw [← neg_neg (gradedBracket 2 (freeProP 2 X) 0 0 _ _), ← hswap,
            gradedPow_neg_of_one_le le_rfl]
          exact neg_mem (hgen k hk _)
        · exact hgen j hj _
    | succ m hm ih =>
      -- `v = δ_ρ(w) + t` with `t` in the tail; `π` carries both summands into the next level.
      have htop : LinearMap.range (basisModificationDelta 2 X hm ρ) ⊔
          basisModificationTail 2 X ρ (m + 1) = ⊤ :=
        eq_top_of_forall_gradedPow_mem_of_forall_gradedBracket_mem (hopen (m + 1 + 1)) ih
          fun v y ↦ hbr m hm v (ih v) y
      intro v
      exact gradedPow_mem_range_basisModificationDelta_sup_basisModificationTail hm
        (htop ▸ Submodule.mem_top)
  exact eq_top_of_forall_gradedPow_mem_of_forall_gradedBracket_mem (hopen (m + 1 + 1))
    (hpow m hm) fun v y ↦ hbr m hm v (hpow m hm v) y

end DyadicSpan

end TauCeti.freeProP
