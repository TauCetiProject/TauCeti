/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Cohomology
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Minimal
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Perturbation
public import TauCeti.Algebra.Homology.Contraction.TensorTrick.Perturbation

/-!
# Homological transfer of A-infinity structures

Let `𝒜` be an `A∞` algebra on `A`, and let `(i, p, h)` be a special contraction of `(A, m₁)` onto
a graded module `(H, d_H)`, with `h` of degree `-1` and `i`, `p` of degree zero.  The tensor trick
turns it into a special contraction of the bar constructions `Tᶜ(sA) ⇄ Tᶜ(sH)` for the letterwise
differentials (`TauCeti.AInfinityAlgebra.barTensorTrick`), and the basic perturbation lemma
transports this contraction along the higher part `δ` of the bar differential of `𝒜`.

The perturbed differential `D'` of `Tᶜ(sH)` squares to zero and is a graded coderivation, so its
letter component is the Taylor map of an `A∞` structure on `H`: the *transferred* structure
`TauCeti.AInfinityAlgebra.transfer`.  With `K` the tensor-trick homotopy and
`X = (1 + δ K)⁻¹ δ`, the perturbed inclusion `i' = i - K X i` is a coalgebra morphism intertwining
`D'` with the bar differential of `𝒜`, hence an `A∞` morphism
`TauCeti.AInfinityAlgebra.transferInclusion` from the transferred structure to `𝒜`.  Its linear
part is `i`, so it is a quasi-isomorphism.  In low arity the transferred structure has
`m₁ = d_H` and `m₂ = p ∘ m₂ ∘ (i ⊗ i)`; in particular it is minimal when `d_H = 0`.

## Main definitions

* `TauCeti.AInfinityAlgebra.barTensorTrick`: the tensor-trick contraction of the bar
  constructions.
* `TauCeti.AInfinityAlgebra.transfer`: the transferred `A∞` structure on `H`.
* `TauCeti.AInfinityAlgebra.transferInclusion`: the `A∞` morphism extending `i`.

## Main results

* `TauCeti.AInfinityAlgebra.barDifferential_transfer`: the bar differential of the transferred
  structure is the perturbed differential `D'`.
* `TauCeti.AInfinityAlgebra.linearPart_transferInclusion`: the linear part of the extending
  morphism is the inclusion of the contraction.
* `TauCeti.AInfinityAlgebra.isQuasiIso_transferInclusion`: the extending morphism is a
  quasi-isomorphism.
* `TauCeti.AInfinityAlgebra.differential_transfer` and `TauCeti.AInfinityAlgebra.mul_transfer`:
  the transferred `m₁` is `d_H` and the transferred `m₂` is `p m₂ (i ⊗ i)`.

## References

* V. K. A. M. Gugenheim, L. A. Lambe, and J. D. Stasheff, *Perturbation theory in differential
  homological algebra II*, Illinois Journal of Mathematics 35 (1991), 357--373.
* J. Huebschmann and T. Kadeishvili, *Small models for chain algebras*, Mathematische Zeitschrift
  207 (1991), 245--280.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.3.
-/

public section

universe uR uA uH

namespace TauCeti.AInfinityAlgebra

open ReducedTensorWords

variable {R : Type uR} {A : Type uA} {H : Type uH} [CommRing R] [AddCommGroup A] [Module R A]
  [AddCommGroup H] [Module R H]

variable (𝒜 : AInfinityAlgebra R A) {GH : InternalGrading R H} {dH : Module.End R H}
  (c : LinearSpecialContraction 𝒜.differential dH)
  (hh : LinearMap.IsHomogeneous c.homotopy 𝒜.grading.piece 𝒜.grading.piece (-1))
  (hincl : LinearMap.IsHomogeneous c.incl GH.piece 𝒜.grading.piece 0)
  (hproj : LinearMap.IsHomogeneous c.proj 𝒜.grading.piece GH.piece 0)

/-- The differential has degree one for the suspended grading. -/
private theorem isHomogeneous_differential_shift_one :
    LinearMap.IsHomogeneous 𝒜.differential (𝒜.grading.shift 1).piece
      (𝒜.grading.shift 1).piece 1 :=
  (LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 <| LinearMap.isHomogeneous_def.2 fun _ _ hx ↦
    𝒜.differential_mem_piece hx

include hh in
/-- The homotopy has degree `-1` for the suspended gradings. -/
private theorem isHomogeneous_homotopy_shift :
    LinearMap.IsHomogeneous c.homotopy (𝒜.grading.shift 1).piece (𝒜.grading.shift 1).piece (-1) :=
  LinearMap.isHomogeneous_shift_piece_iff.2 hh

include hincl in
/-- The inclusion has degree zero for the suspended gradings. -/
private theorem isHomogeneous_incl_shift :
    LinearMap.IsHomogeneous c.incl (GH.shift 1).piece (𝒜.grading.shift 1).piece 0 :=
  LinearMap.isHomogeneous_shift_piece_iff.2 hincl

include hproj in
/-- The projection has degree zero for the suspended gradings. -/
private theorem isHomogeneous_proj_shift :
    LinearMap.IsHomogeneous c.proj (𝒜.grading.shift 1).piece (GH.shift 1).piece 0 :=
  LinearMap.isHomogeneous_shift_piece_iff.2 hproj

/-- The **tensor trick for the bar construction**: a special contraction of `(A, m₁)` onto
`(H, d_H)` by maps of the expected degrees induces a special contraction of the reduced tensor
coalgebras of `sA` and `sH` for the letterwise differentials.  The letterwise differential of
`Tᶜ(sA)` is the unary part of the bar differential of `𝒜`
(`TauCeti.AInfinityAlgebra.unaryBarDifferential_eq_gradedCoderiv`). -/
noncomputable def barTensorTrick :
    LinearSpecialContraction
      (gradedCoderiv (𝒜.grading.shift 1) (𝒜.differential ∘ₗ letter R A) 1)
      (gradedCoderiv (GH.shift 1) (dH ∘ₗ letter R H) 1) :=
  c.reducedTensorWords (𝒜.grading.shift 1) (GH.shift 1) 𝒜.isHomogeneous_differential_shift_one
    (𝒜.isHomogeneous_homotopy_shift c hh) (𝒜.isHomogeneous_incl_shift c hincl)
    (𝒜.isHomogeneous_proj_shift c hproj)

/-- The inclusion of the bar tensor trick is the letterwise inclusion. -/
@[simp]
theorem barTensorTrick_incl :
    (𝒜.barTensorTrick c hh hincl hproj).incl = ReducedTensorWords.map (R := R) c.incl :=
  LinearSpecialContraction.reducedTensorWords_incl ..

/-- The projection of the bar tensor trick is the letterwise projection. -/
@[simp]
theorem barTensorTrick_proj :
    (𝒜.barTensorTrick c hh hincl hproj).proj = ReducedTensorWords.map (R := R) c.proj :=
  LinearSpecialContraction.reducedTensorWords_proj ..

/-- The homotopy of the bar tensor trick is the tensor-trick homotopy for the suspended grading. -/
@[simp]
theorem barTensorTrick_homotopy :
    (𝒜.barTensorTrick c hh hincl hproj).homotopy =
      c.reducedTensorWordsHomotopy (𝒜.grading.shift 1) :=
  LinearSpecialContraction.reducedTensorWords_homotopy ..

/-- The higher bar differential is a perturbation of the letterwise differential `D` of `Tᶜ(sA)`:
`(D + δ)² = D²`, since `D + δ` is the bar differential and both sides vanish. -/
theorem gradedCoderiv_differential_add_higherBarDifferential_comp_self :
    (gradedCoderiv (𝒜.grading.shift 1) (𝒜.differential ∘ₗ letter R A) 1 +
        𝒜.higherBarDifferential) ∘ₗ
      (gradedCoderiv (𝒜.grading.shift 1) (𝒜.differential ∘ₗ letter R A) 1 +
        𝒜.higherBarDifferential) =
      gradedCoderiv (𝒜.grading.shift 1) (𝒜.differential ∘ₗ letter R A) 1 ∘ₗ
        gradedCoderiv (𝒜.grading.shift 1) (𝒜.differential ∘ₗ letter R A) 1 := by
  rw [← unaryBarDifferential_eq_gradedCoderiv, ← barDifferential_eq_unary_add_higher,
    barDifferential_sq, unaryBarDifferential_comp_self]

/-- The unit hypothesis of the perturbation lemma for the higher bar differential and the
tensor-trick contraction. -/
theorem isUnit_one_add_higherBarDifferential_mul_barTensorTrick_homotopy :
    IsUnit (1 + 𝒜.higherBarDifferential * (𝒜.barTensorTrick c hh hincl hproj).homotopy) := by
  rw [barTensorTrick_homotopy]
  exact 𝒜.isUnit_one_add_higherBarDifferential_comp_homotopy c

/-- The perturbation operator `X = (1 + δ K)⁻¹ δ` of the bar construction has degree one. -/
private theorem isHomogeneous_perturbationSeries :
    LinearMap.IsHomogeneous
      ((𝒜.barTensorTrick c hh hincl hproj).perturbationSeries 𝒜.higherBarDifferential)
      (gradedPiece (𝒜.grading.shift 1))
      (gradedPiece (𝒜.grading.shift 1)) 1 := by
  have hδh : LinearMap.IsHomogeneous
      (𝒜.higherBarDifferential * (𝒜.barTensorTrick c hh hincl hproj).homotopy)
      (gradedPiece (𝒜.grading.shift 1)) (gradedPiece (𝒜.grading.shift 1)) 0 := by
    rw [barTensorTrick_homotopy, Module.End.mul_eq_comp]
    simpa only [neg_add_cancel] using 𝒜.isHomogeneous_higherBarDifferential.comp
      (c.isHomogeneous_reducedTensorWordsHomotopy (𝒜.grading.shift 1)
        (𝒜.isHomogeneous_homotopy_shift c hh) (𝒜.isHomogeneous_incl_shift c hincl)
        (𝒜.isHomogeneous_proj_shift c hproj))
  have hinv := hδh.ringInverse_one_add fun z ↦ by
    rw [barTensorTrick_homotopy, Module.End.mul_eq_comp]
    exact 𝒜.exists_pow_higherBarDifferential_comp_homotopy_eq_zero c z
  rw [LinearSpecialContraction.perturbationSeries_def, Module.End.mul_eq_comp]
  simpa only [add_zero] using hinv.comp 𝒜.isHomogeneous_higherBarDifferential

/-- The perturbation operator kills single letters, since the higher bar differential does. -/
private theorem perturbationSeries_ofLetter (a : A) :
    (𝒜.barTensorTrick c hh hincl hproj).perturbationSeries 𝒜.higherBarDifferential
      (ofLetter R A a) = 0 := by
  rw [LinearSpecialContraction.perturbationSeries_def, Module.End.mul_apply,
    higherBarDifferential_ofLetter, map_zero]

/-- On words of length at most two the perturbation operator is the higher bar differential: the
higher bar differential of such a word is a single letter, on which `1 + δ K` is the identity. -/
private theorem perturbationSeries_of_mem_filtration_two {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A 2) :
    (𝒜.barTensorTrick c hh hincl hproj).perturbationSeries 𝒜.higherBarDifferential z =
      𝒜.higherBarDifferential z := by
  set T := 𝒜.barTensorTrick c hh hincl hproj
  have h1 : 𝒜.higherBarDifferential z ∈ filtration R A 1 :=
    𝒜.higherBarDifferential_filtration 1 ⟨z, hz, rfl⟩
  have h2 : T.homotopy (𝒜.higherBarDifferential z) ∈ filtration R A 1 := by
    rw [barTensorTrick_homotopy]
    exact c.reducedTensorWordsHomotopy_filtration (𝒜.grading.shift 1) 1 ⟨_, h1, rfl⟩
  have h3 : 𝒜.higherBarDifferential (T.homotopy (𝒜.higherBarDifferential z)) = 0 := by
    have h := 𝒜.higherBarDifferential_filtration 0 ⟨_, h2, rfl⟩
    rwa [filtration_zero, Submodule.mem_bot] at h
  have hfix : (1 + 𝒜.higherBarDifferential * T.homotopy) (𝒜.higherBarDifferential z) =
      𝒜.higherBarDifferential z := by
    rw [LinearMap.add_apply, Module.End.one_apply, Module.End.mul_apply, h3, add_zero]
  rw [LinearSpecialContraction.perturbationSeries_def, Module.End.mul_apply]
  conv_lhs => rw [← hfix]
  rw [← Module.End.mul_apply, Ring.inverse_mul_cancel _
    (𝒜.isUnit_one_add_higherBarDifferential_mul_barTensorTrick_homotopy c hh hincl hproj),
    Module.End.one_apply]

/-! ### The transferred bar differential -/

/-- The **transferred bar differential**: the perturbed differential `D' = D + p X i` of the
reduced tensor coalgebra of `sH`, obtained from the tensor-trick contraction by perturbing along
the higher bar differential of `𝒜`. -/
noncomputable def transferBarDifferential : Module.End R (ReducedTensorWords R H) :=
  (𝒜.barTensorTrick c hh hincl hproj).perturbedDifferential 𝒜.higherBarDifferential

/-- The transferred bar differential is a graded coderivation for the suspended grading. -/
theorem isGradedCoderivation_transferBarDifferential :
    IsGradedCoderivation (GH.shift 1) 1 (𝒜.transferBarDifferential c hh hincl hproj) :=
  c.isGradedCoderivation_reducedTensorWords_perturbedDifferential _ _ _ _
    (𝒜.gradedCoderiv_differential_add_higherBarDifferential_comp_self)
    (𝒜.isUnit_one_add_higherBarDifferential_mul_barTensorTrick_homotopy c hh hincl hproj)
    𝒜.isGradedCoderivation_higherBarDifferential 𝒜.isHomogeneous_higherBarDifferential
    𝒜.higherBarDifferential_filtration

/-- The transferred bar differential squares to zero. -/
@[simp]
theorem transferBarDifferential_comp_self :
    𝒜.transferBarDifferential c hh hincl hproj ∘ₗ 𝒜.transferBarDifferential c hh hincl hproj =
      0 :=
  LinearSpecialContraction.perturbedDifferential_comp_perturbedDifferential_eq_zero _ _
    (𝒜.gradedCoderiv_differential_add_higherBarDifferential_comp_self)
    (𝒜.isUnit_one_add_higherBarDifferential_mul_barTensorTrick_homotopy c hh hincl hproj)
    (by rw [← unaryBarDifferential_eq_gradedCoderiv, unaryBarDifferential_comp_self])

/-- The transferred bar differential has degree one for the suspended grading. -/
theorem isHomogeneous_transferBarDifferential :
    LinearMap.IsHomogeneous (𝒜.transferBarDifferential c hh hincl hproj)
      (gradedPiece (GH.shift 1)) (gradedPiece (GH.shift 1)) 1 := by
  have hD : LinearMap.IsHomogeneous (gradedCoderiv (GH.shift 1) (dH ∘ₗ letter R H) 1)
      (gradedPiece (GH.shift 1)) (gradedPiece (GH.shift 1)) 1 :=
    isHomogeneous_gradedCoderiv _ _ 1 1 <| by
      simpa only [zero_add] using
        ((LinearMap.isHomogeneous_shift_piece_iff (c := 1)).2 (c.isHomogeneous_dN
          (LinearMap.isHomogeneous_def.2 fun _ _ hx ↦ 𝒜.differential_mem_piece hx) hincl
          hproj)).comp
          (isHomogeneous_letter (GH.shift 1))
  have hpXi := (isHomogeneous_map _ _ (𝒜.isHomogeneous_proj_shift c hproj)).comp
    ((𝒜.isHomogeneous_perturbationSeries c hh hincl hproj).comp
      (isHomogeneous_map _ _ (𝒜.isHomogeneous_incl_shift c hincl)))
  rw [transferBarDifferential, LinearSpecialContraction.perturbedDifferential_def,
    barTensorTrick_incl, barTensorTrick_proj]
  simpa only [zero_add, add_zero] using hD.add hpXi

/-- The transferred bar differential is the coderivation generated by its letter component. -/
theorem gradedCoderiv_letter_comp_transferBarDifferential :
    gradedCoderiv (GH.shift 1) (letter R H ∘ₗ 𝒜.transferBarDifferential c hh hincl hproj) 1 =
      𝒜.transferBarDifferential c hh hincl hproj :=
  (isGradedCoderivation_gradedCoderiv _ _ 1).eq_of_letter_comp_eq
    (𝒜.isGradedCoderivation_transferBarDifferential c hh hincl hproj)
    (letter_comp_gradedCoderiv _ _ 1)

/-! ### The transferred structure and the extending morphism -/

/-- The **transferred `A∞` structure** on the retract `H` of a special contraction of `(A, m₁)`:
its Taylor map is the letter component of the transferred bar differential. -/
noncomputable def transfer : AInfinityAlgebra R H :=
  ofTaylor GH (letter R H ∘ₗ 𝒜.transferBarDifferential c hh hincl hproj)
    (by
      simpa only [add_zero] using (isHomogeneous_letter (GH.shift 1)).comp
        (𝒜.isHomogeneous_transferBarDifferential c hh hincl hproj))
    (by
      rw [gradedCoderiv_letter_comp_transferBarDifferential, transferBarDifferential_comp_self])

/-- The transferred structure lives on the grading of the retract. -/
@[simp]
theorem transfer_grading : (𝒜.transfer c hh hincl hproj).grading = GH := by
  rw [transfer, ofTaylor_grading]

/-- The Taylor map of the transferred structure is the letter component of the transferred bar
differential. -/
@[simp]
theorem transfer_taylor :
    (𝒜.transfer c hh hincl hproj).taylor =
      letter R H ∘ₗ 𝒜.transferBarDifferential c hh hincl hproj := by
  rw [transfer, ofTaylor_taylor]

/-- The bar differential of the transferred structure is the transferred bar differential. -/
@[simp]
theorem barDifferential_transfer :
    (𝒜.transfer c hh hincl hproj).barDifferential = 𝒜.transferBarDifferential c hh hincl hproj :=
  by rw [transfer, barDifferential_ofTaylor, gradedCoderiv_letter_comp_transferBarDifferential]

/-- The **extending `A∞` morphism** from the transferred structure to `𝒜`: its bar map is the
perturbed inclusion `i' = i - K X i` of the bar constructions, where `K` is the tensor-trick
homotopy and `X = (1 + δ K)⁻¹ δ`. -/
noncomputable def transferInclusion : AInfinityHom (𝒜.transfer c hh hincl hproj) 𝒜 where
  barMap := ((𝒜.barTensorTrick c hh hincl hproj).perturb 𝒜.higherBarDifferential
    𝒜.gradedCoderiv_differential_add_higherBarDifferential_comp_self
    (𝒜.isUnit_one_add_higherBarDifferential_mul_barTensorTrick_homotopy c hh hincl hproj)).incl
  isCoalgHom_barMap :=
    c.isCoalgHom_reducedTensorWords_perturb_incl _ _ _ _
      𝒜.gradedCoderiv_differential_add_higherBarDifferential_comp_self
      (𝒜.isUnit_one_add_higherBarDifferential_mul_barTensorTrick_homotopy c hh hincl hproj)
      𝒜.isGradedCoderivation_higherBarDifferential 𝒜.higherBarDifferential_filtration
  isHomogeneous_barMap := by
    have hi := isHomogeneous_map (R := R) _ _ (𝒜.isHomogeneous_incl_shift c hincl)
    have hH := c.isHomogeneous_reducedTensorWordsHomotopy (𝒜.grading.shift 1)
      (𝒜.isHomogeneous_homotopy_shift c hh) (𝒜.isHomogeneous_incl_shift c hincl)
      (𝒜.isHomogeneous_proj_shift c hproj)
    have hHXi := hH.comp ((𝒜.isHomogeneous_perturbationSeries c hh hincl hproj).comp hi)
    rw [LinearSpecialContraction.perturb_incl, barTensorTrick_incl, barTensorTrick_homotopy,
      transfer_grading]
    exact hi.sub (by simpa only [zero_add, add_zero, add_neg_cancel] using hHXi)
  barDifferential_comp_barMap := by
    rw [barDifferential_transfer, barDifferential_eq_unary_add_higher,
      unaryBarDifferential_eq_gradedCoderiv]
    exact LinearSpecialContraction.dM_comp_incl _

/-- The bar map of the extending morphism is the perturbed inclusion `i - K X i`. -/
theorem barMap_transferInclusion :
    (𝒜.transferInclusion c hh hincl hproj).barMap =
      ReducedTensorWords.map (R := R) c.incl -
        c.reducedTensorWordsHomotopy (𝒜.grading.shift 1) ∘ₗ
          (𝒜.barTensorTrick c hh hincl hproj).perturbationSeries 𝒜.higherBarDifferential ∘ₗ
          ReducedTensorWords.map (R := R) c.incl :=
  calc (𝒜.transferInclusion c hh hincl hproj).barMap
      _ = ((𝒜.barTensorTrick c hh hincl hproj).perturb 𝒜.higherBarDifferential
          𝒜.gradedCoderiv_differential_add_higherBarDifferential_comp_self
          (𝒜.isUnit_one_add_higherBarDifferential_mul_barTensorTrick_homotopy c hh hincl
            hproj)).incl := rfl
      _ = _ := by
        rw [LinearSpecialContraction.perturb_incl, barTensorTrick_incl, barTensorTrick_homotopy]

/-- The linear part of the extending morphism is the inclusion of the contraction. -/
@[simp]
theorem linearPart_transferInclusion :
    (𝒜.transferInclusion c hh hincl hproj).linearPart = c.incl := by
  ext a
  rw [AInfinityHom.linearPart_apply, AInfinityHom.taylor_def, LinearMap.comp_apply,
    barMap_transferInclusion, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    map_ofLetter, perturbationSeries_ofLetter, map_zero, sub_zero, letter_ofLetter]

/-! ### Low arities -/

/-- The letter component of the transferred bar differential: the letterwise differential of
`Tᶜ(sH)` contributes `d_H` on single letters, and the perturbation contributes `p X i`. -/
private theorem letter_transferBarDifferential (w : ReducedTensorWords R H) :
    letter R H (𝒜.transferBarDifferential c hh hincl hproj w) =
      dH (letter R H w) + c.proj (letter R A
        ((𝒜.barTensorTrick c hh hincl hproj).perturbationSeries 𝒜.higherBarDifferential
          (ReducedTensorWords.map (R := R) c.incl w))) := by
  have hD := LinearMap.congr_fun (letter_comp_gradedCoderiv (GH.shift 1) (dH ∘ₗ letter R H) 1) w
  have hp := LinearMap.congr_fun (letter_comp_map (R := R) c.proj) <|
    (𝒜.barTensorTrick c hh hincl hproj).perturbationSeries 𝒜.higherBarDifferential
      (ReducedTensorWords.map (R := R) c.incl w)
  simp only [LinearMap.comp_apply] at hD hp
  rw [transferBarDifferential, LinearSpecialContraction.perturbedDifferential_def,
    barTensorTrick_incl, barTensorTrick_proj, LinearMap.add_apply, map_add, hD,
    LinearMap.comp_apply, LinearMap.comp_apply, hp]

/-- The transferred unary operation is the differential of the retract. -/
@[simp]
theorem differential_transfer : (𝒜.transfer c hh hincl hproj).differential = dH := by
  ext x
  rw [differential_apply, ← taylor_ofLetter, transfer_taylor, LinearMap.comp_apply,
    letter_transferBarDifferential, letter_ofLetter, map_ofLetter, perturbationSeries_ofLetter,
    map_zero, map_zero, add_zero]

/-- The transferred structure is minimal when the retract has zero differential. -/
theorem isMinimal_transfer (hdH : dH = 0) : (𝒜.transfer c hh hincl hproj).IsMinimal := by
  rw [isMinimal_def, differential_transfer, hdH]

/-- The transferred binary operation is `p m₂ (i ⊗ i)`. -/
@[simp]
theorem mul_transfer (a b : H) :
    (𝒜.transfer c hh hincl hproj).m 2 ![a, b] = c.proj (𝒜.mul (c.incl a) (c.incl b)) := by
  set τ := GH.koszulTwist 1
  have hτi : 𝒜.grading.koszulTwist 1 (c.incl (τ a)) = c.incl a := by
    have h := LinearMap.congr_fun (hincl.koszulTwist_comp 1) (τ a)
    simp only [mul_zero, Int.negOnePow_zero, Units.val_one, Int.cast_one, one_smul,
      LinearMap.comp_apply] at h
    rw [h, ← LinearMap.comp_apply τ, InternalGrading.koszulTwist_comp_self, LinearMap.id_apply]
  have hw : ReducedTensorWords.map (R := R) c.incl
      (of R H (2 : ℕ+) (PiTensorProduct.tprod R ![τ a, b])) =
        of R A (2 : ℕ+) (PiTensorProduct.tprod R ![c.incl (τ a), c.incl b]) := by
    refine (map_of_tprod (R := R) c.incl (2 : ℕ+) ![τ a, b]).trans ?_
    congr 2
    funext i
    fin_cases i <;> rfl
  have hfil : of R A (2 : ℕ+) (PiTensorProduct.tprod R ![c.incl (τ a), c.incl b]) ∈
      filtration R A 2 := by
    rw [← prepend_ofLetter]
    exact prepend_mem_filtration R A _ (ofLetter_mem_filtration R A _)
  have hab : (𝒜.transfer c hh hincl hproj).m 2 ![a, b] =
      (𝒜.transfer c hh hincl hproj).taylor
        (of R H (2 : ℕ+) (PiTensorProduct.tprod R ![τ a, b])) := by
    rw [← mul_apply, taylor_of_two, transfer_grading, mul_apply, ← LinearMap.comp_apply τ,
      InternalGrading.koszulTwist_comp_self, LinearMap.id_apply]
  have hδ : letter R A (𝒜.higherBarDifferential
      (of R A (2 : ℕ+) (PiTensorProduct.tprod R ![c.incl (τ a), c.incl b]))) =
        𝒜.mul (c.incl a) (c.incl b) := by
    rw [← LinearMap.comp_apply (letter R A), letter_comp_higherBarDifferential,
      𝒜.higherTaylor_of (2 : ℕ+) (by decide), taylor_of_two, hτi, mul_apply]
  rw [hab, transfer_taylor, LinearMap.comp_apply, letter_transferBarDifferential, letter_of_two,
    map_zero, zero_add, hw, 𝒜.perturbationSeries_of_mem_filtration_two c hh hincl hproj hfil, hδ]

/-! ### The extending morphism is a quasi-isomorphism -/

/-- The extending morphism is a quasi-isomorphism: on cohomology, the inclusion of a special
contraction is inverse to the map induced by its projection. -/
theorem isQuasiIso_transferInclusion : (𝒜.transferInclusion c hh hincl hproj).IsQuasiIso := by
  set 𝒯 := 𝒜.transfer c hh hincl hproj
  have hmT (x : H) : 𝒯.m 1 ![x] = dH x := by
    rw [← differential_apply, differential_transfer]
  have hpd (y : A) : c.proj (𝒜.m 1 ![y]) = dH (c.proj y) := by
    rw [← differential_apply, c.proj_dM_apply]
  rw [AInfinityHom.isQuasiIso_def]
  refine ⟨(injective_iff_map_eq_zero _).2 fun u hu ↦ ?_, fun v ↦ ?_⟩
  · obtain ⟨x, hx, rfl⟩ := 𝒯.exists_cohomologyClass_eq u
    rw [AInfinityHom.cohomologyMap_cohomologyClass, cohomologyClass_eq_zero_iff, mem_boundaries,
      linearPart_transferInclusion] at hu
    obtain ⟨y, hy⟩ := hu
    rw [cohomologyClass_eq_zero_iff, mem_boundaries]
    exact ⟨c.proj y, by rw [hmT, ← hpd, hy, c.proj_incl_apply]⟩
  · obtain ⟨z, hz, rfl⟩ := 𝒜.exists_cohomologyClass_eq v
    have hz' : 𝒜.m 1 ![z] = 0 := 𝒜.mem_cycles.1 hz
    have hpz : c.proj z ∈ 𝒯.cycles := by
      rw [mem_cycles, hmT, ← hpd, hz', map_zero]
    refine ⟨𝒯.cohomologyClass hpz, ?_⟩
    rw [AInfinityHom.cohomologyMap_cohomologyClass, cohomologyClass_eq_iff, mem_boundaries,
      linearPart_transferInclusion]
    refine ⟨-c.homotopy z, ?_⟩
    have hc := LinearMap.congr_fun c.dM_comp_homotopy_add_homotopy_comp_dM z
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.id_apply, differential_apply, hz', map_zero, add_zero] at hc
    rw [← differential_apply, map_neg, differential_apply, hc, neg_sub]

end TauCeti.AInfinityAlgebra
