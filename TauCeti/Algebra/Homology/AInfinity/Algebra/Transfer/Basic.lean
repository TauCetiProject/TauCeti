/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.AInfinity.Algebra.Hom.Cohomology
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Minimal
public import TauCeti.Algebra.Homology.AInfinity.Algebra.Transfer.Perturbation
public import TauCeti.Algebra.Homology.Contraction.TensorTrick.Perturbation.Basic

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
part is `i`, so it is a quasi-isomorphism.  Dually, the perturbed projection `p' = p - p X K` is
a coalgebra morphism intertwining the bar differential of `𝒜` with `D'`, hence an `A∞` morphism
`TauCeti.AInfinityAlgebra.transferProjection` from `𝒜` to the transferred structure.  Its linear
part is `p`, it is a left inverse of the extending morphism, and so it is a quasi-isomorphism too.

In low arity the transferred structure has `m₁ = d_H`, `m₂ = p ∘ m₂ ∘ (i ⊗ i)` and the
Kontsevich--Soibelman/Merkulov ternary operation
`m₃ = p m₃ (i ⊗ i ⊗ i) + p m₂ (h m₂ (i ⊗ i) ⊗ i) - p m₂ (i ⊗ h m₂ (i ⊗ i))`, the last term with
the Koszul sign of moving `h` past the first input; in particular it is minimal when `d_H = 0`.
The extending morphism has quadratic component `f₂ = -h m₂ (i ⊗ i)`.

## Main definitions

* `TauCeti.AInfinityAlgebra.barTensorTrick`: the tensor-trick contraction of the bar
  constructions.
* `TauCeti.AInfinityAlgebra.transfer`: the transferred `A∞` structure on `H`.
* `TauCeti.AInfinityAlgebra.transferInclusion`: the `A∞` morphism extending `i`.
* `TauCeti.AInfinityAlgebra.transferProjection`: the `A∞` morphism extending `p`.

## Main results

* `TauCeti.AInfinityAlgebra.barDifferential_transfer`: the bar differential of the transferred
  structure is the perturbed differential `D'`.
* `TauCeti.AInfinityAlgebra.linearPart_transferInclusion`: the linear part of the extending
  morphism is the inclusion of the contraction.
* `TauCeti.AInfinityAlgebra.isQuasiIso_transferInclusion`: the extending morphism is a
  quasi-isomorphism.
* `TauCeti.AInfinityAlgebra.linearPart_transferProjection`,
  `TauCeti.AInfinityAlgebra.transferProjection_comp_transferInclusion` and
  `TauCeti.AInfinityAlgebra.isQuasiIso_transferProjection`: the projection morphism has linear part
  `p`, is a left inverse of the extending morphism, and is a quasi-isomorphism.
* `TauCeti.AInfinityAlgebra.differential_transfer` and `TauCeti.AInfinityAlgebra.mul_transfer`:
  the transferred `m₁` is `d_H` and the transferred `m₂` is `p m₂ (i ⊗ i)`.
* `TauCeti.AInfinityAlgebra.m_three_transfer`: the transferred `m₃` is the
  Kontsevich--Soibelman/Merkulov tree sum `p m₃ (i ⊗ i ⊗ i) + p m₂ (h m₂ ⊗ 1)(i ⊗ i ⊗ i)
  - p m₂ (1 ⊗ h m₂)(i ⊗ i ⊗ i)`.
* `TauCeti.AInfinityAlgebra.component_two_transferInclusion`: the quadratic component of the
  extending morphism is `-h m₂ (i ⊗ i)`.

## References

* V. K. A. M. Gugenheim, L. A. Lambe, and J. D. Stasheff, *Perturbation theory in differential
  homological algebra II*, Illinois Journal of Mathematics 35 (1991), 357--373.
* J. Huebschmann and T. Kadeishvili, *Small models for chain algebras*, Mathematische Zeitschrift
  207 (1991), 245--280.
* B. Keller, *Introduction to A-infinity algebras and modules*, Section 3.3.
* M. Kontsevich and Y. Soibelman, *Homological mirror symmetry and torus fibrations*,
  Section 6.4, and S. A. Merkulov, *Strong homotopy algebras of a Kähler manifold*, for the
  tree formulas of the transferred operations in low arity.
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

/-- The bar tensor trick is the reduced tensor-word contraction for the suspended gradings.
The homogeneity witness for the differential may be supplied by the caller. -/
theorem barTensorTrick_def
    (hd : LinearMap.IsHomogeneous 𝒜.differential (𝒜.grading.shift 1).piece
      (𝒜.grading.shift 1).piece 1) :
    𝒜.barTensorTrick c hh hincl hproj =
      c.reducedTensorWords (𝒜.grading.shift 1) (GH.shift 1) hd
        (LinearMap.isHomogeneous_shift_piece_iff.2 hh)
        (LinearMap.isHomogeneous_shift_piece_iff.2 hincl)
        (LinearMap.isHomogeneous_shift_piece_iff.2 hproj) := (rfl)

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
theorem isHomogeneous_perturbationSeries :
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

/-- The higher bar differential strictly lowers tensor length. -/
private theorem higherBarDifferential_mem_filtration {n : ℕ} {w : ReducedTensorWords R A}
    (hw : w ∈ filtration R A (n + 1)) : 𝒜.higherBarDifferential w ∈ filtration R A n :=
  𝒜.higherBarDifferential_filtration n ⟨w, hw, rfl⟩

/-- The homotopy of the bar tensor trick preserves tensor length. -/
private theorem barTensorTrick_homotopy_mem_filtration {n : ℕ} {w : ReducedTensorWords R A}
    (hw : w ∈ filtration R A n) :
    (𝒜.barTensorTrick c hh hincl hproj).homotopy w ∈ filtration R A n := by
  rw [barTensorTrick_homotopy]
  exact c.reducedTensorWordsHomotopy_filtration (𝒜.grading.shift 1) n ⟨w, hw, rfl⟩

/-- On words of length at most two the perturbation operator is the higher bar differential: the
higher bar differential of such a word is a single letter, on which `1 + δ K` is the identity. -/
private theorem perturbationSeries_of_mem_filtration_two {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A 2) :
    (𝒜.barTensorTrick c hh hincl hproj).perturbationSeries 𝒜.higherBarDifferential z =
      𝒜.higherBarDifferential z := by
  have h0 : ((𝒜.higherBarDifferential * (𝒜.barTensorTrick c hh hincl hproj).homotopy) ^ 1)
      (𝒜.higherBarDifferential z) = 0 := by
    have h := 𝒜.higherBarDifferential_mem_filtration
      (𝒜.barTensorTrick_homotopy_mem_filtration c hh hincl hproj
        (𝒜.higherBarDifferential_mem_filtration hz))
    rw [filtration_zero, Submodule.mem_bot] at h
    rwa [pow_one, Module.End.mul_apply]
  rw [LinearSpecialContraction.perturbationSeries_apply_eq_sum_of_pow_apply_eq_zero _ _
    (𝒜.isUnit_one_add_higherBarDifferential_mul_barTensorTrick_homotopy c hh hincl hproj) h0,
    Finset.sum_range_one, pow_zero, Module.End.one_apply]

/-! ### The transferred bar differential -/

/-- The **transferred bar differential**: the perturbed differential `D' = D + p X i` of the
reduced tensor coalgebra of `sH`, obtained from the tensor-trick contraction by perturbing along
the higher bar differential of `𝒜`. -/
noncomputable def transferBarDifferential : Module.End R (ReducedTensorWords R H) :=
  (𝒜.barTensorTrick c hh hincl hproj).perturbedDifferential 𝒜.higherBarDifferential

/-- The transferred bar differential is the perturbed differential of the bar tensor trick. -/
theorem transferBarDifferential_def :
    𝒜.transferBarDifferential c hh hincl hproj =
      (𝒜.barTensorTrick c hh hincl hproj).perturbedDifferential 𝒜.higherBarDifferential := (rfl)

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
theorem letter_transferBarDifferential (w : ReducedTensorWords R H) :
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

/-- The letterwise inclusion of a two-letter word. -/
private theorem map_incl_of_two (x y : H) :
    ReducedTensorWords.map (R := R) c.incl (of R H (2 : ℕ+) (PiTensorProduct.tprod R ![x, y])) =
      of R A (2 : ℕ+) (PiTensorProduct.tprod R ![c.incl x, c.incl y]) := by
  refine (map_of_tprod (R := R) c.incl (2 : ℕ+) ![x, y]).trans ?_
  congr 2
  funext i
  fin_cases i <;> rfl

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
    map_zero, zero_add, 𝒜.map_incl_of_two c,
    𝒜.perturbationSeries_of_mem_filtration_two c hh hincl hproj hfil, hδ]

/-! ### Arity three and the quadratic component of the extending morphism -/

/-- On words of length at most three the perturbation operator is `δ - δ K δ`: the next term
`δ K δ K δ` of the geometric series already vanishes, since `δ` strictly lowers tensor length, `K`
preserves it, and `δ` kills single letters. -/
private theorem perturbationSeries_of_mem_filtration_three {z : ReducedTensorWords R A}
    (hz : z ∈ filtration R A 3) :
    (𝒜.barTensorTrick c hh hincl hproj).perturbationSeries 𝒜.higherBarDifferential z =
      𝒜.higherBarDifferential z -
        𝒜.higherBarDifferential ((𝒜.barTensorTrick c hh hincl hproj).homotopy
          (𝒜.higherBarDifferential z)) := by
  have h0 : ((𝒜.higherBarDifferential * (𝒜.barTensorTrick c hh hincl hproj).homotopy) ^ 2)
      (𝒜.higherBarDifferential z) = 0 := by
    have h := 𝒜.higherBarDifferential_mem_filtration
      (𝒜.barTensorTrick_homotopy_mem_filtration c hh hincl hproj
        (𝒜.higherBarDifferential_mem_filtration
          (𝒜.barTensorTrick_homotopy_mem_filtration c hh hincl hproj
            (𝒜.higherBarDifferential_mem_filtration hz))))
    rw [filtration_zero, Submodule.mem_bot] at h
    rwa [pow_two, Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply]
  rw [LinearSpecialContraction.perturbationSeries_apply_eq_sum_of_pow_apply_eq_zero _ _
    (𝒜.isUnit_one_add_higherBarDifferential_mul_barTensorTrick_homotopy c hh hincl hproj) h0,
    Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one, Module.End.one_apply,
    LinearMap.neg_apply, Module.End.mul_apply, sub_eq_add_neg]

include hincl in
/-- The inclusion of the contraction has degree zero, so it intertwines the Koszul twists. -/
private theorem koszulTwist_incl_apply (x : H) :
    𝒜.grading.koszulTwist 1 (c.incl x) = c.incl (GH.koszulTwist 1 x) := by
  simpa using LinearMap.congr_fun (hincl.koszulTwist_comp 1) x

include hh in
/-- The homotopy of the contraction has degree `-1`, so it anticommutes with the degree-one
Koszul twist. -/
private theorem homotopy_koszulTwist_apply (u : A) :
    c.homotopy (𝒜.grading.koszulTwist 1 u) = -𝒜.grading.koszulTwist 1 (c.homotopy u) := by
  have h := LinearMap.congr_fun (hh.koszulTwist_comp 1) u
  simp only [mul_neg, mul_one, Int.reduceNeg, Int.negOnePow_neg, Int.negOnePow_one, Units.val_neg,
    Units.val_one, Int.cast_neg, Int.cast_one, neg_smul, one_smul, LinearMap.comp_apply,
    LinearMap.neg_apply] at h
  rw [h, neg_neg]

/-- The letterwise inclusion of a three-letter word. -/
private theorem map_incl_of_three (x y z : H) :
    ReducedTensorWords.map (R := R) c.incl
        (of R H (3 : ℕ+) (PiTensorProduct.tprod R ![x, y, z])) =
      of R A (3 : ℕ+) (PiTensorProduct.tprod R ![c.incl x, c.incl y, c.incl z]) := by
  refine (map_of_tprod (R := R) c.incl (3 : ℕ+) ![x, y, z]).trans ?_
  congr 2
  funext i
  fin_cases i <;> rfl

include hincl in
/-- The degree-one Koszul twist of the suspended grading sends an included twisted letter to minus
the included letter. -/
private theorem koszulTwist_shift_one_incl_apply (x : H) :
    (𝒜.grading.shift 1).koszulTwist 1 (c.incl (GH.koszulTwist 1 x)) = -c.incl x := by
  rw [InternalGrading.koszulTwist_one_shift_one, LinearMap.neg_apply,
    𝒜.koszulTwist_incl_apply c hincl, GH.koszulTwist_koszulTwist]

include hh hincl in
/-- The **twisted binary homotopy**: the Koszul twist of the homotopy of the product of two
twisted included inputs is minus the homotopy of the product of the inputs, since the twist
commutes with the binary operation and the inclusion and anticommutes with the homotopy. -/
private theorem koszulTwist_homotopy_m_two_incl (x y : H) :
    𝒜.grading.koszulTwist 1 (c.homotopy
        (𝒜.m 2 ![c.incl (GH.koszulTwist 1 x), c.incl (GH.koszulTwist 1 y)])) =
      -c.homotopy (𝒜.m 2 ![c.incl x, c.incl y]) := by
  rw [← 𝒜.koszulTwist_incl_apply c hincl x, ← 𝒜.koszulTwist_incl_apply c hincl y,
    ← koszulTwist_m_two, 𝒜.homotopy_koszulTwist_apply c hh, map_neg,
    InternalGrading.koszulTwist_koszulTwist]

/-- The tensor-trick homotopy applied to the higher bar differential of an included three-letter
word: the side conditions `h i = 0` and `p i = 1` kill all but three terms. -/
private theorem barTensorTrick_homotopy_higherBarDifferential_of_three (x y z : H) :
    (𝒜.barTensorTrick c hh hincl hproj).homotopy (𝒜.higherBarDifferential
        (of R A (3 : ℕ+) (PiTensorProduct.tprod R ![c.incl x, c.incl y, c.incl z]))) =
      of R A (2 : ℕ+) (PiTensorProduct.tprod R
          ![c.homotopy (𝒜.m 2 ![c.incl (GH.koszulTwist 1 x), c.incl y]), c.incl z]) +
        of R A (2 : ℕ+) (PiTensorProduct.tprod R
          ![c.incl x, c.homotopy (𝒜.m 2 ![c.incl (GH.koszulTwist 1 y), c.incl z])]) +
        ofLetter R A (c.homotopy (𝒜.m 3 ![c.incl x, c.incl (GH.koszulTwist 1 y), c.incl z])) := by
  -- Structural evaluation: the tensor-trick homotopy on each word of the higher bar differential.
  rw [barTensorTrick_homotopy, higherBarDifferential_of_three, 𝒜.koszulTwist_incl_apply c hincl x,
    𝒜.koszulTwist_incl_apply c hincl y, map_add, map_sub, c.reducedTensorWordsHomotopy_of_two,
    c.reducedTensorWordsHomotopy_of_two, c.reducedTensorWordsHomotopy_ofLetter,
    𝒜.koszulTwist_shift_one_incl_apply c hincl x]
  -- The side conditions and additive normalization.
  simp only [c.proj_incl_apply, c.homotopy_incl_apply, ← prepend_ofLetter, map_zero,
    LinearMap.zero_apply, map_neg, LinearMap.neg_apply, add_zero, zero_add, sub_neg_eq_add]

/-- The letter component of the perturbation operator on an included three-letter word. -/
private theorem letter_perturbationSeries_of_three (x y z : H) :
    letter R A ((𝒜.barTensorTrick c hh hincl hproj).perturbationSeries 𝒜.higherBarDifferential
        (of R A (3 : ℕ+) (PiTensorProduct.tprod R ![c.incl x, c.incl y, c.incl z]))) =
      𝒜.m 3 ![c.incl x, c.incl (GH.koszulTwist 1 y), c.incl z] -
        𝒜.m 2 ![𝒜.grading.koszulTwist 1
          (c.homotopy (𝒜.m 2 ![c.incl (GH.koszulTwist 1 x), c.incl y])), c.incl z] -
        𝒜.m 2 ![c.incl (GH.koszulTwist 1 x),
          c.homotopy (𝒜.m 2 ![c.incl (GH.koszulTwist 1 y), c.incl z])] := by
  have hlt (w : ReducedTensorWords R A) :
      letter R A (𝒜.higherBarDifferential w) = 𝒜.higherTaylor w :=
    LinearMap.congr_fun 𝒜.letter_comp_higherBarDifferential w
  -- The leading term `δ` of the perturbation operator: the ternary operation on the word.
  have h₁ : letter R A (𝒜.higherBarDifferential
      (of R A (3 : ℕ+) (PiTensorProduct.tprod R ![c.incl x, c.incl y, c.incl z]))) =
        𝒜.m 3 ![c.incl x, c.incl (GH.koszulTwist 1 y), c.incl z] := by
    rw [hlt, 𝒜.higherTaylor_of (3 : ℕ+) (by decide), taylor_of_three,
      𝒜.koszulTwist_incl_apply c hincl y]
  -- The correction term `δ K δ`: the two binary products of a contracted adjacent pair.
  have h₂ : letter R A (𝒜.higherBarDifferential ((𝒜.barTensorTrick c hh hincl hproj).homotopy
      (𝒜.higherBarDifferential
        (of R A (3 : ℕ+) (PiTensorProduct.tprod R ![c.incl x, c.incl y, c.incl z]))))) =
        𝒜.m 2 ![𝒜.grading.koszulTwist 1
          (c.homotopy (𝒜.m 2 ![c.incl (GH.koszulTwist 1 x), c.incl y])), c.incl z] +
        𝒜.m 2 ![c.incl (GH.koszulTwist 1 x),
          c.homotopy (𝒜.m 2 ![c.incl (GH.koszulTwist 1 y), c.incl z])] := by
    rw [𝒜.barTensorTrick_homotopy_higherBarDifferential_of_three c hh hincl hproj]
    simp only [map_add, higherBarDifferential_ofLetter, add_zero, hlt]
    rw [𝒜.higherTaylor_of (2 : ℕ+) (by decide), 𝒜.higherTaylor_of (2 : ℕ+) (by decide),
      taylor_of_two, taylor_of_two, 𝒜.koszulTwist_incl_apply c hincl x]
  rw [𝒜.perturbationSeries_of_mem_filtration_three c hh hincl hproj
    (of_mem_filtration R A (k := (3 : ℕ+)) (by decide) _), map_sub, h₁, h₂, sub_add_eq_sub_sub]

/-- The **transferred ternary operation**, in the form of the Kontsevich--Soibelman/Merkulov
formulas: the ternary operation of `𝒜` on the included inputs, plus the two binary products in
which one adjacent pair of inputs has been multiplied and then contracted by the homotopy `h`.  The
second of these carries the Koszul sign `(-1)^|x|` of moving the degree `-1` map `h` past the first
input, encoded by the Koszul twist of that input. -/
@[simp]
theorem m_three_transfer (x y z : H) :
    (𝒜.transfer c hh hincl hproj).m 3 ![x, y, z] =
      c.proj (𝒜.m 3 ![c.incl x, c.incl y, c.incl z]) +
        c.proj (𝒜.m 2 ![c.homotopy (𝒜.m 2 ![c.incl x, c.incl y]), c.incl z]) -
        c.proj (𝒜.m 2 ![c.incl (GH.koszulTwist 1 x),
          c.homotopy (𝒜.m 2 ![c.incl y, c.incl z])]) := by
  -- Structural evaluation: the ternary operation is the projection of the letter component of the
  -- perturbation operator on the included word `x (τ y) z`, `τ` the Koszul twist.
  have hX : (𝒜.transfer c hh hincl hproj).m 3 ![x, y, z] =
      c.proj (letter R A ((𝒜.barTensorTrick c hh hincl hproj).perturbationSeries
        𝒜.higherBarDifferential (of R A (3 : ℕ+) (PiTensorProduct.tprod R
          ![c.incl x, c.incl (GH.koszulTwist 1 y), c.incl z])))) := by
    have hxyz : (𝒜.transfer c hh hincl hproj).m 3 ![x, y, z] =
        (𝒜.transfer c hh hincl hproj).taylor
          (of R H (3 : ℕ+) (PiTensorProduct.tprod R ![x, GH.koszulTwist 1 y, z])) := by
      rw [taylor_of_three, transfer_grading, GH.koszulTwist_koszulTwist]
    rw [hxyz, transfer_taylor, LinearMap.comp_apply, letter_transferBarDifferential,
      letter_of_of_ne_one R H (n := (3 : ℕ+)) (by decide), map_zero, zero_add,
      𝒜.map_incl_of_three c]
  -- The Koszul signs: the twisted binary homotopy carries the sign of the middle term.
  have hneg (u v : A) : 𝒜.m 2 ![-u, v] = -𝒜.m 2 ![u, v] := by
    simpa only [mul_apply, LinearMap.neg_apply] using LinearMap.congr_fun (𝒜.mul.map_neg u) v
  rw [hX, 𝒜.letter_perturbationSeries_of_three c hh hincl hproj, GH.koszulTwist_koszulTwist,
    𝒜.koszulTwist_homotopy_m_two_incl c hh hincl x y, hneg]
  simp only [map_add, map_sub, sub_neg_eq_add]

/-- The **quadratic component of the extending morphism** is `f₂ = -h m₂ (i ⊗ i)`. -/
@[simp]
theorem component_two_transferInclusion (x y : H) :
    (𝒜.transferInclusion c hh hincl hproj).component 2 ![x, y] =
      -c.homotopy (𝒜.m 2 ![c.incl x, c.incl y]) := by
  -- Structural evaluation: the quadratic component is minus the letter component of `K X` on the
  -- included word `(τ x) y`, `τ` the Koszul twist.
  have hX : (𝒜.transferInclusion c hh hincl hproj).component 2 ![x, y] =
      -letter R A (c.reducedTensorWordsHomotopy (𝒜.grading.shift 1)
        ((𝒜.barTensorTrick c hh hincl hproj).perturbationSeries 𝒜.higherBarDifferential
          (of R A (2 : ℕ+)
            (PiTensorProduct.tprod R ![c.incl (GH.koszulTwist 1 x), c.incl y])))) := by
    have hw : (fun i : Fin 2 ↦ (𝒜.transfer c hh hincl hproj).grading.koszulTwist
        (((2 : ℕ) : ℤ) - 1 - i) (![x, y] i)) = ![GH.koszulTwist 1 x, y] := by
      funext i
      fin_cases i <;> simp [transfer_grading, InternalGrading.koszulTwist_zero]
    have hcomp : (𝒜.transferInclusion c hh hincl hproj).component 2 ![x, y] =
        (𝒜.transferInclusion c hh hincl hproj).taylor
          (of R H (2 : ℕ+) (PiTensorProduct.tprod R ![GH.koszulTwist 1 x, y])) := by
      refine (AInfinityHom.component_apply _ 2 two_pos ![x, y]).trans ?_
      rw [hw]
      rfl
    rw [hcomp, AInfinityHom.taylor_def, LinearMap.comp_apply, barMap_transferInclusion,
      LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, 𝒜.map_incl_of_two c,
      map_sub, letter_of_two, zero_sub]
  -- On a two-letter word `X` is the higher bar differential, which collapses the word to the
  -- binary operation; the two Koszul twists of the first letter cancel.
  rw [hX, 𝒜.perturbationSeries_of_mem_filtration_two c hh hincl hproj
      (of_mem_filtration R A (k := (2 : ℕ+)) (by decide) _),
    higherBarDifferential_of_two, c.reducedTensorWordsHomotopy_ofLetter, letter_ofLetter,
    𝒜.koszulTwist_incl_apply c hincl, GH.koszulTwist_koszulTwist]

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

/-! ### The projection onto the transferred structure -/

/-- The **projection `A∞` morphism** from `𝒜` to the transferred structure: its bar map is the
perturbed projection `p' = p - p X K` of the bar constructions, where `K` is the tensor-trick
homotopy and `X = (1 + δ K)⁻¹ δ`. -/
noncomputable def transferProjection : AInfinityHom 𝒜 (𝒜.transfer c hh hincl hproj) where
  barMap := ((𝒜.barTensorTrick c hh hincl hproj).perturb 𝒜.higherBarDifferential
    𝒜.gradedCoderiv_differential_add_higherBarDifferential_comp_self
    (𝒜.isUnit_one_add_higherBarDifferential_mul_barTensorTrick_homotopy c hh hincl hproj)).proj
  isCoalgHom_barMap :=
    c.isCoalgHom_reducedTensorWords_perturb_proj _ _ _ _
      𝒜.gradedCoderiv_differential_add_higherBarDifferential_comp_self
      (𝒜.isUnit_one_add_higherBarDifferential_mul_barTensorTrick_homotopy c hh hincl hproj)
      𝒜.isGradedCoderivation_higherBarDifferential
  isHomogeneous_barMap := by
    have hp := isHomogeneous_map (R := R) _ _ (𝒜.isHomogeneous_proj_shift c hproj)
    have hH := c.isHomogeneous_reducedTensorWordsHomotopy (𝒜.grading.shift 1)
      (𝒜.isHomogeneous_homotopy_shift c hh) (𝒜.isHomogeneous_incl_shift c hincl)
      (𝒜.isHomogeneous_proj_shift c hproj)
    have hpXH := hp.comp ((𝒜.isHomogeneous_perturbationSeries c hh hincl hproj).comp hH)
    rw [LinearSpecialContraction.perturb_proj, barTensorTrick_proj, barTensorTrick_homotopy,
      transfer_grading]
    exact hp.sub (by simpa only [zero_add, add_zero, neg_add_cancel] using hpXH)
  barDifferential_comp_barMap := by
    rw [barDifferential_transfer, barDifferential_eq_unary_add_higher,
      unaryBarDifferential_eq_gradedCoderiv]
    exact (LinearSpecialContraction.proj_comp_dM _).symm

/-- The bar map of the projection morphism is the perturbed projection `p - p X K`. -/
theorem barMap_transferProjection :
    (𝒜.transferProjection c hh hincl hproj).barMap =
      ReducedTensorWords.map (R := R) c.proj -
        ReducedTensorWords.map (R := R) c.proj ∘ₗ
          (𝒜.barTensorTrick c hh hincl hproj).perturbationSeries 𝒜.higherBarDifferential ∘ₗ
          c.reducedTensorWordsHomotopy (𝒜.grading.shift 1) :=
  calc (𝒜.transferProjection c hh hincl hproj).barMap
      _ = ((𝒜.barTensorTrick c hh hincl hproj).perturb 𝒜.higherBarDifferential
          𝒜.gradedCoderiv_differential_add_higherBarDifferential_comp_self
          (𝒜.isUnit_one_add_higherBarDifferential_mul_barTensorTrick_homotopy c hh hincl
            hproj)).proj := rfl
      _ = _ := by
        rw [LinearSpecialContraction.perturb_proj, barTensorTrick_proj, barTensorTrick_homotopy]

/-- The linear part of the projection morphism is the projection of the contraction. -/
@[simp]
theorem linearPart_transferProjection :
    (𝒜.transferProjection c hh hincl hproj).linearPart = c.proj := by
  ext a
  rw [AInfinityHom.linearPart_apply, AInfinityHom.taylor_def, LinearMap.comp_apply,
    barMap_transferProjection, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    c.reducedTensorWordsHomotopy_ofLetter, perturbationSeries_ofLetter, map_zero, sub_zero,
    map_ofLetter, letter_ofLetter]

/-- The projection morphism is a left inverse of the extending morphism. -/
@[simp]
theorem transferProjection_comp_transferInclusion :
    (𝒜.transferProjection c hh hincl hproj).comp (𝒜.transferInclusion c hh hincl hproj) =
      AInfinityHom.id (𝒜.transfer c hh hincl hproj) :=
  AInfinityHom.barMap_injective <| by
    rw [AInfinityHom.barMap_comp, AInfinityHom.barMap_id]
    exact LinearSpecialContraction.proj_comp_incl _

/-- The projection morphism is a quasi-isomorphism, by two out of three: composed with the
extending quasi-isomorphism it is the identity. -/
theorem isQuasiIso_transferProjection : (𝒜.transferProjection c hh hincl hproj).IsQuasiIso :=
  (𝒜.isQuasiIso_transferInclusion c hh hincl hproj).of_precomp <| by
    rw [transferProjection_comp_transferInclusion]
    exact AInfinityHom.isQuasiIso_id _

end TauCeti.AInfinityAlgebra
