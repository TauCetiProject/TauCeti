/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Schwartz
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Duality
import TauCeti.Analysis.FunctionalSpaces.BesovSpace.Norming

/-!
# The dual space of `B^s_{p,q}`

Let `φ : E → ℝ` be a smooth bump function on a finite-dimensional real inner product space, let
`s : ℝ`, and let `p, p'` and `q, q'` be pairs of Hölder conjugate exponents in `[1, ∞]`. This file
identifies the dual of the Besov space `B^s_{p,q}` with `B^{-s}_{p',q'}`:

`(B^s_{p,q})^* ≃ B^{-s}_{p',q'}` for `1 ≤ p < ∞` and `1 ≤ q < ∞`,

including the endpoint `(B^s_{1,q})^* ≃ B^{-s}_{∞,q'}`, through the pairing `⟨v, f⟩` of tempered
distributions with Schwartz functions, which for functions is the bilinear `L²` pairing `∫ v f`.

For `p, q < ∞` the Schwartz functions are dense in `B^s_{p,q}`
(`SchwartzMap.denseRange_toBesovSpaceCLM`), and `|⟨v, f⟩| ≤ C ‖v‖_{B^{-s}_{p',q'}} ‖f‖_{B^s_{p,q}}`
for Schwartz functions `f` (`TauCeti.BesovSpace.exists_norm_toDistr_apply_le`). So `f ↦ ⟨v, f⟩`
extends uniquely to a continuous linear functional on `B^s_{p,q}`. This defines a continuous linear
map `TauCeti.BesovSpace.toStrongDualCLM` from `B^{-s}_{p',q'}` to the dual of `B^s_{p,q}`, which
is injective because an element of a Besov space is determined by its tempered distribution. Here
`v` may take values in any complex Banach space `F`, and the functionals are then `F`-valued.

For scalar `v` and `1 ≤ p < ∞` the map is also onto: every continuous linear functional `Λ` on
`B^s_{p,q}` agrees on the Schwartz functions with the pairing against some `v ∈ B^{-s}_{p',q'}`
with `‖v‖ ≤ C ‖Λ‖` (`TauCeti.BesovSpace.exists_toDistr_apply_eq_and_norm_le`,
Bahouri–Chemin–Danchin, Proposition 2.76), and the two functionals then agree everywhere by
density. Hence
`TauCeti.BesovSpace.strongDualEquiv` is an isomorphism of Banach spaces. Both constants depend only
on `φ` and `s`, not on the exponents.

## Main declarations

* `TauCeti.BesovSpace.toStrongDualCLM`: the pairing of `B^{-s}_{p',q'}` with `B^s_{p,q}`, as a
  continuous linear map into the dual of `B^s_{p,q}`, for `p, q < ∞`.
* `TauCeti.BesovSpace.toStrongDualCLM_apply_toBesovSpaceCLM`: its value at a Schwartz function
  `f` is `⟨v, f⟩`.
* `TauCeti.BesovSpace.toStrongDualCLM_injective` and
  `TauCeti.BesovSpace.exists_norm_toStrongDualCLM_le`: it is injective and bounded uniformly in the
  exponents.
* `TauCeti.BesovSpace.strongDualEquiv`: **the duality `(B^s_{p,q})^* ≃ B^{-s}_{p',q'}`** for
  `1 ≤ p < ∞` and `1 ≤ q < ∞`. Its inverse is a two-sided inverse of the pairing
  (`TauCeti.BesovSpace.toStrongDualCLM_strongDualEquiv_symm_apply` and
  `TauCeti.BesovSpace.strongDualEquiv_symm_toStrongDualCLM`), is characterized on the
  Schwartz functions by `TauCeti.BesovSpace.toDistr_strongDualEquiv_symm_apply` and is bounded
  uniformly in the exponents by `TauCeti.BesovSpace.exists_norm_strongDualEquiv_symm_apply_le`.

## References

* H. Bahouri, J.-Y. Chemin and R. Danchin, *Fourier Analysis and Nonlinear Partial Differential
  Equations*, Proposition 2.76.
* H. Triebel, *Theory of Function Spaces*, Section 2.11.2.
-/

public section

noncomputable section

open scoped ENNReal SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace TauCeti.BesovSpace

variable (φ : ContDiffBump (0 : E)) (s : ℝ) {p p' q q' : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ p')]
  [Fact (1 ≤ q)] [Fact (1 ≤ q')] [p.HolderConjugate p'] [q.HolderConjugate q']

/-- The pairing `f ↦ ⟨v, f⟩` of `v ∈ B^{-s}_{p',q'}` with the Schwartz functions, extended by
continuity to `B^s_{p,q}`. -/
private def pairing (v : BesovSpace F φ (-s) p' q') : BesovSpace ℂ φ s p q →L[ℂ] F :=
  (v.toDistr : 𝓢(E, ℂ) →ₗ[ℂ] F).extendOfNorm
    (SchwartzMap.toBesovSpaceCLM ℂ φ s p q : 𝓢(E, ℂ) →ₗ[ℂ] BesovSpace ℂ φ s p q)

/-- The extended pairing takes the value `⟨v, f⟩` at a Schwartz function `f`. -/
private theorem pairing_apply_toBesovSpaceCLM (hp : p ≠ ∞) (hq : q ≠ ∞)
    (v : BesovSpace F φ (-s) p' q') (f : 𝓢(E, ℂ)) :
    pairing φ s v (SchwartzMap.toBesovSpaceCLM ℂ φ s p q f) = v.toDistr f := by
  obtain ⟨C, -, hC⟩ := exists_norm_toDistr_apply_le (F := F) φ s
  exact LinearMap.extendOfNorm_eq (SchwartzMap.denseRange_toBesovSpaceCLM φ s hp hq)
    ⟨C * ‖v‖, fun g ↦ hC v g⟩ f

omit [p.HolderConjugate p'] [q.HolderConjugate q'] in
/-- The extended pairing is bounded by `C ‖v‖`, with `C` from the duality bound. -/
private theorem norm_pairing_le (hp : p ≠ ∞) (hq : q ≠ ∞) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ (v : BesovSpace F φ (-s) p' q') (f : 𝓢(E, ℂ)),
      ‖v.toDistr f‖ ≤ C * ‖v‖ * ‖SchwartzMap.toBesovSpaceCLM ℂ φ s p q f‖)
    (v : BesovSpace F φ (-s) p' q') :
    ‖(pairing φ s v : BesovSpace ℂ φ s p q →L[ℂ] F)‖ ≤ C * ‖v‖ :=
  LinearMap.opNorm_extendOfNorm_le (SchwartzMap.denseRange_toBesovSpaceCLM φ s hp hq)
    (by positivity) fun f ↦ hC v f

/-- **The pairing of `B^{-s}_{p',q'}` with `B^s_{p,q}`**, for `p, q < ∞`: the continuous linear map
sending `v ∈ B^{-s}_{p',q'}` to the unique continuous linear functional on `B^s_{p,q}` whose value
at every Schwartz function `f` is `⟨v, f⟩`
(`TauCeti.BesovSpace.toStrongDualCLM_apply_toBesovSpaceCLM`). For `v` with values in `F`, the
functionals are `F`-valued. -/
def toStrongDualCLM (hp : p ≠ ∞) (hq : q ≠ ∞) :
    BesovSpace F φ (-s) p' q' →L[ℂ] BesovSpace ℂ φ s p q →L[ℂ] F :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := pairing φ s
      map_add' := fun v w ↦ continuousLinearMap_ext hp hq fun f ↦ by
        simp [pairing_apply_toBesovSpaceCLM φ s hp hq, toDistr_add]
      map_smul' := fun c v ↦ continuousLinearMap_ext hp hq fun f ↦ by
        simp [pairing_apply_toBesovSpaceCLM φ s hp hq, toDistr_smul] }
    (by
      obtain ⟨C, hC0, hC⟩ := exists_norm_toDistr_apply_le (F := F) φ s
      exact ⟨C, norm_pairing_le φ s hp hq hC0 hC⟩)

/-- The functional `toStrongDualCLM v` takes the value `⟨v, f⟩` at a Schwartz function `f`. -/
@[simp]
theorem toStrongDualCLM_apply_toBesovSpaceCLM (hp : p ≠ ∞) (hq : q ≠ ∞)
    (v : BesovSpace F φ (-s) p' q') (f : 𝓢(E, ℂ)) :
    toStrongDualCLM φ s hp hq v (SchwartzMap.toBesovSpaceCLM ℂ φ s p q f) = v.toDistr f :=
  pairing_apply_toBesovSpaceCLM φ s hp hq v f

/-- A continuous linear functional on `B^s_{p,q}`, `p, q < ∞`, equals `toStrongDualCLM v` as soon
as it takes the value `⟨v, f⟩` at every Schwartz function `f`. -/
theorem toStrongDualCLM_eq_of_forall_apply_eq (hp : p ≠ ∞) (hq : q ≠ ∞)
    {v : BesovSpace F φ (-s) p' q'} {Λ : BesovSpace ℂ φ s p q →L[ℂ] F}
    (h : ∀ f : 𝓢(E, ℂ), Λ (SchwartzMap.toBesovSpaceCLM ℂ φ s p q f) = v.toDistr f) :
    toStrongDualCLM φ s hp hq v = Λ :=
  continuousLinearMap_ext hp hq fun f ↦ by rw [toStrongDualCLM_apply_toBesovSpaceCLM, h]

/-- **The pairing is injective**: an element of `B^{-s}_{p',q'}` is determined by its pairing with
`B^s_{p,q}`, and already by its pairing with the Schwartz functions. -/
theorem toStrongDualCLM_injective (hp : p ≠ ∞) (hq : q ≠ ∞) :
    Function.Injective (toStrongDualCLM (F := F) (p' := p') (q' := q') φ s hp hq) := by
  intro v w h
  refine ext (DFunLike.ext _ _ fun f ↦ ?_)
  rw [← toStrongDualCLM_apply_toBesovSpaceCLM φ s hp hq, h,
    toStrongDualCLM_apply_toBesovSpaceCLM]

/-- **The pairing is bounded uniformly in the exponents.** There is `C ≥ 0`, depending only on
`φ` and `s`, such that for all Hölder conjugate pairs `p, p'` and `q, q'` with `p, q < ∞` and every
`v ∈ B^{-s}_{p',q'}`, the functional `toStrongDualCLM v` on `B^s_{p,q}` has norm at most
`C ‖v‖_{B^{-s}_{p',q'}}`. -/
theorem exists_norm_toStrongDualCLM_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p p' q q' : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ p')] [Fact (1 ≤ q)]
      [Fact (1 ≤ q')] [p.HolderConjugate p'] [q.HolderConjugate q'] (hp : p ≠ ∞) (hq : q ≠ ∞)
      (v : BesovSpace F φ (-s) p' q'), ‖toStrongDualCLM φ s hp hq v‖ ≤ C * ‖v‖ := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_toDistr_apply_le (F := F) φ s
  exact ⟨C, hC0, fun {p p' q q'} _ _ _ _ _ _ hp hq v ↦ norm_pairing_le φ s hp hq hC0 hC v⟩

/-- Every continuous linear functional `Λ` on `B^s_{p,q}`, `p, q < ∞`, is the pairing
with some `v ∈ B^{-s}_{p',q'}` of norm at most `C ‖Λ‖`, with `C` depending only on `φ` and `s`. -/
private theorem exists_toStrongDualCLM_eq_and_norm_le :
    ∃ C : ℝ, ∀ {p p' q q' : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ p')] [Fact (1 ≤ q)]
      [Fact (1 ≤ q')] [p.HolderConjugate p'] [q.HolderConjugate q'] (hp : p ≠ ∞) (hq : q ≠ ∞)
      (Λ : StrongDual ℂ (BesovSpace ℂ φ s p q)),
      ∃ v : BesovSpace ℂ φ (-s) p' q', toStrongDualCLM φ s hp hq v = Λ ∧ ‖v‖ ≤ C * ‖Λ‖ := by
  obtain ⟨C, hC⟩ := exists_toDistr_apply_eq_and_norm_le φ s
  refine ⟨C, fun {p p' q q'} _ _ _ _ _ _ hp hq Λ ↦ ?_⟩
  obtain ⟨v, hv, hvn⟩ := hC (p' := p') (q' := q') hp Λ
  exact ⟨v, toStrongDualCLM_eq_of_forall_apply_eq φ s hp hq fun f ↦ (hv f).symm, hvn⟩

/-- **The duality `(B^s_{p,q})^* ≃ B^{-s}_{p',q'}`** (Bahouri–Chemin–Danchin, Proposition 2.76;
Triebel, Section 2.11.2). For `1 ≤ p < ∞` and `1 ≤ q < ∞`, with Hölder conjugate exponents `p'`
and `q'`, the pairing `toStrongDualCLM` is an isomorphism of Banach spaces from `B^{-s}_{p',q'}`
onto the dual of `B^s_{p,q}`. -/
def strongDualEquiv (hp : p ≠ ∞) (hq : q ≠ ∞) :
    BesovSpace ℂ φ (-s) p' q' ≃L[ℂ] StrongDual ℂ (BesovSpace ℂ φ s p q) :=
  ContinuousLinearEquiv.ofBijective (toStrongDualCLM φ s hp hq)
    (LinearMap.ker_eq_bot.2 (toStrongDualCLM_injective φ s hp hq))
    (LinearMap.range_eq_top.2 fun Λ ↦ by
      obtain ⟨C, hC⟩ := exists_toStrongDualCLM_eq_and_norm_le φ s
      obtain ⟨v, hv, -⟩ := hC (p' := p') (q' := q') hp hq Λ
      exact ⟨v, hv⟩)

/-- The duality `strongDualEquiv` is the pairing `toStrongDualCLM`. -/
@[simp]
theorem strongDualEquiv_apply (hp : p ≠ ∞) (hq : q ≠ ∞)
    (v : BesovSpace ℂ φ (-s) p' q') :
    strongDualEquiv φ s hp hq v = toStrongDualCLM φ s hp hq v :=
  (rfl)

/-- The pairing with the element of `B^{-s}_{p',q'}` representing a continuous linear functional
`Λ` on `B^s_{p,q}` is `Λ`. -/
@[simp]
theorem toStrongDualCLM_strongDualEquiv_symm_apply (hp : p ≠ ∞) (hq : q ≠ ∞)
    (Λ : StrongDual ℂ (BesovSpace ℂ φ s p q)) :
    toStrongDualCLM φ s hp hq ((strongDualEquiv (p' := p') (q' := q') φ s hp hq).symm Λ) =
      Λ := by
  rw [← strongDualEquiv_apply φ s hp, ContinuousLinearEquiv.apply_symm_apply]

/-- The element of `B^{-s}_{p',q'}` representing the pairing with `v` is `v`. -/
@[simp]
theorem strongDualEquiv_symm_toStrongDualCLM (hp : p ≠ ∞) (hq : q ≠ ∞)
    (v : BesovSpace ℂ φ (-s) p' q') :
    (strongDualEquiv (p' := p') (q' := q') φ s hp hq).symm (toStrongDualCLM φ s hp hq v) =
      v := by
  rw [← strongDualEquiv_apply φ s hp, ContinuousLinearEquiv.symm_apply_apply]

/-- The element of `B^{-s}_{p',q'}` representing a continuous linear functional `Λ` on
`B^s_{p,q}` pairs with every Schwartz function `f` to `Λ f`. -/
@[simp]
theorem toDistr_strongDualEquiv_symm_apply (hp : p ≠ ∞) (hq : q ≠ ∞)
    (Λ : StrongDual ℂ (BesovSpace ℂ φ s p q)) (f : 𝓢(E, ℂ)) :
    ((strongDualEquiv (p' := p') (q' := q') φ s hp hq).symm Λ).toDistr f =
      Λ (SchwartzMap.toBesovSpaceCLM ℂ φ s p q f) := by
  rw [← toStrongDualCLM_apply_toBesovSpaceCLM φ s hp hq, ← strongDualEquiv_apply φ s hp,
    ContinuousLinearEquiv.apply_symm_apply]

/-- **The inverse of the duality is bounded uniformly in the exponents.** There is `C`, depending
only on `φ` and `s`, such that for all Hölder conjugate pairs `p, p'` and `q, q'` with `p < ∞`
and `q < ∞`, the element of `B^{-s}_{p',q'}` representing a continuous linear functional `Λ` on
`B^s_{p,q}` has norm at most `C ‖Λ‖`. -/
theorem exists_norm_strongDualEquiv_symm_apply_le :
    ∃ C : ℝ, ∀ {p p' q q' : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ p')] [Fact (1 ≤ q)]
      [Fact (1 ≤ q')] [p.HolderConjugate p'] [q.HolderConjugate q']
      (hp : p ≠ ∞) (hq : q ≠ ∞) (Λ : StrongDual ℂ (BesovSpace ℂ φ s p q)),
      ‖(strongDualEquiv (p' := p') (q' := q') φ s hp hq).symm Λ‖ ≤ C * ‖Λ‖ := by
  obtain ⟨C, hC⟩ := exists_toStrongDualCLM_eq_and_norm_le φ s
  refine ⟨C, fun {p p' q q'} _ _ _ _ _ _ hp hq Λ ↦ ?_⟩
  obtain ⟨v, hv, hvn⟩ := hC (p' := p') (q' := q') hp hq Λ
  rwa [(ContinuousLinearEquiv.symm_apply_eq _).2 (by rw [strongDualEquiv_apply, hv])]

end TauCeti.BesovSpace
