/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.CWModel.Lacunary
public import TauCeti.Geometry.Manifold.Morse.Projectivization
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The Morse CW model of projective space

The moment function `[v] ↦ (∑ j, j * ‖v j‖ ^ 2) / ∑ j, ‖v j‖ ^ 2` on the projective space
`ℙ 𝕜 (Fin (n + 1) → 𝕜)`, over `𝕜 = ℝ` or `ℂ`, is a Morse function whose critical points are the
`n + 1` coordinate points `[eₖ]`, of Morse index `dim_ℝ 𝕜 * k`
(`TauCeti.criticalPoints_projectiveMomentFunction`,
`TauCeti.manifoldMorseIndex_projectiveMomentFunction_natCast`,
`TauCeti.projectiveMomentFunctionNatCastCriticalPointsEquiv`). Milnor's CW model of a compact
manifold with a Morse function (`TauCeti.IsMorse.exists_finite_cwComplex_homotopyEquiv`) therefore
makes projective space homotopy equivalent to a finite CW complex with one cell of dimension
`dim_ℝ 𝕜 * k` for each `k ≤ n` and no other cells
(`TauCeti.exists_finite_cwComplex_homotopyEquiv_projectivization`): one cell in each dimension
`0, …, n` for `ℝℙⁿ`, and one cell in each even dimension `0, 2, …, 2n` for `ℂℙⁿ`. For `ℂℙⁿ`
this cell count is compared with the standard CW structure in
`TauCeti.exists_cwComplex_homotopyEquiv_projectivization_complex`.

On `ℂℙⁿ` the critical points have the even indices `0, 2, …, 2n`, so no two of them have indices
differing by one (`TauCeti.manifoldMorseIndex_projectiveMomentFunction_complex_ne_add_one`), and
the lacunary principle for Morse functions
(`TauCeti.IsMorse.nonempty_singularHomology_iso_sigma_of_forall_ne_add_one`) makes the singular
homology free on the critical points: with coefficients `R` in any abelian category with
coproducts, for instance `R = ℤ`, `Hₘ(ℂℙⁿ; R)` is the coproduct of one copy of `R` for each `k ≤ n`
with `2 * k = m` (`TauCeti.nonempty_singularHomology_projectivization_complex_iso_sigma`). This is
the same answer as the cellular computation (`TauCeti.ComplexProjectiveSpace.singularHomologyIso`,
`TauCeti.ComplexProjectiveSpace.isZero_singularHomology_of_odd`,
`TauCeti.ComplexProjectiveSpace.isZero_singularHomology_of_lt`) for the standard CW structure
`TauCeti.ComplexProjectiveSpace.cwComplex` on the quotient model of `ℂℙⁿ`, which is homeomorphic to
the projectivization (`TauCeti.ComplexProjectiveSpace.homeomorphProjectivization`); here it is
obtained on the projectivization itself from the moment function. The isomorphism is stated as
`Nonempty` because the lacunary principle it comes from is: it reads the homology through a CW
model whose existence is only asserted.

## Main results

* `TauCeti.exists_finite_cwComplex_homotopyEquiv_projectivization`: `ℙ 𝕜 (Fin (n + 1) → 𝕜)` is
  homotopy equivalent to a finite CW complex whose `m`-cells correspond to the `k ≤ n` with
  `dim_ℝ 𝕜 * k = m`.
* `TauCeti.nonempty_singularHomology_projectivization_complex_iso_sigma`: `Hₘ(ℂℙⁿ; R)` is the
  coproduct of one copy of `R` for each `k ≤ n` with `2 * k = m`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.5 and the example of `ℂℙⁿ` in §4.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, the cellular homology of `ℂℙⁿ` after Theorem 2.35.
-/

public section

noncomputable section

open Function Set Topology Topology.RelCWComplex CategoryTheory Limits
open scoped ContDiff ContinuousMap Manifold LinearAlgebra.Projectivization

namespace TauCeti

open Projectivization

universe u

section CWModel

variable {𝕜 : Type u} [RCLike 𝕜] {n : ℕ}

variable (𝕜 n) in
/-- **The Morse CW model of projective space.** The projective space `ℙ 𝕜 (Fin (n + 1) → 𝕜)`,
for `𝕜 = ℝ` or `ℂ`, is homotopy equivalent to a finite CW complex whose `m`-cells correspond to the
`k ≤ n` with `dim_ℝ 𝕜 * k = m`: one cell in each dimension `0, …, n` for `ℝℙⁿ`, and one cell in
each even dimension `0, 2, …, 2n` for `ℂℙⁿ`. The complex is the CW model of the moment function
with the weights `w k = k`, whose critical points are the coordinate points `[eₖ]`. -/
theorem exists_finite_cwComplex_homotopyEquiv_projectivization :
    ∃ (W : Type u) (_ : TopologicalSpace W) (_ : T2Space W) (_ : CWComplex (univ : Set W)),
      RelCWComplex.Finite (univ : Set W) ∧ Nonempty (W ≃ₕ ℙ 𝕜 (Fin (n + 1) → 𝕜)) ∧
      ∀ m, Nonempty (cell (univ : Set W) m ≃
        {k : Fin (n + 1) // Module.finrank ℝ 𝕜 * k = m}) := by
  obtain ⟨W, _, _, _, hfin, he, hcell⟩ := (isMorse_projectiveMomentFunction_natCast (𝕜 := 𝕜)
    (n := n)).exists_finite_cwComplex_homotopyEquiv
  exact ⟨W, _, ‹_›, ‹_›, hfin, he, fun m ↦ (hcell m).map fun e ↦
    e.trans (projectiveMomentFunctionNatCastCriticalPointsEquiv 𝕜 n m).symm⟩

end CWModel

/-! ### The homology of complex projective space -/

section Complex

variable (n : ℕ) {A : Type*} [Category A] [HasCoproducts.{0} A] [Abelian A] (R : A)

/-- **The homology of `ℂℙⁿ` from its Morse CW model.** With coefficients `R` in any abelian
category with coproducts, `Hₘ(ℂℙⁿ; R)` is the coproduct of one copy of `R` for each `k ≤ n` with
`2 * k = m`: the critical points of the moment function all have even index, so the lacunary
principle applies in every degree. -/
theorem nonempty_singularHomology_projectivization_complex_iso_sigma (m : ℕ) :
    Nonempty (((AlgebraicTopology.singularHomologyFunctor A m).obj R).obj
        (TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ))) ≅
      ∐ fun _ : {k : Fin (n + 1) // 2 * k = m} ↦ R) := by
  obtain ⟨e⟩ := (isMorse_projectiveMomentFunction_natCast (𝕜 := ℂ) (n := n))
    |>.nonempty_singularHomology_iso_sigma_of_forall_ne_add_one
      (manifoldMorseIndex_projectiveMomentFunction_complex_ne_add_one
        (Nat.cast_injective.comp Fin.val_injective)) R m
  let c := (projectiveMomentFunctionNatCastCriticalPointsEquiv ℂ n m).symm.trans
    (Equiv.subtypeEquivRight fun k ↦ by rw [Complex.finrank_real_complex])
  exact ⟨e ≪≫ Sigma.whiskerEquiv c fun _ ↦ Iso.refl R⟩

end Complex

end TauCeti
