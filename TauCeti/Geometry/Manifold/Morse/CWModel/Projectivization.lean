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
`TauCeti.manifoldMorseIndex_projectiveMomentFunction_natCast`). Milnor's CW model of a compact
manifold with a Morse function (`TauCeti.IsMorse.exists_finite_cwComplex_homotopyEquiv`) therefore
makes projective space homotopy equivalent to a finite CW complex with one cell of dimension
`dim_ℝ 𝕜 * k` for each `k ≤ n` and no other cells
(`TauCeti.exists_finite_cwComplex_homotopyEquiv_projectivization`): one cell in each dimension
`0, …, n` for `ℝℙⁿ`, and one cell in each even dimension `0, 2, …, 2n` for `ℂℙⁿ`. For `ℂℙⁿ`
this cell count is also stated as a comparison with the standard CW structure
(`TauCeti.exists_cwComplex_homotopyEquiv_projectivization_complex`); the statement here covers
`ℝℙⁿ` as well.

On `ℂℙⁿ` the critical points have the even indices `0, 2, …, 2n`, so no two of them have indices
differing by one, and the lacunary principle for Morse functions
(`TauCeti.IsMorse.nonempty_singularHomology_iso_sigma_of_forall_ne_add_one`) makes the singular
homology free on the critical points. With coefficients `R` in any abelian category with
coproducts, for instance `R = ℤ`, this gives `H₂ᵢ(ℂℙⁿ; R) ≅ R` for `i ≤ n`
(`TauCeti.nonempty_singularHomology_projectivization_complex_iso`) and `Hₘ(ℂℙⁿ; R) = 0` for odd `m`
and for `m > 2n` (`TauCeti.isZero_singularHomology_projectivization_complex_of_odd`,
`TauCeti.isZero_singularHomology_projectivization_complex_of_lt`). This is the same answer as the
cellular computation `TauCeti.ComplexProjectiveSpace.singularHomologyIso` for the standard CW
structure `TauCeti.ComplexProjectiveSpace.cwComplex` on the quotient model of `ℂℙⁿ`, here obtained
on the projectivization itself from the moment function. The isomorphisms are stated as `Nonempty`
because the lacunary principle they come from is: it reads the homology through a CW model whose
existence is only asserted.

## Main results

* `TauCeti.exists_finite_cwComplex_homotopyEquiv_projectivization`: `ℙ 𝕜 (Fin (n + 1) → 𝕜)` is
  homotopy equivalent to a finite CW complex whose `m`-cells correspond to the `k ≤ n` with
  `dim_ℝ 𝕜 * k = m`.
* `TauCeti.nonempty_singularHomology_projectivization_complex_iso_sigma`: `Hₘ(ℂℙⁿ; R)` is the
  coproduct of one copy of `R` for each `k ≤ n` with `2 * k = m`.
* `TauCeti.nonempty_singularHomology_projectivization_complex_iso`,
  `TauCeti.isZero_singularHomology_projectivization_complex_of_odd` and
  `TauCeti.isZero_singularHomology_projectivization_complex_of_lt`: `H₂ᵢ(ℂℙⁿ; R) ≅ R` for
  `i ≤ n`, and the other homology vanishes.

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

/-- The critical points of index `m` of a moment function with strictly increasing weights are the
coordinate points `[eₖ]` with `dim_ℝ 𝕜 * k = m`. -/
private def criticalPointsIndexEquiv {w : Fin (n + 1) → ℝ} (hw : StrictMono w) (m : ℕ) :
    {k : Fin (n + 1) // Module.finrank ℝ 𝕜 * k = m} ≃
      ↥{x ∈ criticalPoints 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction 𝕜 w) |
        manifoldMorseIndex 𝓘(ℝ, Fin n → 𝕜) (projectiveMomentFunction 𝕜 w) x = m} :=
  Equiv.ofBijective
    (fun k ↦ ⟨mk 𝕜 (Pi.single k.val 1) (by simp),
      mk_single_mem_criticalPoints_projectiveMomentFunction w k.val,
      (manifoldMorseIndex_projectiveMomentFunction_of_strictMono hw k.val).trans k.property⟩)
    ⟨fun _ _ h ↦ Subtype.ext (mk_single_injective (congrArg Subtype.val h)), fun x ↦ by
      obtain ⟨k, hk⟩ : x.val ∈ range fun k ↦ mk 𝕜 (Pi.single k 1 : Fin (n + 1) → 𝕜) (by simp) := by
        rw [← criticalPoints_projectiveMomentFunction hw.injective]
        exact x.property.1
      replace hk : mk 𝕜 (Pi.single k 1 : Fin (n + 1) → 𝕜) (by simp) = x.val := hk
      refine ⟨⟨k, ?_⟩, Subtype.ext hk⟩
      rw [← manifoldMorseIndex_projectiveMomentFunction_of_strictMono hw k, hk]
      exact x.property.2⟩

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
  have hw : StrictMono fun i : Fin (n + 1) ↦ ((i : ℕ) : ℝ) :=
    Nat.strictMono_cast.comp Fin.val_strictMono
  obtain ⟨W, _, _, _, hfin, he, hcell⟩ :=
    (isMorse_projectiveMomentFunction (𝕜 := 𝕜) hw.injective).exists_finite_cwComplex_homotopyEquiv
  exact ⟨W, _, ‹_›, ‹_›, hfin, he,
    fun m ↦ (hcell m).map fun e ↦ e.trans (criticalPointsIndexEquiv hw m).symm⟩

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
  have hw : StrictMono fun i : Fin (n + 1) ↦ ((i : ℕ) : ℝ) :=
    Nat.strictMono_cast.comp Fin.val_strictMono
  obtain ⟨e⟩ := (isMorse_projectiveMomentFunction (𝕜 := ℂ) hw.injective)
    |>.nonempty_singularHomology_iso_sigma_of_forall_ne_add_one (by
      -- All critical points have even index, so no two indices differ by one.
      rw [criticalPoints_projectiveMomentFunction hw.injective]
      rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
      rw [manifoldMorseIndex_projectiveMomentFunction_of_strictMono hw,
        manifoldMorseIndex_projectiveMomentFunction_of_strictMono hw, Complex.finrank_real_complex]
      omega) R m
  let c := (criticalPointsIndexEquiv (𝕜 := ℂ) hw m).symm.trans
    (Equiv.subtypeEquivRight fun k ↦ by rw [Complex.finrank_real_complex])
  exact ⟨e ≪≫ Sigma.whiskerEquiv c fun _ ↦ Iso.refl R⟩

/-- **The even-degree homology of `ℂℙⁿ`.** For `i ≤ n` and coefficients `R` in any abelian
category with coproducts, `H₂ᵢ(ℂℙⁿ; R) ≅ R`. -/
theorem nonempty_singularHomology_projectivization_complex_iso {i : ℕ} (hi : i ≤ n) :
    Nonempty (((AlgebraicTopology.singularHomologyFunctor A (2 * i)).obj R).obj
        (TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ))) ≅ R) := by
  obtain ⟨e⟩ := nonempty_singularHomology_projectivization_complex_iso_sigma n R (2 * i)
  have : Unique {k : Fin (n + 1) // 2 * (k : ℕ) = 2 * i} :=
    { default := ⟨⟨i, by omega⟩, rfl⟩
      uniq := fun k ↦ Subtype.ext (Fin.ext (by have := k.property; simp; omega)) }
  exact ⟨e ≪≫ coproductUniqueIso _⟩

/-- The homology of `ℂℙⁿ` vanishes in every degree `m` that is not `2 * k` for some `k ≤ n`. -/
private theorem isZero_singularHomology_projectivization_complex_of_forall_ne {m : ℕ}
    (hm : ∀ k : Fin (n + 1), 2 * (k : ℕ) ≠ m) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor A m).obj R).obj
      (TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ)))) := by
  obtain ⟨e⟩ := nonempty_singularHomology_projectivization_complex_iso_sigma n R m
  have : IsEmpty {k : Fin (n + 1) // 2 * (k : ℕ) = m} := ⟨fun k ↦ hm k.val k.property⟩
  exact ((IsZero.iff_id_eq_zero _).2 (Sigma.hom_ext _ _ isEmptyElim)).of_iso e

/-- **The odd-degree homology of `ℂℙⁿ` vanishes.** `Hₘ(ℂℙⁿ; R) = 0` for odd `m`. -/
theorem isZero_singularHomology_projectivization_complex_of_odd {m : ℕ} (hm : Odd m) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor A m).obj R).obj
      (TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ)))) :=
  isZero_singularHomology_projectivization_complex_of_forall_ne n R fun k hk ↦
    Nat.not_even_iff_odd.2 hm (by rw [← hk]; exact even_two_mul _)

/-- The homology of `ℂℙⁿ` vanishes above degree `2n`. -/
theorem isZero_singularHomology_projectivization_complex_of_lt {m : ℕ} (hm : 2 * n < m) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor A m).obj R).obj
      (TopCat.of (ℙ ℂ (Fin (n + 1) → ℂ)))) :=
  isZero_singularHomology_projectivization_complex_of_forall_ne n R fun k hk ↦ by omega

end Complex

end TauCeti
