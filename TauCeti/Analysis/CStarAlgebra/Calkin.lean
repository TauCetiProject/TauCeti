/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.RingTheory.SimpleRing.Basic
public import TauCeti.Analysis.CStarAlgebra.Quotient
public import TauCeti.Analysis.Normed.Operator.Compact.Ideal
import TauCeti.Analysis.InnerProductSpace.BorelCalculus.Cutoff
import TauCeti.Analysis.Normed.Lp.Basic
import TauCeti.Analysis.Normed.Operator.Compact.Idempotent
import TauCeti.Analysis.Normed.Ring.Simple
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.FiniteDimensional

/-!
# Closed ideals of bounded operators and simplicity of the Calkin algebra

For a complex normed space `H`, the quotient
`TauCeti.CalkinAlgebra H := (H →L[ℂ] H) ⧸ ContinuousLinearMap.compactIdeal ℂ H` is the **Calkin
algebra** of `H`. When `H` is a complex Hilbert space, `ContinuousLinearMap.compactIdeal ℂ H` is a
norm-closed two-sided ideal of `H →L[ℂ] H`, hence a nonunital C⋆-algebra on its subtype carrier via
`TwoSidedIdeal.nonUnitalCStarAlgebra`, and `CalkinAlgebra H` is a unital C⋆-algebra with canonical
quotient `⋆`-homomorphism `CalkinAlgebra.mk` and essential-norm formula `CalkinAlgebra.norm_mk_eq`.

Combining the closed-ideal `star a * a` criterion (`TauCeti.Analysis.CStarAlgebra.Quotient`),
spectral cutoffs of normal operators (`TauCeti.Analysis.InnerProductSpace.BorelCalculus.Cutoff`),
noncompact-idempotent factorization (`TauCeti.Analysis.Normed.Operator.Compact.Idempotent`),
the compact-operator and separable-range ideals (`TauCeti.Analysis.Normed.Operator.Compact.Ideal`),
and the Banach-ring simplicity criterion (`TauCeti.Analysis.Normed.Ring.Simple`), this file proves:
* **Calkin's classification:** on a separable complex Hilbert space `H`, the closed two-sided
  ideals of `H →L[ℂ] H` are precisely `⊥`, `compactIdeal ℂ H`, and `⊤`; moreover, this three-ideal
  property holds if and only if `H` is separable.
* **Triviality and simplicity of the Calkin algebra:** `CalkinAlgebra H` is a subsingleton if and
  only if `H` is finite-dimensional, and on a complex Hilbert space `H` it is algebraically simple
  (`IsSimpleRing (CalkinAlgebra H)`) if and only if `H` is separable and infinite-dimensional. In
  particular, `CalkinAlgebra ℓ²(ι, ℂ)` is a simple C⋆-algebra for every countably infinite `ι` (such
  as `ι = ℕ`), while `CalkinAlgebra (EuclideanSpace ℂ n)` is a subsingleton for finite `n`.

## Main declarations

* `ContinuousLinearMap.eq_bot_or_eq_compactIdeal_or_eq_top_of_isClosed` and
  `ContinuousLinearMap.forall_isClosed_eq_bot_or_eq_compactIdeal_or_eq_top_iff`: Calkin's
  classification of closed two-sided ideals of `H →L[ℂ] H` and its equivalence with
  `SeparableSpace H`.
* `TauCeti.CalkinAlgebra`: the quotient `(H →L[ℂ] H) ⧸ ContinuousLinearMap.compactIdeal ℂ H`, with
  quotient projection `TauCeti.CalkinAlgebra.mk`, its characterization lemmas
  (`TauCeti.CalkinAlgebra.mk_eq_zero_iff`, `TauCeti.CalkinAlgebra.mk_eq_mk_iff`,
  `TauCeti.CalkinAlgebra.mk_surjective`, `TauCeti.CalkinAlgebra.ker_mk`), and essential-norm
  formula `TauCeti.CalkinAlgebra.norm_mk_eq`.
* `TauCeti.CalkinAlgebra.subsingleton_iff_finiteDimensional`,
  `TauCeti.CalkinAlgebra.nontrivial_iff_not_finiteDimensional`,
  `TauCeti.CalkinAlgebra.eq_bot_or_eq_top_of_isClosed`,
  `TauCeti.CalkinAlgebra.isSimpleRing`, and `TauCeti.CalkinAlgebra.isSimpleRing_iff`: triviality
  and algebraic simplicity characterizations of the Calkin algebra, instantiated on `ℓ²(ι, ℂ)` for
  countably infinite `ι` (in particular `ℓ²(ℕ, ℂ)`) via `TauCeti.CalkinAlgebra.instIsSimpleRingL2`.

## References

* J. W. Calkin, *Two-sided ideals and congruences in the ring of bounded operators in Hilbert
  space*, Annals of Mathematics 42 (1941), 839–873, Theorem 1.7.
* G. J. Murphy, *C*-Algebras and Operator Theory*, Academic Press (1990), Theorem 2.4.9 and §3.1.
* K. R. Davidson, *C*-Algebras by Example*, Fields Institute Monographs 6, AMS (1996), Theorem I.5.4
  and Example I.5.6.
-/

public noncomputable section

open TopologicalSpace
open scoped lp

namespace ContinuousLinearMap

section CalkinClassification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

-- Verify that `↥(compactIdeal ℂ H)` automatically carries a `NonUnitalCStarAlgebra` structure.
example : NonUnitalCStarAlgebra ↥(compactIdeal ℂ H) := inferInstance

/-- **Calkin's theorem on closed ideals of `B(H)`.** On a separable complex Hilbert space `H`,
every closed two-sided ideal of `H →L[ℂ] H` is `⊥`, `compactIdeal ℂ H`, or `⊤`. -/
theorem eq_bot_or_eq_compactIdeal_or_eq_top_of_isClosed [SeparableSpace H]
    {I : TwoSidedIdeal (H →L[ℂ] H)} (hI : IsClosed (I : Set (H →L[ℂ] H))) :
    I = ⊥ ∨ I = compactIdeal ℂ H ∨ I = ⊤ := by
  rcases eq_bot_or_compactIdeal_le_of_isClosed hI with rfl | hle
  · exact Or.inl rfl
  · by_cases hsub : I ≤ compactIdeal ℂ H
    · exact Or.inr (Or.inl (le_antisymm hsub hle))
    · obtain ⟨a, haI, ha_not_cpt, ha_sa⟩ :=
        (compactIdeal ℂ H).exists_isSelfAdjoint_mem_notMem hsub
      have : IsStarNormal a := ha_sa.isStarNormal
      obtain ⟨ε, hε, hp_not_cpt⟩ :=
        a.exists_spectralCutoff_notMem_of_isClosed isClosed_compactIdeal ha_not_cpt
      have hpI : a.spectralCutoff ε ∈ I := a.spectralCutoff_mem_twoSidedIdeal haI hε
      obtain ⟨v, -, hv⟩ := (a.isStarProjection_spectralCutoff ε).isIdempotentElem
        |>.exists_linearIsometry_mul_eq_and_star_mul_mul_eq_one (mt mem_compactIdeal.mpr hp_not_cpt)
      refine Or.inr (Or.inr (I.eq_top ?_))
      rw [← hv]
      exact I.mul_mem_right _ _ (I.mul_mem_left _ _ hpI)

/-- The closed two-sided ideals of `H →L[ℂ] H` are exhausted by `{⊥, compactIdeal ℂ H, ⊤}` if and
only if `H` is separable. -/
theorem forall_isClosed_eq_bot_or_eq_compactIdeal_or_eq_top_iff :
    (∀ I : TwoSidedIdeal (H →L[ℂ] H),
      IsClosed (I : Set (H →L[ℂ] H)) → I = ⊥ ∨ I = compactIdeal ℂ H ∨ I = ⊤) ↔
      SeparableSpace H := by
  refine ⟨fun h ↦ ?_, fun _ _ hI ↦ eq_bot_or_eq_compactIdeal_or_eq_top_of_isClosed hI⟩
  by_contra hsep
  have hlt₁ : compactIdeal ℂ H < separableRangeIdeal ℂ H := compactIdeal_lt_separableRangeIdeal hsep
  have hlt₂ : separableRangeIdeal ℂ H < ⊤ := separableRangeIdeal_lt_top hsep
  rcases h (separableRangeIdeal ℂ H) isClosed_separableRangeIdeal with hbot | hcpt | htop
  · exact not_lt_bot (hbot ▸ hlt₁)
  · exact hlt₁.ne' hcpt
  · exact hlt₂.ne htop

end CalkinClassification

-- Sanity checks on finite-dimensional complex Euclidean spaces.
example (d : ℕ) : compactIdeal ℂ (EuclideanSpace ℂ (Fin d)) = ⊤ :=
  compactIdeal_eq_top

example (I : TwoSidedIdeal (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))) :
    I = ⊥ ∨ I = ⊤ :=
  IsSimpleOrder.eq_bot_or_eq_top I

end ContinuousLinearMap

namespace TauCeti

/-- The **Calkin algebra** of a complex normed space `H`: the quotient ring
`(H →L[ℂ] H) ⧸ ContinuousLinearMap.compactIdeal ℂ H` of bounded operators modulo compact operators,
which is a unital C⋆-algebra whenever `H` is a complex Hilbert space. -/
abbrev CalkinAlgebra (H : Type*) [NormedAddCommGroup H] [NormedSpace ℂ H] : Type _ :=
  (H →L[ℂ] H) ⧸ ContinuousLinearMap.compactIdeal ℂ H

namespace CalkinAlgebra

section Normed

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- The Calkin algebra of `H` is a subsingleton if and only if `H` is finite-dimensional. -/
@[simp]
theorem subsingleton_iff_finiteDimensional :
    Subsingleton (CalkinAlgebra H) ↔ FiniteDimensional ℂ H :=
  TwoSidedIdeal.Quotient.subsingleton_iff.trans
    ContinuousLinearMap.compactIdeal_eq_top_iff_finiteDimensional

/-- On a finite-dimensional complex normed space, `CalkinAlgebra H` is a subsingleton. -/
instance instSubsingleton [FiniteDimensional ℂ H] : Subsingleton (CalkinAlgebra H) :=
  subsingleton_iff_finiteDimensional.mpr ‹_›

-- Verify subsingleton synthesis on finite-dimensional complex Euclidean spaces.
example (n : Type*) [Fintype n] : Subsingleton (CalkinAlgebra (EuclideanSpace ℂ n)) :=
  inferInstance

/-- The Calkin algebra of `H` is nontrivial if and only if `H` is infinite-dimensional. -/
@[simp]
theorem nontrivial_iff_not_finiteDimensional :
    Nontrivial (CalkinAlgebra H) ↔ ¬ FiniteDimensional ℂ H := by
  rw [← not_subsingleton_iff_nontrivial, subsingleton_iff_finiteDimensional]

end Normed

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

-- Verify that `CalkinAlgebra H` inherits a unital `CStarAlgebra` structure automatically.
example : CStarAlgebra (CalkinAlgebra H) := inferInstance

/-- The canonical surjective unital `⋆`-algebra homomorphism `(H →L[ℂ] H) →⋆ₐ[ℂ] CalkinAlgebra H`.
-/
abbrev mk : (H →L[ℂ] H) →⋆ₐ[ℂ] CalkinAlgebra H :=
  TwoSidedIdeal.Quotient.mkUnitalStarAlgHom (ContinuousLinearMap.compactIdeal ℂ H)

-- Not `@[simp]`: since `mk` is an `abbrev`, `simp` already reduces `mk T = 0` to
-- `IsCompactOperator T` via `TwoSidedIdeal.Quotient` and `ContinuousLinearMap.mem_compactIdeal`.
/-- An operator maps to `0` in `CalkinAlgebra H` if and only if it is compact. -/
theorem mk_eq_zero_iff {T : H →L[ℂ] H} : mk T = 0 ↔ IsCompactOperator T := by
  rw [TwoSidedIdeal.Quotient.mkUnitalStarAlgHom_apply, TwoSidedIdeal.Quotient.eq_zero_iff_mem,
    ContinuousLinearMap.mem_compactIdeal]

/-- Two operators have the same image in `CalkinAlgebra H` if and only if their difference is
compact. -/
theorem mk_eq_mk_iff {S T : H →L[ℂ] H} : mk S = mk T ↔ IsCompactOperator (S - T) := by
  rw [TwoSidedIdeal.Quotient.mkUnitalStarAlgHom_apply,
    TwoSidedIdeal.Quotient.mkUnitalStarAlgHom_apply, TwoSidedIdeal.Quotient.eq,
    ContinuousLinearMap.mem_compactIdeal]

/-- The Calkin quotient homomorphism `CalkinAlgebra.mk` is surjective. -/
theorem mk_surjective : Function.Surjective (mk (H := H)) :=
  TwoSidedIdeal.Quotient.mkUnitalStarAlgHom_surjective _

-- Not `@[simp]`: since `mk` is an `abbrev`, `simp` already reduces `TwoSidedIdeal.ker mk` via
-- `TwoSidedIdeal.Quotient.ker_mkUnitalStarAlgHom`.
/-- The kernel of `CalkinAlgebra.mk` is `ContinuousLinearMap.compactIdeal ℂ H`. -/
theorem ker_mk : TwoSidedIdeal.ker (mk (H := H)) = ContinuousLinearMap.compactIdeal ℂ H :=
  TwoSidedIdeal.Quotient.ker_mkUnitalStarAlgHom _

/-- **Essential norm formula.** The norm of `mk T` in `CalkinAlgebra H` is the infimum of
`‖T + K‖` over all compact operators `K : H →L[ℂ] H`. -/
theorem norm_mk_eq (T : H →L[ℂ] H) :
    ‖mk T‖ = sInf ((‖T + ·‖) '' {K : H →L[ℂ] H | IsCompactOperator K}) := by
  rw [TwoSidedIdeal.Quotient.mkUnitalStarAlgHom_apply, TwoSidedIdeal.Quotient.norm_mk_eq,
    ContinuousLinearMap.coe_compactIdeal]

/-- On a separable complex Hilbert space `H`, every closed two-sided ideal of `CalkinAlgebra H` is
`⊥` or `⊤`. -/
theorem eq_bot_or_eq_top_of_isClosed [SeparableSpace H] (J : TwoSidedIdeal (CalkinAlgebra H))
    (hJ : IsClosed (J : Set (CalkinAlgebra H))) : J = ⊥ ∨ J = ⊤ := by
  let π : (H →L[ℂ] H) →+* CalkinAlgebra H := (mk (H := H)).toRingHom
  let I : TwoSidedIdeal (H →L[ℂ] H) := J.comap π
  have hmemI : ∀ a : H →L[ℂ] H, a ∈ I ↔ mk a ∈ J := fun a ↦ TwoSidedIdeal.mem_comap π
  have hI_set : (I : Set (H →L[ℂ] H)) = mk ⁻¹' (J : Set (CalkinAlgebra H)) :=
    Set.ext hmemI
  have hI_closed : IsClosed (I : Set (H →L[ℂ] H)) := by
    rw [hI_set]
    exact hJ.preimage (by fun_prop)
  rcases ContinuousLinearMap.eq_bot_or_eq_compactIdeal_or_eq_top_of_isClosed hI_closed with
    hbot | hcpt | htop
  · refine Or.inl (le_bot_iff.mp fun x hx ↦ ?_)
    obtain ⟨a, rfl⟩ := mk_surjective x
    have ha : a ∈ (⊥ : TwoSidedIdeal (H →L[ℂ] H)) := hbot ▸ (hmemI a).mpr hx
    rw [TwoSidedIdeal.mem_bot] at ha ⊢
    rw [ha, map_zero]
  · refine Or.inl (le_bot_iff.mp fun x hx ↦ ?_)
    obtain ⟨a, rfl⟩ := mk_surjective x
    have ha : a ∈ ContinuousLinearMap.compactIdeal ℂ H := hcpt ▸ (hmemI a).mpr hx
    rw [TwoSidedIdeal.mem_bot, mk_eq_zero_iff]
    exact ContinuousLinearMap.mem_compactIdeal.mp ha
  · refine Or.inr (J.eq_top ?_)
    have h1 : (1 : H →L[ℂ] H) ∈ I := by rw [htop, TwoSidedIdeal.one_mem_iff]
    simpa only [hmemI, map_one] using h1

/-- **Simplicity of the Calkin algebra.** When `H` is a separable infinite-dimensional complex
Hilbert space, `CalkinAlgebra H` is algebraically simple: it is nontrivial and has no proper
nonzero two-sided ideals (closed or not). -/
theorem isSimpleRing [SeparableSpace H] (hH : ¬ FiniteDimensional ℂ H) :
    IsSimpleRing (CalkinAlgebra H) := by
  have : Nontrivial (CalkinAlgebra H) := nontrivial_iff_not_finiteDimensional.mpr hH
  exact IsSimpleRing.of_forall_isClosed_eq_bot_or_eq_top eq_bot_or_eq_top_of_isClosed

/-- The Calkin algebra `CalkinAlgebra H` is a simple ring if and only if `H` is separable and
infinite-dimensional. -/
theorem isSimpleRing_iff :
    IsSimpleRing (CalkinAlgebra H) ↔ SeparableSpace H ∧ ¬ FiniteDimensional ℂ H := by
  refine ⟨fun h ↦ ?_, fun ⟨_, hinf⟩ ↦ isSimpleRing hinf⟩
  have : IsSimpleRing (CalkinAlgebra H) := h
  have hinf : ¬ FiniteDimensional ℂ H := nontrivial_iff_not_finiteDimensional.mp inferInstance
  refine ⟨?_, hinf⟩
  by_contra hsep
  let f := TwoSidedIdeal.Quotient.factor
    (ContinuousLinearMap.compactIdeal_le_separableRangeIdeal (𝕜 := ℂ) (E := H))
  let J : TwoSidedIdeal (CalkinAlgebra H) := TwoSidedIdeal.ker f
  have hmemJ (T : H →L[ℂ] H) : mk T ∈ J ↔ T ∈ ContinuousLinearMap.separableRangeIdeal ℂ H := by
    simp [J, f, TwoSidedIdeal.mem_ker]
  have hlt₁ := ContinuousLinearMap.compactIdeal_lt_separableRangeIdeal (𝕜 := ℂ) hsep
  have hlt₂ := ContinuousLinearMap.separableRangeIdeal_lt_top (R := ℂ) hsep
  rcases IsSimpleOrder.eq_bot_or_eq_top J with hbot | htop
  · obtain ⟨T, hT_sep, hT_not_cpt⟩ := IsConcreteLE.exists_of_lt hlt₁
    have hmem : mk T ∈ J := (hmemJ T).mpr hT_sep
    rw [hbot, TwoSidedIdeal.mem_bot, mk_eq_zero_iff] at hmem
    exact hT_not_cpt (ContinuousLinearMap.mem_compactIdeal.mpr hmem)
  · have h1 : (1 : CalkinAlgebra H) ∈ J := by rw [htop, TwoSidedIdeal.one_mem_iff]
    rw [← map_one (mk (H := H)), hmemJ, TwoSidedIdeal.one_mem_iff] at h1
    exact hlt₂.ne h1

/-- For any infinite index type `ι`, `CalkinAlgebra ℓ²(ι, ℂ)` is nontrivial. -/
instance instNontrivialL2 {ι : Type*} [Infinite ι] : Nontrivial (CalkinAlgebra ℓ²(ι, ℂ)) :=
  nontrivial_iff_not_finiteDimensional.mpr lp.not_finiteDimensional

/-- For any countably infinite index type `ι` (in particular `ι = ℕ`), `CalkinAlgebra ℓ²(ι, ℂ)` is
a simple C⋆-algebra. -/
instance instIsSimpleRingL2 {ι : Type*} [Countable ι] [Infinite ι] :
    IsSimpleRing (CalkinAlgebra ℓ²(ι, ℂ)) := by
  have : SeparableSpace ℓ²(ι, ℂ) := lp.separableSpace (by norm_num)
  exact isSimpleRing lp.not_finiteDimensional

-- Non-vacuity check on `ℓ²(ℕ, ℂ)` with zero hypotheses.
example : IsSimpleRing (CalkinAlgebra ℓ²(ℕ, ℂ)) := inferInstance

end Hilbert

end CalkinAlgebra

end TauCeti

end
