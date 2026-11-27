/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.RingTheory.SimpleRing.Basic
public import TauCeti.Analysis.Normed.Operator.Compact.Calkin
public import TauCeti.Analysis.Normed.Operator.Compact.Ideal
import TauCeti.Analysis.CStarAlgebra.Hereditary.Ideal
import TauCeti.Analysis.InnerProductSpace.BorelCalculus.Cutoff
import TauCeti.Analysis.Normed.Lp.Basic
import TauCeti.Analysis.Normed.Operator.Compact.Idempotent
import TauCeti.Analysis.Normed.Ring.Simple

/-!
# Closed ideals of bounded operators and simplicity of the Calkin algebra

Building on `TauCeti.compactOperatorIdeal ℂ H` and `TauCeti.CalkinAlgebra ℂ H` from
`TauCeti.Analysis.Normed.Operator.Compact.Calkin`, together with closed-ideal `star a * a`
separation (`TauCeti.Analysis.CStarAlgebra.Hereditary.Ideal`), spectral cutoffs of normal operators
(`TauCeti.Analysis.InnerProductSpace.BorelCalculus.Cutoff`), noncompact-idempotent factorization
(`TauCeti.Analysis.Normed.Operator.Compact.Idempotent`), the compact-operator and separable-range
ideals (`TauCeti.Analysis.Normed.Operator.Compact.Ideal`), and the Banach-ring simplicity criterion
(`TauCeti.Analysis.Normed.Ring.Simple`), this file proves:
* **Calkin's classification:** on a separable complex Hilbert space `H`, the closed two-sided
  ideals of `H →L[ℂ] H` are precisely `⊥`, `TauCeti.compactOperatorIdeal ℂ H`, and `⊤`; moreover,
  this three-ideal property holds if and only if `H` is separable.
* **Simplicity of the Calkin algebra:** on a complex Hilbert space `H`, `TauCeti.CalkinAlgebra ℂ H`
  is algebraically simple (`IsSimpleRing (TauCeti.CalkinAlgebra ℂ H)`) if and only if `H` is
  separable and infinite-dimensional. In particular, `TauCeti.CalkinAlgebra ℂ ℓ²(ι, ℂ)` is a
  simple C⋆-algebra for every countably infinite `ι` (such as `ι = ℕ`).

## Main declarations

* `TauCeti.eq_bot_or_eq_compactOperatorIdeal_or_eq_top_of_isClosed` and
  `TauCeti.forall_isClosed_eq_bot_or_eq_compactOperatorIdeal_or_eq_top_iff`: Calkin's
  classification of closed two-sided ideals of `H →L[ℂ] H` and its equivalence with
  `SeparableSpace H`.
* `TauCeti.CalkinAlgebra.eq_bot_or_eq_top_of_isClosed`,
  `TauCeti.CalkinAlgebra.isSimpleRing`, and `TauCeti.CalkinAlgebra.isSimpleRing_iff`: closed-ideal
  triviality and algebraic simplicity characterizations of `TauCeti.CalkinAlgebra ℂ H`, instantiated
  on `ℓ²(ι, ℂ)` for countably infinite `ι` (in particular `ℓ²(ℕ, ℂ)`) via
  `TauCeti.CalkinAlgebra.instIsSimpleRingL2`.

## References

* J. W. Calkin, *Two-sided ideals and congruences in the ring of bounded operators in Hilbert
  space*, Annals of Mathematics 42 (1941), 839–873, Theorem 1.7.
* G. J. Murphy, *C*-Algebras and Operator Theory*, Academic Press (1990), Theorem 2.4.9 and §3.1.
* K. R. Davidson, *C*-Algebras by Example*, Fields Institute Monographs 6, AMS (1996), Theorem I.5.4
  and Example I.5.6.
-/

public noncomputable section

open TopologicalSpace
open scoped CStarAlgebra lp

namespace TauCeti

section CalkinClassification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- **Calkin's theorem on closed ideals of `B(H)`.** On a separable complex Hilbert space `H`,
every closed two-sided ideal of `H →L[ℂ] H` is `⊥`, `compactOperatorIdeal ℂ H`, or `⊤`. -/
theorem eq_bot_or_eq_compactOperatorIdeal_or_eq_top_of_isClosed [SeparableSpace H]
    {I : TwoSidedIdeal (H →L[ℂ] H)} (hI : IsClosed (I : Set (H →L[ℂ] H))) :
    I = ⊥ ∨ I = compactOperatorIdeal ℂ H ∨ I = ⊤ := by
  rcases eq_bot_or_compactOperatorIdeal_le_of_isClosed hI with rfl | hle
  · exact Or.inl rfl
  · by_cases hsub : I ≤ compactOperatorIdeal ℂ H
    · exact Or.inr (Or.inl (le_antisymm hsub hle))
    · obtain ⟨a, haI, ha_not_cpt, ha_sa⟩ :=
        (compactOperatorIdeal ℂ H).exists_isSelfAdjoint_mem_notMem hsub
      have : IsStarNormal a := ha_sa.isStarNormal
      obtain ⟨ε, hε, hp_not_cpt⟩ :=
        a.exists_spectralCutoff_notMem_of_isClosed isClosed_compactOperatorIdeal ha_not_cpt
      have hpI : a.spectralCutoff ε ∈ I := a.spectralCutoff_mem_twoSidedIdeal haI hε
      obtain ⟨v, -, hv⟩ := (a.isStarProjection_spectralCutoff ε).isIdempotentElem
        |>.exists_linearIsometry_mul_eq_and_star_mul_mul_eq_one
          (mt mem_compactOperatorIdeal.mpr hp_not_cpt)
      refine Or.inr (Or.inr (I.eq_top ?_))
      rw [← hv]
      exact I.mul_mem_right _ _ (I.mul_mem_left _ _ hpI)

/-- The closed two-sided ideals of `H →L[ℂ] H` are exhausted by
`{⊥, compactOperatorIdeal ℂ H, ⊤}` if and only if `H` is separable. -/
theorem forall_isClosed_eq_bot_or_eq_compactOperatorIdeal_or_eq_top_iff :
    (∀ I : TwoSidedIdeal (H →L[ℂ] H),
      IsClosed (I : Set (H →L[ℂ] H)) → I = ⊥ ∨ I = compactOperatorIdeal ℂ H ∨ I = ⊤) ↔
      SeparableSpace H := by
  refine ⟨fun h ↦ ?_,
    fun _ _ hI ↦ eq_bot_or_eq_compactOperatorIdeal_or_eq_top_of_isClosed hI⟩
  by_contra hsep
  have hlt₁ : compactOperatorIdeal ℂ H < ContinuousLinearMap.separableRangeIdeal ℂ H :=
    compactOperatorIdeal_lt_separableRangeIdeal hsep
  have hlt₂ : ContinuousLinearMap.separableRangeIdeal ℂ H < ⊤ :=
    ContinuousLinearMap.separableRangeIdeal_lt_top hsep
  rcases h (ContinuousLinearMap.separableRangeIdeal ℂ H)
      ContinuousLinearMap.isClosed_separableRangeIdeal with hbot | hcpt | htop
  · exact not_lt_bot (hbot ▸ hlt₁)
  · exact hlt₁.ne' hcpt
  · exact hlt₂.ne htop

end CalkinClassification

namespace CalkinAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- On a separable complex Hilbert space `H`, every closed two-sided ideal of `CalkinAlgebra ℂ H`
is `⊥` or `⊤`. -/
theorem eq_bot_or_eq_top_of_isClosed [SeparableSpace H] (J : TwoSidedIdeal (CalkinAlgebra ℂ H))
    (hJ : IsClosed (J : Set (CalkinAlgebra ℂ H))) : J = ⊥ ∨ J = ⊤ := by
  let e := TwoSidedIdeal.Quotient.comapMkRelIso (compactOperatorIdeal ℂ H)
  have hI_closed : IsClosed ((e J).val : Set (H →L[ℂ] H)) := by
    rw [TwoSidedIdeal.Quotient.coe_comapMkRelIso]
    exact hJ.preimage (TwoSidedIdeal.Quotient.continuous_mk (compactOperatorIdeal ℂ H))
  rcases eq_bot_or_eq_compactOperatorIdeal_or_eq_top_of_isClosed hI_closed with
    hbot | hcpt | htop
  · exact Or.inl ((TwoSidedIdeal.Quotient.comapMkRelIso_val_eq_iff_eq_bot _ J).mp
      (le_antisymm (hbot ▸ bot_le) (Set.mem_Ici.mp (e J).property)))
  · exact Or.inl ((TwoSidedIdeal.Quotient.comapMkRelIso_val_eq_iff_eq_bot _ J).mp hcpt)
  · exact Or.inr ((TwoSidedIdeal.Quotient.comapMkRelIso_val_eq_top_iff _ J).mp htop)

/-- **Simplicity of the Calkin algebra.** When `H` is a separable infinite-dimensional complex
Hilbert space, `CalkinAlgebra ℂ H` is algebraically simple: it is nontrivial and has no proper
nonzero two-sided ideals (closed or not). -/
theorem isSimpleRing [SeparableSpace H] (hH : ¬ FiniteDimensional ℂ H) :
    IsSimpleRing (CalkinAlgebra ℂ H) :=
  (isSimpleRing_iff_forall_isClosed_eq_bot_or_eq_top (CalkinAlgebra ℂ H)).mpr
    ⟨nontrivial hH, eq_bot_or_eq_top_of_isClosed⟩

/-- The Calkin algebra `CalkinAlgebra ℂ H` is a simple ring if and only if `H` is separable and
infinite-dimensional. -/
theorem isSimpleRing_iff :
    IsSimpleRing (CalkinAlgebra ℂ H) ↔ SeparableSpace H ∧ ¬ FiniteDimensional ℂ H := by
  refine ⟨fun h ↦ ?_, fun ⟨_, hinf⟩ ↦ isSimpleRing hinf⟩
  refine ⟨?_, nontrivial_iff.mp inferInstance⟩
  by_contra hsep
  let e := TwoSidedIdeal.Quotient.comapMkRelIso (compactOperatorIdeal ℂ H)
  let K : Set.Ici (compactOperatorIdeal ℂ H) :=
    ⟨ContinuousLinearMap.separableRangeIdeal ℂ H, compactOperatorIdeal_le_separableRangeIdeal⟩
  let J := e.symm K
  have hJ : (e J).val = ContinuousLinearMap.separableRangeIdeal ℂ H :=
    congrArg Subtype.val (e.apply_symm_apply K)
  have hlt_bot : compactOperatorIdeal ℂ H < (e J).val :=
    hJ ▸ compactOperatorIdeal_lt_separableRangeIdeal hsep
  have hlt_top : (e J).val < ⊤ :=
    hJ ▸ ContinuousLinearMap.separableRangeIdeal_lt_top hsep
  rcases IsSimpleOrder.eq_bot_or_eq_top J with h0 | h1
  · rw [(TwoSidedIdeal.Quotient.comapMkRelIso_val_eq_iff_eq_bot _ J).mpr h0] at hlt_bot
    exact hlt_bot.false
  · rw [(TwoSidedIdeal.Quotient.comapMkRelIso_val_eq_top_iff _ J).mpr h1] at hlt_top
    exact hlt_top.false

/-- For any infinite index type `ι`, `CalkinAlgebra ℂ ℓ²(ι, ℂ)` is nontrivial. -/
instance instNontrivialL2 {ι : Type*} [Infinite ι] :
    Nontrivial (CalkinAlgebra ℂ ℓ²(ι, ℂ)) :=
  nontrivial (lp.not_finite (𝕜 := ℂ))

/-- For any countably infinite index type `ι` (in particular `ι = ℕ`), `CalkinAlgebra ℂ ℓ²(ι, ℂ)`
is a simple C⋆-algebra. -/
instance instIsSimpleRingL2 {ι : Type*} [Countable ι] [Infinite ι] :
    IsSimpleRing (CalkinAlgebra ℂ ℓ²(ι, ℂ)) := by
  have : SeparableSpace ℓ²(ι, ℂ) := lp.separableSpace (by norm_num)
  exact isSimpleRing (lp.not_finite (𝕜 := ℂ))

end CalkinAlgebra

end TauCeti

end
