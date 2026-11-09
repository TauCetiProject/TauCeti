/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Smooth.CotangentRank
public import TauCeti.RingTheory.Syntomic.Localization
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import TauCeti.RingTheory.Smooth.KrullDimension

/-!
# The smooth locus of a standard syntomic algebra

For a standard syntomic algebra of relative dimension `n`, the nonsmooth locus is the
zero locus of the `n`-th Fitting ideal of the relative differentials. In particular, for
relative curves, the first Fitting subscheme records precisely the nonsmooth points.

## References

* The Stacks Project, Tag 00T7 (standard smooth algebras and their differentials).
* The Stacks Project, Tag 0C58 (the singular subscheme of a relative curve).
-/

public section

noncomputable section

open Module KaehlerDifferential IsLocalRing

open scoped TensorProduct

namespace TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {n : ℕ}
  [hS : IsStandardSyntomicOfRelativeDimension n R S]

/-- The `n`-th Fitting locus of the differentials of a standard syntomic algebra of relative
dimension `n` consists exactly of its nonsmooth points. -/
theorem _root_.Ideal.fittingIdeal_kaehlerDifferential_le_iff_not_isSmoothAt
    (q : Ideal S) [q.IsPrime] :
    letI := hS.finitePresentation
    fittingIdeal S Ω[S⁄R] n ≤ q ↔ ¬ _root_.Algebra.IsSmoothAt R q := by
  classical
  have := hS.finitePresentation
  refine ⟨fun hfit hsm ↦ ?_, fun h ↦ ?_⟩
  · have : _root_.Algebra.IsSmoothAt R q := hsm
    obtain ⟨g, hg, hstd⟩ := _root_.Algebra.IsSmoothAt.exists_notMem_isStandardSmooth R q
    let T := Localization.Away g
    have : _root_.Algebra.IsStandardSmooth R T := hstd
    have : IsStandardSyntomicOfRelativeDimension n R T := trans_localization_away g
    let qT : Ideal T := q.map (algebraMap S T)
    have : qT.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) T q
      inferInstance (by rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime])
    obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := _root_.Algebra.IsStandardSmooth.out (R := R) (S := T)
    have : _root_.Algebra.IsStandardSmoothOfRelativeDimension P.dimension R T :=
      P.isStandardSmoothOfRelativeDimension rfl
    -- Compare relative dimensions on a nonempty field-valued fibre of the smooth chart.
    have hdim : P.dimension = n := by
      suffices key : ∀ (L : Type _) [Field L] [Algebra R L] [Algebra T L]
          [IsScalarTower R T L], P.dimension = n from key qT.ResidueField
      intro L _ _ _ _
      have : Nontrivial (L ⊗[R] T) :=
        (AlgHom.liftEquiv R L T L (IsScalarTower.toAlgHom R T L)).toRingHom.domain_nontrivial
      have h₁ := ringKrullDim_eq_of_isStandardSmoothOfRelativeDimension L
        (S := L ⊗[R] T) P.dimension
      have h₂ := ringKrullDim_tensorProduct_of_field (n := n) (R := R) (S := T) L
      exact_mod_cast h₁.symm.trans h₂
    have : Nontrivial T := (algebraMap T qT.ResidueField).domain_nontrivial
    have hrank : finrank T Ω[T⁄R] = n := by
      rw [← hdim]
      exact finrank_eq_of_rank_eq
        (_root_.Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential P.dimension)
    have hfitt : fittingIdeal T Ω[T⁄R] n = ⊤ :=
      (fittingIdeal_eq_top_iff_finrank_le).mpr hrank.le
    rw [(isBaseChange_of_formallyEtale R S T).fittingIdeal_eq_map n] at hfitt
    have hle : (fittingIdeal S Ω[S⁄R] n).map (algebraMap S T) ≤ qT := Ideal.map_mono hfit
    rw [hfitt] at hle
    exact (inferInstance : qT.IsPrime).ne_top (top_le_iff.mp hle)
  · by_contra hfit
    obtain ⟨ι, σ, _, _, P, hP⟩ := hS.exists_presentation
    exact h (P.isSmoothAt_of_not_fittingIdeal_le (by omega) q hfit)

end TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension
