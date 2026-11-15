/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.NoetherianSpace
public import TauCeti.AlgebraicGeometry.FiniteEtale.MorphismProperty
public import TauCeti.AlgebraicGeometry.FiniteEtale.PuncturedSpectrum
public import TauCeti.AlgebraicGeometry.Stalk
import TauCeti.AlgebraicGeometry.FiniteEtale.Spreading

/-!
# Globalization of local purity across an open subscheme

Let `X` be a scheme whose underlying topological space is Noetherian and `U : X.Opens` an open
subscheme such that local purity (`TauCeti.IsLocalRing.PurityHolds (X.presheaf.stalk s)`) holds at
every point `s ∉ U`. Then pullback of finite étale schemes along `U.ι : U.toScheme ⟶ X` is
essentially surjective (`AlgebraicGeometry.Scheme.Opens.finiteEtale_extend_of_purity`,
`AlgebraicGeometry.Scheme.Opens.finiteEtaleOver_extend_of_purity`;
[Stacks Project, Lemma 58.21.6](https://stacks.math.columbia.edu/tag/0EY7)), reducing global purity
across closed subsets to local purity of the stalk rings `𝒪_{X,s}`.
-/

public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace TauCeti.FiniteEtaleScheme

/-- One extension step across a point `s : X` whose stalk preimage of `U` is the punctured spectrum
of `X.presheaf.stalk s` and at which local purity holds. -/
theorem exists_extend_of_purity_at_point {X : Scheme.{u}} {U : X.Opens} [QuasiCompact U.ι]
    {s : X} (hpunc : X.fromSpecStalk s ⁻¹ᵁ U = IsLocalRing.puncturedSpectrum (X.presheaf.stalk s))
    (hpurity : IsLocalRing.PurityHolds (X.presheaf.stalk s))
    (V : FiniteEtaleScheme U.toScheme) :
    ∃ (W : X.AffineOpenNhds s) (V' : FiniteEtaleScheme (U ⊔ W.opens).toScheme),
      Nonempty ((pullback (X.homOfLE le_sup_left)).obj V' ≅ V) := by
  let S := Spec (X.presheaf.stalk s)
  let toOs := S.homOfLE hpunc.ge; let fromOs := S.homOfLE hpunc.le
  let gU := (X.fromSpecStalk s).resLE U (X.fromSpecStalk s ⁻¹ᵁ U) le_rfl
  obtain ⟨Ys, ⟨eYs⟩⟩ :=
    (IsLocalRing.purityHolds_iff (X.presheaf.stalk s)).mp hpurity ((pullback (toOs ≫ gU)).obj V)
  have hgU : fromOs ≫ toOs ≫ gU = gU := by
    rw [← Category.assoc, S.homOfLE_homOfLE, S.homOfLE_rfl, Category.id_comp]
  obtain ⟨W, V', eU, _, _⟩ := exists_spread_fromSpecStalk V Ys
    (((pullbackCompIsoOfEq fromOs (toOs ≫ gU) gU hgU).app V).symm ≪≫
      (pullback fromOs).mapIso eYs.symm ≪≫
      (pullbackCompIsoOfEq fromOs (IsLocalRing.puncturedSpectrum (X.presheaf.stalk s)).ι _
        (S.homOfLE_ι hpunc.le)).app Ys)
  exact ⟨W, V', ⟨eU⟩⟩

end TauCeti.FiniteEtaleScheme

namespace AlgebraicGeometry.Scheme.Opens

open TauCeti.FiniteEtaleScheme

/-- **Globalization of local purity** (Stacks Project, Lemma 58.21.6): if `X` is a scheme whose
underlying topological space is Noetherian, `U : X.Opens` is an open subscheme, and local purity
holds for `X.presheaf.stalk s` at every point `s ∉ U`, then restriction of finite étale schemes
along `U.ι : U.toScheme ⟶ X` is essentially surjective. -/
@[stacks 0EY7]
theorem finiteEtale_extend_of_purity {X : Scheme.{u}} [NoetherianSpace X] (U : X.Opens)
    (hpurity : ∀ s : X, s ∉ U → TauCeti.IsLocalRing.PurityHolds (X.presheaf.stalk s)) :
    (pullback U.ι).EssSurj := by
  suffices h : ∀ (U' : X.Opens), U ≤ U' → ∀ V' : TauCeti.FiniteEtaleScheme U'.toScheme,
      ∃ Y : TauCeti.FiniteEtaleScheme X, Nonempty ((pullback U'.ι).obj Y ≅ V') from ⟨h U le_rfl⟩
  exact WellFounded.fix (wellFounded_gt (α := X.Opens)) fun U' ih hUU' V' ↦ by
    by_cases htop : U' = ⊤
    · have : IsIso U'.ι := isIso_of_isOpenImmersion_of_opensRange_eq_top U'.ι (by simp [htop])
      exact ⟨(pullback (inv U'.ι)).obj V',
        ⟨(pullbackCompIsoOfEq U'.ι (inv U'.ι) (𝟙 _) (IsIso.hom_inv_id _)).app V' ≪≫
          pullbackId.app V'⟩⟩
    · obtain ⟨s, hsU', hpunc⟩ := U'.exists_notMem_fromSpecStalk_preimage_eq_puncturedSpectrum htop
      have : NoetherianSpace U'.toScheme := U'.ι.isOpenEmbedding.isInducing.noetherianSpace
      have : QuasiCompact U'.ι := ⟨fun _ _ _ ↦ NoetherianSpace.isCompact _⟩
      obtain ⟨W, V'', ⟨eV''⟩⟩ :=
        exists_extend_of_purity_at_point hpunc (hpurity s fun hs ↦ hsU' (hUU' hs)) V'
      have hlt : U' < U' ⊔ W.opens := lt_of_le_of_ne le_sup_left fun heq ↦
        hsU' (heq.symm ▸ (Or.inr W.mem : s ∈ U' ⊔ W.opens))
      obtain ⟨Y, ⟨eY⟩⟩ := ih (U' ⊔ W.opens) hlt (hUU'.trans le_sup_left) V''
      exact ⟨Y, ⟨((pullbackCompIsoOfEq (X.homOfLE (U := U') (V := U' ⊔ W.opens) le_sup_left)
          (U' ⊔ W.opens).ι U'.ι (X.homOfLE_ι le_sup_left)).app Y).symm ≪≫
        (pullback (X.homOfLE le_sup_left)).mapIso eY ≪≫ eV''⟩⟩

/-- Formulation of `AlgebraicGeometry.Scheme.Opens.finiteEtale_extend_of_purity` for Mathlib's
morphism-property over category `(@IsFinite ⊓ @Etale).Over ⊤`. -/
@[stacks 0EY7]
theorem finiteEtaleOver_extend_of_purity {X : Scheme.{u}} [NoetherianSpace X] (U : X.Opens)
    (hpurity : ∀ s : X, s ∉ U → TauCeti.IsLocalRing.PurityHolds (X.presheaf.stalk s)) :
    letI : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange := .inf
    (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ U.ι).EssSurj :=
  (essSurj_pullback_iff U.ι).mp (U.finiteEtale_extend_of_purity hpurity)

end AlgebraicGeometry.Scheme.Opens
