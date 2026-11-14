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
essentially surjective: every finite étale scheme over `U` extends to a finite étale scheme over `X`
(Stacks Project, Lemma 58.21.6 (0EY7)).

This reduces global extension of finite étale covers—such as Zariski–Nagata purity across closed
subsets of codimension at least `2` on regular Noetherian schemes—to local purity of the stalk local
rings `𝒪_{X,s}` at points outside `U`.

## Main results

* `TauCeti.FiniteEtaleScheme.exists_extend_of_purity_at_point`: single extension step across a point
  `s ∉ U` whose strict generizations all lie in `U` and at which local purity holds.
* `AlgebraicGeometry.Scheme.Opens.finiteEtale_extend_of_purity`: essential surjectivity of
  `TauCeti.FiniteEtaleScheme.pullback U.ι` under local purity away from `U`.
* `AlgebraicGeometry.Scheme.Opens.finiteEtaleOver_extend_of_purity`: corresponding essential
  surjectivity of `MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ U.ι`.

## References

* [The Stacks Project, Lemma 58.21.6](https://stacks.math.columbia.edu/tag/0EY7)
-/

public section

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace TauCeti.FiniteEtaleScheme

/-- One extension step across a point `s ∉ U` whose strict generizations all lie in `U` and at
which local purity holds. -/
theorem exists_extend_of_purity_at_point {X : Scheme.{u}} {U : X.Opens} [QuasiCompact U.ι]
    {s : X} (hsU : s ∉ U) (hgen : ∀ ⦃t : X⦄, t ⤳ s → t ≠ s → t ∈ U)
    (hpurity : IsLocalRing.PurityHolds (X.presheaf.stalk s))
    (V : FiniteEtaleScheme U.toScheme) :
    ∃ (W : X.AffineOpenNhds s) (V' : FiniteEtaleScheme (U ⊔ W.opens).toScheme),
      Nonempty ((pullback (X.homOfLE le_sup_left)).obj V' ≅ V) := by
  -- Since `s ∉ U` and all strict generizations of `s` lie in `U`, the preimage of `U` in
  -- `Spec 𝒪_{X,s}` is the punctured spectrum; local purity extends the pulled-back cover across
  -- `Spec 𝒪_{X,s}`, and stalk spreading glues it onto `U ⊔ W.opens`.
  have hpunc :
      X.fromSpecStalk s ⁻¹ᵁ U = IsLocalRing.puncturedSpectrum (X.presheaf.stalk s) :=
    fromSpecStalk_preimage_eq_puncturedSpectrum_of_specializes hsU hgen
  let toOs :
      (IsLocalRing.puncturedSpectrum (X.presheaf.stalk s)).toScheme ⟶
        (X.fromSpecStalk s ⁻¹ᵁ U).toScheme :=
    (Spec (X.presheaf.stalk s)).homOfLE hpunc.ge
  let fromOs :
      (X.fromSpecStalk s ⁻¹ᵁ U).toScheme ⟶
        (IsLocalRing.puncturedSpectrum (X.presheaf.stalk s)).toScheme :=
    (Spec (X.presheaf.stalk s)).homOfLE hpunc.le
  let gU := (X.fromSpecStalk s).resLE U (X.fromSpecStalk s ⁻¹ᵁ U) le_rfl
  obtain ⟨Ys, ⟨eYs⟩⟩ :=
    (IsLocalRing.purityHolds_iff (X.presheaf.stalk s)).mp hpurity ((pullback (toOs ≫ gU)).obj V)
  have hfb : fromOs ≫ toOs = 𝟙 _ := by
    rw [(Spec (X.presheaf.stalk s)).homOfLE_homOfLE, (Spec (X.presheaf.stalk s)).homOfLE_rfl]
  have hfi :
      fromOs ≫ (IsLocalRing.puncturedSpectrum (X.presheaf.stalk s)).ι =
        (X.fromSpecStalk s ⁻¹ᵁ U).ι :=
    (Spec (X.presheaf.stalk s)).homOfLE_ι hpunc.le
  have hgU : fromOs ≫ toOs ≫ gU = gU := by
    rw [← Category.assoc, hfb, Category.id_comp]
  obtain ⟨e₀⟩ : Nonempty ((pullback gU).obj V ≅ (pullback (X.fromSpecStalk s ⁻¹ᵁ U).ι).obj Ys) :=
    ⟨((pullbackCompIsoOfEq fromOs (toOs ≫ gU) gU hgU).app V).symm ≪≫
      (pullback fromOs).mapIso eYs.symm ≪≫
      (pullbackCompIsoOfEq fromOs
        (IsLocalRing.puncturedSpectrum (X.presheaf.stalk s)).ι _ hfi).app Ys⟩
  exact exists_spread_fromSpecStalk V Ys e₀

end TauCeti.FiniteEtaleScheme

namespace AlgebraicGeometry.Scheme.Opens

/-- **Globalization of local purity** (Stacks Project, Lemma 58.21.6): if `X` is a scheme whose
underlying topological space is Noetherian, `U : X.Opens` is an open subscheme, and local purity
holds for `X.presheaf.stalk s` at every point `s ∉ U`, then restriction of finite étale schemes
along `U.ι : U.toScheme ⟶ X` is essentially surjective. -/
@[stacks 0EY7]
theorem finiteEtale_extend_of_purity {X : Scheme.{u}} [NoetherianSpace X] (U : X.Opens)
    (hpurity : ∀ s : X, s ∉ U → TauCeti.IsLocalRing.PurityHolds (X.presheaf.stalk s)) :
    (TauCeti.FiniteEtaleScheme.pullback U.ι).EssSurj := by
  -- Induct on `U'` with respect to `wellFounded_gt` on `X.Opens`: any proper open `U' ≠ ⊤`
  -- misses the generic point `s` of an irreducible component of `X \ U'`, so all strict
  -- generizations of `s` lie in `U'` and `exists_extend_of_purity_at_point` strictly enlarges `U'`.
  suffices h :
      ∀ (U' : X.Opens), U ≤ U' →
        ∀ V' : TauCeti.FiniteEtaleScheme U'.toScheme,
          ∃ Y : TauCeti.FiniteEtaleScheme X,
            Nonempty ((TauCeti.FiniteEtaleScheme.pullback U'.ι).obj Y ≅ V') from
    ⟨h U le_rfl⟩
  intro U'
  refine WellFounded.fix
    (C := fun U' : X.Opens ↦
      U ≤ U' →
        ∀ V' : TauCeti.FiniteEtaleScheme U'.toScheme,
          ∃ Y : TauCeti.FiniteEtaleScheme X,
            Nonempty ((TauCeti.FiniteEtaleScheme.pullback U'.ι).obj Y ≅ V'))
    (wellFounded_gt (α := X.Opens)) (fun U' ih hUU' V' ↦ ?_) U'
  by_cases htop : U' = ⊤
  · have hrange : U'.ι.opensRange = ⊤ := by simp [htop]
    have : IsIso U'.ι := isIso_of_isOpenImmersion_of_opensRange_eq_top U'.ι hrange
    refine ⟨(TauCeti.FiniteEtaleScheme.pullback (inv U'.ι)).obj V', ⟨?_⟩⟩
    exact (TauCeti.FiniteEtaleScheme.pullbackCompIsoOfEq U'.ι (inv U'.ι) (𝟙 _)
        (IsIso.hom_inv_id _)).app V'
      ≪≫ TauCeti.FiniteEtaleScheme.pullbackId.app V'
  · obtain ⟨s, hsU', hgen⟩ := U'.exists_notMem_specializes_imp_mem htop
    have hsU : s ∉ U := fun hs ↦ hsU' (hUU' hs)
    have : NoetherianSpace U'.toScheme := U'.ι.isOpenEmbedding.isInducing.noetherianSpace
    have : QuasiCompact U'.ι := ⟨fun _ _ _ ↦ NoetherianSpace.isCompact _⟩
    obtain ⟨W, V'', ⟨eV''⟩⟩ :=
      TauCeti.FiniteEtaleScheme.exists_extend_of_purity_at_point hsU' hgen (hpurity s hsU) V'
    have hlt : U' < U' ⊔ W.opens := by
      refine lt_of_le_of_ne le_sup_left fun heq ↦ hsU' ?_
      have hsUW : s ∈ U' ⊔ W.opens := Or.inr W.mem
      rwa [← heq] at hsUW
    obtain ⟨Y, ⟨eY⟩⟩ := ih (U' ⊔ W.opens) hlt (hUU'.trans le_sup_left) V''
    refine ⟨Y, ⟨?_⟩⟩
    exact ((TauCeti.FiniteEtaleScheme.pullbackCompIsoOfEq
        (X.homOfLE (U := U') (V := U' ⊔ W.opens) le_sup_left)
        (U' ⊔ W.opens).ι U'.ι (X.homOfLE_ι le_sup_left)).app Y).symm ≪≫
      (TauCeti.FiniteEtaleScheme.pullback (X.homOfLE le_sup_left)).mapIso eY ≪≫ eV''

/-- Formulation of `AlgebraicGeometry.Scheme.Opens.finiteEtale_extend_of_purity` for Mathlib's
morphism-property over category `(@IsFinite ⊓ @Etale).Over ⊤`. -/
@[stacks 0EY7]
theorem finiteEtaleOver_extend_of_purity {X : Scheme.{u}} [NoetherianSpace X] (U : X.Opens)
    (hpurity : ∀ s : X, s ∉ U → TauCeti.IsLocalRing.PurityHolds (X.presheaf.stalk s)) :
    letI : (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}).IsStableUnderBaseChange := .inf
    (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤ U.ι).EssSurj :=
  (TauCeti.FiniteEtaleScheme.essSurj_pullback_iff U.ι).mp (U.finiteEtale_extend_of_purity hpurity)

end AlgebraicGeometry.Scheme.Opens
