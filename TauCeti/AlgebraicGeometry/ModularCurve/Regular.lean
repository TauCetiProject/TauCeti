/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ModularCurve.Simultaneous.Projections
public import TauCeti.AlgebraicGeometry.Scheme.Regular.Dimension

/-!
# Regularity of a moduli problem

Let `𝒫` be a relatively representable moduli problem over `Ell/B`, with representing schemes
`𝒫_{E/S}`. Following Katz and Mazur (KM 4.12), `𝒫` is **regular of dimension `d`**
(`ModuliProblem.RelRepData.IsRegularOfDim`) when, for every representable rigidifying problem
`δ` which is étale and surjective over `Ell/B`, the scheme `𝕄(𝒫, δ)` representing the simultaneous
problem `(𝒫, δ)` is regular of dimension `d` (`TauCeti.AlgebraicGeometry.IsRegularOfDim`):
nonempty, with regular local rings, and with every nonempty open of dimension `d`. If `δ` is
represented by the object `U = (E_U/M)` of `Ell/B`, then `𝕄(𝒫, δ)` is the representing scheme
`𝒫_U` over `M` (`ModuliProblem.RelRepData.tensorRepresentableBy`), and this is how the condition
is stated.

The dimension condition is the one fixed by Katz and Mazur's Notes Added in Proof (p. 505), and
surjectivity of the rigidifiers is what makes the non-emptiness clause meaningful: an empty
representable étale problem would otherwise falsify it.

Katz and Mazur quantify over all such rigidifiers, so their definition does not depend on a
choice of rigidifier. For the formulation adopted here this is a theorem: regularity of dimension
`d` can be tested on any single étale surjective rigidifier
(`ModuliProblem.RelRepData.isRegularOfDim_iff_of_representableBy`). Indeed, for two such
rigidifiers `δ₁`, `δ₂`, represented by `U₁` and `U₂`, the scheme `𝕄(𝒫, δ₁, δ₂)` maps to both
`𝕄(𝒫, δ₁)` and `𝕄(𝒫, δ₂)` by base changes of the forgetful projections `𝕄(δ₁, δ₂) ⟶ 𝕄(δᵢ)`.
These projections are étale and surjective, being base changes of the representing morphisms of
`δ₂` and of `δ₁` (`ModuliProblem.RelRepData.mem_base_of_forget_snd`), and regularity of dimension
`d` is invariant under étale surjective morphisms
(`TauCeti.AlgebraicGeometry.isRegularOfDim_iff_of_etale_of_surjective`).

## Main definitions

* `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.IsRegularOfDim`: the relatively
  representable problem is regular of dimension `d` in the sense of KM 4.12.

## Main results

* `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.isRegularOfDim_rep_iff_of_hom`: along an
  arrow of `Ell/B` whose morphism of bases is étale and surjective, the representing schemes are
  simultaneously regular of dimension `d` or not.
* `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.isRegularOfDim_rep_iff_of_representableBy`:
  two étale surjective rigidifiers give representing schemes which are simultaneously regular of
  dimension `d` or not.
* `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.isRegularOfDim_iff_of_representableBy`:
  regularity of dimension `d` is detected by any single étale surjective rigidifier.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, 4.12 and the Notes Added in Proof, p. 505.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData

variable {B : Scheme.{u}} {P : ModuliProblem B} (D : P.RelRepData) {d : ℕ}

/-- Along an arrow `a : V ⟶ U` of `Ell/B` whose morphism of bases is étale and surjective, the
representing scheme `𝒫_V` is regular of dimension `d` exactly when `𝒫_U` is: `𝒫_V` is the base
change of `𝒫_U` along `a.base`. -/
theorem isRegularOfDim_rep_iff_of_hom {U V : EllObj B} (a : V ⟶ U) [Etale a.base]
    [Surjective a.base] :
    IsRegularOfDim (D.rep V).left d ↔ IsRegularOfDim (D.rep U).left d := by
  have h := D.isPullback a
  have : Etale ((D.repIsoPullback a).hom.left ≫ pullback.fst (D.rep U).hom a.base) :=
    MorphismProperty.of_isPullback (P := @Etale) h.flip ‹_›
  have : Surjective ((D.repIsoPullback a).hom.left ≫ pullback.fst (D.rep U).hom a.base) :=
    MorphismProperty.of_isPullback (P := @Surjective) h.flip ‹_›
  exact isRegularOfDim_iff_of_etale_of_surjective
    ((D.repIsoPullback a).hom.left ≫ pullback.fst (D.rep U).hom a.base)

/-- **Independence of the rigidifier.** Let `δ₁` and `δ₂` be moduli problems which are
represented by objects `U₁` and `U₂` of `Ell/B` and are relatively representable, étale and
surjective over `Ell/B`. Then the representing scheme `𝒫_{U₁} = 𝕄(𝒫, δ₁)` is regular of dimension
`d` exactly when `𝒫_{U₂} = 𝕄(𝒫, δ₂)` is. -/
theorem isRegularOfDim_rep_iff_of_representableBy {Q₁ Q₂ : ModuliProblem B} {U₁ U₂ : EllObj B}
    (R₁ : Q₁.RepresentableBy U₁) (R₂ : Q₂.RepresentableBy U₂) (D₁ : Q₁.RelRepData)
    (D₂ : Q₂.RelRepData) (he₁ : D₁.HasProperty @Etale) (hs₁ : D₁.HasProperty @Surjective)
    (he₂ : D₂.HasProperty @Etale) (hs₂ : D₂.HasProperty @Surjective) :
    IsRegularOfDim (D.rep U₁).left d ↔ IsRegularOfDim (D.rep U₂).left d := by
  -- `V = U₁` base changed to `δ₂_{U₁}` represents `(δ₂, δ₁)`, and projects to `U₁` and to `U₂`
  let S := D₂.tensorRepresentableBy R₁
  let a₁ := U₁.baseChangeFunctorHom (D₂.rep U₁)
  let a₂ := R₂.homEquiv.symm (S.homEquiv (𝟙 _)).1
  have : Etale a₁.base := by
    rw [EllObj.baseChangeFunctorHom_base]
    exact D₂.hasProperty_iff.mp he₂ U₁
  have : Surjective a₁.base := by
    rw [EllObj.baseChangeFunctorHom_base]
    exact D₂.hasProperty_iff.mp hs₂ U₁
  have ha₂ : R₂.homEquiv a₂ = (S.homEquiv (𝟙 _)).1 := R₂.homEquiv.apply_symm_apply _
  -- Fixing the universe lets instance search find isomorphism invariance.
  have : MorphismProperty.RespectsIso @Etale.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : Etale a₂.base := D₁.mem_base_of_forget_snd R₂ S a₂ ha₂ (D₁.hasProperty_iff.mp he₁ U₂)
  have : Surjective a₂.base :=
    D₁.mem_base_of_forget_snd R₂ S a₂ ha₂ (D₁.hasProperty_iff.mp hs₁ U₂)
  exact (D.isRegularOfDim_rep_iff_of_hom a₁).symm.trans (D.isRegularOfDim_rep_iff_of_hom a₂)

/-- A relatively representable moduli problem `𝒫` over `Ell/B` is **regular of dimension `d`**
(Katz–Mazur 4.12) when, for every moduli problem `δ` represented by an object `U` of `Ell/B` and
relatively representable, étale and surjective over `Ell/B`, the scheme `𝕄(𝒫, δ) = 𝒫_U` is regular
of dimension `d`: nonempty, with regular local rings, and with every nonempty open of Krull
dimension `d`. By `isRegularOfDim_iff_of_representableBy` it suffices to test a single such `δ`. -/
def IsRegularOfDim (d : ℕ) : Prop :=
  ∀ ⦃Q : ModuliProblem B⦄ ⦃U : EllObj B⦄ (_ : Q.RepresentableBy U) (DQ : Q.RelRepData),
    DQ.HasProperty @Etale → DQ.HasProperty @Surjective →
      AlgebraicGeometry.IsRegularOfDim (D.rep U).left d

/-- The defining condition of `IsRegularOfDim`: for every moduli problem `δ` represented by an
object `U` of `Ell/B` and relatively representable, étale and surjective over `Ell/B`, the scheme
`𝕄(𝒫, δ) = 𝒫_U` is regular of dimension `d`. -/
theorem isRegularOfDim_def :
    D.IsRegularOfDim d ↔
      ∀ ⦃Q : ModuliProblem B⦄ ⦃U : EllObj B⦄ (_ : Q.RepresentableBy U) (DQ : Q.RelRepData),
        DQ.HasProperty @Etale → DQ.HasProperty @Surjective →
          AlgebraicGeometry.IsRegularOfDim (D.rep U).left d :=
  (Iff.rfl)

/-- **Regularity is detected by a single rigidifier.** If `δ` is represented by `U` and is
relatively representable, étale and surjective over `Ell/B`, then `𝒫` is regular of dimension `d`
exactly when `𝕄(𝒫, δ) = 𝒫_U` is regular of dimension `d`. -/
theorem isRegularOfDim_iff_of_representableBy {Q : ModuliProblem B} {U : EllObj B}
    (R : Q.RepresentableBy U) (DQ : Q.RelRepData) (he : DQ.HasProperty @Etale)
    (hs : DQ.HasProperty @Surjective) :
    D.IsRegularOfDim d ↔ AlgebraicGeometry.IsRegularOfDim (D.rep U).left d :=
  ⟨fun h ↦ h R DQ he hs, fun h _ _ R' DQ' he' hs' ↦
    (D.isRegularOfDim_rep_iff_of_representableBy R R' DQ DQ' he hs he' hs').mp h⟩

end TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData
