/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Limits.Proper
public import TauCeti.AlgebraicGeometry.Limits.Noetherian.Model

/-!
# Proper Noetherian models

Every proper finitely presented family over an affine scheme is the Cartesian base change
of a proper finitely presented family over an affine Noetherian scheme. The original base
need not be Noetherian, and the model source is also Noetherian.

References: The Stacks Project, Tags 081F and 01ZA.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry

namespace CategoryTheory.Limits.IsLimit

/-- A proper finitely presented family over a limit of affine Noetherian stages descends
as a proper finitely presented family to an actual stage. -/
theorem exists_isPullback_of_isProper
    {I : Type u} [SmallCategory I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
    [∀ {i j} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i, IsAffine (D.obj i)] [∀ i, IsNoetherian (D.obj i)]
    {c : Cone D} (hc : IsLimit c)
    {X : Scheme.{u}} (f : X ⟶ c.pt) [IsProper f] [LocallyOfFinitePresentation f] :
    ∃ (i : I) (X₀ : Scheme.{u}) (f₀ : X₀ ⟶ D.obj i)
      (_ : IsProper f₀) (_ : LocallyOfFinitePresentation f₀) (a : X ⟶ X₀),
      IsPullback a f f₀ (c.π.app i) := by
  obtain ⟨baseStage⟩ : Nonempty I := IsCofiltered.nonempty
  obtain ⟨i, Z, p, hfp, hqc, hqs, a, H⟩ :=
    hc.exists_isPullback_of_finitePresentation baseStage f
  have := hfp
  have := hqc
  have := hqs
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace p
  have : IsProper (pullback.snd p (c.π.app i)) := by
    rw [← H.isoPullback_inv_snd]
    infer_instance
  obtain ⟨j, t, hp⟩ := Functor.exists_isProper_pullback_snd_of_isLimit D c hc i p
  have hbase : IsPullback a f p (c.π.app j ≫ D.map t) := by rwa [c.w t]
  let a₀ : X ⟶ pullback p (D.map t) :=
    pullback.lift a (f ≫ c.π.app j) (by simpa only [Category.assoc] using hbase.w)
  have H₀ : IsPullback a₀ f (pullback.snd p (D.map t)) (c.π.app j) := by
    refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback p (D.map t))
    · simpa only [a₀, pullback.lift_fst] using hbase
    · exact pullback.lift_snd _ _ _
  exact ⟨j, _, _, hp, inferInstance, a₀, H₀⟩

end CategoryTheory.Limits.IsLimit

namespace AlgebraicGeometry

/-- A proper finitely presented family over an affine scheme has a proper finitely presented
Noetherian model over an affine Noetherian base. -/
theorem Scheme.Hom.exists_isPullback_over_noetherian_of_isProper
    {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S)
    [IsProper f] [LocallyOfFinitePresentation f] :
    ∃ (S₀ : Scheme.{u}) (_ : IsAffine S₀) (_ : IsNoetherian S₀)
      (X₀ : Scheme.{u}) (_ : IsNoetherian X₀) (f₀ : X₀ ⟶ S₀)
      (_ : IsProper f₀) (_ : LocallyOfFinitePresentation f₀)
      (a : X ⟶ X₀) (b : S ⟶ S₀), IsPullback a f f₀ b := by
  obtain ⟨I, hI, hcof, D, π, ⟨hc⟩, htrans, hstage⟩ :=
    S.exists_isLimit_noetherian_of_isAffine
  let := hI
  let := hcof
  let := htrans
  have (i : I) : IsAffine (D.obj i) := (hstage i).1
  have (i : I) : IsNoetherian (D.obj i) := (hstage i).2
  obtain ⟨i, X₀, f₀, hp, hfp, a, H⟩ := hc.exists_isPullback_of_isProper f
  have := hp
  exact ⟨D.obj i, inferInstance, inferInstance, X₀,
    TauCeti.AlgebraicGeometry.isNoetherian_of_finiteType f₀,
    f₀, hp, hfp, a, π.app i, H⟩

end AlgebraicGeometry
