/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.RelativelyAmple
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Ample
public import TauCeti.AlgebraicGeometry.RelativeProj.Proper
public import TauCeti.AlgebraicGeometry.RelativeProj.TwistingSheaf

/-!
# Relative ampleness of the twisting sheaves of a relative `Proj`

Let `A` be a graded algebra on a scheme `X` with quasi-coherent homogeneous components, and let
`p : Proj_X(A) ⟶ X` be its relative `Proj`. When the standard opens of the degree-one elements
cover every chart of `Proj_X(A)`, for instance when `A` is generated in degree one, the twisting
sheaves `𝒪(n)` are invertible, and this file proves that every positive twist `𝒪(n)` is
relatively ample for `p` exactly when `p` is quasi-compact
(`CategoryTheory.CommMon.isRelativelyAmple_relativeProjTwistingSheaf_iff_of_iSup_eq_top`, and
`CategoryTheory.CommMon.isRelativelyAmple_relativeProjTwistingSheaf_iff` for `A` generated in
degree one). Quasi-compactness is necessary because a morphism carrying a relatively ample line
bundle is quasi-compact. In particular `𝒪(1)` is relatively ample when moreover `A₁` is of
finite type (`CategoryTheory.CommMon.isRelativelyAmple_relativeProjTwistingSheaf_of_isFiniteType`).

This is the positivity of the tautological line bundle `𝒪(1)` of a relative `Proj`. It is the
source of the relatively ample line bundles on closed subschemes of relative `Proj`s, and the
polarization carried by a scheme recovered as the relative `Proj` of a graded section algebra.

The proof is chartwise. Over an affine open `U` of `X`, the preimage `p⁻¹ U` is the chart
`Proj (⨁ n, Γ(Aₙ, U))` (`CategoryTheory.CommMon.relativeProjToBase_preimage`), and the pullback of
`𝒪(n)` to this chart is the twisting sheaf `𝒪(n)` of the chart
(`CategoryTheory.CommMon.pullback_relativeProjCover_f_mk_relativeProjTwistingSheaf`). On a
quasi-compact `Proj` covered by the standard opens of degree-one elements, the positive twists
are ample (`AlgebraicGeometry.Proj.isAmple_twistingSheaf`).

## Main results

* `CategoryTheory.CommMon.pullback_relativeProjCover_f_mk_relativeProjTwistingSheaf`: the
  pullback of the class of `𝒪(n)` to the chart over an affine open `U` is the class of the
  twisting sheaf `𝒪(n)` of `Proj (⨁ n, Γ(Aₙ, U))`.
* `CategoryTheory.CommMon.isRelativelyAmple_relativeProjTwistingSheaf_iff_of_iSup_eq_top`: if the
  degree-one standard opens cover every chart, a positive twist `𝒪(n)` is relatively ample exactly
  when `p` is quasi-compact.
* `CategoryTheory.CommMon.isRelativelyAmple_relativeProjTwistingSheaf_iff`: for `A` generated in
  degree one and `n > 0`, `𝒪(n)` is relatively ample exactly when `p` is quasi-compact.
* `CategoryTheory.CommMon.isRelativelyAmple_relativeProjTwistingSheaf_of_isFiniteType`: for `A`
  generated in degree one with `A₁` of finite type, every positive twist is relatively ample.

## References

* The Stacks Project, *Morphisms of Schemes*, Section *Relatively ample sheaves*.
* A. Grothendieck, *EGA II*, Section 4.6.
-/

public section

open CategoryTheory DirectSum

namespace CategoryTheory.CommMon

open _root_.AlgebraicGeometry TauCeti.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} (A : CommMon (GradedObject ℕ X.Modules)) [∀ n, (A.X n).IsQuasicoherent]

/-- **The twisting sheaf `𝒪(n)` of a relative `Proj` restricts to `𝒪(n)` on each chart**: the
pullback of the class of `𝒪(n)` along the chart `Proj (⨁ n, Γ(Aₙ, U)) ⟶ Proj_X(A)` over an affine
open `U` of `X` is the class of the twisting sheaf `𝒪(n)` of the chart. -/
theorem pullback_relativeProjCover_f_mk_relativeProjTwistingSheaf (U : X.AffineZariskiSite)
    (n : ℤ) (h : SheafOfModules.isInvertible A.relativeProj (A.relativeProjTwistingSheaf n))
    (h' : SheafOfModules.isInvertible _
      (Proj.twistingSheaf (A.gradedSectionsGrading U.toOpens) n)) :
    LineBundleClass.pullback (A.relativeProjCover.f U)
        (LineBundleClass.mk ⟨A.relativeProjTwistingSheaf n, h⟩) =
      LineBundleClass.mk ⟨Proj.twistingSheaf (A.gradedSectionsGrading U.toOpens) n, h'⟩ := by
  rw [LineBundleClass.pullback_mk]
  -- the chart index type `A.relativeProjCover.I₀` is `X.AffineZariskiSite` only up to unfolding,
  -- so `mk_eq_mk_iff` is applied as a term rather than rewritten
  exact LineBundleClass.mk_eq_mk_iff.mpr
    ⟨(Scheme.Modules.restrictFunctorIsoPullback _).symm.app _ ≪≫
      A.restrictRelativeProjTwistingSheafIso n U⟩

/-- **Positive twists of a relative `Proj` are relatively ample exactly when it is quasi-compact
over the base.** If, over every affine open `U` of `X`, the standard opens `D₊(f)` of the elements
`f` of degree one cover the chart `Proj (⨁ n, Γ(Aₙ, U))`, then for `n > 0` the twisting sheaf
`𝒪(n)` is relatively ample for the structure morphism `Proj_X(A) ⟶ X` if and only if this
morphism is quasi-compact. -/
theorem isRelativelyAmple_relativeProjTwistingSheaf_iff_of_iSup_eq_top
    (h : ∀ U : X.Opens, IsAffineOpen U →
      ⨆ f : A.gradedSectionsGrading U 1, Proj.basicOpen (A.gradedSectionsGrading U) f = ⊤)
    {n : ℤ} (hn : 0 < n) :
    (LineBundleClass.mk ⟨A.relativeProjTwistingSheaf n,
        A.isInvertible_relativeProjTwistingSheaf_of_iSup_eq_top h n⟩).IsRelativelyAmple
        A.relativeProjToBase ↔
      QuasiCompact A.relativeProjToBase := by
  refine ⟨LineBundleClass.IsRelativelyAmple.quasiCompact, fun _ ↦ ⟨fun V hV ↦ ?_⟩⟩
  lift n to ℕ using hn.le
  let U : X.AffineZariskiSite := ⟨V, hV⟩
  let 𝒜 := A.gradedSectionsGrading V
  have hcover := h V hV
  -- the chart over `U` is an open immersion onto the preimage of `U`
  have hrange : Set.range (A.relativeProjCover.f U) =
      Set.range (A.relativeProjToBase ⁻¹ᵁ V).ι := by
    rw [Scheme.Opens.range_ι, A.relativeProjToBase_preimage U, Scheme.Hom.coe_opensRange]
  let e := IsOpenImmersion.isoOfRangeEq _ _ hrange
  have : CompactSpace (A.relativeProjToBase ⁻¹ᵁ V) := isCompact_iff_compactSpace.mp
    (quasiCompact_iff_forall_isAffineOpen.mp inferInstance V hV)
  have : CompactSpace (Proj 𝒜) := (Scheme.homeoOfIso e.symm).compactSpace
  rw [← LineBundleClass.isAmple_pullback_iff_of_isIso e.hom, LineBundleClass.pullback_comp,
    IsOpenImmersion.isoOfRangeEq_hom_fac,
    A.pullback_relativeProjCover_f_mk_relativeProjTwistingSheaf U n _
      (Proj.isInvertible_twistingSheaf_of_iSup_eq_top (fun f : 𝒜 1 ↦ (f : ⨁ n, Γ(A.X n, V)))
        (fun f ↦ f.property) hcover n)]
  exact Proj.isAmple_twistingSheaf (fun f : 𝒜 1 ↦ (f : ⨁ n, Γ(A.X n, V))) (fun f ↦ f.property)
    hcover (by exact_mod_cast hn)

/-- **For an algebra generated in degree one, the positive twists of its relative `Proj` are
relatively ample exactly when the relative `Proj` is quasi-compact over the base.** If `A` is
generated in degree one and `n > 0`, then the twisting sheaf `𝒪(n)` is relatively ample for the
structure morphism `Proj_X(A) ⟶ X` if and only if this morphism is quasi-compact. -/
theorem isRelativelyAmple_relativeProjTwistingSheaf_iff (h : A.IsGeneratedInDegreeOne)
    {n : ℤ} (hn : 0 < n) :
    (LineBundleClass.mk ⟨A.relativeProjTwistingSheaf n,
        A.isInvertible_relativeProjTwistingSheaf h n⟩).IsRelativelyAmple A.relativeProjToBase ↔
      QuasiCompact A.relativeProjToBase :=
  A.isRelativelyAmple_relativeProjTwistingSheaf_iff_of_iSup_eq_top (fun U hU ↦
    Proj.iSup_basicOpen_eq_top_of_adjoin_eq_top _ (CommMon.isGeneratedInDegreeOne_iff.mp h U hU))
    hn

/-- **Positive twists are relatively ample on the relative `Proj` of an algebra generated by a
degree-one part of finite type.** If `A` is generated in degree one and `A₁` is of finite type,
then every twisting sheaf `𝒪(n)` with `n > 0` is relatively ample for `Proj_X(A) ⟶ X`. -/
theorem isRelativelyAmple_relativeProjTwistingSheaf_of_isFiniteType
    (h : A.IsGeneratedInDegreeOne) [(A.X 1).IsFiniteType] {n : ℤ} (hn : 0 < n) :
    (LineBundleClass.mk ⟨A.relativeProjTwistingSheaf n,
        A.isInvertible_relativeProjTwistingSheaf h n⟩).IsRelativelyAmple A.relativeProjToBase :=
  have := A.isProper_relativeProjToBase_of_isGeneratedInDegreeOne h
  (A.isRelativelyAmple_relativeProjTwistingSheaf_iff h hn).mpr inferInstance

end CategoryTheory.CommMon
