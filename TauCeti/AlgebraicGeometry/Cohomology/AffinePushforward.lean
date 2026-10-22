/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.SectionsQuotient.Linear
public import TauCeti.AlgebraicGeometry.Cohomology.Module.Base
public import TauCeti.AlgebraicGeometry.Cohomology.OpenImmersion
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Affine

/-!
# Finiteness of cohomology through an affine morphism

For an affine morphism `f : X ⟶ Y` over a ring `R`, finiteness of the zeroth cohomology of
`f_* M` implies that of `M`. If `Y` is locally Noetherian and has a cover by two affine opens,
the same holds in degree one for quasicoherent `M` when `X` is locally Noetherian. Both first
cohomology groups are computed
by the same sections on the overlap modulo differences of restrictions. These results allow
cohomological finiteness on the projective line to be transported to finite covers.

## References

* R. Hartshorne, *Algebraic Geometry*, III, Proposition 8.1 and Section 4.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
  [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of R))]

/-- Finiteness of global sections of a pushforward implies finiteness of global sections on
the source, with no condition on the morphism. -/
theorem finite_cohomology_zero_of_pushforward (M : X.Modules)
    [Module.Finite R (Cohomology ((pushforward f).obj M) 0)] :
    Module.Finite R (Cohomology M 0) := by
  -- Local sections use `baseRingToStructurePresheaf`, whereas global sections use
  -- `baseRingToGlobalSections`; identify these scalar maps at the top open.
  have e : Γ((pushforward f).obj M, ⊤) ≃ₗ[R] Γ(M, ⊤) := by
    convert! pushforwardSectionsBaseLinearEquiv (R := R) f M ⊤ using 1 <;>
      simp only [globalSectionsBaseModule, f.preimage_top,
        Scheme.baseRingToStructurePresheaf_app_top, CommRingCat.hom_ofHom]; rfl
  exact Module.Finite.equiv
    ((cohomologyZeroBaseLinearEquiv R Y ((pushforward f).obj M)).trans
      (e.trans
        (cohomologyZeroBaseLinearEquiv R X M).symm))

/-- On a locally Noetherian target covered by two affine opens, finiteness of first cohomology
of an affine pushforward implies finiteness of first cohomology on the locally Noetherian source. -/
theorem finite_cohomology_one_of_pushforward_of_two_affine_opens [IsAffineHom f]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian X] (M : X.Modules) [M.IsQuasicoherent]
    (U V : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤)
    [Module.Finite R (Cohomology ((pushforward f).obj M) 1)] :
    Module.Finite R (Cohomology M 1) := by
  -- Restrict the two Mayer–Vietoris boundaries to the common scalar ring `R`.
  let N := (pushforward f).obj M
  let : Algebra R Γ(Y, ⊤) := ((Y.baseRingToStructurePresheaf R).app (op ⊤)).hom.toAlgebra
  let : Algebra R Γ(X, ⊤) := ((X.baseRingToStructurePresheaf R).app (op ⊤)).hom.toAlgebra
  let : Module R Γ(N, U ⊓ V) :=
    Module.compHom _ ((Y.baseRingToStructurePresheaf R).app (op (U ⊓ V))).hom
  let : Module R Γ(M, f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V) :=
    Module.compHom _ ((X.baseRingToStructurePresheaf R).app (op (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V))).hom
  have := isScalarTower_sections R N (U ⊓ V)
  have := isScalarTower_sections R M (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V)
  have := isScalarTower_cohomology R Y N 1
  have := isScalarTower_cohomology R X M 1
  have hpre : f ⁻¹ᵁ U ⊔ f ⁻¹ᵁ V = ⊤ := by rw [← f.preimage_sup, hUV, f.preimage_top]
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : IsNoetherianRing Γ(X, f ⁻¹ᵁ U) :=
    IsLocallyNoetherian.component_noetherian ⟨_, hU.preimage f⟩
  have : IsNoetherianRing Γ(X, f ⁻¹ᵁ V) :=
    IsLocallyNoetherian.component_noetherian ⟨_, hV.preimage f⟩
  let : Module R Γ(M, f ⁻¹ᵁ (U ⊓ V)) :=
    Module.compHom _ ((X.baseRingToStructurePresheaf R).app (op (f ⁻¹ᵁ (U ⊓ V)))).hom
  let e := pushforwardSectionsBaseLinearEquiv (R := R) f M (U ⊓ V)
  let bY := (mayerVietorisBoundaryLinear N U V hUV).restrictScalars R
  let bX := ((mayerVietorisBoundaryLinear M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) hpre).restrictScalars R).comp
    e.toLinearMap
  have hbY : Function.Surjective bY := by
    exact mayerVietorisBoundaryLinear_surjective N U V hUV
      (subsingleton_cohomologyOn_succ_of_isAffineOpen N hU 0)
      (subsingleton_cohomologyOn_succ_of_isAffineOpen N hV 0)
  have hbX : Function.Surjective bX := by
    exact (mayerVietorisBoundaryLinear_surjective M _ _ hpre
      (subsingleton_cohomologyOn_succ_of_isAffineOpen M (hU.preimage f) 0)
      (subsingleton_cohomologyOn_succ_of_isAffineOpen M (hV.preimage f) 0)).comp
        (pushforwardSectionsBaseLinearEquiv (R := R) f M (U ⊓ V)).surjective
  have hker : LinearMap.ker bY ≤ LinearMap.ker bX := by
    intro s hs
    have hs' : s ∈ LinearMap.range (mayerVietorisSectionsDifferenceLinear N U V) := by
      rw [← ker_mayerVietorisBoundaryLinear N U V hUV]
      exact hs
    obtain ⟨⟨a, b⟩, rfl⟩ := hs'
    have hz : mayerVietorisSectionsDifferenceLinear N U V (a, b) =
        mayerVietorisSectionsDifferenceLinear M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) (a, b) := by
      erw [mayerVietorisSectionsDifferenceLinear_apply N,
        mayerVietorisSectionsDifferenceLinear_apply M,
        mayerVietorisSectionsDifference_apply N, mayerVietorisSectionsDifference_apply M]
      -- The difference-map API uses module-valued maps; the pushforward API uses presheaves.
      change N.presheaf.map (homOfLE inf_le_left).op a -
        N.presheaf.map (homOfLE inf_le_right).op b =
          M.presheaf.map (homOfLE inf_le_left).op a -
            M.presheaf.map (homOfLE inf_le_right).op b
      simp only [N, pushforward_obj_presheaf_map]
      rfl
    rw [LinearMap.mem_ker]
    dsimp only [bX, e]
    erw [LinearMap.comp_apply, pushforwardSectionsBaseLinearEquiv_apply,
      LinearMap.restrictScalars_apply]
    rw [hz, ← LinearMap.mem_ker, ker_mayerVietorisBoundaryLinear]
    exact ⟨(a, b), rfl⟩
  -- Descend along the surjective boundary downstairs, then transfer finite generation.
  let l := bY.liftOfSurjective hbY ⟨bX, hker⟩
  exact Module.Finite.of_surjective l (by
    intro z
    obtain ⟨s, rfl⟩ := hbX z
    exact ⟨bY s, LinearMap.equivOfSurjective_apply hbY hker⟩)

end AlgebraicGeometry.Scheme.Hom
