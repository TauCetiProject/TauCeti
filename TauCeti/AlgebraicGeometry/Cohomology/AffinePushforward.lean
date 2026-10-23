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

For a morphism `f : X ⟶ Y` over a ring `R`, zeroth cohomology of `f_* M` is finite
exactly when that of `M` is finite. If `f` is affine and `Y` is locally Noetherian with a cover
by two affine opens, the same holds in degree one for quasicoherent `M` when `X` is locally
Noetherian. Both first cohomology groups are computed
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

/-- The difference of restrictions for a pushforward is the difference on the preimage opens.
The overlap section types agree because preimages preserve intersections. -/
lemma mayerVietorisSectionsDifferenceLinear_pushforward {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : X.Modules) (U V : Y.Opens) (a : Γ((pushforward f).obj M, U))
    (b : Γ((pushforward f).obj M, V)) :
    mayerVietorisSectionsDifferenceLinear ((pushforward f).obj M) U V (a, b) =
      mayerVietorisSectionsDifferenceLinear M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) (a, b) := by
  let N := (pushforward f).obj M
  have hres : N.presheaf.map (homOfLE inf_le_left).op a -
      N.presheaf.map (homOfLE inf_le_right).op b =
        M.presheaf.map (homOfLE inf_le_left).op a -
          M.presheaf.map (homOfLE inf_le_right).op b := by
    simp only [N, pushforward_obj_presheaf_map]
    -- Preimages of inclusions are the same morphisms in the opens poset.
    rfl
  -- Compose the public formulas explicitly: their section types agree at default
  -- transparency, but type inference for rewriting does not unfold pushforward objects.
  exact (mayerVietorisSectionsDifferenceLinear_apply N U V a b).trans
    ((mayerVietorisSectionsDifference_apply N U V a b).trans
      (hres.trans ((mayerVietorisSectionsDifference_apply M _ _ a b).symm.trans
        (mayerVietorisSectionsDifferenceLinear_apply M _ _ a b).symm)))

/-- An overlap section has zero boundary for a pushforward exactly when it has zero boundary
on the preimage cover. No affineness or acyclicity is needed for this kernel comparison. -/
lemma mayerVietorisBoundaryLinear_pushforward_eq_zero_iff {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : X.Modules) (U V : Y.Opens) (hUV : U ⊔ V = ⊤)
    (s : Γ((pushforward f).obj M, U ⊓ V)) :
    mayerVietorisBoundaryLinear ((pushforward f).obj M) U V hUV s = 0 ↔
      mayerVietorisBoundaryLinear M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)
        (by rw [← f.preimage_sup, hUV, f.preimage_top]) s = 0 := by
  have hpre : f ⁻¹ᵁ U ⊔ f ⁻¹ᵁ V = ⊤ := by rw [← f.preimage_sup, hUV, f.preimage_top]
  have hY := SetLike.ext_iff.mp
    (ker_mayerVietorisBoundaryLinear ((pushforward f).obj M) U V hUV) s
  have hX := SetLike.ext_iff.mp
    (ker_mayerVietorisBoundaryLinear M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) hpre) s
  refine hY.trans (Iff.trans ?_ hX.symm)
  constructor <;> rintro ⟨⟨a, b⟩, h⟩
  · exact ⟨(a, b), (f.mayerVietorisSectionsDifferenceLinear_pushforward M U V a b).symm.trans h⟩
  · exact ⟨(a, b), (f.mayerVietorisSectionsDifferenceLinear_pushforward M U V a b).trans h⟩

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
  [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of R))]

/-- Zeroth cohomology of a pushforward is finite over the base ring exactly when the original
zeroth cohomology is finite, with no condition on the morphism. -/
@[simp]
theorem moduleFinite_cohomology_zero_pushforward_iff (M : X.Modules) :
    Module.Finite R (Cohomology ((pushforward f).obj M) 0) ↔
      Module.Finite R (Cohomology M 0) := by
  -- Local sections use `baseRingToStructurePresheaf`, whereas global sections use
  -- `baseRingToGlobalSections`; identify these scalar maps at the top open.
  have e : Γ((pushforward f).obj M, ⊤) ≃ₗ[R] Γ(M, ⊤) := by
    convert! pushforwardSectionsBaseLinearEquiv (R := R) f M ⊤ using 1 <;>
      simp only [globalSectionsBaseModule, f.preimage_top,
        Scheme.baseRingToStructurePresheaf_app_top, CommRingCat.hom_ofHom]
      -- The remaining structures are `Module.compHom` for the same scalar map;
      -- its module argument on pushforward sections unfolds restriction of scalars.
      ; rfl
  exact Module.Finite.equiv_iff
    ((cohomologyZeroBaseLinearEquiv R Y ((pushforward f).obj M)).trans
      (e.trans
        (cohomologyZeroBaseLinearEquiv R X M).symm))

/-- On a locally Noetherian target covered by two affine opens, first cohomology of an affine
pushforward is finite exactly when first cohomology on the locally Noetherian source is finite. -/
theorem moduleFinite_cohomology_one_pushforward_iff_of_two_affine_opens [IsAffineHom f]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian X] (M : X.Modules) [M.IsQuasicoherent]
    (U V : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤) :
    Module.Finite R (Cohomology ((pushforward f).obj M) 1) ↔
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
        e.surjective
  -- The compatibility of restriction differences identifies the two boundary kernels.
  have hker : LinearMap.ker bY = LinearMap.ker bX := by
    ext s
    change bY s = 0 ↔ bX s = 0
    have he : e s = s := pushforwardSectionsBaseLinearEquiv_apply R f M (U ⊓ V) s
    have hx : bX s = mayerVietorisBoundaryLinear M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) hpre s := by
      exact congrArg (mayerVietorisBoundaryLinear M (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) hpre) he
    rw [hx]
    exact f.mayerVietorisBoundaryLinear_pushforward_eq_zero_iff M U V hUV s
  -- Both cohomology modules are the quotient of the common overlap by this kernel.
  exact Module.Finite.equiv_iff
    ((bY.quotKerEquivOfSurjective hbY).symm.trans
      ((Submodule.quotEquivOfEq _ _ hker).trans (bX.quotKerEquivOfSurjective hbX)))

end AlgebraicGeometry.Scheme.Hom
