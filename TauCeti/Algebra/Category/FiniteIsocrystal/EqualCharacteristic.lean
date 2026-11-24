/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FiniteIsocrystal.Basic
public import TauCeti.RingTheory.LaurentSeries.CoefficientFrobenius

/-!
# Splitting extensions of equal-characteristic isocrystals

Every surjective morphism of finite isocrystals over `k((X))` with arithmetic
coefficient Frobenius has a Frobenius-equivariant section when `k` is
algebraically closed. The Frobenius defect of an arbitrary linear section
takes values in the kernel, so a solution of `Φ - 1` on the space of linear
maps into that kernel corrects the section.
-/

public section

open CategoryTheory Function
open scoped LaurentSeries

namespace TauCeti.FiniteIsocrystal

open _root_.LaurentSeries

variable {k E : Type*} [Field k] [CommRing E] [Algebra E k⸨X⸩]
  {p : ℕ} [Fact p.Prime] [CharP k p] [IsAlgClosed k] {f : ℕ}
  {σ : k⸨X⸩ ≃ₐ[E] k⸨X⸩} {D D' : FiniteIsocrystal σ}

local instance : RingHomInvPair (σ : k⸨X⸩ →+* k⸨X⸩) (σ.symm : k⸨X⸩ →+* k⸨X⸩) :=
  RingHomInvPair.of_ringEquiv σ.toRingEquiv

local instance : RingHomInvPair (σ.symm : k⸨X⸩ →+* k⸨X⸩) (σ : k⸨X⸩ →+* k⸨X⸩) :=
  RingHomInvPair.of_ringEquiv_symm σ.toRingEquiv

private noncomputable def kerFrobenius (g : D ⟶ D') :
    g.hom.ker ≃ₛₗ[(σ : k⸨X⸩ →+* k⸨X⸩)] g.hom.ker :=
  LinearEquiv.ofBijective (D.frobenius.restrict fun x hx => by
    rw [LinearMap.mem_ker, g.hom_frobenius, LinearMap.mem_ker.mp hx, map_zero]) <| by
      refine ⟨fun x y h => Subtype.ext (D.frobenius_injective (congrArg Subtype.val h)), ?_⟩
      intro y
      obtain ⟨x, hx⟩ := D.frobenius_surjective y.val
      have hxker : x ∈ g.hom.ker := by
        rw [LinearMap.mem_ker]
        apply D'.frobenius_injective
        rw [← g.hom_frobenius, hx, LinearMap.mem_ker.mp y.property, map_zero]
      exact ⟨⟨x, hxker⟩, Subtype.ext hx⟩

/-- Every surjective morphism of equal-characteristic finite isocrystals over an algebraically
closed residue field has an intertwining section. In particular, every short exact sequence
of such isocrystals splits. -/
theorem isSplitEpi_of_surjective (hσ : σ.toRingEquiv = coefficientFrobenius p f)
    (hf : 0 < f) (g : D ⟶ D') (hg : Surjective g.hom) : IsSplitEpi g := by
  obtain ⟨s, hs⟩ := g.hom.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hg)
  let Φ := LinearEquiv.ofBijective D.frobenius D.frobenius_bijective
  let Φ' := LinearEquiv.ofBijective D'.frobenius D'.frobenius_bijective
  -- Conjugation by Frobenius measures whether a linear section intertwines.
  let defect : D' →ₗ[k⸨X⸩] D := s - (Φ'.arrowCongr Φ) s
  have hright (y : D') : g.hom (s y) = y := DFunLike.congr_fun hs y
  have hdefect (x : D') : g.hom (defect x) = 0 := by
    simp only [defect, LinearMap.sub_apply, map_sub, LinearEquiv.arrowCongr_apply, Φ,
      LinearEquiv.ofBijective_apply, g.hom_frobenius, hright]
    exact sub_eq_zero.mpr (Φ'.apply_symm_apply x).symm
  let δ : D' →ₗ[k⸨X⸩] g.hom.ker := defect.codRestrict _ hdefect
  let Ψ : (D' →ₗ[k⸨X⸩] g.hom.ker) ≃ₛₗ[(σ : k⸨X⸩ →+* k⸨X⸩)]
      (D' →ₗ[k⸨X⸩] g.hom.ker) := Φ'.arrowCongr (kerFrobenius g)
  have hsurj : Surjective (fun x => Ψ x - x) := by
    have hRingHom : (σ : k⸨X⸩ →+* k⸨X⸩) = (coefficientFrobenius p f).toRingHom :=
      congrArg RingEquiv.toRingHom hσ
    have h (T : (D' →ₗ[k⸨X⸩] g.hom.ker) →ₛₗ[(σ : k⸨X⸩ →+* k⸨X⸩)]
        (D' →ₗ[k⸨X⸩] g.hom.ker)) : Surjective (fun x => T x - x) := by
      revert T
      rw [hRingHom]
      exact fun T => surjective_sub_id_of_semilinear p hf T
    exact h Ψ.toLinearMap
  -- A correction with image in the kernel preserves the section equation.
  obtain ⟨t, ht⟩ := hsurj δ
  let sectionMap := s + g.hom.ker.subtype.comp t
  have hcomm (x : D') : sectionMap (D'.frobenius x) = D.frobenius (sectionMap x) := by
    have hx : Φ'.symm (D'.frobenius x) = x := Φ'.symm_apply_apply x
    have hker (y : g.hom.ker) : (kerFrobenius g y : D) = D.frobenius y := (rfl)
    have hδ (y : D') : (δ y : D) = defect y := (rfl)
    have h := congrArg Subtype.val (DFunLike.congr_fun ht (D'.frobenius x))
    simp only [LinearMap.sub_apply, Submodule.coe_sub, Ψ, LinearEquiv.arrowCongr_apply,
      hx, hker, hδ, defect, Φ, LinearEquiv.ofBijective_apply] at h
    simpa only [sectionMap, LinearMap.add_apply, LinearMap.comp_apply, Submodule.subtype_apply,
      map_add, add_comm] using sub_eq_sub_iff_add_eq_add.mp h.symm
  refine IsSplitEpi.mk' ⟨ofHom sectionMap hcomm, hom_ext ?_⟩
  ext x
  simp [sectionMap, hright, LinearMap.mem_ker.mp (t x).property]

end TauCeti.FiniteIsocrystal
