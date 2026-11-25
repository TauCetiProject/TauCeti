/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FiniteIsocrystal.Abelian
public import TauCeti.RingTheory.LaurentSeries.DifferenceEquation

import TauCeti.GroupTheory.FixedSubgroup.Lang
import TauCeti.LinearAlgebra.Exact

/-!
# Splitting extensions of equal-characteristic isocrystals

Every epimorphism of finite isocrystals over `k((X))` has a Frobenius-equivariant
section when `k` is algebraically closed and Frobenius fixes `X` and raises
each coefficient to `p^f` for `f > 0`. The identity on the target is fixed by
Frobenius conjugation. Surjectivity of the Lang map on linear maps into the
kernel gives a fixed lift of this identity, hence an equivariant section.
-/

public section

open CategoryTheory Function
open scoped LaurentSeries

namespace TauCeti.FiniteIsocrystal

variable {k E : Type*} [Field k] [CommRing E] [Algebra E k⸨X⸩]
  {p : ℕ} [Fact p.Prime] [CharP k p] [IsAlgClosed k] {f : ℕ}
  {σ : k⸨X⸩ ≃ₐ[E] k⸨X⸩} {D D' : FiniteIsocrystal σ}

local instance : RingHomInvPair (σ : k⸨X⸩ →+* k⸨X⸩) (σ.symm : k⸨X⸩ →+* k⸨X⸩) :=
  RingHomInvPair.of_ringEquiv σ.toRingEquiv

local instance : RingHomInvPair (σ.symm : k⸨X⸩ →+* k⸨X⸩) (σ : k⸨X⸩ →+* k⸨X⸩) :=
  RingHomInvPair.of_ringEquiv_symm σ.toRingEquiv

/-- Every epimorphism of equal-characteristic finite isocrystals over an algebraically
closed residue field splits when Frobenius fixes `X` and raises each coefficient to
`p^f` for `f > 0`. In particular, every short exact sequence of such isocrystals splits. -/
theorem isSplitEpi_of_epi (hσ : σ.toRingEquiv = LaurentSeries.coefficientFrobenius p f)
    (hf : 0 < f) (g : D ⟶ D') [Epi g] : IsSplitEpi g := by
  let Φ := LinearEquiv.ofBijective D.frobenius D.frobenius_bijective
  let Φ' := LinearEquiv.ofBijective D'.frobenius D'.frobenius_bijective
  let F : (D' →ₗ[k⸨X⸩] D) ≃ₛₗ[(σ : k⸨X⸩ →+* k⸨X⸩)] _ := Φ'.arrowCongr Φ
  let F' : (D' →ₗ[k⸨X⸩] D') ≃ₛₗ[(σ : k⸨X⸩ →+* k⸨X⸩)] _ := Φ'.arrowCongr Φ'
  let K := D.sub g.hom.ker (fun _ => frobenius_mem_ker g)
  let Ψ : (D' →ₗ[k⸨X⸩] K) ≃ₛₗ[(σ : k⸨X⸩ →+* k⸨X⸩)]
      (D' →ₗ[k⸨X⸩] K) := Φ'.arrowCongr (LinearEquiv.ofBijective K.frobenius K.frobenius_bijective)
  have hpost (t : D' →ₗ[k⸨X⸩] D) : g.hom.comp (F t) = F' (g.hom.comp t) :=
    LinearMap.ext fun x => by
      simpa only [LinearMap.comp_apply, LinearEquiv.arrowCongr_apply, F, F', Φ, Φ',
        LinearEquiv.ofBijective_apply] using g.hom_frobenius (t (Φ'.symm x))
  have hincl (t : D' →ₗ[k⸨X⸩] g.hom.ker) :
      F (g.hom.ker.subtype.comp t) = g.hom.ker.subtype.comp (Ψ t) :=
    LinearMap.ext fun x => by
      simpa only [F, Ψ, Φ, LinearEquiv.arrowCongr_apply, LinearMap.comp_apply,
        LinearEquiv.ofBijective_apply, subι_hom] using
        ((D.subι _ (fun _ => frobenius_mem_ker g)).hom_frobenius (t (Φ'.symm x))).symm
  have hid : F' LinearMap.id = LinearMap.id := LinearMap.ext fun x => by
    simpa only [F', LinearEquiv.arrowCongr_apply, LinearMap.id_apply] using Φ'.apply_symm_apply x
  have hdiff (T : (D' →ₗ[k⸨X⸩] K) →ₛₗ[(σ : k⸨X⸩ →+* k⸨X⸩)] (D' →ₗ[k⸨X⸩] K)) :
      Surjective (fun t => T t - t) := by
    have hσ' : (σ : k⸨X⸩ →+* k⸨X⸩) = _ := congrArg RingEquiv.toRingHom hσ
    -- Quantify over the map so rewriting its scalar twist also changes its type.
    revert T
    rw [hσ']
    exact LaurentSeries.surjective_sub_id_of_coefficientFrobenius_semilinear p hf
  obtain ⟨s, hfix, hsection⟩ :=
    (g.hom.compRight k⸨X⸩ (M := D')).toAddMonoidHom.exists_fixed_lift_of_surjective_sub_id
      (g.hom.ker.subtype.compRight k⸨X⸩).toAddMonoidHom
      ((LinearMap.exact_subtype_ker_map g.hom).compRight_of_injective (T := k⸨X⸩) D'
        g.hom.ker.injective_subtype)
      Ψ.toLinearMap.toAddMonoidHom F.toLinearMap.toAddMonoidHom F'.toLinearMap.toAddMonoidHom
      hpost hincl ((epi_iff_surjective g).mp inferInstance).surjective_linearMapComp_left
      (hdiff Ψ.toLinearMap) hid
  refine IsSplitEpi.mk' ⟨ofHom s (fun x => ?_), hom_ext hsection⟩
  change F s = s at hfix
  have h := DFunLike.congr_fun hfix (Φ' x)
  simp only [F, LinearEquiv.arrowCongr_apply, LinearEquiv.symm_apply_apply] at h
  simpa only [Φ, Φ', LinearEquiv.ofBijective_apply] using h.symm

end TauCeti.FiniteIsocrystal
