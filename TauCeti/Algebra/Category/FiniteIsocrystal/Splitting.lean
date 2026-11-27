/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FiniteIsocrystal.Abelian
import TauCeti.GroupTheory.FixedSubgroup.Lang
import TauCeti.LinearAlgebra.Exact

/-!
# Splitting finite isocrystal epimorphisms

If every scalar difference polynomial with a nonzero coefficient acts surjectively, the
identity on the target of an epimorphism has a lift fixed by Frobenius conjugation.
This lift is a Frobenius-equivariant section.
-/

public section

open CategoryTheory Function

namespace TauCeti.FiniteIsocrystal

universe u

variable {E L : Type*} [CommRing E] [Field L] [Algebra E L]
  {σ : L ≃ₐ[E] L} {D D' : FiniteIsocrystal.{u} σ}

local instance : RingHomInvPair (σ : L →+* L) (σ.symm : L →+* L) :=
  RingHomInvPair.of_ringEquiv σ.toRingEquiv

local instance : RingHomInvPair (σ.symm : L →+* L) (σ : L →+* L) :=
  RingHomInvPair.of_ringEquiv_symm σ.toRingEquiv

/-- Every epimorphism of finite isocrystals splits if every scalar difference polynomial in
`σ` with at least one nonzero coefficient acts surjectively on the coefficient field. -/
theorem isSplitEpi_of_surjective_sum_mul_iterate
    (hσ : ∀ (s : Finset ℕ) (a : ℕ → L), (∃ i ∈ s, a i ≠ 0) →
      Surjective (fun x : L => ∑ i ∈ s, a i * σ.toRingEquiv^[i] x))
    (g : D ⟶ D') [Epi g] : IsSplitEpi g := by
  let Φ (A : FiniteIsocrystal.{u} σ) := LinearEquiv.ofBijective A.frobenius A.frobenius_bijective
  have fixed_iff {A B : FiniteIsocrystal.{u} σ} (t : A →ₗ[L] B) :
      (Φ A).arrowCongr (Φ B) t = t ↔ ∀ x, t (A.frobenius x) = B.frobenius (t x) := by
    rw [DFunLike.ext_iff, (Φ A).surjective.forall]
    simp only [LinearEquiv.arrowCongr_apply, LinearEquiv.symm_apply_apply]
    simp only [Φ, LinearEquiv.ofBijective_apply]
    exact forall_congr' fun _ => eq_comm
  let K := D.sub g.hom.ker (fun _ => frobenius_mem_ker g)
  let action (A : FiniteIsocrystal.{u} σ) : (D' →ₗ[L] A) →+ (D' →ₗ[L] A) :=
    ((Φ D').arrowCongr (Φ A)).toLinearMap.toAddMonoidHom
  let post := (g.hom.compRight L (M := D')).toAddMonoidHom
  let incl := (g.hom.ker.subtype.compRight L (M := D')).toAddMonoidHom
  have hpost (t : D' →ₗ[L] D) : post (action D t) = action D' (post t) := by
    simpa only [action, post, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_toLinearMap,
      LinearMap.compRight_apply, (fixed_iff g.hom).mpr g.hom_frobenius] using
      (LinearEquiv.arrowCongr_comp (Φ D') (Φ D) (Φ D') t g.hom).symm
  have hincl (t : D' →ₗ[L] K) : action D (incl t) = incl (action K t) := by
    have hι : (Φ K).arrowCongr (Φ D) g.hom.ker.subtype = g.hom.ker.subtype := by
      simpa only [subι_hom] using
        (fixed_iff _).mpr (D.subι _ (fun _ => frobenius_mem_ker g)).hom_frobenius
    simpa only [action, incl, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_toLinearMap,
      LinearMap.compRight_apply, hι] using
      LinearEquiv.arrowCongr_comp (Φ D') (Φ K) (Φ D) t g.hom.ker.subtype
  obtain ⟨s, hfix, hsection⟩ := post.exists_fixed_lift_of_surjective_sub_id incl
    ((LinearMap.exact_subtype_ker_map g.hom).compRight_of_injective (T := L) D'
      g.hom.ker.injective_subtype) (action K) (action D) (action D') hpost hincl
    (((Φ D').arrowCongr (Φ K)).toLinearMap.surjective_sub_id_of_surjective_sum_mul_iterate
      σ.toRingEquiv hσ)
    (y := LinearMap.id) (by
      obtain ⟨t, ht⟩ := ((epi_iff_surjective g).mp inferInstance).surjective_linearMapComp_left
        (LinearMap.id (R := L) (M := D'))
      exact ⟨t, by simpa only [post, LinearMap.toAddMonoidHom_coe, LinearMap.compRight_apply]
        using ht⟩)
    (by simpa only [action, LinearEquiv.conj, LinearMap.toAddMonoidHom_coe,
      LinearEquiv.coe_toLinearMap] using (Φ D').conj_id)
  refine IsSplitEpi.mk' ⟨ofHom s ((fixed_iff s).mp ?_), hom_ext ?_⟩
  · simpa only [action, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_toLinearMap] using hfix
  · simpa only [post, hom_comp, hom_ofHom, hom_id, LinearMap.toAddMonoidHom_coe,
      LinearMap.compRight_apply] using hsection

end TauCeti.FiniteIsocrystal
