/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FiniteIsocrystal.Abelian
import TauCeti.GroupTheory.FixedSubgroup.Lang
import TauCeti.LinearAlgebra.Exact
import TauCeti.LinearAlgebra.FiniteDimensional.Semilinear

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
  let F : (D' →ₗ[L] D) ≃ₛₗ[(σ : L →+* L)] _ := (Φ D').arrowCongr (Φ D)
  let F' := (Φ D').conj
  let Ψ : (D' →ₗ[L] K) ≃ₛₗ[(σ : L →+* L)] (D' →ₗ[L] K) := (Φ D').arrowCongr (Φ K)
  have hpost (t : D' →ₗ[L] D) : g.hom.comp (F t) = F' (g.hom.comp t) := by
    simpa only [F, F', LinearEquiv.conj, (fixed_iff g.hom).mpr g.hom_frobenius] using
      (LinearEquiv.arrowCongr_comp (Φ D') (Φ D) (Φ D') t g.hom).symm
  have hincl (t : D' →ₗ[L] K) : F (g.hom.ker.subtype.comp t) = g.hom.ker.subtype.comp (Ψ t) := by
    have hι : (Φ K).arrowCongr (Φ D) g.hom.ker.subtype = g.hom.ker.subtype := by
      simpa only [subι_hom] using
        (fixed_iff _).mpr (D.subι _ (fun _ => frobenius_mem_ker g)).hom_frobenius
    simpa only [F, Ψ, hι] using
      LinearEquiv.arrowCongr_comp (Φ D') (Φ K) (Φ D) t g.hom.ker.subtype
  obtain ⟨s, hfix, hsection⟩ :=
    (g.hom.compRight L (M := D')).toAddMonoidHom.exists_fixed_lift_of_surjective_sub_id
      (g.hom.ker.subtype.compRight L).toAddMonoidHom
      ((LinearMap.exact_subtype_ker_map g.hom).compRight_of_injective (T := L) D'
        g.hom.ker.injective_subtype)
      Ψ.toLinearMap.toAddMonoidHom F.toLinearMap.toAddMonoidHom F'.toLinearMap.toAddMonoidHom
      hpost hincl (Ψ.toLinearMap.surjective_sub_id_of_surjective_sum_mul_iterate σ.toRingEquiv hσ)
      (((epi_iff_surjective g).mp inferInstance).surjective_linearMapComp_left LinearMap.id)
      (Φ D').conj_id
  have hs : F s = s := by
    simpa only [LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_toLinearMap] using hfix
  exact IsSplitEpi.mk' ⟨ofHom s ((fixed_iff s).mp hs), hom_ext hsection⟩

end TauCeti.FiniteIsocrystal
