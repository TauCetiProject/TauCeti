/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FiniteIsocrystal.Basic
public import TauCeti.RingTheory.LaurentSeries.DifferenceEquation

import TauCeti.GroupTheory.FixedSubgroup.Lang

/-!
# Splitting extensions of equal-characteristic isocrystals

Every epimorphism of finite isocrystals over `k((X))` has a Frobenius-equivariant
section when `k` is algebraically closed and Frobenius fixes `X` and raises
each coefficient to `p^f` for `f > 0`. The identity on the target is fixed by
Frobenius conjugation. Surjectivity of the Lang map on linear maps into the
kernel gives a fixed lift of this identity, hence an equivariant section.
-/

public section

open AddMonoidHom (toMultiplicative_apply_apply)
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

private theorem surjective_commutatorMap_of_coefficientFrobenius
    {V : Type*} [AddCommGroup V] [Module k⸨X⸩ V] [Module.Finite k⸨X⸩ V]
    (hσ : σ.toRingEquiv = LaurentSeries.coefficientFrobenius p f) (hf : 0 < f)
    (Ψ : V →ₛₗ[(σ : k⸨X⸩ →+* k⸨X⸩)] V) :
    Surjective (MonoidHom.commutatorMap Ψ.toAddMonoidHom.toMultiplicative) := by
  have h (T : V →ₛₗ[(σ : k⸨X⸩ →+* k⸨X⸩)] V) : Surjective (fun x => T x - x) := by
    revert T
    rw [show (σ : k⸨X⸩ →+* k⸨X⸩) =
      (LaurentSeries.coefficientFrobenius (k := k) p f : k⸨X⸩ →+* k⸨X⸩) from
      congrArg RingEquiv.toRingHom hσ]
    exact LaurentSeries.surjective_sub_id_of_coefficientFrobenius_semilinear p hf
  intro t
  obtain ⟨s, hs⟩ := h Ψ (-t.toAdd)
  refine ⟨Multiplicative.ofAdd s, Multiplicative.toAdd.injective ?_⟩
  simpa only [MonoidHom.commutatorMap_apply, toAdd_div,
    toMultiplicative_apply_apply, LinearMap.toAddMonoidHom_coe, toAdd_ofAdd,
    neg_sub, neg_neg] using congrArg Neg.neg hs

/-- Every epimorphism of equal-characteristic finite isocrystals over an algebraically
closed residue field splits when Frobenius fixes `X` and raises each coefficient to
`p^f` for `f > 0`. In particular, every short exact sequence of such isocrystals splits. -/
theorem isSplitEpi_of_epi (hσ : σ.toRingEquiv = LaurentSeries.coefficientFrobenius p f)
    (hf : 0 < f) (g : D ⟶ D') [Epi g] : IsSplitEpi g := by
  let Φ := LinearEquiv.ofBijective D.frobenius D.frobenius_bijective
  let Φ' := LinearEquiv.ofBijective D'.frobenius D'.frobenius_bijective
  let F : (D' →ₗ[k⸨X⸩] D) ≃ₛₗ[(σ : k⸨X⸩ →+* k⸨X⸩)] _ := Φ'.arrowCongr Φ
  let F' : (D' →ₗ[k⸨X⸩] D') ≃ₛₗ[(σ : k⸨X⸩ →+* k⸨X⸩)] _ := Φ'.arrowCongr Φ'
  let Ψ : (D' →ₗ[k⸨X⸩] g.hom.ker) ≃ₛₗ[(σ : k⸨X⸩ →+* k⸨X⸩)]
      (D' →ₗ[k⸨X⸩] g.hom.ker) := Φ'.arrowCongr (kerFrobenius g)
  let post := (LinearMap.compRight k⸨X⸩ (M := D') g.hom).toAddMonoidHom.toMultiplicative
  let incl := (LinearMap.compRight k⸨X⸩ (M := D') g.hom.ker.subtype).toAddMonoidHom.toMultiplicative
  have hker : incl.range = post.ker := by
    ext s
    rw [MonoidHom.mem_range, MonoidHom.mem_ker]
    simp only [incl, post, toMultiplicative_apply_apply,
      LinearMap.toAddMonoidHom_coe, LinearMap.compRight_apply, Multiplicative.exists,
      ← Multiplicative.toAdd_symm_eq, Equiv.symm_apply_eq, toAdd_one]
    refine ⟨?_, fun h => ⟨s.toAdd.codRestrict _ (DFunLike.congr_fun h), rfl⟩⟩
    rintro ⟨t, rfl⟩
    exact LinearMap.ext fun x => (t x).property
  have hpost (t : D' →ₗ[k⸨X⸩] D) : g.hom.comp (F t) = F' (g.hom.comp t) :=
    LinearMap.ext fun x => by
      simpa only [LinearMap.comp_apply, LinearEquiv.arrowCongr_apply, F, F', Φ, Φ',
        LinearEquiv.ofBijective_apply] using g.hom_frobenius (t (Φ'.symm x))
  have hincl (t : D' →ₗ[k⸨X⸩] g.hom.ker) :
      F (g.hom.ker.subtype.comp t) = g.hom.ker.subtype.comp (Ψ t) :=
    LinearMap.ext fun x => by
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.arrowCongr_apply,
        Φ, F, Ψ, LinearEquiv.ofBijective_apply, kerFrobenius_apply]
  have hid : F' LinearMap.id = LinearMap.id := LinearMap.ext fun x => by
    simpa only [F', LinearEquiv.arrowCongr_apply, LinearMap.id_apply] using Φ'.apply_symm_apply x
  obtain ⟨s, hfix, hsection⟩ := post.exists_fixed_lift_of_surjective_commutatorMap incl hker
    Ψ.toLinearMap.toAddMonoidHom.toMultiplicative F.toLinearMap.toAddMonoidHom.toMultiplicative
    F'.toLinearMap.toAddMonoidHom.toMultiplicative (fun t => by
      simpa only [post, toMultiplicative_apply_apply, LinearMap.toAddMonoidHom_coe,
        LinearEquiv.coe_toLinearMap, LinearMap.compRight_apply, toAdd_ofAdd] using
        congrArg Multiplicative.ofAdd (hpost t.toAdd))
    (fun t => by
      simpa only [incl, toMultiplicative_apply_apply, LinearMap.toAddMonoidHom_coe,
        LinearEquiv.coe_toLinearMap, LinearMap.compRight_apply, toAdd_ofAdd] using
        congrArg Multiplicative.ofAdd (hincl t.toAdd))
    ((epi_iff_surjective g).mp inferInstance).surjective_linearMapComp_left
    (surjective_commutatorMap_of_coefficientFrobenius hσ hf Ψ.toLinearMap)
    (y := Multiplicative.ofAdd LinearMap.id) (congrArg Multiplicative.ofAdd hid)
  apply_fun Multiplicative.toAdd at hfix hsection
  simp only [post, toMultiplicative_apply_apply,
    LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_toLinearMap, LinearMap.compRight_apply,
    toAdd_ofAdd] at hfix hsection
  refine IsSplitEpi.mk' ⟨ofHom s.toAdd (fun x => ?_), hom_ext hsection⟩
  have h := DFunLike.congr_fun hfix (Φ' x)
  simp only [F, LinearEquiv.arrowCongr_apply, LinearEquiv.symm_apply_apply] at h
  simpa only [Φ, Φ', LinearEquiv.ofBijective_apply] using h.symm

end TauCeti.FiniteIsocrystal
