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
  let Ψ : (D' →ₗ[k⸨X⸩] g.hom.ker) ≃ₛₗ[(σ : k⸨X⸩ →+* k⸨X⸩)]
      (D' →ₗ[k⸨X⸩] g.hom.ker) := Φ'.arrowCongr (kerFrobenius g)
  let post := (LinearMap.compRight k⸨X⸩ (M := D') g.hom).toAddMonoidHom.toMultiplicative
  let incl := (LinearMap.compRight k⸨X⸩ (M := D') g.hom.ker.subtype).toAddMonoidHom.toMultiplicative
  have hker : incl.range = post.ker := by
    ext s
    change (∃ t : D' →ₗ[k⸨X⸩] g.hom.ker, g.hom.ker.subtype.comp t = s) ↔ g.hom.comp s = 0
    refine ⟨?_, fun h => ⟨s.codRestrict _ (DFunLike.congr_fun h), rfl⟩⟩
    rintro ⟨t, rfl⟩
    exact LinearMap.ext fun x => (t x).property
  let Ψmul := Ψ.toLinearMap.toAddMonoidHom.toMultiplicative
  have hLang : Surjective (MonoidHom.commutatorMap Ψmul) := by
    have hRingHom : (σ : k⸨X⸩ →+* k⸨X⸩) =
        (LaurentSeries.coefficientFrobenius (k := k) p f : k⸨X⸩ →+* k⸨X⸩) :=
      congrArg RingEquiv.toRingHom hσ
    have h (T : (D' →ₗ[k⸨X⸩] g.hom.ker) →ₛₗ[(σ : k⸨X⸩ →+* k⸨X⸩)]
        (D' →ₗ[k⸨X⸩] g.hom.ker)) : Surjective (fun x => T x - x) := by
      revert T
      rw [hRingHom]
      exact LaurentSeries.surjective_sub_id_of_coefficientFrobenius_semilinear p hf
    intro t
    obtain ⟨s, hs⟩ : ∃ s, Ψ s - s = -t.toAdd := h Ψ.toLinearMap (-t.toAdd)
    exact ⟨s, by
      change s - Ψ s = t.toAdd
      simpa only [neg_sub, neg_neg] using congrArg Neg.neg hs⟩
  obtain ⟨s, hfix, hsection⟩ := post.exists_fixed_lift_of_surjective_commutatorMap incl hker
    Ψmul F.toLinearMap.toAddMonoidHom.toMultiplicative
    F'.toLinearMap.toAddMonoidHom.toMultiplicative
    (fun t => LinearMap.ext fun x => by
      change g.hom (F t.toAdd x) = F' (g.hom.comp t.toAdd) x
      simpa only [LinearMap.comp_apply, LinearEquiv.arrowCongr_apply, F, F', Φ, Φ',
        LinearEquiv.ofBijective_apply] using g.hom_frobenius (t.toAdd (Φ'.symm x)))
    (fun t => LinearMap.ext fun x => by
      change F (g.hom.ker.subtype.comp t.toAdd) x = (Ψ t.toAdd x).val
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.arrowCongr_apply,
        Φ, F, Ψ, LinearEquiv.ofBijective_apply, kerFrobenius_apply])
    ((epi_iff_surjective g).mp inferInstance).surjective_linearMapComp_left hLang
    (y := Multiplicative.ofAdd LinearMap.id) (LinearMap.ext fun x => Φ'.apply_symm_apply x)
  have hcomm (x : D') : s.toAdd (D'.frobenius x) = D.frobenius (s.toAdd x) := by
    have hx : Φ'.symm (D'.frobenius x) = x := by
      simpa only [Φ', LinearEquiv.ofBijective_apply] using Φ'.symm_apply_apply x
    have h := DFunLike.congr_fun (show F s.toAdd = s.toAdd from hfix) (D'.frobenius x)
    simpa only [F, LinearEquiv.arrowCongr_apply, Φ, LinearEquiv.ofBijective_apply, hx] using h.symm
  exact IsSplitEpi.mk' ⟨ofHom s.toAdd hcomm, hom_ext hsection⟩

end TauCeti.FiniteIsocrystal
