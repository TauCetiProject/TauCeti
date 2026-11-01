/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Twisted.LocallyFinite.Functoriality
public import TauCeti.Algebra.Homology.Homotopy

/-!
# Extending properly supported chain homotopies

A chain homotopy of twisted singular chains extends to locally finite chains when each of its
components is properly supported. In particular the extensions of the two chain maps induce the
same map on Borel–Moore homology. The support condition concerns the homotopy itself, not just
its endpoints: arbitrary homotopies do not preserve locally finite chains.

The construction uses `extendLocallyFinite` and its compatibility with composition and finite
addition. No compactness, local compactness or countability assumption on the space is needed.

## References

* G. E. Bredon, *Sheaf Theory*, 2nd ed., Chapter V, for locally finite homology.
-/

public section

noncomputable section

open CategoryTheory

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] {X Y : TopCat.{v}}
  {L : LocalCoefficientSystem.{u, v, max v w} R X}
  {K : LocalCoefficientSystem.{u, v, max v w} R Y}
  {φ ψ : twistedChainComplex L ⟶ twistedChainComplex K}

/-- A chain homotopy with properly supported components extends to a chain homotopy of locally
finite chains. Proper support of the endpoints alone would not suffice. -/
def extendLocallyFiniteHomotopy
    (hφ : ∀ k, IsProperlySupported (φ.f k))
    (hψ : ∀ k, IsProperlySupported (ψ.f k))
    (H : Homotopy φ ψ) (hH : ∀ k, IsProperlySupported (H.hom k (k + 1))) :
    Homotopy (extendLocallyFiniteChainMap φ hφ) (extendLocallyFiniteChainMap ψ hψ) := by
  refine Homotopy.equivSubZero.symm <| Homotopy.mkChainComplex _
    (fun k ↦ eqToHom (locallyFiniteChainComplex_X L k) ≫
      ModuleCat.ofHom (extendLocallyFinite (hH k)) ≫
        eqToHom (locallyFiniteChainComplex_X K (k + 1)).symm) ?_ ?_
  · -- In degree zero there is only the boundary of the prism, with no preceding component.
    have hh : φ.f 0 - ψ.f 0 = H.hom 0 1 ≫ (twistedChainComplex K).d 1 0 := by
      have h := H.comm 0
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, zero_add] at h
      exact sub_eq_iff_eq_add.mpr h
    have key : extendLocallyFinite (hφ 0) - extendLocallyFinite (hψ 0) =
        locallyFiniteBoundary K 0 ∘ₗ extendLocallyFinite (hH 0) := by
      refine LinearMap.ext fun ⟨c, hc⟩ ↦ Subtype.ext ?_
      replace hc := mem_locallyFiniteChains.mp hc
      simp only [LinearMap.sub_apply, Submodule.coe_sub, LinearMap.comp_apply,
        coe_extendLocallyFinite, coe_locallyFiniteBoundary]
      rw [← extendLocallyFiniteFun_sub (hφ 0) (hψ 0) hc, hh,
        ← extendLocallyFiniteFun_extendLocallyFiniteFun (hH 0) (isProperlySupported_d 0) hc,
        extendLocallyFiniteFun_d]
    -- Transport the module-level identity along the named identifications of complex terms.
    rw [HomologicalComplex.sub_f_apply]
    apply sub_eq_iff_eq_add.mpr
    simpa [extendLocallyFiniteChainMap_f, locallyFiniteChainComplex_d,
      Preadditive.comp_add, Preadditive.add_comp, Category.assoc, ModuleCat.ofHom_comp] using
      congrArg (fun f ↦ eqToHom (locallyFiniteChainComplex_X L 0) ≫ ModuleCat.ofHom f ≫
        eqToHom (locallyFiniteChainComplex_X K 0).symm) (sub_eq_iff_eq_add.mp key)
  · -- In positive degrees both composites extend, and extension respects their sum.
    intro k
    have hh : φ.f (k + 1) - ψ.f (k + 1) =
        (twistedChainComplex L).d (k + 1) k ≫ H.hom k (k + 1) +
          H.hom (k + 1) (k + 2) ≫ (twistedChainComplex K).d (k + 2) (k + 1) := by
      have h := H.comm (k + 1)
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at h
      exact sub_eq_iff_eq_add.mpr h
    have key : extendLocallyFinite (hφ (k + 1)) - extendLocallyFinite (hψ (k + 1)) =
        extendLocallyFinite (hH k) ∘ₗ locallyFiniteBoundary L k +
          locallyFiniteBoundary K (k + 1) ∘ₗ extendLocallyFinite (hH (k + 1)) := by
      refine LinearMap.ext fun ⟨c, hc⟩ ↦ Subtype.ext ?_
      replace hc := mem_locallyFiniteChains.mp hc
      simp only [LinearMap.sub_apply, LinearMap.add_apply, Submodule.coe_sub, Submodule.coe_add,
        LinearMap.comp_apply, coe_extendLocallyFinite, coe_locallyFiniteBoundary]
      rw [← extendLocallyFiniteFun_sub (hφ (k + 1)) (hψ (k + 1)) hc, hh,
        extendLocallyFiniteFun_add ((isProperlySupported_d k).comp (hH k))
          ((hH (k + 1)).comp (isProperlySupported_d (k + 1))) hc,
        ← extendLocallyFiniteFun_extendLocallyFiniteFun (isProperlySupported_d k) (hH k) hc,
        ← extendLocallyFiniteFun_extendLocallyFiniteFun (hH (k + 1))
          (isProperlySupported_d (k + 1)) hc,
        extendLocallyFiniteFun_d, extendLocallyFiniteFun_d]
    rw [HomologicalComplex.sub_f_apply]
    apply sub_eq_iff_eq_add.mpr
    simpa [extendLocallyFiniteChainMap_f, locallyFiniteChainComplex_d,
      Preadditive.comp_add, Preadditive.add_comp, Category.assoc, ModuleCat.ofHom_comp] using
      congrArg (fun f ↦ eqToHom (locallyFiniteChainComplex_X L (k + 1)) ≫ ModuleCat.ofHom f ≫
        eqToHom (locallyFiniteChainComplex_X K (k + 1)).symm) (sub_eq_iff_eq_add.mp key)

/-- In adjacent degrees the extended homotopy is the extension of the original component. -/
@[simp]
lemma extendLocallyFiniteHomotopy_hom
    (hφ : ∀ k, IsProperlySupported (φ.f k))
    (hψ : ∀ k, IsProperlySupported (ψ.f k))
    (H : Homotopy φ ψ) (hH : ∀ k, IsProperlySupported (H.hom k (k + 1))) (k : ℕ) :
    (extendLocallyFiniteHomotopy hφ hψ H hH).hom k (k + 1) =
      eqToHom (locallyFiniteChainComplex_X L k) ≫ ModuleCat.ofHom (extendLocallyFinite (hH k)) ≫
        eqToHom (locallyFiniteChainComplex_X K (k + 1)).symm :=
  Homotopy.mkChainComplex_hom_succ _ _ _ _ k

end TauCeti.LocalCoefficientSystem
