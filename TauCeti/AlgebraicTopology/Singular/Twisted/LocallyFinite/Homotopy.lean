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

-- Transport linear maps to the terms of the locally finite complex. The algebraic laws below
-- keep the homotopy proof independent of the eqToHom/ofHom representation.
private def locallyFiniteHom {a b : ℕ}
    (f : locallyFiniteChains L a →ₗ[R] locallyFiniteChains K b) :
    (locallyFiniteChainComplex L).X a ⟶ (locallyFiniteChainComplex K).X b :=
  eqToHom (locallyFiniteChainComplex_X L a) ≫ ModuleCat.ofHom f ≫
    eqToHom (locallyFiniteChainComplex_X K b).symm

private lemma locallyFiniteHom_add {a b : ℕ}
    (f g : locallyFiniteChains L a →ₗ[R] locallyFiniteChains K b) :
    locallyFiniteHom (f + g) = locallyFiniteHom f + locallyFiniteHom g := by
  simp only [locallyFiniteHom, ModuleCat.ofHom_add, Preadditive.comp_add, Preadditive.add_comp]

private lemma locallyFiniteHom_comp {Z : TopCat.{v}}
    {J : LocalCoefficientSystem.{u, v, max v w} R Z} {a b c : ℕ}
    (f : locallyFiniteChains L a →ₗ[R] locallyFiniteChains K b)
    (g : locallyFiniteChains K b →ₗ[R] locallyFiniteChains J c) :
    locallyFiniteHom (g ∘ₗ f) = locallyFiniteHom f ≫ locallyFiniteHom g := by
  simp only [locallyFiniteHom, ModuleCat.ofHom_comp, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

private lemma locallyFiniteHom_eq_add {a b : ℕ}
    {f g h : locallyFiniteChains L a →ₗ[R] locallyFiniteChains K b} (heq : f - g = h) :
    locallyFiniteHom f = locallyFiniteHom h + locallyFiniteHom g := by
  simpa only [locallyFiniteHom_add] using
    congrArg locallyFiniteHom ((sub_eq_iff_eq_add (a := f) (b := g) (c := h)).mp heq)

/-- A chain homotopy with properly supported components extends to a chain homotopy of locally
finite chains. Proper support of the endpoints alone would not suffice. -/
def extendLocallyFiniteHomotopy
    (hφ : ∀ k, IsProperlySupported (φ.f k))
    (hψ : ∀ k, IsProperlySupported (ψ.f k))
    (H : Homotopy φ ψ) (hH : ∀ k, IsProperlySupported (H.hom k (k + 1))) :
    Homotopy (extendLocallyFiniteChainMap φ hφ) (extendLocallyFiniteChainMap ψ hψ) := by
  refine Homotopy.equivSubZero.symm <| Homotopy.mkChainComplex _
    (fun k ↦ locallyFiniteHom (extendLocallyFinite (hH k))) ?_ ?_
  · -- In degree zero there is only the boundary of the prism, with no preceding component.
    have hh : φ.f 0 - ψ.f 0 = H.hom 0 1 ≫ (twistedChainComplex K).d 1 0 := by
      have h := H.comm 0
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, zero_add] at h
      exact sub_eq_iff_eq_add.mpr h
    have key : extendLocallyFinite (hφ 0) - extendLocallyFinite (hψ 0) =
        locallyFiniteBoundary K 0 ∘ₗ extendLocallyFinite (hH 0) := by
      rw [locallyFiniteBoundary_def, extendLocallyFinite_comp (hH 0) (isProperlySupported_d 0)]
      exact (sub_eq_iff_eq_add (a := extendLocallyFinite (hφ 0))
        (b := extendLocallyFinite (hψ 0))).mpr
          (extendLocallyFinite_eq_add (hφ 0)
            ((hH 0).comp (isProperlySupported_d 0)) (hψ 0) (sub_eq_iff_eq_add.mp hh))
    rw [HomologicalComplex.sub_f_apply]
    apply sub_eq_iff_eq_add.mpr
    have transported := locallyFiniteHom_eq_add key
    rw [locallyFiniteHom_comp] at transported
    simpa only [extendLocallyFiniteChainMap_f, locallyFiniteChainComplex_d,
      locallyFiniteHom] using transported
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
      rw [locallyFiniteBoundary_def, locallyFiniteBoundary_def,
        extendLocallyFinite_comp (isProperlySupported_d k) (hH k),
        extendLocallyFinite_comp (hH (k + 1)) (isProperlySupported_d (k + 1))]
      exact extendLocallyFinite_sub_eq_add (hφ (k + 1)) (hψ (k + 1))
        ((isProperlySupported_d k).comp (hH k))
        ((hH (k + 1)).comp (isProperlySupported_d (k + 1))) hh
    rw [HomologicalComplex.sub_f_apply]
    apply sub_eq_iff_eq_add.mpr
    have transported := locallyFiniteHom_eq_add key
    rw [locallyFiniteHom_add, locallyFiniteHom_comp, locallyFiniteHom_comp] at transported
    simpa only [extendLocallyFiniteChainMap_f, locallyFiniteChainComplex_d,
      locallyFiniteHom] using transported

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
