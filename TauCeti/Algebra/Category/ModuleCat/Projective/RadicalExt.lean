/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Ext.Presentation
public import TauCeti.Algebra.Category.ModuleCat.Quotient
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import TauCeti.RingTheory.Jacobson.Semiprimary

/-!
# Extensions of projective tops and radical layers

Let `K` be a submodule of a projective module `P`, contained in its Jacobson radical.
For a semisimple module `N`, pushing out `0 → K → P → P/K → 0` gives a linear
equivalence `Hom(K, N) ≃ Ext¹(P/K, N)`: every map from `P` to `N` kills `K`, so
there are no nonzero Hom coboundaries. Writing `J` for the ring's Jacobson radical,
every map from `K` to `N` also kills `JK`, giving the equivalent computation using
`Hom(K/JK, N)`.

In particular, taking `K = JP` computes extensions from the top of a projective
module using its first radical layer `JP/J²P`. Applied to projective covers of simple
modules, this is the homological step in reading the arrows of an algebra's
Ext-quiver from its radical layers. The results require neither finite dimension
nor algebraic closedness, and the coefficient ring can be any commutative ring.
The pushout formulas also compute pushforward along maps of semisimple coefficients
by simplification.

The comparisons use `TauCeti.homCokernelEquivExt` and
`TauCeti.linearMapQuotientJacobsonEquiv`.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of
  Associative Algebras*, Vol. 1 (2006), Chapters II–III.
-/

public section

open CategoryTheory CategoryTheory.Abelian TauCeti
open scoped ModuleCat.Algebra Pointwise

namespace Submodule

universe u v w

variable {k : Type u} {A : Type v} [CommRing k] [Ring A] [Algebra k A]
  {P : ModuleCat.{max u v w} A} [Projective P]

/-- If `K` is contained in the radical of a projective module, pushing out its
quotient sequence identifies maps to a semisimple module with extensions. -/
noncomputable def homEquivExtOfLeJacobson (K : Submodule A P)
    (hK : K ≤ Module.jacobson A P) (N : ModuleCat.{max u v w} A)
    [IsSemisimpleModule A N] :
    (ModuleCat.of A K ⟶ N) ≃ₗ[k] Ext (ModuleCat.of A (P ⧸ K)) N 1 := by
  have hzero : (Linear.leftComp k N (ModuleCat.ofHom K.subtype)).range = ⊥ := by
    apply LinearMap.range_eq_bot.mpr
    ext g x
    exact IsSemisimpleModule.jacobson_le_ker A A P N g.hom (hK x.property)
  exact ((Linear.leftComp k N (ModuleCat.ofHom K.subtype)).range.quotEquivOfEqBot
    hzero).symm.trans (homCokernelEquivExt k K.shortExact_quotientShortComplex N)

/-- The comparison is the pushout of the quotient short exact sequence. -/
@[simp]
theorem homEquivExtOfLeJacobson_apply (K : Submodule A P)
    (hK : K ≤ Module.jacobson A P) (N : ModuleCat.{max u v w} A)
    [IsSemisimpleModule A N] (f : ModuleCat.of A K ⟶ N) :
    K.homEquivExtOfLeJacobson (k := k) hK N f =
      K.shortExact_quotientShortComplex.extClass.comp (Ext.mk₀ f) (add_zero 1) := by
  simp only [homEquivExtOfLeJacobson, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEqBot_symm_apply]
  exact homCokernelEquivExt_mk k K.shortExact_quotientShortComplex N f

/-- Inverse comparison recovers the map used to push out the quotient sequence. -/
@[simp]
theorem homEquivExtOfLeJacobson_symm_comp_mk₀ (K : Submodule A P)
    (hK : K ≤ Module.jacobson A P) (N : ModuleCat.{max u v w} A)
    [IsSemisimpleModule A N] (f : ModuleCat.of A K ⟶ N) :
    (K.homEquivExtOfLeJacobson (k := k) hK N).symm
        (K.shortExact_quotientShortComplex.extClass.comp (Ext.mk₀ f) (add_zero 1)) = f := by
  rw [← homEquivExtOfLeJacobson_apply (k := k) K hK N f,
    LinearEquiv.symm_apply_apply]

/-- Maps from `K/JK` to a semisimple module compute extensions of `P/K`, where
`K` is contained in the radical of the projective module `P` and `J` is the ring's
Jacobson radical. For `K = JP`, the source is Hom out of the first radical layer. -/
noncomputable def radicalLayerHomEquivExt (K : Submodule A P)
    (hK : K ≤ Module.jacobson A P) (N : ModuleCat.{max u v w} A)
    [IsSemisimpleModule A N] :
    ((K ⧸ Ring.jacobson A • (⊤ : Submodule A K)) →ₗ[A] N) ≃ₗ[k]
      Ext (ModuleCat.of A (P ⧸ K)) N 1 := by
  let e : ((K ⧸ Ring.jacobson A • (⊤ : Submodule A K)) →ₗ[A] N) ≃ₗ[k]
      (K →ₗ[A] N) :=
    (linearMapQuotientJacobsonEquiv K N).toLinearEquiv fun c f ↦ by
      ext x
      simp
  exact e.trans ((ModuleCat.homLinearEquiv
    (M := ModuleCat.of A K) (N := N) (S := k)).symm.trans
      (K.homEquivExtOfLeJacobson (k := k) hK N))

/-- The radical-layer comparison sends a map to the pushout along its composite with
the layer projection. -/
@[simp]
theorem radicalLayerHomEquivExt_apply (K : Submodule A P)
    (hK : K ≤ Module.jacobson A P) (N : ModuleCat.{max u v w} A)
    [IsSemisimpleModule A N]
    (f : (K ⧸ Ring.jacobson A • (⊤ : Submodule A K)) →ₗ[A] N) :
    K.radicalLayerHomEquivExt (k := k) hK N f =
      K.shortExact_quotientShortComplex.extClass.comp
        (Ext.mk₀ (ModuleCat.ofHom
          (f.comp (Ring.jacobson A • (⊤ : Submodule A K)).mkQ))) (add_zero 1) := by
  simp only [radicalLayerHomEquivExt, LinearEquiv.trans_apply,
    homEquivExtOfLeJacobson_apply]
  congr 2
  apply ModuleCat.hom_ext
  ext x
  exact linearMapQuotientJacobsonEquiv_apply K N f x

/-- The inverse radical-layer comparison recovers a map from its pushout class. -/
@[simp]
theorem radicalLayerHomEquivExt_symm_comp_mk₀ (K : Submodule A P)
    (hK : K ≤ Module.jacobson A P) (N : ModuleCat.{max u v w} A)
    [IsSemisimpleModule A N]
    (f : (K ⧸ Ring.jacobson A • (⊤ : Submodule A K)) →ₗ[A] N) :
    (K.radicalLayerHomEquivExt (k := k) hK N).symm
        (K.shortExact_quotientShortComplex.extClass.comp
          (Ext.mk₀ (ModuleCat.ofHom (Ring.jacobson A • (⊤ : Submodule A K)).mkQ ≫
            ModuleCat.ofHom f)) (add_zero 1)) = f := by
  rw [← ModuleCat.ofHom_comp, ← radicalLayerHomEquivExt_apply (k := k) K hK N f,
    LinearEquiv.symm_apply_apply]

end Submodule
