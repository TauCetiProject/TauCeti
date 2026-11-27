/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.StableEquivalent
public import TauCeti.CategoryTheory.Functor.SummandDense

/-!
# Extension of scalars is summand-dense on finitely generated projective modules

Let `f : R →+* S` be a homomorphism of possibly noncommutative rings. Extension of scalars
`T_f : P ↦ S ⊗_R P` on finitely generated projective modules is summand-dense: every finitely
generated projective `S`-module `Q` has a complement `N` with `Q ⊕ N ≅ Sⁿ`, and `Sⁿ ≅ S ⊗_R Rⁿ` is
the extension of a free module. This is the hypothesis under which the relative Grothendieck group
of `T_f` fits into the exact sequence `K₀(T_f) → K₀(R) → K₀(S)`.

## Main results

* `RingHom.isSummandDense_finiteProjectiveModulesExtendScalars`: extension of scalars along a
  ring homomorphism is summand-dense on finitely generated projective modules.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II,
  Exercise 2.17 (cofinal functors).
-/

public section

open CategoryTheory CategoryTheory.Limits TauCeti

universe u

variable {R S : Type u} [Ring R] [Ring S]

namespace RingHom

/-- **Extension of scalars is summand-dense** on finitely generated projective modules: every
finitely generated projective `S`-module `Q` is a direct summand of a free module `Sⁿ`, which is
the extension of scalars of `Rⁿ`. -/
instance isSummandDense_finiteProjectiveModulesExtendScalars (f : R →+* S) :
    f.finiteProjectiveModulesExtendScalars.IsSummandDense where
  exists_biprod_mem_essImage Q := by
    obtain ⟨N, _, _, _, _, n, ⟨e⟩⟩ := Module.Projective.exists_prod_linearEquiv_fin S Q.obj
    let N' : (finiteProjectiveModules S).FullSubcategory :=
      ⟨ModuleCat.of S N, finiteProjectiveModules_iff.2 ⟨‹_›, ‹_›⟩⟩
    let F : (finiteProjectiveModules R).FullSubcategory :=
      ⟨ModuleCat.of R (Fin n → R), finiteProjectiveModules_iff.2 ⟨inferInstance, inferInstance⟩⟩
    -- `S ⊗_R Rⁿ ≅ Sⁿ ≅ Q × N ≅ Q ⊞ N`.
    exact ⟨N', F, ⟨ObjectProperty.isoMk _
      (eqToIso (f.finiteProjectiveModulesExtendScalars_obj_obj F) ≪≫
        ((BalancedExtension.piScalarRight f (Fin n)).trans
          (e.symm.trans (FiniteProjectiveModules.biprodLinearEquiv Q N').symm)).toModuleIso)⟩⟩

end RingHom
