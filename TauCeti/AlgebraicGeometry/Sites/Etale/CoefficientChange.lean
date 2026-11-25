/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings
public import TauCeti.AlgebraicGeometry.Sites.Etale.ModuleSheaf
public import TauCeti.CategoryTheory.Sites.ComposeAndSheafify
public import TauCeti.CategoryTheory.Sites.ConstantSheaf

/-!
# Change of coefficients for finite lisse étale sheaves

Let `G : A ⥤ B` be a left adjoint, with right adjoint `R`. On sheaves, `G` induces
`Sheaf.composeAndSheafify J G`, the sheafification of the sectionwise composite with `G`, which is
left adjoint to `sheafCompose J R`. This file shows that on the small étale site it preserves
locally constant sheaves, and deduces that change of coefficients preserves finite lisse étale
sheaves of modules.

The sheafified composite with `G` sends the constant sheaf with value `M` to the constant sheaf
with value `G M` (`CategoryTheory.Sheaf.constantSheafCompComposeAndSheafifyIso`), and commutes
with the étale inverse image `f^*` along a morphism of schemes `f`, which is the sheaf pullback
along `f.smallEtaleBaseChange` (`CategoryTheory.Functor.composeAndSheafifyCompSheafPullbackIso`).
Hence if `F` is étale locally constant with values in `P`, the sheafified composite of `F` with
`G` is étale locally constant with values in any `Q` containing every `G M` with `P M`
(`CategoryTheory.Sheaf.IsLocallyConstantIn.composeAndSheafify`).

For a ring homomorphism `φ : Λ →+* Λ'`, extension of scalars `Λ' ⊗_Λ -` is left adjoint to
restriction of scalars, which is left adjoint to coextension of scalars. So extension of scalars
of étale sheaves (sheafified) preserves finite lisse sheaves
(`CategoryTheory.Sheaf.IsFiniteLisse.extendScalars`), and so does restriction of scalars along
a finite `φ` (`CategoryTheory.Sheaf.IsFiniteLisse.restrictScalars`), whose sheafified composite
agrees with `sheafCompose` (`CategoryTheory.Sheaf.composeAndSheafifyIsoSheafCompose`). No
invertibility hypothesis is needed.

## References

* A. Grothendieck, M. Artin, J.-L. Verdier, *SGA 4*, Exposé IX, §2, for locally constant sheaves.
-/

public section

universe u

open CategoryTheory Limits AlgebraicGeometry Scheme

namespace CategoryTheory.Sheaf

variable {S : Scheme.{u}} {A B : Type*} [Category* A] [Category* B] {G : A ⥤ B} {R : B ⥤ A}
  [∀ X : Scheme.{u}, HasWeakSheafify (smallEtaleTopology X) A]
  [∀ X : Scheme.{u}, HasWeakSheafify (smallEtaleTopology X) B]
  [∀ X : Scheme.{u}, (smallEtaleTopology X).HasSheafCompose R]

/-- **Change of coefficients of locally constant étale sheaves.** For a left adjoint `G`, if `F`
is étale locally constant with values in `P`, then the sheafified composite of `F` with `G` is
étale locally constant with values in any `Q` containing every `G M` with `P M`. -/
theorem IsLocallyConstantIn.composeAndSheafify (adj : G ⊣ R) {P : ObjectProperty A}
    {Q : ObjectProperty B} (hPQ : ∀ M, P M → Q (G.obj M)) {F : Sheaf (smallEtaleTopology S) A}
    (hF : F.IsLocallyConstantIn (smallEtaleTopology S) P) :
    ((Sheaf.composeAndSheafify _ G).obj F).IsLocallyConstantIn (smallEtaleTopology S) Q := by
  obtain ⟨ι, U, u, _, hu, h⟩ := (F.isLocallyConstantIn_smallEtaleTopology_iff P).mp hF
  refine .of_etaleCover_constantSheaf u hu fun i ↦ ?_
  obtain ⟨M, hM, ⟨e⟩⟩ := h i
  have := preservesSheafification_of_adjunction (smallEtaleTopology (U i)) adj
  exact ⟨G.obj M, hPQ M hM,
    ⟨((u i).smallEtaleBaseChange.composeAndSheafifyCompSheafPullbackIso adj).app F ≪≫
      (Sheaf.composeAndSheafify _ G).mapIso e ≪≫
      (constantSheafCompComposeAndSheafifyIso _ G).app M⟩⟩

/-- **Extension of scalars of finite lisse sheaves.** For a homomorphism of commutative rings
`φ : Λ →+* Λ'`, the sheafified extension of scalars `Λ' ⊗_Λ F` of a finite lisse étale sheaf of
`Λ`-modules is a finite lisse étale sheaf of `Λ'`-modules. -/
theorem IsFiniteLisse.extendScalars {Λ Λ' : Type u} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ')
    {F : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ)} (hF : F.IsFiniteLisse) :
    ((Sheaf.composeAndSheafify _ (ModuleCat.extendScalars.{u, u, u} φ)).obj F).IsFiniteLisse :=
  hF.composeAndSheafify (ModuleCat.extendRestrictScalarsAdj.{u, u, u} φ)
    fun M (_ : Module.Finite Λ M) ↦
    letI := φ.toAlgebra
    Module.Finite.equiv (ModuleCat.extendScalarsAlgebraMapIso M).toLinearEquiv.symm

/-- **Restriction of scalars of finite lisse sheaves.** For a ring homomorphism `φ : Λ →+* Λ'`
making `Λ'` a finite `Λ`-module, a finite lisse étale sheaf of `Λ'`-modules, viewed as a sheaf of
`Λ`-modules, is finite lisse. The `HasSheafCompose` hypothesis is found automatically for
commutative rings, where restriction of scalars is a right adjoint. -/
theorem IsFiniteLisse.restrictScalars {Λ Λ' : Type u} [Ring Λ] [Ring Λ'] {φ : Λ →+* Λ'}
    [(smallEtaleTopology S).HasSheafCompose (ModuleCat.restrictScalars.{u, u, u} φ)]
    (hφ : letI := φ.toModule; Module.Finite Λ Λ')
    {F : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ')} (hF : F.IsFiniteLisse) :
    ((sheafCompose (smallEtaleTopology S) (ModuleCat.restrictScalars.{u, u, u} φ)).obj
      F).IsFiniteLisse := by
  refine IsLocallyConstantIn.of_iso
    ((composeAndSheafifyIsoSheafCompose (smallEtaleTopology S)
      (ModuleCat.restrictScalars.{u, u, u} φ)).app F) ?_
  exact hF.composeAndSheafify (ModuleCat.restrictCoextendScalarsAdj.{u, u, u} φ) fun M hM ↦
    (ModuleCat.isFG_iff _).mp (φ.isFG_restrictScalars_of_finite hφ ((ModuleCat.isFG_iff M).mpr hM))

end CategoryTheory.Sheaf
