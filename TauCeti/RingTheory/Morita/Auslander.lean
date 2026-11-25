/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Basic
public import TauCeti.CategoryTheory.Generator.GeneratorCogenerator
public import TauCeti.CategoryTheory.Preadditive.AdditiveGenerator
public import TauCeti.RingTheory.DominantDimension
public import TauCeti.RingTheory.GlobalDimension

import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import TauCeti.Algebra.Category.FGModuleCat.Generator.Cogenerator
import TauCeti.Algebra.Category.ModuleCat.Algebra
import TauCeti.CategoryTheory.Functor.RingEquivEnd
import TauCeti.CategoryTheory.Preadditive.Projectivization
import TauCeti.RingTheory.Artinian.Module
import TauCeti.RingTheory.GlobalDimension.AdditiveGenerator
import TauCeti.RingTheory.GlobalDimension.MulOpposite
import TauCeti.RingTheory.Morita.GlobalDimension
import TauCeti.RingTheory.Morita.Tachikawa

/-!
# Auslander algebras

An **Auslander algebra** is an Artin algebra `Γ` with `gl.dim Γ ≤ 2 ≤ dom.dim Γ`
(`TauCeti.IsAuslanderAlgebra`). Like `TauCeti.dominantDimension`, the predicate is stated for any
ring, but it is the notion of the literature only for Artin algebras.

The Auslander correspondence says that `A ↦ Module.End A M`, for an additive generator `M` of
`mod A = FGModuleCat A`, induces a bijection from the Morita classes of representation-finite Artin
algebras onto the Morita classes of Auslander algebras. This file proves the forward direction
(`TauCeti.isAuslanderAlgebra_end`): the endomorphism ring `Γ = Module.End A M` of an additive
generator `M` of `mod A`, for an Artin algebra `A`, is an Auslander algebra. Its global dimension is
at most two (`TauCeti.IsAdditiveGenerator.globalDimension_moduleEnd_le_two`), and since an additive
generator is a generator-cogenerator (`TauCeti.IsAdditiveGenerator.isGeneratorCogenerator`), its
dominant dimension is at least two by the forward direction of the Morita-Tachikawa correspondence
(`TauCeti.two_le_dominantDimension_end`).

For nonsemisimple `A` both dimensions of `Γ` are exactly two. For semisimple `A` the ring `Γ` is
semisimple, of global dimension `0` (or `⊥` when `M = 0`) and of dominant dimension `⊤`.

It also proves the converse (`TauCeti.exists_isAdditiveGenerator_algEquiv_end`): every Auslander
algebra `Γ` that is an Artin algebra is `Module.End B M` for an additive generator `M` of `mod B`,
for some Artin algebra `B`. The converse of the Morita-Tachikawa correspondence
(`TauCeti.exists_algEquiv_end_of_two_le_dominantDimension`) writes `Γ` as `Module.End B M` for a
generator-cogenerator `M`, and the key step is that such an `M` is an additive generator once
`Module.End B M` has global dimension at most two
(`TauCeti.IsGeneratorCogenerator.isAdditiveGenerator_of_globalDimension_le_two`). For `X` in
`mod B`, the cogenerator `M` gives an exact sequence `0 → X → Q₀ → Q₁` with `Q₀`, `Q₁` in `add M`.
The functor `Hom(M, -)` is left exact and sends `add M` to finitely generated projective right
`Γ`-modules, so `Hom(M, X)` is a second syzygy of a module of projective dimension at most two,
hence projective. By projectivization it is `Hom(M, Q')` for some `Q'` in `add M`, the isomorphism
is composition with a morphism `Q' ⟶ X`, and this morphism is an isomorphism since `M` is a
generator. This part works in any abelian category
(`CategoryTheory.IsSeparator.isAdditiveGenerator_of_globalDimension_le_two`).

## Main definitions

* `TauCeti.IsAuslanderAlgebra Γ`: `Γ` has global dimension at most two and dominant dimension at
  least two.

## Main results

* `TauCeti.isAuslanderAlgebra_end`: **the Auslander correspondence, forward direction**: the
  endomorphism ring of an additive generator of `mod A`, for an Artin algebra `A`, is an Auslander
  algebra.
* `CategoryTheory.IsSeparator.additiveClosure_kernel`: for a separator `M` of an abelian category
  with `End M` right Noetherian of right global dimension at most two, `add M` is closed under
  kernels.
* `CategoryTheory.IsSeparator.isAdditiveGenerator_of_globalDimension_le_two`: such a separator is
  an additive generator if every object embeds into an object of `add M`.
* `TauCeti.IsGeneratorCogenerator.isAdditiveGenerator_of_globalDimension_le_two`: a
  generator-cogenerator `M` of `mod B`, for an Artin algebra `B`, with `Module.End B M` of global
  dimension at most two is an additive generator.
* `TauCeti.exists_isAdditiveGenerator_algEquiv_end`: **the Auslander correspondence, converse**:
  an Auslander algebra that is an Artin algebra is the endomorphism algebra of an additive
  generator of `mod B` for some Artin algebra `B`.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  Studies in Advanced Mathematics 36, CUP (1995), §VI.5, Proposition VI.5.4(a) and
  Proposition VI.5.6 (p. 214).
* M. Auslander, *Representation dimension of Artin algebras*, Queen Mary College Mathematics Notes,
  London (1971).
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v w

/-- An **Auslander algebra**: a ring `Γ` with `gl.dim Γ ≤ 2 ≤ dom.dim Γ`. Like
`TauCeti.dominantDimension`, it is stated for any ring, but it is the notion of the literature only
for Artin algebras. -/
def IsAuslanderAlgebra (Γ : Type u) [Ring Γ] : Prop :=
  TauCeti.globalDimension.{u} Γ ≤ 2 ∧ 2 ≤ dominantDimension Γ

/-- The definition of an Auslander algebra: global dimension at most two and dominant dimension at
least two. -/
theorem isAuslanderAlgebra_iff {Γ : Type u} [Ring Γ] :
    IsAuslanderAlgebra Γ ↔ TauCeti.globalDimension.{u} Γ ≤ 2 ∧ 2 ≤ dominantDimension Γ :=
  Iff.rfl

/-- **The Auslander correspondence, forward direction.** For an additive generator `M` of `mod A`,
for an Artin algebra `A`, the endomorphism ring `Module.End A M` is an Auslander algebra. The base
ring `R` may live in any universe, and the modules in any universe in which `A` is small. -/
theorem isAuslanderAlgebra_end (R : Type u) [CommRing R] [IsArtinianRing R] {A : Type v} [Ring A]
    [Algebra R A] [Module.Finite R A] [Small.{w} A] (M : FGModuleCat.{w} A)
    (hM : IsAdditiveGenerator M) : IsAuslanderAlgebra (Module.End A M.obj) :=
  isAuslanderAlgebra_iff.2 ⟨hM.globalDimension_moduleEnd_le_two R,
    two_le_dominantDimension_end R M (hM.isGeneratorCogenerator R)⟩


/-! ### Additive generators from global dimension at most two -/

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] {M : C}

attribute [local instance] Abelian.hasFiniteBiproducts

/-- Let `M` be an object of an abelian category whose endomorphism ring has right global dimension
at most two, and let `d : Q₀ ⟶ Q₁` be a morphism in `add M`. Then `Hom(M, ker d)` is a projective
right `End M`-module. Indeed `Hom(M, -)` is left exact, so `Hom(M, ker d)` is the kernel of the map
`Hom(M, d)` between the projective modules `Hom(M, Q₀)` and `Hom(M, Q₁)`: a second syzygy of its
cokernel, which has projective dimension at most two. -/
theorem projective_preadditiveCoyonedaObj_obj_kernel
    (hgl : globalDimension.{v} (End M)ᵐᵒᵖ ≤ 2) {Q₀ Q₁ : C} (h₀ : additiveClosure M Q₀)
    (h₁ : additiveClosure M Q₁) (d : Q₀ ⟶ Q₁) :
    Projective ((preadditiveCoyonedaObj M).obj (kernel d)) := by
  have := (finiteProjectiveModules_iff.1 (finiteProjectiveModules_preadditiveCoyonedaObj_obj h₀)).2
  have := (finiteProjectiveModules_iff.1 (finiteProjectiveModules_preadditiveCoyonedaObj_obj h₁)).2
  have hC := (globalDimension_le_iff_hasProjectiveDimensionLE _ 2).1 hgl
    (cokernel ((preadditiveCoyonedaObj M).map d))
  have := (hasProjectiveDimensionLT_cokernel_iff_kernel ((preadditiveCoyonedaObj M).map d) 0).1 hC
  exact Projective.of_iso (PreservesKernel.iso (preadditiveCoyonedaObj M) d).symm
    (projective_iff_hasProjectiveDimensionLT_one.2 this)

/-- Let `M` be a separator of an abelian category whose endomorphism ring is right Noetherian of
right global dimension at most two. Then the kernel of every morphism `d : Q₀ ⟶ Q₁` in `add M` lies
in `add M`. By projectivization, the finitely generated projective right `End M`-module
`Hom(M, ker d)` is `Hom(M, Q')` for some `Q'` in `add M`, and the isomorphism is composition with
some `h : Q' ⟶ ker d`. As `M` is a separator, `Hom(M, -)` is faithful, so it reflects isomorphisms
in the balanced category `C`, and `h` is an isomorphism. -/
theorem _root_.CategoryTheory.IsSeparator.additiveClosure_kernel
    [IsNoetherianRing (End M)ᵐᵒᵖ] (hM : IsSeparator M)
    (hgl : globalDimension.{v} (End M)ᵐᵒᵖ ≤ 2) {Q₀ Q₁ : C} (h₀ : additiveClosure M Q₀)
    (h₁ : additiveClosure M Q₁) (d : Q₀ ⟶ Q₁) : additiveClosure M (kernel d) := by
  let F := preadditiveCoyonedaObj M
  have hP := projective_preadditiveCoyonedaObj_obj_kernel hgl h₀ h₁ d
  -- `Hom(M, ker d)` is a submodule of the finitely generated module `Hom(M, Q₀)`.
  have := (finiteProjectiveModules_iff.1 (finiteProjectiveModules_preadditiveCoyonedaObj_obj h₀)).1
  have : Module.Finite (End M)ᵐᵒᵖ (F.obj (kernel d)) := Module.Finite.of_injective
    (F.map (kernel.ι d)).hom ((ModuleCat.mono_iff_injective _).1 inferInstance)
  obtain ⟨Q', ⟨e⟩⟩ := finiteProjectiveModules_le_essImage (M := M) (F.obj (kernel d))
    (finiteProjectiveModules_iff.2 ⟨this, inferInstance⟩)
  obtain ⟨h, hh⟩ := (preadditiveCoyonedaObj_map_bijective Q'.property (kernel d)).2 e.hom
  have : F.Faithful := (isSeparator_iff_faithful_preadditiveCoyonedaObj M).1 hM
  have : IsIso (F.map h) := hh ▸ inferInstance
  have : IsIso h := isIso_of_reflects_iso h F
  exact (additiveClosure M).prop_of_iso (asIso h) Q'.property

/-- **Additive generators from global dimension at most two.** Let `M` be a separator of an abelian
category whose endomorphism ring is right Noetherian of right global dimension at most two. If every
object embeds into an object of `add M`, then `M` is an additive generator. Indeed every object `X`
has a copresentation `0 ⟶ X ⟶ Q₀ ⟶ Q₁` with `Q₀`, `Q₁` in `add M`, so it is a kernel of a morphism
in `add M` (`CategoryTheory.IsSeparator.additiveClosure_kernel`). -/
theorem _root_.CategoryTheory.IsSeparator.isAdditiveGenerator_of_globalDimension_le_two
    [IsNoetherianRing (End M)ᵐᵒᵖ] (hM : IsSeparator M)
    (hgl : globalDimension.{v} (End M)ᵐᵒᵖ ≤ 2)
    (hmono : ∀ X : C, ∃ (Y : C) (i : X ⟶ Y), additiveClosure M Y ∧ Mono i) :
    IsAdditiveGenerator M := by
  refine isAdditiveGenerator_def.2 fun X ↦ ?_
  obtain ⟨Q₀, i, h₀, _⟩ := hmono X
  obtain ⟨Q₁, j, h₁, _⟩ := hmono (cokernel i)
  -- `X` is the kernel of `cokernel.π i`, hence of `cokernel.π i ≫ j` as `j` is a monomorphism.
  let e : X ≅ kernel (cokernel.π i ≫ j) :=
    (Abelian.monoIsKernelOfCokernel _ (colimit.isColimit _)).conePointUniqueUpToIso
      (limit.isLimit _) ≪≫ (kernelCompMono _ _).symm
  exact (additiveClosure M).prop_of_iso e.symm (hM.additiveClosure_kernel hgl h₀ h₁ _)

end Abelian

/-- **Finitely generated Artinian modules embed into finite sums of a coseparator**: if `M` is a
coseparator of `mod A`, then every object `X` of `mod A` that is Artinian as a module admits a
monomorphism into a finite biproduct of copies of `M`. -/
theorem _root_.CategoryTheory.IsCoseparator.exists_mono_biproduct {A : Type u} [Ring A]
    {M : FGModuleCat.{v} A} (hM : IsCoseparator M) (X : FGModuleCat.{v} A) [IsArtinian A X.obj] :
    ∃ (n : ℕ) (i : X ⟶ ⨁ fun _ : Fin n ↦ M), Mono i := by
  -- As `X` is Artinian, it embeds into a finite power `Mⁿ`.
  obtain ⟨n, g, hg⟩ :=
    IsArtinian.exists_injective_linearMap_pi ((FGModuleCat.isCoseparator_iff M).1 hM X)
  let ι : X ⟶ ⨁ fun _ : Fin n ↦ M :=
    biproduct.lift fun j ↦ ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.proj j ∘ₗ g))
  -- The `j`-th coordinate of `ι` is `proj j ∘ g`, so `ι` is injective because `g` is.
  refine ⟨n, ι, ConcreteCategory.mono_of_injective ι fun x y hxy ↦ hg <| funext fun j ↦ ?_⟩
  have hπ : ι ≫ biproduct.π _ j =
      ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.proj j ∘ₗ g)) := biproduct.lift_π _ j
  have h := congrArg (ConcreteCategory.hom (biproduct.π (fun _ : Fin n ↦ M) j)) hxy
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, hπ] at h
  exact h

open scoped ModuleCat.Algebra in
/-- **Generator-cogenerators with endomorphism ring of global dimension at most two are additive
generators.** Let `Q` be a generator-cogenerator of `mod B`, for an Artin algebra `B`. If
`Module.End B Q` has global dimension at most two, then `Q` is an additive generator of `mod B`.
This is the key step of the converse of the Auslander correspondence. -/
theorem IsGeneratorCogenerator.isAdditiveGenerator_of_globalDimension_le_two (R : Type u)
    [CommRing R] [IsArtinianRing R] {B : Type v} [Ring B] [Algebra R B] [Module.Finite R B]
    {Q : FGModuleCat.{w} B} (hQ : IsGeneratorCogenerator Q)
    (hgl : globalDimension.{w} (Module.End B Q.obj) ≤ 2) : IsAdditiveGenerator Q := by
  have := IsArtinianRing.of_finite R B
  have : IsNoetherianRing B := isNoetherian_of_tower R inferInstance
  -- `End Q` is Noetherian on both sides, being finite over `R`.
  have : Module.Finite R (End Q) := Module.Finite.equiv End.linearEquiv.symm
  have : Module.Finite R (End Q)ᵐᵒᵖ := Module.Finite.equiv (MulOpposite.opLinearEquiv R)
  have : IsNoetherianRing (End Q) := isNoetherian_of_tower R inferInstance
  have : IsNoetherianRing (End Q)ᵐᵒᵖ := isNoetherian_of_tower R inferInstance
  let e : End Q ≃+* Module.End B Q.obj :=
    ((ObjectProperty.fullyFaithfulι (ModuleCat.isFG B)).ringEquivEnd Q).trans
      (ModuleCat.endRingEquiv Q.obj)
  refine hQ.isSeparator.isAdditiveGenerator_of_globalDimension_le_two ?_ fun X ↦ ?_
  · rwa [globalDimension_mulOpposite, e.globalDimension_eq]
  · obtain ⟨n, i, hi⟩ := hQ.isCoseparator.exists_mono_biproduct X
    exact ⟨_, i, additiveClosure_biproduct n, hi⟩

open scoped ModuleCat.Algebra in
/-- **The Auslander correspondence, converse.** An Auslander algebra `Γ` that is an Artin algebra
is isomorphic, as an `R`-algebra, to the endomorphism algebra of an additive generator `M` of
`mod B` for some Artin `R`-algebra `B`, which is then representation-finite. The base ring `R` may
live in any universe. By the converse of the Morita-Tachikawa correspondence
(`TauCeti.exists_algEquiv_end_of_two_le_dominantDimension`), `Γ ≅ Module.End B M` for a
generator-cogenerator `M` of `mod B`, and `M` is an additive generator since `Module.End B M` has
global dimension at most two
(`TauCeti.IsGeneratorCogenerator.isAdditiveGenerator_of_globalDimension_le_two`). Dominant dimension
alone does not suffice: `k[ε]/(ε²)` has infinite dominant dimension and infinite global
dimension. -/
theorem exists_isAdditiveGenerator_algEquiv_end (R : Type*) [CommRing R] [IsArtinianRing R]
    (Γ : Type u) [Ring Γ] [Algebra R Γ] [Module.Finite R Γ] (hΓ : IsAuslanderAlgebra Γ) :
    ∃ (B : Type u) (_ : Ring B) (_ : Algebra R B) (_ : Module.Finite R B) (M : FGModuleCat.{u} B),
      IsAdditiveGenerator M ∧ Nonempty (Γ ≃ₐ[R] Module.End B M.obj) := by
  obtain ⟨B, _, _, _, M, hM, ⟨e⟩⟩ := exists_algEquiv_end_of_two_le_dominantDimension R Γ hΓ.2
  refine ⟨B, inferInstance, inferInstance, inferInstance, M,
    hM.isAdditiveGenerator_of_globalDimension_le_two R ?_, ⟨e⟩⟩
  rw [← e.toRingEquiv.globalDimension_eq]
  exact hΓ.1

end TauCeti
