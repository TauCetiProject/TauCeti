/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Basic
public import TauCeti.CategoryTheory.Generator.GeneratorCogenerator
public import TauCeti.CategoryTheory.Preadditive.AdditiveGenerator
public import TauCeti.RingTheory.DominantDimension.Basic
public import TauCeti.RingTheory.GlobalDimension

import Mathlib.RingTheory.HopkinsLevitzki
import TauCeti.Algebra.Category.FGModuleCat.End
import TauCeti.Algebra.Category.FGModuleCat.Generator.Basic
import TauCeti.Algebra.Category.ModuleCat.Algebra
import TauCeti.CategoryTheory.Preadditive.Projectivization.GlobalDimension
import TauCeti.RingTheory.GlobalDimension.AdditiveGenerator
import TauCeti.RingTheory.GlobalDimension.MulOpposite
import TauCeti.RingTheory.Morita.GlobalDimension
import TauCeti.RingTheory.Morita.Tachikawa.Basic

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
(`CategoryTheory.IsSeparator.isAdditiveGenerator_of_globalDimension_le_two`, in
`TauCeti.CategoryTheory.Preadditive.Projectivization.GlobalDimension`).

## Main definitions

* `TauCeti.IsAuslanderAlgebra Γ`: `Γ` has global dimension at most two and dominant dimension at
  least two.

## Main results

* `TauCeti.isAuslanderAlgebra_end`: **the Auslander correspondence, forward direction**: the
  endomorphism ring of an additive generator of `mod A`, for an Artin algebra `A`, is an Auslander
  algebra.
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

open CategoryTheory

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
    two_le_dominantDimension_end R M hM.isGeneratorCogenerator⟩

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
  -- `End Q` is finite over `R`, so `(End Q)ᵐᵒᵖ` is Noetherian.
  have : Module.Finite R (End Q) := Module.Finite.equiv End.linearEquiv.symm
  have : Module.Finite R (End Q)ᵐᵒᵖ := Module.Finite.equiv (MulOpposite.opLinearEquiv R)
  have : IsNoetherianRing (End Q)ᵐᵒᵖ := isNoetherian_of_tower R inferInstance
  refine hQ.isSeparator.isAdditiveGenerator_of_globalDimension_le_two ?_ fun X ↦ ?_
  · rwa [globalDimension_mulOpposite_of_moduleFinite R (End Q),
      (FGModuleCat.endRingEquiv Q).globalDimension_eq]
  · obtain ⟨n, i, hi⟩ := hQ.isCoseparator.exists_mono_biproduct X
    exact ⟨_, i, additiveClosure_biproduct n, hi⟩

open scoped ModuleCat.Algebra in
/-- **The Auslander correspondence, converse.** An Auslander algebra `Γ` that is an Artin algebra
is isomorphic, as an `R`-algebra, to the endomorphism algebra of an additive generator `M` of
`mod B` for some Artin `R`-algebra `B`. The base ring `R` may live in any universe. Dominant
dimension alone does not suffice: `k[ε]/(ε²)` has infinite dominant dimension and infinite global
dimension. -/
theorem exists_isAdditiveGenerator_algEquiv_end (R : Type*) [CommRing R] [IsArtinianRing R]
    (Γ : Type u) [Ring Γ] [Algebra R Γ] [Module.Finite R Γ] (hΓ : IsAuslanderAlgebra Γ) :
    ∃ (B : Type u) (_ : Ring B) (_ : Algebra R B) (_ : Module.Finite R B) (M : FGModuleCat.{u} B),
      IsAdditiveGenerator M ∧ Nonempty (Γ ≃ₐ[R] Module.End B M.obj) := by
  -- Morita-Tachikawa writes `Γ ≅ Module.End B M` for a generator-cogenerator `M`, which is an
  -- additive generator since `Module.End B M` has global dimension at most two.
  obtain ⟨B, _, _, _, M, hM, ⟨e⟩⟩ := exists_algEquiv_end_of_two_le_dominantDimension R Γ hΓ.2
  refine ⟨B, inferInstance, inferInstance, inferInstance, M,
    hM.isAdditiveGenerator_of_globalDimension_le_two R ?_, ⟨e⟩⟩
  rw [← e.toRingEquiv.globalDimension_eq]
  exact hΓ.1

end TauCeti
