/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.RingTheory.SimpleModule.Basic
public import TauCeti.Algebra.Category.FGModuleCat.Generator.Basic
public import TauCeti.CategoryTheory.Preadditive.AdditiveClosure.Basic

import Mathlib.RingTheory.Finiteness.Small
import TauCeti.Algebra.Category.FGModuleCat.End
import TauCeti.Algebra.Category.FGModuleCat.Injective
import TauCeti.Algebra.Category.ModuleCat.MatlisDuality.Projectivization
import TauCeti.Algebra.Module.Projective.Complement
import TauCeti.Algebra.Subalgebra.Center
import TauCeti.CategoryTheory.Preadditive.Projectivization.SelfInjective
import TauCeti.RingTheory.Artinian.FiniteLength
import TauCeti.RingTheory.Artinian.Subalgebra
import TauCeti.RingTheory.MatlisDuality.ArtinAlgebra
import TauCeti.RingTheory.MatlisDuality.Cogenerator

/-!
# Coseparators and injective modules over their endomorphism rings

Over an Artin algebra `A`, with `A` small in the module universe, a coseparator `M` of `mod A` is an
injective module over its endomorphism ring (`CategoryTheory.IsCoseparator.injective_end`),
dually to a generator being projective over it (`TauCeti.Module.IsGenerator.projective_end`). By
projectivization and the Hom-tensor adjunction the dual of `M` is projective as a right module over
the endomorphism ring (a left module over its opposite), and Matlis biduality returns to `M`. This
is the cogenerator half of the forward direction of the Morita-Tachikawa correspondence
(`TauCeti.two_le_dominantDimension_end`).

Conversely, let `Γ` be an algebra over a commutative Artinian ring `R` and `Q` an injective
`Γ`-module that is finitely generated over `R`. Then `Q` is a coseparator of `mod B` for its
endomorphism ring `B = Module.End Γ Q` (`TauCeti.isCoseparator_end_of_injective`). This is dual to
a finitely generated projective module being a generator over its endomorphism ring
(`TauCeti.Module.isGenerator_end_of_projective`), and is the cogenerator half of the converse of
the Morita-Tachikawa correspondence (`TauCeti.exists_algEquiv_end_of_two_le_dominantDimension`).

## Implementation notes

For the converse, Matlis duality over `R` into an injective hull `E` of `R ⧸ J(R)` has `E`
injective with each `Hom_R(R ⧸ 𝔪, E)` of length one. Under these conditions an injective module of
finite length over `R` detects the nonzero elements of every module over its endomorphism ring
(`TauCeti.exists_linearMap_end_apply_ne_zero_of_injective`). The argument works with the
elementwise description `FGModuleCat.isCoseparator_iff`, so the dual of `B` is never needed as an
object of `mod B`.

## Main results

* `CategoryTheory.IsCoseparator.injective_end`: over an Artin algebra, a coseparator `M` of `mod A`
  is an injective module over its endomorphism ring.
* `TauCeti.isCoseparator_end_of_injective`: over a commutative Artinian ring `R`, an injective
  module finitely generated over `R` is a coseparator of `mod B` for its endomorphism ring `B`.

* `TauCeti.isSemisimpleRing_of_selfInjective_moduleEnd`: if `add M` contains every cyclic
  left `A`-module and `Module.End A M` is left self-injective, then `A` is semisimple.

## References

* B. J. Müller, *The classification of algebras by dominant dimension*, Canad. J. Math. 20 (1968),
  398–409, Theorem 2.
* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  Studies in Advanced Mathematics 36, CUP (1995), §VI.5.
-/

public section

namespace TauCeti

open CategoryTheory MatlisDual

universe u v w

/-- **A coseparator is injective over its endomorphism ring.** Over an Artin algebra `A`, a
coseparator `M` of `mod A` is an injective module over `Module.End A M`. The modules may live in
any universe in which `A` is small. -/
theorem _root_.CategoryTheory.IsCoseparator.injective_end {A : Type v} [Ring A] [Small.{w} A]
    {M : FGModuleCat.{w} A} (hM : IsCoseparator M) (R : Type u) [CommRing R] [IsArtinianRing R]
    [Algebra R A] [Module.Finite R A] :
    Module.Injective (Module.End A M.obj) M.obj := by
  have := IsArtinianRing.of_finite R A
  -- Replace `R` by the centre `C` of `A` and take an injective hull `E` of `C ⧸ J(C)` in the
  -- universe of `C`; the dual of the regular module is then shrunk to the universe of `M`.
  let C := Subalgebra.center R A
  have : Module.Finite C A := Subalgebra.finite_centerAlgebra_of_finite
  obtain ⟨E, _, _, f, hf, -⟩ := exists_isInjectiveEnvelope_quotient_jacobson.{v, v} C
  have := hf.moduleInjective
  -- The dual `D_C A`, shrunk to the universe `w`, is a finitely generated injective module.
  have : Module.Finite Aᵐᵒᵖ A := .equiv (MulOpposite.opLinearEquiv Aᵐᵒᵖ).symm
  have : Module.Finite A (MatlisDual C E A) := hf.finite_matlisDual_of_finite_op
  have : Small.{w} (MatlisDual C E A) := Module.Finite.small A _
  let e := Shrink.linearEquiv.{w} A (MatlisDual C E A)
  have : Module.Injective A (Shrink.{w} (MatlisDual C E A)) :=
    ((Module.Baer.of_injective inferInstance).of_equiv e.symm).injective
  let X := FGModuleCat.of A (Shrink.{w} (MatlisDual C E A))
  have : Injective X := FGModuleCat.injective_of_moduleInjective X
  -- As a finitely generated injective object, `X` lies in `add M`; so `D_C M` is projective as a
  -- right module over `End M` (a left module over its opposite).
  have := (ModuleCat.finite_projective_end_op_matlisDual_of_additiveClosure (R := C) M.obj
    ((ModuleCat.isFG.{w} A).ι.additiveClosure_le_inverseImage M _
      (hM.additiveClosure_of_injective X)) e).2
  exact moduleInjective_of_projective_op_matlisDual (MatlisDual.bijective_evalₗ
    hf.length_quotient_linearMap_eq_one (isFiniteLength_of_finite_trans C A M.obj))

/-- **A finitely generated injective module is a coseparator over its endomorphism ring.** Let `R`
be a commutative Artinian ring and `Q` an injective `Γ`-module, for an `R`-algebra `Γ`, that is
finitely generated over `R`. Then `Q` is a coseparator of `mod B` for `B = Module.End Γ Q`. The
finiteness of `Q` over `B`, needed to state this, follows from its finiteness over `R`. The modules
may live in any universe in which `Γ` is small. -/
theorem isCoseparator_end_of_injective (R : Type u) [CommRing R] [IsArtinianRing R] {Γ : Type v}
    [Ring Γ] [Algebra R Γ] [Small.{w} Γ] {Q : Type w} [AddCommGroup Q] [Module Γ Q] [Module R Q]
    [IsScalarTower R Γ Q] [Module.Finite R Q] [Module.Injective Γ Q] :
    letI : Module.Finite (Module.End Γ Q) Q := .of_restrictScalars_finite R _ _
    IsCoseparator (FGModuleCat.of (Module.End Γ Q) Q) := by
  -- Matlis duality over `R`, into an injective hull `E` of `R ⧸ J(R)`, satisfies the hypotheses of
  -- `TauCeti.exists_linearMap_end_apply_ne_zero_of_injective`.
  obtain ⟨E, _, _, f, hf, -⟩ := exists_isInjectiveEnvelope_quotient_jacobson.{u, u} R
  have := hf.moduleInjective
  exact (FGModuleCat.isCoseparator_iff _).2 fun X x hx ↦
    exists_linearMap_end_apply_ne_zero_of_injective hf.length_quotient_linearMap_eq_one
      (isFiniteLength_of_finite R Q) hx

/-- If the additive closure of `M` contains every cyclic left `A`-module, shrunk to the universe
of `M`, and `Module.End A M` is left self-injective, then `A` is semisimple. -/
theorem isSemisimpleRing_of_selfInjective_moduleEnd {A : Type v} [Ring A] [Small.{w} A]
    {M : FGModuleCat.{w} A}
    (hM : ∀ I : Ideal A, additiveClosure M (FGModuleCat.of A (Shrink.{w} (A ⧸ I))))
    (hinj : Module.Injective (Module.End A M.obj) (Module.End A M.obj)) : IsSemisimpleRing A := by
  let e := (FGModuleCat.endRingEquiv M).symm
  have hEnd : Module.Injective (End M) (End M) :=
    Module.Injective.of_ringEquiv e e.toSemilinearEquiv
  let eA := Shrink.linearEquiv.{w} A A
  let eBot := ((Shrink.linearEquiv.{w} A (A ⧸ (⊥ : Ideal A))).trans
    ((⊥ : Submodule A A).quotEquivOfEqBot rfl)).trans eA.symm
  have hA : additiveClosure M (FGModuleCat.of A (Shrink.{w} A)) :=
    (additiveClosure M).prop_of_iso eBot.toFGModuleCatIso (hM ⊥)
  refine (isSemisimpleModule_iff A A).mpr ⟨fun I ↦ ?_⟩
  -- Bring the quotient map into the module universe of `M` before applying projectivization.
  let eQ := Shrink.linearEquiv.{w} A (A ⧸ I)
  let q := eQ.symm.toLinearMap ∘ₗ I.mkQ ∘ₗ eA.toLinearMap
  let f := FGModuleCat.ofHom q
  have hf : Function.Surjective q := eQ.symm.surjective.comp (I.mkQ_surjective.comp eA.surjective)
  have : Epi f := (ModuleCat.isFG A).ι.epi_of_epi_map ((ModuleCat.epi_iff_surjective _).2 hf)
  have := isSplitEpi_of_selfInjective_end hA (hM I) hEnd f
  let s := (section_ f).hom.hom
  have hs : q.comp s = LinearMap.id := by
    simpa only [s, f, FGModuleCat.hom_hom_comp, FGModuleCat.hom_hom_ofHom, FGModuleCat.hom_hom_id]
      using congrArg (fun g ↦ g.hom.hom) (IsSplitEpi.id f)
  have : Module.Projective A (Shrink.{w} (A ⧸ I)) := Module.Projective.of_split s q hs
  have : Module.Projective A (A ⧸ I) := Module.Projective.of_shrink.{w}
  exact I.isComplemented_of_projective_quotient

end TauCeti
