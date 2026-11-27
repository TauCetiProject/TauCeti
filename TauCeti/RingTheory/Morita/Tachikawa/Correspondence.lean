/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Generator.Basic
public import TauCeti.RingTheory.Morita.Progenerator

import TauCeti.Algebra.Category.FGModuleCat.Generator.Endomorphism
import TauCeti.Algebra.Category.ModuleCat.Injective.AdditiveClosure
import TauCeti.Algebra.Category.ModuleCat.RestrictScalars

/-!
# The Morita-Tachikawa correspondence: injectivity on marked pairs

Let `A` and `A'` be Artin algebras over a commutative Artinian ring `R`, with generator-cogenerators
`M` of `mod A` and `M'` of `mod A'`. If the endomorphism algebras `Module.End A M` and
`Module.End A' M'` are isomorphic as `R`-algebras, then an `R`-linear equivalence
`mod A ≌ mod A'` carries `M` to `M'` (`TauCeti.exists_linear_equivalence_of_algEquiv_end`). With
the two directions in `TauCeti.RingTheory.Morita.Tachikawa.Basic`, this makes
`(A, M) ↦ Module.End A M` a bijection from such pairs, up to equivalence, onto the Artin algebras of
dominant dimension at least two, up to isomorphism.

Write `Γ = Module.End A M`, acting on `M` by evaluation. The proof recovers `A` and `M` from `Γ`:

1. `M` is finitely generated, projective and injective over `Γ`, and `A ≅ Module.End Γ M` by the
   double centralizer property of a generator (`TauCeti.algEquivEndEndOfIsGenerator`).
2. Through `e`, the module `M'` becomes a `Γ`-module `Y`, again finitely generated, projective and
   injective, with `A' ≅ Module.End Γ Y`.
3. Over `Γ`, the finitely generated projective-injective modules are the retracts of finite powers
   of `M` (`TauCeti.exists_comp_eq_id_pi_of_projective_of_injective`). The same holds for `Y`
   (`RingHom.exists_comp_eq_id_pi_restrictScalars`), so each of `M` and `Y` is a retract of a
   finite power of the other.
4. Two modules `X` and `Y` with this property have Morita equivalent endomorphism rings, by an
   equivalence carrying `X` to `Y` (`TauCeti.exists_moritaEquivalence_moduleEnd_of_comp_eq_id`).
   Both `Module.End Γ X` and `Module.End Γ Y` are corners of `C = Module.End Γ (X × Y)`, at full
   idempotents, and the corner functors send the `C`-module `X × Y` to `X` and to `Y`.

The multiplicities of `M` are kept: `M` goes to `M'` itself, not only `add M` to `add M'`.

## Main results

* `TauCeti.exists_moritaEquivalence_functor_obj_iso_of_algEquiv_end`: the correspondence at the
  level of all modules.
* `TauCeti.exists_linear_equivalence_of_algEquiv_end`: **the Morita-Tachikawa correspondence,
  injectivity on marked pairs**.

## Implementation notes

`TauCeti.RingTheory.Idempotents.Corner.Retract` identifies the endomorphism ring of a retract with
a corner of the endomorphism ring (`TauCeti.cornerEndRetractAlgEquiv`), not only of its opposite.
The modules `M` and `Y` themselves must be tracked, as modules over `Module.End Γ M` and
`Module.End Γ Y` acting by evaluation, so step 4 uses these corners. The corner functor of
`IsIdempotentElem.cornerEquivalence` is explicit, `V ↦ eV`, which computes the image of the
`C`-module `X × Y` (`TauCeti.smulTopRetractAddEquiv`).

## References

* B. J. Müller, *The classification of algebras by dominant dimension*, Canad. J. Math. 20 (1968),
  398–409, Theorem 2.
* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  Studies in Advanced Mathematics 36, CUP (1995), Section VI.5.
-/

public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u

namespace TauCeti

/-! ### The correspondence -/

section Correspondence

variable (R : Type*) [CommRing R] [IsArtinianRing R] {A A' : Type u} [Ring A] [Algebra R A]
  [Module.Finite R A] [Ring A'] [Algebra R A'] [Module.Finite R A'] {M : FGModuleCat.{u} A}
  {M' : FGModuleCat.{u} A'}

variable (M M') in
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm in
/-- **The Morita-Tachikawa correspondence on all modules.** If two generator-cogenerators `M` and
`M'`, of `mod A` and `mod A'`, have `R`-algebra isomorphic endomorphism rings, a Morita equivalence
between `A` and `A'` carries `M` to `M'`. -/
theorem exists_moritaEquivalence_functor_obj_iso_of_algEquiv_end
    (hM : IsGeneratorCogenerator M) (hM' : IsGeneratorCogenerator M')
    (e : Module.End A M.obj ≃ₐ[R] Module.End A' M'.obj) :
    ∃ F : MoritaEquivalence R A A', Nonempty (F.eqv.functor.obj M.obj ≅ M'.obj) := by
  obtain ⟨hs, hc⟩ := isGeneratorCogenerator_iff.1 hM
  obtain ⟨hs', hc'⟩ := isGeneratorCogenerator_iff.1 hM'
  have : Module.IsGenerator A M.obj := FGModuleCat.isGenerator_of_isSeparator hs
  have : Module.IsGenerator A' M'.obj := FGModuleCat.isGenerator_of_isSeparator hs'
  have := hc.injective_end R
  have := hc'.injective_end R
  let Y := (ModuleCat.restrictScalars e.toRingEquiv.toRingHom).obj
    (ModuleCat.of (Module.End A' M'.obj) M'.obj)
  -- `Y` is `M'` with scalars restricted along `e`, so it is still finitely generated, projective
  -- and injective. The identity of `M'` is `e.symm`-semilinear onto `Y`.
  have : Module.Finite (Module.End A M.obj) Y :=
    (e.toRingEquiv.toRingHom.finite_restrictScalars_iff e.toRingEquiv.surjective _).2 inferInstance
  have : Module.Projective (Module.End A M.obj) Y :=
    (e.toRingEquiv.projective_restrictScalars_iff _).2 inferInstance
  have : Module.Injective (Module.End A M.obj) Y :=
    Module.Injective.of_ringEquiv e.toRingEquiv.symm
      (e.toRingEquiv.restrictScalarsSemilinearEquiv (ModuleCat.of _ M'.obj)).symm
  -- Each of `M` and `Y` is a retract of a finite power of the other, over `Γ = Module.End A M`.
  obtain ⟨m, s, r, hrs⟩ := exists_comp_eq_id_pi_of_projective_of_injective
    (Γ := Module.End A M.obj) A M.obj Y
  obtain ⟨n, s', r', hrs'⟩ := e.toRingEquiv.toRingHom.exists_comp_eq_id_pi_restrictScalars
    (A := A') e.toRingEquiv.injective M'.obj M.obj
  obtain ⟨F, ⟨I⟩⟩ := exists_moritaEquivalence_moduleEnd_of_comp_eq_id R hrs hrs'
  -- `A ≅ Module.End Γ M` and `Module.End Γ Y ≅ A'`, by the double centralizer property.
  let α := algEquivEndEndOfIsGenerator A M.obj R
  let β := (e.toAlgHom.moduleEndRestrictScalarsAlgEquiv e.surjective M'.obj).trans
    (algEquivEndEndOfIsGenerator A' M'.obj R).symm
  have I₁ : (MoritaEquivalence.ofAlgEquiv α).eqv.functor.obj M.obj ≅ ModuleCat.of _ M.obj :=
    RingHom.restrictScalarsIsoOfAddEquiv _ (AddEquiv.refl _)
      fun φ x ↦ algEquivEndEndOfIsGenerator_symm_smul R φ x
  have I₂ : (MoritaEquivalence.ofAlgEquiv β).eqv.functor.obj
      (ModuleCat.of (Module.End (Module.End A M.obj) Y) Y) ≅ M'.obj :=
    RingHom.restrictScalarsIsoOfAddEquiv _ (AddEquiv.refl _)
      fun a y ↦ (AlgHom.moduleEndRestrictScalarsAlgEquiv_symm_apply e.toAlgHom e.surjective
        M'.obj _ y).trans (algEquivEndEndOfIsGenerator_apply (R := A') (M := M'.obj) R a y)
  exact ⟨(MoritaEquivalence.ofAlgEquiv α).trans R (F.trans R (MoritaEquivalence.ofAlgEquiv β)),
    ⟨(MoritaEquivalence.ofAlgEquiv β).eqv.functor.mapIso (F.eqv.functor.mapIso I₁ ≪≫ I) ≪≫ I₂⟩⟩

variable (M M') in
/-- **The Morita-Tachikawa correspondence, injectivity on marked pairs.** Let `M` and `M'` be
generator-cogenerators of `mod A` and `mod A'`, for Artin algebras `A` and `A'` over a commutative
Artinian ring `R`. If their endomorphism rings are isomorphic as `R`-algebras, an `R`-linear
equivalence of the categories `mod A` and `mod A'` carries `M` to `M'`. The `R`-algebra structure
on `Module.End A M.obj` comes from the action of `R` on `M` through `A`. -/
theorem exists_linear_equivalence_of_algEquiv_end (hM : IsGeneratorCogenerator M)
    (hM' : IsGeneratorCogenerator M') (e : Module.End A M.obj ≃ₐ[R] Module.End A' M'.obj) :
    ∃ F : FGModuleCat.{u} A ≌ FGModuleCat.{u} A', F.functor.Linear R ∧
      Nonempty (F.functor.obj M ≅ M') := by
  obtain ⟨F, ⟨I⟩⟩ := exists_moritaEquivalence_functor_obj_iso_of_algEquiv_end R M M' hM hM' e
  exact ⟨F.eqv.finiteModulesEquivalence, inferInstance,
    ⟨(ModuleCat.isFG A').fullyFaithfulι.preimageIso
      (eqToIso (F.eqv.finiteModulesEquivalence_functor_obj_obj M) ≪≫ I)⟩⟩

end Correspondence

end TauCeti
