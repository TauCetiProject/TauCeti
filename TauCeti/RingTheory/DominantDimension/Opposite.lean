/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Artinian.Defs
public import TauCeti.RingTheory.DominantDimension.Basic

import Mathlib.Algebra.Category.ModuleCat.Algebra
import TauCeti.RingTheory.Finiteness.Faithful
import TauCeti.RingTheory.MatlisDuality.ArtinAlgebra
import TauCeti.RingTheory.Morita.DominantDimension

/-!
# Positive dominant dimension of an Artin algebra

The regular left module of an Artin algebra embeds into a projective-injective module if and only
if the regular right module does. An embedding on the left provides a faithful finitely generated
projective-injective module. Its Matlis dual is again faithful and projective-injective, and a
finite power of this dual contains the regular right module.

This is the first-term case of left–right symmetry for dominant dimension. It is the
left–right symmetry of the QF-3 condition for Artin algebras.

## References

* K. Morita, *Noetherian QF-3 rings and two-sided quasi-Frobenius maximal quotient rings*,
  Proc. Japan Acad. 46 (1970), 837–840, Theorem 1. The proof here uses the Matlis dual of a
  finitely generated projective-injective module in place of the character module.
* M. Hoshino, *On dominant dimension of Noetherian rings*, Osaka J. Math. 26 (1989),
  275–280, Theorem (the case `n = 1`).
* B. J. Müller, *The classification of algebras by dominant dimension*, Canad. J. Math. 20
  (1968), 398–409, §3, p. 400 (the faithful projective-injective module characterization).
-/

public section

open CategoryTheory MulOpposite
open scoped ModuleCat.Algebra

namespace TauCeti

universe u v

variable (R : Type u) [CommRing R] [IsArtinianRing R]
  (A : Type v) [Ring A] [Algebra R A] [Module.Finite R A]

include R in
private theorem one_le_dominantDimension_op (h : 1 ≤ dominantDimension A) :
    1 ≤ dominantDimension Aᵐᵒᵖ := by
  rw [← Nat.cast_one, natCast_le_dominantDimension_iff, ObjectProperty.isSyzygy_one_iff] at h
  obtain ⟨P, f, hf, hfin, hp, hi⟩ := h
  have hf' : Function.Injective f.hom := (ModuleCat.mono_iff_injective f).1 hf
  have hP : FaithfulSMul A P := FaithfulSMul.of_injective f.hom hf'
  obtain ⟨E, _, _, ι, hι, -⟩ := exists_isInjectiveEnvelope_quotient_jacobson.{u, u} R
  have := hι.moduleInjective
  have : Module.Projective A P := (IsProjective.iff_projective P).2 hp
  have : Module.Injective A P := Module.injective_module_of_injective_object A P
  let D := MatlisDual R E P
  have : Module.Finite R P := .trans A P
  have : Module.Finite R D := hι.finite_matlisDual P
  have : FaithfulSMul Aᵐᵒᵖ D := (MatlisDual.faithfulSMul_op_iff
    (MatlisDual.injective_evalₗ (N := P)
      (nontrivial_linearMap_of_isMaximal hι.length_quotient_linearMap_eq_one))).2 hP
  have : Module.Projective Aᵐᵒᵖ D := hι.moduleProjective_op_matlisDual_of_injective
  have : Module.Injective Aᵐᵒᵖ D := hι.moduleInjective_op_matlisDual_iff_projective.2 ‹_›
  obtain ⟨n, g, hg⟩ := exists_injective_pi_of_faithfulSMul R Aᵐᵒᵖ D
  -- The finite power can be placed in the universe of the regular module.
  have : Module.Finite Aᵐᵒᵖ D := .of_restrictScalars_finite R Aᵐᵒᵖ D
  have : Small.{v} (Fin n → D) := Module.Finite.small Aᵐᵒᵖ _
  let e := (Shrink.linearEquiv.{v} Aᵐᵒᵖ (Fin n → D)).symm
  have : Module.Injective Aᵐᵒᵖ (Shrink.{v} (Fin n → D)) :=
    (Module.Baer.of_equiv e (Module.Baer.of_injective inferInstance)).injective
  let g' := ModuleCat.ofHom (e.toLinearMap ∘ₗ g)
  rw [dominantDimension_eq_dominantDimension_of]
  exact CategoryTheory.one_le_dominantDimension_iff.2
    ⟨_, g', (ModuleCat.mono_iff_injective g').2 (e.injective.comp hg),
      (IsProjective.iff_projective _).1 (.of_equiv' e),
      Module.injective_object_of_injective_module _ _⟩

include R in
/-- An Artin algebra has positive right dominant dimension exactly when it has positive
left dominant dimension. -/
theorem one_le_dominantDimension_mulOpposite_iff :
    1 ≤ dominantDimension Aᵐᵒᵖ ↔ 1 ≤ dominantDimension A := by
  refine ⟨fun h ↦ ?_, one_le_dominantDimension_op R A⟩
  rw [(RingEquiv.opOp A).dominantDimension_eq]
  exact one_le_dominantDimension_op R Aᵐᵒᵖ h

end TauCeti
