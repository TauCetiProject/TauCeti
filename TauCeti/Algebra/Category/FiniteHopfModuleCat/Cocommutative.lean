/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FiniteHopfModuleCat.Trace
public import TauCeti.CategoryTheory.Monoidal.Pivotal.LeftDual

/-!
# The trivial-pivot spherical structure for cocommutative Hopf algebras

Let `H` be a cocommutative Hopf algebra over a field `k` (such as a group algebra `k[G]` or a
universal enveloping algebra `U(𝔤)`). Its antipode `S` satisfies `S² = id`
(`TauCeti.HopfAlgebra.antipode_antipode_of_isCocomm`), so the unit `1 : H` is a group-like element
implementing `S²` by conjugation. Specializing the generic Hopf-module pivotal and trace
constructions of `Pivotal.lean` and `Trace.lean` over `cocommRigidCategory k H` (from `Rigid.lean`)
therefore equips `FiniteHopfModuleCat k H` with:

* `trivialPivotalCategory k H`: the pivotal structure associated to the group-like pivot `1 : Hˣ`,
  whose components `M ≅ Mᘁᘁ` are the untwisted double-dual evaluation maps `m ↦ (φ ↦ φ m)`, and
  whose induced comparison `leftDualIsoRightDual M : ᘁM ≅ Mᘁ` is `leftDualIsoDual`;
* `trivialSphericalCategory k H`: sphericality of `trivialPivotalCategory k H`, with categorical
  trace equal to the `k`-linear trace and quantum dimension equal to `Module.finrank k M`.

Because a cocommutative Hopf algebra can admit other group-like central elements `g` implementing
`S² = id` (for instance central elements of `G` in `k[G]`), `trivialPivotalCategory` remains an
explicit definition installed locally via `letI`, matching `FiniteHopfModuleCat.pivotalCategory` and
`UqSl2.pivotalCategory`.

## Main declarations

* `TauCeti.FiniteHopfModuleCat.trivialPivotalCategory`: the pivotal structure given by `g = 1`.
* `TauCeti.FiniteHopfModuleCat.leftDualIsoRightDual_trivialPivotalCategory`: for the trivial pivot,
  `leftDualIsoRightDual M` is `leftDualIsoDual`.
* `TauCeti.FiniteHopfModuleCat.trivialSphericalCategory`: the trivial-pivot structure is spherical,
  with trace and quantum dimension computed by `trace_eq_smul_trivialSphericalCategory` and
  `quantumDim_eq_smul_trivialSphericalCategory`.

## References

* P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories*, Mathematical Surveys and
  Monographs 205, Sections 2.10 and 4.7.
* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Chapters III and XIV.
-/

public noncomputable section

open CategoryTheory MonoidalCategory ExactPairing

namespace TauCeti.FiniteHopfModuleCat

open BialgebraModule

universe u v

variable {k : Type u} [Field k] {H : Type v} [Ring H] [HopfAlgebra k H] [Coalgebra.IsCocomm k H]

variable (k H) in
/-- The trivial-pivot structure (`g = 1`) on finite-dimensional modules over a cocommutative Hopf
algebra, whose double-dual identification sends `m` to `φ ↦ φ m`. Not a global instance, because
other central group-like elements of `H` give distinct pivotal structures on the same category. -/
abbrev trivialPivotalCategory :
    letI := cocommRigidCategory k H
    PivotalCategory (FiniteHopfModuleCat k H) :=
  pivotalCategory (g := 1) (fun a => by simp) IsGroupLikeElem.one

/-- The components of `trivialPivotalCategory` are `unitEvalIso` for the unit `1 : Hˣ`. -/
theorem pivotalIsoApp_trivialPivotalCategory (M : FiniteHopfModuleCat k H) :
    letI := cocommRigidCategory k H
    letI := trivialPivotalCategory k H
    pivotalIsoApp M = unitEvalIso 1 (fun a => by simp) M :=
  pivotalIsoApp_pivotalCategory (fun a => by simp) IsGroupLikeElem.one M

/-- For `trivialPivotalCategory`, the pivotal isomorphism `M ≅ Mᘁᘁ` evaluates `m` against a
functional `φ` without twist: `(j_M m)(φ) = φ m`. -/
theorem dualEquiv_pivotalIsoApp_trivialPivotalCategory_hom_apply (M : FiniteHopfModuleCat k H)
    (m : M) (φ : (Mᘁ : FiniteHopfModuleCat k H)) :
    letI := cocommRigidCategory k H
    letI := trivialPivotalCategory k H
    dualEquiv k H (Mᘁ : FiniteHopfModuleCat k H) ((pivotalIsoApp M).hom.hom.hom m) φ =
      dualEquiv k H M φ m := by
  rw [pivotalIsoApp_trivialPivotalCategory, dualEquiv_unitEvalIso_hom_apply]
  simp

/-- For `trivialPivotalCategory`, the canonical pivotal identification `leftDualIsoRightDual M :
ᘁM ≅ Mᘁ` between the `S⁻¹`- and `S`-contragredients is `leftDualIsoDual`. -/
@[simp]
theorem leftDualIsoRightDual_trivialPivotalCategory (M : FiniteHopfModuleCat k H) :
    letI := cocommRigidCategory k H
    letI := trivialPivotalCategory k H
    leftDualIsoRightDual M = leftDualIsoDual HopfAlgebra.antipode_bijective_of_isCocomm M := by
  let := cocommRigidCategory k H
  let := trivialPivotalCategory k H
  ext : 1
  refine @leftDualHom_ext _ _ _ Mᘁ M (ᘁM) (pivotalExactPairing M) _ _ ?_
  rw [pivotalExactPairing_evaluation, whiskerLeft_leftDualIsoRightDual_hom_comp_evaluation]
  ext m φ
  simp only [hom_hom_comp, LinearMap.comp_apply, whiskerLeft_tmul, whiskerRight_tmul,
    evaluation_tmul, dualEquiv_pivotalIsoApp_trivialPivotalCategory_hom_apply,
    rigidCategory_evaluation]
  -- After unfolding `ᘁM` to `leftDual _ M`, `leftDualEvaluation_tmul` and
  -- `dualEquiv_leftDualIsoDual_hom_apply` identify both sides with `φ m`.
  exact (leftDualEvaluation_tmul HopfAlgebra.antipode_bijective_of_isCocomm M m φ).trans
    (congrArg (fun f : Module.Dual k M => (trivialEquiv k H).symm (f m))
      (dualEquiv_leftDualIsoDual_hom_apply HopfAlgebra.antipode_bijective_of_isCocomm M φ).symm)

/-- For `trivialPivotalCategory`, the right pivotal trace of an endomorphism `f` is its ordinary
`k`-linear trace. -/
theorem rightTrace_eq_smul_trivialPivotalCategory {M : FiniteHopfModuleCat k H} (f : M ⟶ M) :
    letI := cocommRigidCategory k H
    letI := trivialPivotalCategory k H
    rightTrace f =
      LinearMap.trace k M (f.hom.hom.restrictScalars k) • 𝟙 (𝟙_ (FiniteHopfModuleCat k H)) := by
  refine (rightTrace_eq_smul (fun a => by simp) IsGroupLikeElem.one f).trans ?_
  have hid : Algebra.lsmul k k M ((1 : Hˣ) : H) ∘ₗ f.hom.hom.restrictScalars k =
      f.hom.hom.restrictScalars k := by
    ext m
    simp
  rw [hid]

/-- For `trivialPivotalCategory`, the left pivotal trace of an endomorphism `f` is its ordinary
`k`-linear trace. -/
theorem leftTrace_eq_smul_trivialPivotalCategory {M : FiniteHopfModuleCat k H} (f : M ⟶ M) :
    letI := cocommRigidCategory k H
    letI := trivialPivotalCategory k H
    leftTrace f =
      LinearMap.trace k M (f.hom.hom.restrictScalars k) • 𝟙 (𝟙_ (FiniteHopfModuleCat k H)) := by
  refine (leftTrace_eq_smul (fun a => by simp) IsGroupLikeElem.one f).trans ?_
  have hid : Algebra.lsmul k k M (↑(1 : Hˣ)⁻¹ : H) ∘ₗ f.hom.hom.restrictScalars k =
      f.hom.hom.restrictScalars k := by
    ext m
    simp
  rw [hid]

variable (k H) in
/-- The trivial-pivot structure on finite-dimensional modules over a cocommutative Hopf algebra is
spherical: both pivotal traces equal the `k`-linear trace. -/
theorem trivialSphericalCategory :
    letI := cocommRigidCategory k H
    letI := trivialPivotalCategory k H
    SphericalCategory (FiniteHopfModuleCat k H) := by
  let := cocommRigidCategory k H
  let := trivialPivotalCategory k H
  exact ⟨fun f => by
    rw [leftTrace_eq_smul_trivialPivotalCategory, rightTrace_eq_smul_trivialPivotalCategory]⟩

/-- For `trivialSphericalCategory`, the categorical trace of `f` is its `k`-linear trace. -/
@[simp]
theorem trace_eq_smul_trivialSphericalCategory {M : FiniteHopfModuleCat k H} (f : M ⟶ M) :
    letI := cocommRigidCategory k H
    letI := trivialPivotalCategory k H
    haveI := trivialSphericalCategory k H
    trace f =
      LinearMap.trace k M (f.hom.hom.restrictScalars k) • 𝟙 (𝟙_ (FiniteHopfModuleCat k H)) := by
  let := cocommRigidCategory k H
  let := trivialPivotalCategory k H
  have := trivialSphericalCategory k H
  rw [trace_eq_rightTrace, rightTrace_eq_smul_trivialPivotalCategory]

/-- For `trivialSphericalCategory`, the quantum dimension of `M` is `Module.finrank k M`. -/
@[simp]
theorem quantumDim_eq_smul_trivialSphericalCategory (M : FiniteHopfModuleCat k H) :
    letI := cocommRigidCategory k H
    letI := trivialPivotalCategory k H
    haveI := trivialSphericalCategory k H
    quantumDim M = (Module.finrank k M : k) • 𝟙 (𝟙_ (FiniteHopfModuleCat k H)) := by
  let := cocommRigidCategory k H
  let := trivialPivotalCategory k H
  have := trivialSphericalCategory k H
  rw [← trace_id, trace_eq_smul_trivialSphericalCategory, hom_hom_id, LinearMap.restrictScalars_id,
    LinearMap.trace_id]

end TauCeti.FiniteHopfModuleCat
