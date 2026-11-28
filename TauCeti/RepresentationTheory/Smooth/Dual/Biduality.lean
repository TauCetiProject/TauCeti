/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.Admissible
public import TauCeti.RepresentationTheory.Smooth.Averaging
public import TauCeti.RepresentationTheory.Smooth.Dual.Basic
import TauCeti.LinearAlgebra.Dual.DoubleDual
import TauCeti.RepresentationTheory.Dual

/-!
# Fixed vectors of the smooth dual and smooth biduality

For a smooth representation and a compact open subgroup `U` of invertible pro-order,
restriction identifies the `U`-fixed smooth functionals with the algebraic dual of `Vᵁ`.
The inverse extends a functional by precomposing with the averaging projector. Applying this
identification twice turns smooth bidual evaluation on `U`-fixed vectors into ordinary bidual
evaluation on `Vᵁ`.

Over a field, when such subgroups form a neighbourhood basis, the smooth dual separates
points and evaluation into the smooth bidual is bijective exactly for admissible representations.

## References

* J. Bernstein, *Representations of p-adic groups*, Chapter I, §2.2, Propositions 6–7.
* C. J. Bushnell and G. Henniart, *The local Langlands conjecture for GL(2)*, §§2.8–2.9.
-/

public section

open Module

namespace Representation

variable {A G V : Type*} [CommRing A] [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  [AddCommGroup V] [Module A V] (ρ : Representation A G V) [IsSmooth ρ]

section Invariants

variable (U : OpenSubgroup G) [CompactSpace U] (hU : TauCeti.HasUnitProOrder A U)

omit [IsSmooth ρ] [CompactSpace U] in
private theorem mem_smoothDual_comp_invariants_iff (f : ρ.dual.smoothVectors.toSubmodule) :
    f ∈ invariants (ρ.smoothDual.comp U.toSubgroup.subtype) ↔
      f.val ∈ (dual (ρ.comp U.toSubgroup.subtype)).invariants := by
  rw [dual_comp]
  constructor
  · intro hf u
    simpa only [MonoidHom.comp_apply, smoothDual, Subrepresentation.coe_toRepresentation_apply]
      using congrArg Subtype.val (hf u)
  · intro hf u
    apply Subtype.ext
    simpa only [MonoidHom.comp_apply, smoothDual, Subrepresentation.coe_toRepresentation_apply]
      using hf u

/-- For a smooth representation, restriction identifies the `U`-fixed vectors of the smooth dual
with the dual of the `U`-fixed vectors. Its inverse extends a functional by averaging its argument
over `U`. -/
noncomputable def smoothDualInvariantsEquiv :
    invariants (V := ρ.dual.smoothVectors.toSubmodule)
        (ρ.smoothDual.comp U.toSubgroup.subtype) ≃ₗ[A]
      Dual A (invariants (ρ.comp U.toSubgroup.subtype)) := by
  let σ : Representation A U V := ρ.comp U.toSubgroup.subtype
  letI : IsSmooth σ := IsSmooth.comp (ρ := ρ) continuous_subtypeVal
  let e : invariants (ρ.smoothDual.comp U.toSubgroup.subtype) ≃ₗ[A] σ.dual.invariants :=
    { toFun := fun f ↦ ⟨f.val.val, (ρ.mem_smoothDual_comp_invariants_iff U f.val).mp f.property⟩
      invFun := fun f ↦
        let hs := (mem_smoothVectors_iff_exists_openSubgroup_mem_invariants (ρ := ρ.dual)).mpr
          ⟨U, dual_comp ρ U.toSubgroup.subtype ▸ f.property⟩
        ⟨⟨f.val, hs⟩, (ρ.mem_smoothDual_comp_invariants_iff U _).mpr f.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  exact e ≪≫ₗ σ.dualInvariantsEquivOfProjection (σ.isProj_smoothAverage hU)
    (σ.smoothAverage_apply_apply hU) fun f hf v ↦
      σ.map_smoothAverage_of_forall_apply_eq hU f
        (fun u ↦ TauCeti.Representation.apply_of_mem_invariants_dual hf u v)

@[simp]
theorem smoothDualInvariantsEquiv_apply
    (f : invariants (V := ρ.dual.smoothVectors.toSubmodule)
      (ρ.smoothDual.comp U.toSubgroup.subtype))
    (v : invariants (ρ.comp U.toSubgroup.subtype)) :
    ρ.smoothDualInvariantsEquiv U hU f v = f.val.val v := by
  simp [smoothDualInvariantsEquiv]

@[simp]
theorem smoothDualInvariantsEquiv_symm_apply (l : Dual A (invariants (ρ.comp U.toSubgroup.subtype)))
    (v : V) :
    ((ρ.smoothDualInvariantsEquiv U hU).symm l).val.val v =
      l ((isProj_smoothAverage (ρ.comp U.toSubgroup.subtype) hU).codRestrict v) := by
  simp [smoothDualInvariantsEquiv]

/-- For a smooth representation, the fixed vectors in the smooth bidual identify with the
algebraic bidual of the fixed vectors. Under this equivalence the two evaluation maps agree. -/
noncomputable def smoothBidualInvariantsEquiv :
    invariants (V := ρ.smoothDual.dual.smoothVectors.toSubmodule)
        (ρ.smoothDual.smoothDual.comp U.toSubgroup.subtype) ≃ₗ[A]
      Dual A (Dual A (invariants (ρ.comp U.toSubgroup.subtype))) :=
  smoothDualInvariantsEquiv (V := ρ.dual.smoothVectors.toSubmodule) ρ.smoothDual U hU ≪≫ₗ
    (ρ.smoothDualInvariantsEquiv U hU).symm.dualMap

@[simp]
theorem smoothBidualInvariantsEquiv_apply
    (b : invariants (V := ρ.smoothDual.dual.smoothVectors.toSubmodule)
      (ρ.smoothDual.smoothDual.comp U.toSubgroup.subtype))
    (l : Dual A (invariants (ρ.comp U.toSubgroup.subtype))) :
    ρ.smoothBidualInvariantsEquiv U hU b l =
      b.val.val ((ρ.smoothDualInvariantsEquiv U hU).symm l) := by
  simp only [smoothBidualInvariantsEquiv, LinearEquiv.trans_apply, LinearEquiv.dualMap_apply,
    smoothDualInvariantsEquiv_apply]

/-- The inverse bidual comparison evaluates a smooth functional after averaging it over `U`
and restricting it to the fixed vectors. -/
@[simp]
theorem smoothBidualInvariantsEquiv_symm_apply
    (b : Dual A (Dual A (invariants (ρ.comp U.toSubgroup.subtype))))
    (f : ρ.dual.smoothVectors.toSubmodule) :
    letI := IsSmooth.comp (ρ := ρ.smoothDual) (φ := U.toSubgroup.subtype) continuous_subtypeVal
    ((ρ.smoothBidualInvariantsEquiv U hU).symm b).val.val f =
      b (ρ.smoothDualInvariantsEquiv U hU
        ((isProj_smoothAverage (ρ.smoothDual.comp U.toSubgroup.subtype) hU).codRestrict f)) := by
  simp only [smoothBidualInvariantsEquiv, LinearEquiv.symm_trans_apply, LinearEquiv.dualMap_symm,
    LinearEquiv.symm_symm, smoothDualInvariantsEquiv_symm_apply, LinearEquiv.dualMap_apply]

/-- For a smooth representation, smooth bidual evaluation agrees with algebraic bidual evaluation
on the fixed vectors. -/
@[simp]
theorem smoothBidualInvariantsEquiv_eval (v : invariants (ρ.comp U.toSubgroup.subtype)) :
    ρ.smoothBidualInvariantsEquiv U hU
      ((ρ.smoothDualEval.res U.toSubgroup.subtype).invariantsMap v) = Dual.eval A _ v := by
  ext l
  simp

end Invariants

section Field

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] (ρ : Representation k G V)
  [IsSmooth ρ]

/-- For a smooth representation over a field, smooth bidual evaluation is surjective on the fixed
vectors of a compact open subgroup of invertible pro-order exactly when that fixed space is
finite-dimensional. As in `Representation.smoothDualEval_surjective_iff`, this uses
`Module.instFiniteDimensionalOfIsReflexive` for the converse after comparison with algebraic
bidual evaluation. -/
theorem smoothDualEval_invariantsMap_surjective_iff (U : OpenSubgroup G) [CompactSpace U]
    (hU : TauCeti.HasUnitProOrder k U) :
    Function.Surjective ((ρ.smoothDualEval.res U.toSubgroup.subtype).invariantsMap
      (W := ρ.smoothDual.dual.smoothVectors.toSubmodule)) ↔
      FiniteDimensional k (invariants (ρ.comp U.toSubgroup.subtype)) := by
  let W := invariants (ρ.comp U.toSubgroup.subtype)
  have he : ⇑(ρ.smoothBidualInvariantsEquiv U hU) ∘
      ⇑(ρ.smoothDualEval.res U.toSubgroup.subtype).invariantsMap = Dual.eval k W :=
    funext (ρ.smoothBidualInvariantsEquiv_eval U hU)
  rw [← EquivLike.comp_surjective _ (ρ.smoothBidualInvariantsEquiv U hU), he,
    TauCeti.Module.Dual.surjective_eval_iff_finiteDimensional]

/-- For a smooth representation over a field, the smooth dual separates points if compact open
subgroups of invertible pro-order form a neighbourhood basis of the identity. -/
theorem smoothDualEval_injective (hG : TauCeti.HasCofinalUnitProOrder k G) :
    Function.Injective ρ.smoothDualEval := by
  apply (injective_iff_map_eq_zero ρ.smoothDualEval.toLinearMap).2
  intro v hv
  obtain ⟨U, hUc, hU, hfix⟩ := hG.exists_openSubgroup_subset
    ((IsSmooth.isOpen_stabilizer (ρ := ρ) v).mem_nhds (ρ.stabilizer v).one_mem)
  let _ : CompactSpace U := isCompact_iff_compactSpace.mp hUc
  let w : invariants (ρ.comp U.toSubgroup.subtype) := ⟨v, mem_invariants_comp_subtype_iff.mpr hfix⟩
  have hz : (ρ.smoothDualEval.res U.toSubgroup.subtype).invariantsMap
      (W := ρ.smoothDual.dual.smoothVectors.toSubmodule) w = 0 := by
    apply Subtype.ext
    simpa [w] using hv
  have h := ρ.smoothBidualInvariantsEquiv_eval U hU w
  rw [hz, map_zero, ← (Dual.eval k _).map_zero] at h
  exact congrArg Subtype.val (eval_apply_injective k h.symm)

/-- A smooth representation over a field is isomorphic to its smooth bidual by evaluation
exactly when it is admissible, provided the compact open subgroups of invertible pro-order
form a neighbourhood basis. -/
theorem smoothDualEval_bijective_iff_isAdmissible (hG : TauCeti.HasCofinalUnitProOrder k G) :
    Function.Bijective ρ.smoothDualEval ↔ IsAdmissible ρ := by
  constructor
  · intro h
    apply IsAdmissible.of_hasBasis (U := fun U : OpenSubgroup G ↦ U.toSubgroup) hG.hasBasis_nhds_one
    rintro U ⟨hUc, hU⟩
    let _ : CompactSpace U := isCompact_iff_compactSpace.mp hUc
    apply (ρ.smoothDualEval_invariantsMap_surjective_iff U hU).1
    have : IsSmooth (ρ.comp U.toSubgroup.subtype) := IsSmooth.comp (ρ := ρ) continuous_subtypeVal
    apply IntertwiningMap.invariantsMap_surjective hU
    simpa using h.2
  · intro h
    refine ⟨ρ.smoothDualEval_injective hG, fun l ↦ ?_⟩
    obtain ⟨U, hUc, hU, hfix⟩ := hG.exists_openSubgroup_subset
      ((IsSmooth.isOpen_stabilizer (ρ := ρ.smoothDual.smoothDual) l).mem_nhds (Subgroup.one_mem _))
    let _ : CompactSpace U := isCompact_iff_compactSpace.mp hUc
    have hs := (ρ.smoothDualEval_invariantsMap_surjective_iff U hU).2 (h.finite_invariants U hUc)
    obtain ⟨v, hv⟩ := hs ⟨l, mem_invariants_comp_subtype_iff.mpr hfix⟩
    exact ⟨v.val, by simpa using congrArg Subtype.val hv⟩

end Field

end Representation
