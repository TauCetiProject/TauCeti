/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.Admissible
public import TauCeti.RepresentationTheory.Smooth.Averaging
public import TauCeti.RepresentationTheory.Smooth.Dual.Basic
import TauCeti.RepresentationTheory.Dual

/-!
# Fixed vectors of the smooth dual and smooth biduality

For a compact open subgroup `U` of invertible pro-order, restriction identifies the
`U`-fixed smooth functionals with the algebraic dual of `Vᵁ`. The inverse extends a
functional by precomposing with the averaging projector. Applying this identification twice
turns smooth bidual evaluation on `U`-fixed vectors into ordinary bidual evaluation on `Vᵁ`.

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

/-- Restriction identifies the `U`-fixed vectors of the smooth dual with the dual of the
`U`-fixed vectors. Its inverse extends a functional by averaging its argument over `U`. -/
noncomputable def smoothDualInvariantsEquiv :
    invariants (V := ρ.dual.smoothVectors.toSubmodule)
        (ρ.smoothDual.comp U.toSubgroup.subtype) ≃ₗ[A]
      Dual A (invariants (ρ.comp U.toSubgroup.subtype)) := by
  let σ : Representation A U V := ρ.comp U.toSubgroup.subtype
  letI : IsSmooth σ := IsSmooth.comp (ρ := ρ) continuous_subtypeVal
  let p := (σ.isProj_smoothAverage hU).codRestrict
  refine
    { toFun := fun f ↦ σ.invariants.dualRestrict f.val
      invFun := fun l ↦ ?_
      left_inv := ?_
      right_inv := ?_
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  · have hfix : l.comp p ∈ σ.dual.invariants :=
      TauCeti.Representation.mem_invariants_dual_iff.mpr fun u v ↦
        congrArg l (Subtype.ext (σ.smoothAverage_apply_apply hU u v))
    have hs := (mem_smoothVectors_iff_exists_openSubgroup_mem_invariants (ρ := ρ.dual)).mpr
      ⟨U, dual_comp ρ U.toSubgroup.subtype ▸ hfix⟩
    exact ⟨⟨l.comp p, hs⟩, fun u ↦ Subtype.ext (hfix u)⟩
  · intro f
    refine Subtype.ext <| Subtype.ext <| LinearMap.ext fun v ↦ ?_
    have hfix : f.val.val ∈ σ.dual.invariants := fun u ↦ congrArg Subtype.val (f.property u)
    exact σ.map_smoothAverage_of_forall_apply_eq hU f.val.val
      (fun u ↦ TauCeti.Representation.apply_of_mem_invariants_dual hfix u v)
  · intro l
    exact LinearMap.ext fun v ↦ congrArg l ((σ.isProj_smoothAverage hU).codRestrict_apply_cod v)

@[simp]
theorem smoothDualInvariantsEquiv_apply
    (f : invariants (V := ρ.dual.smoothVectors.toSubmodule)
      (ρ.smoothDual.comp U.toSubgroup.subtype))
    (v : invariants (ρ.comp U.toSubgroup.subtype)) :
    ρ.smoothDualInvariantsEquiv U hU f v = f.val.val v :=
  (rfl)

@[simp]
theorem smoothDualInvariantsEquiv_symm_apply (l : Dual A (invariants (ρ.comp U.toSubgroup.subtype)))
    (v : V) :
    ((ρ.smoothDualInvariantsEquiv U hU).symm l).val.val v =
      l ((isProj_smoothAverage (ρ.comp U.toSubgroup.subtype) hU).codRestrict v) :=
  (rfl)

/-- The fixed vectors in the smooth bidual identify with the algebraic bidual of the fixed
vectors. Under this equivalence the two evaluation maps agree. -/
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
      b.val.val ((ρ.smoothDualInvariantsEquiv U hU).symm l) :=
  (rfl)

/-- On fixed vectors, smooth bidual evaluation agrees with algebraic bidual evaluation. -/
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

/-- At a compact open subgroup of invertible pro-order, smooth bidual evaluation is surjective
on fixed vectors exactly when the fixed space is finite-dimensional. -/
theorem smoothDualEval_invariantsMap_surjective_iff (U : OpenSubgroup G) [CompactSpace U]
    (hU : TauCeti.HasUnitProOrder k U) :
    Function.Surjective ((ρ.smoothDualEval.res U.toSubgroup.subtype).invariantsMap
      (W := ρ.smoothDual.dual.smoothVectors.toSubmodule)) ↔
      FiniteDimensional k (invariants (ρ.comp U.toSubgroup.subtype)) := by
  let W := invariants (ρ.comp U.toSubgroup.subtype)
  have he : ⇑(ρ.smoothBidualInvariantsEquiv U hU).toEquiv ∘
      ⇑(ρ.smoothDualEval.res U.toSubgroup.subtype).invariantsMap = Dual.eval k W :=
    funext (ρ.smoothBidualInvariantsEquiv_eval U hU)
  rw [← (ρ.smoothBidualInvariantsEquiv U hU).toEquiv.comp_surjective, he]
  refine ⟨fun hs ↦ ?_, fun _ ↦ (bijective_dual_eval k W).2⟩
  let _ : IsReflexive k W := ⟨eval_apply_injective k, hs⟩
  exact instFiniteDimensionalOfIsReflexive k W

/-- The smooth dual separates points if compact open subgroups of invertible pro-order
form a neighbourhood basis of the identity. -/
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
