/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Weights.Dimension
public import TauCeti.Algebra.Lie.Weights.Root.IntegralLattice

/-!
# The root--simple-coroot basis of an integral root--coroot lattice

For a base `b` of the root system, the integral root--coroot span of an `IsSl2System` has the
expected basis: one root vector for every nonzero root and one coroot for every member of
`b.support`. The index is therefore `H.root ⊕ b.support`. A Chevalley Lie lattice receives the
same basis through its canonical identification with the root--coroot span.

This is the coordinate source for reducing a Chevalley lattice modulo a prime: root coordinates
and simple-coroot coordinates remain named after scalar extension.

## Main declarations

* `TauCeti.IsSl2System.rootSimpleCorootBasis`: the corresponding basis of the root--coroot
  lattice, indexed by `H.root ⊕ b.support`.
* `TauCeti.IsChevalleySystem.rootSimpleCorootBasis`: the transported basis of the Chevalley Lie
  lattice.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §25.2.
* M. Geck, *Lie algebras and Chevalley groups*, Cambridge Studies in Advanced Mathematics 165,
  §4.1.
-/

public section

namespace TauCeti

open LieAlgebra LieAlgebra.IsKilling LieModule Module

universe u v

variable {K : Type u} {L : Type v} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [LieAlgebra.IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [LieModule.IsTriangularizable K H L]
  {ω : LieEquiv K L L} {x : Weight K H L → L}

namespace IsSl2System

variable (hx : IsSl2System x) (b : (rootSystem H).Base)

include hx

/-- The root vectors and simple coroots, as elements of the integral root--coroot span. -/
private noncomputable def rootSimpleCorootFamily :
    H.root ⊕ b.support → rootCorootSpan x
  | Sum.inl alpha =>
      ⟨x alpha, rootVector_mem_rootCorootSpan x alpha⟩
  | Sum.inr i =>
      ⟨(coroot (i : Weight K H L) : L), coroot_mem_rootCorootSpan x i⟩

omit hx in
@[simp] private theorem coe_rootSimpleCorootFamily_inl (alpha : H.root) :
    (rootSimpleCorootFamily (x := x) b (Sum.inl alpha) : L) = x alpha := by
  simp [rootSimpleCorootFamily]

omit hx in
@[simp] private theorem coe_rootSimpleCorootFamily_inr (i : b.support) :
    (rootSimpleCorootFamily (x := x) b (Sum.inr i) : L) =
      (coroot (i : Weight K H L) : L) := by
  simp [rootSimpleCorootFamily]

private theorem span_rootSimpleCorootFamily_eq_top :
    Submodule.span K (Set.range fun i : H.root ⊕ b.support =>
      (rootSimpleCorootFamily (x := x) b i : L)) = ⊤ := by
  apply top_unique
  rw [← hx.span_range_sup_toSubmodule_eq_top]
  apply sup_le
  · rw [Submodule.span_le]
    rintro _ ⟨alpha, rfl⟩
    by_cases halpha : alpha.IsNonZero
    · exact Submodule.subset_span ⟨Sum.inl ⟨alpha, by simpa⟩, rfl⟩
    · rw [hx.eq_zero_of_isZero alpha (not_not.mp halpha)]
      exact Submodule.zero_mem _
  · have hspan : Submodule.span K ((rootSystem H).coroot '' b.support) = ⊤ := by
      calc
        _ = (rootSystem H).corootSpan K := b.span_coroot_support
        _ = ⊤ := RootPairing.IsRootSystem.span_coroot_eq_top
    have hmapped := congrArg (Submodule.map H.incl.toLinearMap) hspan
    rw [Submodule.map_span, Submodule.map_top] at hmapped
    have hrange : H.incl.toLinearMap.range = H.toSubmodule := by
      ext y
      constructor
      · rintro ⟨h, rfl⟩
        exact h.property
      · intro hy
        exact ⟨⟨y, hy⟩, rfl⟩
    rw [hrange] at hmapped
    rw [← hmapped]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    let j : b.support := ⟨i, hi⟩
    refine ⟨Sum.inr j, ?_⟩
    have hj : (rootSimpleCorootFamily (x := x) b (Sum.inr j) : L) =
        H.incl ((rootSystem H).coroot i) := by
      rw [coe_rootSimpleCorootFamily_inr, rootSystem_coroot_apply]
      rfl
    exact hj.symm

private theorem linearIndependent_rootSimpleCorootFamily_ambient :
    LinearIndependent K (fun i : H.root ⊕ b.support =>
      (rootSimpleCorootFamily (x := x) b i : L)) :=
  linearIndependent_of_top_le_span_of_card_eq_finrank
    (by rw [hx.span_rootSimpleCorootFamily_eq_top b])
    (card_root_sum_support_eq_finrank H b)

private theorem span_rootSimpleCorootFamily_lattice_eq_top :
    Submodule.span ℤ (Set.range (rootSimpleCorootFamily (x := x) b)) = ⊤ := by
  let P := Submodule.span ℤ (Set.range (rootSimpleCorootFamily (x := x) b))
  let Q := P.map (rootCorootSpan x).subtype
  have hroot (alpha : Weight K H L) : x alpha ∈ Q := by
    by_cases halpha : alpha.IsNonZero
    · let a : H.root := ⟨alpha, by simpa⟩
      exact ⟨rootSimpleCorootFamily (x := x) b (Sum.inl a),
        Submodule.subset_span ⟨Sum.inl a, rfl⟩, rfl⟩
    · rw [hx.eq_zero_of_isZero alpha (not_not.mp halpha)]
      exact Submodule.zero_mem _
  have hcoroot (alpha : Weight K H L) : (coroot alpha : L) ∈ Q := by
    by_cases halpha : alpha.IsNonZero
    · let a : H.root := ⟨alpha, by simpa⟩
      have ha : (rootSystem H).coroot a ∈
          Submodule.span ℤ ((rootSystem H).coroot '' b.support) :=
        b.coroot_mem_span_int a
      let inclℤ : H →ₗ[ℤ] L := H.incl.restrictScalars ℤ
      have hmap : inclℤ ((rootSystem H).coroot a) ∈
          Submodule.map inclℤ
            (Submodule.span ℤ ((rootSystem H).coroot '' b.support)) :=
        ⟨(rootSystem H).coroot a, ha, rfl⟩
      rw [Submodule.map_span] at hmap
      have hle : Submodule.span ℤ
          (inclℤ '' ((rootSystem H).coroot '' b.support)) ≤ Q := by
        rw [Submodule.span_le]
        rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
        let j : b.support := ⟨i, hi⟩
        refine ⟨rootSimpleCorootFamily (x := x) b (Sum.inr j),
          Submodule.subset_span ⟨Sum.inr j, rfl⟩, ?_⟩
        have hj : (rootSimpleCorootFamily (x := x) b (Sum.inr j) : L) =
            H.incl ((rootSystem H).coroot i) := by
          rw [coe_rootSimpleCorootFamily_inr, rootSystem_coroot_apply]
          rfl
        exact hj
      have hm := hle hmap
      have ha_weight : (a : Weight K H L) = alpha := rfl
      have ha_coroot : inclℤ ((rootSystem H).coroot a) = (coroot alpha : L) := by
        dsimp only [inclℤ]
        rw [rootSystem_coroot_apply, ha_weight]
        rfl
      rw [ha_coroot] at hm
      exact hm
    · rw [coroot_eq_zero_iff.2 (not_not.mp halpha)]
      exact Submodule.zero_mem _
  have hspan : rootCorootSpan x ≤ Q := by
    rw [rootCorootSpan_le_iff]
    exact ⟨hroot, hcoroot⟩
  apply top_unique
  intro z _
  have hz : (z : L) ∈ Q := hspan z.property
  obtain ⟨w, hw, hwz⟩ := hz
  have : w = z := Subtype.ext hwz
  simpa [P, this] using hw

/-- The integral basis of the root--coroot span consisting of one root vector for every nonzero
root and the simple coroots belonging to `b`. -/
noncomputable def rootSimpleCorootBasis :
    Basis (H.root ⊕ b.support) ℤ (rootCorootSpan x) := by
  apply Basis.mk
  · apply LinearIndependent.of_comp (rootCorootSpan x).subtype
    exact (hx.linearIndependent_rootSimpleCorootFamily_ambient b).restrict_scalars' ℤ
  · rw [hx.span_rootSimpleCorootFamily_lattice_eq_top b]

@[simp] theorem coe_rootSimpleCorootBasis_inl (alpha : H.root) :
    (hx.rootSimpleCorootBasis b (Sum.inl alpha) : L) = x alpha := by
  rw [rootSimpleCorootBasis, Basis.mk_apply]
  exact coe_rootSimpleCorootFamily_inl (x := x) b alpha

@[simp] theorem coe_rootSimpleCorootBasis_inr (i : b.support) :
    (hx.rootSimpleCorootBasis b (Sum.inr i) : L) =
      (coroot (i : Weight K H L) : L) := by
  rw [rootSimpleCorootBasis, Basis.mk_apply]
  exact coe_rootSimpleCorootFamily_inr (x := x) b i

end IsSl2System

namespace IsChevalleySystem

variable (hx : IsChevalleySystem ω x) (b : (rootSystem H).Base)

/-- The root--simple-coroot basis of the Chevalley Lie lattice, transported from the canonical
basis of its underlying root--coroot span. -/
noncomputable def rootSimpleCorootBasis :
    Basis (H.root ⊕ b.support) ℤ hx.chevalleyLieLattice :=
  (hx.toIsSl2System.rootSimpleCorootBasis b).map
    (LinearEquiv.ofEq _ _ hx.chevalleyLieLattice_toSubmodule.symm)

@[simp] theorem coe_rootSimpleCorootBasis_inl (alpha : H.root) :
    (hx.rootSimpleCorootBasis b (Sum.inl alpha) : L) = x alpha := by
  rw [rootSimpleCorootBasis, Basis.map_apply]
  rw [LinearEquiv.coe_ofEq_apply]
  exact hx.toIsSl2System.coe_rootSimpleCorootBasis_inl b alpha

@[simp] theorem coe_rootSimpleCorootBasis_inr (i : b.support) :
    (hx.rootSimpleCorootBasis b (Sum.inr i) : L) =
      (coroot (i : Weight K H L) : L) := by
  rw [rootSimpleCorootBasis, Basis.map_apply]
  rw [LinearEquiv.coe_ofEq_apply]
  exact hx.toIsSl2System.coe_rootSimpleCorootBasis_inr b i

end IsChevalleySystem

end TauCeti
