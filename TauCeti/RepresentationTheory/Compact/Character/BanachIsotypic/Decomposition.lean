/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.Character.BanachIsotypic.GFinite
import TauCeti.Algebra.DirectSum.Internal
import TauCeti.RepresentationTheory.AsModule
import TauCeti.RepresentationTheory.Compact.Semisimple
import TauCeti.RepresentationTheory.Continuous.Intertwining
import TauCeti.RepresentationTheory.Continuous.Transport
import TauCeti.RepresentationTheory.Irreducible
import TauCeti.RepresentationTheory.Subrepresentation

/-!
# The `G`-finite vectors are the algebraic sum of the isotypic parts

Let `π` be a strongly continuous representation of a compact group `G` on a Banach space `V` over
an algebraically closed `RCLike` field `k` (so `k = ℂ`), and fix a skeleton `models` of the unitary
dual of `G`. The isotypic parts `V(σ)`, the ranges of the isotypic projectors `e_σ`
(`ContRepresentation.banachIsotypicRange`), are independent and consist of `G`-finite vectors
(`ContRepresentation.iSupIndep_banachIsotypicRange_of_isIrrepSkeleton`,
`ContRepresentation.iSup_banachIsotypicRange_le_gFiniteSubmodule`). This file proves the converse
inclusion, so the `G`-finite vectors are the algebraic direct sum `⊕_σ V(σ)`.

A `G`-finite vector `v` lies in a finite-dimensional subrepresentation `S`. The restriction of `π`
to `S` is continuous, hence semisimple, so `v` is a finite sum of vectors of irreducible
subrepresentations `τ ≤ S`. Every such `τ` is equivalent to a member `σ` of the skeleton
(`TauCeti.IsIrrepSkeleton.exists_nonempty_equiv`), and the isotypic projector of `S` for `σ` fixes
`τ`; on `S` it is the restriction of `e_σ`, so the vectors of `τ` lie in `V(σ)`.

## Main results

* `ContRepresentation.gFiniteSubmodule_le_iSup_banachIsotypicRange`: every `G`-finite vector lies
  in the sum of the isotypic parts.
* `ContRepresentation.iSup_banachIsotypicRange_eq_gFiniteSubmodule`: the sum of the isotypic parts
  is the space of `G`-finite vectors.
* `ContRepresentation.isInternal_banachIsotypicRange`: the `G`-finite vectors are the internal
  direct sum of the isotypic parts.

## References

* J. Bernstein, B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, §4.1.
-/

public section

noncomputable section

open MeasureTheory TauCeti
open scoped MonoidAlgebra

namespace ContRepresentation

variable {k G V : Type*} [RCLike k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup V] [NormedSpace k V] [NormedSpace ℝ V] [SMulCommClass ℝ k V]

variable [CompleteSpace V] (π : ContRepresentation k G V) (hπ : ∀ v, Continuous fun g ↦ π g v)

variable [IsAlgClosed k]

/-- On a finite-dimensional subrepresentation `S`, the vectors of an irreducible subrepresentation
`τ` of the restriction of `π` to `S` lie in the isotypic part of the member of a skeleton that is
equivalent to `τ`. -/
private theorem exists_coe_mem_banachIsotypicRange {ι : Type*} {models : ι → IrrepModel k G}
    (h : IsIrrepSkeleton models) (S : Subrepresentation π.toRepresentation)
    [FiniteDimensional k S.toSubmodule]
    {τ : Subrepresentation (π.subrepresentation S.toSubmodule
      fun g _ hu ↦ S.apply_mem_toSubmodule g hu).toRepresentation} (hτ : IsAtom τ) :
    ∃ i, ∀ x ∈ τ.toSubmodule,
      ((x : S.toSubmodule) : V) ∈ banachIsotypicRange π hπ (models i).rep
        (models i).continuous_rep := by
  have hρ : Continuous (π.subrepresentation S.toSubmodule
      fun g _ hu ↦ S.apply_mem_toSubmodule g hu) :=
    continuous_subrepresentation_of_finiteDimensional hπ
  set ρτ := (π.subrepresentation S.toSubmodule
      fun g _ hu ↦ S.apply_mem_toSubmodule g hu).subrepresentation τ.toSubmodule
    fun g _ hv ↦ τ.apply_mem_toSubmodule g hv
  have hρτ : ρτ.toRepresentation = τ.toRepresentation :=
    τ.toRepresentation_subrepresentation_toSubmodule
  have hirr : ρτ.toRepresentation.IsIrreducible := by
    rw [hρτ]
    exact Representation.isIrreducible_toRepresentation_of_isAtom hτ
  obtain ⟨i, ⟨φ⟩⟩ := h.exists_nonempty_equiv ρτ (continuous_subrepresentation hρ) hirr
  obtain ⟨ψ⟩ := ContRepresentation.nonempty_equiv_iff.mp ⟨φ⟩
  rw [hρτ] at ψ
  have e : Nonempty (τ.asSubmodule ≃ₗ[k[G]] (models i).rep.toRepresentation.asModule) :=
    ⟨τ.asModuleEquivAsSubmodule.symm.trans (Representation.asModuleLinearEquivOfEquiv ψ)⟩
  refine ⟨i, fun x hx ↦ (mem_banachIsotypicRange_iff_apply_eq_self π hπ _ _
    (models i).isIrreducible).2 ?_⟩
  rw [banachIsotypicProjector_apply_of_mem π hπ _ _ S x.property]
  exact congrArg Subtype.val (isotypicProjector_apply_subtype_of_equiv _ hρ (models i).rep
    (models i).continuous_rep hτ e ⟨x, hx⟩)

/-- **Every `G`-finite vector lies in the sum of the isotypic parts** of a skeleton. -/
theorem gFiniteSubmodule_le_iSup_banachIsotypicRange {ι : Type*} {models : ι → IrrepModel k G}
    (h : IsIrrepSkeleton models) :
    π.toRepresentation.gFiniteSubmodule ≤
      ⨆ i, banachIsotypicRange π hπ (models i).rep (models i).continuous_rep := by
  intro v hv
  obtain ⟨S, hS, hvS⟩ := (Representation.isGFinite_iff_exists_subrepresentation _ v).1
    ((Representation.mem_gFiniteSubmodule _).1 hv)
  set ρ := π.subrepresentation S.toSubmodule fun g _ hu ↦ S.apply_mem_toSubmodule g hu
  have hρ : Continuous ρ := continuous_subrepresentation_of_finiteDimensional hπ
  have : IsSemisimpleModule k[G] ρ.toRepresentation.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mp
      (ρ.isSemisimpleRepresentation_of_continuous hρ)
  -- Write `v` as a sum of vectors of simple submodules of the restriction to `S`.
  have hmem : ρ.toRepresentation.asModuleEquiv.symm ⟨v, hvS⟩ ∈
      sSup {m : Submodule k[G] ρ.toRepresentation.asModule | IsSimpleModule k[G] m} := by
    rw [IsSemisimpleModule.sSup_simples_eq_top]
    exact Submodule.mem_top
  rw [sSup_eq_iSup'] at hmem
  have key := Submodule.iSup_induction _
    (motive := fun x ↦ ((ρ.toRepresentation.asModuleEquiv x : S.toSubmodule) : V) ∈
      ⨆ i, banachIsotypicRange π hπ (models i).rep (models i).continuous_rep) hmem
    (fun m x hx ↦ ?_) (by rw [map_zero]; exact zero_mem _)
    (fun x y hx hy ↦ by rw [map_add, Submodule.coe_add]; exact add_mem hx hy)
  · exact key
  · obtain ⟨i, hi⟩ := exists_coe_mem_banachIsotypicRange π hπ h S
      (τ := Subrepresentation.ofSubmodule' m.val)
      (Subrepresentation.isSimpleModule_asSubmodule_iff.mp m.property)
    exact Submodule.mem_iSup_of_mem i (hi _ hx)

/-- **The sum of the isotypic parts of a skeleton is the space of `G`-finite vectors.** -/
theorem iSup_banachIsotypicRange_eq_gFiniteSubmodule {ι : Type*} {models : ι → IrrepModel k G}
    (h : IsIrrepSkeleton models) :
    ⨆ i, banachIsotypicRange π hπ (models i).rep (models i).continuous_rep =
      π.toRepresentation.gFiniteSubmodule :=
  le_antisymm (iSup_banachIsotypicRange_le_gFiniteSubmodule π hπ models)
    (gFiniteSubmodule_le_iSup_banachIsotypicRange π hπ h)

/-- **The `G`-finite vectors are the algebraic direct sum `⊕_σ V(σ)`** of the isotypic parts of a
skeleton: the isotypic parts, viewed inside the `G`-finite vectors, form an internal direct sum. -/
theorem isInternal_banachIsotypicRange {ι : Type*} [DecidableEq ι] {models : ι → IrrepModel k G}
    (h : IsIrrepSkeleton models) :
    DirectSum.IsInternal fun i ↦ (banachIsotypicRange π hπ (models i).rep
      (models i).continuous_rep).comap π.toRepresentation.gFiniteSubmodule.subtype :=
  DirectSum.isInternal_submodule_comap_subtype
    (iSupIndep_banachIsotypicRange_of_isIrrepSkeleton π hπ h)
    (iSup_banachIsotypicRange_eq_gFiniteSubmodule π hπ h)

end ContRepresentation
