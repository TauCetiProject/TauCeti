/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Continuous.IntegralModel.Basic
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Integral models of subrepresentations and quotients

An integral model induces integral models on every invariant vector subspace and on its
quotient. The former is the intersection with the original lattice; the latter is its image
in the quotient vector space. The quotient of the original lattice by this intersection
identifies with the quotient lattice, not merely with a finite-index submodule of it.

The restriction requires a Noetherian coefficient domain with the given fraction field;
the quotient image is a lattice without a Noetherian hypothesis. These constructions apply
in particular to discrete valuation rings and do not require compactness of the acting group.

## References

* H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, §2.1.
* J.-P. Serre, *Abelian ℓ-adic Representations and Elliptic Curves*, Chapter I, §1.
-/

public section

namespace TauCeti.GaloisLattice.IntegralModel

variable {Γ : Type*} [Monoid Γ] [TopologicalSpace Γ] {O : Type*} [CommRing O]

section Subspace

variable {E : Type*} [Field E] [Algebra O E]
  {V : Type*} [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]
  [TopologicalSpace V] {ρ : ContinuousRep Γ E V}
  (Λ : IntegralModel O ρ) (W : Submodule E V) (hW : ∀ g, ∀ x ∈ W, ρ g x ∈ W)

/-- The integral model on an invariant subspace obtained by intersecting it with `Λ`. -/
def submodel [IsFractionRing O E] [IsNoetherianRing O] :
    IntegralModel O (ρ.subrepresentation W hW) where
  lattice := Λ.lattice.comap (W.subtype.restrictScalars O)
  isLattice := Λ.lattice.isLattice_comap W.subtype W.injective_subtype
  stable g x hx := by
    simpa only [Submodule.mem_comap, LinearMap.restrictScalars_apply,
      Submodule.subtype_apply, ContinuousRep.coe_subrepresentation_apply] using Λ.stable g x hx

@[simp]
theorem submodel_lattice [IsFractionRing O E] [IsNoetherianRing O] :
    (Λ.submodel W hW).lattice = Λ.lattice.comap (W.subtype.restrictScalars O) :=
  (rfl)

/-- Inclusion of the induced subspace lattice into the original lattice. -/
def submodelInclusion [IsFractionRing O E] [IsNoetherianRing O] :
    (Λ.submodel W hW).lattice →ₗ[O] Λ.lattice :=
  (W.subtype.restrictScalars O).submoduleComap Λ.lattice

@[simp]
theorem coe_submodelInclusion [IsFractionRing O E] [IsNoetherianRing O]
    (x : (Λ.submodel W hW).lattice) :
    (Λ.submodelInclusion W hW x : V) = (x : W) :=
  (rfl)

/-- Inclusion of the subspace lattice is injective. -/
theorem submodelInclusion_injective [IsFractionRing O E] [IsNoetherianRing O] :
    Function.Injective (Λ.submodelInclusion W hW) := by
  intro x y h
  exact Subtype.ext (Subtype.ext (congrArg (fun z : Λ.lattice ↦ (z : V)) h))

/-- Inclusion intertwines the integral actions. -/
theorem submodelInclusion_equivariant [IsFractionRing O E] [IsNoetherianRing O]
    (g : Γ) (x : (Λ.submodel W hW).lattice) :
    Λ.submodelInclusion W hW ((Λ.submodel W hW).toContinuousRep g x) =
      Λ.toContinuousRep g (Λ.submodelInclusion W hW x) := by
  apply Subtype.ext
  simp

end Subspace

section Quotient

variable {E : Type*} [CommRing E] [Algebra O E]
  {V : Type*} [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]
  [TopologicalSpace V] [IsTopologicalAddGroup V] {ρ : ContinuousRep Γ E V}
  (Λ : IntegralModel O ρ) (W : Submodule E V) (hW : ∀ g, ∀ x ∈ W, ρ g x ∈ W)

/-- The image of `Λ` in the quotient by an invariant vector subspace. -/
def quotientModel : IntegralModel O (ρ.quotient W hW) where
  lattice := Λ.lattice.map (W.mkQ.restrictScalars O)
  isLattice := Λ.lattice.isLattice_map W.mkQ W.mkQ_surjective
  stable g x hx := by
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨ρ g y, Λ.stable g y hy, by simp⟩

@[simp]
theorem quotientModel_lattice :
    (Λ.quotientModel W hW).lattice = Λ.lattice.map (W.mkQ.restrictScalars O) :=
  (rfl)

/-- The surjection from the original lattice onto its quotient model. -/
def quotientProjection : Λ.lattice →ₗ[O] (Λ.quotientModel W hW).lattice :=
  (W.mkQ.restrictScalars O).submoduleMap Λ.lattice

@[simp]
theorem coe_quotientProjection (x : Λ.lattice) :
    (Λ.quotientProjection W hW x : V ⧸ W) = W.mkQ (x : V) :=
  (rfl)

/-- The projection onto the quotient lattice is surjective. -/
theorem quotientProjection_surjective : Function.Surjective (Λ.quotientProjection W hW) :=
  (W.mkQ.restrictScalars O).submoduleMap_surjective Λ.lattice

/-- The projection's kernel is exactly the intersection with the invariant subspace,
viewed inside `Λ`. -/
@[simp]
theorem ker_quotientProjection :
    LinearMap.ker (Λ.quotientProjection W hW) =
      (W.restrictScalars O).comap Λ.lattice.subtype := by
  ext x
  simp [LinearMap.mem_ker, ← Subtype.val_inj]

/-- The projection intertwines the integral actions. -/
theorem quotientProjection_equivariant (g : Γ) (x : Λ.lattice) :
    Λ.quotientProjection W hW (Λ.toContinuousRep g x) =
      (Λ.quotientModel W hW).toContinuousRep g (Λ.quotientProjection W hW x) := by
  apply Subtype.ext
  simp

/-- The quotient of the lattice by its intersection with `W` is the induced quotient lattice. -/
noncomputable def quotientLatticeEquiv :
    (Λ.lattice ⧸ (W.restrictScalars O).comap Λ.lattice.subtype) ≃ₗ[O]
      (Λ.quotientModel W hW).lattice :=
  (Submodule.quotEquivOfEq _ _ (Λ.ker_quotientProjection W hW).symm).trans
    ((Λ.quotientProjection W hW).quotKerEquivOfSurjective
      (Λ.quotientProjection_surjective W hW))

@[simp]
theorem quotientLatticeEquiv_mk (x : Λ.lattice) :
    Λ.quotientLatticeEquiv W hW (Submodule.Quotient.mk x) = Λ.quotientProjection W hW x := by
  simp only [quotientLatticeEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
  exact LinearMap.quotKerEquivOfSurjective_apply_mk _ _ x

end Quotient

section Exactness

variable {E : Type*} [Field E] [Algebra O E]
  {V : Type*} [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]
  [TopologicalSpace V] [IsTopologicalAddGroup V] {ρ : ContinuousRep Γ E V}
  (Λ : IntegralModel O ρ) (W : Submodule E V) (hW : ∀ g, ∀ x ∈ W, ρ g x ∈ W)

/-- The inclusion and projection form an exact sequence of integral lattices. -/
theorem range_submodelInclusion_eq_ker_quotientProjection
    [IsFractionRing O E] [IsNoetherianRing O] :
    LinearMap.range (Λ.submodelInclusion W hW) =
      LinearMap.ker (Λ.quotientProjection W hW) := by
  rw [ker_quotientProjection]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (y : W).property
  · intro hx
    exact ⟨⟨⟨x, hx⟩, x.property⟩, rfl⟩

end Exactness

end TauCeti.GaloisLattice.IntegralModel
