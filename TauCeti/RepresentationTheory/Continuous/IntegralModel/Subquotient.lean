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

Subquotient integral models pass integral structures across invariant subspaces, quotients
and short exact sequences of representations. The subspace lattice is the intersection with
the original lattice; the quotient lattice is its image in the quotient vector space. The
inclusion and projection form an exact sequence, and the quotient of the original lattice
by this intersection is isomorphic to its image.

The restriction requires a Noetherian coefficient domain with the given fraction field.
The quotient construction and the exactness statement require only `ContinuousAdd V` for
the ambient topology: the quotient map is then open, so the quotient action is jointly
continuous. The quotient image is a lattice without a Noetherian or fraction-field hypothesis.
These constructions apply in particular to discrete valuation rings and do not require
compactness of the acting group.

## Main declarations

* `TauCeti.GaloisLattice.IntegralModel.submodel`: the model on an invariant subspace.
* `TauCeti.GaloisLattice.IntegralModel.submodelInclusion`: inclusion into the original lattice.
* `TauCeti.GaloisLattice.IntegralModel.quotientModel`: the model on the quotient representation.
* `TauCeti.GaloisLattice.IntegralModel.quotientProjection`: projection onto the quotient lattice.
* `TauCeti.GaloisLattice.IntegralModel.quotientLatticeEquiv`: the lattice quotient isomorphism.
* `TauCeti.GaloisLattice.IntegralModel.range_submodelInclusion_eq_ker_quotientProjection`:
  exactness of the lattice inclusion and projection.

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
theorem lattice_submodel [IsFractionRing O E] [IsNoetherianRing O] :
    (Λ.submodel W hW).lattice = Λ.lattice.comap (W.subtype.restrictScalars O) :=
  (rfl)

/-- Inclusion of the induced subspace lattice into the original lattice. -/
def submodelInclusion [IsFractionRing O E] [IsNoetherianRing O] :
    (Λ.submodel W hW).lattice →ₗ[O] Λ.lattice :=
  (W.subtype.restrictScalars O).submoduleComap Λ.lattice

@[simp]
theorem coe_submodelInclusion_apply [IsFractionRing O E] [IsNoetherianRing O]
    (x : (Λ.submodel W hW).lattice) :
    (Λ.submodelInclusion W hW x : V) = (x : W) :=
  (rfl)

/-- The inclusion has range equal to the intersection with `W`, viewed inside `Λ`. -/
@[simp]
theorem range_submodelInclusion [IsFractionRing O E] [IsNoetherianRing O] :
    LinearMap.range (Λ.submodelInclusion W hW) =
      (W.restrictScalars O).comap Λ.lattice.subtype := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (y : W).property
  · intro hx
    exact ⟨⟨⟨x, hx⟩, x.property⟩, rfl⟩

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
  [TopologicalSpace V] [ContinuousAdd V] {ρ : ContinuousRep Γ E V}
  (Λ : IntegralModel O ρ) (W : Submodule E V) (hW : ∀ g, ∀ x ∈ W, ρ g x ∈ W)

/-- The image of `Λ` in the quotient by an invariant vector subspace. -/
def quotientModel : IntegralModel O (ρ.quotient W hW) where
  lattice := Λ.lattice.map (W.mkQ.restrictScalars O)
  isLattice := Λ.lattice.isLattice_map W.mkQ W.mkQ_surjective
  stable g x hx := by
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨ρ g y, Λ.stable g y hy, by simp⟩

@[simp]
theorem lattice_quotientModel :
    (Λ.quotientModel W hW).lattice = Λ.lattice.map (W.mkQ.restrictScalars O) :=
  (rfl)

/-- The surjection from the original lattice onto its quotient model. -/
def quotientProjection : Λ.lattice →ₗ[O] (Λ.quotientModel W hW).lattice :=
  (W.mkQ.restrictScalars O).submoduleMap Λ.lattice

@[simp]
theorem coe_quotientProjection_apply (x : Λ.lattice) :
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

@[simp]
theorem quotientLatticeEquiv_symm_quotientProjection (x : Λ.lattice) :
    (Λ.quotientLatticeEquiv W hW).symm (Λ.quotientProjection W hW x) =
      Submodule.Quotient.mk x :=
  (Λ.quotientLatticeEquiv W hW).symm_apply_eq.mpr (Λ.quotientLatticeEquiv_mk W hW x).symm

end Quotient

section Exactness

variable {E : Type*} [Field E] [Algebra O E]
  {V : Type*} [AddCommGroup V] [Module E V] [Module O V] [IsScalarTower O E V]
  [TopologicalSpace V] [ContinuousAdd V] {ρ : ContinuousRep Γ E V}
  (Λ : IntegralModel O ρ) (W : Submodule E V) (hW : ∀ g, ∀ x ∈ W, ρ g x ∈ W)

/-- The inclusion and projection form an exact sequence of integral lattices. -/
theorem range_submodelInclusion_eq_ker_quotientProjection
    [IsFractionRing O E] [IsNoetherianRing O] :
    LinearMap.range (Λ.submodelInclusion W hW) =
      LinearMap.ker (Λ.quotientProjection W hW) := by
  rw [range_submodelInclusion, ker_quotientProjection]

end Exactness

end TauCeti.GaloisLattice.IntegralModel
