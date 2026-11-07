/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.CentralIdempotent
public import TauCeti.RepresentationTheory.CharacterTable.Values
public import TauCeti.RepresentationTheory.Unitary
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.RingTheory.SimpleModule.Isotypic
import TauCeti.RepresentationTheory.AsAlgebraHom
import TauCeti.RepresentationTheory.AsModule
import TauCeti.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Maschke

/-!
# The primitive central idempotents act as the isotypic projections

Let `G` be a finite group, `k` an algebraically closed field in which `|G|` is invertible, and `ρ`
an irreducible representation of `G` over `k` with character `χ`. The primitive central idempotent
`e_ρ = (χ(1)/|G|) ∑_g χ(g⁻¹) g` of
`TauCeti/RepresentationTheory/CharacterTable/CentralIdempotent.lean` acts as the identity on `ρ`
and as zero on every irreducible representation not isomorphic to `ρ`. This file reads that off on
an arbitrary representation `σ` of `G`: the operator `σ(e_ρ)` is a projection whose range is the
`ρ`-isotypic component of `σ`, the sum of the subrepresentations isomorphic to `ρ`. No finiteness
is asked of `σ`: Maschke's theorem makes it the sum of its simple subrepresentations, and each of
those is finite-dimensional, being cyclic over the finite-dimensional algebra `k[G]`.

Over `ℂ` this projection is orthogonal as soon as `σ` is unitary on an inner product space.
Inversion conjugates character values, so the coefficients of `e_ρ` satisfy
`e_ρ(g⁻¹) = conj (e_ρ(g))`, and such a group-algebra element acts on a unitary representation by a
symmetric operator (`Representation.isSymmetric_asAlgebraHom`). A symmetric idempotent operator is
the orthogonal projection onto its range, so the orthogonal projection onto the `ρ`-isotypic
component of a finite-dimensional unitary representation is the explicit operator

`(χ(1)/|G|) ∑_g conj (χ(g)) σ(g)`.

## Main statements

* `Representation.primitiveCentralIdempotent_smul_of_mem`: `e_ρ` acts on a simple
  submodule as the identity or as zero, according to whether it is isomorphic to `ρ`.
* `Representation.primitiveCentralIdempotent_smul_eq_self_iff`: a vector is fixed by
  `e_ρ` exactly when it lies in the `ρ`-isotypic component.
* `Representation.range_asAlgebraHom_primitiveCentralIdempotent`: **the range of the action
  of `e_ρ` is the `ρ`-isotypic component**.
* `Representation.primitiveCentralIdempotent_coeff_inv`: over `ℂ`, the coefficients of
  `e_ρ` are conjugate-symmetric.
* `Representation.isSymmetricProjection_asAlgebraHom_primitiveCentralIdempotent`: over `ℂ`,
  `e_ρ` acts on a unitary representation by a symmetric projection.
* `Representation.asAlgebraHom_primitiveCentralIdempotent_eq_starProjection`: **`e_ρ` acts
  on a finite-dimensional unitary representation as the orthogonal projection onto its
  `ρ`-isotypic component**, and `Representation.starProjection_isotypicComponent_apply`
  writes that projection as `(χ(1)/|G|) ∑_g conj (χ(g)) σ(g)`.

## References

See J.-P. Serre, *Linear Representations of Finite Groups*, Section 2.6, Theorem 8, or
I. M. Isaacs, *Character Theory of Finite Groups*, Theorem 2.12.
-/

public section

open scoped InnerProductSpace MonoidAlgebra

open TauCeti.Representation

namespace Representation

/-! ### The range of the action of a primitive central idempotent -/

section Range

variable {k G V W : Type*} [Field k] [Group G] [Fintype G] [IsAlgClosed k]
  [Invertible (Nat.card G : k)]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V] [AddCommGroup W] [Module k W]
  (ρ : Representation k G V) [ρ.IsIrreducible] (σ : Representation k G W)

open scoped Classical in
/-- **A primitive central idempotent acts on a simple `k[G]`-submodule** of a representation as the
identity if the submodule is isomorphic to `ρ`, and as zero otherwise. No finiteness is asked of the
representation: the submodule is cyclic over `k[G]`, hence finite-dimensional, and carries an
irreducible subrepresentation to which
`TauCeti.Representation.asAlgebraHom_primitiveCentralIdempotent` applies. -/
theorem primitiveCentralIdempotent_smul_of_mem (m : Submodule k[G] σ.asModule)
    [IsSimpleModule k[G] m] {x : σ.asModule} (hx : x ∈ m) :
    primitiveCentralIdempotent ρ • x =
      if Nonempty (m ≃ₗ[k[G]] ρ.asModule) then x else 0 := by
  classical
  -- The submodule of the subrepresentation `ofSubmodule' m` is `m` itself, by `rfl`: this is the
  -- `right_inv` field of `Subrepresentation.subrepresentationSubmoduleOrderIso`.
  let τ : Subrepresentation σ := Subrepresentation.ofSubmodule' m
  have hatom : IsAtom τ := Subrepresentation.isSimpleModule_asSubmodule_iff.mp ‹_›
  have : τ.toRepresentation.IsIrreducible :=
    isIrreducible_toRepresentation_of_isAtom hatom
  let eτ : τ.toRepresentation.asModule ≃ₗ[k[G]] m := τ.asModuleEquivAsSubmodule
  have : IsSimpleModule k[G] τ.toRepresentation.asModule := IsSimpleModule.congr eτ
  -- A simple `k[G]`-module is cyclic, hence finite-dimensional over `k`.
  have : FiniteDimensional k τ.toSubmodule := by
    have := IsSimpleModule.nontrivial k[G] τ.toRepresentation.asModule
    obtain ⟨y, hy⟩ := exists_ne (0 : τ.toRepresentation.asModule)
    have : Module.Finite k τ.toRepresentation.asModule :=
      Module.Finite.of_surjective ((LinearMap.toSpanSingleton k[G] _ y).restrictScalars k)
        (IsSimpleModule.toSpanSingleton_surjective k[G] hy)
    exact Module.Finite.equiv τ.toRepresentation.asModuleEquiv
  have hiff : Nonempty (ρ.Equiv τ.toRepresentation) ↔ Nonempty (m ≃ₗ[k[G]] ρ.asModule) :=
    nonempty_equiv_iff.trans
      ⟨fun ⟨f⟩ => ⟨(f.trans eτ).symm⟩, fun ⟨f⟩ => ⟨(eτ.trans f).symm⟩⟩
  -- `ofSubmodule'` has the same carrier as `m`; Mathlib states this membership on `W` directly.
  have hxτ : σ.asModuleEquiv x ∈ τ.toSubmodule := Subrepresentation.mem_ofSubmodule'_iff.mpr hx
  apply σ.asModuleEquiv.injective
  rw [σ.asModuleEquiv_map_smul,
    ← Subrepresentation.coe_toRepresentation_asAlgebraHom_apply τ _ ⟨_, hxτ⟩,
    asAlgebraHom_primitiveCentralIdempotent, hiff]
  split_ifs
  · rw [LinearMap.id_apply]
  · rw [LinearMap.zero_apply, map_zero, ZeroMemClass.coe_zero]

/-- **A vector is fixed by the primitive central idempotent exactly when it lies in the
`ρ`-isotypic component**, the sum of the simple `k[G]`-submodules isomorphic to `ρ`. -/
theorem primitiveCentralIdempotent_smul_eq_self_iff {x : σ.asModule} :
    primitiveCentralIdempotent ρ • x = x ↔ x ∈ isotypicComponent k[G] σ.asModule ρ.asModule := by
  classical
  -- Being central, `e_ρ` acts by a `k[G]`-linear endomorphism.
  let p : σ.asModule →ₗ[k[G]] σ.asModule :=
    { toFun := (primitiveCentralIdempotent ρ • ·)
      map_add' := smul_add _
      map_smul' := fun a y => by
        rw [RingHom.id_apply, smul_smul, smul_smul,
          (Subalgebra.mem_center_iff.mp (primitiveCentralIdempotent_mem_center ρ) a)] }
  have hp (y : σ.asModule) : p y = primitiveCentralIdempotent ρ • y := rfl
  constructor
  · -- `e_ρ` maps each simple submodule into the isotypic component, hence maps everything there.
    intro hx
    have htop : ⊤ ≤ (isotypicComponent k[G] σ.asModule ρ.asModule).comap p := by
      rw [← IsSemisimpleModule.sSup_simples_eq_top k[G] σ.asModule]
      refine sSup_le fun m (hm : IsSimpleModule k[G] m) y hy => ?_
      rw [Submodule.mem_comap, hp, primitiveCentralIdempotent_smul_of_mem ρ σ m hy]
      split_ifs with h
      · rw [← h.some.isotypicComponent_eq]
        exact m.le_isotypicComponent hy
      · exact Submodule.zero_mem _
    rw [← hx]
    exact htop Submodule.mem_top
  · -- `e_ρ` fixes each submodule isomorphic to `ρ`, hence fixes their sum.
    intro hx
    rw [isotypicComponent] at hx
    refine (sSup_le fun m (hm : Nonempty (m ≃ₗ[k[G]] ρ.asModule)) y hy => ?_ :
      _ ≤ LinearMap.eqLocus p LinearMap.id) hx
    have : IsSimpleModule k[G] m := IsSimpleModule.congr hm.some
    rw [LinearMap.mem_eqLocus, hp, LinearMap.id_apply,
      primitiveCentralIdempotent_smul_of_mem ρ σ m hy, ite_eq_left hm]

/-- **The primitive central idempotent projects onto the isotypic component.** The range of its
action on any representation `σ` is the `ρ`-isotypic component of `σ`, read as a subspace of the
carrier of `σ`. -/
theorem range_asAlgebraHom_primitiveCentralIdempotent :
    LinearMap.range (σ.asAlgebraHom (primitiveCentralIdempotent ρ)) =
      ((isotypicComponent k[G] σ.asModule ρ.asModule).restrictScalars k).comap
        σ.asModuleEquiv.symm.toLinearMap := by
  ext w
  rw [LinearMap.IsIdempotentElem.mem_range_iff
      ((isIdempotentElem_primitiveCentralIdempotent ρ).map σ.asAlgebraHom),
    Submodule.mem_comap, Submodule.restrictScalars_mem, LinearEquiv.coe_coe,
    ← primitiveCentralIdempotent_smul_eq_self_iff, ← σ.asModuleEquiv.injective.eq_iff,
    σ.asModuleEquiv_map_smul, LinearEquiv.apply_symm_apply]

end Range

/-! ### Orthogonality over `ℂ` -/

section Complex

variable {G V W : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V)
  [ρ.IsIrreducible] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (σ : Representation ℂ G W)

/-- **The coefficients of a complex primitive central idempotent are conjugate-symmetric**:
inverting the group element conjugates the coefficient, because inversion conjugates character
values (`TauCeti.Representation.conj_char`) and the degree `χ(1)` is real. -/
theorem primitiveCentralIdempotent_coeff_inv (g : G) :
    (primitiveCentralIdempotent ρ).coeff g⁻¹ = star ((primitiveCentralIdempotent ρ).coeff g) := by
  simp

/-- **Over `ℂ`, a primitive central idempotent acts on a unitary representation by a symmetric
projection**, that is, by an orthogonal projection. -/
theorem isSymmetricProjection_asAlgebraHom_primitiveCentralIdempotent
    (hσ : ∀ g v w, ⟪σ g v, σ g w⟫_ℂ = ⟪v, w⟫_ℂ) :
    (σ.asAlgebraHom (primitiveCentralIdempotent ρ)).IsSymmetricProjection :=
  σ.isSymmetricProjection_asAlgebraHom hσ (primitiveCentralIdempotent_coeff_inv ρ)
    (isIdempotentElem_primitiveCentralIdempotent ρ)

variable [FiniteDimensional ℂ W]

/-- **A primitive central idempotent acts on a finite-dimensional unitary representation as the
orthogonal projection onto the isotypic component**: `σ(e_ρ)` is the orthogonal projection of the
carrier of `σ` onto its `ρ`-isotypic component. -/
theorem asAlgebraHom_primitiveCentralIdempotent_eq_starProjection
    (hσ : ∀ g v w, ⟪σ g v, σ g w⟫_ℂ = ⟪v, w⟫_ℂ) :
    σ.asAlgebraHom (primitiveCentralIdempotent ρ) =
      (((isotypicComponent ℂ[G] σ.asModule ρ.asModule).restrictScalars ℂ).comap
        σ.asModuleEquiv.symm.toLinearMap).starProjection.toLinearMap := by
  have h := isSymmetricProjection_asAlgebraHom_primitiveCentralIdempotent ρ σ hσ
  rw [LinearMap.isSymmetricProjection_iff_eq_coe_starProjection_range,
    range_asAlgebraHom_primitiveCentralIdempotent] at h
  obtain ⟨_, h⟩ := h
  exact h

/-- **The orthogonal projection onto an isotypic component, explicitly.** In a finite-dimensional
unitary representation `σ`, the orthogonal projection onto the `ρ`-isotypic component is
`w ↦ ∑_g (χ(1)/|G|) conj (χ(g)) σ(g) w`, where `χ` is the character of `ρ`. -/
theorem starProjection_isotypicComponent_apply (hσ : ∀ g v w, ⟪σ g v, σ g w⟫_ℂ = ⟪v, w⟫_ℂ)
    (w : W) :
    (((isotypicComponent ℂ[G] σ.asModule ρ.asModule).restrictScalars ℂ).comap
        σ.asModuleEquiv.symm.toLinearMap).starProjection w =
      ∑ g, ((Nat.card G : ℂ)⁻¹ * ρ.character 1 * starRingEnd ℂ (ρ.character g)) • σ g w := by
  rw [← ContinuousLinearMap.coe_coe,
    ← asAlgebraHom_primitiveCentralIdempotent_eq_starProjection ρ σ hσ, σ.asAlgebraHom_eq_sum]
  simp

end Complex

end Representation
